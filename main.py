#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Каталогизатор фото и видео файлов.

Описание:
    Скрипт сканирует указанные директории, извлекает дату создания из метаданных
    (EXIF для изображений, медиа-теги для видео) и копирует файлы в структурированную
    иерархию: {год}/{год-месяц-день}/{дата-время_оригинал.расширение}

Особенности:
    - Поддержка многопоточной обработки через ProcessPoolExecutor
    - Распаковка ZIP-архивов во временную директорию
    - Гибкий парсинг дат из различных форматов метаданных
    - Сухой запуск (dry-run) для тестирования без записи
    - Интерактивный режим и работа через аргументы командной строки
    - Детальная статистика и логирование ошибок

Зависимости:
    - Pillow (PIL) — для работы с EXIF изображений
    - pymediainfo — для извлечения метаданных видео (опционально, но рекомендуется)
    - tqdm — для отображения прогресс-бара (опционально)

Дата: 2026
"""

# =============================================================================
# ИМПОРТ МОДУЛЕЙ
# =============================================================================

# Стандартная библиотека
import os
import sys
import shutil
import argparse
import multiprocessing
import zipfile
import tempfile
import time
import hashlib
import re
from datetime import datetime
from collections import Counter
from concurrent.futures import ProcessPoolExecutor, as_completed
from pathlib import Path
from typing import Optional, List, Dict, Tuple, Set, Any

# Сторонние библиотеки (обязательные)
from PIL import Image, ExifTags
from pymediainfo import MediaInfo
from tqdm import tqdm

USE_TQDM: bool = True

# =============================================================================
# ГЛОБАЛЬНЫЕ НАСТРОЙКИ И КОНСТАНТЫ
# =============================================================================

# --- Расширения поддерживаемых файлов ---
IMAGE_EXTENSIONS: Set[str] = {
    '.jpg', '.jpeg', '.png', '.tiff', '.bmp', '.gif', '.webp',
    '.heic', '.dng', '.cr2', '.nef', '.arw'
}
VIDEO_EXTENSIONS: Set[str] = {
    '.mp4', '.mov', '.avi', '.mkv', '.m4v', '.3gp',
    '.mts', '.m2ts', '.wmv', '.flv'
}
ARCHIVE_EXTENSIONS: Set[str] = {'.zip'}

# Объединённое множество всех поддерживаемых расширений
SUPPORTED_EXTENSIONS: Set[str] = IMAGE_EXTENSIONS.union(VIDEO_EXTENSIONS)

# --- Пути по умолчанию ---
DEFAULT_SOURCE_PATH: str = r"c:\Свалка"
DEFAULT_DEST_PATH: str = r"c:\Фото"

# --- Настройки многопоточности ---
DEFAULT_WORKERS: int = multiprocessing.cpu_count()
DEFAULT_BATCH_SIZE: int = 50

# --- Настройки поведения по умолчанию ---
# ВАЖНО: fast_video=False означает, что метаданные видео БУДУТ анализироваться
DEFAULT_FAST_VIDEO: bool = False  # По умолчанию — полный анализ метаданных
DEFAULT_EXTRACT_ZIPS: bool = True
DEFAULT_DRY_RUN: bool = False

# =============================================================================
# ИНИЦИАЛИЗАЦИЯ MEDIAINFO (для видео-метаданных)
# =============================================================================

# Глобальные флаги доступности MediaInfo
MEDIAINFO_AVAILABLE: bool = False
MEDIAINFO_ERROR_MESSAGE: str = ""


def _initialize_mediainfo() -> Tuple[bool, str]:
    """
    Инициализация MediaInfo с поддержкой всех версий pymediainfo.
    
    Алгоритм:
    1. Пробуем современный API configure() (pymediainfo >= 2.x)
    2. Фоллбэк на устаревший set_library_path() (pymediainfo < 2.x)
    3. Системный фоллбэк через os.add_dll_directory() для Windows
    4. Проверка работоспособности через тестовый файл
    
    Returns:
        Tuple[bool, str]: (успех, сообщение об ошибке или пустая строка)
    """
    import sys
    import platform
    
    # Проверяем, что модуль импортирован
    try:
        from pymediainfo import MediaInfo
    except ImportError as e:
        return False, f"❌ Модуль pymediainfo не установлен: {e}"
    
    # Список путей для поиска MediaInfo.dll / libmediainfo.so
    dll_paths_to_try = []
    
    # Добавляем стандартные пути в зависимости от ОС
    if platform.system() == "Windows":
        # Пути Windows
        dll_paths_to_try.extend([
            os.path.join(os.environ.get("ProgramFiles", "C:\\Program Files"), "MediaInfo"),
            os.path.join(os.environ.get("ProgramFiles(x86)", "C:\\Program Files (x86)"), "MediaInfo"),
            os.path.dirname(os.path.abspath(__file__)),
            os.getcwd(),
        ])
        # Добавляем путь из PATH если есть
        system_path = os.environ.get("PATH", "")
        for path_entry in system_path.split(";"):
            if "MediaInfo" in path_entry and os.path.isdir(path_entry):
                dll_paths_to_try.append(path_entry)
    else:
        # Пути Linux/macOS
        dll_paths_to_try.extend([
            "/usr/lib",
            "/usr/local/lib",
            "/opt/homebrew/lib",
            "/usr/lib/x86_64-linux-gnu",
            os.path.dirname(os.path.abspath(__file__)),
        ])
    
    # Попытка инициализации через современный API configure()
    try:
        if hasattr(MediaInfo, 'configure'):
            # Современный API (pymediainfo >= 2.x)
            for dll_path in dll_paths_to_try:
                try:
                    MediaInfo.configure(dll_path=dll_path)
                    if _check_mediainfo_functionality():
                        return True, ""
                except Exception:
                    continue
            # Пробуем без явного пути (системный поиск)
            MediaInfo.configure()
            if _check_mediainfo_functionality():
                return True, ""
    except Exception:
        pass
    
    # Попытка инициализации через устаревший API set_library_path()
    try:
        if hasattr(MediaInfo, 'set_library_path'):
            # Устаревший API (pymediainfo < 2.x)
            for dll_path in dll_paths_to_try:
                try:
                    MediaInfo.set_library_path(dll_path)
                    if _check_mediainfo_functionality():
                        return True, ""
                except Exception:
                    continue
    except Exception:
        pass
    
    # Системный фоллбэк через os.add_dll_directory() для Windows
    if platform.system() == "Windows":
        try:
            for dll_path in dll_paths_to_try:
                try:
                    if os.path.isdir(dll_path):
                        os.add_dll_directory(dll_path)
                except (OSError, AttributeError):
                    # os.add_dll_directory доступен только в Python 3.8+
                    continue
            
            # После добавления путей пробуем ещё раз
            if _check_mediainfo_functionality():
                return True, ""
        except Exception:
            pass
    
    # Финальная проверка: современные версии pymediainfo могут работать без конфигурации
    # Если MediaInfo.parse работает напрямую — считаем что всё ок
    if _check_mediainfo_functionality():
        return True, ""
    
    # Если ничего не помогло — возвращаем ошибку
    return False, "⚠️  MediaInfo.dll не найдена или не загружается. Установите MediaInfo."


def _check_mediainfo_functionality() -> bool:
    """
    Внутренняя проверка работоспособности pymediainfo.

    Создаёт временный файл и пытается проанализировать его,
    чтобы убедиться, что DLL-библиотека загружена корректно.

    Returns:
        bool: True если MediaInfo работает, False иначе
    """
    try:
        with tempfile.NamedTemporaryFile(suffix='.mp4', delete=False) as tmp:
            test_path = tmp.name
        try:
            # Попытка парсинга — даже если файл пустой, это проверит загрузку DLL
            MediaInfo.parse(test_path)
        except Exception:
            # Ожидаем ошибку парсинга пустого файла — это нормально
            # Важно, что не возникло ошибки импорта/загрузки DLL
            pass
        finally:
            if os.path.exists(test_path):
                os.unlink(test_path)
        return True
    except Exception:
        return False


# Инициализация MediaInfo при загрузке модуля
MEDIAINFO_AVAILABLE, MEDIAINFO_ERROR_MESSAGE = _initialize_mediainfo()


# =============================================================================
# ФУНКЦИИ ИЗВЛЕЧЕНИЯ ДАТЫ ИЗ МЕТАДАННЫХ
# =============================================================================

def extract_date_from_image(filepath: str) -> Optional[datetime]:
    """
    Извлекает дату съёмки из EXIF-метаданных изображения.

    Алгоритм:
    1. Открывает изображение через Pillow
    2. Получает EXIF-словарь
    3. Ищет теги DateTimeOriginal или DateTime
    4. Парсит строку даты в объект datetime

    Args:
        filepath: Путь к файлу изображения

    Returns:
        datetime: Дата съёмки если найдена, None иначе
    """
    try:
        with Image.open(filepath) as img:
            exif_data = img._getexif()
            if not exif_data:
                return None

            # Перебираем EXIF-теги и ищем нужные поля даты
            for tag_id, value in exif_data.items():
                tag_name = ExifTags.TAGS.get(tag_id, tag_id)
                if tag_name in ('DateTimeOriginal', 'DateTime'):
                    # Формат даты в EXIF: "YYYY:MM:DD HH:MM:SS"
                    return datetime.strptime(value, "%Y:%m:%d %H:%M:%S")
    except Exception:
        # Любая ошибка (повреждённый файл, нет EXIF и т.д.) — возвращаем None
        pass
    return None


def parse_flexible_date(date_string: Optional[str]) -> Optional[datetime]:
    """
    Гибкий парсер дат из видео-метаданных.

    Поддерживает множественные форматы:
    - Стандартные: "%Y-%m-%d %H:%M:%S", "%Y/%m/%d %H:%M:%S"
    - С микросекундами: "%Y-%m-%d %H:%M:%S.%f"
    - ISO 8601: "%Y-%m-%dT%H:%M:%S"
    - Регулярное выражение как запасной вариант

    Args:
        date_string: Строка с датой из метаданных

    Returns:
        datetime: Распаршенная дата или None если не удалось
    """
    if not date_string:
        return None

    # Очистка строки от служебных маркеров временных зон
    cleaned = str(date_string).replace('UTC', '').replace('GMT', '').replace('.', '').strip()

    # Список форматов для попытки парсинга (по приоритету)
    date_formats = [
        "%Y-%m-%d %H:%M:%S",
        "%Y-%m-%d %H:%M:%S.%f",
        "%Y-%m-%dT%H:%M:%S",
        "%Y/%m/%d %H:%M:%S"
    ]

    # Пробуем каждый формат последовательно
    for fmt in date_formats:
        try:
            # Обрезаем строку до длины формата (для совместимости с %f)
            return datetime.strptime(cleaned[:len(fmt)], fmt)
        except ValueError:
            continue

    # Запасной вариант: парсинг через регулярное выражение
    date_pattern = r'(\d{4})[-/](\d{2})[-/](\d{2})[T ](\d{2}):(\d{2}):(\d{2})'
    match = re.search(date_pattern, cleaned)
    if match:
        try:
            return datetime(
                year=int(match.group(1)),
                month=int(match.group(2)),
                day=int(match.group(3)),
                hour=int(match.group(4)),
                minute=int(match.group(5)),
                second=int(match.group(6))
            )
        except (ValueError, IndexError):
            pass

    return None


def extract_date_from_video(filepath: str, fast_mode: bool = False) -> Optional[datetime]:
    """
    Извлекает дату записи из метаданных видеофайла.

    Args:
        filepath: Путь к видеофайлу
        fast_mode:
            - False (по умолчанию): пытается извлечь дату из медиа-тегов через MediaInfo
            - True: пропускает анализ метаданных, возвращает None (будет использована дата файла)

    Returns:
        datetime: Дата записи если найдена, None иначе
    """
    # Если включён быстрый режим — сразу возвращаем None
    if fast_mode:
        return None

    # Если MediaInfo недоступен — нечего парсить
    if not MEDIAINFO_AVAILABLE:
        return None

    try:
        # Парсим файл через MediaInfo
        media_info = MediaInfo.parse(filepath)

        # Ищем трек типа "General" — там хранятся основные метаданные
        for track in media_info.tracks:
            if track.track_type != 'General':
                continue

            # Список полей-кандидатов на дату создания (по приоритету)
            date_fields = [
                'encoded_date',  # Дата кодирования
                'recorded_date',  # Дата записи (наиболее релевантно)
                'tagged_date',  # Дата добавления тегов
                'file_created_date'  # Дата создания файла в контейнере
            ]

            for field_name in date_fields:
                field_value = getattr(track, field_name, None)
                if field_value:
                    parsed_date = parse_flexible_date(str(field_value))
                    if parsed_date:
                        return parsed_date

    except Exception:
        # Любая ошибка парсинга — не критична, возвращаем None
        pass

    return None


def get_file_creation_date(filepath: str, fast_video: bool = False) -> datetime:
    """
    Универсальная функция получения даты файла.

    Приоритет источников даты:
    1. Для изображений: EXIF (DateTimeOriginal)
    2. Для видео: метаданные через MediaInfo (если fast_video=False)
    3. Запасной вариант: дата последнего изменения файла (mtime)
    4. Крайний случай: текущее время

    Args:
        filepath: Путь к файлу
        fast_video: Если True — пропускать анализ метаданных видео

    Returns:
        datetime: Определённая дата файла
    """
    file_extension = os.path.splitext(filepath)[1].lower()
    detected_date: Optional[datetime] = None

    # Определяем тип файла и извлекаем дату соответствующим методом
    if file_extension in IMAGE_EXTENSIONS:
        detected_date = extract_date_from_image(filepath)
    elif file_extension in VIDEO_EXTENSIONS:
        detected_date = extract_date_from_video(filepath, fast_mode=fast_video)

    # Если метаданные не дали результат — используем дату изменения файла
    if detected_date is None:
        try:
            detected_date = datetime.fromtimestamp(os.stat(filepath).st_mtime)
        except OSError:
            # Если даже stat не работает — берём текущее время
            detected_date = datetime.now()

    return detected_date


# =============================================================================
# ФУНКЦИИ ОБРАБОТКИ ФАЙЛОВ
# =============================================================================

def generate_target_path(source_file: str, dest_root: str, file_date: datetime) -> Tuple[str, str]:
    """
    Генерирует целевой путь для файла на основе его даты.

    Структура: {dest_root}/{год}/{год-месяц-день}/{год-месяц-день_час-мин-сек.расширение}

    Args:
        source_file: Исходный путь к файлу
        dest_root: Корневая директория назначения
        file_date: Дата файла для формирования пути

    Returns:
        Tuple[str, str]: (целевая_директория, полный_целевой_путь)
    """
    # Формируем компоненты пути
    year_folder = file_date.strftime("%Y")
    day_folder = file_date.strftime("%Y-%m-%d")
    timestamp_filename = file_date.strftime("%Y-%m-%d %H-%M-%S")

    # Получаем расширение исходного файла (в нижнем регистре)
    file_extension = os.path.splitext(source_file)[1].lower()

    # Собираем полный целевой путь
    target_directory = os.path.join(dest_root, year_folder, day_folder)
    target_filename = f"{timestamp_filename}{file_extension}"
    target_path = os.path.join(target_directory, target_filename)

    return target_directory, target_path


def copy_file_with_retry(source: str, target: str, max_retries: int = 3, retry_delay: float = 0.5) -> bool:
    """
    Копирует файл с механизмом повторных попыток при ошибке блокировки.
    
    Обработка WinError 32 (файл занят другим процессом):
    - Делает несколько попыток копирования с задержкой
    - Использует shutil.copy вместо copy2 для минимизации блокировок
    - Закрывает все возможные дескрипторы перед копированием
    
    Args:
        source: Исходный путь
        target: Целевой путь
        max_retries: Максимальное количество попыток
        retry_delay: Задержка между попытками в секундах
        
    Returns:
        bool: True если копирование успешно
    """
    import errno
    
    for attempt in range(max_retries):
        try:
            # Принудительно закрываем любые возможные дескрипторы файла
            # через сборку мусора (на случай если файл был открыт ранее)
            import gc
            gc.collect()
            
            # Копируем файл с сохранением метаданных
            shutil.copy2(source, target)
            return True
            
        except PermissionError as e:
            # WinError 32: файл занят другим процессом
            if attempt < max_retries - 1:
                time.sleep(retry_delay * (attempt + 1))  # Экспоненциальная задержка
                continue
            raise
            
        except OSError as e:
            # Проверяем код ошибки Windows
            if hasattr(e, 'winerror') and e.winerror == 32:
                # Файл занят — пробуем снова
                if attempt < max_retries - 1:
                    time.sleep(retry_delay * (attempt + 1))
                    continue
            raise
    
    return False


def copy_file_with_metadata(source: str, target: str, target_dir: str) -> bool:
    """
    Копирует файл с сохранением метаданных (через copy2).
    
    Включает обработку ошибок блокировки файлов (WinError 32).

    Args:
        source: Исходный путь
        target: Целевой путь
        target_dir: Директория назначения (будет создана если не существует)

    Returns:
        bool: True если операция успешна
    """
    # Создаём директорию если нужно
    os.makedirs(target_dir, exist_ok=True)

    # Копируем файл с механизмом повторных попыток
    return copy_file_with_retry(source, target)


def process_file_batch(batch_args: Tuple[List[str], str, bool, bool]) -> Dict[str, Any]:
    """
    Обрабатывает пачку файлов в отдельном процессе.

    Функция предназначена для выполнения в ProcessPoolExecutor.

    Args:
        batch_args: Кортеж (список_файлов, dest_root, fast_video, dry_run)

    Returns:
        Dict с результатами:
            - success: количество успешно обработанных
            - overwritten: количество перезаписанных
            - errors: количество ошибок
            - error_messages: список сообщений об ошибках
    """
    file_list, dest_root, fast_video, dry_run = batch_args

    # Счётчики результатов
    stats = {
        'success': 0,
        'overwritten': 0,
        'errors': 0,
        'error_messages': []
    }

    # Обрабатываем каждый файл в пачке
    for file_path in file_list:
        try:
            # 1. Определяем дату файла
            file_date = get_file_creation_date(file_path, fast_video=fast_video)

            # 2. Генерируем целевой путь
            target_dir, target_path = generate_target_path(file_path, dest_root, file_date)

            # 3. Проверяем существование целевого файла
            file_exists = os.path.exists(target_path)

            # 4. Выполняем копирование (если не dry-run)
            if not dry_run:
                copy_file_with_metadata(file_path, target_path, target_dir)

            # 5. Обновляем статистику
            if file_exists:
                stats['overwritten'] += 1
            else:
                stats['success'] += 1

        except Exception as error:
            # Ловим все исключения, логируем и продолжаем обработку
            stats['errors'] += 1
            filename = os.path.basename(file_path)
            stats['error_messages'].append(f"{filename}: {str(error)}")

    return stats


# =============================================================================
# ФУНКЦИИ СКАНИРОВАНИЯ И СТАТИСТИКИ
# =============================================================================

def scan_directory_for_media(source_paths: List[str]) -> Tuple[List[str], Dict[str, int], int, int]:
    """
    Рекурсивно сканирует директории в поисках медиафайлов.

    Args:
        source_paths: Список путей для сканирования

    Returns:
        Tuple:
            - supported_files: список путей к поддерживаемым файлам
            - extension_stats: словарь {расширение: количество}
            - total_size: общий размер всех файлов в байтах
            - skipped_size: размер неподдерживаемых файлов
    """
    # Нормализуем вход: если передана строка — превращаем в список
    if isinstance(source_paths, str):
        source_paths = [source_paths]

    supported_files: List[str] = []
    extension_counter: Counter = Counter()
    total_bytes: int = 0
    skipped_bytes: int = 0

    # Проходим по каждой исходной директории
    for source_dir in source_paths:
        if not os.path.isdir(source_dir):
            continue

        # Рекурсивный обход дерева файлов
        for root_dir, _, filenames in os.walk(source_dir):
            for filename in filenames:
                file_path = os.path.join(root_dir, filename)
                file_extension = os.path.splitext(filename)[1].lower()

                # Получаем размер файла (с обработкой ошибок)
                try:
                    file_size = os.path.getsize(file_path)
                except OSError:
                    file_size = 0

                # Обновляем общую статистику
                total_bytes += file_size
                extension_counter[file_extension if file_extension else '(без расширения)'] += 1

                # Классифицируем файл: поддерживаемый или нет
                if file_extension in SUPPORTED_EXTENSIONS:
                    supported_files.append(file_path)
                else:
                    skipped_bytes += file_size

    return supported_files, dict(extension_counter), total_bytes, skipped_bytes


def format_file_size(size_bytes: int) -> str:
    """
    Форматирует размер файла в человекочитаемом виде.

    Args:
        size_bytes: Размер в байтах

    Returns:
        str: Отформатированная строка (например, "1.25 ГБ")
    """
    units = ['Б', 'КБ', 'МБ', 'ГБ', 'ТБ', 'ПБ']
    size = float(size_bytes)

    for unit in units:
        if size < 1024.0:
            return f"{size:.2f} {unit}"
        size /= 1024.0

    return f"{size:.2f} ПБ"


# =============================================================================
# ФУНКЦИИ РАБОТЫ С АРХИВАМИ
# =============================================================================

def extract_zip_archives(source_dir: str, temp_base: str) -> int:
    """
    Находит и распаковывает ZIP-архивы во временную директорию.

    Особенности:
    - Каждому архиву присваивается уникальный суффикс (хеш пути)
    - Сохраняются исходные даты файлов внутри архива
    - Ошибки распаковки логируются, но не прерывают выполнение

    Args:
        source_dir: Корневая директория для поиска архивов
        temp_base: Базовая директория для временных файлов

    Returns:
        int: Количество успешно распакованных архивов
    """
    extracted_count = 0

    # Рекурсивный поиск ZIP-файлов
    for root, _, files in os.walk(source_dir):
        for filename in files:
            if os.path.splitext(filename)[1].lower() not in ARCHIVE_EXTENSIONS:
                continue

            zip_path = os.path.join(root, filename)

            try:
                # Генерируем уникальное имя для директории распаковки
                path_hash = hashlib.md5(zip_path.encode()).hexdigest()[:6]
                safe_name = "".join(c for c in os.path.splitext(filename)[0]
                                    if c.isalnum() or c in (' ', '_')).rstrip()
                extract_path = os.path.join(temp_base, f"{safe_name}_{path_hash}")

                os.makedirs(extract_path, exist_ok=True)

                # Распаковываем архив
                with zipfile.ZipFile(zip_path, 'r') as zip_file:
                    zip_file.extractall(extract_path)

                    # Восстанавливаем даты файлов из архива
                    for zip_info in zip_file.infolist():
                        extracted_file = os.path.join(extract_path, zip_info.filename)
                        if os.path.exists(extracted_file):
                            # Конвертируем дату из формата ZIP в timestamp
                            timestamp = time.mktime(zip_info.date_time + (0, 0, -1))
                            os.utime(extracted_file, (timestamp, timestamp))

                extracted_count += 1

            except Exception as error:
                print(f"⚠️  Ошибка распаковки '{filename}': {error}")

    return extracted_count


# =============================================================================
# ДИАГНОСТИКА И МЕНЮ
# =============================================================================

def diagnose_mediainfo_status() -> None:
    """
    Выводит подробную диагностику состояния MediaInfo.

    Полезно для отладки проблем с парсингом видео-метаданных.
    """
    import struct

    print("\n" + "=" * 70)
    print(" " * 20 + "🔍 ДИАГНОСТИКА MEDIAINFO")
    print("=" * 70)

    # Определяем разрядность Python
    python_bits = struct.calcsize("P") * 8
    print(f"   • Разрядность Python:        {python_bits}-бит")

    # Статус установки pymediainfo
    pymediainfo_installed = 'pymediainfo' in sys.modules
    print(f"   • Модуль pymediainfo:        {'✅ Установлен' if pymediainfo_installed else '❌ Не установлен'}")

    # Статус доступности DLL
    print(f"   • MediaInfo DLL:             {'✅ Доступна' if MEDIAINFO_AVAILABLE else '❌ Не найдена'}")

    # Итоговая рекомендация
    print()
    if MEDIAINFO_AVAILABLE:
        print("   🎉 MediaInfo полностью готов к работе!")
    else:
        print(f"   ❌ Проблема: {MEDIAINFO_ERROR_MESSAGE}")
        print("\n   💡 Пошаговое решение:")
        print("      1. pip install --upgrade pymediainfo")
        print("      2. Скачайте MediaInfo DLL:")
        print("         https://mediaarea.net/ru/MediaInfo/Download/Windows")
        print("      3. Выберите ZIP-архив (НЕ установщик!)")
        print(f"      4. Для {python_bits}-бит Python нужна {python_bits}-бит DLL")
        print("      5. Положите MediaInfo.dll в одну папку со скриптом")
        print("         ИЛИ укажите путь через --mediainfo-lib")

    print("=" * 70 + "\n")


def run_interactive_menu() -> Dict[str, Any]:
    """
    Запускает интерактивное меню для ввода параметров.

    Returns:
        Dict: Словарь с выбранными параметрами запуска
    """
    # Сначала показываем диагностику MediaInfo
    diagnose_mediainfo_status()

    print("\n" + " " * 15 + "📁 КАТАЛОГИЗАТОР ФОТО И ВИДЕО (v4.2)")
    print("=" * 70)

    # Сбор параметров с подсказками и значениями по умолчанию
    print(f"\n📁 Путь к папке-источнику [ {DEFAULT_SOURCE_PATH} ]:")
    source = input("   Введите путь (или Enter):  ").strip() or DEFAULT_SOURCE_PATH

    print(f"\n📂 Путь к папке-назначению [ {DEFAULT_DEST_PATH} ]:")
    dest = input("   Введите путь (или Enter):  ").strip() or DEFAULT_DEST_PATH

    print(f"\n⚙️  Количество потоков обработки [ {DEFAULT_WORKERS} ]:")
    workers_input = input("   Введите число (или Enter):  ").strip()
    workers = int(workers_input) if workers_input.isdigit() else DEFAULT_WORKERS

    print(f"\n📦 Размер пачки файлов [ {DEFAULT_BATCH_SIZE} ]:")
    batch_input = input("   Введите число (или Enter):  ").strip()
    batch_size = int(batch_input) if batch_input.isdigit() else DEFAULT_BATCH_SIZE

    # ВАЖНО: По умолчанию метаданные видео АНАЛИЗИРУЮТСЯ (fast_video=False)
    print(f"\n🎬 Анализ метаданных видео [ДА - по умолчанию]:")
    print("   (Если НЕТ — будет использоваться только дата файла)")
    fast_video_input = input("   ДА/НЕТ: ").strip().lower()
    # Инвертируем логику: "нет" означает fast_mode=True
    fast_video = fast_video_input in ['нет', 'no', 'n', 'false']

    print(f"\n📦 Распаковка ZIP-архивов [ДА - по умолчанию]:")
    extract_input = input("   ДА/НЕТ: ").strip().lower()
    extract_zips = extract_input not in ['нет', 'no', 'n', 'false']

    print(f"\n🧪 Тестовый режим (без записи на диск) [НЕТ]:")
    dry_run_input = input("   ДА/НЕТ: ").strip().lower()
    dry_run = dry_run_input in ['да', 'yes', 'y', 'true']

    # Итоговое подтверждение
    print("\n" + "=" * 70)
    print("   📋 СВОДКА ПАРАМЕТРОВ:")
    print(f"      • Источник:      {source}")
    print(f"      • Назначение:    {dest}")
    print(f"      • Потоки:        {workers}")
    print(f"      • Размер пачки:  {batch_size}")
    print(f"      • ZIP-архивы:    {'✅' if extract_zips else '❌'}")
    print(f"      • Метаданные видео: {'✅ Полный анализ' if not fast_video else '⚡ Быстрый режим'}")
    print(f"      • Тестовый режим: {'🧪 ВКЛЮЧЁН' if dry_run else '❌ Выключен'}")
    print("=" * 70)

    # Финальное подтверждение запуска
    confirm = input("\n   ▶️  Запустить обработку? (Enter/ДА): ").strip().lower()
    if confirm not in ['да', 'yes', 'y', '']:
        print("   ⏹️  Запуск отменён пользователем.")
        sys.exit(0)

    return {
        'source': source,
        'destination': dest,
        'workers': workers,
        'batch_size': batch_size,
        'fast_video': fast_video,
        'extract_zips': extract_zips,
        'dry_run': dry_run
    }


# =============================================================================
# ОСНОВНАЯ ФУНКЦИЯ ЗАПУСКА
# =============================================================================

def main() -> None:
    """
    Точка входа в приложение.

    Обрабатывает аргументы командной строки, инициализирует окружение
    и запускает процесс каталогизации.
    """
    # Поддержка multiprocessing в Windows
    multiprocessing.freeze_support()

    # Настройка парсера аргументов
    parser = argparse.ArgumentParser(
        description="📁 Каталогизатор медиафайлов v4.2",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Примеры использования:
  %(prog)s "C:\\Фото" "D:\\Архив"                          # Базовый запуск
  %(prog)s -i                                               # Интерактивный режим
  %(prog)s source dest -w 8 -b 100 --fast-video            # Быстрый режим
  %(prog)s source dest --dry-run                           # Тест без записи
  %(prog)s --check-mediainfo                               # Диагностика MediaInfo
        """
    )

    # Позиционные аргументы
    parser.add_argument(
        'source',
        nargs='?',
        help='Папка-источник с медиафайлами'
    )
    parser.add_argument(
        'destination',
        nargs='?',
        help='Папка-назначение для структурирования'
    )

    # Опции многопоточности
    parser.add_argument(
        '-w', '--workers',
        type=int,
        default=DEFAULT_WORKERS,
        help=f'Количество потоков (по умолчанию: {DEFAULT_WORKERS})'
    )
    parser.add_argument(
        '-b', '--batch-size',
        type=int,
        default=DEFAULT_BATCH_SIZE,
        help=f'Размер пачки файлов (по умолчанию: {DEFAULT_BATCH_SIZE})'
    )

    # Опции поведения
    parser.add_argument(
        '--fast-video',
        action='store_true',
        help='Пропускать анализ метаданных видео (использовать дату файла)'
    )
    parser.add_argument(
        '--no-fast-video',
        action='store_true',
        help='Явно включить анализ метаданных видео (по умолчанию и так включён)'
    )
    parser.add_argument(
        '--dry-run',
        action='store_true',
        help='Тестовый режим: сканирование без записи файлов'
    )
    parser.add_argument(
        '--no-extract-zips',
        action='store_true',
        help='Не распаковывать ZIP-архивы'
    )

    # Режимы и утилиты
    parser.add_argument(
        '-i', '--interactive',
        action='store_true',
        help='Запустить интерактивное меню'
    )
    parser.add_argument(
        '--check-mediainfo',
        action='store_true',
        help='Только проверить статус MediaInfo и выйти'
    )
    parser.add_argument(
        '--mediainfo-lib',
        type=str,
        help='Путь к MediaInfo.dll (если не в PATH)'
    )

    # Парсинг аргументов
    args = parser.parse_args()

    # === Режим диагностики MediaInfo ===
    if args.check_mediainfo:
        diagnose_mediainfo_status()
        sys.exit(0)

    # === Установка пути к MediaInfo DLL (если указан) ===
    if args.mediainfo_lib and os.path.exists(args.mediainfo_lib):
        try:
            from pymediainfo import MediaInfo
            MediaInfo.set_library_path(args.mediainfo_lib)
            # Обновляем глобальный флаг
            global MEDIAINFO_AVAILABLE
            MEDIAINFO_AVAILABLE = True
            print(f"✅ Указан путь к MediaInfo: {args.mediainfo_lib}")
        except Exception as e:
            print(f"⚠️  Не удалось установить путь к MediaInfo: {e}")

    # === Определение параметров запуска ===
    if args.interactive or not args.source or not args.destination:
        # Интерактивный режим или недостающие аргументы
        config = run_interactive_menu()
        source = config['source']
        dest = config['destination']
        workers = config['workers']
        batch_size = config['batch_size']
        fast_video = config['fast_video']
        extract_zips = config['extract_zips']
        dry_run = config['dry_run']
    else:
        # Режим командной строки
        source = args.source
        dest = args.destination
        workers = args.workers
        batch_size = args.batch_size

        # Логика обработки флагов видео:
        # --no-fast-video имеет приоритет, по умолчанию fast_video=False
        if args.no_fast_video:
            fast_video = False
        elif args.fast_video:
            fast_video = True
        else:
            fast_video = DEFAULT_FAST_VIDEO  # = False (анализ включён)

        extract_zips = not args.no_extract_zips
        dry_run = args.dry_run

    # Нормализация путей
    source = os.path.abspath(source)
    dest = os.path.abspath(dest)

    # Валидация источника
    if not os.path.isdir(source):
        print(f"❌ Ошибка: Директория-источник не найдена: {source}")
        sys.exit(1)

    # Создание директории назначения
    os.makedirs(dest, exist_ok=True)

    # === Подготовка: распаковка архивов ===
    temp_directory = None
    scan_path_list = [source]

    if extract_zips:
        print("🔍 Поиск и распаковка ZIP-архивов...")
        temp_directory = tempfile.mkdtemp(prefix="MediaCatalog_")

        try:
            archive_count = extract_zip_archives(source, temp_directory)
            if archive_count > 0:
                print(f"   ✅ Распаковано архивов: {archive_count}")
                scan_path_list.append(temp_directory)
            else:
                # Нет архивов — убираем временную директорию
                shutil.rmtree(temp_directory)
                temp_directory = None
        except Exception as e:
            print(f"   ⚠️  Ошибка работы с архивами: {e}")
            if temp_directory and os.path.exists(temp_directory):
                shutil.rmtree(temp_directory)
            temp_directory = None

    # === Сканирование файлов ===
    print(f"\n🔍 Сканирование: {source} ...")
    media_files, ext_statistics, total_size, skipped_size = scan_directory_for_media(scan_path_list)
    total_count = len(media_files)

    # Обработка случая "ничего не найдено"
    if total_count == 0:
        print("\n⚠️  Поддерживаемые медиафайлы не найдены.")
        print(f"   Поддерживаемые форматы: {', '.join(sorted(SUPPORTED_EXTENSIONS))}")
        sys.exit(0)

    # === Вывод статистики сканирования ===
    print("\n" + "=" * 70)
    print(" " * 22 + "📊 СТАТИСТИКА ИСТОЧНИКА")
    print("=" * 70)
    print(f"   📁 Всего файлов:           {sum(ext_statistics.values())}")
    print(f"   📸 Медиафайлов найдено:    {total_count}")
    print(f"   💾 Общий объём:            {format_file_size(total_size)}")

    # Топ-5 расширений
    sorted_extensions = sorted(ext_statistics.items(), key=lambda x: x[1], reverse=True)
    supported_stats = {ext: cnt for ext, cnt in ext_statistics.items() if ext in SUPPORTED_EXTENSIONS}

    if supported_stats:
        print(f"\n   ✅ Поддерживаемые форматы (Топ-5):")
        for ext, count in list(sorted(supported_stats.items(), key=lambda x: x[1], reverse=True))[:5]:
            print(f"      {ext:10} → {count:6} файлов")

    print("=" * 70)

    # === Информация о режиме запуска ===
    print(f"\n⚙️  Конфигурация обработки:")
    print(f"   • Потоки:           {workers}")
    print(f"   • Размер пачки:     {batch_size}")

    if fast_video:
        print(f"   • Видео-режим:      ⚡ Быстрый (дата файла)")
    else:
        if MEDIAINFO_AVAILABLE:
            print(f"   • Видео-режим:      🎬 Полный анализ метаданных")
        else:
            print(f"   • Видео-режим:      ⚠️  MediaInfo недоступен → дата файла")

    if extract_zips:
        print(f"   • ZIP-архивы:       ✅ Распаковывать")
    if dry_run:
        print(f"   • Режим:            🧪 DRY-RUN (без записи)")

    print()

    # === Подготовка пачек для параллельной обработки ===
    file_batches = [
        (media_files[i:i + batch_size], dest, fast_video, dry_run)
        for i in range(0, len(media_files), batch_size)
    ]

    # === Инициализация счётчиков результатов ===
    total_stats = {
        'success': 0,
        'overwritten': 0,
        'errors': 0,
        'error_messages': []
    }

    # Прогресс-бар (если доступен tqdm)
    progress_bar = tqdm(total=total_count, unit="файл", desc="Обработка") if USE_TQDM else None

    # === Запуск параллельной обработки ===
    try:
        with ProcessPoolExecutor(max_workers=workers) as executor:
            # Отправляем задачи и собираем результаты по мере завершения
            future_to_batch = {
                executor.submit(process_file_batch, batch): batch
                for batch in file_batches
            }

            for future in as_completed(future_to_batch):
                batch_result = future.result()

                # Агрегация статистики
                total_stats['success'] += batch_result['success']
                total_stats['overwritten'] += batch_result['overwritten']
                total_stats['errors'] += batch_result['errors']
                total_stats['error_messages'].extend(batch_result['error_messages'])

                # Обновление прогресс-бара
                if progress_bar:
                    progress_bar.update(
                        batch_result['success'] +
                        batch_result['overwritten'] +
                        batch_result['errors']
                    )

    except KeyboardInterrupt:
        print("\n\n⚠️  Обработка прервана пользователем (Ctrl+C)")
    finally:
        # Закрытие прогресс-бара
        if progress_bar:
            progress_bar.close()

        # Очистка временных файлов
        if temp_directory and os.path.exists(temp_directory):
            print("\n🧹 Очистка временных файлов...")
            try:
                shutil.rmtree(temp_directory)
            except Exception as cleanup_err:
                print(f"   ⚠️  Не удалось удалить временную папку: {cleanup_err}")

    # === Итоговый отчёт ===
    print("\n" + "=" * 70)
    print(" " * 25 + "✅ ОБРАБОТКА ЗАВЕРШЕНА")
    print("=" * 70)
    print(f"   📥 Скопировано новых:      {total_stats['success']}")
    print(f"   🔄 Обновлено существующих: {total_stats['overwritten']}")
    print(f"   ❌ Ошибок обработки:       {total_stats['errors']}")
    print("=" * 70)

    # Детали ошибок (если есть)
    if total_stats['error_messages']:
        print(f"\n⚠️  Подробности ошибок (первые 10 из {len(total_stats['error_messages'])}):")
        for error_msg in total_stats['error_messages'][:10]:
            print(f"   • {error_msg}")
        if len(total_stats['error_messages']) > 10:
            print(f"   ... и ещё {len(total_stats['error_messages']) - 10} ошибок")

    print()


# =============================================================================
# ТОЧКА ВХОДА
# =============================================================================

if __name__ == "__main__":
    main()





