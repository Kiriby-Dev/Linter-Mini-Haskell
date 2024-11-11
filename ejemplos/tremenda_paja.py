import subprocess
import os
import difflib

# Definir el directorio base y la cantidad de casos
BASE_DIR = os.path.join('ejemplos/casos')
SALIDAS_DIR = os.path.join(BASE_DIR, 'salidas')
NUM_CASOS = 24

def leer_archivo(ruta):
    """Leer el contenido de un archivo y devolverlo como string (forzando utf-8)."""
    try:
        with open(ruta, 'r', encoding='utf-8') as file:
            return file.read().strip()
    except FileNotFoundError:
        print(f"Error: No se encontró el archivo {ruta}.")
        return None

def ejecutar_comando(comando):
    """Ejecutar un comando en la terminal y devolver la salida (forzando utf-8)."""
    try:
        # Forzar la terminal a usar utf-8 agregando `chcp 65001`
        comando_completo = f'chcp 65001 > nul && {comando}'
        
        # Capturar tanto stdout como stderr, forzando la codificación utf-8
        resultado = subprocess.run(
            comando_completo, capture_output=True, text=True, shell=True, encoding='utf-8', errors='ignore'
        )
        
        # Combinar stdout y stderr
        salida = resultado.stdout + resultado.stderr
        return salida.strip()
    except Exception as e:
        print(f"Error ejecutando el comando {comando}: {e}")
        return None

def comparar_archivos(caso_num):
    """Comparar las salidas de Linter con los archivos esperados."""
    errores = []

    # Rutas de archivos
    archivo_caso = os.path.join(BASE_DIR, f'caso{caso_num:02}.mhs')
    archivo_sug = os.path.join(SALIDAS_DIR, f'caso{caso_num:02}-sug')
    archivo_lint = os.path.join(SALIDAS_DIR, f'caso{caso_num:02}-lint.mhs')

    # Comparar sugerencias (-s)
    salida_s = ejecutar_comando(f'.\\Linter -s {archivo_caso}')
    esperado_s = leer_archivo(archivo_sug)
    if salida_s != esperado_s:
        errores.append(f"Error en sugerencias para caso {caso_num:02}")

    # Comparar archivo corregido (-c)
    salida_c = ejecutar_comando(f'.\\Linter -c {archivo_caso}')
    esperado_c = leer_archivo(archivo_lint)
    if salida_c != esperado_c:
        errores.append(f"Error en corrección para caso {caso_num:02}")

    return errores

def main():
    errores_totales = []

    # Iterar por todos los casos de prueba
    for i in range(1, NUM_CASOS + 1):
        errores = comparar_archivos(i)
        if errores:
            errores_totales.extend(errores)

    # Reportar resultados
    if errores_totales:
        print("\n".join(errores_totales))
    else:
        print("Todos los casos pasaron correctamente.")

if __name__ == '__main__':
    main()
