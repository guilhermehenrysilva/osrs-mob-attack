# OSRS Mob attack

Bot de apoio para combate repetitivo por deteccao de cor, com menu interativo para carregar/criar mobs e configurar execucao.

## Requisitos

- Python 3.10+ (recomendado 3.11+)
- Dependencias Python do `requirements.txt`
- Jagex Launcher com `osclient.exe` (Old School RuneScape) em execucao
- OBS: RuneLite Client Not Tested

## Importante: Zoom e Enquadramento

Para melhor funcionamento da deteccao de cor:

- aumente o zoom do jogo (aproxime a camera)
- limite a visao para reduzir ruido visual
- mantenha o alvo em cena com boa nitidez

Isso melhora bastante a consistencia na identificacao dos mobs.

## Instalacao

No diretorio do projeto:

```bash
python -m pip install -r requirements.txt
```

## Como Executar

### Windows (PowerShell)

```powershell
cd C:\Users\Guilherme\Desktop\apoio
python ".\OSRS Mob attack.py"
```

### Linux

```bash
cd /caminho/para/apoio
python3 "OSRS Mob attack.py"
```

## Estrutura de Configuracao

- Configuracao geral: `config/script.conf`
- Mobs por arquivo: `config/mob/<nome-do-mob>.conf`

O nome do novo mob e normalizado para minusculo e separadores viram `-`.

## Fluxo de Uso (Menu)

1. `Carregar Mob`
2. `Inserir novo Mob`
3. `Configuracao`
4. `Sair`

### Inserir novo Mob

- coletar amostras de cor
- limpar amostras do mob atual
- salvar configuracao do mob

### Carregar Mob

- selecionar mob por numero
- iniciar/pausar sessao
- excluir mob

### Configuracao

- Tempo Programado de Execucao
- Pausas Programadas (Humanizacao)

## Atalhos Durante Sessao

- `F7`: iniciar/pausar
- `F8`: encerrar sessao e retornar ao menu

## Observacoes

- Se `osclient.exe` estiver rodando como administrador, execute o Python com privilegios equivalentes.
- O bot depende da janela correta do cliente e da qualidade das amostras de cor.
