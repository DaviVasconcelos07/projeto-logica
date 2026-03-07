// Um complexo de cinemas deseja desenvolver um sistema para gerenciar as sessões de filmes.
// O sistema registra as exibições realizadas em cada sala e controla a venda de ingressos.
// Cada sala pertence a um complexo físico e possui um único formato de exibição: 2D, 3D ou IMAX.
// Uma sessão só pode exibir um filme cujo formato seja compatível com o formato da sala em que será exibido.
// Cada sessão possui duração fixa de duas horas.
// Entre duas sessões consecutivas na mesma sala deve existir um intervalo de trinta minutos
// destinado à limpeza e preparação do ambiente.
// Cada sessão está associada a um filme e a uma sala.
// O número de ingressos vendidos para uma sessão nunca pode ultrapassar a capacidade máxima da sala vinculada.
// Um espectador não pode adquirir ingresso para sessão cuja classificação indicativa do filme
// seja superior à sua idade.
// O sistema também mantém um programa de fidelidade, no qual um espectador pode resgatar
// um ingresso cortesia se tiver assistido a pelo menos cinco filmes no mesmo complexo nos últimos trinta dias.


// ENTIDADES DO SISTEMA( ou objetos)

// deve existir pelo menos um complexo

// o complexo deve ter N salas

// o complexo é o contexto do programa de fidelidade


// devem existir salas

// cada sala pertence a um complexo

// cada sala tem uma capacidade máxima

// cada sala deve ter UM formato: 2D, 3D ou IMAX


// devem existir filmes

// cada filme tem um formato (2D, 3D ou IMAX)

// cada filme tem uma classificação indicativa


// devem existir espectadores

// cada espectador tem uma idade


// devem existir sessões

// cada sessão tem uma sala

// cada sessão tem um filme

// cada sessão só pode exibir UM filme por vez

// cada sessão tem um horário de início


// devem existir ingressos

// cada ingresso está associado a um espectador e a uma sessão



// REGRAS DE NEGÓCIO

// o formato do filme deve ser compatível com o formato da sala da sessão

// o número de ingressos de uma sessão não pode ultrapassar a capacidade da sala

// o espectador não pode comprar ingresso para sessão com classificação indicativa superior à sua idade

// entre duas sessões CONSECUTIVAS na mesma sala deve existir um intervalo mínimo fixo



// FIDELIDADE

// a contagem de filmes assistidos pelo espectador é derivada dos seus ingressos

// ingresso cortesia é resgatado quando espectador assiste 5 filmes no mesmo complexo nos últimos 30 dias