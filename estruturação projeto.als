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

// a classificação indicativa é um valor numérico comparável à idade do espectador


// devem existir espectadores

// cada espectador tem uma idade

// a idade do espectador é um valor numérico comparável à classificação indicativa do filme

// um espectador não pode ter mais de um ingresso para a mesma sessão


// devem existir sessões

// cada sessão tem uma sala

// cada sessão tem um filme

// cada sessão só pode exibir UM filme por vez

// cada sessão tem um horário de início

// o complexo de uma sessão é derivado via: sessão -> sala -> complexo


// devem existir ingressos

// cada ingresso está associado a um espectador e a uma sessão

// cada ingresso tem um atributo que indica se é cortesia ou não


// REGRAS DE NEGÓCIO

// o formato do filme deve ser IGUAL ao formato da sala da sessão

// o número de ingressos de uma sessão não pode ultrapassar a capacidade da sala

// o espectador não pode comprar ingresso para sessão com classificação indicativa superior à sua idade

// entre duas sessões CONSECUTIVAS na mesma sala deve existir um intervalo mínimo fixo

// o intervalo mínimo é: duração da sessão (120 min) + intervalo de limpeza (30 min) = 150 min



// FIDELIDADE

// a contagem de filmes assistidos pelo espectador é derivada dos seus ingressos

// a condição de fidelidade considera apenas ingressos dos últimos 30 dias

// a condição de fidelidade exige 5 filmes DISTINTOS no mesmo complexo

// espectador só pode ter ingresso cortesia se satisfizer a condição de fidelidade

// ingresso cortesia é resgatado quando espectador assiste 5 filmes DISTINTOS no mesmo complexo nos últimos 30 dias