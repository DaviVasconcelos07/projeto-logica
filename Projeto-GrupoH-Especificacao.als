-- Um complexo de cinemas deseja desenvolver um sistema para gerenciar as sessoes de filmes.
-- O sistema registra as exibicoes realizadas em cada sala e controla a venda de ingressos.

-- formato de exibicao: toda sala e todo filme tem exatamente um formato (2D, 3D ou IMAX)
abstract sig Formato {}
one sig Formato2D, Formato3D, FormatoIMAX extends Formato {}

-- deve existir pelo menos um complexo
-- o complexo deve ter N salas (N >= 1)
-- o complexo e o contexto do programa de fidelidade
sig Complexo {
    salas: some Sala
}

-- cada sala pertence a um complexo
-- cada sala tem uma capacidade maxima fixa
-- cada sala deve ter UM formato: 2D, 3D ou IMAX
sig Sala {
    complexo:   one Complexo,
    formato:    one Formato,
    capacidade: one Int
}

-- cada filme tem um formato (2D, 3D ou IMAX)
-- cada filme tem uma classificacao indicativa
-- a classificacao indicativa e um valor numerico comparavel a idade do espectador
sig Filme {
    formatoFilme:  one Formato,
    classificacao: one Int
}

-- cada sessao tem uma sala
-- cada sessao tem um filme
-- cada sessao so pode exibir UM filme por vez
-- cada sessao tem um horario de inicio
-- o complexo de uma sessao e derivado via: sessao -> sala -> complexo
sig Sessao {
    sala:   one Sala,
    filme:  one Filme,
    inicio: one Int
}

-- cada espectador tem uma idade
-- a idade do espectador e um valor numerico comparavel a classificacao indicativa do filme
-- um espectador nao pode ter mais de um ingresso para a mesma sessao
-- um espectador e cadastrado no momento da primeira compra (sempre tem ao menos um ingresso)
sig Espectador {
    idade:           one Int,
    sessoesRecentes: set Sessao
}

-- cada ingresso esta associado a um espectador e a uma sessao
-- cada ingresso indica se e cortesia ou nao (normal vs cortesia via extends)
-- um ingresso e sempre normal ou cortesia, nunca generico
abstract sig Ingresso {
    sessao:     one Sessao,
    espectador: one Espectador
}
-- ingresso adquirido normalmente
sig IngressoNormal   extends Ingresso {}
-- ingresso resgatado pelo programa de fidelidade (nao acumulativo)
sig IngressoCortesia extends Ingresso {}
