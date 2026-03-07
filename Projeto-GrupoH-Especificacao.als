abstract sig Formato {}
one sig Formato2D, Formato3D, FormatoIMAX extends Formato {}

abstract sig ClassificacaoIndicativa {}
one sig Livre, C10, C12, C14, C16, C18 extends ClassificacaoIndicativa {}

sig Complexo {
    salas: some Sala
}

sig Sala {
    complexo:   one Complexo,
    formato:    one Formato,
    capacidade: one Int
}

sig Filme {
    formatoFilme:  one Formato,
    classificacao: one ClassificacaoIndicativa
}

sig Sessao {
    sala:  one Sala,
    filme: one Filme
}

sig Espectador {
    idade:           one Int,
    sessoesRecentes: set Sessao
}

abstract sig Ingresso {
    sessao:     one Sessao,
    espectador: one Espectador
}
sig IngressoNormal   extends Ingresso {}
sig IngressoCortesia extends Ingresso {}
