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
-- cada sessao tem um horario de inicio (pode ser passado ou futuro)
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
    idade: one Int
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

-- ============================================================
-- RELOGIO: ponto de referencia temporal do sistema
-- Representa o "agora".
-- Os ultimos 30 dias sao o intervalo [agora.minus[30], agora].
-- Usamos 7 Int (range -64 a 63) para dar espaco suficiente
-- sem overflow, permitindo agora >= 30 com folga.
-- ============================================================
one sig Relogio {
    agora: one Int
}

-- ============================================================
-- FUNCAO AUXILIAR: sessoes recentes de um espectador
-- Retorna as sessoes associadas a ingressos NORMAIS do espectador
-- cujo inicio esteja dentro dos ultimos 30 dias.
-- Ingressos cortesia NAO contam para fidelidade (confirmado).
-- ============================================================
fun sessoesRecentes[e: Espectador] : set Sessao {
    { s: Sessao | some i: IngressoNormal |
        i.espectador = e
        and i.sessao = s
        and s.inicio >= Relogio.agora.minus[30]
        and s.inicio <= Relogio.agora
    }
}

-- ============================================================
-- FATOS ESTRUTURAIS
-- ============================================================

-- a relacao complexo<->salas e bidirecional e consistente
fact SalaPertenceAUmComplexo {
    all s: Sala | s in s.complexo.salas
    all c: Complexo, s: Sala | s in c.salas implies s.complexo = c
}

-- a capacidade de toda sala deve ser positiva
fact CapacidadePositiva {
    all s: Sala | s.capacidade > 0
}

-- a classificacao indicativa de todo filme deve ser nao-negativa
fact ClassificacaoNaoNegativa {
    all f: Filme | f.classificacao >= 0
}

-- a idade de todo espectador deve ser positiva
fact IdadePositiva {
    all e: Espectador | e.idade > 0
}

-- o horario de inicio de toda sessao deve ser nao-negativo
-- sessoes podem ser passadas ou futuras (o sistema gerencia agendamento)
fact InicioNaoNegativo {
    all s: Sessao | s.inicio >= 0
}

-- o "agora" do relogio deve ser >= 30 para que a janela
-- de fidelidade seja sempre calculavel sem valores negativos
fact RelogioValido {
    Relogio.agora >= 30
}

-- todo ingresso pertence a um espectador e sessao reais
fact IngressoSempreAssociado {
    all i: Ingresso |
        i.espectador in Espectador and i.sessao in Sessao
}

-- um espectador nao pode ter mais de um ingresso para a mesma sessao
fact UmIngressoPorSessaoPorEspectador {
    all e: Espectador, s: Sessao |
        lone i: Ingresso | i.espectador = e and i.sessao = s
}

-- todo espectador tem ao menos um ingresso (cadastrado na primeira compra)
fact EspectadorTemPeloMenosUmIngresso {
    all e: Espectador | some i: Ingresso | i.espectador = e
}

-- ============================================================
-- REGRAS DE NEGOCIO
-- ============================================================

-- REGRA 1: o formato do filme deve ser igual ao formato da sala da sessao
fact FormatoCompativelComSala {
    all s: Sessao | s.filme.formatoFilme = s.sala.formato
}

-- REGRA 2: o numero de ingressos de uma sessao nao pode ultrapassar a capacidade da sala
fact CapacidadeDaSalaRespeitada {
    all s: Sessao |
        #{ i: Ingresso | i.sessao = s } <= s.sala.capacidade
}

-- REGRA 3: o espectador nao pode comprar ingresso para sessao com
--          classificacao indicativa superior a sua idade
fact ClassificacaoRespeitada {
    all i: Ingresso |
        i.sessao.filme.classificacao <= i.espectador.idade
}

-- REGRA 4: duas sessoes distintas na mesma sala nao podem se sobrepor e
--          deve existir intervalo minimo de 5 unidades entre elas.
--          No modelo abstrato usamos 5 unidades (representando 150 min:
--          120 min de duracao + 30 min de limpeza).
--          A semantica e: |inicio_s1 - inicio_s2| >= 5
fact IntervaloEntreSessoesDaMesmaSala {
    all s1, s2: Sessao |
        (s1 != s2 and s1.sala = s2.sala) implies
            (s1.inicio >= s2.inicio.plus[5] or s2.inicio >= s1.inicio.plus[5])
}

-- ============================================================
-- PROGRAMA DE FIDELIDADE
-- ============================================================

-- REGRA DE FIDELIDADE:
-- um espectador so pode ter ingresso cortesia se tiver assistido a
-- pelo menos 5 filmes DISTINTOS no mesmo complexo nos ultimos 30 dias.
-- Apenas IngressoNormal conta para fidelidade.
fact CondicaoFidelidade {
    all i: IngressoCortesia |
        let c = i.sessao.sala.complexo |
        let filmesNoComplexo = {
            f: Filme | some s: sessoesRecentes[i.espectador] |
                s.sala.complexo = c and s.filme = f
        } |
        #filmesNoComplexo >= 5
}

-- um espectador nao pode ter mais de um ingresso cortesia por complexo
fact NoMaximoUmIngressoCortesiaPorComplexo {
    all e: Espectador, c: Complexo |
        lone i: IngressoCortesia |
            i.espectador = e and i.sessao.sala.complexo = c
}

-- ============================================================
-- PREDICADOS E EXECUCAO
-- ============================================================

-- instancia minima valida do sistema (sem cortesia)
pred show {}
run show for 5 but
    1  Complexo,
    2  Sala,
    3  Filme,
    4  Sessao,
    3  Espectador,
    6  Ingresso,
    7  Int

-- instancia que demonstra o programa de fidelidade com ingresso cortesia:
-- requer ao menos 5 filmes distintos assistidos pelo mesmo espectador
-- no mesmo complexo dentro dos ultimos 30 dias
pred showComFidelidade {
    some IngressoCortesia
}
run showComFidelidade for 8 but
    1  Complexo,
    3  Sala,
    6  Filme,
    8  Sessao,
    2  Espectador,
    10 Ingresso,
    7  Int

-- ============================================================
-- ASSERTIONS (verificacoes de corretude)
-- ============================================================

-- nunca dois ingressos do mesmo espectador apontam para a mesma sessao
assert SemDuplicataDeIngresso {
    no disj i1, i2: Ingresso |
        i1.espectador = i2.espectador and i1.sessao = i2.sessao
}
check SemDuplicataDeIngresso for 5 but 7 Int

-- a capacidade da sala nunca e excedida
assert CapacidadeNuncaExcedida {
    all s: Sessao |
        #{ i: Ingresso | i.sessao = s } <= s.sala.capacidade
}
check CapacidadeNuncaExcedida for 5 but 7 Int

-- o formato do filme sempre bate com o da sala
assert FormatoSempreCompativel {
    all s: Sessao | s.filme.formatoFilme = s.sala.formato
}
check FormatoSempreCompativel for 5 but 7 Int

-- nenhum espectador assiste filme com classificacao superior a sua idade
assert ClassificacaoSempreRespeitada {
    all i: Ingresso |
        i.sessao.filme.classificacao <= i.espectador.idade
}
check ClassificacaoSempreRespeitada for 5 but 7 Int

-- toda cortesia pertence a espectador que satisfaz a condicao de fidelidade
assert CortesiaSoParaFieis {
    all i: IngressoCortesia |
        let c = i.sessao.sala.complexo |
        #{ f: Filme | some s: sessoesRecentes[i.espectador] |
               s.sala.complexo = c and s.filme = f } >= 5
}
check CortesiaSoParaFieis for 7 but 7 Int

-- sessoes na mesma sala sempre respeitam o intervalo minimo
assert IntervaloSempreMantido {
    all s1, s2: Sessao |
        (s1 != s2 and s1.sala = s2.sala) implies
            (s1.inicio >= s2.inicio.plus[5] or s2.inicio >= s1.inicio.plus[5])
}
check IntervaloSempreMantido for 5 but 7 Int
