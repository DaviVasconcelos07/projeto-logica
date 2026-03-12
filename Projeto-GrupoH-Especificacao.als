-- Um complexo de cinemas deseja desenvolver um sistema para gerenciar as sessoes de filmes.
-- O sistema registra as exibicoes realizadas em cada sala e controla a venda de ingressos.

-- BOOLEANO: representacao de verdadeiro/falso para cortesia
abstract sig Bool {}
one sig True, False extends Bool {}

-- FORMATO: toda sala e todo filme tem exatamente um formato
abstract sig Formato {}
one sig Formato2D, Formato3D, FormatoIMAX extends Formato {}

-- COMPLEXO
-- deve existir pelo menos um complexo
-- o complexo deve ter N salas (N >= 1)
-- o complexo e o contexto do programa de fidelidade
sig Complexo {
    salas: some Sala
}

-- SALA
-- cada sala pertence a um complexo
-- cada sala tem uma capacidade maxima fixa
-- cada sala deve ter UM formato: 2D, 3D ou IMAX
sig Sala {
    complexo:   one Complexo,
    formato:    one Formato,
    capacidade: one Int
}

-- FILME
-- cada filme tem um formato (2D, 3D ou IMAX)
-- cada filme tem uma classificacao indicativa comparavel a idade
sig Filme {
    formato:      one Formato,
    classif:      one Int
}

-- SESSAO
-- cada sessao tem uma sala e um filme
-- cada sessao so pode exibir UM filme por vez
-- cada sessao tem um horario de inicio (passado ou futuro)
-- o complexo e derivado via: sessao -> sala -> complexo
sig Sessao {
    sala:   one Sala,
    filme:  one Filme,
    inicio: one Int
}

-- ESPECTADOR
-- cada espectador tem uma idade comparavel a classificacao do filme
-- um espectador e cadastrado na primeira compra (tem ao menos um ingresso)
sig Espectador {
    idade: one Int
}

-- INGRESSO
-- cada ingresso esta associado a uma sessao e a um espectador
-- cortesia: Bool indica se e ingresso de fidelidade (True) ou normal (False)
sig Ingresso {
    sessao:     one Sessao,
    espectador: one Espectador,
    cortesia:   one Bool
}

-- RELOGIO: ponto de referencia temporal do sistema
-- Representa o "agora".
-- ESCALA DE TEMPO: 1 unidade = 1 dia
--   - Janela de fidelidade: 30 unidades (30 dias) -- semanticamente exato
--   - Intervalo minimo entre sessoes: 5 unidades -- aproximacao formal
--     (no dominio real: 150 min = 2h30; no modelo: unidade minima adotada = 1 dia)
--     NOTA: a escala de dias e necessaria para representar a janela de 30 dias
--     sem overflow. O intervalo de 5 unidades preserva a ORDEM e a RESTRICAO
--     de separacao entre sessoes, mesmo que a granularidade seja diferente.
-- Usamos 7 Int (range -64 a 63): agora >= 30 garante janela
-- de fidelidade calculavel sem valores negativos.
one sig Relogio {
    agora: one Int
}

-- FUNCAO AUXILIAR: sessoes recentes de um espectador
-- Retorna sessoes de ingressos NAO-cortesia (cortesia = False)
-- cujo inicio esteja dentro dos ultimos 30 dias (janela de fidelidade).
-- Ingressos cortesia NAO contam para fidelidade.
fun sessoesRecentes[e: Espectador] : set Sessao {
    { s: Sessao | some i: Ingresso |
        i.espectador = e
        and i.sessao = s
        and i.cortesia = False
        and s.inicio >= Relogio.agora.minus[30]
        and s.inicio <= Relogio.agora
    }
}

-- FATOS ESTRUTURAIS

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
    all f: Filme | f.classif >= 0
}

-- a idade de todo espectador deve ser positiva
fact IdadePositiva {
    all e: Espectador | e.idade > 0
}

-- o horario de inicio de toda sessao deve ser nao-negativo
fact InicioNaoNegativo {
    all s: Sessao | s.inicio >= 0
}

-- limite superior dos horarios de inicio para evitar overflow nas operacoes
-- de soma (plus[5]) usadas no intervalo entre sessoes.
-- Com 7 Int (max = 63): garantimos inicio <= 58 para que inicio.plus[5] <= 63
-- e nao ocorra overflow.
fact InicioSemOverflow {
    all s: Sessao | s.inicio <= 58
}

-- o "agora" deve ser >= 30 para que a janela de fidelidade
-- [agora - 30, agora] seja sempre calculavel sem valores negativos
fact RelogioValido {
    Relogio.agora >= 30
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

-- REGRAS DE NEGOCIO

-- REGRA 1: o formato do filme deve ser igual ao formato da sala da sessao
fact FormatoCompativelComSala {
    all s: Sessao | s.filme.formato = s.sala.formato
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
        i.sessao.filme.classif <= i.espectador.idade
}

-- REGRA 4: duas sessoes distintas na mesma sala devem ter intervalo
--          minimo de 5 unidades entre seus horarios de inicio.
--          NOTA: no dominio real o intervalo e de 150 min (120 de duracao
--          + 30 de limpeza). No modelo, 1 unidade = 1 dia; o valor 5
--          preserva a restricao de separacao, sendo uma aproximacao formal
--          necessaria para compatibilizar as escalas de tempo do modelo.
--          Semantica: |inicio_s1 - inicio_s2| >= 5
fact IntervaloEntreSessoesDaMesmaSala {
    all s1, s2: Sessao |
        (s1 != s2 and s1.sala = s2.sala) implies
            (s1.inicio >= s2.inicio.plus[5] or s2.inicio >= s1.inicio.plus[5])
}

-- PROGRAMA DE FIDELIDADE

-- REGRA DE FIDELIDADE:
-- um espectador so pode ter ingresso cortesia (cortesia = True) se tiver
-- assistido a pelo menos 5 filmes (sessoes, nao necessariamente distintas)
-- no mesmo complexo nos ultimos 30 dias via ingressos normais
-- (cortesia = False). Um mesmo filme em sessoes diferentes conta multiplas vezes.
fact CondicaoFidelidade {
    all i: Ingresso |
        i.cortesia = True implies
            let c = i.sessao.sala.complexo |
            let sessoesNoComplexo = {
                s: sessoesRecentes[i.espectador] | s.sala.complexo = c
            } |
            #sessoesNoComplexo >= 5
}

-- um espectador nao pode ter mais de um ingresso cortesia por complexo
fact NoMaximoUmIngressoCortesiaPorComplexo {
    all e: Espectador, c: Complexo |
        lone i: Ingresso |
            i.espectador = e
            and i.sessao.sala.complexo = c
            and i.cortesia = True
}

-- PREDICADOS E EXECUCAO

-- CENARIO EXEMPLO (escopo 5, conforme exigido pelo enunciado)
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
-- requer ao menos 5 sessoes assistidas pelo mesmo espectador
-- no mesmo complexo dentro dos ultimos 30 dias
pred showComFidelidade {
    some i: Ingresso | i.cortesia = True
}
run showComFidelidade for 8 but
    1  Complexo,
    3  Sala,
    6  Filme,
    8  Sessao,
    2  Espectador,
    10 Ingresso,
    7  Int

-- ASSERTIONS (verificacoes de corretude)

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
    all s: Sessao | s.filme.formato = s.sala.formato
}
check FormatoSempreCompativel for 5 but 7 Int

-- nenhum espectador assiste filme com classificacao superior a sua idade
assert ClassificacaoSempreRespeitada {
    all i: Ingresso |
        i.sessao.filme.classif <= i.espectador.idade
}
check ClassificacaoSempreRespeitada for 3 but 7 Int

-- toda cortesia pertence a espectador que satisfaz a condicao de fidelidade
assert CortesiaSoParaFieis {
    all i: Ingresso |
        i.cortesia = True implies
            let c = i.sessao.sala.complexo |
            #{ s: sessoesRecentes[i.espectador] | s.sala.complexo = c } >= 5
}
check CortesiaSoParaFieis for 7 but 7 Int

-- sessoes na mesma sala sempre respeitam o intervalo minimo de 5 unidades
assert IntervaloSempreMantido {
    all s1, s2: Sessao |
        (s1 != s2 and s1.sala = s2.sala) implies
            (s1.inicio >= s2.inicio.plus[5] or s2.inicio >= s1.inicio.plus[5])
}
check IntervaloSempreMantido for 5 but 7 Int

-- todo complexo tem pelo menos uma sala
assert ComplexoTemPeloMenosUmaSala {
    all c: Complexo | some s: Sala | s.complexo = c
}
check ComplexoTemPeloMenosUmaSala for 5 but 7 Int