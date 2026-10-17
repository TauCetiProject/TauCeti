/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.Combinatorics.DenseGraphLimits.ExchangeableGraphLaw.Relational.Basic
import TauCeti.MeasureTheory.Measure.RelationalConfiguration
import Mathlib.Logic.Equiv.Fintype

/-!
# Regression examples: exchangeable relational laws

These examples exercise the correspondence between exchangeable relational laws and invariant laws
on `ℕ`, and its agreement with the graph-specific correspondence, from a downstream module through
public statements only:

* the level-`0` marginal is recovered: nullary relation symbols have atoms on the empty carrier, so
  that marginal need not be deterministic;
* an invariant law is recovered along every injection `Fin n → ℕ`, not only along the initial
  windows;
* both round trips of the correspondence;
* a law on `ℕ` is determined by its windows without any countability assumption on the language;
* for the language of graphs, the windows of the encoded extension of an exchangeable graph law
  are its encoded marginals;
* decoding a relational law carried by simple graphs and re-encoding it recovers each marginal;
* decoding an invariant law carried by simple graphs and taking a window agrees with decoding the
  corresponding finite law.
-/

open MeasureTheory TauCeti TauCeti.RelationalConfiguration TauCeti.Probability
  TauCeti.DenseGraphLimits

open _root_.FirstOrder (Language)

/-! ### Levels and injections -/

-- The level-`0` marginal is recovered. Only nullary symbols contribute atoms on the empty carrier,
-- and their joint law there need not be deterministic.
example {L : Language} [∀ n, Countable (L.Relations n)] (μ : ExchangeableRelationalLaw L) :
    (exchangeableRelationalLawEquivInfinite L μ).law.map (restrict (Fin.val : Fin 0 → ℕ)) =
      μ.law 0 := by
  simp

-- An invariant law is recovered along every injection, not only along the initial windows.
example {L : Language} (μ : InfiniteExchangeableRelationalLaw L) {n : ℕ} (g : Fin n → ℕ)
    (hg : Function.Injective g) :
    μ.law.map (restrict g) = μ.law.map (restrict (Fin.val : Fin n → ℕ)) := by
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair (fun i : Fin n => (i : ℕ)) g
    Fin.val_injective hg
  have hg' : g = ⇑σ ∘ (Fin.val : Fin n → ℕ) := funext fun i => (hσ i).symm
  have hcomp : restrict (L := L) g = restrict (Fin.val : Fin n → ℕ) ∘ restrict ⇑σ := by
    funext c
    rw [hg', Function.comp_apply, restrict_comp]
  rw [hcomp, ← Measure.map_map (measurable_restrict _) (measurable_restrict _), μ.exchangeable]

/-! ### Round trips and uniqueness -/

example {L : Language} [∀ n, Countable (L.Relations n)] (μ : ExchangeableRelationalLaw L) :
    (exchangeableRelationalLawEquivInfinite L).symm (exchangeableRelationalLawEquivInfinite L μ) =
      μ :=
  Equiv.symm_apply_apply _ μ

example {L : Language} [∀ n, Countable (L.Relations n)] (μ : InfiniteExchangeableRelationalLaw L) :
    exchangeableRelationalLawEquivInfinite L ((exchangeableRelationalLawEquivInfinite L).symm μ) =
      μ :=
  Equiv.apply_symm_apply _ μ

-- A finite measure on the configurations on `ℕ` is determined by its windows, with no countability
-- assumption on the language.
example {L : Language} {μ ν : Measure (RelationalConfiguration L ℕ)} [IsProbabilityMeasure μ]
    (h : ∀ n, μ.map (restrict (Fin.val : Fin n → ℕ)) = ν.map (restrict (Fin.val : Fin n → ℕ))) :
    μ = ν :=
  measure_ext_of_map_restrict_val h

/-! ### Graphs -/

-- The windows of the encoded extension of an exchangeable graph law are its encoded marginals.
example (L : ExchangeableGraphLaw) (n : ℕ) :
    (exchangeableGraphLawEquivInfinite L).toRelationalLaw.law.map
        (restrict (Fin.val : Fin n → ℕ)) =
      (L.law n).map SimpleGraph.toRelationalConfiguration := by
  rw [← ExchangeableGraphLaw.exchangeableRelationalLawEquivInfinite_toRelationalLaw,
    exchangeableRelationalLawEquivInfinite_law_map_restrict,
    ExchangeableGraphLaw.toRelationalLaw_law]

/-! ### Decoding relational laws carried by simple graphs -/

-- Decoding a relational law carried by simple graphs and re-encoding it recovers each marginal.
example
    (μ : {μ : ExchangeableRelationalLaw Language.graph //
      ∀ n, ∀ᵐ c ∂μ.law n, IsSimpleGraph c})
    (n : ℕ) :
    ((ExchangeableGraphLaw.relationalLawEquiv.symm μ).law n).map
        SimpleGraph.toRelationalConfiguration =
      μ.1.law n := by
  rw [ExchangeableGraphLaw.relationalLawEquiv_symm_law,
    SimpleGraph.measurableEmbedding_toRelationalConfiguration.map_comap,
    SimpleGraph.range_toRelationalConfiguration]
  exact Measure.restrict_eq_self_of_ae_mem (μ.2 n)

-- Decoding an invariant law carried by simple graphs and taking a window agrees with decoding the
-- corresponding finite law.
example
    (μ : {μ : InfiniteExchangeableRelationalLaw Language.graph //
      ∀ᵐ c ∂μ.law, IsSimpleGraph c})
    (n : ℕ) :
    (InfiniteExchangeableGraphLaw.relationalLawEquiv.symm μ).law.map (·.restrictFin n) =
      (ExchangeableGraphLaw.relationalLawEquiv.symm
        ⟨(exchangeableRelationalLawEquivInfinite Language.graph).symm μ.1,
          (ae_isSimpleGraph_exchangeableRelationalLawEquivInfinite_law_iff _).1 (by
            rw [Equiv.apply_symm_apply]; exact μ.2)⟩).law n := by
  set F := ExchangeableGraphLaw.relationalLawEquiv.symm
    ⟨(exchangeableRelationalLawEquivInfinite Language.graph).symm μ.1,
      (ae_isSimpleGraph_exchangeableRelationalLawEquivInfinite_law_iff _).1 (by
        rw [Equiv.apply_symm_apply]; exact μ.2)⟩ with hF
  -- The decoded infinite law is the graph extension of the decoded finite law.
  have hext : exchangeableGraphLawEquivInfinite F =
      InfiniteExchangeableGraphLaw.relationalLawEquiv.symm μ := by
    apply InfiniteExchangeableGraphLaw.toRelationalLaw_injective
    rw [← ExchangeableGraphLaw.exchangeableRelationalLawEquivInfinite_toRelationalLaw,
      ← ExchangeableGraphLaw.coe_relationalLawEquiv, hF, Equiv.apply_symm_apply,
      Equiv.apply_symm_apply, ← InfiniteExchangeableGraphLaw.coe_relationalLawEquiv,
      Equiv.apply_symm_apply]
  rw [← hext, exchangeableGraphLawEquivInfinite_law_map_restrictFin]
