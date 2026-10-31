/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.LaurentSeries.ContinuousDerivation
public import TauCeti.RingTheory.LaurentSeries.Puiseux.Derivative

/-!
# Continuous derivations of Puiseux series

Let `K` be a field of characteristic zero and `P = puiseuxField K`, with its valuation topology
and the derivative `d/dt` of `TauCeti.puiseuxField.derivation K`. This file shows that every
continuous `K`-derivation `δ` of `P` into a Hausdorff `P`-module with continuous scalar
multiplication is `δ x = (dx/dt) • δ t`.

On level `n`, written in the variable `u = t ^ (1 / n)`, the derivation `δ` restricts to a
continuous derivation of `K⸨u⸩`, to which the classification
`Derivation.apply_eq_laurentSeriesDerivation_smul` of continuous derivations of Laurent series
applies. Comparing `δ` with `d/dt` at `t = u ^ n` then expresses `δ u` through `δ t`.

## Main results

* `Derivation.apply_eq_puiseuxFieldDerivation_smul`: continuous derivations of `P` are multiples
  of `d/dt`.
* `Derivation.continuous_iff_exists_apply_eq_puiseuxFieldDerivation_smul`: a derivation of `P` is
  continuous if and only if it is `x ↦ (dx/dt) • m` for some `m`.
-/

public section

open HahnSeries
open scoped LaurentSeries

namespace TauCeti

namespace puiseuxField

variable {K : Type*} [Field K] [CharZero K]

section Module

variable {M : Type*} [AddCommGroup M] [Module (puiseuxField K) M] [Module K M]
  [IsScalarTower K (puiseuxField K) M] [TopologicalSpace M] [ContinuousSMul (puiseuxField K) M]
  [T2Space M]

omit [CharZero K] in
/-- On level `n`, a continuous derivation `δ` satisfies `δ (f (u)) = (D f) (u) • δ u`, where
`u = t ^ (1 / n)`. -/
private theorem apply_levelEmbedding_eq_smul (δ : Derivation K (puiseuxField K) M)
    (hδ : Continuous δ) (n : ℕ+) (f : K⸨X⸩) :
    δ (levelEmbedding K n f) =
      levelEmbedding K n (LaurentSeries.derivative K f) •
        δ (levelEmbedding K n (HahnSeries.single 1 1)) := by
  -- View `M` as a `K⸨X⸩`-module through the level-`n` embedding, and restrict `δ` to it.
  let : Module K⸨X⸩ M := Module.compHom M (levelEmbedding K n : K⸨X⸩ →+* puiseuxField K)
  have : IsScalarTower K K⸨X⸩ M := ⟨fun c f m ↦ by
    -- The scalar action of `K` on `K⸨X⸩` is multiplication by the image of `K`.
    have h : levelEmbedding K n (c • f) = c • levelEmbedding K n f := by
      rw [← C_mul_eq_smul, ← LaurentSeries.algebraMap_apply, map_mul, AlgHom.commutes,
        Algebra.smul_def]
    exact (congrArg (· • m) h).trans (smul_assoc _ _ _)⟩
  have : ContinuousSMul K⸨X⸩ M :=
    ⟨((continuous_levelEmbedding n).comp continuous_fst).smul continuous_snd⟩
  -- By construction of `Module.compHom`, `g • m` is `levelEmbedding K n g • m`; this closes the
  -- Leibniz rule for `δ'` and identifies the classification of `δ'` with the claim.
  let δ' : Derivation K K⸨X⸩ M :=
    { toLinearMap := δ.toLinearMap ∘ₗ (levelEmbedding K n).toLinearMap
      map_one_eq_zero' := by simp
      leibniz' f g := by simp [Derivation.leibniz]; rfl }
  have h := δ'.apply_eq_laurentSeriesDerivation_smul (hδ.comp (continuous_levelEmbedding n)) f
  rw [laurentSeriesDerivation_apply] at h
  exact h

/-- **Continuous derivations of Puiseux series.** A `K`-derivation `δ` of the Puiseux field into
a Hausdorff module with continuous scalar multiplication that is continuous for the valuation
topology satisfies `δ x = (dx/dt) • δ t`. -/
theorem _root_.Derivation.apply_eq_puiseuxFieldDerivation_smul
    (δ : Derivation K (puiseuxField K) M) (hδ : Continuous δ) (x : puiseuxField K) :
    δ x = derivation K x • δ (single K 1 1) := by
  obtain ⟨n, hn⟩ := exists_mem_range_levelEmbedding x
  obtain ⟨f, rfl⟩ := (AlgHom.mem_range _).mp hn
  -- Both `δ` and `d/dt` follow the chain rule on level `n`; comparing them at `t = u ^ n`
  -- expresses `δ u` through `δ t`.
  have hD := apply_levelEmbedding_eq_smul (derivation K) continuous_derivation n
  have ht := apply_levelEmbedding_eq_smul δ hδ n (HahnSeries.single (n : ℤ) 1)
  have ht' := hD (HahnSeries.single (n : ℤ) 1)
  rw [levelEmbedding_single_self] at ht ht'
  rw [derivation_single_one, smul_eq_mul] at ht'
  rw [apply_levelEmbedding_eq_smul δ hδ n f, hD f, ht, smul_eq_mul, mul_smul, smul_smul _ _ (δ _),
    mul_comm, ← ht', one_smul]

/-- A `K`-derivation of the Puiseux field into a Hausdorff module with continuous scalar
multiplication is continuous if and only if it is `x ↦ (dx/dt) • m` for some `m`. -/
theorem _root_.Derivation.continuous_iff_exists_apply_eq_puiseuxFieldDerivation_smul
    {δ : Derivation K (puiseuxField K) M} :
    Continuous δ ↔ ∃ m : M, ∀ x, δ x = derivation K x • m := by
  refine ⟨fun hδ ↦ ⟨_, δ.apply_eq_puiseuxFieldDerivation_smul hδ⟩, ?_⟩
  rintro ⟨m, hm⟩
  have h : (δ : puiseuxField K → M) = fun x ↦ derivation K x • m := funext hm
  rw [h]
  exact continuous_derivation.smul continuous_const

end Module

end puiseuxField

end TauCeti
