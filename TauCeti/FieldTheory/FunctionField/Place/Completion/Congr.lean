/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Place.Completion.Basic
public import TauCeti.Topology.Algebra.Valued.WithVal
public import Mathlib.RingTheory.Valuation.RamificationGroup

/-!
# Transporting completions along isomorphisms

Let `σ : F ≃ₐ[k] F'` be an isomorphism carrying a place `P` of `F` to a place `Q` of `F'`, in the
sense that `v_Q (σ x) = v_P (x)`. Then `σ` is uniformly continuous for the two valuations and
extends by continuity to an isomorphism of completions `F_P ≃ₐ[k] F'_Q`, `Place.completionCongr`:
the general transport `Valuation.Completion.congr` together with its `k`-linearity. It is the
only continuous extension of `σ`, it preserves the completed valuations, and it is functorial:
the identity extends to the identity, composites to composites, inverses to inverses.

For an automorphism `σ` of `F` fixing `P`, the extension preserves the completed valuation ring,
so it lies in the decomposition group of the completed place. This is how the decomposition group
of a place in a Galois extension acts on the completion.

This API adapts `IsDedekindDomain.HeightOneSpectrum.adicCompletionCongr` and its transport
lemmas from `TauCeti/RingTheory/DedekindDomain/AdicValuation/Transport.lean` to places of
function fields, using the extracted general transport `Valuation.Completion.congr`.

## Main definitions

* `TauCeti.Place.completionCongr`: the isomorphism of completions `F_P ≃ₐ[k] F'_Q` extending `σ`.

## Main results

* `TauCeti.Place.completionCongr_completionEmbedding`: `completionCongr` extends `σ`.
* `TauCeti.Place.eq_completionCongr_of_continuous`: it is the only continuous ring homomorphism
  extending `σ`.
* `TauCeti.Place.valuation_completionCongr`: it preserves the completed valuations.
* `TauCeti.Place.completionCongr_refl`, `TauCeti.Place.completionCongr_trans` and
  `TauCeti.Place.completionCongr_symm`: functoriality.
* `TauCeti.Place.completionCongr_mem_decompositionSubgroup`: for an automorphism fixing `P`, the
  extension lies in the decomposition group of the completed valuation ring.
-/

public section

open scoped Pointwise

namespace TauCeti.Place

variable {k F F' F'' : Type*} [Field k] [Field F] [Field F'] [Field F''] [Algebra k F]
  [Algebra k F'] [Algebra k F''] {P : Place k F} {Q : Place k F'} {R : Place k F''}

variable (P Q) in
/-- **The isomorphism of completions extending `σ`**: an isomorphism `σ : F ≃ₐ[k] F'` carrying
`v_P` to `v_Q` extends by continuity to `F_P ≃ₐ[k] F'_Q`. This is `Valuation.Completion.congr`
with its `k`-linearity. -/
noncomputable def completionCongr (σ : F ≃ₐ[k] F')
    (hσ : ∀ x, Q.valuation (σ x) = P.valuation x) : P.Completion ≃ₐ[k] Q.Completion :=
  AlgEquiv.ofRingEquiv (f := Valuation.Completion.congr σ.toRingEquiv hσ)
    fun c ↦ by
      rw [← P.completionEmbedding.commutes, ← Q.completionEmbedding.commutes, ← σ.commutes,
        completionEmbedding_apply, completionEmbedding_apply]
      exact Valuation.Completion.congr_coe hσ _

variable {σ : F ≃ₐ[k] F'} (hσ : ∀ x, Q.valuation (σ x) = P.valuation x)

/-- `completionCongr` extends `σ`. -/
@[simp]
theorem completionCongr_completionEmbedding (x : F) :
    completionCongr P Q σ hσ (P.completionEmbedding x) = Q.completionEmbedding (σ x) := by
  rw [completionEmbedding_apply, completionEmbedding_apply]
  exact Valuation.Completion.congr_coe (σ := σ.toRingEquiv) hσ x

/-- `completionCongr` is continuous. -/
theorem continuous_completionCongr : Continuous (completionCongr P Q σ hσ) :=
  Valuation.Completion.continuous_congr hσ

/-- **`completionCongr` is the only continuous extension of `σ`.** -/
theorem eq_completionCongr_of_continuous {f : P.Completion →+* Q.Completion} (hf : Continuous f)
    (hfF : ∀ x : F, f (P.completionEmbedding x) = Q.completionEmbedding (σ x)) :
    f = (completionCongr P Q σ hσ : P.Completion →+* Q.Completion) :=
  Valuation.Completion.eq_congr_of_continuous (σ := σ.toRingEquiv) hσ hf fun x ↦ by
    rw [← completionEmbedding_apply, ← completionEmbedding_apply]
    exact hfF x

/-- `completionCongr` preserves the completed valuations. -/
@[simp]
theorem valuation_completionCongr (x : P.Completion) :
    Valued.v (completionCongr P Q σ hσ x) = Valued.v x :=
  Valuation.Completion.valued_congr P.valuation_surjective hσ x

/-- `completionCongr` maps the completed valuation ring of `P` into that of `Q`, and only it. -/
theorem completionCongr_mem_integers_iff {x : P.Completion} :
    completionCongr P Q σ hσ x ∈ Q.completionPlace.integers ↔ x ∈ P.completionPlace.integers := by
  simp only [mem_integers_iff, completionPlace_valuation, valuation_completionCongr]

variable (P) in
/-- `completionCongr` of the identity is the identity. -/
@[simp]
theorem completionCongr_refl :
    completionCongr P P (AlgEquiv.refl : F ≃ₐ[k] F) (fun _ ↦ by rw [AlgEquiv.coe_refl, id]) =
      AlgEquiv.refl :=
  AlgEquiv.ext fun x ↦ DFunLike.congr_fun Valuation.Completion.congr_refl x

/-- `completionCongr` is compatible with composition. -/
@[simp]
theorem completionCongr_trans {τ : F' ≃ₐ[k] F''} (hτ : ∀ y, R.valuation (τ y) = Q.valuation y) :
    (completionCongr P Q σ hσ).trans (completionCongr Q R τ hτ) =
      completionCongr P R (σ.trans τ) (fun x ↦ by rw [AlgEquiv.trans_apply, hτ, hσ]) :=
  AlgEquiv.ext fun x ↦ DFunLike.congr_fun (Valuation.Completion.congr_trans (σ := σ.toRingEquiv)
    (τ := τ.toRingEquiv) hσ hτ) x

/-- The inverse of `completionCongr` is `completionCongr` of the inverse. -/
@[simp]
theorem completionCongr_symm :
    (completionCongr P Q σ hσ).symm =
      completionCongr Q P σ.symm (fun y ↦ by rw [← hσ, AlgEquiv.apply_symm_apply]) :=
  AlgEquiv.ext fun x ↦
    DFunLike.congr_fun (Valuation.Completion.congr_symm (σ := σ.toRingEquiv) hσ) x

variable (σ : F ≃ₐ[k] F) (hσ : ∀ x, P.valuation (σ x) = P.valuation x)

/-- For an automorphism `σ` fixing `P`, the extension of `σ` to the completion lies in the
decomposition group of the completed valuation ring. -/
theorem completionCongr_mem_decompositionSubgroup :
    completionCongr P P σ hσ ∈ P.completionPlace.integers.decompositionSubgroup k := by
  rw [MulAction.mem_stabilizer_iff]
  ext x
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def, AlgEquiv.aut_inv,
    ← completionCongr_mem_integers_iff hσ, AlgEquiv.apply_symm_apply]

end TauCeti.Place
