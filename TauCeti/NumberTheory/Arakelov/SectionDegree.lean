/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.RingTheory.Flat.TorsionFree
import TauCeti.Algebra.Module.Torsion.GenericRankOne
import TauCeti.NumberTheory.NumberField.RingOfIntegers.Norm
import TauCeti.RingTheory.Ideal.Norm.AbsNorm

/-!
# The degree computed with a section, for a family of norms

For an `𝓞 K`-module `E`, a family `ν σ : E → ℝ` of norms indexed by the complex embeddings
`σ : K →+* ℂ` and a section `s : E`, the expression `log #(E / 𝓞 K • s) - Σ_σ log ν_σ(s)` is the
Arakelov degree of a hermitian line computed with a nonzero section. Each model of hermitian
bundles specializes it to its own norms.

If `E` is finitely generated and torsion-free with `K ⊗[𝓞 K] E` a line, and the norms scale like
norms, `ν_σ(a • x) = |σ(a)| ν_σ(x)`, the expression does not depend on the nonzero section `s`
(`TauCeti.sectionDegreeOfNorms_eq_of_finrank_eq_one`): replacing `s` by `a • s` multiplies the
index by `|N(a)|` and each `ν_σ(s)` by `|σ(a)|`, and `∏_σ |σ(a)| = |N(a)|`. For an injective map
`f : E → F` preserving the norms, the expression for `F` computed with `f s` is the one for `E`
computed with `s` plus `log #(F / f E)`
(`TauCeti.sectionDegreeOfNorms_map_eq_add_log_cardQuot_range`). Both hold for an arbitrary family
of norms, so that they apply to every carrier of hermitian line bundles.

## Main definitions

* `TauCeti.sectionDegreeOfNorms`: the expression `log #(E / 𝓞 K • s) - Σ_σ log ν_σ(s)`.

## Main statements

* `TauCeti.sectionDegreeOfNorms_exp_neg_mul`: multiplying every norm by `e^{-c}` adds
  `[K : ℚ] c`.
* `TauCeti.sectionDegreeOfNorms_eq_zero`: a generating section of norm `1` everywhere has
  degree `0`.
* `TauCeti.sectionDegreeOfNorms_smul`: the expression computed with `a • s` equals the one
  computed with `s`, for `a ≠ 0`.
* `TauCeti.sectionDegreeOfNorms_eq_of_finrank_eq_one`: any two nonzero sections compute the same
  expression.
* `TauCeti.sectionDegreeOfNorms_map_eq_add_log_cardQuot_range`: the lattice index term.

## References

* P. Deligne, *Preuves des conjectures de Tate et de Shafarevitch*, Séminaire Bourbaki 616
  (1983/84), §1.1, pp. 25–26, and §2.1, p. 36.
* L. Szpiro, *Degrés, intersections, hauteurs*, Astérisque 127 (1985), §1.2, Proposition 1.1 and
  Corollaire, pp. 13–14.
-/

public noncomputable section

open NumberField

namespace TauCeti

variable {K : Type*} [Field K] [NumberField K] {E : Type*} [AddCommGroup E] [Module (𝓞 K) E]

/-- The expression `log #(E / 𝓞 K • s) - Σ_σ log ν_σ(s)` attached to a family of norms `ν` and a
section `s`, the sum running over all field embeddings `σ : K →+* ℂ`. -/
def sectionDegreeOfNorms (ν : (K →+* ℂ) → E → ℝ) (s : E) : ℝ :=
  Real.log (Submodule.span (𝓞 K) {s}).cardQuot - ∑ σ : K →+* ℂ, Real.log (ν σ s)

/-- The degree computed with `s` is `log #(E / 𝓞 K • s) - Σ_σ log ν_σ(s)`. -/
theorem sectionDegreeOfNorms_def (ν : (K →+* ℂ) → E → ℝ) (s : E) :
    sectionDegreeOfNorms ν s =
      Real.log (Submodule.span (𝓞 K) {s}).cardQuot - ∑ σ : K →+* ℂ, Real.log (ν σ s) :=
  (rfl)

/-- Multiplying every norm by `e^{-c}` adds `[K : ℚ] c` to the degree computed with a section
of nonzero norms. -/
theorem sectionDegreeOfNorms_exp_neg_mul (ν : (K →+* ℂ) → E → ℝ) (c : ℝ) {s : E}
    (hs : ∀ σ, ν σ s ≠ 0) :
    sectionDegreeOfNorms (fun σ x => Real.exp (-c) * ν σ x) s =
      sectionDegreeOfNorms ν s + Module.finrank ℚ K * c := by
  have h σ : Real.log (Real.exp (-c) * ν σ s) = -c + Real.log (ν σ s) := by
    rw [Real.log_mul (Real.exp_pos _).ne' (hs σ), Real.log_exp]
  simp only [sectionDegreeOfNorms_def, h, Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_univ, NumberField.Embeddings.card, nsmul_eq_mul]
  ring

/-- A section generating `E` and of norm `1` at every embedding has degree `0`. -/
theorem sectionDegreeOfNorms_eq_zero {ν : (K →+* ℂ) → E → ℝ} {s : E}
    (hs : Submodule.span (𝓞 K) {s} = ⊤) (hν : ∀ σ, ν σ s = 1) : sectionDegreeOfNorms ν s = 0 := by
  simp [sectionDegreeOfNorms_def, hs, hν, Submodule.cardQuot_top]

section Independence

open Module Submodule
open scoped TensorProduct

variable {F : Type*} [AddCommGroup F] [Module (𝓞 K) F]

/-- **Independence of the multiple.** If `K ⊗[𝓞 K] E` is a line and the norms scale by
`ν_σ(a • x) = |σ(a)| ν_σ(x)`, the expression computed with `a • s` equals the one computed with a
section `s` of nonzero norms, for every nonzero integer `a` of `K`: the index of the multiples of
`s` grows by `|N(a)|` and the norms of `s` by `|σ(a)|`, and `∏_σ |σ(a)| = |N(a)|`. -/
theorem sectionDegreeOfNorms_smul [Module.Finite (𝓞 K) E] [Module.IsTorsionFree (𝓞 K) E]
    (hE : finrank K (K ⊗[𝓞 K] E) = 1) {ν : (K →+* ℂ) → E → ℝ}
    (hν : ∀ (σ : K →+* ℂ) (a : 𝓞 K) (x : E), ν σ (a • x) = ‖σ (algebraMap (𝓞 K) K a)‖ * ν σ x)
    {s : E} (hs : s ≠ 0) (hνs : ∀ σ, ν σ s ≠ 0) {a : 𝓞 K} (ha : a ≠ 0) :
    sectionDegreeOfNorms ν (a • s) = sectionDegreeOfNorms ν s := by
  have hq : (span (𝓞 K) {s}).cardQuot ≠ 0 := by
    have := finite_quotient_span_singleton_of_finrank_eq_one hE hs
    rw [cardQuot_apply]
    exact Nat.card_pos.ne'
  have hN : (Ideal.span {a}).cardQuot ≠ 0 := by
    rwa [← Ideal.absNorm_apply, Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
  have hσ (σ : K →+* ℂ) : σ (algebraMap (𝓞 K) K a) ≠ 0 :=
    (map_ne_zero σ).2 ((map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 K) K)).2 ha)
  -- The archimedean change `Σ_σ log |σ(a)|` is the logarithm of the index of `(a)`.
  have hsum : ∑ σ : K →+* ℂ, Real.log ‖σ (algebraMap (𝓞 K) K a)‖ =
      Real.log (Ideal.span {a}).cardQuot := by
    rw [← Real.log_prod fun σ _ => norm_ne_zero_iff.2 (hσ σ), prod_norm_embedding_eq_abs_norm,
      ← Ideal.absNorm_apply, Ideal.absNorm_span_singleton, Nat.cast_natAbs, ← Algebra.coe_norm_int]
    norm_cast
  simp only [sectionDegreeOfNorms_def, cardQuot_span_singleton_smul a hs, Nat.cast_mul,
    Real.log_mul (Nat.cast_ne_zero.2 hN) (Nat.cast_ne_zero.2 hq), hν,
    Real.log_mul (norm_ne_zero_iff.2 (hσ _)) (hνs _), Finset.sum_add_distrib, hsum]
  ring

/-- **Independence of the section.** If `K ⊗[𝓞 K] E` is a line and the norms scale like norms and
do not vanish on nonzero sections, any two nonzero sections compute the same expression
`log #(E / 𝓞 K • s) - Σ_σ log ν_σ(s)`. This is the product formula. -/
theorem sectionDegreeOfNorms_eq_of_finrank_eq_one [Module.Finite (𝓞 K) E]
    [Module.IsTorsionFree (𝓞 K) E] (hE : finrank K (K ⊗[𝓞 K] E) = 1)
    {ν : (K →+* ℂ) → E → ℝ}
    (hν : ∀ (σ : K →+* ℂ) (a : 𝓞 K) (x : E), ν σ (a • x) = ‖σ (algebraMap (𝓞 K) K a)‖ * ν σ x)
    (hν0 : ∀ σ x, x ≠ 0 → ν σ x ≠ 0) {s t : E} (hs : s ≠ 0) (ht : t ≠ 0) :
    sectionDegreeOfNorms ν s = sectionDegreeOfNorms ν t := by
  obtain ⟨a, b, ha, h⟩ := exists_smul_eq_smul_of_finrank_eq_one hE hs t
  have hb : b ≠ 0 := by
    rintro rfl
    exact smul_ne_zero ha ht (h.trans (zero_smul _ s))
  rw [← sectionDegreeOfNorms_smul hE hν hs (hν0 · s hs) hb, ← h,
    sectionDegreeOfNorms_smul hE hν ht (hν0 · t ht) ha]

/-- **Lattice index term.** Let `f : E → F` be an injective `𝓞 K`-linear map preserving the norms.
For a section `s` of `E` generating a sublattice of finite index, and `F / f E` finite, the
expression for `F` computed with `f s` is the one for `E` computed with `s` plus
`log #(F / f E)`. -/
theorem sectionDegreeOfNorms_map_eq_add_log_cardQuot_range {ν : (K →+* ℂ) → E → ℝ}
    {ν' : (K →+* ℂ) → F → ℝ} (f : E →ₗ[𝓞 K] F) (hf : Function.Injective f)
    (hnorm : ∀ σ x, ν' σ (f x) = ν σ x) (s : E)
    [Finite (E ⧸ Submodule.span (𝓞 K) {s})] [Finite (F ⧸ LinearMap.range f)] :
    sectionDegreeOfNorms ν' (f s) =
      sectionDegreeOfNorms ν s + Real.log (LinearMap.range f).cardQuot := by
  have hmap : Submodule.span (𝓞 K) {f s} = (Submodule.span (𝓞 K) {s}).map f := by
    rw [Submodule.map_span, Set.image_singleton]
  have hidx : (Submodule.span (𝓞 K) {f s}).cardQuot =
      (Submodule.span (𝓞 K) {s}).cardQuot * (LinearMap.range f).cardQuot := by
    unfold Submodule.cardQuot
    rw [hmap, Submodule.map_toAddSubgroup, AddSubgroup.index_map_of_injective _ hf]
    -- `(LinearMap.range f).toAddSubgroup` is `(f : E →+ F).range` by definition. The rewrite
    -- `LinearMap.range_toAddSubgroup` states this with `f.toAddMonoidHom` rather than the
    -- coercion that `Submodule.map_toAddSubgroup` produces, so it does not match and `rfl` closes.
    rfl
  simp only [sectionDegreeOfNorms_def, hnorm, hidx, Nat.cast_mul]
  rw [Real.log_mul]
  · ring
  -- Both quotients are finite and nonempty, so both indices are nonzero.
  all_goals
    exact Nat.cast_ne_zero.2
      ((Submodule.cardQuot_apply _).trans_ne (Nat.card_ne_zero.2 ⟨inferInstance, inferInstance⟩))

end Independence

end TauCeti
