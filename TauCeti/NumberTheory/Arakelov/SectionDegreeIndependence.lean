/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Arakelov.SectionDegree
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.RingTheory.DedekindDomain.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import TauCeti.Algebra.Module.Torsion.GenericRankOne
import TauCeti.NumberTheory.NumberField.RingOfIntegers.Norm
import TauCeti.RingTheory.Ideal.Norm.AbsNorm

/-!
# Independence of the section and the lattice index term, for any family of norms

Let `K` be a number field, `E` a finitely generated torsion-free `𝓞 K`-module with
`K ⊗[𝓞 K] E` a line, and `ν_σ` a family of functions on `E`, one for each embedding
`σ : K →+* ℂ`, which scale like norms: `ν_σ(a • x) = |σ(a)| ν_σ(x)`. The expression
`sectionDegreeOfNorms ν s = log #(E / 𝓞 K • s) - Σ_σ log ν_σ(s)` does not depend on the nonzero
section `s` (`TauCeti.sectionDegreeOfNorms_eq_of_finrank_eq_one`): replacing `s` by `a • s`
multiplies the index by `|N(a)|` and each `ν_σ(s)` by `|σ(a)|`, and `∏_σ |σ(a)| = |N(a)|`.

For an injective map `f : E → F` preserving the norms, the expression for `F` computed with
`f s` is the one for `E` computed with `s` plus `log #(F / f E)`
(`TauCeti.sectionDegreeOfNorms_map_eq_add_log_cardQuot_range`).

These are the statements of ArakelovGeometryAndAbelianHeights §1.4 and the lattice index term of
§1.5 for an arbitrary family of norms, so that they apply to every carrier of hermitian line
bundles.

## Main statements

* `TauCeti.sectionDegreeOfNorms_smul`: the expression computed with `a • s` equals the one
  computed with `s`, for `a ≠ 0`.
* `TauCeti.sectionDegreeOfNorms_eq_of_finrank_eq_one`: any two nonzero sections compute the same
  expression.
* `TauCeti.sectionDegreeOfNorms_map_eq_add_log_cardQuot_range`: the lattice index term.

## References

* P. Deligne, *Preuve des conjectures de Tate et de Shafarevitch*, Séminaire Bourbaki 616
  (1983/84), §1.1, p. 25, and §2.1, p. 36.
* L. Szpiro, *Degrés, intersections, hauteurs*, Astérisque 127 (1985), §1.2, Proposition 1.1 and
  Corollaire, pp. 13–14.
-/

public section

open NumberField Module Submodule
open scoped TensorProduct

namespace TauCeti

variable {K : Type*} [Field K] [NumberField K] {E F : Type*} [AddCommGroup E] [Module (𝓞 K) E]
  [AddCommGroup F] [Module (𝓞 K) F]

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
    -- `(LinearMap.range f).toAddSubgroup` is `(f : E →+ F).range` by definition.
    rfl
  simp only [sectionDegreeOfNorms_def, hnorm, hidx, Nat.cast_mul]
  rw [Real.log_mul]
  · ring
  -- Both quotients are finite and nonempty, so both indices are nonzero.
  all_goals
    exact Nat.cast_ne_zero.2
      ((Submodule.cardQuot_apply _).trans_ne (Nat.card_ne_zero.2 ⟨inferInstance, inferInstance⟩))

end TauCeti
