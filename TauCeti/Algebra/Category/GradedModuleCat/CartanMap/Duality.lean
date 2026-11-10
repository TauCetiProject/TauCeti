/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.Category.GradedModuleCat.CartanMap.ExtEuler.Basic
public import TauCeti.Algebra.Category.GradedModuleCat.Ext.Generated
public import Mathlib.LinearAlgebra.Dual.Basis

/-!
# Projective/simple duality for the q-Euler pairing

For a finite-dimensional graded algebra, suppose the classes of the degree-zero idempotent
projectives `Aeᵢ` form a Laurent basis, and the idempotents cut out an exhaustive family of
graded simples `Sᵢ` with `gdim(eᵢ Sⱼ) = 0` for `i ≠ j` and `dᵢ = gdim(eᵢ Sᵢ) ≠ 0`. Then the
projective/module q-Euler pairing has matrix `diagonal d` in these bases:
`χ_q(x, [Sᵢ]) = dᵢ · bar(xᵢ)`, where `xᵢ` is the `i`th projective coordinate of `x`.

Since `ℤ[q,q⁻¹]` is a domain, both radicals of the pairing vanish. The pairing identifies the
projective Grothendieck group semilinearly with the linear dual of the module Grothendieck group,
or the module group linearly with the semilinear dual of the projective group, exactly when every
`dᵢ` is a unit of `ℤ[q,q⁻¹]`. For the head `Sᵢ = A eᵢ / A₊eᵢ` of a primitive idempotent `eᵢ` of a
nonnegatively graded algebra with semisimple degree-zero part, the diagonal entry `dᵢ` is the
constant `dim_k End_A(Sᵢ)`, so perfectness fails over a field that does not split the simple
modules even though nondegeneracy survives
(`TauCeti.gradedProjectiveExtEuler_bijective_iff_finrank_end_eq_one`).

When `dᵢ = 1` for every `i`, the projective basis maps to the usual dual basis of the simple-class
basis, and coordinates in the projective basis are recovered by pairing against simples and
applying `LaurentPolynomial.invert`. No finite-global-dimension hypothesis is needed: only
projectives occur in the first argument. The finite index hypothesis is needed for surjectivity
onto the full dual.

## Main results

* `TauCeti.gradedProjectiveExtEuler_simple_eq_mul_invert_repr`: `χ_q(x, [Sᵢ]) = dᵢ · bar(xᵢ)`.
* `TauCeti.gradedProjectiveExtEuler_nondegenerate`: both radicals vanish when every `dᵢ ≠ 0`.
* `TauCeti.gradedProjectiveExtEuler_bijective_iff` and
  `TauCeti.gradedProjectiveExtEuler_flip_bijective_iff`: either side is identified with the dual
  of the other exactly when every `dᵢ` is a unit.
* `TauCeti.gradedProjectiveExtEuler_basis_eq_dualBasis`: for `dᵢ = 1` the projective basis is the
  dual basis of the simple-class basis.

## References

* Zsuzsanna Dancso and Anthony Licata, "Koszul algebras and flow lattices", Sections 2.2 and
  3.1--3.2, for q-antilinearity and the distinction between left and right duals.
* Peter Webb, *A Course in Finite Group Representation Theory*, Proposition 7.4.1, for the factor
  `dim_k End_A(Sᵢ)` in the pairing of projective covers with simples over a general field.

The diagonal pairing of `[A eᵢ]` with `[Sⱼ]` is `TauCeti.gradedProjectiveExtEuler_basis`; dual
bases use Mathlib's `Module.Basis.dualBasis`.
-/

public section

noncomputable section

namespace TauCeti

open CategoryTheory LaurentPolynomial

universe uk uA uI

variable {k : Type uk} [Field k] {A : Type uA} [Ring A] [Algebra k A] [Module.Finite k A]
  {𝒜 : ℤ → Submodule k A} [GradedAlgebra 𝒜]
  [HasExt.{uA} (GradedModuleCat.{uA} 𝒜)]
  {I : Type uI} [Finite I]
  (S : I → (gradedFiniteModules 𝒜).FullSubcategory) {e : I → A}
  (he : ∀ i, IsIdempotentElem (e i)) (he₀ : ∀ i, e i ∈ 𝒜 0)
  (hI : ∀ i, (Ideal.span {e i} : Ideal A).IsHomogeneous 𝒜)
  (hne : Pairwise fun i j => (S j).obj.smulGradedDimension (e i) = 0)
  (bP : Module.Basis I (LaurentPolynomial ℤ)
    (LaurentK0.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜)))
  (hbP : ∀ i, bP i = LaurentK0.of.{uA} _
    ⟨GradedModuleCat.ofIdeal 𝒜 (Ideal.span {e i}) (hI i),
      gradedFiniteProjectiveModules_ofIdeal_span_singleton (he i) (hI i)⟩)

omit [Finite I] in
include he₀ hne hbP in
/-- **Pairing a projective class against a simple class.** The q-Euler pairing of `x` with `[Sᵢ]`
is the diagonal graded dimension `gdim(eᵢ • Sᵢ)` times the conjugate of the `i`th projective
coordinate of `x`. -/
theorem gradedProjectiveExtEuler_simple_eq_mul_invert_repr
    (x : LaurentK0.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜)) (i : I) :
    gradedProjectiveExtEuler 𝒜 x (LaurentK0.of.{uA} _ (S i)) =
      (S i).obj.smulGradedDimension (e i) * invert (bP.repr x i) := by
  classical
  conv_lhs => rw [← bP.linearCombination_repr x]
  simp only [Finsupp.linearCombination_apply, Finsupp.sum, map_sum, LinearMap.sum_apply,
    LinearMap.map_smulₛₗ, LinearMap.smul_apply, hbP,
    gradedProjectiveExtEuler_basis S he he₀ hI hne]
  simp only [smul_eq_mul, mul_ite, mul_zero, Finset.sum_ite_eq', Finsupp.mem_support_iff]
  split_ifs with h
  · exact mul_comm _ _
  · rw [not_not.mp h, map_zero, mul_zero]

omit [Finite I] in
include he₀ hne hbP in
/-- The projective coordinate of a module generated in degree `d` is a single monomial,
scaled by the idempotent dimension of its degree-zero simple target. -/
theorem smulGradedDimension_mul_repr_of_isGeneratedInDegree
    (P : (gradedFiniteProjectiveModules 𝒜).FullSubcategory) {d : ℤ}
    (hP : P.obj.grading.IsGeneratedInDegree A d)
    (hconc : ∀ i p, p ≠ 0 → (S i).obj.grading.piece p = ⊥) (i : I) :
    (S i).obj.smulGradedDimension (e i) * bP.repr (LaurentK0.of.{uA} _ P) i =
      C (Module.finrank k (P.obj ⟶ (S i).obj.shiftObj d) : ℤ) * T d := by
  let _ : Module.Projective A P.obj := (gradedFiniteProjectiveModules_iff.mp P.property).2
  have hpair := gradedProjectiveExtEuler_simple_eq_mul_invert_repr
    S he he₀ hI hne bP hbP (LaurentK0.of.{uA} _ P) i
  rw [gradedProjectiveExtEuler_of_of,
    GradedModuleCat.gradedExtEuler_eq_C_mul_T_of_isGeneratedInDegree
      P.obj (S i).obj hP (hconc i)] at hpair
  have hinv := congrArg (LaurentPolynomial.invert (R := ℤ)) hpair
  have hfixed : invert ((S i).obj.smulGradedDimension (e i)) =
      (S i).obj.smulGradedDimension (e i) := by
    rw [GradedModuleCat.smulGradedDimension_eq_C_of_concentrated _ _ (hconc i), invert_C]
  simpa only [map_mul, invert_C, invert_T, neg_neg, hfixed,
    involutive_invert (R := ℤ) (bP.repr (LaurentK0.of.{uA} _ P) i)] using hinv.symm

section NeZero

variable (hself : ∀ i, (S i).obj.smulGradedDimension (e i) ≠ 0)
  (hS : IsExhaustiveGradedSimpleFamily S)

omit [Finite I] in
include he₀ hI hne hself hbP in
/-- The q-Euler pairing separates projective classes when every diagonal graded dimension
`gdim(eᵢ • Sᵢ)` is nonzero. -/
theorem gradedProjectiveExtEuler_injective :
    Function.Injective (gradedProjectiveExtEuler 𝒜) := by
  intro x y hxy
  apply bP.ext_elem
  intro i
  apply (invert (R := ℤ)).injective
  apply mul_left_cancel₀ (hself i)
  simpa only [gradedProjectiveExtEuler_simple_eq_mul_invert_repr S he he₀ hI hne bP hbP]
    using DFunLike.congr_fun hxy (LaurentK0.of.{uA} _ (S i))

omit [Finite I] in
include he he₀ hne hself hS in
/-- The q-Euler pairing separates module classes when every diagonal graded dimension
`gdim(eᵢ • Sᵢ)` is nonzero: pairing against `[A eᵢ]` reads `gdim(eᵢ • Sᵢ)` times the `i`th
simple-class coordinate. -/
theorem gradedProjectiveExtEuler_flip_injective :
    Function.Injective (gradedProjectiveExtEuler 𝒜).flip := by
  have hI (i : I) : (Ideal.span {e i} : Ideal A).IsHomogeneous 𝒜 :=
    Ideal.isHomogeneous_span_singleton 𝒜 ⟨0, he₀ i⟩
  intro x y hxy
  apply (gradedSimpleClassBasisOfNeZero S he he₀ hne hself hS).ext_elem
  intro i
  apply mul_left_cancel₀ (hself i)
  rw [← gradedProjectiveExtEuler_ofIdeal_span_singleton_eq_mul_repr S he he₀ hI hne hself hS,
    ← gradedProjectiveExtEuler_ofIdeal_span_singleton_eq_mul_repr S he he₀ hI hne hself hS]
  exact DFunLike.congr_fun hxy _

omit [Finite I] in
include he he₀ hI hne hself hS hbP in
/-- **Both radicals of the projective/module q-Euler pairing vanish** when every diagonal graded
dimension `gdim(eᵢ • Sᵢ)` is nonzero. This does not identify either side with the dual of the
other; see `TauCeti.gradedProjectiveExtEuler_bijective_iff`. -/
theorem gradedProjectiveExtEuler_nondegenerate :
    (gradedProjectiveExtEuler 𝒜).Nondegenerate := by
  constructor
  · rw [LinearMap.separatingLeft_iff_ker_eq_bot]
    exact LinearMap.ker_eq_bot_of_injective
      (gradedProjectiveExtEuler_injective S he he₀ hI hne bP hbP hself)
  · rw [LinearMap.separatingRight_iff_flip_ker_eq_bot]
    exact LinearMap.ker_eq_bot_of_injective
      (gradedProjectiveExtEuler_flip_injective S he he₀ hne hself hS)

include he he₀ hI hne hS hbP in
/-- **The q-Euler pairing identifies the projective group with the dual of the module group
exactly when every diagonal graded dimension is a unit.** Every linear functional on
`G₀^gr(mod A)` is `χ_q(x, -)` for exactly one projective class `x` if and only if each
`gdim(eᵢ • Sᵢ)` is a unit of `ℤ[q,q⁻¹]`. -/
theorem gradedProjectiveExtEuler_bijective_iff :
    Function.Bijective (gradedProjectiveExtEuler 𝒜) ↔
      ∀ i, IsUnit ((S i).obj.smulGradedDimension (e i)) := by
  classical
  let : Fintype I := Fintype.ofFinite I
  have hpair := gradedProjectiveExtEuler_simple_eq_mul_invert_repr S he he₀ hI hne bP hbP
  have key (hself : ∀ i, (S i).obj.smulGradedDimension (e i) ≠ 0) :
      Function.Bijective (gradedProjectiveExtEuler 𝒜) ↔
        ∀ i, IsUnit ((S i).obj.smulGradedDimension (e i)) := by
    let bS := gradedSimpleClassBasisOfNeZero S he he₀ hne hself hS
    have hbS (i : I) : bS i = LaurentK0.of.{uA} _ (S i) :=
      gradedSimpleClassBasisOfNeZero_apply S he he₀ hne hself hS i
    constructor
    · -- The `i`th coordinate functional is represented, and pairing its representative with
      -- `[Sᵢ]` exhibits an inverse of `gdim(eᵢ • Sᵢ)`.
      intro h i
      obtain ⟨x, hx⟩ := h.2 (bS.coord i)
      have hxi := DFunLike.congr_fun hx (bS i)
      rw [Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_eq_same, hbS,
        hpair] at hxi
      exact IsUnit.of_mul_eq_one _ hxi
    · intro hu
      refine ⟨gradedProjectiveExtEuler_injective S he he₀ hI hne bP hbP hself, fun f => ?_⟩
      refine ⟨∑ i, invert ((↑(hu i).unit⁻¹ : LaurentPolynomial ℤ) * f (bS i)) • bP i, ?_⟩
      refine bS.ext fun j => ?_
      conv_lhs => rw [hbS j, hpair, bP.repr_sum_self, involutive_invert (R := ℤ) _]
      exact (hu j).unit.mul_inv_cancel_left _
  constructor
  · intro h
    -- A vanishing diagonal graded dimension makes `χ_q([A eᵢ], -)` vanish on the spanning
    -- simple classes, contradicting injectivity.
    refine (key fun i hi ↦ ?_).mp h
    have hzero : gradedProjectiveExtEuler 𝒜 (bP i) = gradedProjectiveExtEuler 𝒜 0 := by
      refine LinearMap.ext_on (span_range_laurentK0_of_eq_top S hS) ?_
      rintro _ ⟨j, rfl⟩
      rw [map_zero, LinearMap.zero_apply, hpair, Module.Basis.repr_self, Finsupp.single_apply]
      split_ifs with hij
      · subst hij
        rw [hi, zero_mul]
      · rw [map_zero, mul_zero]
    exact bP.ne_zero i (h.1 hzero)
  · intro hu
    exact (key fun i ↦ (hu i).ne_zero).mpr hu

include he he₀ hI hne hS hbP in
/-- **The q-Euler pairing identifies the module group with the semilinear dual of the projective
group exactly when every diagonal graded dimension is a unit.** Every `q ↦ q⁻¹` semilinear
functional on `K₀^gr(proj A)` is `χ_q(-, y)` for exactly one module class `y` if and only if each
`gdim(eᵢ • Sᵢ)` is a unit of `ℤ[q,q⁻¹]`. -/
theorem gradedProjectiveExtEuler_flip_bijective_iff :
    Function.Bijective (gradedProjectiveExtEuler 𝒜).flip ↔
      ∀ i, IsUnit ((S i).obj.smulGradedDimension (e i)) := by
  classical
  let : Fintype I := Fintype.ofFinite I
  constructor
  · -- The conjugated `i`th projective coordinate is represented by some module class `y`. Writing
    -- `y` in the spanning simple classes, pairing `[A eᵢ]` with `y` exhibits an inverse of
    -- `gdim(eᵢ • Sᵢ)`.
    intro h i
    obtain ⟨y, hy⟩ := h.2
      ((invert (R := ℤ)).toRingEquiv.toRingHom.toSemilinearMap.comp (bP.coord i))
    have hyi : gradedProjectiveExtEuler 𝒜 (bP i) y = 1 := by
      rw [← LinearMap.flip_apply, hy, LinearMap.comp_apply, RingHom.coe_toSemilinearMap,
        Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_eq_same, map_one]
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun (LaurentPolynomial ℤ)).mp
      (span_range_laurentK0_of_eq_top S hS ▸ Submodule.mem_top (x := y))
    simp only [map_sum, map_smul, gradedProjectiveExtEuler_simple_eq_mul_invert_repr S he he₀ hI hne
      bP hbP, Module.Basis.repr_self, Finsupp.single_apply, apply_ite (invert (R := ℤ)), map_zero,
      mul_ite, mul_zero, smul_eq_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true, map_one,
      mul_one] at hyi
    exact IsUnit.of_mul_eq_one (c i) (by rw [mul_comm]; exact hyi)
  · intro hu
    have hself : ∀ i, (S i).obj.smulGradedDimension (e i) ≠ 0 := fun i ↦ (hu i).ne_zero
    let bS := gradedSimpleClassBasisOfNeZero S he he₀ hne hself hS
    have hpair (i : I) (y : LaurentK0.{uA} (gradedFiniteModulesExactStructure 𝒜)) :
        gradedProjectiveExtEuler 𝒜 (bP i) y =
          (S i).obj.smulGradedDimension (e i) * bS.repr y i := by
      rw [hbP, gradedProjectiveExtEuler_ofIdeal_span_singleton_eq_mul_repr S he he₀ hI hne hself
        hS]
    refine ⟨gradedProjectiveExtEuler_flip_injective S he he₀ hne hself hS, fun f => ?_⟩
    refine ⟨∑ i, ((↑(hu i).unit⁻¹ : LaurentPolynomial ℤ) * f (bP i)) • bS i, ?_⟩
    refine bP.ext fun j => ?_
    conv_lhs => rw [LinearMap.flip_apply, hpair, bS.repr_sum_self]
    exact (hu j).unit.mul_inv_cancel_left _

end NeZero

/-! ### Kronecker diagonal -/

section One

variable (hself : ∀ i, (S i).obj.smulGradedDimension (e i) = 1)
  (hS : IsExhaustiveGradedSimpleFamily S)

include he₀ hI hne hself hS hbP in
/-- The projective basis vectors are the linear dual basis of the graded simple classes
under the q-Euler pairing. -/
theorem gradedProjectiveExtEuler_basis_eq_dualBasis (i : I) :
    gradedProjectiveExtEuler 𝒜 (bP i) =
      (open scoped Classical in
        (gradedSimpleClassBasis S he he₀ hne hself hS).dualBasis i) := by
  classical
  apply LinearMap.ext
  intro y
  rw [hbP, gradedProjectiveExtEuler_ofIdeal_span_singleton_eq_repr S he he₀ hI hne hself hS,
    Module.Basis.dualBasis_apply]

end One

end TauCeti
