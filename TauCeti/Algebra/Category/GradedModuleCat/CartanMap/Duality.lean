/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.Category.GradedModuleCat.CartanMap.ExtEuler.Basic
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

The Kronecker pairing is `TauCeti.gradedProjectiveExtEuler_basis`; dual bases use Mathlib's
`Module.Basis.dualBasis`.
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

include he₀ hne hbP in
/-- **Pairing a projective class against a simple class.** The q-Euler pairing of `x` with `[Sᵢ]`
is the diagonal graded dimension `gdim(eᵢ • Sᵢ)` times the conjugate of the `i`th projective
coordinate of `x`. -/
@[simp]
theorem gradedProjectiveExtEuler_simple_eq_mul_invert_repr
    (x : LaurentK0.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜)) (i : I) :
    gradedProjectiveExtEuler 𝒜 x (LaurentK0.of.{uA} _ (S i)) =
      (S i).obj.smulGradedDimension (e i) * invert (bP.repr x i) := by
  classical
  let : Fintype I := Fintype.ofFinite I
  have hpair (j : I) : gradedProjectiveExtEuler 𝒜 (bP j) (LaurentK0.of.{uA} _ (S i)) =
      if j = i then (S i).obj.smulGradedDimension (e i) else 0 := by
    rw [hbP, gradedProjectiveExtEuler_ofIdeal_span_singleton (he j) (he₀ j) (hI j),
      gradedIdempotentCoordinate_of]
    split_ifs with hji
    · rw [hji]
    · exact hne hji
  conv_lhs => rw [← bP.sum_repr x]
  simp only [map_sum, LinearMap.sum_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply, hpair]
  simp [mul_comm]

section NeZero

variable (hself : ∀ i, (S i).obj.smulGradedDimension (e i) ≠ 0)
  (hS : IsExhaustiveGradedSimpleFamily S)

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
include he he₀ hI hne hself hS in
/-- The q-Euler pairing separates module classes when every diagonal graded dimension
`gdim(eᵢ • Sᵢ)` is nonzero: pairing against `[A eᵢ]` reads `gdim(eᵢ • Sᵢ)` times the `i`th
simple-class coordinate. -/
theorem gradedProjectiveExtEuler_flip_injective :
    Function.Injective (gradedProjectiveExtEuler 𝒜).flip := by
  intro x y hxy
  apply (gradedSimpleClassBasisOfNeZero S he he₀ hne hself hS).ext_elem
  intro i
  apply mul_left_cancel₀ (hself i)
  have h := DFunLike.congr_fun hxy (LaurentK0.of.{uA} _
    ⟨GradedModuleCat.ofIdeal 𝒜 (Ideal.span {e i}) (hI i),
      gradedFiniteProjectiveModules_ofIdeal_span_singleton (he i) (hI i)⟩)
  simp only [LinearMap.flip_apply,
    gradedProjectiveExtEuler_ofIdeal_span_singleton (he i) (he₀ i) (hI i)] at h
  rwa [gradedIdempotentCoordinate_eq_mul_gradedSimpleClassBasisOfNeZero_repr S he he₀ hne hself hS,
    gradedIdempotentCoordinate_eq_mul_gradedSimpleClassBasisOfNeZero_repr S he he₀ hne hself hS]
    at h

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
      (gradedProjectiveExtEuler_flip_injective S he he₀ hI hne hself hS)

include he he₀ hI hne hself hS hbP in
/-- **The q-Euler pairing identifies the projective group with the dual of the module group
exactly when every diagonal graded dimension is a unit.** Every linear functional on
`G₀^gr(mod A)` is `χ_q(x, -)` for exactly one projective class `x` if and only if each
`gdim(eᵢ • Sᵢ)` is a unit of `ℤ[q,q⁻¹]`. -/
theorem gradedProjectiveExtEuler_bijective_iff :
    Function.Bijective (gradedProjectiveExtEuler 𝒜) ↔
      ∀ i, IsUnit ((S i).obj.smulGradedDimension (e i)) := by
  classical
  let : Fintype I := Fintype.ofFinite I
  let bS := gradedSimpleClassBasisOfNeZero S he he₀ hne hself hS
  have hpair := gradedProjectiveExtEuler_simple_eq_mul_invert_repr S he he₀ hI hne bP hbP
  constructor
  · -- The `i`th coordinate functional is represented, and pairing its representative with `[Sᵢ]`
    -- exhibits an inverse of `gdim(eᵢ • Sᵢ)`.
    intro h i
    obtain ⟨x, hx⟩ := h.2 (bS.coord i)
    have hxi := DFunLike.congr_fun hx (LaurentK0.of.{uA} _ (S i))
    rw [hpair, ← gradedSimpleClassBasisOfNeZero_apply S he he₀ hne hself hS i,
      Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_eq_same] at hxi
    exact IsUnit.of_mul_eq_one _ hxi
  · intro hu
    refine ⟨gradedProjectiveExtEuler_injective S he he₀ hI hne bP hbP hself, fun f => ?_⟩
    refine ⟨∑ i, invert ((↑(hu i).unit⁻¹ : LaurentPolynomial ℤ) * f (bS i)) • bP i, ?_⟩
    apply bS.ext
    intro j
    rw [gradedSimpleClassBasisOfNeZero_apply, hpair]
    simp only [map_sum, map_smul, Module.Basis.repr_self, Finset.sum_apply',
      Finsupp.smul_single, smul_eq_mul, mul_one, Finsupp.single_apply, Finset.sum_ite_eq',
      Finset.mem_univ, ite_true, involutive_invert (R := ℤ) _,
      ← gradedSimpleClassBasisOfNeZero_apply S he he₀ hne hself hS j]
    rw [← mul_assoc, IsUnit.mul_val_inv, one_mul]

include he he₀ hI hne hself hS hbP in
/-- **The q-Euler pairing identifies the module group with the semilinear dual of the projective
group exactly when every diagonal graded dimension is a unit.** Every `q ↦ q⁻¹` semilinear
functional on `K₀^gr(proj A)` is `χ_q(-, y)` for exactly one module class `y` if and only if each
`gdim(eᵢ • Sᵢ)` is a unit of `ℤ[q,q⁻¹]`. -/
theorem gradedProjectiveExtEuler_flip_bijective_iff :
    Function.Bijective (gradedProjectiveExtEuler 𝒜).flip ↔
      ∀ i, IsUnit ((S i).obj.smulGradedDimension (e i)) := by
  classical
  let : Fintype I := Fintype.ofFinite I
  let bS := gradedSimpleClassBasisOfNeZero S he he₀ hne hself hS
  have hpair := gradedProjectiveExtEuler_simple_eq_mul_invert_repr S he he₀ hI hne bP hbP
  constructor
  · -- The conjugated `i`th projective coordinate is represented by some module class `y`, and
    -- pairing `[A eᵢ]` with `y` exhibits an inverse of `gdim(eᵢ • Sᵢ)`.
    intro h i
    obtain ⟨y, hy⟩ := h.2
      ((invert (R := ℤ)).toRingEquiv.toRingHom.toSemilinearMap.comp (bP.coord i))
    have hyi : gradedProjectiveExtEuler 𝒜 (bP i) y = 1 := by
      rw [← LinearMap.flip_apply, hy, LinearMap.comp_apply, RingHom.coe_toSemilinearMap,
        Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_eq_same, map_one]
    rw [hbP, gradedProjectiveExtEuler_ofIdeal_span_singleton (he i) (he₀ i) (hI i),
      gradedIdempotentCoordinate_eq_mul_gradedSimpleClassBasisOfNeZero_repr S he he₀ hne hself
        hS] at hyi
    exact IsUnit.of_mul_eq_one _ hyi
  · intro hu
    refine ⟨gradedProjectiveExtEuler_flip_injective S he he₀ hI hne hself hS, fun f => ?_⟩
    refine ⟨∑ i, ((↑(hu i).unit⁻¹ : LaurentPolynomial ℤ) * f (bP i)) • bS i, ?_⟩
    apply bP.ext
    intro j
    rw [LinearMap.flip_apply, hbP, gradedProjectiveExtEuler_ofIdeal_span_singleton (he j) (he₀ j)
      (hI j), gradedIdempotentCoordinate_eq_mul_gradedSimpleClassBasisOfNeZero_repr S he he₀ hne
        hself hS, ← hbP]
    simp only [map_sum, map_smul, Module.Basis.repr_self, Finset.sum_apply',
      Finsupp.smul_single, smul_eq_mul, mul_one, Finsupp.single_apply, Finset.sum_ite_eq',
      Finset.mem_univ, ite_true, bS]
    rw [← mul_assoc, IsUnit.mul_val_inv, one_mul]

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

include he he₀ hI hne hself hS hbP in
/-- The q-Euler pairing represents every linear functional on the module Grothendieck group
by exactly one projective class. -/
theorem gradedProjectiveExtEuler_bijective :
    Function.Bijective (gradedProjectiveExtEuler 𝒜) :=
  (gradedProjectiveExtEuler_bijective_iff S he he₀ hI hne bP hbP
    (fun i => (hself i).symm ▸ one_ne_zero) hS).2 fun i => (hself i).symm ▸ isUnit_one

include he he₀ hI hne hself hS hbP in
/-- Every `q ↦ q⁻¹` semilinear functional on the projective Grothendieck group is represented
by exactly one module class in the second argument of the q-Euler pairing. -/
theorem gradedProjectiveExtEuler_flip_bijective :
    Function.Bijective (gradedProjectiveExtEuler 𝒜).flip :=
  (gradedProjectiveExtEuler_flip_bijective_iff S he he₀ hI hne bP hbP
    (fun i => (hself i).symm ▸ one_ne_zero) hS).2 fun i => (hself i).symm ▸ isUnit_one

end One

end TauCeti
