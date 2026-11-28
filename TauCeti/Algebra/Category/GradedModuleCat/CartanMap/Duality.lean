/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.GradedModuleCat.CartanMap.ExtEuler.Basic
public import Mathlib.LinearAlgebra.Dual.Basis

/-!
# Projective/simple duality for the q-Euler pairing

For a finite-dimensional graded algebra `A`, suppose the classes of the degree-zero idempotent
projectives `A eᵢ` form a Laurent basis `bP` of `K₀^gr(proj A)`. For any finite graded module `M`
with `gdim(eⱼ • M) = 0` for every `j ≠ i`, the projective/module q-Euler pairing satisfies
`χ_q(x, [M]) = gdim(eᵢ • M) · bar(xᵢ)`
(`TauCeti.gradedProjectiveExtEuler_of_right_eq_mul_invert_repr`). In particular, if the
idempotents cut out an exhaustive family of graded simples `Sᵢ` with `gdim(eᵢ • Sⱼ) = 0` for
`i ≠ j` and `dᵢ = gdim(eᵢ • Sᵢ) ≠ 0`, then the pairing has matrix `diagonal d` in these bases.

Since `ℤ[q,q⁻¹]` is a domain, both radicals of the pairing vanish. The pairing identifies the
projective Grothendieck group semilinearly with the linear dual of the module Grothendieck group,
or the module group linearly with the semilinear dual of the projective group, exactly when every
`dᵢ` is a unit of `ℤ[q,q⁻¹]`. No separate finiteness assumption on the index set `I` is needed for
these bijectivity criteria: finite-dimensionality of `A` together with nonvanishing diagonal
entries forces `I` to be finite. For the head `Sᵢ = A eᵢ / A₊eᵢ` of a primitive idempotent `eᵢ`
of a nonnegatively graded algebra with semisimple degree-zero part, the diagonal entry `dᵢ` is
the constant `dim_k End_A(Sᵢ)`, so perfectness fails over a field that does not split the simple
modules even though nondegeneracy survives
(`TauCeti.gradedProjectiveExtEuler_bijective_iff_finrank_end_eq_one`).

When `dᵢ = 1` for every `i`, coordinates in the projective basis are recovered individually by
pairing against `[Sᵢ]` and applying `LaurentPolynomial.invert` (without requiring `Finite I`);
when `I` is moreover equipped with `[Finite I]` and `[DecidableEq I]` to form Mathlib's
`Module.Basis.dualBasis`, the classes `[A eᵢ]` map to the dual basis of the simple-class basis.
No finite-global-dimension hypothesis is needed: only projectives occur in the first argument.

## Main results

* `TauCeti.gradedProjectiveExtEulerTarget_eq_mul_invert_repr`: for a finite-dimensional graded
  module `M` with `gdim(eⱼ • M) = 0` for every `j ≠ i`,
  `gradedProjectiveExtEulerTarget M x = gdim(eᵢ • M) · bar(xᵢ)` (without assuming `A` is
  finite-dimensional or `HasExt`).
* `TauCeti.gradedProjectiveExtEuler_of_right_eq_mul_invert_repr`: for a finite graded module `M`
  with `gdim(eⱼ • M) = 0` for every `j ≠ i`, `χ_q(x, [M]) = gdim(eᵢ • M) · bar(xᵢ)`.
* `TauCeti.gradedProjectiveExtEuler_nondegenerate`: both radicals vanish when every `dᵢ ≠ 0`.
* `TauCeti.gradedProjectiveExtEuler_bijective_iff` and
  `TauCeti.gradedProjectiveExtEuler_flip_bijective_iff`: either side is identified with the full
  dual of the other exactly when every `dᵢ` is a unit (finiteness of `I` is derived from
  finite-dimensionality of `A` and nonvanishing `dᵢ`).
* `TauCeti.gradedProjectiveExtEuler_basis_eq_dualBasis`: for `dᵢ = 1` and finite `I`, the classes
  `[A eᵢ]` map to the dual basis of the simple-class basis.

## References

* Zsuzsanna Dancso and Anthony Licata, "Koszul algebras and flow lattices", Sections 2.2 and
  3.1--3.2, for q-antilinearity and the distinction between left and right duals.
* Peter Webb, *A Course in Finite Group Representation Theory*, Proposition 7.4.1, for the factor
  `dim_k End_A(Sᵢ)` in the pairing of projective covers with simples over a general field.

The diagonal pairing of `[A eᵢ]` with `[Sⱼ]` is `TauCeti.gradedProjectiveExtEuler_basis`; dual
bases use Mathlib's `Module.Basis.dualBasis`. For Ext-free projective coordinates via graded Hom
dimensions over possibly infinite-dimensional algebras, see
`TauCeti.Algebra.Category.GradedModuleCat.CartanMap.HomCoordinate`.
-/

public section

noncomputable section

namespace TauCeti

open CategoryTheory LaurentPolynomial

universe uk uA uI

variable {k : Type uk} [Field k] {A : Type uA} [Ring A] [Algebra k A]
  {𝒜 : ℤ → Submodule k A} [GradedAlgebra 𝒜]

/-- An idempotent whose projective ideal class is a basis vector of `K₀^gr(proj A)` is nonzero. -/
private theorem idempotent_ne_zero_of_basis_eq {I : Type uI} {e : I → A}
    (he : ∀ i, IsIdempotentElem (e i)) (he₀ : ∀ i, e i ∈ 𝒜 0)
    (bP : Module.Basis I (LaurentPolynomial ℤ)
      (LaurentK0.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜)))
    (i : I)
    (hbi : bP i = LaurentK0.of.{uA} _
      (gradedIdempotentProjective (he i) (he₀ i))) :
    e i ≠ 0 := by
  intro h0
  apply bP.ne_zero i
  rw [hbi]
  let P := gradedIdempotentProjective (he i) (he₀ i)
  have hval (x : P.obj) : (x : A) = 0 := by
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp x.property
    rw [← ha, h0, mul_zero]
  have hsub : Subsingleton ((gradedFiniteProjectiveModules 𝒜).ι.obj P).carrier :=
    ⟨fun x y => Subtype.ext ((hval x).trans (hval y).symm)⟩
  have hzero : Limits.IsZero P :=
    Limits.IsZero.of_full_of_faithful_of_isZero (gradedFiniteProjectiveModules 𝒜).ι P
      (GradedModuleCat.isZero_of_subsingleton _)
  rw [← LaurentK0.ofExactK0_exactK0_of.{uA}, ExactK0.of_eq_zero_of_isZero.{uA} hzero, map_zero]

/-- **Pairing a projective class against a single idempotent-isolated target.** Without assuming
`A` is finite-dimensional over `k` or a `HasExt` instance, if `gdim(eⱼ • M) = 0` for every `j ≠ i`,
then `gradedProjectiveExtEulerTarget M x` equals `gdim(eᵢ • M)` times the conjugate of the `i`th
projective coordinate of `x`. -/
theorem gradedProjectiveExtEulerTarget_eq_mul_invert_repr
    {I : Type uI} {e : I → A} (he : ∀ i, IsIdempotentElem (e i)) (he₀ : ∀ i, e i ∈ 𝒜 0)
    (bP : Module.Basis I (LaurentPolynomial ℤ)
      (LaurentK0.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜)))
    (hbP : ∀ i, bP i = LaurentK0.of.{uA} _
      (gradedIdempotentProjective (he i) (he₀ i)))
    (x : LaurentK0.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜))
    (M : GradedModuleCat.{uA} 𝒜) [Module.Finite k M] (i : I)
    (hne : ∀ j, j ≠ i → M.smulGradedDimension (e j) = 0) :
    gradedProjectiveExtEulerTarget M x =
      M.smulGradedDimension (e i) * invert (bP.repr x i) := by
  rw [gradedProjectiveExtEulerTarget_apply,
    gradedHomShiftCoordinate_eq_mul_repr he he₀ bP hbP M i hne, map_mul, involutive_invert]

variable [Module.Finite k A]

/-! ### Evaluation against an idempotent-isolated module -/

/-- **Pairing a projective class against an idempotent-isolated module.** If `gdim(eⱼ • M) = 0` for
every `j ≠ i`, then the q-Euler pairing of `x` with `[M]` is `gdim(eᵢ • M)` times the conjugate of
the `i`th projective coordinate of `x`. -/
theorem gradedProjectiveExtEuler_of_right_eq_mul_invert_repr
    [HasExt.{uA} (GradedModuleCat.{uA} 𝒜)]
    {I : Type uI} {e : I → A} (he : ∀ i, IsIdempotentElem (e i)) (he₀ : ∀ i, e i ∈ 𝒜 0)
    (bP : Module.Basis I (LaurentPolynomial ℤ)
      (LaurentK0.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜)))
    (hbP : ∀ i, bP i = LaurentK0.of.{uA} _
      (gradedIdempotentProjective (he i) (he₀ i)))
    (x : LaurentK0.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜))
    (M : (gradedFiniteModules 𝒜).FullSubcategory) (i : I)
    (hne : ∀ j, j ≠ i → M.obj.smulGradedDimension (e j) = 0) :
    gradedProjectiveExtEuler 𝒜 x (LaurentK0.of.{uA} _ M) =
      M.obj.smulGradedDimension (e i) * invert (bP.repr x i) :=
  (gradedProjectiveExtEuler_of_right x M).trans
    (gradedProjectiveExtEulerTarget_eq_mul_invert_repr he he₀ bP hbP x M.obj i hne)

/-! ### Nondegeneracy and perfectness -/

section Family

variable {I : Type uI}
  (S : I → (gradedFiniteModules 𝒜).FullSubcategory) {e : I → A}
  (he : ∀ i, IsIdempotentElem (e i)) (he₀ : ∀ i, e i ∈ 𝒜 0)
  (hne : Pairwise fun i j => (S j).obj.smulGradedDimension (e i) = 0)

include hne in
/-- Each diagonal idempotent dimension is nonzero when the projective classes form a basis
and the simple family is exhaustive and vanishes off the diagonal. -/
private theorem diagonal_smulGradedDimension_ne_zero
    (bP : Module.Basis I (LaurentPolynomial ℤ)
      (LaurentK0.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜)))
    (hbP : ∀ i, bP i = LaurentK0.of.{uA} _
      (gradedIdempotentProjective (he i) (he₀ i)))
    (hS : IsExhaustiveGradedSimpleFamily S) (i : I) :
    (S i).obj.smulGradedDimension (e i) ≠ 0 :=
  smulGradedDimension_ne_zero_of_span_eq_top S (span_range_laurentK0_of_eq_top S hS) (he i)
    (he₀ i) (idempotent_ne_zero_of_basis_eq he he₀ bP i (hbP i)) i (fun _ hli => hne hli.symm)

variable [HasExt.{uA} (GradedModuleCat.{uA} 𝒜)]

section Nondegenerate

variable (hself : ∀ i, (S i).obj.smulGradedDimension (e i) ≠ 0)

include hne hself in
/-- The q-Euler pairing separates projective classes when every diagonal graded dimension
`gdim(eᵢ • Sᵢ)` is nonzero. -/
theorem gradedProjectiveExtEuler_injective
    (bP : Module.Basis I (LaurentPolynomial ℤ)
      (LaurentK0.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜)))
    (hbP : ∀ i, bP i = LaurentK0.of.{uA} _
      (gradedIdempotentProjective (he i) (he₀ i))) :
    Function.Injective (gradedProjectiveExtEuler 𝒜) := by
  intro x y hxy
  apply bP.ext_elem
  intro i
  apply (invert (R := ℤ)).injective
  apply mul_left_cancel₀ (hself i)
  have hx := gradedProjectiveExtEuler_of_right_eq_mul_invert_repr he he₀ bP hbP x (S i) i
    (fun j hji => hne hji)
  have hy := gradedProjectiveExtEuler_of_right_eq_mul_invert_repr he he₀ bP hbP y (S i) i
    (fun j hji => hne hji)
  rw [← hx, ← hy]
  exact DFunLike.congr_fun hxy (LaurentK0.of.{uA} _ (S i))

include he he₀ hne hself in
/-- The q-Euler pairing separates module classes when every diagonal graded dimension
`gdim(eᵢ • Sᵢ)` is nonzero: pairing against `[A eᵢ]` reads `gdim(eᵢ • Sᵢ)` times the `i`th
simple-class coordinate. -/
theorem gradedProjectiveExtEuler_flip_injective (hS : IsExhaustiveGradedSimpleFamily S) :
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

include hne in
/-- **Both radicals of the projective/module q-Euler pairing vanish** when an exhaustive family of
simples is isolated by idempotents whose projective classes form a basis. For bijectivity, see
`TauCeti.gradedProjectiveExtEuler_bijective_iff`. -/
theorem gradedProjectiveExtEuler_nondegenerate
    (bP : Module.Basis I (LaurentPolynomial ℤ)
      (LaurentK0.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜)))
    (hbP : ∀ i, bP i = LaurentK0.of.{uA} _
      (gradedIdempotentProjective (he i) (he₀ i)))
    (hS : IsExhaustiveGradedSimpleFamily S) :
    (gradedProjectiveExtEuler 𝒜).Nondegenerate := by
  have hself := diagonal_smulGradedDimension_ne_zero S he he₀ hne bP hbP hS
  constructor
  · rw [LinearMap.separatingLeft_iff_ker_eq_bot]
    exact LinearMap.ker_eq_bot_of_injective
      (gradedProjectiveExtEuler_injective S he he₀ hne hself bP hbP)
  · rw [LinearMap.separatingRight_iff_flip_ker_eq_bot]
    exact LinearMap.ker_eq_bot_of_injective
      (gradedProjectiveExtEuler_flip_injective S he he₀ hne hself hS)

end Nondegenerate

section Bijective

variable (bP : Module.Basis I (LaurentPolynomial ℤ)
    (LaurentK0.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜)))
  (hbP : ∀ i, bP i = LaurentK0.of.{uA} _
    (gradedIdempotentProjective (he i) (he₀ i)))
  (hS : IsExhaustiveGradedSimpleFamily S)

include hne hbP hS in
/-- **The q-Euler pairing identifies the projective group with the dual of the module group
exactly when every diagonal graded dimension is a unit.** Every linear functional on
`G₀^gr(mod A)` is `χ_q(x, -)` for exactly one projective class `x` if and only if each
`gdim(eᵢ • Sᵢ)` is a unit of `ℤ[q,q⁻¹]`. -/
theorem gradedProjectiveExtEuler_bijective_iff :
    Function.Bijective (gradedProjectiveExtEuler 𝒜) ↔
      ∀ i, IsUnit ((S i).obj.smulGradedDimension (e i)) := by
  classical
  have hpair (x) (i) :=
    gradedProjectiveExtEuler_of_right_eq_mul_invert_repr he he₀ bP hbP x (S i) i
      (fun j hji => hne hji)
  constructor
  · -- The `i`th coordinate functional is represented, and pairing its representative with
    -- `[Sᵢ]` exhibits an inverse of `gdim(eᵢ • Sᵢ)`.
    intro h i
    have hself := diagonal_smulGradedDimension_ne_zero S he he₀ hne bP hbP hS
    let bS := gradedSimpleClassBasisOfNeZero S he he₀ hne hself hS
    obtain ⟨x, hx⟩ := h.2 (bS.coord i)
    have hxi := DFunLike.congr_fun hx (bS i)
    rw [Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_eq_same,
      gradedSimpleClassBasisOfNeZero_apply, hpair] at hxi
    exact IsUnit.of_mul_eq_one _ hxi
  · intro hu
    have hself : ∀ i, (S i).obj.smulGradedDimension (e i) ≠ 0 := fun i ↦ (hu i).ne_zero
    have : Finite I := finite_of_smulGradedDimension_ne_zero S he he₀ hne hself hS
    let : Fintype I := Fintype.ofFinite I
    let bS := gradedSimpleClassBasisOfNeZero S he he₀ hne hself hS
    refine ⟨gradedProjectiveExtEuler_injective S he he₀ hne hself bP hbP, fun f => ?_⟩
    refine ⟨∑ i, invert ((↑(hu i).unit⁻¹ : LaurentPolynomial ℤ) * f (bS i)) • bP i, ?_⟩
    refine bS.ext fun j => ?_
    conv_lhs =>
      rw [gradedSimpleClassBasisOfNeZero_apply, hpair, bP.repr_sum_self,
        involutive_invert (R := ℤ) _]
    exact (hu j).unit.mul_inv_cancel_left _

include hne hbP hS in
/-- **The q-Euler pairing identifies the module group with the semilinear dual of the projective
group exactly when every diagonal graded dimension is a unit.** Every `q ↦ q⁻¹` semilinear
functional on `K₀^gr(proj A)` is `χ_q(-, y)` for exactly one module class `y` if and only if each
`gdim(eᵢ • Sᵢ)` is a unit of `ℤ[q,q⁻¹]`. -/
theorem gradedProjectiveExtEuler_flip_bijective_iff :
    Function.Bijective (gradedProjectiveExtEuler 𝒜).flip ↔
      ∀ i, IsUnit ((S i).obj.smulGradedDimension (e i)) := by
  classical
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
    obtain ⟨c, rfl⟩ := (Finsupp.mem_span_range_iff_exists_finsupp (R := LaurentPolynomial ℤ)).mp
      (span_range_laurentK0_of_eq_top S hS ▸ Submodule.mem_top (x := y))
    simp only [Finsupp.sum, map_sum, map_smul,
      gradedProjectiveExtEuler_of_right_eq_mul_invert_repr he he₀ bP hbP _ (S _) _
        (fun _ hji => hne hji)] at hyi
    rw [Finset.sum_eq_single i] at hyi
    · exact IsUnit.of_mul_eq_one (c i)
        (by simpa [Module.Basis.repr_self, mul_comm] using hyi)
    · intro j _ hji
      simp [Module.Basis.repr_self, Ne.symm hji]
    · intro hi
      simp [Finsupp.notMem_support_iff.mp hi]
  · intro hu
    have hself : ∀ i, (S i).obj.smulGradedDimension (e i) ≠ 0 := fun i ↦ (hu i).ne_zero
    have : Finite I := finite_of_smulGradedDimension_ne_zero S he he₀ hne hself hS
    let : Fintype I := Fintype.ofFinite I
    let bS := gradedSimpleClassBasisOfNeZero S he he₀ hne hself hS
    have hpair (i : I) (y : LaurentK0.{uA} (gradedFiniteModulesExactStructure 𝒜)) :
        gradedProjectiveExtEuler 𝒜 (bP i) y =
          (S i).obj.smulGradedDimension (e i) * bS.repr y i := by
      have hI (j : I) := Ideal.isHomogeneous_span_singleton 𝒜 ⟨0, he₀ j⟩
      rw [hbP, gradedIdempotentProjective_eq _ _ (hI i),
        gradedProjectiveExtEuler_ofIdeal_span_singleton_eq_mul_repr S he he₀ hI hne hself hS]
    refine ⟨gradedProjectiveExtEuler_flip_injective S he he₀ hne hself hS, fun f => ?_⟩
    refine ⟨∑ i, ((↑(hu i).unit⁻¹ : LaurentPolynomial ℤ) * f (bP i)) • bS i, ?_⟩
    refine bP.ext fun j => ?_
    conv_lhs => rw [LinearMap.flip_apply, hpair, bS.repr_sum_self]
    exact (hu j).unit.mul_inv_cancel_left _

end Bijective

/-! ### Kronecker diagonal -/

/-- Under the q-Euler pairing over a finite index set, the idempotent projective classes `[A eᵢ]`
map to the linear dual basis of the graded simple classes when `gdim(eᵢ • Sᵢ) = 1`. -/
theorem gradedProjectiveExtEuler_basis_eq_dualBasis [Finite I] [DecidableEq I]
    (hself : ∀ i, (S i).obj.smulGradedDimension (e i) = 1)
    (hS : IsExhaustiveGradedSimpleFamily S) (i : I) :
    gradedProjectiveExtEuler 𝒜
        (LaurentK0.of.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜)
          (gradedIdempotentProjective (he i) (he₀ i))) =
      (gradedSimpleClassBasis S he he₀ hne hself hS).dualBasis i := by
  ext y
  have hI (j : I) := Ideal.isHomogeneous_span_singleton 𝒜 ⟨0, he₀ j⟩
  rw [gradedIdempotentProjective_eq _ _ (hI i),
    gradedProjectiveExtEuler_ofIdeal_span_singleton_eq_repr S he he₀ hI hne hself hS,
    Module.Basis.dualBasis_apply]

end Family

end TauCeti
