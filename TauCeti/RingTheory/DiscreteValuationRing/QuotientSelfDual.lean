/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.DiscreteValuationRing.MatlisDual
public import TauCeti.RingTheory.MatlisDuality.Basic

/-!
# The coefficient rings `O ⧸ (a)` are Matlis self-dual

Let `O` be a domain with fraction field `K`, let `a ≠ 0` and `A = O ⧸ (a)`. Division by `a`
(`IsDiscreteValuationRing.divQuotient`) identifies `A` with the elements of `K/O` killed by `a`.
This file upgrades that identification to an isomorphism of `A`-modules between `A` and its Matlis
dual `Hom_O(A, K/O)`, sending `x` to `y ↦ yx/a mod O`. Consequently, for every `A`-module `N`, the
`A`-linear dual `Hom_A(N, A)` is the Matlis dual `Hom_O(N, K/O)`, through `f ↦ (x ↦ f(x)/a mod O)`,
naturally in `N` and compatibly with the two actions of `A`.

For a discrete valuation ring `O` with uniformizer `ϖ` these are the coefficient rings
`Aₙ = O ⧸ (ϖⁿ)` of finite-coefficient coherent duality. A duality statement phrased with the
`Aₙ`-linear dual of a cohomology module is thereby a statement about its `O`-linear Matlis dual
into `K/O`, which is how coherent homology with `Aₙ` coefficients is defined. The identification
depends on the chosen generator `a`: replacing `a` by `ua` for a unit `u` multiplies it by `u⁻¹`.
Over a ramified `O` it differs from Pontryagin duality into `ℚₚ/ℤₚ`, which needs a trace character
and the inverse different.

## Main definitions

* `IsDiscreteValuationRing.quotientEquivMatlisDual`: the `A`-linear isomorphism
  `A ≅ Hom_O(A, K/O)`, `x ↦ (y ↦ yx/a mod O)`.
* `IsDiscreteValuationRing.dualEquivMatlisDual`: the `O`-linear isomorphism
  `Hom_A(N, A) ≅ Hom_O(N, K/O)`, `f ↦ (x ↦ f(x)/a mod O)`, for an `A`-module `N`.

## Main results

* `IsDiscreteValuationRing.dualEquivMatlisDual_comp`: naturality in `N`; precomposition with an
  `A`-linear map `g` corresponds to the Matlis dual `MatlisDual.map g`.
* `IsDiscreteValuationRing.dualEquivMatlisDual_smul`: the action of `A` on values of `A`-linear
  functionals corresponds to its action on arguments of Matlis functionals.

## References

* [C. Calegari and D. Geraghty, *Modularity lifting beyond the Taylor–Wiles method*,
  Invent. Math. 211 (2018)], Section 7.2, for coherent homology with coefficients in `O ⧸ ϖⁿ`
  defined by Matlis duality into `K/O`.
* E. Matlis, *Injective modules over Noetherian rings*, Pacific J. Math. 8 (1958).
-/

public section

open LinearMap MulOpposite TauCeti

namespace IsDiscreteValuationRing

universe u v w

variable {O : Type u} {K : Type v} [CommRing O] [Field K] [Algebra O K]
  [IsFractionRing O K] {a : O}

/-- **Matlis self-duality of `O ⧸ (a)`.** For `a ≠ 0`, the quotient `A = O ⧸ (a)` is isomorphic,
as an `A`-module, to its Matlis dual `Hom_O(A, K/O)`: the class `x` goes to the functional
`y ↦ yx/a mod O`, that is, to `x` acting on the functional `divQuotient a`. -/
noncomputable def quotientEquivMatlisDual (ha : a ≠ 0) :
    (O ⧸ Ideal.span {a}) ≃ₗ[O ⧸ Ideal.span {a}]
      MatlisDual O (K ⧸ range (Algebra.linearMap O K)) (O ⧸ Ideal.span {a}) :=
  LinearEquiv.ofBijective
    (toSpanSingleton _ _ ((MatlisDual.equivLinearMap _ _ _).symm (divQuotient a))) <| by
    -- Evaluation at `1` turns the map into `quotientEquivTorsionBySet`, and is itself bijective.
    let ev := (MatlisDual.equivLinearMap O (K ⧸ range (Algebra.linearMap O K))
      (O ⧸ Ideal.span {a})).trans ((Ideal.span {a}).quotientLinearMapEquivTorsionBySet _)
    refine (Function.Bijective.of_comp_iff' ev.bijective _).mp ?_
    convert (quotientEquivTorsionBySet (K := K) ha).bijective using 1
    funext x
    obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective x
    refine Subtype.ext ?_
    simp [ev, MatlisDual.smul_apply]

@[simp]
theorem quotientEquivMatlisDual_apply_apply (ha : a ≠ 0) (x y : O ⧸ Ideal.span {a}) :
    MatlisDual.equivLinearMap _ _ _ (quotientEquivMatlisDual (K := K) ha x) y =
      divQuotient a (y * x) := by
  simp [quotientEquivMatlisDual, MatlisDual.smul_apply]

/-- The inverse of `quotientEquivMatlisDual` is characterized by evaluation at `1`. -/
@[simp]
theorem divQuotient_quotientEquivMatlisDual_symm (ha : a ≠ 0)
    (φ : MatlisDual O (K ⧸ range (Algebra.linearMap O K)) (O ⧸ Ideal.span {a})) :
    divQuotient a ((quotientEquivMatlisDual ha).symm φ) = MatlisDual.equivLinearMap _ _ _ φ 1 := by
  conv_rhs => rw [← (quotientEquivMatlisDual ha).apply_symm_apply φ]
  rw [quotientEquivMatlisDual_apply_apply, one_mul]

variable (N : Type w) [AddCommGroup N] [Module O N] [Module (O ⧸ Ideal.span {a}) N]
  [IsScalarTower O (O ⧸ Ideal.span {a}) N]

/-- **The `O ⧸ (a)`-linear dual is the Matlis dual into `K/O`.** For `a ≠ 0` and a module `N` over
`A = O ⧸ (a)`, a functional `f : N → A` goes to the `O`-linear functional `x ↦ f(x)/a mod O` with
values in `K/O`. It is the composite of `quotientEquivMatlisDual` with the Hom-tensor adjunction
`MatlisDual.equivLinearMapDualRegular`. -/
noncomputable def dualEquivMatlisDual (ha : a ≠ 0) :
    Module.Dual (O ⧸ Ideal.span {a}) N ≃ₗ[O] MatlisDual O (K ⧸ range (Algebra.linearMap O K)) N :=
  ((quotientEquivMatlisDual ha).congrRight.restrictScalars O).trans
    MatlisDual.equivLinearMapDualRegular.symm

@[simp]
theorem dualEquivMatlisDual_apply_apply (ha : a ≠ 0) (f : Module.Dual (O ⧸ Ideal.span {a}) N)
    (x : N) :
    MatlisDual.equivLinearMap _ _ _ (dualEquivMatlisDual (K := K) N ha f) x =
      divQuotient a (f x) := by
  simp [dualEquivMatlisDual]

/-- The inverse of `dualEquivMatlisDual` is characterized by dividing its values by `a`. -/
@[simp]
theorem divQuotient_dualEquivMatlisDual_symm_apply (ha : a ≠ 0)
    (φ : MatlisDual O (K ⧸ range (Algebra.linearMap O K)) N) (x : N) :
    divQuotient a ((dualEquivMatlisDual N ha).symm φ x) = MatlisDual.equivLinearMap _ _ _ φ x := by
  conv_rhs => rw [← (dualEquivMatlisDual N ha).apply_symm_apply φ]
  rw [dualEquivMatlisDual_apply_apply]

/-- **Naturality of `dualEquivMatlisDual`.** Precomposing an `O ⧸ (a)`-linear functional with an
`O ⧸ (a)`-linear map `g` corresponds to applying the Matlis dual `MatlisDual.map g`. -/
@[simp]
theorem dualEquivMatlisDual_comp (ha : a ≠ 0) {N' : Type*} [AddCommGroup N'] [Module O N']
    [Module (O ⧸ Ideal.span {a}) N'] [IsScalarTower O (O ⧸ Ideal.span {a}) N']
    (g : N →ₗ[O ⧸ Ideal.span {a}] N') (f : Module.Dual (O ⧸ Ideal.span {a}) N') :
    dualEquivMatlisDual (K := K) N ha (f ∘ₗ g) =
      MatlisDual.map g (dualEquivMatlisDual N' ha f) := by
  ext x
  simp [MatlisDual.map_apply]

/-- **`dualEquivMatlisDual` is `O ⧸ (a)`-linear.** Multiplying the values of a functional by `c`
corresponds to the right action of `c` on Matlis functionals, precomposition with `c • ·`. -/
@[simp]
theorem dualEquivMatlisDual_smul (ha : a ≠ 0) (c : O ⧸ Ideal.span {a})
    (f : Module.Dual (O ⧸ Ideal.span {a}) N) :
    dualEquivMatlisDual (K := K) N ha (c • f) = op c • dualEquivMatlisDual N ha f := by
  ext x
  simp [MatlisDual.smul_op_apply, mul_comm c]

end IsDiscreteValuationRing
