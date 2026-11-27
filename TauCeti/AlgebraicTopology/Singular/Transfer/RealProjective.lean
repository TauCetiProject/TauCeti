/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cellular.RealProjective.Homology
public import TauCeti.AlgebraicTopology.Singular.Sphere
public import TauCeti.AlgebraicTopology.Singular.Transfer.Sign

/-!
# Top homology of even-dimensional real projective space with sign coefficients

Real projective space `ℝPᴺ` is the quotient of the unit sphere `Sᴺ` by the antipode `x ↦ -x`, and
the quotient map is a double cover (`TauCeti.RealProjectiveSpace.isCoveringMap_coverHom`). The
sign local system of the antipode over it (`IsCoveringMap.signLocalSystem`) has as fibre over `[x]`
the functions on `{x, -x}` with values in `R` changing sign under the antipode; these are the
twisted coefficients of `ℝPᴺ`, written `sign` below.

For even `N > 0` the untwisted top homology vanishes, `H_N(ℝPᴺ; R) = 0` as soon as `2` is not
a right zero divisor in `R` (`TauCeti.RealProjectiveSpace.isZero_singularHomology_of_even`), and
so does `H_{N+1}(ℝPᴺ; R)`. The coefficient long exact sequence of `0 ⟶ sign ⟶ R[p⁻¹ b] ⟶ R ⟶ 0` then
identifies `H_N(ℝPᴺ; sign)` with the homology `H_N(Sᴺ; R)` of the cover
(`IsCoveringMap.bijective_signHomologyToCover_of_isZero`), which is a copy of `R`. So

`H_N(ℝPᴺ; sign) ≅ R`

(`TauCeti.RealProjectiveSpace.twistedHomologyTopLinearEquivOfEven`): the even-dimensional real
projective spaces have no integral fundamental class, while their top homology with twisted
integer coefficients is infinite cyclic, read on the cover by the fundamental class of `Sᴺ`. For
`N = 2` this is `H₂(ℝP²; ℤ) = 0` and `H₂(ℝP²; sign) ≅ ℤ`.

## Main definitions

* `TauCeti.RealProjectiveSpace.coverHom`: the antipodal double cover `Sᴺ → ℝPᴺ`.
* `TauCeti.RealProjectiveSpace.antipode`: the antipode of `Sᴺ`, the deck involution of this cover.
* `TauCeti.RealProjectiveSpace.twistedHomologyTopLinearEquivOfEven`: `H_N(ℝPᴺ; sign) ≅ R` for even
  `N > 0`.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.H, for homology with local coefficients, the local system of a covering space and the
  twisted integer coefficients of a nonorientable manifold, and Example 2.42 for the homology of
  real projective space.
-/

public section

noncomputable section

open CategoryTheory Metric TauCeti.LocalCoefficientSystem

namespace TauCeti.RealProjectiveSpace

variable (N : ℕ)

/-- The antipodal double cover `Sᴺ → ℝPᴺ`, the quotient map of the unit sphere, as a morphism of
topological spaces. -/
def coverHom :
    TopCat.of (sphere (0 : EuclideanSpace ℝ (Fin (N + 1))) 1) ⟶
      TopCat.of (RealProjectiveSpace N) :=
  TopCat.ofHom ⟨mk N, continuous_mk N⟩

@[simp]
theorem coverHom_apply (x : sphere (0 : EuclideanSpace ℝ (Fin (N + 1))) 1) :
    coverHom N x = mk N x :=
  (rfl)

/-- The antipodal map of the unit sphere `Sᴺ`. -/
def antipode : C(sphere (0 : EuclideanSpace ℝ (Fin (N + 1))) 1,
    sphere (0 : EuclideanSpace ℝ (Fin (N + 1))) 1) :=
  ⟨Neg.neg, continuous_neg⟩

@[simp]
theorem antipode_apply (x : sphere (0 : EuclideanSpace ℝ (Fin (N + 1))) 1) :
    antipode N x = -x :=
  (rfl)

/-- The antipode is the action of `-1 ∈ ℤˣ`, the deck involution of the quotient `Sᴺ → ℝPᴺ`. -/
theorem antipode_eq_neg_one_smul (x : sphere (0 : EuclideanSpace ℝ (Fin (N + 1))) 1) :
    antipode N x = (-1 : ℤˣ) • x :=
  (Sphere.neg_one_smul x).symm

/-- The quotient map `Sᴺ → ℝPᴺ` is a covering map. -/
theorem isCoveringMap_coverHom : IsCoveringMap (coverHom N) :=
  isCoveringMap_mk N

/-- The antipode is a map over `ℝPᴺ`. -/
theorem coverHom_comp_antipode : ⇑(coverHom N) ∘ ⇑(antipode N) = ⇑(coverHom N) :=
  (isQuotientCoveringMap_mk N).comp_eq_of_forall_eq_neg_one_smul (antipode_eq_neg_one_smul N)

/-- The fibres of the antipodal cover `Sᴺ → ℝPᴺ`, the antipodal pairs, are finite. -/
theorem finite_preimage_coverHom (b : RealProjectiveSpace N) : Finite (coverHom N ⁻¹' {b}) :=
  (isQuotientCoveringMap_mk N).finite_fiber b

variable (R : Type) [Ring R] {N}

/-- **Top homology of even-dimensional real projective space with sign coefficients.** For even
`N > 0` and a ring `R` in which `2` is not a right zero divisor, `H_N(ℝPᴺ; sign) ≅ R`. Reading a
twisted class on the antipodal cover identifies it with a class of `H_N(Sᴺ; R) ≅ R`, which is
possible because the untwisted groups `H_N(ℝPᴺ; R)` and `H_{N+1}(ℝPᴺ; R)` vanish. -/
def twistedHomologyTopLinearEquivOfEven (h2 : IsRightRegular (2 : R)) (hN : Even N)
    (hN0 : N ≠ 0) :
    twistedHomology
      ((isCoveringMap_coverHom N).signLocalSystem R (antipode N) (coverHom_comp_antipode N)) N ≃ₗ[R]
        R :=
  LinearEquiv.ofBijective
    (((ContinuousMap.HomotopyEquiv.refl _).singularHomologySphereIso (ModuleCat.of R R)
        finrank_euclideanSpace_fin (Nat.one_le_iff_ne_zero.2 hN0)).hom.hom ∘ₗ
      ((isCoveringMap_coverHom N).signHomologyToCover R (coverHom_comp_antipode N)
        (finite_preimage_coverHom N) N).hom)
    (((ContinuousMap.HomotopyEquiv.refl _).singularHomologySphereIso (ModuleCat.of R R)
        finrank_euclideanSpace_fin (Nat.one_le_iff_ne_zero.2 hN0)).toLinearEquiv.bijective.comp
      ((isCoveringMap_coverHom N).bijective_signHomologyToCover_of_isZero R
        (coverHom_comp_antipode N)
        (involutive_of_forall_eq_neg_one_smul (antipode_eq_neg_one_smul N))
        (finite_preimage_coverHom N)
        ((isQuotientCoveringMap_mk N).ne_self_of_forall_eq_neg_one_smul
          (antipode_eq_neg_one_smul N))
        ((isQuotientCoveringMap_mk N).eq_or_eq_of_forall_eq_neg_one_smul
          (antipode_eq_neg_one_smul N))
        (mk_surjective N) N (isZero_singularHomology_of_even R h2 hN hN0)
        (isZero_singularHomology_of_lt R N.lt_succ_self)))

/-- The equivalence `twistedHomologyTopLinearEquivOfEven` reads a twisted class on the antipodal
cover (`IsCoveringMap.signHomologyToCover`) and identifies the top homology of the sphere with
`R`. -/
@[simp]
theorem twistedHomologyTopLinearEquivOfEven_apply (h2 : IsRightRegular (2 : R)) (hN : Even N)
    (hN0 : N ≠ 0) (g : twistedHomology
      ((isCoveringMap_coverHom N).signLocalSystem R (antipode N) (coverHom_comp_antipode N)) N) :
    twistedHomologyTopLinearEquivOfEven R h2 hN hN0 g =
      ((ContinuousMap.HomotopyEquiv.refl _).singularHomologySphereIso (ModuleCat.of R R)
        finrank_euclideanSpace_fin (Nat.one_le_iff_ne_zero.2 hN0)).hom.hom
        ((isCoveringMap_coverHom N).signHomologyToCover R (coverHom_comp_antipode N)
          (finite_preimage_coverHom N) N |>.hom g) :=
  (rfl)

end TauCeti.RealProjectiveSpace
