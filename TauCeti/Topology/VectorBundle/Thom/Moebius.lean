/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Reduced
public import TauCeti.Geometry.Manifold.LocallyContractible
public import TauCeti.Topology.VectorBundle.Moebius
public import TauCeti.Topology.VectorBundle.Thom.LineBundle

/-!
# The Thom pair of the Möbius line bundle

The Möbius line bundle `E` over the circle (`TauCeti.moebiusCore`) has a continuous fibre norm and
is not orientable, so the Thom isomorphism of a line bundle with orientation coefficients gives
`H₁(E, E₀; R) ≅ H₀(S¹; o(E)) ≅ R ⧸ 2R` (`TauCeti.moebiusThomPairSingularHomologyOneEquiv`). With
integer coefficients this is `ℤ/2`, which is not the zeroth homology `H₀(S¹; ℤ) ≅ ℤ` of the circle
with constant coefficients
(`TauCeti.not_nonempty_moebiusThomPair_singularHomology_one_linearEquiv`): the relative homology
across the level of a critical circle of index one whose negative normal bundle is a Möbius line is
the homology of the circle twisted by the orientation local system of that line, and constant
integer coefficients give the wrong answer.

## Main results

* `TauCeti.moebiusThomPairSingularHomologyOneEquiv`: `H₁(E, E₀; R) ≅ R ⧸ 2R`.
* `TauCeti.not_nonempty_moebiusThomPair_singularHomology_one_linearEquiv`:
  `H₁(E, E₀; ℤ)` is not isomorphic to `H₀(S¹; ℤ)`.

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §10 and §12 (the Thom isomorphism and the orientation double cover).
* R. Bott, *Nondegenerate critical manifolds*, Annals of Mathematics 60 (1954), 248–261, for the
  orientation twist of the negative normal bundle of a critical submanifold.
-/

public section

noncomputable section

open Bundle CategoryTheory Module

namespace TauCeti

/-- The orientation of the fibre of the Möbius line bundle over `1` given by the vector `1`. -/
private def moebiusOrientationOne : Orientation ℝ (moebiusCore.Fiber 1) (Fin 1) :=
  (Module.Basis.singleton (Fin 1) ℝ).orientation

/-- **The Thom pair of the Möbius line bundle.** For the Möbius line `E` over the circle and every
commutative ring `R`, `H₁(E, E₀; R) ≅ H₀(S¹; o(E)) ≅ R ⧸ 2R`. -/
def moebiusThomPairSingularHomologyOneEquiv (R : Type) [CommRing R] :
    ((thomPair ℝ moebiusCore.Fiber).singularHomology (ModuleCat.of R R) 1 : ModuleCat R) ≃ₗ[R]
      R ⧸ Ideal.span {(2 : R)} :=
  VectorBundleOrientationCover.thomPairSingularHomologyOneEquivQuotientTwo
    continuous_norm_moebiusCore (finrank_self ℝ) isEmpty_vectorBundleOrientation_moebiusCore
    moebiusOrientationOne

/-- The identification `H₁(E, E₀; R) ≅ R ⧸ 2R` for the Möbius line is
`TauCeti.VectorBundleOrientationCover.thomPairSingularHomologyOneEquivQuotientTwo` for the Möbius
line bundle, constructed from any orientation `o` of any fibre. -/
theorem moebiusThomPairSingularHomologyOneEquiv_eq (R : Type) [CommRing R] {b : Circle}
    (o : Orientation ℝ (moebiusCore.Fiber b) (Fin 1)) :
    moebiusThomPairSingularHomologyOneEquiv R =
      VectorBundleOrientationCover.thomPairSingularHomologyOneEquivQuotientTwo
        continuous_norm_moebiusCore (finrank_self ℝ) isEmpty_vectorBundleOrientation_moebiusCore
        o := by
  ext x
  rw [moebiusThomPairSingularHomologyOneEquiv,
    VectorBundleOrientationCover.thomPairSingularHomologyOneEquivQuotientTwo_apply,
    VectorBundleOrientationCover.thomPairSingularHomologyOneEquivQuotientTwo_apply,
    VectorBundleOrientationCover.twistedHomology₀EquivQuotientTwo_eq _ _ moebiusOrientationOne o]

/-- **The Thom comparison for the Möbius line needs its orientation local system.** The first
homology of the Thom pair of the Möbius line `E` over the circle, `H₁(E, E₀; ℤ) ≅ ℤ/2`, is not
isomorphic to the zeroth homology `H₀(S¹; ℤ) ≅ ℤ` of the circle with constant integer coefficients:
the Thom isomorphism shifts the homology of the base twisted by the orientation local system of
`E`. -/
theorem not_nonempty_moebiusThomPair_singularHomology_one_linearEquiv :
    ¬ Nonempty (((thomPair ℝ moebiusCore.Fiber).singularHomology (ModuleCat.of ℤ ℤ) 1 :
        ModuleCat.{0} ℤ) ≃ₗ[ℤ]
      (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) 0).obj
        (ModuleCat.of ℤ ℤ)).obj (TopCat.of Circle) : ModuleCat.{0} ℤ)) := by
  rintro ⟨e⟩
  -- Compose to an isomorphism `ℤ ⧸ 2ℤ ≃ ℤ`, using the augmentation `H₀(S¹; ℤ) ≅ ℤ`.
  let f : (ℤ ⧸ Ideal.span {(2 : ℤ)}) ≃ₗ[ℤ] ℤ :=
    (moebiusThomPairSingularHomologyOneEquiv ℤ).symm ≪≫ₗ e ≪≫ₗ
      (asIso ((TopCat.of Circle).singularHomology₀ε (ModuleCat.of ℤ ℤ))).toLinearEquiv
  -- In `ℤ ⧸ 2ℤ` the class of `1` is killed by `2` but is not zero; in `ℤ` no such element exists.
  have h2 : (2 : ℤ) • f (Submodule.Quotient.mk 1) = 0 := by
    rw [← map_smul, ← Submodule.Quotient.mk_smul, smul_eq_mul, mul_one,
      (Submodule.Quotient.mk_eq_zero _).2 (Ideal.mem_span_singleton_self 2), map_zero]
  have h1 : (Submodule.Quotient.mk 1 : ℤ ⧸ Ideal.span {(2 : ℤ)}) = 0 :=
    f.injective ((smul_eq_zero.1 h2).resolve_left two_ne_zero |>.trans (map_zero f).symm)
  rw [Submodule.Quotient.mk_eq_zero, Ideal.mem_span_singleton] at h1
  exact absurd (Int.eq_one_of_dvd_one zero_le_two h1) (by norm_num)

end TauCeti
