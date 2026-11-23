/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.BettiNumber
public import TauCeti.AlgebraicTopology.Singular.Twisted.Basic
public import TauCeti.Topology.VectorBundle.Orientation.TwistedHomology.Basic

/-!
# Betti numbers with coefficients in the orientation local system

Let `E → B` be a real vector bundle and `o(E)` its orientation local system
(`TauCeti.VectorBundleOrientationCover.signLocalSystem`), with coefficients in a ring `K`: its
fibre over `b` is a copy of `K` whose two generators are the two orientations of `E_b`. The
dimensions `dim Hⱼ(B; o(E) ⊗ K)` of the homology of `B` with these coefficients are the twisted
Betti numbers of `B`. They are the coefficients through which a bundle that need not be
orientable enters the Thom isomorphism `Hⱼ₊ᵣ(E, E₀; K) ≅ Hⱼ(B; o(E) ⊗ K)` of a bundle of rank `r`,
and so the contribution of a critical submanifold `B` with negative normal bundle `E` to the
Morse–Bott inequalities. This file compares them with the ordinary Betti numbers
`TauCeti.bettiNumber K B j`.

* An orientation of `E` trivializes `o(E)`, so it identifies `Hⱼ(B; o(E) ⊗ K)` with the ordinary
  singular homology of `B` (`TauCeti.VectorBundleOrientation.twistedHomologySignLocalSystemIso`),
  and the twisted Betti numbers are the ordinary ones
  (`TauCeti.VectorBundleOrientation.finrank_twistedHomology_signLocalSystem`).
* If `2 = 0` in `K`, as for `K = 𝔽₂`, the system `o(E)` is constant with no orientation
  (`TauCeti.VectorBundleOrientationCover.signLocalSystemIsoOfTwoEqZero`), so the same holds for
  every bundle
  (`TauCeti.VectorBundleOrientationCover.twistedHomologySignLocalSystemIsoOfTwoEqZero` and
  `TauCeti.VectorBundleOrientationCover.finrank_twistedHomology_signLocalSystem_of_two_eq_zero`).
* Otherwise the twist is visible already in degree zero: over a connected, locally path-connected
  base and a field `K` with `2 ≠ 0`, `dim H₀(B; o(E) ⊗ K)` is `1` if `E` is orientable and `0` if
  not (`TauCeti.VectorBundleOrientationCover.finrank_twistedHomology_zero_signLocalSystem`),
  while the ordinary zeroth Betti number of such a base is `1`. For the Möbius line over the
  circle, which is not orientable, the twisted zeroth Betti number over `ℚ` is `0`.

The comparisons with `TauCeti.bettiNumber`, which takes the coefficient ring and the space in a
common universe, are stated with the base, the fibres of `E`, the index type of orientations and
the coefficients in one universe.

## References

* A. Hatcher, *Algebraic Topology*, Section 3.H (homology with local coefficients and the
  orientation system).
* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §12 (the orientation double cover and twisted coefficients).
-/

public section

noncomputable section

open Bundle CategoryTheory Module

namespace TauCeti

open LocalCoefficientSystem

section Iso

universe u uB uE uι

variable {B : Type uB} [TopologicalSpace B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type uE} [TopologicalSpace (TotalSpace F E)] [∀ b, AddCommMonoid (E b)]
  [∀ b, Module ℝ (E b)] [∀ b, TopologicalSpace (E b)] [FiberBundle F E] [VectorBundle ℝ F E]
  {ι : Type uι} [Fintype ι] {R : Type u} [Ring R] (hι : Fintype.card ι = finrank ℝ F)

/-- An orientation `o` of `E` identifies the homology of `B` with coefficients in the orientation
local system with the singular homology of `B` with coefficients in `R`, through the
trivialization of the orientation local system given by `o`
(`TauCeti.VectorBundleOrientation.signLocalSystemIso`). -/
def VectorBundleOrientation.twistedHomologySignLocalSystemIso (o : VectorBundleOrientation F E ι)
    (n : ℕ) :
    twistedHomology.{u, uB, max uE uι u} (VectorBundleOrientationCover.signLocalSystem F E R hι) n ≅
      ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{max uB uE uι u} R) n).obj
        (ModuleCat.of R (ULift.{max uB uE uι} R))).obj (TopCat.of B) :=
  asIso (twistedHomologyCoefficientMap (signLocalSystemIso hι o).hom n) ≪≫
    twistedHomologyConstantIso (TopCat.of B) _ n

/-- The identification of homology twisted by the orientation local system with singular homology
given by `o` is the map induced by the trivialization given by `o`, followed by the comparison of
twisted homology with constant coefficients and singular homology. -/
theorem VectorBundleOrientation.twistedHomologySignLocalSystemIso_hom
    (o : VectorBundleOrientation F E ι) (n : ℕ) :
    (twistedHomologySignLocalSystemIso (R := R) hι o n).hom =
      twistedHomologyCoefficientMap (signLocalSystemIso hι o).hom n ≫
        (twistedHomologyConstantIso (TopCat.of B) _ n).hom :=
  (rfl)

/-- If `2 = 0` in `R`, the homology of `B` with coefficients in the orientation local system is
the singular homology of `B` with coefficients in `R`, for every bundle, through the
trivialization of the orientation local system in characteristic two
(`TauCeti.VectorBundleOrientationCover.signLocalSystemIsoOfTwoEqZero`). -/
def VectorBundleOrientationCover.twistedHomologySignLocalSystemIsoOfTwoEqZero
    [FiniteDimensional ℝ F] (h2 : (2 : R) = 0) (n : ℕ) :
    twistedHomology.{u, uB, max uE uι u} (signLocalSystem F E R hι) n ≅
      ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{max uB uE uι u} R) n).obj
        (ModuleCat.of R (ULift.{max uB uE uι} R))).obj (TopCat.of B) :=
  asIso (twistedHomologyCoefficientMap (signLocalSystemIsoOfTwoEqZero hι h2).hom n) ≪≫
    twistedHomologyConstantIso (TopCat.of B) _ n

/-- The identification in characteristic two of homology twisted by the orientation local system
with singular homology is the map induced by the trivialization of the orientation local system,
followed by the comparison of twisted homology with constant coefficients and singular
homology. -/
theorem VectorBundleOrientationCover.twistedHomologySignLocalSystemIsoOfTwoEqZero_hom
    [FiniteDimensional ℝ F] (h2 : (2 : R) = 0) (n : ℕ) :
    (twistedHomologySignLocalSystemIsoOfTwoEqZero (F := F) (E := E) hι h2 n).hom =
      twistedHomologyCoefficientMap (signLocalSystemIsoOfTwoEqZero (F := F) (E := E) hι h2).hom n ≫
        (twistedHomologyConstantIso (TopCat.of B) _ n).hom :=
  (rfl)

open scoped Classical in
/-- **The twist in degree zero.** Over a connected, locally path-connected base and a field `K`
in which `2 ≠ 0`, the zeroth homology of `B` with coefficients in the orientation local system
has dimension `1` if `E` is orientable and `0` if it is not. -/
theorem VectorBundleOrientationCover.finrank_twistedHomology_zero_signLocalSystem
    [FiniteDimensional ℝ F] [ConnectedSpace B] [LocallyPathConnectedSpace B] {K : Type u}
    [Field K] (h2 : (2 : K) ≠ 0) :
    finrank K (twistedHomology.{u, uB, max uE uι u} (signLocalSystem F E K hι) 0) =
      if Nonempty (VectorBundleOrientation F E ι) then 1 else 0 := by
  have : PathConnectedSpace B := PathConnectedSpace.of_locallyPathConnectedSpace
  obtain ⟨b⟩ := (inferInstance : Nonempty B)
  split_ifs with h
  · exact ((VectorBundleOrientation.twistedHomology₀Equiv hι h.some b).finrank_eq).trans
      (finrank_self K)
  -- Otherwise `H₀(B; o(E)) ≅ K ⧸ 2K`, which vanishes since `2` is a unit of `K`.
  obtain ⟨q, -⟩ := surjective_proj (F := F) (E := E) hι b
  have : Subsingleton (K ⧸ Ideal.span {(2 : K)}) :=
    Ideal.Quotient.subsingleton_iff.2 (Ideal.span_singleton_eq_top.2 (IsUnit.mk0 _ h2))
  rw [(twistedHomology₀EquivQuotientTwo hι (not_nonempty_iff.1 h) q.orientation).finrank_eq]
  exact finrank_zero_of_subsingleton

end Iso

section BettiNumber

universe u

variable {B : Type u} [TopologicalSpace B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type u} [TopologicalSpace (TotalSpace F E)] [∀ b, AddCommMonoid (E b)]
  [∀ b, Module ℝ (E b)] [∀ b, TopologicalSpace (E b)] [FiberBundle F E] [VectorBundle ℝ F E]
  {ι : Type u} [Fintype ι] {K : Type u} [Ring K] (hι : Fintype.card ι = finrank ℝ F)

/-- **Twisted Betti numbers of an orientable bundle.** If `E` is orientable, the homology of `B`
with coefficients in the orientation local system has the ordinary Betti numbers of `B`. -/
theorem VectorBundleOrientation.finrank_twistedHomology_signLocalSystem
    (o : VectorBundleOrientation F E ι) (n : ℕ) :
    finrank K (twistedHomology (VectorBundleOrientationCover.signLocalSystem F E K hι) n) =
      bettiNumber K B n :=
  (twistedHomologySignLocalSystemIso hι o n).toLinearEquiv.finrank_eq.trans
    (finrank_singularHomology_uLift_eq_bettiNumber K B n)

/-- **Twisted Betti numbers in characteristic two.** If `2 = 0` in `K`, as for `K = 𝔽₂`, the
homology of `B` with coefficients in the orientation local system of any bundle has the ordinary
Betti numbers of `B`. -/
theorem VectorBundleOrientationCover.finrank_twistedHomology_signLocalSystem_of_two_eq_zero
    [FiniteDimensional ℝ F] (h2 : (2 : K) = 0) (n : ℕ) :
    finrank K (twistedHomology (signLocalSystem F E K hι) n) = bettiNumber K B n :=
  (twistedHomologySignLocalSystemIsoOfTwoEqZero hι h2 n).toLinearEquiv.finrank_eq.trans
    (finrank_singularHomology_uLift_eq_bettiNumber K B n)

end BettiNumber

end TauCeti
