/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Grading.SimplyBlocked
public import TauCeti.KnotTheory.Grid.Stabilization.Map.Grading
public import TauCeti.KnotTheory.Grid.Stabilization.SimplyBlocked.Basic

/-!
# The bigrading of the simply blocked stabilization chain map

Let `G` be a grid diagram of size `n` with an odd number of link components, let `s` and `i` be
columns of `G`, and let `G' = G.stabilizeX s` be the stabilization splitting the `X`-marking of
column `s`, with `j = s.castSucc.succAbove i` the column of `G'` carrying the old `O`-marking of
column `i`. Both specialized chain modules `GC^_j(G')` and `GC^_i(G)` carry the integral
`(O-Maslov, Alexander)` bigrading of `Grading/SimplyBlocked.lean`.

This file shows that the specialized stabilization comparison
`GridDiagram.simplyBlockedStabilizeXMap` has bidegree `(0, 0)` over every commutative ring. Every
homogeneous chain of `GC^_j(G')` lifts to a chain of `GC⁻(G')` of the same bidegree
(`mem_bigradedChainHatPiece_iff_exists`), the unblocked stabilization chain map preserves that
bidegree (`stabilizeXCoefficientFormula_mem_bigradedChainMinusPiece`), and specializing at `V_i = 0`
descends back to the same homogeneous piece of `GC^_i(G)`
(`simplyBlockedStabilizeXMap_simplyBlockedSpecialization`).

Restricting to each bidegree `g` gives an `R`-linear comparison between homogeneous chain pieces
(`gradedSimplyBlockedStabilizeXChainMap`). Over a commutative ring of characteristic two, these
piecewise maps intertwine the graded differentials and assemble at each Alexander degree `a` into a
chain map `gradedSimplyBlockedStabilizeXMap` of Maslov-indexed complexes of `R`-modules. For a knot
grid this is chain-level bigrading compatibility of the `X`-stabilization map on `GC^`.

## Main definitions

* `TauCeti.OddComponentGridDiagram.gradedSimplyBlockedStabilizeXChainMap`: the restriction of the
  specialized stabilization chain map to the homogeneous piece of bidegree `g`.
* `TauCeti.OddComponentGridDiagram.gradedSimplyBlockedStabilizeXMap`: the induced chain map of
  Maslov-graded complexes in Alexander degree `a`.

## Main results

* `TauCeti.OddComponentGridDiagram.simplyBlockedStabilizeXMap_mem_bigradedChainHatPiece`: the
  specialized stabilization chain map preserves the `(O-Maslov, Alexander)` bigrading over any
  commutative ring.
* `TauCeti.OddComponentGridDiagram.gradedSimplyBlockedStabilizeXChainMap_differential`: in
  characteristic two, the homogeneous piece maps intertwine the graded differentials.

## References

* Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Sections 4.6 and 5.2.
* Manolescu--Ozsváth--Szabó--Thurston, *On combinatorial link Floer homology*, Section 3.2
  (arXiv:math/0610559).
-/

public section

open CategoryTheory MvPolynomial

namespace TauCeti.OddComponentGridDiagram

variable {n : ℕ} (G : OddComponentGridDiagram n) (s i : Fin n)

local notation "j" => Fin.succAbove (Fin.castSucc s) i

section CommRing

variable (R : Type*) [CommRing R]

/-- **The specialized stabilization chain map preserves the bigrading.** Blocking the transported
old `O`-marking `j = s.castSucc.succAbove i` in `G.stabilizeX s` and column `i` in `G`, the
stabilization chain map carries every chain of bidegree `g` to a chain of bidegree `g`. -/
theorem simplyBlockedStabilizeXMap_mem_bigradedChainHatPiece {g : ℤ × ℤ}
    {c : GridChainHat R (n + 1) j}
    (hc : c ∈ (G.stabilizeX s).bigradedChainHatPiece R j g) :
    G.1.simplyBlockedStabilizeXMap s i R c ∈ G.bigradedChainHatPiece R i g := by
  obtain ⟨b, hb, rfl⟩ := (G.stabilizeX s).mem_bigradedChainHatPiece_iff_exists.mp hc
  rw [GridDiagram.simplyBlockedStabilizeXMap_simplyBlockedSpecialization,
    GridDiagram.stabilizeXChainMap_apply]
  exact G.simplyBlockedSpecialization_mem_bigradedChainHatPiece i
    (G.stabilizeXCoefficientFormula_mem_bigradedChainMinusPiece s R hb)

/-- The specialized stabilization chain map restricted to the homogeneous piece of bidegree `g`, as
a linear map over the ground ring `R`. -/
noncomputable def gradedSimplyBlockedStabilizeXChainMap (g : ℤ × ℤ) :
    (G.stabilizeX s).bigradedChainHatPiece R j g →ₗ[R] G.bigradedChainHatPiece R i g where
  toFun c := ⟨G.1.simplyBlockedStabilizeXMap s i R c,
    G.simplyBlockedStabilizeXMap_mem_bigradedChainHatPiece s i R c.2⟩
  map_add' c d := Subtype.ext (map_add _ c.1 d.1)
  map_smul' r c := by
    apply Subtype.ext
    simp only [Submodule.coe_smul, RingHom.id_apply]
    have h := (G.1.simplyBlockedStabilizeXMap s i R).map_smulₛₗ
      (MvPolynomial.C r : MvPolynomial {k : Fin (n + 1) // k ≠ j} R) c.1
    rw [GridDiagram.simplyBlockedStabilizeXRingHom_C] at h
    simpa only [← MvPolynomial.algebraMap_eq, algebraMap_smul] using h

/-- Inclusion of homogeneous pieces intertwines `gradedSimplyBlockedStabilizeXChainMap` with
`GridDiagram.simplyBlockedStabilizeXMap`. -/
@[simp]
theorem coe_gradedSimplyBlockedStabilizeXChainMap (g : ℤ × ℤ)
    (c : (G.stabilizeX s).bigradedChainHatPiece R j g) :
    (G.gradedSimplyBlockedStabilizeXChainMap s i R g c : GridChainHat R n i) =
      G.1.simplyBlockedStabilizeXMap s i R c :=
  (rfl)

/-- On homogeneous chains specialized from `GC⁻`, `gradedSimplyBlockedStabilizeXChainMap` agrees
with specializing the unblocked stabilization chain map. -/
theorem gradedSimplyBlockedStabilizeXChainMap_gradedSimplyBlockedSpecialization (g : ℤ × ℤ)
    (c : (G.stabilizeX s).bigradedChainMinusPiece R g) :
    G.gradedSimplyBlockedStabilizeXChainMap s i R g
        ((G.stabilizeX s).gradedSimplyBlockedSpecialization R j g c) =
      G.gradedSimplyBlockedSpecialization R i g
        ⟨G.1.stabilizeXChainMap s R c, by
          rw [GridDiagram.stabilizeXChainMap_apply]
          exact G.stabilizeXCoefficientFormula_mem_bigradedChainMinusPiece s R c.2⟩ := by
  apply Subtype.ext
  rw [coe_gradedSimplyBlockedStabilizeXChainMap, coe_gradedSimplyBlockedSpecialization,
    coe_gradedSimplyBlockedSpecialization]
  exact G.1.simplyBlockedStabilizeXMap_simplyBlockedSpecialization s i R c.1

end CommRing

section CharTwo

variable (R : Type*) [CommRing R] [CharP R 2]

/-- In characteristic two, the homogeneous piece maps of the specialized stabilization comparison
intertwine the graded differentials at every Maslov and Alexander degree. -/
theorem gradedSimplyBlockedStabilizeXChainMap_differential (a m : ℤ)
    (c : (G.stabilizeX s).bigradedChainHatPiece R j (m + 1, a)) :
    G.gradedSimplyBlockedStabilizeXChainMap s i R (m, a)
        ((G.stabilizeX s).gradedSimplyBlockedDifferential R j a m c) =
      G.gradedSimplyBlockedDifferential R i a m
        (G.gradedSimplyBlockedStabilizeXChainMap s i R (m + 1, a) c) := by
  apply Subtype.ext
  rw [coe_gradedSimplyBlockedStabilizeXChainMap, coe_gradedSimplyBlockedDifferential,
    coe_gradedSimplyBlockedDifferential, coe_gradedSimplyBlockedStabilizeXChainMap]
  exact G.1.simplyBlockedStabilizeXMap_simplyBlockedDifferential s i R c.1

/-- The specialized `X`-stabilization comparison as a chain map of Maslov-indexed complexes of
`R`-modules in Alexander degree `a`. -/
noncomputable def gradedSimplyBlockedStabilizeXMap (a : ℤ) :
    (G.stabilizeX s).gradedSimplyBlockedComplex R j a ⟶
      G.gradedSimplyBlockedComplex R i a :=
  ChainComplex.ofHom
    (fun m => eqToHom ((G.stabilizeX s).gradedSimplyBlockedComplex_X R j a m) ≫
      ModuleCat.ofHom (G.gradedSimplyBlockedStabilizeXChainMap s i R (m, a)) ≫
        eqToHom (G.gradedSimplyBlockedComplex_X R i a m).symm)
    (fun m => by
      rw [gradedSimplyBlockedComplex_d, gradedSimplyBlockedComplex_d]
      apply (cancel_epi
        (eqToHom ((G.stabilizeX s).gradedSimplyBlockedComplex_X R j a (m + 1)).symm)).mp
      apply (cancel_mono (eqToHom (G.gradedSimplyBlockedComplex_X R i a m))).mp
      simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp,
        Category.comp_id, eqToHom_trans]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro c
      exact (G.gradedSimplyBlockedStabilizeXChainMap_differential s i R a m c).symm)

/-- The degree-`m` component of `gradedSimplyBlockedStabilizeXMap` is the homogeneous piece map
`gradedSimplyBlockedStabilizeXChainMap` in bidegree `(m, a)`, up to the object identifications of
the graded complexes. -/
@[simp]
theorem gradedSimplyBlockedStabilizeXMap_f (a m : ℤ) :
    (G.gradedSimplyBlockedStabilizeXMap s i R a).f m =
      eqToHom ((G.stabilizeX s).gradedSimplyBlockedComplex_X R j a m) ≫
        ModuleCat.ofHom (G.gradedSimplyBlockedStabilizeXChainMap s i R (m, a)) ≫
          eqToHom (G.gradedSimplyBlockedComplex_X R i a m).symm :=
  (rfl)

end CharTwo

end TauCeti.OddComponentGridDiagram
