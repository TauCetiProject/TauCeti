/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Stabilization.Grading
public import TauCeti.KnotTheory.Grid.Stabilization.Map.Basic

/-!
# The chain map of an `X`-stabilization preserves the bigrading

Let `G` be a grid diagram of size `n` with an odd number of link components, let `s` be a column,
and let `G' = G.stabilizeX s.castSucc (G.X s).castSucc s` be the stabilization splitting the
`X`-marking of column `s`. Adding the center of the new block to a state of `G` lowers its
doubled Alexander grading by two (`GridDiagram.alexanderTwoℤ_stabilizeX_insertPoint`), so the
parity criterion `GridDiagram.even_alexanderTwoℤ_iff` shows that `G'` again has an odd number of
components (`OddComponentGridDiagram.stabilizeX`, in `Stabilization/Grading.lean`). Both
unblocked complexes `GC⁻(G')` and `GC⁻(G)` therefore carry the (`O`-Maslov, Alexander) bigrading
of `Grading/UnblockedChain.lean`.

This file proves that the stabilization chain map `GC⁻(G') ⟶ GC⁻(G)`
(`GridDiagram.stabilizeXMap`) has bidegree `(0, 0)`. On a chain `c` it is `H_I^N` applied to the
off-center part of `c`, followed by the renaming `V_j ↦ V_{s.predAbove j}` that merges the two
variables of the new block (`GridDiagram.stabilizeXMap_f_apply`). A monomial `V^e · y` of `c`, for
`y` an off-center state, therefore contributes terms `V^{e + O(r)} · x` with the exponent renamed,
one for each rectangle `r` of the `X₂`-homotopy from `y` to the state `x'` obtained by inserting the
center of the new block into `x`. Renaming variables does not change the total degree, and each
such term has the bigrading of `V^e · y` (`GridDiagram.maslovOℤ_stabilizeX_eq_of_isEmpty` and
`GridDiagram.alexander_stabilizeX_eq_of_mem_XHomotopyRectangles`).

Since `stabilizeXMap` is a quasi-isomorphism (`GridDiagram.quasiIso_stabilizeXMap`), this is the
chain-level input for identifying the bigraded homologies `GH⁻(G')` and `GH⁻(G)`, and so the
invariants `τ` of a knot grid and of this stabilization.

## Main results

* `TauCeti.OddComponentGridDiagram.stabilizeXMap_mem_bigradedChainMinusPiece`: the stabilization
  chain map preserves the bigrading of `GC⁻`.
* `TauCeti.OddComponentGridDiagram.stabilizeXMap_mem_alexanderChainMinusPiece`: it preserves the
  Alexander grading of `GC⁻`.

## References

This is the statement that the stabilization quasi-isomorphism is bigraded, in the proof of
stabilization invariance in Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*,
Section 5.2, and Manolescu--Ozsváth--Szabó--Thurston, *On combinatorial link Floer homology*,
Section 3.2.
-/

public section

open CategoryTheory MvPolynomial

namespace TauCeti

namespace OddComponentGridDiagram

variable {n : ℕ} (G : OddComponentGridDiagram n) (s : Fin n)

variable (R : Type*) [CommRing R] [CharP R 2]

local notation "A" => MvPolynomial (Fin n) R
local notation "S" => MvPolynomial (Fin (n + 1)) R

/-- Every monomial `V^e · x` of the image of a chain `c` under the stabilization map has the
bidegree of some monomial `V^d · y` of `c`. -/
private theorem exists_monomialBidegree_eq_of_mem_support {c : GridChainMinus R (n + 1)}
    {x : GridState n} {e : Fin n →₀ ℕ}
    (he : e ∈ (((ModuleCat.restrictScalars
        (↑(rename (R := R) (Fin.succAbove (Fin.castSucc s))) : A →+* S)).map
          (eqToHom
            ((G.1.stabilizeX s.castSucc (G.1.X s).castSucc s).unblockedComplex_X R ()).symm) ≫
        (G.1.stabilizeXMap s R).f () ≫ eqToHom (G.1.unblockedComplex_X R ())).hom c x).support) :
    ∃ y : GridState (n + 1), ∃ d ∈ (c y).support,
      G.monomialBidegree x e = (G.stabilizeX s).monomialBidegree y d := by
  classical
  rw [GridDiagram.stabilizeXMap_f_apply, Finsupp.mapRange_apply] at he
  -- The monomial `e` is the renaming of a monomial `u` of the coefficient before renaming.
  obtain ⟨u, hu, rfl⟩ : ∃ u ∈ (G.1.stabilizeXOffCenterToCenter s R
      (G.1.stabilizeXOffCenterProjection s R c) x).support, u.mapDomain s.predAbove = e := by
    by_contra! h
    exact (MvPolynomial.mem_support_iff.mp he) (coeff_rename_eq_zero _ _ _ fun u hu =>
      MvPolynomial.notMem_support_iff.mp fun hu' => h u hu' hu)
  -- The monomial `u` comes from a monomial `d` of `c` at an off-center state `y` and a rectangle
  -- `r` of the `X₂`-homotopy from `y` to the center state of `x`.
  rw [GridDiagram.stabilizeXOffCenterToCenter_apply, Finsupp.sum] at hu
  obtain ⟨y, -, huy⟩ := Finset.mem_biUnion.mp (MvPolynomial.support_sum hu)
  obtain ⟨d, hd, d', hd', rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul _ _ huy)
  obtain ⟨r, hr, rfl⟩ :=
    GridDiagram.exists_mem_XHomotopyRectangles_of_mem_support_XHomotopyCoefficient _ R hd'
  rw [GridDiagram.stabilizeXOffCenterProjection_apply] at hd
  refine ⟨y.1, d, hd, ?_⟩
  have hM := G.1.maslovOℤ_stabilizeX_eq_of_isEmpty s x
    ((GridDiagram.mem_XHomotopyRectangles _ _ r).mp hr).1
  have hA := G.1.alexander_stabilizeX_eq_of_mem_XHomotopyRectangles s x hr
  rw [← val_stabilizeX, alexander_eq_intCast, G.alexander_eq_intCast] at hA
  have hA' : (G.stabilizeX s).alexanderℤ y.1 = G.alexanderℤ x -
      ((G.stabilizeX s).1.OColumns r.toGridRectangle).card := by
    exact_mod_cast hA
  rw [val_stabilizeX] at hA'
  refine Prod.ext ?_ ?_ <;>
    simp only [monomialBidegree_fst, monomialBidegree_snd, Finsupp.degree_mapDomain, map_add,
      map_sum, Finsupp.degree_single, Finset.sum_const, smul_eq_mul, mul_one, val_stabilizeX] <;>
    push_cast <;> omega

/-- **The stabilization chain map preserves the bigrading.** The chain map `GC⁻(G') ⟶ GC⁻(G)` of
the stabilization splitting the `X`-marking of column `s` sends a chain of `GC⁻(G')` that is
homogeneous of bidegree `g` to a chain of `GC⁻(G)` homogeneous of the same bidegree. -/
theorem stabilizeXMap_mem_bigradedChainMinusPiece {g : ℤ × ℤ} {c : GridChainMinus R (n + 1)}
    (hc : c ∈ (G.stabilizeX s).bigradedChainMinusPiece R g) :
    ((ModuleCat.restrictScalars
        (↑(rename (R := R) (Fin.succAbove (Fin.castSucc s))) : A →+* S)).map
          (eqToHom
            ((G.1.stabilizeX s.castSucc (G.1.X s).castSucc s).unblockedComplex_X R ()).symm) ≫
        (G.1.stabilizeXMap s R).f () ≫ eqToHom (G.1.unblockedComplex_X R ())).hom c ∈
      G.bigradedChainMinusPiece R g := by
  rw [mem_bigradedChainMinusPiece] at hc ⊢
  intro x e he
  obtain ⟨y, d, hd, h⟩ := G.exists_monomialBidegree_eq_of_mem_support s R he
  rw [h, hc y d hd]

/-- **The stabilization chain map preserves the Alexander grading.** The chain map
`GC⁻(G') ⟶ GC⁻(G)` of the stabilization splitting the `X`-marking of column `s` sends a chain of
`GC⁻(G')` of Alexander degree `a` to a chain of `GC⁻(G)` of the same Alexander degree. -/
theorem stabilizeXMap_mem_alexanderChainMinusPiece {a : ℤ} {c : GridChainMinus R (n + 1)}
    (hc : c ∈ (G.stabilizeX s).alexanderChainMinusPiece R a) :
    ((ModuleCat.restrictScalars
        (↑(rename (R := R) (Fin.succAbove (Fin.castSucc s))) : A →+* S)).map
          (eqToHom
            ((G.1.stabilizeX s.castSucc (G.1.X s).castSucc s).unblockedComplex_X R ()).symm) ≫
        (G.1.stabilizeXMap s R).f () ≫ eqToHom (G.1.unblockedComplex_X R ())).hom c ∈
      G.alexanderChainMinusPiece R a := by
  rw [mem_alexanderChainMinusPiece] at hc ⊢
  intro x e he
  obtain ⟨y, d, hd, h⟩ := G.exists_monomialBidegree_eq_of_mem_support s R he
  rw [← monomialBidegree_snd, h, monomialBidegree_snd, hc y d hd]

end OddComponentGridDiagram

end TauCeti
