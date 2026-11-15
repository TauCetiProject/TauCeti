/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.GradedModule.Coarsen
public import TauCeti.KnotTheory.Grid.Homology.Alexander
public import TauCeti.KnotTheory.Grid.Homology.Bigraded.Basic

/-!
# Coarsening the bigrading of `GH⁻` to the Alexander grading

For a grid diagram with an odd number of link components, projecting bidegrees `(m, a)` onto
their second coordinate `a` coarsens the `(O-Maslov, Alexander)` bigrading of `GC⁻` to its
Alexander grading (`coarsen_bigradedChainMinusGrading_snd`). Over a commutative ring of
characteristic two, the same projection coarsens the induced bigrading on unblocked grid homology
`GH⁻` to `alexanderUnblockedHomologyGrading` (`coarsen_bigradedUnblockedHomologyGrading_snd`), so
each Alexander piece of `GH⁻` is the sum of its Maslov subpieces
(`iSup_bigradedUnblockedHomologyPiece_eq_alexanderUnblockedHomologyGrading_piece`).

## References

Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Sections 4.3 and 4.6.
-/

public section

open MvPolynomial

namespace TauCeti.OddComponentGridDiagram

variable {n : ℕ} (G : OddComponentGridDiagram n) (R : Type*)

section Chain

variable [CommSemiring R]

/-- Coarsening the Maslov--Alexander chain pieces along `Prod.snd` recovers the Alexander chain
pieces. -/
theorem coarsenGrading_bigradedChainMinusPiece_snd :
    coarsenGrading (G.bigradedChainMinusPiece R) Prod.snd = G.alexanderChainMinusPiece R := by
  classical
  funext a
  refine le_antisymm (coarsenGrading_le_iff.mpr ?_) fun c hc ↦ ?_
  · rintro ⟨m, b⟩ (rfl : b = a)
    exact G.bigradedChainMinusPiece_le_alexanderChainMinusPiece R m b
  · induction c using Finsupp.induction with
    | zero => exact Submodule.zero_mem _
    | single_add x p c hx _ ih =>
      have hxp : ∀ e ∈ p.support, G.alexanderℤ x - (e.degree : ℤ) = a := by
        intro e he
        refine (G.mem_alexanderChainMinusPiece.mp hc) x e ?_
        rwa [Finsupp.add_apply, Finsupp.single_eq_same, Finsupp.notMem_support_iff.mp hx, add_zero]
      have hc' : c ∈ G.alexanderChainMinusPiece R a := by
        rw [mem_alexanderChainMinusPiece]
        intro y e he
        have hyx : x ≠ y := by
          rintro rfl
          exact hx (Finsupp.mem_support_iff.mpr fun h0 ↦ by simp [h0] at he)
        refine (G.mem_alexanderChainMinusPiece.mp hc) y e ?_
        simpa [Finsupp.single_apply, hyx] using he
      refine Submodule.add_mem _ ?_ (ih hc')
      have hp : (Finsupp.single x p : GridChainMinus R n) =
          ∑ e ∈ p.support, Finsupp.single x (monomial e (p.coeff e)) := by
        conv_lhs => rw [MvPolynomial.as_sum p]
        exact map_sum (Finsupp.singleAddHom x) _ _
      rw [hp]
      refine Submodule.sum_mem _ fun e he ↦ ?_
      have hmem := mem_coarsenGrading_of_mem Prod.snd
        (G.single_monomial_mem_bigradedChainMinusPiece R x e (p.coeff e))
      rwa [monomialBidegree_snd, hxp e he] at hmem

/-- Each Alexander piece of `GC⁻` is the supremum of the Maslov--Alexander pieces with that
Alexander degree. -/
theorem iSup_bigradedChainMinusPiece_eq_alexanderChainMinusPiece (a : ℤ) :
    ⨆ m : ℤ, G.bigradedChainMinusPiece R (m, a) = G.alexanderChainMinusPiece R a := by
  rw [← G.coarsenGrading_bigradedChainMinusPiece_snd R]
  refine le_antisymm
    (iSup_le fun m ↦ le_coarsenGrading (G.bigradedChainMinusPiece R) Prod.snd (m, a))
    (coarsenGrading_le_iff.mpr ?_)
  rintro ⟨m, b⟩ (rfl : b = a)
  exact le_iSup (fun m ↦ G.bigradedChainMinusPiece R (m, b)) m

end Chain

section ChainRing

variable [CommRing R]

/-- Projecting bidegrees to their Alexander coordinate coarsens the internal bigrading of `GC⁻`
to its internal Alexander grading. -/
@[simp]
theorem coarsen_bigradedChainMinusGrading_snd :
    (G.bigradedChainMinusGrading R).coarsen Prod.snd = G.alexanderChainMinusGrading R := by
  refine InternalGrading.ext fun a ↦ ?_
  have hp : (G.bigradedChainMinusGrading R).piece = G.bigradedChainMinusPiece R :=
    funext (G.bigradedChainMinusGrading_piece R)
  rw [InternalGrading.coarsen_piece, hp, alexanderChainMinusGrading_piece,
    G.coarsenGrading_bigradedChainMinusPiece_snd R]

end ChainRing

section Homology

variable [CommRing R] [CharP R 2]

/-- Every Maslov--Alexander piece of `GH⁻` lies in the Alexander piece of its second
coordinate. -/
theorem bigradedUnblockedHomologyPiece_le_alexanderUnblockedHomologyGrading_piece (m a : ℤ) :
    G.bigradedUnblockedHomologyPiece R (m, a) ≤
      (G.alexanderUnblockedHomologyGrading R).piece a := by
  intro y hy
  obtain ⟨z, hz, rfl⟩ := (G.mem_bigradedUnblockedHomologyPiece_iff R).mp hy
  rw [G.mem_alexanderUnblockedHomologyGrading_piece_iff R, G.mem_alexanderHomologyGrading_piece_iff]
  exact ⟨z, G.bigradedChainMinusPiece_le_alexanderChainMinusPiece R m a hz,
    (G.1.unblockedHomologyIso_hom_unblockedHomologyClass R z).symm⟩

/-- Projecting bidegrees to their Alexander coordinate coarsens the internal bigrading of `GH⁻`
to its internal Alexander grading. -/
@[simp]
theorem coarsen_bigradedUnblockedHomologyGrading_snd :
    (G.bigradedUnblockedHomologyGrading R).coarsen Prod.snd =
      G.alexanderUnblockedHomologyGrading R := by
  let 𝒞 := (G.bigradedUnblockedHomologyGrading R).coarsen Prod.snd
  let 𝒜 := G.alexanderUnblockedHomologyGrading R
  have hle : ∀ b, 𝒞.piece b ≤ 𝒜.piece b := by
    intro b
    rw [InternalGrading.coarsen_piece]
    refine coarsenGrading_le_iff.mpr ?_
    rintro ⟨m, c⟩ (rfl : c = b)
    rw [bigradedUnblockedHomologyGrading_piece]
    exact G.bigradedUnblockedHomologyPiece_le_alexanderUnblockedHomologyGrading_piece R m c
  refine InternalGrading.ext fun a ↦ le_antisymm (hle a) fun y hy ↦ ?_
  classical
  -- Both `𝒞` and `𝒜` are internal direct sums with `𝒞.piece b ≤ 𝒜.piece b`, so projecting `y`'s
  -- `𝒞`-decomposition to degree `a` in `𝒜` kills every component outside degree `a`.
  have hy_eq : (DirectSum.decompose 𝒜.piece y a : G.1.unblockedHomology R) = y :=
    DirectSum.decompose_of_mem_same 𝒜.piece hy
  conv_lhs at hy_eq => rw [← DirectSum.sum_support_decompose 𝒞.piece y]
  rw [DirectSum.decompose_sum, DirectSum.sum_apply, Submodule.coe_sum,
    Finset.sum_eq_single a
      (fun b _ hb ↦ DirectSum.decompose_of_mem_ne 𝒜.piece
        (hle b (DirectSum.decompose 𝒞.piece y b).2) hb)
      (fun ha ↦ by simp [DFinsupp.notMem_support_iff.mp ha]),
    DirectSum.decompose_of_mem_same 𝒜.piece (hle a (DirectSum.decompose 𝒞.piece y a).2)] at hy_eq
  exact hy_eq ▸ (DirectSum.decompose 𝒞.piece y a).2

/-- Coarsening the Maslov--Alexander homology pieces along `Prod.snd` recovers the Alexander
homology pieces. -/
theorem coarsenGrading_bigradedUnblockedHomologyPiece_snd :
    coarsenGrading (G.bigradedUnblockedHomologyPiece R) Prod.snd =
      (G.alexanderUnblockedHomologyGrading R).piece := by
  have hp : (G.bigradedUnblockedHomologyGrading R).piece = G.bigradedUnblockedHomologyPiece R :=
    funext (G.bigradedUnblockedHomologyGrading_piece R)
  simpa only [InternalGrading.coarsen_piece, hp] using
    congrArg InternalGrading.piece (G.coarsen_bigradedUnblockedHomologyGrading_snd R)

/-- Each Alexander piece of `GH⁻` is the supremum of the Maslov--Alexander pieces with that
Alexander degree. -/
theorem iSup_bigradedUnblockedHomologyPiece_eq_alexanderUnblockedHomologyGrading_piece (a : ℤ) :
    ⨆ m : ℤ, G.bigradedUnblockedHomologyPiece R (m, a) =
      (G.alexanderUnblockedHomologyGrading R).piece a := by
  rw [← G.coarsenGrading_bigradedUnblockedHomologyPiece_snd R]
  refine le_antisymm
    (iSup_le fun m ↦ le_coarsenGrading (G.bigradedUnblockedHomologyPiece R) Prod.snd (m, a))
    (coarsenGrading_le_iff.mpr ?_)
  rintro ⟨m, b⟩ (rfl : b = a)
  exact le_iSup (fun m ↦ G.bigradedUnblockedHomologyPiece R (m, b)) m

end Homology

end TauCeti.OddComponentGridDiagram
