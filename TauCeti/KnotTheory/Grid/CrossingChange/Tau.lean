/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.CrossingChange.Grading
public import TauCeti.KnotTheory.Grid.Homology.Tau

/-!
# Crossing change maps and the invariant `τ`

Let `C` be a column turn at the columns `a = C.column` and `b = finRotate n a` of a grid diagram
`G`, and let `G' = G.swapColumns a b`. Write `Φ : GC⁻(G) → GC⁻(G')` for the commutation map of
`C` and `Ψ : GC⁻(G') → GC⁻(G)` for the commutation map of `G'` turning at the same columns in
another row `t`; the target of `Ψ` is the complex of `G'.swapColumns a b`, which is `G`. This file
turns a chain homotopy `∂H + H∂ = p + ΨΦ` into statements on unblocked grid homology and on `τ`.

On `GH⁻(G)`, over a ring of characteristic two, `ΨΦ` then acts as multiplication by `p`
(`GridDiagram.unblockedHomologyClass_commutationMap_withTurnRow_commutationMap`). For a knot grid
and a polynomial `p` with `p(U, …, U) = U ^ k`, the induced `K[U]`-linear maps `Φ_*` and `Ψ_*`
satisfy `Ψ_* ∘ Φ_* = U ^ k`. So `Φ_*` reflects torsion, `GH⁻(G')` is not torsion if `GH⁻(G)` is not
(`GridDiagram.IsKnot.not_isTorsion_swapColumns_of_homotopy`), and the comparison lemma
`GridDiagram.IsKnot.tau_le_tau_sub_of_comp_eq_X_pow_smul` bounds `τ(G')` by `τ(G)` minus the
Alexander degree of `Φ` (`GridDiagram.IsKnot.tau_swapColumns_le_of_homotopy`).

The main application is to a crossing change. If the segments of the columns `a` and `b`
interleave with `O_a` on the arc of column `b`, the crossing change maps are the commutation map
`Φ` turning in the row of `O_a`, of Alexander degree `0`, and the commutation map `Ψ` of `G'`
turning in the row of `X_b`, of Alexander degree `-1`
(`GridDiagram.commutationBidegree_eq_zero_of_mem_columnArc` and
`GridDiagram.commutationBidegree_eq_of_notMem_columnArc`). Ozsváth, Stipsicz and Szabó show that
both composites are chain homotopic to multiplication by a variable, `ΨΦ` to `V_b` and `ΦΨ` to
`V_a`, with hexagon-counting maps such as `GridDiagram.crossingChangeHomotopy` as the homotopies.
Given two such homotopies, `τ(G) - 1 ≤ τ(G') ≤ τ(G)`
(`GridDiagram.IsKnot.tau_swapColumns_mem_Icc_of_homotopy`). No assumption that `GH⁻` is non-torsion
is needed here: the two composites show that `GH⁻(G)` and `GH⁻(G')` are torsion together, and then
both invariants vanish. This is the inequality from which the bound of `|τ|` by the unknotting
number follows.

## Main results

* `TauCeti.GridDiagram.unblockedHomologyClass_commutationMap_withTurnRow_commutationMap`: if
  `ΨΦ` is chain homotopic to multiplication by `p`, it acts on `GH⁻(G)` as `p`.
* `TauCeti.GridDiagram.IsKnot.not_isTorsion_swapColumns_of_homotopy`: then, for a knot grid and
  `p(U, …, U) = U ^ k`, `GH⁻(G')` is not torsion when `GH⁻(G)` is not.
* `TauCeti.GridDiagram.IsKnot.tau_swapColumns_le_of_homotopy`: in that case `τ(G')` is at most
  `τ(G)` minus the Alexander degree of `Φ`.
* `TauCeti.GridDiagram.IsKnot.tau_swapColumns_mem_Icc_of_homotopy`: **the crossing change
  inequality**, `τ(G) - 1 ≤ τ(G') ≤ τ(G)` across a crossing change whose two composites are chain
  homotopic to multiplication by the variables of the exchanged columns.

## References

* P. Ozsváth, A. Stipsicz, Z. Szabó, *Grid Homology for Knots and Links*, AMS Mathematical Surveys
  and Monographs 208, 2015, Sections 6.1 and 6.2: the crossing change maps, their composites, and
  the resulting inequality for `τ`.
* S. Sarkar, *Grid diagrams and the Ozsváth--Szabó tau-invariant*, Math. Res. Lett. 18 (2011),
  arXiv:1011.5265: the crossing change inequality for `τ` from grid diagrams.
-/

public section

open MvPolynomial

namespace TauCeti

namespace GridDiagram

section Homology

variable {n : ℕ} (G : GridDiagram n) (R : Type*) [CommRing R] [CharP R 2] (C : ColumnTurn n)
  (t : Fin n)

local notation "a" => C.column
local notation "b" => finRotate n C.column
local notation "G'" => G.swapColumns a b

/-- The commutation map of a column turn followed by the commutation map back, turning at the same
columns in any row, sends cycles of `GC⁻(G)` to cycles of `GC⁻(G)`. -/
theorem commutationMap_withTurnRow_commutationMap_mem_ker {z : GridChainMinus R n}
    (hz : z ∈ LinearMap.ker (G.unblockedDifferential R)) :
    (G').commutationMap R (C.withTurnRow t) (G.commutationMap R C z) ∈
      LinearMap.ker (G.unblockedDifferential R) := by
  simpa only [ColumnTurn.withTurnRow_column, swapColumns_swapColumns] using
    (G').commutationMap_mem_ker_unblockedDifferential R (C.withTurnRow t)
      (G.commutationMap_mem_ker_unblockedDifferential R C hz)

/-- **The return composite on homology.** Let `Φ` be the commutation map of the column turn `C`
and `Ψ` the commutation map back, turning at the same columns in row `t`. If `ΨΦ` is chain
homotopic to multiplication by a polynomial `p`, that is `∂H + H∂ = p + ΨΦ` over a ring of
characteristic two, then `ΨΦ` sends the class in `GH⁻(G)` of every cycle `z` to `p` times that
class. -/
theorem unblockedHomologyClass_commutationMap_withTurnRow_commutationMap
    (H : GridChainMinus R n →ₗ[MvPolynomial (Fin n) R] GridChainMinus R n)
    (p : MvPolynomial (Fin n) R)
    (hH : ∀ c, G.unblockedDifferential R (H c) + H (G.unblockedDifferential R c) =
      p • c + (G').commutationMap R (C.withTurnRow t) (G.commutationMap R C c))
    (z : LinearMap.ker (G.unblockedDifferential R)) :
    G.unblockedHomologyClass R
        ⟨_, G.commutationMap_withTurnRow_commutationMap_mem_ker R C t z.2⟩ =
      p • G.unblockedHomologyClass R z := by
  rw [← map_smul, ← sub_eq_zero, ← map_sub, unblockedHomologyClass_eq_zero_iff]
  refine ⟨H z, ?_⟩
  have h := hH z
  rw [LinearMap.mem_ker.mp z.2, map_zero, add_zero] at h
  rw [h, Submodule.coe_sub, Submodule.coe_smul, sub_eq_add_neg, ← neg_smul, CharTwo.neg_eq,
    add_comm]

end Homology

namespace IsKnot

variable {n : ℕ} {G : GridDiagram n} (hG : G.IsKnot) (K : Type*) [CommRing K] [CharP K 2]
  (C : ColumnTurn n) (t : Fin n)

local notation "a" => C.column
local notation "b" => finRotate n C.column
local notation "G'" => G.swapColumns a b

/-- The `K[U]`-linear map `GH⁻(G') → GH⁻(G)` induced by the commutation map back, turning at the
columns of `C` in row `t`. Its natural target is `GH⁻` of `G'.swapColumns a b`, which is read as
`GH⁻(G)` through the identity of the two diagrams. -/
private noncomputable def returnLinearMap :
    letI := (hG.swapColumns a b).unblockedHomologyModule K
    letI := hG.unblockedHomologyModule K
    (G').unblockedHomology K →ₗ[Polynomial K] G.unblockedHomology K := by
  letI := (hG.swapColumns a b).unblockedHomologyModule K
  letI := hG.unblockedHomologyModule K
  have : Nonempty (Fin n) := ⟨⟨0, Nat.pos_of_ne_zero hG.ne_zero⟩⟩
  let e := ((G').swapColumns a b).unblockedHomologyEquivOfIntertwining K G
    (LinearEquiv.refl _ _) fun c => by
      simp only [LinearEquiv.refl_apply, swapColumns_swapColumns]
  exact
    { toFun := fun y => e ((G').unblockedHomologyCommutationMap K (C.withTurnRow t) y)
      map_add' := fun y y' => by simp only [map_add]
      map_smul' := fun q y => by
        obtain ⟨p, rfl⟩ := aeval_const_X_surjective (Fin n) K q
        rw [(hG.swapColumns a b).aeval_smul_unblockedHomology, LinearMap.map_smulₛₗ,
          LinearEquiv.map_smulₛₗ, ← hG.aeval_smul_unblockedHomology]
        simp only [AlgEquiv.toRingEquiv_toRingHom, RingHom.coe_coe, renameEquiv_apply,
          aeval_rename, Function.comp_def, RingHom.id_apply] }

variable {K C t} in
/-- If `ΨΦ` is chain homotopic to multiplication by a polynomial `p` with `p(U, …, U) = U ^ k`,
the return map is a left inverse of `Φ_*` up to `U ^ k`. -/
private theorem returnLinearMap_unblockedHomologyCommutationMap
    {H : GridChainMinus K n →ₗ[MvPolynomial (Fin n) K] GridChainMinus K n}
    {p : MvPolynomial (Fin n) K} {k : ℕ}
    (hp : aeval (fun _ => (Polynomial.X : Polynomial K)) p = Polynomial.X ^ k)
    (hH : ∀ c, G.unblockedDifferential K (H c) + H (G.unblockedDifferential K c) =
      p • c + (G').commutationMap K (C.withTurnRow t) (G.commutationMap K C c))
    (y : G.unblockedHomology K) :
    letI := hG.unblockedHomologyModule K
    hG.returnLinearMap K C t (hG.unblockedHomologyCommutationLinearMap K C y) =
      (Polynomial.X ^ k : Polynomial K) • y := by
  let _ := hG.unblockedHomologyModule K
  obtain ⟨z, rfl⟩ := G.unblockedHomologyClass_surjective K y
  rw [unblockedHomologyCommutationLinearMap_apply, ← hp, hG.aeval_smul_unblockedHomology,
    ← G.unblockedHomologyClass_commutationMap_withTurnRow_commutationMap K C t H p hH z]
  simp only [returnLinearMap, LinearMap.coe_mk, AddHom.coe_mk,
    unblockedHomologyCommutationMap_unblockedHomologyClass]
  exact unblockedHomologyEquivOfIntertwining_unblockedHomologyClass ..

/-- If `ΨΦ` is chain homotopic to multiplication by a polynomial `p` with `p(U, …, U) = U ^ k`,
then `GH⁻(G')` is not a torsion `K[U]`-module as soon as `GH⁻(G)` is not: `Φ_*` reflects torsion,
since it has a left inverse up to `U ^ k`. -/
theorem not_isTorsion_swapColumns_of_homotopy
    (H : GridChainMinus K n →ₗ[MvPolynomial (Fin n) K] GridChainMinus K n)
    {p : MvPolynomial (Fin n) K} {k : ℕ}
    (hp : aeval (fun _ => (Polynomial.X : Polynomial K)) p = Polynomial.X ^ k)
    (hH : ∀ c, G.unblockedDifferential K (H c) + H (G.unblockedDifferential K c) =
      p • c + (G').commutationMap K (C.withTurnRow t) (G.commutationMap K C c)) :
    letI := hG.unblockedHomologyModule K
    letI := (hG.swapColumns a b).unblockedHomologyModule K
    ¬Module.IsTorsion (Polynomial K) (G.unblockedHomology K) →
      ¬Module.IsTorsion (Polynomial K) ((G').unblockedHomology K) := by
  let _ := hG.unblockedHomologyModule K
  let _ := (hG.swapColumns a b).unblockedHomologyModule K
  intro hT hT'
  refine hT fun y => (Submodule.mem_torsion_iff y).mp ?_
  exact
    Submodule.comap_torsion_le_of_comp_eq_smul (pow_mem Polynomial.X_mem_nonZeroDivisors k)
      (f := hG.unblockedHomologyCommutationLinearMap K C) (g := hG.returnLinearMap K C t)
      (hG.returnLinearMap_unblockedHomologyCommutationMap hp hH)
      (Submodule.mem_comap.mpr ((Submodule.mem_torsion_iff _).mpr (@hT' _)))

/-- **Comparison of `τ` along a column turn with a homotopy inverse up to `U ^ k`.** If `ΨΦ` is
chain homotopic to multiplication by a polynomial `p` with `p(U, …, U) = U ^ k` and `GH⁻(G)` is not
torsion, then `τ(G')` is at most `τ(G)` minus the Alexander degree of the commutation map `Φ`. -/
theorem tau_swapColumns_le_of_homotopy [IsNoetherianRing K]
    (H : GridChainMinus K n →ₗ[MvPolynomial (Fin n) K] GridChainMinus K n)
    {p : MvPolynomial (Fin n) K} {k : ℕ}
    (hp : aeval (fun _ => (Polynomial.X : Polynomial K)) p = Polynomial.X ^ k)
    (hH : ∀ c, G.unblockedDifferential K (H c) + H (G.unblockedDifferential K c) =
      p • c + (G').commutationMap K (C.withTurnRow t) (G.commutationMap K C c)) :
    letI := hG.unblockedHomologyModule K
    ¬Module.IsTorsion (Polynomial K) (G.unblockedHomology K) →
      (hG.swapColumns a b).tau K ≤ hG.tau K - (G.commutationBidegree C).2 :=
  hG.tau_le_tau_sub_of_comp_eq_X_pow_smul K (hG.swapColumns a b) k _ (hG.returnLinearMap K C t)
    (hG.isHomogeneous_unblockedHomologyCommutationLinearMap K C)
    (hG.returnLinearMap_unblockedHomologyCommutationMap hp hH)

/-- Exchanging the same two columns twice returns the original knot grid, with the same `τ`. -/
private theorem tau_swapColumns_swapColumns :
    ((hG.swapColumns a b).swapColumns a b).tau K = hG.tau K := by
  have key : ∀ {G₁ : GridDiagram n} (h₁ : G₁.IsKnot), G₁ = G → h₁.tau K = hG.tau K := by
    rintro _ _ rfl
    rfl
  exact key _ (swapColumns_swapColumns ..)

/-- Exchanging the same two columns twice returns the original knot grid, whose `GH⁻` is torsion
exactly when it was before. -/
private theorem isTorsion_swapColumns_swapColumns_iff :
    letI := hG.unblockedHomologyModule K
    letI := ((hG.swapColumns a b).swapColumns a b).unblockedHomologyModule K
    Module.IsTorsion (Polynomial K) (((G').swapColumns a b).unblockedHomology K) ↔
      Module.IsTorsion (Polynomial K) (G.unblockedHomology K) := by
  have key : ∀ {G₁ : GridDiagram n} (h₁ : G₁.IsKnot), G₁ = G →
      (letI := hG.unblockedHomologyModule K
       letI := h₁.unblockedHomologyModule K
       Module.IsTorsion (Polynomial K) (G₁.unblockedHomology K) ↔
        Module.IsTorsion (Polynomial K) (G.unblockedHomology K)) := by
    rintro _ _ rfl
    exact Iff.rfl
  exact key _ (swapColumns_swapColumns ..)

variable {K C}

/-- **The crossing change inequality for `τ`.** Let the segments of the columns `a` and
`b = finRotate n a` of a knot grid `G` interleave with `O_a` on the arc of column `b`, and let `C`
turn in the row of `O_a`. Suppose that the crossing change maps, the commutation map `Φ` of `C`
and the commutation map `Ψ` of `G' = G.swapColumns a b` turning in the row of `X_b`, have
composites `ΨΦ` and `ΦΨ` chain homotopic to multiplication by `V_b` and `V_a`. Then
`τ(G) - 1 ≤ τ(G') ≤ τ(G)`. -/
theorem tau_swapColumns_mem_Icc_of_homotopy [IsNoetherianRing K]
    (h : G.ColumnsInterleaving a b) (hO : G.O a ∈ G.columnArc b) (hs : C.turnRow = G.O a)
    (hH : ∃ H : GridChainMinus K n →ₗ[MvPolynomial (Fin n) K] GridChainMinus K n,
      ∀ c, G.unblockedDifferential K (H c) + H (G.unblockedDifferential K c) =
        (MvPolynomial.X b : MvPolynomial (Fin n) K) • c +
          (G').commutationMap K (C.withTurnRow (G.X b)) (G.commutationMap K C c))
    (hH' : ∃ H' : GridChainMinus K n →ₗ[MvPolynomial (Fin n) K] GridChainMinus K n,
      ∀ c, (G').unblockedDifferential K (H' c) + H' ((G').unblockedDifferential K c) =
        (MvPolynomial.X a : MvPolynomial (Fin n) K) • c +
          ((G').swapColumns a b).commutationMap K ((C.withTurnRow (G.X b)).withTurnRow (G.O a))
            ((G').commutationMap K (C.withTurnRow (G.X b)) c)) :
    (hG.swapColumns a b).tau K ∈ Set.Icc (hG.tau K - 1) (hG.tau K) := by
  obtain ⟨H, hH⟩ := hH
  obtain ⟨H', hH'⟩ := hH'
  let _ := hG.unblockedHomologyModule K
  let _ := (hG.swapColumns a b).unblockedHomologyModule K
  let _ := ((hG.swapColumns a b).swapColumns a b).unblockedHomologyModule K
  have hp (c : Fin n) :
      aeval (fun _ => (Polynomial.X : Polynomial K)) (MvPolynomial.X c : MvPolynomial (Fin n) K) =
        Polynomial.X ^ 1 := by
    rw [aeval_X, pow_one]
  -- In `G'` the markings of the exchanged columns appear in the other cyclic order, so the
  -- commutation map back has the bidegree of multiplication by `U`.
  have hΦ := commutationBidegree_eq_zero_of_mem_columnArc C h hO hs
  have hΨ := commutationBidegree_eq_of_notMem_columnArc (G := G') (C.withTurnRow (G.X b))
    (((columnsInterleaving_swapColumns G _ _).mpr h.symm))
    (fun hO' => h.O_swapColumns_mem_columnArc_iff.mp hO' hO)
    (by simp [swapColumns_X, GridState.swapColumns_apply])
  have hΨ' := (hG.swapColumns a b).not_isTorsion_swapColumns_of_homotopy K
    (C.withTurnRow (G.X b)) (G.O a) H' (hp a) hH'
  by_cases hT : Module.IsTorsion (Polynomial K) (G.unblockedHomology K)
  · -- Both homologies are torsion, and both invariants vanish.
    have hT' : Module.IsTorsion (Polynomial K) ((G').unblockedHomology K) := by
      by_contra hT'
      exact (hΨ' hT') ((isTorsion_swapColumns_swapColumns_iff hG K C).mpr hT)
    rw [hG.tau_eq_zero_of_isTorsion K hT, (hG.swapColumns a b).tau_eq_zero_of_isTorsion K hT']
    simp
  · have h₁ := hG.tau_swapColumns_le_of_homotopy K C (G.X b) H (hp b) hH hT
    have h₂ := (hG.swapColumns a b).tau_swapColumns_le_of_homotopy K (C.withTurnRow (G.X b))
      (G.O a) H' (hp a) hH' (hG.not_isTorsion_swapColumns_of_homotopy K C (G.X b) H (hp b) hH hT)
    rw [hΦ, Prod.snd_zero, sub_zero] at h₁
    rw [hΨ, tau_swapColumns_swapColumns hG K C, sub_neg_eq_add] at h₂
    exact ⟨by linarith, h₁⟩

end IsKnot

end GridDiagram

end TauCeti
