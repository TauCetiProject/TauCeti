/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Homology.Commutation.Basic
public import TauCeti.KnotTheory.Grid.Homology.Tau

/-!
# Commutation maps with a homotopy inverse up to `U ^ k`, and the invariant `τ`

Let `C` be a column turn at the columns `a = C.column` and `b = finRotate n a` of a knot grid `G`,
and let `G' = G.swapColumns a b`. Write `Φ : GC⁻(G) → GC⁻(G')` for the commutation map of `C`
and `Ψ : GC⁻(G') → GC⁻(G)` for the commutation map of `G'` turning at the same columns in
another row `t`; the target of `Ψ` is the complex of `G'.swapColumns a b`, which is `G`.

Suppose `ΨΦ` is chain homotopic to multiplication by a polynomial `p` with `p(U, …, U) = U ^ k`.
Since `ΨΦ` then acts on `GH⁻(G)` as `p`
(`GridDiagram.unblockedHomologyClass_commutationMap_withTurnRow_commutationMap`), the induced
`K[U]`-linear maps `Φ_*` and `Ψ_*` satisfy `Ψ_* ∘ Φ_* = U ^ k`. So `Φ_*` reflects torsion,
`GH⁻(G')` is not torsion if `GH⁻(G)` is not
(`GridDiagram.IsKnot.not_isTorsion_swapColumns_of_homotopy`), and the comparison lemma
`GridDiagram.IsKnot.tau_le_tau_sub_of_comp_eq_X_pow_smul` bounds `τ(G')` by `τ(G)` minus the
Alexander degree of `Φ` (`GridDiagram.IsKnot.tau_swapColumns_le_of_homotopy`). The crossing change
inequality, in `CrossingChange/Tau.lean`, applies this in both directions.

## Main results

* `TauCeti.GridDiagram.IsKnot.not_isTorsion_swapColumns_of_homotopy`: for a knot grid and
  `ΨΦ ≃ p` with `p(U, …, U) = U ^ k`, `GH⁻(G')` is not torsion when `GH⁻(G)` is not.
* `TauCeti.GridDiagram.IsKnot.tau_swapColumns_le_of_homotopy`: in that case `τ(G')` is at most
  `τ(G)` minus the Alexander degree of `Φ`.

## References

* P. Ozsváth, A. Stipsicz, Z. Szabó, *Grid Homology for Knots and Links*, AMS Mathematical Surveys
  and Monographs 208, 2015, Sections 6.1 and 6.2: maps between grid complexes and the resulting
  inequalities for `τ`.
-/

public section

open MvPolynomial

namespace TauCeti

namespace GridDiagram

namespace IsKnot

variable {n : ℕ} {G : GridDiagram n} (hG : G.IsKnot) (K : Type*) [CommRing K] [CharP K 2]
  (C : ColumnTurn n) (t : Fin n)

local notation "a" => C.column
local notation "b" => finRotate n C.column
local notation "G'" => G.swapColumns a b

/-- The identity of `GH⁻` as a `K[U]`-linear equivalence between two equal knot grids. -/
private noncomputable def linearEquivOfEq {G₁ : GridDiagram n} (h₁ : G₁.IsKnot) (h : G₁ = G) :
    letI := h₁.unblockedHomologyModule K
    letI := hG.unblockedHomologyModule K
    G₁.unblockedHomology K ≃ₗ[Polynomial K] G.unblockedHomology K := by
  subst h
  letI := hG.unblockedHomologyModule K
  exact LinearEquiv.refl _ _

/-- The identity of two equal knot grids sends the class of a cycle to the class of the same
chain. -/
private theorem linearEquivOfEq_unblockedHomologyClass {G₁ : GridDiagram n} (h₁ : G₁.IsKnot)
    (h : G₁ = G) {z : GridChainMinus K n} (hz : z ∈ LinearMap.ker (G₁.unblockedDifferential K))
    (hz' : z ∈ LinearMap.ker (G.unblockedDifferential K)) :
    hG.linearEquivOfEq K h₁ h (G₁.unblockedHomologyClass K ⟨z, hz⟩) =
      G.unblockedHomologyClass K ⟨z, hz'⟩ := by
  subst h
  rfl

/-- The `K[U]`-linear map `GH⁻(G') → GH⁻(G)` induced by the commutation map back, turning at the
columns of `C` in row `t`. Its natural target is `GH⁻` of `G'.swapColumns a b`, which is read as
`GH⁻(G)` through the identity of the two diagrams. -/
private noncomputable def returnLinearMap :
    letI := (hG.swapColumns a b).unblockedHomologyModule K
    letI := hG.unblockedHomologyModule K
    (G').unblockedHomology K →ₗ[Polynomial K] G.unblockedHomology K :=
  letI := (hG.swapColumns a b).unblockedHomologyModule K
  letI := ((hG.swapColumns a b).swapColumns a b).unblockedHomologyModule K
  letI := hG.unblockedHomologyModule K
  (hG.linearEquivOfEq K ((hG.swapColumns a b).swapColumns a b)
      (swapColumns_swapColumns ..)).toLinearMap ∘ₗ
    (hG.swapColumns a b).unblockedHomologyCommutationLinearMap K (C.withTurnRow t)

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
  simp only [returnLinearMap, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    unblockedHomologyCommutationLinearMap_apply,
    unblockedHomologyCommutationMap_unblockedHomologyClass]
  exact linearEquivOfEq_unblockedHomologyClass ..

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

end IsKnot

end GridDiagram

end TauCeti
