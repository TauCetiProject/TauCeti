/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.NormTwoShell.RootPairing
public import TauCeti.RepresentationTheory.Quiver.EulerForm

/-!
# The root system of a quiver with positive definite Tits form

Let `Q` be a finite connected quiver whose Tits form `q` is positive definite. The Gram matrix
of the polarized form `B(d, e) = q(d + e) - q(d) - q(e)` in the simple dimension vectors is the
symmetrized Cartan matrix `2I - (A + Aᵀ)`, `A` the matrix of arrow counts
(`TauCeti.titsPolarForm_single_single`), and `B(d, d) = 2 q(d)`. So the integral vectors `d`
with `q(d) = 1` are the norm-two shell of this matrix, and the root system of the norm-two shell
(`Matrix.PosDef.normTwoShellRootPairing`) makes them the roots of a reduced, crystallographic,
irreducible rational root system on the vertex space `Q → ℚ`. The vertex vectors `eᵢ` form a
base, its Cartan matrix is `2I - (A + Aᵀ)`, and the roots are exactly the nonzero integral
vectors of Tits value one (`TauCeti.exists_rootPairing_titsForm`).

This is the root system behind Gabriel's theorem, by which the dimension vectors of the
indecomposable representations of a Dynkin quiver are the nonnegative integral vectors of Tits
value one: here those vectors are roots of an actual root system, whose base is marked by the
vertices.

## Main results

* `TauCeti.diagramGraph_toMatrix_titsPolarForm`: the diagram of this Gram matrix is the underlying
  graph of `Q`.
* `TauCeti.exists_rootPairing_titsForm`: **the root system of a connected quiver with positive
  definite Tits form**, with the vertex vectors as a base.

## References

* I. N. Bernstein, I. M. Gelfand and V. A. Ponomarev, *Coxeter functors and Gabriel's theorem*,
  Russian Math. Surveys 28 (1973), §2.
* P. Etingof et al., *Introduction to representation theory*, Definition 5.20 and Remark 5.21.
-/

public section

namespace TauCeti

open _root_.Matrix

universe u v

variable {Q : Type u} [_root_.Quiver.{v} Q] [Fintype Q] [∀ a b : Q, Fintype (a ⟶ b)]
  [DecidableEq Q]

/-- **The diagram of the Gram matrix of the polarized Tits form is the underlying graph** of the
quiver: two distinct vertices are joined exactly when there is an arrow between them. -/
theorem diagramGraph_toMatrix_titsPolarForm :
    diagramGraph ((titsPolarForm Q).toMatrix (Pi.basisFun ℤ Q)) = Quiver.underlyingGraph Q := by
  ext i j
  rw [diagramGraph_adj, Quiver.underlyingGraph_adj, toMatrix_titsPolarForm_apply,
    toMatrix_titsPolarForm_apply]
  refine and_congr_right fun hij ↦ ?_
  simp only [hij, Ne.symm hij, ↓reduceIte, zero_sub, ne_eq, neg_eq_zero, add_comm (_ : ℤ)]
  rw [← Fintype.card_pos_iff, ← Fintype.card_pos_iff]
  omega

/-- **The root system of a quiver with positive definite Tits form.** For a nonempty connected
quiver whose Tits form `q` is positive definite there is a reduced, crystallographic, irreducible
rational root system on the vertex space `Q → ℚ` with a base indexed by the vertices, the root at
the vertex `i` being the vertex vector `eᵢ`. Its Cartan matrix is `2I - (A + Aᵀ)`, `A` the matrix
of arrow counts, and its roots are exactly the nonzero integral vectors `d` with `q(d) = 1`. -/
theorem exists_rootPairing_titsForm (hconn : (Quiver.underlyingGraph Q).Connected)
    (hpd : (titsForm Q).PosDef) :
    ∃ (ι : Type u) (P : RootPairing ι ℚ (Q → ℚ) (Q → ℚ)) (b : P.Base)
      (_ : P.IsRootSystem) (_ : P.IsCrystallographic) (_ : P.IsReduced) (_ : P.IsIrreducible)
      (e : Q ≃ b.support),
      (∀ i : Q, P.root (e i) = Pi.single i 1) ∧
      (∀ i j : Q, b.cartanMatrix (e i) (e j) =
        (if i = j then (2 : ℤ) else 0) - (Fintype.card (i ⟶ j) + Fintype.card (j ⟶ i))) ∧
      ∀ d : Q → ℤ, (∃ r : ι, P.root r = fun v ↦ (d v : ℚ)) ↔ (d ≠ 0 ∧ titsForm Q d = 1) := by
  have hB : ((titsPolarForm Q).toMatrix (Pi.basisFun ℤ Q)).PosDef :=
    (titsForm_posDef_iff_posDef_toMatrix Q).mp hpd
  have hdiag (i : Q) : (titsPolarForm Q).toMatrix (Pi.basisFun ℤ Q) i i = 2 := by
    rw [LinearMap.BilinForm.toMatrix_apply, Pi.basisFun_apply]
    exact titsPolarForm_single_self_of_isEmpty Q (isEmpty_hom_self_of_titsForm_posDef Q hpd i)
  have hoff (i j : Q) (hij : i ≠ j) : (titsPolarForm Q).toMatrix (Pi.basisFun ℤ Q) i j ≤ 0 := by
    rw [toMatrix_titsPolarForm_apply, ite_eq_right hij]
    omega
  have hirr := hB.isIrreducible_normTwoShellRootPairing ℚ hdiag hoff
    (diagramGraph_toMatrix_titsPolarForm (Q := Q) ▸ hconn)
  refine ⟨_, hB.normTwoShellRootPairing ℚ, hB.normTwoShellBase ℚ hdiag hoff,
    hB.isRootSystem_normTwoShellRootPairing ℚ hdiag, inferInstance, inferInstance, hirr,
    hB.normTwoShellBaseEquiv ℚ hdiag hoff, fun i ↦ ?_, fun i j ↦ ?_, fun d ↦ ?_⟩
  · rw [Matrix.PosDef.coe_normTwoShellBaseEquiv_apply,
      Matrix.PosDef.root_normTwoShellRootPairing_normTwoShellSimple]
  · rw [Matrix.PosDef.cartanMatrix_normTwoShellBase, toMatrix_titsPolarForm_apply]
  · rw [hB.exists_root_normTwoShellRootPairing_eq_iff ℚ]
    have hmem : d ∈ ((titsPolarForm Q).toMatrix (Pi.basisFun ℤ Q)).normTwoShell ↔
        titsForm Q d = 1 := by
      rw [mem_normTwoShell, dotProduct_toMatrix_titsPolarForm_mulVec_self]
      omega
    exact ⟨fun hd ↦ ⟨ne_zero_of_mem_normTwoShell hd, hmem.mp hd⟩, fun hd ↦ hmem.mpr hd.2⟩

end TauCeti
