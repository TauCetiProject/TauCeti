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

## Main definitions

* `TauCeti.titsRootPairing`: the rational root pairing of a positive definite Tits form.
* `TauCeti.titsRootBase` and `TauCeti.titsRootBaseEquiv`: its coordinate base and vertex marking.

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

public noncomputable section

namespace TauCeti

open _root_.Matrix

universe u v

variable {Q : Type u} [_root_.Quiver.{v} Q] [Fintype Q] [∀ a b : Q, Fintype (a ⟶ b)]
  [DecidableEq Q]

/-- **The diagram of the Gram matrix of the polarized Tits form is the underlying graph** of the
quiver: two distinct vertices are joined exactly when there is an arrow between them. -/
@[simp]
theorem diagramGraph_toMatrix_titsPolarForm :
    diagramGraph ((titsPolarForm Q).toMatrix (Pi.basisFun ℤ Q)) = Quiver.underlyingGraph Q := by
  ext i j
  rw [diagramGraph_adj, Quiver.underlyingGraph_adj, toMatrix_titsPolarForm_apply,
    toMatrix_titsPolarForm_apply]
  refine and_congr_right fun hij ↦ ?_
  simp only [hij, Ne.symm hij, ↓reduceIte, zero_sub, ne_eq, neg_eq_zero, add_comm (_ : ℤ)]
  rw [← Fintype.card_pos_iff, ← Fintype.card_pos_iff]
  omega

/-- An integral vector lies in the Tits Gram matrix's norm-two shell exactly when its Tits
value is one. -/
@[simp]
theorem mem_normTwoShell_toMatrix_titsPolarForm (d : Q → ℤ) :
    d ∈ ((titsPolarForm Q).toMatrix (Pi.basisFun ℤ Q)).normTwoShell ↔ titsForm Q d = 1 := by
  rw [mem_normTwoShell, dotProduct_toMatrix_titsPolarForm_mulVec_self]
  omega

variable (Q) (hpd : (titsForm Q).PosDef)

/-- The rational root pairing whose roots are the integral vectors of Tits value one.
Its coroot at `d` is the Tits Gram matrix applied to `d`. -/
def titsRootPairing :
    RootPairing ((titsPolarForm Q).toMatrix (Pi.basisFun ℤ Q)).normTwoShell ℚ (Q → ℚ) (Q → ℚ) :=
  ((titsForm_posDef_iff_posDef_toMatrix Q).mp hpd).normTwoShellRootPairing ℚ

/-- The Tits root pairing is the root pairing of the norm-two shell of the Tits Gram matrix. -/
theorem titsRootPairing_def :
    titsRootPairing Q hpd =
      ((titsForm_posDef_iff_posDef_toMatrix Q).mp hpd).normTwoShellRootPairing ℚ :=
  (rfl)

@[simp]
theorem root_titsRootPairing
    (a : ((titsPolarForm Q).toMatrix (Pi.basisFun ℤ Q)).normTwoShell) :
    (titsRootPairing Q hpd).root a = fun i ↦ (a.1 i : ℚ) :=
  Matrix.PosDef.root_normTwoShellRootPairing _ ℚ a

@[simp]
theorem coroot_titsRootPairing
    (a : ((titsPolarForm Q).toMatrix (Pi.basisFun ℤ Q)).normTwoShell) :
    (titsRootPairing Q hpd).coroot a =
      fun i ↦ (((titsPolarForm Q).toMatrix (Pi.basisFun ℤ Q) *ᵥ a.1) i : ℚ) :=
  Matrix.PosDef.coroot_normTwoShellRootPairing _ ℚ a

@[simp]
theorem toLinearMap_titsRootPairing (x y : Q → ℚ) :
    (titsRootPairing Q hpd).toLinearMap x y = x ⬝ᵥ y :=
  Matrix.PosDef.toLinearMap_normTwoShellRootPairing _ ℚ x y

instance : (titsRootPairing Q hpd).IsCrystallographic :=
  inferInstanceAs
    (((titsForm_posDef_iff_posDef_toMatrix Q).mp hpd).normTwoShellRootPairing ℚ).IsCrystallographic

instance : (titsRootPairing Q hpd).IsReduced :=
  inferInstanceAs
    (((titsForm_posDef_iff_posDef_toMatrix Q).mp hpd).normTwoShellRootPairing ℚ).IsReduced

instance : (titsRootPairing Q hpd).IsRootSystem :=
  ((titsForm_posDef_iff_posDef_toMatrix Q).mp hpd).isRootSystem_normTwoShellRootPairing ℚ
    (toMatrix_titsPolarForm_apply_self_of_posDef Q hpd)

/-- The integral Cartan pairing of two Tits roots is the polarized Tits form. -/
@[simp]
theorem pairingIn_titsRootPairing
    (a b : ((titsPolarForm Q).toMatrix (Pi.basisFun ℤ Q)).normTwoShell) :
    (titsRootPairing Q hpd).pairingIn ℤ a b = titsPolarForm Q a.1 b.1 := by
  exact (((titsForm_posDef_iff_posDef_toMatrix Q).mp hpd).pairingIn_normTwoShellRootPairing
    ℚ a b).trans (dotProduct_toMatrix_titsPolarForm_mulVec Q a.1 b.1)

/-- The pairing of two Tits roots is the polarized Tits form. -/
@[simp]
theorem pairing_titsRootPairing
    (a b : ((titsPolarForm Q).toMatrix (Pi.basisFun ℤ Q)).normTwoShell) :
    (titsRootPairing Q hpd).pairing a b = (titsPolarForm Q a.1 b.1 : ℚ) := by
  rw [titsRootPairing_def, Matrix.PosDef.pairing_normTwoShellRootPairing,
    dotProduct_toMatrix_titsPolarForm_mulVec]

/-- Reflection in a Tits root is its integral lattice reflection. -/
@[simp]
theorem coe_reflectionPerm_titsRootPairing
    (a b : ((titsPolarForm Q).toMatrix (Pi.basisFun ℤ Q)).normTwoShell) :
    ((titsRootPairing Q hpd).reflectionPerm a b : Q → ℤ) =
      b.1 - titsPolarForm Q b.1 a.1 • a.1 := by
  rw [titsRootPairing, Matrix.PosDef.coe_reflectionPerm_normTwoShellRootPairing,
    dotProduct_toMatrix_titsPolarForm_mulVec]

/-- The integral vectors occurring as Tits roots are exactly those of Tits value one. -/
theorem exists_root_titsRootPairing_eq_iff (d : Q → ℤ) :
    (∃ a, (titsRootPairing Q hpd).root a = fun i ↦ (d i : ℚ)) ↔ titsForm Q d = 1 := by
  rw [titsRootPairing, Matrix.PosDef.exists_root_normTwoShellRootPairing_eq_iff,
    mem_normTwoShell_toMatrix_titsPolarForm]

/-- The coordinate base of the Tits root pairing, marked by the vertices of the quiver. -/
def titsRootBase : (titsRootPairing Q hpd).Base :=
  ((titsForm_posDef_iff_posDef_toMatrix Q).mp hpd).normTwoShellBase ℚ
    (toMatrix_titsPolarForm_apply_self_of_posDef Q hpd)
    (toMatrix_titsPolarForm_apply_nonpos_of_ne Q)

/-- The support of the Tits base consists of the coordinate roots. -/
@[simp]
theorem support_titsRootBase :
    (titsRootBase Q hpd).support =
      Finset.univ.image
        (normTwoShellSimple (toMatrix_titsPolarForm_apply_self_of_posDef Q hpd)) := by
  rw [titsRootBase, Matrix.PosDef.support_normTwoShellBase]

/-- The vertices index the simple roots of the Tits base by their coordinate vectors. -/
def titsRootBaseEquiv : Q ≃ (titsRootBase Q hpd).support :=
  ((titsForm_posDef_iff_posDef_toMatrix Q).mp hpd).normTwoShellBaseEquiv ℚ
    (toMatrix_titsPolarForm_apply_self_of_posDef Q hpd)
    (toMatrix_titsPolarForm_apply_nonpos_of_ne Q)

@[simp]
theorem coe_titsRootBaseEquiv_apply (i : Q) :
    (titsRootBaseEquiv Q hpd i :
      ((titsPolarForm Q).toMatrix (Pi.basisFun ℤ Q)).normTwoShell) =
        normTwoShellSimple (toMatrix_titsPolarForm_apply_self_of_posDef Q hpd) i :=
  Matrix.PosDef.coe_normTwoShellBaseEquiv_apply _ ℚ _ _ i

@[simp]
theorem titsRootBaseEquiv_symm_mk (i : Q)
    (hi : normTwoShellSimple (toMatrix_titsPolarForm_apply_self_of_posDef Q hpd) i ∈
      (titsRootBase Q hpd).support) :
    (titsRootBaseEquiv Q hpd).symm
      ⟨normTwoShellSimple (toMatrix_titsPolarForm_apply_self_of_posDef Q hpd) i, hi⟩ = i :=
  Matrix.PosDef.normTwoShellBaseEquiv_symm_mk _ ℚ _ _ i hi

/-- The root at a marked vertex is its coordinate vector. -/
theorem root_titsRootBaseEquiv (i : Q) :
    (titsRootPairing Q hpd).root (titsRootBaseEquiv Q hpd i) = Pi.single i 1 := by
  rw [coe_titsRootBaseEquiv_apply, titsRootPairing,
    Matrix.PosDef.root_normTwoShellRootPairing_normTwoShellSimple]

/-- The Cartan matrix of the marked Tits base is the symmetrized arrow-count matrix. -/
@[simp]
theorem cartanMatrix_titsRootBase (i j : Q) :
    (titsRootBase Q hpd).cartanMatrix (titsRootBaseEquiv Q hpd i) (titsRootBaseEquiv Q hpd j) =
      (if i = j then (2 : ℤ) else 0) - (Fintype.card (i ⟶ j) + Fintype.card (j ⟶ i)) := by
  rw [← toMatrix_titsPolarForm_apply]
  exact Matrix.PosDef.cartanMatrix_normTwoShellBase _ ℚ _ _ i j

/-- The height relative to the Tits base is the sum of the integer coordinates. -/
@[simp]
theorem height_titsRootBase
    (a : ((titsPolarForm Q).toMatrix (Pi.basisFun ℤ Q)).normTwoShell) :
    (titsRootBase Q hpd).height a = ∑ i, a.1 i :=
  Matrix.PosDef.height_normTwoShellBase _ ℚ _ _ a

/-- Positivity for the Tits base is coordinatewise nonnegativity. -/
@[simp]
theorem isPos_titsRootBase_iff
    (a : ((titsPolarForm Q).toMatrix (Pi.basisFun ℤ Q)).normTwoShell) :
    (titsRootBase Q hpd).IsPos a ↔ 0 ≤ a.1 :=
  Matrix.PosDef.isPos_normTwoShellBase_iff _ ℚ _ _ a

/-- A connected quiver with positive definite Tits form has an irreducible Tits root pairing. -/
theorem isIrreducible_titsRootPairing (hconn : (Quiver.underlyingGraph Q).Connected) :
    (titsRootPairing Q hpd).IsIrreducible :=
  ((titsForm_posDef_iff_posDef_toMatrix Q).mp hpd).isIrreducible_normTwoShellRootPairing ℚ
    (toMatrix_titsPolarForm_apply_self_of_posDef Q hpd)
    (diagramGraph_toMatrix_titsPolarForm (Q := Q) ▸ hconn)

variable {Q} {hpd}

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
  refine ⟨_, titsRootPairing Q hpd, titsRootBase Q hpd, inferInstance, inferInstance, inferInstance,
    isIrreducible_titsRootPairing Q hpd hconn, titsRootBaseEquiv Q hpd,
    root_titsRootBaseEquiv Q hpd, cartanMatrix_titsRootBase Q hpd, fun d ↦ ?_⟩
  rw [exists_root_titsRootPairing_eq_iff]
  exact ⟨fun hd ↦ ⟨ne_zero_of_mem_normTwoShell
    ((mem_normTwoShell_toMatrix_titsPolarForm d).mpr hd), hd⟩, fun hd ↦ hd.2⟩

end TauCeti
