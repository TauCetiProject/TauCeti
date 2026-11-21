/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.UpperHalfPlane.Polygon.SidePairing.Side.Presentation
public import TauCeti.Analysis.Complex.UpperHalfPlane.Polygon.SidePairing.Vertex.Ideal
public import TauCeti.Analysis.Complex.UpperHalfPlane.Polygon.SidePairing.Vertex.Orbit
public import TauCeti.Combinatorics.PermutationTriple.EulerCharacteristic
import TauCeti.GroupTheory.Perm.OrbitCount.FinRotate

/-!
# The permutation triple of a side-paired hyperbolic polygon

Let `σ` pair the sides of a convex hyperbolic `n`-gon `P`. The side involution `σ.pair`, the
vertex successor `σ.next : j ↦ σ.pair j + 1`, and `(finRotate n)⁻¹` form a connected degree-`n`
permutation triple `σ.toPermutationTriple`. Its orbits count the side pairs
(`σ.SideRepresentative`), the finite and ideal vertex cycles (`σ.FiniteVertexCycle`,
`σ.IdealVertexCycle`), and the single polygonal face, giving
`σ.toPermutationTriple.eulerChar = V + c + k - E + 1`.

## Main definitions and results

* `ConvexPolygon.SidePairing.toPermutationTriple`: the permutation triple
  `(σ.pair, σ.next, (finRotate n)⁻¹)`.
* `ConvexPolygon.SidePairing.orbitCount_pair`, `ConvexPolygon.SidePairing.orbitCount_next`:
  orbit counts of `σ.pair` and `σ.next`.
* `ConvexPolygon.SidePairing.isConnected_toPermutationTriple`: `σ.toPermutationTriple` is
  connected.
* `ConvexPolygon.SidePairing.eulerChar_toPermutationTriple`:
  `σ.toPermutationTriple.eulerChar = V + c + k - E + 1`.

## References

* S. K. Lando and A. K. Zvonkin, *Graphs on Surfaces and Their Applications*, Springer, 2004, §1.5.
* Alan Beardon, *The Geometry of Discrete Groups*, GTM 91, Springer, 1983, §§9.3 and 10.4.
-/

public section

noncomputable section

open Equiv Equiv.Perm

namespace TauCeti.UpperHalfPlane.ConvexPolygon.SidePairing

variable {n : ℕ} [NeZero n] {P : ConvexPolygon n} (σ : P.SidePairing)

/-- **The permutation triple of a side pairing.** Its three components are the side involution
`σ.pair`, the vertex-cycle permutation `σ.next`, and `(finRotate n)⁻¹`. -/
def toPermutationTriple : PermutationTriple n where
  σ0 := σ.pair
  σ1 := σ.next
  σinf := (finRotate n)⁻¹
  product_eq_one := Equiv.ext fun i ↦ by simp [Perm.mul_apply, Perm.inv_def]

/-- The edge component `σ0` of `σ.toPermutationTriple` is `σ.pair`. -/
@[simp] theorem toPermutationTriple_σ0 : σ.toPermutationTriple.σ0 = σ.pair := (rfl)

/-- The vertex component `σ1` of `σ.toPermutationTriple` is `σ.next`. -/
@[simp] theorem toPermutationTriple_σ1 : σ.toPermutationTriple.σ1 = σ.next := (rfl)

/-- The face component `σinf` of `σ.toPermutationTriple` is `(finRotate n)⁻¹`. -/
@[simp] theorem toPermutationTriple_σinf : σ.toPermutationTriple.σinf = (finRotate n)⁻¹ := (rfl)

private theorem pair_sameCycle_iff (i j : Fin n) :
    σ.pair.SameCycle i j ↔ i = j ∨ σ.pair i = j := by
  have hsq : σ.pair ^ 2 = 1 := by rw [sq]; exact Equiv.ext fun x ↦ by simp
  refine ⟨fun ⟨k, hk⟩ ↦ ?_,
    fun h ↦ h.elim (fun h ↦ h ▸ SameCycle.rfl) (fun h ↦ ⟨1, by simpa using h⟩)⟩
  obtain ⟨m, rfl | rfl⟩ := Int.even_or_odd' k
  · left; simpa [zpow_mul, hsq] using hk
  · right; simpa [zpow_add, zpow_mul, hsq] using hk

/-- Each orbit of `σ.pair` contains a unique representative `i` with `i ≤ σ.pair i`. -/
def pairOrbitEquivSideRepresentative :
    Quotient (SameCycle.setoid σ.pair) ≃ σ.SideRepresentative where
  toFun := Quotient.lift
    (fun i ↦ ⟨min i (σ.pair i), by rcases le_total i (σ.pair i) with h | h <;> simp [h]⟩)
    (fun i j hij ↦ Subtype.ext <| by
      rcases (σ.pair_sameCycle_iff i j).1 hij with rfl | rfl
      exacts [rfl, by simp [min_comm]])
  invFun i := Quotient.mk'' i.val
  left_inv := Quotient.ind fun i ↦ Quotient.sound <| (σ.pair_sameCycle_iff _ i).2 <| by
    rcases le_total i (σ.pair i) with h | h
    · exact Or.inl (min_eq_left h)
    · exact Or.inr (by simp [min_eq_right h])
  right_inv i := Subtype.ext (min_eq_left i.property)

/-- `pairOrbitEquivSideRepresentative` sends the orbit of `i` to the minimum representative
`min i (σ.pair i)`. -/
@[simp]
theorem coe_pairOrbitEquivSideRepresentative_mk (i : Fin n) :
    (σ.pairOrbitEquivSideRepresentative (Quotient.mk'' i) : Fin n) = min i (σ.pair i) :=
  (rfl)

/-- The inverse of `pairOrbitEquivSideRepresentative` sends a side representative to its
`σ.pair`-orbit. -/
@[simp]
theorem pairOrbitEquivSideRepresentative_symm_apply (i : σ.SideRepresentative) :
    σ.pairOrbitEquivSideRepresentative.symm i = Quotient.mk'' i.val :=
  (rfl)

/-- **The number of orbits of `σ.pair` is the number of side pairs.** -/
theorem orbitCount_pair : orbitCount σ.pair = Nat.card σ.SideRepresentative := by
  rw [orbitCount_def]; exact Nat.card_congr σ.pairOrbitEquivSideRepresentative

/-- The orbits of `σ.next` split into the finite vertex cycles and the ideal vertex cycles. -/
def nextOrbitEquivSum :
    Quotient (SameCycle.setoid σ.next) ≃ σ.FiniteVertexCycle ⊕ σ.IdealVertexCycle where
  toFun := Quotient.lift
    (fun i ↦ if hi : (P.vertex i).isLeft then .inl (Quotient.mk'' ⟨i, hi⟩)
      else .inr (Quotient.mk'' ⟨i, Sum.not_isLeft.1 hi⟩))
    (fun i j hij ↦ by
      have hl := σ.isLeft_vertex_eq_of_mem_cycle ((σ.mem_cycle_iff_sameCycle i j).2 hij)
      by_cases hi : (P.vertex i).isLeft
      · have hj : (P.vertex j).isLeft := hl.symm ▸ hi
        rw [dite_eq_left hi, dite_eq_left hj, Sum.inl.injEq]; exact Quotient.sound hij
      · have hj : ¬ (P.vertex j).isLeft := fun h ↦ hi (hl ▸ h)
        rw [dite_eq_right hi, dite_eq_right hj, Sum.inr.injEq]; exact Quotient.sound hij)
  invFun := Sum.elim
    (Quotient.lift (fun i ↦ Quotient.mk'' i.val) fun _ _ h ↦ Quotient.sound h)
    (Quotient.lift (fun i ↦ Quotient.mk'' i.val) fun _ _ h ↦ Quotient.sound h)
  left_inv := Quotient.ind fun i ↦ by by_cases hi : (P.vertex i).isLeft <;> simp [hi]
  right_inv := by
    rintro (c | c) <;> refine Quotient.inductionOn c fun i ↦ ?_
    · simp [i.property]
    · simp [Sum.not_isLeft.2 i.property]

/-- On a finite vertex `i`, `nextOrbitEquivSum` sends its `σ.next`-orbit to its finite vertex
cycle. -/
@[simp]
theorem nextOrbitEquivSum_mk_of_isLeft {i : Fin n} (hi : (P.vertex i).isLeft) :
    σ.nextOrbitEquivSum (Quotient.mk'' i) = .inl (Quotient.mk'' ⟨i, hi⟩) := by
  simp [nextOrbitEquivSum, hi]

/-- On an ideal vertex `i`, `nextOrbitEquivSum` sends its `σ.next`-orbit to its ideal vertex
cycle. -/
@[simp]
theorem nextOrbitEquivSum_mk_of_isRight {i : Fin n} (hi : (P.vertex i).isRight) :
    σ.nextOrbitEquivSum (Quotient.mk'' i) = .inr (Quotient.mk'' ⟨i, hi⟩) := by
  simp [nextOrbitEquivSum, Sum.not_isLeft.2 hi]

/-- The inverse of `nextOrbitEquivSum` sends a finite vertex cycle to its underlying
`σ.next`-orbit. -/
@[simp]
theorem nextOrbitEquivSum_symm_inl_mk (i : {i : Fin n // (P.vertex i).isLeft}) :
    σ.nextOrbitEquivSum.symm (.inl (Quotient.mk'' i)) = Quotient.mk'' i.val :=
  (rfl)

/-- The inverse of `nextOrbitEquivSum` sends an ideal vertex cycle to its underlying
`σ.next`-orbit. -/
@[simp]
theorem nextOrbitEquivSum_symm_inr_mk (i : {i : Fin n // (P.vertex i).isRight}) :
    σ.nextOrbitEquivSum.symm (.inr (Quotient.mk'' i)) = Quotient.mk'' i.val :=
  (rfl)

/-- **The number of orbits of `σ.next` is the sum of the finite and ideal vertex cycle counts.** -/
theorem orbitCount_next :
    orbitCount σ.next = Nat.card σ.FiniteVertexCycle + Nat.card σ.IdealVertexCycle := by
  rw [orbitCount_def, Nat.card_congr σ.nextOrbitEquivSum, Nat.card_sum]

open Fin.NatCast in
/-- **The permutation triple of a side pairing is connected.** The boundary shift `finRotate n`
lies in its monodromy group and cycles transitively through the `n` sides. -/
theorem isConnected_toPermutationTriple : σ.toPermutationTriple.IsConnected := by
  rw [PermutationTriple.isConnected_iff]
  refine ⟨NeZero.ne n, ⟨fun i j ↦ ?_⟩⟩
  have hmem : finRotate n ∈ σ.toPermutationTriple.monodromyGroup := by
    simpa using σ.toPermutationTriple.monodromyGroup.inv_mem
      σ.toPermutationTriple.σinf_mem_monodromyGroup
  have hpow (k : ℕ) : (finRotate n ^ k) i = i + (k : Fin n) := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', Perm.mul_apply, ih, finRotate_apply, Nat.cast_add, Nat.cast_one, add_assoc]
  refine ⟨⟨finRotate n, hmem⟩ ^ (j - i).val, ?_⟩
  rw [Subgroup.smul_def, Subgroup.coe_pow, Subgroup.coe_mk, Perm.smul_def, hpow,
    Fin.cast_val_eq_self, add_sub_cancel]

/-- **The combinatorial Euler characteristic of `σ.toPermutationTriple`** is the alternating cell
count `V + c + k - E + 1`. -/
theorem eulerChar_toPermutationTriple :
    σ.toPermutationTriple.eulerChar =
      Nat.card σ.FiniteVertexCycle + Nat.card σ.IdealVertexCycle +
        Nat.card {i : Fin n // σ.pair i = i} - Nat.card σ.SideRepresentative + 1 := by
  rw [PermutationTriple.eulerChar_def, toPermutationTriple_σ0, toPermutationTriple_σ1,
    toPermutationTriple_σinf, orbitCount_inv, orbitCount_finRotate, ite_eq_right (NeZero.ne n),
    σ.orbitCount_pair, σ.orbitCount_next]
  have hE : (2 * Nat.card σ.SideRepresentative : ℤ) =
      n + Nat.card {i : Fin n // σ.pair i = i} := by
    exact_mod_cast σ.two_mul_natCard_sideRepresentative
  omega

end TauCeti.UpperHalfPlane.ConvexPolygon.SidePairing
