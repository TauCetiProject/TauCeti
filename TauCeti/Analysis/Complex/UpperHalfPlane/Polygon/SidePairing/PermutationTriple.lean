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
vertex successor `σ.next : j ↦ σ.pair j + 1`, and the inverse cyclic shift `(j ↦ j + 1)⁻¹`
around the boundary of `P` satisfy `(finRotate n)⁻¹ * σ.next * σ.pair = 1`, so they form a
degree-`n` permutation triple `σ.toPermutationTriple`.

Its three components count the cells of the compactified quotient glued from `P`:

* the orbits of `σ.pair` are the pairs of identified sides (`σ.SideRepresentative`), of which
  there are `(n + k) / 2` when `k` sides are paired with themselves;
* the orbits of `σ.next` split into the finite vertex cycles (`σ.FiniteVertexCycle`) and the
  ideal vertex cycles (`σ.IdealVertexCycle`), because `σ.next` preserves whether a vertex lies in
  `ℍ` or on `∂ℍ`;
* the boundary shift `(finRotate n)⁻¹` is a single `n`-cycle, corresponding to the one face of `P`,
  and makes `σ.toPermutationTriple` connected.

Consequently the combinatorial Euler characteristic `σ.toPermutationTriple.eulerChar` equals the
alternating cell count `V + c + k - E + 1` (equivalently `V + c + 1 - (n - k) / 2`), and the
general permutation-triple theory immediately shows that this integer is even and at most `2`.
This supplies the combinatorial half of the genus identity `χ = 2 - 2g` for quotients by
fundamental polygons without invoking Poincaré duality.

## Main definitions

* `ConvexPolygon.SidePairing.toPermutationTriple`: the degree-`n` permutation triple
  `(σ.pair, σ.next, (finRotate n)⁻¹)` attached to a side pairing `σ`.

## Main results

* `ConvexPolygon.SidePairing.orbitCount_pair`: `orbitCount σ.pair = Nat.card σ.SideRepresentative`.
* `ConvexPolygon.SidePairing.orbitCount_next`:
  `orbitCount σ.next = Nat.card σ.FiniteVertexCycle + Nat.card σ.IdealVertexCycle`.
* `ConvexPolygon.SidePairing.isConnected_toPermutationTriple`: `σ.toPermutationTriple` is
  connected.
* `ConvexPolygon.SidePairing.eulerChar_toPermutationTriple`: the Euler characteristic of
  `σ.toPermutationTriple` is `V + c + k - E + 1`.

## References

* S. K. Lando and A. K. Zvonkin, *Graphs on Surfaces and Their Applications*, Encyclopaedia of
  Mathematical Sciences 141, Springer, 2004, §1.5 (hypermaps and the Euler characteristic of a
  glued polygon).
* Alan Beardon, *The Geometry of Discrete Groups*, Graduate Texts in Mathematics 91, Springer,
  1983, §§9.3 and 10.4.
-/

public section

noncomputable section

open Equiv Equiv.Perm

namespace TauCeti.UpperHalfPlane.ConvexPolygon.SidePairing

variable {n : ℕ} [NeZero n] {P : ConvexPolygon n} (σ : P.SidePairing)

private theorem finRotate_eq_addRight_one : finRotate n = Equiv.addRight (1 : Fin n) :=
  Equiv.ext fun i ↦ finRotate_apply i

/-- **The permutation triple of a side pairing.** Its three components are the side involution
`σ.pair`, the vertex-cycle permutation `σ.next`, and the inverse cyclic shift `(finRotate n)⁻¹`
around the single polygonal face. -/
def toPermutationTriple : PermutationTriple n where
  σ0 := σ.pair
  σ1 := σ.next
  σinf := (finRotate n)⁻¹
  product_eq_one :=
    Equiv.ext fun i ↦ by simp [Perm.mul_apply, finRotate_eq_addRight_one]

/-- The edge component `σ0` of `σ.toPermutationTriple` is the side involution `σ.pair`. -/
@[simp]
theorem toPermutationTriple_σ0 : σ.toPermutationTriple.σ0 = σ.pair :=
  (rfl)

/-- The vertex component `σ1` of `σ.toPermutationTriple` is the vertex successor `σ.next`. -/
@[simp]
theorem toPermutationTriple_σ1 : σ.toPermutationTriple.σ1 = σ.next :=
  (rfl)

/-- The face component `σinf` of `σ.toPermutationTriple` is `(finRotate n)⁻¹`. -/
@[simp]
theorem toPermutationTriple_σinf : σ.toPermutationTriple.σinf = (finRotate n)⁻¹ :=
  (rfl)

/-- Two sides lie in the same orbit of the involution `σ.pair` if and only if they coincide or are
paired with each other. -/
private theorem pair_sameCycle_iff (i j : Fin n) :
    σ.pair.SameCycle i j ↔ i = j ∨ σ.pair i = j := by
  have hsq : σ.pair * σ.pair = 1 := Equiv.ext fun x ↦ by simp
  constructor
  · rintro ⟨k, rfl⟩
    obtain ⟨m, rfl | rfl⟩ := Int.even_or_odd' k
    · left
      rw [zpow_mul, zpow_two]
      simp [hsq]
    · right
      rw [zpow_add, zpow_mul, zpow_two, zpow_one]
      simp [hsq]
  · rintro (rfl | rfl)
    · exact SameCycle.rfl
    · exact ⟨1, by simp⟩

/-- Each orbit of `σ.pair` contains a unique representative `i` with `i ≤ σ.pair i`. -/
def pairOrbitEquivSideRepresentative :
    Quotient (SameCycle.setoid σ.pair) ≃ σ.SideRepresentative where
  toFun := Quotient.lift
    (fun i ↦ ⟨min i (σ.pair i), by
      rcases le_total i (σ.pair i) with h | h <;> simp [h]⟩)
    (fun i j hij ↦ by
      apply Subtype.ext
      rcases (σ.pair_sameCycle_iff i j).1 hij with rfl | rfl
      · rfl
      · simp [min_comm])
  invFun i := Quotient.mk'' i.1
  left_inv := Quotient.ind fun i ↦ Quotient.sound <|
    (σ.pair_sameCycle_iff (min i (σ.pair i)) i).2 <| by
      rcases le_total i (σ.pair i) with h | h
      · exact Or.inl (min_eq_left h)
      · exact Or.inr (by simp [min_eq_right h])
  right_inv i := by
    ext
    exact min_eq_left i.2

/-- **The number of orbits of `σ.pair` is the number of side pairs.** -/
theorem orbitCount_pair : orbitCount σ.pair = Nat.card σ.SideRepresentative := by
  rw [orbitCount_def]
  exact Nat.card_congr σ.pairOrbitEquivSideRepresentative

/-- The orbits of `σ.next` split into the finite vertex cycles and the ideal vertex cycles. -/
def nextOrbitEquivSum :
    Quotient (SameCycle.setoid σ.next) ≃ σ.FiniteVertexCycle ⊕ σ.IdealVertexCycle where
  toFun := Quotient.lift
    (fun i ↦ if hi : (P.vertex i).isLeft then .inl (Quotient.mk'' ⟨i, hi⟩)
      else .inr (Quotient.mk'' ⟨i, Sum.not_isLeft.1 hi⟩))
    (fun i j hij ↦ by
      have hmem : j ∈ σ.cycle i := (σ.mem_cycle_iff_sameCycle i j).2 hij
      have hl : (P.vertex j).isLeft = (P.vertex i).isLeft := σ.isLeft_vertex_eq_of_mem_cycle hmem
      by_cases hi : (P.vertex i).isLeft
      · have hj : (P.vertex j).isLeft := hl.symm ▸ hi
        rw [dite_eq_left hi, dite_eq_left hj, Sum.inl.injEq]
        exact Quotient.sound hij
      · have hj : ¬ (P.vertex j).isLeft := fun h ↦ hi (hl ▸ h)
        rw [dite_eq_right hi, dite_eq_right hj, Sum.inr.injEq]
        exact Quotient.sound hij)
  invFun := Sum.elim
    (Quotient.lift (fun i ↦ Quotient.mk'' i.1) fun _ _ h ↦ Quotient.sound h)
    (Quotient.lift (fun i ↦ Quotient.mk'' i.1) fun _ _ h ↦ Quotient.sound h)
  left_inv := Quotient.ind fun i ↦ by
    by_cases hi : (P.vertex i).isLeft <;> simp [hi]
  right_inv := by
    rintro (c | c)
    · refine Quotient.inductionOn c fun i ↦ ?_
      simp [i.2]
    · refine Quotient.inductionOn c fun i ↦ ?_
      have hi : ¬ (P.vertex i.1).isLeft := Sum.not_isLeft.2 i.2
      simp [hi]

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
count `V + c + k - E + 1`, where `V` is the number of finite vertex cycles, `c` the number of
ideal vertex cycles, `k` the number of self-paired sides and `E` the number of side pairs. -/
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
