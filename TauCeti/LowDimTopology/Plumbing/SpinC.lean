/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LowDimTopology.Plumbing.Characteristic
public import Mathlib.LinearAlgebra.AffineSpace.Defs
import TauCeti.LinearAlgebra.FreeModule.Int

/-!
# Characteristic-covector orbits of a plumbing lattice

This file packages characteristic covectors of the plumbing intersection lattice modulo twice
the image of the integral lattice under the intersection matrix. For a negative-definite
plumbing, these orbits index the **torsion** spin-c structures of the boundary. If the plumbing
graph has cycles, the boundary may also have non-torsion spin-c structures, which this quotient
does not index. The definitions below apply to an arbitrary plumbing graph and assert only the
lattice quotient, without a topological identification for a degenerate intersection matrix.

The relation is deliberately stated using the intersection matrix acting on coordinate vectors:
this is the integral form of the usual quotient
`Char(P) / 2 PD(H₂(P))`. The existing weight-translation API then supplies the corresponding
comparison between representatives of one class.

Since two characteristic covectors differ by an even covector, the orbits form a torsor over the
cokernel `ℤ^V ⧸ A ℤ^V` of the intersection matrix `A`, the discriminant group `L' / L` of the
plumbing lattice `L` when `A` is nondegenerate: a class `[x]` moves the orbit of `k` to the orbit
of `k + 2 x`, and the orbits of `l` and `k` differ by the class of `(l - k) / 2`. This is the
lattice form of the statement that the spin-c structures of the boundary form a torsor over its
second cohomology, which for a negative-definite plumbing tree of spheres is `L' / L`. Counting
the cokernel, there are exactly `|det A|` orbits, finitely many exactly when `A` is
nondegenerate.

## Main definitions

* `TauCeti.PlumbingGraph.addTwoMulVec`: the shifted characteristic covector `k + 2 * A x`.
* `TauCeti.PlumbingGraph.IsSpinCEquivalent`: characteristic covectors differing by `2 * A x`.
* `TauCeti.PlumbingGraph.characteristicOrbits`: characteristic covectors modulo this relation.
* `TauCeti.PlumbingGraph.characteristicOrbit`: the orbit of a characteristic covector.
* `TauCeti.PlumbingGraph.intersectionCokernel`: the cokernel `ℤ^V ⧸ A ℤ^V`.
* The instance `AddTorsor P.intersectionCokernel P.characteristicOrbits`.

## Main results

* `TauCeti.PlumbingGraph.mk_vadd_characteristicOrbit`,
  `TauCeti.PlumbingGraph.characteristicOrbit_vsub_characteristicOrbit`: the torsor operations
  on representatives.
* `TauCeti.PlumbingGraph.natCard_characteristicOrbits`: there are `|det A|` orbits.
* `TauCeti.PlumbingGraph.finite_characteristicOrbits_iff`: the orbits are finite exactly when
  `det A ≠ 0`.

## References

For negative-definite plumbings, the identification of these orbits with torsion boundary
spin-c structures is given by A. Némethi,
[arXiv:0709.0841](https://arxiv.org/abs/0709.0841), Section 2.2.2, which also describes the
action of `L' / L` on them. This is the indexing convention for lattice homology.
-/

public section

namespace TauCeti

namespace PlumbingGraph

variable {V : Type*} [DecidableEq V] [Fintype V] (P : PlumbingGraph V)

/-- The characteristic covector `k + 2 * A x`, the shift of `k` by twice the image of the lattice
point `x` under the intersection matrix `A`. -/
def addTwoMulVec (k : P.characteristicVectors) (x : V → ℤ) : P.characteristicVectors :=
  P.addTwoMul k (P.intersectionMatrix.mulVec x)

/-- The value of the shifted covector `k + 2 * A x`. -/
@[simp]
theorem addTwoMulVec_val (k : P.characteristicVectors) (x : V → ℤ) :
    (P.addTwoMulVec k x).val = fun v => k.val v + 2 * (P.intersectionMatrix.mulVec x) v :=
  P.addTwoMul_val k _

/-- Shifting by `2 * A 0` does nothing. -/
@[simp]
theorem addTwoMulVec_zero (k : P.characteristicVectors) : P.addTwoMulVec k 0 = k := by
  ext v
  simp

/-- Shifts compose by addition: shifting `k + 2 * A x` by `2 * A m` gives `k + 2 * A (x + m)`. -/
@[simp]
theorem addTwoMulVec_addTwoMulVec (k : P.characteristicVectors) (x m : V → ℤ) :
    P.addTwoMulVec (P.addTwoMulVec k x) m = P.addTwoMulVec k (x + m) := by
  ext v
  simp only [addTwoMulVec_val, Matrix.mulVec_add, Pi.add_apply]
  ring

/-- Two characteristic covectors lie in the same lattice orbit when their difference is twice
an integral covector in the image of the plumbing intersection matrix. -/
def IsSpinCEquivalent (k l : P.characteristicVectors) : Prop :=
  ∃ x : V → ℤ, P.addTwoMulVec k x = l

/-- Unfolds `TauCeti.PlumbingGraph.IsSpinCEquivalent`: `k + 2 * A x = l` for some lattice
point `x`. -/
theorem isSpinCEquivalent_iff (k l : P.characteristicVectors) :
    P.IsSpinCEquivalent k l ↔ ∃ x : V → ℤ, P.addTwoMulVec k x = l :=
  Iff.rfl

/-- Every characteristic covector lies in its own lattice orbit. -/
@[refl]
theorem isSpinCEquivalent_refl (k : P.characteristicVectors) : P.IsSpinCEquivalent k k :=
  (P.isSpinCEquivalent_iff k k).2 ⟨0, P.addTwoMulVec_zero k⟩

/-- Reversing an integral translation reverses the lattice equivalence. -/
@[symm]
theorem IsSpinCEquivalent.symm {k l : P.characteristicVectors}
    (h : P.IsSpinCEquivalent k l) : P.IsSpinCEquivalent l k := by
  obtain ⟨x, rfl⟩ := (P.isSpinCEquivalent_iff k l).1 h
  refine (P.isSpinCEquivalent_iff _ k).2 ⟨-x, ?_⟩
  rw [addTwoMulVec_addTwoMulVec, add_neg_cancel, addTwoMulVec_zero]

/-- Integral translations compose by addition, so lattice equivalence is transitive. -/
@[trans]
theorem IsSpinCEquivalent.trans {k l m : P.characteristicVectors}
    (h₁ : P.IsSpinCEquivalent k l) (h₂ : P.IsSpinCEquivalent l m) :
    P.IsSpinCEquivalent k m := by
  obtain ⟨x, rfl⟩ := (P.isSpinCEquivalent_iff k l).1 h₁
  obtain ⟨y, rfl⟩ := (P.isSpinCEquivalent_iff _ m).1 h₂
  exact (P.isSpinCEquivalent_iff k _).2 ⟨x + y, (P.addTwoMulVec_addTwoMulVec k x y).symm⟩

/-- The setoid of characteristic covectors in the same lattice orbit. -/
def spinCSetoid : Setoid P.characteristicVectors where
  r := P.IsSpinCEquivalent
  iseqv := {
    refl := fun k => P.isSpinCEquivalent_refl k
    symm := fun {_ _} h => IsSpinCEquivalent.symm P h
    trans := fun {_ _ _} h₁ h₂ => IsSpinCEquivalent.trans P h₁ h₂ }

/-- Characteristic covectors modulo twice the image of the plumbing intersection matrix. -/
abbrev characteristicOrbits : Type _ := Quotient P.spinCSetoid

/-- The lattice orbit of a characteristic covector. -/
def characteristicOrbit (k : P.characteristicVectors) : P.characteristicOrbits := Quotient.mk _ k

/-- Every characteristic orbit has a characteristic-covector representative. -/
theorem characteristicOrbit_surjective : Function.Surjective P.characteristicOrbit :=
  Quotient.mk_surjective

/-- Two characteristic covectors have the same orbit exactly when they differ by twice an
intersection-matrix vector. -/
@[simp]
theorem characteristicOrbit_eq_iff (k l : P.characteristicVectors) :
    P.characteristicOrbit k = P.characteristicOrbit l ↔ P.IsSpinCEquivalent k l :=
  Quotient.eq

/-- Adding twice an intersection-matrix vector does not change the lattice orbit. -/
@[simp]
theorem characteristicOrbit_addTwoMulVec (k : P.characteristicVectors) (x : V → ℤ) :
    P.characteristicOrbit (P.addTwoMulVec k x) = P.characteristicOrbit k :=
  (P.characteristicOrbit_eq_iff _ _).2
    (IsSpinCEquivalent.symm P ((P.isSpinCEquivalent_iff k _).2 ⟨x, rfl⟩))

/-! ### The characteristic orbits as a torsor -/

/-- Shifting by twice the image `A x` of a lattice point is `addTwoMulVec`. -/
@[simp]
theorem addTwoMul_mulVec (k : P.characteristicVectors) (x : V → ℤ) :
    P.addTwoMul k (P.intersectionMatrix.mulVec x) = P.addTwoMulVec k x :=
  (rfl)

/-- Shifting both covectors by lattice-image vectors changes their half difference by a
lattice-image vector. -/
theorem halfSub_addTwoMulVec (l k : P.characteristicVectors) (x y : V → ℤ) :
    P.halfSub (P.addTwoMulVec l y) (P.addTwoMulVec k x) =
      P.halfSub l k + P.intersectionMatrix.mulVec (y - x) := by
  ext v
  have : (P.addTwoMulVec l y).val v - (P.addTwoMulVec k x).val v =
      (l.val v - k.val v) + 2 * (P.intersectionMatrix.mulVec (y - x)) v := by
    simp only [addTwoMulVec_val, Matrix.mulVec_sub, Pi.sub_apply]
    ring
  rw [halfSub_apply, this, Int.add_mul_ediv_left _ _ two_ne_zero, Pi.add_apply, halfSub_apply]

/-- The cokernel `ℤ^V ⧸ A ℤ^V` of the intersection matrix `A`: covectors modulo the image of the
lattice. When `A` is nondegenerate this is the discriminant group `L' / L` of the plumbing lattice
`L`, which for a negative-definite plumbing tree is `H₁` of the boundary three-manifold. It acts
simply transitively on the characteristic orbits by `[x] +ᵥ [k] = [k + 2 x]`. -/
abbrev intersectionCokernel : Type _ :=
  (V → ℤ) ⧸ LinearMap.range P.intersectionMatrix.mulVecLin

/-- A covector of the form `A x` is zero in the cokernel. -/
@[simp]
theorem mk_mulVec_eq_zero (x : V → ℤ) :
    (Submodule.Quotient.mk (P.intersectionMatrix.mulVec x) : P.intersectionCokernel) = 0 :=
  (Submodule.Quotient.mk_eq_zero _).2 ⟨x, rfl⟩

/-- Two covectors have the same class in the cokernel exactly when they differ by `A y`. -/
theorem mk_eq_mk_iff_exists_eq_add_mulVec {x x' : V → ℤ} :
    (Submodule.Quotient.mk x : P.intersectionCokernel) = Submodule.Quotient.mk x' ↔
      ∃ y : V → ℤ, x = x' + P.intersectionMatrix.mulVec y := by
  rw [Submodule.Quotient.eq, LinearMap.mem_range]
  simp only [Matrix.mulVecLin_apply, eq_sub_iff_add_eq', eq_comm (a := x)]

/-- Translating the characteristic orbit of `k` by the class of `x`: the orbit of `k + 2 * x`. -/
instance : VAdd P.intersectionCokernel P.characteristicOrbits where
  vadd c o := Quotient.liftOn₂' c o (fun x k => P.characteristicOrbit (P.addTwoMul k x)) <| by
    intro x k x' k' hx hk
    obtain ⟨y, rfl⟩ := (P.mk_eq_mk_iff_exists_eq_add_mulVec).1 (Quotient.sound' hx)
    obtain ⟨z, rfl⟩ := (P.isSpinCEquivalent_iff _ _).1 hk
    refine (P.characteristicOrbit_eq_iff _ _).2 ((P.isSpinCEquivalent_iff _ _).2 ⟨z - y, ?_⟩)
    ext v
    simp only [addTwoMulVec_val, addTwoMul_val, Matrix.mulVec_sub, Pi.add_apply, Pi.sub_apply]
    ring

/-- The difference of the orbits of `l` and `k`: the cokernel class of `(l - k) / 2`. -/
instance : VSub P.intersectionCokernel P.characteristicOrbits where
  vsub o o' := Quotient.liftOn₂' o o' (fun l k => Submodule.Quotient.mk (P.halfSub l k)) <| by
    intro l k l' k' hl hk
    obtain ⟨y, rfl⟩ := (P.isSpinCEquivalent_iff _ _).1 hl
    obtain ⟨x, rfl⟩ := (P.isSpinCEquivalent_iff _ _).1 hk
    refine (P.mk_eq_mk_iff_exists_eq_add_mulVec).2 ⟨x - y, ?_⟩
    simp [halfSub_addTwoMulVec, add_assoc, ← Matrix.mulVec_add]

/-- Translating the orbit of `k` by the class of `x` gives the orbit of `k + 2 * x`. -/
@[simp]
theorem mk_vadd_characteristicOrbit (x : V → ℤ) (k : P.characteristicVectors) :
    (Submodule.Quotient.mk x : P.intersectionCokernel) +ᵥ P.characteristicOrbit k =
      P.characteristicOrbit (P.addTwoMul k x) :=
  (rfl)

/-- The difference of the orbits of `l` and `k` is the class of `(l - k) / 2`. -/
@[simp]
theorem characteristicOrbit_vsub_characteristicOrbit (l k : P.characteristicVectors) :
    P.characteristicOrbit l -ᵥ P.characteristicOrbit k =
      (Submodule.Quotient.mk (P.halfSub l k) : P.intersectionCokernel) :=
  (rfl)

/-- **The characteristic orbits are a torsor over the cokernel of the intersection matrix**, by
`[x] +ᵥ [k] = [k + 2 x]` and `[l] -ᵥ [k] = [(l - k) / 2]`. This is the lattice form of the
statement that the spin-c structures of the boundary form a torsor over its second cohomology. -/
instance : AddTorsor P.intersectionCokernel P.characteristicOrbits where
  zero_vadd o := by
    obtain ⟨k, rfl⟩ := P.characteristicOrbit_surjective o
    rw [← Submodule.Quotient.mk_zero, mk_vadd_characteristicOrbit, addTwoMul_zero]
  add_vadd c c' o := by
    induction c using Submodule.Quotient.induction_on with | H x =>
    induction c' using Submodule.Quotient.induction_on with | H x' =>
    obtain ⟨k, rfl⟩ := P.characteristicOrbit_surjective o
    rw [← Submodule.Quotient.mk_add, mk_vadd_characteristicOrbit, mk_vadd_characteristicOrbit,
      mk_vadd_characteristicOrbit, addTwoMul_addTwoMul, add_comm x']
  nonempty := ⟨P.characteristicOrbit ⟨_, P.isCharacteristicVector_canonicalCharacteristic⟩⟩
  vsub_vadd' o o' := by
    obtain ⟨l, rfl⟩ := P.characteristicOrbit_surjective o
    obtain ⟨k, rfl⟩ := P.characteristicOrbit_surjective o'
    rw [characteristicOrbit_vsub_characteristicOrbit, mk_vadd_characteristicOrbit,
      addTwoMul_halfSub]
  vadd_vsub' c o := by
    induction c using Submodule.Quotient.induction_on with | H x =>
    obtain ⟨k, rfl⟩ := P.characteristicOrbit_surjective o
    rw [mk_vadd_characteristicOrbit, characteristicOrbit_vsub_characteristicOrbit,
      halfSub_addTwoMul]

/-- **The number of characteristic orbits is `|det A|`.** The orbits are in bijection with the
cokernel of the intersection matrix `A`, which has `|det A|` elements when `A` is nondegenerate
and is infinite otherwise; then both sides are `0`. For a negative-definite plumbing tree this is
the number `|H₁(Y)|` of spin-c structures of the boundary. -/
theorem natCard_characteristicOrbits :
    Nat.card P.characteristicOrbits = P.intersectionMatrix.det.natAbs := by
  obtain ⟨o⟩ := (inferInstance : Nonempty P.characteristicOrbits)
  rw [← Nat.card_congr (Equiv.vaddConst o),
    Matrix.natCard_quotient_range_mulVecLin_eq_natAbs_det]

/-- There are finitely many characteristic orbits exactly when the intersection matrix is
nondegenerate. -/
theorem finite_characteristicOrbits_iff :
    Finite P.characteristicOrbits ↔ P.intersectionMatrix.det ≠ 0 := by
  rw [← Int.natAbs_ne_zero, ← natCard_characteristicOrbits, Nat.card_ne_zero]
  exact ⟨fun h ↦ ⟨inferInstance, h⟩, fun h ↦ h.2⟩

end PlumbingGraph

end TauCeti
