/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.CharP.Defs
public import Mathlib.GroupTheory.Abelianization.Defs
public import Mathlib.GroupTheory.PGroup
public import TauCeti.GroupTheory.PLowerCentralSeries
public import TauCeti.GroupTheory.ProperPower
public import Mathlib.LinearAlgebra.Matrix.Notation
-- Private: `fin_cases` is used only inside proofs.
import Mathlib.Tactic.FinCases

/-!
# The Heisenberg group over a ring

The **Heisenberg group** `HeisenbergGroup R` over a ring `R` is the group of unipotent
upper triangular `3 × 3` matrices over `R`, written in the coordinates `(x, y, z)` of the strictly
upper triangle, so that

  `(x, y, z) * (x', y', z') = (x + x', y + y', z + z' + x * y')`.

It is nilpotent of class at most two: every commutator lies on the `z`-axis, which is central, and
the commutator of `(x, y, z)` and `(x', y', z')` is `(0, 0, x * y' - x' * y)`. Every element of the
`z`-axis is such a commutator, so the commutator subgroup is the `z`-axis and the abelianization is
the additive group `R × R`, through `(x, y, z) ↦ (x, y)`. Over a ring of
characteristic `p` the `p`-th power of every element lies on the `z`-axis as well, so the second
term of the lower `p`-central series is trivial. Over `𝔽_p`, for a prime `p`, the group is
nonabelian of order `p ^ 3`, hence the smallest nonabelian `p`-group, and has `p`-class exactly
two; it detects brackets in the degree-one graded piece of the lower `p`-series of a free pro-`p`
group.

## Main definitions

* `TauCeti.HeisenbergGroup`: the Heisenberg group over a ring, with its group structure.
* `TauCeti.HeisenbergGroup.zAxis`: the central subgroup of elements `(0, 0, z)`.
* `TauCeti.HeisenbergGroup.map`: the homomorphism induced by a ring homomorphism, with
  `map_id` and `map_comp`.
* `TauCeti.HeisenbergGroup.toMatrix`: the unipotent upper triangular matrix
  `!![1, x, z; 0, 1, y; 0, 0, 1]` of `(x, y, z)`, an injective monoid homomorphism
  (`TauCeti.HeisenbergGroup.toMatrix_injective`).
* `TauCeti.HeisenbergGroup.projXY`: the projection `(x, y, z) ↦ (x, y)` onto `R × R`.
* `TauCeti.HeisenbergGroup.abelianizationMulEquiv`: the abelianization is `R × R`.
* `TauCeti.HeisenbergGroup.opMulEquiv`: over a commutative ring, the group is isomorphic to its
  opposite by `(x, y, z) ↦ (x, y, x * y - z)`.

## Main results

* `TauCeti.HeisenbergGroup.commutatorElement_eq`: the commutator formula.
* `TauCeti.HeisenbergGroup.commutator_eq_zAxis`: the commutator subgroup is the `z`-axis.
* `TauCeti.HeisenbergGroup.pow_eq`: the power formula
  `(x, y, z) ^ n = (n • x, n • y, n • z + (n choose 2) • (x * y))`.
* `TauCeti.HeisenbergGroup.pLowerCentralSeries_top_two_eq_bot`: over a ring of characteristic
  `p`, the second term of the lower `p`-central series is trivial.
* `TauCeti.HeisenbergGroup.isPGroup_zmod`: over `ZMod p` the Heisenberg group is a `p`-group.
-/

public section

open Subgroup
open scoped commutatorElement

namespace TauCeti

/-- The **Heisenberg group** over a ring `R`: triples `(x, y, z)` with the
multiplication `(x, y, z) * (x', y', z') = (x + x', y + y', z + z' + x * y')`, the group of
unipotent upper triangular `3 × 3` matrices in the coordinates of the strictly upper triangle. -/
@[ext]
structure HeisenbergGroup (R : Type*) where
  /-- The `(1, 2)` matrix entry. -/
  x : R
  /-- The `(2, 3)` matrix entry. -/
  y : R
  /-- The `(1, 3)` matrix entry. -/
  z : R

namespace HeisenbergGroup

variable {R : Type*}

/-- The Heisenberg group is the product `R × R × R` as a type. -/
def equivProd : HeisenbergGroup R ≃ R × R × R where
  toFun a := (a.x, a.y, a.z)
  invFun a := ⟨a.1, a.2.1, a.2.2⟩

@[simp]
theorem equivProd_apply (a : HeisenbergGroup R) : equivProd a = (a.x, a.y, a.z) :=
  (rfl)

@[simp]
theorem equivProd_symm_apply (a : R × R × R) : equivProd.symm a = ⟨a.1, a.2.1, a.2.2⟩ :=
  (rfl)

instance [Fintype R] : Fintype (HeisenbergGroup R) := Fintype.ofEquiv _ equivProd.symm

instance [Finite R] : Finite (HeisenbergGroup R) := Finite.of_equiv _ equivProd.symm

/-- The Heisenberg group over `R` has cardinality `(Nat.card R) ^ 3`; over `𝔽_p` its order is
`p ^ 3`. -/
theorem card_eq : Nat.card (HeisenbergGroup R) = Nat.card R ^ 3 := by
  rw [Nat.card_congr equivProd, Nat.card_prod, Nat.card_prod]
  ring

variable [Ring R]

instance : Mul (HeisenbergGroup R) := ⟨fun a b => ⟨a.x + b.x, a.y + b.y, a.z + b.z + a.x * b.y⟩⟩
instance : One (HeisenbergGroup R) := ⟨⟨0, 0, 0⟩⟩
instance : Inv (HeisenbergGroup R) := ⟨fun a => ⟨-a.x, -a.y, -a.z + a.x * a.y⟩⟩

@[simp] theorem mul_x (a b : HeisenbergGroup R) : (a * b).x = a.x + b.x := rfl
@[simp] theorem mul_y (a b : HeisenbergGroup R) : (a * b).y = a.y + b.y := rfl
@[simp] theorem mul_z (a b : HeisenbergGroup R) : (a * b).z = a.z + b.z + a.x * b.y := rfl
@[simp] theorem one_x : (1 : HeisenbergGroup R).x = 0 := rfl
@[simp] theorem one_y : (1 : HeisenbergGroup R).y = 0 := rfl
@[simp] theorem one_z : (1 : HeisenbergGroup R).z = 0 := rfl
@[simp] theorem inv_x (a : HeisenbergGroup R) : a⁻¹.x = -a.x := rfl
@[simp] theorem inv_y (a : HeisenbergGroup R) : a⁻¹.y = -a.y := rfl
@[simp] theorem inv_z (a : HeisenbergGroup R) : a⁻¹.z = -a.z + a.x * a.y := rfl

instance : Group (HeisenbergGroup R) where
  mul_assoc a b c := by ext <;> simp only [mul_x, mul_y, mul_z, add_mul, mul_add] <;> abel
  one_mul a := by ext <;> simp
  mul_one a := by ext <;> simp
  inv_mul_cancel a := by ext <;> simp

/-- **The commutator formula**: `⁅(x, y, z), (x', y', z')⁆ = (0, 0, x * y' - x' * y)`. -/
theorem commutatorElement_eq (a b : HeisenbergGroup R) :
    ⁅a, b⁆ = ⟨0, 0, a.x * b.y - b.x * a.y⟩ := by
  ext <;> simp [commutatorElement_def, add_mul]
  abel

/-- **The power formula**: `(x, y, z) ^ n = (n • x, n • y, n • z + (n choose 2) • (x * y))`. -/
theorem pow_eq (a : HeisenbergGroup R) (n : ℕ) :
    a ^ n = ⟨n • a.x, n • a.y, n • a.z + n.choose 2 • (a.x * a.y)⟩ := by
  induction n with
  | zero => ext <;> simp
  | succ n ih =>
    rw [pow_succ, ih, Nat.choose_succ_succ' n 1, Nat.choose_one_right]
    ext <;> simp [add_smul, nsmul_eq_mul, mul_assoc]
    abel

/-- The **`z`-axis** `{(0, 0, z)}`, a central subgroup. -/
def zAxis : Subgroup (HeisenbergGroup R) where
  carrier := {a | a.x = 0 ∧ a.y = 0}
  mul_mem' := by
    rintro a b ⟨hax, hay⟩ ⟨hbx, hby⟩
    simp [hax, hay, hbx, hby]
  one_mem' := by simp
  inv_mem' := by
    rintro a ⟨hax, hay⟩
    simp [hax, hay]

@[simp]
theorem mem_zAxis_iff {a : HeisenbergGroup R} : a ∈ zAxis ↔ a.x = 0 ∧ a.y = 0 := Iff.rfl

/-- The `z`-axis is central. -/
theorem zAxis_le_center : zAxis ≤ center (HeisenbergGroup R) := by
  rintro a ⟨hax, hay⟩
  rw [Subgroup.mem_center_iff]
  intro b
  ext <;> simp [hax, hay, add_comm]

/-- Every commutator lies on the `z`-axis: the Heisenberg group is nilpotent of class at most
two. -/
theorem commutatorElement_mem_zAxis (a b : HeisenbergGroup R) : ⁅a, b⁆ ∈ zAxis := by
  rw [commutatorElement_eq]
  exact ⟨rfl, rfl⟩

/-- The commutator of an element of the `z`-axis with any element is trivial. -/
theorem commutatorElement_eq_one_of_mem_zAxis {a : HeisenbergGroup R} (ha : a ∈ zAxis)
    (b : HeisenbergGroup R) : ⁅a, b⁆ = 1 :=
  commutatorElement_eq_one_iff_mul_comm.mpr
    ((Subgroup.mem_center_iff.mp (zAxis_le_center ha) b).symm)

/-- A ring homomorphism `f : R →+* S` induces the group homomorphism
`HeisenbergGroup R →* HeisenbergGroup S` applying `f` to each coordinate. -/
def map {S : Type*} [Ring S] (f : R →+* S) : HeisenbergGroup R →* HeisenbergGroup S where
  toFun a := ⟨f a.x, f a.y, f a.z⟩
  map_one' := by ext <;> simp
  map_mul' a b := by ext <;> simp

@[simp]
theorem map_apply {S : Type*} [Ring S] (f : R →+* S) (a : HeisenbergGroup R) :
    map f a = ⟨f a.x, f a.y, f a.z⟩ :=
  (rfl)

/-- The identity ring homomorphism induces the identity of the Heisenberg group. -/
@[simp]
theorem map_id : map (RingHom.id R) = MonoidHom.id (HeisenbergGroup R) := by
  ext <;> simp

/-- The homomorphism induced by a composite of ring homomorphisms is the composite of the induced
homomorphisms. -/
@[simp]
theorem map_comp {S T : Type*} [Ring S] [Ring T] (g : S →+* T) (f : R →+* S) :
    map (g.comp f) = (map g).comp (map f) := by
  ext <;> simp

/-- The homomorphism induced by a surjective ring homomorphism is surjective. -/
theorem map_surjective {S : Type*} [Ring S] {f : R →+* S} (hf : Function.Surjective f) :
    Function.Surjective (map f) := fun b ↦ by
  obtain ⟨x, hx⟩ := hf b.x
  obtain ⟨y, hy⟩ := hf b.y
  obtain ⟨z, hz⟩ := hf b.z
  exact ⟨⟨x, y, z⟩, by ext <;> simp [hx, hy, hz]⟩

/-- The **unipotent upper triangular matrix** `!![1, x, z; 0, 1, y; 0, 0, 1]` of `(x, y, z)`. The
group law of the Heisenberg group is the matrix product, so this is a monoid homomorphism. -/
def toMatrix : HeisenbergGroup R →* Matrix (Fin 3) (Fin 3) R where
  toFun a := !![1, a.x, a.z; 0, 1, a.y; 0, 0, 1]
  map_one' := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  map_mul' a b := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three] <;> abel

theorem toMatrix_apply (a : HeisenbergGroup R) :
    toMatrix a = !![1, a.x, a.z; 0, 1, a.y; 0, 0, 1] := (rfl)

/-- A group element is determined by its matrix. -/
theorem toMatrix_injective : Function.Injective (toMatrix : HeisenbergGroup R → _) := by
  intro a b h
  have h01 := congrFun (congrFun h 0) 1
  have h12 := congrFun (congrFun h 1) 2
  have h02 := congrFun (congrFun h 0) 2
  simp only [toMatrix_apply] at h01 h12 h02
  ext
  · simpa using h01
  · simpa using h12
  · simpa using h02

/-! ### The commutator subgroup and the abelianization -/

/-- **The commutator subgroup of the Heisenberg group is its `z`-axis**: every commutator lies on
the `z`-axis, and `(0, 0, c)` is the commutator of `(c, 0, 0)` and `(0, 1, 0)`. -/
theorem commutator_eq_zAxis : commutator (HeisenbergGroup R) = zAxis := by
  refine le_antisymm (commutator_le.mpr fun a _ b _ ↦ commutatorElement_mem_zAxis a b)
    fun a ha ↦ ?_
  obtain ⟨hax, hay⟩ := mem_zAxis_iff.mp ha
  have h : ⁅(⟨a.z, 0, 0⟩ : HeisenbergGroup R), ⟨0, 1, 0⟩⁆ = a := by
    rw [commutatorElement_eq]
    ext <;> simp [hax, hay]
  rw [← h]
  exact commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)

/-- The projection `(x, y, z) ↦ (x, y)` of the Heisenberg group onto the additive group `R × R`,
written multiplicatively. Its kernel is the `z`-axis (`TauCeti.HeisenbergGroup.ker_projXY`). -/
def projXY : HeisenbergGroup R →* Multiplicative (R × R) where
  toFun a := .ofAdd (a.x, a.y)
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp]
theorem projXY_apply (a : HeisenbergGroup R) : projXY a = .ofAdd (a.x, a.y) :=
  (rfl)

/-- The kernel of the projection `(x, y, z) ↦ (x, y)` is the `z`-axis. -/
theorem ker_projXY : (projXY : HeisenbergGroup R →* _).ker = zAxis := by
  ext a
  simp [MonoidHom.mem_ker, Prod.ext_iff]

/-- **The abelianization of the Heisenberg group** is the additive group `R × R`, through the
projection `(x, y, z) ↦ (x, y)`. -/
def abelianizationMulEquiv : Abelianization (HeisenbergGroup R) ≃* Multiplicative (R × R) :=
  (QuotientGroup.quotientMulEquivOfEq (commutator_eq_zAxis.trans ker_projXY.symm)).trans
    (QuotientGroup.quotientKerEquivOfRightInverse (projXY : HeisenbergGroup R →* _)
      (fun v ↦ (⟨v.toAdd.1, v.toAdd.2, 0⟩ : HeisenbergGroup R)) fun _ ↦ by rfl)

@[simp]
theorem abelianizationMulEquiv_of (a : HeisenbergGroup R) :
    abelianizationMulEquiv (Abelianization.of a) = .ofAdd (a.x, a.y) :=
  (rfl)

@[simp]
theorem abelianizationMulEquiv_symm_apply (v : Multiplicative (R × R)) :
    abelianizationMulEquiv.symm v =
      Abelianization.of (⟨v.toAdd.1, v.toAdd.2, 0⟩ : HeisenbergGroup R) :=
  (rfl)

/-- The Heisenberg group over a commutative ring is isomorphic to its opposite group by
`(x, y, z) ↦ (x, y, x * y - z)`, an anti-automorphism fixing the first two coordinates. -/
def opMulEquiv {R : Type*} [CommRing R] : HeisenbergGroup R ≃* (HeisenbergGroup R)ᵐᵒᵖ where
  toFun a := .op ⟨a.x, a.y, a.x * a.y - a.z⟩
  invFun a := ⟨a.unop.x, a.unop.y, a.unop.x * a.unop.y - a.unop.z⟩
  left_inv a := by ext <;> simp
  right_inv a := MulOpposite.unop_injective <| by ext <;> simp
  map_mul' a b := MulOpposite.unop_injective <| by ext <;> simp <;> ring

@[simp]
theorem unop_opMulEquiv {R : Type*} [CommRing R] (a : HeisenbergGroup R) :
    (opMulEquiv a).unop = ⟨a.x, a.y, a.x * a.y - a.z⟩ :=
  (rfl)

@[simp]
theorem opMulEquiv_symm_apply {R : Type*} [CommRing R] (a : (HeisenbergGroup R)ᵐᵒᵖ) :
    opMulEquiv.symm a = ⟨a.unop.x, a.unop.y, a.unop.x * a.unop.y - a.unop.z⟩ :=
  (rfl)

section CharP

variable (p : ℕ) [CharP R p]

/-- In characteristic `p`, the `p`-th power of every element lies on the `z`-axis. -/
theorem pow_char_mem_zAxis (a : HeisenbergGroup R) : a ^ p ∈ zAxis := by
  rw [pow_eq, mem_zAxis_iff]
  simp [nsmul_eq_mul, CharP.cast_eq_zero]

/-- In characteristic `p`, the `p`-th power of an element of the `z`-axis is trivial. -/
theorem pow_char_eq_one_of_mem_zAxis {a : HeisenbergGroup R} (ha : a ∈ zAxis) : a ^ p = 1 := by
  obtain ⟨hax, hay⟩ := mem_zAxis_iff.mp ha
  rw [pow_eq]
  ext <;> simp [hax, hay, nsmul_eq_mul, CharP.cast_eq_zero]

/-- In characteristic `p`, the first term of the lower `p`-central series lies on the `z`-axis. -/
theorem pLowerCentralSeries_top_one_le_zAxis :
    (⊤ : Subgroup (HeisenbergGroup R)).pLowerCentralSeries p 1 ≤ zAxis :=
  Subgroup.pLowerCentralSeries_succ_le_iff.mpr
    ⟨fun a _ => pow_char_mem_zAxis p a, fun a _ b _ => commutatorElement_mem_zAxis a b⟩

/-- **The Heisenberg group has `p`-class at most two** in characteristic `p`: the second term of
its lower `p`-central series is trivial. -/
theorem pLowerCentralSeries_top_two_eq_bot :
    (⊤ : Subgroup (HeisenbergGroup R)).pLowerCentralSeries p 2 = ⊥ := by
  refine le_bot_iff.mp (Subgroup.pLowerCentralSeries_succ_le_iff.mpr ⟨fun a ha => ?_, ?_⟩)
  · rw [mem_bot]
    exact pow_char_eq_one_of_mem_zAxis p (pLowerCentralSeries_top_one_le_zAxis p ha)
  · intro a ha b _
    rw [mem_bot]
    exact commutatorElement_eq_one_of_mem_zAxis (pLowerCentralSeries_top_one_le_zAxis p ha) b

end CharP

/-- The Heisenberg group over `ZMod p` is a `p`-group; for `p > 0` it has order `p ^ 3`. -/
theorem isPGroup_zmod (p : ℕ) : IsPGroup p (HeisenbergGroup (ZMod p)) :=
  IsPGroup.of_card (n := 3) (by rw [card_eq, Nat.card_zmod])

/-- The central element with third coordinate one in the integer Heisenberg group is not a
proper power. -/
theorem not_isProperPower_mk_zero_zero_one :
    ¬ Group.IsProperPower (⟨0, 0, 1⟩ : HeisenbergGroup ℤ) := by
  intro h
  obtain ⟨y, n, hn, heq⟩ := Group.isProperPower_iff.mp h
  have hx := congrArg HeisenbergGroup.x heq
  have hy := congrArg HeisenbergGroup.y heq
  simp only [pow_eq, Int.nsmul_eq_mul, zero_eq_mul, Int.natCast_eq_zero] at hx hy
  have hxy : y.x = 0 ∧ y.y = 0 := by
    constructor <;> omega
  have hz := congrArg HeisenbergGroup.z heq
  simp only [pow_eq, hxy.1, nsmul_zero, hxy.2,
    Int.nsmul_eq_mul, mul_zero, add_zero] at hz
  have hdiv' : n ∣ 1 := Int.natCast_dvd_natCast.mp ⟨y.z, hz⟩
  have hle : n ≤ 1 := Nat.le_of_dvd (by omega) hdiv'
  omega

end HeisenbergGroup

end TauCeti
