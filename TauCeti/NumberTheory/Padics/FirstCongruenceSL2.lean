/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
public import Mathlib.Topology.Algebra.Group.Matrix
public import Mathlib.GroupTheory.Index
public import Mathlib.NumberTheory.Padics.ProperSpace
public import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Lift
public import TauCeti.NumberTheory.Padics.RingHoms

/-!
# First congruence subgroups of SL₂ over the p-adic integers

The kernel of reduction `SL₂(ℤ_p) → SL₂(𝔽_p)` is a compact open normal subgroup of
index `p * (p² - 1)`. We construct this subgroup and its finite products, with entrywise
membership tests and a homeomorphism from the subgroup of the product to the product of
subgroups. These are concrete topological groups on which one can form completed group
algebras and study the matrix logarithm.

No odd-prime hypothesis is needed here. In fact, the central matrix `-1` belongs to the
first congruence subgroup exactly at `p = 2`; this distinguishes that prime before studying
uniformity.

## References

* W. Fu, *Sharp bounds for multiplicities of Bianchi modular forms*, §1 and §5.
-/

public section

open Matrix

noncomputable section

namespace TauCeti

variable (p : ℕ) [Fact p.Prime]

/-- The first congruence subgroup of `SL₂(ℤ_p)`, the kernel of reduction modulo `p`. -/
def firstCongruenceSL2 : Subgroup (SpecialLinearGroup (Fin 2) ℤ_[p]) :=
  (SpecialLinearGroup.map (PadicInt.toZMod (p := p))).ker

/-- Membership means that reduction modulo `p` is the identity matrix. -/
@[simp 900]
theorem mem_firstCongruenceSL2_iff {g : SpecialLinearGroup (Fin 2) ℤ_[p]} :
    g ∈ firstCongruenceSL2 p ↔ SpecialLinearGroup.map PadicInt.toZMod g = 1 :=
  MonoidHom.mem_ker

/-- Entrywise, a first-congruence matrix differs from the identity by multiples of `p`. -/
theorem mem_firstCongruenceSL2_iff_dvd {g : SpecialLinearGroup (Fin 2) ℤ_[p]} :
    g ∈ firstCongruenceSL2 p ↔
      ∀ i j, (p : ℤ_[p]) ∣ g i j - (1 : Matrix (Fin 2) (Fin 2) ℤ_[p]) i j := by
  rw [mem_firstCongruenceSL2_iff, SpecialLinearGroup.ext_iff]
  refine forall_congr' fun i ↦ forall_congr' fun j ↦ ?_
  rw [← Ideal.mem_span_singleton, ← PadicInt.maximalIdeal_eq_span_p,
    ← PadicInt.ker_toZMod, RingHom.mem_ker, map_sub, sub_eq_zero]
  simp [SpecialLinearGroup.map_apply_coe, Matrix.one_apply]

/-- An elementary unipotent matrix is first-congruence exactly when its entry is a multiple
of `p`. In particular, the upper unipotent with entry `p` belongs, but the one with entry `1`
does not. -/
@[simp]
theorem transvection_mem_firstCongruenceSL2_iff {i j : Fin 2} (hij : i ≠ j) (a : ℤ_[p]) :
    SpecialLinearGroup.transvection hij a ∈ firstCongruenceSL2 p ↔ (p : ℤ_[p]) ∣ a := by
  rw [mem_firstCongruenceSL2_iff_dvd]
  simp only [SpecialLinearGroup.transvection_coe, Matrix.add_apply, add_sub_cancel_left]
  constructor
  · intro h
    simpa using h i j
  · intro h k l
    by_cases hk : i = k <;> by_cases hl : j = l <;> simp_all [Matrix.single]

instance firstCongruenceSL2_normal : (firstCongruenceSL2 p).Normal :=
  MonoidHom.normal_ker _

/-- Reduction from `SL₂(ℤ_p)` onto `SL₂(𝔽_p)` is surjective. -/
theorem surjective_reductionSL2 :
    Function.Surjective (SpecialLinearGroup.map (n := Fin 2) (PadicInt.toZMod (p := p))) := by
  let : IsLocalHom (PadicInt.toZMod (p := p)) := by
    rw [PadicInt.toZMod_eq_residueField_comp_residue]
    infer_instance
  exact SpecialLinearGroup.map_surjective _ (ZMod.ringHom_surjective _)

/-- The quotient by the first congruence subgroup is `SL₂(𝔽_p)`. -/
noncomputable def firstCongruenceSL2QuotientEquiv :
    (SpecialLinearGroup (Fin 2) ℤ_[p] ⧸ firstCongruenceSL2 p) ≃*
      SpecialLinearGroup (Fin 2) (ZMod p) :=
  QuotientGroup.quotientKerEquivOfSurjective _ (surjective_reductionSL2 p)

/-- The quotient identification sends the class of a matrix to its reduction. -/
@[simp]
theorem firstCongruenceSL2QuotientEquiv_mk (g : SpecialLinearGroup (Fin 2) ℤ_[p]) :
    firstCongruenceSL2QuotientEquiv p (QuotientGroup.mk g) =
      SpecialLinearGroup.map PadicInt.toZMod g := by
  rfl

/-- The index of the first congruence subgroup is `|SL₂(𝔽_p)| = p * (p² - 1)`. -/
theorem index_firstCongruenceSL2 : (firstCongruenceSL2 p).index = p * (p ^ 2 - 1) := by
  rw [Subgroup.index_eq_card, Nat.card_congr (firstCongruenceSL2QuotientEquiv p).toEquiv,
    Matrix.card_SL_field]
  have hp : 0 < p - 1 := Nat.sub_pos_of_lt (Fact.out : p.Prime).one_lt
  have hsub : p ^ 2 - p = p * (p - 1) := by
    rw [pow_two, Nat.mul_sub_left_distrib, Nat.mul_one]
  simp only [ZMod.card, Fin.prod_univ_two, Fin.val_zero, Fin.val_one,
    pow_zero, pow_one]
  rw [hsub, ← mul_assoc, mul_comm (p ^ 2 - 1) p, Nat.mul_div_cancel _ hp]

/-- The first congruence subgroup is open in the matrix topology. -/
theorem isOpen_firstCongruenceSL2 :
    IsOpen (firstCongruenceSL2 p : Set (SpecialLinearGroup (Fin 2) ℤ_[p])) :=
  (isOpen_discrete {1}).preimage PadicInt.continuous_toZMod.specialLinearGroup_map

/-- The first congruence subgroup is closed in the matrix topology. -/
theorem isClosed_firstCongruenceSL2 :
    IsClosed (firstCongruenceSL2 p : Set (SpecialLinearGroup (Fin 2) ℤ_[p])) :=
  isClosed_singleton.preimage PadicInt.continuous_toZMod.specialLinearGroup_map

/-- The first congruence subgroup, with its subspace topology, is compact. -/
instance firstCongruenceSL2_compactSpace : CompactSpace (firstCongruenceSL2 p) := by
  let : CompactSpace (Matrix (Fin 2) (Fin 2) ℤ_[p]) :=
    inferInstanceAs (CompactSpace (Fin 2 → Fin 2 → ℤ_[p]))
  have : CompactSpace (SpecialLinearGroup (Fin 2) ℤ_[p]) :=
    SpecialLinearGroup.isClosedEmbedding_val.compactSpace
  exact isCompact_iff_compactSpace.mp (isClosed_firstCongruenceSL2 p).isCompact

/-- The product of `m` first congruence subgroups inside `SL₂(ℤ_p)^m`. -/
def firstCongruenceProduct (m : ℕ) :
    Subgroup (Fin m → SpecialLinearGroup (Fin 2) ℤ_[p]) :=
  Subgroup.pi Set.univ fun _ ↦ firstCongruenceSL2 p

/-- Membership in the product is tested in each coordinate. -/
@[simp]
theorem mem_firstCongruenceProduct_iff {m : ℕ}
    {g : Fin m → SpecialLinearGroup (Fin 2) ℤ_[p]} :
    g ∈ firstCongruenceProduct p m ↔ ∀ i, g i ∈ firstCongruenceSL2 p := by
  simp [firstCongruenceProduct, Subgroup.mem_pi]

instance firstCongruenceProduct_normal (m : ℕ) : (firstCongruenceProduct p m).Normal where
  conj_mem g hg x := by
    simp only [mem_firstCongruenceProduct_iff] at hg ⊢
    exact fun i ↦ Subgroup.Normal.conj_mem _ (hg i) _

/-- Finite products have the expected index, including the empty product. -/
theorem index_firstCongruenceProduct (m : ℕ) :
    (firstCongruenceProduct p m).index = (p * (p ^ 2 - 1)) ^ m := by
  simp [firstCongruenceProduct, Subgroup.index_pi, index_firstCongruenceSL2]

/-- The finite product of first congruence subgroups is open. -/
theorem isOpen_firstCongruenceProduct (m : ℕ) :
    IsOpen (firstCongruenceProduct p m :
      Set (Fin m → SpecialLinearGroup (Fin 2) ℤ_[p])) := by
  have hset : (firstCongruenceProduct p m :
      Set (Fin m → SpecialLinearGroup (Fin 2) ℤ_[p])) =
      ⋂ i : Fin m, (fun g : Fin m → SpecialLinearGroup (Fin 2) ℤ_[p] ↦ g i) ⁻¹'
        (firstCongruenceSL2 p : Set (SpecialLinearGroup (Fin 2) ℤ_[p])) := by
    ext g
    simp
  rw [hset]
  exact isOpen_iInter_of_finite fun i ↦
    (isOpen_firstCongruenceSL2 p).preimage (continuous_apply i)

/-- The subgroup-of-product topology agrees with the product of the subgroup topologies. -/
def firstCongruenceProductHomeomorph (m : ℕ) :
    firstCongruenceProduct p m ≃ₜ (Fin m → firstCongruenceSL2 p) where
  toFun g i := ⟨g.val i, (mem_firstCongruenceProduct_iff p).1 g.prop i⟩
  invFun g := ⟨fun i ↦ (g i).val, (mem_firstCongruenceProduct_iff p).2 fun i ↦ (g i).prop⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := continuous_pi fun i ↦
    ((continuous_apply i).comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_pi fun i ↦
    continuous_subtype_val.comp (continuous_apply i)).subtype_mk _

/-- The product comparison leaves each matrix entry unchanged. -/
@[simp]
theorem firstCongruenceProductHomeomorph_apply (m : ℕ) (g : firstCongruenceProduct p m)
    (i : Fin m) :
    (firstCongruenceProductHomeomorph p m g i).val = g.val i := (rfl)

/-- The inverse product comparison assembles the coordinate matrices. -/
@[simp]
theorem firstCongruenceProductHomeomorph_symm_apply (m : ℕ)
    (g : Fin m → firstCongruenceSL2 p) :
    ((firstCongruenceProductHomeomorph p m).symm g).val = fun i ↦ (g i).val := (rfl)

/-- Finite products of first congruence subgroups are compact. -/
instance firstCongruenceProduct_compactSpace (m : ℕ) :
    CompactSpace (firstCongruenceProduct p m) :=
  (firstCongruenceProductHomeomorph p m).symm.compactSpace

/-- The central matrix `-1` belongs to the first congruence subgroup exactly at `p = 2`. -/
@[simp]
theorem neg_one_mem_firstCongruenceSL2_iff :
    (-1 : SpecialLinearGroup (Fin 2) ℤ_[p]) ∈ firstCongruenceSL2 p ↔ p = 2 := by
  rw [mem_firstCongruenceSL2_iff]
  constructor
  · intro h
    have he := congrArg (fun g : SpecialLinearGroup (Fin 2) (ZMod p) ↦ g 0 0) h
    have hz : (-1 : ZMod p) = 1 := by
      simpa [SpecialLinearGroup.map_apply_coe, SpecialLinearGroup.coe_neg,
        Matrix.one_apply] using he
    exact (ZMod.neg_one_eq_one_iff.1 hz).resolve_left (Fact.out : p.Prime).ne_one
  · rintro rfl
    ext i j
    simp [SpecialLinearGroup.map_apply_coe, SpecialLinearGroup.coe_neg, Matrix.one_apply]

end TauCeti
