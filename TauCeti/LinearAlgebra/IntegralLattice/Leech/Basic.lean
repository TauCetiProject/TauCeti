/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.IntegralLattice.ConstructionB.Golay
public import TauCeti.LinearAlgebra.IntegralLattice.Overlattice.Dual

/-!
# The Leech lattice from Construction B and an odd shift

Let `K` be the Construction B lattice of the extended binary Golay code on `Fin 24`, with the
halved dot product `B(x, y) = (∑ i, xᵢ yᵢ) / 2`. It is even of discriminant four. Taking the
distinguished coordinate `∞ = 0`, the odd shift

`s = (-3/2, 1/2, …, 1/2)`

satisfies `B(s, s) = 4`, pairs integrally with `K`, and has `2s ∈ K` but `s ∉ K`. Its class
spans an order-two quadratic-isotropic subgroup of the discriminant group `A_K`, which is
Lagrangian because `A_K` has order four. The Leech lattice is the even overlattice of `K` glued
along this subgroup; its carrier is `K ∪ (s + K)`, and it is even, unimodular, positive definite
and of rank `24`.

The discriminant group of `K` is described explicitly: it consists of `0`, the class of `2e_∞`
(the nonzero class of the Golay Construction A lattice, which is `K ∪ (2e_∞ + K)`), the class of
`s`, and their sum, represented by `(1/2, …, 1/2)`. The half-norms of these classes are `0`, `0`,
`0` and `1/2` modulo `ℤ`.

## Main declarations

* `TauCeti.leechShift`: the odd shift `s`.
* `TauCeti.leechShiftClass`, `TauCeti.golayConstructionAClass`: the classes of `s` and `2e_∞` in
  the discriminant group of `K`, with the description
  `eq_zero_or_eq_golayConstructionAClass_or_eq_leechShiftClass_or_eq_add` of that group.
* `TauCeti.leechShiftSubgroup`: the order-two Lagrangian subgroup spanned by the class of `s`.
* `TauCeti.leechLattice`: the Leech lattice, with the carrier description
  `mem_leechLattice_carrier_iff` and the properties `isEven_leechLattice`,
  `isUnimodular_leechLattice`, `isPosDef_leechLattice` and `finrank_leechLattice`.

## References

* J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, Chapter 4, §11 and
  Chapter 5, §4.4.
* R. A. Wilson, *The Finite Simple Groups*, §5.4.
-/

public section

namespace TauCeti

open BinaryGolay IntegralLattice

/-! ### The odd shift -/

/-- **The odd Leech shift** `s = (-3/2, 1/2, …, 1/2)`, whose coordinate `-3/2` sits at the
distinguished coordinate `∞ = 0`. -/
def leechShift : Fin 24 → ℚ := fun i ↦ if i = 0 then -3 / 2 else 1 / 2

/-- The odd shift has coordinate `-3/2` at the distinguished coordinate. -/
@[simp]
theorem leechShift_zero : leechShift 0 = -3 / 2 := by
  simp [leechShift]

/-- The odd shift has coordinate `1/2` away from the distinguished coordinate. -/
@[simp]
theorem leechShift_of_ne_zero {i : Fin 24} (hi : i ≠ 0) : leechShift i = 1 / 2 := by
  simp [leechShift, hi]

/-- The odd shift is the all-halves vector minus `2e_∞`. -/
theorem leechShift_eq_sub : leechShift = (fun _ ↦ 1 / 2) - Pi.single 0 2 := by
  ext i
  rcases eq_or_ne i 0 with rfl | hi
  · norm_num
  · simp [hi]

/-- The coordinates of the odd shift sum to `10`. -/
@[simp]
theorem sum_leechShift : ∑ i, leechShift i = 10 := by
  rw [leechShift_eq_sub]
  simp only [Pi.sub_apply, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, Finset.sum_pi_single', Finset.mem_univ, ite_true]
  norm_num

/-- Pairing with the odd shift: `B(x, s) = (∑ i, xᵢ) / 4 - x_∞`. -/
theorem constructionBLattice_form_leechShift (x : Fin 24 → ℚ) :
    constructionBLattice.form x leechShift = (∑ i, x i) / 4 - x 0 := by
  rw [constructionBLattice_form, ConstructionA.form_apply, leechShift_eq_sub, dotProduct_sub,
    dotProduct_single]
  simp only [dotProduct, ← Finset.sum_mul]
  push_cast
  ring

/-- **The odd shift has norm four.** -/
theorem constructionBLattice_form_leechShift_self :
    constructionBLattice.form leechShift leechShift = 4 := by
  rw [constructionBLattice_form_leechShift, sum_leechShift, leechShift_zero]
  norm_num

/-- A vector with a coordinate `1/2` does not lie in the Golay Construction B lattice, whose
vectors are integral. -/
private theorem notMem_constructionBLattice_carrier_of_eq_half {x : Fin 24 → ℚ} (i : Fin 24)
    (hx : x i = 1 / 2) : x ∉ constructionBLattice.carrier := by
  rw [constructionBLattice_carrier]
  intro h
  obtain ⟨z, -, rfl⟩ := (ConstructionA.mem_lattice 2).mp (ConstructionB.lattice_le _ h)
  have h2 : ((2 * z i : ℤ) : ℚ) = 1 := by
    push_cast
    rw [show (z i : ℚ) = 1 / 2 from hx]
    norm_num
  have h2' : 2 * z i = 1 := by exact_mod_cast h2
  omega

/-- The odd shift is not a vector of the Golay Construction B lattice. -/
theorem leechShift_notMem_constructionBLattice_carrier :
    leechShift ∉ constructionBLattice.carrier :=
  notMem_constructionBLattice_carrier_of_eq_half 1 (leechShift_of_ne_zero (by decide))

/-- Twice the odd shift, `(-3, 1, …, 1)`, is a vector of the Golay Construction B lattice: it
reduces to the all-ones Golay word and has coordinate sum `20`. -/
theorem two_smul_leechShift_mem_constructionBLattice_carrier :
    (2 : ℤ) • leechShift ∈ constructionBLattice.carrier := by
  have hcast : (2 : ℤ) • leechShift =
      fun i ↦ (((if i = 0 then -3 else 1 : ℤ)) : ℚ) := by
    ext i
    rcases eq_or_ne i 0 with rfl | hi
    · norm_num
    · simp [hi]
  have hone : (fun i : Fin 24 ↦ (((if i = 0 then -3 else 1 : ℤ)) : ZMod 2)) = 1 := by
    ext i
    rw [Pi.one_apply]
    split_ifs <;> decide
  rw [hcast, constructionBLattice_carrier, ConstructionB.intCast_mem_lattice, hone]
  refine ⟨BinaryCode.one_mem_of_isSelfDual isSelfDual_code, ⟨5, ?_⟩⟩
  simp [Finset.sum_ite, Finset.filter_ne', Finset.filter_eq']

/-- **The odd shift pairs integrally with the Golay Construction B lattice.** -/
theorem leechShift_mem_dualCarrier : leechShift ∈ constructionBLattice.dualCarrier := by
  rw [LinearMap.BilinForm.mem_dualSubmodule]
  intro x hx
  rw [constructionBLattice_carrier] at hx
  obtain ⟨hxA, k, hk⟩ := ConstructionB.mem_lattice.mp hx
  obtain ⟨z, -, rfl⟩ := (ConstructionA.mem_lattice 2).mp hxA
  refine Submodule.mem_one.mpr ⟨k - z 0, ?_⟩
  rw [constructionBLattice.isSymm.eq, constructionBLattice_form_leechShift, hk]
  simp only [algebraMap_int_eq, eq_intCast, Int.cast_sub]
  ring

/-- The vector `2e_∞` pairs integrally with the Golay Construction B lattice: the pairing reads
off the distinguished coordinate. -/
theorem single_zero_two_mem_constructionBLattice_dualCarrier :
    Pi.single 0 2 ∈ constructionBLattice.dualCarrier := by
  rw [LinearMap.BilinForm.mem_dualSubmodule]
  intro x hx
  rw [constructionBLattice_carrier] at hx
  obtain ⟨z, -, rfl⟩ := (ConstructionA.mem_lattice 2).mp (ConstructionB.lattice_le _ hx)
  refine Submodule.mem_one.mpr ⟨z 0, ?_⟩
  rw [constructionBLattice.isSymm.eq, constructionBLattice_form]
  simp

/-- The all-halves vector `s + 2e_∞` pairs integrally with the Golay Construction B lattice. -/
theorem const_half_mem_constructionBLattice_dualCarrier :
    (fun _ ↦ 1 / 2 : Fin 24 → ℚ) ∈ constructionBLattice.dualCarrier := by
  simpa [leechShift_eq_sub] using constructionBLattice.dualCarrier.add_mem
    leechShift_mem_dualCarrier single_zero_two_mem_constructionBLattice_dualCarrier

/-- The vector `2e_∞` is not a vector of the Golay Construction B lattice: its coordinate sum is
`2`. -/
theorem single_zero_two_notMem_constructionBLattice_carrier :
    Pi.single 0 2 ∉ constructionBLattice.carrier := by
  rw [constructionBLattice_carrier]
  intro h
  obtain ⟨-, k, hk⟩ := ConstructionB.mem_lattice.mp h
  simp only [Finset.sum_pi_single', Finset.mem_univ, ite_true] at hk
  have hk' : (2 : ℤ) = 4 * k := by exact_mod_cast hk
  omega

/-! ### The discriminant group of the Golay Construction B lattice -/

/-- **The class of the odd shift** in the discriminant group of the Golay Construction B
lattice. -/
noncomputable def leechShiftClass : constructionBLattice.DiscriminantGroup :=
  Submodule.Quotient.mk ⟨leechShift, leechShift_mem_dualCarrier⟩

/-- The class of `2e_∞` in the discriminant group of the Golay Construction B lattice. It is the
nonzero class of the Golay Construction A lattice, which is `K ∪ (2e_∞ + K)` by
`ConstructionB.mem_constructionA_lattice_iff`. -/
noncomputable def golayConstructionAClass : constructionBLattice.DiscriminantGroup :=
  Submodule.Quotient.mk ⟨Pi.single 0 2, single_zero_two_mem_constructionBLattice_dualCarrier⟩

/-- The class of the odd shift is nonzero. -/
theorem leechShiftClass_ne_zero : leechShiftClass ≠ 0 := by
  rw [leechShiftClass, Ne, discriminantGroup_mk_eq_zero_iff]
  exact leechShift_notMem_constructionBLattice_carrier

/-- The class of `2e_∞` is nonzero. -/
theorem golayConstructionAClass_ne_zero : golayConstructionAClass ≠ 0 := by
  rw [golayConstructionAClass, Ne, discriminantGroup_mk_eq_zero_iff]
  exact single_zero_two_notMem_constructionBLattice_carrier

/-- The class of the odd shift differs from the class of `2e_∞`. -/
theorem leechShiftClass_ne_golayConstructionAClass :
    leechShiftClass ≠ golayConstructionAClass := by
  rw [leechShiftClass, golayConstructionAClass, Ne, discriminantGroup_mk_eq_iff]
  refine notMem_constructionBLattice_carrier_of_eq_half 1 ?_
  simp

/-- The sum of the classes of `s` and `2e_∞` is represented by the all-halves vector. -/
theorem leechShiftClass_add_golayConstructionAClass :
    leechShiftClass + golayConstructionAClass =
      Submodule.Quotient.mk ⟨fun _ ↦ 1 / 2, const_half_mem_constructionBLattice_dualCarrier⟩ := by
  rw [leechShiftClass, golayConstructionAClass, ← Submodule.Quotient.mk_add]
  congr
  simp [leechShift_eq_sub]

/-- The sum of the classes of `s` and `2e_∞` is nonzero. -/
theorem leechShiftClass_add_golayConstructionAClass_ne_zero :
    leechShiftClass + golayConstructionAClass ≠ 0 := by
  rw [leechShiftClass_add_golayConstructionAClass, Ne, discriminantGroup_mk_eq_zero_iff]
  exact notMem_constructionBLattice_carrier_of_eq_half 0 rfl

/-- **The discriminant group of the Golay Construction B lattice** consists of exactly four
classes: `0`, the class of `2e_∞`, the class of the odd shift, and their sum. -/
theorem eq_zero_or_eq_golayConstructionAClass_or_eq_leechShiftClass_or_eq_add
    (g : constructionBLattice.DiscriminantGroup) :
    g = 0 ∨ g = golayConstructionAClass ∨ g = leechShiftClass ∨
      g = leechShiftClass + golayConstructionAClass := by
  classical
  have : Fintype constructionBLattice.DiscriminantGroup := Fintype.ofFinite _
  have hS := leechShiftClass_ne_zero
  have hA := golayConstructionAClass_ne_zero
  have hSA := leechShiftClass_ne_golayConstructionAClass
  have hsum := leechShiftClass_add_golayConstructionAClass_ne_zero
  have hcard : ({0, golayConstructionAClass, leechShiftClass,
      leechShiftClass + golayConstructionAClass} : Finset _).card =
      Fintype.card constructionBLattice.DiscriminantGroup := by
    rw [Fintype.card_eq_nat_card, natCard_discriminantGroup_constructionBLattice,
      Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_pair]
    all_goals simp [hS, hA, hSA.symm, hS.symm, hA.symm, hsum.symm]
  have hg := Finset.mem_univ g
  rw [← Finset.eq_univ_of_card _ hcard] at hg
  simpa using hg

/-- The class of the odd shift is quadratic-isotropic: `B(s, s) / 2 = 2`. -/
@[simp]
theorem discriminantQuadraticMap_leechShiftClass :
    constructionBLattice.discriminantQuadraticMap isEven_constructionBLattice
      leechShiftClass = 0 := by
  rw [leechShiftClass, discriminantQuadraticMap_mk_eq_zero_iff]
  exact ⟨2, by rw [constructionBLattice_form_leechShift_self]; norm_num⟩

/-- The class of `2e_∞` is quadratic-isotropic: `B(2e_∞, 2e_∞) / 2 = 1`. -/
@[simp]
theorem discriminantQuadraticMap_golayConstructionAClass :
    constructionBLattice.discriminantQuadraticMap isEven_constructionBLattice
      golayConstructionAClass = 0 := by
  rw [golayConstructionAClass, discriminantQuadraticMap_mk_eq_zero_iff]
  refine ⟨1, ?_⟩
  rw [constructionBLattice_form]
  simp

/-- The sum of the classes of `s` and `2e_∞` has half-norm `1/2` modulo `ℤ`. -/
@[simp]
theorem discriminantQuadraticMap_leechShiftClass_add_golayConstructionAClass :
    constructionBLattice.discriminantQuadraticMap isEven_constructionBLattice
      (leechShiftClass + golayConstructionAClass) = ((1 / 2 : ℚ) : AddCircle (1 : ℚ)) := by
  have h : ((fun _ : Fin 24 ↦ (1 / 2 : ℚ)) ⬝ᵥ fun _ ↦ 1 / 2) / (2 : ℕ) / 2 =
      1 / 2 + 1 := by
    simp [dotProduct]
    norm_num
  rw [leechShiftClass_add_golayConstructionAClass, discriminantQuadraticMap_mk,
    constructionBLattice_form, ConstructionA.form_apply]
  dsimp only
  rw [h, AddCircle.coe_add_period]

/-! ### The glue subgroup -/

/-- **The glue subgroup of the Leech lattice**: the subgroup of the discriminant group of the
Golay Construction B lattice spanned by the class of the odd shift. -/
noncomputable def leechShiftSubgroup : AddSubgroup constructionBLattice.DiscriminantGroup :=
  AddSubgroup.zmultiples leechShiftClass

/-- Twice the class of the odd shift vanishes, since `2s ∈ K`. -/
@[simp]
theorem two_nsmul_leechShiftClass : 2 • leechShiftClass = 0 := by
  rw [leechShiftClass, ← Submodule.Quotient.mk_smul, discriminantGroup_mk_eq_zero_iff]
  simpa only [Submodule.coe_smul_of_tower, ← natCast_zsmul, Nat.cast_ofNat] using
    two_smul_leechShift_mem_constructionBLattice_carrier

/-- The class of the odd shift has order two. -/
@[simp]
theorem addOrderOf_leechShiftClass : addOrderOf leechShiftClass = 2 :=
  addOrderOf_eq_prime two_nsmul_leechShiftClass leechShiftClass_ne_zero

/-- The glue subgroup consists of zero and the class of the odd shift. -/
theorem mem_leechShiftSubgroup_iff (g : constructionBLattice.DiscriminantGroup) :
    g ∈ leechShiftSubgroup ↔ g = 0 ∨ g = leechShiftClass := by
  classical
  rw [leechShiftSubgroup,
    (isOfFinAddOrder_of_finite _).mem_zmultiples_iff_mem_range_addOrderOf,
    addOrderOf_leechShiftClass, Finset.mem_image]
  constructor
  · rintro ⟨a, ha, rfl⟩
    rw [Finset.mem_range] at ha
    interval_cases a <;> simp
  · rintro (rfl | rfl)
    · exact ⟨0, by simp, zero_nsmul _⟩
    · exact ⟨1, by simp, one_nsmul _⟩

/-- The glue subgroup has order two. -/
@[simp]
theorem natCard_leechShiftSubgroup : Nat.card leechShiftSubgroup = 2 := by
  rw [leechShiftSubgroup, Nat.card_zmultiples, addOrderOf_leechShiftClass]

/-- The glue subgroup is quadratic-isotropic. -/
theorem isIsotropic_leechShiftSubgroup :
    (constructionBLattice.discriminantQuadraticModule isEven_constructionBLattice).IsIsotropic
      leechShiftSubgroup := by
  rw [← constructionBLattice.isEven_intermediateCarrierOfDiscriminantSubgroup_iff
    isEven_constructionBLattice,
    IntermediateCarrier.isEven_iff_forall_discriminantQuadraticMap_eq_zero
      isEven_constructionBLattice,
    discriminantSubgroup_intermediateCarrierOfDiscriminantSubgroup]
  intro g hg
  rcases (mem_leechShiftSubgroup_iff g).mp hg with rfl | rfl
  · exact QuadraticMap.map_zero _
  · exact discriminantQuadraticMap_leechShiftClass

/-- **The glue subgroup is Lagrangian**: it is quadratic-isotropic of order two in a
discriminant group of order four. -/
theorem isLagrangian_leechShiftSubgroup :
    (constructionBLattice.discriminantQuadraticModule isEven_constructionBLattice).IsLagrangian
      leechShiftSubgroup := by
  have hcard : Nat.card leechShiftSubgroup ^ 2 =
      Nat.card constructionBLattice.DiscriminantGroup := by
    rw [natCard_leechShiftSubgroup, natCard_discriminantGroup_constructionBLattice]
    norm_num
  exact FiniteQuadraticModule.IsIsotropic.isLagrangian_of_card_sq_eq _
    isIsotropic_leechShiftSubgroup
    (constructionBLattice.isNondegenerate_discriminantQuadraticModule isEven_constructionBLattice)
    hcard

/-! ### The Leech lattice -/

/-- **The Leech lattice**: the even overlattice of the Golay Construction B lattice glued along
the class of the odd shift. Its carrier is `K ∪ (s + K)`, by `mem_leechLattice_carrier_iff`, and
its form is the halved dot product. -/
noncomputable def leechLattice : IntegralLattice (Fin 24 → ℚ) :=
  constructionBLattice.ofIsotropicSubgroup isEven_constructionBLattice leechShiftSubgroup
    isIsotropic_leechShiftSubgroup

/-- The form of the Leech lattice is the halved coordinate dot product. -/
@[simp]
theorem leechLattice_form : leechLattice.form = ConstructionA.form 2 := by
  rw [leechLattice, ofIsotropicSubgroup_form, constructionBLattice_form]

/-- **The carrier of the Leech lattice is `K ∪ (s + K)`**, where `K` is the Golay Construction
B lattice and `s` is the odd shift. -/
theorem mem_leechLattice_carrier_iff (x : Fin 24 → ℚ) :
    x ∈ leechLattice.carrier ↔
      x ∈ constructionBLattice.carrier ∨ x - leechShift ∈ constructionBLattice.carrier := by
  rw [leechLattice, ofIsotropicSubgroup_carrier,
    constructionBLattice.mem_intermediateCarrierOfDiscriminantSubgroup_iff]
  constructor
  · rintro ⟨hxdual, hx⟩
    rcases (mem_leechShiftSubgroup_iff _).mp hx with hx | hx
    · exact Or.inl ((discriminantGroup_mk_eq_zero_iff _ _).mp hx)
    · exact Or.inr ((discriminantGroup_mk_eq_iff _ _ _).mp hx)
  · rintro (hx | hx)
    · refine ⟨constructionBLattice.le_dualCarrier hx, (mem_leechShiftSubgroup_iff _).mpr
        (Or.inl ((discriminantGroup_mk_eq_zero_iff _ _).mpr hx))⟩
    · have hxdual : x ∈ constructionBLattice.dualCarrier := by
        simpa using constructionBLattice.dualCarrier.add_mem
          (constructionBLattice.le_dualCarrier hx) leechShift_mem_dualCarrier
      exact ⟨hxdual, (mem_leechShiftSubgroup_iff _).mpr
        (Or.inr ((discriminantGroup_mk_eq_iff _ _ _).mpr hx))⟩

/-- The Golay Construction B lattice is a sublattice of the Leech lattice. -/
theorem constructionBLattice_carrier_le_leechLattice_carrier :
    constructionBLattice.carrier ≤ leechLattice.carrier :=
  fun x hx ↦ (mem_leechLattice_carrier_iff x).mpr (Or.inl hx)

/-- The odd shift is a vector of the Leech lattice. -/
theorem leechShift_mem_leechLattice_carrier : leechShift ∈ leechLattice.carrier :=
  (mem_leechLattice_carrier_iff _).mpr (Or.inr (by rw [sub_self]; exact zero_mem _))

/-- The Leech lattice is nondegenerate. -/
instance instIsNondegenerateLeechLattice : leechLattice.IsNondegenerate := by
  rw [leechLattice]
  infer_instance

/-- **The Leech lattice is even.** -/
theorem isEven_leechLattice : leechLattice.IsEven :=
  isEven_ofIsotropicSubgroup _ _ _ _

/-- **The Leech lattice is positive definite.** -/
theorem isPosDef_leechLattice : leechLattice.IsPosDef :=
  (isPosDef_ofIsotropicSubgroup_iff _ _ _ _).mpr isPosDef_constructionBLattice

/-- **The Leech lattice is unimodular**, being glued along a Lagrangian subgroup. -/
theorem isUnimodular_leechLattice : leechLattice.IsUnimodular :=
  (isUnimodular_ofIsotropicSubgroup_iff_isLagrangian _ _ _ _).mpr
    isLagrangian_leechShiftSubgroup.toFiniteBilinearModule

/-- The Leech lattice has discriminant one. -/
@[simp]
theorem discriminant_leechLattice : leechLattice.discriminant = 1 :=
  leechLattice.isUnimodular_iff_discriminant_eq_one.mp isUnimodular_leechLattice

/-- The Leech lattice has rank `24`. -/
@[simp]
theorem finrank_leechLattice : Module.finrank ℤ leechLattice = 24 := by
  rw [finrank_carrier, Module.finrank_fintype_fun_eq_card, Fintype.card_fin]

end TauCeti
