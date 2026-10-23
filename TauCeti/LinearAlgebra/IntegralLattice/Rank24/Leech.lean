/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.IntegralLattice.ConstructionB.Golay
public import TauCeti.LinearAlgebra.IntegralLattice.Overlattice.Dual
public import TauCeti.LinearAlgebra.IntegralLattice.Overlattice.Index
import TauCeti.Algebra.Group.Subgroup.ZPowers

/-!
# The Leech lattice from Construction B and an odd shift

Let `K` be the Construction B lattice of the extended binary Golay code: the integer vectors of
`ℚ^(Fin 24)` reducing to a Golay codeword modulo two and having coordinate sum divisible by four,
with the halved dot product `B(x, y) = (∑ xᵢ yᵢ) / 2`. It is even of discriminant four.

The *odd Leech shift* is `s = (-3/2, 1/2, …, 1/2)`, the distinguished coordinate being `0`.
It pairs integrally with `K`, since `B(s, x) = (∑ xᵢ) / 4 - x₀`; it has norm `B(s, s) = 4`;
and `2s = (-3, 1, …, 1)` lies in `K` while `s` does not, because its coordinates are not
integers. Its class therefore generates an order-two subgroup of the discriminant group `A_K`,
which is quadratic-isotropic because `B(s, s) / 2` is an integer, and Lagrangian because
`2² = #A_K`.

The Leech lattice is the even overlattice of `K` glued along this subgroup. Its carrier is
literally `K ∪ (s + K)`, and it is a positive definite, even, unimodular lattice of rank `24`.
Its rootlessness is a separate argument through the Golay weights and is not part of this file.

## Main declarations

* `TauCeti.leechShift`: the odd shift `(-3/2, 1/2, …, 1/2)`.
* `TauCeti.leechShiftClass`, `TauCeti.leechShiftSubgroup`: its discriminant class and the
  order-two Lagrangian subgroup it generates.
* `TauCeti.leechLattice`: the Leech lattice, with the carrier decomposition
  `TauCeti.mem_leechLattice_carrier_iff`, and `TauCeti.isEven_leechLattice`,
  `TauCeti.isUnimodular_leechLattice`, `TauCeti.isPosDef_leechLattice`, and
  `TauCeti.finrank_leechLattice`.

## References

* J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, Chapter 4, §11, and
  Chapter 10.
* R. A. Wilson, *The Finite Simple Groups*, §5.4.
-/

public section

namespace TauCeti

open BinaryGolay IntegralLattice

/-! ### The odd shift -/

/-- **The odd Leech shift** `(-3/2, 1/2, …, 1/2)`, whose distinguished coordinate is `0`. -/
def leechShift : Fin 24 → ℚ := fun i ↦ if i = 0 then -(3 / 2) else 1 / 2

/-- The distinguished coordinate of the Leech shift is `-3/2`. -/
@[simp]
theorem leechShift_zero : leechShift 0 = -(3 / 2) := by
  simp [leechShift]

/-- Every other coordinate of the Leech shift is `1/2`. -/
@[simp]
theorem leechShift_of_ne_zero {i : Fin 24} (hi : i ≠ 0) : leechShift i = 1 / 2 := by
  simp [leechShift, hi]

/-- The dot product with the Leech shift is half the coordinate sum minus twice the distinguished
coordinate. -/
theorem leechShift_dotProduct (x : Fin 24 → ℚ) :
    leechShift ⬝ᵥ x = (∑ i, x i) / 2 - 2 * x 0 := by
  simp only [dotProduct, Fin.sum_univ_succ (f := fun i ↦ leechShift i * x i),
    Fin.sum_univ_succ (f := x), leechShift_zero, leechShift_of_ne_zero (Fin.succ_ne_zero _),
    ← Finset.mul_sum]
  ring

/-- The Golay Construction B form pairs the Leech shift with `x` to a quarter of the coordinate
sum minus the distinguished coordinate. -/
theorem constructionBLattice_form_leechShift_left (x : Fin 24 → ℚ) :
    constructionBLattice.form leechShift x = (∑ i, x i) / 4 - x 0 := by
  rw [constructionBLattice_form, ConstructionA.form_apply, leechShift_dotProduct]
  push_cast
  ring

/-- **The Leech shift has norm four.** -/
theorem constructionBLattice_form_leechShift_leechShift :
    constructionBLattice.form leechShift leechShift = 4 := by
  rw [constructionBLattice_form_leechShift_left, Fin.sum_univ_succ, leechShift_zero]
  simp only [leechShift_of_ne_zero (Fin.succ_ne_zero _), Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  norm_num

/-- **The Leech shift pairs integrally with Construction B**: for `x` in Construction B,
`B(s, x) = (∑ xᵢ) / 4 - x₀` is an integer. -/
theorem leechShift_mem_constructionBLattice_dualCarrier :
    leechShift ∈ constructionBLattice.dualCarrier := by
  rw [IntegralLattice.dualCarrier, LinearMap.BilinForm.mem_dualSubmodule]
  intro x hx
  rw [constructionBLattice_carrier, ConstructionB.mem_lattice] at hx
  obtain ⟨hA, k, hk⟩ := hx
  obtain ⟨z, -, rfl⟩ := (ConstructionA.mem_lattice 2).mp hA
  refine Submodule.mem_one.mpr ⟨k - z 0, ?_⟩
  rw [constructionBLattice_form_leechShift_left, hk]
  simp only [algebraMap_int_eq, eq_intCast, Int.cast_sub]
  ring

/-- Twice the Leech shift, `(-3, 1, …, 1)`, lies in Construction B: it reduces to the all-ones
Golay word and has coordinate sum `20`. -/
theorem two_zsmul_leechShift_mem_constructionBLattice_carrier :
    (2 : ℤ) • leechShift ∈ constructionBLattice.carrier := by
  have hcast : (2 : ℤ) • leechShift = fun i ↦ ((if i = 0 then -3 else 1 : ℤ) : ℚ) := by
    ext i
    by_cases hi : i = 0
    · simp [hi]
      norm_num
    · simp [hi]
  rw [hcast, constructionBLattice_carrier, ConstructionB.intCast_mem_lattice]
  refine ⟨?_, ⟨5, by decide⟩⟩
  convert BinaryCode.one_mem_of_isSelfDual isSelfDual_code using 1
  ext i
  by_cases hi : i = 0
  · simp only [hi, ite_true, Pi.one_apply]
    decide
  · simp [hi]

/-- The Leech shift does not lie in Construction B, whose vectors have integer coordinates. -/
theorem leechShift_notMem_constructionBLattice_carrier :
    leechShift ∉ constructionBLattice.carrier := by
  rw [constructionBLattice_carrier, ConstructionB.mem_lattice]
  rintro ⟨hA, -⟩
  obtain ⟨z, -, hz⟩ := (ConstructionA.mem_lattice 2).mp hA
  have h := congrFun hz 1
  rw [leechShift_of_ne_zero (by decide)] at h
  have h2 : ((2 * z 1 : ℤ) : ℚ) = 1 := by
    push_cast
    rw [h]
    norm_num
  have h2' : 2 * z 1 = 1 := by exact_mod_cast h2
  omega

/-! ### The glue subgroup -/

/-- The discriminant class of the Leech shift in the Golay Construction B lattice. -/
noncomputable def leechShiftClass : constructionBLattice.DiscriminantGroup :=
  Submodule.Quotient.mk ⟨leechShift, leechShift_mem_constructionBLattice_dualCarrier⟩

/-- The class of the Leech shift is represented by the Leech shift. -/
theorem leechShiftClass_def :
    leechShiftClass =
      Submodule.Quotient.mk ⟨leechShift, leechShift_mem_constructionBLattice_dualCarrier⟩ :=
  (rfl)

/-- The class of the Leech shift is nonzero. -/
theorem leechShiftClass_ne_zero : leechShiftClass ≠ 0 := by
  rw [leechShiftClass_def, Ne, constructionBLattice.discriminantGroup_mk_eq_zero_iff]
  exact leechShift_notMem_constructionBLattice_carrier

/-- Twice the class of the Leech shift vanishes. -/
theorem two_nsmul_leechShiftClass : 2 • leechShiftClass = 0 := by
  rw [leechShiftClass_def, ← Submodule.Quotient.mk_smul,
    constructionBLattice.discriminantGroup_mk_eq_zero_iff]
  simpa only [two_nsmul, Submodule.coe_add, two_zsmul] using
    two_zsmul_leechShift_mem_constructionBLattice_carrier

/-- The class of the Leech shift has order two. -/
@[simp]
theorem addOrderOf_leechShiftClass : addOrderOf leechShiftClass = 2 :=
  addOrderOf_eq_prime two_nsmul_leechShiftClass leechShiftClass_ne_zero

/-- **The Leech glue subgroup** of the discriminant group of the Golay Construction B lattice,
generated by the class of the Leech shift. -/
noncomputable def leechShiftSubgroup : AddSubgroup constructionBLattice.DiscriminantGroup :=
  AddSubgroup.zmultiples leechShiftClass

/-- The Leech glue subgroup consists of zero and the class of the Leech shift. -/
@[simp]
theorem mem_leechShiftSubgroup_iff (x : constructionBLattice.DiscriminantGroup) :
    x ∈ leechShiftSubgroup ↔ x = 0 ∨ x = leechShiftClass :=
  AddSubgroup.mem_zmultiples_iff_of_two_nsmul_eq_zero two_nsmul_leechShiftClass

/-- The Leech glue subgroup has order two. -/
theorem natCard_leechShiftSubgroup : Nat.card leechShiftSubgroup = 2 := by
  rw [leechShiftSubgroup, Nat.card_zmultiples, addOrderOf_leechShiftClass]

/-- The discriminant quadratic map vanishes on the class of the Leech shift, whose half-norm
`4 / 2` is an integer. -/
@[simp]
theorem discriminantQuadraticMap_leechShiftClass :
    constructionBLattice.discriminantQuadraticMap isEven_constructionBLattice
      leechShiftClass = 0 := by
  rw [leechShiftClass_def, constructionBLattice.discriminantQuadraticMap_mk_eq_zero_iff]
  exact ⟨2, by rw [constructionBLattice_form_leechShift_leechShift]; norm_num⟩

/-- **The Leech glue subgroup is quadratic-isotropic.** -/
theorem isIsotropic_leechShiftSubgroup :
    (constructionBLattice.discriminantQuadraticModule
      isEven_constructionBLattice).IsIsotropic leechShiftSubgroup := by
  rw [← constructionBLattice.isEven_intermediateCarrierOfDiscriminantSubgroup_iff,
    IntermediateCarrier.isEven_iff_forall_discriminantQuadraticMap_eq_zero
      isEven_constructionBLattice,
    discriminantSubgroup_intermediateCarrierOfDiscriminantSubgroup]
  intro x hx
  rcases (mem_leechShiftSubgroup_iff x).mp hx with rfl | rfl
  · exact QuadraticMap.map_zero _
  · exact discriminantQuadraticMap_leechShiftClass

/-- **The Leech glue subgroup is Lagrangian**: it is isotropic of order two in a discriminant
group of order four. -/
theorem isLagrangian_leechShiftSubgroup :
    (constructionBLattice.discriminantQuadraticModule
      isEven_constructionBLattice).IsLagrangian leechShiftSubgroup :=
  FiniteQuadraticModule.IsIsotropic.isLagrangian_of_card_sq_eq _ isIsotropic_leechShiftSubgroup
    (constructionBLattice.isNondegenerate_discriminantQuadraticModule
      isEven_constructionBLattice)
    (by
      have hcard : Nat.card leechShiftSubgroup ^ 2 =
          Nat.card constructionBLattice.DiscriminantGroup := by
        rw [natCard_leechShiftSubgroup, natCard_discriminantGroup_constructionBLattice]
        norm_num
      exact hcard)

/-! ### The Leech lattice -/

/-- **The Leech lattice**, glued from the Golay Construction B lattice along the order-two
subgroup generated by the odd shift `(-3/2, 1/2, …, 1/2)`. Its carrier is the union of the
Construction B lattice and its translate by the shift, by `mem_leechLattice_carrier_iff`. -/
noncomputable def leechLattice : IntegralLattice (Fin 24 → ℚ) :=
  constructionBLattice.ofIsotropicSubgroup isEven_constructionBLattice leechShiftSubgroup
    isIsotropic_leechShiftSubgroup

/-- The carrier of the Leech lattice is the inverse image of the Leech glue subgroup. -/
theorem leechLattice_carrier : leechLattice.carrier =
    (constructionBLattice.intermediateCarrierOfDiscriminantSubgroup leechShiftSubgroup :
      Submodule ℤ (Fin 24 → ℚ)) :=
  ofIsotropicSubgroup_carrier _ _ _ _

/-- The form of the Leech lattice is the halved coordinate dot product. -/
@[simp]
theorem leechLattice_form : leechLattice.form = ConstructionA.form 2 := by
  rw [leechLattice, ofIsotropicSubgroup_form, constructionBLattice_form]

/-- **The carrier decomposition of the Leech lattice**: a vector lies in the Leech lattice
exactly when it or its difference with the odd shift lies in the Golay Construction B
lattice. -/
@[simp]
theorem mem_leechLattice_carrier_iff (x : Fin 24 → ℚ) :
    x ∈ leechLattice.carrier ↔
      x ∈ constructionBLattice.carrier ∨ x - leechShift ∈ constructionBLattice.carrier := by
  rw [leechLattice_carrier, leechShiftSubgroup, leechShiftClass_def]
  refine constructionBLattice.mem_intermediateCarrierOfDiscriminantSubgroup_zmultiples_iff
    leechShift_mem_constructionBLattice_dualCarrier ?_ x
  rw [← leechShiftClass_def]
  exact two_nsmul_leechShiftClass

/-- The Golay Construction B lattice is a sublattice of the Leech lattice. -/
theorem constructionBLattice_carrier_le_leechLattice_carrier :
    constructionBLattice.carrier ≤ leechLattice.carrier :=
  fun x hx ↦ (mem_leechLattice_carrier_iff x).mpr (Or.inl hx)

/-- The odd shift lies in the Leech lattice. -/
theorem leechShift_mem_leechLattice_carrier : leechShift ∈ leechLattice.carrier :=
  (mem_leechLattice_carrier_iff _).mpr (Or.inr (by rw [sub_self]; exact zero_mem _))

/-- **The Golay Construction B lattice has index two in the Leech lattice.** -/
theorem relIndex_constructionBLattice_leechLattice :
    constructionBLattice.carrier.toAddSubgroup.relIndex leechLattice.carrier.toAddSubgroup = 2 := by
  rw [leechLattice_carrier, ← IntermediateCarrier.index_def,
    IntermediateCarrier.index_intermediateCarrierOfDiscriminantSubgroup,
    natCard_leechShiftSubgroup]

/-- The Leech lattice is nondegenerate. -/
instance instIsNondegenerateLeechLattice : leechLattice.IsNondegenerate :=
  instIsNondegenerateOfIsotropicSubgroup _ _ _ _

/-- **The Leech lattice is even.** -/
theorem isEven_leechLattice : leechLattice.IsEven :=
  isEven_ofIsotropicSubgroup _ _ _ _

/-- **The Leech lattice is unimodular**, being glued along a Lagrangian subgroup. -/
theorem isUnimodular_leechLattice : leechLattice.IsUnimodular :=
  (constructionBLattice.isUnimodular_ofIsotropicSubgroup_iff_isLagrangian _ _ _).mpr
    isLagrangian_leechShiftSubgroup.toFiniteBilinearModule

/-- The Leech lattice has discriminant one. -/
@[simp]
theorem discriminant_leechLattice : leechLattice.discriminant = 1 :=
  leechLattice.isUnimodular_iff_discriminant_eq_one.mp isUnimodular_leechLattice

/-- **The Leech lattice is positive definite.** -/
theorem isPosDef_leechLattice : leechLattice.IsPosDef :=
  (isPosDef_ofIsotropicSubgroup_iff _ _ _ _).mpr isPosDef_constructionBLattice

/-- The Leech lattice has rank `24`. -/
@[simp]
theorem finrank_leechLattice : Module.finrank ℤ leechLattice = 24 := by
  rw [finrank_carrier, Module.finrank_fintype_fun_eq_card, Fintype.card_fin]

/-- The odd shift is a vector of norm four in the Leech lattice. -/
theorem leechLattice_form_leechShift_leechShift : leechLattice.form leechShift leechShift = 4 := by
  rw [leechLattice_form, ← constructionBLattice_form,
    constructionBLattice_form_leechShift_leechShift]

end TauCeti
