/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import TauCeti.Analysis.Complex.Circle
public import TauCeti.Topology.Homotopy.AddCircle
public import TauCeti.Topology.Homotopy.LusternikSchnirelmann.Sphere
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# The Lusternik–Schnirelmann category of a torus

The torus `Tᵐ = ∀ i, AddCircle (p i)`, with `m = card ι` factors of positive periods `p i`, has
Lusternik–Schnirelmann count `m + 1` (`TauCeti.lsCategoryCount_univ_pi_addCircle`): it is covered
by `m + 1` open sets whose inclusions are nullhomotopic, and by no fewer. Its normalized category
and its cup length over every nontrivial commutative ring are both `m`.

The lower bound is the cup-length bound: `Tᵐ` is a product of `m` circles, and a product of `m`
spheres of positive dimension has cup length at least `m`
(`TauCeti.natCast_le_normalizedLSCategory_pi_sphere`).

The upper bound is an explicit cover adapted to the cells of the product CW structure of `Tᵐ`,
whose open cells are indexed by the subsets `S` of the factors: the cell `e_S` consists of the
points whose coordinates are nonzero exactly at the indices in `S`. Its open neighbourhood `V_S`
consists of the points `x` with `x i ≠ p i / 2` for `i ∉ S`, with `x j ≠ 0` for `j ∈ S`, and with
`‖x i‖ < ‖x j‖` whenever `i ∉ S` and `j ∈ S`.

* Every coordinate of a point of `V_S` avoids one point of its circle, and the circle with a point
  removed contracts in the circle (`AddCircle.nullhomotopic_subtypeVal_compl_singleton`), so the
  inclusion of `V_S` is nullhomotopic (`ContinuousMap.Nullhomotopic.pi`).
* For two distinct sets `S` and `S'` with the same number `k` of elements, some `i ∈ S \ S'` and
  `j ∈ S' \ S` would satisfy both `‖x j‖ < ‖x i‖` and `‖x i‖ < ‖x j‖` on `V_S ∩ V_S'`, so these
  neighbourhoods are disjoint and their union `U_k` is again categorical
  (`TauCeti.nullhomotopic_subtypeVal_iUnion`).
* Every point lies in the cell `e_S` of its set `S` of nonzero coordinates, so the `m + 1` sets
  `U_0, …, U_m` cover `Tᵐ`.

## Main results

* `TauCeti.lsCategoryCount_univ_pi_addCircle_le`: the torus `Tᵐ` has a categorical cover by
  `m + 1` open sets.
* `TauCeti.lsCategoryCount_univ_pi_addCircle` and `TauCeti.normalizedLSCategory_pi_addCircle`: the
  torus `Tᵐ` has count `m + 1` and normalized category `m`.
* `TauCeti.lsCupLength_pi_addCircle`: the cup length of `Tᵐ` is `m` over every nontrivial
  commutative ring.

## References

* O. Cornea, G. Lupton, J. Oprea and D. Tanré, *Lusternik–Schnirelmann Category*, Mathematical
  Surveys and Monographs 103, American Mathematical Society, 2003, Chapter 1, for the category of
  a torus and the bound of the category of a CW complex by its dimension through thickened open
  cells.
-/

public section

noncomputable section

open Set ContinuousMap TopologicalSpace Topology Module Metric
open scoped Function

universe u

namespace TauCeti

variable {ι : Type u} (p : ι → ℝ)

section Cells

variable [DecidableEq ι]

/-- The point avoided by the `i`-th coordinate on the neighbourhood of the cell indexed by `S`:
`0` if `i ∈ S`, and the half period `p i / 2` otherwise. -/
private def torusCellAvoided (S : Finset ι) (i : ι) : AddCircle (p i) :=
  if i ∈ S then 0 else ((p i / 2 : ℝ) : AddCircle (p i))

/-- The open neighbourhood `V_S` of the open cell of the torus indexed by `S`: the points `x` with
`x i ≠ p i / 2` for `i ∉ S`, with `x j ≠ 0` for `j ∈ S`, and with `‖x i‖ < ‖x j‖` whenever
`i ∉ S` and `j ∈ S`. -/
private def torusCellNhd (S : Finset ι) : Set (∀ i, AddCircle (p i)) :=
  {x | (∀ i, x i ≠ torusCellAvoided p S i) ∧ ∀ i ∉ S, ∀ j ∈ S, ‖x i‖ < ‖x j‖}

variable {p}

private theorem isOpen_torusCellNhd [Finite ι] (S : Finset ι) : IsOpen (torusCellNhd p S) := by
  have : torusCellNhd p S = (⋂ i, {x | x i ≠ torusCellAvoided p S i}) ∩
      ⋂ i, ⋂ (_ : i ∉ S), ⋂ j, ⋂ (_ : j ∈ S), {x | ‖x i‖ < ‖x j‖} := by
    ext
    simp [torusCellNhd]
  rw [this]
  exact (isOpen_iInter_of_finite fun i ↦ isOpen_ne_fun (continuous_apply i) continuous_const).inter
    (isOpen_iInter_of_finite fun i ↦ isOpen_iInter_of_finite fun _ ↦ isOpen_iInter_of_finite
      fun j ↦ isOpen_iInter_of_finite fun _ ↦ isOpen_lt (by fun_prop) (by fun_prop))

/-- The inclusion of `V_S` is nullhomotopic, since each coordinate avoids a point of its circle. -/
private theorem nullhomotopic_subtypeVal_torusCellNhd [∀ i, Fact (0 < p i)] (S : Finset ι) :
    (subtypeVal (torusCellNhd p S)).Nullhomotopic :=
  ContinuousMap.Nullhomotopic.pi fun i ↦
    (AddCircle.nullhomotopic_subtypeVal_compl_singleton (torusCellAvoided p S i)).comp_left
      ⟨fun x : torusCellNhd p S ↦ ⟨x.1 i, x.2.1 i⟩,
        ((continuous_apply i).comp continuous_subtype_val).subtype_mk _⟩

/-- Every point lies in the neighbourhood `V_S` of the cell of its set `S` of nonzero
coordinates. -/
private theorem mem_torusCellNhd [∀ i, Fact (0 < p i)] {x : ∀ i, AddCircle (p i)} {S : Finset ι}
    (hS : ∀ j, j ∈ S ↔ x j ≠ 0) : x ∈ torusCellNhd p S := by
  refine ⟨fun i ↦ ?_, fun i hi j hj ↦ ?_⟩
  · by_cases hx : x i = 0
    · have : ((p i / 2 : ℝ) : AddCircle (p i)) ≠ 0 := by
        rw [← norm_pos_iff, AddCircle.norm_half_period_eq]
        have := (Fact.out : 0 < p i)
        positivity
      simp [torusCellAvoided, hS, hx, this.symm]
    · simp [torusCellAvoided, hS, hx]
  · rw [hS, not_not] at hi
    rw [hi, norm_zero, norm_pos_iff]
    exact (hS j).1 hj

/-- Two of the neighbourhoods `V_S` and `V_S'` with `S ≠ S'` of the same size are disjoint. -/
private theorem disjoint_torusCellNhd {S S' : Finset ι} (hS : S.card = S'.card) (h : S ≠ S') :
    Disjoint (torusCellNhd p S) (torusCellNhd p S') := by
  obtain ⟨i, hiS, hiS'⟩ := Finset.not_subset.1 fun hsub ↦ h (Finset.eq_of_subset_of_card_le hsub
    hS.ge)
  obtain ⟨j, hjS', hjS⟩ := Finset.not_subset.1 fun hsub ↦ h (Finset.eq_of_subset_of_card_le hsub
    hS.le).symm
  exact disjoint_left.2 fun x hx hx' ↦ (hx.2 j hjS i hiS).not_gt (hx'.2 i hiS' j hjS')

end Cells

variable {p} [Fintype ι] [∀ i, Fact (0 < p i)]

/-- **The torus has a categorical cover by `m + 1` open sets.** The `k`-th open set is the union of
the disjoint neighbourhoods of the open cells of dimension `k` of the product CW structure. -/
theorem lsCategoryCount_univ_pi_addCircle_le :
    lsCategoryCount (∀ i, AddCircle (p i)) univ ≤ Fintype.card ι + 1 := by
  classical
  let U (k : Fin (Fintype.card ι + 1)) : Opens (∀ i, AddCircle (p i)) :=
    ⟨⋃ S : {S : Finset ι // S.card = k}, torusCellNhd p S,
      isOpen_iUnion fun S ↦ isOpen_torusCellNhd S.1⟩
  have hcover : univ ⊆ ⋃ k, (U k : Set (∀ i, AddCircle (p i))) := fun x _ ↦
    mem_iUnion.2 ⟨⟨_, Nat.lt_succ_of_le (Finset.card_le_univ {j | x j ≠ 0})⟩,
      mem_iUnion.2 ⟨⟨_, rfl⟩, mem_torusCellNhd (by simp)⟩⟩
  have hnull (k : Fin (Fintype.card ι + 1)) :
      (subtypeVal (U k : Set (∀ i, AddCircle (p i)))).Nullhomotopic :=
    nullhomotopic_subtypeVal_iUnion (fun S ↦ isOpen_torusCellNhd S.1)
      (fun S S' h ↦ disjoint_torusCellNhd (S.2.trans S'.2.symm) (Subtype.coe_ne_coe.2 h))
      fun S ↦ nullhomotopic_subtypeVal_torusCellNhd S.1
  exact_mod_cast (LSCategoricalCover.mk U hcover hnull).lsCategoryCount_le

variable (p) in
/-- The torus `Tᵐ` is homeomorphic to the product of `m` copies of the unit circle of `ℂ`, lifted
to the universe of the index type so that cup lengths can be compared. -/
private def piAddCircleHomeomorphPiSphere :
    (∀ i, AddCircle (p i)) ≃ₜ (Fin (Fintype.card ι) → sphere (0 : ULift.{u} ℂ) 1) :=
  (Homeomorph.piCongrRight fun i ↦ ((AddCircle.homeomorphCircle (Fact.out : 0 < p i).ne').trans
      Circle.homeomorphSphere).trans
        (Homeomorph.ulift.subtype fun x ↦ by simp [Homeomorph.ulift]).symm).trans
    (Homeomorph.piCongrLeft (Y := fun _ ↦ sphere (0 : ULift.{u} ℂ) 1) (Fintype.equivFin ι))

/-- **The normalized Lusternik–Schnirelmann category of the torus `Tᵐ` is `m`.** -/
@[simp]
theorem normalizedLSCategory_pi_addCircle :
    normalizedLSCategory (∀ i, AddCircle (p i)) = Fintype.card ι := by
  refine le_antisymm ?_ ?_
  · rw [normalizedLSCategory_le_iff]
    exact lsCategoryCount_univ_pi_addCircle_le
  · rw [(piAddCircleHomeomorphPiSphere p).normalizedLSCategory_eq]
    exact natCast_le_normalizedLSCategory_pi_sphere (fun _ ↦ ULift.{u} ℂ) fun _ ↦
      (ULift.moduleEquiv.finrank_eq.trans Complex.finrank_real_complex).ge

/-- **The Lusternik–Schnirelmann count of the torus `Tᵐ` is `m + 1`.** -/
@[simp]
theorem lsCategoryCount_univ_pi_addCircle :
    lsCategoryCount (∀ i, AddCircle (p i)) univ = Fintype.card ι + 1 := by
  rw [lsCategoryCount_univ_eq_normalizedLSCategory_add_one, normalizedLSCategory_pi_addCircle]

/-- **The cup length of the torus `Tᵐ` is `m`** over every nontrivial commutative ring: the
product of the classes of the `m` circle factors is nonzero, and the normalized category `m`
bounds the cup length above. -/
@[simp]
theorem lsCupLength_pi_addCircle (R : Type u) [CommRing R] [Nontrivial R] :
    lsCupLength (∀ i, AddCircle (p i)) R = Fintype.card ι := by
  refine le_antisymm (lsCupLength_le_normalizedLSCategory.trans_eq
    (normalizedLSCategory_pi_addCircle (p := p))) ?_
  rw [(piAddCircleHomeomorphPiSphere p).toHomotopyEquiv.lsCupLength_eq]
  exact natCast_le_lsCupLength_pi_sphere (fun _ ↦ ULift.{u} ℂ)
    (fun _ ↦ (ULift.moduleEquiv.finrank_eq.trans Complex.finrank_real_complex).ge) R

end TauCeti
