/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.FreeGroup.IsFreeGroup
public import Mathlib.GroupTheory.Rank
public import TauCeti.GroupTheory.SurfaceGroup.Basic
import TauCeti.GroupTheory.FreeGroup.Rank

/-!
# Surface groups with boundary are free

The fundamental group of a compact surface with nonempty boundary is free. For the surface groups
`S±(g, m + 1)` of `TauCeti.GroupTheory.SurfaceGroup.Basic` this is a Tietze transformation: the
single defining relation

`[a₁, b₁] ⋯ [a_g, b_g] p₁ ⋯ p_{m+1} = 1`, respectively `c₁ ^ 2 ⋯ c_g ^ 2 p₁ ⋯ p_{m+1} = 1`,

expresses the last peripheral element `p_{m+1}` as the inverse of the product of the other
generators in the order of the relator, and eliminating `p_{m+1}` leaves no relation. Hence
`S⁺(g, m + 1)` is free on `a₁, b₁, …, a_g, b_g, p₁, …, p_m` and `S⁻(g, m + 1)` is free on
`c₁, …, c_g, p₁, …, p_m`. The ranks are `2g + m` and `g + m`, which in both cases is `1 - χ` for
the Euler characteristic `χ` of the surface.

## Main definitions

* `TauCeti.SurfaceGroup.Orientable.equivFreeGroup`:
  `S⁺(g, m + 1) ≃* FreeGroup (Fin g ⊕ Fin g ⊕ Fin m)`.
* `TauCeti.SurfaceGroup.Orientable.freeBasis`: the free basis `a₁, …, a_g, b₁, …, b_g, p₁, …, p_m`
  of `S⁺(g, m + 1)`.
* `TauCeti.SurfaceGroup.Nonorientable.equivFreeGroup`:
  `S⁻(g, m + 1) ≃* FreeGroup (Fin g ⊕ Fin m)`.
* `TauCeti.SurfaceGroup.Nonorientable.freeBasis`: the free basis `c₁, …, c_g, p₁, …, p_m` of
  `S⁻(g, m + 1)`.

## Main results

* `TauCeti.SurfaceGroup.Orientable.instIsFreeGroupSucc` and
  `TauCeti.SurfaceGroup.Nonorientable.instIsFreeGroupSucc`: surface groups with nonempty boundary
  are free.
* `TauCeti.SurfaceGroup.Orientable.rank_eq` and `TauCeti.SurfaceGroup.Nonorientable.rank_eq`: the
  ranks of `S⁺(g, m + 1)` and `S⁻(g, m + 1)` are `2 * g + m` and `g + m`.
* `TauCeti.SurfaceGroup.Orientable.rank_eq_one_sub_eulerChar` and
  `TauCeti.SurfaceGroup.Nonorientable.rank_eq_one_sub_eulerChar`: in both cases the rank is
  `1 - χ`.

## References

* V. Guirardel, G. Levitt, *JSJ decompositions of groups*, Astérisque 395 (2017), §5.1
  (compact surfaces with boundary, their boundary subgroups and Euler characteristic).
* O. Kharlampovich, A. Myasnikov, *Implicit function theorem over free groups*, J. Algebra 290
  (2005), §2.7, Definition 3 (the standard quadratic words, whose coefficient-free parts are the
  surface relators).
* R. C. Lyndon, P. E. Schupp, *Combinatorial Group Theory*, Chapter II, §2 (Tietze
  transformations).
-/

public section

namespace TauCeti

namespace SurfaceGroup

open FreeGroup (of)

namespace Orientable

/-- **Orientable surface groups with boundary are free.** The orientable surface group
`S⁺(g, m + 1)` is the free group on `a₁, …, a_g`, `b₁, …, b_g` and the peripheral elements
`p₁, …, p_m`; the last peripheral element is
`p_{m+1} = ([a₁, b₁] ⋯ [a_g, b_g] p₁ ⋯ p_m)⁻¹`. -/
def equivFreeGroup (g m : ℕ) : Orientable g (m + 1) ≃* FreeGroup (Fin g ⊕ Fin g ⊕ Fin m) :=
  MonoidHom.toMulEquiv
    (lift (fun i ↦ of (.inl i)) (fun i ↦ of (.inr (.inl i)))
      (Fin.snoc (α := fun _ ↦ FreeGroup (Fin g ⊕ Fin g ⊕ Fin m)) (fun j ↦ of (.inr (.inr j)))
        (orientableWord (fun i ↦ of (.inl i)) (fun i ↦ of (.inr (.inl i)))
          fun j ↦ of (.inr (.inr j)))⁻¹)
      (by rw [orientableWord_snoc, mul_inv_cancel]))
    (FreeGroup.lift <| Sum.elim (a g (m + 1)) <| Sum.elim (b g (m + 1)) fun j ↦
      peripheral g (m + 1) j.castSucc)
    (hom_ext (by simp) (by simp) fun j ↦ by
      induction j using Fin.lastCases with
      | last =>
        simp [peripheral_last, orientableWord_def, map_list_prod, List.map_ofFn, Function.comp_def]
      | cast j => simp)
    (FreeGroup.ext_hom _ _ <| by rintro (i | i | j) <;> simp)

variable {g m : ℕ}

@[simp]
theorem equivFreeGroup_a (i : Fin g) : equivFreeGroup g m (a g (m + 1) i) = of (.inl i) := by
  simp [equivFreeGroup]

@[simp]
theorem equivFreeGroup_b (i : Fin g) : equivFreeGroup g m (b g (m + 1) i) = of (.inr (.inl i)) := by
  simp [equivFreeGroup]

@[simp]
theorem equivFreeGroup_peripheral_castSucc (j : Fin m) :
    equivFreeGroup g m (peripheral g (m + 1) j.castSucc) = of (.inr (.inr j)) := by
  simp [equivFreeGroup]

variable (g m) in
@[simp]
theorem equivFreeGroup_peripheral_last :
    equivFreeGroup g m (peripheral g (m + 1) (Fin.last m)) =
      (orientableWord (fun i ↦ of (.inl i)) (fun i ↦ of (.inr (.inl i)))
        fun j ↦ of (.inr (.inr j)) : FreeGroup (Fin g ⊕ Fin g ⊕ Fin m))⁻¹ := by
  simp [equivFreeGroup]

@[simp]
theorem equivFreeGroup_symm_of_inl (i : Fin g) :
    (equivFreeGroup g m).symm (of (.inl i)) = a g (m + 1) i := by
  simp [equivFreeGroup]

@[simp]
theorem equivFreeGroup_symm_of_inr_inl (i : Fin g) :
    (equivFreeGroup g m).symm (of (.inr (.inl i))) = b g (m + 1) i := by
  simp [equivFreeGroup]

@[simp]
theorem equivFreeGroup_symm_of_inr_inr (j : Fin m) :
    (equivFreeGroup g m).symm (of (.inr (.inr j))) = peripheral g (m + 1) j.castSucc := by
  simp [equivFreeGroup]

variable (g m) in
/-- The free basis `a₁, …, a_g, b₁, …, b_g, p₁, …, p_m` of the orientable surface group
`S⁺(g, m + 1)`. -/
def freeBasis : FreeGroupBasis (Fin g ⊕ Fin g ⊕ Fin m) (Orientable g (m + 1)) :=
  .ofRepr (equivFreeGroup g m)

@[simp]
theorem freeBasis_inl (i : Fin g) : freeBasis g m (.inl i) = a g (m + 1) i :=
  equivFreeGroup_symm_of_inl i

@[simp]
theorem freeBasis_inr_inl (i : Fin g) : freeBasis g m (.inr (.inl i)) = b g (m + 1) i :=
  equivFreeGroup_symm_of_inr_inl i

@[simp]
theorem freeBasis_inr_inr (j : Fin m) :
    freeBasis g m (.inr (.inr j)) = peripheral g (m + 1) j.castSucc :=
  equivFreeGroup_symm_of_inr_inr j

variable (g m)

/-- An orientable surface group with nonempty boundary is free. -/
instance instIsFreeGroupSucc : IsFreeGroup (Orientable g (m + 1)) :=
  (freeBasis g m).isFreeGroup

/-- An orientable surface group with nonempty boundary is finitely generated. -/
instance instFGSucc : Group.FG (Orientable g (m + 1)) :=
  (freeBasis g m).fg_iff_finite.mpr inferInstance

/-- The orientable surface group `S⁺(g, m + 1)` has rank `2g + m`. -/
theorem rank_eq : Group.rank (Orientable g (m + 1)) = 2 * g + m := by
  rw [(freeBasis g m).rank_eq_nat_card]
  simp [two_mul, add_assoc]

/-- The rank of an orientable surface group with nonempty boundary is `1 - χ`, where `χ` is the
Euler characteristic of the surface. -/
theorem rank_eq_one_sub_eulerChar :
    (Group.rank (Orientable g (m + 1)) : ℤ) = 1 - eulerChar g (m + 1) := by
  rw [rank_eq, eulerChar_def]
  lia

end Orientable

namespace Nonorientable

/-- **Nonorientable surface groups with boundary are free.** The nonorientable surface group
`S⁻(g, m + 1)` is the free group on `c₁, …, c_g` and the peripheral elements `p₁, …, p_m`; the
last peripheral element is `p_{m+1} = (c₁ ^ 2 ⋯ c_g ^ 2 p₁ ⋯ p_m)⁻¹`. -/
def equivFreeGroup (g m : ℕ) : Nonorientable g (m + 1) ≃* FreeGroup (Fin g ⊕ Fin m) :=
  MonoidHom.toMulEquiv
    (lift (fun i ↦ of (.inl i))
      (Fin.snoc (α := fun _ ↦ FreeGroup (Fin g ⊕ Fin m)) (fun j ↦ of (.inr j))
        (nonorientableWord (fun i ↦ of (.inl i)) fun j ↦ of (.inr j))⁻¹)
      (by rw [nonorientableWord_snoc, mul_inv_cancel]))
    (FreeGroup.lift <| Sum.elim (c g (m + 1)) fun j ↦ peripheral g (m + 1) j.castSucc)
    (hom_ext (by simp) fun j ↦ by
      induction j using Fin.lastCases with
      | last =>
        simp [peripheral_last, nonorientableWord_def, map_list_prod, List.map_ofFn,
          Function.comp_def]
      | cast j => simp)
    (FreeGroup.ext_hom _ _ <| by rintro (i | j) <;> simp)

variable {g m : ℕ}

@[simp]
theorem equivFreeGroup_c (i : Fin g) : equivFreeGroup g m (c g (m + 1) i) = of (.inl i) := by
  simp [equivFreeGroup]

@[simp]
theorem equivFreeGroup_peripheral_castSucc (j : Fin m) :
    equivFreeGroup g m (peripheral g (m + 1) j.castSucc) = of (.inr j) := by
  simp [equivFreeGroup]

variable (g m) in
@[simp]
theorem equivFreeGroup_peripheral_last :
    equivFreeGroup g m (peripheral g (m + 1) (Fin.last m)) =
      (nonorientableWord (fun i ↦ of (.inl i)) fun j ↦ of (.inr j) :
        FreeGroup (Fin g ⊕ Fin m))⁻¹ := by
  simp [equivFreeGroup]

@[simp]
theorem equivFreeGroup_symm_of_inl (i : Fin g) :
    (equivFreeGroup g m).symm (of (.inl i)) = c g (m + 1) i := by
  simp [equivFreeGroup]

@[simp]
theorem equivFreeGroup_symm_of_inr (j : Fin m) :
    (equivFreeGroup g m).symm (of (.inr j)) = peripheral g (m + 1) j.castSucc := by
  simp [equivFreeGroup]

variable (g m) in
/-- The free basis `c₁, …, c_g, p₁, …, p_m` of the nonorientable surface group
`S⁻(g, m + 1)`. -/
def freeBasis : FreeGroupBasis (Fin g ⊕ Fin m) (Nonorientable g (m + 1)) :=
  .ofRepr (equivFreeGroup g m)

@[simp]
theorem freeBasis_inl (i : Fin g) : freeBasis g m (.inl i) = c g (m + 1) i :=
  equivFreeGroup_symm_of_inl i

@[simp]
theorem freeBasis_inr (j : Fin m) : freeBasis g m (.inr j) = peripheral g (m + 1) j.castSucc :=
  equivFreeGroup_symm_of_inr j

variable (g m)

/-- A nonorientable surface group with nonempty boundary is free. -/
instance instIsFreeGroupSucc : IsFreeGroup (Nonorientable g (m + 1)) :=
  (freeBasis g m).isFreeGroup

/-- A nonorientable surface group with nonempty boundary is finitely generated. -/
instance instFGSucc : Group.FG (Nonorientable g (m + 1)) :=
  (freeBasis g m).fg_iff_finite.mpr inferInstance

/-- The nonorientable surface group `S⁻(g, m + 1)` has rank `g + m`. -/
theorem rank_eq : Group.rank (Nonorientable g (m + 1)) = g + m := by
  rw [(freeBasis g m).rank_eq_nat_card]
  simp

/-- The rank of a nonorientable surface group with nonempty boundary is `1 - χ`, where `χ` is the
Euler characteristic of the surface. -/
theorem rank_eq_one_sub_eulerChar :
    (Group.rank (Nonorientable g (m + 1)) : ℤ) = 1 - eulerChar g (m + 1) := by
  rw [rank_eq, eulerChar_def]
  lia

end Nonorientable

end SurfaceGroup

end TauCeti
