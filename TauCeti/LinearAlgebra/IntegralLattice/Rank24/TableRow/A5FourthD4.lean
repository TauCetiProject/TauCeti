/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.IntegralLattice.Rank24.TableRow.Symmetry
public import TauCeti.LinearAlgebra.IntegralLattice.RootLattice.TypeD.Triality

/-!
# The coupled triality symmetry of the table row `A₅⁴ D₄`

In the rootful rank-24 table, `TauCeti.RootfulNiemeierType.a5FourthD4` is the unique row whose
parenthesized pattern symmetry is not a pure coordinate glue symmetry: its glue columns are
`[2(024)0]`, `[33001]`, `[30302]`, and `[30033]`, and rotating the three marked `A₅` positions
`1, 2, 3` while leaving the `D₄` label in position `4` unchanged sends `[33001]` outside the glue
subgroup (`a5FourthD4BlockRot_notMem_glueSymmetries`).

Because the three literal generators cycle the nonzero `D₄` labels `1 ↦ 2 ↦ 3 ↦ 1` (`s ↦ v ↦ c ↦ s`)
in lockstep with the three marked `A₅` positions, coupling the block rotation with `D₄` triality
(`TauCeti.DynkinType.typeD4Triality`) on the `D₄` component preserves `a5FourthD4.glueSubgroup` and
lifts to an order-three self-isometry `TauCeti.RootfulNiemeierType.a5FourthD4TrialityRotation` of
`TauCeti.niemeierA5FourthD4`.  This yields a faithful action
`TauCeti.RootfulNiemeierType.a5FourthD4CyclicSymmetryHom` of the cyclic pattern's symmetry group,
and hence a faithful lattice action `TauCeti.RootfulNiemeierType.coupledPatternIsometryHom` for
every pattern of every row of the rootful rank-24 table without exception.

## Main declarations

* `TauCeti.RootfulNiemeierType.a5FourthD4BlockRot`: the cyclic rotation of positions `1, 2, 3`
  generating `(GluePattern.cyclic [2] [0, 2, 4] [0]).symmetries`, of order three
  (`orderOf_a5FourthD4BlockRot`).
* `TauCeti.RootfulNiemeierType.a5FourthD4BlockRot_notMem_glueSymmetries`: the uncoupled block
  rotation is not a glue symmetry of `a5FourthD4`.
* `TauCeti.RootfulNiemeierType.a5FourthD4TrialityRotation`: the order-three self-isometry
  (`orderOf_a5FourthD4TrialityRotation`) of `niemeierA5FourthD4` rotating the three marked `A₅`
  components and applying `typeD4Triality` on the `D₄` component.
* `TauCeti.RootfulNiemeierType.mem_symmetries_cyclic_a5FourthD4_iff`,
  `TauCeti.RootfulNiemeierType.a5FourthD4CyclicSymmetryHom`: membership characterization and
  faithful action of `(GluePattern.cyclic [2] [0, 2, 4] [0]).symmetries` on `niemeierA5FourthD4`.
* `TauCeti.RootfulNiemeierType.coupledPatternIsometryHom`,
  `TauCeti.RootfulNiemeierType.coupledPatternIsometryHom_injective`: faithful action of every
  pattern symmetry group across all 23 rootful Niemeier rows.

## References

* J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, 3rd ed., Chapter 4
  §§3 and 7, and Chapter 16 §1, Table 16.1.
-/

public section

namespace TauCeti

namespace RootfulNiemeierType

open DynkinType IntegralLattice

/-! ### The marked-block rotation of `[2(024)0]` and its uncoupled obstruction -/

/-- **The marked-block rotation of `A₅⁴ D₄`**: the 3-cycle `1 ↦ 2 ↦ 3 ↦ 1` fixing positions `0` and
`4`, which generates `(GluePattern.cyclic [2] [0, 2, 4] [0]).symmetries`. -/
def a5FourthD4BlockRot : Equiv.Perm (Fin 5) :=
  Equiv.Perm.finSumPerm (Equiv.Perm.finSumPerm (1 : Equiv.Perm (Fin 1)) (finRotate 3))
    (1 : Equiv.Perm (Fin 1))

/-- `a5FourthD4BlockRot` is the 3-cycle `swap 1 2 * swap 2 3` on `Fin 5`. -/
theorem a5FourthD4BlockRot_eq_swap_mul_swap :
    a5FourthD4BlockRot = Equiv.swap 1 2 * Equiv.swap 2 3 := by
  apply Equiv.ext
  intro i
  -- Write each element of `Fin 5` in `Fin (1 + 3 + 1)` block form so `finSumPerm_apply_*` applies.
  fin_cases i
  · change a5FourthD4BlockRot (Fin.castAdd 1 (Fin.castAdd 3 (0 : Fin 1))) = _
    rw [a5FourthD4BlockRot, Equiv.Perm.finSumPerm_apply_castAdd,
      Equiv.Perm.finSumPerm_apply_castAdd]
    decide
  · change a5FourthD4BlockRot (Fin.castAdd 1 (Fin.natAdd 1 (0 : Fin 3))) = _
    rw [a5FourthD4BlockRot, Equiv.Perm.finSumPerm_apply_castAdd,
      Equiv.Perm.finSumPerm_apply_natAdd]
    decide
  · change a5FourthD4BlockRot (Fin.castAdd 1 (Fin.natAdd 1 (1 : Fin 3))) = _
    rw [a5FourthD4BlockRot, Equiv.Perm.finSumPerm_apply_castAdd,
      Equiv.Perm.finSumPerm_apply_natAdd]
    decide
  · change a5FourthD4BlockRot (Fin.castAdd 1 (Fin.natAdd 1 (2 : Fin 3))) = _
    rw [a5FourthD4BlockRot, Equiv.Perm.finSumPerm_apply_castAdd,
      Equiv.Perm.finSumPerm_apply_natAdd]
    decide
  · change a5FourthD4BlockRot (Fin.natAdd 4 (0 : Fin 1)) = _
    rw [a5FourthD4BlockRot, Equiv.Perm.finSumPerm_apply_natAdd]
    decide

@[simp]
theorem a5FourthD4BlockRot_zero : a5FourthD4BlockRot 0 = 0 := by
  rw [a5FourthD4BlockRot_eq_swap_mul_swap]; decide

@[simp]
theorem a5FourthD4BlockRot_one : a5FourthD4BlockRot 1 = 2 := by
  rw [a5FourthD4BlockRot_eq_swap_mul_swap]; decide

@[simp]
theorem a5FourthD4BlockRot_two : a5FourthD4BlockRot 2 = 3 := by
  rw [a5FourthD4BlockRot_eq_swap_mul_swap]; decide

@[simp]
theorem a5FourthD4BlockRot_three : a5FourthD4BlockRot 3 = 1 := by
  rw [a5FourthD4BlockRot_eq_swap_mul_swap]; decide

@[simp]
theorem a5FourthD4BlockRot_four : a5FourthD4BlockRot 4 = 4 := by
  rw [a5FourthD4BlockRot_eq_swap_mul_swap]; decide

@[simp]
theorem a5FourthD4BlockRot_inv_zero : a5FourthD4BlockRot⁻¹ 0 = 0 := by
  rw [a5FourthD4BlockRot_eq_swap_mul_swap]; decide

@[simp]
theorem a5FourthD4BlockRot_inv_one : a5FourthD4BlockRot⁻¹ 1 = 3 := by
  rw [a5FourthD4BlockRot_eq_swap_mul_swap]; decide

@[simp]
theorem a5FourthD4BlockRot_inv_two : a5FourthD4BlockRot⁻¹ 2 = 1 := by
  rw [a5FourthD4BlockRot_eq_swap_mul_swap]; decide

@[simp]
theorem a5FourthD4BlockRot_inv_three : a5FourthD4BlockRot⁻¹ 3 = 2 := by
  rw [a5FourthD4BlockRot_eq_swap_mul_swap]; decide

@[simp]
theorem a5FourthD4BlockRot_inv_four : a5FourthD4BlockRot⁻¹ 4 = 4 := by
  rw [a5FourthD4BlockRot_eq_swap_mul_swap]; decide

/-- `a5FourthD4BlockRot` has order three. -/
@[simp]
theorem a5FourthD4BlockRot_pow_three : a5FourthD4BlockRot ^ 3 = 1 := by
  rw [a5FourthD4BlockRot_eq_swap_mul_swap]; decide

/-- The inverse of `a5FourthD4BlockRot` is its square. -/
theorem a5FourthD4BlockRot_inv : a5FourthD4BlockRot⁻¹ = a5FourthD4BlockRot ^ 2 := by
  rw [a5FourthD4BlockRot_eq_swap_mul_swap]; decide

/-- `a5FourthD4BlockRot` has exact order `3`. -/
@[simp]
theorem orderOf_a5FourthD4BlockRot : orderOf a5FourthD4BlockRot = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine orderOf_eq_prime a5FourthD4BlockRot_pow_three fun h ↦ ?_
  have h1 := Equiv.congr_fun h 1
  simp at h1

/-- `a5FourthD4BlockRot` belongs to the symmetry group of the cyclic pattern `[2(024)0]`. -/
theorem a5FourthD4BlockRot_mem_symmetries :
    a5FourthD4BlockRot ∈ (GluePattern.cyclic [2] [0, 2, 4] [0]).symmetries := by
  rw [GluePattern.symmetries_cyclic]
  exact Subgroup.mem_zpowers _

private theorem glueLabelWord_mem_a5FourthD4_glueSubgroup
    (d : ∀ i : Fin a5FourthD4.components.length, Fin (a5FourthD4.componentType i).glueLabelCount)
    (hd : (List.ofFn fun i ↦ (d i).val) ∈ a5FourthD4.glueWords) :
    (fun i ↦ (a5FourthD4.componentType i).glueLabelEquiv
      (a5FourthD4.isSimplyLaced_componentType i) (d i)) ∈ a5FourthD4.glueSubgroup := by
  rw [glueSubgroup_def]
  refine AddSubgroup.subset_closure (mem_glueGenerators_iff.mpr ?_)
  rwa [encodeGlueWord_glueLabelEquiv]

/-- **The uncoupled block rotation of `[2(024)0]` is not a glue symmetry of `A₅⁴ D₄`**: reindexing
`[33001]` along `a5FourthD4BlockRot` gives `[30031]`, whose sum with `[30033]` is the nonzero glue
word `[00002]` of shortest norm `1 < 4`. -/
theorem a5FourthD4BlockRot_notMem_glueSymmetries :
    (a5FourthD4BlockRot : Equiv.Perm (Fin a5FourthD4.components.length)) ∉
      a5FourthD4.glueSymmetries := by
  intro hrot
  let d₁ : ∀ i : Fin 5, Fin (a5FourthD4.componentType i).glueLabelCount :=
    fun i ↦ ⟨![3, 3, 0, 0, 1] i, by fin_cases i <;> decide⟩
  let d₃ : ∀ i : Fin 5, Fin (a5FourthD4.componentType i).glueLabelCount :=
    fun i ↦ ⟨![3, 0, 0, 3, 3] i, by fin_cases i <;> decide⟩
  let w₁ : a5FourthD4.glueModule := fun i ↦
    (a5FourthD4.componentType i).glueLabelEquiv (a5FourthD4.isSimplyLaced_componentType i) (d₁ i)
  let w₃ : a5FourthD4.glueModule := fun i ↦
    (a5FourthD4.componentType i).glueLabelEquiv (a5FourthD4.isSimplyLaced_componentType i) (d₃ i)
  let v := piGlueAlphabetCongr a5FourthD4.componentType a5FourthD4.isSimplyLaced_componentType
    a5FourthD4BlockRot (a5FourthD4.componentType_apply_of_mem_glueSymmetries hrot)
    (hs := a5FourthD4.isSimplyLaced_componentType) w₁
  have hv : v ∈ a5FourthD4.glueSubgroup :=
    (a5FourthD4.piGlueAlphabetCongr_mem_glueSubgroup_iff hrot w₁).mpr
      (glueLabelWord_mem_a5FourthD4_glueSubgroup d₁ (by decide))
  have hw₃ : w₃ ∈ a5FourthD4.glueSubgroup :=
    glueLabelWord_mem_a5FourthD4_glueSubgroup d₃ (by decide)
  have hv_enc : encodeGlueWord a5FourthD4.componentType a5FourthD4.isSimplyLaced_componentType v =
      [3, 0, 0, 3, 1] := by
    refine (encodeGlueWord_piGlueAlphabetCongr_eq_ofFn _ _ _ _ _ w₁).trans ?_
    refine (congrArg List.ofFn (funext fun k : Fin 5 ↦
      congrArg Fin.val (Equiv.symm_apply_apply _ (d₁ (a5FourthD4BlockRot k))))).trans ?_
    dsimp only [d₁]
    rw [a5FourthD4BlockRot_eq_swap_mul_swap]
    decide
  have hw₃_enc :
      encodeGlueWord a5FourthD4.componentType a5FourthD4.isSimplyLaced_componentType w₃ =
        [3, 0, 0, 3, 3] := by
    rw [encodeGlueWord_glueLabelEquiv]
    decide
  have henc : encodeGlueWord a5FourthD4.componentType a5FourthD4.isSimplyLaced_componentType
      (v + w₃) = [0, 0, 0, 0, 2] := by
    refine (encodeGlueWord_add _ _ v w₃).trans ?_
    rw [hv_enc, hw₃_enc]
    decide +kernel
  have hne : v + w₃ ≠ 0 := fun h0 ↦ absurd
    (henc.symm.trans ((congrArg (encodeGlueWord a5FourthD4.componentType
      a5FourthD4.isSimplyLaced_componentType) h0).trans (encodeGlueWord_zero _ _))) (by decide)
  have hmin := four_le_sum_glueMinimum_of_mem_glueSubgroup a5FourthD4 (add_mem hv hw₃) hne
  rw [← glueWordMinimum_encodeGlueWord, henc] at hmin
  exact absurd hmin (by decide +kernel)

/-! ### Lifting `[2(024)0]` to `niemeierA5FourthD4` via `D₄` triality -/

private theorem componentType_a5FourthD4BlockRot_inv (k : Fin a5FourthD4.components.length) :
    a5FourthD4.componentType ((a5FourthD4BlockRot⁻¹ : Equiv.Perm (Fin 5)) k) =
      a5FourthD4.componentType k := by
  have h : ∀ j : Fin 5,
      a5FourthD4.componentType (a5FourthD4BlockRot⁻¹ j) = a5FourthD4.componentType j
    | 0 => by rw [a5FourthD4BlockRot_inv_zero]
    | 1 => by rw [a5FourthD4BlockRot_inv_one]; rfl
    | 2 => by rw [a5FourthD4BlockRot_inv_two]; rfl
    | 3 => by rw [a5FourthD4BlockRot_inv_three]; rfl
    | 4 => by rw [a5FourthD4BlockRot_inv_four]
  exact h k

private noncomputable def a5FourthD4ComponentIsometry :
    ∀ k : Fin a5FourthD4.components.length, Isometry
      ((a5FourthD4.componentType k).rootLattice (a5FourthD4.isSimplyLaced_componentType k))
      ((a5FourthD4.componentType k).rootLattice (a5FourthD4.isSimplyLaced_componentType k))
  | ⟨0, _⟩ | ⟨1, _⟩ | ⟨2, _⟩ | ⟨3, _⟩ => Isometry.refl _
  | ⟨4, h⟩ => typeD4Triality (a5FourthD4.isSimplyLaced_componentType ⟨4, h⟩)
  | ⟨_ + 5, h⟩ => False.elim (Nat.not_lt_of_ge (Nat.le_add_left 5 _) h)

private noncomputable def a5FourthD4ComponentGlueEquiv
    (k : Fin a5FourthD4.components.length) :
    (a5FourthD4.componentType k).glueAlphabet (a5FourthD4.isSimplyLaced_componentType k) ≃+
      (a5FourthD4.componentType k).glueAlphabet (a5FourthD4.isSimplyLaced_componentType k) :=
  (glueAlphabetIsometryOfIsometry (a5FourthD4.valid_componentType k)
    (a5FourthD4.valid_componentType k) (a5FourthD4ComponentIsometry k)).toLinearEquiv.toAddEquiv

private def a5FourthD4DigitPerm : Fin a5FourthD4.components.length → ℕ → ℕ
  | ⟨0, _⟩ | ⟨1, _⟩ | ⟨2, _⟩ | ⟨3, _⟩ => id
  | ⟨4, _⟩ => fun n ↦ if hn : n < 4 then (typeD4TrialityLabelPerm ⟨n, hn⟩).val else n
  | ⟨_ + 5, h⟩ => False.elim (Nat.not_lt_of_ge (Nat.le_add_left 5 _) h)

private theorem a5FourthD4ComponentIsometry_glueAlphabetIsometry
    (k : Fin a5FourthD4.components.length)
    (x : (a5FourthD4.componentType k).glueAlphabet (a5FourthD4.isSimplyLaced_componentType k)) :
    (a5FourthD4.componentType k).glueAlphabetIsometry (a5FourthD4.valid_componentType k)
        (a5FourthD4.isSimplyLaced_componentType k) (a5FourthD4ComponentGlueEquiv k x) =
      (a5FourthD4ComponentIsometry k).discriminantQuadraticIsometry
        ((a5FourthD4.componentType k).isEven_rootLattice (a5FourthD4.isSimplyLaced_componentType k))
        ((a5FourthD4.componentType k).glueAlphabetIsometry (a5FourthD4.valid_componentType k)
          (a5FourthD4.isSimplyLaced_componentType k) x) :=
  glueAlphabetIsometry_glueAlphabetIsometryOfIsometry (a5FourthD4.valid_componentType k)
    (a5FourthD4.valid_componentType k) (a5FourthD4ComponentIsometry k) x

private theorem val_glueLabelEquiv_symm_a5FourthD4ComponentGlueEquiv
    (k : Fin a5FourthD4.components.length)
    (j : Fin (a5FourthD4.componentType k).glueLabelCount) :
    (((a5FourthD4.componentType k).glueLabelEquiv
        (a5FourthD4.isSimplyLaced_componentType k)).symm
      (a5FourthD4ComponentGlueEquiv k
        ((a5FourthD4.componentType k).glueLabelEquiv
          (a5FourthD4.isSimplyLaced_componentType k) j))).val =
      a5FourthD4DigitPerm k j.val := by
  have hcoe (y) : a5FourthD4ComponentGlueEquiv k y =
      glueAlphabetIsometryOfIsometry (a5FourthD4.valid_componentType k)
        (a5FourthD4.valid_componentType k) (a5FourthD4ComponentIsometry k) y := rfl
  rw [hcoe]
  match k with
  | ⟨0, _⟩ | ⟨1, _⟩ | ⟨2, _⟩ | ⟨3, _⟩ =>
    simp only [a5FourthD4ComponentIsometry, a5FourthD4DigitPerm,
      glueAlphabetIsometryOfIsometry_refl]
    exact congrArg Fin.val (Equiv.symm_apply_apply _ j)
  | ⟨4, h⟩ =>
    let e := (D 4).glueLabelEquiv (a5FourthD4.isSimplyLaced_componentType ⟨4, h⟩)
    have hm : j.val < 4 := j.isLt
    have h4 : (e.symm (glueAlphabetIsometryOfIsometry (a5FourthD4.valid_componentType ⟨4, h⟩)
        (a5FourthD4.valid_componentType ⟨4, h⟩) (a5FourthD4ComponentIsometry ⟨4, h⟩)
        (e ⟨j.val, hm⟩))).val = (typeD4TrialityLabelPerm ⟨j.val, hm⟩).val :=
      congrArg Fin.val ((congrArg e.symm
        (glueAlphabetIsometryOfIsometry_typeD4Triality_glueLabelEquiv _ _ _ ⟨j.val, hm⟩)).trans
        (e.symm_apply_apply _))
    exact h4.trans (by simp [a5FourthD4DigitPerm, hm])
  | ⟨_ + 5, h⟩ => exact False.elim (Nat.not_lt_of_ge (Nat.le_add_left 5 _) h)

private theorem a5FourthD4ComponentGlueEquiv_mem_glueSubgroup_iff (w : a5FourthD4.glueModule) :
    (fun k ↦ a5FourthD4ComponentGlueEquiv k
      (piGlueAlphabetCongr a5FourthD4.componentType a5FourthD4.isSimplyLaced_componentType
        (a5FourthD4BlockRot⁻¹ : Equiv.Perm (Fin 5)) componentType_a5FourthD4BlockRot_inv w k)) ∈
      a5FourthD4.glueSubgroup ↔ w ∈ a5FourthD4.glueSubgroup := by
  refine a5FourthD4.coupled_mem_glueSubgroup_iff_of_glueWords
    (g := (a5FourthD4BlockRot⁻¹ : Equiv.Perm (Fin 5))) componentType_a5FourthD4BlockRot_inv
    a5FourthD4ComponentGlueEquiv a5FourthD4DigitPerm
    val_glueLabelEquiv_symm_a5FourthD4ComponentGlueEquiv ?_ w
  -- Specialize `a5FourthD4.components.length` to `5` so `decide` reduces `List.ofFn`.
  change ∀ l ∈ a5FourthD4.glueWords,
    (List.ofFn fun k : Fin 5 ↦
      a5FourthD4DigitPerm k (l.getD (a5FourthD4BlockRot⁻¹ k) 0)) ∈ a5FourthD4.glueWords
  rw [a5FourthD4BlockRot_eq_swap_mul_swap]
  decide

/-- **The coupled triality rotation of `niemeierA5FourthD4`**: the self-isometry moving the three
marked `A₅` components by `1 ↦ 2 ↦ 3 ↦ 1`, fixing the leading `A₅` component `0`, and applying
`TauCeti.DynkinType.typeD4Triality` on the `D₄` component `4`. -/
noncomputable def a5FourthD4TrialityRotation :
    Isometry niemeierA5FourthD4 niemeierA5FourthD4 :=
  a5FourthD4.coupledLatticeIsometry (g := (a5FourthD4BlockRot⁻¹ : Equiv.Perm (Fin 5)))
    componentType_a5FourthD4BlockRot_inv a5FourthD4ComponentIsometry
    (fun k x ↦ a5FourthD4ComponentGlueEquiv k x)
    a5FourthD4ComponentIsometry_glueAlphabetIsometry
    a5FourthD4ComponentGlueEquiv_mem_glueSubgroup_iff

private theorem a5FourthD4TrialityRotation_apply
    (x : ∀ i, Fin (a5FourthD4.componentType i).rank → ℚ) (k : Fin 5) :
    a5FourthD4TrialityRotation x k =
      a5FourthD4ComponentIsometry k fun j ↦
        x ((a5FourthD4BlockRot⁻¹ : Equiv.Perm (Fin 5)) k)
          (Fin.cast (congrArg rank (componentType_a5FourthD4BlockRot_inv k)).symm j) := by
  refine (a5FourthD4.coupledLatticeIsometry_apply _ _ _ _ _ x k).trans
    (congrArg (a5FourthD4ComponentIsometry k) (funext fun j ↦ ?_))
  exact rootLatticeIsometryOfEq_apply _ _ _ _ _ j

private theorem a5FourthD4TrialityRotation_apply_of_inv_eq
    (x : ∀ i, Fin (a5FourthD4.componentType i).rank → ℚ) {k b : Fin 5}
    (hkb : a5FourthD4BlockRot⁻¹ k = b)
    (hb : (a5FourthD4.componentType k).rank = (a5FourthD4.componentType b).rank := by rfl) :
    a5FourthD4TrialityRotation x k =
      a5FourthD4ComponentIsometry k fun j ↦ x b (Fin.cast hb j) := by
  rw [a5FourthD4TrialityRotation_apply]
  subst hkb
  -- After substituting `b = a5FourthD4BlockRot⁻¹ k`, the two rank casts agree by proof irrelevance.
  rfl

private theorem a5FourthD4TrialityRotation_apply_of_refl
    (x : ∀ i, Fin (a5FourthD4.componentType i).rank → ℚ) {k b : Fin 5}
    (hk : a5FourthD4ComponentIsometry k = Isometry.refl _)
    (hkb : a5FourthD4BlockRot⁻¹ k = b)
    (hb : (a5FourthD4.componentType k).rank = (a5FourthD4.componentType b).rank := by rfl) :
    a5FourthD4TrialityRotation x k = fun j ↦ x b (Fin.cast hb j) := by
  rw [a5FourthD4TrialityRotation_apply_of_inv_eq x hkb hb, hk, Isometry.refl_apply]

@[simp]
theorem a5FourthD4TrialityRotation_apply_zero
    (x : ∀ i, Fin (a5FourthD4.componentType i).rank → ℚ) :
    a5FourthD4TrialityRotation x (0 : Fin 5) = x (0 : Fin 5) :=
  a5FourthD4TrialityRotation_apply_of_refl x rfl a5FourthD4BlockRot_inv_zero

@[simp]
theorem a5FourthD4TrialityRotation_apply_one
    (x : ∀ i, Fin (a5FourthD4.componentType i).rank → ℚ) :
    a5FourthD4TrialityRotation x (1 : Fin 5) = x (3 : Fin 5) :=
  a5FourthD4TrialityRotation_apply_of_refl x rfl a5FourthD4BlockRot_inv_one

@[simp]
theorem a5FourthD4TrialityRotation_apply_two
    (x : ∀ i, Fin (a5FourthD4.componentType i).rank → ℚ) :
    a5FourthD4TrialityRotation x (2 : Fin 5) = x (1 : Fin 5) :=
  a5FourthD4TrialityRotation_apply_of_refl x rfl a5FourthD4BlockRot_inv_two

@[simp]
theorem a5FourthD4TrialityRotation_apply_three
    (x : ∀ i, Fin (a5FourthD4.componentType i).rank → ℚ) :
    a5FourthD4TrialityRotation x (3 : Fin 5) = x (2 : Fin 5) :=
  a5FourthD4TrialityRotation_apply_of_refl x rfl a5FourthD4BlockRot_inv_three

@[simp]
theorem a5FourthD4TrialityRotation_apply_four
    (x : ∀ i, Fin (a5FourthD4.componentType i).rank → ℚ) :
    a5FourthD4TrialityRotation x (4 : Fin 5) =
      typeD4Triality (isSimplyLaced_D 4) (x (4 : Fin 5)) :=
  a5FourthD4TrialityRotation_apply_of_inv_eq x a5FourthD4BlockRot_inv_four

/-- **The coupled triality rotation has order three.** -/
@[simp]
theorem a5FourthD4TrialityRotation_pow_three : a5FourthD4TrialityRotation ^ 3 = 1 := by
  let τ := typeD4Triality (isSimplyLaced_D 4)
  have h4 : ∀ y : Fin (D 4).rank → ℚ, τ (τ (τ y)) = y := fun y ↦ by
    rw [← Isometry.mul_apply, ← Isometry.mul_apply, ← pow_two, ← pow_succ,
      typeD4Triality_pow_three, Isometry.one_apply]
  apply Isometry.ext
  intro x
  rw [pow_succ, pow_two, Isometry.mul_apply, Isometry.mul_apply, Isometry.one_apply]
  funext k
  generalize (k : Fin 5) = j
  fin_cases j
  · exact (a5FourthD4TrialityRotation_apply_zero _).trans <|
      (a5FourthD4TrialityRotation_apply_zero _).trans (a5FourthD4TrialityRotation_apply_zero _)
  · exact (a5FourthD4TrialityRotation_apply_one _).trans <|
      (a5FourthD4TrialityRotation_apply_three _).trans (a5FourthD4TrialityRotation_apply_two _)
  · exact (a5FourthD4TrialityRotation_apply_two _).trans <|
      (a5FourthD4TrialityRotation_apply_one _).trans (a5FourthD4TrialityRotation_apply_three _)
  · exact (a5FourthD4TrialityRotation_apply_three _).trans <|
      (a5FourthD4TrialityRotation_apply_two _).trans (a5FourthD4TrialityRotation_apply_one _)
  · exact (a5FourthD4TrialityRotation_apply_four _).trans <|
      (congrArg τ (a5FourthD4TrialityRotation_apply_four _)).trans <|
        (congrArg (fun v ↦ τ (τ v)) (a5FourthD4TrialityRotation_apply_four _)).trans
          (h4 (x (4 : Fin 5)))

/-- `a5FourthD4TrialityRotation` is nontrivial. -/
theorem a5FourthD4TrialityRotation_ne_one : a5FourthD4TrialityRotation ≠ 1 := by
  intro h
  let x : ∀ i, Fin (a5FourthD4.componentType i).rank → ℚ :=
    fun i _ ↦ if i.val = 1 then 1 else 0
  have hx := congrFun (congrFun (DFunLike.congr_fun h x) (2 : Fin 5)) ⟨0, by decide⟩
  have hlhs : a5FourthD4TrialityRotation x (2 : Fin 5) ⟨0, by decide⟩ = 1 := by
    rw [congrFun (a5FourthD4TrialityRotation_apply_two x) ⟨0, by decide⟩]
    rfl
  have hrhs : (1 : Isometry niemeierA5FourthD4 niemeierA5FourthD4) x (2 : Fin 5) ⟨0, by decide⟩ =
      0 := by
    rw [Isometry.one_apply]
    rfl
  exact one_ne_zero (hlhs.symm.trans (hx.trans hrhs))

/-- `a5FourthD4TrialityRotation` has exact order `3`. -/
@[simp]
theorem orderOf_a5FourthD4TrialityRotation : orderOf a5FourthD4TrialityRotation = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact orderOf_eq_prime a5FourthD4TrialityRotation_pow_three a5FourthD4TrialityRotation_ne_one

/-! ### Faithful action of all pattern symmetry groups across all 23 rows -/

/-- **The symmetries of the cyclic pattern `[2(024)0]` of `A₅⁴ D₄`** are `1`,
`a5FourthD4BlockRot`, and `a5FourthD4BlockRot ^ 2`. -/
theorem mem_symmetries_cyclic_a5FourthD4_iff (g : Equiv.Perm (Fin 5)) :
    g ∈ (GluePattern.cyclic [2] [0, 2, 4] [0]).symmetries ↔
      g = 1 ∨ g = a5FourthD4BlockRot ∨ g = a5FourthD4BlockRot ^ 2 := by
  rw [GluePattern.symmetries_cyclic]
  -- `[2]`, `[0, 2, 4]`, `[0]` have lengths `1, 3, 1`, matching `a5FourthD4BlockRot`.
  change g ∈ Subgroup.zpowers a5FourthD4BlockRot ↔ _
  constructor
  · intro hg
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    rw [← zpow_mod_orderOf, orderOf_a5FourthD4BlockRot]
    have hk0 : 0 ≤ k % 3 := Int.emod_nonneg k (by decide)
    have hk3 : k % 3 < 3 := Int.emod_lt_of_pos k (by decide)
    interval_cases k % 3
    · exact Or.inl (zpow_zero _)
    · exact Or.inr (Or.inl (zpow_one _))
    · exact Or.inr (Or.inr (zpow_ofNat _ 2))
  · rintro (rfl | rfl | rfl)
    · exact one_mem _
    · exact Subgroup.mem_zpowers _
    · exact pow_mem (Subgroup.mem_zpowers _) 2

/-- **The indicated symmetry group of `[2(024)0]` acts on `niemeierA5FourthD4`** by powers of
`a5FourthD4TrialityRotation`. -/
noncomputable def a5FourthD4CyclicSymmetryHom :
    (GluePattern.cyclic [2] [0, 2, 4] [0]).symmetries →*
      Isometry niemeierA5FourthD4 niemeierA5FourthD4 where
  toFun g := a5FourthD4TrialityRotation ^ ((g.val ⟨1, by decide⟩).val - 1)
  map_one' := pow_zero _
  map_mul' a b := by
    have ha := (mem_symmetries_cyclic_a5FourthD4_iff a.val).mp a.property
    have hb := (mem_symmetries_cyclic_a5FourthD4_iff b.val).mp b.property
    rcases ha with ha | ha | ha <;> rcases hb with hb | hb | hb <;>
      simp only [Subgroup.coe_mul, ha, hb, a5FourthD4BlockRot_eq_swap_mul_swap, ← pow_add] <;>
      (conv_lhs => rw [← pow_mod_orderOf]) <;>
      (conv_rhs => rw [← pow_mod_orderOf]) <;>
      rw [orderOf_a5FourthD4TrialityRotation] <;>
      exact congrArg (a5FourthD4TrialityRotation ^ ·) (by decide)

/-- The generator `a5FourthD4BlockRot` of `[2(024)0].symmetries` acts as
`a5FourthD4TrialityRotation`. -/
@[simp]
theorem a5FourthD4CyclicSymmetryHom_blockRot :
    a5FourthD4CyclicSymmetryHom ⟨a5FourthD4BlockRot, a5FourthD4BlockRot_mem_symmetries⟩ =
      a5FourthD4TrialityRotation := by
  have hexp : (a5FourthD4BlockRot (1 : Fin 5)).val - 1 = 1 := by
    rw [a5FourthD4BlockRot_eq_swap_mul_swap]; decide
  exact (congrArg (a5FourthD4TrialityRotation ^ ·) hexp).trans (pow_one _)

/-- **The cyclic pattern `[2(024)0]` acts faithfully on `niemeierA5FourthD4`.** -/
theorem a5FourthD4CyclicSymmetryHom_injective :
    Function.Injective a5FourthD4CyclicSymmetryHom := by
  rw [injective_iff_map_eq_one]
  intro g hg
  let gen : (GluePattern.cyclic [2] [0, 2, 4] [0]).symmetries :=
    ⟨a5FourthD4BlockRot, a5FourthD4BlockRot_mem_symmetries⟩
  rcases (mem_symmetries_cyclic_a5FourthD4_iff g.val).mp g.property with h | h | h
  · exact Subtype.ext h
  · have hg_eq : g = gen := Subtype.ext h
    rw [hg_eq, a5FourthD4CyclicSymmetryHom_blockRot] at hg
    exact absurd hg a5FourthD4TrialityRotation_ne_one
  · have hg_eq : g = gen ^ 2 := Subtype.ext h
    rw [hg_eq, map_pow, a5FourthD4CyclicSymmetryHom_blockRot] at hg
    have hdvd := orderOf_dvd_of_pow_eq_one hg
    rw [orderOf_a5FourthD4TrialityRotation] at hdvd
    exact absurd hdvd (by decide)

/-- **Every table pattern of every rootful Niemeier row acts on the lattice of its row**: by pure
component permutation (`patternIsometryHom`) on the 22 rows other than `A₅⁴ D₄`, and by the
coupled triality action (`a5FourthD4CyclicSymmetryHom`) on `A₅⁴ D₄`. -/
noncomputable def coupledPatternIsometryHom {r : RootfulNiemeierType} {p : GluePattern}
    (hp : p ∈ r.gluePatterns) :
    p.symmetries →* Isometry r.lattice r.lattice :=
  if hr : r = a5FourthD4 then
    match p, hp with
    | .literal _, _ => 1
    | .evenPermutations _, hp => by simp [hr, gluePatterns] at hp
    | .cyclic pre block post, hp => by
      have hp' : pre = [2] ∧ block = [0, 2, 4] ∧ post = [0] := by
        simpa [hr, gluePatterns] using hp
      rcases hp' with ⟨rfl, rfl, rfl⟩
      subst hr
      exact a5FourthD4CyclicSymmetryHom
  else
    patternIsometryHom hr hp

/-- On every row other than `A₅⁴ D₄`, `coupledPatternIsometryHom` agrees with
`patternIsometryHom`. -/
@[simp]
theorem coupledPatternIsometryHom_eq_patternIsometryHom {r : RootfulNiemeierType}
    (hr : r ≠ a5FourthD4) {p : GluePattern} (hp : p ∈ r.gluePatterns) :
    coupledPatternIsometryHom hp = patternIsometryHom hr hp := by
  simp [coupledPatternIsometryHom, hr]

/-- On the cyclic pattern `[2(024)0]` of `A₅⁴ D₄`, `coupledPatternIsometryHom` is
`a5FourthD4CyclicSymmetryHom`. -/
@[simp]
theorem coupledPatternIsometryHom_a5FourthD4_cyclic
    (hp : GluePattern.cyclic [2] [0, 2, 4] [0] ∈ a5FourthD4.gluePatterns) :
    coupledPatternIsometryHom hp = a5FourthD4CyclicSymmetryHom := by
  simp [coupledPatternIsometryHom]

/-- On any literal pattern of any row, `coupledPatternIsometryHom` is trivial. -/
@[simp]
theorem coupledPatternIsometryHom_literal {r : RootfulNiemeierType} (word : List ℕ)
    (hp : GluePattern.literal word ∈ r.gluePatterns) :
    coupledPatternIsometryHom hp = 1 := by
  ext g
  rw [Subsingleton.elim g 1, map_one, MonoidHom.one_apply]

/-- **Every pattern symmetry group across all 23 rootful Niemeier rows embeds faithfully into the
isometry group of its row's lattice.** -/
theorem coupledPatternIsometryHom_injective {r : RootfulNiemeierType} {p : GluePattern}
    (hp : p ∈ r.gluePatterns) :
    Function.Injective (coupledPatternIsometryHom hp) := by
  by_cases hr : r = a5FourthD4
  · subst hr
    rcases p with word | ⟨pre, block, post⟩ | @⟨n, word⟩
    · exact fun a b _ ↦ Subsingleton.elim a b
    · have hp' : pre = [2] ∧ block = [0, 2, 4] ∧ post = [0] := by
        simpa [gluePatterns] using hp
      rcases hp' with ⟨rfl, rfl, rfl⟩
      exact a5FourthD4CyclicSymmetryHom_injective
    · simp [gluePatterns] at hp
  · rw [coupledPatternIsometryHom_eq_patternIsometryHom hr]
    exact patternIsometryHom_injective hr hp

end RootfulNiemeierType

end TauCeti
