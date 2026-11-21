/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.IntegralLattice.Rank24.TableRow.A5FourthD4

/-!
# The coupled triality symmetry of the table row `A₅⁴ D₄`

In the rootful rank-24 table, `TauCeti.RootfulNiemeierType.a5FourthD4` is the unique row whose
parenthesized pattern symmetry is not a pure coordinate glue symmetry: rotating the three marked
`A₅` positions `1, 2, 3` (`TauCeti.RootfulNiemeierType.a5FourthD4BlockRot`) while leaving the `D₄`
label in position `4` unchanged sends `[33001]` outside the glue subgroup
(`TauCeti.RootfulNiemeierType.a5FourthD4BlockRot_notMem_glueSymmetries`).

Coupling the block rotation with `D₄` triality (`TauCeti.DynkinType.typeD4Triality`) on the `D₄`
component preserves `a5FourthD4.glueSubgroup`
(`TauCeti.RootfulNiemeierType.a5FourthD4TrialityGlueIsometry_mem_glueSubgroup_iff`), and this module
lifts that glue-word symmetry via `coupledLatticeIsometry` to the order-three, determinant-one
self-isometry `TauCeti.RootfulNiemeierType.a5FourthD4TrialityRotation` of
`TauCeti.niemeierA5FourthD4`.  This yields a faithful action
`TauCeti.RootfulNiemeierType.a5FourthD4CyclicSymmetryHom` of the cyclic pattern's symmetry group on
`niemeierA5FourthD4`.

## Main declarations

* `TauCeti.RootfulNiemeierType.a5FourthD4TrialityRotation`: the order-three, determinant-one
  (`orderOf_a5FourthD4TrialityRotation`, `det_a5FourthD4TrialityRotation`) self-isometry of
  `niemeierA5FourthD4` rotating the three marked `A₅` components and applying `typeD4Triality` on
  the `D₄` component.
* `TauCeti.RootfulNiemeierType.mem_symmetries_cyclic_a5FourthD4_iff`,
  `TauCeti.RootfulNiemeierType.a5FourthD4CyclicSymmetryHom`,
  `TauCeti.RootfulNiemeierType.exists_a5FourthD4CyclicSymmetryHom_eq_pow`,
  `TauCeti.RootfulNiemeierType.det_a5FourthD4CyclicSymmetryHom`,
  `TauCeti.RootfulNiemeierType.a5FourthD4CyclicSymmetryHom_injective`: membership characterization
  and faithful determinant-one action of `(GluePattern.cyclic [2] [0, 2, 4] [0]).symmetries` on
  `niemeierA5FourthD4`.

## References

* J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, 3rd ed., Chapter 4
  §§3 and 7, and Chapter 16 §1, Table 16.1.
-/

public section

namespace TauCeti

namespace RootfulNiemeierType

open DynkinType IntegralLattice

/-! ### Lifting `[2(024)0]` to `niemeierA5FourthD4` via `D₄` triality -/

/-- **The coupled triality rotation of `niemeierA5FourthD4`**: the self-isometry moving the three
marked `A₅` components by `1 ↦ 2 ↦ 3 ↦ 1`, fixing the leading `A₅` component `0`, and applying
`TauCeti.DynkinType.typeD4Triality` on the `D₄` component `4`. -/
noncomputable def a5FourthD4TrialityRotation :
    Isometry niemeierA5FourthD4 niemeierA5FourthD4 :=
  a5FourthD4.coupledLatticeIsometry
    (g := (a5FourthD4BlockRot⁻¹ : Equiv.Perm (Fin a5FourthD4.components.length)))
    componentType_a5FourthD4BlockRot_inv componentTriality
    (fun k x ↦ componentTrialityLabel k x)
    glueAlphabetIsometry_componentTrialityLabel
    fun w ↦ by
      have h := a5FourthD4TrialityGlueIsometry_mem_glueSubgroup_iff w
      rw [a5FourthD4TrialityGlueIsometry, QuadraticMap.IsometryEquiv.trans_apply] at h
      rwa [← funext fun k ↦ QuadraticMap.IsometryEquiv.pi_apply componentTrialityLabel _ k]

private theorem a5FourthD4TrialityRotation_apply
    (x : ∀ i, Fin (a5FourthD4.componentType i).rank → ℚ) (k : Fin 5) :
    a5FourthD4TrialityRotation x k =
      componentTriality k fun j ↦
        x ((a5FourthD4BlockRot⁻¹ : Equiv.Perm (Fin a5FourthD4.components.length)) k)
          (Fin.cast (congrArg rank (componentType_a5FourthD4BlockRot_inv k)).symm j) := by
  refine (a5FourthD4.coupledLatticeIsometry_apply _ _ _ _ _ x k).trans
    (congrArg (componentTriality k) (funext fun j ↦ ?_))
  exact rootLatticeIsometryOfEq_apply _ _ _ _ _ j

private theorem a5FourthD4TrialityRotation_apply_of_inv_eq
    (x : ∀ i, Fin (a5FourthD4.componentType i).rank → ℚ) {k b : Fin 5}
    (hkb : a5FourthD4BlockRot⁻¹ k = b)
    (hb : (a5FourthD4.componentType k).rank = (a5FourthD4.componentType b).rank := by rfl) :
    a5FourthD4TrialityRotation x k =
      componentTriality k fun j ↦ x b (Fin.cast hb j) := by
  rw [a5FourthD4TrialityRotation_apply]
  subst hkb
  -- After substituting `b = a5FourthD4BlockRot⁻¹ k`, the two rank casts agree by proof irrelevance.
  rfl

private theorem a5FourthD4TrialityRotation_apply_of_refl
    (x : ∀ i, Fin (a5FourthD4.componentType i).rank → ℚ) {k b : Fin 5}
    (hk : componentTriality k = 1)
    (hkb : a5FourthD4BlockRot⁻¹ k = b)
    (hb : (a5FourthD4.componentType k).rank = (a5FourthD4.componentType b).rank := by rfl) :
    a5FourthD4TrialityRotation x k = fun j ↦ x b (Fin.cast hb j) := by
  rw [a5FourthD4TrialityRotation_apply_of_inv_eq x hkb hb, hk, Isometry.one_apply]

@[simp]
theorem a5FourthD4TrialityRotation_apply_zero
    (x : ∀ i, Fin (a5FourthD4.componentType i).rank → ℚ) :
    a5FourthD4TrialityRotation x (0 : Fin 5) = x (0 : Fin 5) :=
  a5FourthD4TrialityRotation_apply_of_refl x
    (componentTriality_of_ne fun h ↦ absurd (congrArg Fin.val h) (by decide))
    a5FourthD4BlockRot_inv_zero

@[simp]
theorem a5FourthD4TrialityRotation_apply_one
    (x : ∀ i, Fin (a5FourthD4.componentType i).rank → ℚ) :
    a5FourthD4TrialityRotation x (1 : Fin 5) = x (3 : Fin 5) :=
  a5FourthD4TrialityRotation_apply_of_refl x
    (componentTriality_of_ne fun h ↦ absurd (congrArg Fin.val h) (by decide))
    a5FourthD4BlockRot_inv_one

@[simp]
theorem a5FourthD4TrialityRotation_apply_two
    (x : ∀ i, Fin (a5FourthD4.componentType i).rank → ℚ) :
    a5FourthD4TrialityRotation x (2 : Fin 5) = x (1 : Fin 5) :=
  a5FourthD4TrialityRotation_apply_of_refl x
    (componentTriality_of_ne fun h ↦ absurd (congrArg Fin.val h) (by decide))
    a5FourthD4BlockRot_inv_two

@[simp]
theorem a5FourthD4TrialityRotation_apply_three
    (x : ∀ i, Fin (a5FourthD4.componentType i).rank → ℚ) :
    a5FourthD4TrialityRotation x (3 : Fin 5) = x (2 : Fin 5) :=
  a5FourthD4TrialityRotation_apply_of_refl x
    (componentTriality_of_ne fun h ↦ absurd (congrArg Fin.val h) (by decide))
    a5FourthD4BlockRot_inv_three

@[simp]
theorem a5FourthD4TrialityRotation_apply_four
    (x : ∀ i, Fin (a5FourthD4.componentType i).rank → ℚ) :
    a5FourthD4TrialityRotation x (4 : Fin 5) =
      typeD4Triality (isSimplyLaced_D 4) (x (4 : Fin 5)) := by
  rw [a5FourthD4TrialityRotation_apply_of_inv_eq x a5FourthD4BlockRot_inv_four]
  change componentTriality a5FourthD4D4Index (x (4 : Fin 5)) = _
  rw [componentTriality_d4Index]
  rfl

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

/-- **`a5FourthD4TrialityRotation` is a proper isometry (`det = 1`).** -/
@[simp]
theorem det_a5FourthD4TrialityRotation :
    Isometry.det niemeierA5FourthD4 a5FourthD4TrialityRotation = 1 :=
  Isometry.det_eq_one_of_pow_eq_one (by decide : Odd 3) a5FourthD4TrialityRotation_pow_three

/-! ### Faithful action of `[2(024)0].symmetries` on `niemeierA5FourthD4` -/

/-- **The symmetries of the cyclic pattern `[2(024)0]` of `A₅⁴ D₄`** are `1`,
`a5FourthD4BlockRot`, and `a5FourthD4BlockRot ^ 2`. -/
theorem mem_symmetries_cyclic_a5FourthD4_iff (g : Equiv.Perm (Fin 5)) :
    g ∈ (GluePattern.cyclic [2] [0, 2, 4] [0]).symmetries ↔
      g = 1 ∨ g = a5FourthD4BlockRot ∨ g = a5FourthD4BlockRot ^ 2 := by
  refine (SetLike.ext_iff.mp symmetries_cyclic_a5FourthD4 g).trans
    ((mem_zpowers_iff_mem_range_orderOf (x := a5FourthD4BlockRot) (y := g)).trans ?_)
  rw [orderOf_a5FourthD4BlockRot]
  simp only [Finset.range_add_one, Finset.range_zero, Finset.mem_image, Finset.mem_insert,
    Finset.notMem_empty, exists_eq_or_imp, pow_zero, pow_one]
  tauto

private theorem forall_mem_zpowers_a5FourthD4BlockRot
    (g : (GluePattern.cyclic [2] [0, 2, 4] [0]).symmetries) :
    g ∈ Subgroup.zpowers ⟨a5FourthD4BlockRot, a5FourthD4BlockRot_mem_symmetries⟩ := by
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp
    ((SetLike.ext_iff.mp symmetries_cyclic_a5FourthD4 g.val).mp g.property)
  exact ⟨k, Subtype.ext hk⟩

private theorem orderOf_a5FourthD4BlockRot_mk_eq_orderOf_a5FourthD4TrialityRotation_mk :
    orderOf (⟨a5FourthD4BlockRot, a5FourthD4BlockRot_mem_symmetries⟩ :
        (GluePattern.cyclic [2] [0, 2, 4] [0]).symmetries) =
      orderOf (⟨a5FourthD4TrialityRotation, Subgroup.mem_zpowers _⟩ :
        Subgroup.zpowers a5FourthD4TrialityRotation) :=
  (Subgroup.orderOf_mk a5FourthD4BlockRot a5FourthD4BlockRot_mem_symmetries).trans
    (orderOf_a5FourthD4BlockRot.trans
      (orderOf_a5FourthD4TrialityRotation.symm.trans (Subgroup.orderOf_mk _ _).symm))

/-- **The indicated symmetry group of `[2(024)0]` acts on `niemeierA5FourthD4`** by powers of
`a5FourthD4TrialityRotation`. -/
noncomputable def a5FourthD4CyclicSymmetryHom :
    (GluePattern.cyclic [2] [0, 2, 4] [0]).symmetries →*
      Isometry niemeierA5FourthD4 niemeierA5FourthD4 :=
  (Subgroup.zpowers a5FourthD4TrialityRotation).subtype.comp
    (mulEquivOfOrderOfEq forall_mem_zpowers_a5FourthD4BlockRot
      (Subgroup.forall_zpowers.mpr fun m ↦ ⟨m, rfl⟩)
      orderOf_a5FourthD4BlockRot_mk_eq_orderOf_a5FourthD4TrialityRotation_mk).toMonoidHom

/-- The generator `a5FourthD4BlockRot` of `[2(024)0].symmetries` acts as
`a5FourthD4TrialityRotation`. -/
@[simp]
theorem a5FourthD4CyclicSymmetryHom_blockRot :
    a5FourthD4CyclicSymmetryHom ⟨a5FourthD4BlockRot, a5FourthD4BlockRot_mem_symmetries⟩ =
      a5FourthD4TrialityRotation := by
  simp [a5FourthD4CyclicSymmetryHom, mulEquivOfOrderOfEq_apply_gen]

/-- Every symmetry of `[2(024)0]` acts on the component positions as `a5FourthD4BlockRot ^ k`
(`k < 3`) and on `niemeierA5FourthD4` as the matching power `a5FourthD4TrialityRotation ^ k`. -/
theorem exists_a5FourthD4CyclicSymmetryHom_eq_pow
    (g : (GluePattern.cyclic [2] [0, 2, 4] [0]).symmetries) :
    ∃ k < 3,
      g.val = a5FourthD4BlockRot ^ k ∧
        a5FourthD4CyclicSymmetryHom g = a5FourthD4TrialityRotation ^ k := by
  obtain ⟨k, hk, hgk⟩ : ∃ k < 3, g.val = a5FourthD4BlockRot ^ k := by
    rcases (mem_symmetries_cyclic_a5FourthD4_iff g.val).mp g.property with h | h | h
    · exact ⟨0, by decide, h.trans (pow_zero _).symm⟩
    · exact ⟨1, by decide, h.trans (pow_one _).symm⟩
    · exact ⟨2, by decide, h⟩
  refine ⟨k, hk, hgk, ?_⟩
  rw [show g = ⟨a5FourthD4BlockRot, a5FourthD4BlockRot_mem_symmetries⟩ ^ k from Subtype.ext hgk,
    map_pow, a5FourthD4CyclicSymmetryHom_blockRot]

/-- Every symmetry of the cyclic pattern `[2(024)0]` acts on `niemeierA5FourthD4` with
determinant `1`. -/
@[simp]
theorem det_a5FourthD4CyclicSymmetryHom
    (g : (GluePattern.cyclic [2] [0, 2, 4] [0]).symmetries) :
    Isometry.det niemeierA5FourthD4 (a5FourthD4CyclicSymmetryHom g) = 1 := by
  obtain ⟨k, -, -, hg⟩ := exists_a5FourthD4CyclicSymmetryHom_eq_pow g
  rw [hg, map_pow, det_a5FourthD4TrialityRotation, one_pow]

/-- **The cyclic pattern `[2(024)0]` acts faithfully on `niemeierA5FourthD4`.** -/
theorem a5FourthD4CyclicSymmetryHom_injective :
    Function.Injective a5FourthD4CyclicSymmetryHom :=
  (Subgroup.subtype_injective _).comp (MulEquiv.injective _)

end RootfulNiemeierType

end TauCeti
