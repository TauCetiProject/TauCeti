/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.SpecificGroups.Dihedral.Basic
public import TauCeti.LinearAlgebra.Matrix.Cartan.Coxeter.Reflection
public import TauCeti.LinearAlgebra.Matrix.Cartan.Realization.WeylGroup
import TauCeti.GroupTheory.Coxeter.Geometric.Basic
import TauCeti.LinearAlgebra.Finsupp.LinearCombination

/-!
# The Coxeter presentation of the Weyl group of a Cartan realization

Let `R` be a `TauCeti.CartanRealization (B.map Int.cast) H` of a generalized Cartan matrix
`B : Matrix I I ℤ` (`Matrix.IsGeneralizedCartan`) over a field `K`.

Over an arbitrary field `K`, the simple reflections `R.simpleReflection` satisfy the braid relations
of `B.cartanCoxeterMatrix` (`isLiftable_simpleReflection`). When `K` has characteristic zero, the
simple roots and coroots remain linearly independent over `ℤ`, and combining
`CoxeterSystem.cartanRepresentation_injective` with the intertwining map on `R.rootLattice` yields:

* **Kac's Proposition 3.13** (`weylGroupMulEquiv`, `weylCoxeterSystem`,
  `orderOf_simpleReflection_mul`, and `rootLatticeAct_injective`): `R.weylGroup` is canonically
  isomorphic to `B.cartanCoxeterMatrix.Group`, the pairwise product `sᵢ sⱼ` has exact order
  `B.cartanCoxeterMatrix i j` (`0` when infinite), distinct indices give distinct nontrivial simple
  reflections, and the action on `R.rootLattice` is faithful.
* **Kac's Lemma 3.11** (`not_isRightDescent_weylCoxeterSystem_iff`,
  `isRightDescent_weylCoxeterSystem_iff`, and `isRightDescent_weylCoxeterSystem_iff_rootLE`):
  `ℓ(w sᵢ) > ℓ(w)` iff `w(αᵢ) ∈ R.posRootCone`, and `ℓ(w sᵢ) < ℓ(w)` iff `-w(αᵢ) ∈ R.posRootCone`
  (`R.RootLE (w(αᵢ)) 0`).

Finally we record the empty-index, rank-one (`A₁`, order `2`), and general rank-two dihedral
specializations (`DihedralGroup (B.cartanCoxeterMatrix 0 1)`), including finite type `B₂`
(`DihedralGroup 4` of order `8`) and affine type `A₁⁽¹⁾` (`DihedralGroup 0`, infinite, fixing the
null root `δ = α₀ + α₁` and translating `α₁` by `-2n δ` under `(s₀ s₁)^n`).

## References

* V. G. Kac, *Infinite-dimensional Lie algebras*, third edition, §§3.7–3.13.
-/

public section

open Function Module Set
open scoped Matrix

namespace TauCeti.CartanRealization

/-! ### Coxeter presentation, Kac's Lemma 3.11, and Kac's Proposition 3.13 -/

section CoxeterPresentation

variable {I K H : Type*} [Field K] [CharZero K] [AddCommGroup H] [Module K H]
  {B : Matrix I I ℤ} (R : CartanRealization (B.map (Int.cast : ℤ → K)) H)

/-- Over a field of characteristic zero, the simple roots are linearly independent over `ℤ`. -/
theorem linearIndependent_int_root : LinearIndependent ℤ R.root :=
  R.root_linearIndependent.restrict_scalars' ℤ

/-- Over a field of characteristic zero, the simple coroots are linearly independent over `ℤ`. -/
theorem linearIndependent_int_coroot : LinearIndependent ℤ R.coroot :=
  R.coroot_linearIndependent.restrict_scalars' ℤ

private theorem linearCombination_int_root_injective :
    Injective (Finsupp.linearCombination ℤ R.root) :=
  linearIndependent_iff_injective_finsuppLinearCombination.mp R.linearIndependent_int_root

private theorem linearCombination_int_coroot_injective :
    Injective (Finsupp.linearCombination ℤ R.coroot) :=
  linearIndependent_iff_injective_finsuppLinearCombination.mp R.linearIndependent_int_coroot

private theorem linearCombination_int_root_mem_posRootCone_iff (z : I →₀ ℤ) :
    Finsupp.linearCombination ℤ R.root z ∈ R.posRootCone ↔ 0 ≤ z := by
  rw [R.posRootCone_def, ← Finsupp.range_linearCombination (R := ℕ), LinearMap.mem_range]
  refine ⟨fun ⟨c, hc⟩ ↦ ?_, fun hz ↦ ?_⟩
  · have hzz' : z = c.mapRange (Nat.cast : ℕ → ℤ) rfl :=
      R.linearCombination_int_root_injective
        (hc.symm.trans (Finsupp.linearCombination_mapRange_natCast R.root c).symm)
    subst hzz'
    exact fun i ↦ Nat.cast_nonneg (c i)
  · refine ⟨z.mapRange Int.toNat rfl, ?_⟩
    rw [← Finsupp.linearCombination_mapRange_natCast (R := ℤ) R.root _ (hf := rfl)]
    congr 1
    ext i
    exact Int.toNat_of_nonneg (hz i)

variable (hB : B.IsGeneralizedCartan)
include hB

omit [CharZero K] in
/-- The simple reflections of a realization of a generalized Cartan matrix satisfy the braid
relations of `B.cartanCoxeterMatrix`. -/
theorem isLiftable_simpleReflection :
    B.cartanCoxeterMatrix.IsLiftable (R.simpleReflection (hB.diag_map K)) := by
  have hpair : ∀ i j, Dual.eval K H (R.coroot i) (R.root j) = B i j := fun i j ↦ by simp
  have heq : R.simpleReflection (hB.diag_map K) =
      fun i ↦ Module.reflection ((hpair i i).trans (by simp [hB.diag i])) :=
    funext (R.simpleReflection_eq_reflection (hB.diag_map K))
  rw [heq]
  exact hB.isLiftable_reflection hpair

omit [CharZero K] in
/-- Subgroup-valued braid relations: the simple reflection generators `R.simpleReflectionMem` in
`R.weylGroup` satisfy all braid relations of `B.cartanCoxeterMatrix`. -/
theorem isLiftable_simpleReflectionMem :
    B.cartanCoxeterMatrix.IsLiftable (R.simpleReflectionMem (hB.diag_map K)) := fun i j ↦
  Subtype.ext <| by
    have h := R.isLiftable_simpleReflection hB i j
    simpa only [Subgroup.coe_pow, Subgroup.coe_mul, Subgroup.coe_one, coe_simpleReflectionMem]
      using h

private noncomputable def weylGroupHom :
    B.cartanCoxeterMatrix.Group →* R.weylGroup (hB.diag_map K) :=
  B.cartanCoxeterMatrix.toCoxeterSystem.lift
    ⟨R.simpleReflectionMem (hB.diag_map K), R.isLiftable_simpleReflectionMem hB⟩

omit [CharZero K] in
private theorem apply_linearCombination_root_of_coxeterSystem {W : Type*} [Group W]
    (cs : CoxeterSystem B.cartanCoxeterMatrix W) (ρ : W →* R.weylGroup (hB.diag_map K))
    (hρ : ∀ i, ρ (cs.simple i) = R.simpleReflectionMem (hB.diag_map K) i)
    (w : W) (z : I →₀ ℤ) :
    (ρ w).1 (Finsupp.linearCombination ℤ R.root z) =
      Finsupp.linearCombination ℤ R.root (cs.cartanRepresentation hB w z) := by
  induction w using cs.simple_induction generalizing z with
  | simple i =>
    induction z using Finsupp.induction_linear with
    | zero => simp
    | add u v ihu ihv => simp only [map_add, ihu, ihv]
    | single j c =>
      have hlhs :
          (ρ (cs.simple i)).1 (Finsupp.linearCombination ℤ R.root (Finsupp.single j c)) =
            c • (R.root j - B i j • R.root i) := by
        rw [hρ, coe_simpleReflectionMem, Finsupp.linearCombination_single, map_zsmul,
          R.simpleReflection_root_intCast]
      have hrhs :
          Finsupp.linearCombination ℤ R.root
              (cs.cartanRepresentation hB (cs.simple i) (Finsupp.single j c)) =
            c • (R.root j - B i j • R.root i) := by
        rw [← Finsupp.smul_single_one j c, map_smul,
          CoxeterSystem.cartanRepresentation_simple_single, map_smul, map_sub, map_smul,
          Finsupp.linearCombination_single, Finsupp.linearCombination_single, one_smul, one_smul]
      exact hlhs.trans hrhs.symm
  | one => simp
  | mul w₁ w₂ ih₁ ih₂ =>
    rw [map_mul, Subgroup.coe_mul, mul_apply_eq_comp, ih₂, ih₁, map_mul, mul_apply_eq_comp]

omit [CharZero K] in
private theorem weylGroupHom_intertwines (g : B.cartanCoxeterMatrix.Group) (z : I →₀ ℤ) :
    (R.weylGroupHom hB g).1 (Finsupp.linearCombination ℤ R.root z) =
      Finsupp.linearCombination ℤ R.root
        (B.cartanCoxeterMatrix.toCoxeterSystem.cartanRepresentation hB g z) :=
  R.apply_linearCombination_root_of_coxeterSystem hB B.cartanCoxeterMatrix.toCoxeterSystem
    (R.weylGroupHom hB) (B.cartanCoxeterMatrix.toCoxeterSystem.lift_apply_simple _) g z

private theorem weylGroupHom_bijective : Bijective (R.weylGroupHom hB) :=
  ⟨(injective_iff_map_eq_one _).mpr fun g hg ↦
      B.cartanCoxeterMatrix.toCoxeterSystem.cartanRepresentation_injective hB <|
        LinearEquiv.ext fun z ↦ R.linearCombination_int_root_injective <| by
          have h := R.weylGroupHom_intertwines hB g z
          rw [hg, Subgroup.coe_one, one_apply_eq_self] at h
          simpa using h.symm,
    MonoidHom.range_eq_top.mp <| eq_top_iff.mpr <| by
      rw [← R.closure_range_simpleReflectionMem (hB.diag_map K), Subgroup.closure_le]
      rintro _ ⟨i, rfl⟩
      exact ⟨B.cartanCoxeterMatrix.simple i,
        B.cartanCoxeterMatrix.toCoxeterSystem.lift_apply_simple _ i⟩⟩

/-- **Kac's Proposition 3.13 (Coxeter isomorphism).** Over a field of characteristic zero, the Weyl
group of any realization of a generalized Cartan matrix `B` is canonically isomorphic to
`B.cartanCoxeterMatrix.Group`. -/
noncomputable def weylGroupMulEquiv :
    B.cartanCoxeterMatrix.Group ≃* R.weylGroup (hB.diag_map K) :=
  MulEquiv.ofBijective (R.weylGroupHom hB) (R.weylGroupHom_bijective hB)

@[simp]
theorem weylGroupMulEquiv_simple (i : I) :
    R.weylGroupMulEquiv hB (B.cartanCoxeterMatrix.simple i) =
      R.simpleReflectionMem (hB.diag_map K) i := by
  rw [weylGroupMulEquiv, MulEquiv.ofBijective_apply]
  exact B.cartanCoxeterMatrix.toCoxeterSystem.lift_apply_simple _ i

/-- **The canonical Coxeter system on the Weyl group** of a realization of a generalized Cartan
matrix `B`. -/
noncomputable def weylCoxeterSystem :
    CoxeterSystem B.cartanCoxeterMatrix (R.weylGroup (hB.diag_map K)) :=
  B.cartanCoxeterMatrix.toCoxeterSystem.map (R.weylGroupMulEquiv hB)

@[simp]
theorem weylCoxeterSystem_simple (i : I) :
    (R.weylCoxeterSystem hB).simple i = R.simpleReflectionMem (hB.diag_map K) i :=
  R.weylGroupMulEquiv_simple hB i

/-- Intertwining of the Weyl action on `R.rootLattice` with `CoxeterSystem.cartanRepresentation`. -/
theorem apply_linearCombination_root (w : R.weylGroup (hB.diag_map K)) (z : I →₀ ℤ) :
    w.1 (Finsupp.linearCombination ℤ R.root z) =
      Finsupp.linearCombination ℤ R.root
        ((R.weylCoxeterSystem hB).cartanRepresentation hB w z) :=
  R.apply_linearCombination_root_of_coxeterSystem hB (R.weylCoxeterSystem hB)
    (MonoidHom.id _) (R.weylCoxeterSystem_simple hB) w z

/-- Intertwining of `R.dualAct` on coroots with `CoxeterSystem.dualCartanRepresentation`. -/
theorem dualAct_linearCombination_coroot (w : R.weylGroup (hB.diag_map K)) (z : I →₀ ℤ) :
    R.dualAct (hB.diag_map K) w (Finsupp.linearCombination ℤ R.coroot z) =
      Finsupp.linearCombination ℤ R.coroot
        ((R.weylCoxeterSystem hB).dualCartanRepresentation hB w z) := by
  induction w using (R.weylCoxeterSystem hB).simple_induction generalizing z with
  | simple i =>
    induction z using Finsupp.induction_linear with
    | zero => simp
    | add u v ihu ihv => simp only [map_add, ihu, ihv]
    | single j c =>
      have hlhs :
          R.dualAct (hB.diag_map K) ((R.weylCoxeterSystem hB).simple i)
              (Finsupp.linearCombination ℤ R.coroot (Finsupp.single j c)) =
            c • (R.coroot j - B j i • R.coroot i) := by
        rw [weylCoxeterSystem_simple, dualAct_simpleReflectionMem,
          Finsupp.linearCombination_single, map_zsmul, R.dualReflection_coroot_intCast]
      have hrhs :
          Finsupp.linearCombination ℤ R.coroot
              ((R.weylCoxeterSystem hB).dualCartanRepresentation hB
                ((R.weylCoxeterSystem hB).simple i) (Finsupp.single j c)) =
            c • (R.coroot j - B j i • R.coroot i) := by
        rw [← Finsupp.smul_single_one j c, map_smul,
          CoxeterSystem.dualCartanRepresentation_simple_single, map_smul, map_sub, map_smul,
          Finsupp.linearCombination_single, Finsupp.linearCombination_single, one_smul, one_smul]
      exact hlhs.trans hrhs.symm
  | one => simp
  | mul w₁ w₂ ih₁ ih₂ =>
    rw [map_mul, mul_apply_eq_comp, ih₂, ih₁, map_mul, mul_apply_eq_comp]

/-- The product of two simple reflections in `R.weylGroup` has exact order
`B.cartanCoxeterMatrix i j` (`0` when infinite). -/
theorem orderOf_simpleReflectionMem_mul (i j : I) :
    orderOf (R.simpleReflectionMem (hB.diag_map K) i *
      R.simpleReflectionMem (hB.diag_map K) j) = B.cartanCoxeterMatrix i j := by
  rw [← R.weylCoxeterSystem_simple hB i, ← R.weylCoxeterSystem_simple hB j]
  exact (R.weylCoxeterSystem hB).orderOf_simple_mul_simple i j

/-- The product of two simple reflections in `Dual K H ≃ₗ[K] Dual K H` has exact order
`B.cartanCoxeterMatrix i j`. -/
theorem orderOf_simpleReflection_mul (i j : I) :
    orderOf (R.simpleReflection (hB.diag_map K) i *
      R.simpleReflection (hB.diag_map K) j) = B.cartanCoxeterMatrix i j := by
  rw [← R.orderOf_simpleReflectionMem_mul hB i j]
  simpa only [Subgroup.coe_subtype, Subgroup.coe_mul, coe_simpleReflectionMem] using
    orderOf_injective (R.weylGroup (hB.diag_map K)).subtype Subtype.val_injective
      (R.simpleReflectionMem (hB.diag_map K) i * R.simpleReflectionMem (hB.diag_map K) j)

/-- The product of two dual reflections in `H ≃ₗ[K] H` has exact order
`B.cartanCoxeterMatrix i j`. -/
theorem orderOf_dualReflection_mul (i j : I) :
    orderOf (R.dualReflection (hB.diag_map K) i *
      R.dualReflection (hB.diag_map K) j) = B.cartanCoxeterMatrix i j := by
  rw [← R.orderOf_simpleReflectionMem_mul hB i j]
  simpa only [map_mul, dualAct_simpleReflectionMem] using
    orderOf_injective (R.dualAct (hB.diag_map K)) (R.dualAct_injective _)
      (R.simpleReflectionMem (hB.diag_map K) i * R.simpleReflectionMem (hB.diag_map K) j)

omit [CharZero K] in
/-- Ambient linear-equivalence braid relation: `(sᵢ * sⱼ) ^ (B.cartanCoxeterMatrix i j) = 1` in
`Dual K H ≃ₗ[K] Dual K H`. -/
theorem simpleReflection_mul_pow (i j : I) :
    (R.simpleReflection (hB.diag_map K) i *
      R.simpleReflection (hB.diag_map K) j) ^ B.cartanCoxeterMatrix i j = 1 :=
  R.isLiftable_simpleReflection hB i j

/-- Over a characteristic-zero field, every simple reflection in `R.weylGroup` is nontrivial. -/
theorem simpleReflectionMem_ne_one (i : I) :
    R.simpleReflectionMem (hB.diag_map K) i ≠ 1 := by
  intro h
  have := (R.weylCoxeterSystem hB).length_simple i
  rw [weylCoxeterSystem_simple, h, CoxeterSystem.length_one] at this
  omega

/-- Over a characteristic-zero field, every simple reflection on `Dual K H` is nontrivial. -/
theorem simpleReflection_ne_one (i : I) :
    R.simpleReflection (hB.diag_map K) i ≠ 1 :=
  fun h ↦ R.simpleReflectionMem_ne_one hB i <| Subtype.ext <| by simpa using h

/-- Over a characteristic-zero field, distinct nodes yield distinct simple reflections. -/
theorem simpleReflection_injective : Injective (R.simpleReflection (hB.diag_map K)) :=
  fun _ _ h ↦ (R.weylCoxeterSystem hB).simple_injective <| by
    rw [weylCoxeterSystem_simple, weylCoxeterSystem_simple]
    exact Subtype.ext (by simpa using h)

/-- **Faithfulness on simple roots:** an element of `R.weylGroup` fixing every simple root is
`1`. -/
theorem eq_one_of_forall_apply_root_eq {w : R.weylGroup (hB.diag_map K)}
    (hw : ∀ i, w.1 (R.root i) = R.root i) : w = 1 := by
  refine (injective_iff_map_eq_one _).mp
    ((R.weylCoxeterSystem hB).cartanRepresentation_injective hB) w (LinearEquiv.ext fun z ↦ ?_)
  apply R.linearCombination_int_root_injective
  rw [← R.apply_linearCombination_root hB w z, one_apply_eq_self]
  induction z using Finsupp.induction_linear with
  | zero => simp
  | add u v ihu ihv => simp only [map_add, ihu, ihv]
  | single i c => simp [hw i]

/-- Two elements of `R.weylGroup` that agree on every simple root are equal. -/
theorem ext_of_forall_apply_root_eq {w₁ w₂ : R.weylGroup (hB.diag_map K)}
    (hw : ∀ i, w₁.1 (R.root i) = w₂.1 (R.root i)) : w₁ = w₂ := by
  rw [← inv_mul_eq_one]
  refine R.eq_one_of_forall_apply_root_eq hB fun i ↦ ?_
  rw [Subgroup.coe_mul, Subgroup.coe_inv, mul_apply_eq_comp]
  exact w₁.1.symm_apply_eq.mpr (hw i).symm

/-- **Faithfulness on simple coroots:** an element of `R.weylGroup` fixing every simple coroot
under `R.dualAct` is `1`. -/
theorem eq_one_of_forall_dualAct_coroot_eq {w : R.weylGroup (hB.diag_map K)}
    (hw : ∀ i, R.dualAct (hB.diag_map K) w (R.coroot i) = R.coroot i) : w = 1 := by
  refine (injective_iff_map_eq_one _).mp
    ((R.weylCoxeterSystem hB).dualCartanRepresentation_injective hB) w (LinearEquiv.ext fun z ↦ ?_)
  apply R.linearCombination_int_coroot_injective
  rw [← R.dualAct_linearCombination_coroot hB w z, one_apply_eq_self]
  induction z using Finsupp.induction_linear with
  | zero => simp
  | add u v ihu ihv => simp only [map_add, ihu, ihv]
  | single i c => simp [hw i]

/-- **Kac's Proposition 3.13 (faithfulness on the root lattice).** The integral action of
`R.weylGroup` on `R.rootLattice` is injective. -/
theorem rootLatticeAct_injective : Injective (R.rootLatticeAct (hB.diag_map K)) :=
  (injective_iff_map_eq_one _).mpr fun w hw ↦ R.eq_one_of_forall_apply_root_eq hB fun i ↦ by
    have hi := congrArg (fun e : R.rootLattice ≃ₗ[ℤ] R.rootLattice ↦
      (e ⟨R.root i, R.root_mem_rootLattice i⟩ : Dual K H)) hw
    simpa using hi

/-- **Kac's Lemma 3.11 (positive form).** A simple reflection `sᵢ` lengthens `w` on the right
(`¬IsRightDescent w i`) iff `w(αᵢ)` lies in the positive root cone `R.posRootCone`. -/
theorem not_isRightDescent_weylCoxeterSystem_iff (w : R.weylGroup (hB.diag_map K)) (i : I) :
    ¬(R.weylCoxeterSystem hB).IsRightDescent w i ↔ w.1 (R.root i) ∈ R.posRootCone := by
  have hroot : w.1 (R.root i) =
      Finsupp.linearCombination ℤ R.root
        ((R.weylCoxeterSystem hB).cartanRepresentation hB w (Finsupp.single i 1)) := by
    simpa using R.apply_linearCombination_root hB w (Finsupp.single i 1)
  rw [← (R.weylCoxeterSystem hB).cartanRepresentation_single_pos_iff hB w i, hroot,
    R.linearCombination_int_root_mem_posRootCone_iff]
  have hne : (R.weylCoxeterSystem hB).cartanRepresentation hB w (Finsupp.single i 1) ≠ 0 :=
    (map_ne_zero_iff _ ((R.weylCoxeterSystem hB).cartanRepresentation hB w).injective).mpr
      (Finsupp.single_ne_zero.mpr one_ne_zero)
  exact ⟨fun h ↦ h.le, fun h ↦ lt_of_le_of_ne h hne.symm⟩

/-- **Kac's Lemma 3.11 (negative form).** A simple reflection `sᵢ` shortens `w` on the right
(`IsRightDescent w i`, i.e. `ℓ(w sᵢ) < ℓ(w)`) iff `-w(αᵢ) ∈ R.posRootCone`. -/
theorem isRightDescent_weylCoxeterSystem_iff (w : R.weylGroup (hB.diag_map K)) (i : I) :
    (R.weylCoxeterSystem hB).IsRightDescent w i ↔ -(w.1 (R.root i)) ∈ R.posRootCone := by
  have h := R.not_isRightDescent_weylCoxeterSystem_iff hB
    (w * (R.weylCoxeterSystem hB).simple i) i
  rw [← (R.weylCoxeterSystem hB).isRightDescent_iff_not_isRightDescent_mul] at h
  simpa [Subgroup.coe_mul, mul_apply_eq_comp] using h

/-- **Kac's Lemma 3.11 (weight-order form).** `IsRightDescent w i` holds iff `w(αᵢ) ≤ 0` in the
weight order `R.RootLE`. -/
theorem isRightDescent_weylCoxeterSystem_iff_rootLE (w : R.weylGroup (hB.diag_map K)) (i : I) :
    (R.weylCoxeterSystem hB).IsRightDescent w i ↔ R.RootLE (w.1 (R.root i)) 0 := by
  rw [R.isRightDescent_weylCoxeterSystem_iff hB, rootLE_iff, zero_sub]

end CoxeterPresentation

namespace CoweightLattice

variable {I H : Type*} [AddCommGroup H] [Module ℚ H] {B : Matrix I I ℤ}
  {R : CartanRealization (B.map (Int.cast : ℤ → ℚ)) H} (L : R.CoweightLattice)
  (hB : B.IsGeneralizedCartan)
include hB

/-- The integral action of `R.weylGroup` on the coweight lattice `L.lattice` is injective. -/
theorem coweightAct_injective : Injective (L.coweightAct (hB.diag_map ℚ)) :=
  (injective_iff_map_eq_one _).mpr fun w hw ↦ R.eq_one_of_forall_dualAct_coroot_eq hB fun i ↦ by
    have hi := congrArg (fun e : L.lattice ≃ₗ[ℤ] L.lattice ↦ (e (L.coroot i) : H)) hw
    simpa using hi

/-- The integral action of `R.weylGroup` on the weight lattice `L.weightLattice` is injective. -/
theorem weightAct_injective : Injective (L.weightAct (hB.diag_map ℚ)) :=
  (injective_iff_map_eq_one _).mpr fun w hw ↦ R.eq_one_of_forall_apply_root_eq hB fun i ↦ by
    have hi := congrArg (fun e : L.weightLattice ≃ₗ[ℤ] L.weightLattice ↦
      (e (L.root i) : Dual ℚ H)) hw
    simpa using hi

end CoweightLattice

/-! ### Low-rank and affine specializations -/

section Specializations

section EmptyAndRankOne

variable {I K H : Type*} [Field K] [AddCommGroup H] [Module K H]
  {B : Matrix I I ℤ} (R : CartanRealization (B.map (Int.cast : ℤ → K)) H)
  (hB : B.IsGeneralizedCartan)

@[simp]
theorem length_weylCoxeterSystem_of_isEmpty [CharZero K] [IsEmpty I]
    (w : R.weylGroup (hB.diag_map K)) :
    (R.weylCoxeterSystem hB).length w = 0 := by
  rw [Subsingleton.elim w 1, CoxeterSystem.length_one]

/-- **Rank one (type `A₁`):** when `I` has a single element, `R.weylGroup` has order `2`. -/
theorem card_weylGroup_of_unique [CharZero K] [Unique I] :
    Nat.card (R.weylGroup (hB.diag_map K)) = 2 := by
  classical
  set s := R.simpleReflectionMem (hB.diag_map K) default
  have hs_ne : s ≠ 1 := R.simpleReflectionMem_ne_one hB default
  have hmem : ∀ w : R.weylGroup (hB.diag_map K), w = 1 ∨ w = s := by
    intro w
    induction w using (R.weylCoxeterSystem hB).simple_induction with
    | simple i =>
      rw [Subsingleton.elim i default, R.weylCoxeterSystem_simple hB]
      exact Or.inr rfl
    | one => exact Or.inl rfl
    | mul w₁ w₂ ih₁ ih₂ =>
      rcases ih₁ with rfl | rfl <;> rcases ih₂ with rfl | rfl <;> simp [s]
  let e : Bool ≃ R.weylGroup (hB.diag_map K) :=
    { toFun b := cond b s 1
      invFun w := decide (w = s)
      left_inv b := by cases b <;> simp [hs_ne.symm]
      right_inv w := by rcases hmem w with rfl | rfl <;> simp [hs_ne.symm] }
  simpa using (Nat.card_congr e).symm

end EmptyAndRankOne

section RankTwo

variable {K H : Type*} [Field K] [AddCommGroup H] [Module K H]

/-- **Rank-two dihedral recognition:** the Weyl group of any realization of a `2 × 2` generalized
Cartan matrix `B` over a characteristic-zero field is canonically isomorphic to
`DihedralGroup (B.cartanCoxeterMatrix 0 1)`. -/
noncomputable def weylGroupFinTwoDihedralEquiv [CharZero K] {B : Matrix (Fin 2) (Fin 2) ℤ}
    (R : CartanRealization (B.map (Int.cast : ℤ → K)) H) (hB : B.IsGeneralizedCartan) :
    DihedralGroup (B.cartanCoxeterMatrix 0 1) ≃* R.weylGroup (hB.diag_map K) :=
  TauCeti.dihedralGroupMulEquiv
    (R.simpleReflectionMem_mul_self (hB.diag_map K) 0)
    (R.simpleReflectionMem_mul_self (hB.diag_map K) 1)
    (R.simpleReflectionMem_ne_one hB 0)
    (R.simpleReflectionMem_ne_one hB 1)
    (R.orderOf_simpleReflectionMem_mul hB 0 1)
    (by
      rw [← R.closure_range_simpleReflectionMem (hB.diag_map K)]
      congr 1
      ext x
      simp [Fin.exists_fin_two, eq_comm])

/-- Cardinality of the Weyl group of a rank-two generalized Cartan matrix (`0` when infinite). -/
theorem card_weylGroup_fin_two [CharZero K] {B : Matrix (Fin 2) (Fin 2) ℤ}
    (R : CartanRealization (B.map (Int.cast : ℤ → K)) H) (hB : B.IsGeneralizedCartan) :
    Nat.card (R.weylGroup (hB.diag_map K)) = 2 * B.cartanCoxeterMatrix 0 1 := by
  rw [← Nat.card_congr (R.weylGroupFinTwoDihedralEquiv hB).toEquiv, DihedralGroup.nat_card]

/-- **Type `B₂`:** the Weyl group of any realization of `CartanMatrix.B 2` is isomorphic to
`DihedralGroup 4`. -/
noncomputable def weylGroupB₂DihedralEquiv [CharZero K]
    (R : CartanRealization ((CartanMatrix.B 2).map (Int.cast : ℤ → K)) H) :
    DihedralGroup 4 ≃* R.weylGroup ((CartanMatrix.isGeneralizedCartan_B 2).diag_map K) :=
  CartanMatrix.cartanCoxeterMatrix_B_two ▸
    R.weylGroupFinTwoDihedralEquiv (CartanMatrix.isGeneralizedCartan_B 2)

/-- **Type `B₂`:** the Weyl group of any realization of `CartanMatrix.B 2` has order `8`. -/
theorem card_weylGroup_B_two [CharZero K]
    (R : CartanRealization ((CartanMatrix.B 2).map (Int.cast : ℤ → K)) H) :
    Nat.card (R.weylGroup ((CartanMatrix.isGeneralizedCartan_B 2).diag_map K)) = 8 := by
  rw [R.card_weylGroup_fin_two (CartanMatrix.isGeneralizedCartan_B 2),
    CartanMatrix.cartanCoxeterMatrix_B_two]

/-- **Affine `A₁⁽¹⁾`:** the Weyl group of any realization of `CartanMatrix.affineA₁` is isomorphic
to the infinite dihedral group `DihedralGroup 0`. -/
noncomputable def weylGroupAffineA₁DihedralEquiv [CharZero K]
    (R : CartanRealization (CartanMatrix.affineA₁.map (Int.cast : ℤ → K)) H) :
    DihedralGroup 0 ≃* R.weylGroup (CartanMatrix.isGeneralizedCartan_affineA₁.diag_map K) :=
  CartanMatrix.cartanCoxeterMatrix_affineA₁ ▸
    R.weylGroupFinTwoDihedralEquiv CartanMatrix.isGeneralizedCartan_affineA₁

/-- In affine type `A₁⁽¹⁾`, the product `s₀ s₁` has infinite order (`orderOf = 0`). -/
theorem orderOf_simpleReflection_mul_affineA₁ [CharZero K]
    (R : CartanRealization (CartanMatrix.affineA₁.map (Int.cast : ℤ → K)) H) :
    orderOf (R.simpleReflection (CartanMatrix.isGeneralizedCartan_affineA₁.diag_map K) 0 *
      R.simpleReflection (CartanMatrix.isGeneralizedCartan_affineA₁.diag_map K) 1) = 0 := by
  rw [R.orderOf_simpleReflection_mul CartanMatrix.isGeneralizedCartan_affineA₁,
    CartanMatrix.cartanCoxeterMatrix_affineA₁]

/-- In affine type `A₁⁽¹⁾`, the Weyl group is infinite. -/
theorem infinite_weylGroup_affineA₁ [CharZero K]
    (R : CartanRealization (CartanMatrix.affineA₁.map (Int.cast : ℤ → K)) H) :
    Infinite (R.weylGroup (CartanMatrix.isGeneralizedCartan_affineA₁.diag_map K)) :=
  Infinite.of_injective _ R.weylGroupAffineA₁DihedralEquiv.injective

/-- **Affine `A₁⁽¹⁾`:** both simple reflections fix the null root `δ = α₀ + α₁`. -/
theorem simpleReflection_nullRoot_affineA₁
    (R : CartanRealization (CartanMatrix.affineA₁.map (Int.cast : ℤ → K)) H) (i : Fin 2) :
    R.simpleReflection (CartanMatrix.isGeneralizedCartan_affineA₁.diag_map K) i
        (R.root 0 + R.root 1) =
      R.root 0 + R.root 1 := by
  rcases Fin.exists_fin_two.mp ⟨i, rfl⟩ with rfl | rfl
  · have h01 : CartanMatrix.affineA₁ 0 1 = -2 := rfl
    rw [map_add, R.simpleReflection_root_self, R.simpleReflection_root_intCast, h01]
    abel
  · have h10 : CartanMatrix.affineA₁ 1 0 = -2 := rfl
    rw [map_add, R.simpleReflection_root_intCast, R.simpleReflection_root_self, h10]
    abel

/-- **Affine `A₁⁽¹⁾` translation:** the rotation `s₀ s₁` translates `α₁` by `-2 • (α₀ + α₁)`, and
more generally `(s₀ s₁)^n (α₁) = α₁ - (2 * n) • (α₀ + α₁)` for every `n : ℤ`. -/
theorem simpleReflection_mul_zpow_root_one_affineA₁
    (R : CartanRealization (CartanMatrix.affineA₁.map (Int.cast : ℤ → K)) H) (n : ℤ) :
    ((R.simpleReflection (CartanMatrix.isGeneralizedCartan_affineA₁.diag_map K) 0 *
      R.simpleReflection (CartanMatrix.isGeneralizedCartan_affineA₁.diag_map K) 1) ^ n)
        (R.root 1) =
      R.root 1 - (2 * n) • (R.root 0 + R.root 1) := by
  have h01 : CartanMatrix.affineA₁ 0 1 = -2 := rfl
  have h10 : CartanMatrix.affineA₁ 1 0 = -2 := rfl
  have h11 : CartanMatrix.affineA₁ 1 1 = 2 := rfl
  have ht : (2 : K) = Dual.eval K H (R.coroot 0) (R.root 1) *
      Dual.eval K H (R.coroot 1) (R.root 0) - 2 := by
    simp only [Dual.eval_apply, R.root_coroot, Matrix.map_apply, h01, h10, Int.cast_neg,
      Int.cast_ofNat]
    norm_num
  have hu : (n - 2) / 2 = n / 2 - 1 := by omega
  have hv : (n - 3) / 2 = (n - 1) / 2 - 1 := by omega
  have huv : n / 2 + (n - 1) / 2 + 1 = n := by omega
  rw [R.simpleReflection_eq_reflection, R.simpleReflection_eq_reflection,
    Module.reflection_mul_reflection_zpow_apply _ _ n (R.root 1) (2 : K) ht]
  simp only [Dual.eval_apply, R.root_coroot, Matrix.map_apply, h01, h10, h11, Int.cast_neg,
    Int.cast_ofNat, Polynomial.Chebyshev.S_eval_two, hu, hv]
  rw [← Int.cast_smul_eq_zsmul K (2 * n), Int.cast_mul, Int.cast_ofNat]
  have hcast : ((n / 2 : ℤ) : K) + (((n - 1) / 2 : ℤ) : K) + 1 = (n : K) := by
    simpa [Int.cast_add, Int.cast_one] using congrArg (Int.cast : ℤ → K) huv
  rw [← hcast]
  module

end RankTwo

end Specializations

end TauCeti.CartanRealization

end
