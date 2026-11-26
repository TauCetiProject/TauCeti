/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Algebra.Subalgebra.Basic
public import TauCeti.Algebra.Module.Equiv.Basic
public import TauCeti.Algebra.Module.FreeClassIndex
public import TauCeti.Algebra.Module.Lattice
public import TauCeti.RingTheory.IntegralOrder.Basic

/-!
# Class indices of orders

The class index of an order is the supremum of the least free indices of its full stable
lattices. The module invariant `Module.freeClassIndex` is defined independently in
`TauCeti.Algebra.Module.FreeClassIndex`. Thus the class-index definition does not assume the
finiteness theorem for class indices.

Every full stable lattice admits an embedding of the standard free module of positive finite
index. All indices are indices of additive groups.

## References

D. Masser and G. Wüstholz, *Factorization estimates for abelian varieties*, §2.
-/

public section

namespace Subalgebra

variable {D : Type*} [Ring D] (O : Subalgebra ℤ D) (e : ℕ)

variable [Algebra ℚ D]

/-- The class index is the supremum of least free indices of full stable lattices. -/
noncomputable def classIndex : ℕ∞ :=
  ⨆ M : Submodule O (Fin e → D), ⨆ (_ : (M.restrictScalars ℤ).IsFullLattice ℚ),
    Module.freeClassIndex O e M

/-- The class index is the supremum of the least free indices over all full stable lattices. -/
theorem classIndex_def : O.classIndex e =
    ⨆ M : Submodule O (Fin e → D), ⨆ (_ : (M.restrictScalars ℤ).IsFullLattice ℚ),
      Module.freeClassIndex O e M := by
  rfl

/-- The class index for right modules over an order, viewed as left modules over its opposite. -/
noncomputable def rightClassIndex : ℕ∞ :=
  O.op.classIndex e

/-- The right class index is the left class index of the opposite order. -/
theorem rightClassIndex_def : O.rightClassIndex e = O.op.classIndex e := by
  rfl

/-- The least free index of a full stable lattice is bounded by the class index. -/
theorem freeClassIndex_le_classIndex (M : Submodule O (Fin e → D))
    [(M.restrictScalars ℤ).IsFullLattice ℚ] :
    Module.freeClassIndex O e M ≤ O.classIndex e := by
  rw [classIndex_def]
  exact le_iSup_of_le M (le_iSup_of_le inferInstance le_rfl)

/-- A uniform bound for all least free indices bounds the class index, and conversely. -/
theorem classIndex_le_iff {n : ℕ∞} : O.classIndex e ≤ n ↔
    ∀ M : Submodule O (Fin e → D), (M.restrictScalars ℤ).IsFullLattice ℚ →
      Module.freeClassIndex O e M ≤ n := by
  simp only [classIndex_def, iSup_le_iff]

/-- A finite class-index bound gives precisely uniform embeddings of bounded additive index. -/
theorem classIndex_le_natCast_iff (n : ℕ) : O.classIndex e ≤ n ↔
    ∀ M : Submodule O (Fin e → D), (M.restrictScalars ℤ).IsFullLattice ℚ →
      ∃ f : (Fin e → O) →ₗ[O] M, Function.Injective f ∧
        (LinearMap.range f).toAddSubgroup.index ≠ 0 ∧
        (LinearMap.range f).toAddSubgroup.index ≤ n := by
  simp only [classIndex_le_iff, Module.freeClassIndex_le_natCast_iff]

/-- The class index in rank zero equals one. -/
@[simp]
theorem classIndex_zero : O.classIndex 0 = 1 := by
  apply le_antisymm
  · exact (classIndex_le_iff O 0).2 fun M _ => (Module.freeClassIndex_zero (R := O) (M := M)).le
  · let M : Submodule O (Fin 0 → D) := ⊥
    have hM : (M.restrictScalars ℤ).IsFullLattice ℚ := .of_subsingleton _
    rw [classIndex_def]
    exact (Module.one_le_freeClassIndex (R := O) (e := 0) (M := M)).trans
      (le_iSup_of_le M (le_iSup_of_le hM le_rfl))

section Transport

-- Use the inverse-pair instances locally when mapping submodules by the transport equivalence.
attribute [local instance] RingHomInvPair.of_ringEquiv

/-- Coordinate transport over the image order preserves and reflects full lattices after
restriction to the integers. -/
theorem isFullLattice_map_equivMapPiSemilinear_iff {E : Type*} [Ring E] [Algebra ℚ E]
    {ι : Type*} (f : D ≃ₐ[ℚ] E) (M : Submodule O (ι → D)) :
    Submodule.IsFullLattice ℚ
      ((M.map (O.equivMapPiSemilinear (f.restrictScalars ℤ) ι).toLinearMap).restrictScalars ℤ) ↔
      (M.restrictScalars ℤ).IsFullLattice ℚ := by
  let a := O.equivMapPiSemilinear (f.restrictScalars ℤ) ι
  let c := LinearEquiv.piCongrRight (fun _ : ι => f.toLinearEquiv)
  have heq : (M.map a.toLinearMap).restrictScalars ℤ =
      (M.restrictScalars ℤ).map (c.toLinearMap.restrictScalars ℤ) := by
    have h_apply (x : ι → D) : a.toLinearMap x = c.toLinearMap x := by
      funext i
      simp only [a, c, LinearEquiv.coe_coe, equivMapPiSemilinear_apply,
        LinearEquiv.piCongrRight_apply,
        AlgEquiv.toLinearEquiv_apply, AlgEquiv.restrictScalars_apply]
    ext x
    simp only [Submodule.restrictScalars_mem, Submodule.mem_map,
      LinearMap.restrictScalars_apply, h_apply]
  rw [heq, Submodule.isFullLattice_map_iff]

/-- Transporting an order by a rational algebra equivalence preserves its class index. -/
theorem classIndex_map {E : Type*} [Ring E] [Algebra ℚ E] (f : D ≃ₐ[ℚ] E) :
    (O.map (f.restrictScalars ℤ).toAlgHom).classIndex e = O.classIndex e := by
  let a := O.equivMapPiSemilinear (f.restrictScalars ℤ) (Fin e)
  rw [classIndex_def, classIndex_def]
  rw [← (Submodule.orderIsoMapComapOfBijective a.toLinearMap a.bijective).toEquiv.iSup_comp]
  refine iSup_congr fun M => ?_
  exact iSup_congr_Prop (O.isFullLattice_map_equivMapPiSemilinear_iff f M) fun _ =>
    (Module.freeClassIndex_equiv (a.submoduleMap M)).symm

end Transport

end Subalgebra

namespace TauCeti.IntegralOrder

open scoped Pointwise

variable {D : Type*} [Ring D] [Algebra ℚ D]
  {O : Subalgebra ℤ D} {e : ℕ}

/-- Every full stable lattice contains an injective image of `O^e` of positive finite additive
index. -/
theorem IsOrder.exists_injective_index_ne_zero (hO : IsOrder ℚ O)
    (M : Submodule O (Fin e → D)) [(M.restrictScalars ℤ).IsFullLattice ℚ] :
    ∃ f : (Fin e → O) →ₗ[O] M,
      Function.Injective f ∧ (LinearMap.range f).toAddSubgroup.index ≠ 0 := by
  let N := Submodule.pi Set.univ (fun _ : Fin e => O.toSubmodule)
  have : O.toSubmodule.IsFullLattice ℚ := isOrder_iff_isFullLattice.1 hO
  have : N.IsFullLattice ℚ := Submodule.IsFullLattice.pi _
  obtain ⟨n, hn, hmem⟩ := Submodule.IsLattice.exists_ne_zero_forall_smul_mem ℚ
    (M.restrictScalars ℤ) (Submodule.IsFullLattice.span_eq_top (A := ℚ))
    (Submodule.IsLattice.fg ℚ N)
  let g : (Fin e → O) →ₗ[O] (Fin e → D) :=
    (LinearMap.toSpanSingleton O D 1).compLeft (Fin e)
  have hg_apply (x : Fin e → O) : g x = fun i => (x i : D) := by
    ext i
    simp [g, Subalgebra.smul_def, smul_eq_mul]
  have hg_mem (x : Fin e → O) : g x ∈ N := by
    rw [hg_apply]
    exact fun i _ => (x i).property
  let f := (n • g).codRestrict M (fun x => hmem _ (hg_mem x))
  have hf : Function.Injective f := by
    intro x y hxy
    have h : n • g x = n • g y := congrArg (fun z : M => (z : Fin e → D)) hxy
    have hg : g x = g y := smul_right_injective (R := ℚ)
      (M := Fin e → D) (Int.cast_ne_zero.mpr hn) (by simpa only [Int.cast_smul_eq_zsmul] using h)
    exact funext fun i => Subtype.ext (by simpa only [hg_apply] using congrFun hg i)
  let u : ℚˣ := Units.mk0 (n : ℚ) (Int.cast_ne_zero.mpr hn)
  let P : Submodule ℤ (Fin e → D) := u • N
  have : P.IsFullLattice ℚ := inferInstance
  have hu (y : Fin e → D) : u • y = n • y := by
    dsimp only [u]
    rw [Units.smul_def, Units.val_mk0, Int.cast_smul_eq_zsmul]
  have hP (x : Fin e → D) : x ∈ P ↔ ∃ y ∈ N, n • y = x := by
    exact (Submodule.mem_smul_pointwise_iff_exists x u N).trans (by simp only [hu])
  have hf_apply (y : Fin e → O) : (f y : Fin e → D) = n • g y := by
    exact (LinearMap.codRestrict_apply M (n • g) y).trans (LinearMap.smul_apply n g y)
  have hgroup : (LinearMap.range f).toAddSubgroup =
      P.toAddSubgroup.comap (M.subtype.toAddMonoidHom) := by
    ext x
    simp only [Submodule.mem_toAddSubgroup, LinearMap.mem_range, AddSubgroup.mem_comap,
      LinearMap.toAddMonoidHom_coe, Submodule.subtype_apply, hP]
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨g y, hg_mem y, (hf_apply y).symm⟩
    · rintro ⟨y, hy, hxy⟩
      refine ⟨fun i => ⟨y i, hy i (Set.mem_univ _)⟩, Subtype.ext ?_⟩
      rw [hf_apply, hg_apply]
      exact hxy
  refine ⟨f, hf, ?_⟩
  rw [hgroup, AddSubgroup.index_comap, ← LinearMap.range_toAddSubgroup, Submodule.range_subtype]
  simpa only [← Submodule.toIntSubmodule_toAddSubgroup M, AddSubgroup.toIntSubmodule_toAddSubgroup]
    using (Submodule.IsFullLattice.relIndex_ne_zero (N := P) (M := M.restrictScalars ℤ))

/-- The least free index of a full stable lattice is attained by an injective map of positive
finite additive index. -/
theorem IsOrder.exists_index_eq_freeClassIndex (hO : IsOrder ℚ O)
    (M : Submodule O (Fin e → D)) [(M.restrictScalars ℤ).IsFullLattice ℚ] :
    ∃ f : (Fin e → O) →ₗ[O] M, Function.Injective f ∧
      (LinearMap.range f).toAddSubgroup.index ≠ 0 ∧
      ((LinearMap.range f).toAddSubgroup.index : ℕ∞) = Module.freeClassIndex O e M :=
  Module.exists_index_eq_freeClassIndex (hO.exists_injective_index_ne_zero M)

/-- The least free index of an individual full stable lattice is finite. This does not assert a
uniform bound over all lattices. -/
theorem IsOrder.freeClassIndex_ne_top (hO : IsOrder ℚ O)
    (M : Submodule O (Fin e → D)) [(M.restrictScalars ℤ).IsFullLattice ℚ] :
    Module.freeClassIndex O e M ≠ ⊤ :=
  Module.freeClassIndex_ne_top_iff.mpr (hO.exists_injective_index_ne_zero M)

end TauCeti.IntegralOrder
