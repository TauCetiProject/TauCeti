/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.IntegralOrder.Basic
public import TauCeti.Algebra.Module.Lattice
public import TauCeti.Algebra.Module.FreeClassIndex

/-!
# Class indices of orders

The class index of an order is the supremum of the least free indices of its full stable
lattices. The module invariant `Module.freeClassIndex` is defined independently in
`TauCeti.Algebra.Module.FreeClassIndex`. Thus the class-index definition does not assume the
finiteness theorem for class indices.

The finite-index embedding below clears one common integer denominator in the standard free
lattice. All indices are indices of additive groups.

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
    have hM : (M.restrictScalars ℤ).IsFullLattice ℚ := by
      have heq : M.restrictScalars ℤ = ⊥ := Subsingleton.elim _ _
      rw [heq]
      exact { toIsLattice := Submodule.IsLattice.of_fg ℚ Submodule.fg_bot
              span_eq_top := Subsingleton.elim _ _ }
    rw [classIndex_def]
    exact (Module.one_le_freeClassIndex (R := O) (e := 0) (M := M)).trans
      (le_iSup_of_le M (le_iSup_of_le hM le_rfl))

/-- Transporting an order by a rational algebra equivalence preserves its class index. -/
theorem classIndex_map {E : Type*} [Ring E] [Algebra ℚ E] (f : D ≃ₐ[ℚ] E) :
    (O.map (f.restrictScalars ℤ).toAlgHom).classIndex e = O.classIndex e := by
  let r := O.equivMapOfInjective (f.restrictScalars ℤ).toAlgHom f.injective
  have := RingHomInvPair.of_ringEquiv r.toRingEquiv
  have := RingHomInvPair.symm (r.toRingEquiv : O →+* (O.map (f.restrictScalars ℤ).toAlgHom))
    (r.toRingEquiv.symm : (O.map (f.restrictScalars ℤ).toAlgHom) →+* O)
  let c := LinearEquiv.piCongrRight (fun _ : Fin e => f.toLinearEquiv)
  let a : (Fin e → D) ≃ₛₗ[
      (r.toRingEquiv : O →+* (O.map (f.restrictScalars ℤ).toAlgHom))] (Fin e → E) :=
    { c.toEquiv with
      map_add' := c.map_add
      map_smul' := fun b x => funext fun i => f.map_mul (b : D) (x i) }
  have hfull (M : Submodule O (Fin e → D)) :
      ((M.map a.toLinearMap).restrictScalars ℤ).IsFullLattice ℚ ↔
        (M.restrictScalars ℤ).IsFullLattice ℚ := by
    have heq : (M.map a.toLinearMap).restrictScalars ℤ =
        (M.restrictScalars ℤ).map (c.toLinearMap.restrictScalars ℤ) := by
      -- The semilinear order transport and the rational linear transport agree pointwise.
      have h_apply (x : Fin e → D) : a.toLinearMap x = c.toLinearMap x := rfl
      ext x
      simp only [Submodule.restrictScalars_mem, Submodule.mem_map,
        LinearMap.restrictScalars_apply, h_apply]
    rw [heq, Submodule.isFullLattice_map_iff]
  rw [classIndex_def, classIndex_def]
  rw [← (Submodule.orderIsoMapComapOfBijective a.toLinearMap a.bijective).toEquiv.iSup_comp]
  refine iSup_congr fun M => ?_
  exact iSup_congr_Prop (hfull M) fun _ =>
    (Module.freeClassIndex_equiv (a.submoduleMap M)).symm

end Subalgebra

namespace TauCeti.IntegralOrder

open scoped Pointwise

variable {D : Type*} [Ring D] [Algebra ℚ D]
  {O : Subalgebra ℤ D} {e : ℕ}

/-- Every full stable lattice contains an injective image of `O^e` of positive finite additive
index. A single nonzero integer clears denominators in the standard free lattice. -/
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
    { toFun := fun x i => (x i : D)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let f : (Fin e → O) →ₗ[O] M :=
    { toFun := fun x => ⟨n • g x, hmem _ (by intro i _; exact (x i).property)⟩
      map_add' := fun x y => Subtype.ext (by simp)
      map_smul' := fun a x => Subtype.ext (by simp [smul_comm]) }
  have hf : Function.Injective f := by
    intro x y hxy
    have h : n • g x = n • g y := congrArg (fun z : M => (z : Fin e → D)) hxy
    have hg : g x = g y := smul_right_injective (R := ℚ)
      (M := Fin e → D) (Int.cast_ne_zero.mpr hn) (by simpa only [Int.cast_smul_eq_zsmul] using h)
    exact funext fun i => Subtype.ext (congrFun hg i)
  let u : ℚˣ := Units.mk0 (n : ℚ) (Int.cast_ne_zero.mpr hn)
  let P : Submodule ℤ (Fin e → D) := u • N
  have : P.IsFullLattice ℚ := inferInstance
  have hu (y : Fin e → D) : u • y = n • y := by
    dsimp only [u]
    rw [Units.smul_def, Units.val_mk0, Int.cast_smul_eq_zsmul]
  have hP (x : Fin e → D) : x ∈ P ↔ ∃ y ∈ N, n • y = x := by
    exact (Submodule.mem_smul_pointwise_iff_exists x u N).trans (by simp only [hu])
  -- The map `f` was constructed by scaling `g` and bundling the result in `M`.
  have hf_apply (y : Fin e → O) : (f y : Fin e → D) = n • g y := rfl
  have hgroup : (LinearMap.range f).toAddSubgroup =
      P.toAddSubgroup.comap (M.subtype.toAddMonoidHom) := by
    ext x
    simp only [Submodule.mem_toAddSubgroup, LinearMap.mem_range, AddSubgroup.mem_comap,
      LinearMap.toAddMonoidHom_coe, Submodule.subtype_apply, hP]
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨g y, (by intro i _; exact (y i).property), (hf_apply y).symm⟩
    · rintro ⟨y, hy, hxy⟩
      exact ⟨fun i => ⟨y i, hy i (Set.mem_univ _)⟩, Subtype.ext ((hf_apply _).trans hxy)⟩
  refine ⟨f, hf, ?_⟩
  rw [hgroup, AddSubgroup.index_comap]
  have hM : M.subtype.toAddMonoidHom.range = (M.restrictScalars ℤ).toAddSubgroup := by
    rw [← LinearMap.range_toAddSubgroup, Submodule.range_subtype,
      ← Submodule.toIntSubmodule_toAddSubgroup, AddSubgroup.toIntSubmodule_toAddSubgroup]
  rw [hM]
  exact Submodule.IsFullLattice.relIndex_ne_zero

/-- The least free index of a full stable lattice is attained by an injective map of positive
finite additive index. -/
theorem IsOrder.freeClassIndex_exists_eq (hO : IsOrder ℚ O)
    (M : Submodule O (Fin e → D)) [(M.restrictScalars ℤ).IsFullLattice ℚ] :
    ∃ f : (Fin e → O) →ₗ[O] M, Function.Injective f ∧
      (LinearMap.range f).toAddSubgroup.index ≠ 0 ∧
      ((LinearMap.range f).toAddSubgroup.index : ℕ∞) = Module.freeClassIndex O e M :=
  Module.freeClassIndex_exists_eq (hO.exists_injective_index_ne_zero M)

/-- The least free index of an individual full stable lattice is finite. This does not assert a
uniform bound over all lattices. -/
theorem IsOrder.freeClassIndex_ne_top (hO : IsOrder ℚ O)
    (M : Submodule O (Fin e → D)) [(M.restrictScalars ℤ).IsFullLattice ℚ] :
    Module.freeClassIndex O e M ≠ ⊤ :=
  Module.freeClassIndex_ne_top_iff.mpr (hO.exists_injective_index_ne_zero M)

end TauCeti.IntegralOrder
