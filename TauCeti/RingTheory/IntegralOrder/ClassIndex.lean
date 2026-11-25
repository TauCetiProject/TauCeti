/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.IntegralOrder.Basic
public import TauCeti.Algebra.Module.Lattice
public import Mathlib.Data.ENat.Lattice

/-!
# Class indices of orders

The least free index of a module is the least positive finite additive index of an injective
map from a free module of the specified rank. It is infinite when no such map exists. The
class index of an order is the supremum of these least indices over its full stable lattices.
Thus its definition does not assume the finiteness theorem for class indices.

The finite-index embedding below clears one common integer denominator in the standard free
lattice. All indices are indices of additive groups.

## References

D. Masser and G. Wüstholz, *Factorization estimates for abelian varieties*, §2.
-/

public section

namespace Module

variable (R : Type*) [Ring R] (e : ℕ) (M : Type*) [AddCommGroup M] [Module R M]

/-- The least positive finite additive index of a free submodule of rank `e`, or infinity if
there is no such free submodule. -/
noncomputable def freeClassIndex : ℕ∞ :=
  ⨅ f : {f : (Fin e → R) →ₗ[R] M //
    Function.Injective f ∧ (LinearMap.range f).toAddSubgroup.index ≠ 0},
    ((LinearMap.range f.val).toAddSubgroup.index : ℕ∞)

variable {R e M}

/-- A finite bound for the least free index is equivalent to an embedding satisfying that bound. -/
theorem freeClassIndex_le_natCast_iff (n : ℕ) : freeClassIndex R e M ≤ n ↔
    ∃ f : (Fin e → R) →ₗ[R] M, Function.Injective f ∧
      (LinearMap.range f).toAddSubgroup.index ≠ 0 ∧
      (LinearMap.range f).toAddSubgroup.index ≤ n := by
  rw [← ENat.lt_add_one_iff (ENat.natCast_ne_top n), freeClassIndex, iInf_lt_iff]
  simp only [ENat.lt_add_one_iff (ENat.natCast_ne_top n), ENat.natCast_le_natCast]
  exact ⟨fun ⟨f, h⟩ => ⟨f.val, f.property.1, f.property.2, h⟩,
    fun ⟨f, hf, hi, h⟩ => ⟨⟨f, hf, hi⟩, h⟩⟩

/-- An injective map of positive finite additive index bounds the least free index. -/
theorem freeClassIndex_le (f : (Fin e → R) →ₗ[R] M) (hf : Function.Injective f)
    (hi : (LinearMap.range f).toAddSubgroup.index ≠ 0) :
    freeClassIndex R e M ≤ (LinearMap.range f).toAddSubgroup.index :=
  (freeClassIndex_le_natCast_iff _).2 ⟨f, hf, hi, le_rfl⟩

/-- Every least free index is at least one, including when no embedding exists. -/
theorem one_le_freeClassIndex : 1 ≤ freeClassIndex R e M := by
  refine le_iInf fun f => ?_
  exact_mod_cast Nat.one_le_iff_ne_zero.2 f.property.2

/-- Whenever an embedding of positive finite index exists, the least index is attained. -/
theorem freeClassIndex_exists_eq
    (h : ∃ f : (Fin e → R) →ₗ[R] M,
      Function.Injective f ∧ (LinearMap.range f).toAddSubgroup.index ≠ 0) :
    ∃ f : (Fin e → R) →ₗ[R] M, Function.Injective f ∧
      (LinearMap.range f).toAddSubgroup.index ≠ 0 ∧
      ((LinearMap.range f).toAddSubgroup.index : ℕ∞) = freeClassIndex R e M := by
  have : Nonempty {f : (Fin e → R) →ₗ[R] M //
      Function.Injective f ∧ (LinearMap.range f).toAddSubgroup.index ≠ 0} :=
    ⟨⟨h.choose, h.choose_spec⟩⟩
  obtain ⟨f, hf⟩ := ENat.exists_eq_iInf (fun f : {f : (Fin e → R) →ₗ[R] M //
      Function.Injective f ∧ (LinearMap.range f).toAddSubgroup.index ≠ 0} =>
    ((LinearMap.range f.val).toAddSubgroup.index : ℕ∞))
  exact ⟨f.val, f.property.1, f.property.2, hf⟩

private theorem freeClassIndex_le_semilinearEquiv {S : Type*} [Ring S] {N : Type*}
    [AddCommGroup N] [Module S N] {σ : R →+* S} {τ : S →+* R}
    [RingHomInvPair σ τ] [RingHomInvPair τ σ] (a : M ≃ₛₗ[σ] N) :
    freeClassIndex S e N ≤ freeClassIndex R e M := by
  conv_rhs => rw [freeClassIndex]
  refine le_iInf fun f => ?_
  let c : (Fin e → S) ≃ₛₗ[τ] (Fin e → R) :=
    { toFun := fun x i => τ (x i)
      invFun := fun x i => σ (x i)
      left_inv := fun x => funext fun i => RingHomInvPair.comp_apply_eq₂
      right_inv := fun x => funext fun i => RingHomInvPair.comp_apply_eq
      map_add' := fun x y => funext fun i => τ.map_add _ _
      map_smul' := fun r x => funext fun i => τ.map_mul _ _ }
  let g : (Fin e → S) →ₗ[S] N := a.toLinearMap.comp (f.val.comp c.toLinearMap)
  have hr : g.toAddMonoidHom.range = f.val.toAddMonoidHom.range.map a.toAddMonoidHom := by
    rw [show g.toAddMonoidHom = a.toAddMonoidHom.comp
      (f.val.toAddMonoidHom.comp c.toAddMonoidHom) from rfl]
    rw [AddMonoidHom.range_comp, AddMonoidHom.range_comp]
    rw [AddMonoidHom.range_eq_top.mpr c.surjective, AddSubgroup.map_top]
  have hi : (LinearMap.range g).toAddSubgroup.index =
      (LinearMap.range f.val).toAddSubgroup.index := by
    rw [LinearMap.range_toAddSubgroup, LinearMap.range_toAddSubgroup, hr]
    exact AddSubgroup.index_map_equiv _ a.toAddEquiv
  simpa only [hi] using freeClassIndex_le g
    (a.injective.comp (f.property.1.comp c.injective)) (hi ▸ f.property.2)

/-- A semilinear equivalence over a ring equivalence preserves the least free index. -/
theorem freeClassIndex_equiv {S : Type*} [Ring S] {N : Type*}
    [AddCommGroup N] [Module S N] {σ : R →+* S} {τ : S →+* R}
    [RingHomInvPair σ τ] [RingHomInvPair τ σ] (a : M ≃ₛₗ[σ] N) :
    freeClassIndex R e M = freeClassIndex S e N :=
  le_antisymm (freeClassIndex_le_semilinearEquiv a.symm)
    (freeClassIndex_le_semilinearEquiv a)

/-- A free module has least free index one in its own rank. -/
@[simp]
theorem freeClassIndex_pi : freeClassIndex R e (Fin e → R) = 1 := by
  apply le_antisymm _ one_le_freeClassIndex
  simpa using freeClassIndex_le (LinearMap.id : (Fin e → R) →ₗ[R] (Fin e → R))
    Function.injective_id (by simp)

/-- A zero-rank free module has index one in a trivial module. -/
@[simp]
theorem freeClassIndex_zero [Subsingleton M] : freeClassIndex R 0 M = 1 := by
  apply le_antisymm _ one_le_freeClassIndex
  let f : (Fin 0 → R) →ₗ[R] M := 0
  have hf : Function.Injective f := Function.injective_of_subsingleton _
  have hr : LinearMap.range f = ⊤ := Subsingleton.elim _ _
  simpa only [hr, Submodule.top_toAddSubgroup, AddSubgroup.index_top, Nat.cast_one] using
    freeClassIndex_le f hf (by simp [hr])

end Module

namespace Subalgebra

variable {D : Type*} [Ring D] (O : Subalgebra ℤ D) (e : ℕ)

variable [Algebra ℚ D]

/-- The class index is the supremum of least free indices of full stable lattices. -/
noncomputable def classIndex : ℕ∞ :=
  ⨆ M : Submodule O (Fin e → D), ⨆ (_ : (M.restrictScalars ℤ).IsFullLattice ℚ),
    Module.freeClassIndex O e M

/-- The least free index of a full stable lattice is bounded by the class index. -/
theorem freeClassIndex_le_classIndex (M : Submodule O (Fin e → D))
    [(M.restrictScalars ℤ).IsFullLattice ℚ] :
    Module.freeClassIndex O e M ≤ O.classIndex e :=
  le_iSup_of_le M (le_iSup_of_le inferInstance le_rfl)

/-- A uniform bound for all least free indices bounds the class index, and conversely. -/
theorem classIndex_le_iff {n : ℕ∞} : O.classIndex e ≤ n ↔
    ∀ M : Submodule O (Fin e → D), (M.restrictScalars ℤ).IsFullLattice ℚ →
      Module.freeClassIndex O e M ≤ n := by
  simp only [classIndex, iSup_le_iff]

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
      ext x
      rfl
    rw [heq]
    constructor
    · intro h
      have := h
      have hh := Submodule.isFullLattice_comap
        ((M.restrictScalars ℤ).map (c.toLinearMap.restrictScalars ℤ))
        c.toLinearMap c.injective
      have hc : Function.Injective (c.toLinearMap.restrictScalars ℤ) := c.injective
      rwa [Submodule.comap_map_eq_of_injective hc] at hh
    · intro h
      have := h
      exact Submodule.isFullLattice_map _ c.toLinearMap c.surjective
  unfold classIndex
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
  -- View the same scaling first as a rational unit, then as an integer multiple.
  have hgroup : (LinearMap.range f).toAddSubgroup =
      P.toAddSubgroup.comap (M.subtype.toAddMonoidHom) := by
    ext x
    change (∃ y, f y = x) ↔ ∃ y ∈ N, u • y = (x : Fin e → D)
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨g y, (by intro i _; exact (y i).property), by
        change (n : ℚ) • g y = n • g y
        exact Int.cast_smul_eq_zsmul ℚ n (g y)⟩
    · rintro ⟨y, hy, hxy⟩
      refine ⟨fun i => ⟨y i, hy i (Set.mem_univ _)⟩, Subtype.ext ?_⟩
      change n • y = (x : Fin e → D)
      change (n : ℚ) • y = (x : Fin e → D) at hxy
      simpa only [Int.cast_smul_eq_zsmul] using hxy
  refine ⟨f, hf, ?_⟩
  rw [hgroup, AddSubgroup.index_comap]
  have hM : M.subtype.toAddMonoidHom.range = (M.restrictScalars ℤ).toAddSubgroup := by
    rw [← LinearMap.range_toAddSubgroup, Submodule.range_subtype]
    rfl
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
    Module.freeClassIndex O e M ≠ ⊤ := by
  obtain ⟨f, hf, hi⟩ := hO.exists_injective_index_ne_zero M
  exact ne_top_of_le_ne_top (ENat.natCast_ne_top _) (Module.freeClassIndex_le f hf hi)

end TauCeti.IntegralOrder
