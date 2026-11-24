/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.FreeModule.PID
public import TauCeti.Geometry.Toric.Algebraic.Cone.Basic
public import TauCeti.Geometry.Toric.Algebraic.DualSemigroup.Basic

/-!
# The sublattice spanned by a cone

For a cone `σ` in the real vector space of a lattice `i : N →+ V`, the sublattice `N_σ` consists
of the lattice vectors in the real span of `σ`. It is saturated: the quotient lattice
`N(σ) = N ⧸ N_σ` is torsion free, and hence free when `N` is finitely generated. The torus of
`N(σ)` is the torus acting simply transitively on the orbit of `σ` in a toric variety.

An integral character vanishes on a lattice-rational cone `σ` exactly when it vanishes on `N_σ`.
So the characters of `N(σ)` are the integral characters vanishing on `σ`; these are the characters
whose monomials are units along the orbit of `σ`.

## Main declarations

* `TauCeti.Toric.coneSublattice`: the sublattice `N_σ` of lattice vectors in the span of `σ`.
* `TauCeti.Toric.mem_coneSublattice_of_zsmul_mem` and
  `TauCeti.Toric.hasUniqueDiv_quotient_coneSublattice`: `N_σ` is saturated, so the quotient
  `N ⧸ N_σ` is torsion free.
* `TauCeti.Toric.free_quotient_coneSublattice`: for finitely generated `N`, the quotient
  `N ⧸ N_σ` is free.
* `TauCeti.Toric.IsLatticeRational.finrank_coneSublattice`: for a lattice-rational cone, the rank
  of `N_σ` is the dimension of the real span of `σ`.
* `TauCeti.Toric.IsLatticeRational.exists_mem_notMem_coneSublattice`: if the span of a
  lattice-rational cone `σ` is not contained in the span of `τ`, some lattice vector of `σ` lies
  outside `N_τ`.
* `TauCeti.Toric.IsLatticeRational.forall_realCharacter_eq_zero_iff_coneSublattice_le_ker`: an
  integral character vanishes on a lattice-rational cone exactly when its kernel contains `N_σ`.
* `TauCeti.Toric.IsLatticeRational.realCharacter_comp_mk'_eq_zero` and
  `TauCeti.Toric.IsLatticeRational.comp_mk'_mem_dualSemigroup`: every character of `N ⧸ N_σ`
  vanishes on `σ`, so it lies in the dual semigroup of `σ`.

## References

* W. Fulton, *Introduction to Toric Varieties*, §3.1.
* D. Cox, J. Little and H. Schenck, *Toric Varieties*, §3.2.
-/

public section

namespace TauCeti.Toric

variable {N V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {σ : PointedCone ℝ V}

/-- The sublattice `N_σ` of a cone `σ`: the lattice vectors whose images lie in the real span
of `σ`. -/
def coneSublattice (i : N →+ V) (σ : PointedCone ℝ V) : AddSubgroup N :=
  (Submodule.span ℝ (σ : Set V)).toAddSubgroup.comap i

/-- A lattice vector lies in `N_σ` exactly when its image lies in the real span of `σ`. -/
@[simp]
theorem mem_coneSublattice {n : N} :
    n ∈ coneSublattice i σ ↔ i n ∈ Submodule.span ℝ (σ : Set V) :=
  (Iff.rfl)

/-- The sublattice of a cone grows with the cone. -/
theorem coneSublattice_mono {τ : PointedCone ℝ V} (h : τ ≤ σ) :
    coneSublattice i τ ≤ coneSublattice i σ :=
  fun _ hn ↦ Submodule.span_mono h hn

/-- The sublattice of the zero cone is zero, since an integral lattice map is injective. -/
theorem coneSublattice_bot (hi : IsIntegralLattice i) : coneSublattice i ⊥ = ⊥ := by
  ext n
  simp [hi.injective.eq_iff' (map_zero i)]

/-- The sublattice of a cone is saturated: if a nonzero multiple of a lattice vector lies in
`N_σ`, so does the vector. -/
theorem mem_coneSublattice_of_zsmul_mem {k : ℤ} (hk : k ≠ 0) {n : N}
    (h : k • n ∈ coneSublattice i σ) : n ∈ coneSublattice i σ := by
  rw [mem_coneSublattice, map_zsmul, ← Int.cast_smul_eq_zsmul ℝ] at h
  simpa [Int.cast_ne_zero.2 hk] using Submodule.smul_mem _ (k : ℝ)⁻¹ h

/-- The sublattice of a cone is saturated: the quotient lattice `N ⧸ N_σ` is torsion free. -/
instance hasUniqueDiv_quotient_coneSublattice :
    HasUniqueDiv (N ⧸ coneSublattice i σ) := by
  rw [← Module.isTorsionFree_int_iff_hasUniqueDiv, Module.isTorsionFree_iff_smul_eq_zero]
  intro k x hkx
  induction x using QuotientAddGroup.induction_on with
  | H n =>
    rw [← QuotientAddGroup.mk_zsmul, QuotientAddGroup.eq_zero_iff] at hkx
    rw [or_iff_not_imp_left, QuotientAddGroup.eq_zero_iff]
    exact fun hk ↦ mem_coneSublattice_of_zsmul_mem hk hkx

/-- For a finitely generated lattice `N`, the quotient lattice `N ⧸ N_σ` is free: it is finitely
generated and torsion free. -/
instance free_quotient_coneSublattice [Module.Finite ℤ N] :
    Module.Free ℤ (N ⧸ coneSublattice i σ) :=
  have : Module.Finite ℤ (N ⧸ coneSublattice i σ) :=
    Module.Finite.of_surjective (QuotientAddGroup.mk' _).toIntLinearMap
      (QuotientAddGroup.mk'_surjective _)
  inferInstance

/-- An integral character vanishes on a lattice-rational cone `σ` exactly when it vanishes on the
sublattice `N_σ`. -/
theorem IsLatticeRational.forall_realCharacter_eq_zero_iff_coneSublattice_le_ker
    (hσ : IsLatticeRational i σ) (hi : IsIntegralLattice i) (m : N →+ ℤ) :
    (∀ y ∈ σ, hi.realCharacter m y = 0) ↔ coneSublattice i σ ≤ m.ker := by
  constructor
  · intro hm n hn
    -- The character vanishes on the real span of `σ`, which contains `i n`.
    have hspan : Submodule.span ℝ (σ : Set V) ≤ LinearMap.ker (hi.realCharacter m) :=
      Submodule.span_le.2 hm
    have h := hspan (mem_coneSublattice.1 hn)
    rw [LinearMap.mem_ker, hi.realCharacter_apply, Int.cast_eq_zero] at h
    exact h
  · intro hm y hy
    -- The cone is the hull of finitely many lattice vectors, all of which lie in `N_σ`.
    obtain ⟨s, rfl⟩ := isLatticeRational_iff.1 hσ
    have hgen : i '' (s : Set N) ⊆ LinearMap.ker (hi.realCharacter m) := by
      rintro _ ⟨n, hn, rfl⟩
      have hn' : n ∈ coneSublattice i (PointedCone.hull ℝ (i '' (s : Set N))) :=
        Submodule.subset_span (PointedCone.subset_hull ⟨n, hn, rfl⟩)
      rw [SetLike.mem_coe, LinearMap.mem_ker, hi.realCharacter_apply,
        AddMonoidHom.mem_ker.1 (hm hn'), Int.cast_zero]
    exact Submodule.span_le.2 hgen (PointedCone.hull_le_span ℝ _ hy)

/-- Every character of the quotient lattice `N ⧸ N_σ` of a lattice-rational cone `σ` vanishes on
`σ`. -/
theorem IsLatticeRational.realCharacter_comp_mk'_eq_zero (hσ : IsLatticeRational i σ)
    (hi : IsIntegralLattice i) (m : N ⧸ coneSublattice i σ →+ ℤ) {y : V} (hy : y ∈ σ) :
    hi.realCharacter (m.comp (QuotientAddGroup.mk' (coneSublattice i σ))) y = 0 :=
  (hσ.forall_realCharacter_eq_zero_iff_coneSublattice_le_ker hi _).2
    (fun n hn ↦ by simp [(QuotientAddGroup.eq_zero_iff n).2 hn]) y hy

/-- Every character of the quotient lattice `N ⧸ N_σ` of a lattice-rational cone `σ` lies in the
dual semigroup of `σ`. -/
theorem IsLatticeRational.comp_mk'_mem_dualSemigroup (hσ : IsLatticeRational i σ)
    (hi : IsIntegralLattice i) (m : N ⧸ coneSublattice i σ →+ ℤ) :
    m.comp (QuotientAddGroup.mk' (coneSublattice i σ)) ∈ dualSemigroup hi σ :=
  (mem_dualSemigroup hi _).2 fun _ hy ↦ (hσ.realCharacter_comp_mk'_eq_zero hi m hy).ge

/-- The real span of the sublattice of a lattice-rational cone is the real span of the cone. -/
theorem IsLatticeRational.span_image_coneSublattice (hσ : IsLatticeRational i σ) :
    Submodule.span ℝ (i '' coneSublattice i σ) = Submodule.span ℝ (σ : Set V) := by
  refine le_antisymm (Submodule.span_le.2 ?_) ?_
  · rintro _ ⟨n, hn, rfl⟩
    exact mem_coneSublattice.1 hn
  · obtain ⟨s, hs⟩ := isLatticeRational_iff.1 hσ
    have hsub : i '' (s : Set N) ⊆ i '' coneSublattice i σ := by
      rintro _ ⟨n, hn, rfl⟩
      exact ⟨n, Submodule.subset_span (hs ▸ PointedCone.subset_hull ⟨n, hn, rfl⟩), rfl⟩
    refine Submodule.span_le.2 fun x hx ↦ ?_
    rw [hs] at hx
    exact Submodule.span_mono hsub (PointedCone.hull_le_span ℝ _ hx)

/-- The integral rank of the sublattice `N_σ` of a lattice-rational cone is the dimension of the
real span of `σ`. -/
theorem IsLatticeRational.finrank_coneSublattice (hσ : IsLatticeRational i σ)
    (hi : IsIntegralLattice i) :
    Module.finrank ℤ (coneSublattice i σ).toIntSubmodule =
      Module.finrank ℝ (Submodule.span ℝ (σ : Set V)) := by
  rw [← hσ.span_image_coneSublattice, ← hi.finrank_span_image, AddSubgroup.coe_toIntSubmodule]

/-- If the real span of a lattice-rational cone `σ` is not contained in the real span of `τ`, some
lattice vector of `σ` lies outside `N_τ`. -/
theorem IsLatticeRational.exists_mem_notMem_coneSublattice (hσ : IsLatticeRational i σ)
    {τ : PointedCone ℝ V}
    (h : ¬ Submodule.span ℝ (σ : Set V) ≤ Submodule.span ℝ (τ : Set V)) :
    ∃ g : N, i g ∈ σ ∧ g ∉ coneSublattice i τ := by
  by_contra! hg
  obtain ⟨s, hs⟩ := isLatticeRational_iff.1 hσ
  refine h ?_
  rw [hs, PointedCone.hull, Submodule.span_span_of_tower]
  refine Submodule.span_le.2 ?_
  rintro _ ⟨n, hn, rfl⟩
  exact mem_coneSublattice.1 (hg n (hs ▸ PointedCone.subset_hull ⟨n, hn, rfl⟩))

end TauCeti.Toric
