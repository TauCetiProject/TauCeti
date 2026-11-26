/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.CartanInvolution.RestrictedRoot.Basic
public import TauCeti.Algebra.Lie.SpecialLinear.Cartan
public import TauCeti.Algebra.Lie.SpecialLinear.Character
public import TauCeti.Algebra.Lie.SpecialLinear.Root.Base

/-!
# Restricted roots of `𝔰𝔩_n(ℝ)`

On `𝔰𝔩_{r+1}(ℝ)` with the Cartan involution `θ X = -Xᵀ` (`TauCeti.specialLinearNegTranspose`), the
trace-zero diagonal matrices `𝔞 = TauCeti.specialLinearDiagonal r ℝ` form a maximal abelian
subspace of the `-1`-eigenspace `𝔭` (the symmetric matrices). For `H ∈ 𝔞` the bracket `[H, X]`
has `(k, l)` entry `(H k k - H l l) X k l` (`TauCeti.lie_apply_of_mem_specialLinearDiagonal`), so:

* the centralizer `𝔤_0` of `𝔞` is `𝔞` itself, and `𝔪 = 𝔤_0 ∩ 𝔨 = 0`;
* the restricted roots are the functionals `e_i - e_j : H ↦ H i i - H j j` for `i ≠ j`, the
  roots `εᵢ - εⱼ` of the coordinate weights `TauCeti.specialLinearEpsilon` read on `𝔞`;
* the restricted root space of `e_i - e_j` is the line `ℝ E_ij` of the matrix unit.

This is the split case of the restricted root decomposition: `𝔞` is a Cartan subalgebra, every
restricted root space is a line, and `𝔪 = 0`.

## Main results

* `TauCeti.specialLinearRestrictedRoot`: the functional `e_i - e_j` on `𝔞`.
* `TauCeti.isMaximalAbelianInP_specialLinearDiagonal`: `𝔞` is maximal abelian in `𝔭`.
* `TauCeti.restrictedRootSpace_zero_inf_fixedSubalgebra_specialLinearDiagonal`: `𝔪 = 0`.
* `TauCeti.restrictedRootSpace_specialLinearRestrictedRoot`: the root space of `e_i - e_j` is
  `ℝ E_ij`.
* `TauCeti.mem_restrictedRoots_specialLinearDiagonal_iff`: the restricted roots are the
  `e_i - e_j` with `i ≠ j`.

## References

* A. W. Knapp, *Lie Groups Beyond an Introduction*, 2nd ed., Chapter VI, §4, and Appendix C.
* S. Helgason, *Differential Geometry, Lie Groups, and Symmetric Spaces*, Chapter X, Table VI.
-/

public section

open LieAlgebra LieAlgebra.SpecialLinear Matrix Module Submodule

attribute [local instance 100] LieRing.ofAssociativeRing

namespace TauCeti

variable (r : ℕ) (A : Type*) [CommRing A]

/-- The functional `e_i - e_j : H ↦ H i i - H j j` on the trace-zero diagonal matrices: the
root `εᵢ - εⱼ` of the coordinate weights `TauCeti.specialLinearEpsilon`, read on
`specialLinearDiagonal r A`, the underlying submodule of `specialLinearDiagonalCartan r A`.
Over `ℝ` it is a restricted root exactly when `i ≠ j`
(`TauCeti.mem_restrictedRoots_specialLinearDiagonal_iff`); for `i = j` it is `0`. -/
def specialLinearRestrictedRoot (i j : Fin (r + 1)) : Dual A (specialLinearDiagonal r A) :=
  (specialLinearEpsilon r A i - specialLinearEpsilon r A j) ∘ₗ
    (LinearEquiv.ofEq _ _ (specialLinearDiagonalCartan_toSubmodule r A).symm).toLinearMap

variable {r A}

/-- The functional `e_i - e_j` evaluates to `H i i - H j j`. -/
@[simp]
theorem specialLinearRestrictedRoot_apply (i j : Fin (r + 1)) (H : specialLinearDiagonal r A) :
    specialLinearRestrictedRoot r A i j H =
      ((H : sl (Fin (r + 1)) A) : Matrix (Fin (r + 1)) (Fin (r + 1)) A) i i -
        ((H : sl (Fin (r + 1)) A) : Matrix (Fin (r + 1)) (Fin (r + 1)) A) j j := by
  rw [specialLinearRestrictedRoot, LinearMap.comp_apply, LinearMap.sub_apply,
    specialLinearEpsilon_apply, specialLinearEpsilon_apply, LinearEquiv.coe_coe,
    LinearEquiv.coe_ofEq_apply]

/-- On `H ∈ specialLinearDiagonalCartan r A`, the functional `e_i - e_j` is `εᵢ - εⱼ`. -/
theorem specialLinearRestrictedRoot_apply_mk (i j : Fin (r + 1))
    (H : specialLinearDiagonalCartan r A) :
    specialLinearRestrictedRoot r A i j
        ⟨H, mem_specialLinearDiagonalCartan_iff_mem_specialLinearDiagonal.mp H.property⟩ =
      (specialLinearEpsilon r A i - specialLinearEpsilon r A j) H := by
  rw [specialLinearRestrictedRoot, LinearMap.comp_apply, LinearEquiv.coe_coe]
  exact congrArg _ (Subtype.ext (LinearEquiv.coe_ofEq_apply _ _))

/-- On `H ∈ specialLinearDiagonalCartan r K`, the functional `e_i - e_j` with `i ≠ j` is the root
`εᵢ - εⱼ` (`TauCeti.specialLinearRoot`). -/
theorem specialLinearRestrictedRoot_apply_mk_eq_specialLinearRoot {K : Type*} [Field K]
    {i j : Fin (r + 1)} (hij : i ≠ j) (H : specialLinearDiagonalCartan r K) :
    specialLinearRestrictedRoot r K i j
        ⟨H, mem_specialLinearDiagonalCartan_iff_mem_specialLinearDiagonal.mp H.property⟩ =
      specialLinearRoot r K i j hij H := by
  rw [specialLinearRestrictedRoot_apply_mk, specialLinearRoot_apply, LinearMap.sub_apply]

/-- `e_k - e_k = 0`. -/
@[simp]
theorem specialLinearRestrictedRoot_self (k : Fin (r + 1)) :
    specialLinearRestrictedRoot r A k k = 0 :=
  LinearMap.ext fun H ↦ by rw [specialLinearRestrictedRoot_apply, sub_self, LinearMap.zero_apply]

/-- The functionals `e_k - e_l` and `e_i - e_j` with `i ≠ j` coincide exactly when
`(k, l) = (i, j)`. -/
@[simp]
theorem specialLinearRestrictedRoot_inj {i j k l : Fin (r + 1)} (hij : i ≠ j) :
    specialLinearRestrictedRoot r ℝ k l = specialLinearRestrictedRoot r ℝ i j ↔ k = i ∧ l = j := by
  refine ⟨fun h ↦ ?_, fun ⟨hki, hlj⟩ ↦ hki ▸ hlj ▸ rfl⟩
  by_cases hkl : k = l
  · subst hkl
    rw [specialLinearRestrictedRoot_self] at h
    refine absurd (funext fun H ↦ ?_) (specialLinearRoot_isNonZero (K := ℝ) hij)
    rw [Pi.zero_apply, ← specialLinearRestrictedRoot_apply_mk_eq_specialLinearRoot hij, ← h,
      LinearMap.zero_apply]
  · refine (specialLinearRoot_inj (K := ℝ) hkl hij).mp (LieModule.Weight.ext fun H ↦ ?_)
    rw [← specialLinearRestrictedRoot_apply_mk_eq_specialLinearRoot hkl, h,
      specialLinearRestrictedRoot_apply_mk_eq_specialLinearRoot hij]

/-- `X ∈ 𝔤_μ` exactly when `(H k k - H l l - μ H) X k l = 0` for every `H ∈ 𝔞` and every entry. -/
theorem mem_restrictedRootSpace_specialLinearDiagonal_iff {μ : Dual A (specialLinearDiagonal r A)}
    {X : sl (Fin (r + 1)) A} :
    X ∈ (specialLinearDiagonal r A).restrictedRootSpace μ ↔
      ∀ (H : specialLinearDiagonal r A) (k l : Fin (r + 1)),
        (specialLinearRestrictedRoot r A k l H - μ H) *
          (X : Matrix (Fin (r + 1)) (Fin (r + 1)) A) k l = 0 := by
  rw [mem_restrictedRootSpace]
  refine forall_congr' fun H ↦ ⟨fun h k l ↦ ?_, fun h ↦ ?_⟩
  · have := congrFun (congrFun (congrArg Subtype.val h) k) l
    rw [lie_apply_of_mem_specialLinearDiagonal H.property] at this
    rw [SetLike.val_smul, Matrix.smul_apply, smul_eq_mul] at this
    rw [specialLinearRestrictedRoot_apply, sub_mul, this, sub_self]
  · ext k l
    rw [lie_apply_of_mem_specialLinearDiagonal H.property, SetLike.val_smul, Matrix.smul_apply,
      smul_eq_mul, ← sub_eq_zero, ← sub_mul, ← specialLinearRestrictedRoot_apply]
    exact h k l

/-- The centralizer `𝔤_0` of `𝔞` in `𝔰𝔩_{r+1}(ℝ)` is `𝔞` itself: an element commuting with every
trace-zero diagonal matrix is diagonal. -/
theorem restrictedRootSpace_zero_specialLinearDiagonal :
    (specialLinearDiagonal r ℝ).restrictedRootSpace 0 = specialLinearDiagonal r ℝ := by
  refine le_antisymm (fun X hX ↦ ?_) (Submodule.le_restrictedRootSpace_zero
    fun _ hX _ hY ↦ lie_eq_zero_of_mem_specialLinearDiagonal hX hY)
  rw [← specialLinearDiagonalCartan_toSubmodule, LieSubalgebra.mem_toSubmodule,
    ← specialLinearDiagonalCartan_normalizer_eq_self r ℝ (.inr (.of_ne_zero' two_ne_zero)),
    LieSubalgebra.mem_normalizer_iff']
  intro H hH
  rw [mem_restrictedRootSpace_zero.mp hX
    ⟨H, mem_specialLinearDiagonalCartan_iff_mem_specialLinearDiagonal.mp hH⟩]
  exact zero_mem _

/-- `𝔞` lies in the `-1`-eigenspace `𝔭` of `X ↦ -Xᵀ`: diagonal matrices are symmetric. -/
theorem specialLinearDiagonal_le_cartanP :
    specialLinearDiagonal r ℝ ≤ (specialLinearNegTranspose r).cartanP := fun _ hX ↦
  LieEquiv.mem_cartanP.mpr (specialLinearNegTranspose_apply_of_mem_specialLinearDiagonal hX)

/-- **The trace-zero diagonal matrices are a maximal abelian subspace of `𝔭`.** -/
theorem isMaximalAbelianInP_specialLinearDiagonal :
    (specialLinearNegTranspose r).IsMaximalAbelianInP (specialLinearDiagonal r ℝ) := by
  refine LieEquiv.isMaximalAbelianInP_iff.mpr ⟨⟨specialLinearDiagonal_le_cartanP, ?_⟩,
    fun 𝔟 h𝔟 hle Y hY ↦ ?_⟩
  · exact fun _ hX _ hY ↦ lie_eq_zero_of_mem_specialLinearDiagonal hX hY
  · rw [← restrictedRootSpace_zero_specialLinearDiagonal, mem_restrictedRootSpace_zero]
    exact fun H ↦ h𝔟.2 _ (hle H.property) Y hY

/-- **`𝔪 = 0`**: no nonzero element of the fixed subalgebra `𝔨` (the skew-symmetric matrices)
centralizes `𝔞`. -/
theorem restrictedRootSpace_zero_inf_fixedSubalgebra_specialLinearDiagonal :
    (specialLinearDiagonal r ℝ).restrictedRootSpace 0 ⊓
      (specialLinearNegTranspose r).toLieHom.fixedSubalgebra.toSubmodule = ⊥ := by
  rw [restrictedRootSpace_zero_specialLinearDiagonal, ← disjoint_iff]
  exact ((specialLinearNegTranspose r).isCompl_fixedSubalgebra_cartanP two_ne_zero.isUnit
    (isCartanInvolution_specialLinearNegTranspose r).involutive).disjoint.symm.mono_left
      specialLinearDiagonal_le_cartanP

/-- **The restricted root space of `e_i - e_j` is the line of the matrix unit `E_ij`.** -/
theorem restrictedRootSpace_specialLinearRestrictedRoot {i j : Fin (r + 1)} (hij : i ≠ j) :
    (specialLinearDiagonal r ℝ).restrictedRootSpace (specialLinearRestrictedRoot r ℝ i j) =
      span ℝ {single i j hij 1} := by
  ext X
  rw [mem_span_singleton]
  constructor
  · rw [mem_restrictedRootSpace_specialLinearDiagonal_iff]
    intro h
    refine ⟨(X : Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ) i j, Subtype.ext ?_⟩
    ext k l
    rw [SetLike.val_smul, val_single, Matrix.smul_apply, single_apply, smul_eq_mul]
    by_cases hkl : i = k ∧ j = l
    · obtain ⟨rfl, rfl⟩ := hkl
      simp
    · rw [ite_eq_right hkl, mul_zero, eq_comm]
      -- Choose `H ∈ 𝔞` with `H k k - H l l ≠ H i i - H j j`.
      have hne : specialLinearRestrictedRoot r ℝ k l ≠ specialLinearRestrictedRoot r ℝ i j :=
        fun h' ↦ hkl (((specialLinearRestrictedRoot_inj hij).mp h').imp Eq.symm Eq.symm)
      obtain ⟨H, hH⟩ := not_forall.mp (mt LinearMap.ext hne)
      exact (mul_eq_zero.mp (h H k l)).resolve_left (sub_ne_zero.mpr hH)
  · rintro ⟨c, rfl⟩
    refine mem_restrictedRootSpace.mpr fun H ↦ ?_
    have := lie_specialLinearDiagonalCartan_single
      ⟨H, mem_specialLinearDiagonalCartan_iff_mem_specialLinearDiagonal.mpr H.property⟩ hij c
    rw [LieSubalgebra.coe_bracket_of_module, ← specialLinearRestrictedRoot_apply_mk] at this
    rw [← map_smul, smul_eq_mul, mul_one]
    exact this

/-- **The restricted roots of `𝔰𝔩_{r+1}(ℝ)` are the `e_i - e_j` with `i ≠ j`.** -/
theorem mem_restrictedRoots_specialLinearDiagonal_iff {μ : Dual ℝ (specialLinearDiagonal r ℝ)} :
    μ ∈ (specialLinearDiagonal r ℝ).restrictedRoots ↔
      ∃ i j, i ≠ j ∧ μ = specialLinearRestrictedRoot r ℝ i j := by
  rw [mem_restrictedRoots]
  constructor
  · rintro ⟨hμ, hne⟩
    obtain ⟨X, hX, hX0⟩ := (Submodule.ne_bot_iff _).mp hne
    have hX0' : (X : Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ) ≠ 0 := fun h ↦ hX0 (Subtype.ext h)
    obtain ⟨k, l, hkl⟩ : ∃ k l, (X : Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ) k l ≠ 0 := by
      by_contra! h
      exact hX0' (Matrix.ext h)
    have hroot : μ = specialLinearRestrictedRoot r ℝ k l := LinearMap.ext fun H ↦
      (sub_eq_zero.mp ((mul_eq_zero.mp
        (mem_restrictedRootSpace_specialLinearDiagonal_iff.mp hX H k l)).resolve_right hkl)).symm
    refine ⟨k, l, fun h ↦ hμ ?_, hroot⟩
    rw [hroot, h, specialLinearRestrictedRoot_self]
  · rintro ⟨i, j, hij, rfl⟩
    refine ⟨fun h ↦ ?_, ?_⟩
    · exact hij ((specialLinearRestrictedRoot_inj hij).mp
        ((specialLinearRestrictedRoot_self i).trans h.symm)).2
    · rw [restrictedRootSpace_specialLinearRestrictedRoot hij, Ne, span_singleton_eq_bot]
      intro h
      have := congrFun (congrFun (congrArg Subtype.val h) i) j
      simp at this

end TauCeti
