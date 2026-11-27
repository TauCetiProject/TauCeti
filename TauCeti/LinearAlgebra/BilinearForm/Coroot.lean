/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.BilinearForm.Properties
public import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import TauCeti.LinearAlgebra.BilinearForm.Basic

/-!
# Coroots of a bilinear form on an anisotropic subspace

Let `B` be a bilinear form on a module `V` over a field `K` and `t` a finite-dimensional subspace
on which `B` is anisotropic, for instance a subspace on which `B` is positive definite over `ℝ`.
The restriction of `B` to `t` is nondegenerate (`LinearMap.BilinForm.nondegenerate_of_anisotropic`),
so every linear form `γ` on `t` is represented by a vector `a ∈ t`, `B(a, H) = γ(H)` for `H ∈ t`
(`LinearMap.BilinForm.exists_forall_apply_eq`). The **coroot** of `γ` is

`γ^∨ = 2 a / B(a, a)`

(`LinearMap.BilinForm.coroot`, characterized by
`LinearMap.BilinForm.coroot_eq_of_forall_apply_eq`). It is the coroot of the reflection
`H ↦ H - γ(H) γ^∨` of `t` in the hyperplane `ker γ`, which is `B`-orthogonal when `B` is
symmetric: `γ(γ^∨) = 2` for `γ ≠ 0` (`LinearMap.BilinForm.apply_coroot`). This is the coroot of a
root in the invariant metric, as for the roots of a compact Lie algebra with respect to a maximal
abelian subalgebra.

* The pairing of a form `δ` with `γ^∨` is `δ(γ^∨) = 2 δ(a) / B(a, a)`
  (`LinearMap.BilinForm.apply_coroot_eq_of_forall_apply_eq`).
* The coroot of `c γ` is `c⁻¹ γ^∨` (`LinearMap.BilinForm.coroot_smul`), in particular the coroot of
  `-γ` is `-γ^∨` (`LinearMap.BilinForm.coroot_neg`), and the coroot of a nonzero form is nonzero
  (`LinearMap.BilinForm.coroot_ne_zero`).
* The reflection `δ - δ(γ^∨) γ` of a nonzero form `δ` in a nonzero form `γ` is nonzero
  (`LinearMap.BilinForm.sub_apply_coroot_smul_ne_zero`).
* A nonzero form is recovered from its coroot `c` as `γ = (2 / B(c, c)) B(c, ·)`
  (`LinearMap.BilinForm.apply_eq_div_mul_coroot`), so the coroot map is injective on nonzero
  forms (`LinearMap.BilinForm.coroot_injOn`).
* For a symmetric `B`, the coroot of the reflection `δ - δ(γ^∨) γ` of `δ` is the reflection
  `δ^∨ - γ(δ^∨) γ^∨` of `δ^∨` (`LinearMap.BilinForm.coroot_sub_smul`). These are the compatibility
  conditions of roots and coroots in a root pairing (`RootPairing.mk'`).
-/

public section

open Module Set

namespace LinearMap.BilinForm

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {B : LinearMap.BilinForm K V}
  {t : Submodule K V} (hB : (B.restrict t).toQuadraticMap.Anisotropic) [FiniteDimensional K t]

variable (B) in
/-- The **coroot** of a form `γ` on a subspace `t` on which `B` is anisotropic: the vector
`γ^∨ = 2 a / γ(a) = 2 a / B(a, a)` of `t`, where `a ∈ t` represents `γ` through `B`, that is
`B(a, H) = γ(H)` for every `H ∈ t`. The coroot of `0` is `0`. -/
noncomputable def coroot (γ : Dual K t) : t :=
  (2 / γ (((B.restrict t).toDual (nondegenerate_of_anisotropic _ hB)).symm γ)) •
    ((B.restrict t).toDual (nondegenerate_of_anisotropic _ hB)).symm γ

include hB in
/-- Every form on `t` is represented by a vector of `t` through `B`, when `B` is anisotropic on
`t`. -/
theorem exists_forall_apply_eq (γ : Dual K t) : ∃ a : t, ∀ H : t, B a H = γ H :=
  ⟨_, apply_toDual_symm_apply (hB := nondegenerate_of_anisotropic _ hB) γ⟩

/-- **The coroot of a represented form.** If `a ∈ t` represents `γ` through `B`, then
`γ^∨ = 2 a / B(a, a)`. -/
theorem coroot_eq_of_forall_apply_eq {γ : Dual K t} {a : t} (ha : ∀ H : t, B a H = γ H) :
    B.coroot hB γ = (2 / B a a) • a := by
  have h : ((B.restrict t).toDual (nondegenerate_of_anisotropic _ hB)).symm γ = a :=
    (LinearEquiv.symm_apply_eq _).mpr (LinearMap.ext fun H ↦ (ha H).symm)
  rw [coroot, h, ← ha]

/-- The coroot of the zero form is zero. -/
@[simp]
theorem coroot_zero : B.coroot hB (0 : Dual K t) = 0 := by
  simp [coroot]

/-- **The pairing of a form with a coroot.** If `a ∈ t` represents `γ` through `B`, then
`δ(γ^∨) = 2 δ(a) / B(a, a)` for every form `δ` on `t`. -/
theorem apply_coroot_eq_of_forall_apply_eq {γ : Dual K t} {a : t} (ha : ∀ H : t, B a H = γ H)
    (δ : Dual K t) : δ (B.coroot hB γ) = 2 * δ a / B a a := by
  rw [coroot_eq_of_forall_apply_eq hB ha, map_smul, smul_eq_mul, div_mul_eq_mul_div]

omit [FiniteDimensional K t] in
include hB in
/-- A vector of `t` representing a nonzero form through `B`, anisotropic on `t`, has nonzero
length. -/
theorem apply_self_ne_zero_of_forall_apply_eq {γ : Dual K t} (hγ : γ ≠ 0) {a : t}
    (ha : ∀ H : t, B a H = γ H) : B a a ≠ 0 := fun h ↦
  hγ (LinearMap.ext fun H ↦ by simp [← ha, hB a h])

variable {hB}

/-- **`γ(γ^∨) = 2`** for a nonzero form `γ`. -/
@[simp]
theorem apply_coroot {γ : Dual K t} (hγ : γ ≠ 0) : γ (B.coroot hB γ) = 2 := by
  obtain ⟨a, ha⟩ := exists_forall_apply_eq hB γ
  rw [apply_coroot_eq_of_forall_apply_eq hB ha, ← ha,
    mul_div_cancel_right₀ _ (apply_self_ne_zero_of_forall_apply_eq hB hγ ha)]

/-- **The reflection of a nonzero form is nonzero.** For `γ ≠ 0` and `δ ≠ 0`, the reflection
`δ - δ(γ^∨) γ` is nonzero: evaluated at `γ^∨` it is `-δ(γ^∨)`, so if it vanished then
`δ(γ^∨) = 0` and `δ` would be `0`. -/
theorem sub_apply_coroot_smul_ne_zero {γ δ : Dual K t} (hγ : γ ≠ 0) (hδ : δ ≠ 0) :
    δ - δ (B.coroot hB γ) • γ ≠ 0 := by
  intro h
  have hc : δ (B.coroot hB γ) = 0 := by
    have := LinearMap.congr_fun h (B.coroot hB γ)
    rw [LinearMap.sub_apply, LinearMap.smul_apply, apply_coroot hγ, smul_eq_mul,
      LinearMap.zero_apply] at this
    linear_combination -this
  exact hδ (by rwa [hc, zero_smul, sub_zero] at h)

/-- The coroot of `c γ` is `c⁻¹ γ^∨`. -/
@[simp]
theorem coroot_smul (c : K) (γ : Dual K t) : B.coroot hB (c • γ) = c⁻¹ • B.coroot hB γ := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  rcases eq_or_ne γ 0 with rfl | hγ
  · simp
  obtain ⟨a, ha⟩ := exists_forall_apply_eq hB γ
  have haa := apply_self_ne_zero_of_forall_apply_eq hB hγ ha
  have hca (H : t) : B ((c • a : t) : V) H = (c • γ) H := by
    simp [← ha]
  rw [coroot_eq_of_forall_apply_eq hB hca, coroot_eq_of_forall_apply_eq hB ha, smul_smul,
    smul_smul]
  congr 1
  simp only [Submodule.coe_smul, map_smul, LinearMap.smul_apply, smul_eq_mul]
  field_simp

/-- The coroot of `-γ` is `-γ^∨`. -/
@[simp]
theorem coroot_neg (γ : Dual K t) : B.coroot hB (-γ) = -B.coroot hB γ := by
  rw [← neg_one_smul K γ, coroot_smul, inv_neg, inv_one, neg_one_smul]

variable [NeZero (2 : K)]

/-- The coroot of a nonzero form is nonzero. -/
theorem coroot_ne_zero {γ : Dual K t} (hγ : γ ≠ 0) : B.coroot hB γ ≠ 0 := fun h ↦
  two_ne_zero (α := K) <| by rw [← apply_coroot (hB := hB) hγ, h, map_zero]

/-- A nonzero form `γ` is recovered from its coroot `c = γ^∨` as `γ(H) = (2 / B(c, c)) B(c, H)`. -/
theorem apply_eq_div_mul_coroot {γ : Dual K t} (hγ : γ ≠ 0) (H : t) :
    γ H = 2 / B (B.coroot hB γ) (B.coroot hB γ) * B (B.coroot hB γ) H := by
  obtain ⟨a, ha⟩ := exists_forall_apply_eq hB γ
  have haa := apply_self_ne_zero_of_forall_apply_eq hB hγ ha
  simp only [coroot_eq_of_forall_apply_eq hB ha, Submodule.coe_smul, map_smul,
    LinearMap.smul_apply, smul_eq_mul, ← ha]
  field_simp

/-- **A nonzero form is determined by its coroot.** -/
theorem coroot_injOn : InjOn (B.coroot hB (t := t)) {γ | γ ≠ 0} := fun γ hγ δ hδ h ↦
  LinearMap.ext fun H ↦ by
    rw [apply_eq_div_mul_coroot (hB := hB) hγ, apply_eq_div_mul_coroot (hB := hB) hδ, h]

/-- **The coroots are compatible with the reflections.** For a symmetric form `B`, anisotropic on
`t`, and forms `γ, δ` on `t`, the coroot of the reflection `δ - δ(γ^∨) γ` of `δ` is the reflection
`δ^∨ - γ(δ^∨) γ^∨` of the coroot: the reflection is an isometry of `B`. -/
theorem coroot_sub_smul (hBs : B.IsSymm) (γ δ : Dual K t) :
    B.coroot hB (δ - δ (B.coroot hB γ) • γ) =
      B.coroot hB δ - γ (B.coroot hB δ) • B.coroot hB γ := by
  rcases eq_or_ne γ 0 with rfl | hγ
  · simp
  rcases eq_or_ne δ 0 with rfl | hδ
  · simp
  obtain ⟨a, ha⟩ := exists_forall_apply_eq hB γ
  obtain ⟨b, hb⟩ := exists_forall_apply_eq hB δ
  have haa := apply_self_ne_zero_of_forall_apply_eq hB hγ ha
  have hbb := apply_self_ne_zero_of_forall_apply_eq hB hδ hb
  have hab : B b a = B a b := hBs.eq b a
  rw [apply_coroot_eq_of_forall_apply_eq hB ha, apply_coroot_eq_of_forall_apply_eq hB hb, ← ha,
    ← hb, hab, coroot_eq_of_forall_apply_eq hB ha, coroot_eq_of_forall_apply_eq hB hb]
  -- `b - k a` represents the reflection and has the length of `b`.
  have hrep (H : t) : B ((b - (2 * B a b / B a a) • a : t) : V) H =
      (δ - (2 * B a b / B a a) • γ) H := by
    simp [← ha, ← hb]
  have hlen : B ((b - (2 * B a b / B a a) • a : t) : V) ((b - (2 * B a b / B a a) • a : t) : V) =
      B b b := by
    simp only [Submodule.coe_sub, Submodule.coe_smul, map_sub, map_smul, LinearMap.sub_apply,
      LinearMap.smul_apply, smul_eq_mul, hab]
    field_simp
    ring
  rw [coroot_eq_of_forall_apply_eq hB hrep, hlen, smul_sub, smul_smul, smul_smul]
  congr 2
  field_simp

end LinearMap.BilinForm
