/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.BilinearForm.Properties
public import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.Tactic.FieldSimp

/-!
# Coroots of a positive definite bilinear form

Let `B` be a positive definite bilinear form on a module `V` over a field `K`, and `t` a
finite-dimensional subspace. The restriction of `B` to `t` is nondegenerate
(`LinearMap.BilinForm.nondegenerate_restrict_of_posDef`), so every linear form `γ` on `t` is
represented by a vector `a ∈ t`, `B(a, H) = γ(H)` for `H ∈ t`
(`LinearMap.BilinForm.exists_forall_apply_eq`). The **coroot** of `γ` is

`γ^∨ = 2 a / B(a, a)`

(`LinearMap.BilinForm.coroot`, characterized by
`LinearMap.BilinForm.coroot_eq_of_forall_apply_eq`). It is the coroot of the reflection
`H ↦ H - γ(H) γ^∨` of `t` in the hyperplane `ker γ`, which is `B`-orthogonal when `B` is
symmetric: `γ(γ^∨) = 2` for `γ ≠ 0` (`LinearMap.BilinForm.apply_coroot`). This is the coroot of a
root in the invariant metric, as for the roots of a compact Lie algebra with respect to a maximal
abelian subalgebra.

* A nonzero form is recovered from its coroot `c` as `γ = (2 / B(c, c)) B(c, ·)`
  (`LinearMap.BilinForm.apply_eq_div_mul_of_ne_zero`), so the coroot map is injective on nonzero
  forms (`LinearMap.BilinForm.coroot_injOn`).
* For a symmetric `B`, the coroot of the reflection `δ - δ(γ^∨) γ` of `δ` is the reflection
  `δ^∨ - γ(δ^∨) γ^∨` of `δ^∨` (`LinearMap.BilinForm.coroot_sub_smul`). These are the compatibility
  conditions of roots and coroots in a root pairing (`RootPairing.mk'`).
-/

public section

open Module Set

namespace LinearMap.BilinForm

variable {K V : Type*} [Field K] [PartialOrder K] [AddCommGroup V] [Module K V]
  {B : LinearMap.BilinForm K V}

/-- A positive definite form restricts to a nondegenerate form on every subspace. -/
theorem nondegenerate_restrict_of_posDef (hB : B.toQuadraticMap.PosDef) (t : Submodule K V) :
    (B.restrict t).Nondegenerate :=
  ⟨fun a ha ↦ by
    by_contra h0
    exact (hB a (by simpa using h0)).ne' (by simpa using ha a),
  fun a ha ↦ by
    by_contra h0
    exact (hB a (by simpa using h0)).ne' (by simpa using ha a)⟩

variable (hB : B.toQuadraticMap.PosDef) {t : Submodule K V} [FiniteDimensional K t]

variable (B) in
/-- The **coroot** of a form `γ` on a subspace `t` for a positive definite form `B`: the vector
`γ^∨ = 2 a / γ(a) = 2 a / B(a, a)` of `t`, where `a ∈ t` represents `γ` through `B`, that is
`B(a, H) = γ(H)` for every `H ∈ t`. The coroot of `0` is `0`. -/
noncomputable def coroot (γ : Dual K t) : t :=
  (2 / γ (((B.restrict t).toDual (nondegenerate_restrict_of_posDef hB t)).symm γ)) •
    ((B.restrict t).toDual (nondegenerate_restrict_of_posDef hB t)).symm γ

include hB in
/-- Every form on `t` is represented by a vector of `t` through a positive definite form `B`. -/
theorem exists_forall_apply_eq (γ : Dual K t) : ∃ a : t, ∀ H : t, B a H = γ H :=
  ⟨_, apply_toDual_symm_apply (hB := nondegenerate_restrict_of_posDef hB t) γ⟩

/-- **The coroot of a represented form.** If `a ∈ t` represents `γ` through `B`, then
`γ^∨ = 2 a / B(a, a)`. -/
theorem coroot_eq_of_forall_apply_eq {γ : Dual K t} {a : t} (ha : ∀ H : t, B a H = γ H) :
    B.coroot hB γ = (2 / B a a) • a := by
  have h : ((B.restrict t).toDual (nondegenerate_restrict_of_posDef hB t)).symm γ = a :=
    (LinearEquiv.symm_apply_eq _).mpr (LinearMap.ext fun H ↦ (ha H).symm)
  rw [coroot, h, ← ha]

omit [FiniteDimensional K t] in
include hB in
/-- A vector representing a nonzero form through a positive definite form has nonzero length. -/
theorem apply_self_ne_zero_of_forall_apply_eq {γ : Dual K t} (hγ : γ ≠ 0) {a : t}
    (ha : ∀ H : t, B a H = γ H) : B a a ≠ 0 :=
  (hB _ fun h ↦ hγ (LinearMap.ext fun H ↦ by simp [← ha, h])).ne'

variable {hB}

/-- **`γ(γ^∨) = 2`** for a nonzero form `γ`. -/
theorem apply_coroot {γ : Dual K t} (hγ : γ ≠ 0) : γ (B.coroot hB γ) = 2 := by
  obtain ⟨a, ha⟩ := exists_forall_apply_eq hB γ
  rw [coroot_eq_of_forall_apply_eq hB ha, map_smul, ← ha, smul_eq_mul,
    div_mul_cancel₀ _ (apply_self_ne_zero_of_forall_apply_eq hB hγ ha)]

variable [NeZero (2 : K)]

/-- A nonzero form `γ` is recovered from its coroot `c = γ^∨` as `γ(H) = (2 / B(c, c)) B(c, H)`. -/
theorem apply_eq_div_mul_of_ne_zero {γ : Dual K t} (hγ : γ ≠ 0) (H : t) :
    γ H = 2 / B (B.coroot hB γ) (B.coroot hB γ) * B (B.coroot hB γ) H := by
  obtain ⟨a, ha⟩ := exists_forall_apply_eq hB γ
  have haa := apply_self_ne_zero_of_forall_apply_eq hB hγ ha
  simp only [coroot_eq_of_forall_apply_eq hB ha, Submodule.coe_smul, map_smul,
    LinearMap.smul_apply, smul_eq_mul, ← ha]
  field_simp

/-- **A nonzero form is determined by its coroot.** -/
theorem coroot_injOn : InjOn (B.coroot hB (t := t)) {γ | γ ≠ 0} := fun γ hγ δ hδ h ↦
  LinearMap.ext fun H ↦ by
    rw [apply_eq_div_mul_of_ne_zero (hB := hB) hγ, apply_eq_div_mul_of_ne_zero (hB := hB) hδ, h]

/-- **The coroots are compatible with the reflections.** For a symmetric positive definite form
`B` and nonzero forms `γ, δ` on `t`, the coroot of the reflection `δ - δ(γ^∨) γ` of `δ` is the
reflection `δ^∨ - γ(δ^∨) γ^∨` of the coroot: the reflection is an isometry of `B`. -/
theorem coroot_sub_smul (hBs : B.IsSymm) {γ δ : Dual K t} (hγ : γ ≠ 0) (hδ : δ ≠ 0) :
    B.coroot hB (δ - δ (B.coroot hB γ) • γ) =
      B.coroot hB δ - γ (B.coroot hB δ) • B.coroot hB γ := by
  obtain ⟨a, ha⟩ := exists_forall_apply_eq hB γ
  obtain ⟨b, hb⟩ := exists_forall_apply_eq hB δ
  have haa := apply_self_ne_zero_of_forall_apply_eq hB hγ ha
  have hbb := apply_self_ne_zero_of_forall_apply_eq hB hδ hb
  have hab : B b a = B a b := hBs.eq b a
  have hk : δ (B.coroot hB γ) = 2 * B a b / B a a := by
    rw [coroot_eq_of_forall_apply_eq hB ha, map_smul, ← hb, hab, smul_eq_mul]
    ring
  have hk' : γ (B.coroot hB δ) = 2 * B a b / B b b := by
    rw [coroot_eq_of_forall_apply_eq hB hb, map_smul, ← ha, smul_eq_mul]
    ring
  rw [hk, hk', coroot_eq_of_forall_apply_eq hB ha, coroot_eq_of_forall_apply_eq hB hb]
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
