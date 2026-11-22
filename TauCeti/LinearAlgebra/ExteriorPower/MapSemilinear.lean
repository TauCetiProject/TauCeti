/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.ExteriorPower.WedgePairing
public import TauCeti.LinearAlgebra.ExteriorAlgebra.MapSemilinear
public import TauCeti.LinearAlgebra.ExteriorPower.Basic

/-!
# Semilinear functoriality of exterior powers

A `σ`-semilinear map `g : M →ₛₗ[σ] N` along `σ : A →+* B` preserves the exterior-power grading
under `ExteriorAlgebra.mapSemilinear g` and restricts to `σ`-semilinear maps
`exteriorPower.mapSemilinear n g : ⋀[A]^n M →ₛₗ[σ] ⋀[B]^n N`, compatible with `ιMulti`, `wedge`,
`wedgeLeft`, `zeroEquiv`, `oneEquiv`, and surjectivity.
-/

public section

namespace ExteriorAlgebra

variable {A B M N : Type*} [CommRing A] [CommRing B] {σ : A →+* B}
  [AddCommGroup M] [Module A M] [AddCommGroup N] [Module B N]

/-- `mapSemilinear` carries the `n`-th exterior power into the `n`-th exterior power. -/
theorem mapSemilinear_mem_exteriorPower (g : M →ₛₗ[σ] N) {n : ℕ} {x : ExteriorAlgebra A M}
    (hx : x ∈ ⋀[A]^n M) : mapSemilinear g x ∈ ⋀[B]^n N := by
  induction hx using Submodule.pow_induction_on_left' with
  | algebraMap a =>
    rw [mapSemilinear_algebraMap, ExteriorAlgebra.exteriorPower, pow_zero]
    exact Submodule.algebraMap_mem _
  | add _ _ _ _ _ ihx ihy => exact map_add (mapSemilinear g) .. ▸ add_mem ihx ihy
  | mem_mul _ hu _ _ _ ih =>
    obtain ⟨m, rfl⟩ := hu; rw [map_mul, mapSemilinear_ι, ExteriorAlgebra.exteriorPower, pow_succ']
    exact Submodule.mul_mem_mul (LinearMap.mem_range_self _ (g m)) ih

end ExteriorAlgebra

namespace exteriorPower

variable {A B C M N P : Type*} [CommRing A] [CommRing B] [CommRing C]
  {σ : A →+* B} {τ : B →+* C} {ρ : A →+* C}
  [AddCommGroup M] [Module A M] [AddCommGroup N] [Module B N] [AddCommGroup P] [Module C P]

/-- **Semilinear functoriality of exterior powers.** A `σ`-semilinear map `g : M →ₛₗ[σ] N`
induces `⋀[A]^n M →ₛₗ[σ] ⋀[B]^n N` sending `v₀ ∧ ⋯ ∧ vₙ₋₁` to `g v₀ ∧ ⋯ ∧ g vₙ₋₁`. -/
noncomputable def mapSemilinear (n : ℕ) (g : M →ₛₗ[σ] N) : ⋀[A]^n M →ₛₗ[σ] ⋀[B]^n N where
  toFun x := ⟨ExteriorAlgebra.mapSemilinear g x.val,
    ExteriorAlgebra.mapSemilinear_mem_exteriorPower g x.property⟩
  map_add' x y := Subtype.ext (map_add (ExteriorAlgebra.mapSemilinear g) x.val y.val)
  map_smul' a x := Subtype.ext (ExteriorAlgebra.mapSemilinear_smul g a x.val)

@[simp] theorem coe_mapSemilinear_apply (n : ℕ) (g : M →ₛₗ[σ] N) (x : ⋀[A]^n M) :
    (mapSemilinear n g x : ExteriorAlgebra B N) = ExteriorAlgebra.mapSemilinear g x.val := (rfl)
@[simp] theorem mapSemilinear_apply_ιMulti (n : ℕ) (g : M →ₛₗ[σ] N) (v : Fin n → M) :
    mapSemilinear n g (ιMulti A n v) = ιMulti B n (g ∘ v) :=
  Subtype.ext (ExteriorAlgebra.mapSemilinear_ιMulti g v)
theorem mapSemilinear_eq_map {N' : Type*} [AddCommGroup N'] [Module A N'] (n : ℕ)
    (g : M →ₗ[A] N') : mapSemilinear n g = map n g :=
  linearMap_ext (AlternatingMap.ext fun _ ↦ by simp [Function.comp_def])
@[simp] theorem mapSemilinear_id (n : ℕ) :
    mapSemilinear n (LinearMap.id : M →ₗ[A] M) = LinearMap.id :=
  (mapSemilinear_eq_map n LinearMap.id).trans map_id
theorem mapSemilinear_id_apply (n : ℕ) (x : ⋀[A]^n M) :
    mapSemilinear n (LinearMap.id : M →ₗ[A] M) x = x := DFunLike.congr_fun (mapSemilinear_id n) x
theorem mapSemilinear_comp [RingHomCompTriple σ τ ρ] (n : ℕ) (h : N →ₛₗ[τ] P) (g : M →ₛₗ[σ] N) :
    mapSemilinear n (h.comp g) = (mapSemilinear n h).comp (mapSemilinear n g) :=
  LinearMap.ext fun x ↦ Subtype.ext (ExteriorAlgebra.mapSemilinear_comp_apply h g x.val)
@[simp] theorem mapSemilinear_comp_apply [RingHomCompTriple σ τ ρ] (n : ℕ) (h : N →ₛₗ[τ] P)
    (g : M →ₛₗ[σ] N) (x : ⋀[A]^n M) :
    mapSemilinear n (h.comp g) x = mapSemilinear n h (mapSemilinear n g x) :=
  DFunLike.congr_fun (mapSemilinear_comp n h g) x
@[simp] theorem mapSemilinear_apply_symm_apply {σ' : B →+* A} [RingHomInvPair σ σ']
    [RingHomInvPair σ' σ] (n : ℕ) (e : M ≃ₛₗ[σ] N) (y : ⋀[B]^n N) :
    mapSemilinear n e.toLinearMap (mapSemilinear n e.symm.toLinearMap y) = y := by
  rw [← mapSemilinear_comp_apply, e.comp_symm, mapSemilinear_id_apply]
@[simp] theorem mapSemilinear_symm_apply_apply {σ' : B →+* A} [RingHomInvPair σ σ']
    [RingHomInvPair σ' σ] (n : ℕ) (e : M ≃ₛₗ[σ] N) (x : ⋀[A]^n M) :
    mapSemilinear n e.symm.toLinearMap (mapSemilinear n e.toLinearMap x) = x :=
  mapSemilinear_apply_symm_apply n e.symm x
@[simp] theorem mapSemilinear_zeroEquiv_symm (g : M →ₛₗ[σ] N) (a : A) :
    mapSemilinear 0 g ((zeroEquiv A M).symm a) = (zeroEquiv B N).symm (σ a) :=
  Subtype.ext <| by simp [zeroEquiv_symm_apply, ExteriorAlgebra.ιMulti_zero_apply]
@[simp] theorem zeroEquiv_mapSemilinear (g : M →ₛₗ[σ] N) (x : ⋀[A]^0 M) :
    zeroEquiv B N (mapSemilinear 0 g x) = σ (zeroEquiv A M x) := by
  conv_lhs => rw [← (zeroEquiv A M).symm_apply_apply x, mapSemilinear_zeroEquiv_symm,
    LinearEquiv.apply_symm_apply]
@[simp] theorem mapSemilinear_oneEquiv_symm (g : M →ₛₗ[σ] N) (m : M) :
    mapSemilinear 1 g ((oneEquiv A M).symm m) = (oneEquiv B N).symm (g m) := by
  simp [oneEquiv_symm_apply, Function.comp_def]
@[simp] theorem oneEquiv_mapSemilinear (g : M →ₛₗ[σ] N) (x : ⋀[A]^1 M) :
    oneEquiv B N (mapSemilinear 1 g x) = g (oneEquiv A M x) := by
  conv_lhs => rw [← (oneEquiv A M).symm_apply_apply x, mapSemilinear_oneEquiv_symm,
    LinearEquiv.apply_symm_apply]
/-- `mapSemilinear` preserves the wedge product of exterior powers. -/
theorem mapSemilinear_wedge (p q : ℕ) (g : M →ₛₗ[σ] N) (x : ⋀[A]^p M) (y : ⋀[A]^q M) :
    mapSemilinear (p + q) g (wedge A M p q x y) =
      wedge B N p q (mapSemilinear p g x) (mapSemilinear q g y) :=
  Subtype.ext (map_mul (ExteriorAlgebra.mapSemilinear g) x.val y.val)
/-- `mapSemilinear` intertwines left exterior multiplication by a vector. -/
theorem mapSemilinear_wedgeLeft (n : ℕ) (g : M →ₛₗ[σ] N) (m : M) (x : ⋀[A]^n M) :
    mapSemilinear (n + 1) g (TauCeti.ExteriorAlgebra.wedgeLeft m n x) =
      TauCeti.ExteriorAlgebra.wedgeLeft (g m) n (mapSemilinear n g x) := Subtype.ext (by simp)

/-- A surjective `σ`-semilinear map over a surjective ring homomorphism induces a surjective map
on every exterior power. -/
theorem mapSemilinear_surjective {n : ℕ} {g : M →ₛₗ[σ] N} (hσ : Function.Surjective σ)
    (hg : Function.Surjective g) : Function.Surjective (mapSemilinear n g) := by
  have : RingHomSurjective σ := ⟨hσ⟩
  have h : Submodule.span B (Set.range (ιMulti B n)) ≤ LinearMap.range (mapSemilinear n g) := by
    rw [Submodule.span_le]; rintro _ ⟨v, rfl⟩
    choose u hu using fun i ↦ hg (v i); exact ⟨ιMulti A n u, by simp [Function.comp_def, hu]⟩
  exact fun y ↦ h (ιMulti_span B n N ▸ Submodule.mem_top)

end exteriorPower
