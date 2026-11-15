/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.CliffordAlgebra.Conjugation
public import Mathlib.LinearAlgebra.ExteriorPower.WedgePairing
public import TauCeti.LinearAlgebra.ExteriorPower.Basic

/-!
# Semilinear functoriality of exterior algebras and exterior powers

Let `σ : A →+* B` be a homomorphism of commutative rings and `g : M →ₛₗ[σ] N` a `σ`-semilinear
map of modules. Viewing `ExteriorAlgebra B N` temporarily as an `A`-algebra through `σ`, the
composite `ι B ∘ g` is `A`-linear with square-zero values, so the universal property of the
exterior algebra extends `g` to a ring homomorphism
`ExteriorAlgebra.mapSemilinear g : ExteriorAlgebra A M →+* ExteriorAlgebra B N`.

This homomorphism carries `a • x` to `σ a • mapSemilinear g x`, intertwines the grade involutions,
and preserves each exterior power `⋀[A]^n M`, inducing the `σ`-semilinear map
`exteriorPower.mapSemilinear n g : ⋀[A]^n M →ₛₗ[σ] ⋀[B]^n N`. Both constructions recover
Mathlib's `ExteriorAlgebra.map` and `exteriorPower.map` when `σ = RingHom.id A` and compose
functorially along `RingHomCompTriple`.

## Main definitions

* `ExteriorAlgebra.mapSemilinear`: the ring homomorphism
  `ExteriorAlgebra A M →+* ExteriorAlgebra B N` induced by `g : M →ₛₗ[σ] N`.
* `exteriorPower.mapSemilinear`: the `σ`-semilinear map `⋀[A]^n M →ₛₗ[σ] ⋀[B]^n N` on the `n`-th
  exterior power.
-/

public section

namespace ExteriorAlgebra

variable {A B C M N P : Type*} [CommRing A] [CommRing B] [CommRing C]
  {σ : A →+* B} {τ : B →+* C} {ρ : A →+* C}
  [AddCommGroup M] [Module A M] [AddCommGroup N] [Module B N] [AddCommGroup P] [Module C P]

/-- **Semilinear functoriality of the exterior algebra.** A `σ`-semilinear map `g : M →ₛₗ[σ] N`
induces a ring homomorphism `ExteriorAlgebra A M →+* ExteriorAlgebra B N` sending `algebraMap a`
to `algebraMap (σ a)` and `ι A m` to `ι B (g m)`. -/
noncomputable def mapSemilinear (g : M →ₛₗ[σ] N) :
    ExteriorAlgebra A M →+* ExteriorAlgebra B N := by
  let : Algebra A (ExteriorAlgebra B N) :=
    ((algebraMap B (ExteriorAlgebra B N)).comp σ).toAlgebra' fun a x ↦ Algebra.commutes (σ a) x
  let g' : M →ₗ[A] ExteriorAlgebra B N :=
    { toFun := fun m ↦ ι B (g m)
      map_add' := fun m₁ m₂ ↦ by simp
      map_smul' := fun a m ↦ by
        simp only [g.map_smulₛₗ, LinearMap.map_smul, RingHom.id_apply]
        exact (Algebra.smul_def (σ a) (ι B (g m))).symm }
  exact (lift A ⟨g', fun m ↦ ι_sq_zero (g m)⟩).toRingHom

@[simp]
theorem mapSemilinear_algebraMap (g : M →ₛₗ[σ] N) (a : A) :
    mapSemilinear g (algebraMap A (ExteriorAlgebra A M) a) =
      algebraMap B (ExteriorAlgebra B N) (σ a) := by
  let : Algebra A (ExteriorAlgebra B N) :=
    ((algebraMap B (ExteriorAlgebra B N)).comp σ).toAlgebra' fun a x ↦ Algebra.commutes (σ a) x
  exact (lift A ⟨_, fun m ↦ ι_sq_zero (g m)⟩).commutes a

@[simp]
theorem mapSemilinear_ι (g : M →ₛₗ[σ] N) (m : M) :
    mapSemilinear g (ι A m) = ι B (g m) := by
  let : Algebra A (ExteriorAlgebra B N) :=
    ((algebraMap B (ExteriorAlgebra B N)).comp σ).toAlgebra' fun a x ↦ Algebra.commutes (σ a) x
  exact lift_ι_apply A _ (fun m ↦ ι_sq_zero (g m)) m

@[simp]
theorem mapSemilinear_smul (g : M →ₛₗ[σ] N) (a : A) (x : ExteriorAlgebra A M) :
    mapSemilinear g (a • x) = σ a • mapSemilinear g x := by
  rw [Algebra.smul_def, map_mul, mapSemilinear_algebraMap, Algebra.smul_def]

@[simp]
theorem mapSemilinear_ιMulti (g : M →ₛₗ[σ] N) {n : ℕ} (v : Fin n → M) :
    mapSemilinear g (ιMulti A n v) = ιMulti B n (g ∘ v) := by
  induction n with
  | zero => simp [ιMulti_zero_apply]
  | succ n ih =>
    simp [ιMulti_succ_apply, ih, Matrix.vecTail, Function.comp_def]

/-- Two ring homomorphisms out of `ExteriorAlgebra A M` that agree on `algebraMap A` and on
`ι A` are equal. -/
theorem ringHom_ext {S : Type*} [Semiring S] {f₁ f₂ : ExteriorAlgebra A M →+* S}
    (halg : ∀ a, f₁ (algebraMap A _ a) = f₂ (algebraMap A _ a))
    (hι : ∀ m, f₁ (ι A m) = f₂ (ι A m)) : f₁ = f₂ := by
  ext x
  induction x using ExteriorAlgebra.induction with
  | algebraMap a => exact halg a
  | ι m => exact hι m
  | mul x y hx hy => simp [hx, hy]
  | add x y hx hy => simp [hx, hy]

/-- For an `A`-linear map, `mapSemilinear` agrees with `ExteriorAlgebra.map`. -/
theorem mapSemilinear_eq_map {N' : Type*} [AddCommGroup N'] [Module A N'] (g : M →ₗ[A] N') :
    mapSemilinear g = (map g).toRingHom :=
  ringHom_ext (fun a ↦ by simp) (fun m ↦ by simp)

@[simp]
theorem mapSemilinear_id :
    mapSemilinear (LinearMap.id : M →ₗ[A] M) = RingHom.id (ExteriorAlgebra A M) :=
  ringHom_ext (fun a ↦ by simp) (fun m ↦ by simp)

theorem mapSemilinear_id_apply (x : ExteriorAlgebra A M) :
    mapSemilinear (LinearMap.id : M →ₗ[A] M) x = x :=
  RingHom.congr_fun mapSemilinear_id x

theorem mapSemilinear_comp [RingHomCompTriple σ τ ρ] (h : N →ₛₗ[τ] P) (g : M →ₛₗ[σ] N) :
    mapSemilinear (h.comp g) = (mapSemilinear h).comp (mapSemilinear g) :=
  ringHom_ext (fun a ↦ by simp [RingHomCompTriple.comp_apply]) (fun m ↦ by simp)

@[simp]
theorem mapSemilinear_comp_apply [RingHomCompTriple σ τ ρ] (h : N →ₛₗ[τ] P) (g : M →ₛₗ[σ] N)
    (x : ExteriorAlgebra A M) :
    mapSemilinear (h.comp g) x = mapSemilinear h (mapSemilinear g x) :=
  RingHom.congr_fun (mapSemilinear_comp h g) x

/-- `mapSemilinear` commutes with the grade involution on the exterior algebra. -/
@[simp]
theorem mapSemilinear_involute (g : M →ₛₗ[σ] N) (x : ExteriorAlgebra A M) :
    mapSemilinear g (CliffordAlgebra.involute (Q := (0 : QuadraticForm A M)) x) =
      CliffordAlgebra.involute (Q := (0 : QuadraticForm B N)) (mapSemilinear g x) := by
  induction x using CliffordAlgebra.induction with
  | algebraMap a => simp
  | ι m => simp
  | mul x y hx hy => simp [hx, hy]
  | add x y hx hy => simp [hx, hy]

/-- `mapSemilinear` carries the `n`-th exterior power into the `n`-th exterior power. -/
theorem mapSemilinear_mem_exteriorPower (g : M →ₛₗ[σ] N) {n : ℕ} {x : ExteriorAlgebra A M}
    (hx : x ∈ ⋀[A]^n M) : mapSemilinear g x ∈ ⋀[B]^n N := by
  induction hx using Submodule.pow_induction_on_left' with
  | algebraMap a =>
    rw [mapSemilinear_algebraMap, ExteriorAlgebra.exteriorPower, pow_zero]
    exact Submodule.algebraMap_mem _
  | add x y i _ _ ihx ihy =>
    rw [map_add]
    exact add_mem ihx ihy
  | mem_mul u hu i x _ ih =>
    obtain ⟨m, rfl⟩ := hu
    rw [map_mul, mapSemilinear_ι, ExteriorAlgebra.exteriorPower, pow_succ']
    exact Submodule.mul_mem_mul (LinearMap.mem_range_self _ (g m)) ih

end ExteriorAlgebra

namespace exteriorPower

variable {A B C M N P : Type*} [CommRing A] [CommRing B] [CommRing C]
  {σ : A →+* B} {τ : B →+* C} {ρ : A →+* C}
  [AddCommGroup M] [Module A M] [AddCommGroup N] [Module B N] [AddCommGroup P] [Module C P]

/-- **Semilinear functoriality of exterior powers.** A `σ`-semilinear map `g : M →ₛₗ[σ] N`
induces a `σ`-semilinear map `⋀[A]^n M →ₛₗ[σ] ⋀[B]^n N` sending `v₀ ∧ ⋯ ∧ vₙ₋₁` to
`g v₀ ∧ ⋯ ∧ g vₙ₋₁`. -/
noncomputable def mapSemilinear (n : ℕ) (g : M →ₛₗ[σ] N) : ⋀[A]^n M →ₛₗ[σ] ⋀[B]^n N where
  toFun x := ⟨ExteriorAlgebra.mapSemilinear g x.1,
    ExteriorAlgebra.mapSemilinear_mem_exteriorPower g x.2⟩
  map_add' x y := Subtype.ext (map_add (ExteriorAlgebra.mapSemilinear g) x.1 y.1)
  map_smul' a x := Subtype.ext (ExteriorAlgebra.mapSemilinear_smul g a x.1)

@[simp]
theorem coe_mapSemilinear_apply (n : ℕ) (g : M →ₛₗ[σ] N) (x : ⋀[A]^n M) :
    (mapSemilinear n g x : ExteriorAlgebra B N) = ExteriorAlgebra.mapSemilinear g x.1 :=
  (rfl)

@[simp]
theorem mapSemilinear_apply_ιMulti (n : ℕ) (g : M →ₛₗ[σ] N) (v : Fin n → M) :
    mapSemilinear n g (ιMulti A n v) = ιMulti B n (g ∘ v) :=
  Subtype.ext (ExteriorAlgebra.mapSemilinear_ιMulti g v)

theorem mapSemilinear_eq_map {N' : Type*} [AddCommGroup N'] [Module A N'] (n : ℕ)
    (g : M →ₗ[A] N') : mapSemilinear n g = map n g := by
  refine linearMap_ext (AlternatingMap.ext fun v ↦ ?_)
  simp [Function.comp_def]

@[simp]
theorem mapSemilinear_id (n : ℕ) :
    mapSemilinear n (LinearMap.id : M →ₗ[A] M) = LinearMap.id :=
  (mapSemilinear_eq_map n (LinearMap.id : M →ₗ[A] M)).trans map_id

theorem mapSemilinear_id_apply (n : ℕ) (x : ⋀[A]^n M) :
    mapSemilinear n (LinearMap.id : M →ₗ[A] M) x = x :=
  DFunLike.congr_fun (mapSemilinear_id n) x

theorem mapSemilinear_comp [RingHomCompTriple σ τ ρ] (n : ℕ) (h : N →ₛₗ[τ] P) (g : M →ₛₗ[σ] N) :
    mapSemilinear n (h.comp g) = (mapSemilinear n h).comp (mapSemilinear n g) := by
  ext x : 1
  exact Subtype.ext (ExteriorAlgebra.mapSemilinear_comp_apply h g x.1)

@[simp]
theorem mapSemilinear_comp_apply [RingHomCompTriple σ τ ρ] (n : ℕ) (h : N →ₛₗ[τ] P)
    (g : M →ₛₗ[σ] N) (x : ⋀[A]^n M) :
    mapSemilinear n (h.comp g) x = mapSemilinear n h (mapSemilinear n g x) :=
  DFunLike.congr_fun (mapSemilinear_comp n h g) x

@[simp]
theorem mapSemilinear_apply_symm_apply {σ' : B →+* A} [RingHomInvPair σ σ'] [RingHomInvPair σ' σ]
    (n : ℕ) (e : M ≃ₛₗ[σ] N) (y : ⋀[B]^n N) :
    mapSemilinear n e.toLinearMap (mapSemilinear n e.symm.toLinearMap y) = y := by
  rw [← mapSemilinear_comp_apply, e.comp_symm, mapSemilinear_id_apply]

@[simp]
theorem mapSemilinear_symm_apply_apply {σ' : B →+* A} [RingHomInvPair σ σ'] [RingHomInvPair σ' σ]
    (n : ℕ) (e : M ≃ₛₗ[σ] N) (x : ⋀[A]^n M) :
    mapSemilinear n e.symm.toLinearMap (mapSemilinear n e.toLinearMap x) = x :=
  mapSemilinear_apply_symm_apply n e.symm x

@[simp]
theorem mapSemilinear_zeroEquiv_symm (g : M →ₛₗ[σ] N) (a : A) :
    mapSemilinear 0 g ((zeroEquiv A M).symm a) = (zeroEquiv B N).symm (σ a) := by
  apply Subtype.ext
  simp [zeroEquiv_symm_apply, ExteriorAlgebra.ιMulti_zero_apply]

@[simp]
theorem zeroEquiv_mapSemilinear (g : M →ₛₗ[σ] N) (x : ⋀[A]^0 M) :
    zeroEquiv B N (mapSemilinear 0 g x) = σ (zeroEquiv A M x) := by
  conv_lhs => rw [← (zeroEquiv A M).symm_apply_apply x, mapSemilinear_zeroEquiv_symm,
    LinearEquiv.apply_symm_apply]

@[simp]
theorem mapSemilinear_oneEquiv_symm (g : M →ₛₗ[σ] N) (m : M) :
    mapSemilinear 1 g ((oneEquiv A M).symm m) = (oneEquiv B N).symm (g m) := by
  simp [oneEquiv_symm_apply, Function.comp_def]

@[simp]
theorem oneEquiv_mapSemilinear (g : M →ₛₗ[σ] N) (x : ⋀[A]^1 M) :
    oneEquiv B N (mapSemilinear 1 g x) = g (oneEquiv A M x) := by
  conv_lhs => rw [← (oneEquiv A M).symm_apply_apply x, mapSemilinear_oneEquiv_symm,
    LinearEquiv.apply_symm_apply]

/-- `mapSemilinear` preserves the wedge product of exterior powers. -/
theorem mapSemilinear_wedge (p q : ℕ) (g : M →ₛₗ[σ] N) (x : ⋀[A]^p M) (y : ⋀[A]^q M) :
    mapSemilinear (p + q) g (wedge A M p q x y) =
      wedge B N p q (mapSemilinear p g x) (mapSemilinear q g y) :=
  Subtype.ext (map_mul (ExteriorAlgebra.mapSemilinear g) x.1 y.1)

/-- `mapSemilinear` intertwines left exterior multiplication by a vector. -/
theorem mapSemilinear_wedgeLeft (n : ℕ) (g : M →ₛₗ[σ] N) (m : M) (x : ⋀[A]^n M) :
    mapSemilinear (n + 1) g (TauCeti.ExteriorAlgebra.wedgeLeft m n x) =
      TauCeti.ExteriorAlgebra.wedgeLeft (g m) n (mapSemilinear n g x) :=
  Subtype.ext (by simp)

/-- A surjective `σ`-semilinear map over a surjective ring homomorphism induces a surjective map
on every exterior power. -/
theorem mapSemilinear_surjective {n : ℕ} {g : M →ₛₗ[σ] N} (hσ : Function.Surjective σ)
    (hg : Function.Surjective g) : Function.Surjective (mapSemilinear n g) := by
  intro y
  have hy : y ∈ Submodule.span B (Set.range (ιMulti B n)) :=
    ιMulti_span B n N ▸ Submodule.mem_top
  induction hy using Submodule.span_induction with
  | mem _ hv =>
    obtain ⟨v, rfl⟩ := hv
    choose u hu using fun i ↦ hg (v i)
    exact ⟨ιMulti A n u, by simp [Function.comp_def, hu]⟩
  | zero => exact ⟨0, map_zero _⟩
  | add _ _ _ _ ih₁ ih₂ =>
    obtain ⟨x₁, rfl⟩ := ih₁
    obtain ⟨x₂, rfl⟩ := ih₂
    exact ⟨x₁ + x₂, map_add _ x₁ x₂⟩
  | smul b _ _ ih =>
    obtain ⟨a, rfl⟩ := hσ b
    obtain ⟨x, rfl⟩ := ih
    exact ⟨a • x, (mapSemilinear n g).map_smulₛₗ a x⟩

end exteriorPower
