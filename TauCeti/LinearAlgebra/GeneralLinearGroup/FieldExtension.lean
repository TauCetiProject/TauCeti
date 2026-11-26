/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Bilinear
public import Mathlib.Algebra.Module.Equiv.Basic
public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# The normalizer of `Eˣ` in `GL_F(E)`

Let `E/F` be a field extension. The units of `E` act on the `F`-vector space `E` by left
multiplication, giving a subgroup `TauCeti.lmulUnitsRange F E` of the general linear group
`GL_F(E)`. When `E/F` is finite-dimensional, its normalizer consists of the `F`-linear
automorphisms `v ↦ c τ(v)` of `E` with `c ∈ Eˣ` and `τ` an `F`-algebra automorphism of `E`
(`TauCeti.mulGalois`), and the pair `(c, τ)` is unique, so the normalizer is in bijection with
`Eˣ × Gal(E/F)`.

An automorphism `φ` normalizing `Eˣ` satisfies `φ ∘ (x ·) = (τ x ·) ∘ φ` for a map `τ`, and
evaluating at `1` gives `φ x = τ(x) φ(1)`, so `τ = φ(1)⁻¹ φ` is multiplicative.

## Main declarations

* `TauCeti.lmulUnitsRange`: the units of `E` acting by multiplication, in `GL_F(E)`.
* `TauCeti.mulGalois`: the automorphism `v ↦ c τ(v)`.
* `TauCeti.mem_normalizer_lmulUnitsRange_iff`: the normalizer of `Eˣ` in `GL_F(E)` consists of
  the maps `v ↦ c τ(v)`.
* `TauCeti.normalizerLmulUnitsRangeEquiv`: the bijection with `Eˣ × Gal(E/F)`.
-/

public section

namespace TauCeti

variable {F : Type*} [Field F] {E : Type*} [Field E] [Algebra F E]

variable (F E) in
/-- The units of `E` acting on `E` by left multiplication, as a subgroup of `GL_F(E)`. -/
noncomputable def lmulUnitsRange : Subgroup (LinearMap.GeneralLinearGroup F E) :=
  (Units.map (Algebra.lmul F E : E →* Module.End F E)).range

/-- The members of `TauCeti.lmulUnitsRange F E` are the multiplications by units of `E`. -/
theorem mem_lmulUnitsRange_iff {u : LinearMap.GeneralLinearGroup F E} :
    u ∈ lmulUnitsRange F E ↔ ∃ x : Eˣ, Units.map (Algebra.lmul F E : E →* Module.End F E) x = u :=
  Iff.rfl

/-- Multiplication by a unit of `E` lies in `TauCeti.lmulUnitsRange F E`. -/
@[simp]
theorem units_map_lmul_mem_lmulUnitsRange (x : Eˣ) :
    Units.map (Algebra.lmul F E : E →* Module.End F E) x ∈ lmulUnitsRange F E :=
  ⟨x, rfl⟩

/-- The automorphism `v ↦ c τ(v)` of `E` as an element of `GL_F(E)`, for `c ∈ Eˣ` and
`τ ∈ Gal(E/F)`. -/
noncomputable def mulGalois (c : Eˣ) (τ : E ≃ₐ[F] E) : LinearMap.GeneralLinearGroup F E :=
  LinearMap.GeneralLinearGroup.ofLinearEquiv (τ.toLinearEquiv.trans (c.mulLeftLinearEquiv F E))

/-- The value of `v ↦ c τ(v)` at `v`. -/
@[simp]
theorem mulGalois_apply (c : Eˣ) (τ : E ≃ₐ[F] E) (v : E) :
    (mulGalois c τ : E →ₗ[F] E) v = c * τ v :=
  (rfl)

/-- `v ↦ c τ(v)` conjugates multiplication by `x` to multiplication by `τ x`. -/
theorem mulGalois_mul_lmul (c : Eˣ) (τ : E ≃ₐ[F] E) (x : E) :
    (mulGalois c τ : E →ₗ[F] E) * Algebra.lmul F E x =
      Algebra.lmul F E (τ x) * (mulGalois c τ : E →ₗ[F] E) := by
  ext v
  simp only [mul_apply_eq_comp, mulGalois_apply, Algebra.coe_lmul_eq_mul,
    LinearMap.mul_apply', map_mul]
  ring

/-- The inverse of `v ↦ c τ(v)` is `w ↦ τ⁻¹(c⁻¹) τ⁻¹(w)`. -/
theorem mulGalois_inv (c : Eˣ) (τ : E ≃ₐ[F] E) :
    (mulGalois c τ)⁻¹ = mulGalois (Units.map (τ.symm : E →* E) c⁻¹) τ.symm := by
  refine inv_eq_of_mul_eq_one_right (Units.ext (LinearMap.ext fun v ↦ ?_))
  simp

/-- Conjugation by `v ↦ c τ(v)` maps the units of `E` acting by multiplication into themselves. -/
theorem mulGalois_conj_mem_lmulUnitsRange (c : Eˣ) (τ : E ≃ₐ[F] E)
    {u : LinearMap.GeneralLinearGroup F E} (hu : u ∈ lmulUnitsRange F E) :
    mulGalois c τ * u * (mulGalois c τ)⁻¹ ∈ lmulUnitsRange F E := by
  obtain ⟨x, rfl⟩ := mem_lmulUnitsRange_iff.1 hu
  refine mem_lmulUnitsRange_iff.2 ⟨Units.map (τ : E →* E) x, Units.ext ?_⟩
  simp only [Units.val_mul, Units.coe_map, MonoidHom.coe_ofClass]
  rw [mulGalois_mul_lmul, mul_assoc, Units.mul_inv, mul_one]

/-- A linear map `φ` with `φ ∘ (x ·) = (τ x ·) ∘ φ` for some `τ` and every `x` satisfies
`φ v = τ(v) φ(1)`. -/
theorem apply_eq_of_mul_lmul {φ : E →ₗ[F] E} {τ : E → E}
    (h : ∀ x, φ * Algebra.lmul F E x = Algebra.lmul F E (τ x) * φ) (v : E) :
    φ v = τ v * φ 1 := by
  simpa [Algebra.coe_lmul_eq_mul, LinearMap.mul_apply'] using
    congrArg (fun ψ : E →ₗ[F] E ↦ ψ 1) (h v)

section FiniteDimensional

variable [FiniteDimensional F E]

/-- **The normalizer of `Eˣ` in `GL_F(E)`** consists of the maps `v ↦ c τ(v)` with `c ∈ Eˣ` and
`τ ∈ Gal(E/F)`. -/
theorem mem_normalizer_lmulUnitsRange_iff {φ : LinearMap.GeneralLinearGroup F E} :
    φ ∈ Subgroup.normalizer (lmulUnitsRange F E : Set (LinearMap.GeneralLinearGroup F E)) ↔
      ∃ c : Eˣ, ∃ τ : E ≃ₐ[F] E, φ = mulGalois c τ := by
  constructor
  · intro hφ
    -- conjugation by `φ` carries multiplication by `x` to multiplication by some `τ x`
    have hconj (x : E) : ∃ y : E, (φ : E →ₗ[F] E) * Algebra.lmul F E x =
        Algebra.lmul F E y * (φ : E →ₗ[F] E) := by
      obtain rfl | hx := eq_or_ne x 0
      · exact ⟨0, by simp⟩
      obtain ⟨y, hy⟩ := mem_lmulUnitsRange_iff.1 ((Subgroup.mem_normalizer_iff.1 hφ
        (Units.map (Algebra.lmul F E : E →* Module.End F E) (Units.mk0 x hx))).1
        (units_map_lmul_mem_lmulUnitsRange _))
      refine ⟨y, ?_⟩
      have := congrArg (fun u : LinearMap.GeneralLinearGroup F E ↦ (u : E →ₗ[F] E) *
        (φ : E →ₗ[F] E)) hy
      simp only [Units.val_mul, Units.coe_map, mul_assoc, Units.inv_mul, mul_one] at this
      exact this.symm
    choose τ hτ using hconj
    have hφ1 : (φ : E →ₗ[F] E) 1 ≠ 0 := fun h0 ↦ one_ne_zero
      ((LinearMap.GeneralLinearGroup.toLinearEquiv φ).injective (h0.trans (map_zero _).symm))
    have hφv := apply_eq_of_mul_lmul hτ
    have hτv (v : E) : τ v = (φ : E →ₗ[F] E) v * ((φ : E →ₗ[F] E) 1)⁻¹ := by
      rw [hφv v, mul_inv_cancel_right₀ hφ1]
    -- `τ` is an `F`-algebra endomorphism of `E`
    let τ' : E →ₐ[F] E :=
      { toFun := τ
        map_one' := by rw [hτv, mul_inv_cancel₀ hφ1]
        map_mul' := fun x y ↦ by
          have h := congrArg (fun ψ : E →ₗ[F] E ↦ ψ y) (hτ x)
          simp only [mul_apply_eq_comp, Algebra.coe_lmul_eq_mul,
            LinearMap.mul_apply'] at h
          rw [hτv (x * y), h, hτv y]
          ring
        map_zero' := by rw [hτv, map_zero, zero_mul]
        map_add' := fun x y ↦ by rw [hτv, hτv, hτv, map_add, add_mul]
        commutes' := fun a ↦ by
          rw [hτv, Algebra.algebraMap_eq_smul_one, map_smul, smul_mul_assoc,
            mul_inv_cancel₀ hφ1] }
    have hτ' (v : E) : τ' v = τ v := rfl
    refine ⟨Units.mk0 _ hφ1, AlgEquiv.ofBijective τ' (AlgHom.bijective τ'), ?_⟩
    ext v
    rw [mulGalois_apply, Units.val_mk0, AlgEquiv.ofBijective_apply, hτ', hφv v, mul_comm]
  · rintro ⟨c, τ, rfl⟩
    refine Subgroup.mem_normalizer_iff.2 fun u ↦ ?_
    refine ⟨mulGalois_conj_mem_lmulUnitsRange c τ, fun hu ↦ ?_⟩
    have h := mulGalois_conj_mem_lmulUnitsRange (Units.map (τ.symm : E →* E) c⁻¹) τ.symm hu
    rwa [← mulGalois_inv, inv_inv, ← mul_assoc, ← mul_assoc, inv_mul_cancel, one_mul,
      mul_assoc, inv_mul_cancel, mul_one] at h

omit [FiniteDimensional F E] in
/-- The factorization `v ↦ c τ(v)` is unique. -/
theorem mulGalois_injective :
    Function.Injective fun p : Eˣ × (E ≃ₐ[F] E) ↦ mulGalois p.1 p.2 := by
  rintro ⟨c, τ⟩ ⟨c', τ'⟩ h
  have h' (v : E) := congrArg (fun u : LinearMap.GeneralLinearGroup F E ↦ (u : E →ₗ[F] E) v) h
  simp only [mulGalois_apply] at h'
  have hc : c = c' := Units.ext (by simpa using h' 1)
  subst hc
  exact Prod.ext rfl (AlgEquiv.ext fun v ↦ mul_left_cancel₀ c.ne_zero (h' v))

/-- **The normalizer of `Eˣ` in `GL_F(E)` is in bijection with `Eˣ × Gal(E/F)`**, by
`(c, τ) ↦ (v ↦ c τ(v))`. -/
noncomputable def normalizerLmulUnitsRangeEquiv :
    Eˣ × (E ≃ₐ[F] E) ≃
      Subgroup.normalizer (lmulUnitsRange F E : Set (LinearMap.GeneralLinearGroup F E)) :=
  Equiv.ofBijective
    (fun p ↦ ⟨mulGalois p.1 p.2, mem_normalizer_lmulUnitsRange_iff.2 ⟨p.1, p.2, rfl⟩⟩)
    ⟨fun _ _ h ↦ mulGalois_injective (congrArg Subtype.val h), fun ⟨_, hφ⟩ ↦ by
      obtain ⟨c, τ, rfl⟩ := mem_normalizer_lmulUnitsRange_iff.1 hφ
      exact ⟨(c, τ), rfl⟩⟩

/-- The bijection sends `(c, τ)` to `v ↦ c τ(v)`. -/
@[simp]
theorem coe_normalizerLmulUnitsRangeEquiv_apply (p : Eˣ × (E ≃ₐ[F] E)) :
    (normalizerLmulUnitsRangeEquiv p : LinearMap.GeneralLinearGroup F E) = mulGalois p.1 p.2 :=
  (rfl)

end FiniteDimensional

end TauCeti
