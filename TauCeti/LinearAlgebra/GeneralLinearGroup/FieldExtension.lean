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
import Mathlib.Tactic.Ring

/-!
# The normalizer of `Eˣ` in `GL_F(E)`

Let `E/F` be a field extension. The units of `E` act on the `F`-vector space `E` by left
multiplication, giving a subgroup `TauCeti.lmulUnitsRange F E` of the general linear group
`GL_F(E)`. Its normalizer consists of the `F`-linear automorphisms `v ↦ c τ(v)` of `E` with
`c ∈ Eˣ` and `τ` an `F`-algebra automorphism of `E` (`TauCeti.mulGalois`), and the pair `(c, τ)`
is unique, so the normalizer is in bijection with `Eˣ × Gal(E/F)`.

An automorphism `φ` normalizing `Eˣ` satisfies `φ ∘ (x ·) = (τ x ·) ∘ φ` for a map `τ`, and
evaluating at `1` gives `φ x = τ(x) φ(1)`, so `τ = φ(1)⁻¹ φ` is multiplicative
(`LinearMap.GeneralLinearGroup.algEquivOfMulLmul`).

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
@[simp]
theorem mulGalois_inv (c : Eˣ) (τ : E ≃ₐ[F] E) :
    (mulGalois c τ)⁻¹ = mulGalois (Units.map (τ.symm : E →* E) c⁻¹) τ.symm := by
  refine inv_eq_of_mul_eq_one_right (Units.ext (LinearMap.ext fun v ↦ ?_))
  simp

/-- `v ↦ c τ(v)` multiplies as in `Eˣ ⋊ Gal(E/F)`: `(c, τ) (c', τ') = (c τ(c'), τ τ')`. -/
@[simp]
theorem mulGalois_mul (c c' : Eˣ) (τ τ' : E ≃ₐ[F] E) :
    mulGalois c τ * mulGalois c' τ' = mulGalois (c * Units.map (τ : E →* E) c') (τ * τ') :=
  Units.ext (LinearMap.ext fun v ↦ by simp [mul_assoc])

/-- `v ↦ c id(v)` is multiplication by `c`. -/
@[simp]
theorem mulGalois_one_right (c : Eˣ) :
    mulGalois c (1 : E ≃ₐ[F] E) = Units.map (Algebra.lmul F E : E →* Module.End F E) c :=
  Units.ext (LinearMap.ext fun v ↦ by simp [Algebra.coe_lmul_eq_mul])

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

end TauCeti

namespace LinearMap.GeneralLinearGroup

variable {F : Type*} [Field F] {E : Type*} [Field E] [Algebra F E]

private theorem apply_one_ne_zero (φ : LinearMap.GeneralLinearGroup F E) :
    (φ : E →ₗ[F] E) 1 ≠ 0 :=
  (LinearMap.GeneralLinearGroup.toLinearEquiv φ).map_ne_zero_iff.2 one_ne_zero

/-- A linear automorphism `φ` with `φ ∘ (x ·) = (τ x ·) ∘ φ` for some `τ` and every `x` makes `τ`
an `F`-algebra automorphism of `E`, namely `v ↦ φ(v) φ(1)⁻¹`. -/
noncomputable def algEquivOfMulLmul (φ : LinearMap.GeneralLinearGroup F E) {τ : E → E}
    (h : ∀ x, (φ : E →ₗ[F] E) * Algebra.lmul F E x = Algebra.lmul F E (τ x) * φ) :
    E ≃ₐ[F] E :=
  AlgEquiv.ofBijective
    (AlgHom.ofLinearMap (LinearMap.mulRight F ((φ : E →ₗ[F] E) 1)⁻¹ ∘ₗ (φ : E →ₗ[F] E))
      (mul_inv_cancel₀ (apply_one_ne_zero φ)) fun x y ↦ by
        have hxy := congrArg (fun ψ : E →ₗ[F] E ↦ ψ y) (h x)
        simp only [mul_apply_eq_comp, Algebra.coe_lmul_eq_mul, LinearMap.mul_apply'] at hxy
        simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.mulRight_apply, hxy,
          TauCeti.apply_eq_of_mul_lmul h x, mul_inv_cancel_right₀ (apply_one_ne_zero φ)]
        ring)
    ((Units.mk0 _ (inv_ne_zero (apply_one_ne_zero φ))).mulRight_bijective.comp
      (LinearMap.GeneralLinearGroup.toLinearEquiv φ).bijective)

/-- `LinearMap.GeneralLinearGroup.algEquivOfMulLmul` is `τ`. -/
@[simp]
theorem algEquivOfMulLmul_apply (φ : LinearMap.GeneralLinearGroup F E) {τ : E → E}
    (h : ∀ x, (φ : E →ₗ[F] E) * Algebra.lmul F E x = Algebra.lmul F E (τ x) * φ) (v : E) :
    algEquivOfMulLmul φ h v = τ v :=
  (congrArg (· * ((φ : E →ₗ[F] E) 1)⁻¹) (TauCeti.apply_eq_of_mul_lmul h v)).trans
    (mul_inv_cancel_right₀ (apply_one_ne_zero φ) _)

end LinearMap.GeneralLinearGroup

namespace TauCeti

variable {F : Type*} [Field F] {E : Type*} [Field E] [Algebra F E]

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
    refine ⟨Units.mk0 _ (LinearMap.GeneralLinearGroup.apply_one_ne_zero φ),
      φ.algEquivOfMulLmul hτ, ?_⟩
    ext v
    rw [mulGalois_apply, Units.val_mk0, LinearMap.GeneralLinearGroup.algEquivOfMulLmul_apply,
      apply_eq_of_mul_lmul hτ v, mul_comm]
  · rintro ⟨c, τ, rfl⟩
    refine Subgroup.mem_normalizer_iff.2 fun u ↦ ?_
    refine ⟨mulGalois_conj_mem_lmulUnitsRange c τ, fun hu ↦ ?_⟩
    have h := mulGalois_conj_mem_lmulUnitsRange (Units.map (τ.symm : E →* E) c⁻¹) τ.symm hu
    rw [← mulGalois_inv, inv_inv] at h
    simpa only [mul_assoc, inv_mul_cancel, mul_one, inv_mul_cancel_left] using h

/-- The factorization `v ↦ c τ(v)` is unique. -/
theorem mulGalois_injective :
    Function.Injective fun p : Eˣ × (E ≃ₐ[F] E) ↦ mulGalois p.1 p.2 := by
  rintro ⟨c, τ⟩ ⟨c', τ'⟩ h
  have h' (v : E) := congrArg (fun u : LinearMap.GeneralLinearGroup F E ↦ (u : E →ₗ[F] E) v) h
  simp only [mulGalois_apply] at h'
  have hc : c = c' := Units.ext (by simpa using h' 1)
  subst hc
  exact Prod.ext rfl (AlgEquiv.ext fun v ↦ mul_left_cancel₀ c.ne_zero (h' v))

/-- `v ↦ c τ(v)` determines `c` and `τ`. -/
@[simp]
theorem mulGalois_inj {c c' : Eˣ} {τ τ' : E ≃ₐ[F] E} :
    mulGalois c τ = mulGalois c' τ' ↔ c = c' ∧ τ = τ' := by
  refine ⟨fun h ↦ Prod.ext_iff.1 (mulGalois_injective (a₁ := (c, τ)) (a₂ := (c', τ')) h), ?_⟩
  rintro ⟨rfl, rfl⟩
  rfl

/-- `v ↦ c τ(v)` is a multiplication by a unit of `E` exactly when `τ` is the identity. -/
@[simp]
theorem mulGalois_mem_lmulUnitsRange_iff {c : Eˣ} {τ : E ≃ₐ[F] E} :
    mulGalois c τ ∈ lmulUnitsRange F E ↔ τ = 1 := by
  refine ⟨fun h ↦ ?_, by rintro rfl; simp⟩
  obtain ⟨x, hx⟩ := mem_lmulUnitsRange_iff.1 h
  rw [← mulGalois_one_right] at hx
  exact (mulGalois_inj.1 hx).2.symm

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

end TauCeti
