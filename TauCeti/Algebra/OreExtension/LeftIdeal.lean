/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.OreExtension.Basic
public import Mathlib.LinearAlgebra.Quotient.Basic

import Mathlib.LinearAlgebra.Isomorphisms

/-!
# Left ideals of Ore extensions and differential operator rings

For a `(σ, δ)`-invariant left ideal `I` of `R`, the Ore polynomials in `R[X; σ, δ]` whose left
coefficients lie in `I` form a left ideal `TauCeti.OreExtension.coeffLeftIdeal` preserved by right
multiplication by `X`, with left `R`-linear quotient `(R[X; σ, δ] ⧸ coeffLeftIdeal I) ≃ₗ[R]
(ℕ →₀ (R ⧸ I))` (`TauCeti.OreExtension.quotientCoeffLeftIdealEquiv`). In a differential operator
ring `R[X; δ]` (`σ = id`), `C '' I` generates `coeffLeftIdeal I` as a left ideal
(`TauCeti.OreExtension.span_image_C_eq_coeffLeftIdeal`), transferring the right-shift estimate from
`R` to `R[X; δ]` (`TauCeti.OreExtension.exists_forall_mul_mem_coeffLeftIdeal`).

## References

* J. C. McConnell and J. C. Robson, *Noncommutative Noetherian Rings*, Chapter 1, §1.2.
-/

public section

noncomputable section

namespace TauCeti.OreExtension

section Semiring

variable {k R : Type*} [CommSemiring k] [Semiring R] [Algebra k R]
  {σ : R →ₐ[k] R} {δ : SigmaDerivation σ}

/-- Right multiplication of `a Xⁿ` by `X` raises its degree by one. -/
theorem monomial_mul_X (n : ℕ) (a : R) :
    monomial (σ := σ) (δ := δ) n a * X = monomial (n + 1) a := by
  rw [← C_mul_X_pow_eq_monomial, mul_assoc, ← pow_succ, C_mul_X_pow_eq_monomial]

/-- Right multiplication by `X` clears the constant left coefficient. -/
@[simp]
theorem coeff_mul_X_zero (p : OreExtension σ δ) : coeff (p * X) 0 = 0 := by
  induction p using induction_on with
  | zero => simp
  | add n a p _ _ ih => simp [add_mul, monomial_mul_X, coeff_monomial, ih]

/-- Right multiplication by `X` shifts left coefficients upward by one. -/
@[simp]
theorem coeff_mul_X_succ (p : OreExtension σ δ) (n : ℕ) :
    coeff (p * X) (n + 1) = coeff p n := by
  induction p using induction_on with
  | zero => simp
  | add m a p _ _ ih => simp [add_mul, monomial_mul_X, coeff_monomial, ih]

/-- Right multiplication by `Xᵐ` shifts left coefficients upward by `m`. -/
@[simp]
theorem coeff_mul_X_pow_add (p : OreExtension σ δ) (n m : ℕ) :
    coeff (p * X ^ m) (n + m) = coeff p n := by
  induction m with
  | zero => simp
  | succ m ih => rw [pow_succ, ← mul_assoc, ← Nat.add_assoc, coeff_mul_X_succ, ih]

/-- Left scalar multiplication by `R` associates with multiplication in `R[X; σ, δ]`. -/
instance instIsScalarTowerSelf : IsScalarTower R (OreExtension σ δ) (OreExtension σ δ) where
  smul_assoc a p q := by rw [smul_eq_C_mul, smul_eq_C_mul, smul_eq_mul, smul_eq_mul, mul_assoc]

/-- **The coefficientwise left ideal** `{p | ∀ n, coeff p n ∈ I}` of `R[X; σ, δ]` associated to a
`(σ, δ)`-invariant left ideal `I` of `R`. -/
def coeffLeftIdeal (I : Submodule R R) (hσ : Set.MapsTo σ I I) (hδ : Set.MapsTo δ I I) :
    Submodule (OreExtension σ δ) (OreExtension σ δ) where
  carrier := {p | ∀ n, coeff p n ∈ I}
  zero_mem' _ := by simp
  add_mem' hp hq n := by rw [coeff_add]; exact add_mem (hp n) (hq n)
  smul_mem' q := by
    induction q using induction_on_mul with
    | C a => intro p hp n; rw [smul_eq_mul, coeff_C_mul, ← smul_eq_mul]; exact I.smul_mem a (hp n)
    | X =>
      rintro p hp (_ | n)
      · rw [smul_eq_mul, coeff_X_mul_zero]; exact hδ (hp 0)
      · rw [smul_eq_mul, coeff_X_mul_succ]; exact add_mem (hσ (hp n)) (hδ (hp (n + 1)))
    | add _ _ h₁ h₂ =>
      intro p hp n; rw [smul_eq_mul, add_mul, coeff_add]; exact add_mem (h₁ hp n) (h₂ hp n)
    | mul _ _ h₁ h₂ => intro p hp; rw [smul_eq_mul, mul_assoc]; exact h₁ (h₂ hp)

theorem mem_coeffLeftIdeal_iff {I : Submodule R R} {hσ : Set.MapsTo σ I I}
    {hδ : Set.MapsTo δ I I} {p : OreExtension σ δ} :
    p ∈ coeffLeftIdeal I hσ hδ ↔ ∀ n, coeff p n ∈ I := Iff.rfl

@[simp]
theorem C_mem_coeffLeftIdeal_iff {I : Submodule R R} {hσ : Set.MapsTo σ I I}
    {hδ : Set.MapsTo δ I I} {a : R} : C a ∈ coeffLeftIdeal I hσ hδ ↔ a ∈ I :=
  ⟨fun h ↦ by simpa using h 0, fun ha n ↦ by by_cases hn : n = 0 <;> simp [hn, ha]⟩

theorem monomial_mem_coeffLeftIdeal {I : Submodule R R} {hσ : Set.MapsTo σ I I}
    {hδ : Set.MapsTo δ I I} (n : ℕ) {a : R} (ha : a ∈ I) :
    monomial n a ∈ coeffLeftIdeal I hσ hδ := fun m ↦ by
  by_cases h : n = m <;> simp [coeff_monomial, h, ha]

/-- Right multiplication by `X` preserves `coeffLeftIdeal I` without any shift. -/
theorem mul_X_mem_coeffLeftIdeal {I : Submodule R R} {hσ : Set.MapsTo σ I I}
    {hδ : Set.MapsTo δ I I} {p : OreExtension σ δ} (hp : p ∈ coeffLeftIdeal I hσ hδ) :
    p * X ∈ coeffLeftIdeal I hσ hδ := by
  rintro (_ | n); · simp
  exact coeff_mul_X_succ p n ▸ hp n

/-- Right multiplication by `Xᵐ` preserves `coeffLeftIdeal I`. -/
theorem mul_X_pow_mem_coeffLeftIdeal {I : Submodule R R} {hσ : Set.MapsTo σ I I}
    {hδ : Set.MapsTo δ I I} {p : OreExtension σ δ} (hp : p ∈ coeffLeftIdeal I hσ hδ) (m : ℕ) :
    p * X ^ m ∈ coeffLeftIdeal I hσ hδ := by
  induction m with
  | zero => simpa using hp
  | succ m ih => rw [pow_succ, ← mul_assoc]; exact mul_X_mem_coeffLeftIdeal ih

/-- `coeffLeftIdeal` is monotone in the coefficient left ideal `I`. -/
theorem coeffLeftIdeal_mono {I₁ I₂ : Submodule R R} {hσ₁ : Set.MapsTo σ I₁ I₁}
    {hδ₁ : Set.MapsTo δ I₁ I₁} {hσ₂ : Set.MapsTo σ I₂ I₂} {hδ₂ : Set.MapsTo δ I₂ I₂}
    (h : I₁ ≤ I₂) : coeffLeftIdeal I₁ hσ₁ hδ₁ ≤ coeffLeftIdeal I₂ hσ₂ hδ₂ :=
  fun _ hp n ↦ h (hp n)

/-- The zero left ideal of `R` induces the zero left ideal of `R[X; σ, δ]`. -/
@[simp]
theorem coeffLeftIdeal_bot :
    coeffLeftIdeal (⊥ : Submodule R R) (by rintro _ rfl; simp) (by rintro _ rfl; simp) =
      (⊥ : Submodule (OreExtension σ δ) (OreExtension σ δ)) := by
  rw [eq_bot_iff]; intro p hp; ext n; simpa using mem_coeffLeftIdeal_iff.1 hp n

/-- Intersecting a family of `coeffLeftIdeal`s intersects their coefficient ideals. -/
theorem iInf_coeffLeftIdeal {ι : Sort*} {I : ι → Submodule R R}
    (hσ : ∀ i, Set.MapsTo σ (I i) (I i)) (hδ : ∀ i, Set.MapsTo δ (I i) (I i)) :
    (⨅ i, coeffLeftIdeal (I i) (hσ i) (hδ i)) =
      coeffLeftIdeal (⨅ i, I i)
        (fun x hx ↦ (Submodule.mem_iInf _).2 fun i ↦ hσ i ((Submodule.mem_iInf _).1 hx i))
        (fun x hx ↦ (Submodule.mem_iInf _).2 fun i ↦ hδ i ((Submodule.mem_iInf _).1 hx i)) := by
  ext p
  exact ⟨fun hp n ↦ (Submodule.mem_iInf _).2 fun i ↦
      mem_coeffLeftIdeal_iff.1 ((Submodule.mem_iInf _).1 hp i) n,
    fun hp ↦ (Submodule.mem_iInf _).2 fun i ↦
      mem_coeffLeftIdeal_iff.2 fun n ↦ (Submodule.mem_iInf _).1 (mem_coeffLeftIdeal_iff.1 hp n) i⟩

/-- `C '' (Submodule.span R s)` and `C '' s` generate the same left ideal of `R[X; σ, δ]`. -/
theorem span_image_C_span (σ : R →ₐ[k] R) (δ : SigmaDerivation σ) (s : Set R) :
    Submodule.span (OreExtension σ δ) ((C (σ := σ) (δ := δ)) '' (Submodule.span R s : Set R)) =
      Submodule.span (OreExtension σ δ) ((C (σ := σ) (δ := δ)) '' s) := by
  refine le_antisymm (Submodule.span_le.2 ?_)
    (Submodule.span_mono (Set.image_mono Submodule.subset_span))
  rintro _ ⟨a, ha, rfl⟩
  induction ha using Submodule.span_induction with
  | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
  | zero => simp
  | add _ _ _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul r _ _ hx => rw [smul_eq_mul, C_mul]; exact Submodule.smul_mem _ (C r) hx

end Semiring

section Ring

variable {k R : Type*} [CommSemiring k] [Ring R] [Algebra k R]

section Quotient

variable {σ : R →ₐ[k] R} {δ : SigmaDerivation σ}

/-- The left `R`-linear map reading off left coefficients modulo a left ideal `I` of `R`. -/
def toQuotientFinsupp (I : Submodule R R) : OreExtension σ δ →ₗ[R] (ℕ →₀ (R ⧸ I)) :=
  (Finsupp.mapRange.linearMap I.mkQ).comp leftCoeffLinearEquiv.toLinearMap

@[simp]
theorem toQuotientFinsupp_apply (I : Submodule R R) (p : OreExtension σ δ) (n : ℕ) :
    toQuotientFinsupp I p n = I.mkQ (coeff p n) := by simp [toQuotientFinsupp, coeff_def]

@[simp]
theorem toQuotientFinsupp_monomial (I : Submodule R R) (n : ℕ) (a : R) :
    toQuotientFinsupp (σ := σ) (δ := δ) I (monomial n a) = Finsupp.single n (I.mkQ a) := by
  simp [toQuotientFinsupp]

theorem toQuotientFinsupp_surjective (I : Submodule R R) :
    Function.Surjective (toQuotientFinsupp (σ := σ) (δ := δ) I) :=
  (Finsupp.mapRange_surjective _ (map_zero _) I.mkQ_surjective).comp
    leftCoeffLinearEquiv.surjective

@[simp]
theorem ker_toQuotientFinsupp (I : Submodule R R) (hσ : Set.MapsTo σ I I)
    (hδ : Set.MapsTo δ I I) :
    LinearMap.ker (toQuotientFinsupp (σ := σ) (δ := δ) I) =
      (coeffLeftIdeal I hσ hδ).restrictScalars R := by
  ext p
  simp [LinearMap.mem_ker, Finsupp.ext_iff, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero,
    mem_coeffLeftIdeal_iff]

/-- **Left-coefficient decomposition** `(R[X; σ, δ] ⧸ coeffLeftIdeal I) ≃ₗ[R] (ℕ →₀ (R ⧸ I))`. -/
def quotientCoeffLeftIdealEquiv (I : Submodule R R) (hσ : Set.MapsTo σ I I)
    (hδ : Set.MapsTo δ I I) :
    (OreExtension σ δ ⧸ coeffLeftIdeal I hσ hδ) ≃ₗ[R] (ℕ →₀ (R ⧸ I)) :=
  ((Submodule.Quotient.restrictScalarsEquiv R (coeffLeftIdeal I hσ hδ)).symm.trans
    (Submodule.quotEquivOfEq _ _ (ker_toQuotientFinsupp I hσ hδ).symm)).trans
      ((toQuotientFinsupp I).quotKerEquivOfSurjective (toQuotientFinsupp_surjective I))

@[simp]
theorem quotientCoeffLeftIdealEquiv_mk (I : Submodule R R) (hσ : Set.MapsTo σ I I)
    (hδ : Set.MapsTo δ I I) (p : OreExtension σ δ) :
    quotientCoeffLeftIdealEquiv I hσ hδ (Submodule.Quotient.mk p) = toQuotientFinsupp I p := by
  simp [quotientCoeffLeftIdealEquiv]

@[simp]
theorem quotientCoeffLeftIdealEquiv_symm_single (I : Submodule R R) (hσ : Set.MapsTo σ I I)
    (hδ : Set.MapsTo δ I I) (n : ℕ) (a : R) :
    (quotientCoeffLeftIdealEquiv (σ := σ) (δ := δ) I hσ hδ).symm
        (Finsupp.single n (Submodule.Quotient.mk a)) = Submodule.Quotient.mk (monomial n a) := by
  rw [LinearEquiv.symm_apply_eq, quotientCoeffLeftIdealEquiv_mk, toQuotientFinsupp_monomial,
    Submodule.mkQ_apply]

theorem quotientCoeffLeftIdealEquiv_factor {I₁ I₂ : Submodule R R}
    {hσ₁ : Set.MapsTo σ I₁ I₁} {hδ₁ : Set.MapsTo δ I₁ I₁}
    {hσ₂ : Set.MapsTo σ I₂ I₂} {hδ₂ : Set.MapsTo δ I₂ I₂} (h : I₁ ≤ I₂)
    (q : OreExtension σ δ ⧸ coeffLeftIdeal I₁ hσ₁ hδ₁) :
    quotientCoeffLeftIdealEquiv I₂ hσ₂ hδ₂ (Submodule.factor (coeffLeftIdeal_mono h) q) =
      Finsupp.mapRange.linearMap (Submodule.factor h)
        (quotientCoeffLeftIdealEquiv I₁ hσ₁ hδ₁ q) := by
  obtain ⟨p, rfl⟩ := Submodule.Quotient.mk_surjective _ q; ext n; simp

end Quotient

section DifferentialOperator

variable {δ : SigmaDerivation (AlgHom.id k R)}

/-- Every submodule of `R` is invariant under `AlgHom.id k R`. -/
theorem mapsTo_id (I : Submodule R R) : Set.MapsTo (AlgHom.id k R) I I :=
  fun _ hx ↦ by rwa [AlgHom.id_apply]

/-- **Generators of `coeffLeftIdeal` in `R[X; δ]`.** For a `δ`-invariant left ideal `I` of `R`,
`C '' I` generates `coeffLeftIdeal I` as a left ideal. -/
theorem span_image_C_eq_coeffLeftIdeal (I : Submodule R R) (hδ : Set.MapsTo δ I I) :
    Submodule.span (OreExtension (AlgHom.id k R) δ) (C '' (I : Set R)) =
      coeffLeftIdeal I (mapsTo_id I) hδ := by
  refine le_antisymm (Submodule.span_le.2 fun _ ⟨a, ha, h⟩ ↦ h ▸ C_mem_coeffLeftIdeal_iff.2 ha)
    fun p hp ↦ ?_
  have hmon (n : ℕ) {a : R} (ha : a ∈ I) :
      monomial (σ := AlgHom.id k R) (δ := δ) n a ∈
        Submodule.span (OreExtension (AlgHom.id k R) δ) (C '' (I : Set R)) := by
    induction n generalizing a with
    | zero => rw [monomial_zero_left]; exact Submodule.subset_span ⟨a, ha, rfl⟩
    | succ n ih =>
      have hX : monomial (σ := AlgHom.id k R) (δ := δ) (n + 1) a =
          X * monomial n a - monomial n (δ a) := by
        rw [X_mul_monomial, AlgHom.id_apply, add_sub_cancel_right]
      exact hX ▸ sub_mem (Submodule.smul_mem _ X (ih ha)) (ih (hδ ha))
  exact sum_monomial_eq p ▸ Submodule.sum_mem _ fun n _ ↦ hmon n (hp n)

/-- **Right-shift estimate in `R[X; δ]`.** A downward-directed family of `δ`-invariant left ideals
satisfying the right-shift estimate in `R` induces one in `R[X; δ]`. -/
theorem exists_forall_mul_mem_coeffLeftIdeal {ι : Type*} {I : ι → Submodule R R}
    (hI : Directed (· ≥ ·) I) (hδ : ∀ i, Set.MapsTo δ (I i) (I i))
    (hIr : ∀ (b : R) (i : ι), ∃ j, ∀ a ∈ I j, a * b ∈ I i)
    (q : OreExtension (AlgHom.id k R) δ) (i : ι) :
    ∃ j, ∀ p ∈ coeffLeftIdeal (I j) (mapsTo_id (I j)) (hδ j),
      p * q ∈ coeffLeftIdeal (I i) (mapsTo_id (I i)) (hδ i) := by
  induction q using induction_on_mul generalizing i with
  | C b =>
    obtain ⟨j, hj⟩ := hIr b i
    refine ⟨j, fun p hp ↦ ?_⟩
    rw [← span_image_C_eq_coeffLeftIdeal (I j) (hδ j)] at hp
    induction hp using Submodule.span_induction with
    | mem _ hx => obtain ⟨a, ha, rfl⟩ := hx; rw [← C_mul, C_mem_coeffLeftIdeal_iff]; exact hj a ha
    | zero => simp
    | add _ _ _ _ hx hy => rw [add_mul]; exact add_mem hx hy
    | smul r _ _ hx => rw [smul_eq_mul, mul_assoc]; exact Submodule.smul_mem _ r hx
  | X => exact ⟨i, fun _ ↦ mul_X_mem_coeffLeftIdeal⟩
  | add _ _ h₁ h₂ =>
    obtain ⟨⟨j₁, hj₁⟩, ⟨j₂, hj₂⟩⟩ := h₁ i, h₂ i
    obtain ⟨j, hle₁, hle₂⟩ := hI j₁ j₂
    exact ⟨j, fun p hp ↦ mul_add p _ _ ▸
      add_mem (hj₁ p (coeffLeftIdeal_mono hle₁ hp)) (hj₂ p (coeffLeftIdeal_mono hle₂ hp))⟩
  | mul q₁ _ h₁ h₂ =>
    obtain ⟨j₁, hj₁⟩ := h₂ i
    obtain ⟨j, hj⟩ := h₁ j₁
    exact ⟨j, fun p hp ↦ by rw [← mul_assoc]; exact hj₁ (p * q₁) (hj p hp)⟩

end DifferentialOperator

end Ring

end TauCeti.OreExtension
