/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.CongruenceSubgroups.FunctionField.Invariant
public import TauCeti.NumberTheory.ModularForms.SiegelFunction.Asymptotics
public import TauCeti.NumberTheory.ModularForms.SiegelFunction.Congruence
import TauCeti.Algebra.BigOperators.ZPow
import TauCeti.LinearAlgebra.Matrix.Divisibility
import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Basic

/-!
# Siegel modular units on `X(N)`

Let `(aᵢ, mᵢ)` be a finite family of integral numerators `aᵢ ∈ ℤ²` and integral exponents `mᵢ`,
with no `aᵢ` in `N ℤ²`, satisfying the Kubert–Lang conditions of level `N`: `gcd(2, N) N` divides
`∑ mᵢ aᵢ₁²` and `∑ mᵢ aᵢ₂²`, `N` divides `∑ mᵢ aᵢ₁ aᵢ₂`, and `12` divides `gcd(12, N) ∑ mᵢ`. Then
the product `∏ g_{aᵢ/N}^{mᵢ}` of Siegel functions is invariant under `Γ(N)`
(`TauCeti.ModularForm.prod_siegelFunction_div_zpow_smul_of_mem_Gamma`). It is holomorphic and
nowhere zero on the upper half-plane, and after composition with any `γ ∈ SL(2, ℤ)` it is a
product of the same shape up to a root of unity, so it has at most exponential growth at every
cusp (`TauCeti.ModularForm.isBigO_siegelFunction_zpow`). Hence it is a nonzero meromorphic function
on the compactified modular curve `X(N)` (`TauCeti.ModularForm.siegelMeromorphicFunction`), a
modular unit of level `N`: its zeros and poles lie at the cusps.

The action of `γ ∈ SL(2, ℤ)` on the function field of `X(N)` sends the unit of `(aᵢ, mᵢ)` to a
twelfth root of unity times the unit of `(aᵢ γ, mᵢ)`, with the row vectors `aᵢ` multiplied on the
right by `γ`; the conditions are preserved by this substitution.

## Main declarations

* `TauCeti.ModularForm.IsSiegelUnitData`: the Kubert–Lang conditions of level `N` on `(aᵢ, mᵢ)`,
  preserved by `aᵢ ↦ aᵢ γ` (`TauCeti.ModularForm.isSiegelUnitData_vecMul_iff`).
* `TauCeti.ModularForm.siegelMeromorphicFunction`: the product `∏ g_{aᵢ/N}^{mᵢ}` as a meromorphic
  function on `X(N)`, under the Kubert–Lang conditions (and `0` otherwise).
* `TauCeti.ModularForm.siegelMeromorphicFunction_ofQuotient_mk`: its value at the orbit of `τ`.
* `TauCeti.ModularForm.siegelMeromorphicFunction_ne_zero_iff`: it is not the zero function
  exactly when the conditions hold.
* `TauCeti.ModularForm.exists_unop_modularFunctionAction_siegelMeromorphicFunction`: `γ` sends the
  unit of `(aᵢ, mᵢ)` to a twelfth root of unity times the unit of `(aᵢ γ, mᵢ)`.

## References

* D. S. Kubert, S. Lang, *Modular Units*, Chapter 2, §1, and Chapter 3, §5.
* D. H. Shin, *Generation of class fields by Siegel–Ramachandra invariants*, §2.
-/

public noncomputable section

open Asymptotics CongruenceSubgroup Filter Matrix MulOpposite UpperHalfPlane
open Subgroup.CompactifiedQuotient TauCeti.RiemannSurface
open scoped Manifold MatrixGroups

namespace TauCeti.ModularForm

variable {N : ℕ} {ι : Type*} {s : Finset ι} {a : ι → Fin 2 → ℤ} {m : ι → ℤ}

/-! ### The product on the upper half-plane -/

/-- The parameter `a / N` multiplied on the right by `γ` is `(a γ) / N`. -/
private theorem vecMul_map_div (a : Fin 2 → ℤ) (γ : SL(2, ℤ)) :
    (fun j ↦ (a j : ℝ) / N) ᵥ* (γ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom ℝ) =
      fun j ↦ ((a ᵥ* (γ : Matrix (Fin 2) (Fin 2) ℤ)) j : ℝ) / N := by
  ext j
  simp only [vecMul, dotProduct, Fin.sum_univ_two, map_apply, eq_intCast]
  push_cast
  ring

/-- A numerator outside `N ℤ²` gives a parameter outside `ℤ²`. -/
private theorem div_ne_intCast [NeZero N] {a : Fin 2 → ℤ} (ha : ¬ ∀ j, (N : ℤ) ∣ a j)
    (t : Fin 2 → ℤ) : (fun j ↦ (a j : ℝ) / N) ≠ fun j ↦ (t j : ℝ) := by
  intro h
  refine ha fun j ↦ ⟨t j, ?_⟩
  have hN : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have := congrFun h j
  rw [div_eq_iff hN] at this
  exact_mod_cast this.trans (mul_comm _ _)

/-- Right multiplication by `γ ∈ SL(2, ℤ)` keeps a numerator outside `N ℤ²`. -/
private theorem not_forall_dvd_vecMul {a : Fin 2 → ℤ} (ha : ¬ ∀ j, (N : ℤ) ∣ a j)
    (γ : SL(2, ℤ)) : ¬ ∀ j, (N : ℤ) ∣ (a ᵥ* (γ : Matrix (Fin 2) (Fin 2) ℤ)) j :=
  fun h ↦ ha (dvd_of_forall_dvd_vecMul (by simp) h)

/-- The product `∏ g_{aᵢ/N}^{mᵢ}` is holomorphic on the upper half-plane. -/
private theorem mdifferentiable_prod_siegelFunction [NeZero N]
    (ha : ∀ i ∈ s, ¬ ∀ j, (N : ℤ) ∣ a i j) :
    MDiff fun τ : ℍ ↦ ∏ i ∈ s, siegelFunction (fun j ↦ (a i j : ℝ) / N) τ ^ m i := by
  rw [UpperHalfPlane.mdifferentiable_iff]
  refine DifferentiableOn.congr
    (f := fun z : ℂ ↦ ∏ i ∈ s, siegelFunction (fun j ↦ (a i j : ℝ) / N) z ^ m i)
    (DifferentiableOn.fun_finsetProd fun i hi ↦ (differentiableOn_siegelFunction _).zpow
      (.inl fun z hz ↦ siegelFunction_ne_zero (div_ne_intCast (ha i hi)) hz)) fun z hz ↦ ?_
  simp [Function.comp_apply, ofComplex_apply_of_im_pos hz]

/-- The product `∏ g_{aᵢ/N}^{mᵢ}` is `O(exp (c Im τ))` at `i∞` for some real `c`. -/
private theorem exists_isBigO_prod_siegelFunction [NeZero N]
    (ha : ∀ i ∈ s, ¬ ∀ j, (N : ℤ) ∣ a i j) :
    ∃ c : ℝ, (fun τ : ℍ ↦ ∏ i ∈ s, siegelFunction (fun j ↦ (a i j : ℝ) / N) τ ^ m i)
      =O[atImInfty] fun τ ↦ Real.exp (c * τ.im) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, by simpa using isBigO_refl (fun _ : ℍ ↦ (1 : ℝ)) atImInfty⟩
  | insert i s hi ih =>
    obtain ⟨c, hc⟩ := ih fun k hk ↦ ha k (Finset.mem_insert_of_mem hk)
    refine ⟨-(Real.pi * m i * bernoulliFun 2 (Int.fract ((a i 0 : ℝ) / N))) + c,
      ((isBigO_siegelFunction_zpow (div_ne_intCast
      (ha i (Finset.mem_insert_self i s))) (m i)).mul hc).congr (fun τ ↦ ?_) fun τ ↦ ?_⟩
    · rw [Finset.prod_insert hi]
    · rw [← Real.exp_add, add_mul]

/-- **The transformation law of the product.** For `γ ∈ SL(2, ℤ)` there is a twelfth root of
unity `ζ` with `∏ g_{aᵢ/N}^{mᵢ}(γ τ) = ζ ∏ g_{(aᵢ γ)/N}^{mᵢ}(τ)` for every `τ`: if
`g_r(γ τ) = ε g_{r γ}(τ)` for every `r`, then `ζ = ε ^ ∑ mᵢ`. -/
private theorem exists_prod_siegelFunction_div_zpow_smul (γ : SL(2, ℤ)) :
    ∃ ζ : ℂ, ζ ^ 12 = 1 ∧ ∀ τ : ℍ,
      ∏ i ∈ s, siegelFunction (fun j ↦ (a i j : ℝ) / N) ↑(γ • τ) ^ m i =
        ζ * ∏ i ∈ s, siegelFunction
          (fun j ↦ ((a i ᵥ* (γ : Matrix (Fin 2) (Fin 2) ℤ)) j : ℝ) / N) τ ^ m i := by
  obtain ⟨ε, hε12, hε⟩ := exists_siegelFunction_smul_eq_mul γ
  have hε₀ : ε ≠ 0 := by rintro rfl; norm_num at hε12
  refine ⟨ε ^ ∑ i ∈ s, m i, by rw [← zpow_natCast, ← _root_.zpow_mul, mul_comm,
    _root_.zpow_mul, zpow_natCast, hε12, _root_.one_zpow], fun τ ↦ ?_⟩
  simp_rw [hε, vecMul_map_div, mul_zpow, Finset.prod_mul_distrib]
  rw [Finset.prod_zpow_eq_zpow_sum_of_isUnit s (IsUnit.mk0 ε hε₀)]

/-! ### The Kubert–Lang conditions under `SL(2, ℤ)` -/

/-- The sums `∑ mᵢ aᵢⱼ aᵢₖ` after the substitution `aᵢ ↦ aᵢ γ`. -/
private theorem sum_mul_vecMul_mul_vecMul (γ : Matrix (Fin 2) (Fin 2) ℤ) (j k : Fin 2) :
    ∑ i ∈ s, m i * ((a i ᵥ* γ) j * (a i ᵥ* γ) k) =
      γ 0 j * γ 0 k * ∑ i ∈ s, m i * a i 0 ^ 2 +
        (γ 0 j * γ 1 k + γ 1 j * γ 0 k) * ∑ i ∈ s, m i * (a i 0 * a i 1) +
          γ 1 j * γ 1 k * ∑ i ∈ s, m i * a i 1 ^ 2 := by
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  simp only [vecMul, dotProduct, Fin.sum_univ_two]
  ring

/-- The divisibility of `∑ mᵢ (aᵢ γ)ⱼ²` by `gcd(2, N) N`. -/
private theorem dvd_sum_mul_vecMul_sq (γ : Matrix (Fin 2) (Fin 2) ℤ)
    (h₀ : ((Nat.gcd 2 N * N : ℕ) : ℤ) ∣ ∑ i ∈ s, m i * a i 0 ^ 2)
    (h₁ : ((Nat.gcd 2 N * N : ℕ) : ℤ) ∣ ∑ i ∈ s, m i * a i 1 ^ 2)
    (h₀₁ : (N : ℤ) ∣ ∑ i ∈ s, m i * (a i 0 * a i 1)) (j : Fin 2) :
    ((Nat.gcd 2 N * N : ℕ) : ℤ) ∣ ∑ i ∈ s, m i * (a i ᵥ* γ) j ^ 2 := by
  have h2 : ((Nat.gcd 2 N * N : ℕ) : ℤ) ∣ 2 * N := by
    exact_mod_cast Nat.mul_dvd_mul_right (Nat.gcd_dvd_left 2 N) N
  have h := sum_mul_vecMul_mul_vecMul (s := s) (m := m) (a := a) γ j j
  simp only [← sq] at h
  rw [h, show γ 0 j * γ 1 j + γ 1 j * γ 0 j = 2 * (γ 0 j * γ 1 j) by ring]
  refine dvd_add (dvd_add (dvd_mul_of_dvd_right h₀ _) ?_) (dvd_mul_of_dvd_right h₁ _)
  obtain ⟨t, ht⟩ := h₀₁
  rw [ht]
  exact (h2.mul_right (γ 0 j * γ 1 j * t)).trans (dvd_of_eq (by ring))

/-- The divisibility of `∑ mᵢ (aᵢ γ)₁ (aᵢ γ)₂` by `N`. -/
private theorem dvd_sum_mul_vecMul_mul_vecMul (γ : Matrix (Fin 2) (Fin 2) ℤ)
    (h₀ : ((Nat.gcd 2 N * N : ℕ) : ℤ) ∣ ∑ i ∈ s, m i * a i 0 ^ 2)
    (h₁ : ((Nat.gcd 2 N * N : ℕ) : ℤ) ∣ ∑ i ∈ s, m i * a i 1 ^ 2)
    (h₀₁ : (N : ℤ) ∣ ∑ i ∈ s, m i * (a i 0 * a i 1)) :
    (N : ℤ) ∣ ∑ i ∈ s, m i * ((a i ᵥ* γ) 0 * (a i ᵥ* γ) 1) := by
  have hN : (N : ℤ) ∣ ((Nat.gcd 2 N * N : ℕ) : ℤ) := by
    exact_mod_cast Nat.dvd_mul_left N _
  rw [sum_mul_vecMul_mul_vecMul]
  exact dvd_add (dvd_add (dvd_mul_of_dvd_right (hN.trans h₀) _) (dvd_mul_of_dvd_right h₀₁ _))
    (dvd_mul_of_dvd_right (hN.trans h₁) _)

/-! ### The modular unit on `X(N)` -/

/-- **The Kubert–Lang conditions** of level `N` on a family `(aᵢ, mᵢ)` of numerators
`aᵢ ∈ ℤ²` and exponents `mᵢ ∈ ℤ`, indexed by `s`: no `aᵢ` lies in `N ℤ²` (so the parameters
`aᵢ / N` are not in `ℤ²`), `gcd(2, N) N` divides `∑ mᵢ aᵢ₁²` and `∑ mᵢ aᵢ₂²`, `N` divides
`∑ mᵢ aᵢ₁ aᵢ₂`, and `12` divides `gcd(12, N) ∑ mᵢ`. Under these conditions `∏ g_{aᵢ/N}^{mᵢ}` is a
modular unit of level `N` (`TauCeti.ModularForm.siegelMeromorphicFunction`). -/
structure IsSiegelUnitData (N : ℕ) (s : Finset ι) (a : ι → Fin 2 → ℤ) (m : ι → ℤ) : Prop where
  /-- No numerator `aᵢ` lies in `N ℤ²`. -/
  not_dvd : ∀ i ∈ s, ¬ ∀ j, (N : ℤ) ∣ a i j
  /-- `gcd(2, N) N` divides `∑ mᵢ aᵢ₁²`. -/
  dvd_sum_sq₀ : ((Nat.gcd 2 N * N : ℕ) : ℤ) ∣ ∑ i ∈ s, m i * a i 0 ^ 2
  /-- `gcd(2, N) N` divides `∑ mᵢ aᵢ₂²`. -/
  dvd_sum_sq₁ : ((Nat.gcd 2 N * N : ℕ) : ℤ) ∣ ∑ i ∈ s, m i * a i 1 ^ 2
  /-- `N` divides `∑ mᵢ aᵢ₁ aᵢ₂`. -/
  dvd_sum_mul : (N : ℤ) ∣ ∑ i ∈ s, m i * (a i 0 * a i 1)
  /-- `12` divides `gcd(12, N) ∑ mᵢ`. -/
  twelve_dvd : (12 : ℤ) ∣ Nat.gcd 12 N * ∑ i ∈ s, m i

/-- The Kubert–Lang conditions are preserved by the substitution `aᵢ ↦ aᵢ γ`, `γ ∈ SL(2, ℤ)`. -/
theorem IsSiegelUnitData.vecMul (h : IsSiegelUnitData N s a m) (γ : SL(2, ℤ)) :
    IsSiegelUnitData N s (fun i ↦ a i ᵥ* (γ : Matrix (Fin 2) (Fin 2) ℤ)) m :=
  ⟨fun i hi ↦ not_forall_dvd_vecMul (h.not_dvd i hi) γ,
    dvd_sum_mul_vecMul_sq _ h.dvd_sum_sq₀ h.dvd_sum_sq₁ h.dvd_sum_mul 0,
    dvd_sum_mul_vecMul_sq _ h.dvd_sum_sq₀ h.dvd_sum_sq₁ h.dvd_sum_mul 1,
    dvd_sum_mul_vecMul_mul_vecMul _ h.dvd_sum_sq₀ h.dvd_sum_sq₁ h.dvd_sum_mul, h.twelve_dvd⟩

/-- The family `(aᵢ γ, mᵢ)` satisfies the Kubert–Lang conditions exactly when `(aᵢ, mᵢ)` does,
since `γ⁻¹` carries it back. -/
theorem isSiegelUnitData_vecMul_iff (γ : SL(2, ℤ)) :
    IsSiegelUnitData N s (fun i ↦ a i ᵥ* (γ : Matrix (Fin 2) (Fin 2) ℤ)) m ↔
      IsSiegelUnitData N s a m :=
  ⟨fun h ↦ by
    have hinv : (fun i ↦ (a i ᵥ* (γ : Matrix (Fin 2) (Fin 2) ℤ)) ᵥ*
        ((γ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) = a :=
      funext fun i ↦ ((SpecialLinearGroup.vecMul_eq_iff_eq_vecMul_inv γ (a i) _).mp rfl).symm
    simpa only [hinv] using h.vecMul γ⁻¹, fun h ↦ h.vecMul γ⟩

/-- Every `SL(2, ℤ)`-translate of the product has at most exponential growth at `i∞`. -/
private theorem exists_isBigO_prod_siegelFunction_smul [NeZero N]
    (ha : ∀ i ∈ s, ¬ ∀ j, (N : ℤ) ∣ a i j) (γ : SL(2, ℤ)) :
    ∃ c : ℝ, (fun τ : ℍ ↦ ∏ i ∈ s, siegelFunction (fun j ↦ (a i j : ℝ) / N) ↑(γ • τ) ^ m i)
      =O[atImInfty] fun τ ↦ Real.exp (c * τ.im) := by
  obtain ⟨ζ, -, hζ⟩ := exists_prod_siegelFunction_div_zpow_smul (N := N) (s := s) (a := a)
    (m := m) γ
  obtain ⟨c, hc⟩ := exists_isBigO_prod_siegelFunction (m := m)
    fun i hi ↦ not_forall_dvd_vecMul (ha i hi) γ
  exact ⟨c, (hc.const_mul_left ζ).congr_left fun τ ↦ (hζ τ).symm⟩

open Classical in
/-- **The Siegel modular unit** `∏ g_{aᵢ/N}^{mᵢ}` as a meromorphic function on `X(N)`. When no
`aᵢ` lies in `N ℤ²` and the family satisfies the Kubert–Lang conditions (`gcd(2, N) N` divides
`∑ mᵢ aᵢ₁²` and `∑ mᵢ aᵢ₂²`, `N` divides `∑ mᵢ aᵢ₁ aᵢ₂` and `12` divides `gcd(12, N) ∑ mᵢ`;
`TauCeti.ModularForm.IsSiegelUnitData`), its value at the orbit of `τ` is `∏ g_{aᵢ/N}(τ)^{mᵢ}`
(`TauCeti.ModularForm.siegelMeromorphicFunction_ofQuotient_mk`); otherwise it is `0`
(`TauCeti.ModularForm.siegelMeromorphicFunction_of_not`). -/
def siegelMeromorphicFunction (N : ℕ) [NeZero N] (s : Finset ι) (a : ι → Fin 2 → ℤ)
    (m : ι → ℤ) : MeromorphicFunction ((Gamma N).map sl2zToPSL2R).CompactifiedQuotient :=
  if h : IsSiegelUnitData N s a m then
    meromorphicFunctionOfGammaInvariant
      (fun τ ↦ ∏ i ∈ s, siegelFunction (fun j ↦ (a i j : ℝ) / N) τ ^ m i)
      (mdifferentiable_prod_siegelFunction h.not_dvd)
      (fun _ hγ τ ↦ prod_siegelFunction_div_zpow_smul_of_mem_Gamma s a m h.dvd_sum_sq₀
        h.dvd_sum_sq₁ h.dvd_sum_mul h.twelve_dvd hγ τ)
      (exists_isBigO_prod_siegelFunction_smul h.not_dvd)
  else 0

variable [NeZero N]

/-- The value of the Siegel modular unit at the orbit of `τ` is `∏ g_{aᵢ/N}(τ)^{mᵢ}`. -/
@[simp]
theorem siegelMeromorphicFunction_ofQuotient_mk (h : IsSiegelUnitData N s a m) (τ : ℍ) :
    siegelMeromorphicFunction N s a m (ofQuotient (Quotient.mk _ τ)) =
      (∏ i ∈ s, siegelFunction (fun j ↦ (a i j : ℝ) / N) τ ^ m i : ℂ) := by
  rw [siegelMeromorphicFunction, dite_eq_left_of_eq_true (eq_true h),
    meromorphicFunctionOfGammaInvariant_ofQuotient_mk]

/-- The finite part of the Siegel modular unit at the orbit of `τ` is
`∏ g_{aᵢ/N}(τ)^{mᵢ}`. -/
@[simp]
theorem finitePart_siegelMeromorphicFunction_ofQuotient_mk (h : IsSiegelUnitData N s a m)
    (τ : ℍ) :
    (siegelMeromorphicFunction N s a m).finitePart (ofQuotient (Quotient.mk _ τ)) =
      ∏ i ∈ s, siegelFunction (fun j ↦ (a i j : ℝ) / N) τ ^ m i :=
  MeromorphicFunction.finitePart_of_eq_coe (siegelMeromorphicFunction_ofQuotient_mk h τ)

/-- Outside the Kubert–Lang conditions the Siegel modular unit is defined to be `0`. -/
theorem siegelMeromorphicFunction_of_not (h : ¬ IsSiegelUnitData N s a m) :
    siegelMeromorphicFunction N s a m = 0 := by
  rw [siegelMeromorphicFunction, dite_eq_right_of_eq_false (eq_false h)]

/-- **The Siegel modular unit is not zero**: its values on the open modular curve are products of
nonzero Siegel function values. -/
theorem siegelMeromorphicFunction_ne_zero (h : IsSiegelUnitData N s a m) :
    siegelMeromorphicFunction N s a m ≠ 0 := by
  intro h0
  have hτ := finitePart_siegelMeromorphicFunction_ofQuotient_mk h UpperHalfPlane.I
  rw [h0, MeromorphicFunction.finitePart_zero, Pi.zero_apply] at hτ
  refine (Finset.prod_ne_zero_iff.mpr fun i hi ↦ zpow_ne_zero _ <|
    siegelFunction_ne_zero (div_ne_intCast (h.not_dvd i hi)) UpperHalfPlane.I.im_pos) hτ.symm

/-- The Siegel modular unit is not zero exactly when the Kubert–Lang conditions hold. -/
theorem siegelMeromorphicFunction_ne_zero_iff :
    siegelMeromorphicFunction N s a m ≠ 0 ↔ IsSiegelUnitData N s a m :=
  ⟨fun h0 ↦ of_not_not fun h ↦ h0 (siegelMeromorphicFunction_of_not h),
    siegelMeromorphicFunction_ne_zero⟩

/-- **`SL(2, ℤ)` permutes the Siegel modular units up to roots of unity.** The action of
`γ ∈ SL(2, ℤ)` on the function field of `X(N)` sends the unit of `(aᵢ, mᵢ)` to a twelfth root of
unity times the unit of `(aᵢ γ, mᵢ)`. The family `(aᵢ γ, mᵢ)` satisfies the Kubert–Lang
conditions exactly when `(aᵢ, mᵢ)` does (`TauCeti.ModularForm.isSiegelUnitData_vecMul_iff`), so
no hypothesis is needed: otherwise both sides are `0`. -/
theorem exists_unop_modularFunctionAction_siegelMeromorphicFunction (γ : SL(2, ℤ)) :
    ∃ ζ : ℂ, ζ ^ 12 = 1 ∧ unop (modularFunctionAction N γ) (siegelMeromorphicFunction N s a m) =
      algebraMap ℂ _ ζ *
        siegelMeromorphicFunction N s (fun i ↦ a i ᵥ* (γ : Matrix (Fin 2) (Fin 2) ℤ)) m := by
  by_cases h : IsSiegelUnitData N s a m
  · obtain ⟨ζ, hζ, hprod⟩ := exists_prod_siegelFunction_div_zpow_smul (N := N) (s := s) (a := a)
      (m := m) γ
    refine ⟨ζ, hζ, meromorphicFunction_ext fun τ ↦ ?_⟩
    rw [modularFunctionAction_apply_ofQuotient, siegelMeromorphicFunction_ofQuotient_mk h,
      MeromorphicFunction.mul_apply_of_eq_coe (congrFun (MeromorphicFunction.coe_algebraMap _) _)
      (siegelMeromorphicFunction_ofQuotient_mk (h.vecMul γ) τ), hprod τ]
  · refine ⟨1, one_pow _, ?_⟩
    rw [siegelMeromorphicFunction_of_not h,
      siegelMeromorphicFunction_of_not (mt (isSiegelUnitData_vecMul_iff γ).mp h), map_zero,
      mul_zero]

end TauCeti.ModularForm
