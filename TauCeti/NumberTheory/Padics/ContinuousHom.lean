/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Padics.RingHoms
public import TauCeti.Topology.Algebra.ContinuousZModDual

/-!
# Continuous characters of the p-adic integers

Evaluation at `1` identifies the continuous additive homomorphisms from `ℤ_[p]` to
`ZMod (p ^ k)` with `ZMod (p ^ k)`: the character with value `a` at `1` is
`x ↦ PadicInt.toZModPow k x * a`. Density of the ordinary integers gives uniqueness;
continuity of the truncation map gives existence. The exponent `k` may be zero.

The multiplicative encoding identifies the continuous `ZMod (p ^ k)`-dual with the
coefficient ring as a module. This is the coefficient calculation for first continuous cohomology
with trivial action, developed in `TauCeti.NumberTheory.Padics.Cohomology`.
-/

public section

namespace ContinuousAddMonoidHom

variable {p : ℕ} [Fact p.Prime] {k : ℕ}

/-- A continuous character of the p-adic integers modulo `p ^ k` is the truncation map
multiplied by its value at `1`. -/
theorem padicInt_apply_eq_toZModPow_mul_apply_one
    (φ : ℤ_[p] →ₜ+ ZMod (p ^ k)) (x : ℤ_[p]) :
    φ x = PadicInt.toZModPow k x * φ 1 := by
  have hcont : Continuous (fun x : ℤ_[p] ↦ PadicInt.toZModPow k x * φ 1) :=
    (PadicInt.continuous_toZModPow k).mul continuous_const
  have h := PadicInt.denseRange_intCast.equalizer φ.continuous hcont
    (funext fun n ↦ by
      calc
        φ (n : ℤ_[p]) = φ (n • (1 : ℤ_[p])) := by rw [zsmul_one]
        _ = n • φ 1 := map_zsmul φ n 1
        _ = PadicInt.toZModPow k (n : ℤ_[p]) * φ 1 := by simp [zsmul_eq_mul])
  exact congrFun h x

end ContinuousAddMonoidHom

namespace PadicInt

variable {p : ℕ} [Fact p.Prime] (k : ℕ)

/-- Evaluation at `1` identifies the continuous additive characters of `ℤ_[p]` modulo `p ^ k`
with the coefficient group. Its inverse multiplies the truncation map by the chosen value. -/
noncomputable def continuousAddHomZModPowEquiv :
    (ℤ_[p] →ₜ+ ZMod (p ^ k)) ≃+ ZMod (p ^ k) where
  toFun φ := φ 1
  invFun a :=
    { toFun := fun x ↦ toZModPow k x * a
      map_zero' := by simp
      map_add' := fun x y ↦ by simp [add_mul]
      continuous_toFun := (continuous_toZModPow k).mul continuous_const }
  left_inv φ := by
    ext x
    exact (φ.padicInt_apply_eq_toZModPow_mul_apply_one x).symm
  right_inv a := (congrArg (· * a) (map_one (toZModPow k))).trans (one_mul a)
  map_add' φ ψ := by simp

/-- The character equivalence evaluates a homomorphism at `1`. -/
@[simp] theorem continuousAddHomZModPowEquiv_apply (φ : ℤ_[p] →ₜ+ ZMod (p ^ k)) :
    continuousAddHomZModPowEquiv k φ = φ 1 := (rfl)

/-- The character with parameter `a` sends `x` to its truncation multiplied by `a`. -/
-- The inverse formulas simplify before argument normalization changes the exponent presentation.
@[simp↓]
theorem continuousAddHomZModPowEquiv_symm_apply (a : ZMod (p ^ k)) (x : ℤ_[p]) :
    (continuousAddHomZModPowEquiv k).symm a x = toZModPow k x * a := (rfl)

/-- Reduction of the coefficient of a character agrees with reducing all its values.
In particular the evaluation descriptions are compatible for every pair of exponents,
including reduction to modulus `1`. -/
theorem castHom_continuousAddHomZModPowEquiv_symm_apply (m n : ℕ) (h : m ≤ n)
    (a : ZMod (p ^ n)) (x : ℤ_[p]) :
    ZMod.castHom (pow_dvd_pow p h) (ZMod (p ^ m))
        ((continuousAddHomZModPowEquiv n).symm a x) =
      (continuousAddHomZModPowEquiv m).symm
        (ZMod.castHom (pow_dvd_pow p h) (ZMod (p ^ m)) a) x := by
  simp only [continuousAddHomZModPowEquiv_symm_apply, map_mul]
  rw [← RingHom.comp_apply, zmod_cast_comp_toZModPow m n h]

end PadicInt

namespace TauCeti.continuousZModDual

variable {p : ℕ} [Fact p.Prime] {k : ℕ}

/-- A continuous character of the multiplicatively written p-adic integers is determined
by its value at the additive generator `1`. -/
theorem padicInt_apply_eq_toZModPow_mul_eval_one
    (χ : continuousZModDual (p ^ k) (Multiplicative ℤ_[p])) (x : ℤ_[p]) :
    Multiplicative.toAdd (χ.toMul (Multiplicative.ofAdd x)) =
      PadicInt.toZModPow k x * evalₗ (Multiplicative.ofAdd (1 : ℤ_[p])) χ := by
  let φ : ℤ_[p] →ₜ+ ZMod (p ^ k) :=
    ⟨χ.toMul.toMonoidHom.toAdditive,
      continuous_toAdd.comp (χ.toMul.continuous.comp continuous_ofAdd)⟩
  rw [evalₗ_apply]
  exact φ.padicInt_apply_eq_toZModPow_mul_apply_one x

end TauCeti.continuousZModDual

namespace PadicInt

variable {p : ℕ} [Fact p.Prime] (k : ℕ)

/-- Evaluation at the additive generator `1` identifies the continuous `ZMod (p ^ k)`-dual
of `ℤ_[p]` with its coefficient ring, as modules. -/
noncomputable def continuousZModDualEquiv :
    TauCeti.continuousZModDual (p ^ k) (Multiplicative ℤ_[p]) ≃ₗ[ZMod (p ^ k)] ZMod (p ^ k) :=
  LinearEquiv.ofBijective
    (TauCeti.continuousZModDual.evalₗ (Multiplicative.ofAdd (1 : ℤ_[p]))) (by
      constructor
      · intro χ ψ h
        apply Additive.toMul.injective
        ext x
        obtain ⟨x, rfl⟩ := Multiplicative.ofAdd.surjective x
        apply Multiplicative.toAdd.injective
        rw [TauCeti.continuousZModDual.padicInt_apply_eq_toZModPow_mul_eval_one,
          TauCeti.continuousZModDual.padicInt_apply_eq_toZModPow_mul_eval_one, h]
      · intro a
        let φ := (continuousAddHomZModPowEquiv (p := p) k).symm a
        refine ⟨Additive.ofMul
          ⟨φ.toAddMonoidHom.toMultiplicative,
            continuous_ofAdd.comp (φ.continuous.comp continuous_toAdd)⟩, ?_⟩
        rw [TauCeti.continuousZModDual.evalₗ_apply]
        simp only [toMul_ofMul]
        -- The bundled character evaluates by the defining type-tag conversion of `φ`.
        change φ 1 = a
        simpa only [continuousAddHomZModPowEquiv_apply] using
          (continuousAddHomZModPowEquiv k).apply_symm_apply a)

/-- The module equivalence evaluates a continuous character at the additive generator `1`. -/
@[simp] theorem continuousZModDualEquiv_apply
    (χ : TauCeti.continuousZModDual (p ^ k) (Multiplicative ℤ_[p])) :
    continuousZModDualEquiv k χ =
      Multiplicative.toAdd (χ.toMul (Multiplicative.ofAdd (1 : ℤ_[p]))) := by
  rw [← TauCeti.continuousZModDual.evalₗ_apply]
  rfl

/-- The inverse dual equivalence gives the character obtained by multiplying truncation by
the chosen coefficient. -/
@[simp↓]
theorem continuousZModDualEquiv_symm_apply (a : ZMod (p ^ k)) (x : ℤ_[p]) :
    Multiplicative.toAdd (((continuousZModDualEquiv k).symm a).toMul
      (Multiplicative.ofAdd x)) = toZModPow k x * a := by
  rw [TauCeti.continuousZModDual.padicInt_apply_eq_toZModPow_mul_eval_one]
  exact congrArg (toZModPow k x * ·) ((continuousZModDualEquiv k).apply_symm_apply a)

end PadicInt
