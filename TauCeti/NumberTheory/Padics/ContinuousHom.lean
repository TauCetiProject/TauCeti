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

Evaluation at `1` identifies the continuous additive homomorphisms from `ℤ_[p]` to a Hausdorff
topological `ℤ_[p]`-module `A`, such as `ℤ_[p]` or `ℚ_[p]`, with `A`
(`PadicInt.continuousAddHomEquiv`): the homomorphism with value `a` at `1` is `x ↦ x • a`.
Density of the ordinary integers gives uniqueness; continuity of scalar multiplication gives
existence.

Viewing `ZMod (p ^ k)` as a discrete `ℤ_[p]`-module through the truncation map specialises this
to the continuous additive characters of `ℤ_[p]` modulo `p ^ k`: the character with value `a` at
`1` is `x ↦ PadicInt.toZModPow k x * a`. The exponent `k` may be zero.

The multiplicative encoding identifies the continuous `ZMod (p ^ k)`-dual with the
coefficient ring as a module. This is the coefficient calculation for first continuous cohomology
with trivial action, developed in `TauCeti.NumberTheory.Padics.Cohomology`.
-/

public section

/-! ### Continuous homomorphisms into a topological `ℤ_[p]`-module -/

namespace ContinuousAddMonoidHom

variable {p : ℕ} [Fact p.Prime] {A : Type*} [AddCommGroup A] [Module ℤ_[p] A]
  [TopologicalSpace A] [T2Space A] [ContinuousSMul ℤ_[p] A]

/-- A continuous additive homomorphism from `ℤ_[p]` to a Hausdorff topological `ℤ_[p]`-module is
scalar multiplication on its value at `1`: both sides are continuous and agree on the dense
image of `ℤ`. -/
theorem padicInt_apply_eq_smul_apply_one (φ : ℤ_[p] →ₜ+ A) (x : ℤ_[p]) :
    φ x = x • φ 1 := by
  have hcont : Continuous (fun x : ℤ_[p] ↦ x • φ 1) := continuous_id.smul continuous_const
  have h := PadicInt.denseRange_intCast.equalizer φ.continuous hcont
    (funext fun n ↦ by
      calc
        φ (n : ℤ_[p]) = φ (n • (1 : ℤ_[p])) := by rw [zsmul_one]
        _ = n • φ 1 := map_zsmul φ n 1
        _ = (n : ℤ_[p]) • φ 1 := (Int.cast_smul_eq_zsmul ℤ_[p] n (φ 1)).symm)
  exact congrFun h x

end ContinuousAddMonoidHom

namespace PadicInt

variable {p : ℕ} [Fact p.Prime] (A : Type*) [AddCommGroup A] [Module ℤ_[p] A]
  [TopologicalSpace A] [IsTopologicalAddGroup A] [T2Space A] [ContinuousSMul ℤ_[p] A]

/-- Evaluation at `1` identifies the continuous additive homomorphisms from `ℤ_[p]` to a
Hausdorff topological `ℤ_[p]`-module `A` with `A`. Its inverse sends `a` to `x ↦ x • a`. -/
noncomputable def continuousAddHomEquiv : (ℤ_[p] →ₜ+ A) ≃+ A where
  toFun φ := φ 1
  invFun a := (ContinuousLinearMap.toSpanSingleton ℤ_[p] a : ℤ_[p] →ₜ+ A)
  left_inv φ := by
    ext x
    exact (φ.padicInt_apply_eq_smul_apply_one x).symm
  right_inv a := ContinuousLinearMap.toSpanSingleton_apply_one ℤ_[p] a
  map_add' _ _ := (rfl)

/-- The equivalence evaluates a homomorphism at `1`. -/
@[simp] theorem continuousAddHomEquiv_apply (φ : ℤ_[p] →ₜ+ A) :
    continuousAddHomEquiv A φ = φ 1 := (rfl)

/-- The homomorphism with value `a` at `1` is `x ↦ x • a`. -/
@[simp] theorem continuousAddHomEquiv_symm_apply (a : A) (x : ℤ_[p]) :
    (continuousAddHomEquiv (p := p) A).symm a x = x • a := (rfl)

end PadicInt

/-! ### Characters modulo `p ^ k` -/

namespace ContinuousAddMonoidHom

variable {p : ℕ} [Fact p.Prime] {k : ℕ}

/-- A continuous character of the p-adic integers modulo `p ^ k` is the truncation map
multiplied by its value at `1`. -/
theorem padicInt_apply_eq_toZModPow_mul_apply_one
    (φ : ℤ_[p] →ₜ+ ZMod (p ^ k)) (x : ℤ_[p]) :
    φ x = PadicInt.toZModPow k x * φ 1 := by
  let := (PadicInt.toZModPow (p := p) k).toModule
  have : ContinuousSMul ℤ_[p] (ZMod (p ^ k)) :=
    ⟨((PadicInt.continuous_toZModPow k).comp continuous_fst).mul continuous_snd⟩
  exact φ.padicInt_apply_eq_smul_apply_one x

end ContinuousAddMonoidHom

namespace PadicInt

variable {p : ℕ} [Fact p.Prime] (k : ℕ)

/-- Evaluation at `1` identifies the continuous additive characters of `ℤ_[p]` modulo `p ^ k`
with the coefficient group. Its inverse multiplies the truncation map by the chosen value. -/
noncomputable def continuousAddHomZModPowEquiv :
    (ℤ_[p] →ₜ+ ZMod (p ^ k)) ≃+ ZMod (p ^ k) :=
  letI := (toZModPow (p := p) k).toModule
  haveI : ContinuousSMul ℤ_[p] (ZMod (p ^ k)) :=
    ⟨((continuous_toZModPow k).comp continuous_fst).mul continuous_snd⟩
  continuousAddHomEquiv (ZMod (p ^ k))

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
