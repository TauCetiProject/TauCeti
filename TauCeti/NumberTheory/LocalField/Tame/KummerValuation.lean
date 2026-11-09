/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.Tame.PadicCharacter

/-!
# Valuations and Kummer characters on inertia

For an element `a` of a nonarchimedean local field, its Kummer character on inertia is
`t(σ) ^ v(a)`, where `t` is the tame character and `v` is the normalized additive valuation.
This holds at every prime-to-residue-characteristic level and in the prime-to-`p` inverse limit.
The `ℓ`-adic version is `v(a) • t_ℓ(σ)` in `ℤ_ℓ(1)`.

In particular this computes the inertia action on roots of a Tate parameter: the unit part of
the parameter contributes nothing, and its valuation is the coefficient of tame monodromy.
The `ℓ`-adic character is trivial exactly when the valuation is zero, even when that valuation
is divisible by `ℓ`; no single finite torsion level detects all nonzero valuations.

## References

* J.-P. Serre, *Corps Locaux*, Chapter IV, §2.
* J. Silverman, *Advanced Topics in the Arithmetic of Elliptic Curves*, V.6.
-/

public section

noncomputable section

namespace TauCeti

open _root_.ValuativeRel

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- The tame Kummer character respects integer powers of its argument. -/
@[simp]
theorem tameKummerCharacter_zpow (a : Kˣ) (n : ℤ) :
    tameKummerCharacter K (a ^ n) = tameKummerCharacter K a ^ n := by
  cases n <;> simp [zpow_natCast, zpow_negSucc]

/-- The tame Kummer character of `a` is the normalized valuation of `a` times the tame
character, written multiplicatively. -/
theorem tameKummerCharacter_eq_inertiaTameCharacter_zpow (a : Kˣ) :
    tameKummerCharacter K a = inertiaTameCharacter K ^ (normalizedValuation K a).toAdd := by
  obtain ⟨π, hπ⟩ := exists_isUniformizer K
  have hu := tameKummerCharacter_eq_one_of_mem_unitFiltration_zero
    (mul_zpow_neg_mem_unitFiltration_zero ((isUniformizer_def π).1 hπ) a)
  have ha : a = (a * π ^ (-(normalizedValuation K a).toAdd)) *
      π ^ (normalizedValuation K a).toAdd := by group
  calc
    tameKummerCharacter K a = tameKummerCharacter K
        (a * π ^ (-(normalizedValuation K a).toAdd)) *
        tameKummerCharacter K (π ^ (normalizedValuation K a).toAdd) := by
      rw [← tameKummerCharacter_mul, ← ha]
    _ = inertiaTameCharacter K ^ (normalizedValuation K a).toAdd := by
      rw [hu, one_mul, tameKummerCharacter_zpow,
        ← inertiaTameCharacter_eq_tameKummerCharacter hπ]

/-- At level `m`, inertia acts on the `m`-th roots of `a` by the valuation power of the
level-`m` tame character. -/
theorem inertiaKummerCharacter_apply_eq_proj_zpow {m : ℕ}
    (hm : m.Coprime (ringChar 𝓀[K])) (a : Kˣ) (σ : inertiaSubgroup K) :
    inertiaKummerCharacter K m hm a σ =
      PrimeToPTateModule.proj ⟨m, ne_zero_of_coprime_ringChar hm, hm⟩
        (inertiaTameCharacter K σ) ^ (normalizedValuation K a).toAdd := by
  calc
    _ = PrimeToPTateModule.proj ⟨m, ne_zero_of_coprime_ringChar hm, hm⟩
        (tameKummerCharacter K a σ) :=
      (proj_tameKummerCharacter_apply a ⟨m, ne_zero_of_coprime_ringChar hm, hm⟩ σ).symm
    _ = _ := by
      rw [tameKummerCharacter_eq_inertiaTameCharacter_zpow,
        ContinuousMonoidHom.zpow_apply, map_zpow]

variable (K) in
/-- The `ℓ`-adic Kummer character of `a` on inertia, with values in the multiplicatively
written Tate twist. Its finite components are `σ(α)/α` for `α ^ (ℓ ^ n) = a`. -/
def inertiaPadicKummerCharacter {ℓ : ℕ} (hℓ : ℓ.Coprime (ringChar 𝓀[K])) (a : Kˣ) :
    inertiaSubgroup K →ₜ* Multiplicative (PadicTateTwist ℓ (AlgebraicClosure K)) :=
  have : NeZero ℓ := ⟨ne_zero_of_coprime_ringChar hℓ⟩
  (PrimeToPTateModule.toPadicTateTwist ℓ hℓ).comp (tameKummerCharacter K a)

variable {ℓ : ℕ} (hℓ : ℓ.Coprime (ringChar 𝓀[K]))

/-- Projection of the `ℓ`-adic Kummer character recovers the finite Kummer character. -/
@[simp]
theorem proj_inertiaPadicKummerCharacter (a : Kˣ) (σ : inertiaSubgroup K) (n : ℕ) :
    PadicTateTwist.proj n (inertiaPadicKummerCharacter K hℓ a σ).toAdd =
      Additive.ofMul (inertiaKummerCharacter K (ℓ ^ n) (hℓ.pow_left n) a σ) := by
  have : NeZero ℓ := ⟨ne_zero_of_coprime_ringChar hℓ⟩
  simp only [inertiaPadicKummerCharacter, ContinuousMonoidHom.coe_comp, Function.comp_apply,
    PrimeToPTateModule.proj_toPadicTateTwist]
  exact congrArg Additive.ofMul
    (proj_tameKummerCharacter_apply a ⟨ℓ ^ n, pow_ne_zero n (NeZero.ne ℓ), hℓ.pow_left n⟩ σ)

/-- The `ℓ`-adic Kummer character is the valuation power of the `ℓ`-adic tame character. -/
theorem inertiaPadicKummerCharacter_eq_zpow (a : Kˣ) :
    inertiaPadicKummerCharacter K hℓ a =
      inertiaPadicTameCharacter K hℓ ^ (normalizedValuation K a).toAdd := by
  have : NeZero ℓ := ⟨ne_zero_of_coprime_ringChar hℓ⟩
  apply ContinuousMonoidHom.ext
  intro σ
  simp only [inertiaPadicKummerCharacter, ContinuousMonoidHom.coe_comp, Function.comp_apply,
    tameKummerCharacter_eq_inertiaTameCharacter_zpow, ContinuousMonoidHom.zpow_apply, map_zpow,
    inertiaPadicTameCharacter_apply]

/-- In additive notation the Kummer character on inertia is `v(a) • t_ℓ`. -/
theorem inertiaPadicKummerCharacter_toAdd (a : Kˣ) (σ : inertiaSubgroup K) :
    (inertiaPadicKummerCharacter K hℓ a σ).toAdd =
      (normalizedValuation K a).toAdd • (inertiaPadicTameCharacter K hℓ σ).toAdd := by
  rw [inertiaPadicKummerCharacter_eq_zpow, ContinuousMonoidHom.zpow_apply,
    toAdd_zpow]

/-- The `ℓ`-adic Kummer character, computed on any root of the parameter. -/
theorem coe_proj_inertiaPadicKummerCharacter_apply {σ : Gal(AlgebraicClosure K/K)}
    (hσ : σ ∈ inertiaSubgroup K) {a : Kˣ} (n : ℕ) {α : AlgebraicClosure K}
    (hα : α ^ ℓ ^ n = algebraMap K (AlgebraicClosure K) a) :
    (((PadicTateTwist.proj n (inertiaPadicKummerCharacter K hℓ a ⟨σ, hσ⟩).toAdd).toMul :
      (AlgebraicClosure K)ˣ) : AlgebraicClosure K) = σ α / α := by
  rw [proj_inertiaPadicKummerCharacter]
  exact coe_inertiaKummerCharacter_apply hσ hα

/-- The image of the `ℓ`-adic Kummer character is exactly `v(a) ℤ_ℓ(1)`, written
multiplicatively. -/
theorem range_inertiaPadicKummerCharacter (a : Kˣ) :
    Set.range (inertiaPadicKummerCharacter K hℓ a) =
      Set.range (fun x : Multiplicative (PadicTateTwist ℓ (AlgebraicClosure K)) ↦
        x ^ (normalizedValuation K a).toAdd) := by
  rw [inertiaPadicKummerCharacter_eq_zpow]
  have hf : ⇑(inertiaPadicTameCharacter K hℓ ^ (normalizedValuation K a).toAdd) =
      (fun x ↦ x ^ (normalizedValuation K a).toAdd) ∘ inertiaPadicTameCharacter K hℓ :=
    funext fun σ ↦ ContinuousMonoidHom.zpow_apply _ _ _
  rw [hf]
  exact (inertiaPadicTameCharacter_surjective K hℓ).range_comp _

/-- Wild inertia acts trivially on every prime-to-residue-characteristic Kummer tower. -/
theorem inertiaPadicKummerCharacter_eq_one_of_mem_wildInertiaSubgroup (a : Kˣ)
    {σ : Gal(AlgebraicClosure K/K)} (hσ : σ ∈ inertiaSubgroup K)
    (hw : σ ∈ wildInertiaSubgroup K) :
    inertiaPadicKummerCharacter K hℓ a ⟨σ, hσ⟩ = 1 := by
  rw [inertiaPadicKummerCharacter_eq_zpow, ContinuousMonoidHom.zpow_apply,
    inertiaPadicTameCharacter_eq_one_of_mem_wildInertiaSubgroup hσ hw, one_zpow]

/-- The Kummer character of the trivial parameter is trivial. -/
@[simp]
theorem inertiaPadicKummerCharacter_one :
    inertiaPadicKummerCharacter K hℓ (1 : Kˣ) = 1 := by
  rw [inertiaPadicKummerCharacter_eq_zpow, map_one, toAdd_one, zpow_zero]

/-- Kummer characters multiply when their parameters multiply. -/
@[simp]
theorem inertiaPadicKummerCharacter_mul (a b : Kˣ) :
    inertiaPadicKummerCharacter K hℓ (a * b) =
      inertiaPadicKummerCharacter K hℓ a * inertiaPadicKummerCharacter K hℓ b := by
  simp only [inertiaPadicKummerCharacter_eq_zpow, map_mul, toAdd_mul, zpow_add]

/-- A prime-to-residue-characteristic `ℓ`-adic Kummer tower is unramified exactly when its
parameter has valuation zero. Divisibility of the valuation by `ℓ` does not suffice. -/
@[simp]
theorem inertiaPadicKummerCharacter_eq_one_iff [Fact ℓ.Prime] (a : Kˣ) :
    inertiaPadicKummerCharacter K hℓ a = 1 ↔ (normalizedValuation K a).toAdd = 0 := by
  have hp := CharP.prime_ringChar 𝓀[K]
  have hroots (n : ℕ) : HasEnoughRootsOfUnity (AlgebraicClosure K) (ℓ ^ n) := by
    have : NeZero (((ℓ ^ n : ℕ) : K)) := ⟨natCast_ne_zero_of_isUnit
      (IsLocalRing.isUnit_natCast_iff_not_dvd.2
        (hp.coprime_iff_not_dvd.1 (hℓ.pow_left n).symm))⟩
    infer_instance
  let := hroots
  obtain ⟨e⟩ := PadicTateTwist.nonempty_linearEquiv ℓ (AlgebraicClosure K)
  constructor
  · intro h
    obtain ⟨σ, hσ⟩ := inertiaPadicTameCharacter_surjective K hℓ
      (Multiplicative.ofAdd (e.symm 1))
    have hz := inertiaPadicKummerCharacter_toAdd hℓ a σ
    have hzero : (inertiaPadicKummerCharacter K hℓ a σ).toAdd = 0 :=
      congrArg (fun f : inertiaSubgroup K →ₜ* Multiplicative
        (PadicTateTwist ℓ (AlgebraicClosure K)) ↦ (f σ).toAdd) h
    rw [hzero, hσ, toAdd_ofAdd] at hz
    have he := congrArg e hz
    simpa using he.symm
  · intro h
    rw [inertiaPadicKummerCharacter_eq_zpow, h, zpow_zero]

end TauCeti
