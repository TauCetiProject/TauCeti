/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Oscillatory asymptotic decay

This file defines the predicate `TauCeti.HasOscillatoryDecay c p α₀ f`, expressing that a real
function `f : ℝ → ℝ` decomposes at `+∞` to every polynomial order `B` into a finite linear
combination of power-damped oscillations `t ^ (-α i) * cos (c * t ^ p)` and
`t ^ (-α i) * sin (c * t ^ p)` with `α₀ ≤ α i`, up to an `O(t ^ (-B))` remainder.

The fixed-order decomposition is packaged as `TauCeti.HasOscillatoryDecayAt c p α₀ B f`, and
`TauCeti.HasOscillatoryDecay` is defined as `∀ B, HasOscillatoryDecayAt c p α₀ B f`. This
class covers Fresnel (`p = 2, α₀ = 0`), negative-argument Airy (`c = 2 / 3, p = 3 / 2, α₀ = 1 / 4`),
and Bessel (`p = 1, α₀ = 1 / 2`) asymptotics.

## Main declarations

* `TauCeti.HasOscillatoryDecayAt`: fixed-order oscillatory decomposition up to `O(t ^ (-B))`.
* `TauCeti.HasOscillatoryDecay`, `TauCeti.hasOscillatoryDecay_iff`, and
  `TauCeti.hasOscillatoryDecay_def`: all-orders oscillatory asymptotic decay predicate and its
  characterizations.
* `TauCeti.HasOscillatoryDecay.of_asymptoticExpansion`: criterion from a Poincaré oscillatory
  asymptotic series.
* `TauCeti.HasOscillatoryDecay.isBigO_rpow_neg`: leading amplitude bound `O(t ^ (-α₀))`.
* Algebraic and mode-construction lemmas: `of_isBigO`, `zero`, `congr_atTop`, `mono`, `const_mul`,
  `neg`, `add`, `sub`, `sum`, `rpow_mul_cos`, `rpow_mul_sin`, `rpow_mul_cos_add`,
  `rpow_mul_sin_add`.

## References

* F. W. J. Olver, *Asymptotics and Special Functions*, Academic Press, 1974.
* NIST Digital Library of Mathematical Functions, §9.10(v).
-/

public section

namespace TauCeti

open Asymptotics Filter

/-- Single-threshold oscillatory decomposition of phase `c * t ^ p` and leading damping `α₀` up to
remainder `O(t ^ (-B))`: `f` agrees eventually at `+∞` with a finite linear combination of modes
`t ^ (-α i) * cos (c * t ^ p)` and `t ^ (-α i) * sin (c * t ^ p)` with `α₀ ≤ α i`, plus a
remainder `r =O[atTop] fun t ↦ t ^ (-B)`. -/
def HasOscillatoryDecayAt (c p α₀ B : ℝ) (f : ℝ → ℝ) : Prop :=
  ∃ (k : ℕ) (α u v : Fin k → ℝ) (r : ℝ → ℝ),
    (∀ i, α₀ ≤ α i) ∧ r =O[atTop] (fun t : ℝ ↦ t ^ (-B)) ∧
    f =ᶠ[atTop] fun t ↦
      (∑ i, (u i * (t ^ (-α i) * Real.cos (c * t ^ p)) +
        v i * (t ^ (-α i) * Real.sin (c * t ^ p)))) + r t

/-- **Asymptotic oscillatory decay of phase `c * t ^ p` and leading damping `α₀`.**
A function `f : ℝ → ℝ` satisfies `HasOscillatoryDecay c p α₀ f` if to every polynomial order `B`
it decomposes at `+∞` into a finite linear combination of power-damped oscillations
`t ^ (-α i) * cos (c * t ^ p)` and `t ^ (-α i) * sin (c * t ^ p)` with `α₀ ≤ α i`, plus an
`O(t ^ (-B))` remainder. This class includes Fresnel (`p = 2, α₀ = 0`), negative-argument Airy
(`c = 2 / 3, p = 3 / 2, α₀ = 1 / 4`), and half-integer/general Bessel (`p = 1, α₀ = 1 / 2`)
oscillations. -/
def HasOscillatoryDecay (c p α₀ : ℝ) (f : ℝ → ℝ) : Prop :=
  ∀ B : ℝ, HasOscillatoryDecayAt c p α₀ B f

/-- Characterization of `TauCeti.HasOscillatoryDecay` via the single-threshold predicate
`TauCeti.HasOscillatoryDecayAt`. -/
theorem hasOscillatoryDecay_iff {c p α₀ : ℝ} {f : ℝ → ℝ} :
    HasOscillatoryDecay c p α₀ f ↔ ∀ B, HasOscillatoryDecayAt c p α₀ B f :=
  Iff.rfl

/-- Defining equivalence of `TauCeti.HasOscillatoryDecay`. -/
theorem hasOscillatoryDecay_def {c p α₀ : ℝ} {f : ℝ → ℝ} :
    HasOscillatoryDecay c p α₀ f ↔
      ∀ B : ℝ, ∃ (k : ℕ) (α u v : Fin k → ℝ) (r : ℝ → ℝ),
        (∀ i, α₀ ≤ α i) ∧ r =O[atTop] (fun t : ℝ ↦ t ^ (-B)) ∧
        f =ᶠ[atTop] fun t ↦
          (∑ i, (u i * (t ^ (-α i) * Real.cos (c * t ^ p)) +
            v i * (t ^ (-α i) * Real.sin (c * t ^ p)))) + r t :=
  Iff.rfl

namespace HasOscillatoryDecayAt

/-- Any function that is `O(t ^ (-B))` at `+∞` satisfies `HasOscillatoryDecayAt c p α₀ B`. -/
theorem of_isBigO {c p α₀ B : ℝ} {f : ℝ → ℝ}
    (hf : f =O[atTop] fun t : ℝ ↦ t ^ (-B)) : HasOscillatoryDecayAt c p α₀ B f :=
  ⟨0, Fin.elim0, Fin.elim0, Fin.elim0, f, fun i ↦ i.elim0, hf, by simp⟩

/-- `HasOscillatoryDecayAt` depends only on the eventual germ of `f` at `+∞`. -/
theorem congr_atTop {c p α₀ B : ℝ} {f g : ℝ → ℝ}
    (hf : HasOscillatoryDecayAt c p α₀ B f) (hfg : f =ᶠ[atTop] g) :
    HasOscillatoryDecayAt c p α₀ B g := by
  obtain ⟨k, α, u, v, r, hα, hr, heq⟩ := hf
  exact ⟨k, α, u, v, r, hα, hr, hfg.symm.trans heq⟩

/-- Lowering the leading damping threshold `α₀` preserves `HasOscillatoryDecayAt`. -/
theorem mono {c p α₀ α₁ B : ℝ} {f : ℝ → ℝ}
    (hf : HasOscillatoryDecayAt c p α₀ B f) (hα : α₁ ≤ α₀) :
    HasOscillatoryDecayAt c p α₁ B f := by
  obtain ⟨k, α, u, v, r, hαi, hr, heq⟩ := hf
  exact ⟨k, α, u, v, r, fun i ↦ hα.trans (hαi i), hr, heq⟩

/-- Multiplication by a constant preserves `HasOscillatoryDecayAt`. -/
theorem const_mul {c p α₀ B : ℝ} {f : ℝ → ℝ}
    (hf : HasOscillatoryDecayAt c p α₀ B f) (d : ℝ) :
    HasOscillatoryDecayAt c p α₀ B (fun t ↦ d * f t) := by
  obtain ⟨k, α, u, v, r, hα, hr, heq⟩ := hf
  refine ⟨k, α, fun i ↦ d * u i, fun i ↦ d * v i, fun t ↦ d * r t, hα, hr.const_mul_left d, ?_⟩
  filter_upwards [heq] with t ht
  rw [ht, mul_add, Finset.mul_sum]
  exact congrArg (· + d * r t) (Finset.sum_congr rfl fun _ _ ↦ by ring)

/-- Addition preserves `HasOscillatoryDecayAt`. -/
theorem add {c p α₀ B : ℝ} {f g : ℝ → ℝ}
    (hf : HasOscillatoryDecayAt c p α₀ B f) (hg : HasOscillatoryDecayAt c p α₀ B g) :
    HasOscillatoryDecayAt c p α₀ B (f + g) := by
  obtain ⟨k₁, α₁, u₁, v₁, r₁, hα₁, hr₁, heq₁⟩ := hf
  obtain ⟨k₂, α₂, u₂, v₂, r₂, hα₂, hr₂, heq₂⟩ := hg
  refine ⟨k₁ + k₂, Fin.append α₁ α₂, Fin.append u₁ u₂, Fin.append v₁ v₂, r₁ + r₂,
    Fin.addCases (fun i ↦ by simpa [Fin.append_left] using hα₁ i)
      (fun i ↦ by simpa [Fin.append_right] using hα₂ i), hr₁.add hr₂, ?_⟩
  filter_upwards [heq₁, heq₂] with t ht₁ ht₂
  simp only [Pi.add_apply, ht₁, ht₂, Fin.sum_univ_add, Fin.append_left, Fin.append_right]; ring

/-- Finite sums preserve `HasOscillatoryDecayAt`. -/
theorem sum {ι : Type*} {s : Finset ι} {c p α₀ B : ℝ}
    {F : ι → ℝ → ℝ} (hF : ∀ j ∈ s, HasOscillatoryDecayAt c p α₀ B (F j)) :
    HasOscillatoryDecayAt c p α₀ B (fun t ↦ ∑ j ∈ s, F j t) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using of_isBigO (isBigO_zero (fun t : ℝ ↦ t ^ (-B)) atTop)
  | insert j₀ s hj₀ ih =>
    have hsplit : (fun t ↦ ∑ j ∈ insert j₀ s, F j t) = F j₀ + fun t ↦ ∑ j ∈ s, F j t := by
      ext t; exact Finset.sum_insert hj₀
    rw [hsplit]
    exact (hF j₀ (Finset.mem_insert_self j₀ s)).add
      (ih fun j hj ↦ hF j (Finset.mem_insert_of_mem hj))

/-- Single linear combination of cosine and sine modes with damping `α ≥ α₀` satisfies
`HasOscillatoryDecayAt`. -/
theorem rpow_mul_cos_add_sin {c p α₀ α B : ℝ} (u v : ℝ) (hα : α₀ ≤ α) :
    HasOscillatoryDecayAt c p α₀ B
      (fun t ↦ u * (t ^ (-α) * Real.cos (c * t ^ p)) + v * (t ^ (-α) * Real.sin (c * t ^ p))) :=
  ⟨1, fun _ ↦ α, fun _ ↦ u, fun _ ↦ v, 0, fun _ ↦ hα, isBigO_zero _ _, by simp⟩

end HasOscillatoryDecayAt

namespace HasOscillatoryDecay

/-- Any function decaying faster than every power of `t` at `+∞` has `HasOscillatoryDecay c p α₀`
for all `c, p, α₀`. -/
theorem of_isBigO {c p α₀ : ℝ} {f : ℝ → ℝ}
    (hf : ∀ B : ℝ, f =O[atTop] fun t : ℝ ↦ t ^ (-B)) : HasOscillatoryDecay c p α₀ f :=
  hasOscillatoryDecay_iff.mpr fun B ↦ HasOscillatoryDecayAt.of_isBigO (hf B)

/-- The zero function satisfies `HasOscillatoryDecay c p α₀`. -/
@[simp]
theorem zero (c p α₀ : ℝ) : HasOscillatoryDecay c p α₀ 0 :=
  of_isBigO fun _ ↦ isBigO_zero _ _

/-- `HasOscillatoryDecay` depends only on the eventual germ of `f` at `+∞`. -/
theorem congr_atTop {c p α₀ : ℝ} {f g : ℝ → ℝ}
    (hf : HasOscillatoryDecay c p α₀ f) (hfg : f =ᶠ[atTop] g) :
    HasOscillatoryDecay c p α₀ g :=
  hasOscillatoryDecay_iff.mpr fun B ↦ (hasOscillatoryDecay_iff.mp hf B).congr_atTop hfg

/-- Lowering the leading damping threshold `α₀` preserves `HasOscillatoryDecay`. -/
theorem mono {c p α₀ α₁ : ℝ} {f : ℝ → ℝ}
    (hf : HasOscillatoryDecay c p α₀ f) (hα : α₁ ≤ α₀) :
    HasOscillatoryDecay c p α₁ f :=
  hasOscillatoryDecay_iff.mpr fun B ↦ (hasOscillatoryDecay_iff.mp hf B).mono hα

/-- Multiplication by a constant preserves `HasOscillatoryDecay`. -/
theorem const_mul {c p α₀ : ℝ} {f : ℝ → ℝ}
    (hf : HasOscillatoryDecay c p α₀ f) (d : ℝ) :
    HasOscillatoryDecay c p α₀ (fun t ↦ d * f t) :=
  hasOscillatoryDecay_iff.mpr fun B ↦ (hasOscillatoryDecay_iff.mp hf B).const_mul d

/-- Negation preserves `HasOscillatoryDecay`. -/
theorem neg {c p α₀ : ℝ} {f : ℝ → ℝ} (hf : HasOscillatoryDecay c p α₀ f) :
    HasOscillatoryDecay c p α₀ (-f) :=
  (hf.const_mul (-1)).congr_atTop (Eventually.of_forall fun _ ↦ by simp)

/-- Addition preserves `HasOscillatoryDecay`. -/
theorem add {c p α₀ : ℝ} {f g : ℝ → ℝ}
    (hf : HasOscillatoryDecay c p α₀ f) (hg : HasOscillatoryDecay c p α₀ g) :
    HasOscillatoryDecay c p α₀ (f + g) :=
  hasOscillatoryDecay_iff.mpr fun B ↦
    (hasOscillatoryDecay_iff.mp hf B).add (hasOscillatoryDecay_iff.mp hg B)

/-- Subtraction preserves `HasOscillatoryDecay`. -/
theorem sub {c p α₀ : ℝ} {f g : ℝ → ℝ}
    (hf : HasOscillatoryDecay c p α₀ f) (hg : HasOscillatoryDecay c p α₀ g) :
    HasOscillatoryDecay c p α₀ (f - g) := by
  rw [sub_eq_add_neg]; exact hf.add hg.neg

/-- Finite sums preserve `HasOscillatoryDecay`. -/
theorem sum {ι : Type*} {s : Finset ι} {c p α₀ : ℝ} {F : ι → ℝ → ℝ}
    (hF : ∀ j ∈ s, HasOscillatoryDecay c p α₀ (F j)) :
    HasOscillatoryDecay c p α₀ (fun t ↦ ∑ j ∈ s, F j t) :=
  hasOscillatoryDecay_iff.mpr fun B ↦
    HasOscillatoryDecayAt.sum fun j hj ↦ hasOscillatoryDecay_iff.mp (hF j hj) B

/-- Single cosine mode `t ↦ t ^ (-α) * cos (c * t ^ p)` with `α₀ ≤ α`. -/
theorem rpow_mul_cos {c p α₀ α : ℝ} (hα : α₀ ≤ α) :
    HasOscillatoryDecay c p α₀ (fun t ↦ t ^ (-α) * Real.cos (c * t ^ p)) :=
  hasOscillatoryDecay_iff.mpr fun B ↦ (HasOscillatoryDecayAt.rpow_mul_cos_add_sin
    (c := c) (p := p) (B := B) 1 0 hα).congr_atTop (Eventually.of_forall fun _ ↦ by simp)

/-- Single sine mode `t ↦ t ^ (-α) * sin (c * t ^ p)` with `α₀ ≤ α`. -/
theorem rpow_mul_sin {c p α₀ α : ℝ} (hα : α₀ ≤ α) :
    HasOscillatoryDecay c p α₀ (fun t ↦ t ^ (-α) * Real.sin (c * t ^ p)) :=
  hasOscillatoryDecay_iff.mpr fun B ↦ (HasOscillatoryDecayAt.rpow_mul_cos_add_sin
    (c := c) (p := p) (B := B) 0 1 hα).congr_atTop (Eventually.of_forall fun _ ↦ by simp)

/-- Phase-shifted cosine mode `t ↦ t ^ (-α) * cos (c * t ^ p + φ)` with `α₀ ≤ α`. -/
theorem rpow_mul_cos_add {c p α₀ α : ℝ} (hα : α₀ ≤ α) (φ : ℝ) :
    HasOscillatoryDecay c p α₀ (fun t ↦ t ^ (-α) * Real.cos (c * t ^ p + φ)) :=
  (((rpow_mul_cos hα).const_mul (Real.cos φ)).sub
    ((rpow_mul_sin hα).const_mul (Real.sin φ))).congr_atTop
    (Eventually.of_forall fun _ ↦ by simp only [Pi.sub_apply, Real.cos_add]; ring)

/-- Phase-shifted sine mode `t ↦ t ^ (-α) * sin (c * t ^ p + φ)` with `α₀ ≤ α`. -/
theorem rpow_mul_sin_add {c p α₀ α : ℝ} (hα : α₀ ≤ α) (φ : ℝ) :
    HasOscillatoryDecay c p α₀ (fun t ↦ t ^ (-α) * Real.sin (c * t ^ p + φ)) :=
  (((rpow_mul_sin hα).const_mul (Real.cos φ)).add
    ((rpow_mul_cos hα).const_mul (Real.sin φ))).congr_atTop
    (Eventually.of_forall fun _ ↦ by simp only [Pi.add_apply, Real.sin_add]; ring)

/-- **Criterion from a Poincaré oscillatory asymptotic expansion.** If `β : ℕ → ℝ` satisfies
`∀ m, α₀ ≤ β m` and `β m → ∞`, and truncating the oscillatory series at `N` terms leaves a
remainder `O(t ^ (-β N))`, then `HasOscillatoryDecay c p α₀ f`. -/
theorem of_asymptoticExpansion {c p α₀ : ℝ} {f : ℝ → ℝ} {β u v : ℕ → ℝ}
    (hβ_ge : ∀ m, α₀ ≤ β m) (hβ_top : Tendsto β atTop atTop)
    (hexp : ∀ N : ℕ,
      (fun t ↦ f t - ∑ m ∈ Finset.range N,
        (u m * (t ^ (-β m) * Real.cos (c * t ^ p)) +
          v m * (t ^ (-β m) * Real.sin (c * t ^ p)))) =O[atTop] fun t ↦ t ^ (-β N)) :
    HasOscillatoryDecay c p α₀ f := by
  rw [hasOscillatoryDecay_def]
  intro B
  obtain ⟨N, hN⟩ := (hβ_top.eventually_ge_atTop B).exists
  have hrpow : (fun t : ℝ ↦ t ^ (-β N)) =O[atTop] fun t : ℝ ↦ t ^ (-B) := by
    refine isBigO_iff.mpr ⟨1, ?_⟩
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (zero_le_one.trans ht) _),
      Real.norm_of_nonneg (Real.rpow_nonneg (zero_le_one.trans ht) _), one_mul]
    exact Real.rpow_le_rpow_of_exponent_le ht (neg_le_neg hN)
  refine ⟨N, fun i ↦ β i, fun i ↦ u i, fun i ↦ v i,
    fun t ↦ f t - ∑ m ∈ Finset.range N,
      (u m * (t ^ (-β m) * Real.cos (c * t ^ p)) +
        v m * (t ^ (-β m) * Real.sin (c * t ^ p))),
    fun i ↦ hβ_ge i, (hexp N).trans hrpow, Eventually.of_forall fun t ↦ ?_⟩
  dsimp only
  rw [Fin.sum_univ_eq_sum_range (fun m ↦
    u m * (t ^ (-β m) * Real.cos (c * t ^ p)) + v m * (t ^ (-β m) * Real.sin (c * t ^ p)))]
  ring

/-- Every function satisfying `HasOscillatoryDecay c p α₀ f` satisfies the leading amplitude bound
`f =O[atTop] fun t : ℝ ↦ t ^ (-α₀)`. -/
theorem isBigO_rpow_neg {c p α₀ : ℝ} {f : ℝ → ℝ} (hf : HasOscillatoryDecay c p α₀ f) :
    f =O[atTop] fun t : ℝ ↦ t ^ (-α₀) := by
  obtain ⟨k, α, u, v, r, hα, hr, heq⟩ := hasOscillatoryDecay_def.mp hf α₀
  have hmode (i : Fin k) (trig : ℝ → ℝ) (htrig : ∀ θ, |trig θ| ≤ 1) :
      (fun t : ℝ ↦ t ^ (-α i) * trig (c * t ^ p)) =O[atTop] fun t : ℝ ↦ t ^ (-α₀) := by
    refine isBigO_iff.mpr ⟨1, ?_⟩
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
    have ht0 : 0 ≤ t := zero_le_one.trans ht
    rw [norm_mul, Real.norm_eq_abs (trig _), Real.norm_of_nonneg (Real.rpow_nonneg ht0 _),
      Real.norm_of_nonneg (Real.rpow_nonneg ht0 _), one_mul]
    exact (mul_le_of_le_one_right (Real.rpow_nonneg ht0 _) (htrig _)).trans
      (Real.rpow_le_rpow_of_exponent_le ht (neg_le_neg (hα i)))
  exact (((IsBigO.sum (s := Finset.univ) fun i _ ↦
      ((hmode i Real.cos Real.abs_cos_le_one).const_mul_left (u i)).add
        ((hmode i Real.sin Real.abs_sin_le_one).const_mul_left (v i))).congr_left
      fun t ↦ Finset.sum_apply t Finset.univ _).add hr).congr' heq.symm EventuallyEq.rfl

end HasOscillatoryDecay

end TauCeti
