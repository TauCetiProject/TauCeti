/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Composition.Uniform.Sharp
public import TauCeti.Analysis.Sobolev.BesselPotential.Extension
import TauCeti.Analysis.Distribution.SchwartzSpace.Fourier

/-!
# Conjugation of uniform symbols by Bessel multipliers

Write `J^t` for Mathlib's Bessel multiplier, the Fourier multiplier `(1 + ‖ζ‖²) ^ (t / 2)`; it is
the quantization of the uniform symbol `⟨ξ / 2π⟩ ^ t` of order `t`
(`TauCeti.Symbol.besselPotential`, `TauCeti.Symbol.quantizeUniformCLM_besselPotential`).
Composition with `J^t` on the right is exact: `Op(a) ∘ J^t` is the quantization of
`a ⟨ξ / 2π⟩ ^ t` (`TauCeti.Symbol.quantizeUniformCLM_comp_besselMultiplier`). Composition on the
left is given explicitly by `TauCeti.Symbol.uniformSharp`, so for a uniform symbol `a` of order `m`
and every real `s`, the explicit order-zero symbol

`a.besselConjugate ha s = ⟨ξ / 2π⟩ ^ (s - m) # (a ∘ ⟨ξ / 2π⟩ ^ (-s))`

is uniform (`TauCeti.Symbol.IsUniform.besselConjugate`) and satisfies

`Op(a.besselConjugate ha s) = J^{s - m} ∘ Op(a) ∘ J^{-s}` and
`J^{s - m} ∘ Op(a) = Op(a.besselConjugate ha s) ∘ J^s`

on Schwartz space (`TauCeti.Symbol.quantizeUniformCLM_besselConjugate`,
`TauCeti.Symbol.quantizeUniformCLM_besselConjugate_fourierMultiplierCLM`,
`TauCeti.Symbol.IsUniform.exists_besselMultiplier_comp_quantizeUniformCLM_eq`).
This reduces the mapping of `Op(a)` between Bessel-potential spaces of orders `s` and `s - m` to
the boundedness of `a.besselConjugate ha s` at order `0`
(`TauCeti.Symbol.hasSobolevExtension_quantizeUniformCLM_iff_besselConjugate`), on `L²` by
Calderón–Vaillancourt and on `Lᵖ` by Calderón–Zygmund.

## Main declarations

* `TauCeti.Symbol.besselConjugate`, `TauCeti.Symbol.IsUniform.besselConjugate`: explicit order-zero
  uniform symbol `⟨ξ / 2π⟩ ^ (s - m) # (a ∘ ⟨ξ / 2π⟩ ^ (-s))`, linear in `a`
  (`besselConjugate_{add,smul,zero,neg,sub}`).
* `TauCeti.Symbol.quantizeUniformCLM_besselConjugate`,
  `TauCeti.Symbol.quantizeUniformCLM_besselConjugate_fourierMultiplierCLM`,
  `TauCeti.Symbol.IsUniform.exists_besselMultiplier_comp_quantizeUniformCLM_eq`: intertwining of
  `Op(a)` with Bessel multipliers on Schwartz space.
* `TauCeti.Symbol.hasSobolevExtension_quantizeUniformCLM_iff_besselConjugate`: `Op(a)` extends to
  `H^s → H^{s - m}` if and only if `Op(a.besselConjugate ha s)` extends on `H^0 = L²`.

## References

* M. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI* (2008), Lecture I, §3.
-/

public section
noncomputable section

open ContinuousLinearMap (comp_apply)
open SchwartzMap (HasSobolevExtension hasSobolevExtension_besselMultiplier fourierMultiplierCLM
  fourierMultiplierCLM_one_add_norm_sq_rpow_fourierMultiplierCLM_neg)
open scoped SchwartzMap

namespace TauCeti
namespace Symbol

variable {n : ℕ} {m : ℝ}

section Symbol

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [NormedAddCommGroup W] [NormedSpace ℂ W]

/-- **Bessel conjugation of a uniform symbol.** For uniform `a : Symbol n V W m` and `s : ℝ`, the
symbol `⟨ξ / 2π⟩ ^ (s - m) # (a ∘ ⟨ξ / 2π⟩ ^ (-s))` viewed at order `0`, quantizing on Schwartz
space to `J^{s - m} ∘ Op(a) ∘ J^{-s}` (`quantizeUniformCLM_besselConjugate`). -/
def besselConjugate (a : Symbol n V W m) (ha : a.IsUniform) (s : ℝ) : Symbol n V W 0 :=
  inclusion (by linarith) ((besselPotential (s - m) : Symbol n W W (s - m)).uniformSharp
    (a.comp (besselPotential (-s))) (ha.comp (isUniform_besselPotential (-s))))

/-- Defining formula for `Symbol.besselConjugate`. -/
theorem besselConjugate_def (a : Symbol n V W m) (ha : a.IsUniform) (s : ℝ) :
    a.besselConjugate ha s = inclusion (by linarith)
      ((besselPotential (s - m) : Symbol n W W (s - m)).uniformSharp
        (a.comp (besselPotential (-s))) (ha.comp (isUniform_besselPotential (-s)))) := (rfl)

theorem IsUniform.besselConjugate {a : Symbol n V W m} (ha : a.IsUniform) (s : ℝ) :
    (a.besselConjugate ha s).IsUniform :=
  ((isUniform_besselPotential (s - m)).uniformSharp
    (ha.comp (isUniform_besselPotential (-s)))).inclusion (by linarith)

private theorem besselConjugate_congr {a b : Symbol n V W m} (h : a = b) (ha : a.IsUniform)
    (hb : b.IsUniform) (s : ℝ) : a.besselConjugate ha s = b.besselConjugate hb s := by
  subst h; rfl

theorem besselConjugate_add {a b : Symbol n V W m} (ha : a.IsUniform) (hb : b.IsUniform) (s : ℝ) :
    (a + b).besselConjugate (ha.add hb) s = a.besselConjugate ha s + b.besselConjugate hb s := by
  ext1
  rw [besselConjugate_def, besselConjugate_def, besselConjugate_def, ← map_add,
    coefficient_inclusion, coefficient_inclusion, ← uniformSharp_add]
  exact coefficient_uniformSharp_congr _ _ rfl (congrArg Symbol.coefficient (add_comp a b _))

theorem besselConjugate_smul {a : Symbol n V W m} (ha : a.IsUniform) (c : ℂ) (s : ℝ) :
    (c • a).besselConjugate (ha.smul c) s = c • a.besselConjugate ha s := by
  ext1
  rw [besselConjugate_def, besselConjugate_def, ← map_smul, coefficient_inclusion,
    coefficient_inclusion, ← uniformSharp_smul]
  exact coefficient_uniformSharp_congr _ _ rfl (congrArg Symbol.coefficient (smul_comp c a _))

@[simp]
theorem besselConjugate_zero (h : (0 : Symbol n V W m).IsUniform) (s : ℝ) :
    (0 : Symbol n V W m).besselConjugate h s = 0 := by
  rw [besselConjugate_congr (zero_smul ℂ (0 : Symbol n V W m)).symm h (h.smul 0) s,
    besselConjugate_smul h 0 s, zero_smul]

theorem besselConjugate_neg {a : Symbol n V W m} (ha : a.IsUniform) (s : ℝ) :
    (-a).besselConjugate ha.neg s = -a.besselConjugate ha s := by
  rw [besselConjugate_congr (neg_one_smul ℂ a).symm ha.neg (ha.smul (-1)) s,
    besselConjugate_smul ha (-1) s, neg_one_smul]

theorem besselConjugate_sub {a b : Symbol n V W m} (ha : a.IsUniform) (hb : b.IsUniform) (s : ℝ) :
    (a - b).besselConjugate (ha.sub hb) s = a.besselConjugate ha s - b.besselConjugate hb s := by
  rw [eq_sub_iff_add_eq, ← besselConjugate_add (ha.sub hb) hb s]
  exact besselConjugate_congr (sub_add_cancel a b) _ ha s

end Symbol

section Quantize

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
  [NormedAddCommGroup W] [NormedSpace ℂ W] [CompleteSpace W]

/-- On Schwartz functions, `Op(a.besselConjugate ha s) = J^{s - m} ∘ Op(a) ∘ J^{-s}`. -/
theorem quantizeUniformCLM_besselConjugate {a : Symbol n V W m} (ha : a.IsUniform) (s : ℝ)
    (v : 𝓢(CoordinateSpace n, V)) :
    quantizeUniformCLM (a.besselConjugate ha s) (ha.besselConjugate s) v =
      fourierMultiplierCLM W
        (fun ζ : CoordinateSpace n ↦ (((1 + ‖ζ‖ ^ 2) ^ ((s - m) / 2) : ℝ) : ℂ))
        (quantizeUniformCLM a ha (fourierMultiplierCLM V
          (fun ζ : CoordinateSpace n ↦ (((1 + ‖ζ‖ ^ 2) ^ (-s / 2) : ℝ) : ℂ)) v)) := by
  have hcomp := congrArg (fun T ↦ T v) (quantizeUniformCLM_comp_besselMultiplier a ha (-s)).symm
  have hc := (isUniform_besselPotential (s - m)).uniformSharp
    (ha.comp (isUniform_besselPotential (-s)))
  ext x
  rw [quantizeUniformCLM_apply, besselConjugate_def, coefficient_inclusion,
    ← quantizeUniformCLM_apply _ hc, quantizeUniformCLM_besselPotential_uniformSharp,
    comp_apply, hcomp, comp_apply]

/-- **Intertwining with Bessel multipliers**: `Op(a.besselConjugate ha s) (J^s u) = J^{s - m}
(Op(a) u)`. -/
theorem quantizeUniformCLM_besselConjugate_fourierMultiplierCLM {a : Symbol n V W m}
    (ha : a.IsUniform) (s : ℝ) (u : 𝓢(CoordinateSpace n, V)) :
    quantizeUniformCLM (a.besselConjugate ha s) (ha.besselConjugate s)
        (fourierMultiplierCLM V
          (fun ζ : CoordinateSpace n ↦ (((1 + ‖ζ‖ ^ 2) ^ (s / 2) : ℝ) : ℂ)) u) =
      fourierMultiplierCLM W
        (fun ζ : CoordinateSpace n ↦ (((1 + ‖ζ‖ ^ 2) ^ ((s - m) / 2) : ℝ) : ℂ))
        (quantizeUniformCLM a ha u) := by
  have hinv := fourierMultiplierCLM_one_add_norm_sq_rpow_fourierMultiplierCLM_neg (-s) u
  rw [neg_neg] at hinv
  rw [quantizeUniformCLM_besselConjugate, hinv]

/-- **Conjugation by Bessel multipliers.** For a uniform symbol `a` of order `m` and every real
`s` there is a uniform symbol `b` of order `0` with `J^{s - m} ∘ Op(a) = Op(b) ∘ J^s` on Schwartz
space. -/
theorem IsUniform.exists_besselMultiplier_comp_quantizeUniformCLM_eq {a : Symbol n V W m}
    (ha : a.IsUniform) (s : ℝ) :
    ∃ (b : Symbol n V W 0) (hb : b.IsUniform),
      SchwartzMap.fourierMultiplierCLM W
          (fun ζ : CoordinateSpace n ↦ (((1 + ‖ζ‖ ^ 2) ^ ((s - m) / 2) : ℝ) : ℂ)) ∘L
        quantizeUniformCLM a ha =
      quantizeUniformCLM b hb ∘L SchwartzMap.fourierMultiplierCLM V
        (fun ζ : CoordinateSpace n ↦ (((1 + ‖ζ‖ ^ 2) ^ (s / 2) : ℝ) : ℂ)) :=
  ⟨a.besselConjugate ha s, ha.besselConjugate s, ContinuousLinearMap.ext fun u ↦
    (quantizeUniformCLM_besselConjugate_fourierMultiplierCLM ha s u).symm⟩

/-- Over arbitrary complete complex normed fibres, `Op(a)` extends to `H^s → H^{s - m}` if and only
if its Bessel conjugate `a.besselConjugate ha s` extends on `H^0 = L²`. -/
theorem hasSobolevExtension_quantizeUniformCLM_iff_besselConjugate {a : Symbol n V W m}
    (ha : a.IsUniform) (s : ℝ) :
    HasSobolevExtension (quantizeUniformCLM a ha) s (s - m) ↔
      HasSobolevExtension
        (quantizeUniformCLM (a.besselConjugate ha s) (ha.besselConjugate s)) 0 0 := by
  let f (t : ℝ) (ζ : CoordinateSpace n) : ℂ := ((1 + ‖ζ‖ ^ 2) ^ (t / 2) : ℝ)
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · have heq : quantizeUniformCLM (a.besselConjugate ha s) (ha.besselConjugate s) =
        fourierMultiplierCLM W (f (s - m)) ∘L quantizeUniformCLM a ha ∘L
          fourierMultiplierCLM V (f (-s)) :=
      ContinuousLinearMap.ext (quantizeUniformCLM_besselConjugate ha s)
    rw [heq]
    exact ((hasSobolevExtension_besselMultiplier (s - m) (by ring)).comp h).comp
      (hasSobolevExtension_besselMultiplier (-s) (by ring))
  · have heq : quantizeUniformCLM a ha = fourierMultiplierCLM W (f (-(s - m))) ∘L
        quantizeUniformCLM (a.besselConjugate ha s) (ha.besselConjugate s) ∘L
          fourierMultiplierCLM V (f s) := by
      ext1 u
      simp only [comp_apply, f, quantizeUniformCLM_besselConjugate_fourierMultiplierCLM ha s u]
      simpa only [neg_neg] using (fourierMultiplierCLM_one_add_norm_sq_rpow_fourierMultiplierCLM_neg
        (-(s - m)) (quantizeUniformCLM a ha u)).symm
    rw [heq]
    exact ((hasSobolevExtension_besselMultiplier (-(s - m)) (by ring)).comp h).comp
      (hasSobolevExtension_besselMultiplier s (by ring))

end Quantize

end Symbol
end TauCeti
