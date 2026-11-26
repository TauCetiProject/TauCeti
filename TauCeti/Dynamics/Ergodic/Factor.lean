/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Dynamics.Ergodic.Ergodic
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Measure.Dirac.Basic

/-!
# Factor maps of measure-preserving systems

A *factor map* from a system `T : X → X` on `(X, μ)` to a system `S : Y → Y` on `(Y, ν)` is a
measure-preserving map `π : X → Y` intertwining the two systems almost everywhere:
`π ∘ T =ᵐ[μ] S ∘ π`.

## Main definitions

* `TauCeti.IsFactorMap π T S μ ν` — `π` is a factor map from `(X, μ, T)` to `(Y, ν, S)`.

## Main results

* `TauCeti.IsFactorMap.id`, `TauCeti.IsFactorMap.comp` — factor maps contain the identity and
  compose.
* `TauCeti.IsFactorMap.of_semiconj` — a measure-preserving map that semiconjugates everywhere is a
  factor map.
* `TauCeti.IsFactorMap.toUnit` — the constant map to a point is a factor map onto the trivial
  system.
* `TauCeti.IsFactorMap.fst`, `TauCeti.IsFactorMap.snd` — the coordinate projections of a product of
  probability systems are factor maps.
* `TauCeti.IsFactorMap.measurePreserving_target` — if `T` preserves `μ` and `S` is measurable,
  then `S` preserves `ν`.
* `TauCeti.IsFactorMap.comp_iterate_ae_eq` — a factor map intertwines all iterates almost
  everywhere when `T` is quasi-measure-preserving.
* `TauCeti.IsFactorMap.preErgodic`, `TauCeti.IsFactorMap.ergodic` — pre-ergodicity passes to
  factors, and ergodicity passes to factors whose target map is measurable.

The last two adapt Mathlib's `MeasureTheory.MeasurePreserving.preErgodic_of_preErgodic_semiconj`
and `MeasureTheory.MeasurePreserving.ergodic_of_ergodic_semiconj` from everywhere to
almost-everywhere semiconjugacies.
-/

public section

namespace TauCeti

open MeasureTheory Function Filter

variable {X Y Z : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
  {μ : Measure X} {ν : Measure Y} {ρ : Measure Z}
  {T : X → X} {S : Y → Y} {R : Z → Z} {π : X → Y} {σ : Y → Z}

/-- `π : X → Y` is a factor map from the system `T` on `(X, μ)` to the system `S` on `(Y, ν)`: it
is measure-preserving and intertwines the systems almost everywhere, `π ∘ T =ᵐ[μ] S ∘ π`. -/
structure IsFactorMap (π : X → Y) (T : X → X) (S : Y → Y) (μ : Measure X) (ν : Measure Y) :
    Prop where
  /-- A factor map is measure-preserving. -/
  measurePreserving : MeasurePreserving π μ ν
  /-- A factor map intertwines the two systems almost everywhere. -/
  comp_ae_eq : π ∘ T =ᵐ[μ] S ∘ π

namespace IsFactorMap

/-- The identity is a factor map from any system to itself. -/
protected theorem id (T : X → X) (μ : Measure X) : IsFactorMap id T T μ μ :=
  ⟨.id μ, .rfl⟩

/-- A measure-preserving map that semiconjugates `T` to `S` everywhere is a factor map. -/
theorem of_semiconj (hπ : MeasurePreserving π μ ν) (h : Semiconj π T S) :
    IsFactorMap π T S μ ν :=
  ⟨hπ, .of_eq h.comp_eq⟩

/-- Factor maps compose. -/
protected theorem comp (hσ : IsFactorMap σ S R ν ρ) (hπ : IsFactorMap π T S μ ν) :
    IsFactorMap (σ ∘ π) T R μ ρ := by
  refine ⟨hσ.measurePreserving.comp hπ.measurePreserving, ?_⟩
  have h₁ : σ ∘ (π ∘ T) =ᵐ[μ] σ ∘ (S ∘ π) := hπ.comp_ae_eq.fun_comp σ
  have h₂ : (σ ∘ S) ∘ π =ᵐ[μ] (R ∘ σ) ∘ π :=
    hπ.measurePreserving.quasiMeasurePreserving.ae_eq_comp hσ.comp_ae_eq
  exact h₁.trans h₂

/-- The constant map to a point is a factor map from a probability system onto the trivial
system. -/
theorem toUnit [IsProbabilityMeasure μ] (T : X → X) :
    IsFactorMap (fun _ ↦ ()) T id μ (Measure.dirac ()) :=
  of_semiconj ⟨measurable_const, by simp [Measure.map_const]⟩ fun _ ↦ rfl

/-- The first coordinate projection is a factor map from the product of two systems, the second
on a probability space, to the first. -/
protected theorem fst [IsProbabilityMeasure ν] (T : X → X) (S : Y → Y) :
    IsFactorMap Prod.fst (Prod.map T S) T (μ.prod ν) μ :=
  of_semiconj (measurePreserving_fst) fun _ ↦ rfl

/-- The second coordinate projection is a factor map from the product of two systems, the first
on a probability space, to the second. -/
protected theorem snd [IsProbabilityMeasure μ] [SFinite ν] (T : X → X) (S : Y → Y) :
    IsFactorMap Prod.snd (Prod.map T S) S (μ.prod ν) ν :=
  of_semiconj (measurePreserving_snd) fun _ ↦ rfl

/-- If `π` is a factor map from `T` to `S`, `T` preserves `μ` and `S` is measurable, then `S`
preserves `ν`. -/
theorem measurePreserving_target (h : IsFactorMap π T S μ ν) (hT : MeasurePreserving T μ μ)
    (hS : Measurable S) : MeasurePreserving S ν ν := by
  refine ⟨hS, ?_⟩
  have hπ := h.measurePreserving
  calc ν.map S = (μ.map π).map S := by rw [hπ.map_eq]
    _ = μ.map (S ∘ π) := Measure.map_map hS hπ.measurable
    _ = μ.map (π ∘ T) := (Measure.map_congr h.comp_ae_eq).symm
    _ = ν := (hπ.comp hT).map_eq

/-- A factor map intertwines all iterates almost everywhere, when `T` is quasi-measure-preserving:
`π ∘ T^[k] =ᵐ[μ] S^[k] ∘ π`. -/
theorem comp_iterate_ae_eq (h : IsFactorMap π T S μ ν) (hT : QuasiMeasurePreserving T μ μ)
    (k : ℕ) : π ∘ T^[k] =ᵐ[μ] S^[k] ∘ π := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have h₁ : π ∘ T^[k] ∘ T =ᵐ[μ] (S^[k] ∘ π) ∘ T := hT.ae_eq_comp ih
    have h₂ : S^[k] ∘ (π ∘ T) =ᵐ[μ] S^[k] ∘ (S ∘ π) := h.comp_ae_eq.fun_comp _
    rw [iterate_succ, iterate_succ]
    exact h₁.trans h₂

/-- A factor of a pre-ergodic system is pre-ergodic. -/
theorem preErgodic (h : IsFactorMap π T S μ ν) (hT : PreErgodic T μ) : PreErgodic S ν where
  aeconst_set s hs₀ hs₁ := by
    have hπ := h.measurePreserving
    rw [← hπ.aeconst_preimage hs₀]
    refine hT.aeconst_set (hs₀.preimage hπ.quasiMeasurePreserving) ?_
    exact (h.comp_ae_eq.preimage s).trans (hπ.quasiMeasurePreserving.preimage_ae_eq hs₁)

/-- Ergodicity passes to factors whose target map is measurable. -/
theorem ergodic (h : IsFactorMap π T S μ ν) (hT : Ergodic T μ) (hS : Measurable S) :
    Ergodic S ν :=
  ⟨h.measurePreserving_target hT.toMeasurePreserving hS, h.preErgodic hT.toPreErgodic⟩

end IsFactorMap

end TauCeti
