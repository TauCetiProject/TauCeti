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
  factor map; in particular so is a measure-preserving conjugacy `X ≃ᵐ Y`.
* `TauCeti.IsFactorMap.toUnit` — the constant map to a point is a factor map onto the trivial
  system.
* `TauCeti.IsFactorMap.fst`, `TauCeti.IsFactorMap.snd` — the coordinate projections of a product of
  probability systems are factor maps.
* `TauCeti.IsFactorMap.measurePreserving` — the target map of a factor of a system preserves the
  target measure.
* `TauCeti.IsFactorMap.ergodic` — ergodicity passes to factors.
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
  measurePreserving_map : MeasurePreserving π μ ν
  /-- A factor map intertwines the two systems almost everywhere. -/
  comp_ae_eq : π ∘ T =ᵐ[μ] S ∘ π

namespace IsFactorMap

/-- The identity is a factor map from any system to itself. -/
theorem id (T : X → X) (μ : Measure X) : IsFactorMap _root_.id T T μ μ :=
  ⟨.id μ, .rfl⟩

/-- A measure-preserving map that semiconjugates `T` to `S` everywhere is a factor map. -/
theorem of_semiconj (hπ : MeasurePreserving π μ ν) (h : Semiconj π T S) :
    IsFactorMap π T S μ ν :=
  ⟨hπ, .of_eq h.comp_eq⟩

/-- A measure-preserving conjugacy `e : X ≃ᵐ Y` with `e ∘ T = S ∘ e` is a factor map. -/
theorem of_measurableEquiv (e : X ≃ᵐ Y) (he : MeasurePreserving e μ ν) (h : Semiconj e T S) :
    IsFactorMap e T S μ ν :=
  of_semiconj he h

/-- Factor maps compose. -/
theorem comp (hσ : IsFactorMap σ S R ν ρ) (hπ : IsFactorMap π T S μ ν) :
    IsFactorMap (σ ∘ π) T R μ ρ := by
  refine ⟨hσ.measurePreserving_map.comp hπ.measurePreserving_map, ?_⟩
  have h₁ : σ ∘ (π ∘ T) =ᵐ[μ] σ ∘ (S ∘ π) := hπ.comp_ae_eq.fun_comp σ
  have h₂ : (σ ∘ S) ∘ π =ᵐ[μ] (R ∘ σ) ∘ π :=
    hπ.measurePreserving_map.quasiMeasurePreserving.ae_eq_comp hσ.comp_ae_eq
  exact h₁.trans h₂

/-- The constant map to a point is a factor map from a probability system onto the trivial
system. -/
theorem toUnit [IsProbabilityMeasure μ] (T : X → X) :
    IsFactorMap (fun _ ↦ ()) T _root_.id μ (Measure.dirac ()) :=
  of_semiconj ⟨measurable_const, by simp [Measure.map_const]⟩ fun _ ↦ rfl

/-- The first coordinate projection is a factor map from the product of two systems, the second
on a probability space, to the first. -/
theorem fst [IsProbabilityMeasure ν] (T : X → X) (S : Y → Y) :
    IsFactorMap Prod.fst (Prod.map T S) T (μ.prod ν) μ :=
  of_semiconj (measurePreserving_fst) fun _ ↦ rfl

/-- The second coordinate projection is a factor map from the product of two systems, the first
on a probability space, to the second. -/
theorem snd [IsProbabilityMeasure μ] [SFinite ν] (T : X → X) (S : Y → Y) :
    IsFactorMap Prod.snd (Prod.map T S) S (μ.prod ν) ν :=
  of_semiconj (measurePreserving_snd) fun _ ↦ rfl

/-- The target map of a factor of a measure-preserving system preserves the target measure. -/
theorem measurePreserving (h : IsFactorMap π T S μ ν) (hT : MeasurePreserving T μ μ)
    (hS : Measurable S) : MeasurePreserving S ν ν := by
  refine ⟨hS, ?_⟩
  have hπ := h.measurePreserving_map
  calc ν.map S = (μ.map π).map S := by rw [hπ.map_eq]
    _ = μ.map (S ∘ π) := Measure.map_map hS hπ.measurable
    _ = μ.map (π ∘ T) := (Measure.map_congr h.comp_ae_eq).symm
    _ = ν := (hπ.comp hT).map_eq

/-- A factor of a pre-ergodic system is pre-ergodic. -/
theorem preErgodic (h : IsFactorMap π T S μ ν) (hT : PreErgodic T μ) : PreErgodic S ν where
  aeconst_set s hs₀ hs₁ := by
    have hπ := h.measurePreserving_map
    rw [← hπ.aeconst_preimage hs₀]
    refine hT.aeconst_set (hs₀.preimage hπ.quasiMeasurePreserving) ?_
    have hST : S ∘ π =ᵐ[μ] π ∘ T := h.comp_ae_eq.symm
    have h₁ : T ⁻¹' (π ⁻¹' s) =ᵐ[μ] π ⁻¹' (S ⁻¹' s) := by
      filter_upwards [hST] with x hx
      simp only [Set.mem_preimage]
      rw [← comp_apply (f := π), ← hx, comp_apply]
    exact h₁.trans (hπ.quasiMeasurePreserving.preimage_ae_eq hs₁)

/-- Ergodicity passes to factors. -/
theorem ergodic (h : IsFactorMap π T S μ ν) (hT : Ergodic T μ) (hS : Measurable S) :
    Ergodic S ν :=
  ⟨h.measurePreserving hT.toMeasurePreserving hS, h.preErgodic hT.toPreErgodic⟩

end IsFactorMap

end TauCeti
