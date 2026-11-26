/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Topology.LocallyConstant.Basic

/-!
# Integrability of functions factoring through a locally constant map to a finite type

A function that agrees on an open set `U` of finite measure with `Φ ∘ π`, for a locally constant
map `π : U → R` to a finite type, is a finite sum of constants times indicators of the open fibres
of `π`, hence integrable on `U` (`MeasureTheory.integrableOn_of_eq_comp`).
-/

public section

namespace MeasureTheory

variable {G R E : Type*} [MeasurableSpace G] {μ : Measure G} [NormedAddCommGroup E]
  [TopologicalSpace G] [OpensMeasurableSpace G]

/-- A function that agrees on an open set `U` of finite measure with a function of a locally
constant map `π : U → R` to a finite type is integrable on `U`. -/
theorem integrableOn_of_eq_comp [Finite R] {U : Set G} (hU : IsOpen U) (hμU : μ U ≠ ⊤)
    {π : U → R} (hπ : IsLocallyConstant π) {f : G → E} {Φ : R → E}
    (hf : ∀ x : U, f x = Φ (π x)) : IntegrableOn f U μ := by
  classical
  have := Fintype.ofFinite R
  -- the fibres of `π`, seen in `G`, are open
  let A (r : R) : Set G := Subtype.val '' (π ⁻¹' {r})
  have hA (r : R) : MeasurableSet (A r) :=
    (hU.isOpenMap_subtypeVal _ (hπ.isOpen_fiber r)).measurableSet
  have hmem {x : G} (hx : x ∈ U) (r : R) : x ∈ A r ↔ π ⟨x, hx⟩ = r := by
    simp [A, hx]
  have hint : IntegrableOn (fun x ↦ ∑ r, (A r).indicator (fun _ ↦ Φ r) x) U μ :=
    integrable_finsetSum _ fun r _ ↦
      (integrableOn_const (C := Φ r) hμU).indicator (hA r)
  refine hint.congr_fun (fun x hx ↦ ?_) hU.measurableSet
  dsimp only
  rw [hf ⟨x, hx⟩, Finset.sum_eq_single (π ⟨x, hx⟩)]
  · simp [Set.indicator_of_mem ((hmem hx _).mpr rfl)]
  · exact fun r _ hr ↦ Set.indicator_of_notMem (fun h ↦ hr ((hmem hx r).mp h).symm) _
  · simp

end MeasureTheory
