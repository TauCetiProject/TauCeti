/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.CriticalPoints

/-!
# Regular values, critical bands and collars

This file collects helper lemmas about regular values and critical points on bands `f ⁻¹' s` and
`f ⁻¹' [a, b]` building on `TauCeti.Geometry.Manifold.Morse.CriticalPoints`:

* `TauCeti.isRegularValue_iff_notMem_image_criticalPoints_inter_preimage`,
  `TauCeti.isRegularValue_of_mem_of_ne` and
  `TauCeti.apply_eq_of_mem_criticalPoints_inter_preimage`: regular values and critical values on
  a band or preimage.
* `TauCeti.mfderiv_ne_zero_of_isEmpty`: a band whose critical points lie in the range of a map
  from an empty type has nowhere-vanishing manifold derivative.
* `TauCeti.exists_mem_Icc_isCompact_forall_mfderiv_ne_zero`: a compact band starting at a regular
  value begins with a compact collar free of critical points, allowing a degenerate band `a = b`.
-/

public section

open Function Set
open scoped ContDiff Manifold

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] {f : M → ℝ}

/-- A scalar value `d ∈ s` is regular for `f` exactly when it is not a critical value of `f` on
`f ⁻¹' s`. -/
theorem isRegularValue_iff_notMem_image_criticalPoints_inter_preimage {s : Set ℝ} {d : ℝ}
    (hd : d ∈ s) :
    IsRegularValue I 𝓘(ℝ) f d ↔ d ∉ f '' (criticalPoints I f ∩ f ⁻¹' s) := by
  rw [isRegularValue_iff_notMem_image_criticalPoints]
  exact not_congr ⟨fun ⟨x, hx, hxd⟩ ↦ ⟨x, ⟨hx, show f x ∈ s from hxd.symm ▸ hd⟩, hxd⟩,
    fun ⟨x, ⟨hx, _⟩, hxd⟩ ↦ ⟨x, hx, hxd⟩⟩

/-- A scalar value `d ∈ s` other than `c` is regular for `f` whenever every critical point of `f`
in `f ⁻¹' s` lies on the level `c`. -/
theorem isRegularValue_of_mem_of_ne {s : Set ℝ} {c d : ℝ} (hd : d ∈ s) (hdc : d ≠ c)
    (hcrit : ∀ x ∈ criticalPoints I f, f x ∈ s → f x = c) :
    IsRegularValue I 𝓘(ℝ) f d :=
  (isRegularValue_iff_notMem_image_criticalPoints_inter_preimage hd).2
    fun ⟨x, ⟨hx, hfx⟩, hxd⟩ ↦ hdc (hxd.symm.trans (hcrit x hx hfx))

/-- If `f` takes the constant value `c` on the range of `g` and every critical point of `f` in
`f ⁻¹' s` lies in the range of `g`, then `f x = c` at every critical point `x` with `f x ∈ s`. -/
theorem apply_eq_of_mem_criticalPoints_inter_preimage {S : Type*} {g : S → M} {s : Set ℝ} {c : ℝ}
    (hc : ∀ s, f (g s) = c) (hcrit : criticalPoints I f ∩ f ⁻¹' s ⊆ range g) :
    ∀ x ∈ criticalPoints I f, f x ∈ s → f x = c := fun x hx hfx ↦ by
  obtain ⟨s₀, rfl⟩ := hcrit ⟨hx, hfx⟩
  exact hc s₀

/-- If all critical points of `f` in the band `f⁻¹[a, b]` lie in the image of a map from an empty
type `S`, then `f` has nonzero manifold derivative throughout the band. -/
theorem mfderiv_ne_zero_of_isEmpty {S : Type*} [IsEmpty S] {i : S → M} {a b : ℝ}
    (hcrit : criticalPoints I f ∩ f ⁻¹' Icc a b ⊆ range i) (x : M) (hax : a ≤ f x)
    (hxb : f x ≤ b) : mfderiv I 𝓘(ℝ) f x ≠ 0 := fun hx ↦
  isEmptyElim (hcrit ⟨mem_criticalPoints_iff_mfderiv_eq_zero.2 hx, hax, hxb⟩).choose

/-- **A regular value has a compact collar without critical points above it, allowing a degenerate
band.** If `f` is `C¹`, `a ≤ b`, the band `f⁻¹[a, b]` is compact and `a` is a regular value of `f`,
then for some `a' ∈ [a, b]` (with `a < a'` whenever `a < b`, or `a' = b`) the band `f⁻¹[a, a']` is
compact and `f` has nonzero derivative on it. -/
theorem exists_mem_Icc_isCompact_forall_mfderiv_ne_zero [IsManifold I 1 M]
    (hf : ContMDiff I 𝓘(ℝ) 1 f) {a b : ℝ} (hab : a ≤ b) (hcompact : IsCompact (f ⁻¹' Icc a b))
    (ha : IsRegularValue I 𝓘(ℝ) f a) :
    ∃ a' ∈ Icc a b, (a < a' ∨ a' = b) ∧ IsCompact (f ⁻¹' Icc a a') ∧
      ∀ x, a ≤ f x → f x ≤ a' → mfderiv I 𝓘(ℝ) f x ≠ 0 := by
  rcases hab.eq_or_lt with rfl | hlt
  · exact ⟨a, ⟨le_rfl, le_rfl⟩, Or.inr rfl, hcompact, fun x h₁ h₂ hx ↦
      isRegularPoint_iff_notMem_criticalPoints.1 (ha.isRegularPoint (le_antisymm h₂ h₁))
        (mem_criticalPoints_iff_mfderiv_eq_zero.2 hx)⟩
  · obtain ⟨a', ha', hc, h⟩ := exists_mem_Ioc_isCompact_forall_mfderiv_ne_zero hf hlt hcompact ha
    exact ⟨a', ⟨ha'.1.le, ha'.2⟩, Or.inl ha'.1, hc, h⟩

end TauCeti
