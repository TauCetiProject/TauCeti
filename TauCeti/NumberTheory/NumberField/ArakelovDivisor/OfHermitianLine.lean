/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.ArakelovDivisor.HermitianLine
public import TauCeti.NumberTheory.NumberField.HermitianBundle.Line
public import TauCeti.NumberTheory.NumberField.HermitianBundle.Submodule
public import TauCeti.RingTheory.PicardGroup.Contraction

/-!
# Every hermitian line is the line of an Arakelov divisor

A hermitian line over `Spec 𝓞 K`, an invertible `𝓞 K`-module `E` with a hermitian metric, is
isometric to the line `O(D)` of some Arakelov divisor `D`
(`TauCeti.ArakelovDivisor.exists_isometryEquiv_hermitianMetric`). So `D ↦ O(D)` induces a
surjection from the compactified Picard group onto the isometry classes of hermitian lines.

The module `E` is isomorphic to an ideal
(Mathlib's `Module.Invertible.exists_linearEquiv_ideal`), hence to a nonzero fractional ideal `I`.
A hermitian metric on `I` is `HermitianMetric.fractionalIdeal` for weights
`w_v = log |x₀|_v - log ‖x₀‖_v` read off at any nonzero `x₀ ∈ I`
(`TauCeti.HermitianMetric.eq_fractionalIdeal`), and that is the line `O(D)` of
`D = (I⁻¹, v ↦ mult(v) w_v)` (`TauCeti.ArakelovDivisor.exists_isometryEquiv_fractionalIdeal`).

## Main results

* `TauCeti.ArakelovDivisor.exists_isometryEquiv_fractionalIdeal`: a hermitian metric on a nonzero
  fractional ideal is isometric to some `O(D)`.
* `TauCeti.ArakelovDivisor.exists_isometryEquiv_hermitianMetric`: a hermitian metric on an
  invertible `𝓞 K`-module is isometric to some `O(D)`.

## References

* L. Szpiro, *Degrés, intersections, hauteurs*, Astérisque 127 (1985), §1.1–1.2,
  Proposition 1.1 and Corollaire.
-/

public section

open NumberField NumberField.InfinitePlace FractionalIdeal
open scoped nonZeroDivisors TensorProduct

namespace TauCeti.ArakelovDivisor

variable {K : Type*} [Field K] [NumberField K]

/-- **A hermitian metric on a nonzero fractional ideal is the line of an Arakelov divisor.** For
`h` on `I` and a nonzero `x₀ ∈ I`, `h` is isometric to `O(D)` for
`D = (I⁻¹, v ↦ mult(v) (log |x₀|_v - log ‖x₀‖_v))`. -/
theorem exists_isometryEquiv_fractionalIdeal {I : FractionalIdeal (𝓞 K)⁰ K} (hI : I ≠ 0)
    (h : HermitianMetric K I) :
    ∃ D : ArakelovDivisor K, Nonempty (HermitianMetric.IsometryEquiv h D.hermitianMetric) := by
  obtain ⟨x₀, hx₀I, hx₀⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    ((FractionalIdeal.coeToSubmodule_ne_bot).mpr hI)
  set w : InfinitePlace K → ℝ := fun v ↦
    Real.log (v x₀) - Real.log (h.placeNorm v ⟨x₀, hx₀I⟩)
  have hh : h = HermitianMetric.fractionalIdeal I hI w :=
    HermitianMetric.eq_fractionalIdeal hI h (x₀ := ⟨x₀, hx₀I⟩) hx₀
  let D : ArakelovDivisor K := ⟨(Units.mk0 I hI)⁻¹, fun v ↦ v.mult * w v⟩
  have hIJ : I = spanSingleton _ ((1 : Kˣ) : K)⁻¹ *
      ((D.finitePart⁻¹ : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) := by
    simp [D]
  have e₀ : HermitianMetric.IsometryEquiv h (HermitianMetric.fractionalIdeal I hI w) := by
    rw [← hh]
  refine ⟨D, ⟨e₀.trans ?_⟩⟩
  rw [hermitianMetric_def]
  refine HermitianMetric.isometryEquivFractionalIdealMul _ hI 1 hIJ fun v ↦ ?_
  have hm : (v.mult : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr mult_ne_zero
  simp [D, hm]

/-- **Every hermitian line is the line of an Arakelov divisor.** A hermitian metric on an
invertible `𝓞 K`-module is isometric to `O(D)` for some Arakelov divisor `D`; so `D ↦ O(D)` is
surjective onto the isometry classes of hermitian lines. -/
theorem exists_isometryEquiv_hermitianMetric {E : Type*} [AddCommGroup E] [Module (𝓞 K) E]
    [Module.Invertible (𝓞 K) E] (h : HermitianMetric K E) :
    ∃ D : ArakelovDivisor K, Nonempty (HermitianMetric.IsometryEquiv h D.hermitianMetric) := by
  obtain ⟨I, ⟨e⟩⟩ := Module.Invertible.exists_linearEquiv_ideal (𝓞 K) E
  set J : FractionalIdeal (𝓞 K)⁰ K := (I : FractionalIdeal (𝓞 K)⁰ K)
  let ee : E ≃ₗ[𝓞 K] J := e.trans (coeIdealEquiv I).symm
  have := Module.Invertible.nontrivial (𝓞 K) E
  have : Nontrivial I := e.symm.toEquiv.nontrivial
  have hJ0 : J ≠ 0 := mt coeIdeal_eq_zero.mp (Submodule.nontrivial_iff_ne_bot.mp this)
  let h' : HermitianMetric K J := h.comap ee.symm.toLinearMap ee.symm.injective
  let e₁ : HermitianMetric.IsometryEquiv h h' := h.isometryEquivComap ee.symm
  obtain ⟨D, ⟨e₂⟩⟩ := exists_isometryEquiv_fractionalIdeal hJ0 h'
  exact ⟨D, ⟨e₁.trans e₂⟩⟩

end TauCeti.ArakelovDivisor
