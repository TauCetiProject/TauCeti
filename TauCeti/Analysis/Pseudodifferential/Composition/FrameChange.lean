/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Composition.Expansion
import TauCeti.Analysis.Pseudodifferential.OutputSupport.Basic

/-!
# Changes of frame for pseudodifferential operators

In a local trivialization of vector bundles `E` and `F`, a pseudodifferential operator
`P : Γ(E) → Γ(F)` is a quantization `Op(a)` of a symbol `a(x, ξ) : V → W` between the model
fibres. Changing the frames of `E` and `F` replaces `Op(a)` by `u ↦ Φ · Op(a) (Ψ u)`, where
`Ψ(x) : V' → V` expresses the new frame of `E` in the old one and `Φ(x) : W → W'` expresses the old
frame of `F` in the new one. In a chart the operator is localized by cutoffs, so `Ψ` is taken
compactly supported. This file shows that the transformed operator is again a quantization, of the
**frame change** `Φ (a # Ψ)` of `a` (`TauCeti.Symbol.frameChange`), and computes its symbol.

* **The frame transformation formula.** The frame change has the asymptotic expansion

  `Φ (a # Ψ) ∼ ∑ₖ ((-i)^k / k!) ∑_{|w| = k} Φ ∘ ∂_ξ^w a ∘ ∂_x^w Ψ`,

  the term of index `k` having order `m - k`, with an actual remainder of order `m - N` after `N`
  terms (`TauCeti.Symbol.exists_coefficient_frameChange_eq_sum`). The leading term
  `Φ(x) a(x, ξ) Ψ(x)` is the transformation law of a `Hom(E, F)`-valued function on the cotangent
  bundle, so the principal symbol transforms intrinsically; the next term
  `-i ∑ⱼ Φ ∂_{ξⱼ} a ∂ⱼΨ` shows that the full symbol does not
  (`TauCeti.Symbol.exists_coefficient_frameChange_eq`).
* **Composition of frame changes.** Changing frames twice is one change of frame by the composed
  transition maps, exactly: `Φ' (Φ (a # Ψ) # Ψ') = Φ' Φ (a # Ψ Ψ')`
  (`TauCeti.Symbol.frameChange_frameChange`). Both sides quantize to the same operator, and a symbol
  is determined by its quantization.
* **Locality.** Modulo smoothing symbols the frame change only depends on the germs of `Ψ` at the
  points where `Φ ≠ 0` (`TauCeti.Symbol.isSmoothing_frameChange_sub_frameChange`). If `Ψ = T` is
  constant near those points, the frame change is `Φ a T` up to a smoothing symbol
  (`TauCeti.Symbol.exists_isSmoothing_coefficient_frameChange_eq`); with `T = 0` it is smoothing
  (`TauCeti.Symbol.isSmoothing_frameChange_of_eventuallyEq_zero`). Together with the composition
  law, changing frames by `(Φ, Ψ)` and back by `(Φ', Ψ')` with `Ψ Ψ' = id` near the points where
  `Φ' Φ ≠ 0` returns `Φ' Φ a` up to a smoothing symbol.

## Main declarations

* `TauCeti.Symbol.frameChange a Φ Ψ`: the symbol `Φ (a # Ψ)` of `u ↦ Φ · Op(a) (Ψ u)`, with
  `TauCeti.Symbol.quantizeSchwartzValue_frameChange`.
* `TauCeti.Symbol.exists_coefficient_frameChange_eq_sum`,
  `TauCeti.Symbol.exists_coefficient_frameChange_eq`: the frame transformation formula, to any
  order and explicitly to second order.
* `TauCeti.Symbol.frameChange_frameChange`: changes of frame compose.
* `TauCeti.Symbol.exists_isSmoothing_coefficient_frameChange_eq`,
  `TauCeti.Symbol.isSmoothing_frameChange_of_eventuallyEq_zero`,
  `TauCeti.Symbol.isSmoothing_frameChange_sub_frameChange`: locality modulo smoothing symbols.

## References

* M. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI* (2008), Lecture I, (2.5)–(2.7)
  and §8.
* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, §18.1 (composition,
  Theorem 18.1.8, and pseudodifferential operators on vector bundles).
-/

public section

noncomputable section

open Filter Finset MeasureTheory
open scoped ContDiff SchwartzMap Topology RealInnerProductSpace FourierTransform

namespace TauCeti

namespace Symbol

variable {n : ℕ} {m : ℝ} {V V' W W' : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [NormedAddCommGroup V'] [NormedSpace ℂ V'] [NormedAddCommGroup W] [NormedSpace ℂ W]
  [NormedAddCommGroup W'] [NormedSpace ℂ W']
  {Φ : CoordinateSpace n → W →L[ℂ] W'} {Ψ : CoordinateSpace n → V' →L[ℂ] V}

/-! ### The frame change of a symbol -/

section Def

/-- The **frame change** of a symbol `a` of order `m` by a smooth family `Φ(x) : W → W'` and a
compactly supported smooth family `Ψ(x) : V' → V`: the symbol `Φ(x) (a # Ψ)(x, ξ)` of order `m`,
whose quantization is `u ↦ Φ · Op(a) (Ψ u)` (`TauCeti.Symbol.quantizeSchwartzValue_frameChange`).
For real scalar `Φ` and `Ψ` this is the compression of `a` by two cutoffs. -/
def frameChange (a : Symbol n V W m) (Φ : CoordinateSpace n → W →L[ℂ] W')
    (Ψ : CoordinateSpace n → V' →L[ℂ] V) (hΦ : ContDiff ℝ ∞ Φ) (hΨ : ContDiff ℝ ∞ Ψ)
    (hΨc : HasCompactSupport Ψ) : Symbol n V' W' m :=
  inclusion (by simp) ((ofSpatial Φ hΦ).comp
    (a.sharp (ofSpatial Ψ hΨ) ((hasCompactSpatialSupport_ofSpatial_iff hΨ).2 hΨc)))

variable {a : Symbol n V W m} (hΦ : ContDiff ℝ ∞ Φ) (hΨ : ContDiff ℝ ∞ Ψ)
  (hΨc : HasCompactSupport Ψ)

/-- The coefficient of the frame change `Φ (a # Ψ)`. -/
@[simp]
theorem coefficient_frameChange (p : CoordinateSpace n × CoordinateSpace n) :
    (a.frameChange Φ Ψ hΦ hΨ hΨc).coefficient p = (Φ p.1).comp
      ((a.sharp (ofSpatial Ψ hΨ) ((hasCompactSpatialSupport_ofSpatial_iff hΨ).2 hΨc)).coefficient
        p) := by
  simp [frameChange]

include hΦ hΨ hΨc

theorem add_frameChange (a b : Symbol n V W m) :
    (a + b).frameChange Φ Ψ hΦ hΨ hΨc = a.frameChange Φ Ψ hΦ hΨ hΨc + b.frameChange Φ Ψ hΦ hΨ hΨc
    := by
  ext1
  funext p
  simp [add_sharp]

@[simp]
theorem smul_frameChange (c : ℂ) (a : Symbol n V W m) :
    (c • a).frameChange Φ Ψ hΦ hΨ hΨc = c • a.frameChange Φ Ψ hΦ hΨ hΨc := by
  ext1
  funext p
  simp [smul_sharp]

@[simp]
theorem zero_frameChange : (0 : Symbol n V W m).frameChange Φ Ψ hΦ hΨ hΨc = 0 := by
  simpa using smul_frameChange hΦ hΨ hΨc 0 (0 : Symbol n V W m)

@[simp]
theorem neg_frameChange (a : Symbol n V W m) :
    (-a).frameChange Φ Ψ hΦ hΨ hΨc = -a.frameChange Φ Ψ hΦ hΨ hΨc := by
  simpa using smul_frameChange hΦ hΨ hΨc (-1) a

theorem sub_frameChange (a b : Symbol n V W m) :
    (a - b).frameChange Φ Ψ hΦ hΨ hΨc = a.frameChange Φ Ψ hΦ hΨ hΨc - b.frameChange Φ Ψ hΦ hΨ hΨc
    := by
  rw [sub_eq_add_neg, add_frameChange, neg_frameChange, ← sub_eq_add_neg]

theorem inclusion_frameChange {m' : ℝ} (h : m ≤ m') (a : Symbol n V W m) :
    (inclusion h a).frameChange Φ Ψ hΦ hΨ hΨc = inclusion h (a.frameChange Φ Ψ hΦ hΨ hΨc) := by
  ext1
  funext p
  simp [inclusion_sharp]

/-- The frame change is additive in the output transition map. -/
theorem frameChange_add_left {Φ' : CoordinateSpace n → W →L[ℂ] W'} (hΦ' : ContDiff ℝ ∞ Φ') :
    a.frameChange (Φ + Φ') Ψ (hΦ.add hΦ') hΨ hΨc =
      a.frameChange Φ Ψ hΦ hΨ hΨc + a.frameChange Φ' Ψ hΦ' hΨ hΨc := by
  ext1
  funext p
  simp [ContinuousLinearMap.add_comp]

/-- The frame change is additive in the input transition map. -/
theorem frameChange_add_right {Ψ' : CoordinateSpace n → V' →L[ℂ] V} (hΨ' : ContDiff ℝ ∞ Ψ')
    (hΨ'c : HasCompactSupport Ψ') :
    a.frameChange Φ (Ψ + Ψ') hΦ (hΨ.add hΨ') (hΨc.add hΨ'c) =
      a.frameChange Φ Ψ hΦ hΨ hΨc + a.frameChange Φ Ψ' hΦ hΨ' hΨ'c := by
  ext1
  funext p
  rw [coefficient_frameChange, sharp_congr _ (((hasCompactSpatialSupport_ofSpatial_iff hΨ).2
      hΨc).add ((hasCompactSpatialSupport_ofSpatial_iff hΨ').2 hΨ'c)) (ofSpatial_add hΨ hΨ'),
    sharp_add _ ((hasCompactSpatialSupport_ofSpatial_iff hΨ).2 hΨc)
      ((hasCompactSpatialSupport_ofSpatial_iff hΨ').2 hΨ'c)]
  simp [ContinuousLinearMap.comp_add]

/-- The frame change commutes with subtraction of input transition maps. -/
theorem frameChange_sub_right {Ψ' : CoordinateSpace n → V' →L[ℂ] V} (hΨ' : ContDiff ℝ ∞ Ψ')
    (hΨ'c : HasCompactSupport Ψ') :
    a.frameChange Φ (Ψ - Ψ') hΦ (hΨ.sub hΨ') (hΨc.sub hΨ'c) =
      a.frameChange Φ Ψ hΦ hΨ hΨc - a.frameChange Φ Ψ' hΦ hΨ' hΨ'c := by
  ext1
  funext p
  rw [coefficient_frameChange, sharp_congr _ (((hasCompactSpatialSupport_ofSpatial_iff hΨ).2
      hΨc).sub ((hasCompactSpatialSupport_ofSpatial_iff hΨ').2 hΨ'c)) (ofSpatial_sub hΨ hΨ'),
    sharp_sub _ ((hasCompactSpatialSupport_ofSpatial_iff hΨ).2 hΨc)
      ((hasCompactSpatialSupport_ofSpatial_iff hΨ').2 hΨ'c)]
  simp [ContinuousLinearMap.comp_sub]

omit hΦ in
@[simp]
theorem frameChange_zero_left (hΦ : ContDiff ℝ ∞ (0 : CoordinateSpace n → W →L[ℂ] W')) :
    a.frameChange 0 Ψ hΦ hΨ hΨc = 0 := by
  ext1
  funext p
  simp

omit hΨ hΨc in
@[simp]
theorem frameChange_zero_right (hΨ : ContDiff ℝ ∞ (0 : CoordinateSpace n → V' →L[ℂ] V))
    (hΨc : HasCompactSupport (0 : CoordinateSpace n → V' →L[ℂ] V)) :
    a.frameChange Φ 0 hΦ hΨ hΨc = 0 := by
  ext1
  funext p
  rw [coefficient_frameChange, sharp_congr _ hasCompactSpatialSupport_zero (ofSpatial_zero hΨ),
    sharp_zero]
  simp

/-- The frame change of a symbol with compact spatial support has compact spatial support. -/
theorem HasCompactSpatialSupport.frameChange (ha : a.HasCompactSpatialSupport) :
    (a.frameChange Φ Ψ hΦ hΨ hΨc).HasCompactSpatialSupport :=
  ((ha.sharp _).comp_left _).inclusion _

/-- A frame change by a compactly supported output transition map has compact spatial support. -/
theorem hasCompactSpatialSupport_frameChange (hΦc : HasCompactSupport Φ) :
    (a.frameChange Φ Ψ hΦ hΨ hΨc).HasCompactSpatialSupport :=
  (((hasCompactSpatialSupport_ofSpatial_iff hΦ).2 hΦc).comp_right _).inclusion _

/-- The frame change of a smoothing symbol is smoothing. -/
theorem IsSmoothing.frameChange (ha : a.IsSmoothing) :
    (a.frameChange Φ Ψ hΦ hΨ hΨc).IsSmoothing :=
  ((ha.sharp_right _ _).comp_left _).inclusion _

end Def

/-! ### The quantization of a frame change -/

section Operator

variable [CompleteSpace V] [CompleteSpace V'] [CompleteSpace W] [CompleteSpace W']
  {a : Symbol n V W m}
  (hΦ : ContDiff ℝ ∞ Φ) (hΨ : ContDiff ℝ ∞ Ψ) (hΨc : HasCompactSupport Ψ)

/-- **The quantization of a frame change** is the operator in the new frames:
`Op(Φ (a # Ψ)) u = Φ · Op(a) (Ψ u)`, for every Schwartz function `v` equal to `Ψ u`. -/
theorem quantizeSchwartzValue_frameChange (u : 𝓢(CoordinateSpace n, V'))
    (v : 𝓢(CoordinateSpace n, V)) (hv : ∀ y, v y = Ψ y (u y)) (x : CoordinateSpace n) :
    quantizeSchwartzValue (a.frameChange Φ Ψ hΦ hΨ hΨc).coefficient u x =
      Φ x (quantizeSchwartzValue a.coefficient v x) := by
  set hb := (hasCompactSpatialSupport_ofSpatial_iff hΨ).2 hΨc
  set c := a.sharp (ofSpatial Ψ hΨ) hb
  obtain ⟨C, hC⟩ := c.exists_norm_coefficient_le {x} isCompact_singleton
  have hint := integrable_quantizeSchwartzValue_integrand
    ((c.contDiff_coefficient.continuous.comp (continuous_const.prodMk continuous_id)
      ).aestronglyMeasurable) (hC x rfl) (𝓕 u)
  calc quantizeSchwartzValue (a.frameChange Φ Ψ hΦ hΨ hΨc).coefficient u x
      = ∫ ζ, Φ x (𝐞 ⟪ζ, x⟫ • c.coefficient (x, (2 * Real.pi) • ζ) (𝓕 u ζ)) := by
        simp [quantizeSchwartzValue_def, c, Circle.smul_def]
    _ = Φ x (quantizeSchwartzValue c.coefficient u x) := by
        rw [(Φ x).integral_comp_comm hint, quantizeSchwartzValue_def]
    _ = Φ x (quantizeSchwartzValue a.coefficient v x) := by
        rw [quantizeSchwartzValue_sharp_eq_quantizeSchwartzValue hb]
        congr 2
        ext y
        rw [HasCompactSupport.toSchwartzMap_toFun, coefficient_ofSpatial_eq,
          quantizeSchwartzValue_comp_fst, hv]

variable {V'' W'' : Type*} [NormedAddCommGroup V''] [NormedSpace ℂ V''] [CompleteSpace V'']
  [NormedAddCommGroup W''] [NormedSpace ℂ W''] [CompleteSpace W'']
  {Φ' : CoordinateSpace n → W' →L[ℂ] W''} {Ψ' : CoordinateSpace n → V'' →L[ℂ] V'}

/-- **Changes of frame compose.** Changing frames by `(Φ, Ψ)` and then by `(Φ', Ψ')` is the change
of frame by `(Φ' Φ, Ψ Ψ')`: `Φ' (Φ (a # Ψ) # Ψ') = Φ' Φ (a # Ψ Ψ')`. -/
theorem frameChange_frameChange (hΦ' : ContDiff ℝ ∞ Φ') (hΨ' : ContDiff ℝ ∞ Ψ')
    (hΨ'c : HasCompactSupport Ψ') :
    (a.frameChange Φ Ψ hΦ hΨ hΨc).frameChange Φ' Ψ' hΦ' hΨ' hΨ'c =
      a.frameChange (fun x ↦ (Φ' x).comp (Φ x)) (fun x ↦ (Ψ x).comp (Ψ' x))
        ((((ContinuousLinearMap.compL ℂ W W' W'').bilinearRestrictScalars ℝ
          ).isBoundedBilinearMap.contDiff (n := ∞)).comp (hΦ'.prodMk hΦ))
        ((((ContinuousLinearMap.compL ℂ V'' V' V).bilinearRestrictScalars ℝ
          ).isBoundedBilinearMap.contDiff (n := ∞)).comp (hΨ.prodMk hΨ'))
        (hΨ'c.mono fun y hy h ↦ hy (by simp [h])) := by
  ext1
  refine coefficient_eq_of_forall_quantizeSchwartzValue_eq fun u _ ↦ funext fun x ↦ ?_
  -- The products `Ψ' u` and `Ψ (Ψ' u)` as Schwartz functions.
  set v := SchwartzMap.bilinLeftCLM (ContinuousLinearMap.apply ℂ V')
    (hΨ'c.hasTemperateGrowth hΨ') u
  set w := SchwartzMap.bilinLeftCLM (ContinuousLinearMap.apply ℂ V) (hΨc.hasTemperateGrowth hΨ) v
  rw [quantizeSchwartzValue_frameChange hΦ' hΨ' hΨ'c u v fun _ ↦ rfl,
    quantizeSchwartzValue_frameChange hΦ hΨ hΨc v w fun _ ↦ rfl]
  exact (quantizeSchwartzValue_frameChange (a := a) (Φ := fun x ↦ (Φ' x).comp (Φ x))
    (Ψ := fun x ↦ (Ψ x).comp (Ψ' x)) _ _ _ u w (fun _ ↦ rfl) x).symm

end Operator

/-! ### The frame transformation formula -/

section Expansion

variable {a : Symbol n V W m} (hΦ : ContDiff ℝ ∞ Φ) (hΨ : ContDiff ℝ ∞ Ψ)
  (hΨc : HasCompactSupport Ψ)

/-- If `Ψ` is constant near `x`, every term of index `k ≥ 1` of the expansion of `a # Ψ` vanishes
at `x`. -/
private theorem coefficient_sharpTerm_ofSpatial_eq_zero {x : CoordinateSpace n} {T : V' →L[ℂ] V}
    (hx : Ψ =ᶠ[𝓝 x] fun _ ↦ T) {k : ℕ} (hk : k ≠ 0) (ξ : CoordinateSpace n) :
    (a.sharpTerm (ofSpatial Ψ hΨ) k).coefficient (x, ξ) = 0 := by
  rw [coefficient_sharpTerm_ofSpatial, Finset.sum_eq_zero, smul_zero]
  intro w _
  rw [(hx.coordinateDeriv _).eq_of_nhds, coordinateDeriv_const T (by simpa using hk),
    Pi.zero_apply, ContinuousLinearMap.comp_zero]

variable [CompleteSpace V] [CompleteSpace W]

/-- The remainder `Φ r` of a frame change, for a remainder `r` of order `m - N` of the expansion of
`a # Ψ`. -/
private def remainder (N : ℕ) : Symbol n V' W' (m - N) :=
  inclusion (by simp) ((ofSpatial Φ hΦ).comp
    (a.sharpRemainder (ofSpatial Ψ hΨ) ((hasCompactSpatialSupport_ofSpatial_iff hΨ).2 hΨc) N))

/-- The frame change is the expansion of `Φ (a # Ψ)` with `N` terms plus the remainder. -/
private theorem coefficient_frameChange_eq_sum (N : ℕ) (x ξ : CoordinateSpace n) :
    (a.frameChange Φ Ψ hΦ hΨ hΨc).coefficient (x, ξ) =
      ∑ k ∈ range N, (Φ x).comp ((a.sharpTerm (ofSpatial Ψ hΨ) k).coefficient (x, ξ)) +
        (remainder (a := a) hΦ hΨ hΨc N).coefficient (x, ξ) := by
  simp [remainder, ← ContinuousLinearMap.comp_finsetSum]

/-- **The frame transformation formula.** For every `N`, the frame change of a symbol `a` of order
`m` by `Φ` and `Ψ` is

`Φ (a # Ψ) = ∑_{k < N} ((-i)^k / k!) ∑_{|w| = k} Φ ∘ ∂_ξ^w a ∘ ∂_x^w Ψ`

up to a symbol of order `m - N`. -/
theorem exists_coefficient_frameChange_eq_sum (N : ℕ) :
    ∃ r : Symbol n V' W' (m - N), ∀ x ξ, (a.frameChange Φ Ψ hΦ hΨ hΨc).coefficient (x, ξ) =
      ∑ k ∈ range N, ((-Complex.I) ^ k / k.factorial) • ∑ w : Fin k → Fin n,
        (Φ x).comp ((mixedDeriv [] (List.ofFn w) a.coefficient x ξ).comp
          (coordinateDeriv (List.ofFn w) Ψ x)) + r.coefficient (x, ξ) := by
  refine ⟨remainder (a := a) hΦ hΨ hΨc N, fun x ξ ↦ ?_⟩
  rw [coefficient_frameChange_eq_sum hΦ hΨ hΨc N]
  simp only [coefficient_sharpTerm_ofSpatial, ContinuousLinearMap.comp_smul,
    ContinuousLinearMap.comp_finsetSum]

/-- **The frame transformation formula to second order.** The frame change of a symbol `a` of
order `m` by `Φ` and `Ψ` is

`Φ (a # Ψ) = Φ a Ψ - i ∑ⱼ Φ ∂_{ξⱼ} a ∂ⱼΨ`

up to a symbol of order `m - 2`. In particular its principal part `Φ a Ψ` transforms as a
`Hom`-valued function, while the next term depends on the derivatives of `Ψ`. -/
theorem exists_coefficient_frameChange_eq :
    ∃ r : Symbol n V' W' (m - 2), ∀ x ξ, (a.frameChange Φ Ψ hΦ hΨ hΨc).coefficient (x, ξ) =
      (Φ x).comp ((a.coefficient (x, ξ)).comp (Ψ x)) - Complex.I • ∑ j,
        (Φ x).comp (((frequencyDeriv j a).coefficient (x, ξ)).comp (coordinateDeriv [j] Ψ x)) +
        r.coefficient (x, ξ) := by
  refine ⟨inclusion (by norm_num) (remainder (a := a) hΦ hΨ hΨc 2), fun x ξ ↦ ?_⟩
  have hj (j : Fin n) :
      (spatialDeriv j (ofSpatial Ψ hΨ)).coefficient (x, ξ) = coordinateDeriv [j] Ψ x := by
    rw [← mixedDeriv_nil_nil (spatialDeriv j (ofSpatial Ψ hΨ)).coefficient, mixedDeriv_spatialDeriv,
      List.nil_append, coefficient_ofSpatial_eq, mixedDeriv_nil_comp_fst]
  rw [coefficient_frameChange_eq_sum hΦ hΨ hΨc 2, coefficient_inclusion, sum_range_succ,
    sum_range_one, coefficient_sharpTerm_zero, coefficient_sharpTerm_one]
  simp only [hj, coefficient_ofSpatial, ContinuousLinearMap.comp_neg,
    ContinuousLinearMap.comp_smul, ContinuousLinearMap.comp_finsetSum, sub_eq_add_neg, neg_smul]

/-- **Frame changes by input transition maps that are constant near the support of the output
one.** If `Ψ = T` near every point where `Φ ≠ 0`, the frame change `Φ (a # Ψ)` is the product
`Φ a T` up to a symbol of order `m - (N + 1)`, for every `N`. -/
private theorem coefficient_frameChange_eq_of_eventuallyEq {T : V' →L[ℂ] V}
    (hΨΦ : ∀ x ∈ Function.support Φ, Ψ =ᶠ[𝓝 x] fun _ ↦ T) (N : ℕ) (x ξ : CoordinateSpace n) :
    (a.frameChange Φ Ψ hΦ hΨ hΨc).coefficient (x, ξ) =
      (Φ x).comp ((a.coefficient (x, ξ)).comp T) +
        (remainder (a := a) hΦ hΨ hΨc (N + 1)).coefficient (x, ξ) := by
  rw [coefficient_frameChange_eq_sum hΦ hΨ hΨc (N + 1)]
  congr 1
  by_cases hx : Φ x = 0
  · simp [hx]
  have hΨx := hΨΦ x hx
  rw [sum_range_succ', Finset.sum_eq_zero fun k _ ↦ by
      rw [coefficient_sharpTerm_ofSpatial_eq_zero hΨ hΨx (Nat.succ_ne_zero k) ξ,
        ContinuousLinearMap.comp_zero], zero_add, coefficient_sharpTerm_zero,
    coefficient_ofSpatial, hΨx.eq_of_nhds]

/-- **Frame changes by input transition maps that are constant near the support of the output
one.** If `Ψ = T` near every point where `Φ ≠ 0`, the frame change `Φ (a # Ψ)` is the product
`Φ a T` up to a smoothing symbol. -/
theorem exists_isSmoothing_coefficient_frameChange_eq {T : V' →L[ℂ] V}
    (hΨΦ : ∀ x ∈ Function.support Φ, Ψ =ᶠ[𝓝 x] fun _ ↦ T) :
    ∃ r : Symbol n V' W' m, r.IsSmoothing ∧ ∀ x ξ,
      (a.frameChange Φ Ψ hΦ hΨ hΨc).coefficient (x, ξ) =
        (Φ x).comp ((a.coefficient (x, ξ)).comp T) + r.coefficient (x, ξ) := by
  have h := coefficient_frameChange_eq_of_eventuallyEq (a := a) hΦ hΨ hΨc hΨΦ
  refine ⟨inclusion (by push_cast; linarith) (remainder (a := a) hΦ hΨ hΨc (0 + 1)),
    isSmoothing_iff_forall_nat.2 fun N ↦ ⟨inclusion (by push_cast; linarith)
      (remainder (a := a) hΦ hΨ hΨc (N + 1)), funext fun ⟨x, ξ⟩ ↦ ?_⟩, fun x ξ ↦ ?_⟩
  · rw [coefficient_inclusion, coefficient_inclusion]
    exact add_left_cancel ((h N x ξ).symm.trans (h 0 x ξ))
  · rw [h 0 x ξ, coefficient_inclusion]

/-- **Frame changes by an input transition map vanishing near the support of the output one.** If
`Ψ = 0` near every point where `Φ ≠ 0`, the frame change `Φ (a # Ψ)` is smoothing. -/
theorem isSmoothing_frameChange_of_eventuallyEq_zero
    (hΨΦ : ∀ x ∈ Function.support Φ, Ψ =ᶠ[𝓝 x] 0) :
    (a.frameChange Φ Ψ hΦ hΨ hΨc).IsSmoothing := by
  obtain ⟨r, hr, h⟩ := exists_isSmoothing_coefficient_frameChange_eq (a := a) hΦ hΨ hΨc
    (T := 0) hΨΦ
  exact isSmoothing_iff.2 fun m' ↦ (isSmoothing_iff.1 hr m').imp fun b hb ↦ by
    rw [hb]
    funext ⟨x, ξ⟩
    rw [h x ξ]
    simp

/-- **Locality of frame changes.** If `Ψ` and `Ψ'` agree near every point where `Φ ≠ 0`, the frame
changes of `a` by `Φ, Ψ` and by `Φ, Ψ'` differ by a smoothing symbol. -/
theorem isSmoothing_frameChange_sub_frameChange {Ψ' : CoordinateSpace n → V' →L[ℂ] V}
    (hΨ' : ContDiff ℝ ∞ Ψ') (hΨ'c : HasCompactSupport Ψ')
    (hΨΨ' : ∀ x ∈ Function.support Φ, Ψ =ᶠ[𝓝 x] Ψ') :
    (a.frameChange Φ Ψ hΦ hΨ hΨc - a.frameChange Φ Ψ' hΦ hΨ' hΨ'c).IsSmoothing := by
  rw [← frameChange_sub_right]
  exact isSmoothing_frameChange_of_eventuallyEq_zero _ _ _ fun x hx ↦ (hΨΨ' x hx).sub_eq

end Expansion

end Symbol

end TauCeti
