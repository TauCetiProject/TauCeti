/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Lp.ProdLp.Lipschitz
public import TauCeti.Analysis.Sobolev.Trace.Continuous
public import TauCeti.MeasureTheory.Measure.Haar.InnerProductSpace.Prod
import TauCeti.Analysis.Sobolev.Trace.HalfSpace
import TauCeti.Analysis.Sobolev.W1p.Density
import TauCeti.MeasureTheory.Function.Lp.CompMeasurePreserving.Equiv
import TauCeti.MeasureTheory.Measure.Restrict

/-!
# The flat trace under tangential changes of variables

Let `Φ` be a volume-preserving map of the product `ℝ × E`, `E` a finite-dimensional real inner
product space, that is locally Lipschitz with bounded derivative, so that precomposition with it
acts on `W^{1,p}` (`TauCeti.W1p.compMeasurePreservingL`), and suppose that on the hyperplane
`{a} × E` it acts tangentially, `Φ (a, y) = (a, ψ y)`, through a volume-preserving map `ψ` of `E`.
This file proves, for `1 ≤ p < ∞`, that the traces on `{a} × E` commute with these changes of
variables:

`Tr (u ∘ Φ) = (Tr u) ∘ ψ` in `Lᵖ(E)`,

for the flat trace of a whole-space function (`TauCeti.W1p.hyperplaneTrace_compMeasurePreservingL`)
and, when `Φ` also maps the half-space `H = {a < t}` into itself, `H = Φ⁻¹(H)`, and is continuous
up to its boundary, for the trace of a function on `H`
(`TauCeti.W1p.halfSpaceTrace_compMeasurePreservingL`). So `ψ` carries the set where the trace of
`u ∘ Φ` vanishes to the set where the trace of `u` vanishes
(`TauCeti.W1p.halfSpaceTrace_compMeasurePreservingL_ae_eq_zero_iff`).

The basic instance is the map `Ψ (t, y) = (t, ψ y)`, written `WithLp.map 2 (Prod.map id ψ)`, for a
volume-preserving `K`-Lipschitz map `ψ` of `E`: it preserves volume
(`MeasureTheory.MeasurePreserving.withLpProdMap`) and each half-space
(`TauCeti.preimage_withLpMap_prodMap_id_normalHalfSpace`), and it is `max 1 K`-Lipschitz
(`LipschitzWith.withLpProdMap`), so the half-space statement applies to it
(`TauCeti.W1p.halfSpaceTrace_compMeasurePreservingL_withLpMap_prodMap_id`). Such `ψ` are the
tangential translations, the linear isometries of `E`, and the Lipschitz shears of the base: for
an affine isometry `e : E ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × E')` and a Lipschitz `β : E' → ℝ`, the map
`e⁻¹ ∘ TauCeti.graphFlattening β ∘ e` subtracts `β` of the other coordinates from the first
coordinate of `e y`. It preserves volume (`TauCeti.measurePreserving_graphFlattening`,
`AffineIsometryEquiv.measurePreserving`), is Lipschitz
(`TauCeti.lipschitzWith_graphFlattening`), and carries the region `{y | β (e y).snd < (e y).fst}`
of the boundary hyperplane onto `{y | 0 < (e y).fst}`. Together with the graph flattening of the
normal coordinate, which carries the region above a Lipschitz graph onto a half-space
(`TauCeti.W1p.normalEpigraphTrace`), it straightens a part of the boundary of a Lipschitz domain
lying over the region above a Lipschitz interface into a half-hyperplane, keeping track of the
trace.

## The argument

Both sides are continuous linear in `u`, so it suffices to compare them on a dense set. On a test
function `φ` of the whole space, `φ ∘ Φ` is continuous, so its trace is its restriction
`y ↦ φ (Φ (a, y)) = φ (a, ψ y)` (`TauCeti.W1p.hyperplaneTrace_apply_ae_of_continuous`), which is the
trace of `φ` composed with `ψ`; test functions are dense in `W^{1,p}` of the whole space. On the
half-space the dense set is the restrictions of test functions, since restriction undoes the
reflection extension, and `φ ∘ Φ` is continuous up to the boundary
(`TauCeti.W1p.halfSpaceTrace_apply_ae_of_continuousOn`).

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., §5.5 (the trace operator, defined by
  restricting continuous functions and extending by density).
-/

public section

namespace TauCeti

open MeasureTheory Set TopologicalSpace
open scoped ENNReal NNReal Distributions

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {p : ℝ≥0∞} [Fact (1 ≤ p)] {ψ : E → E}
  {Φ : WithLp 2 (ℝ × E) → WithLp 2 (ℝ × E)} {M : ℝ}

/-- **The flat trace commutes with changes of variables acting tangentially on the hyperplane.**
Let `Φ` be a volume-preserving map of `ℝ × E`, locally Lipschitz with `‖DΦ‖ ≤ M`, that maps each
point `(a, y)` of the hyperplane `{a} × E` to `(a, ψ y)` for a volume-preserving `ψ`. For
`1 ≤ p < ∞` and a whole-space `u ∈ W^{1,p}`, the trace of `u ∘ Φ` on `{a} × E` is the trace of `u`
composed with `ψ`. -/
theorem W1p.hyperplaneTrace_compMeasurePreservingL (hp : p ≠ ∞) (a : ℝ)
    (hΦ : MeasurePreserving Φ (volume : Measure (WithLp 2 (ℝ × E))) volume)
    (hUV : ((⊤ : Opens (WithLp 2 (ℝ × E))) : Set (WithLp 2 (ℝ × E))) =
      Φ ⁻¹' (⊤ : Opens (WithLp 2 (ℝ × E))))
    (hΦl : LocallyLipschitzOn (⊤ : Opens (WithLp 2 (ℝ × E))) Φ)
    (hM : ∀ x ∈ ((⊤ : Opens (WithLp 2 (ℝ × E))) : Set (WithLp 2 (ℝ × E))), ‖fderiv ℝ Φ x‖ ≤ M)
    (hψ : MeasurePreserving ψ) (hΦa : ∀ y : E, Φ (WithLp.toLp 2 (a, y)) = WithLp.toLp 2 (a, ψ y))
    (u : W1p (volume : Measure (WithLp 2 (ℝ × E))) ⊤ p) :
    W1p.hyperplaneTrace hp a (W1p.compMeasurePreservingL hΦ hUV hΦl hM u) =
      Lp.compMeasurePreserving ψ hψ (W1p.hyperplaneTrace hp a u) := by
  have hΦc : Continuous Φ := by
    have h := hΦl.continuousOn
    rw [Opens.coe_top] at h
    exact continuousOn_univ.1 h
  let C : W1p (volume : Measure (WithLp 2 (ℝ × E))) ⊤ p →L[ℝ]
      W1p (volume : Measure (WithLp 2 (ℝ × E))) ⊤ p :=
    W1p.compMeasurePreservingL hΦ hUV hΦl hM
  -- Both sides are continuous in `u`, so it suffices to compare them on test functions.
  have key : (fun v => W1p.hyperplaneTrace hp a (C v)) =
      fun v => Lp.compMeasurePreserving ψ hψ (W1p.hyperplaneTrace hp a v) := by
    refine (W1p.denseRange_ofTestFunctionₗ_top hp).equalizer
      ((W1p.hyperplaneTrace hp a).continuous.comp C.continuous)
      ((Lp.compMeasurePreservingₗᵢ ℝ ψ hψ (E := ℝ) (p := p)).continuous.comp
        (W1p.hyperplaneTrace hp a).continuous)
      (funext fun φ => Lp.ext ?_)
    -- On a test function `φ`, `φ ∘ Φ` is continuous, and its trace is its restriction.
    have hval : W1p.value (C (W1p.ofTestFunctionₗ volume ⊤ p φ)) =ᵐ[volume] fun x => φ (Φ x) := by
      have h := W1p.value_compMeasurePreservingL_ae hΦ hUV hΦl hM
        (W1p.ofTestFunctionₗ volume ⊤ p φ)
      rw [Measure.ae_restrict_coe_opens_top] at h
      filter_upwards [h, hΦ.quasiMeasurePreserving.ae (W1p.value_ofTestFunctionₗ_top_ae (p := p) φ)]
        with x h1 h2
      rw [h1, h2]
    filter_upwards [W1p.hyperplaneTrace_apply_ae_of_continuous hp a (φ.continuous.comp hΦc) hval,
      Lp.coeFn_compMeasurePreserving (W1p.hyperplaneTrace hp a (W1p.ofTestFunctionₗ volume ⊤ p φ))
        hψ, hψ.quasiMeasurePreserving.ae (W1p.hyperplaneTrace_ofTestFunction_apply_ae hp a φ)]
      with y h1 h2 h3
    simp only [Function.comp_apply] at h1 h2 ⊢
    rw [h1, h2, h3, hΦa]
  exact congrFun key u

/-- **The half-space trace commutes with changes of variables acting tangentially on the
boundary.** Let `Φ` be a volume-preserving map of `ℝ × E` that maps the half-space `H = {a < t}`
into itself, `H = Φ⁻¹(H)`, is locally Lipschitz on `H` with `‖DΦ‖ ≤ M` there, is continuous on the
closed half-space, and maps each point `(a, y)` of the boundary hyperplane to `(a, ψ y)` for a
volume-preserving `ψ`. For `1 ≤ p < ∞` and `u ∈ W^{1,p}(H)`, the trace of `u ∘ Φ` on `{a} × E` is
the trace of `u` composed with `ψ`. -/
theorem W1p.halfSpaceTrace_compMeasurePreservingL (hp : p ≠ ∞) (a : ℝ)
    (hΦ : MeasurePreserving Φ (volume : Measure (WithLp 2 (ℝ × E))) volume)
    (hUV : (normalHalfSpace (E := E) a : Set (WithLp 2 (ℝ × E))) =
      Φ ⁻¹' normalHalfSpace (E := E) a)
    (hΦl : LocallyLipschitzOn (normalHalfSpace (E := E) a : Set (WithLp 2 (ℝ × E))) Φ)
    (hM : ∀ x ∈ (normalHalfSpace (E := E) a : Set (WithLp 2 (ℝ × E))), ‖fderiv ℝ Φ x‖ ≤ M)
    (hΦc : ContinuousOn Φ {x | a ≤ x.fst}) (hψ : MeasurePreserving ψ)
    (hΦa : ∀ y : E, Φ (WithLp.toLp 2 (a, y)) = WithLp.toLp 2 (a, ψ y))
    (u : W1p (volume : Measure (WithLp 2 (ℝ × E))) (normalHalfSpace a) p) :
    W1p.halfSpaceTrace hp a (W1p.compMeasurePreservingL hΦ hUV hΦl hM u) =
      Lp.compMeasurePreserving ψ hψ (W1p.halfSpaceTrace hp a u) := by
  have hle : normalHalfSpace (E := E) a ≤ ⊤ := le_top
  have hH : MeasurableSet (normalHalfSpace (E := E) a : Set (WithLp 2 (ℝ × E))) :=
    (normalHalfSpace (E := E) a).isOpen.measurableSet
  let C : W1p (volume : Measure (WithLp 2 (ℝ × E))) (normalHalfSpace a) p →L[ℝ]
      W1p (volume : Measure (WithLp 2 (ℝ × E))) (normalHalfSpace a) p :=
    W1p.compMeasurePreservingL hΦ hUV hΦl hM
  -- Restrictions of test functions are dense in `W^{1,p}(H)`: restriction is onto, since it
  -- undoes the reflection extension.
  have hd : DenseRange fun φ : 𝓓((⊤ : Opens (WithLp 2 (ℝ × E))), ℝ) =>
      W1p.restrictL hle (W1p.ofTestFunctionₗ volume ⊤ p φ) :=
    (Function.RightInverse.surjective (W1p.restrictL_extendByReflectionL a)).denseRange.comp
      (W1p.denseRange_ofTestFunctionₗ_top hp) (W1p.restrictL hle).continuous
  have key : (fun v => W1p.halfSpaceTrace hp a (C v)) =
      fun v => Lp.compMeasurePreserving ψ hψ (W1p.halfSpaceTrace hp a v) := by
    refine hd.equalizer ((W1p.halfSpaceTrace hp a).continuous.comp C.continuous)
      ((Lp.compMeasurePreservingₗᵢ ℝ ψ hψ (E := ℝ) (p := p)).continuous.comp
        (W1p.halfSpaceTrace hp a).continuous)
      (funext fun φ => Lp.ext ?_)
    -- On the restriction of a test function `φ`, `u ∘ Φ` agrees on `H` with `φ ∘ Φ`, which is
    -- continuous on the closed half-space, so its trace is its restriction.
    have hφ : ∀ᵐ z ∂volume, z ∈ (normalHalfSpace (E := E) a : Set (WithLp 2 (ℝ × E))) →
        W1p.value (W1p.restrictL hle (W1p.ofTestFunctionₗ volume ⊤ p φ)) z = φ z := by
      refine (ae_restrict_iff' hH).1 ?_
      filter_upwards [W1p.value_restrictL_ae hle (W1p.ofTestFunctionₗ volume ⊤ p φ),
        ae_restrict_of_ae (W1p.value_ofTestFunctionₗ_top_ae (p := p) φ)] with z h1 h2
      rw [h1, h2]
    have hval : W1p.value (C (W1p.restrictL hle (W1p.ofTestFunctionₗ volume ⊤ p φ)))
        =ᵐ[volume.restrict (normalHalfSpace (E := E) a : Set (WithLp 2 (ℝ × E)))]
          fun x => φ (Φ x) := by
      filter_upwards [W1p.value_compMeasurePreservingL_ae hΦ hUV hΦl hM
          (W1p.restrictL hle (W1p.ofTestFunctionₗ volume ⊤ p φ)),
        ae_restrict_of_ae (hΦ.quasiMeasurePreserving.ae hφ), ae_restrict_mem hH] with x h1 h2 hx
      rw [h1, h2 (by rwa [hUV] at hx)]
    filter_upwards [W1p.halfSpaceTrace_apply_ae_of_continuousOn hp a
        (φ.continuous.comp_continuousOn hΦc) hval,
      Lp.coeFn_compMeasurePreserving (W1p.halfSpaceTrace hp a
        (W1p.restrictL hle (W1p.ofTestFunctionₗ volume ⊤ p φ))) hψ,
      hψ.quasiMeasurePreserving.ae (W1p.hyperplaneTrace_ofTestFunction_apply_ae hp a φ)]
      with y h1 h2 h3
    simp only [Function.comp_apply] at h1 h2 ⊢
    rw [h1, h2, W1p.halfSpaceTrace_restrictL, h3, hΦa]
  exact congrFun key u

/-- **The half-space trace under a Lipschitz map of the tangential variables.** For a
volume-preserving `K`-Lipschitz `ψ : E → E`, the map `Ψ (t, y) = (t, ψ y)` preserves volume and the
half-space `H = {a < t}` and is `max 1 K`-Lipschitz, so `u ↦ u ∘ Ψ` acts on `W^{1,p}(H)`; for
`1 ≤ p < ∞` the trace of `u ∘ Ψ` is the trace of `u` composed with `ψ`. The Lipschitz shears of
the base, which move one tangential coordinate by a Lipschitz function of the others, are such
`ψ`. -/
theorem W1p.halfSpaceTrace_compMeasurePreservingL_withLpMap_prodMap_id (hp : p ≠ ∞) (a : ℝ)
    {K : ℝ≥0} (hψ : MeasurePreserving ψ) (hψl : LipschitzWith K ψ)
    (u : W1p (volume : Measure (WithLp 2 (ℝ × E))) (normalHalfSpace a) p) :
    W1p.halfSpaceTrace hp a (W1p.compMeasurePreservingL
        ((MeasurePreserving.id volume).withLpProdMap hψ)
        (preimage_withLpMap_prodMap_id_normalHalfSpace ψ a).symm
        (LipschitzWith.id.withLpProdMap hψl).locallyLipschitz.locallyLipschitzOn
        (fun _ _ => norm_fderiv_le_of_lipschitz ℝ (LipschitzWith.id.withLpProdMap hψl)) u) =
      Lp.compMeasurePreserving ψ hψ (W1p.halfSpaceTrace hp a u) :=
  W1p.halfSpaceTrace_compMeasurePreservingL hp a _ _ _ _
    (LipschitzWith.id.withLpProdMap hψl).continuous.continuousOn hψ (fun _ => by simp) u

/-- **Tangential changes of variables carry the zero set of the half-space trace.** With `Φ` and
`ψ` as in `TauCeti.W1p.halfSpaceTrace_compMeasurePreservingL` and a measurable set `S ⊆ E`, the
trace of `u ∘ Φ` vanishes almost everywhere on `ψ⁻¹(S)` if and only if the trace of `u` vanishes
almost everywhere on `S`. -/
theorem W1p.halfSpaceTrace_compMeasurePreservingL_ae_eq_zero_iff (hp : p ≠ ∞) (a : ℝ)
    (hΦ : MeasurePreserving Φ (volume : Measure (WithLp 2 (ℝ × E))) volume)
    (hUV : (normalHalfSpace (E := E) a : Set (WithLp 2 (ℝ × E))) =
      Φ ⁻¹' normalHalfSpace (E := E) a)
    (hΦl : LocallyLipschitzOn (normalHalfSpace (E := E) a : Set (WithLp 2 (ℝ × E))) Φ)
    (hM : ∀ x ∈ (normalHalfSpace (E := E) a : Set (WithLp 2 (ℝ × E))), ‖fderiv ℝ Φ x‖ ≤ M)
    (hΦc : ContinuousOn Φ {x | a ≤ x.fst}) (hψ : MeasurePreserving ψ)
    (hΦa : ∀ y : E, Φ (WithLp.toLp 2 (a, y)) = WithLp.toLp 2 (a, ψ y))
    (u : W1p (volume : Measure (WithLp 2 (ℝ × E))) (normalHalfSpace a) p) {S : Set E}
    (hS : MeasurableSet S) :
    (∀ᵐ y ∂volume, ψ y ∈ S →
        W1p.halfSpaceTrace hp a (W1p.compMeasurePreservingL hΦ hUV hΦl hM u) y = 0) ↔
      ∀ᵐ z ∂volume, z ∈ S → W1p.halfSpaceTrace hp a u z = 0 := by
  rw [W1p.halfSpaceTrace_compMeasurePreservingL hp a hΦ hUV hΦl hM hΦc hψ hΦa]
  exact Lp.ae_compMeasurePreserving_eq_zero_iff hψ hS _

end TauCeti
