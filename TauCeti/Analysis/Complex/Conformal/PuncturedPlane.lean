/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Complex.Basic
public import TauCeti.Topology.Compactification.OnePoint.CrossRatio
import Mathlib.Analysis.Complex.RemovableSingularity
import TauCeti.Analysis.Complex.Conformal.EntireInjection

/-!
# Holomorphic embeddings of planes with labelled punctures

A Riemann sphere with finitely many ordered punctures, one of them at `∞`, is the plane `ℂ`
with the remaining punctures `c i` removed. Pairs of pants, and the four-punctured spheres in
which two of them are composed, are of this form, with the output puncture at `∞` and the inputs
at the `c i`. This file classifies such domains up to holomorphic maps respecting the labels.

Let `c` and `c'` be finite families of points of `ℂ`. A map `f` is a *punctured embedding* from
`c` to `c'` (`TauCeti.IsPuncturedEmbedding c c' f`) if it is holomorphic and injective on
`ℂ ∖ range c` and tends to `c' i` at each puncture `c i`. Filling in the punctures removes the
singularities and gives an entire function that is injective off a finite set, hence injective
(`Differentiable.injective_of_injOn_compl`, by the open mapping theorem) and therefore affine
(`Differentiable.exists_eq_mul_add_of_injective`). So every punctured embedding is the restriction
of an affine map `w ↦ a w + b`, `a ≠ 0`, carrying each `c i` to `c' i`
(`TauCeti.IsPuncturedEmbedding.exists_eq_mul_add`), and such a map exists exactly when the two
families are affinely equivalent (`TauCeti.exists_isPuncturedEmbedding_iff`). Nothing is assumed
at `∞`, the image is not assumed to avoid the punctures `c' i`, and `f` need not be surjective; all
of this follows.

For three finite punctures, the affine class of `(c 0, c 1, c 2)` is the cross ratio
`OnePoint.crossRatio (c 0) (c 2) ∞ (c 1) = (c 1 - c 0) / (c 2 - c 0)` of the four labelled points
`c 0, c 2, ∞, c 1` of the Riemann sphere. So two spheres with three ordered input punctures and the
output at `∞` admit a label-preserving punctured embedding exactly when these cross ratios agree
(`TauCeti.exists_isPuncturedEmbedding_iff_crossRatio_eq`). This is the cross ratio coordinate
of the moduli space `M(0, 4)` of four-punctured spheres, in which the domains of the associativity
of the pair-of-pants product are described.

## Main definitions

* `TauCeti.IsPuncturedEmbedding c c' f`: `f` is holomorphic and injective on `ℂ ∖ range c` and
  carries each puncture `c i` to `c' i`.

## Main results

* `TauCeti.IsPuncturedEmbedding.exists_eq_mul_add`: a punctured embedding is affine.
* `TauCeti.IsPuncturedEmbedding.mapsTo`: it maps `ℂ ∖ range c` into `ℂ ∖ range c'`.
* `TauCeti.isPuncturedEmbedding_mul_add`: affine maps are punctured embeddings.
* `TauCeti.exists_isPuncturedEmbedding_iff`: a punctured embedding exists exactly when the
  punctures are affinely equivalent.
* `TauCeti.exists_isPuncturedEmbedding_iff_crossRatio_eq`: for three finite punctures, exactly
  when the cross ratios agree.

## References

* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, Appendix D, on
  stable curves of genus zero and the cross ratio coordinates of their moduli spaces.
* J. B. Conway, *Functions of One Complex Variable I*, Springer GTM 11, on the conformal
  automorphisms of the plane.
-/

public section

open Filter Set Topology Function
open scoped OnePoint

namespace TauCeti

variable {ι : Type*} {c c' : ι → ℂ} {f : ℂ → ℂ}

/-- A *punctured embedding* from the punctures `c` to the punctures `c'`: a map `f` that is
holomorphic and injective on `ℂ ∖ range c` and tends to `c' i` at `c i` for every `i`. It is a
holomorphic embedding of spheres with labelled punctures, the puncture at `∞` being matched with
the puncture at `∞`. For finitely many punctures it maps `ℂ ∖ range c` into `ℂ ∖ range c'`
(`TauCeti.IsPuncturedEmbedding.mapsTo`). -/
structure IsPuncturedEmbedding (c c' : ι → ℂ) (f : ℂ → ℂ) : Prop where
  /-- The map is holomorphic off the punctures. -/
  differentiableOn : DifferentiableOn ℂ f (range c)ᶜ
  /-- The map is injective off the punctures. -/
  injOn : InjOn f (range c)ᶜ
  /-- The map carries the puncture `c i` to the puncture `c' i`. -/
  tendsto : ∀ i, Tendsto f (𝓝[≠] c i) (𝓝 (c' i))

namespace IsPuncturedEmbedding

/-- **Punctured embeddings are affine.** A holomorphic embedding of the plane with finitely many
labelled punctures `c i` into the plane, which tends to `c' i` at each `c i`, is the restriction of
an affine map `w ↦ a w + b` with `a ≠ 0`, and this map carries each `c i` to `c' i`. -/
theorem exists_eq_mul_add [Finite ι] (hf : IsPuncturedEmbedding c c' f) :
    ∃ a b : ℂ, a ≠ 0 ∧ (∀ w ∉ range c, f w = a * w + b) ∧ ∀ i, c' i = a * c i + b := by
  have hopen : IsOpen (range c)ᶜ := (finite_range c).isClosed.isOpen_compl
  -- Near each puncture, the other points of a punctured neighbourhood lie off the punctures.
  have hoff (p : ℂ) : ∀ᶠ w in 𝓝[≠] p, w ∉ range c :=
    Filter.mem_of_superset (nhdsNE_of_nhdsNE_sdiff_finite univ_mem (finite_range c))
      fun _ hw => hw.2
  -- Fill in each puncture `c i` with its limit `c' i`; the limits at a common puncture agree.
  set g : ℂ → ℂ := extend c c' f
  have hgc : ∀ i, g (c i) = c' i :=
    FactorsThrough.extend_apply (fun i j (h : c i = c j) => tendsto_nhds_unique (hf.tendsto i)
      (h ▸ hf.tendsto j)) f
  have hgf : ∀ w ∉ range c, g w = f w := fun w hw => extend_apply' c' f w hw
  have hdiff : ∀ w ∉ range c, DifferentiableAt ℂ g w := fun w hw =>
    (hf.differentiableOn.differentiableAt (hopen.mem_nhds hw)).congr_of_eventuallyEq
      (eventually_of_mem (hopen.mem_nhds hw) hgf)
  -- The singularities at the punctures are removable, so `g` is entire.
  have hd : Differentiable ℂ g := fun w => by
    by_cases hw : w ∈ range c
    · obtain ⟨i, rfl⟩ := hw
      refine (Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt
        ((hoff (c i)).mono hdiff) ?_).differentiableAt
      rw [← continuousWithinAt_compl_self, ContinuousWithinAt, hgc]
      exact (hf.tendsto i).congr' ((hoff (c i)).mono fun w hw => (hgf w hw).symm)
    · exact hdiff w hw
  -- `g` is injective off the finite set of punctures, hence injective, hence affine.
  have hginj : Injective g := hd.injective_of_injOn_compl (finite_range c)
    fun x hx y hy hxy => hf.injOn hx hy (by rwa [← hgf x hx, ← hgf y hy])
  obtain ⟨a, b, ha, hab⟩ := hd.exists_eq_mul_add_of_injective hginj
  exact ⟨a, b, ha, fun w hw => (hgf w hw).symm.trans (hab w),
    fun i => (hgc i).symm.trans (hab (c i))⟩

/-- A punctured embedding maps the plane punctured at the `c i` into the plane punctured at the
`c' i`. -/
theorem mapsTo [Finite ι] (hf : IsPuncturedEmbedding c c' f) :
    MapsTo f (range c)ᶜ (range c')ᶜ := by
  obtain ⟨a, b, ha, hab, hc⟩ := hf.exists_eq_mul_add
  rintro w hw ⟨i, hi⟩
  rw [hab w hw, hc i] at hi
  exact hw ⟨i, mul_left_cancel₀ ha (add_right_cancel hi)⟩

end IsPuncturedEmbedding

/-- An affine map `w ↦ a w + b` with `a ≠ 0` is a punctured embedding from any punctures `c` to
their images `a c i + b`. -/
theorem isPuncturedEmbedding_mul_add {a : ℂ} (ha : a ≠ 0) (b : ℂ) (c : ι → ℂ) :
    IsPuncturedEmbedding c (fun i => a * c i + b) (fun w => a * w + b) where
  differentiableOn := ((differentiable_id.const_mul a).add_const b).differentiableOn
  injOn _ _ _ _ h := mul_left_cancel₀ ha (add_right_cancel h)
  tendsto i := by
    have hcont : Continuous fun w : ℂ => a * w + b := by fun_prop
    exact (hcont.tendsto (c i)).mono_left nhdsWithin_le_nhds

/-- **Classification of planes with labelled punctures.** For finitely many punctures `c i` and
`c' i`, there is a punctured embedding from `c` to `c'` exactly when `c' i = a c i + b` for some
`a ≠ 0` and `b`. -/
theorem exists_isPuncturedEmbedding_iff [Finite ι] :
    (∃ f, IsPuncturedEmbedding c c' f) ↔ ∃ a b : ℂ, a ≠ 0 ∧ ∀ i, c' i = a * c i + b := by
  refine ⟨fun ⟨f, hf⟩ => ?_, fun ⟨a, b, ha, hab⟩ => ?_⟩
  · obtain ⟨a, b, ha, -, hab⟩ := hf.exists_eq_mul_add
    exact ⟨a, b, ha, hab⟩
  · have hc : c' = fun i => a * c i + b := funext hab
    exact ⟨_, hc ▸ isPuncturedEmbedding_mul_add ha b c⟩

/-- Three distinct points of `ℂ` are carried to three distinct points by an affine map exactly
when the cross ratios `(c 1 - c 0) / (c 2 - c 0)` of the two triples, read as the cross ratios
`OnePoint.crossRatio (c 0) (c 2) ∞ (c 1)` of the Riemann sphere, agree. -/
theorem exists_eq_mul_add_iff_crossRatio_eq {c c' : Fin 3 → ℂ} (hc : Injective c)
    (hc' : Injective c') :
    (∃ a b : ℂ, a ≠ 0 ∧ ∀ i, c' i = a * c i + b) ↔
      OnePoint.crossRatio (c' 0 : OnePoint ℂ) (c' 2) ∞ (c' 1) =
        OnePoint.crossRatio (c 0 : OnePoint ℂ) (c 2) ∞ (c 1) := by
  have h02 : c 0 ≠ c 2 := hc.ne (by decide)
  have h02' : c' 0 ≠ c' 2 := hc'.ne (by decide)
  rw [OnePoint.crossRatio_coe_coe_infty_coe h02', OnePoint.crossRatio_coe_coe_infty_coe h02,
    OnePoint.coe_eq_coe]
  have h20 : c 2 - c 0 ≠ 0 := sub_ne_zero.2 h02.symm
  have h20' : c' 2 - c' 0 ≠ 0 := sub_ne_zero.2 h02'.symm
  constructor
  · rintro ⟨a, b, ha, hab⟩
    have hsub (i j : Fin 3) : c' i - c' j = a * (c i - c j) := by
      rw [hab i, hab j]
      ring
    rw [hsub, hsub, mul_div_mul_left _ _ ha]
  · intro h
    -- The affine map is determined by the images of `c 0` and `c 2`; the cross ratio then
    -- places `c' 1` correctly.
    rw [div_eq_div_iff h20' h20] at h
    refine ⟨(c' 2 - c' 0) / (c 2 - c 0), c' 0 - (c' 2 - c' 0) / (c 2 - c 0) * c 0,
      div_ne_zero h20' h20, fun i => ?_⟩
    field_simp
    fin_cases i
    · simp
    · simp only [Fin.mk_one]
      linear_combination h
    · simp only [Fin.reduceFinMk]
      ring

/-- **Spheres with three labelled input punctures.** For three distinct finite punctures `c` and
three distinct finite punctures `c'`, the output puncture being `∞` in both, a label-preserving
punctured embedding exists exactly when the cross ratios `OnePoint.crossRatio (c 0) (c 2) ∞ (c 1)`
and `OnePoint.crossRatio (c' 0) (c' 2) ∞ (c' 1)` agree. -/
theorem exists_isPuncturedEmbedding_iff_crossRatio_eq {c c' : Fin 3 → ℂ} (hc : Injective c)
    (hc' : Injective c') :
    (∃ f, IsPuncturedEmbedding c c' f) ↔
      OnePoint.crossRatio (c' 0 : OnePoint ℂ) (c' 2) ∞ (c' 1) =
        OnePoint.crossRatio (c 0 : OnePoint ℂ) (c 2) ∞ (c 1) :=
  exists_isPuncturedEmbedding_iff.trans (exists_eq_mul_add_iff_crossRatio_eq hc hc')

end TauCeti
