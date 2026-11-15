/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Sard.VanishingDerivative
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.LocallyConvex.SeparatingDual
import TauCeti.Analysis.Calculus.FDeriv.Comp
import TauCeti.Analysis.Calculus.FDeriv.CriticalSet
import TauCeti.MeasureTheory.Measure.Haar.NormedSpace
import TauCeti.MeasureTheory.Measure.LocallyNull

/-!
# The outermost stratum, and the Morse--Sard theorem

The critical values of a sufficiently smooth map between finite-dimensional real normed spaces
form a set of additive Haar measure zero, and its regular values are therefore dense. A point is
critical when the Fréchet derivative there fails to be surjective. The conclusion is recorded here
in a measure-free form as well -- the critical values have empty interior -- for use where the
target carries no measurable structure of its own.

The locus where the derivative vanishes is handled in
`TauCeti.Analysis.Calculus.Sard.VanishingDerivative`, and this file supplies the outermost
stratum, where the derivative is nonzero but not surjective, together with the assembly of the
two into the theorem itself. The two earlier results,
`Differentiable.addHaar_image_criticalPoints_eq_zero` (equal dimensions),
`Differentiable.addHaar_image_not_surjective_fderiv_eq_zero_of_finrank_lt_finrank`
(smaller source), need only differentiability. The theorem here needs no relation between the
two dimensions, and holds at Sard's regularity: `C^k` with `k > finrank ℝ E - finrank ℝ F` and
`k ≥ 1`.

The argument for the outermost stratum is Milnor's. Near a point `a` where the derivative does not
vanish, pick `v₀` with `Df(a) v₀ ≠ 0` and a functional `φ` on the target with `φ (Df(a) v₀) = 1`.
Then `u := φ ∘ f` has a nonvanishing differential at `a`, so `x ↦ (u x, π x)` is a local
diffeomorphism onto `ℝ × ker (D u a)` for the projection `π` along `v₀`, and its local inverse `Θ`
parametrizes all the nearby level sets of `u` at once. Splitting the target as `ℝ × ker φ` too,
`f` becomes the map `(t, z) ↦ (t, G t z)` with `G t z := ρ (f (Θ (t, z)))`, where `ρ` projects the
target along `Df(a) v₀`: it preserves the level `t`, so it carries each hyperplane into a
hyperplane. Whenever a point is critical for `f`, it is critical for the restricted map `G t`,
whose source has one dimension less, so the induction hypothesis makes every slice of the image of
the critical set null, and Fubini finishes. Compactness enters only to make the slicing legitimate:
an image with null slices need not be null unless it is measurable, so the
argument runs over the pieces `crit f ∩ closedBall a r`. These are compact because
`TauCeti.isOpen_setOf_surjective` makes the surjective operators an open set, so the critical
locus, its preimage under the continuous derivative, is closed on the ball, and a closed subset of
a compact ball is compact.

The induction is on the dimension of the source, and both spaces are quantified inside the
statement carried through it, since the induction step replaces each of them by a
hyperplane. No regularity is lost in the descent, since the inverse function theorem returns a
local inverse as smooth as the map, and the difference `finrank ℝ E - finrank ℝ F` of the two
dimensions is unchanged. The whole theorem therefore holds at every regularity at which the
vanishing-derivative locus has null image, in every pair of dimensions reached by the descent.
By `TauCeti.addHaar_image_eq_zero_of_fderiv_eq_zero` that locus has null image for `C^k` maps as
soon as `finrank ℝ E ≤ k * finrank ℝ F`, and this inequality holds at the sharp exponent
`k = max 1 (finrank ℝ E - finrank ℝ F + 1)` whenever the target is nontrivial.

## Main results

* `TauCeti.addHaar_image_criticalPoints_eq_zero`: **the Morse--Sard theorem** on a set, at the
  sharp regularity `max 1 (finrank ℝ E - finrank ℝ F + 1)`: the critical values taken on a set
  where the map is that smooth at every point form a null set.
* `ContDiff.addHaar_image_criticalPoints_eq_zero`: its global form.
* `ContDiff.ae_forall_surjective_fderiv`: almost every value is a regular value.
* `ContDiff.dense_compl_image_criticalPoints`: the regular values are dense, without requiring a
  measurable structure on the target.
* `TauCeti.interior_image_criticalPoints_eq_empty`: the measure-free restatement, that the
  critical values have empty interior.

Finite-dimensional Sard supplies the fibrewise step in Sard--Smale and the regular values used
in transversality arguments.

## References

The stratification and the Fubini step are the proof of Sard's theorem in J. Milnor, *Topology
from the Differentiable Viewpoint*, Section 3, and M. Hirsch, *Differential Topology*, Chapter 3.
The sharp regularity is that of A. Sard, *The measure of the critical values of differentiable
maps*, Bull. Amer. Math. Soc. 48 (1942), 883–890; Whitney's example showing it cannot be lowered
is in H. Whitney, *A function not constant on a connected set of critical points*, Duke Math. J.
1 (1935), 514–517.
-/

public section

open Function MeasureTheory MeasureTheory.Measure Module Set

open scoped ContDiff Topology

namespace TauCeti

universe u v

section MorseSard

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {F : Type v} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F] {U : Set E} {f : E → F} (ν : Measure F) [IsAddHaarMeasure ν]

omit [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F] in
/-- The straightening step: if `g` has an invertible derivative at `a` and is `C^k` there, then
`g` has a `C^k` local inverse `Θ`, defined on an open set `V` around `g a`, whose values lie in `U`
and keep `φ ∘ Df` nonzero in the direction `v₀`, and `g` is inverted by `Θ` on an open set `W`
around `a` that `g` maps into `V`. -/
private theorem exists_isOpen_localInverse_nhds {k : ℕ} (hk : (k : ℕ∞ω) ≠ 0)
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (hU : IsOpen U) {a : E} (haU : a ∈ U) (hfc : ContinuousAt (fderiv ℝ f) a)
    {φ : F →L[ℝ] ℝ} {v₀ : E} (hφ : φ (fderiv ℝ f a v₀) = 1) {g : E → G} {e : E ≃L[ℝ] G}
    (hgC : ContDiffAt ℝ (k : ℕ∞ω) g a) (hgd : HasFDerivAt g (e : E →L[ℝ] G) a) :
    ∃ (Θ : G → E) (V : Set G) (W : Set E), IsOpen V ∧ IsOpen W ∧ g a ∈ V ∧ a ∈ W ∧
      (∀ p ∈ V, ContDiffAt ℝ (k : ℕ∞ω) Θ p ∧ g (Θ p) = p ∧ Θ p ∈ U ∧
        φ (fderiv ℝ f (Θ p) v₀) ≠ 0) ∧ (∀ x ∈ W, x ∈ U ∧ Θ (g x) = x ∧ g x ∈ V) := by
  have hstrict : HasStrictFDerivAt g (e : E →L[ℝ] G) a := hgC.hasStrictFDerivAt hgd hk
  have hΘC : ContDiffAt ℝ (k : ℕ∞ω) (hgC.localInverse hgd hk) (g a) := hgC.to_localInverse hgd hk
  have hΘleft : ∀ᶠ x in 𝓝 a, hgC.localInverse hgd hk (g x) = x := hstrict.eventually_left_inverse
  have hΘright : ∀ᶠ p in 𝓝 (g a), g (hgC.localInverse hgd hk p) = p :=
    hstrict.eventually_right_inverse
  generalize hgC.localInverse hgd hk = Θ at hΘC hΘleft hΘright
  have hΘa : Θ (g a) = a := hΘleft.self_of_nhds
  have hevalC : Continuous fun A : E →L[ℝ] F ↦ φ (A v₀) :=
    φ.continuous.comp (ContinuousLinearMap.apply ℝ F v₀).continuous
  obtain ⟨V, hVsub, hVopen, hVmem⟩ : ∃ V, (∀ p ∈ V, ContDiffAt ℝ (k : ℕ∞ω) Θ p ∧
      g (Θ p) = p ∧ Θ p ∈ U ∧ φ (fderiv ℝ f (Θ p) v₀) ≠ 0) ∧ IsOpen V ∧ g a ∈ V := by
    refine eventually_nhds_iff.1 ?_
    have hΘU : ∀ᶠ p in 𝓝 (g a), Θ p ∈ U :=
      hΘC.continuousAt.preimage_mem_nhds (by rw [hΘa]; exact hU.mem_nhds haU)
    have hne : ∀ᶠ p in 𝓝 (g a), φ (fderiv ℝ f (Θ p) v₀) ≠ 0 := by
      refine ContinuousAt.eventually_ne ?_ ?_
      · have h2 : ContinuousAt (fderiv ℝ f) (Θ (g a)) := by rwa [hΘa]
        exact hevalC.continuousAt.comp (h2.comp hΘC.continuousAt)
      · rw [hΘa, hφ]; exact one_ne_zero
    filter_upwards [hΘC.eventually (by simp), hΘright, hΘU, hne] with p h1 h2 h3 h4
    exact ⟨h1, h2, h3, h4⟩
  refine ⟨Θ, V, ?_⟩
  obtain ⟨W, hWsub, hWopen, hWmem⟩ : ∃ W, (∀ x ∈ W, x ∈ U ∧ Θ (g x) = x ∧ g x ∈ V) ∧
      IsOpen W ∧ a ∈ W := by
    refine eventually_nhds_iff.1 ?_
    filter_upwards [hU.mem_nhds haU, hΘleft,
      hgC.continuousAt.preimage_mem_nhds (hVopen.mem_nhds hVmem)] with x h1 h2 h3
    exact ⟨h1, h2, h3⟩
  exact ⟨W, hVopen, hWopen, hVmem, hWmem, hVsub, hWsub⟩

omit [FiniteDimensional ℝ E] in
/-- The slices of a straightened map: if the critical points of `f` in a compact set `K` are cut
by the level sets of `φ ∘ f` through a chart `Θ` onto slice maps `z ↦ ρ (f (Θ (t, z)))` whose
critical values are null, then the image of the critical points in `K` is null. -/
private theorem addHaar_image_criticalPoints_inter_eq_zero {K : Set E} (hK : IsCompact K)
    {G₁ G₂ : Type*} [NormedAddCommGroup G₁] [NormedSpace ℝ G₁]
    [NormedAddCommGroup G₂] [NormedSpace ℝ G₂] [FiniteDimensional ℝ G₂]
    [MeasurableSpace G₂] [BorelSpace G₂] (φ : F →L[ℝ] ℝ) (ρ : F →L[ℝ] G₂)
    (eF : F ≃L[ℝ] ℝ × G₂) (heF : ∀ w, eF w = (φ w, ρ w)) (π : E → G₁) (Θ : ℝ × G₁ → E)
    (V : Set (ℝ × G₁)) (hfK : ContinuousOn f K) (hfK' : ContinuousOn (fderiv ℝ f) K)
    (hKV : ∀ x ∈ K, Θ (φ (f x), π x) = x ∧ (φ (f x), π x) ∈ V)
    (hcrit : ∀ t z, (t, z) ∈ V → ¬ Surjective (fderiv ℝ f (Θ (t, z))) →
      ¬ Surjective (fderiv ℝ (fun w ↦ ρ (f (Θ (t, w)))) z))
    (hrec : ∀ t, (addHaar : Measure G₂) ((fun z ↦ ρ (f (Θ (t, z)))) ''
      ({z | (t, z) ∈ V} ∩ {z | ¬ Surjective (fderiv ℝ (fun w ↦ ρ (f (Θ (t, w)))) z)})) = 0) :
    ν (f '' ({x | ¬ Surjective (fderiv ℝ f x)} ∩ K)) = 0 := by
  refine addHaar_eq_zero_of_prod_mk_preimage_image_eq_zero ν addHaar addHaar eF
    (hK.image_inter_setOf_not_surjective_fderiv hfK hfK').isClosed.measurableSet
    (.of_forall fun t ↦ measure_mono_null ?_ (hrec t))
  rintro y ⟨-, ⟨x, ⟨hxc, hxK⟩, rfl⟩, hxy⟩
  obtain ⟨hxΘ, hxV⟩ := hKV x hxK
  rw [heF] at hxy
  have hfst : φ (f x) = t := congrArg Prod.fst hxy
  have hxeq : Θ (t, π x) = x := by rw [← hfst]; exact hxΘ
  have hmem : π x ∈ {z | (t, z) ∈ V} := by
    rw [Set.mem_ofPred_eq, ← hfst]; exact hxV
  refine ⟨π x, ⟨hmem, hcrit t _ hmem ?_⟩, ?_⟩
  · rw [hxeq]; exact hxc
  · simp only [hxeq]; exact congrArg Prod.snd hxy

/-- The outermost stratum at one point: if `φ ∘ Df` is nonzero at `a`, `f` splits through the
charts `eE`, `eF` as `ℝ × G₁` and `ℝ × G₂`, and the critical values of every smooth map from an
open subset of `G₁` to `G₂` are null, then the critical points of `f` near `a` have a null
image. -/
private theorem exists_pos_addHaar_image_criticalPoints_inter_closedBall_eq_zero {k : ℕ}
    (hk : (k : ℕ∞ω) ≠ 0) (hU : IsOpen U) {a : E} (haU : a ∈ U)
    (hf : ∀ x ∈ U, ContDiffAt ℝ (k : ℕ∞ω) f x) {φ : F →L[ℝ] ℝ} {v₀ : E}
    (hφ : φ (fderiv ℝ f a v₀) = 1) {G₁ G₂ : Type*} [NormedAddCommGroup G₁] [NormedSpace ℝ G₁]
    [NormedAddCommGroup G₂] [NormedSpace ℝ G₂] [FiniteDimensional ℝ G₂]
    [MeasurableSpace G₂] [BorelSpace G₂] (π : E →L[ℝ] G₁) (ρ : F →L[ℝ] G₂)
    (eE : E ≃L[ℝ] ℝ × G₁) (eF : F ≃L[ℝ] ℝ × G₂) (heE : ∀ x, eE x = (φ (fderiv ℝ f a x), π x))
    (heF : ∀ w, eF w = (φ w, ρ w))
    (hrec : ∀ (O : Set G₁) (g : G₁ → G₂), IsOpen O → (∀ z ∈ O, ContDiffAt ℝ (k : ℕ∞ω) g z) →
      (addHaar : Measure G₂) (g '' (O ∩ {z | ¬ Surjective (fderiv ℝ g z)})) = 0) :
    ∃ r > 0, ν (f '' ({x | ¬ Surjective (fderiv ℝ f x)} ∩ Metric.closedBall a r)) = 0 := by
  set hmap : E → ℝ × G₁ := fun x ↦ (φ (f x), π x)
  have hfa : HasFDerivAt f (fderiv ℝ f a) a := ((hf a haU).differentiableAt hk).hasFDerivAt
  have heE' : (eE : E →L[ℝ] ℝ × G₁) = (φ.comp (fderiv ℝ f a)).prod π :=
    ContinuousLinearMap.ext heE
  have hmapd : HasFDerivAt hmap (eE : E →L[ℝ] ℝ × G₁) a := by
    rw [heE']
    exact (φ.hasFDerivAt.comp a hfa).prodMk π.hasFDerivAt
  have hmapC : ContDiffAt ℝ (k : ℕ∞ω) hmap a :=
    (φ.contDiff.comp_contDiffAt a (hf a haU)).prodMk π.contDiff.contDiffAt
  obtain ⟨Θ, V, W, hVopen, hWopen, -, hWmem, hVsub, hWsub⟩ :=
    exists_isOpen_localInverse_nhds hk hU haU ((hf a haU).continuousAt_fderiv hk) hφ hmapC hmapd
  obtain ⟨r, hr, hrW⟩ := Metric.isOpen_iff.1 hWopen a hWmem
  have hKW : Metric.closedBall a (r / 2) ⊆ W :=
    (Metric.closedBall_subset_ball (by linarith)).trans hrW
  refine ⟨r / 2, by positivity, ?_⟩
  have hKU : ∀ x ∈ Metric.closedBall a (r / 2), x ∈ U := fun x hx ↦ (hWsub x (hKW hx)).1
  refine addHaar_image_criticalPoints_inter_eq_zero ν (isCompact_closedBall a (r / 2)) φ ρ eF heF
    π Θ V (fun x hx ↦ (hf x (hKU x hx)).continuousAt.continuousWithinAt)
    (fun x hx ↦ ((hf x (hKU x hx)).continuousAt_fderiv hk).continuousWithinAt)
    (fun x hx ↦ ⟨(hWsub x (hKW hx)).2.1, (hWsub x (hKW hx)).2.2⟩)
    (fun t z hz hx hs ↦ hx ?_) fun t ↦ hrec _ _ (hVopen.preimage (by fun_prop)) fun z hz ↦ ?_
  · obtain ⟨hΘC, -, hΘU, hΘne⟩ := hVsub (t, z) hz
    have hΘt : ContDiffAt ℝ (k : ℕ∞ω) (fun w ↦ Θ (t, w)) z :=
      hΘC.comp z (contDiffAt_const.prodMk contDiffAt_id)
    refine ContinuousLinearMap.surjective_fderiv_of_surjective_fderiv_comp φ ρ
      (by simpa [funext heF] using eF.injective)
      (γ := fun w ↦ Θ (t, w)) (z := z)
      (hΘt.differentiableAt hk) ((hf _ hΘU).differentiableAt hk) (c := t) ?_ ?_ hs
    · refine Filter.eventuallyEq_of_mem ((hVopen.preimage (by fun_prop)).mem_nhds hz) fun w hw ↦ ?_
      exact congrArg Prod.fst (hVsub (t, w) hw).2.1
    · exact ⟨v₀, hΘne⟩
  · obtain ⟨hΘC, -, hΘU, -⟩ := hVsub (t, z) hz
    refine ρ.contDiff.comp_contDiffAt z ((hf _ hΘU).comp z ?_)
    exact hΘC.comp z (contDiffAt_const.prodMk contDiffAt_id)

omit [FiniteDimensional ℝ F] [BorelSpace F] [IsAddHaarMeasure ν] in
/-- The vanishing-derivative locus and a point-by-point null statement for the outermost stratum
give the whole critical set. -/
private theorem addHaar_image_criticalPoints_eq_zero_of_flat_of_local
    (h0 : ν (f '' (U ∩ {x | fderiv ℝ f x = 0})) = 0)
    (hloc : ∀ a ∈ U, ¬ Surjective (fderiv ℝ f a) → fderiv ℝ f a ≠ 0 → ∃ r > 0,
      ν (f '' ({x | ¬ Surjective (fderiv ℝ f x)} ∩ Metric.closedBall a r)) = 0) :
    ν (f '' (U ∩ {x | ¬ Surjective (fderiv ℝ f x)})) = 0 := by
  have hsub : U ∩ {x | ¬ Surjective (fderiv ℝ f x)} ⊆
      (U ∩ {x | fderiv ℝ f x = 0}) ∪
        (U ∩ {x | ¬ Surjective (fderiv ℝ f x)} ∩ {x | fderiv ℝ f x ≠ 0}) := by
    rintro x ⟨hxU, hxc⟩
    by_cases hx0 : fderiv ℝ f x = 0
    · exact Or.inl ⟨hxU, hx0⟩
    · exact Or.inr ⟨⟨hxU, hxc⟩, hx0⟩
  refine measure_mono_null (image_mono hsub) ?_
  rw [image_union]
  refine measure_union_null h0 ?_
  refine measure_image_null_of_locally_null (HereditarilyLindelofSpace.isLindelof _)
    fun a ha ↦ ?_
  obtain ⟨⟨haU, hac⟩, hane⟩ := ha
  obtain ⟨r, hr, hnull⟩ := hloc a haU hac hane
  refine ⟨(U ∩ {x | ¬ Surjective (fderiv ℝ f x)} ∩ {x | fderiv ℝ f x ≠ 0}) ∩ Metric.ball a r,
    inter_mem_nhdsWithin _ (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hr)), ?_⟩
  refine measure_mono_null (image_mono ?_) hnull
  rintro x ⟨⟨⟨-, hxc⟩, -⟩, hxb⟩
  exact ⟨hxc, Metric.ball_subset_closedBall hxb⟩

/-- The induction behind `TauCeti.addHaar_image_criticalPoints_eq_zero`, on the dimension `n` of
the source, at a regularity `k ≥ finrank ℝ E - finrank ℝ F + 1`. The outermost stratum passes
from the source and target to hyperplanes of each, at the same regularity `k`, and the
vanishing-derivative locus is handled by `TauCeti.addHaar_image_eq_zero_of_fderiv_eq_zero`. Both
spaces are quantified inside the statement because the induction step replaces each of them by a
hyperplane; they stay in their own universes, since a hyperplane of a space is a submodule of
it. -/
private theorem addHaar_image_criticalPoints_eq_zero_aux (k : ℕ) (hk1 : 1 ≤ k) (n : ℕ) :
    ∀ (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E],
      finrank ℝ E ≤ n →
      ∀ (F : Type v) [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
        [MeasurableSpace F] [BorelSpace F] (ν : Measure F) [IsAddHaarMeasure ν],
        finrank ℝ E - finrank ℝ F + 1 ≤ k →
        ∀ (U : Set E), IsOpen U → ∀ f : E → F, (∀ x ∈ U, ContDiffAt ℝ (k : ℕ∞ω) f x) →
        ν (f '' (U ∩ {x | ¬ Surjective (fderiv ℝ f x)})) = 0 := by
  induction n with
  | zero =>
    intro E _ _ _ hE F _ _ _ _ _ ν _ _ U _ f _
    rcases subsingleton_or_nontrivial F with _ | _
    · simp [surjective_to_subsingleton]
    · have : Subsingleton E := Module.finrank_zero_iff.mp (Nat.le_zero.mp hE)
      exact (Set.Subsingleton.image (fun x _ y _ ↦ Subsingleton.elim x y) f).measure_zero ν
  | succ n ih =>
    intro E _ _ _ hE F _ _ _ _ _ ν _ hkEF U hU f hf
    -- A trivial target has no critical points at all.
    rcases subsingleton_or_nontrivial F with _ | hF
    · simp [surjective_to_subsingleton]
    have hkne : (k : ℕ∞ω) ≠ 0 := by
      simpa using Nat.one_le_iff_ne_zero.1 hk1
    -- At this regularity `finrank ℝ E ≤ k * finrank ℝ F`, since
    -- `(finrank ℝ E - finrank ℝ F + 1) * finrank ℝ F - finrank ℝ E` is
    -- `(finrank ℝ E - finrank ℝ F) * (finrank ℝ F - 1)` when the source is larger.
    have hdim : finrank ℝ E ≤ k * finrank ℝ F := by
      have hF1 : 1 ≤ finrank ℝ F := finrank_pos
      rcases le_total (finrank ℝ E) (finrank ℝ F) with hEF | hEF
      · nlinarith [show 1 ≤ k by omega]
      · obtain ⟨c, hc⟩ := Nat.exists_eq_add_of_le hEF
        nlinarith [show c + 1 ≤ k by omega]
    refine addHaar_image_criticalPoints_eq_zero_of_flat_of_local ν
      (addHaar_image_eq_zero_of_fderiv_eq_zero ν (fun x hx ↦ hf x hx.1) le_rfl hdim
        fun x hx ↦ hx.2) fun a haU _ hane ↦ ?_
    -- A direction on which the derivative does not vanish, and a functional dual to its image.
    obtain ⟨v₀, hv₀⟩ : ∃ v, fderiv ℝ f a v ≠ 0 := by
      by_contra hc
      exact hane (ContinuousLinearMap.ext fun v ↦ by
        simpa using not_not.1 (not_exists.1 hc v))
    obtain ⟨φ, hφ⟩ := SeparatingDual.exists_eq_one (R := ℝ) hv₀
    -- The two hyperplanes, and the splittings of the source and target along them.
    set sE : ℝ →L[ℝ] E := (ContinuousLinearMap.id ℝ ℝ).smulRight v₀
    have hsE : Function.RightInverse sE (φ.comp (fderiv ℝ f a)) := fun t ↦ by simp [sE, hφ]
    set sF : ℝ →L[ℝ] F := (ContinuousLinearMap.id ℝ ℝ).smulRight (fderiv ℝ f a v₀)
    have hsF : Function.RightInverse sF φ := fun t ↦ by simp [sF, hφ]
    set π := (φ.comp (fderiv ℝ f a)).projKerOfRightInverse sE hsE
    set eE := ContinuousLinearEquiv.equivOfRightInverse (φ.comp (fderiv ℝ f a)) sE hsE
    set ρ := φ.projKerOfRightInverse sF hsF
    set eF := ContinuousLinearEquiv.equivOfRightInverse φ sF hsF
    have heE : ∀ x, eE x = (φ (fderiv ℝ f a x), π x) := fun x ↦ rfl
    have heF : ∀ x, eF x = (φ x, ρ x) := fun x ↦ rfl
    let mFk : MeasurableSpace ↥(LinearMap.ker (φ : F →ₗ[ℝ] ℝ)) := borel _
    have bFk : BorelSpace ↥(LinearMap.ker (φ : F →ₗ[ℝ] ℝ)) := ⟨rfl⟩
    have hEk : finrank ℝ ↥(LinearMap.ker ((φ.comp (fderiv ℝ f a) : E →L[ℝ] ℝ) : E →ₗ[ℝ] ℝ)) + 1 =
        finrank ℝ E :=
      Module.Dual.finrank_ker_add_one_of_ne_zero fun h ↦ by
        simpa [hφ] using LinearMap.congr_fun h v₀
    have hFk : finrank ℝ ↥(LinearMap.ker (φ : F →ₗ[ℝ] ℝ)) + 1 = finrank ℝ F :=
      Module.Dual.finrank_ker_add_one_of_ne_zero fun h ↦ by
        simpa [hφ] using LinearMap.congr_fun h (fderiv ℝ f a v₀)
    have hkk : finrank ℝ ↥(LinearMap.ker ((φ.comp (fderiv ℝ f a) : E →L[ℝ] ℝ) : E →ₗ[ℝ] ℝ)) -
        finrank ℝ ↥(LinearMap.ker (φ : F →ₗ[ℝ] ℝ)) + 1 ≤ k := by omega
    exact exists_pos_addHaar_image_criticalPoints_inter_closedBall_eq_zero ν hkne hU haU hf hφ
      π ρ eE eF heE heF fun O g hO hg ↦ ih _ (by omega) _ addHaar hkk O hO g hg

/-- **The Morse--Sard theorem** on a set. The values taken at the points of `U` where the Fréchet
derivative is not surjective form a set of additive Haar measure zero, provided the map is `C^n`
at every point of `U` with `n > finrank ℝ E - finrank ℝ F` and `n ≥ 1`. The set need not be open,
and no relation between the two finite dimensions is required.

This is the regularity of Sard's theorem. It cannot be lowered in general: Whitney's `C¹`
function on the plane that is not constant along a connected arc of critical points has critical
values of positive measure. -/
theorem addHaar_image_criticalPoints_eq_zero {n : ℕ∞ω}
    (hf : ∀ x ∈ U, ContDiffAt ℝ n f x)
    (hk : ((finrank ℝ E - finrank ℝ F + 1 : ℕ) : ℕ∞ω) ≤ n) :
    ν (f '' (U ∩ {x | ¬ Surjective (fderiv ℝ f x)})) = 0 := by
  -- Finite-order smoothness at each point of `U` supplies an open smooth neighbourhood for the
  -- induction.
  refine measure_image_null_of_locally_null (HereditarilyLindelofSpace.isLindelof _)
    fun a ha ↦ ?_
  obtain ⟨V, hVsmooth, hVopen, hVmem⟩ :=
    eventually_nhds_iff.1 (((hf a ha.1).of_le hk).eventually (by simp))
  refine ⟨(U ∩ {x | ¬ Surjective (fderiv ℝ f x)}) ∩ V,
    inter_mem_nhdsWithin _ (hVopen.mem_nhds hVmem), ?_⟩
  refine measure_mono_null (image_mono ?_) (addHaar_image_criticalPoints_eq_zero_aux _
    (by omega) (finrank ℝ E) E le_rfl F ν le_rfl V hVopen f hVsmooth)
  exact fun _ hx ↦ ⟨hx.2, hx.1.2⟩

/-- **The Morse--Sard theorem.** The critical values of a `C^n` map between finite-dimensional
real normed spaces, that is the values it takes at the points where its Fréchet derivative is not
surjective, form a set of additive Haar measure zero, provided `n > finrank ℝ E - finrank ℝ F`
and `n ≥ 1`. No relation between the two dimensions is required. -/
theorem _root_.ContDiff.addHaar_image_criticalPoints_eq_zero {n : ℕ∞ω} (hf : ContDiff ℝ n f)
    (hk : ((finrank ℝ E - finrank ℝ F + 1 : ℕ) : ℕ∞ω) ≤ n) :
    ν (f '' {x | ¬ Surjective (fderiv ℝ f x)}) = 0 := by
  simpa using TauCeti.addHaar_image_criticalPoints_eq_zero (U := univ) ν
    (fun x _ ↦ hf.contDiffAt) hk

/-- Almost every value of a `C^n` map between finite-dimensional real normed spaces, with
`n > finrank ℝ E - finrank ℝ F` and `n ≥ 1`, is a regular value: the derivative is surjective at
every point of its preimage. -/
theorem _root_.ContDiff.ae_forall_surjective_fderiv {n : ℕ∞ω} (hf : ContDiff ℝ n f)
    (hk : ((finrank ℝ E - finrank ℝ F + 1 : ℕ) : ℕ∞ω) ≤ n) :
    ∀ᵐ y ∂ν, ∀ x, f x = y → Surjective (fderiv ℝ f x) := by
  rw [ae_iff]
  refine measure_mono_null ?_ (hf.addHaar_image_criticalPoints_eq_zero ν hk)
  intro y hy
  push Not at hy
  obtain ⟨x, hxy, hx⟩ := hy
  exact ⟨x, hx, hxy⟩

end MorseSard

section EmptyInterior

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {F : Type v} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {U : Set E} {f : E → F}

/-- **The Morse--Sard theorem**, in the form that carries no measure-theoretic data: the critical
values taken on a set where the map is `C^n` at every point, with
`n > finrank ℝ E - finrank ℝ F` and `n ≥ 1`, have empty interior. The measure structure used to
prove it is chosen inside the proof, so the target here carries no `MeasurableSpace` instance; this
is the shape in which Sard is fed to the fibrewise step of the Sard--Smale theorem, where the
target is a complement subspace with no measurable structure of its own. -/
theorem interior_image_criticalPoints_eq_empty {n : ℕ∞ω}
    (hf : ∀ x ∈ U, ContDiffAt ℝ n f x)
    (hk : ((finrank ℝ E - finrank ℝ F + 1 : ℕ) : ℕ∞ω) ≤ n) :
    interior (f '' (U ∩ {x | ¬ Surjective (fderiv ℝ f x)})) = ∅ := by
  borelize F
  exact Measure.interior_eq_empty_of_null
    (TauCeti.addHaar_image_criticalPoints_eq_zero (ν := addHaar) hf hk)

/-- The regular values of a `C^n` map between finite-dimensional real normed spaces, with
`n > finrank ℝ E - finrank ℝ F` and `n ≥ 1`, are dense. This form of the Morse--Sard theorem needs
no measurable structure on the target and supplies the regular values used in transversality
arguments. -/
theorem _root_.ContDiff.dense_compl_image_criticalPoints {n : ℕ∞ω} (hf : ContDiff ℝ n f)
    (hk : ((finrank ℝ E - finrank ℝ F + 1 : ℕ) : ℕ∞ω) ≤ n) :
    Dense (f '' {x | ¬ Surjective (fderiv ℝ f x)})ᶜ := by
  apply interior_eq_empty_iff_dense_compl.1
  simpa using interior_image_criticalPoints_eq_empty (U := univ)
    (fun x _ ↦ hf.contDiffAt) hk

end EmptyInterior

end TauCeti

end
