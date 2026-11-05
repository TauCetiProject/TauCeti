/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fredholm.LevelSet.GlobalParametric
public import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Measure.OpenPos
import TauCeti.Analysis.Calculus.Sard.OutermostStratum

/-!
# Parametric transversality in finite dimensions: the exceptional parameters are null

Let `f : E × Λ → F` be a parametrized equation between finite-dimensional real normed spaces and
`U ⊆ E × Λ` any set. A parameter `l` is *regular on `U`* at the level `c` when the
fixed-parameter linearization of `x ↦ f (x, l)` is surjective at every solution `x` with
`(x, l) ∈ U`. This file proves that the parameters which are not regular on `U` form a set of
additive Haar measure zero in `Λ`, provided the total linearization is surjective at every solution
in `U` and `f` is sufficiently smooth there. The regular parameters are then dense.

This is the finite-dimensional parametric transversality theorem in its measure-theoretic form
(Guillemin--Pollack, *Differential Topology*, Chapter 2 §3, the transversality theorem; Hirsch,
*Differential Topology*, Chapter 3 Theorem 2.7). It is not a special case of
`TauCeti.dense_setOf_isRegularParameter`, for two reasons. That theorem concludes that the
non-regular parameters are meagre, which in finite dimensions neither implies nor is implied by
measure zero; the applications here, to the Morse--Smale condition for almost every small
perturbation of a Morse function, need the measure statement. And its hypotheses are imposed at
every solution of an equation defined on all of `E × Λ`, while the universal equations of those
applications are only smooth, and only transverse, on a subset of their domain.

## The proof

The local step is the finite-dimensional counterpart of
`TauCeti.exists_mem_nhds_isClosed_isNowhereDense_image_not_surjective_levelSetParameterMap`. Near a
solution with surjective total linearization, `TauCeti.levelSetChart` parametrizes the universal
level set `{f = c}` by the kernel of the total linearization, and `TauCeti.levelSetParameterMap`,
the projection to `Λ` read in that chart, is as smooth as `f`. By
`TauCeti.surjective_fderiv_levelSetParameterMap_iff_of_mem` its critical points are the solutions
at which the fixed-parameter linearization is not surjective. The Morse--Sard theorem
`TauCeti.addHaar_image_criticalPoints_eq_zero` makes its critical values near the chart origin a
null set. The global step is the one of `TauCeti.isMeagre_setOf_not_isRegularParameter`: the
universal level set inside `U` is second countable, so countably many of these neighbourhoods
cover it, and a countable union of null sets is null.

The regularity threshold is the one of the Morse--Sard theorem in Tau Ceti, `(dim)² + 1` with
`dim` the dimension of the source of the parameter map, which is the kernel of the *total*
linearization. It is imposed pointwise along the level set inside `U`. This is coarser than
Sard's sharp threshold, and it differs from the threshold `(dim ker D₁)² + 1` of the Sard--Smale
route, which is in terms of the kernel of the *fixed-parameter* linearization.

## Main results

* `TauCeti.IsRegularParameterOn f U c l`: the fixed-parameter linearization is surjective at every
  solution in `U` with parameter `l`; `TauCeti.isRegularParameterOn_univ` identifies the case
  `U = univ` with `TauCeti.IsRegularParameter`.
* `TauCeti.exists_mem_nhds_addHaar_setOf_exists_not_surjective_fderiv_comp_inl_eq_zero`: the local
  theorem, near one solution.
* `TauCeti.addHaar_setOf_not_isRegularParameterOn_eq_zero`,
  `TauCeti.ae_isRegularParameterOn`: the non-regular parameters on a set are null.
* `TauCeti.dense_setOf_isRegularParameterOn`: the regular parameters are dense.

## References

* V. Guillemin, A. Pollack, *Differential Topology*, Prentice-Hall, 1974, Chapter 2 §3.
* M. W. Hirsch, *Differential Topology*, Graduate Texts in Mathematics 33, Springer, 1976,
  Chapter 3, Theorem 2.7.
* D. McDuff, D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS Colloquium
  Publications 52, 2012, Appendix A.3.
-/

public section

open Filter Function MeasureTheory MeasureTheory.Measure Module Set
open scoped ContDiff Topology

namespace TauCeti

variable {E Λ F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup Λ] [NormedSpace ℝ Λ] [FiniteDimensional ℝ Λ]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

/-- A parameter `l` is regular on the set `U` for the level equation `f (x, l) = c` when its
fixed-parameter linearization is surjective at every solution `x` with `(x, l) ∈ U`.

This is `TauCeti.IsRegularParameter` with the solutions restricted to `U`; the two agree for
`U = univ` (`TauCeti.isRegularParameterOn_univ`). As there, surjectivity of the total derivative
on `E × Λ` is a separate hypothesis of the transversality theorems. -/
def IsRegularParameterOn (f : E × Λ → F) (U : Set (E × Λ)) (c : F) (l : Λ) : Prop :=
  ∀ x, (x, l) ∈ U → f (x, l) = c →
    Surjective ((fderiv ℝ f (x, l)).comp (ContinuousLinearMap.inl ℝ E Λ))

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ Λ] [FiniteDimensional ℝ F] in
/-- Regularity on the whole space is regularity. -/
theorem isRegularParameterOn_univ {f : E × Λ → F} {c : F} {l : Λ} :
    IsRegularParameterOn f univ c l ↔ IsRegularParameter f c l := by
  rw [isRegularParameter_iff]
  exact ⟨fun h x hx ↦ h x (mem_univ _) hx, fun h x _ hx ↦ h x hx⟩

variable [MeasurableSpace Λ] [BorelSpace Λ] (ν : Measure Λ) [IsAddHaarMeasure ν]

/-- **Local parametric transversality, measure form.** Near a solution `(x, l)` of a
parametrized equation whose total linearization is surjective, the parameters carrying a nearby
solution at which the fixed-parameter linearization fails to be surjective form a set of additive
Haar measure zero.

The smoothness order must meet the Morse--Sard threshold `(dim)² + 1` for the kernel of the total
linearization, the source of the local parameter map. -/
theorem exists_mem_nhds_addHaar_setOf_exists_not_surjective_fderiv_comp_inl_eq_zero
    {f : E × Λ → F} {c : F} {n : ℕ∞ω} {x : E} {l : Λ}
    (hcont : ContDiffAt ℝ n f (x, l)) (htotal : Surjective (fderiv ℝ f (x, l)))
    (hxl : f (x, l) = c)
    (hn : ((finrank ℝ (fderiv ℝ f (x, l)).ker * finrank ℝ (fderiv ℝ f (x, l)).ker + 1 : ℕ) :
      ℕ∞ω) ≤ n) :
    ∃ Q ∈ 𝓝 (x, l), ν {l' | ∃ x', (x', l') ∈ Q ∧ f (x', l') = c ∧
      ¬ Surjective ((fderiv ℝ f (x', l')).comp (ContinuousLinearMap.inl ℝ E Λ))} = 0 := by
  have : CompleteSpace E := FiniteDimensional.complete ℝ E
  have : CompleteSpace Λ := FiniteDimensional.complete ℝ Λ
  have : CompleteSpace F := FiniteDimensional.complete ℝ F
  set T := fderiv ℝ f (x, l)
  set k : ℕ := finrank ℝ T.ker * finrank ℝ T.ker + 1 with hkdef
  have hk0 : ((k : ℕ∞ω)) ≠ 0 := by simp [hkdef]
  have hkω : ((k : ℕ∞ω)) ≠ ∞ := by simp
  have hn0 : n ≠ 0 := fun h ↦ hk0 (le_antisymm (h ▸ hn) bot_le)
  -- The total linearization in coproduct form, and the level-set chart it provides.
  set D₁ : E →L[ℝ] F := T.comp (ContinuousLinearMap.inl ℝ E Λ)
  set D₂ : Λ →L[ℝ] F := T.comp (ContinuousLinearMap.inr ℝ E Λ)
  have hcop : D₁.coprod D₂ = T := ContinuousLinearMap.coprod_comp_inl_inr T
  have hstrict : HasStrictFDerivAt f (D₁.coprod D₂) (x, l) := by
    rw [hcop]
    exact hcont.hasStrictFDerivAt_fderiv hn0
  have hsurj : Surjective (D₁.coprod D₂) := by rwa [hcop]
  have hker : (D₁.coprod D₂).ker.ClosedComplemented :=
    (D₁.coprod D₂).ker_closedComplemented_of_finiteDimensional_range
  set Φ := levelSetChart hstrict (LinearMap.range_eq_top.mpr hsurj) hker hxl with hΦ
  set g := levelSetParameterMap hstrict hsurj hker hxl
  have hgC : ContDiffAt ℝ n g 0 := contDiffAt_levelSetParameterMap hstrict hcont hsurj hker hxl
  -- Morse--Sard for the parameter map on a neighbourhood of the chart origin.
  obtain ⟨V, hVC, hVopen, hV0⟩ :=
    eventually_nhds_iff.1 ((hgC.of_le hn).eventually hkω)
  have hkV : ((finrank ℝ (D₁.coprod D₂).ker * finrank ℝ (D₁.coprod D₂).ker + 1 : ℕ) : ℕ∞ω) ≤
      (k : ℕ∞ω) := by
    rw [hcop]
  have hnull : ν (g '' (V ∩ {y | ¬ Surjective (fderiv ℝ g y)})) = 0 :=
    TauCeti.addHaar_image_criticalPoints_eq_zero ν (fun y hy ↦ hVC y hy) hkV
  -- Points of the chart near the origin at which `f` is differentiable and the chart is the
  -- implicit-function coordinate.
  have hdiff : ∀ᶠ w in 𝓝 ((x, l) : E × Λ), DifferentiableAt ℝ f w := by
    filter_upwards [(hcont.of_le hn).eventually hkω] with w hw
    exact hw.differentiableAt hk0
  have hsource : hstrict.implicitCoordSource (LinearMap.range_eq_top.mpr hsurj) hker ∈
      𝓝 ((x, l) : E × Λ) :=
    (hstrict.isOpen_implicitCoordSource _ _).mem_nhds (hstrict.mem_implicitCoordSource _ _)
  have hval0 : ((Φ.symm 0 : ↥{z | f z = c}) : E × Λ) = (x, l) := by
    rw [hΦ, levelSetChart_symm_zero]
  have hcontAt : ContinuousAt (fun y ↦ ((Φ.symm y : ↥{z | f z = c}) : E × Λ)) 0 :=
    (hasStrictFDerivAt_coe_levelSetChart_symm hstrict (LinearMap.range_eq_top.mpr hsurj) hker
      hxl).continuousAt
  have hW : (fun y ↦ ((Φ.symm y : ↥{z | f z = c}) : E × Λ)) ⁻¹'
      (hstrict.implicitCoordSource (LinearMap.range_eq_top.mpr hsurj) hker ∩
        {w | DifferentiableAt ℝ f w}) ∈ 𝓝 (0 : (D₁.coprod D₂).ker) := by
    refine hcontAt.preimage_mem_nhds ?_
    rw [hval0]
    exact inter_mem hsource hdiff
  set N : Set (D₁.coprod D₂).ker := V ∩ Φ.target ∩
    (fun y ↦ ((Φ.symm y : ↥{z | f z = c}) : E × Λ)) ⁻¹'
      (hstrict.implicitCoordSource (LinearMap.range_eq_top.mpr hsurj) hker ∩
        {w | DifferentiableAt ℝ f w})
  have hNnhds : N ∈ 𝓝 (0 : (D₁.coprod D₂).ker) :=
    inter_mem (inter_mem (hVopen.mem_nhds hV0)
      (Φ.open_target.mem_nhds (mem_levelSetChart_target hstrict _ hker hxl))) hW
  -- The chart source, pulled back to a neighbourhood of `(x, l)` in `E × Λ`.
  have hz0 : (⟨(x, l), hxl⟩ : ↥{z | f z = c}) ∈ Φ.source :=
    mem_levelSetChart_source hstrict (LinearMap.range_eq_top.mpr hsurj) hker hxl
  have hΦ0 : Φ ⟨(x, l), hxl⟩ = 0 :=
    levelSetChart_apply_self hstrict (LinearMap.range_eq_top.mpr hsurj) hker hxl
  have hQ' : Φ.source ∩ Φ ⁻¹' N ∈ 𝓝 (⟨(x, l), hxl⟩ : ↥{z | f z = c}) :=
    inter_mem (Φ.open_source.mem_nhds hz0) (Φ.continuousAt hz0 (hΦ0 ▸ hNnhds))
  obtain ⟨Q, hQnhds, hQsub⟩ := (mem_nhds_subtype _ _ _).1 hQ'
  refine ⟨Q, hQnhds, measure_mono_null ?_ hnull⟩
  rintro l' ⟨x', hx'Q, hx'c, hx'bad⟩
  set w : ↥{z | f z = c} := ⟨(x', l'), hx'c⟩
  have hwQ : w ∈ Φ.source ∩ Φ ⁻¹' N := hQsub hx'Q
  obtain ⟨hwsource, hwN⟩ := hwQ
  obtain ⟨⟨hwV, hwtarget⟩, hwcoord, hwdiff⟩ := hwN
  have hwback : Φ.symm (Φ w) = w := Φ.left_inv hwsource
  refine ⟨Φ w, ⟨hwV, ?_⟩, levelSetParameterMap_levelSetChart hstrict hsurj hker hxl hwsource⟩
  -- Criticality of the parameter map at `Φ w` is failure of regularity at `w`.
  have hA : HasFDerivAt f
      (((fderiv ℝ f ((Φ.symm (Φ w) : ↥{z | f z = c}) : E × Λ)).comp
          (ContinuousLinearMap.inl ℝ E Λ)).coprod
        ((fderiv ℝ f ((Φ.symm (Φ w) : ↥{z | f z = c}) : E × Λ)).comp
          (ContinuousLinearMap.inr ℝ E Λ)))
      ((Φ.symm (Φ w) : ↥{z | f z = c}) : E × Λ) := by
    rw [ContinuousLinearMap.coprod_comp_inl_inr]
    exact hwdiff.hasFDerivAt
  have hiff : Surjective (fderiv ℝ g (Φ w)) ↔
      Surjective ((fderiv ℝ f ((Φ.symm (Φ w) : ↥{z | f z = c}) : E × Λ)).comp
        (ContinuousLinearMap.inl ℝ E Λ)) :=
    surjective_fderiv_levelSetParameterMap_iff_of_mem hstrict hsurj hker hxl hwtarget hwcoord hA
  rw [hwback] at hiff
  exact fun hs ↦ hx'bad (hiff.1 hs)

/-- **Parametric transversality in finite dimensions, measure form.** For a parametrized equation
between finite-dimensional real normed spaces, the parameters that are not regular on a set `U`
form a set of additive Haar measure zero, provided the total linearization is surjective at
every solution in `U` and the smoothness order meets the Morse--Sard threshold `(dim)² + 1` for
the kernel of the total linearization there.

The hypotheses are imposed only along the level set `f⁻¹(c)` inside `U`. Countably many of the
neighbourhoods of the local theorem
`TauCeti.exists_mem_nhds_addHaar_setOf_exists_not_surjective_fderiv_comp_inl_eq_zero` cover that
level set, which is second countable. -/
theorem addHaar_setOf_not_isRegularParameterOn_eq_zero {f : E × Λ → F} {U : Set (E × Λ)}
    {c : F} {n : ℕ∞ω}
    (hcont : ∀ z ∈ U, f z = c → ContDiffAt ℝ n f z)
    (htotal : ∀ z ∈ U, f z = c → Surjective (fderiv ℝ f z))
    (hn : ∀ z ∈ U, f z = c →
      ((finrank ℝ (fderiv ℝ f z).ker * finrank ℝ (fderiv ℝ f z).ker + 1 : ℕ) : ℕ∞ω) ≤ n) :
    ν {l | ¬ IsRegularParameterOn f U c l} = 0 := by
  let S : Set (E × Λ) := {z | z ∈ U ∧ f z = c}
  -- The local theorem at each solution in `U`, with the neighbourhood confined to `U`.
  have hlocal : ∀ z ∈ S, ∃ Q ∈ 𝓝 z, ν {l' | ∃ x', (x', l') ∈ Q ∧ f (x', l') = c ∧
      ¬ Surjective ((fderiv ℝ f (x', l')).comp (ContinuousLinearMap.inl ℝ E Λ))} = 0 := by
    rintro ⟨x, l⟩ ⟨hzU, hzc⟩
    exact exists_mem_nhds_addHaar_setOf_exists_not_surjective_fderiv_comp_inl_eq_zero ν
      (hcont _ hzU hzc) (htotal _ hzU hzc) hzc (hn _ hzU hzc)
  choose! Q hQnhds hQnull using hlocal
  let B : E × Λ → Set Λ := fun z ↦ {l' | ∃ x', (x', l') ∈ Q z ∧ f (x', l') = c ∧
    ¬ Surjective ((fderiv ℝ f (x', l')).comp (ContinuousLinearMap.inl ℝ E Λ))}
  -- Second countability reduces this neighbourhood cover of the level set to a countable one.
  obtain ⟨t, hts, htcount, htcover⟩ := TopologicalSpace.countable_cover_nhdsWithin
    (f := Q) (s := S) fun z hz ↦ nhdsWithin_le_nhds (hQnhds z hz)
  refine measure_mono_null (fun l hl ↦ ?_)
    ((measure_biUnion_null_iff (s := B) htcount).2 fun z hz ↦ hQnull z (hts hz))
  simp only [mem_ofPred_eq, IsRegularParameterOn, not_forall] at hl
  obtain ⟨x, hxU, hxc, hxbad⟩ := hl
  obtain ⟨z, hzt, hwQ⟩ := mem_iUnion₂.1 (htcover ⟨hxU, hxc⟩)
  exact mem_iUnion₂.2 ⟨z, hzt, x, hwQ, hxc, hxbad⟩

/-- Almost every parameter is regular on a set `U`, for additive Haar measure. -/
theorem ae_isRegularParameterOn {f : E × Λ → F} {U : Set (E × Λ)} {c : F} {n : ℕ∞ω}
    (hcont : ∀ z ∈ U, f z = c → ContDiffAt ℝ n f z)
    (htotal : ∀ z ∈ U, f z = c → Surjective (fderiv ℝ f z))
    (hn : ∀ z ∈ U, f z = c →
      ((finrank ℝ (fderiv ℝ f z).ker * finrank ℝ (fderiv ℝ f z).ker + 1 : ℕ) : ℕ∞ω) ≤ n) :
    ∀ᵐ l ∂ν, IsRegularParameterOn f U c l :=
  ae_iff.2 (addHaar_setOf_not_isRegularParameterOn_eq_zero ν hcont htotal hn)

omit [MeasurableSpace Λ] [BorelSpace Λ] in
/-- The parameters that are regular on a set `U` are dense. This form carries no
measure-theoretic data; the Haar measure used to prove it is chosen inside the proof. -/
theorem dense_setOf_isRegularParameterOn {f : E × Λ → F} {U : Set (E × Λ)} {c : F}
    {n : ℕ∞ω} (hcont : ∀ z ∈ U, f z = c → ContDiffAt ℝ n f z)
    (htotal : ∀ z ∈ U, f z = c → Surjective (fderiv ℝ f z))
    (hn : ∀ z ∈ U, f z = c →
      ((finrank ℝ (fderiv ℝ f z).ker * finrank ℝ (fderiv ℝ f z).ker + 1 : ℕ) : ℕ∞ω) ≤ n) :
    Dense {l | IsRegularParameterOn f U c l} := by
  borelize Λ
  exact Measure.dense_of_ae (μ := (addHaar : Measure Λ))
    (ae_isRegularParameterOn addHaar hcont htotal hn)

end TauCeti
