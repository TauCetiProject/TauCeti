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
import TauCeti.MeasureTheory.Measure.LocallyNull

/-!
# Parametric transversality in finite dimensions: the exceptional parameters are null

Let `f : E × Λ → F` be a parametrized equation between finite-dimensional real normed spaces and
`U ⊆ E × Λ` any set. A parameter `l` is *regular on `U`* at the level `c`
(`TauCeti.IsRegularParameterOn`, in `TauCeti.Analysis.Fredholm.LevelSet.GlobalParametric`) when
the fixed-parameter linearization of `x ↦ f (x, l)` is surjective at every solution `x` with
`(x, l) ∈ U`. This file proves that the parameters which are not regular on `U` form a set of
additive Haar measure zero in `Λ`, provided the total linearization is surjective at every solution
in `U` and `f` is sufficiently smooth there. The regular parameters are then dense.

This is the finite-dimensional parametric transversality theorem in its measure-theoretic form
(Guillemin--Pollack, *Differential Topology*, Chapter 2 §3, the transversality theorem; Hirsch,
*Differential Topology*, Chapter 3 Theorem 2.7). It is not a special case of
`TauCeti.isMeagre_setOf_not_isRegularParameter` and its corollary
`TauCeti.dense_setOf_isRegularParameter`, for two reasons. Those theorems conclude that the
non-regular parameters are meagre and the regular ones dense, and in finite dimensions meagreness
neither implies nor is implied by measure zero; the applications here, to the Morse--Smale
condition for almost every small perturbation of a Morse function, need the measure statement. And
their hypotheses are imposed at every solution of an equation defined on all of `E × Λ`, while the
universal equations of those applications are only smooth, and only transverse, on a subset of
their domain.

## The proof

The local step is the finite-dimensional counterpart of
`TauCeti.exists_mem_nhds_isClosed_isNowhereDense_image_not_surjective_levelSetParameterMap`. Near a
solution with surjective total linearization, `TauCeti.levelSetChart` parametrizes the universal
level set `{f = c}` by the kernel of the total linearization, and `TauCeti.levelSetParameterMap`,
the projection to `Λ` read in that chart, is as smooth as `f`. By
`TauCeti.surjective_fderiv_levelSetParameterMap_iff_of_mem` its critical points are the solutions
at which the fixed-parameter linearization is not surjective. The Morse--Sard theorem
`TauCeti.addHaar_image_criticalPoints_eq_zero` makes its critical values near the chart origin a
null set. The global step is `TauCeti.measure_image_null_of_locally_null`: the exceptional
parameters are the projection to `Λ` of the non-regular solutions in `U`, a Lindelöf set, and a
set whose projection is null near each of its points has null projection.

The regularity threshold is the one of the Morse--Sard theorem in Tau Ceti, `(dim)² + 1` with
`dim = dim E + dim Λ − dim F` the dimension of the source of the parameter map: the kernel of the
*total* linearization, which has this dimension at every solution by rank--nullity since the
total linearization is surjective there. This is coarser than Sard's sharp threshold, and it
differs from the threshold `(dim ker D₁)² + 1` of the Sard--Smale route, which is in terms of the
kernel of the *fixed-parameter* linearization.

## Main results

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

variable [MeasurableSpace Λ] [BorelSpace Λ] (ν : Measure Λ) [IsAddHaarMeasure ν]

/-- **Local parametric transversality, measure form.** Near a solution `(x, l)` of a
parametrized equation whose total linearization is surjective, the parameters carrying a nearby
solution at which the fixed-parameter linearization fails to be surjective form a set of additive
Haar measure zero.

The smoothness order must meet the Morse--Sard threshold `(dim)² + 1` for
`dim = dim E + dim Λ − dim F`, the dimension of the kernel of the total linearization, which is
the source of the local parameter map. -/
theorem exists_mem_nhds_addHaar_setOf_exists_not_surjective_fderiv_comp_inl_eq_zero
    {f : E × Λ → F} {c : F} {n : ℕ∞ω} {x : E} {l : Λ}
    (hcont : ContDiffAt ℝ n f (x, l)) (htotal : Surjective (fderiv ℝ f (x, l)))
    (hxl : f (x, l) = c)
    (hn : ((finrank ℝ E + finrank ℝ Λ - finrank ℝ F) * (finrank ℝ E + finrank ℝ Λ - finrank ℝ F)
      + 1 : ℕ) ≤ n) :
    ∃ Q ∈ 𝓝 (x, l), ν {l' | ∃ x', (x', l') ∈ Q ∧ f (x', l') = c ∧
      ¬ Surjective ((fderiv ℝ f (x', l')).comp (ContinuousLinearMap.inl ℝ E Λ))} = 0 := by
  have : CompleteSpace E := FiniteDimensional.complete ℝ E
  have : CompleteSpace Λ := FiniteDimensional.complete ℝ Λ
  have : CompleteSpace F := FiniteDimensional.complete ℝ F
  set T := fderiv ℝ f (x, l)
  set k : ℕ := (finrank ℝ E + finrank ℝ Λ - finrank ℝ F) *
    (finrank ℝ E + finrank ℝ Λ - finrank ℝ F) + 1 with hkdef
  -- By rank--nullity, the kernel of the surjective total linearization has dimension
  -- `dim E + dim Λ − dim F`.
  have hrank : finrank ℝ T.ker = finrank ℝ E + finrank ℝ Λ - finrank ℝ F := by
    have h := LinearMap.finrank_range_add_finrank_ker (T : E × Λ →ₗ[ℝ] F)
    rw [LinearMap.range_eq_top.mpr htotal, finrank_top, Module.finrank_prod] at h
    omega
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
    rw [hcop, hrank, hkdef]
  have hnull : ν (g '' (V ∩ {y | ¬ Surjective (fderiv ℝ g y)})) = 0 :=
    TauCeti.addHaar_image_criticalPoints_eq_zero ν (fun y hy ↦ hVC y hy) hkV
  -- Near the chart origin, criticality of the parameter map is failure of regularity; pull both
  -- neighbourhoods back to a neighbourhood of `(x, l)`.
  have hdiff : ∀ᶠ w in 𝓝 ((x, l) : E × Λ), DifferentiableAt ℝ f w := by
    filter_upwards [(hcont.of_le hn).eventually hkω] with w hw
    exact hw.differentiableAt hk0
  obtain ⟨W, hW, hWopen, hW0⟩ := eventually_nhds_iff.1
    (eventually_mem_target_and_surjective_fderiv_levelSetParameterMap_iff hstrict hdiff hsurj
      hker hxl)
  obtain ⟨Q, hQnhds, hQ⟩ := exists_mem_nhds_forall_mem_source_and_levelSetChart_mem hstrict hsurj
    hker hxl (inter_mem (hVopen.mem_nhds hV0) (hWopen.mem_nhds hW0))
  refine ⟨Q, hQnhds, measure_mono_null ?_ hnull⟩
  rintro l' ⟨x', hx'Q, hx'c, hx'bad⟩
  obtain ⟨hwsource, hwV, hwW⟩ := hQ ⟨(x', l'), hx'c⟩ hx'Q
  refine ⟨Φ ⟨(x', l'), hx'c⟩, ⟨hwV, fun hs ↦ hx'bad ?_⟩,
    levelSetParameterMap_levelSetChart hstrict hsurj hker hxl hwsource⟩
  have h := (hW _ hwW).2.1 hs
  rwa [Φ.left_inv hwsource] at h

/-- **Parametric transversality in finite dimensions, measure form.** For a parametrized equation
between finite-dimensional real normed spaces, the parameters that are not regular on a set `U`
form a set of additive Haar measure zero, provided the total linearization is surjective at
every solution in `U` and the smoothness order meets the Morse--Sard threshold `(dim)² + 1` for
`dim = dim E + dim Λ − dim F`, the dimension of the universal level set there.

The hypotheses are imposed only along the level set `f⁻¹(c)` inside `U`. -/
theorem addHaar_setOf_not_isRegularParameterOn_eq_zero {f : E × Λ → F} {U : Set (E × Λ)}
    {c : F} {n : ℕ∞ω}
    (hcont : ∀ z ∈ U, f z = c → ContDiffAt ℝ n f z)
    (htotal : ∀ z ∈ U, f z = c → Surjective (fderiv ℝ f z))
    (hn : ((finrank ℝ E + finrank ℝ Λ - finrank ℝ F) * (finrank ℝ E + finrank ℝ Λ - finrank ℝ F)
      + 1 : ℕ) ≤ n) :
    ν {l | ¬ IsRegularParameterOn f U c l} = 0 := by
  -- The exceptional parameters are the projection of the non-regular solutions in `U`.
  have hset : {l | ¬ IsRegularParameterOn f U c l} = Prod.snd '' {z : E × Λ | z ∈ U ∧ f z = c ∧
      ¬ Surjective ((fderiv ℝ f z).comp (ContinuousLinearMap.inl ℝ E Λ))} := by
    ext l
    constructor
    · intro hl
      rw [mem_ofPred_eq, isRegularParameterOn_iff] at hl
      push Not at hl
      obtain ⟨x, hxU, hxc, hxbad⟩ := hl
      exact ⟨(x, l), ⟨hxU, hxc, hxbad⟩, rfl⟩
    · rintro ⟨⟨x, l'⟩, ⟨hxU, hxc, hxbad⟩, rfl⟩
      exact fun h ↦ hxbad (isRegularParameterOn_iff.1 h x hxU hxc)
  rw [hset]
  refine measure_image_null_of_locally_null (HereditarilyLindelofSpace.isLindelof _) ?_
  rintro ⟨x, l⟩ ⟨hzU, hzc, -⟩
  obtain ⟨Q, hQ, hQnull⟩ :=
    exists_mem_nhds_addHaar_setOf_exists_not_surjective_fderiv_comp_inl_eq_zero ν
      (hcont _ hzU hzc) (htotal _ hzU hzc) hzc hn
  refine ⟨Q ∩ _, inter_mem (mem_nhdsWithin_of_mem_nhds hQ) self_mem_nhdsWithin,
    measure_mono_null ?_ hQnull⟩
  rintro _ ⟨⟨x', l'⟩, ⟨hx'Q, -, hx'c, hx'bad⟩, rfl⟩
  exact ⟨x', hx'Q, hx'c, hx'bad⟩

/-- Almost every parameter is regular on a set `U`, for additive Haar measure. -/
theorem ae_isRegularParameterOn {f : E × Λ → F} {U : Set (E × Λ)} {c : F} {n : ℕ∞ω}
    (hcont : ∀ z ∈ U, f z = c → ContDiffAt ℝ n f z)
    (htotal : ∀ z ∈ U, f z = c → Surjective (fderiv ℝ f z))
    (hn : ((finrank ℝ E + finrank ℝ Λ - finrank ℝ F) * (finrank ℝ E + finrank ℝ Λ - finrank ℝ F)
      + 1 : ℕ) ≤ n) :
    ∀ᵐ l ∂ν, IsRegularParameterOn f U c l :=
  ae_iff.2 (addHaar_setOf_not_isRegularParameterOn_eq_zero ν hcont htotal hn)

omit [MeasurableSpace Λ] [BorelSpace Λ] in
/-- The parameters that are regular on a set `U` are dense. The statement needs no measurable
structure on `Λ`. -/
theorem dense_setOf_isRegularParameterOn {f : E × Λ → F} {U : Set (E × Λ)} {c : F}
    {n : ℕ∞ω} (hcont : ∀ z ∈ U, f z = c → ContDiffAt ℝ n f z)
    (htotal : ∀ z ∈ U, f z = c → Surjective (fderiv ℝ f z))
    (hn : ((finrank ℝ E + finrank ℝ Λ - finrank ℝ F) * (finrank ℝ E + finrank ℝ Λ - finrank ℝ F)
      + 1 : ℕ) ≤ n) :
    Dense {l | IsRegularParameterOn f U c l} := by
  borelize Λ
  exact Measure.dense_of_ae (μ := (addHaar : Measure Λ))
    (ae_isRegularParameterOn addHaar hcont htotal hn)

end TauCeti
