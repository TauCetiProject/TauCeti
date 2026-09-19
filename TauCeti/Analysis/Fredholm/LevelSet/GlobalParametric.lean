/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fredholm.LevelSet.Parametric

/-!
# Global parametric transversality for Fredholm equations

Let `f : E × Λ → F` be a parametrized equation. A parameter `l` is regular at the level
`c` when the fixed-parameter linearization of `x ↦ f (x, l)` is surjective at every solution.
This file proves that the regular parameters form a residual, and hence dense, subset of `Λ`
provided the universal linearization is surjective and the fixed-parameter linearization is
Fredholm at every solution.

The proof globalizes the local statement in
`TauCeti.Analysis.Fredholm.LevelSet.Parametric`. Around each solution, a level-set chart turns the
projection to `Λ` into `TauCeti.levelSetParameterMap`; local Sard--Smale puts its non-regular
values in a nowhere dense set. Second countability of the universal level set supplies a
countable subcover, so all non-regular parameters form a meagre set. Completeness of `Λ` then
makes the residual set of regular parameters dense by the Baire category theorem.

This is the parametric transversality theorem for maps between Banach spaces. Fredholm sections
of Banach bundles require a separate bundle-level extension.

## Main results

* `TauCeti.IsRegularParameter`: every solution at a parameter has surjective fixed-parameter
  linearization.
* `TauCeti.isMeagre_setOfPred_not_isRegularParameter`: the non-regular parameters of a universal
  Fredholm equation form a meagre set.
* `TauCeti.dense_setOfPred_isRegularParameter`: the regular parameters are dense.

## References

* D. McDuff, D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS Colloquium
  Publications 52, 2012, Appendix A.3.
* S. Smale, *An infinite dimensional version of Sard's theorem*, Amer. J. Math. 87 (1965),
  861--866.
-/

public section

open Filter Function Module Set
open scoped ContDiff Topology

namespace TauCeti

variable {E Λ F : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable [NormedAddCommGroup Λ] [NormedSpace ℝ Λ] [CompleteSpace Λ]
variable [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- A parameter `l` is regular for the level equation `f (x, l) = c` when its fixed-parameter
linearization is surjective at every solution `x`.

This is deliberately a condition only on the `E` direction. Surjectivity of the total derivative
on `E × Λ`, used by the parametric transversality theorem, is a separate hypothesis. -/
def IsRegularParameter (f : E × Λ → F) (c : F) (l : Λ) : Prop :=
  ∀ x, f (x, l) = c →
    Surjective ((fderiv ℝ f (x, l)).comp (ContinuousLinearMap.inl ℝ E Λ))

omit [CompleteSpace E] [CompleteSpace Λ] [CompleteSpace F] in
/-- The defining characterization of a regular parameter. -/
theorem isRegularParameter_iff {f : E × Λ → F} {c : F} {l : Λ} :
    IsRegularParameter f c l ↔
      ∀ x, f (x, l) = c →
        Surjective ((fderiv ℝ f (x, l)).comp (ContinuousLinearMap.inl ℝ E Λ)) :=
  Iff.rfl

omit [CompleteSpace E] [CompleteSpace Λ] [CompleteSpace F] in
/-- At every solution belonging to a regular parameter, the fixed-parameter linearization is
surjective. -/
theorem IsRegularParameter.surjective {f : E × Λ → F} {c : F} {l : Λ}
    (hl : IsRegularParameter f c l) {x : E} (hx : f (x, l) = c) :
    Surjective ((fderiv ℝ f (x, l)).comp (ContinuousLinearMap.inl ℝ E Λ)) :=
  hl x hx

/-- **Global parametric transversality.** The non-regular parameters of a sufficiently smooth
universal Fredholm equation form a meagre set.

The hypotheses are imposed only along the level set `f⁻¹(c)`. There the fixed-parameter
linearization must be Fredholm, the total linearization must be surjective, and the smoothness
order must meet the current Sard--Smale threshold `(dim ker)² + 1`. Second countability of the
universal source makes the level set second countable and hence allows the local nowhere dense
exceptional sets to be reduced to a countable family. -/
theorem isMeagre_setOfPred_not_isRegularParameter [SecondCountableTopology (E × Λ)]
    {f : E × Λ → F} {c : F} {n : ℕ∞ω}
    (hcont : ∀ z, f z = c → ContDiffAt ℝ n f z)
    (hFred : ∀ z, f z = c →
      ContinuousLinearMap.IsFredholm
        ((fderiv ℝ f z).comp (ContinuousLinearMap.inl ℝ E Λ)))
    (htotal : ∀ z, f z = c → Surjective (fderiv ℝ f z))
    (hn : ∀ z, f z = c →
      ((finrank ℝ ((fderiv ℝ f z).comp (ContinuousLinearMap.inl ℝ E Λ)).ker *
          finrank ℝ ((fderiv ℝ f z).comp (ContinuousLinearMap.inl ℝ E Λ)).ker + 1 : ℕ) :
        ℕ∞ω) ≤ n) :
    IsMeagre {l | ¬ IsRegularParameter f c l} := by
  let S := {z : E × Λ | f z = c}
  let fixedDeriv (z : S) : E →L[ℝ] F :=
    (fderiv ℝ f z).comp (ContinuousLinearMap.inl ℝ E Λ)
  let parameterDeriv (z : S) : Λ →L[ℝ] F :=
    (fderiv ℝ f z).comp (ContinuousLinearMap.inr ℝ E Λ)
  -- Package the coordinate-level local theorem as a neighbourhood of each solution together
  -- with one nowhere dense exceptional set in the common parameter space.
  have hlocal : ∀ z : S, ∃ Q ∈ 𝓝 z, ∃ B : Set Λ, IsNowhereDense B ∧
      ∀ w : S, w ∈ Q → ¬ Surjective (fixedDeriv w) → (w : E × Λ).2 ∈ B := by
    intro z
    have hn0 : n ≠ 0 := by
      intro hnzero
      have hpos : (0 : ℕ∞ω) <
          ((finrank ℝ (fixedDeriv z).ker * finrank ℝ (fixedDeriv z).ker + 1 : ℕ) :
            ℕ∞ω) := by
        simp
      exact (not_lt_of_ge ((hn z z.2).trans_eq hnzero) hpos)
    have hstrict : HasStrictFDerivAt f ((fixedDeriv z).coprod (parameterDeriv z)) z := by
      simpa only [fixedDeriv, parameterDeriv,
        ContinuousLinearMap.coprod_comp_inl_inr] using
        (hcont z z.2).hasStrictFDerivAt hn0
    have hfixed : ContinuousLinearMap.IsFredholm (fixedDeriv z) := hFred z z.2
    have hsurj : Surjective ((fixedDeriv z).coprod (parameterDeriv z)) := by
      simpa only [fixedDeriv, parameterDeriv,
        ContinuousLinearMap.coprod_comp_inl_inr] using htotal z z.2
    obtain ⟨N, hNnhds, -, -, hNnowhere⟩ :=
      exists_mem_nhds_isClosed_isNowhereDense_image_not_surjective_levelSetParameterMap
        hstrict (hcont z z.2) hfixed hsurj z.2 (hn z z.2) (U := univ) univ_mem
    let Φ := levelSetChart hstrict (LinearMap.range_eq_top.mpr hsurj)
      (hfixed.closedComplemented_ker_coprod hsurj) z.2
    let g := levelSetParameterMap hstrict hsurj
      (hfixed.closedComplemented_ker_coprod hsurj) z.2
    let Q : Set S := Φ.source ∩ Φ ⁻¹' N
    let B : Set Λ := g ''
      (N ∩ {k | ¬ Surjective ((fderiv ℝ f ((Φ.symm k : S) : E × Λ)).comp
        (ContinuousLinearMap.inl ℝ E Λ))})
    have hzsource : z ∈ Φ.source :=
      mem_levelSetChart_source hstrict (LinearMap.range_eq_top.mpr hsurj)
        (hfixed.closedComplemented_ker_coprod hsurj) z.2
    have hΦz : Φ z = 0 :=
      levelSetChart_apply_self hstrict (LinearMap.range_eq_top.mpr hsurj)
        (hfixed.closedComplemented_ker_coprod hsurj) z.2
    have hQnhds : Q ∈ 𝓝 z := by
      refine Filter.inter_mem (Φ.open_source.mem_nhds hzsource) ?_
      exact Φ.continuousAt hzsource (hΦz ▸ hNnhds)
    refine ⟨Q, hQnhds, B, hNnowhere, ?_⟩
    intro w hwQ hwbad
    have hwsource : w ∈ Φ.source := hwQ.1
    have hwN : Φ w ∈ N := hwQ.2
    have hwback : Φ.symm (Φ w) = w := Φ.left_inv hwsource
    have hwbad' : ¬ Surjective ((fderiv ℝ f ((Φ.symm (Φ w) : S) : E × Λ)).comp
        (ContinuousLinearMap.inl ℝ E Λ)) := by
      rw [hwback]
      exact hwbad
    refine ⟨Φ w, ⟨hwN, hwbad'⟩, ?_⟩
    exact levelSetParameterMap_levelSetChart hstrict hsurj
      (hfixed.closedComplemented_ker_coprod hsurj) z.2 hwsource
  -- Second countability reduces this neighbourhood cover of the universal level set to a
  -- countable subcover.
  choose! Q hQnhds B hBnowhere hQB using hlocal
  obtain ⟨t, -, htcount, htcover⟩ := TopologicalSpace.countable_cover_nhdsWithin
    (f := Q) (s := (univ : Set S)) fun z _ ↦ nhdsWithin_le_nhds (hQnhds z)
  have hsub : {l | ¬ IsRegularParameter f c l} ⊆ ⋃ z ∈ t, B z := by
    intro l hl
    have hl' : ¬ IsRegularParameter f c l := hl
    rw [isRegularParameter_iff] at hl'
    push Not at hl'
    obtain ⟨x, hx, hxbad⟩ := hl'
    let w : S := ⟨(x, l), hx⟩
    obtain ⟨z, hzt, hwQ⟩ := Set.mem_iUnion₂.1 (htcover (Set.mem_univ w))
    exact Set.mem_iUnion₂.2 ⟨z, hzt, hQB z w hwQ hxbad⟩
  exact IsMeagre.mono hsub
    (isMeagre_biUnion htcount fun z _ ↦ (hBnowhere z).isMeagre)

/-- The regular parameters of a sufficiently smooth universal Fredholm equation are dense.

This is the Baire-category consequence of
`TauCeti.isMeagre_setOfPred_not_isRegularParameter`. -/
theorem dense_setOfPred_isRegularParameter [SecondCountableTopology (E × Λ)]
    {f : E × Λ → F} {c : F} {n : ℕ∞ω}
    (hcont : ∀ z, f z = c → ContDiffAt ℝ n f z)
    (hFred : ∀ z, f z = c →
      ContinuousLinearMap.IsFredholm
        ((fderiv ℝ f z).comp (ContinuousLinearMap.inl ℝ E Λ)))
    (htotal : ∀ z, f z = c → Surjective (fderiv ℝ f z))
    (hn : ∀ z, f z = c →
      ((finrank ℝ ((fderiv ℝ f z).comp (ContinuousLinearMap.inl ℝ E Λ)).ker *
          finrank ℝ ((fderiv ℝ f z).comp (ContinuousLinearMap.inl ℝ E Λ)).ker + 1 : ℕ) :
        ℕ∞ω) ≤ n) :
    Dense {l | IsRegularParameter f c l} := by
  have hmeagre := isMeagre_setOfPred_not_isRegularParameter hcont hFred htotal hn
  have hcompl : {l | IsRegularParameter f c l} = {l | ¬ IsRegularParameter f c l}ᶜ := by
    ext l
    simp
  rw [hcompl]
  exact dense_of_mem_residual hmeagre

end TauCeti

end
