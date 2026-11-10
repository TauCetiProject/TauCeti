/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Sard.FlatStratum
public import TauCeti.Analysis.Calculus.Sard.IntermediateStratum
import TauCeti.Analysis.Calculus.BumpFunction.FiniteDimension
import TauCeti.Analysis.Calculus.Sard.MorseVanishing.Basic
import TauCeti.Analysis.Calculus.Sard.Oscillation
import TauCeti.MeasureTheory.Measure.Haar.Hausdorff
import TauCeti.MeasureTheory.Measure.Haar.Unique
import TauCeti.MeasureTheory.Measure.LocallyNull

/-!
# Sard's theorem on the locus where the derivative vanishes

This file proves that a map between finite-dimensional real normed spaces `E` and `F`, with `F`
nontrivial, sends the set of points at which its Fréchet derivative vanishes to a set of additive
Haar measure zero, provided it is `C^k` at those points with `k ≥ finrank ℝ E - finrank ℝ F + 1`.
This is the sharp regularity of the Morse--Sard theorem. Since a linear map onto a
one-dimensional space is surjective exactly when it is nonzero, this is the full Morse--Sard
theorem whenever the target is one-dimensional. For a general target the remaining stratum, the
set of critical points at which the derivative is nonzero but not surjective, is handled by a
Fubini argument on a local fibration of the source in
`TauCeti.Analysis.Calculus.Sard.OutermostStratum`, which runs its induction against the result
here.

The proof is Morse's, in the formulation of Norton. Write `m = finrank ℝ E`, `d = finrank ℝ F`
and `N = m - d + 1`, so that `m ≤ N * d`. After choosing coordinates on `E` and `F` and extending
a local germ of `f` to a globally `C^N` map, the Morse criticality lemma
`TauCeti.exists_cover_of_critical` covers the vanishing-derivative locus by a countable set and
countably many bounded pieces on each of which `‖f y - f x‖ = o(‖y - x‖ ^ N)` uniformly. Such a
modulus is a Hölder bound of exponent `m / d` with an arbitrarily small constant, so
`TauCeti.volume_image_eq_zero_of_oscillation_pow` makes the image of each piece null. Second
countability of the source turns local nullity into global nullity through
`TauCeti.measure_image_null_of_locally_null`.

The file also records the stratum estimate
`TauCeti.addHaar_image_eq_zero_of_iteratedFDeriv_ne_zero`: the points where the derivatives of
order `1 ≤ j ≤ i` vanish and the one of order `i + 1` does not lie locally on a hypersurface, so
the flat-stratum estimate controls their image at regularity `C^{i+1}`.

## Main results

* `TauCeti.addHaar_image_eq_zero_of_fderiv_eq_zero`: the image of a set of points at which the
  derivative vanishes is null, for a map that is `C^k` at those points with
  `k ≥ finrank ℝ E - finrank ℝ F + 1`.
* `TauCeti.ContDiff.addHaar_image_vanishingFDeriv_eq_zero`: its global form.
* `TauCeti.addHaar_image_eq_zero_of_iteratedFDeriv_ne_zero`: the image of an intermediate stratum
  `Σ_i \ Σ_{i+1}` is null at regularity `C^{i+1}`, when `finrank ℝ E ≤ (i + 1) * finrank ℝ F`.
* `TauCeti.setOf_not_surjective_fderiv_eq_setOf_fderiv_eq_zero_of_finrank_eq_one`: for a
  one-dimensional target, the critical locus is exactly the vanishing-derivative locus.

## References

* A. P. Morse, *The behavior of a function on its critical set*, Ann. of Math. 40 (1939), 62–70.
* A. Sard, *The measure of the critical values of differentiable maps*, Bull. Amer. Math. Soc. 48
  (1942), 883–890, for the sharp regularity.
* A. Norton, *A critical set with nonnull image has large Hausdorff dimension*, Trans. Amer. Math.
  Soc. 296 (1986), Sections 4 and 5, for the decomposition and the measure estimate in the
  integer-regularity case.
-/

public section

open Function MeasureTheory MeasureTheory.Measure Module Set

open scoped ContDiff Topology

namespace TauCeti

section Sard

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F] [Nontrivial F] (ν : Measure F) [IsAddHaarMeasure ν]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {f : E → F} {s : Set E} {k : ℕ}

/-- A finite smoothness exponent is not `∞`, the side condition of `ContDiffAt.contDiffOn`. -/
private theorem natCast_ne_infty (m : ℕ) : (m : ℕ∞ω) ≠ ∞ := by simp

/-- The vanishing-derivative estimate between coordinate spaces: the Morse criticality lemma
cuts the vanishing locus into pieces with a small oscillation modulus of order `k + 1`. -/
private theorem volume_image_vanishingFDeriv_eq_zero_pi {m d : ℕ} (hd : 0 < d)
    (hmd : m ≤ (k + 1) * d) {g : (Fin m → ℝ) → Fin d → ℝ} (hg : ContDiff ℝ (k + 1) g) :
    volume (g '' {x | fderiv ℝ g x = 0}) = 0 := by
  have : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  obtain ⟨A₀, P, hA₀, hP, hcov, hmod⟩ :=
    exists_cover_of_critical (f := g) {x | fderiv ℝ g x = 0} hg fun _ hx ↦ hx
  refine measure_mono_null (image_mono hcov) ?_
  rw [image_union]
  refine measure_union_null ((hA₀.image g).measure_zero _) ?_
  rw [sUnion_eq_biUnion, image_iUnion₂]
  refine (measure_biUnion_null_iff hP).2 fun S hS ↦ ?_
  exact volume_image_eq_zero_of_oscillation_pow (hmod S hS).1 (by simpa using hmd) (hmod S hS).2

/-- The vanishing-derivative estimate for a globally `C^(k+1)` map, transported to coordinate
spaces by linear equivalences. -/
private theorem addHaar_image_vanishingFDeriv_eq_zero_of_contDiff
    (hmd : finrank ℝ E ≤ (k + 1) * finrank ℝ F) {g : E → F} (hg : ContDiff ℝ (k + 1) g) :
    ν (g '' {x | fderiv ℝ g x = 0}) = 0 := by
  let e₁ : (Fin (finrank ℝ E) → ℝ) ≃L[ℝ] E := ContinuousLinearEquiv.ofFinrankEq (by simp)
  let e₂ : F ≃L[ℝ] (Fin (finrank ℝ F) → ℝ) := ContinuousLinearEquiv.ofFinrankEq (by simp)
  let G : (Fin (finrank ℝ E) → ℝ) → Fin (finrank ℝ F) → ℝ := fun y ↦ e₂ (g (e₁ y))
  have hG : ContDiff ℝ (k + 1) G := e₂.contDiff.comp (hg.comp e₁.contDiff)
  have hnull := volume_image_vanishingFDeriv_eq_zero_pi finrank_pos hmd hG
  -- The coordinate change carries the vanishing locus of `g` into that of `G`.
  have hsub : g '' {x | fderiv ℝ g x = 0} ⊆ e₂ ⁻¹' (G '' {y | fderiv ℝ G y = 0}) := by
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨e₁.symm x, ?_, by simp [G]⟩
    have hgx : HasFDerivAt g (fderiv ℝ g (e₁ (e₁.symm x))) (e₁ (e₁.symm x)) :=
      (hg.differentiable (by simp) _).hasFDerivAt
    have h := (e₂.hasFDerivAt.comp (e₁.symm x) (hgx.comp (e₁.symm x) e₁.hasFDerivAt)).fderiv
    rw [ContinuousLinearEquiv.apply_symm_apply, show fderiv ℝ g x = 0 from hx] at h
    simpa [G, Function.comp_def] using h
  refine measure_mono_null hsub ?_
  simpa only [ContinuousLinearEquiv.toContinuousAddEquiv_coe] using
    (e₂.toContinuousAddEquiv.quasiMeasurePreserving_addHaar ν volume).preimage_null hnull

/-- **Sard's theorem on the locus where the derivative vanishes, at the sharp regularity.** Let
`f` be a map between finite-dimensional real normed spaces with nontrivial target, and let `s` be
a set at each point of which `f` is `C^n` and the Fréchet derivative of `f` vanishes. If
`finrank ℝ E - finrank ℝ F < n`, then `f '' s` has additive Haar measure zero. The set need not be
open or measurable. -/
theorem addHaar_image_eq_zero_of_fderiv_eq_zero {n : ℕ∞ω}
    (hk : ((finrank ℝ E - finrank ℝ F + 1 : ℕ) : ℕ∞ω) ≤ n)
    (hf : ∀ x ∈ s, ContDiffAt ℝ n f x) (hs : ∀ x ∈ s, fderiv ℝ f x = 0) : ν (f '' s) = 0 := by
  have hF : 0 < finrank ℝ F := finrank_pos
  have hmd : finrank ℝ E ≤ (finrank ℝ E - finrank ℝ F + 1) * finrank ℝ F := by
    rcases le_or_gt (finrank ℝ E) (finrank ℝ F) with h | h
    · simpa [Nat.sub_eq_zero_of_le h] using h
    · obtain ⟨t, ht⟩ := Nat.exists_eq_add_of_lt h
      rw [ht, show finrank ℝ F + t + 1 - finrank ℝ F + 1 = t + 2 by omega]
      nlinarith
  refine measure_image_null_of_locally_null (HereditarilyLindelofSpace.isLindelof _)
    fun x hx ↦ ?_
  obtain ⟨g, hg, -, hgf⟩ :=
    ((hf x hx).of_le hk).exists_contDiff_eventuallyEq_of_finiteDimensional _
  obtain ⟨U, hU, hUopen, hxU⟩ := _root_.mem_nhds_iff.1 (hgf.and (hgf.fderiv (𝕜 := ℝ)))
  refine ⟨s ∩ U, inter_mem_nhdsWithin s (hUopen.mem_nhds hxU), ?_⟩
  refine measure_mono_null ?_
    (addHaar_image_vanishingFDeriv_eq_zero_of_contDiff ν hmd (by exact_mod_cast hg))
  rintro _ ⟨y, hy, rfl⟩
  exact ⟨y, (hU hy.2).2.trans (hs y hy.1), (hU hy.2).1⟩

/-- The image under a sufficiently smooth map with nontrivial target of the whole locus where its
Fréchet derivative vanishes has additive Haar measure zero. The map must be `C^n` with
`finrank ℝ E - finrank ℝ F < n`. -/
theorem ContDiff.addHaar_image_vanishingFDeriv_eq_zero {n : ℕ∞ω} (hf : ContDiff ℝ n f)
    (hk : ((finrank ℝ E - finrank ℝ F + 1 : ℕ) : ℕ∞ω) ≤ n) :
    ν (f '' {x | fderiv ℝ f x = 0}) = 0 :=
  addHaar_image_eq_zero_of_fderiv_eq_zero ν hk (fun _ _ ↦ hf.contDiffAt) fun _ hx ↦ hx

/-- The complement of the image of the locus where the derivative of a sufficiently smooth map
with nontrivial target vanishes is dense. -/
theorem ContDiff.dense_compl_image_vanishingFDeriv {n : ℕ∞ω} (hf : ContDiff ℝ n f)
    (hk : ((finrank ℝ E - finrank ℝ F + 1 : ℕ) : ℕ∞ω) ≤ n) :
    Dense (f '' {x | fderiv ℝ f x = 0})ᶜ :=
  interior_eq_empty_iff_dense_compl.1 <| Measure.interior_eq_empty_of_null <|
    ContDiff.addHaar_image_vanishingFDeriv_eq_zero (ν := addHaar) hf hk

omit [Nontrivial F] in
/-- An intermediate stratum is null at the regularity of its order. Let `s` be a set of points at
which the derivatives of order `1 ≤ j ≤ i` vanish but the derivative of order `i + 1` does not, and
at which `f` is `C^{i+1}`. Near each such point, `s` lies on a `C¹` hypersurface by
`TauCeti.exists_parametrization_iteratedFDeriv_eq_zero`, so it has Hausdorff dimension at most
`finrank ℝ E - 1`, and the flat-stratum estimate divides this by `i + 1` under `f`. Hence
`f '' s` is null as soon as `finrank ℝ E ≤ (i + 1) * finrank ℝ F`. -/
theorem addHaar_image_eq_zero_of_iteratedFDeriv_ne_zero {i : ℕ} (hi : 1 ≤ i)
    (hf : ∀ x ∈ s, ContDiffAt ℝ (i + 1 : ℕ) f x)
    (hs : ∀ x ∈ s, (∀ j, 1 ≤ j → j ≤ i → iteratedFDeriv ℝ j f x = 0) ∧
      iteratedFDeriv ℝ (i + 1) f x ≠ 0)
    (hdim : finrank ℝ E ≤ (i + 1) * finrank ℝ F) : ν (f '' s) = 0 := by
  refine measure_image_null_of_locally_null (HereditarilyLindelofSpace.isLindelof _)
    fun a ha ↦ ?_
  obtain ⟨hai, hai1⟩ := hs a ha
  have hfa : ContDiffAt ℝ ((1 : ℕ∞ω) + i) f a := by
    simpa [add_comm] using hf a ha
  obtain ⟨g, g', θ, -, -, -, -, -, hθ, -, hcover, hrank⟩ :=
    exists_parametrization_iteratedFDeriv_eq_zero hfa one_ne_zero (hai i hi le_rfl) hai1
  obtain ⟨w, hw, hθw⟩ := hθ.contDiffOn (m := 1) le_rfl (by simp)
  obtain ⟨ρ, hρ, hρw⟩ := Metric.mem_nhds_iff.1 hw
  obtain ⟨u, hu, hfu⟩ := (hf a ha).contDiffOn (m := ((i + 1 : ℕ) : ℕ∞ω)) le_rfl
    fun h ↦ absurd h (natCast_ne_infty _)
  set t : Set E := s ∩ (interior u ∩
    {x | iteratedFDeriv ℝ i f x = 0 → x ∈ θ '' Metric.ball 0 ρ}) with ht
  refine ⟨t, inter_mem_nhdsWithin _ (Filter.inter_mem (interior_mem_nhds.2 hu)
    (hcover _ (Metric.ball_mem_nhds 0 hρ))), ?_⟩
  -- The local piece lies on the hypersurface parametrized by `θ`.
  have hdimt : dimH t ≤ finrank ℝ ↥g'.ker := by
    have hθt : t ⊆ θ '' Metric.ball 0 ρ := fun x hx ↦ hx.2.2 ((hs x hx.1).1 i hi le_rfl)
    refine (dimH_mono hθt).trans ((DifferentiableOn.dimH_image_le
      ((hθw.mono hρw).differentiableOn one_ne_zero)).trans ?_)
    simpa only [Real.dimH_univ_eq_finrank] using
      dimH_mono (subset_univ (Metric.ball (0 : ↥g'.ker) ρ))
  have himg := dimH_image_le_of_iteratedFDeriv_eq_zero (k := i) (s := t)
    isOpen_interior (hfu.mono interior_subset) (fun x hx ↦ hx.2.1) fun x hx ↦ (hs x hx.1).1
  apply addHaar_eq_zero_of_dimH_lt_finrank ν
  refine himg.trans_lt ((ENNReal.div_le_div_right hdimt _).trans_lt ?_)
  rw [ENNReal.div_lt_iff (Or.inl (by simp)) (Or.inl (by simp)), mul_comm]
  exact_mod_cast (by omega : finrank ℝ ↥g'.ker < (i + 1) * finrank ℝ F)

section OneDimensional

variable (hF : finrank ℝ F = 1)

include hF

omit [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F] [Nontrivial F]
  [FiniteDimensional ℝ E] in
/-- A linear map into a one-dimensional space is surjective exactly when it is nonzero, so the
critical points of a map into such a space are the points where its derivative vanishes. -/
@[simp] theorem setOf_not_surjective_fderiv_eq_setOf_fderiv_eq_zero_of_finrank_eq_one :
    {x | ¬ Surjective (fderiv ℝ f x)} = {x | fderiv ℝ f x = 0} := by
  let _ : Nontrivial F := Module.nontrivial_of_finrank_eq_succ hF
  ext x
  simp only [mem_ofPred_eq, not_iff_comm]
  constructor
  · intro hx
    exact _root_.surjective_of_ne_zero_of_finrank_eq_one (f := (fderiv ℝ f x : E →ₗ[ℝ] F)) hF
      fun hzero ↦ hx (ContinuousLinearMap.coe_injective hzero)
  · rintro hsurj h
    have h1 : iteratedFDeriv ℝ 1 f x = 0 := by
      rw [← norm_eq_zero, norm_iteratedFDeriv_one, h, norm_zero]
    exact not_surjective_fderiv_of_iteratedFDeriv_one_eq_zero h1 hsurj

end OneDimensional

end Sard

end TauCeti

end
