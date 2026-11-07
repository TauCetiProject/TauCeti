/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Sard.FlatStratum
public import TauCeti.Analysis.Calculus.Sard.IntermediateStratum
import TauCeti.Analysis.Calculus.Sard.LowEqualDimension
import TauCeti.MeasureTheory.Measure.Haar.Hausdorff
import TauCeti.MeasureTheory.Measure.LocallyNull

/-!
# Sard's theorem on the locus where the derivative vanishes

This file proves that a sufficiently smooth map between finite-dimensional real normed spaces
sends the set of points at which its Fréchet derivative vanishes to a set of additive Haar measure
zero, with no relation required between the two dimensions beyond a nontrivial target. Since a
linear map onto a one-dimensional space is surjective exactly when it is nonzero, this is the full
Morse--Sard theorem whenever the target is one-dimensional: the critical values of a smooth
real-valued function on a finite-dimensional real normed space form a null set, and its regular
values are dense.

The proof is Morse's stratification argument, run by induction on the dimension of the source and
assembling the two estimates already available. Write `Σ_i` for the set of points at which the
iterated derivatives of order `1 ≤ j ≤ i` all vanish, and stratify `Σ_1` as
`Σ_1 = Σ_K ∪ ⋃_{i < K} (Σ_i \ Σ_{i+1})` for a depth `K` large enough that
`finrank ℝ E < (K + 1) * finrank ℝ F`.

* On the innermost stratum `Σ_K`, `TauCeti.addHaar_image_eq_zero_of_iteratedFDeriv_eq_zero`
  applies directly: enough derivatives vanish for the Hölder estimate to force nullity.
* Near a point of `Σ_i \ Σ_{i+1}`,
  `TauCeti.exists_parametrization_iteratedFDeriv_eq_zero` carries `Σ_i` by a `C^r` map `θ` out of
  a space of dimension `finrank ℝ E - 1`. Every point of `Σ_1` in the image is a point where
  `f ∘ θ` has vanishing derivative, by the chain rule, so the inductive hypothesis in dimension
  `finrank ℝ E - 1` applies to `f ∘ θ` and returns the local nullity of the image.

Both steps are local, and second countability of the source turns local nullity into global
nullity through `TauCeti.measure_image_null_of_locally_null`.

Each descent step costs derivatives, since the parametrization `θ` is only as smooth as the
implicit function theorem makes it; the regularity `finrank ℝ E * finrank ℝ E + 1` recorded below
is a convenient sufficient bound rather than the sharp one. Morse--Sard holds already for `C^k`
maps with `k ≥ max 1 (finrank ℝ E - finrank ℝ F + 1)`, and smooth maps satisfy every bound in
sight.

At that sharp exponent `N = finrank ℝ E - finrank ℝ F + 1` the descent can still be run when
`finrank ℝ E ≤ finrank ℝ F + 2`
(`TauCeti.addHaar_image_eq_zero_of_fderiv_eq_zero_of_finrank_le_add_two`). Only the stratum
`Σ_1 \ Σ_2` is handled by induction: there the parametrization `θ` costs one derivative, exactly
what the drop in source dimension saves. A stratum `Σ_i \ Σ_{i+1}` with `2 ≤ i < N` lies locally
on a `C¹` hypersurface, so its image has Hausdorff dimension at most
`(finrank ℝ E - 1) / (i + 1)`, which is less than `finrank ℝ F` in this range. The innermost
stratum `Σ_N` is handled by the Hausdorff-measure form of the flat-stratum estimate,
`TauCeti.addHaar_image_eq_zero_of_iteratedFDeriv_eq_zero_of_finrank_le_mul`, which needs only
`C^N`. In higher codimension the strata with `i ≥ 2` are no longer small enough for this
dimension count, and the sharp theorem needs a finer argument than the one run here.

The remaining stratum of the general Morse--Sard theorem, the set of critical points at which the
derivative is nonzero but not surjective, is handled by a Fubini argument on a local fibration of
the source in `TauCeti.Analysis.Calculus.Sard.OutermostStratum`, where the theorem itself is
assembled; the results here are what that argument runs its induction against.

The nullity result also yields density of the complement of the image of the vanishing-derivative
locus; for a one-dimensional target this complement is exactly the set of regular values.

## Main results

* `TauCeti.addHaar_image_eq_zero_of_fderiv_eq_zero`: the image of a set of points at which the
  derivative vanishes is null, for a map that is `C^k` at those points with `k` large enough.
* `TauCeti.ContDiff.addHaar_image_vanishingFDeriv_eq_zero`: its global form for a smooth map.
* `TauCeti.addHaar_image_eq_zero_of_fderiv_eq_zero_of_finrank_le_add_two`: the same conclusion at
  the sharp regularity `finrank ℝ E - finrank ℝ F + 1`, when `finrank ℝ E ≤ finrank ℝ F + 2`.
* `TauCeti.addHaar_image_eq_zero_of_iteratedFDeriv_ne_zero`: the image of an intermediate stratum
  `Σ_i \ Σ_{i+1}` is null at regularity `C^{i+1}`, when `finrank ℝ E ≤ (i + 1) * finrank ℝ F`.
* `TauCeti.setOf_not_surjective_fderiv_eq_setOf_fderiv_eq_zero_of_finrank_eq_one`: for a
  one-dimensional target, the critical locus is exactly the vanishing-derivative locus.

## References

The stratification is the proof of Sard's theorem in J. Milnor, *Topology from the Differentiable
Viewpoint*, Section 3, and M. Hirsch, *Differential Topology*, Chapter 3.
-/

public section

open Function MeasureTheory MeasureTheory.Measure Module Set

open scoped ContDiff Topology

namespace TauCeti

universe u

section Sard

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F] [Nontrivial F] (ν : Measure F) [IsAddHaarMeasure ν]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {f : E → F} {s : Set E} {k : ℕ}

/-- A finite smoothness exponent is not `∞`, the side condition of `ContDiffAt.contDiffOn`. -/
private theorem natCast_ne_infty (m : ℕ) : (m : ℕ∞ω) ≠ ∞ := by simp

omit [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F] [Nontrivial F]
  [FiniteDimensional ℝ E] in
/-- The vanishing-derivative locus is covered by the flat stratum and the strata where
vanishing stops at a finite order: at a point of the `i`th of these, the derivatives of order
`1 ≤ j ≤ i` vanish and the derivative of order `i + 1` does not. -/
private theorem subset_flatStratum_union_iUnion (f : E → F) (s : Set E) (N : ℕ)
    (hs : ∀ x ∈ s, fderiv ℝ f x = 0) :
    s ⊆ {x ∈ s | ∀ i, 1 ≤ i → i ≤ N → iteratedFDeriv ℝ i f x = 0} ∪
      ⋃ i ∈ Set.Ico 1 N, {x ∈ s | (∀ j, 1 ≤ j → j ≤ i → iteratedFDeriv ℝ j f x = 0) ∧
        iteratedFDeriv ℝ (i + 1) f x ≠ 0} := by
  classical
  intro x hx
  by_cases hflat : ∀ i, 1 ≤ i → i ≤ N → iteratedFDeriv ℝ i f x = 0
  · exact Or.inl ⟨hx, hflat⟩
  refine Or.inr ?_
  push Not at hflat
  obtain ⟨i, hi1, hiN, hine⟩ := hflat
  have h1 : iteratedFDeriv ℝ 1 f x = 0 := by
    rw [← norm_eq_zero, norm_iteratedFDeriv_one, hs x hx, norm_zero]
  let p : ℕ → Prop := fun j ↦ iteratedFDeriv ℝ (j + 1) f x ≠ 0
  have hp : ∃ j, p j := ⟨i - 1, by
    change iteratedFDeriv ℝ (i - 1 + 1) f x ≠ 0
    rwa [Nat.sub_add_cancel hi1]⟩
  have hjpos : 0 < Nat.find hp := (Nat.find_pos hp).2 (by simpa [p] using h1)
  have hjzero : ∀ j, 1 ≤ j → j ≤ Nat.find hp → iteratedFDeriv ℝ j f x = 0 := by
    intro j hj1 hj
    have hmin := Nat.find_min hp (by omega : j - 1 < Nat.find hp)
    simp only [p, not_ne_iff] at hmin
    rwa [Nat.sub_add_cancel hj1] at hmin
  have hjN : Nat.find hp < N := by
    have hlast : p (i - 1) := by
      change iteratedFDeriv ℝ (i - 1 + 1) f x ≠ 0
      rwa [Nat.sub_add_cancel hi1]
    have hji : Nat.find hp ≤ i - 1 := Nat.find_le (h := hp) hlast
    omega
  exact mem_biUnion ⟨hjpos, hjN⟩ ⟨hx, hjzero, Nat.find_spec hp⟩

omit [FiniteDimensional ℝ F] [BorelSpace F] [Nontrivial F] [ν.IsAddHaarMeasure] in
/-- **Local nullity near a point of an intermediate stratum.** Let `f` be `C^{r+i}` at `a`, with
`1 ≤ i` and `1 ≤ r`, let its derivatives of order `i` vanish at `a` and those of order `i + 1`
not, and let `f` be `C^r` with vanishing derivative along `s`. If the images of such sets in the
kernel of any linear functional on `E` are null, the image under `f` of a neighbourhood of `a` in
the stratum `Σ_i \ Σ_{i+1}` is null. -/
private theorem exists_nhdsWithin_stratum_image_null (r i : ℕ) (hr : 1 ≤ r) (hi : 1 ≤ i) {a : E}
    (hfa : ContDiffAt ℝ ((r : ℕ∞ω) + i) f a) (hai : iteratedFDeriv ℝ i f a = 0)
    (hai1 : iteratedFDeriv ℝ (i + 1) f a ≠ 0) (hf : ∀ x ∈ s, ContDiffAt ℝ r f x)
    (hs : ∀ x ∈ s, fderiv ℝ f x = 0)
    (ih : ∀ g' : E →L[ℝ] ℝ, finrank ℝ ↥g'.ker + 1 = finrank ℝ E → ∀ (f' : ↥g'.ker → F)
      (s' : Set ↥g'.ker), (∀ x ∈ s', ContDiffAt ℝ r f' x) → (∀ x ∈ s', fderiv ℝ f' x = 0) →
        ν (f' '' s') = 0) :
    ∃ t ∈ 𝓝[{x ∈ s | (∀ j, 1 ≤ j → j ≤ i → iteratedFDeriv ℝ j f x = 0) ∧
      iteratedFDeriv ℝ (i + 1) f x ≠ 0}] a, ν (f '' t) = 0 := by
  obtain ⟨g, g', θ, -, -, -, -, -, hθ, -, hcover, hrank⟩ :=
    exists_parametrization_iteratedFDeriv_eq_zero hfa
      (by exact_mod_cast (by omega : r ≠ 0)) hai hai1
  obtain ⟨w, hw, hθw⟩ := hθ.contDiffOn (m := (r : ℕ∞ω)) le_rfl
    fun h ↦ absurd h (natCast_ne_infty _)
  -- Every point of the stratum close to `a` is `θ z` for some `z` where `θ` is `C^r`.
  refine ⟨_ ∩ {x | iteratedFDeriv ℝ i f x = 0 → x ∈ θ '' interior w},
    inter_mem_nhdsWithin _ (hcover _ (isOpen_interior.mem_nhds (mem_interior_iff_mem_nhds.2 hw))),
    ?_⟩
  have hθz : ∀ z ∈ interior w, ContDiffAt ℝ (r : ℕ∞ω) θ z := fun z hz ↦
    (hθw.mono interior_subset).contDiffAt (isOpen_interior.mem_nhds hz)
  refine measure_mono_null (fun y hy ↦ ?_)
    (ih g' hrank (f ∘ θ) (interior w ∩ θ ⁻¹' s) ?_ ?_)
  · obtain ⟨x, ⟨⟨hxs, hxi, -⟩, hxV⟩, rfl⟩ := hy
    obtain ⟨z, hz, rfl⟩ := hxV (hxi i hi le_rfl)
    exact ⟨z, ⟨hz, hxs⟩, rfl⟩
  · rintro z ⟨hzw, hzs⟩
    exact (hf (θ z) hzs).comp z (hθz z hzw)
  · rintro z ⟨hzw, hzs⟩
    have hone : (1 : ℕ∞ω) ≤ (r : ℕ∞ω) := mod_cast hr
    have hfz : DifferentiableAt ℝ f (θ z) := ((hf (θ z) hzs).of_le hone).differentiableAt_one
    rw [fderiv_comp z hfz ((hθz z hzw).of_le hone).differentiableAt_one, hs (θ z) hzs,
      ContinuousLinearMap.zero_comp]

/-- The induction behind `TauCeti.addHaar_image_eq_zero_of_fderiv_eq_zero`, on the dimension `n`
of the source. The source is quantified inside the statement because the induction step replaces
it by the kernel of a linear functional, a space of dimension one less. -/
private theorem addHaar_image_eq_zero_of_fderiv_eq_zero_aux (n : ℕ) :
    ∀ (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E],
      finrank ℝ E ≤ n → ∀ (k : ℕ), n * n + 1 ≤ k → ∀ (f : E → F) (s : Set E),
        (∀ x ∈ s, ContDiffAt ℝ k f x) → (∀ x ∈ s, fderiv ℝ f x = 0) → ν (f '' s) = 0 := by
  induction n with
  | zero =>
    intro E _ _ _ hE k _ f s _ _
    have : Subsingleton E := Module.finrank_zero_iff.mp (Nat.le_zero.mp hE)
    exact (Set.Subsingleton.image (fun x _ y _ ↦ Subsingleton.elim x y) f).measure_zero ν
  | succ n ih =>
    intro E _ _ _ hE k hk f s hf hs
    have hF : 0 < finrank ℝ F := finrank_pos
    have hk' : n * n + n + 2 ≤ k := by nlinarith
    have hkK : n + 2 ≤ k := by omega
    -- Split `s` into the innermost stratum, where the derivatives of order `1 ≤ i ≤ n + 1` all
    -- vanish, and the strata where the vanishing stops at some order `i < n + 1`.
    have hsub := subset_flatStratum_union_iUnion f s (n + 1) hs
    refine measure_mono_null (image_mono hsub) ?_
    rw [image_union, image_iUnion₂]
    refine measure_union_null ?_ ((measure_biUnion_null_iff (Set.to_countable _)).2 fun i hi ↦ ?_)
    · -- The innermost stratum: enough derivatives vanish for the flat-stratum estimate.
      refine measure_image_null_of_locally_null (HereditarilyLindelofSpace.isLindelof _)
        fun a ha ↦ ?_
      obtain ⟨u, hu, hfu⟩ := (hf a ha.1).contDiffOn (m := ((n + 1 + 1 : ℕ) : ℕ∞ω))
        (mod_cast hkK) fun h ↦ absurd h (natCast_ne_infty _)
      have humem : interior u ∈ 𝓝 a := isOpen_interior.mem_nhds (mem_interior_iff_mem_nhds.2 hu)
      refine ⟨_ ∩ interior u, inter_mem_nhdsWithin _ humem, ?_⟩
      refine addHaar_image_eq_zero_of_iteratedFDeriv_eq_zero (k := n + 1) ν isOpen_interior
        (hfu.mono interior_subset) inter_subset_right (fun x hx ↦ hx.1.2) ?_
      calc finrank ℝ E ≤ n + 1 := hE
        _ < n + 2 := by omega
        _ ≤ (n + 1 + 1) * finrank ℝ F := Nat.le_mul_of_pos_right _ hF
    · -- An intermediate stratum: descend to the kernel of a linear functional.
      refine measure_image_null_of_locally_null (HereditarilyLindelofSpace.isLindelof _)
        fun a ha ↦ ?_
      obtain ⟨has, hai, hai1⟩ := ha
      refine exists_nhdsWithin_stratum_image_null ν (n * n + 1) i (by omega) hi.1
        ((hf a has).of_le (mod_cast show n * n + 1 + i ≤ k by have := hi.2; omega))
        (hai i hi.1 le_rfl) hai1
        (fun x hx ↦ (hf x hx).of_le (mod_cast show n * n + 1 ≤ k by omega)) hs
        fun g' hg' ↦ ih ↥g'.ker (by omega) (n * n + 1) le_rfl

/-- **Sard's theorem on the locus where the derivative vanishes.** Let `f` be a map between
finite-dimensional real normed spaces with nontrivial target, and let `s` be a set at each point
of which `f` is `C^n` and the Fréchet derivative of `f` vanishes. If
`((finrank ℝ E * finrank ℝ E + 1 : ℕ) : ℕ∞ω) ≤ n`, then `f '' s` has additive Haar measure zero.

No relation between the two dimensions is required, beyond a nontrivial (positive-dimensional)
target: the vanishing of the derivative, rather than a dimension count, is what the higher
derivatives are used against. The smoothness bound is sufficient, not the sharp exponent of the
Morse--Sard theorem. -/
theorem addHaar_image_eq_zero_of_fderiv_eq_zero {n : ℕ∞ω}
    (hk : ((finrank ℝ E * finrank ℝ E + 1 : ℕ) : ℕ∞ω) ≤ n)
    (hf : ∀ x ∈ s, ContDiffAt ℝ n f x) (hs : ∀ x ∈ s, fderiv ℝ f x = 0) : ν (f '' s) = 0 :=
  addHaar_image_eq_zero_of_fderiv_eq_zero_aux ν (finrank ℝ E) E le_rfl
    (finrank ℝ E * finrank ℝ E + 1) le_rfl f s (fun x hx ↦ (hf x hx).of_le hk) hs

/-- The image under a sufficiently smooth map with nontrivial target of the whole locus where its
Fréchet derivative vanishes has additive Haar measure zero, with no relation required between the
two finite dimensions. -/
theorem ContDiff.addHaar_image_vanishingFDeriv_eq_zero {n : ℕ∞ω} (hf : ContDiff ℝ n f)
    (hk : ((finrank ℝ E * finrank ℝ E + 1 : ℕ) : ℕ∞ω) ≤ n) :
    ν (f '' {x | fderiv ℝ f x = 0}) = 0 :=
  addHaar_image_eq_zero_of_fderiv_eq_zero ν hk (fun _ _ ↦ hf.contDiffAt) fun _ hx ↦ hx

/-- The complement of the image of the locus where the derivative of a sufficiently smooth map
with nontrivial target vanishes is dense. -/
theorem ContDiff.dense_compl_image_vanishingFDeriv {n : ℕ∞ω} (hf : ContDiff ℝ n f)
    (hk : ((finrank ℝ E * finrank ℝ E + 1 : ℕ) : ℕ∞ω) ≤ n) :
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

/-- The induction behind `TauCeti.addHaar_image_eq_zero_of_fderiv_eq_zero_of_finrank_le_add_two`,
on the dimension `m` of the source, at the sharp regularity `finrank ℝ E - finrank ℝ F + 1`. -/
private theorem addHaar_image_eq_zero_of_fderiv_eq_zero_of_finrank_le_add_two_aux (m : ℕ) :
    ∀ (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E],
      finrank ℝ E ≤ m → finrank ℝ E ≤ finrank ℝ F + 2 →
      ∀ (k : ℕ), finrank ℝ E - finrank ℝ F + 1 ≤ k → ∀ (f : E → F) (s : Set E),
        (∀ x ∈ s, ContDiffAt ℝ k f x) → (∀ x ∈ s, fderiv ℝ f x = 0) → ν (f '' s) = 0 := by
  induction m with
  | zero =>
    intro E _ _ _ hE _ k _ f s _ _
    have : Subsingleton E := Module.finrank_zero_iff.mp (Nat.le_zero.mp hE)
    exact (Set.Subsingleton.image (fun x _ y _ ↦ Subsingleton.elim x y) f).measure_zero ν
  | succ m ih =>
    intro E _ _ _ hEm hcodim k hk f s hf hs
    have hF : 0 < finrank ℝ F := finrank_pos
    have hdiff : ∀ x ∈ s, DifferentiableAt ℝ f x := fun x hx ↦
      ((hf x hx).of_le (mod_cast show 1 ≤ k by omega)).differentiableAt_one
    rcases le_or_gt (finrank ℝ E) (finrank ℝ F) with hEF | hEF
    · exact addHaar_image_eq_zero_of_finrank_le_finrank ν hEF hdiff hs
    -- A larger source: stratify `s` down to the sharp depth `N`.
    set N := finrank ℝ E - finrank ℝ F + 1 with hNdef
    have hsub := subset_flatStratum_union_iUnion f s N hs
    refine measure_mono_null (image_mono hsub) ?_
    rw [image_union, image_iUnion₂]
    refine measure_union_null ?_ ((measure_biUnion_null_iff (Set.to_countable _)).2 fun i hi ↦ ?_)
    · -- The innermost stratum: the sharp flat-stratum estimate.
      refine measure_image_null_of_locally_null (HereditarilyLindelofSpace.isLindelof _)
        fun a ha ↦ ?_
      obtain ⟨u, hu, hfu⟩ := ((hf a ha.1).of_le (mod_cast hk)).contDiffOn
        (m := ((N : ℕ) : ℕ∞ω)) le_rfl fun h ↦ absurd h (natCast_ne_infty _)
      refine ⟨_ ∩ interior u, inter_mem_nhdsWithin _ (interior_mem_nhds.2 hu), ?_⟩
      refine addHaar_image_eq_zero_of_iteratedFDeriv_eq_zero_of_finrank_le_mul ν isOpen_interior
        (hfu.mono interior_subset) inter_subset_right (fun x hx ↦ hx.1.2) ?_
      have : finrank ℝ E - finrank ℝ F + finrank ℝ F = finrank ℝ E := by omega
      nlinarith
    obtain ⟨hi1, hiN⟩ := hi
    rcases hi1.eq_or_lt with rfl | hi2
    · -- The stratum `Σ_1 \ Σ_2`: descend to a hypersurface, losing exactly one derivative.
      refine measure_image_null_of_locally_null (HereditarilyLindelofSpace.isLindelof _)
        fun a ha ↦ ?_
      obtain ⟨has, hai, hai1⟩ := ha
      refine exists_nhdsWithin_stratum_image_null ν (N - 1) 1 (by omega) le_rfl
        ((hf a has).of_le (mod_cast show N - 1 + 1 ≤ k by omega)) (hai 1 le_rfl le_rfl) hai1
        (fun x hx ↦ (hf x hx).of_le (mod_cast show N - 1 ≤ k by omega)) hs
        fun g' hg' ↦ ih ↥g'.ker (by omega) (by omega) (N - 1) (by omega)
    · -- The strata `Σ_i \ Σ_{i+1}` with `i ≥ 2` have small Hausdorff dimension.
      refine addHaar_image_eq_zero_of_iteratedFDeriv_ne_zero ν hi1
        (fun x hx ↦ (hf x hx.1).of_le (mod_cast show i + 1 ≤ k by omega)) (fun x hx ↦ hx.2) ?_
      nlinarith

/-- **Sard's theorem on the locus where the derivative vanishes, at the sharp regularity, in
codimension at most two.** Let `f` be a map between finite-dimensional real normed spaces with
nontrivial target and `finrank ℝ E ≤ finrank ℝ F + 2`, and let `s` be a set at each point of
which `f` is `C^n` and the Fréchet derivative of `f` vanishes. If
`finrank ℝ E - finrank ℝ F < n`, then `f '' s` has additive Haar measure zero. -/
theorem addHaar_image_eq_zero_of_fderiv_eq_zero_of_finrank_le_add_two {n : ℕ∞ω}
    (hcodim : finrank ℝ E ≤ finrank ℝ F + 2)
    (hk : ((finrank ℝ E - finrank ℝ F + 1 : ℕ) : ℕ∞ω) ≤ n)
    (hf : ∀ x ∈ s, ContDiffAt ℝ n f x) (hs : ∀ x ∈ s, fderiv ℝ f x = 0) : ν (f '' s) = 0 :=
  addHaar_image_eq_zero_of_fderiv_eq_zero_of_finrank_le_add_two_aux ν (finrank ℝ E) E le_rfl
    hcodim _ le_rfl f s (fun x hx ↦ (hf x hx).of_le hk) hs

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
