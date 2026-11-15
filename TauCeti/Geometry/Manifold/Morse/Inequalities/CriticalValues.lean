/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Sublevel
public import TauCeti.Geometry.Manifold.Morse.Deformation.Homology
import Mathlib.Order.SuccPred.IntervalSucc

/-!
# The Morse inequalities of a function with finitely many critical values

Let `f` be a smooth function on a compact boundaryless finite-dimensional manifold `M` with
finitely many critical values, and let `ε > 0` be smaller than the distance between any two
distinct critical values. The critical points of `f` may be degenerate and need not be isolated.
Each critical value `c` contributes the relative singular homology

`Hᵢ({f ≤ c + ε}, {f ≤ c - ε}; V)`

of its window, which by the deformation across bands without critical points
(`TauCeti.singularHomologySublevelPairIsoOfCriticalValue`) does not depend on `ε`. Write
`bᵢ = dim Hᵢ(M; V)` and `cᵢ` for the sum over the critical values of the dimensions of these
contributions in degree `i`. Then `b` and `c` satisfy the Morse inequalities (Bott, *Nondegenerate
critical manifolds*):

* if the contributions are finite-dimensional in degree `n`, so is `Hₙ(M; V)`, and `bₙ ≤ cₙ`
  (`TauCeti.finite_singularHomology_of_finite_image_criticalPoints` and
  `TauCeti.finrank_singularHomology_le_of_finite_image_criticalPoints`);
* if they are finite-dimensional in degrees `≤ n`, then `bₙ - bₙ₋₁ + ⋯ ± b₀ ≤ cₙ - cₙ₋₁ + ⋯ ± c₀`
  (`TauCeti.sum_range_neg_one_pow_mul_finrank_singularHomology_le_of_finite_image_criticalPoints`);
* if moreover they vanish in degree `n + 1`, then `∑ᵢ₌₀ⁿ (-1)ⁱ bᵢ = ∑ᵢ₌₀ⁿ (-1)ⁱ cᵢ` and
  `∑ᵢ₌₀ⁿ cᵢ tⁱ = ∑ᵢ₌₀ⁿ bᵢ tⁱ + (1 + t) Q(t)` for a polynomial `Q` with natural number
  coefficients
  (`TauCeti.sum_range_neg_one_pow_mul_finrank_singularHomology_eq_of_finite_image_criticalPoints`
  and
  `TauCeti.exists_sum_range_monomial_eq_add_mul_of_finite_image_criticalPoints`);
* if they are finite-dimensional in every degree and of any two consecutive `cᵢ` one vanishes, then
  `bₙ = cₙ` for every `n`
  (`TauCeti.finrank_singularHomology_eq_of_finite_image_criticalPoints`).

For a Morse function the contribution of `c` is free on the critical points of the level `c`
(`TauCeti.IsMorse.nonempty_singularHomology_sublevelPair_iso_sigma`), and these statements
specialize to the Morse inequalities of a compact manifold in
`TauCeti.Geometry.Manifold.Morse.Inequalities`. For a Morse–Bott function
(`TauCeti.IsMorseBottFamily`, which has finitely many critical values on a compact manifold by
`TauCeti.IsMorseBottFamily.finite_image_criticalPoints`) the contribution of `c` is the relative
homology of the negative disc bundles of the critical submanifolds on the level `c`, by Bott's
attachment theorem; with that identification these statements become the Morse–Bott inequalities.

The proof cuts `M` at regular values into bands each containing at most one critical value
(`TauCeti.exists_isCriticalBandCut_of_finite_image_criticalPoints`). A band without critical
values has no relative homology (`TauCeti.isZero_singularHomology_sublevelPair_of_mfderiv_ne_zero`),
and a band around the critical value `c` has the relative homology of the window of `c`
(`TauCeti.singularHomologySublevelPairIsoOfCriticalValue`). The statements are then those of the
filtration of `M` by the sublevels at the cut values
(`TauCeti.AlgebraicTopology.Singular.FilteredSpace.Finrank`).

## References

* R. Bott, *Nondegenerate critical manifolds*, Annals of Mathematics 60 (1954), 248–261.
* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  Section 5.
-/

public section

noncomputable section

open CategoryTheory Limits Module Set
open Polynomial (monomial)
open scoped ContDiff Manifold Polynomial

universe u

namespace TauCeti

variable {E H : Type*} {M : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] {f : M → ℝ} {ε : ℝ}

/-- If `c` is a critical value lying in the band `[a q, a (q + 1)]` of a critical-band cut, then it
lies strictly inside the band and is the only critical value there. -/
private lemma IsCriticalBandCut.mem_Ioo_and_forall_eq {a : ℤ → ℝ} (ha : IsCriticalBandCut I f a)
    {c : ℝ} (hc : c ∈ f '' criticalPoints I f) {q : ℤ} (hcq : c ∈ Icc (a q) (a (q + 1))) :
    c ∈ Ioo (a q) (a (q + 1)) ∧
      ∀ x ∈ criticalPoints I f, f x ∈ Icc (a q) (a (q + 1)) → f x = c := by
  obtain ⟨c', hc', hall⟩ := (ha.isCriticalBand q).exists_mem_Ioo_forall_eq
  obtain ⟨x, hx, rfl⟩ := hc
  rw [hall x hx hcq]
  exact ⟨hc', hall⟩

/-- A value strictly inside two bands of a critical-band cut determines the band. -/
private lemma IsCriticalBandCut.eq_of_mem_Ioo {a : ℤ → ℝ} (ha : IsCriticalBandCut I f a) {c : ℝ}
    {q q' : ℤ} (hq : c ∈ Ioo (a q) (a (q + 1))) (hq' : c ∈ Ioo (a q') (a (q' + 1))) : q = q' := by
  by_contra hne
  have h := ha.monotone.pairwise_disjoint_on_Ioo_succ hne
  simp only [Function.onFun, Order.succ_eq_add_one] at h
  exact disjoint_left.1 h hq hq'

/-- The window `[c - ε, c + ε]` of a critical value `c`, for `ε` smaller than the distance between
any two distinct critical values, contains no other critical value. -/
private lemma eq_of_mem_Icc_sub_add
    (hsep : ∀ c ∈ f '' criticalPoints I f, ∀ c' ∈ f '' criticalPoints I f, c ≠ c' → ε < |c - c'|)
    {c : ℝ} (hc : c ∈ f '' criticalPoints I f) :
    ∀ x ∈ criticalPoints I f, f x ∈ Icc (c - ε) (c + ε) → f x = c := by
  intro x hx hxc
  by_contra hne
  have := hsep _ (mem_image_of_mem f hx) _ hc hne
  rw [lt_abs] at this
  rcases this with h | h <;> linarith [hxc.1, hxc.2]

variable [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M] [T2Space M] [CompactSpace M]
  {k : Type*} [DivisionRing k] (V : ModuleCat.{u} k)
  (hf : ContMDiff I 𝓘(ℝ) ∞ f) (hfin : (f '' criticalPoints I f).Finite) (hε : 0 < ε)
  (hsep : ∀ c ∈ f '' criticalPoints I f, ∀ c' ∈ f '' criticalPoints I f, c ≠ c' → ε < |c - c'|)

include hf hfin hsep in
/-- **Matching the bands of a cut with the critical values.** There is a cut `a q₀ < f ≤ a q₁` of
`M` by sublevels and an injective assignment `j` of a band `q₀ ≤ j c < q₁` to each critical value
`c`, such that the band of index `j c` has the relative homology of the window of `c`, and every
other band has no relative homology. -/
private lemma exists_cut_matching :
    ∃ (a : ℤ → ℝ) (ha : Monotone a) (q₀ q₁ : ℤ) (j : ℝ → ℤ), q₀ ≤ q₁ ∧
      (∀ x, a q₀ < f x) ∧ (∀ x, f x ≤ a q₁) ∧
      (∀ c ∈ f '' criticalPoints I f, j c ∈ Finset.Ico q₀ q₁) ∧ InjOn j (f '' criticalPoints I f) ∧
      (∀ c ∈ f '' criticalPoints I f, ∀ n,
        Nonempty ((sublevelPair f (ha (lt_add_one (j c)).le)).singularHomology V n ≅
          (sublevelPair f (a := c - ε) (b := c + ε) (by linarith)).singularHomology V n)) ∧
      ∀ q ∉ j '' (f '' criticalPoints I f), ∀ n,
        IsZero ((sublevelPair f (ha (lt_add_one q).le)).singularHomology V n) := by
  have hfc := hf.continuous
  obtain ⟨a, hcut, ⟨q₀, h₀⟩, ⟨q₁, h₁⟩⟩ :=
    exists_isCriticalBandCut_of_finite_image_criticalPoints (I := I) hfc hfin
  have ha := hcut.monotone
  set C := f '' criticalPoints I f
  -- Make the cut end above its start.
  have h₁' (x : M) : f x ≤ a (max q₀ q₁) := (h₁ x).trans (ha (le_max_right q₀ q₁))
  -- Each critical value `c` lies in the band of index `j c`.
  have hj (c : ℝ) : ∃ q, c ∈ C → q ∈ Finset.Ico q₀ (max q₀ q₁) ∧ c ∈ Icc (a q) (a (q + 1)) := by
    by_cases hc : c ∈ C
    · obtain ⟨x, -, rfl⟩ := hc
      have hx : f x ∈ ⋃ q ∈ Ico q₀ (max q₀ q₁), Ioc (a q) (a (Order.succ q)) := by
        rw [ha.biUnion_Ico_Ioc_map_succ]
        exact ⟨h₀ x, h₁' x⟩
      simp only [mem_iUnion, Order.succ_eq_add_one] at hx
      obtain ⟨q, hq, hxq⟩ := hx
      exact ⟨q, fun _ ↦ ⟨Finset.mem_Ico.2 hq, Ioc_subset_Icc_self hxq⟩⟩
    · exact ⟨0, fun h ↦ absurd h hc⟩
  choose j hj using hj
  have hjC {c : ℝ} (hc : c ∈ C) := hcut.mem_Ioo_and_forall_eq hc (hj c hc).2
  refine ⟨a, ha, q₀, max q₀ q₁, j, le_max_left _ _, h₀, h₁', fun c hc ↦ (hj c hc).1,
    fun c hc c' hc' h ↦ ?_, fun c hc n ↦ ?_, fun q hq n ↦ ?_⟩
  · obtain ⟨x, hx, rfl⟩ := hc
    exact (hjC hc').2 x hx (h ▸ (hj _ ⟨x, hx, rfl⟩).2)
  · -- The band of index `j c` and the window of `c` both contain only the critical value `c`.
    exact ⟨singularHomologySublevelPairIsoOfCriticalValue hf (hjC hc).1.1 (hjC hc).1.2
      (sub_lt_self c hε) (lt_add_of_pos_right c hε) (isClosed_Icc.preimage hfc).isCompact
      (isClosed_Icc.preimage hfc).isCompact (hjC hc).2 (eq_of_mem_Icc_sub_add hsep hc) V n⟩
  · -- A band whose index is not of the form `j c` contains no critical point.
    refine isZero_singularHomology_sublevelPair_of_mfderiv_ne_zero hf (ha (lt_add_one q).le)
      (isClosed_Icc.preimage hfc).isCompact (fun x h₁ h₂ hx ↦ ?_) V n
    have hc : f x ∈ C := mem_image_of_mem f (mem_criticalPoints_iff_mfderiv_eq_zero.2 hx)
    exact hq ⟨f x, hc, hcut.eq_of_mem_Ioo (hjC hc).1 (hcut.mem_Ioo_and_forall_eq hc ⟨h₁, h₂⟩).1⟩

include hf hsep in
/-- **The critical-band filtration, read through the windows of the critical values.** There is a
cut `a q₀ < f ≤ a q₁` of `M` by sublevels such that finiteness and vanishing of relative homology
pass from the windows of the critical values to the steps `({f ≤ a (q + 1)}, {f ≤ a q})`, and in
every degree the dimensions of the steps add up to those of the windows. -/
private lemma exists_cut :
    ∃ (a : ℤ → ℝ) (ha : Monotone a) (q₀ q₁ : ℤ), q₀ ≤ q₁ ∧
      (∀ x, a q₀ < f x) ∧ (∀ x, f x ≤ a q₁) ∧
      (∀ n, (∀ c ∈ f '' criticalPoints I f, Module.Finite k
          ((sublevelPair f (a := c - ε) (b := c + ε) (by linarith)).singularHomology V n :
            ModuleCat k)) →
        ∀ q ∈ Finset.Ico q₀ q₁, Module.Finite k
          ((sublevelPair f (ha (lt_add_one q).le)).singularHomology V n : ModuleCat k)) ∧
      (∀ n, (∀ c ∈ f '' criticalPoints I f,
          IsZero ((sublevelPair f (a := c - ε) (b := c + ε) (by linarith)).singularHomology V n)) →
        ∀ q ∈ Finset.Ico q₀ q₁,
          IsZero ((sublevelPair f (ha (lt_add_one q).le)).singularHomology V n)) ∧
      ∀ n, ∑ q ∈ Finset.Ico q₀ q₁,
          finrank k ((sublevelPair f (ha (lt_add_one q).le)).singularHomology V n : ModuleCat k) =
        ∑ c ∈ hfin.toFinset, finrank k
          ((sublevelPair f (a := c - ε) (b := c + ε) (by linarith)).singularHomology V n :
            ModuleCat k) := by
  obtain ⟨a, ha, q₀, q₁, j, hq, h₀, h₁, hjI, hinj, hwin, hzero⟩ :=
    exists_cut_matching V hf hfin hε hsep
  refine ⟨a, ha, q₀, q₁, hq, h₀, h₁, fun n hV q _ ↦ ?_, fun n hV q _ ↦ ?_, fun n ↦ ?_⟩
  · by_cases hqC : q ∈ j '' (f '' criticalPoints I f)
    · obtain ⟨c, hc, rfl⟩ := hqC
      have := hV c hc
      exact Module.Finite.equiv (hwin c hc n).some.symm.toLinearEquiv
    · have := ModuleCat.isZero_iff_subsingleton.1 (hzero q hqC n)
      infer_instance
  · by_cases hqC : q ∈ j '' (f '' criticalPoints I f)
    · obtain ⟨c, hc, rfl⟩ := hqC
      exact (hV c hc).of_iso (hwin c hc n).some
    · exact hzero q hqC n
  · -- The sum over the bands is the sum over the bands of index `j c`, one for each `c`.
    classical
    have himage : hfin.toFinset.image j ⊆ Finset.Ico q₀ q₁ := fun q hq ↦ by
      obtain ⟨c, hc, rfl⟩ := Finset.mem_image.1 hq
      exact hjI c (hfin.mem_toFinset.1 hc)
    rw [← Finset.sum_subset himage fun q _ hq ↦ ?_, Finset.sum_image fun c hc c' hc' h ↦
      hinj (hfin.mem_toFinset.1 hc) (hfin.mem_toFinset.1 hc') h]
    · exact Finset.sum_congr rfl fun c hc ↦
        (hwin c (hfin.mem_toFinset.1 hc) n).some.toLinearEquiv.finrank_eq
    · have := ModuleCat.isZero_iff_subsingleton.1 (hzero q (fun ⟨c, hc, hcq⟩ ↦
        hq (Finset.mem_image.2 ⟨c, hfin.mem_toFinset.2 hc, hcq⟩)) n)
      exact finrank_zero_of_subsingleton

include hf hfin hsep

/-- **Finiteness of homology from the critical values.** Let `f` be a smooth function on a compact
manifold `M` with finitely many critical values, and `ε > 0` smaller than the distance between any
two distinct critical values. If the relative homology `Hₙ({f ≤ c + ε}, {f ≤ c - ε}; V)` of the
window of every critical value `c` is finite-dimensional, so is `Hₙ(M; V)`. -/
theorem finite_singularHomology_of_finite_image_criticalPoints (n : ℕ)
    (hV : ∀ c ∈ f '' criticalPoints I f, Module.Finite k
      ((sublevelPair f (a := c - ε) (b := c + ε) (by linarith)).singularHomology V n :
        ModuleCat k)) :
    Module.Finite k
      (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} k) n).obj V).obj
        (TopCat.of M)) := by
  obtain ⟨a, ha, q₀, q₁, hq, h₀, h₁, hfinite, -, -⟩ := exists_cut V hf hfin hε hsep
  have hX : Monotone fun q ↦ ({x | f x ≤ a q} : Set (TopCat.of M)) := (sublevel_mono f).comp ha
  have := hX.finite_singularHomology_ofInclusion_of_forall_mem_Ico V hq n (hfinite n hV)
  exact Module.Finite.equiv (singularHomologyIsoSublevelPair (ha hq) h₀ h₁ V n).symm.toLinearEquiv

/-- **The weak Morse inequalities of a function with finitely many critical values.** Let `f` be
a smooth function on a compact manifold `M` with finitely many critical values, and `ε > 0` smaller
than the distance between any two distinct critical values. If the relative homology of the window
`({f ≤ c + ε}, {f ≤ c - ε})` of every critical value `c` is finite-dimensional in degree `n`, then
`dim Hₙ(M; V)` is at most the sum over the critical values of the dimensions of these. -/
theorem finrank_singularHomology_le_of_finite_image_criticalPoints (n : ℕ)
    (hV : ∀ c ∈ f '' criticalPoints I f, Module.Finite k
      ((sublevelPair f (a := c - ε) (b := c + ε) (by linarith)).singularHomology V n :
        ModuleCat k)) :
    finrank k (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} k) n).obj V).obj
        (TopCat.of M)) ≤
      ∑ c ∈ hfin.toFinset, finrank k
        ((sublevelPair f (a := c - ε) (b := c + ε) (by linarith)).singularHomology V n :
          ModuleCat k) := by
  obtain ⟨a, ha, q₀, q₁, hq, h₀, h₁, hfinite, -, hsum⟩ := exists_cut V hf hfin hε hsep
  have hX : Monotone fun q ↦ ({x | f x ≤ a q} : Set (TopCat.of M)) := (sublevel_mono f).comp ha
  rw [← hsum, (singularHomologyIsoSublevelPair (ha hq) h₀ h₁ V n).toLinearEquiv.finrank_eq]
  exact hX.finrank_singularHomology_ofInclusion_le_sum V hq n (hfinite n hV)

/-- **The strong Morse inequalities of a function with finitely many critical values** (Bott). Let
`f` be a smooth function on a compact manifold `M` with finitely many critical values, and `ε > 0`
smaller than the distance between any two distinct critical values. Suppose the relative homology
of the window `({f ≤ c + ε}, {f ≤ c - ε})` of every critical value `c` is finite-dimensional in
degrees `≤ n`. Write `bᵢ = dim Hᵢ(M; V)` and `cᵢ` for the sum over the critical values of the
dimensions of these in degree `i`. Then `bₙ - bₙ₋₁ + ⋯ ± b₀ ≤ cₙ - cₙ₋₁ + ⋯ ± c₀`. -/
theorem sum_range_neg_one_pow_mul_finrank_singularHomology_le_of_finite_image_criticalPoints
    (n : ℕ) (hV : ∀ c ∈ f '' criticalPoints I f, ∀ i ≤ n, Module.Finite k
      ((sublevelPair f (a := c - ε) (b := c + ε) (by linarith)).singularHomology V i :
        ModuleCat k)) :
    ∑ i ∈ Finset.range (n + 1), (-1 : ℤ) ^ (n - i) *
        finrank k (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} k) i).obj V).obj
          (TopCat.of M)) ≤
      ∑ i ∈ Finset.range (n + 1), (-1 : ℤ) ^ (n - i) * ((∑ c ∈ hfin.toFinset, finrank k
        ((sublevelPair f (a := c - ε) (b := c + ε) (by linarith)).singularHomology V i :
          ModuleCat k) : ℕ) : ℤ) := by
  obtain ⟨a, ha, q₀, q₁, hq, h₀, h₁, hfinite, -, hsum⟩ := exists_cut V hf hfin hε hsep
  have hX : Monotone fun q ↦ ({x | f x ≤ a q} : Set (TopCat.of M)) := (sublevel_mono f).comp ha
  simp only [(singularHomologyIsoSublevelPair (ha hq) h₀ h₁ V _).toLinearEquiv.finrank_eq,
    ← hsum, Nat.cast_sum]
  exact hX.sum_range_neg_one_pow_mul_finrank_singularHomology_ofInclusion_le V hq n
    fun q hq i hi ↦ hfinite i (fun c hc ↦ hV c hc i hi) q hq

/-- **Euler's equality for a function with finitely many critical values.** Let `f` be a smooth
function on a compact manifold `M` with finitely many critical values, and `ε > 0` smaller than the
distance between any two distinct critical values. Suppose the relative homology of the window
`({f ≤ c + ε}, {f ≤ c - ε})` of every critical value `c` is finite-dimensional in degrees `≤ n` and
vanishes in degree `n + 1`. Write `bᵢ = dim Hᵢ(M; V)` and `cᵢ` for the sum over the critical values
of the dimensions of these in degree `i`. Then `∑ᵢ₌₀ⁿ (-1)ⁱ bᵢ = ∑ᵢ₌₀ⁿ (-1)ⁱ cᵢ`. -/
theorem sum_range_neg_one_pow_mul_finrank_singularHomology_eq_of_finite_image_criticalPoints
    {n : ℕ} (hV : ∀ c ∈ f '' criticalPoints I f, ∀ i ≤ n, Module.Finite k
      ((sublevelPair f (a := c - ε) (b := c + ε) (by linarith)).singularHomology V i :
        ModuleCat k))
    (hzero : ∀ c ∈ f '' criticalPoints I f,
      IsZero ((sublevelPair f (a := c - ε) (b := c + ε) (by linarith)).singularHomology V
        (n + 1))) :
    ∑ i ∈ Finset.range (n + 1), (-1 : ℤ) ^ i *
        finrank k (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} k) i).obj V).obj
          (TopCat.of M)) =
      ∑ i ∈ Finset.range (n + 1), (-1 : ℤ) ^ i * ((∑ c ∈ hfin.toFinset, finrank k
        ((sublevelPair f (a := c - ε) (b := c + ε) (by linarith)).singularHomology V i :
          ModuleCat k) : ℕ) : ℤ) := by
  obtain ⟨a, ha, q₀, q₁, hq, h₀, h₁, hfinite, hvanish, hsum⟩ := exists_cut V hf hfin hε hsep
  have hX : Monotone fun q ↦ ({x | f x ≤ a q} : Set (TopCat.of M)) := (sublevel_mono f).comp ha
  simp only [(singularHomologyIsoSublevelPair (ha hq) h₀ h₁ V _).toLinearEquiv.finrank_eq,
    ← hsum, Nat.cast_sum]
  exact hX.sum_range_neg_one_pow_mul_finrank_singularHomology_ofInclusion_eq V hq
    (fun q hq i hi ↦ hfinite i (fun c hc ↦ hV c hc i hi) q hq) (hvanish (n + 1) hzero)

/-- **The Morse polynomial identity of a function with finitely many critical values** (Bott). Let
`f` be a smooth function on a compact manifold `M` with finitely many critical values, and `ε > 0`
smaller than the distance between any two distinct critical values. Suppose the relative homology of
the window `({f ≤ c + ε}, {f ≤ c - ε})` of every critical value `c` is finite-dimensional in degrees
`≤ n` and vanishes in degree `n + 1`. Write `bᵢ = dim Hᵢ(M; V)` and `cᵢ` for the sum over the
critical values of the dimensions of these in degree `i`. Then
`∑ᵢ₌₀ⁿ cᵢ tⁱ = ∑ᵢ₌₀ⁿ bᵢ tⁱ + (1 + t) Q(t)` for a polynomial `Q` with natural number coefficients:
for `i < n` the coefficient of `tⁱ` is the gap `(cᵢ - cᵢ₋₁ + ⋯ ± c₀) - (bᵢ - bᵢ₋₁ + ⋯ ± b₀)` in the
`i`-th strong inequality, and for `i ≥ n` it is zero. -/
theorem exists_sum_range_monomial_eq_add_mul_of_finite_image_criticalPoints
    {n : ℕ} (hV : ∀ c ∈ f '' criticalPoints I f, ∀ i ≤ n, Module.Finite k
      ((sublevelPair f (a := c - ε) (b := c + ε) (by linarith)).singularHomology V i :
        ModuleCat k))
    (hzero : ∀ c ∈ f '' criticalPoints I f,
      IsZero ((sublevelPair f (a := c - ε) (b := c + ε) (by linarith)).singularHomology V
        (n + 1))) :
    ∃ Q : ℕ[X], ∑ i ∈ Finset.range (n + 1), monomial i (∑ c ∈ hfin.toFinset, finrank k
        ((sublevelPair f (a := c - ε) (b := c + ε) (by linarith)).singularHomology V i :
          ModuleCat k)) =
        ∑ i ∈ Finset.range (n + 1), monomial i
          (finrank k (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} k) i).obj V).obj
            (TopCat.of M))) + (1 + Polynomial.X) * Q ∧
      (∀ i < n, (Q.coeff i : ℤ) =
        ∑ j ∈ Finset.range (i + 1), (-1 : ℤ) ^ (i - j) * ∑ c ∈ hfin.toFinset, (finrank k
          ((sublevelPair f (a := c - ε) (b := c + ε) (by linarith)).singularHomology V j :
            ModuleCat k) : ℤ) -
        ∑ j ∈ Finset.range (i + 1), (-1 : ℤ) ^ (i - j) *
          finrank k (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} k) j).obj V).obj
            (TopCat.of M))) ∧
      ∀ i, n ≤ i → Q.coeff i = 0 := by
  obtain ⟨a, ha, q₀, q₁, hq, h₀, h₁, hfinite, hvanish, hsum⟩ := exists_cut V hf hfin hε hsep
  have hX : Monotone fun q ↦ ({x | f x ≤ a q} : Set (TopCat.of M)) := (sublevel_mono f).comp ha
  have hsum' (i : ℕ) := congrArg (Nat.cast (R := ℤ)) (hsum i)
  push_cast at hsum'
  simp only [(singularHomologyIsoSublevelPair (ha hq) h₀ h₁ V _).toLinearEquiv.finrank_eq,
    ← hsum, ← hsum']
  exact hX.exists_sum_range_monomial_sum_finrank_singularHomology_ofInclusion_eq_add_mul V hq
    (fun q hq i hi ↦ hfinite i (fun c hc ↦ hV c hc i hi) q hq) (hvanish (n + 1) hzero)

/-- **The lacunary principle for a function with finitely many critical values.** Let `f` be a
smooth function on a compact manifold `M` with finitely many critical values, and `ε > 0` smaller
than the distance between any two distinct critical values. Suppose the relative homology of the
window `({f ≤ c + ε}, {f ≤ c - ε})` of every critical value `c` is finite-dimensional in every
degree, and write `cᵢ` for the sum over the critical values of the dimensions of these in degree
`i`. If of any two consecutive `cᵢ` one vanishes, then `dim Hₙ(M; V) = cₙ` for every `n`. -/
theorem finrank_singularHomology_eq_of_finite_image_criticalPoints
    (hV : ∀ c ∈ f '' criticalPoints I f, ∀ i, Module.Finite k
      ((sublevelPair f (a := c - ε) (b := c + ε) (by linarith)).singularHomology V i :
        ModuleCat k))
    (hc : ∀ i, ∑ c ∈ hfin.toFinset, finrank k
        ((sublevelPair f (a := c - ε) (b := c + ε) (by linarith)).singularHomology V i :
          ModuleCat k) = 0 ∨
      ∑ c ∈ hfin.toFinset, finrank k
        ((sublevelPair f (a := c - ε) (b := c + ε) (by linarith)).singularHomology V (i + 1) :
          ModuleCat k) = 0) (n : ℕ) :
    finrank k (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} k) n).obj V).obj
        (TopCat.of M)) =
      ∑ c ∈ hfin.toFinset, finrank k
        ((sublevelPair f (a := c - ε) (b := c + ε) (by linarith)).singularHomology V n :
          ModuleCat k) := by
  obtain ⟨a, ha, q₀, q₁, hq, h₀, h₁, hfinite, -, hsum⟩ := exists_cut V hf hfin hε hsep
  have hX : Monotone fun q ↦ ({x | f x ≤ a q} : Set (TopCat.of M)) := (sublevel_mono f).comp ha
  rw [(singularHomologyIsoSublevelPair (ha hq) h₀ h₁ V n).toLinearEquiv.finrank_eq, ← hsum]
  simp only [← hsum] at hc
  exact hX.finrank_singularHomology_ofInclusion_eq_sum_of_eq_zero_or V hq
    (fun q hq i ↦ hfinite i (fun c hc ↦ hV c hc i) q hq) hc n

end TauCeti
