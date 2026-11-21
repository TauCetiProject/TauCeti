/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Amplitude.Comp
public import TauCeti.Analysis.Pseudodifferential.Amplitude.Expansion
public import TauCeti.Analysis.Pseudodifferential.Symbol.Classical
import TauCeti.Analysis.Normed.Operator.Basic

/-!
# Homogeneous amplitudes and the terms of their left symbols

A *homogeneous amplitude* of degree `m` is a homogeneous symbol `h((x, y), ξ)` whose position is a
pair of an output position `x` and an input position `y`, that is, an element of
`TauCeti.HomogeneousSymbol (ℝⁿ × ℝⁿ) ℝⁿ V W m`: it vanishes at `ξ = 0`, is smooth away from
`ξ = 0`, and is positively homogeneous of degree `m` in `ξ`. Homogeneous amplitudes are to
amplitudes what homogeneous symbols are to symbols: the terms of classical expansions.

The terms `leftTerm a k = ((-i)^k / k!) ∑_{|w| = k} (∂_y^w ∂_ξ^w a)(x, x, ξ)` of the expansion of
the left symbol of an amplitude `a` (`TauCeti.Amplitude.leftTerm`) only involve derivatives of `a`
at the diagonal `y = x`, so they make sense for homogeneous amplitudes too:
`TauCeti.HomogeneousSymbol.leftTerm h k` is homogeneous of degree `m - k`, defined by the same
recursion. If an amplitude `a` agrees with `h` at all large frequencies, locally uniformly in the
positions, then so do all of their terms
(`TauCeti.Amplitude.exists_coefficient_leftTerm_eq_of_forall_isCompact`); hence `leftTerm a k` is
the cut-off term `χ(ξ) (leftTerm h k)(x, ξ)` up to a smoothing symbol
(`TauCeti.Amplitude.isSmoothing_leftTerm_sub_cutoffSymbol_leftTerm`). This is what shows the left
symbol of an amplitude with a classical expansion to be a classical symbol.

The main example is `TauCeti.HomogeneousSymbol.compAmplitude`, the homogeneous amplitude
`g(x, y) • a(κ x, M(x, y) ξ)` of a homogeneous symbol `a` in moving frequency coordinates, the
homogeneous counterpart of the amplitude `TauCeti.Symbol.compAmplitude` that arises in changes of
coordinates. The amplitude of the cut-off term `χ(η) a(z, η)` agrees with it at all large
frequencies (`TauCeti.HomogeneousSymbol.exists_coefficient_compAmplitude_cutoffSymbol_eq`).

Consequently, for a classical symbol `a ∼ ∑ⱼ a_{m-j}` of order `m`, the left symbol of the
amplitude `g(x, y) • a(κ x, M(x, y) ξ)` is a classical symbol of order `m`
(`TauCeti.ClassicalSymbol.leftSymbolCompAmplitude`). Its term of degree `m - l` collects the terms
of degree `m - l` of the expansions of the homogeneous amplitudes
`g(x, y) • a_{m-j}(κ x, M(x, y) ξ)` (`TauCeti.ClassicalSymbol.compAmplitudeTerms`), and its
principal symbol is `g(x, x) • a_m(κ x, M(x, x) ξ)`
(`TauCeti.ClassicalSymbol.coefficient_principal_leftSymbolCompAmplitude`). This is the step that
makes changes of coordinates preserve classical symbols
(`TauCeti.ClassicalSymbol.exists_quantizeSchwartzValue_comp_eq`).

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, §18.1,
  Theorem 18.1.17 and its proof.
* M. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI* (2008), Lecture I, §8.
-/

public section

noncomputable section

open Filter Metric Set
open scoped ContDiff Topology

namespace TauCeti

variable {n : ℕ} {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W]
  [NormedSpace ℂ W]

/-! ### The terms of a homogeneous amplitude -/

namespace HomogeneousSymbol

/-- The term of degree `m - k` of the expansion of the left symbol of a homogeneous amplitude `a` of
degree `m`, `((-i)^k / k!) ∑_{|w| = k} (∂_y^w ∂_ξ^w a)((x, x), ξ)`. It is defined by the recursion
of `TauCeti.Amplitude.leftTerm`: `leftTerm a 0` is the restriction `a((x, x), ξ)` of `a` to the
diagonal and `leftTerm a (k + 1) = (-i / (k + 1)) ∑ⱼ leftTerm (∂_{y_j} ∂_{ξ_j} a) k`. -/
def leftTerm : {m : ℝ} →
    HomogeneousSymbol (CoordinateSpace n × CoordinateSpace n) (CoordinateSpace n) V W m →
    (k : ℕ) → HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W (m - k)
  | _, a, 0 => (a.compPosition (fun x ↦ (x, x)) (contDiff_id.prodMk contDiff_id)).castDegree
      (by simp)
  | _, a, k + 1 => (-Complex.I / (k + 1 : ℂ)) • ∑ j : Fin n,
      (leftTerm ((a.frequencyDeriv (EuclideanSpace.single j 1)).spatialDeriv
        (0, EuclideanSpace.single j 1)) k).castDegree (by push_cast; ring)

variable {m : ℝ}
  (a : HomogeneousSymbol (CoordinateSpace n × CoordinateSpace n) (CoordinateSpace n) V W m)

theorem leftTerm_zero :
    a.leftTerm 0 =
      (a.compPosition (fun x ↦ (x, x)) (contDiff_id.prodMk contDiff_id)).castDegree (by simp) :=
  (rfl)

theorem leftTerm_succ (k : ℕ) :
    a.leftTerm (k + 1) = (-Complex.I / (k + 1 : ℂ)) • ∑ j : Fin n,
      (((a.frequencyDeriv (EuclideanSpace.single j 1)).spatialDeriv
        (0, EuclideanSpace.single j 1)).leftTerm k).castDegree (by push_cast; ring) :=
  (rfl)

/-- The term of degree `m` is the restriction of `a` to the diagonal. -/
@[simp]
theorem coefficient_leftTerm_zero (x ξ : CoordinateSpace n) :
    (a.leftTerm 0).coefficient (x, ξ) = a.coefficient ((x, x), ξ) := by
  simp [leftTerm_zero]

theorem coefficient_leftTerm_succ (k : ℕ) (p : CoordinateSpace n × CoordinateSpace n) :
    (a.leftTerm (k + 1)).coefficient p = (-Complex.I / (k + 1 : ℂ)) • ∑ j : Fin n,
      (((a.frequencyDeriv (EuclideanSpace.single j 1)).spatialDeriv
        (0, EuclideanSpace.single j 1)).leftTerm k).coefficient p := by
  simp [leftTerm_succ]

end HomogeneousSymbol

/-! ### Amplitudes agreeing with a homogeneous amplitude at large frequencies -/

namespace Amplitude

variable {m m' : ℝ}

/-- An amplitude `a` agrees with a homogeneous amplitude `h` at large frequencies, locally
uniformly in the positions. -/
private def EqAtInfinity (a : Amplitude n V W m)
    (h : HomogeneousSymbol (CoordinateSpace n × CoordinateSpace n) (CoordinateSpace n) V W m') :
    Prop :=
  ∀ K : Set (CoordinateSpace n × CoordinateSpace n), IsCompact K → ∃ R, ∀ x y, (x, y) ∈ K →
    ∀ ξ, R ≤ ‖ξ‖ → a.coefficient (x, y, ξ) = h.coefficient ((x, y), ξ)

variable {a : Amplitude n V W m}
  {h : HomogeneousSymbol (CoordinateSpace n × CoordinateSpace n) (CoordinateSpace n) V W m'}

/-- If `a` and `h` agree at large frequencies, they agree on a neighbourhood of every point of
large frequency over a compact set of positions. -/
private theorem EqAtInfinity.exists_eventuallyEq (hah : EqAtInfinity a h)
    {K : Set (CoordinateSpace n × CoordinateSpace n)} (hK : IsCompact K) :
    ∃ R, 0 < R ∧ ∀ x y, (x, y) ∈ K → ∀ ξ, R ≤ ‖ξ‖ →
      a.coefficient =ᶠ[𝓝 (x, y, ξ)] fun p ↦ h.coefficient ((p.1, p.2.1), p.2.2) := by
  obtain ⟨R, hR⟩ := hah _ (hK.cthickening (r := 1))
  refine ⟨max R 0 + 1, by positivity, fun x y hxy ξ hξ ↦ ?_⟩
  have hU : (fun p : CoordinateSpace n × CoordinateSpace n × CoordinateSpace n ↦ (p.1, p.2.1)) ⁻¹'
      thickening 1 K ∩ {p | R < ‖p.2.2‖} ∈ 𝓝 (x, y, ξ) :=
    IsOpen.mem_nhds ((isOpen_thickening.preimage (continuous_fst.prodMk
      (continuous_fst.comp continuous_snd))).inter (isOpen_lt continuous_const
      (continuous_norm.comp (continuous_snd.comp continuous_snd))))
      ⟨self_subset_thickening one_pos K hxy, by
        simp only [Set.mem_ofPred_eq]
        linarith [le_max_left R 0]⟩
  filter_upwards [hU] with p hp
  exact hR p.1 p.2.1 (thickening_subset_cthickening 1 K hp.1) p.2.2 hp.2.le

/-- Where `a` agrees with `h` near a point of nonzero frequency, their derivatives agree. -/
private theorem fderiv_coefficient_eq_of_eventuallyEq
    {p : CoordinateSpace n × CoordinateSpace n × CoordinateSpace n}
    (hp : a.coefficient =ᶠ[𝓝 p] fun q ↦ h.coefficient ((q.1, q.2.1), q.2.2)) (hξ : p.2.2 ≠ 0)
    (d : CoordinateSpace n × CoordinateSpace n × CoordinateSpace n) :
    fderiv ℝ a.coefficient p d =
      fderiv ℝ h.coefficient ((p.1, p.2.1), p.2.2) ((d.1, d.2.1), d.2.2) := by
  let e := (ContinuousLinearEquiv.prodAssoc ℝ (CoordinateSpace n) (CoordinateSpace n)
    (CoordinateSpace n)).symm
  have hpe (q : CoordinateSpace n × CoordinateSpace n × CoordinateSpace n) :
      e q = ((q.1, q.2.1), q.2.2) :=
    ContinuousLinearEquiv.prodAssoc_symm_apply ℝ _ _ _ q.1 q.2.1 q.2.2
  have he : (fun q : CoordinateSpace n × CoordinateSpace n × CoordinateSpace n ↦
      h.coefficient ((q.1, q.2.1), q.2.2)) = h.coefficient ∘ e := by
    funext q
    rw [Function.comp_apply, hpe]
  rw [hp.fderiv_eq, he, fderiv_comp _ (h.differentiableAt_coefficient (p := e p) hξ)
    e.differentiableAt, e.fderiv, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    hpe, hpe]

private theorem EqAtInfinity.frequencyDeriv (hah : EqAtInfinity a h) (j : Fin n) :
    EqAtInfinity (frequencyDeriv j a) (h.frequencyDeriv (EuclideanSpace.single j 1)) := by
  intro K hK
  obtain ⟨R, hR0, hR⟩ := hah.exists_eventuallyEq hK
  refine ⟨R, fun x y hxy ξ hξ ↦ ?_⟩
  have hξ0 : ξ ≠ 0 := norm_pos_iff.1 (hR0.trans_le hξ)
  rw [coefficient_frequencyDeriv, fderiv_coefficient_eq_of_eventuallyEq (hR x y hxy ξ hξ) hξ0,
    HomogeneousSymbol.coefficient_frequencyDeriv_eq_fderiv _ _ hξ0, Prod.mk_zero_zero]

private theorem EqAtInfinity.spatialDerivSnd (hah : EqAtInfinity a h) (j : Fin n) :
    EqAtInfinity (spatialDerivSnd j a) (h.spatialDeriv (0, EuclideanSpace.single j 1)) := by
  intro K hK
  obtain ⟨R, hR0, hR⟩ := hah.exists_eventuallyEq hK
  refine ⟨R, fun x y hxy ξ hξ ↦ ?_⟩
  have hξ0 : ξ ≠ 0 := norm_pos_iff.1 (hR0.trans_le hξ)
  rw [coefficient_spatialDerivSnd, fderiv_coefficient_eq_of_eventuallyEq (hR x y hxy ξ hξ) hξ0,
    HomogeneousSymbol.coefficient_spatialDeriv_eq_fderiv]

/-- **Terms of an amplitude with a homogeneous leading part.** If an amplitude `a` agrees with a
homogeneous amplitude `h` at all large frequencies, locally uniformly in the positions, then every
term `leftTerm a k` of the expansion of the left symbol of `a` agrees with the homogeneous term
`leftTerm h k` at all large frequencies, locally uniformly in the position. -/
theorem exists_coefficient_leftTerm_eq_of_forall_isCompact (a : Amplitude n V W m)
    (h : HomogeneousSymbol (CoordinateSpace n × CoordinateSpace n) (CoordinateSpace n) V W m')
    (hah : ∀ K : Set (CoordinateSpace n × CoordinateSpace n), IsCompact K → ∃ R, ∀ x y,
      (x, y) ∈ K → ∀ ξ, R ≤ ‖ξ‖ → a.coefficient (x, y, ξ) = h.coefficient ((x, y), ξ))
    (k : ℕ) {K : Set (CoordinateSpace n)} (hK : IsCompact K) :
    ∃ R, ∀ x ∈ K, ∀ ξ, R ≤ ‖ξ‖ →
      (a.leftTerm k).coefficient (x, ξ) = (h.leftTerm k).coefficient (x, ξ) := by
  induction k generalizing m m' with
  | zero =>
    obtain ⟨R, hR⟩ := hah _ (hK.image (continuous_id.prodMk continuous_id))
    exact ⟨R, fun x hx ξ hξ ↦ by simpa using hR x x ⟨x, hx, rfl⟩ ξ hξ⟩
  | succ k ih =>
    choose R hR using fun j : Fin n ↦ ih (spatialDerivSnd j (frequencyDeriv j a))
      ((h.frequencyDeriv (EuclideanSpace.single j 1)).spatialDeriv
        (0, EuclideanSpace.single j 1))
      (EqAtInfinity.spatialDerivSnd (EqAtInfinity.frequencyDeriv hah j) j)
    refine ⟨∑ j, |R j|, fun x hx ξ hξ ↦ ?_⟩
    rw [coefficient_leftTerm_succ, HomogeneousSymbol.coefficient_leftTerm_succ]
    refine congrArg _ (Finset.sum_congr rfl fun j _ ↦ hR j x hx ξ ?_)
    exact (le_abs_self _).trans
      ((Finset.single_le_sum (fun i _ ↦ abs_nonneg (R i)) (Finset.mem_univ j)).trans hξ)

/-- If an amplitude `a` of order `m` agrees with a homogeneous amplitude `h` of degree `m` at all
large frequencies, locally uniformly in the positions, then each term `leftTerm a k` of the
expansion of the left symbol of `a` is the cut-off term `χ(ξ) (leftTerm h k)(x, ξ)` up to a
smoothing symbol. -/
theorem isSmoothing_leftTerm_sub_cutoffSymbol_leftTerm (χ : FrequencyCutoff (CoordinateSpace n))
    (a : Amplitude n V W m)
    (h : HomogeneousSymbol (CoordinateSpace n × CoordinateSpace n) (CoordinateSpace n) V W m)
    (hah : ∀ K : Set (CoordinateSpace n × CoordinateSpace n), IsCompact K → ∃ R, ∀ x y,
      (x, y) ∈ K → ∀ ξ, R ≤ ‖ξ‖ → a.coefficient (x, y, ξ) = h.coefficient ((x, y), ξ))
    (k : ℕ) : (a.leftTerm k - HomogeneousSymbol.cutoffSymbol χ (h.leftTerm k)).IsSmoothing := by
  refine Symbol.isSmoothing_of_forall_isCompact_coefficient_eq_zero fun K hK ↦ ?_
  obtain ⟨R, hR⟩ := a.exists_coefficient_leftTerm_eq_of_forall_isCompact h hah k hK
  refine ⟨max R 2, fun x hx ξ hξ ↦ ?_⟩
  rw [Symbol.coefficient_sub, Pi.sub_apply,
    HomogeneousSymbol.coefficient_cutoffSymbol_of_two_le_norm _ _ ((le_max_right _ _).trans hξ),
    hR x hx ξ ((le_max_left _ _).trans hξ), sub_self]

end Amplitude

/-! ### Homogeneous amplitudes in moving frequency coordinates -/

namespace HomogeneousSymbol

variable {κ : CoordinateSpace n → CoordinateSpace n}
  {M : CoordinateSpace n × CoordinateSpace n → CoordinateSpace n →L[ℝ] CoordinateSpace n}
  {g : CoordinateSpace n × CoordinateSpace n → ℝ} {m : ℝ}

/-- The function `g(x, y) • a(κ x, M(x, y) ξ)` is smooth near every point of nonzero frequency:
near a point outside the support of `g` it vanishes, and on the support of `g` the frequency
`M(x, y) ξ` is nonzero. -/
private theorem contDiffAt_smul_coefficient_comp
    (a : HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W m)
    (hκ : ContDiff ℝ ∞ κ) (hM : ContDiff ℝ ∞ M) (hg : ContDiff ℝ ∞ g)
    (hgM : ∀ w ∈ tsupport g, IsUnit (M w))
    {p : (CoordinateSpace n × CoordinateSpace n) × CoordinateSpace n} (hp : p.2 ≠ 0) :
    ContDiffAt ℝ ∞ (fun q : (CoordinateSpace n × CoordinateSpace n) × CoordinateSpace n ↦
      g q.1 • a.coefficient (κ q.1.1, M q.1 q.2)) p := by
  by_cases hpg : p.1 ∈ tsupport g
  · have hMp : M p.1 p.2 ≠ 0 := fun h0 ↦ hp (by
      rw [← ContinuousLinearMap.ringInverse_apply_apply (hgM _ hpg) p.2, h0, map_zero])
    exact (hg.contDiffAt.comp p contDiffAt_fst).smul
      ((a.contDiffAt_coefficient (p := (κ p.1.1, M p.1 p.2)) hMp).comp p
        ((hκ.contDiffAt.comp p (contDiffAt_fst.comp p contDiffAt_fst)).prodMk
          ((hM.contDiffAt.comp p contDiffAt_fst).clm_apply contDiffAt_snd)))
  · refine (contDiffAt_const (c := (0 : V →L[ℂ] W))).congr_of_eventuallyEq ?_
    filter_upwards [(continuous_fst.tendsto p).eventually
      ((isClosed_tsupport g).isOpen_compl.mem_nhds hpg)] with q hq
    simp [image_eq_zero_of_notMem_tsupport hq]

/-- The **homogeneous amplitude `g(x, y) • a(κ x, M(x, y) ξ)`** of a homogeneous symbol `a` of
degree `m`, for a smooth map `κ`, a smooth family `M(x, y)` of linear maps of `ℝⁿ` and a smooth
weight `g` such that `M(x, y)` is invertible on the support of `g`. It is the homogeneous
counterpart of the amplitude `TauCeti.Symbol.compAmplitude`. -/
def compAmplitude (a : HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W m)
    (hκ : ContDiff ℝ ∞ κ) (hM : ContDiff ℝ ∞ M) (hg : ContDiff ℝ ∞ g)
    (hgM : ∀ w ∈ tsupport g, IsUnit (M w)) :
    HomogeneousSymbol (CoordinateSpace n × CoordinateSpace n) (CoordinateSpace n) V W m where
  coefficient p := g p.1 • a.coefficient (κ p.1.1, M p.1 p.2)
  zero_covector w := by simp
  contDiffOn_coefficient p hp :=
    (contDiffAt_smul_coefficient_comp a hκ hM hg hgM hp).contDiffWithinAt
  homogeneous w ξ t ht := by
    simp only [map_smul, a.homogeneous _ _ t ht]
    exact smul_comm _ _ _

@[simp]
theorem coefficient_compAmplitude
    (a : HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W m)
    (hκ : ContDiff ℝ ∞ κ) (hM : ContDiff ℝ ∞ M) (hg : ContDiff ℝ ∞ g)
    (hgM : ∀ w ∈ tsupport g, IsUnit (M w))
    (p : (CoordinateSpace n × CoordinateSpace n) × CoordinateSpace n) :
    (a.compAmplitude hκ hM hg hgM).coefficient p = g p.1 • a.coefficient (κ p.1.1, M p.1 p.2) :=
  (rfl)

/-- The amplitude `g(x, y) • χ(M(x, y) ξ) a(κ x, M(x, y) ξ)` of the cut-off term of a homogeneous
symbol `a` agrees with the homogeneous amplitude `g(x, y) • a(κ x, M(x, y) ξ)` at all large
frequencies, uniformly in the positions: on the compact support of `g`, `‖M(x, y) ξ‖` is bounded
below by a multiple of `‖ξ‖`. -/
theorem exists_coefficient_compAmplitude_cutoffSymbol_eq
    (χ : FrequencyCutoff (CoordinateSpace n))
    (a : HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W m)
    (hκ : ContDiff ℝ ∞ κ) (hM : ContDiff ℝ ∞ M) (hg : ContDiff ℝ ∞ g)
    (hgc : HasCompactSupport g) (hgM : ∀ w ∈ tsupport g, IsUnit (M w)) :
    ∃ R, ∀ x y ξ, R ≤ ‖ξ‖ →
      ((cutoffSymbol χ a).compAmplitude hκ hM hg hgc hgM).coefficient (x, y, ξ) =
        (a.compAmplitude hκ hM hg hgM).coefficient ((x, y), ξ) := by
  obtain ⟨c, hc, hcS⟩ :=
    exists_norm_clm_apply_le_and_norm_le_of_isUnit hgc.isCompact hM.continuous.continuousOn hgM
  refine ⟨2 * c, fun x y ξ hξ ↦ ?_⟩
  rw [Symbol.coefficient_compAmplitude, coefficient_compAmplitude, coefficient_cutoffSymbol]
  by_cases hxy : (x, y) ∈ tsupport g
  · have h2 : 2 ≤ ‖M (x, y) ξ‖ := by
      have := (hcS _ hxy ξ).2
      nlinarith
    simp only [χ.apply_eq_one_of_two_le_norm h2, one_smul]
  · simp [image_eq_zero_of_notMem_tsupport hxy]

end HomogeneousSymbol

/-! ### Classical symbols in moving frequency coordinates -/

namespace ClassicalSymbol

open HomogeneousSymbol Finset

variable {κ : CoordinateSpace n → CoordinateSpace n}
  {M : CoordinateSpace n × CoordinateSpace n → CoordinateSpace n →L[ℝ] CoordinateSpace n}
  {g : CoordinateSpace n × CoordinateSpace n → ℝ}
  (hκ : ContDiff ℝ ∞ κ) (hM : ContDiff ℝ ∞ M) (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g)
  (hgM : ∀ w ∈ tsupport g, IsUnit (M w))

/-- The homogeneous terms of the left symbol of the amplitude `g(x, y) • a(κ x, M(x, y) ξ)` of a
classical symbol `a` of order `m`: the term of degree `m - l` collects the terms of degree `m - l`
of the expansions of the homogeneous amplitudes `g(x, y) • a_{m-j}(κ x, M(x, y) ξ)`,

`∑_{k ≤ l} leftTerm (g(x, y) • a_{m-l+k}(κ x, M(x, y) ξ)) k`. -/
def compAmplitudeTerms (a : ClassicalSymbol n V W m) (l : ℕ) :
    HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W (m - l) :=
  ∑ k ∈ range (l + 1),
    if h : k ≤ l then
      (((a.term (l - k)).compAmplitude hκ hM hg hgM).leftTerm k).castDegree
        (by rw [Nat.cast_sub h]; ring)
    else 0

theorem coefficient_compAmplitudeTerms (a : ClassicalSymbol n V W m) (l : ℕ)
    (p : CoordinateSpace n × CoordinateSpace n) :
    (a.compAmplitudeTerms hκ hM hg hgM l).coefficient p =
      ∑ k ∈ range (l + 1),
        (((a.term (l - k)).compAmplitude hκ hM hg hgM).leftTerm k).coefficient p := by
  simp only [compAmplitudeTerms, HomogeneousSymbol.coefficient_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun k hk ↦ ?_
  simp [Nat.lt_succ_iff.1 (mem_range.1 hk)]

/-- The leading term `g(x, x) • a_m(κ x, M(x, x) ξ)` of the left symbol of the amplitude
`g(x, y) • a(κ x, M(x, y) ξ)`. -/
@[simp]
theorem coefficient_compAmplitudeTerms_zero (a : ClassicalSymbol n V W m)
    (x ξ : CoordinateSpace n) :
    (a.compAmplitudeTerms hκ hM hg hgM 0).coefficient (x, ξ) =
      g (x, x) • a.principal.coefficient (κ x, M (x, x) ξ) := by
  simp [coefficient_compAmplitudeTerms, coefficient_principal]

/-- The term `leftTerm k` of the amplitude `g(x, y) • a(κ x, M(x, y) ξ)` of a classical symbol `a`
is, up to a symbol of order `m - N`, the sum of the cut-off terms `leftTerm k` of the homogeneous
amplitudes `g(x, y) • a_{m-j}(κ x, M(x, y) ξ)`, `j < N - k`. -/
private theorem exists_coefficient_leftTerm_compAmplitude_sub (a : ClassicalSymbol n V W m)
    (χ : FrequencyCutoff (CoordinateSpace n)) (k N : ℕ) :
    ∃ r : Symbol n V W (m - N), ∀ p, r.coefficient p =
      ((a.toSymbol.compAmplitude hκ hM hg hgc hgM).leftTerm k).coefficient p -
        ∑ j ∈ range (N - k),
          χ p.2 • (((a.term j).compAmplitude hκ hM hg hgM).leftTerm k).coefficient p := by
  -- Expand `a = ∑_{j < N - k} χ(η) a_{m-j}(z, η) + r_{N-k}(z, η)` inside the amplitude.
  have hdec : ∀ p, (a.toSymbol.compAmplitude hκ hM hg hgc hgM).coefficient p =
      ∑ j ∈ range (N - k),
          ((cutoffSymbol χ (a.term j)).compAmplitude hκ hM hg hgc hgM).coefficient p +
        ((a.remainder χ (N - k)).compAmplitude hκ hM hg hgc hgM).coefficient p := fun p ↦ by
    simp only [Symbol.coefficient_compAmplitude, coefficient_cutoffSymbol, coefficient_remainder,
      ← Finset.smul_sum, ← smul_add, add_sub_cancel]
  -- Each cut-off term contributes its homogeneous term, up to a smoothing symbol.
  choose s hs using fun j ↦ Symbol.isSmoothing_iff.1
    (Amplitude.isSmoothing_leftTerm_sub_cutoffSymbol_leftTerm χ
      ((cutoffSymbol χ (a.term j)).compAmplitude hκ hM hg hgc hgM)
      ((a.term j).compAmplitude hκ hM hg hgM)
      (fun _ _ ↦ (exists_coefficient_compAmplitude_cutoffSymbol_eq χ (a.term j) hκ hM hg hgc
        hgM).imp fun _ hR x y _ ξ hξ ↦ hR x y ξ hξ) k) (m - N)
  -- The remainder `r_{N-k}` contributes a term of order `m - (N - k) - k ≤ m - N`.
  have hord : m - ((N - k : ℕ) : ℝ) - k ≤ m - N := by
    have : (N : ℝ) ≤ ((N - k : ℕ) : ℝ) + k := by exact_mod_cast le_tsub_add
    linarith
  refine ⟨Symbol.inclusion hord
    (((a.remainder χ (N - k)).compAmplitude hκ hM hg hgc hgM).leftTerm k) +
      ∑ j ∈ range (N - k), s j, fun p ↦ ?_⟩
  rw [Amplitude.coefficient_leftTerm_eq_sum_add _ _ _ _ hdec]
  simp only [Symbol.coefficient_add, Symbol.coefficient_inclusion, Symbol.coefficient_sum,
    Pi.add_apply, Finset.sum_apply, hs, Symbol.coefficient_sub, Pi.sub_apply,
    coefficient_cutoffSymbol, Finset.sum_sub_distrib]
  abel

variable [CompleteSpace W]

/-- The remainder of the left symbol of the amplitude `g(x, y) • a(κ x, M(x, y) ξ)` after its first
`N` homogeneous terms `compAmplitudeTerms` has order `m - N`: it is the remainder of the expansion
of the left symbol after `N` terms, plus the remainders of the terms `leftTerm k`, `k < N`, after
`N - k` homogeneous terms. -/
private theorem exists_remainder_leftSymbol_compAmplitude (a : ClassicalSymbol n V W m)
    (χ : FrequencyCutoff (CoordinateSpace n)) (N : ℕ) :
    ∃ r : Symbol n V W (m - N), ∀ p, r.coefficient p =
      ((a.toSymbol.compAmplitude hκ hM hg hgc hgM).leftSymbol
          (a.toSymbol.hasProperInputSupport_compAmplitude hκ hM hg hgc hgM)).coefficient p -
        ∑ l ∈ range N, χ p.2 • (a.compAmplitudeTerms hκ hM hg hgM l).coefficient p := by
  choose r hr using fun k ↦ exists_coefficient_leftTerm_compAmplitude_sub hκ hM hg hgc hgM a χ k N
  refine ⟨Amplitude.leftRemainder _
    (a.toSymbol.hasProperInputSupport_compAmplitude hκ hM hg hgc hgM) N + ∑ k ∈ range N, r k,
    fun p ↦ ?_⟩
  simp only [Symbol.coefficient_add, Symbol.coefficient_sum, Pi.add_apply, Finset.sum_apply, hr,
    Amplitude.coefficient_leftRemainder, Pi.sub_apply, coefficient_compAmplitudeTerms,
    Finset.smul_sum, Finset.sum_sub_distrib]
  -- Reindex the double sum over `k + j = l < N` by `k < N`, `j < N - k`.
  rw [Finset.sum_range_diag_flip N fun k j ↦
    χ p.2 • (((a.term j).compAmplitude hκ hM hg hgM).leftTerm k).coefficient p]
  abel

/-- **Classical symbols in moving frequency coordinates.** For a classical symbol `a` of order `m`,
the left symbol of the amplitude `g(x, y) • a(κ x, M(x, y) ξ)` (`TauCeti.Symbol.compAmplitude`) is a
classical symbol of order `m`, with the homogeneous terms `compAmplitudeTerms`: the term of degree
`m - l` is `∑_{k ≤ l} leftTerm (g(x, y) • a_{m-l+k}(κ x, M(x, y) ξ)) k`. Its principal symbol is
`g(x, x) • a_m(κ x, M(x, x) ξ)`
(`TauCeti.ClassicalSymbol.coefficient_principal_leftSymbolCompAmplitude`). -/
def leftSymbolCompAmplitude (a : ClassicalSymbol n V W m) : ClassicalSymbol n V W m where
  toSymbol := (a.toSymbol.compAmplitude hκ hM hg hgc hgM).leftSymbol
    (a.toSymbol.hasProperInputSupport_compAmplitude hκ hM hg hgc hgM)
  term := a.compAmplitudeTerms hκ hM hg hgM
  exists_remainder' :=
    ⟨default, exists_remainder_leftSymbol_compAmplitude hκ hM hg hgc hgM a default⟩

variable (a : ClassicalSymbol n V W m)

@[simp]
theorem toSymbol_leftSymbolCompAmplitude :
    (a.leftSymbolCompAmplitude hκ hM hg hgc hgM).toSymbol =
      (a.toSymbol.compAmplitude hκ hM hg hgc hgM).leftSymbol
        (a.toSymbol.hasProperInputSupport_compAmplitude hκ hM hg hgc hgM) :=
  (rfl)

@[simp]
theorem term_leftSymbolCompAmplitude (l : ℕ) :
    (a.leftSymbolCompAmplitude hκ hM hg hgc hgM).term l = a.compAmplitudeTerms hκ hM hg hgM l :=
  (rfl)

/-- The principal symbol of the left symbol of the amplitude `g(x, y) • a(κ x, M(x, y) ξ)` is
`g(x, x) • a_m(κ x, M(x, x) ξ)`. -/
@[simp]
theorem coefficient_principal_leftSymbolCompAmplitude (x ξ : CoordinateSpace n) :
    (a.leftSymbolCompAmplitude hκ hM hg hgc hgM).principal.coefficient (x, ξ) =
      g (x, x) • a.principal.coefficient (κ x, M (x, x) ξ) := by
  rw [coefficient_principal, term_leftSymbolCompAmplitude, coefficient_compAmplitudeTerms_zero]

end ClassicalSymbol

end TauCeti
