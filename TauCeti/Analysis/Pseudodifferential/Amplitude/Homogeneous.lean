/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Amplitude.Expansion
public import TauCeti.Analysis.Pseudodifferential.HomogeneousSymbol
import TauCeti.Analysis.Pseudodifferential.Amplitude.Comp

/-!
# The left expansion of a homogeneous amplitude

The terms `TauCeti.Amplitude.leftTerm a k = ((-i)^k / k!) ∑_{|w| = k} (∂_y^w ∂_ξ^w a)(x, x, ξ)` of
the asymptotic expansion of the left symbol of an amplitude `a(x, y, ξ)` only involve derivatives
of `a` at the diagonal. When `a` is homogeneous in the frequency, so is each term, of a degree one
lower for every frequency derivative. This file computes the terms for a homogeneous symbol `h`
whose positions are pairs `(x, y)`, a *homogeneous amplitude*: they are homogeneous symbols
`TauCeti.HomogeneousSymbol.leftTerm h k` of degree `m - k`.

If an amplitude `a` agrees with `h` at all frequencies of norm larger than some `R`, then so do
all their derivatives, and the terms of the left expansion of `a` agree there with those of `h`
(`TauCeti.Amplitude.coefficient_leftTerm_eq_of_eq`). This is how the classical expansion of an
amplitude `a ∼ ∑ⱼ χ(ξ) hⱼ` with homogeneous terms `hⱼ` passes to its left symbol: each term of the
left expansion of `χ(ξ) hⱼ` is the cut-off homogeneous symbol `χ(ξ) leftTerm hⱼ k` up to a
smoothing symbol.

Homogeneous amplitudes arise from changes of coordinates: for a homogeneous symbol `h` of degree
`m`, a smooth family `M(x, y)` of linear maps and a smooth weight `g(x, y)` such that `M` is
invertible on the support of `g`, `g(x, y) • h(κ x, M(x, y) ξ)` is a homogeneous amplitude of
degree `m` (`TauCeti.HomogeneousSymbol.compAmplitude`), the homogeneous counterpart of the
amplitude `TauCeti.Symbol.compAmplitude`.

## Main declarations

* `TauCeti.HomogeneousSymbol.leftTerm`: the term of degree `m - k` of the left expansion of a
  homogeneous amplitude, defined by the recursion of `TauCeti.Amplitude.leftTerm`.
* `TauCeti.Amplitude.coefficient_leftTerm_eq_of_eq`: an amplitude that agrees with a homogeneous
  amplitude at large frequencies has the same terms of the left expansion there.
* `TauCeti.HomogeneousSymbol.compAmplitude`: the homogeneous amplitude
  `g(x, y) • h(κ x, M(x, y) ξ)` of a homogeneous symbol `h`.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, Theorem 18.1.7 and
  Definition 18.1.5.
* M. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI* (2008), Lecture I,
  (1.21)–(1.28).
-/

public section

noncomputable section

open Set Filter
open scoped ContDiff Topology

namespace TauCeti

variable {n : ℕ} {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W]
  [NormedSpace ℂ W]

namespace HomogeneousSymbol

/-- The term `((-i)^k / k!) ∑_{|w| = k} (∂_y^w ∂_ξ^w h)((x, x), ξ)` of degree `m - k` of the left
expansion of a homogeneous amplitude `h((x, y), ξ)` of degree `m`. It is defined by the recursion
of `TauCeti.Amplitude.leftTerm`: `leftTerm h 0` is the restriction of `h` to the diagonal
`y = x`, and `leftTerm h (k + 1) = (-i / (k + 1)) ∑ⱼ leftTerm (∂_{y_j} ∂_{ξ_j} h) k`. -/
def leftTerm : {m : ℝ} →
    HomogeneousSymbol (CoordinateSpace n × CoordinateSpace n) (CoordinateSpace n) V W m →
    (k : ℕ) → HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W (m - k)
  | _, h, 0 => (h.compPosition (fun x ↦ (x, x)) (contDiff_id.prodMk contDiff_id)).castDegree
      (by simp)
  | _, h, k + 1 => (-Complex.I / (k + 1 : ℂ)) • ∑ j : Fin n,
      (leftTerm ((h.frequencyDeriv (EuclideanSpace.single j 1)).spatialDeriv
        (0, EuclideanSpace.single j 1)) k).castDegree (by push_cast; ring)

variable {m : ℝ}
  (h : HomogeneousSymbol (CoordinateSpace n × CoordinateSpace n) (CoordinateSpace n) V W m)

theorem leftTerm_zero :
    h.leftTerm 0 = (h.compPosition (fun x ↦ (x, x)) (contDiff_id.prodMk contDiff_id)).castDegree
      (by simp) :=
  (rfl)

theorem leftTerm_succ (k : ℕ) :
    h.leftTerm (k + 1) = (-Complex.I / (k + 1 : ℂ)) • ∑ j : Fin n,
      (((h.frequencyDeriv (EuclideanSpace.single j 1)).spatialDeriv
        (0, EuclideanSpace.single j 1)).leftTerm k).castDegree (by push_cast; ring) :=
  (rfl)

/-- The leading term of the left expansion is the restriction to the diagonal. -/
@[simp]
theorem coefficient_leftTerm_zero (p : CoordinateSpace n × CoordinateSpace n) :
    (h.leftTerm 0).coefficient p = h.coefficient ((p.1, p.1), p.2) := by
  simp [leftTerm_zero]

theorem coefficient_leftTerm_succ (k : ℕ) (p : CoordinateSpace n × CoordinateSpace n) :
    (h.leftTerm (k + 1)).coefficient p = (-Complex.I / (k + 1 : ℂ)) • ∑ j : Fin n,
      (((h.frequencyDeriv (EuclideanSpace.single j 1)).spatialDeriv
        (0, EuclideanSpace.single j 1)).leftTerm k).coefficient p := by
  simp [leftTerm_succ]

end HomogeneousSymbol

namespace Amplitude

/-! ### Agreement at large frequencies -/

section Agreement

variable {m m' R : ℝ} {f : CoordinateSpace n × CoordinateSpace n × CoordinateSpace n → V →L[ℂ] W}
  {h : HomogeneousSymbol (CoordinateSpace n × CoordinateSpace n) (CoordinateSpace n) V W m'}

/-- A function of `(x, y, ξ)` that agrees with a homogeneous amplitude `h` at the frequencies of
norm larger than `R ≥ 0` has the same derivatives there: its derivative in the direction
`(0, v, w)` is that of `h` in the direction `((0, v), w)`. -/
private theorem fderiv_eq_of_eq
    (hf : ∀ x y ξ, R < ‖ξ‖ → f (x, y, ξ) = h.coefficient ((x, y), ξ)) {x y ξ : CoordinateSpace n}
    (hξ : R < ‖ξ‖) (v w : CoordinateSpace n) :
    fderiv ℝ f (x, y, ξ) (0, v, w) = fderiv ℝ h.coefficient ((x, y), ξ) ((0, v), w) := by
  set e := (ContinuousLinearEquiv.prodAssoc ℝ (CoordinateSpace n) (CoordinateSpace n)
    (CoordinateSpace n)).symm
  have hU : IsOpen {p : CoordinateSpace n × CoordinateSpace n × CoordinateSpace n |
      R < ‖p.2.2‖} :=
    isOpen_lt continuous_const (continuous_norm.comp (continuous_snd.comp continuous_snd))
  have heq : f =ᶠ[𝓝 (x, y, ξ)] h.coefficient ∘ e :=
    eventuallyEq_of_mem (hU.mem_nhds hξ) fun p hp ↦ hf p.1 p.2.1 p.2.2 hp
  rw [heq.fderiv_eq, e.comp_right_fderiv]
  simp [e, ContinuousLinearEquiv.prodAssoc_symm_apply]

/-- The frequency derivatives of a function agreeing with a homogeneous amplitude at large
frequencies agree with those of the homogeneous amplitude. -/
private theorem fderiv_frequency_eq_of_eq (hR : 0 ≤ R)
    (hf : ∀ x y ξ, R < ‖ξ‖ → f (x, y, ξ) = h.coefficient ((x, y), ξ)) (w : CoordinateSpace n) :
    ∀ x y ξ, R < ‖ξ‖ →
      fderiv ℝ f (x, y, ξ) (0, 0, w) = (h.frequencyDeriv w).coefficient ((x, y), ξ) := by
  intro x y ξ hξ
  have hξ0 : ξ ≠ 0 := norm_pos_iff.1 (hR.trans_lt hξ)
  rw [fderiv_eq_of_eq hf hξ, h.coefficient_frequencyDeriv_eq_fderiv w hξ0, Prod.mk_zero_zero]

/-- The input-position derivatives of a function agreeing with a homogeneous amplitude at large
frequencies agree with those of the homogeneous amplitude. -/
private theorem fderiv_input_eq_of_eq
    (hf : ∀ x y ξ, R < ‖ξ‖ → f (x, y, ξ) = h.coefficient ((x, y), ξ)) (v : CoordinateSpace n) :
    ∀ x y ξ, R < ‖ξ‖ →
      fderiv ℝ f (x, y, ξ) (0, v, 0) = (h.spatialDeriv (0, v)).coefficient ((x, y), ξ) := by
  intro x y ξ hξ
  rw [fderiv_eq_of_eq hf hξ, h.coefficient_spatialDeriv_eq_fderiv]

/-- **The left expansion of an amplitude that is homogeneous at large frequencies.** If an
amplitude `a(x, y, ξ)` agrees with a homogeneous amplitude `h((x, y), ξ)` at all frequencies of
norm larger than `R ≥ 0`, then every term of the left expansion of `a` agrees there with the
corresponding homogeneous term `h.leftTerm k`. -/
theorem coefficient_leftTerm_eq_of_eq (hR : 0 ≤ R) {a : Amplitude n V W m}
    (ha : ∀ x y ξ, R < ‖ξ‖ → a.coefficient (x, y, ξ) = h.coefficient ((x, y), ξ)) (k : ℕ)
    {x ξ : CoordinateSpace n} (hξ : R < ‖ξ‖) :
    (a.leftTerm k).coefficient (x, ξ) = (h.leftTerm k).coefficient (x, ξ) := by
  induction k generalizing m m' with
  | zero => simp [ha x x ξ hξ]
  | succ k ih =>
    rw [coefficient_leftTerm_succ, HomogeneousSymbol.coefficient_leftTerm_succ]
    refine congrArg _ (Finset.sum_congr rfl fun j _ ↦ ih fun x y ξ hξ ↦ ?_)
    -- Differentiate the agreement in `ξ_j`, then in `y_j`.
    rw [coefficient_spatialDerivSnd]
    exact fderiv_input_eq_of_eq (fun x y ξ hξ ↦ by
      rw [coefficient_frequencyDeriv]
      exact fderiv_frequency_eq_of_eq hR ha _ x y ξ hξ) _ x y ξ hξ

end Agreement

end Amplitude

/-! ### Homogeneous amplitudes in moving frequency coordinates -/

namespace HomogeneousSymbol

variable {m : ℝ} {κ : CoordinateSpace n → CoordinateSpace n}
  {M : CoordinateSpace n × CoordinateSpace n → CoordinateSpace n →L[ℝ] CoordinateSpace n}
  {g : CoordinateSpace n × CoordinateSpace n → ℝ}

/-- The function `((x, y), ξ) ↦ g(x, y) • h(κ x, M(x, y) ξ)` is smooth at the nonzero frequencies
when `M` is invertible on the support of `g`: near a point of the support, `M(x, y) ξ ≠ 0`, and
elsewhere it vanishes nearby. -/
private theorem contDiffOn_compAmplitude
    (h : HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W m) (hκ : ContDiff ℝ ∞ κ)
    (hM : ContDiff ℝ ∞ M) (hg : ContDiff ℝ ∞ g) (hgM : ∀ w ∈ tsupport g, IsUnit (M w)) :
    ContDiffOn ℝ ∞ (fun p : (CoordinateSpace n × CoordinateSpace n) × CoordinateSpace n ↦
      g p.1 • h.coefficient (κ p.1.1, M p.1 p.2)) {p | p.2 ≠ 0} := by
  intro p hp
  refine ContDiffAt.contDiffWithinAt ?_
  by_cases hpg : p.1 ∈ tsupport g
  · have hne : M p.1 p.2 ≠ 0 :=
      (map_ne_zero_iff _ (ContinuousLinearMap.isUnit_iff_bijective.1 (hgM _ hpg)).1).2 hp
    have hin : ContDiff ℝ ∞ fun q : (CoordinateSpace n × CoordinateSpace n) × CoordinateSpace n ↦
        (κ q.1.1, M q.1 q.2) :=
      (hκ.comp (contDiff_fst.comp contDiff_fst)).prodMk
        ((hM.comp contDiff_fst).clm_apply contDiff_snd)
    exact (hg.comp contDiff_fst).contDiffAt.smul
      ((h.contDiffAt_coefficient (p := (κ p.1.1, M p.1 p.2)) hne).comp p hin.contDiffAt)
  · have hev : (fun q : (CoordinateSpace n × CoordinateSpace n) × CoordinateSpace n ↦
        g q.1 • h.coefficient (κ q.1.1, M q.1 q.2)) =ᶠ[nhds p] fun _ ↦ 0 := by
      filter_upwards [continuous_fst.continuousAt.preimage_mem_nhds
        ((isClosed_tsupport g).isOpen_compl.mem_nhds hpg)] with q hq
      rw [image_eq_zero_of_notMem_tsupport hq, zero_smul]
    exact contDiffAt_const.congr_of_eventuallyEq hev

/-- The homogeneous amplitude `((x, y), ξ) ↦ g(x, y) • h(κ x, M(x, y) ξ)` of degree `m` of a
homogeneous symbol `h` of degree `m`, for a smooth family `M(x, y)` of linear maps that are
invertible on the support of the smooth weight `g`. It is the homogeneous counterpart of the
amplitude `TauCeti.Symbol.compAmplitude` describing changes of coordinates. -/
def compAmplitude (h : HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W m)
    (hκ : ContDiff ℝ ∞ κ) (hM : ContDiff ℝ ∞ M) (hg : ContDiff ℝ ∞ g)
    (hgM : ∀ w ∈ tsupport g, IsUnit (M w)) :
    HomogeneousSymbol (CoordinateSpace n × CoordinateSpace n) (CoordinateSpace n) V W m :=
  mk' (fun p ↦ g p.1 • h.coefficient (κ p.1.1, M p.1 p.2))
    (contDiffOn_compAmplitude h hκ hM hg hgM) fun x ξ _ t ht ↦ by
      simp only [map_smul, h.homogeneous _ _ _ ht, smul_comm (g x)]

@[simp]
theorem coefficient_compAmplitude
    (h : HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W m) (hκ : ContDiff ℝ ∞ κ)
    (hM : ContDiff ℝ ∞ M) (hg : ContDiff ℝ ∞ g) (hgM : ∀ w ∈ tsupport g, IsUnit (M w))
    (p : (CoordinateSpace n × CoordinateSpace n) × CoordinateSpace n) :
    (h.compAmplitude hκ hM hg hgM).coefficient p = g p.1 • h.coefficient (κ p.1.1, M p.1 p.2) := by
  obtain ⟨w, ξ⟩ := p
  rcases eq_or_ne ξ 0 with rfl | hξ
  · simp
  · exact coefficient_mk'_of_ne_zero _ _ _ hξ

end HomogeneousSymbol

end TauCeti
