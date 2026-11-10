/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Frequency.Cutoff
public import TauCeti.Analysis.Pseudodifferential.Symbol.Basic
import TauCeti.Analysis.Calculus.BumpFunction.FiniteDimension
import TauCeti.Analysis.Calculus.ContinuousLinearMapInverse

/-!
# Inverses of symbols

Let `a` be a symbol of order `m` (`TauCeti.Symbol n V W m`) which, at all frequencies `‖ξ‖ ≥ t`,
is invertible with `‖a(x, ξ)⁻¹‖ ≤ C ⟨ξ⟩ ^ (-m)`. Differentiating `a⁻¹ ∘ a = 1` gives
`∂(a⁻¹) = -(a⁻¹ ∘ ∂a ∘ a⁻¹)`, and induction on the number of derivatives, with the Leibniz rule,
bounds every mixed derivative by `‖∂_x^α ∂_ξ^β (a⁻¹)(x, ξ)‖ ≤ C' ⟨ξ⟩ ^ (-m - |β|)`: the
pointwise inverse satisfies the symbol estimates of order `-m`. Cut off near the frequencies where
`a` may fail to be invertible, it becomes a symbol of order `-m` inverting `a` modulo smoothing
symbols. This is the first step of the parametrix construction for elliptic symbols, which are
then inverted to all orders by an asymptotic sum.

The file treats full symbols in `S^m_{1,0}`, with no homogeneity; the inverse of an elliptic
homogeneous principal symbol is `TauCeti.HomogeneousSymbol.inverse`.

## Main declarations

* `TauCeti.exists_norm_mixedDeriv_inverse_le`: the derivative estimates for the inverse of a smooth
  family `a(x, ξ)` at the positions of a set `K` and the frequencies `‖ξ‖ ≥ R`. For a compact `K`
  they are the local symbol estimates, for `K = univ` the estimates uniform in the position.
* `TauCeti.Symbol.cutoffInverse χ a ht hinv hbound`: for a frequency cutoff `χ` and a radius
  `t ≥ 1` such that `a` is invertible at all frequencies `‖ξ‖ ≥ t`, with
  `‖a(x, ξ)⁻¹‖ ≤ C_K ⟨ξ⟩ ^ (-m)` there for the positions `x` of each compact set `K`, the
  symbol `χ(ξ / t) a(x, ξ)⁻¹` of order `-m`. It equals `a⁻¹` at the frequencies `‖ξ‖ ≥ 2 t`
  (`TauCeti.Symbol.coefficient_cutoffInverse_of_two_mul_le_norm`).
* `TauCeti.Symbol.isSmoothing_cutoffInverse_comp_sub` and
  `TauCeti.Symbol.isSmoothing_comp_cutoffInverse_sub`: the cut-off inverse is a two-sided inverse
  of `a` for `TauCeti.Symbol.comp` modulo smoothing symbols.
* `TauCeti.Symbol.IsUniform.cutoffInverse`: for a uniform symbol with `‖a(x, ξ)⁻¹‖ ≤ C ⟨ξ⟩ ^ (-m)`
  for all positions, the cut-off inverse is uniform.

## Implementation notes

The pointwise inverse is only smooth where `a` is invertible, while the Leibniz rule for mixed
derivatives (`TauCeti.Symbol.norm_mixedDeriv_comp_le`) is stated for globally smooth functions.
Near each point of invertibility the inverse agrees with a globally smooth function
(`ContDiffOn.exists_contDiff_eventuallyEq_of_finiteDimensional`), and mixed derivatives only
depend on germs, so the induction is carried out for that function.

## References

* M. E. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI*, September 2008,
  Lecture I, (4.1)–(4.6).
* M. A. Shubin, *Pseudodifferential Operators and Spectral Theory*, 2nd ed., Springer, 2001,
  Chapter I, §5.
-/

public section

noncomputable section

open Filter Topology
open scoped ContDiff

namespace TauCeti

variable {n : ℕ} {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W]
  [NormedSpace ℂ W] {m : ℝ}

/-! ### The Leibniz estimate for a triple product -/

/-- The Leibniz estimate for the triple product `g ∘ b ∘ g`, where `g` has the estimates of
order `-m` up to the derivatives along `α` and `β`, and `b` those of order `μ`. -/
private theorem norm_mixedDeriv_comp_comp_le
    {g : CoordinateSpace n × CoordinateSpace n → W →L[ℂ] V}
    {b : CoordinateSpace n × CoordinateSpace n → V →L[ℂ] W} (hg : ContDiff ℝ ∞ g)
    (hb : ContDiff ℝ ∞ b) {x ξ : CoordinateSpace n} {μ : ℝ}
    {G B : List (Fin n) → List (Fin n) → ℝ} {α β : List (Fin n)}
    (hG : ∀ s t, s.length ≤ α.length → t.length ≤ β.length →
      ‖mixedDeriv s t g x ξ‖ ≤ G s t * (1 + ‖ξ‖ ^ 2) ^ ((-m - t.length) / 2))
    (hB : ∀ s t, ‖mixedDeriv s t b x ξ‖ ≤ B s t * (1 + ‖ξ‖ ^ 2) ^ ((μ - t.length) / 2)) :
    ‖mixedDeriv α β (fun q ↦ g q ∘L (b q ∘L g q)) x ξ‖ ≤
      Symbol.compBound G (Symbol.compBound B G) α β *
        (1 + ‖ξ‖ ^ 2) ^ ((-m + (μ + -m) - β.length) / 2) := by
  have hbg : ContDiff ℝ ∞ fun q ↦ b q ∘L g q :=
    (((ContinuousLinearMap.compL ℂ W V W).bilinearRestrictScalars ℝ).isBoundedBilinearMap.contDiff
      (n := ∞)).comp (hb.prodMk hg)
  exact Symbol.norm_mixedDeriv_comp_le hg hbg hG fun s t hs ht ↦
    Symbol.norm_mixedDeriv_comp_le hb hg (fun s' t' _ _ ↦ hB s' t')
      fun s' t' hs' ht' ↦ hG s' t' (hs'.trans hs) (ht'.trans ht)

/-! ### Derivatives of the pointwise inverse -/

section Inverse

variable [CompleteSpace V] {a : CoordinateSpace n × CoordinateSpace n → V →L[ℂ] W}

/-- Near a point where `a` is invertible, its pointwise inverse agrees with a globally smooth
function `g`, whose derivatives near that point satisfy `g' v = -(g ∘ a' v ∘ g)`. -/
private theorem exists_contDiff_eventuallyEq_inverse (ha : ContDiff ℝ ∞ a)
    {p : CoordinateSpace n × CoordinateSpace n} (hp : (a p).IsInvertible) :
    ∃ g : CoordinateSpace n × CoordinateSpace n → W →L[ℂ] V, ContDiff ℝ ∞ g ∧
      g =ᶠ[𝓝 p] (fun q ↦ (a q).inverse) ∧ ∀ v, (fun q ↦ fderiv ℝ g q v) =ᶠ[𝓝 p]
        fun q ↦ -(g q ∘L (fderiv ℝ a q v ∘L g q)) := by
  have hU : {q | (a q).IsInvertible} ∈ 𝓝 p :=
    ha.continuous.continuousAt.preimage_mem_nhds
      (ContinuousLinearMap.isOpen_setOfPred_isInvertible.mem_nhds hp)
  obtain ⟨g, hg, -, hgp⟩ := ContDiffOn.exists_contDiff_eventuallyEq_of_finiteDimensional (n := ⊤)
    (fun q hq ↦ (ha.contDiffAt.clm_inverse hq).contDiffWithinAt) hU
  refine ⟨g, hg, hgp, fun v ↦ ?_⟩
  filter_upwards [hgp.eventually_nhds, hU] with q (hq : g =ᶠ[𝓝 q] _) hqU
  rw [hq.fderiv_eq, fderiv_clm_inverse_apply (ha.differentiable (by simp) q) hqU, hq.eq_of_nhds]

omit [CompleteSpace V] in
/-- One step of the induction behind `exists_norm_mixedDeriv_inverse_le`: if `g` agrees with
`a⁻¹` near `(x, ξ)`, then the mixed derivatives of `g' v = -(g ∘ a' v ∘ g)` are bounded by those of
`a⁻¹` of lower order and those of `a' v`. -/
private theorem norm_mixedDeriv_fderiv_le (ha : ContDiff ℝ ∞ a) {x ξ : CoordinateSpace n}
    {g : CoordinateSpace n × CoordinateSpace n → W →L[ℂ] V} (hg : ContDiff ℝ ∞ g)
    (hgp : g =ᶠ[𝓝 (x, ξ)] fun q ↦ (a q).inverse) {v : CoordinateSpace n × CoordinateSpace n}
    (hgv : (fun q ↦ fderiv ℝ g q v) =ᶠ[𝓝 (x, ξ)] fun q ↦ -(g q ∘L (fderiv ℝ a q v ∘L g q)))
    {μ : ℝ} {G B : List (Fin n) → List (Fin n) → ℝ} {α β : List (Fin n)}
    (hG : ∀ s t, s.length ≤ α.length → t.length ≤ β.length →
      ‖mixedDeriv s t (fun q ↦ (a q).inverse) x ξ‖ ≤
        G s t * (1 + ‖ξ‖ ^ 2) ^ ((-m - t.length) / 2))
    (hB : ∀ s t, ‖mixedDeriv s t (fun q ↦ fderiv ℝ a q v) x ξ‖ ≤
      B s t * (1 + ‖ξ‖ ^ 2) ^ ((μ - t.length) / 2)) :
    ‖mixedDeriv α β (fun q ↦ fderiv ℝ g q v) x ξ‖ ≤
      Symbol.compBound G (Symbol.compBound B G) α β *
        (1 + ‖ξ‖ ^ 2) ^ ((-m + (μ + -m) - β.length) / 2) := by
  have hav : ContDiff ℝ ∞ fun q ↦ fderiv ℝ a q v :=
    (ha.fderiv_right (m := ∞) le_rfl).clm_apply contDiff_const
  rw [hgv.mixedDeriv_eq, ← Pi.neg_def, mixedDeriv_neg, norm_neg]
  exact norm_mixedDeriv_comp_comp_le hg hav
    (fun s t hs ht ↦ hgp.mixedDeriv_eq s t ▸ hG s t hs ht) hB

/-- **Derivative estimates for the inverse of a symbol.** Let `a(x, ξ)` be a smooth family of
continuous linear maps which, for positions `x ∈ K` and frequencies `‖ξ‖ ≥ R`, is invertible with
`‖a(x, ξ)⁻¹‖ ≤ C ⟨ξ⟩ ^ (-m)` and satisfies the symbol estimates of order `m`. Then `a⁻¹` satisfies
the symbol estimates of order `-m` there: `‖∂_x^α ∂_ξ^β a⁻¹(x, ξ)‖ ≤ C' ⟨ξ⟩ ^ (-m - |β|)`.
The set `K` is arbitrary: for a compact `K` these are the local estimates, for `K = univ` the
estimates uniform in the position. -/
theorem exists_norm_mixedDeriv_inverse_le (ha : ContDiff ℝ ∞ a) {K : Set (CoordinateSpace n)}
    {R : ℝ} (hinv : ∀ x ∈ K, ∀ ξ, R ≤ ‖ξ‖ → (a (x, ξ)).IsInvertible)
    (hbound : ∃ C, ∀ x ∈ K, ∀ ξ, R ≤ ‖ξ‖ →
      ‖(a (x, ξ)).inverse‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ (-m / 2))
    (hder : ∀ α β : List (Fin n), ∃ C, ∀ x ∈ K, ∀ ξ, R ≤ ‖ξ‖ →
      ‖mixedDeriv α β a x ξ‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ ((m - β.length) / 2))
    (α β : List (Fin n)) :
    ∃ C, ∀ x ∈ K, ∀ ξ, R ≤ ‖ξ‖ →
      ‖mixedDeriv α β (fun p ↦ (a p).inverse) x ξ‖ ≤
        C * (1 + ‖ξ‖ ^ 2) ^ ((-m - β.length) / 2) := by
  -- Strong induction on the total number `|α| + |β|` of derivatives.
  suffices h : ∀ N : ℕ, ∀ α β : List (Fin n), α.length + β.length ≤ N → ∃ C, ∀ x ∈ K, ∀ ξ,
      R ≤ ‖ξ‖ → ‖mixedDeriv α β (fun p ↦ (a p).inverse) x ξ‖ ≤
        C * (1 + ‖ξ‖ ^ 2) ^ ((-m - β.length) / 2) from h _ α β le_rfl
  intro N
  induction N with
  | zero =>
    intro α β h
    obtain ⟨rfl, rfl⟩ : α = [] ∧ β = [] := by
      simpa [List.length_eq_zero_iff] using h
    obtain ⟨C, hC⟩ := hbound
    exact ⟨C, fun x hx ξ hξ ↦ by simpa using hC x hx ξ hξ⟩
  | succ N ih =>
    intro α β hαβ
    choose c hc using ih
    -- The bounds for fewer derivatives, as a function of all words.
    let G : List (Fin n) → List (Fin n) → ℝ := fun s t ↦
      if h : s.length + t.length ≤ N then c s t h else 0
    have hG (s t : List (Fin n)) (h : s.length + t.length ≤ N) {x : CoordinateSpace n}
        (hx : x ∈ K) {ξ : CoordinateSpace n} (hξ : R ≤ ‖ξ‖) :
        ‖mixedDeriv s t (fun p ↦ (a p).inverse) x ξ‖ ≤
          G s t * (1 + ‖ξ‖ ^ 2) ^ ((-m - t.length) / 2) := by
      simpa [G, h] using hc s t h x hx ξ hξ
    rcases β.eq_nil_or_concat with rfl | ⟨β', j, rfl⟩
    · rcases α.eq_nil_or_concat with rfl | ⟨α', j, rfl⟩
      · exact ⟨c [] [] (by simp), hc [] [] (by simp)⟩
      -- Peel off the last position derivative, `∂ₓ (a⁻¹) = -(a⁻¹ ∘ ∂ₓ a ∘ a⁻¹)`.
      choose B hB using fun s t : List (Fin n) ↦ hder (s ++ [j]) t
      refine ⟨Symbol.compBound G (Symbol.compBound B G) α' [], fun x hx ξ hξ ↦ ?_⟩
      obtain ⟨g, hg, hgp, hgv⟩ := exists_contDiff_eventuallyEq_inverse ha (hinv x hx ξ hξ)
      rw [List.concat_eq_append] at hαβ ⊢
      rw [← hgp.mixedDeriv_eq, ← mixedDeriv_fderiv_apply_fst hg]
      refine (norm_mixedDeriv_fderiv_le ha hg hgp (hgv _) (μ := m)
        (fun s t hs ht ↦ hG s t (by simp only [List.length_nil] at ht; simp at hαβ; omega) hx hξ)
        fun s t ↦ mixedDeriv_fderiv_apply_fst ha s t j x ξ ▸ hB s t x hx ξ hξ).trans_eq ?_
      congr 2
      ring
    -- Peel off the last frequency derivative, `∂_ξ (a⁻¹) = -(a⁻¹ ∘ ∂_ξ a ∘ a⁻¹)`.
    choose B hB using fun s t : List (Fin n) ↦ hder s (t ++ [j])
    refine ⟨Symbol.compBound G (Symbol.compBound B G) α β', fun x hx ξ hξ ↦ ?_⟩
    obtain ⟨g, hg, hgp, hgv⟩ := exists_contDiff_eventuallyEq_inverse ha (hinv x hx ξ hξ)
    rw [List.concat_eq_append] at hαβ ⊢
    rw [← hgp.mixedDeriv_eq, ← mixedDeriv_fderiv_apply_snd hg]
    refine (norm_mixedDeriv_fderiv_le ha hg hgp (hgv _) (μ := m - 1) (B := B)
      (fun s t hs ht ↦ hG s t (by simp at hαβ; omega) hx hξ)
      fun s t ↦ (mixedDeriv_fderiv_apply_snd ha s t j x ξ ▸ hB s t x hx ξ hξ).trans_eq ?_).trans_eq
        ?_
    · simp only [List.length_append, List.length_singleton, Nat.cast_add, Nat.cast_one]
      ring_nf
    · simp only [List.length_append, List.length_singleton, Nat.cast_add, Nat.cast_one]
      ring_nf

/-- Symbol estimates for the cut-off inverse `χ(ξ / t) a(x, ξ)⁻¹`, at all frequencies, from the
estimates of `exists_norm_mixedDeriv_inverse_le` at the frequencies `‖ξ‖ ≥ t`. -/
private theorem exists_norm_mixedDeriv_cutoff_smul_inverse_le (ha : ContDiff ℝ ∞ a)
    (χ : FrequencyCutoff (CoordinateSpace n)) {t : ℝ} (ht : 1 ≤ t) {K : Set (CoordinateSpace n)}
    (hinv : ∀ x ∈ K, ∀ ξ, t ≤ ‖ξ‖ → (a (x, ξ)).IsInvertible)
    (hbound : ∃ C, ∀ x ∈ K, ∀ ξ, t ≤ ‖ξ‖ →
      ‖(a (x, ξ)).inverse‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ (-m / 2))
    (hder : ∀ α β : List (Fin n), ∃ C, ∀ x ∈ K, ∀ ξ, t ≤ ‖ξ‖ →
      ‖mixedDeriv α β a x ξ‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ ((m - β.length) / 2))
    (α β : List (Fin n)) :
    ∃ C, 0 ≤ C ∧ ∀ x ∈ K, ∀ ξ,
      ‖mixedDeriv α β (fun p ↦ χ (t⁻¹ • p.2) • (a p).inverse) x ξ‖ ≤
        C * (1 + ‖ξ‖ ^ 2) ^ ((-m - β.length) / 2) := by
  have ht0 : 0 < t := one_pos.trans_le ht
  choose D hD using exists_norm_mixedDeriv_inverse_le ha hinv hbound hder α
  choose B hB0 hB using fun i : ℕ ↦
    χ.exists_norm_iteratedFDeriv_comp_inv_smul_mul_rpow_weight_le i
  refine ⟨max (∑ i ∈ Finset.range (β.length + 1), (β.length.choose i : ℝ) * B i *
    ∑ w : Fin (β.length - i) → Fin n, D (List.ofFn w)) 0, le_max_right _ _, fun x hx ξ ↦ ?_⟩
  rcases lt_or_ge ‖ξ‖ t with hξ | hξ
  · -- Below the radius `t` the cutoff vanishes near `ξ`.
    rw [(χ.comp_inv_smul_snd_smul_eventuallyEq_zero (fun p ↦ (a p).inverse) ht0
      (p := (x, ξ)) hξ).mixedDeriv_eq, mixedDeriv_zero, norm_zero]
    exact mul_nonneg (le_max_right _ _) (rpow_weight_pos ξ _).le
  -- Above it, replace `a⁻¹` by a globally smooth function with the same germ.
  obtain ⟨g, hg, hgp, -⟩ := exists_contDiff_eventuallyEq_inverse ha (hinv x hx ξ hξ)
  have hloc : (fun p ↦ χ (t⁻¹ • p.2) • (a p).inverse) =ᶠ[𝓝 (x, ξ)]
      fun p ↦ χ (t⁻¹ • p.2) • g p := by
    filter_upwards [hgp] with q hq
    rw [hq]
  rw [hloc.mixedDeriv_eq]
  have hψ : ContDiff ℝ ∞ fun η : CoordinateSpace n ↦ χ (t⁻¹ • η) :=
    χ.contDiff.comp (contDiff_const_smul _)
  refine (norm_mixedDeriv_comp_snd_smul_le_mul_rpow_weight (ψ := fun η ↦ χ (t⁻¹ • η))
    (B := B) (m := -m) hψ hg (fun i ↦ hB i t ht ξ)
    (fun w ↦ by rw [hgp.mixedDeriv_eq]; exact hD w x hx ξ hξ) β).trans
    (mul_le_mul_of_nonneg_right (le_max_left _ _) (rpow_weight_pos ξ _).le)

end Inverse

/-! ### The cut-off inverse of a symbol -/

namespace Symbol

variable [CompleteSpace V] (χ : FrequencyCutoff (CoordinateSpace n)) (a : Symbol n V W m) {t : ℝ}
  (ht : 1 ≤ t) (hinv : ∀ x ξ, t ≤ ‖ξ‖ → (a.coefficient (x, ξ)).IsInvertible)
  (hbound : ∀ K : Set (CoordinateSpace n), IsCompact K → ∃ C, ∀ x ∈ K, ∀ ξ, t ≤ ‖ξ‖ →
    ‖(a.coefficient (x, ξ)).inverse‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ (-m / 2))

/-- The **cut-off inverse** `χ(ξ / t) a(x, ξ)⁻¹` of a symbol `a` of order `m` which, for a radius
`t ≥ 1`, is invertible at all frequencies `‖ξ‖ ≥ t`, with `‖a(x, ξ)⁻¹‖ ≤ C ⟨ξ⟩ ^ (-m)` there for
`x` in each compact set: a symbol of order `-m`, equal to `a⁻¹` at the frequencies `‖ξ‖ ≥ 2 t`
(`TauCeti.Symbol.coefficient_cutoffInverse_of_two_mul_le_norm`). It inverts `a` modulo smoothing
symbols (`TauCeti.Symbol.isSmoothing_cutoffInverse_comp_sub`,
`TauCeti.Symbol.isSmoothing_comp_cutoffInverse_sub`). -/
def cutoffInverse : Symbol n W V (-m) where
  coefficient p := χ (t⁻¹ • p.2) • (a.coefficient p).inverse
  contDiff_coefficient := contDiff_iff_contDiffAt.2 fun p ↦ by
    rcases lt_or_ge ‖p.2‖ t with hp | hp
    · -- Below the radius `t` the cutoff vanishes near `p`.
      exact contDiffAt_const (c := (0 : W →L[ℂ] V)).congr_of_eventuallyEq
        (χ.comp_inv_smul_snd_smul_eventuallyEq_zero _ (one_pos.trans_le ht) hp)
    · exact (χ.contDiff.comp (contDiff_const_smul _)).contDiffAt.comp p contDiffAt_snd |>.smul
        (a.contDiff_coefficient.contDiffAt.clm_inverse (hinv p.1 p.2 hp))
  exists_bound K hK α β :=
    exists_norm_mixedDeriv_cutoff_smul_inverse_le a.contDiff_coefficient χ ht
      (fun x _ ξ hξ ↦ hinv x ξ hξ) (hbound K hK)
      (fun α β ↦ (a.exists_bound K hK α β).imp fun _ hC x hx ξ _ ↦ hC.2 x hx ξ) α β

@[simp]
theorem coefficient_cutoffInverse (p : CoordinateSpace n × CoordinateSpace n) :
    (a.cutoffInverse χ ht hinv hbound).coefficient p =
      χ (t⁻¹ • p.2) • (a.coefficient p).inverse :=
  (rfl)

/-- At the frequencies `‖ξ‖ ≥ 2 t` the cut-off inverse is the inverse of `a`. -/
theorem coefficient_cutoffInverse_of_two_mul_le_norm {x ξ : CoordinateSpace n} (hξ : 2 * t ≤ ‖ξ‖) :
    (a.cutoffInverse χ ht hinv hbound).coefficient (x, ξ) = (a.coefficient (x, ξ)).inverse := by
  simp [χ.apply_inv_smul_eq_one (one_pos.trans_le ht) hξ]

/-- At the frequencies `‖ξ‖ ≥ 2 t` the cut-off inverse is a left inverse of `a`. -/
theorem coefficient_cutoffInverse_comp_coefficient {x ξ : CoordinateSpace n} (hξ : 2 * t ≤ ‖ξ‖) :
    (a.cutoffInverse χ ht hinv hbound).coefficient (x, ξ) ∘L a.coefficient (x, ξ) =
      ContinuousLinearMap.id ℂ V := by
  rw [coefficient_cutoffInverse_of_two_mul_le_norm χ a ht hinv hbound hξ]
  exact (hinv x ξ (by linarith)).inverse_comp_self

/-- At the frequencies `‖ξ‖ ≥ 2 t` the cut-off inverse is a right inverse of `a`. -/
theorem coefficient_comp_coefficient_cutoffInverse {x ξ : CoordinateSpace n} (hξ : 2 * t ≤ ‖ξ‖) :
    a.coefficient (x, ξ) ∘L (a.cutoffInverse χ ht hinv hbound).coefficient (x, ξ) =
      ContinuousLinearMap.id ℂ W := by
  rw [coefficient_cutoffInverse_of_two_mul_le_norm χ a ht hinv hbound hξ]
  exact (hinv x ξ (by linarith)).self_comp_inverse

/-- The cut-off inverse is a left inverse of `a` modulo smoothing symbols: `a⁻¹ ∘ a - 1` vanishes
at the frequencies `‖ξ‖ ≥ 2 t`. -/
theorem isSmoothing_cutoffInverse_comp_sub :
    ((a.cutoffInverse χ ht hinv hbound).comp a -
      inclusion (neg_add_cancel m).ge (const (ContinuousLinearMap.id ℂ V))).IsSmoothing :=
  isSmoothing_iff.2 fun _ ↦ ⟨ofBoundedFrequencySupport _ (Symbol.contDiff_coefficient _) (2 * t)
    (fun x ξ hξ ↦ by
      rw [coefficient_sub, Pi.sub_apply, coefficient_comp, coefficient_inclusion,
        coefficient_const, coefficient_cutoffInverse_comp_coefficient χ a ht hinv hbound hξ,
        sub_self]),
    coefficient_ofBoundedFrequencySupport ..⟩

/-- The cut-off inverse is a right inverse of `a` modulo smoothing symbols: `a ∘ a⁻¹ - 1`
vanishes at the frequencies `‖ξ‖ ≥ 2 t`. -/
theorem isSmoothing_comp_cutoffInverse_sub :
    (a.comp (a.cutoffInverse χ ht hinv hbound) -
      inclusion (add_neg_cancel m).ge (const (ContinuousLinearMap.id ℂ W))).IsSmoothing :=
  isSmoothing_iff.2 fun _ ↦ ⟨ofBoundedFrequencySupport _ (Symbol.contDiff_coefficient _) (2 * t)
    (fun x ξ hξ ↦ by
      rw [coefficient_sub, Pi.sub_apply, coefficient_comp, coefficient_inclusion,
        coefficient_const, coefficient_comp_coefficient_cutoffInverse χ a ht hinv hbound hξ,
        sub_self]),
    coefficient_ofBoundedFrequencySupport ..⟩

/-- If `a` satisfies its estimates uniformly in the position and `‖a(x, ξ)⁻¹‖ ≤ C ⟨ξ⟩ ^ (-m)`
for all positions `x` and all frequencies `‖ξ‖ ≥ t`, then the cut-off inverse satisfies its
estimates uniformly in the position. -/
theorem IsUniform.cutoffInverse {a : Symbol n V W m} (ha : a.IsUniform)
    {hinv : ∀ x ξ, t ≤ ‖ξ‖ → (a.coefficient (x, ξ)).IsInvertible}
    {hbound : ∀ K : Set (CoordinateSpace n), IsCompact K → ∃ C, ∀ x ∈ K, ∀ ξ, t ≤ ‖ξ‖ →
      ‖(a.coefficient (x, ξ)).inverse‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ (-m / 2)}
    (hbound' : ∃ C, ∀ x ξ, t ≤ ‖ξ‖ →
      ‖(a.coefficient (x, ξ)).inverse‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ (-m / 2)) :
    (a.cutoffInverse χ ht hinv hbound).IsUniform := isUniform_iff.2 fun α β ↦ by
  obtain ⟨C, hC0, hC⟩ := exists_norm_mixedDeriv_cutoff_smul_inverse_le a.contDiff_coefficient χ
    ht (K := Set.univ) (fun x _ ξ hξ ↦ hinv x ξ hξ)
    (hbound'.imp fun _ hC x _ ξ hξ ↦ hC x ξ hξ)
    (fun α β ↦ (isUniform_iff.1 ha α β).imp fun _ hC x _ ξ _ ↦ hC.2 x ξ) α β
  exact ⟨C, hC0, fun x ξ ↦ hC x (Set.mem_univ x) ξ⟩

end Symbol

end TauCeti
