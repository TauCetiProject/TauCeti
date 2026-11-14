/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Symbol.Classical
public import TauCeti.Analysis.Pseudodifferential.Symbol.Frequency
import TauCeti.Analysis.Calculus.ContinuousLinearMapInverse
import TauCeti.Analysis.Normed.Operator.CompactFamily
import TauCeti.Analysis.SpecialFunctions.JapaneseBracket.Peetre

/-!
# Pullback of symbols along fibrewise linear maps

Let `κ : ℝⁿ → ℝⁿ` be a smooth map of the positions and `M` a smooth family of invertible linear maps
`M x : ℝⁿ → ℝⁿ` of the frequencies. This file shows that the pullback

`(x, ξ) ↦ a(κ x, M x ξ)`

of a symbol `a ∈ S^m_{1,0}` is again a symbol of order `m`, and that pulling back preserves
classical symbols, acting on their homogeneous terms. For a diffeomorphism `κ` and
`M x = (Dκ(x)ᵀ)⁻¹` the map `(x, ξ) ↦ (κ x, M x ξ)` is the cotangent lift of `κ`, which sends a
covector `ξ` at `x` to the covector at `κ x` that it becomes under `κ`. Pulling back along it is
how the principal symbol of a pseudodifferential operator changes under a change of coordinates,
so that the principal symbol is a function on the cotangent bundle. In contrast to a linear change
of coordinates, `M x` depends on the position, so position derivatives of the pullback also fall
on `M x ξ` and produce a factor `ξ`. Such a term still has order `m`, since it multiplies a
frequency derivative of `a`, of order `m - 1`.

## Main declarations

* `TauCeti.Symbol.pullback κ M`: the pullback, a linear map `S^m_{1,0} → S^m_{1,0}`, with
  `TauCeti.Symbol.pullback_pullback` (pulling back twice), `TauCeti.Symbol.pullback_comp` (it
  commutes with the pointwise composition of symbols) and `TauCeti.Symbol.IsSmoothing.pullback`.
* `TauCeti.HomogeneousSymbol.isSmoothing_pullback_cutoffSymbol_sub_cutoffSymbol_pullback`: pulling
  back the cut-off term `χ(ξ) a(x, ξ)` gives the cut-off term of the pulled back homogeneous
  symbol `TauCeti.HomogeneousSymbol.pullback`, up to a smoothing symbol.
* `TauCeti.Symbol.isSmoothing_of_forall_isCompact_coefficient_eq_zero`: a symbol vanishing, for
  positions in each compact set, at all large enough frequencies is smoothing.
* `TauCeti.ClassicalSymbol.pullback κ M`: the pullback of a classical symbol, whose homogeneous
  terms are the pullbacks of those of `a` (`TauCeti.ClassicalSymbol.term_pullback`); its principal
  symbol is the pullback of the principal symbol (`TauCeti.ClassicalSymbol.principal_pullback`), and
  it preserves ellipticity (`TauCeti.ClassicalSymbol.IsElliptic.pullback`).

## Implementation notes

The symbol estimates are proved for the functions `(x, ξ) ↦ c(x) b(κ x, M x ξ)` with a smooth
scalar function `c` and a symbol `b` of any order, by induction on the number of derivatives. A
frequency derivative of such a function is a combination of the same functions for the frequency
derivatives of `b`, of order one less. A position derivative is a combination of the same functions
for `b`, for its position derivatives and for the symbols `η_i ∂_{η_l} b(y, η)`, all of the order of
`b`: writing `(D_{x_j} M x) ξ = (D_{x_j} M x ∘ (M x)⁻¹)(M x ξ)` makes the coefficients functions of
the position alone. The growth bound of `b` at `(κ x, M x ξ)` ends the induction, since `⟨M x ξ⟩`
and `⟨ξ⟩` are comparable uniformly for `x` in a compact set.

## References

* M. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI* (2008), Lecture I, §8,
  (8.1)–(8.3).
* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, §18.1.
-/

public section

noncomputable section

open scoped ContDiff

namespace TauCeti

variable {n : ℕ} {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W]
  [NormedSpace ℂ W] {m : ℝ} {κ : CoordinateSpace n → CoordinateSpace n}
  {M : CoordinateSpace n → CoordinateSpace n →L[ℝ] CoordinateSpace n}

namespace Symbol

/-- A symbol is smoothing if, for positions in each compact set, it vanishes at all large enough
frequencies. Unlike `TauCeti.Symbol.isSmoothing_of_coefficient_eq_zero`, the frequency radius may
grow with the compact set, as for the difference `(χ(M(x) ξ) - χ(ξ)) a(x, ξ)` of two cutoffs
related by a position-dependent linear change of frequency. -/
theorem isSmoothing_of_forall_isCompact_coefficient_eq_zero {a : Symbol n V W m}
    (ha : ∀ K : Set (CoordinateSpace n), IsCompact K →
      ∃ R, ∀ x ∈ K, ∀ ξ, R ≤ ‖ξ‖ → a.coefficient (x, ξ) = 0) :
    a.IsSmoothing := by
  refine isSmoothing_iff.2 fun m' => ⟨⟨a.coefficient, a.contDiff_coefficient, fun K hK α β => ?_⟩,
    rfl⟩
  -- The radius for the unit neighbourhood of `K` makes every mixed derivative vanish at larger
  -- frequencies over `K`; on `K ×ˢ closedBall 0 R` the derivative divided by the weight is
  -- continuous, hence bounded.
  obtain ⟨R, hR⟩ := ha _ (hK.cthickening (r := 1))
  have hw : Continuous fun p : CoordinateSpace n × CoordinateSpace n =>
      (1 + ‖p.2‖ ^ 2) ^ ((m' - β.length) / 2) :=
    (continuous_const.add (continuous_snd.norm.pow 2)).rpow_const fun p =>
      Or.inl (by positivity : (0 : ℝ) < 1 + ‖p.2‖ ^ 2).ne'
  have hKR := hK.prod (isCompact_closedBall (0 : CoordinateSpace n) R)
  obtain ⟨C, hC⟩ := hKR.exists_bound_of_continuousOn
    ((a.contDiff_coefficient.mixedDeriv α β).continuous.norm.div hw
      fun p => (rpow_weight_pos p.2 _).ne').continuousOn
  refine ⟨max C 0, le_max_right _ _, fun x hx ξ => ?_⟩
  rcases le_or_gt ‖ξ‖ R with hξ | hξ
  · have h := (le_abs_self _).trans ((hC (x, ξ) ⟨hx, mem_closedBall_zero_iff.2 hξ⟩).trans
      (le_max_left C 0))
    rwa [Pi.div_apply, div_le_iff₀ (rpow_weight_pos ξ _)] at h
  · have hzero : (fun y => coordinateDeriv β (fun η => a.coefficient (y, η)) ξ) =ᶠ[nhds x] 0 := by
      filter_upwards [Metric.ball_mem_nhds x one_pos] with y hy
      have hy' : (fun η => a.coefficient (y, η)) =ᶠ[nhds ξ] 0 :=
        Filter.eventually_of_mem ((isOpen_lt continuous_const continuous_norm).mem_nhds hξ)
          fun η hη => hR y (Metric.mem_cthickening_of_dist_le y x 1 K hx
            (Metric.mem_ball.1 hy).le) η (le_of_lt hη)
      rw [(hy'.coordinateDeriv β).eq_of_nhds, coordinateDeriv_zero]
      rfl
    rw [mixedDeriv_def, (hzero.coordinateDeriv α).eq_of_nhds, coordinateDeriv_zero, Pi.zero_apply,
      norm_zero]
    exact mul_nonneg (le_max_right _ _) (rpow_weight_pos ξ _).le

section Estimates

/-- The functions `(x, ξ) ↦ c(x) b(κ x, M x ξ)`, for a smooth scalar function `c` and a symbol `b`,
in terms of which the derivatives of a pulled back symbol are computed. -/
private def pullbackTerm (κ : CoordinateSpace n → CoordinateSpace n)
    (M : CoordinateSpace n → CoordinateSpace n →L[ℝ] CoordinateSpace n)
    (c : CoordinateSpace n → ℝ) {m : ℝ} (b : Symbol n V W m) :
    CoordinateSpace n × CoordinateSpace n → V →L[ℂ] W :=
  fun p ↦ c p.1 • b.coefficient (κ p.1, M p.1 p.2)

private theorem pullbackTerm_one {m : ℝ} (b : Symbol n V W m) :
    pullbackTerm κ M (fun _ ↦ 1) b = fun p ↦ b.coefficient (κ p.1, M p.1 p.2) :=
  funext fun _ ↦ one_smul ℝ _

private theorem contDiff_pullbackMap (hκ : ContDiff ℝ ∞ κ) (hM : ContDiff ℝ ∞ M) :
    ContDiff ℝ ∞ fun p : CoordinateSpace n × CoordinateSpace n ↦ (κ p.1, M p.1 p.2) :=
  (hκ.comp contDiff_fst).prodMk ((hM.comp contDiff_fst).clm_apply contDiff_snd)

private theorem contDiff_pullbackTerm (hκ : ContDiff ℝ ∞ κ) (hM : ContDiff ℝ ∞ M)
    {c : CoordinateSpace n → ℝ} (hc : ContDiff ℝ ∞ c) {m : ℝ} (b : Symbol n V W m) :
    ContDiff ℝ ∞ (pullbackTerm κ M c b) :=
  (hc.comp contDiff_fst).smul (b.contDiff_coefficient.comp (contDiff_pullbackMap hκ hM))

/-- The chain rule for `(x, ξ) ↦ c(x) b(κ x, M x ξ)`. -/
private theorem fderiv_pullbackTerm_apply (hκ : ContDiff ℝ ∞ κ) (hM : ContDiff ℝ ∞ M)
    {c : CoordinateSpace n → ℝ} (hc : ContDiff ℝ ∞ c) {m : ℝ} (b : Symbol n V W m)
    (x ξ : CoordinateSpace n) (v : CoordinateSpace n × CoordinateSpace n) :
    fderiv ℝ (pullbackTerm κ M c b) (x, ξ) v =
      fderiv ℝ c x v.1 • b.coefficient (κ x, M x ξ) +
        c x • fderiv ℝ b.coefficient (κ x, M x ξ)
          (fderiv ℝ κ x v.1, fderiv ℝ M x v.1 ξ + M x v.2) := by
  have hfst := hasFDerivAt_fst (𝕜 := ℝ) (p := (x, ξ))
  have hc' := (hc.differentiable (by simp) x).hasFDerivAt.comp (x, ξ) hfst
  have hκ' := (hκ.differentiable (by simp) x).hasFDerivAt.comp (x, ξ) hfst
  have hM' := ((hM.differentiable (by simp) x).hasFDerivAt.comp (x, ξ) hfst).clm_apply
    (hasFDerivAt_snd (𝕜 := ℝ) (p := (x, ξ)))
  have hb := (b.contDiff_coefficient.differentiable (by simp) (κ x, M x ξ)).hasFDerivAt.comp (x, ξ)
    (hκ'.prodMk hM')
  -- `pullbackTerm κ M c b` is the product `(c ∘ fst) • (b ∘ (κ ∘ fst, M ∘ fst ⬝ snd))`.
  have h : HasFDerivAt (pullbackTerm κ M c b) _ (x, ξ) := hc'.smul hb
  rw [h.fderiv]
  simp [add_comm]

/-- A frequency derivative of `c(x) b(κ x, M x ξ)`: the chain rule through `M x` turns it into a
combination of the frequency derivatives of `b`, of one order less. -/
private theorem coordinateDeriv_snd_pullbackTerm (hκ : ContDiff ℝ ∞ κ) (hM : ContDiff ℝ ∞ M)
    {c : CoordinateSpace n → ℝ} (hc : ContDiff ℝ ∞ c) {m : ℝ} (b : Symbol n V W m) (j : Fin n)
    (x ξ : CoordinateSpace n) :
    coordinateDeriv [j] (fun η ↦ pullbackTerm κ M c b (x, η)) ξ =
      ∑ l, pullbackTerm κ M (fun y ↦ c y * M y (EuclideanSpace.single j 1) l)
        (frequencyDeriv l b) (x, ξ) := by
  rw [coordinateDeriv_snd_eq_fderiv (p := (x, ξ))
      ((contDiff_pullbackTerm hκ hM hc b).differentiable (by simp) _),
    fderiv_pullbackTerm_apply hκ hM hc b,
    fderiv_apply_eq_sum_coordinateDeriv (b.contDiff_coefficient.differentiable (by simp) _)]
  simp [pullbackTerm, Finset.smul_sum, smul_smul]

/-- A position derivative of `c(x) b(κ x, M x ξ)`. Besides the derivative of `c` and the position
derivatives of `b`, it has the terms `⟪D_{x_j} M x ξ, ∂_ξ⟫ b`; writing
`D_{x_j} M x ξ = (D_{x_j} M x ∘ (M x)⁻¹) (M x ξ)`, these are combinations of the symbols
`η_i ∂_{η_l} b(y, η)` of the same order as `b`, evaluated at `(κ x, M x ξ)`. -/
private theorem coordinateDeriv_fst_pullbackTerm (hκ : ContDiff ℝ ∞ κ) (hM : ContDiff ℝ ∞ M)
    (hMinv : ∀ x, (M x).IsInvertible) {c : CoordinateSpace n → ℝ} (hc : ContDiff ℝ ∞ c) {m : ℝ}
    (b : Symbol n V W m) (j : Fin n) (x ξ : CoordinateSpace n) :
    coordinateDeriv [j] (fun y ↦ pullbackTerm κ M c b (y, ξ)) x =
      pullbackTerm κ M (coordinateDeriv [j] c) b (x, ξ) +
      ∑ l, pullbackTerm κ M (fun y ↦ c y * fderiv ℝ κ y (EuclideanSpace.single j 1) l)
        (spatialDeriv l b) (x, ξ) +
      ∑ l, ∑ i, pullbackTerm κ M (fun y ↦ c y *
          ((fderiv ℝ M y (EuclideanSpace.single j 1)).comp (M y).inverse
            (EuclideanSpace.single i 1)) l)
        ((frequencyDeriv l b).comp (ofInner (EuclideanSpace.single i 1))) (x, ξ) := by
  have hN : fderiv ℝ M x (EuclideanSpace.single j 1) ξ = ∑ i, (M x ξ) i •
      (fderiv ℝ M x (EuclideanSpace.single j 1)).comp (M x).inverse
        (EuclideanSpace.single i 1) := by
    rw [← ContinuousLinearMap.apply_eq_sum_single, ContinuousLinearMap.comp_apply,
      (hMinv x).inverse_apply_self]
  rw [coordinateDeriv_fst_eq_fderiv (p := (x, ξ))
      ((contDiff_pullbackTerm hκ hM hc b).differentiable (by simp) _),
    fderiv_pullbackTerm_apply hκ hM hc b,
    fderiv_apply_eq_sum_coordinateDeriv (b.contDiff_coefficient.differentiable (by simp) _)]
  simp only [map_zero, add_zero, hN]
  simp [pullbackTerm, coordinateDeriv_cons, Finset.smul_sum, Finset.sum_smul, smul_smul, add_assoc,
    EuclideanSpace.inner_single_right, mul_comm, mul_left_comm]

/-- **The symbol estimates of a pullback.** Every mixed derivative `∂_x^α ∂_ξ^β` of
`c(x) b(κ x, M x ξ)` is bounded by `C ⟨ξ⟩ ^ (m - |β|)` for positions in a compact set. By the chain
rule (`coordinateDeriv_snd_pullbackTerm`, `coordinateDeriv_fst_pullbackTerm`) a derivative of such
a function is a finite sum of functions of the same kind, built from symbols of order `m - 1` for a
frequency derivative and of order `m` for a position derivative; the induction on the number of
derivatives ends with the growth bound of `b` and the comparison of `⟨M x ξ⟩` with `⟨ξ⟩`. -/
private theorem exists_norm_mixedDeriv_pullbackTerm_le (hκ : ContDiff ℝ ∞ κ)
    (hM : ContDiff ℝ ∞ M) (hMinv : ∀ x, (M x).IsInvertible) (D : ℕ) :
    ∀ {m : ℝ} (b : Symbol n V W m) {c : CoordinateSpace n → ℝ}, ContDiff ℝ ∞ c →
      ∀ α β : List (Fin n), α.length + β.length = D → ∀ {K : Set (CoordinateSpace n)},
        IsCompact K → ∃ C, 0 ≤ C ∧ ∀ x ∈ K, ∀ ξ,
          ‖mixedDeriv α β (pullbackTerm κ M c b) x ξ‖ ≤
            C * (1 + ‖ξ‖ ^ 2) ^ ((m - β.length) / 2) := by
  have hDκ : ContDiff ℝ ∞ (fderiv ℝ κ) := (contDiff_infty_iff_fderiv.1 hκ).2
  have hDM : ContDiff ℝ ∞ (fderiv ℝ M) := (contDiff_infty_iff_fderiv.1 hM).2
  have hinv : ContDiff ℝ ∞ fun y ↦ (M y).inverse :=
    contDiff_iff_contDiffAt.2 fun y ↦ ContDiffAt.clm_inverse hM.contDiffAt (hMinv y)
  induction D with
  | zero =>
    intro m b c hc α β hD K hK
    obtain ⟨rfl, rfl⟩ : α = [] ∧ β = [] := by simpa [List.length_eq_zero_iff] using hD
    obtain ⟨A, hA⟩ := hK.exists_bound_of_continuousOn hc.continuous.continuousOn
    obtain ⟨B, hB⟩ := b.exists_norm_coefficient_le _ (hK.image hκ.continuous)
    obtain ⟨c₀, hc₀, hM₀⟩ := hK.exists_norm_apply_le_mul_norm_and_norm_le_mul_norm_apply M
      (fun x _ ↦ hM.continuous.continuousAt) fun x _ ↦ hMinv x
    refine ⟨|A| * |B| * c₀ ^ |m|, by positivity, fun x hx ξ ↦ ?_⟩
    rw [mixedDeriv_nil_nil, List.length_nil, Nat.cast_zero, sub_zero]
    calc ‖pullbackTerm κ M c b (x, ξ)‖ = ‖c x‖ * ‖b.coefficient (κ x, M x ξ)‖ := norm_smul _ _
      _ ≤ |A| * (|B| * (1 + ‖M x ξ‖ ^ 2) ^ (m / 2)) := by
          gcongr
          · exact (hA x hx).trans (le_abs_self A)
          · exact (hB _ (Set.mem_image_of_mem κ hx) _).trans (by gcongr; exact le_abs_self B)
      _ ≤ |A| * (|B| * (c₀ ^ |m| * (1 + ‖ξ‖ ^ 2) ^ (m / 2))) := by
          gcongr
          exact one_add_norm_sq_rpow_le_of_norm_le_mul hc₀ m (hM₀ x hx ξ).1 (hM₀ x hx ξ).2
      _ = |A| * |B| * c₀ ^ |m| * (1 + ‖ξ‖ ^ 2) ^ (m / 2) := by ring
  | succ D ih =>
    intro m b c hc α β hD K hK
    have hF := contDiff_pullbackTerm hκ hM hc b
    rcases List.eq_nil_or_concat' β with rfl | ⟨β, j, rfl⟩
    · rcases List.eq_nil_or_concat' α with rfl | ⟨α, j, rfl⟩
      · simp at hD
      have hlen : α.length + ([] : List (Fin n)).length = D := by simpa using hD
      -- A position derivative: the derivative of `c`, the position derivatives of `b`, and the
      -- symbols `η_i ∂_{η_l} b` of order `m - 1 + 1`.
      have hc₁ : ContDiff ℝ ∞ (coordinateDeriv [j] c) := hc.coordinateDeriv [j]
      have hc₂ (l : Fin n) : ContDiff ℝ ∞ fun y ↦
          c y * fderiv ℝ κ y (EuclideanSpace.single j 1) l :=
        hc.mul (contDiff_euclidean.1 (hDκ.clm_apply contDiff_const) l)
      have hc₃ (l i : Fin n) : ContDiff ℝ ∞ fun y ↦ c y *
          ((fderiv ℝ M y (EuclideanSpace.single j 1)).comp (M y).inverse
            (EuclideanSpace.single i 1)) l :=
        hc.mul (contDiff_euclidean.1
          (((hDM.clm_apply contDiff_const).clm_comp hinv).clm_apply contDiff_const) l)
      set F₂ : CoordinateSpace n × CoordinateSpace n → V →L[ℂ] W := fun q ↦ ∑ l, pullbackTerm κ M
        (fun y ↦ c y * fderiv ℝ κ y (EuclideanSpace.single j 1) l) (spatialDeriv l b) q
      set F₃ : CoordinateSpace n × CoordinateSpace n → V →L[ℂ] W := fun q ↦ ∑ l, ∑ i,
        pullbackTerm κ M (fun y ↦ c y * ((fderiv ℝ M y (EuclideanSpace.single j 1)).comp
          (M y).inverse (EuclideanSpace.single i 1)) l)
        ((frequencyDeriv l b).comp (ofInner (EuclideanSpace.single i 1))) q
      have hF₂ : ContDiff ℝ ∞ F₂ := ContDiff.sum fun l _ ↦ contDiff_pullbackTerm hκ hM (hc₂ l) _
      have hF₃ : ContDiff ℝ ∞ F₃ :=
        ContDiff.sum fun l _ ↦ ContDiff.sum fun i _ ↦ contDiff_pullbackTerm hκ hM (hc₃ l i) _
      have hfun : (fun q : CoordinateSpace n × CoordinateSpace n ↦
          coordinateDeriv [j] (fun y ↦ pullbackTerm κ M c b (y, q.2)) q.1) =
            pullbackTerm κ M (coordinateDeriv [j] c) b + (F₂ + F₃) := by
        funext q
        rw [Pi.add_apply, Pi.add_apply, coordinateDeriv_fst_pullbackTerm hκ hM hMinv hc b j q.1 q.2,
          add_assoc]
      have h₂ := exists_norm_mixedDeriv_sum_le (α := α) (β := []) (K := K)
        (ρ := fun ξ ↦ (1 + ‖ξ‖ ^ 2) ^ ((m - ([] : List (Fin n)).length) / 2)) Finset.univ
        (fun l _ ↦ contDiff_pullbackTerm hκ hM (hc₂ l) _)
        fun l _ ↦ ih (spatialDeriv l b) (hc₂ l) α [] hlen hK
      have h₃ := exists_norm_mixedDeriv_sum_le (α := α) (β := []) (K := K)
        (ρ := fun ξ ↦ (1 + ‖ξ‖ ^ 2) ^ ((m - ([] : List (Fin n)).length) / 2)) Finset.univ
        (fun l _ ↦ ContDiff.sum fun i _ ↦ contDiff_pullbackTerm hκ hM (hc₃ l i) _)
        fun l _ ↦ exists_norm_mixedDeriv_sum_le Finset.univ
          (fun i _ ↦ contDiff_pullbackTerm hκ hM (hc₃ l i) _)
          fun i _ ↦ (ih ((frequencyDeriv l b).comp (ofInner (EuclideanSpace.single i 1))) (hc₃ l i)
            α [] hlen hK).imp fun C hC ↦
              ⟨hC.1, fun x hx ξ ↦ (hC.2 x hx ξ).trans_eq (by rw [sub_add_cancel])⟩
      obtain ⟨C, hC0, hC⟩ := exists_norm_mixedDeriv_add_le (contDiff_pullbackTerm hκ hM hc₁ b)
        (hF₂.add hF₃) (ih b hc₁ α [] hlen hK) (exists_norm_mixedDeriv_add_le hF₂ hF₃ h₂ h₃)
      refine ⟨C, hC0, fun x hx ξ ↦ ?_⟩
      rw [← mixedDeriv_coordinateDeriv_fst hF, hfun]
      exact hC x hx ξ
    · have hlen : α.length + β.length = D := by
        simp only [List.length_append, List.length_singleton] at hD
        omega
      -- A frequency derivative: the frequency derivatives of `b`, of order `m - 1`.
      have hc' (l : Fin n) : ContDiff ℝ ∞ fun y ↦ c y * M y (EuclideanSpace.single j 1) l :=
        hc.mul (contDiff_euclidean.1 (hM.clm_apply contDiff_const) l)
      have hfun : (fun q : CoordinateSpace n × CoordinateSpace n ↦
          coordinateDeriv [j] (fun η ↦ pullbackTerm κ M c b (q.1, η)) q.2) =
            fun q ↦ ∑ l, pullbackTerm κ M (fun y ↦ c y * M y (EuclideanSpace.single j 1) l)
              (frequencyDeriv l b) q :=
        funext fun q ↦ coordinateDeriv_snd_pullbackTerm hκ hM hc b j q.1 q.2
      obtain ⟨C, hC0, hC⟩ := exists_norm_mixedDeriv_sum_le (α := α) (β := β) (K := K) Finset.univ
        (fun l _ ↦ contDiff_pullbackTerm hκ hM (hc' l) _)
        fun l _ ↦ ih (frequencyDeriv l b) (hc' l) α β hlen hK
      refine ⟨C, hC0, fun x hx ξ ↦ ?_⟩
      rw [← mixedDeriv_coordinateDeriv_snd, hfun, ← order_sub_one_sub_length]
      exact hC x hx ξ

end Estimates

section Pullback

variable (κ M) in
/-- The **pullback** `(x, ξ) ↦ a(κ x, M x ξ)` of a symbol of order `m` along a smooth map `κ` of the
positions and a smooth family `M` of invertible linear maps of the frequencies, again a symbol of
order `m`. For a diffeomorphism `κ` and `M x = (Dκ(x)ᵀ)⁻¹` this is the composition with the
cotangent lift of `κ`, which maps the covector `ξ` at `x` to the covector `(Dκ(x)ᵀ)⁻¹ ξ` at `κ x`:
the change of coordinates of the principal symbol of a pseudodifferential operator. -/
def pullback (hκ : ContDiff ℝ ∞ κ) (hM : ContDiff ℝ ∞ M) (hMinv : ∀ x, (M x).IsInvertible) :
    Symbol n V W m →ₗ[ℂ] Symbol n V W m where
  toFun a :=
    { coefficient := fun p ↦ a.coefficient (κ p.1, M p.1 p.2)
      contDiff_coefficient := a.contDiff_coefficient.comp (contDiff_pullbackMap hκ hM)
      exists_bound := fun K hK α β ↦ by
        rw [← pullbackTerm_one]
        exact exists_norm_mixedDeriv_pullbackTerm_le hκ hM hMinv _ a contDiff_const α β rfl hK }
  map_add' a b := Symbol.ext <| funext fun p ↦ by simp
  map_smul' c a := Symbol.ext <| funext fun p ↦ by simp

variable (hκ : ContDiff ℝ ∞ κ) (hM : ContDiff ℝ ∞ M) (hMinv : ∀ x, (M x).IsInvertible)

@[simp]
theorem coefficient_pullback (a : Symbol n V W m) (p : CoordinateSpace n × CoordinateSpace n) :
    (pullback κ M hκ hM hMinv a).coefficient p = a.coefficient (κ p.1, M p.1 p.2) :=
  (rfl)

/-- Pulling back along the identity and the identity family is the identity. -/
@[simp]
theorem pullback_id (hκ : ContDiff ℝ ∞ (id : CoordinateSpace n → CoordinateSpace n))
    (hM : ContDiff ℝ ∞ fun _ : CoordinateSpace n ↦ ContinuousLinearMap.id ℝ (CoordinateSpace n))
    (hMinv : ∀ _ : CoordinateSpace n, (ContinuousLinearMap.id ℝ (CoordinateSpace n)).IsInvertible)
    (a : Symbol n V W m) : pullback id (fun _ ↦ ContinuousLinearMap.id ℝ _) hκ hM hMinv a = a :=
  (rfl)

/-- Pulling back along `(κ₁, M₁)` and then along `(κ₂, M₂)` is pulling back along
`(κ₁ ∘ κ₂, x ↦ M₁ (κ₂ x) ∘ M₂ x)`. -/
theorem pullback_pullback {κ₁ κ₂ : CoordinateSpace n → CoordinateSpace n}
    {M₁ M₂ : CoordinateSpace n → CoordinateSpace n →L[ℝ] CoordinateSpace n}
    (hκ₁ : ContDiff ℝ ∞ κ₁) (hM₁ : ContDiff ℝ ∞ M₁) (hM₁inv : ∀ x, (M₁ x).IsInvertible)
    (hκ₂ : ContDiff ℝ ∞ κ₂) (hM₂ : ContDiff ℝ ∞ M₂) (hM₂inv : ∀ x, (M₂ x).IsInvertible)
    (a : Symbol n V W m) :
    pullback κ₂ M₂ hκ₂ hM₂ hM₂inv (pullback κ₁ M₁ hκ₁ hM₁ hM₁inv a) =
      pullback (κ₁ ∘ κ₂) (fun x ↦ (M₁ (κ₂ x)).comp (M₂ x)) (hκ₁.comp hκ₂)
        ((hM₁.comp hκ₂).clm_comp hM₂) (fun x ↦ (hM₁inv (κ₂ x)).comp (hM₂inv x)) a :=
  (rfl)

/-- Pulling back commutes with the pointwise composition of symbols. -/
@[simp]
theorem pullback_comp {U : Type*} [NormedAddCommGroup U] [NormedSpace ℂ U] {m' : ℝ}
    (b : Symbol n W U m') (a : Symbol n V W m) :
    pullback κ M hκ hM hMinv (b.comp a) =
      (pullback κ M hκ hM hMinv b).comp (pullback κ M hκ hM hMinv a) :=
  Symbol.ext <| funext fun p ↦ by simp [coefficient_comp]

/-- Pulling back commutes with the inclusion of a symbol class into one of larger order. -/
@[simp]
theorem pullback_inclusion {m' : ℝ} (h : m ≤ m') (a : Symbol n V W m) :
    pullback κ M hκ hM hMinv (inclusion h a) = inclusion h (pullback κ M hκ hM hMinv a) :=
  Symbol.ext <| funext fun p ↦ by simp

/-- The pullback of a smoothing symbol is smoothing. -/
theorem IsSmoothing.pullback {a : Symbol n V W m} (ha : a.IsSmoothing) :
    (Symbol.pullback κ M hκ hM hMinv a).IsSmoothing := isSmoothing_iff.2 fun m' ↦ by
  obtain ⟨b, hb⟩ := isSmoothing_iff.1 ha m'
  exact ⟨Symbol.pullback κ M hκ hM hMinv b, funext fun p ↦ by simp [hb]⟩

end Pullback

end Symbol

namespace HomogeneousSymbol

/-- **Change of cutoff under a pullback.** On `ℝⁿ`, pulling back the cut-off term `χ(ξ) a(x, ξ)`
gives `χ(M x ξ) a(κ x, M x ξ)`, which differs from the cut-off term `χ(ξ) a(κ x, M x ξ)` of the
pulled back homogeneous symbol by a smoothing symbol: on a compact set of positions `M x` changes
the norm of a frequency by a bounded factor, so both cutoffs are `1` at all large frequencies. -/
theorem isSmoothing_pullback_cutoffSymbol_sub_cutoffSymbol_pullback
    {κ : CoordinateSpace n → CoordinateSpace n}
    {M : CoordinateSpace n → CoordinateSpace n →L[ℝ] CoordinateSpace n}
    (hκ : ContDiff ℝ ∞ κ) (hM : ContDiff ℝ ∞ M) (hMinv : ∀ x, (M x).IsInvertible)
    (χ : FrequencyCutoff (CoordinateSpace n))
    (a : HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W m) :
    (Symbol.pullback κ M hκ hM hMinv (cutoffSymbol χ a) -
      cutoffSymbol χ (a.pullback κ M hκ hM fun x ↦ (hMinv x).injective)).IsSmoothing := by
  refine Symbol.isSmoothing_of_forall_isCompact_coefficient_eq_zero fun K hK ↦ ?_
  obtain ⟨c, hc, hcK⟩ := hK.exists_norm_apply_le_mul_norm_and_norm_le_mul_norm_apply M
    (fun x _ ↦ hM.continuous.continuousAt) fun x _ ↦ hMinv x
  refine ⟨2 * c, fun x hx ξ hξ ↦ ?_⟩
  have h₁ : 2 ≤ ‖ξ‖ := le_trans (by linarith) hξ
  have h₂ : 2 ≤ ‖M x ξ‖ := by
    have := (hcK x hx ξ).2
    nlinarith
  simp [χ.apply_eq_one_of_two_le_norm h₁, χ.apply_eq_one_of_two_le_norm h₂]

end HomogeneousSymbol

namespace ClassicalSymbol

variable (hκ : ContDiff ℝ ∞ κ) (hM : ContDiff ℝ ∞ M) (hMinv : ∀ x, (M x).IsInvertible)

/-- The remainder of a pulled back classical symbol after `N` terms has order `m - N`. -/
private theorem exists_remainder_pullback (a : ClassicalSymbol n V W m)
    (χ : FrequencyCutoff (CoordinateSpace n)) (N : ℕ) :
    ∃ r : Symbol n V W (m - N), ∀ p, r.coefficient p =
      (Symbol.pullback κ M hκ hM hMinv a.toSymbol).coefficient p - ∑ j ∈ Finset.range N,
        χ p.2 • ((a.term j).pullback κ M hκ hM fun x ↦ (hMinv x).injective).coefficient p := by
  -- Pulling back `a = r_N + ∑_{j<N} χ(ξ) a_{m-j}` gives the pullback of `r_N`, of order `m - N`,
  -- plus the terms `χ(M x ξ) a_{m-j}(κ x, M x ξ)`, each of which differs from
  -- `χ(ξ) a_{m-j}(κ x, M x ξ)` by a smoothing symbol.
  choose s hs using fun j ↦ Symbol.isSmoothing_iff.1
    (HomogeneousSymbol.isSmoothing_pullback_cutoffSymbol_sub_cutoffSymbol_pullback hκ hM hMinv χ
      (a.term j)) (m - N)
  refine ⟨Symbol.pullback κ M hκ hM hMinv (a.remainder χ N) + ∑ j ∈ Finset.range N, s j,
    fun p ↦ ?_⟩
  have h := congrArg (fun s ↦ (Symbol.pullback κ M hκ hM hMinv s).coefficient p)
    (a.inclusion_remainder χ N)
  simp only [map_sub, map_sum, Symbol.pullback_inclusion, Symbol.coefficient_inclusion,
    Symbol.coefficient_sub, Symbol.coefficient_sum, Pi.sub_apply, Finset.sum_apply] at h
  simp only [Symbol.coefficient_add, Symbol.coefficient_sum, Pi.add_apply, Finset.sum_apply, hs,
    Symbol.coefficient_sub, Pi.sub_apply, Finset.sum_sub_distrib,
    HomogeneousSymbol.coefficient_cutoffSymbol]
  rw [h]
  abel

variable (κ M) in
/-- The **pullback** `(x, ξ) ↦ a(κ x, M x ξ)` of a classical symbol along a smooth map `κ` of the
positions and a smooth family `M` of invertible linear maps of the frequencies: a classical symbol
of the same order, whose homogeneous terms are the pullbacks of those of `a`. In particular the
principal symbol transforms as a function on the cotangent bundle
(`TauCeti.ClassicalSymbol.principal_pullback`). -/
def pullback : ClassicalSymbol n V W m →ₗ[ℂ] ClassicalSymbol n V W m where
  toFun a :=
    { toSymbol := Symbol.pullback κ M hκ hM hMinv a.toSymbol
      term j := (a.term j).pullback κ M hκ hM fun x ↦ (hMinv x).injective
      exists_remainder' := ⟨default, a.exists_remainder_pullback hκ hM hMinv default⟩ }
  map_add' a b := ext <| by simp
  map_smul' c a := ext <| by simp

@[simp]
theorem toSymbol_pullback (a : ClassicalSymbol n V W m) :
    (pullback κ M hκ hM hMinv a).toSymbol = Symbol.pullback κ M hκ hM hMinv a.toSymbol :=
  (rfl)

@[simp]
theorem term_pullback (a : ClassicalSymbol n V W m) (j : ℕ) :
    (pullback κ M hκ hM hMinv a).term j =
      (a.term j).pullback κ M hκ hM fun x ↦ (hMinv x).injective :=
  (rfl)

/-- **The principal symbol of a pullback** is the pullback of the principal symbol:
`σ(a ∘ (κ, M))(x, ξ) = σ(a)(κ x, M x ξ)`. -/
@[simp]
theorem principal_pullback (a : ClassicalSymbol n V W m) :
    (pullback κ M hκ hM hMinv a).principal =
      a.principal.pullback κ M hκ hM fun x ↦ (hMinv x).injective :=
  HomogeneousSymbol.ext <| funext fun p ↦ by simp

/-- The pullback of an elliptic classical symbol is elliptic. -/
theorem IsElliptic.pullback {a : ClassicalSymbol n V W m} (ha : a.IsElliptic) :
    (ClassicalSymbol.pullback κ M hκ hM hMinv a).IsElliptic := by
  rw [isElliptic_def, principal_pullback]
  exact HomogeneousSymbol.IsElliptic.pullback hκ hM _ (isElliptic_def.1 ha)

end ClassicalSymbol

end TauCeti
