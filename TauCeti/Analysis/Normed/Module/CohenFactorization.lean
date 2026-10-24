/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.SpecificLimits.Normed
public import TauCeti.Analysis.Normed.Module.Unitization
public import TauCeti.Analysis.Normed.Ring.Units

/-!
# Cohen–Hewitt factorization for Banach left modules

Let `A` be a possibly nonunital Banach algebra acting on a Banach space `E` on the left through a
bounded bilinear map `L : A →L[𝕜] E →L[𝕜] E` with `L (a * b) x = L a (L b x)`. The action need not
be contractive or unital. A left approximate identity of `A` is a proper filter `l` on `A` with
`e * a → a` along `l` for every `a`; it is bounded by `C` when `‖e‖ ≤ C` eventually along `l`.

The *essential part* of `E` is the closed linear span of `A · E`. This file proves:

* a bounded left approximate identity converges to the identity pointwise on the essential part,
  and the essential part consists exactly of the points where it does;
* the Cohen–Hewitt factorization theorem: every `x` in the essential part factors as `x = a · y`
  with `‖a‖ ≤ C`, `y` in the closure of `A · x`, and `y` arbitrarily close to `x`;
* consequently `A · E` is already a closed linear subspace: it equals the essential part.

## Implementation notes

The proof is the classical one. Fix `0 < t` with `t * (1 + C) = 1 / 2`. In the `ℓ¹`
unitization `A⁺ = WithLp 1 (Unitization 𝕜 A)` put
`aₙ = (1 - t) ^ n + ∑_{k < n} t (1 - t) ^ k eₖ`, with `eₖ` chosen inductively from the approximate
identity. The identity `aₙ₊₁ = ((1 - t) + t eₙ) aₙ + t (fₙ - eₙ fₙ)`, where `fₙ` is the `A`-part
of `aₙ`, shows that each `aₙ` is invertible with `‖aₙ⁻¹‖ ≤ 4 ^ n`, once `eₙ` nearly fixes `fₙ`.
Choosing `eₙ` to nearly fix `aₙ⁻¹ · x` as well makes `yₙ = aₙ⁻¹ · x` a Cauchy sequence. Its limit
`y` satisfies `a · y = x`, where `a = ∑ₖ t (1 - t) ^ k eₖ` has norm at most `C`.

## Main results

* `ContinuousLinearMap.tendsto_apply_of_mem_topologicalClosure_span` and
  `ContinuousLinearMap.tendsto_apply_iff_mem_topologicalClosure_span`: convergence of a bounded
  left approximate identity on the essential part.
* `ContinuousLinearMap.exists_apply_eq_of_mem_topologicalClosure_span`: the Cohen–Hewitt
  factorization theorem.
* `ContinuousLinearMap.coe_topologicalClosure_span_range_eq`: the essential part is `A · E`.

## References

* H. G. Dales, *Banach Algebras and Automatic Continuity*, Theorem 2.9.24.
* E. Hewitt, *The ranges of certain convolution operators*, Math. Scand. 15 (1964), 147–155.
* P. J. Cohen, *Factorization in group algebras*, Duke Math. J. 26 (1959), 199–205.
-/

public section

open Filter Topology Submodule Unitization WithLp

namespace ContinuousLinearMap

section Essential

variable {𝕜 A E : Type*} [NontriviallyNormedField 𝕜] [NonUnitalNormedRing A] [NormedSpace 𝕜 A]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- A bounded left approximate identity of `A` converges to the identity at every point of the
essential part `closure (span (A · E))` of a left `A`-module `E`. -/
theorem tendsto_apply_of_mem_topologicalClosure_span (L : A →L[𝕜] E →L[𝕜] E)
    (hL : ∀ a b z, L (a * b) z = L a (L b z)) {l : Filter A} {C : ℝ}
    (hC : ∀ᶠ e in l, ‖e‖ ≤ C) (hl : ∀ a, Tendsto (· * a) l (𝓝 a)) {z : E}
    (hz : z ∈ (span 𝕜 (Set.range fun p : A × E ↦ L p.1 p.2)).topologicalClosure) :
    Tendsto (fun e ↦ L e z) l (𝓝 z) := by
  let S : Submodule 𝕜 E :=
    { carrier := {z | Tendsto (fun e ↦ L e z) l (𝓝 z)}
      add_mem' := fun hz hw ↦ by simpa using hz.add hw
      zero_mem' := by simpa using tendsto_const_nhds
      smul_mem' := fun c _ hz ↦ by simpa using hz.const_smul c }
  have hspan : span 𝕜 (Set.range fun p : A × E ↦ L p.1 p.2) ≤ S := by
    rw [span_le]
    rintro _ ⟨⟨a, w⟩, rfl⟩
    have : Tendsto (fun e ↦ L e (L a w)) l (𝓝 (L a w)) := by
      simpa [Function.comp_def, hL] using ((L.flip w).continuous.tendsto a).comp (hl a)
    exact this
  have hclosed : IsClosed (S : Set E) := by
    refine isClosed_of_closure_subset fun z hz ↦ Metric.tendsto_nhds.mpr fun ε hε ↦ ?_
    have hB : 0 < ‖L‖ * |C| + 1 := by positivity
    obtain ⟨s, hs, hzs⟩ := Metric.mem_closure_iff.mp hz (ε / 2 / (‖L‖ * |C| + 1)) (by positivity)
    have hzs' : (‖L‖ * |C| + 1) * dist z s < ε / 2 := by
      rwa [lt_div_iff₀ hB, mul_comm] at hzs
    filter_upwards [hC, Metric.tendsto_nhds.mp hs _ (half_pos hε)] with e he hes
    have hLe : dist (L e z) (L e s) ≤ ‖L‖ * |C| * dist z s := by
      rw [dist_eq_norm, ← map_sub, dist_eq_norm]
      calc ‖L e (z - s)‖ ≤ ‖L‖ * ‖e‖ * ‖z - s‖ := L.le_opNorm₂ e (z - s)
        _ ≤ ‖L‖ * |C| * ‖z - s‖ := by gcongr; exact he.trans (le_abs_self C)
    calc dist (L e z) z ≤ dist (L e z) (L e s) + dist (L e s) s + dist s z := dist_triangle4 ..
      _ < ε := by rw [dist_comm s z]; nlinarith [dist_nonneg (x := z) (y := s)]
  exact topologicalClosure_minimal _ hspan hclosed hz

/-- The essential part `closure (span (A · E))` of a left `A`-module `E` consists exactly of the
points at which a bounded left approximate identity of `A` converges to the identity. -/
theorem tendsto_apply_iff_mem_topologicalClosure_span (L : A →L[𝕜] E →L[𝕜] E)
    (hL : ∀ a b z, L (a * b) z = L a (L b z)) {l : Filter A} [l.NeBot] {C : ℝ}
    (hC : ∀ᶠ e in l, ‖e‖ ≤ C) (hl : ∀ a, Tendsto (· * a) l (𝓝 a)) {z : E} :
    Tendsto (fun e ↦ L e z) l (𝓝 z) ↔
      z ∈ (span 𝕜 (Set.range fun p : A × E ↦ L p.1 p.2)).topologicalClosure :=
  ⟨fun h ↦ (isClosed_topologicalClosure _).mem_of_tendsto h <| .of_forall fun e ↦
      le_topologicalClosure _ <| subset_span ⟨(e, z), rfl⟩,
    tendsto_apply_of_mem_topologicalClosure_span L hL hC hl⟩

end Essential

end ContinuousLinearMap

/-! ### The Cohen–Hewitt construction -/

namespace TauCeti.CohenHewitt

variable {𝕜 A E : Type*} [RCLike 𝕜] [NonUnitalNormedRing A] [NormedSpace 𝕜 A]
  [IsScalarTower 𝕜 A A] [SMulCommClass 𝕜 A A] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

variable [CompleteSpace A]

/-- One step of the Cohen–Hewitt construction. Suppose `a = s + f` is a unit of the `ℓ¹`
unitization with `‖a⁻¹‖ ≤ M`, and `‖τ‖ * (1 + C) ≤ 1 / 2`. Choosing `e` from the approximate
identity so that it nearly fixes both `f` and `a⁻¹ · x`, the element
`a' = (1 - τ) s + (f + τ s e) = ((1 - τ) + τ e) a + τ (f - e f)` is again a unit, with
`‖a'⁻¹‖ ≤ 4 M`, and `a'⁻¹ · x` is within `δ` of `a⁻¹ · x`. -/
private lemma exists_step (L : A →L[𝕜] E →L[𝕜] E) (hL : ∀ a b z, L (a * b) z = L a (L b z))
    {l : Filter A} [l.NeBot] {C : ℝ} (hC : ∀ᶠ e in l, ‖e‖ ≤ C)
    (hl : ∀ a, Tendsto (· * a) l (𝓝 a)) {x : E} (hlx : Tendsto (fun e ↦ L e x) l (𝓝 x))
    {τ s : 𝕜} (hτ : ‖τ‖ * (1 + C) ≤ 1 / 2) (hs : ‖τ * s‖ ≤ 1) {f : A} {M δ : ℝ} (hδ : 0 < δ)
    (hu : IsUnit (toLp 1 (inl s + (f : Unitization 𝕜 A))))
    (hM : ‖Ring.inverse (toLp 1 (inl s + (f : Unitization 𝕜 A)))‖ ≤ M) :
    ∃ e : A, ‖e‖ ≤ C ∧
      IsUnit (toLp 1 (inl ((1 - τ) * s) + ((f + (τ * s) • e : A) : Unitization 𝕜 A))) ∧
      ‖Ring.inverse (toLp 1 (inl ((1 - τ) * s) + ((f + (τ * s) • e : A) : Unitization 𝕜 A)))‖ ≤
        4 * M ∧
      dist (L.unitizationAction hL (Ring.inverse (toLp 1 (inl s + (f : Unitization 𝕜 A)))) x)
        (L.unitizationAction hL (Ring.inverse
          (toLp 1 (inl ((1 - τ) * s) + ((f + (τ * s) • e : A) : Unitization 𝕜 A)))) x) ≤ δ := by
  set ι : Unitization 𝕜 A ≃ₐ[𝕜] WithLp 1 (Unitization 𝕜 A) := (unitizationAlgEquiv 𝕜).symm
  have hι : ∀ u, toLp 1 u = ι u := fun u ↦ (unitizationAlgEquiv_symm_apply 𝕜 u).symm
  set Φ := L.unitizationAction hL
  set a := toLp 1 (inl s + (f : Unitization 𝕜 A))
  set y := Φ (Ring.inverse a) x
  have hM0 : 0 ≤ M := (norm_nonneg _).trans hM
  have hK : 0 < 1 + ‖L‖ := by positivity
  have hη₁ : 0 < 1 / (4 * ‖τ‖ * M + 1) := by positivity
  have hη₂ : 0 < δ / ((1 + ‖L‖) * (4 * M) + 1) := by positivity
  have h₁ : ∀ᶠ e in l, ‖f - e * f‖ < 1 / (4 * ‖τ‖ * M + 1) := by
    simpa [dist_eq_norm, norm_sub_rev] using Metric.tendsto_nhds.mp (hl f) _ hη₁
  have h₂ : ∀ᶠ e in l, ‖y - L e y‖ < δ / ((1 + ‖L‖) * (4 * M) + 1) :=
    (Metric.tendsto_nhds.mp (L.tendsto_apply_unitizationAction hL hl hlx (Ring.inverse a)) _
      hη₂).mono fun e he ↦ by rwa [dist_eq_norm, norm_sub_rev] at he
  obtain ⟨e, heC, he₁, he₂⟩ := (hC.and (h₁.and h₂)).exists
  set a' := toLp 1 (inl ((1 - τ) * s) + ((f + (τ * s) • e : A) : Unitization 𝕜 A))
  /- `a'` is a small perturbation of the unit `(1 - w) * a`, where `‖w‖ ≤ 1 / 2`. -/
  set w := toLp 1 (inl τ + ((-(τ • e) : A) : Unitization 𝕜 A))
  have hkey : a' = (1 - w) * a + toLp 1 ((τ • (f - e * f) : A) : Unitization 𝕜 A) := by
    simp only [a', a, w, hι, ← map_one ι, ← map_sub, ← map_mul, ← map_add]
    congr 1
    ext
    · simp
    · simp [smul_sub, mul_smul, smul_mul_assoc]
      module
  have hw : ‖w‖ ≤ 1 / 2 := by
    simp only [w, unitization_norm_def, Unitization.fst_add, Unitization.fst_inl,
      Unitization.fst_inr, add_zero, Unitization.snd_add, Unitization.snd_inl,
      Unitization.snd_inr, zero_add, norm_neg, norm_smul]
    nlinarith [norm_nonneg τ]
  have hd : ‖toLp 1 ((τ • (f - e * f) : A) : Unitization 𝕜 A)‖ * (2 * M) ≤ 1 / 2 := by
    rw [unitization_norm_inr, norm_smul]
    rw [lt_div_iff₀ (by positivity)] at he₁
    nlinarith [norm_nonneg τ, norm_nonneg (f - e * f),
      mul_nonneg (norm_nonneg τ) (norm_nonneg (f - e * f))]
  obtain ⟨ha', hM''⟩ := hkey ▸ NormedRing.isUnit_one_sub_mul_add_and_norm_inverse_le hu hM hw hd
  refine ⟨e, heC, ha', hM'', ?_⟩
  /- The increment `a'⁻¹ · x - a⁻¹ · x` is `a'⁻¹ · (τ s (y - e · y))`. -/
  have hinv : Ring.inverse a' - Ring.inverse a = Ring.inverse a' * (a - a') * Ring.inverse a :=
    Ring.inverse_sub_inverse ⟨fun _ ↦ hu, fun _ ↦ ha'⟩
  have hdiff : a - a' = toLp 1 ((τ * s) • (1 - (e : Unitization 𝕜 A))) := by
    simp only [a', a, hι, ← map_sub]
    congr 1
    ext
    · simp
      ring
    · simp
  have hincr : Φ (Ring.inverse a') x - y = Φ (Ring.inverse a') ((τ * s) • (y - L e y)) := by
    rw [← sub_apply, ← map_sub, hinv, map_mul, map_mul, mul_apply_eq_comp, mul_apply_eq_comp,
      hdiff, ContinuousLinearMap.unitizationAction_apply L hL
        (toLp 1 ((τ * s) • (1 - (e : Unitization 𝕜 A))))]
    congr 1
    simp [sub_eq_add_neg, y]
  rw [dist_comm, dist_eq_norm, hincr]
  calc ‖Φ (Ring.inverse a') ((τ * s) • (y - L e y))‖
      ≤ (1 + ‖L‖) * ‖Ring.inverse a'‖ * ‖(τ * s) • (y - L e y)‖ :=
        L.norm_unitizationAction_apply_le hL _ _
    _ ≤ (1 + ‖L‖) * (4 * M) * (1 * (δ / ((1 + ‖L‖) * (4 * M) + 1))) := by
        rw [norm_smul]
        gcongr
    _ ≤ δ := by
        rw [one_mul, ← mul_div_assoc, div_le_iff₀ (by positivity)]
        nlinarith [mul_nonneg hK.le hM0]

omit [IsScalarTower 𝕜 A A] [SMulCommClass 𝕜 A A] in
/-- The limit step of the Cohen–Hewitt construction. If `f n → a` in `A` and `y n → y₀` in `E`
geometrically, starting from `f 0 = 0` and `y 0 = x`, and `(1 - τ) ^ n • y n + f n · y n = x` for
all `n` with `‖1 - τ‖ < 1`, then `‖a‖ ≤ C`, `‖y₀ - x‖ ≤ ε / 2` and `a · y₀ = x`. -/
private lemma exists_apply_eq_of_tendsto [CompleteSpace E] (L : A →L[𝕜] E →L[𝕜] E) {x : E}
    {τ : 𝕜} (hτ : ‖1 - τ‖ < 1) {t C ε : ℝ} (ht₀ : 0 < t) {f : ℕ → A} {y : ℕ → E}
    (hf₀ : f 0 = 0) (hy₀ : y 0 = x) (hf : ∀ n, dist (f n) (f (n + 1)) ≤ t * C * (1 - t) ^ n)
    (hy : ∀ n, dist (y n) (y (n + 1)) ≤ ε / 2 / 2 / 2 ^ n)
    (hfac : ∀ n, (1 - τ) ^ n • y n + L (f n) (y n) = x) :
    ∃ a z, ‖a‖ ≤ C ∧ Tendsto y atTop (𝓝 z) ∧ ‖z - x‖ ≤ ε / 2 ∧ L a z = x := by
  obtain ⟨a, ha⟩ := cauchySeq_tendsto_of_complete (cauchySeq_of_le_geometric _ _ (by linarith) hf)
  obtain ⟨z, hz⟩ := cauchySeq_tendsto_of_complete (cauchySeq_of_le_geometric_two hy)
  refine ⟨a, z, ?_, hz, ?_, ?_⟩
  · have := dist_le_of_le_geometric_of_tendsto₀ _ _ (by linarith) hf ha
    rwa [hf₀, dist_zero_left, sub_sub_cancel, mul_div_cancel_left₀ _ ht₀.ne'] at this
  · have := dist_le_of_le_geometric_two_of_tendsto₀ hy hz
    rwa [hy₀, dist_comm, dist_eq_norm] at this
  · have hlim : Tendsto (fun n ↦ (1 - τ) ^ n • y n + L (f n) (y n)) atTop
        (𝓝 ((0 : 𝕜) • z + L a z)) :=
      ((tendsto_pow_atTop_nhds_zero_of_norm_lt_one hτ).smul hz).add
        ((L.continuous₂.tendsto (a, z)).comp (ha.prodMk_nhds hz))
    simp only [hfac, zero_smul, zero_add] at hlim
    exact (tendsto_nhds_unique tendsto_const_nhds hlim).symm

end TauCeti.CohenHewitt

namespace ContinuousLinearMap

open TauCeti.CohenHewitt

variable {𝕜 A E : Type*} [RCLike 𝕜] [NonUnitalNormedRing A] [NormedSpace 𝕜 A]
  [IsScalarTower 𝕜 A A] [SMulCommClass 𝕜 A A] [CompleteSpace A]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]

/-- **Cohen–Hewitt factorization.** Let `A` be a Banach algebra with a left approximate identity
`l` bounded by `C`, acting boundedly on the left of a Banach space `E` through `L`. Every `x` in
the essential part `closure (span (A · E))` factors as `x = L a y` with `‖a‖ ≤ C`, where `y` lies in
the closure of `A · x` and within any prescribed distance `ε` of `x`. -/
theorem exists_apply_eq_of_mem_topologicalClosure_span (L : A →L[𝕜] E →L[𝕜] E)
    (hL : ∀ a b z, L (a * b) z = L a (L b z)) {l : Filter A} [l.NeBot] {C : ℝ}
    (hC : ∀ᶠ e in l, ‖e‖ ≤ C) (hl : ∀ a, Tendsto (· * a) l (𝓝 a)) {x : E}
    (hx : x ∈ (span 𝕜 (Set.range fun p : A × E ↦ L p.1 p.2)).topologicalClosure)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ a y, ‖a‖ ≤ C ∧ y ∈ closure (Set.range fun b ↦ L b x) ∧ ‖y - x‖ < ε ∧ L a y = x := by
  have hlx := tendsto_apply_of_mem_topologicalClosure_span L hL hC hl hx
  set Φ := unitizationAction L hL
  /- Fix `t` with `t * (1 + C) = 1 / 2`. -/
  have hC0 : 0 ≤ C := let ⟨e, he⟩ := hC.exists; (norm_nonneg e).trans he
  set t : ℝ := 1 / (2 * (1 + C)) with ht_def
  have ht0 : 0 < t := by positivity
  have htC : t * (1 + C) = 1 / 2 := by rw [ht_def]; field_simp
  have ht1 : t < 1 := by nlinarith
  set τ : 𝕜 := (t : 𝕜)
  have hτ : ‖τ‖ = t := by simp [τ, ht0.le]
  have hτ' : ‖1 - τ‖ = 1 - t := by
    simp only [τ]
    norm_cast
    exact abs_of_pos (by linarith)
  have hc : ∀ n : ℕ, ‖τ * (1 - τ) ^ n‖ = t * (1 - t) ^ n := fun n ↦ by
    rw [norm_mul, norm_pow, hτ, hτ']
  have hc1 : ∀ n : ℕ, t * (1 - t) ^ n ≤ 1 := fun n ↦ by
    nlinarith [pow_le_one₀ (n := n) (by linarith : (0 : ℝ) ≤ 1 - t) (by linarith),
      pow_nonneg (by linarith : (0 : ℝ) ≤ 1 - t) n]
  /- `a n f = (1 - τ) ^ n + f` in the unitization, and `yy n f = (a n f)⁻¹ · x`. -/
  let a : ℕ → A → WithLp 1 (Unitization 𝕜 A) := fun n f ↦
    toLp 1 (Unitization.inl ((1 - τ) ^ n) + (f : Unitization 𝕜 A))
  let yy : ℕ → A → E := fun n f ↦ Φ (Ring.inverse (a n f)) x
  have step : ∀ n f, ∃ e : A, ‖e‖ ≤ C ∧ (IsUnit (a n f) → ‖Ring.inverse (a n f)‖ ≤ 4 ^ n →
      IsUnit (a (n + 1) (f + (τ * (1 - τ) ^ n) • e)) ∧
      ‖Ring.inverse (a (n + 1) (f + (τ * (1 - τ) ^ n) • e))‖ ≤ 4 ^ (n + 1) ∧
      dist (yy n f) (yy (n + 1) (f + (τ * (1 - τ) ^ n) • e)) ≤ ε / 2 / 2 / 2 ^ n) := by
    intro n f
    by_cases h : IsUnit (a n f) ∧ ‖Ring.inverse (a n f)‖ ≤ 4 ^ n
    · obtain ⟨e, he, h₁, h₂, h₃⟩ := exists_step L hL hC hl hlx (M := 4 ^ n)
        (δ := ε / 2 / 2 / 2 ^ n) (by rw [hτ, htC])
        (by rw [hc]; exact hc1 n) (by positivity) h.1 h.2
      refine ⟨e, he, fun _ _ ↦ ⟨?_, ?_, ?_⟩⟩ <;> simpa only [a, yy, pow_succ', ← mul_assoc]
    · obtain ⟨e, he⟩ := hC.exists
      exact ⟨e, he, fun h₁ h₂ ↦ absurd ⟨h₁, h₂⟩ h⟩
  choose E' hE'C hE' using step
  /- The recursive sequence of `A`-parts `f n = ∑_{k < n} τ (1 - τ) ^ k E' k (f k)`. -/
  obtain ⟨f, hf0, hfs⟩ : ∃ f : ℕ → A, f 0 = 0 ∧
      ∀ n, f (n + 1) = f n + (τ * (1 - τ) ^ n) • E' n (f n) :=
    ⟨fun n ↦ Nat.rec 0 (fun k fk ↦ fk + (τ * (1 - τ) ^ k) • E' k fk) n, rfl, fun _ ↦ rfl⟩
  have hinv : ∀ n, IsUnit (a n (f n)) ∧ ‖Ring.inverse (a n (f n))‖ ≤ 4 ^ n := by
    intro n
    induction n with
    | zero => simp [hf0, a]
    | succ n ih =>
      obtain ⟨h₁, h₂, -⟩ := hE' n (f n) ih.1 ih.2
      rw [hfs]
      exact ⟨h₁, h₂⟩
  have hy : ∀ n, dist (yy n (f n)) (yy (n + 1) (f (n + 1))) ≤ ε / 2 / 2 / 2 ^ n := fun n ↦ by
    rw [hfs]
    exact (hE' n (f n) (hinv n).1 (hinv n).2).2.2
  have hf : ∀ n, dist (f n) (f (n + 1)) ≤ t * C * (1 - t) ^ n := fun n ↦ by
    rw [hfs, dist_eq_norm, sub_add_cancel_left, norm_neg, norm_smul, hc]
    nlinarith [mul_le_mul_of_nonneg_left (hE'C n (f n))
      (mul_nonneg ht0.le (pow_nonneg (by linarith : (0 : ℝ) ≤ 1 - t) n))]
  /- Pass to the limit in `a n (f n) · yy n (f n) = x`. -/
  have hfac : ∀ n, (1 - τ) ^ n • yy n (f n) + L (f n) (yy n (f n)) = x := fun n ↦ by
    have : Φ (a n (f n)) (yy n (f n)) = x := by
      rw [← mul_apply_eq_comp, ← map_mul, Ring.mul_inverse_cancel _ (hinv n).1, map_one,
        one_apply_eq_self]
    rw [unitizationAction_apply] at this
    simpa [a] using this
  have hyy0 : yy 0 (f 0) = x := by simp [yy, a, hf0]
  obtain ⟨a₀, y₀, ha₀, hy₀, hdist, hfac₀⟩ := exists_apply_eq_of_tendsto L
    (by rw [hτ']; linarith) ht0 hf0 hyy0 hf hy hfac
  exact ⟨a₀, y₀, ha₀, isClosed_closure.mem_of_tendsto hy₀
    (.of_forall fun n ↦ unitizationAction_apply_mem_closure L hL hlx _), by linarith, hfac₀⟩

/-- Over a Banach algebra with a bounded left approximate identity, the set `A · E` of products
is already a closed linear subspace of a Banach left module `E`: it equals the essential part
`closure (span (A · E))`. -/
theorem coe_topologicalClosure_span_range_eq (L : A →L[𝕜] E →L[𝕜] E)
    (hL : ∀ a b z, L (a * b) z = L a (L b z)) {l : Filter A} [l.NeBot] {C : ℝ}
    (hC : ∀ᶠ e in l, ‖e‖ ≤ C) (hl : ∀ a, Tendsto (· * a) l (𝓝 a)) :
    ((span 𝕜 (Set.range fun p : A × E ↦ L p.1 p.2)).topologicalClosure : Set E) =
      Set.range fun p : A × E ↦ L p.1 p.2 := by
  refine subset_antisymm (fun x hx ↦ ?_) ((subset_span).trans (le_topologicalClosure _))
  obtain ⟨a, y, -, -, -, h⟩ := exists_apply_eq_of_mem_topologicalClosure_span L hL hC hl hx one_pos
  exact ⟨(a, y), h⟩

end ContinuousLinearMap
