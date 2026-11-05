/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.SpecificLimits.Normed
public import TauCeti.Analysis.Normed.Module.Essential
public import TauCeti.Analysis.Normed.Module.Unitization
public import TauCeti.Analysis.Normed.Ring.Units

/-!
# Cohen–Hewitt factorization for Banach left modules

Let `A` be a possibly nonunital Banach algebra acting on a Banach space `E` on the left through a
bounded bilinear map `L : A →L[𝕜] E →L[𝕜] E` with `L (a * b) x = L a (L b x)`. The action need not
be contractive or unital. A left approximate identity of `A` is a proper filter `l` on `A` with
`e * a → a` along `l` for every `a`; it is bounded by `C` when `‖e‖ ≤ C` eventually along `l`.

The *essential part* of `E` is the closed linear span of `A · E`; a bounded left approximate
identity converges to the identity on it (`TauCeti.Analysis.Normed.Module.Essential`). This file
proves:

* the Cohen–Hewitt factorization theorem: every `x` in the essential part factors as `x = a · y`
  with `‖a‖ ≤ C`, `y` in the closure of `A · x`, and `y` arbitrarily close to `x`;
* consequently `A · E` is already a closed linear subspace: it equals the essential part;
* in particular, every element of `A` is a product of two elements of `A`.

## Implementation notes

The proof is the classical one. Fix `0 < t` with `t * (1 + C) = 1 / 2`. In the `ℓ¹`
unitization `A⁺ = WithLp 1 (Unitization 𝕜 A)` put
`aₙ = (1 - t) ^ n + ∑_{k < n} t (1 - t) ^ k eₖ`, with `eₖ` chosen inductively from the approximate
identity. The identity `aₙ₊₁ = ((1 - t) + t eₙ) aₙ + t (fₙ - eₙ fₙ)`, where `fₙ` is the `A`-part
of `aₙ`, shows that each `aₙ` is invertible with `‖aₙ⁻¹‖ ≤ 4 ^ n`, once `eₙ` nearly fixes `fₙ`.
Choosing `eₙ` to nearly fix `aₙ⁻¹ · x` as well makes `yₙ = aₙ⁻¹ · x` a Cauchy sequence. Its limit
`y` satisfies `a · y = x`, where `a = ∑ₖ t (1 - t) ^ k eₖ` has norm at most `C`.

## Main results

* `ContinuousLinearMap.exists_apply_eq_of_mem_topologicalClosure_span`: the Cohen–Hewitt
  factorization theorem.
* `ContinuousLinearMap.coe_topologicalClosure_span_range_eq`: the essential part is `A · E`.
* `TauCeti.exists_mul_eq_of_tendsto_mul_right`: every element of `A` factors as `a * y` with
  `‖a‖ ≤ C`.

## References

* H. G. Dales, *Banach Algebras and Automatic Continuity*, Theorem 2.9.24.
* E. Hewitt, *The ranges of certain convolution operators*, Math. Scand. 15 (1964), 147–155.
* P. J. Cohen, *Factorization in group algebras*, Duke Math. J. 26 (1959), 199–205.
-/

public section

open Filter Topology Submodule Unitization WithLp

/-! ### The Cohen–Hewitt construction -/

namespace TauCeti.CohenHewitt

variable {𝕜 A E : Type*} [RCLike 𝕜] [NonUnitalNormedRing A] [NormedSpace 𝕜 A]
  [IsScalarTower 𝕜 A A] [SMulCommClass 𝕜 A A] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- The algebraic identity behind one Cohen–Hewitt step: in the `ℓ¹` unitization,
`(1 - τ) s + (f + τ s e) = (1 - w) (s + f) + τ (f - e f)` with `w = τ - τ e`. -/
private lemma toLp_inl_add_eq_one_sub_mul_add (τ s : 𝕜) (f e : A) :
    toLp 1 (inl ((1 - τ) * s) + ((f + (τ * s) • e : A) : Unitization 𝕜 A)) =
      (1 - toLp 1 (inl τ + ((-(τ • e) : A) : Unitization 𝕜 A))) *
          toLp 1 (inl s + (f : Unitization 𝕜 A)) +
        toLp 1 ((τ • (f - e * f) : A) : Unitization 𝕜 A) := by
  set ι : Unitization 𝕜 A ≃ₐ[𝕜] WithLp 1 (Unitization 𝕜 A) := (unitizationAlgEquiv 𝕜).symm
  have hι : ∀ u, toLp 1 u = ι u := fun u ↦ (unitizationAlgEquiv_symm_apply 𝕜 u).symm
  simp only [hι, ← map_one ι, ← map_sub, ← map_mul, ← map_add]
  congr 1
  ext
  · simp
  · simp [smul_mul_assoc]
    module

/-- The increment of one Cohen–Hewitt step. Let `a` and `a'` be units of the `ℓ¹` unitization
with `a - a' = c (1 - e)`, `‖c‖ ≤ 1` and `‖a'⁻¹‖ ≤ M`, and put `y = a⁻¹ · x`. Then
`a'⁻¹ · x - y = a'⁻¹ · c (y - e · y)`, so `a'⁻¹ · x` is within `δ` of `y` once `e` nearly
fixes `y`. -/
private lemma dist_unitizationAction_inverse_le (L : A →L[𝕜] E →L[𝕜] E)
    (hL : ∀ a b z, L (a * b) z = L a (L b z)) {a a' : WithLp 1 (Unitization 𝕜 A)}
    (ha : IsUnit a) (ha' : IsUnit a') {c : 𝕜} (hc : ‖c‖ ≤ 1) {e : A}
    (haa' : a - a' = toLp 1 (c • (1 - (e : Unitization 𝕜 A)))) {M δ : ℝ}
    (hM : ‖Ring.inverse a'‖ ≤ M) (hδ : 0 < δ) {x : E}
    (he : ‖L.unitizationAction hL (Ring.inverse a) x -
      L e (L.unitizationAction hL (Ring.inverse a) x)‖ < δ / ((1 + ‖L‖) * M + 1)) :
    dist (L.unitizationAction hL (Ring.inverse a) x)
      (L.unitizationAction hL (Ring.inverse a') x) ≤ δ := by
  set Φ := L.unitizationAction hL
  set y := Φ (Ring.inverse a) x
  have hM0 : 0 ≤ M := (norm_nonneg _).trans hM
  have hK : 0 < 1 + ‖L‖ := by positivity
  have hinv : Ring.inverse a' - Ring.inverse a = Ring.inverse a' * (a - a') * Ring.inverse a :=
    Ring.inverse_sub_inverse ⟨fun _ ↦ ha, fun _ ↦ ha'⟩
  have hincr : Φ (Ring.inverse a') x - y = Φ (Ring.inverse a') (c • (y - L e y)) := by
    calc Φ (Ring.inverse a') x - y = Φ (Ring.inverse a' - Ring.inverse a) x := by simp [y]
      _ = Φ (Ring.inverse a') (Φ (a - a') y) := by simp [hinv, y, mul_apply_eq_comp]
      _ = Φ (Ring.inverse a') (c • (y - L e y)) := by
        rw [haa']
        congr 1
        simp [Φ, smul_sub]
  rw [dist_comm, dist_eq_norm, hincr]
  calc ‖Φ (Ring.inverse a') (c • (y - L e y))‖
      ≤ (1 + ‖L‖) * ‖Ring.inverse a'‖ * ‖c • (y - L e y)‖ :=
        L.norm_unitizationAction_apply_le hL _ _
    _ ≤ (1 + ‖L‖) * M * (1 * (δ / ((1 + ‖L‖) * M + 1))) := by
        rw [norm_smul]
        gcongr
    _ ≤ δ := by
        rw [one_mul, ← mul_div_assoc, div_le_iff₀ (by positivity)]
        nlinarith [mul_nonneg hK.le hM0]

/-- If `s + f` is a unit of the `ℓ¹` unitization, then `y = (s + f)⁻¹ · x` solves
`s • y + f · y = x`. -/
private lemma smul_add_apply_unitizationAction_inverse (L : A →L[𝕜] E →L[𝕜] E)
    (hL : ∀ a b z, L (a * b) z = L a (L b z)) {s : 𝕜} {f : A}
    (hu : IsUnit (toLp 1 (inl s + (f : Unitization 𝕜 A)))) (x : E) :
    s • L.unitizationAction hL (Ring.inverse (toLp 1 (inl s + (f : Unitization 𝕜 A)))) x +
      L f (L.unitizationAction hL (Ring.inverse (toLp 1 (inl s + (f : Unitization 𝕜 A)))) x) =
      x := by
  have := congr(L.unitizationAction hL $(Ring.mul_inverse_cancel _ hu) x)
  rw [map_mul, mul_apply_eq_comp, ContinuousLinearMap.unitizationAction_apply] at this
  simpa using this

variable [CompleteSpace A]

/-- The unit part of one Cohen–Hewitt step. Suppose `a = s + f` is a unit of the `ℓ¹`
unitization with `‖a⁻¹‖ ≤ M`, and `‖τ‖ * (1 + C) ≤ 1 / 2`. If `‖e‖ ≤ C` and `e` nearly fixes `f`,
then `a' = (1 - τ) s + (f + τ s e)` is again a unit, with `‖a'⁻¹‖ ≤ 4 M`. -/
private lemma isUnit_and_norm_inverse_le_step {τ s : 𝕜} {C M : ℝ} (hτ : ‖τ‖ * (1 + C) ≤ 1 / 2)
    {f e : A} (heC : ‖e‖ ≤ C) (he : ‖f - e * f‖ < 1 / (4 * ‖τ‖ * M + 1))
    (hu : IsUnit (toLp 1 (inl s + (f : Unitization 𝕜 A))))
    (hM : ‖Ring.inverse (toLp 1 (inl s + (f : Unitization 𝕜 A)))‖ ≤ M) :
    IsUnit (toLp 1 (inl ((1 - τ) * s) + ((f + (τ * s) • e : A) : Unitization 𝕜 A))) ∧
      ‖Ring.inverse (toLp 1 (inl ((1 - τ) * s) + ((f + (τ * s) • e : A) : Unitization 𝕜 A)))‖ ≤
        4 * M := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans hM
  /- `a'` is a small perturbation `(1 - w) * a + d` of the unit `(1 - w) * a`, where
  `‖w‖ ≤ 1 / 2` and `‖d‖ * (2 * M) ≤ 1 / 2`. -/
  set w := toLp 1 (inl τ + ((-(τ • e) : A) : Unitization 𝕜 A))
  set d := toLp 1 ((τ • (f - e * f) : A) : Unitization 𝕜 A)
  have hw : ‖w‖ ≤ 1 / 2 := by
    simp [w, unitization_norm_def, norm_smul]
    nlinarith [norm_nonneg τ]
  have hd : ‖d‖ * (2 * M) ≤ 1 / 2 := by
    rw [unitization_norm_inr, norm_smul]
    rw [lt_div_iff₀ (by positivity)] at he
    nlinarith [norm_nonneg τ, norm_nonneg (f - e * f),
      mul_nonneg (norm_nonneg τ) (norm_nonneg (f - e * f))]
  obtain ⟨ha', hM'⟩ := NormedRing.isUnit_one_sub_mul_add_and_norm_inverse_le (w := w) (d := d)
    hu hM (by linarith) (by linarith)
  rw [toLp_inl_add_eq_one_sub_mul_add]
  refine ⟨ha', hM'.trans ?_⟩
  rw [div_le_iff₀ (by linarith)]
  nlinarith

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
  set y := L.unitizationAction hL (Ring.inverse (toLp 1 (inl s + (f : Unitization 𝕜 A)))) x
  have hM0 : 0 ≤ M := (norm_nonneg _).trans hM
  have h₁ : ∀ᶠ e in l, ‖f - e * f‖ < 1 / (4 * ‖τ‖ * M + 1) := by
    simpa [dist_eq_norm, norm_sub_rev] using
      Metric.tendsto_nhds.mp (hl f) _ (by positivity : 0 < 1 / (4 * ‖τ‖ * M + 1))
  have h₂ : ∀ᶠ e in l, ‖y - L e y‖ < δ / ((1 + ‖L‖) * (4 * M) + 1) :=
    (Metric.tendsto_nhds.mp (L.tendsto_apply_unitizationAction hL hl hlx _) _
      (by positivity : 0 < δ / ((1 + ‖L‖) * (4 * M) + 1))).mono fun e he ↦ by
        rwa [dist_eq_norm, norm_sub_rev] at he
  obtain ⟨e, heC, he₁, he₂⟩ := (hC.and (h₁.and h₂)).exists
  obtain ⟨ha', hM'⟩ := isUnit_and_norm_inverse_le_step hτ heC he₁ hu hM
  refine ⟨e, heC, ha', hM', dist_unitizationAction_inverse_le L hL hu ha' hs ?_ hM' hδ he₂⟩
  /- `a - a' = τ s (1 - e)`. -/
  rw [← toLp_sub]
  congr 1
  ext
  · simp
    ring
  · simp

/-- `exists_step` at stage `n` of the recursion, with `s = (1 - τ) ^ n`, `M = 4 ^ n` and
`δ = ε / 2 / 2 / 2 ^ n`. It is stated for every `f`, so that `choose` can build the sequence: the
conclusion is only claimed when `(1 - τ) ^ n + f` is a unit with inverse of norm at most
`4 ^ n`, which the recursion maintains. -/
private lemma exists_step_pow (L : A →L[𝕜] E →L[𝕜] E) (hL : ∀ a b z, L (a * b) z = L a (L b z))
    {l : Filter A} [l.NeBot] {C : ℝ} (hC : ∀ᶠ e in l, ‖e‖ ≤ C)
    (hl : ∀ a, Tendsto (· * a) l (𝓝 a)) {x : E} (hlx : Tendsto (fun e ↦ L e x) l (𝓝 x))
    {τ : 𝕜} (hτ : ‖τ‖ * (1 + C) ≤ 1 / 2) {n : ℕ} (hτ₁ : ‖τ * (1 - τ) ^ n‖ ≤ 1) {ε : ℝ}
    (hε : 0 < ε) (f : A) :
    ∃ e : A, ‖e‖ ≤ C ∧ (IsUnit (toLp 1 (inl ((1 - τ) ^ n) + (f : Unitization 𝕜 A))) →
      ‖Ring.inverse (toLp 1 (inl ((1 - τ) ^ n) + (f : Unitization 𝕜 A)))‖ ≤ 4 ^ n →
      IsUnit (toLp 1 (inl ((1 - τ) ^ (n + 1)) +
        ((f + (τ * (1 - τ) ^ n) • e : A) : Unitization 𝕜 A))) ∧
      ‖Ring.inverse (toLp 1 (inl ((1 - τ) ^ (n + 1)) +
        ((f + (τ * (1 - τ) ^ n) • e : A) : Unitization 𝕜 A)))‖ ≤ 4 ^ (n + 1) ∧
      dist (L.unitizationAction hL
          (Ring.inverse (toLp 1 (inl ((1 - τ) ^ n) + (f : Unitization 𝕜 A)))) x)
        (L.unitizationAction hL (Ring.inverse (toLp 1 (inl ((1 - τ) ^ (n + 1)) +
          ((f + (τ * (1 - τ) ^ n) • e : A) : Unitization 𝕜 A)))) x) ≤ ε / 2 / 2 / 2 ^ n) := by
  by_cases h : IsUnit (toLp 1 (inl ((1 - τ) ^ n) + (f : Unitization 𝕜 A))) ∧
      ‖Ring.inverse (toLp 1 (inl ((1 - τ) ^ n) + (f : Unitization 𝕜 A)))‖ ≤ 4 ^ n
  · obtain ⟨e, he, h₁, h₂, h₃⟩ := exists_step L hL hC hl hlx (M := 4 ^ n)
      (δ := ε / 2 / 2 / 2 ^ n) hτ hτ₁ (by positivity) h.1 h.2
    /- `exists_step` states its conclusion with `(1 - τ) * (1 - τ) ^ n` and `4 * 4 ^ n`. -/
    simp only [pow_succ' (1 - τ), pow_succ' (4 : ℝ)]
    exact ⟨e, he, fun _ _ ↦ ⟨h₁, h₂, h₃⟩⟩
  · obtain ⟨e, he⟩ := hC.exists
    exact ⟨e, he, fun h₁ h₂ ↦ absurd ⟨h₁, h₂⟩ h⟩

/-- The recursive part of the Cohen–Hewitt construction. Iterating `exists_step` with
`s = (1 - τ) ^ n`, starting from `f 0 = 0`, produces `A`-parts `f n` whose increments are
`τ (1 - τ) ^ n eₙ` with `‖eₙ‖ ≤ C`, such that `aₙ = (1 - τ) ^ n + f n` is a unit of the `ℓ¹`
unitization and `y n = aₙ⁻¹ · x` moves by at most `ε / 2 / 2 / 2 ^ n` at each step. -/
private lemma exists_seq (L : A →L[𝕜] E →L[𝕜] E) (hL : ∀ a b z, L (a * b) z = L a (L b z))
    {l : Filter A} [l.NeBot] {C : ℝ} (hC : ∀ᶠ e in l, ‖e‖ ≤ C)
    (hl : ∀ a, Tendsto (· * a) l (𝓝 a)) {x : E} (hlx : Tendsto (fun e ↦ L e x) l (𝓝 x))
    {τ : 𝕜} (hτ : ‖τ‖ * (1 + C) ≤ 1 / 2) (hτ₁ : ∀ n : ℕ, ‖τ * (1 - τ) ^ n‖ ≤ 1) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ (f : ℕ → A) (y : ℕ → E), f 0 = 0 ∧ y 0 = x ∧
      (∀ n, dist (f n) (f (n + 1)) ≤ ‖τ * (1 - τ) ^ n‖ * C) ∧
      (∀ n, dist (y n) (y (n + 1)) ≤ ε / 2 / 2 / 2 ^ n) ∧
      (∀ n, (1 - τ) ^ n • y n + L (f n) (y n) = x) ∧
      ∀ n, y n ∈ closure (Set.range fun b ↦ L b x) := by
  /- `a n f = (1 - τ) ^ n + f` in the unitization, and `yy n f = (a n f)⁻¹ · x`. -/
  let a : ℕ → A → WithLp 1 (Unitization 𝕜 A) := fun n f ↦
    toLp 1 (inl ((1 - τ) ^ n) + (f : Unitization 𝕜 A))
  let yy : ℕ → A → E := fun n f ↦ L.unitizationAction hL (Ring.inverse (a n f)) x
  choose E' hE'C hE' using fun n ↦ exists_step_pow L hL hC hl hlx hτ (hτ₁ n) hε
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
  refine ⟨f, fun n ↦ yy n (f n), hf0, by simp [yy, a, hf0], fun n ↦ ?_, fun n ↦ ?_,
    fun n ↦ smul_add_apply_unitizationAction_inverse L hL (hinv n).1 x,
    fun n ↦ L.unitizationAction_apply_mem_closure hL hlx _⟩
  · rw [hfs, dist_self_add_right, norm_smul]
    exact mul_le_mul_of_nonneg_left (hE'C n (f n)) (norm_nonneg _)
  · dsimp only
    rw [hfs]
    exact (hE' n (f n) (hinv n).1 (hinv n).2).2.2

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
    simpa [hf₀, ht₀.ne'] using this
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
  obtain ⟨f, y, hf0, hy0, hf, hy, hfac, hyx⟩ :=
    exists_seq L hL hC hl hlx (by rw [hτ, htC]) (fun n ↦ (hc n).trans_le (hc1 n)) hε
  obtain ⟨a₀, y₀, ha₀, hy₀, hdist, hfac₀⟩ := exists_apply_eq_of_tendsto L
    (by rw [hτ']; linarith) ht0 hf0 hy0 (fun n ↦ (hf n).trans_eq (by rw [hc]; ring)) hy hfac
  exact ⟨a₀, y₀, ha₀, isClosed_closure.mem_of_tendsto hy₀ (.of_forall hyx), by linarith, hfac₀⟩

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

namespace TauCeti

variable {A : Type*} [NonUnitalNormedRing A] [CompleteSpace A]

/-- **Cohen's factorization theorem** for Banach algebras: if `A` has a left approximate identity
bounded by `C`, then every element of `A` is a product `a * y` with `‖a‖ ≤ C`. -/
theorem exists_mul_eq_of_tendsto_mul_right (𝕜 : Type*) [RCLike 𝕜] [NormedSpace 𝕜 A]
    [IsScalarTower 𝕜 A A] [SMulCommClass 𝕜 A A] {l : Filter A} [l.NeBot] {C : ℝ}
    (hC : ∀ᶠ e in l, ‖e‖ ≤ C) (hl : ∀ a, Tendsto (· * a) l (𝓝 a)) (x : A) :
    ∃ a y, ‖a‖ ≤ C ∧ a * y = x := by
  have hL : ∀ a b z : A, ContinuousLinearMap.mul 𝕜 A (a * b) z =
      ContinuousLinearMap.mul 𝕜 A a (ContinuousLinearMap.mul 𝕜 A b z) := fun a b z ↦ by
    simp [mul_assoc]
  have hx := (ContinuousLinearMap.tendsto_apply_iff_mem_topologicalClosure_span _ hL hC hl).1
    (by simpa using hl x)
  obtain ⟨a, y, ha, -, -, h⟩ :=
    ContinuousLinearMap.exists_apply_eq_of_mem_topologicalClosure_span _ hL hC hl hx one_pos
  exact ⟨a, y, ha, by simpa using h⟩

end TauCeti
