/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.StableRange
public import Mathlib.Analysis.Complex.Tietze
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Topology.ContinuousMap.Star
public import Mathlib.Topology.ContinuousMap.Units
public import Mathlib.Topology.ContinuousMap.Weierstrass

/-!
# Stable range of rings of continuous functions

For a topological space `X` and `𝕜 = ℝ` or `ℂ`, this file relates the Bass stable range
`TauCeti.HasStableRangeLE` of the ring `C(X, 𝕜)` to the topology of `X`, through the
covering-dimension-free ingredients of Vaserstein's computation of that stable range.

* A row `(a₁, …, aₙ)` of `C(X, 𝕜)` is unimodular exactly when its entries have no common zero.
  No compactness is needed: `∑ aᵢ conj aᵢ` is then a nowhere vanishing function, hence a unit.
* **Upper bounds from density.** For compact `X`, if the unimodular rows are uniformly dense in
  `C(X, 𝕜)ⁿ` (the topological stable rank of `C(X, 𝕜)` is at most `n`), then `C(X, 𝕜)` has Bass
  stable range at most `n`.
* **Lower bounds from extension.** For normal `X`, if `C(X, 𝕜)` has stable range at most `s`, then
  every continuous map from a closed subset of `X` to `𝕜ˢ ∖ {0}` extends to `X`; equivalently,
  maps to the unit sphere of `𝕜ˢ`, a sphere of dimension `s - 1` or `2s - 1`, extend.
* **The interval.** For a compact interval `[a, b]`, polynomial approximation shows that pairs of
  real functions without common zero, and nowhere vanishing complex functions, are dense. Hence
  `C([a, b], ℂ)` has stable range at most `1` and `C([a, b], ℝ)` at most `2`, while for `a < b` the
  intermediate value theorem shows that `C([a, b], ℝ)` does not have stable range at most `1`.

These are the bounds `sr C([a, b], ℂ) = 1` and `sr C([a, b], ℝ) = 2` of Vaserstein's formulas
`sr C(X, ℂ) = ⌊dim X / 2⌋ + 1` and `sr C(X, ℝ) = dim X + 1` for the one-dimensional space `[a, b]`.

## Main results

* `TauCeti.isUnimodular_continuousMap_iff_forall_exists_ne_zero`: unimodular rows of `C(X, 𝕜)` are
  the rows without common zero.
* `TauCeti.hasStableRangeLE_continuousMap_of_dense`: dense unimodular `n`-rows give stable range
  at most `n`.
* `TauCeti.HasStableRangeLE.exists_extension_ne_zero`: stable range at most `s` lets nonvanishing
  maps from closed subsets to `𝕜ˢ` extend.
* `TauCeti.hasStableRangeLE_one_continuousMap_Icc_complex`,
  `TauCeti.hasStableRangeLE_two_continuousMap_Icc_real` and
  `TauCeti.not_hasStableRangeLE_one_continuousMap_Icc_real`: the stable ranges of the interval.

## References

* L. N. Vaserstein, *Stable rank of rings and dimensionality of topological spaces*, Functional
  Analysis and Its Applications 5 (1971), 102–110, §2, Theorems 5 and 7.
* M. A. Rieffel, *Dimension and stable rank in the K-theory of C*-algebras*, Proc. London Math.
  Soc. (3) 46 (1983), 301–333, §2 (Bass stable rank is at most topological stable rank).
-/

public section

open scoped ComplexConjugate

namespace TauCeti

variable {X 𝕜 : Type*} [TopologicalSpace X] [RCLike 𝕜]

/-! ### Unimodular rows of continuous functions -/

/-- A finite row of continuous functions `X → 𝕜` is unimodular in `C(X, 𝕜)` exactly when its
entries have no common zero. -/
theorem isUnimodular_continuousMap_iff_forall_exists_ne_zero {ι : Type*} [Finite ι]
    {a : ι → C(X, 𝕜)} : Module.IsUnimodular C(X, 𝕜) a ↔ ∀ x, ∃ i, a i x ≠ 0 := by
  have := Fintype.ofFinite ι
  rw [TauCeti.Module.isUnimodular_pi_iff]
  constructor
  · rintro ⟨b, hb⟩ x
    have hx : ∑ i, a i x * b i x = 1 := by
      simpa using congr($hb x)
    obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero (hx ▸ one_ne_zero)
    exact ⟨i, left_ne_zero_of_mul hi⟩
  · intro h
    set s : C(X, 𝕜) := ∑ i, a i * star (a i) with hs
    have hsx (x : X) : s x = ((∑ i, ‖a i x‖ ^ 2 : ℝ) : 𝕜) := by
      simp [hs, RCLike.mul_conj]
    have hunit : IsUnit s := by
      rw [ContinuousMap.isUnit_iff_forall_ne_zero]
      intro x
      rw [hsx, RCLike.ofReal_ne_zero]
      obtain ⟨i, hi⟩ := h x
      exact (Finset.sum_pos' (fun j _ ↦ by positivity) ⟨i, Finset.mem_univ _,
        by positivity⟩).ne'
    refine ⟨fun i ↦ star (a i) * ↑hunit.unit⁻¹, ?_⟩
    simp_rw [← mul_assoc, ← Finset.sum_mul]
    exact hunit.mul_val_inv

/-! ### Dense unimodular rows bound the stable range -/

/-- The shortening step of `TauCeti.hasStableRangeLE_continuousMap_of_dense`: if some `f i` has
norm at least `δ > 0` wherever `‖g‖ < δ`, and `b` has no common zero and lies within `δ` of `f`
pointwise, then `f + g c` has no common zero for some `c`. -/
private theorem exists_forall_exists_add_mul_ne_zero {n : ℕ} {f b : Fin n → C(X, 𝕜)}
    {g : C(X, 𝕜)} {δ : ℝ} (hδ : 0 < δ) (hf : ∀ x, ‖g x‖ < δ → ∃ i, δ ≤ ‖f i x‖)
    (hb : ∀ x, ∃ i, b i x ≠ 0) (hbf : ∀ i x, ‖b i x - f i x‖ < δ) :
    ∃ c : Fin n → C(X, 𝕜), ∀ x, ∃ i, (f i + g * c i) x ≠ 0 := by
  have hmax (x : X) : 0 < max (‖g x‖ ^ 2) (δ ^ 2) := lt_max_of_lt_right (by positivity)
  let k : C(X, 𝕜) := ⟨fun x ↦ ((max (‖g x‖ ^ 2) (δ ^ 2))⁻¹ : ℝ),
    RCLike.continuous_ofReal.comp ((by fun_prop : Continuous fun x ↦
      max (‖g x‖ ^ 2) (δ ^ 2)).inv₀ fun x ↦ (hmax x).ne')⟩
  have hk (x : X) : k x = ((max (‖g x‖ ^ 2) (δ ^ 2))⁻¹ : ℝ) := rfl
  refine ⟨fun i ↦ star g * (b i - f i) * k, fun x ↦ ?_⟩
  -- The new row is `f + θ (b - f)` with `θ = ‖g‖² / max (‖g‖², δ²) ∈ [0, 1]`.
  set θ : ℝ := ‖g x‖ ^ 2 * (max (‖g x‖ ^ 2) (δ ^ 2))⁻¹ with hθ
  have hrow (i : Fin n) : (f i + g * (star g * (b i - f i) * k)) x =
      f i x + (θ : 𝕜) * (b i x - f i x) := by
    simp only [ContinuousMap.add_apply, ContinuousMap.mul_apply, ContinuousMap.star_apply,
      ContinuousMap.sub_apply, hk, hθ, RCLike.star_def]
    rw [← mul_assoc, ← mul_assoc, RCLike.mul_conj]
    push_cast
    ring
  simp_rw [hrow]
  by_cases hgx : δ ≤ ‖g x‖
  · -- Where `g` is large, `θ = 1` and the new row is `b`.
    have hθ1 : θ = 1 := by
      rw [hθ, max_eq_left (pow_le_pow_left₀ hδ.le hgx 2)]
      exact mul_inv_cancel₀ (pow_pos (hδ.trans_le hgx) 2).ne'
    obtain ⟨i, hi⟩ := hb x
    exact ⟨i, by simpa [hθ1] using hi⟩
  · -- Where `g` is small, some `f i` is at least `δ`, and moves by less than `δ`.
    obtain ⟨i, hi⟩ := hf x (not_le.1 hgx)
    refine ⟨i, fun h0 ↦ ?_⟩
    have hθ0 : 0 ≤ θ := by positivity
    have hθ1 : θ ≤ 1 := mul_inv_le_one_of_le₀ (le_max_left _ _) (hmax x).le
    have h1 : ‖f i x‖ = θ * ‖b i x - f i x‖ := by
      simpa [norm_mul, RCLike.norm_ofReal, abs_of_nonneg hθ0] using
        congrArg norm (eq_neg_of_add_eq_zero_left h0)
    exact (hi.trans (h1.trans_le (mul_le_of_le_one_left (norm_nonneg _) hθ1))).not_gt
      (hbf i x)

/-- **Dense unimodular rows bound the stable range.** Let `X` be compact. If the unimodular rows
are dense in `C(X, 𝕜)ⁿ` for the uniform topology, that is, if `C(X, 𝕜)` has topological stable rank
at most `n`, then `C(X, 𝕜)` has Bass stable range at most `n`. -/
theorem hasStableRangeLE_continuousMap_of_dense [CompactSpace X] {n : ℕ}
    (h : Dense {a : Fin n → C(X, 𝕜) | Module.IsUnimodular C(X, 𝕜) a}) :
    HasStableRangeLE C(X, 𝕜) n := by
  rw [hasStableRangeLE_def]
  intro a ha
  rw [isUnimodular_continuousMap_iff_forall_exists_ne_zero] at ha
  -- Write the row as `(f, g)` with `g` its last entry. Approximate `f` by a unimodular `b` so
  -- closely that `f + g c` with `c = conj g (b - f) / max (‖g‖², δ²)` has no common zero.
  -- A uniform lower bound: at every point some entry of `a` has norm at least `δ`.
  obtain ⟨δ, hδ, hδa⟩ : ∃ δ > 0, ∀ x, ∃ j, δ ≤ ‖a j x‖ := by
    rcases isEmpty_or_nonempty X with hX | hX
    · exact ⟨1, one_pos, fun x ↦ isEmptyElim x⟩
    have hcont : Continuous fun x ↦ ‖fun j ↦ a j x‖ := by fun_prop
    obtain ⟨x₀, -, hx₀⟩ := isCompact_univ.exists_isMinOn Set.univ_nonempty hcont.continuousOn
    obtain ⟨j₀, hj₀⟩ := ha x₀
    have hm : 0 < ‖fun j ↦ a j x₀‖ := norm_pos_iff.2 fun h0 ↦ hj₀ (congr_fun h0 j₀)
    refine ⟨_, hm, fun x ↦ ?_⟩
    by_contra! hx
    exact (isMinOn_iff.1 hx₀ x trivial).not_gt ((pi_norm_lt_iff hm).2 hx)
  -- Approximate the first `n` entries by a unimodular row `b`.
  obtain ⟨b, hb, hbf⟩ := h.exists_dist_lt (fun i ↦ a (Fin.castSucc i)) hδ
  have hf (x : X) (hx : ‖a (Fin.last n) x‖ < δ) : ∃ i, δ ≤ ‖a (Fin.castSucc i) x‖ := by
    obtain ⟨j, hj⟩ := hδa x
    induction j using Fin.lastCases with
    | last => exact absurd hj (not_le.2 hx)
    | cast i => exact ⟨i, hj⟩
  have hbf' (i : Fin n) (x : X) : ‖b i x - a (Fin.castSucc i) x‖ < δ := by
    rw [← dist_eq_norm, dist_comm]
    exact (ContinuousMap.dist_apply_le_dist x).trans_lt ((dist_pi_lt_iff hδ).1 hbf i)
  obtain ⟨c, hc⟩ := exists_forall_exists_add_mul_ne_zero hδ hf
    (isUnimodular_continuousMap_iff_forall_exists_ne_zero.1 hb) hbf'
  exact ⟨c, isUnimodular_continuousMap_iff_forall_exists_ne_zero.2 hc⟩

/-! ### The extension obstruction -/

/-- **Stable range and extension of nonvanishing maps.** If `C(X, 𝕜)` has stable range at most `s`
for a normal space `X`, then every continuous map from a closed subset `A ⊆ X` to `𝕜ˢ ∖ {0}`
extends to a continuous map `X → 𝕜ˢ ∖ {0}`. Normalizing, every map from `A` to the unit sphere of
`𝕜ˢ`, which is `Sˢ⁻¹` for `𝕜 = ℝ` and `S²ˢ⁻¹` for `𝕜 = ℂ`, extends to `X`. This is the obstruction
giving the lower bounds in Vaserstein's computation of the stable range of `C(X, 𝕜)`. -/
theorem HasStableRangeLE.exists_extension_ne_zero [NormalSpace X] {s : ℕ}
    (hR : HasStableRangeLE C(X, 𝕜) s) {A : Set X} (hA : IsClosed A) (f : C(A, Fin s → 𝕜))
    (hf : ∀ x, f x ≠ 0) : ∃ F : C(X, Fin s → 𝕜), F.restrict A = f ∧ ∀ x, F x ≠ 0 := by
  -- Extend `f` by Tietze to `G`, and choose by Urysohn `φ` vanishing on `A` and equal to `1`
  -- where `G` vanishes. The row `(G, φ)` is unimodular, and a shortening `G + φ c` is nowhere
  -- zero and agrees with `G` on `A`.
  obtain ⟨G, hG⟩ := f.exists_restrict_eq hA
  have hGA (x : X) (hx : x ∈ A) : G x = f ⟨x, hx⟩ := by rw [← hG, ContinuousMap.restrict_apply]
  obtain ⟨φ, hφA, hφ1, -⟩ := exists_continuous_zero_one_of_isClosed hA
    (isClosed_eq G.continuous continuous_const)
    (Set.disjoint_left.2 fun x hx hx0 ↦ hf ⟨x, hx⟩ (by rw [← hGA x hx]; exact hx0))
  let a : Fin (s + 1) → C(X, 𝕜) :=
    Fin.snoc (α := fun _ ↦ C(X, 𝕜)) (fun i ↦ ⟨fun x ↦ G x i, by fun_prop⟩)
      ⟨fun x ↦ (φ x : 𝕜), by fun_prop⟩
  have ha : Module.IsUnimodular C(X, 𝕜) a := by
    rw [isUnimodular_continuousMap_iff_forall_exists_ne_zero]
    intro x
    by_cases hx : G x = 0
    · exact ⟨Fin.last s, by simp [a, hφ1 hx]⟩
    · obtain ⟨i, hi⟩ := Function.ne_iff.1 hx
      exact ⟨Fin.castSucc i, by simpa [a] using hi⟩
  obtain ⟨c, hc⟩ := (hasStableRangeLE_def _ _).1 hR a ha
  rw [isUnimodular_continuousMap_iff_forall_exists_ne_zero] at hc
  refine ⟨ContinuousMap.pi fun i ↦ a (Fin.castSucc i) + a (Fin.last s) * c i, ?_, ?_⟩
  · ext x i
    simp [a, hφA x.property, hGA x x.property]
  · intro x hx
    obtain ⟨i, hi⟩ := hc x
    exact hi (congr_fun hx i)

/-! ### Stable ranges of `C([a, b], ℂ)` and `C([a, b], ℝ)` -/

section Icc

open Polynomial

/-- Unimodular pairs, that is pairs without common zero, are dense in `C([a, b], ℝ)²`: the
topological stable rank of `C([a, b], ℝ)` is at most `2`. -/
theorem dense_isUnimodular_continuousMap_Icc_real (a b : ℝ) :
    Dense {r : Fin 2 → C(Set.Icc a b, ℝ) | Module.IsUnimodular C(Set.Icc a b, ℝ) r} := by
  classical
  refine Metric.dense_iff.2 fun r ε hε ↦ ?_
  -- Approximate both entries by polynomials `p`, `q` (Weierstrass). Then move `p` by a small
  -- constant `u` so that `p - u` is a nonzero polynomial, and `q` by a small constant `v` avoiding
  -- the finitely many values of `q` at the roots of `p - u`.
  have hε4 : 0 < ε / 4 := by positivity
  obtain ⟨p, hp⟩ := exists_polynomial_near_continuousMap a b (r 0) (ε / 4) hε4
  obtain ⟨q, hq⟩ := exists_polynomial_near_continuousMap a b (r 1) (ε / 4) hε4
  obtain ⟨u, hu, hpu⟩ : ∃ u : ℝ, |u| < ε / 4 ∧ p - C u ≠ 0 := by
    by_cases hp0 : p = 0
    · refine ⟨ε / 8, by rw [abs_of_pos (by positivity)]; linarith, ?_⟩
      simpa [hp0] using (by positivity : ε / 8 ≠ 0)
    · exact ⟨0, by simpa using hε4, by simpa using hp0⟩
  obtain ⟨v, hv, hvS⟩ := (Set.Ioo_infinite (neg_lt_self hε4)).exists_notMem_finset
    ((p - C u).roots.toFinset.image q.eval)
  have key (h : C(Set.Icc a b, ℝ)) (P : ℝ[X]) (w : ℝ) (hP : ‖P.toContinuousMapOn _ - h‖ < ε / 4)
      (hw : |w| < ε / 4) : dist (P.toContinuousMapOn _ - .const _ w) h < ε := by
    refine ((ContinuousMap.dist_le (by positivity)).2 fun t ↦ ?_).trans_lt
      (by linarith : ε / 2 < ε)
    have ht := (ContinuousMap.norm_coe_le_norm (P.toContinuousMapOn _ - h) t).trans_lt hP
    rw [ContinuousMap.sub_apply, Real.norm_eq_abs] at ht
    rw [ContinuousMap.sub_apply, ContinuousMap.const_apply, Real.dist_eq, sub_right_comm]
    linarith [abs_sub (P.toContinuousMapOn _ t - h t) w]
  refine ⟨![p.toContinuousMapOn _ - .const _ u, q.toContinuousMapOn _ - .const _ v], ?_, ?_⟩
  · rw [Metric.mem_ball, dist_pi_lt_iff hε, Fin.forall_fin_two]
    exact ⟨key _ p u hp hu, key _ q v hq (abs_lt.2 hv)⟩
  · rw [Set.mem_ofPred_eq, isUnimodular_continuousMap_iff_forall_exists_ne_zero]
    intro t
    by_cases ht : p.eval (t : ℝ) = u
    · refine ⟨1, fun hq0 ↦ hvS (Finset.mem_image.2 ⟨t, ?_, ?_⟩)⟩
      · rw [Multiset.mem_toFinset, mem_roots hpu]
        simp [ht]
      · simpa [Polynomial.toContinuousMapOn_apply, Polynomial.toContinuousMap_apply, sub_eq_zero]
          using hq0
    · exact ⟨0, by simpa [Polynomial.toContinuousMapOn_apply, Polynomial.toContinuousMap_apply,
        sub_eq_zero] using ht⟩

/-- Unimodular `1`-rows, that is nowhere vanishing functions, are dense in `C([a, b], ℂ)`: the
topological stable rank of `C([a, b], ℂ)` is at most `1`. -/
theorem dense_isUnimodular_continuousMap_Icc_complex (a b : ℝ) :
    Dense {r : Fin 1 → C(Set.Icc a b, ℂ) | Module.IsUnimodular C(Set.Icc a b, ℂ) r} := by
  refine Metric.dense_iff.2 fun r ε hε ↦ ?_
  -- Approximate the real and imaginary parts of `r 0` by a pair without common zero.
  obtain ⟨s, hs, hs1⟩ := Metric.dense_iff.1 (dense_isUnimodular_continuousMap_Icc_real a b)
    ![⟨fun t ↦ (r 0 t).re, by fun_prop⟩, ⟨fun t ↦ (r 0 t).im, by fun_prop⟩] (ε / 4)
    (by positivity)
  rw [Metric.mem_ball, dist_pi_lt_iff (by positivity), Fin.forall_fin_two] at hs
  rw [Set.mem_ofPred_eq, isUnimodular_continuousMap_iff_forall_exists_ne_zero] at hs1
  let h : C(Set.Icc a b, ℂ) := ⟨fun t ↦ (s 0 t : ℂ) + (s 1 t : ℂ) * Complex.I, by fun_prop⟩
  have hre (t) : (h t).re = s 0 t := by simp [h]
  have him (t) : (h t).im = s 1 t := by simp [h]
  refine ⟨fun _ ↦ h, ?_, ?_⟩
  · rw [Metric.mem_ball, dist_pi_lt_iff hε]
    intro i
    refine (ContinuousMap.dist_le (half_pos hε).le |>.2 fun t ↦ ?_).trans_lt (half_lt_self hε)
    have h1 := (ContinuousMap.dist_apply_le_dist t).trans_lt hs.1
    have h2 := (ContinuousMap.dist_apply_le_dist t).trans_lt hs.2
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, ContinuousMap.coe_mk,
      Real.dist_eq] at h1 h2
    rw [Complex.dist_eq, Fin.fin_one_eq_zero i]
    refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    rw [Complex.sub_re, Complex.sub_im, hre, him]
    linarith
  · rw [Set.mem_ofPred_eq, isUnimodular_continuousMap_iff_forall_exists_ne_zero]
    intro t
    refine ⟨0, fun h0 ↦ ?_⟩
    obtain ⟨i, hi⟩ := hs1 t
    fin_cases i
    · exact hi (by simpa [h0] using (hre t).symm)
    · exact hi (by simpa [h0] using (him t).symm)

/-- `C([a, b], ℂ)` has stable range at most `1`. -/
theorem hasStableRangeLE_one_continuousMap_Icc_complex (a b : ℝ) :
    HasStableRangeLE C(Set.Icc a b, ℂ) 1 :=
  hasStableRangeLE_continuousMap_of_dense (dense_isUnimodular_continuousMap_Icc_complex a b)

/-- `C([a, b], ℝ)` has stable range at most `2`. -/
theorem hasStableRangeLE_two_continuousMap_Icc_real (a b : ℝ) :
    HasStableRangeLE C(Set.Icc a b, ℝ) 2 :=
  hasStableRangeLE_continuousMap_of_dense (dense_isUnimodular_continuousMap_Icc_real a b)

/-- For `a < b`, `C([a, b], ℝ)` does not have stable range at most `1`. -/
theorem not_hasStableRangeLE_one_continuousMap_Icc_real {a b : ℝ} (hab : a < b) :
    ¬HasStableRangeLE C(Set.Icc a b, ℝ) 1 := by
  -- The map from the endpoints to `{-1, 1}` taking `a` to `-1` and `b` to `1` has no nowhere
  -- vanishing continuous extension, by the intermediate value theorem.
  intro hR
  have : PreconnectedSpace (Set.Icc a b) := Subtype.preconnectedSpace isPreconnected_Icc
  let A : Set (Set.Icc a b) := {t | (t : ℝ) = a ∨ (t : ℝ) = b}
  have hA : IsClosed A :=
    (isClosed_eq continuous_subtypeVal continuous_const).union
      (isClosed_eq continuous_subtypeVal continuous_const)
  -- On the endpoints, `t ↦ (2t - a - b) / (b - a)` takes the values `-1` and `1`.
  let φ : C(A, Fin 1 → ℝ) := ⟨fun t _ ↦ (2 * (t : ℝ) - a - b) / (b - a), by fun_prop⟩
  have hba : b - a ≠ 0 := (sub_pos.2 hab).ne'
  have hφ (t : A) : φ t ≠ 0 := by
    intro h0
    have h1 : (2 * (t : ℝ) - a - b) / (b - a) = 0 := congr_fun h0 0
    rw [div_eq_zero_iff, or_iff_left hba] at h1
    rcases t.property with h | h <;> rw [h] at h1 <;> exact hba (by linarith)
  obtain ⟨F, hFA, hF⟩ := hR.exists_extension_ne_zero hA φ hφ
  have hval (t : Set.Icc a b) (ht : t ∈ A) : F t 0 = (2 * (t : ℝ) - a - b) / (b - a) :=
    congr_fun (congr($hFA ⟨t, ht⟩)) 0
  let l : Set.Icc a b := ⟨a, le_rfl, hab.le⟩
  let r : Set.Icc a b := ⟨b, hab.le, le_rfl⟩
  have hl : F l 0 = -1 := by
    rw [hval l (Or.inl rfl)]
    field_simp
    ring
  have hr : F r 0 = 1 := by
    rw [hval r (Or.inr rfl)]
    field_simp
    ring
  obtain ⟨t, ht⟩ := intermediate_value_univ l r (continuous_apply 0 |>.comp F.continuous)
    (show (0 : ℝ) ∈ Set.Icc (F l 0) (F r 0) by rw [hl, hr]; constructor <;> norm_num)
  exact hF t (funext fun i ↦ by rw [Fin.fin_one_eq_zero i]; exact ht)

end Icc

end TauCeti
