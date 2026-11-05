/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.HomogeneousSymbol
public import TauCeti.Analysis.Pseudodifferential.Symbol
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Cut-off homogeneous terms are symbols

A classical symbol of order `m` has an expansion `a ∼ ∑ⱼ χ(ξ) aₘ₋ⱼ(x, ξ)` whose terms are
homogeneous symbols `aₘ₋ⱼ` of degree `m - j`, made smooth at the zero frequency by a frequency
cutoff `χ`. For this expansion to make sense in the symbol classes, each cut-off term must be a
symbol of its degree. This file proves this:

* `TauCeti.HomogeneousSymbol.exists_norm_mixedDeriv_le`: on a compact set of positions, the mixed
  derivatives of a homogeneous symbol of degree `m` on `ℝⁿ × ℝⁿ` satisfy
  `‖∂_x^α ∂_ξ^β a(x, ξ)‖ ≤ C ‖ξ‖ ^ (m - |β|)` at every nonzero frequency;
* `TauCeti.HomogeneousSymbol.toSymbol χ`: the cut-off term `χ(ξ) • a(x, ξ)` as a symbol in
  `S^m_{1,0}`, linear in `a`. It vanishes for `‖ξ‖ ≤ 1`, has the same mixed derivatives as `a`
  for `‖ξ‖ > 2`
  (`TauCeti.HomogeneousSymbol.mixedDeriv_coefficient_toSymbol_of_two_lt_norm`), and commutes
  with spatial derivatives (`TauCeti.HomogeneousSymbol.spatialDeriv_toSymbol`);
* `TauCeti.HomogeneousSymbol.eq_zero_of_coefficient_toSymbol_eq`: uniqueness of homogeneous
  terms. If the cut-off term of a homogeneous symbol of degree `m` is a symbol of some order
  `m' < m`, the homogeneous symbol vanishes. In particular `toSymbol χ` is injective
  (`TauCeti.HomogeneousSymbol.toSymbol_injective`), and the homogeneous terms of a classical
  expansion are determined by the symbol.

The symbol estimates for `χ(ξ) • a(x, ξ)` come from the homogeneous bound for `‖ξ‖ > 2`, where
`‖ξ‖ ^ (m - |β|)` and `⟨ξ⟩ ^ (m - |β|) = (1 + ‖ξ‖²) ^ ((m - |β|) / 2)` are comparable, and from
compactness of `K × {‖ξ‖ ≤ 2}`.

## References

* M. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI* (2008), Lecture I, (1.17).
* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, §18.1.
-/

public section

noncomputable section

open Filter Metric
open scoped ContDiff Topology

namespace TauCeti

/-- For `t ≥ 1` and an exponent `r` of either sign, `t ^ r ≤ 2 ^ (|r| / 2) (1 + t²) ^ (r / 2)`. -/
private theorem rpow_le_two_rpow_mul_one_add_sq_rpow {t : ℝ} (ht : 1 ≤ t) (r : ℝ) :
    t ^ r ≤ 2 ^ (|r| / 2) * (1 + t ^ 2) ^ (r / 2) := by
  have hu : 0 < t ^ 2 := by positivity
  have hs : 0 < 1 + t ^ 2 := by positivity
  have htr : t ^ r = (t ^ 2) ^ (r / 2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
    congr 1
    push_cast
    ring
  rw [htr]
  rcases le_total 0 r with hr | hr
  · calc (t ^ 2) ^ (r / 2) ≤ (1 + t ^ 2) ^ (r / 2) :=
          Real.rpow_le_rpow hu.le (by linarith) (by linarith)
      _ ≤ 2 ^ (|r| / 2) * (1 + t ^ 2) ^ (r / 2) :=
          le_mul_of_one_le_left (by positivity)
            (Real.one_le_rpow (by norm_num) (by positivity))
  · -- For a nonpositive exponent use `(1 + t²) / 2 ≤ t²`, and `2 ^ (|r| / 2) = 2 ^ (-(r / 2))`.
    have h2 : (1 + t ^ 2) / 2 ≤ t ^ 2 := by nlinarith
    calc (t ^ 2) ^ (r / 2) ≤ ((1 + t ^ 2) / 2) ^ (r / 2) :=
          Real.rpow_le_rpow_of_nonpos (by positivity) h2 (by linarith)
      _ = 2 ^ (|r| / 2) * (1 + t ^ 2) ^ (r / 2) := by
          rw [Real.div_rpow hs.le (by norm_num), abs_of_nonpos hr, neg_div, Real.rpow_neg
            (by norm_num), div_eq_inv_mul]

/-- For `t ≥ 1` and an exponent `r` of either sign, `(1 + t²) ^ (r / 2) ≤ 2 ^ (|r| / 2) t ^ r`. -/
private theorem one_add_sq_rpow_le_two_rpow_mul_rpow {t : ℝ} (ht : 1 ≤ t) (r : ℝ) :
    (1 + t ^ 2) ^ (r / 2) ≤ 2 ^ (|r| / 2) * t ^ r := by
  have hu : 0 < t ^ 2 := by positivity
  have htr : t ^ r = (t ^ 2) ^ (r / 2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
    congr 1
    push_cast
    ring
  rw [htr]
  rcases le_total 0 r with hr | hr
  · -- For a nonnegative exponent use `1 + t² ≤ 2 t²`.
    calc (1 + t ^ 2) ^ (r / 2) ≤ (2 * t ^ 2) ^ (r / 2) :=
          Real.rpow_le_rpow (by positivity) (by nlinarith) (by linarith)
      _ = 2 ^ (|r| / 2) * (t ^ 2) ^ (r / 2) := by
          rw [Real.mul_rpow (by norm_num) hu.le, abs_of_nonneg hr]
  · calc (1 + t ^ 2) ^ (r / 2) ≤ (t ^ 2) ^ (r / 2) :=
          Real.rpow_le_rpow_of_nonpos hu (by linarith) (by linarith)
      _ ≤ 2 ^ (|r| / 2) * (t ^ 2) ^ (r / 2) :=
          le_mul_of_one_le_left (by positivity)
            (Real.one_le_rpow (by norm_num) (by positivity))

/-- For `|t| ≤ 2` and an exponent `r` of either sign, `(1 + t²) ^ (r / 2)` is at least
`5 ^ (-|r| / 2)`. -/
private theorem one_le_five_rpow_mul_one_add_sq_rpow {t : ℝ} (ht : |t| ≤ 2) (r : ℝ) :
    1 ≤ 5 ^ (|r| / 2) * (1 + t ^ 2) ^ (r / 2) := by
  have hs : 1 ≤ 1 + t ^ 2 := by nlinarith [sq_nonneg t]
  have hs5 : 1 + t ^ 2 ≤ 5 := by nlinarith [sq_abs t, abs_nonneg t]
  calc (1 : ℝ) ≤ (1 + t ^ 2) ^ ((|r| + r) / 2) :=
        Real.one_le_rpow hs (by linarith [neg_abs_le r])
    _ = (1 + t ^ 2) ^ (|r| / 2) * (1 + t ^ 2) ^ (r / 2) := by
        rw [← Real.rpow_add (by linarith), add_div]
    _ ≤ 5 ^ (|r| / 2) * (1 + t ^ 2) ^ (r / 2) := by
        gcongr

namespace HomogeneousSymbol

variable {n : ℕ} {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {E : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [NormedAddCommGroup W] [NormedSpace ℂ W] {m : ℝ}

/-! ### Mixed derivatives of homogeneous symbols -/

/-- The iterated frequency derivative `∂_ξ^β a`, a homogeneous symbol of degree `m - |β|`. -/
private def iterFrequencyDeriv (a : HomogeneousSymbol X (CoordinateSpace n) V W m) :
    (β : List (Fin n)) → HomogeneousSymbol X (CoordinateSpace n) V W (m - β.length)
  | [] => a.castDegree (by simp)
  | j :: js => ((iterFrequencyDeriv a js).frequencyDeriv (EuclideanSpace.single j 1)).castDegree
      (by simp only [List.length_cons]; push_cast; ring)

/-- The iterated spatial derivative `∂_x^α a`, a homogeneous symbol of the same degree. -/
private def iterSpatialDeriv (a : HomogeneousSymbol (CoordinateSpace n) E V W m) :
    List (Fin n) → HomogeneousSymbol (CoordinateSpace n) E V W m
  | [] => a
  | j :: js => (iterSpatialDeriv a js).spatialDeriv (EuclideanSpace.single j 1)

private theorem coefficient_iterFrequencyDeriv (a : HomogeneousSymbol X (CoordinateSpace n) V W m)
    (β : List (Fin n)) (x : X) {ξ : CoordinateSpace n} (hξ : ξ ≠ 0) :
    (iterFrequencyDeriv a β).coefficient (x, ξ) =
      coordinateDeriv β (fun η => a.coefficient (x, η)) ξ := by
  induction β generalizing ξ with
  | nil => simp [iterFrequencyDeriv]
  | cons j js ih =>
    -- The two sides are derivatives of functions that agree on the open set of nonzero
    -- frequencies.
    have h : (fun η => (iterFrequencyDeriv a js).coefficient (x, η)) =ᶠ[𝓝 ξ]
        coordinateDeriv js (fun η => a.coefficient (x, η)) :=
      eventually_of_mem (isOpen_ne.mem_nhds hξ) fun η hη => ih hη
    rw [iterFrequencyDeriv, coefficient_castDegree, coefficient_frequencyDeriv _ _ hξ,
      coordinateDeriv_cons, h.fderiv_eq]

private theorem coefficient_iterSpatialDeriv (a : HomogeneousSymbol (CoordinateSpace n) E V W m)
    (α : List (Fin n)) (x : CoordinateSpace n) {ξ : E} (hξ : ξ ≠ 0) :
    (iterSpatialDeriv a α).coefficient (x, ξ) =
      coordinateDeriv α (fun y => a.coefficient (y, ξ)) x := by
  induction α generalizing x with
  | nil => simp [iterSpatialDeriv]
  | cons j js ih =>
    rw [iterSpatialDeriv, coefficient_spatialDeriv _ _ hξ, coordinateDeriv_cons, funext ih]

/-- **Growth of the mixed derivatives of a homogeneous symbol.** On a compact set of positions,
the mixed derivatives of a homogeneous symbol of degree `m` satisfy
`‖∂_x^α ∂_ξ^β a(x, ξ)‖ ≤ C ‖ξ‖ ^ (m - |β|)` at every nonzero frequency. -/
theorem exists_norm_mixedDeriv_le
    (a : HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W m)
    {K : Set (CoordinateSpace n)} (hK : IsCompact K) (α β : List (Fin n)) :
    ∃ C, 0 ≤ C ∧ ∀ x ∈ K, ∀ ξ, ξ ≠ 0 →
      ‖mixedDeriv α β a.coefficient x ξ‖ ≤ C * ‖ξ‖ ^ (m - β.length) := by
  obtain ⟨C, hC, hCK⟩ := (iterSpatialDeriv (iterFrequencyDeriv a β) α).exists_norm_coefficient_le hK
  refine ⟨C, hC, fun x hx ξ hξ => ?_⟩
  have h : (iterSpatialDeriv (iterFrequencyDeriv a β) α).coefficient (x, ξ) =
      mixedDeriv α β a.coefficient x ξ := by
    rw [coefficient_iterSpatialDeriv _ _ _ hξ, mixedDeriv_def]
    exact congrArg (coordinateDeriv α · x)
      (funext fun y => coefficient_iterFrequencyDeriv a β y hξ)
  exact h ▸ hCK x hx ξ

/-! ### The cut-off term -/

/-- Beyond the transition annulus of the cutoff, the cut-off term `χ(ξ) • a(x, ξ)` has the same
mixed derivatives as `a`. -/
private theorem mixedDeriv_smul_coefficient_of_two_lt_norm (χ : FrequencyCutoff (CoordinateSpace n))
    (a : HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W m) (α β : List (Fin n))
    (x : CoordinateSpace n) {ξ : CoordinateSpace n} (hξ : 2 < ‖ξ‖) :
    mixedDeriv α β (fun p => χ p.2 • a.coefficient p) x ξ =
      mixedDeriv α β a.coefficient x ξ := by
  simp only [mixedDeriv_def]
  congr 1
  funext y
  refine (EventuallyEq.coordinateDeriv ?_ β).eq_of_nhds
  filter_upwards [χ.eventuallyEq_one_of_two_lt_norm hξ] with η hη
  rw [hη, Pi.one_apply, one_smul]

/-- The symbol estimates for the cut-off term `χ(ξ) • a(x, ξ)` of a homogeneous symbol of
degree `m`. -/
private theorem exists_bound_smul_coefficient (χ : FrequencyCutoff (CoordinateSpace n))
    (a : HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W m)
    {K : Set (CoordinateSpace n)} (hK : IsCompact K) (α β : List (Fin n)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ K, ∀ ξ,
      ‖mixedDeriv α β (fun p => χ p.2 • a.coefficient p) x ξ‖ ≤
        C * (1 + ‖ξ‖ ^ 2) ^ ((m - β.length) / 2) := by
  set r : ℝ := m - β.length
  -- For `‖ξ‖ > 2` the cut-off term agrees with `a` near `ξ`, which is homogeneous.
  obtain ⟨C, hC, hCK⟩ := a.exists_norm_mixedDeriv_le hK α β
  -- On the compact set `K × {‖ξ‖ ≤ 2}` the smooth cut-off term has bounded mixed derivatives.
  obtain ⟨B, hB⟩ := (hK.prod (isCompact_closedBall (0 : CoordinateSpace n) 2))
    |>.exists_bound_of_continuousOn
      ((a.contDiff_smul_coefficient χ).mixedDeriv α β).continuous.continuousOn
  refine ⟨C * 2 ^ (|r| / 2) + max B 0 * 5 ^ (|r| / 2), by positivity, fun x hx ξ => ?_⟩
  have hw : 0 ≤ (1 + ‖ξ‖ ^ 2) ^ (r / 2) := by positivity
  rcases le_or_gt ‖ξ‖ 2 with hξ | hξ
  · have h := hB (x, ξ) (Set.mk_mem_prod hx (mem_closedBall_zero_iff.2 hξ))
    calc _ ≤ max B 0 := h.trans (le_max_left _ _)
      _ ≤ max B 0 * (5 ^ (|r| / 2) * (1 + ‖ξ‖ ^ 2) ^ (r / 2)) :=
          le_mul_of_one_le_right (le_max_right _ _)
            (one_le_five_rpow_mul_one_add_sq_rpow (by rwa [abs_norm]) r)
      _ ≤ _ := by rw [add_mul, ← mul_assoc]; exact le_add_of_nonneg_left (by positivity)
  · rw [mixedDeriv_smul_coefficient_of_two_lt_norm χ a α β x hξ]
    have hξ0 : ξ ≠ 0 := norm_pos_iff.1 (by linarith)
    calc _ ≤ C * ‖ξ‖ ^ r := hCK x hx ξ hξ0
      _ ≤ C * (2 ^ (|r| / 2) * (1 + ‖ξ‖ ^ 2) ^ (r / 2)) :=
          mul_le_mul_of_nonneg_left (rpow_le_two_rpow_mul_one_add_sq_rpow (by linarith) r) hC
      _ ≤ _ := by rw [add_mul, ← mul_assoc]; exact le_add_of_nonneg_right (by positivity)

/-- The cut-off term `χ(ξ) • a(x, ξ)` of a homogeneous symbol `a` of degree `m`, a symbol of
order `m`. This is how the homogeneous terms of a classical expansion enter the symbol
classes. -/
def toSymbol (χ : FrequencyCutoff (CoordinateSpace n)) :
    HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W m →ₗ[ℂ] Symbol n V W m where
  toFun a :=
    { coefficient := fun p => χ p.2 • a.coefficient p
      contDiff_coefficient := a.contDiff_smul_coefficient χ
      exists_bound := fun _ hK α β => exists_bound_smul_coefficient χ a hK α β }
  map_add' a b := by
    ext1
    funext p
    simp [smul_add]
  map_smul' c a := by
    ext1
    funext p
    simp [smul_comm (χ p.2) c]

variable (χ : FrequencyCutoff (CoordinateSpace n))
  (a : HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W m)

@[simp]
theorem coefficient_toSymbol (p : CoordinateSpace n × CoordinateSpace n) :
    (toSymbol χ a).coefficient p = χ p.2 • a.coefficient p := (rfl)

/-- For `‖ξ‖ ≥ 2` the cut-off term is the homogeneous symbol itself. -/
theorem coefficient_toSymbol_of_two_le_norm (x : CoordinateSpace n) {ξ : CoordinateSpace n}
    (hξ : 2 ≤ ‖ξ‖) : (toSymbol χ a).coefficient (x, ξ) = a.coefficient (x, ξ) := by
  simp [χ.apply_eq_one_of_two_le_norm hξ]

/-- For `‖ξ‖ > 2` the cut-off term has the same mixed derivatives as the homogeneous symbol. -/
theorem mixedDeriv_coefficient_toSymbol_of_two_lt_norm (α β : List (Fin n)) (x : CoordinateSpace n)
    {ξ : CoordinateSpace n} (hξ : 2 < ‖ξ‖) :
    mixedDeriv α β (toSymbol χ a).coefficient x ξ = mixedDeriv α β a.coefficient x ξ :=
  mixedDeriv_smul_coefficient_of_two_lt_norm χ a α β x hξ

/-- For `‖ξ‖ ≤ 1` the cut-off term vanishes. -/
theorem coefficient_toSymbol_of_norm_le_one (x : CoordinateSpace n) {ξ : CoordinateSpace n}
    (hξ : ‖ξ‖ ≤ 1) : (toSymbol χ a).coefficient (x, ξ) = 0 := by
  simp [χ.apply_eq_zero_of_norm_le_one hξ]

/-- A spatial derivative of the cut-off term is the cut-off term of the spatial derivative: the
cutoff does not depend on the position. -/
@[simp]
theorem spatialDeriv_toSymbol (j : Fin n) :
    Symbol.spatialDeriv j (toSymbol χ a) =
      toSymbol χ (a.spatialDeriv (EuclideanSpace.single j 1)) := by
  ext1
  funext ⟨x, ξ⟩
  simp only [Symbol.coefficient_spatialDeriv, coefficient_toSymbol, coordinateDeriv_cons,
    coordinateDeriv_nil]
  rcases eq_or_ne ξ 0 with rfl | hξ
  · simp [χ.apply_zero]
  · have hd : DifferentiableAt ℝ (fun y => a.coefficient (y, ξ)) x :=
      (a.differentiableAt_coefficient (p := (x, ξ)) hξ).comp x (by fun_prop)
    rw [fderiv_fun_const_smul hd, smul_apply, coefficient_spatialDeriv _ _ hξ]

/-! ### Uniqueness of homogeneous terms -/

/-- **Uniqueness of homogeneous terms.** If the cut-off term `χ(ξ) • a(x, ξ)` of a homogeneous
symbol of degree `m` is a symbol of some lower order `m' < m`, then `a = 0`. -/
theorem eq_zero_of_coefficient_toSymbol_eq {m' : ℝ} (hm : m' < m) (b : Symbol n V W m')
    (hb : (toSymbol χ a).coefficient = b.coefficient) : a = 0 := by
  refine ext_of_ne_zero fun x ξ hξ => ?_
  rw [coefficient_zero, Pi.zero_apply, ← norm_le_zero_iff]
  obtain ⟨C, hC, hCb⟩ := b.exists_bound {x} isCompact_singleton [] []
  have hn : 0 < ‖ξ‖ := norm_pos_iff.2 hξ
  set D := C * 2 ^ (|m'| / 2) * ‖ξ‖ ^ m'
  -- Along the ray `t ↦ t • ξ` the homogeneous term grows like `t ^ m`, while the symbol `b` of
  -- order `m'` grows at most like `t ^ m'`: far out, `t ^ m ‖a(x, ξ)‖ ≤ D t ^ m'`.
  have key : ∀ t, 2 / ‖ξ‖ ≤ t → ‖a.coefficient (x, ξ)‖ ≤ D * t ^ (m' - m) := by
    intro t ht
    have ht0 : 0 < t := lt_of_lt_of_le (by positivity) ht
    have htξ : 2 ≤ ‖t • ξ‖ := by
      rw [norm_smul, Real.norm_of_nonneg ht0.le]
      exact (div_le_iff₀ hn).1 ht
    have h := hCb x rfl (t • ξ)
    rw [mixedDeriv_nil_nil, ← hb, coefficient_toSymbol_of_two_le_norm χ a x htξ,
      a.homogeneous x ξ t ht0, norm_smul, Real.norm_of_nonneg (by positivity)] at h
    simp only [List.length_nil, CharP.cast_eq_zero, sub_zero] at h
    have hw := one_add_sq_rpow_le_two_rpow_mul_rpow (by linarith) m' (t := ‖t • ξ‖)
    rw [norm_smul, Real.norm_of_nonneg ht0.le, Real.mul_rpow ht0.le hn.le] at hw
    rw [Real.rpow_sub ht0, ← mul_div_assoc, le_div_iff₀' (by positivity)]
    calc t ^ m * ‖a.coefficient (x, ξ)‖ ≤ C * (1 + (t * ‖ξ‖) ^ 2) ^ (m' / 2) := by
          rwa [norm_smul, Real.norm_of_nonneg ht0.le] at h
      _ ≤ C * (2 ^ (|m'| / 2) * (t ^ m' * ‖ξ‖ ^ m')) := mul_le_mul_of_nonneg_left hw hC
      _ = D * t ^ m' := by ring
  have hlim : Tendsto (fun t : ℝ => D * t ^ (m' - m)) atTop (𝓝 0) := by
    simpa [neg_sub] using (tendsto_rpow_neg_atTop (sub_pos.2 hm)).const_mul D
  exact ge_of_tendsto hlim (eventually_atTop.2 ⟨2 / ‖ξ‖, key⟩)

/-- A homogeneous symbol is determined by its cut-off term. -/
theorem toSymbol_injective :
    Function.Injective (toSymbol χ :
      HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W m →ₗ[ℂ] Symbol n V W m) :=
  (injective_iff_map_eq_zero _).2 fun a ha =>
    eq_zero_of_coefficient_toSymbol_eq χ a (sub_one_lt m) (0 : Symbol n V W (m - 1)) (by
      rw [ha, Symbol.coefficient_zero, Symbol.coefficient_zero])

end HomogeneousSymbol

end TauCeti
