/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Convex.Sequence.FiniteSlopeMultiset
public import TauCeti.Data.Rat.NumDenDvd
public import TauCeti.NumberTheory.NewtonPolygon.Basic
public import TauCeti.RingTheory.Valuation.AddValuation

/-!
# Finite slopes of the Newton polygon of a polynomial

The Newton polygon of a polynomial has finitely many finite unit edges. Its *finite slope
multiset* `Polynomial.newtonSlopes f v` lists the slopes of these edges, with multiplicity.
With the orientation of `Polynomial.newtonPolygon`, a slope `m` corresponds to a nonzero root
of valuation `-m`; for a linear polynomial `X - C α` with `v α` finite this is
`Polynomial.newtonSlopes_X_sub_C`. These multisets are the invariants in which the slopes of
products and of split polynomials are stated.

The multiset depends only on the polygon. Whenever the polygon is nonempty it is represented
by finite slope data, and the finite slope multiset is the slope multiset of that
presentation, so the geometric results about `TauCeti.FiniteSlopeData.slopeMultiset` apply.

## Main definitions

* `Polynomial.newtonSlopes f v`: the multiset of the slopes of the finite unit edges of
  `f.newtonPolygon v`.

## Main results

* `Polynomial.newtonSlopes_eq_slopeMultiset`: the finite slope multiset is the slope multiset
  of any finite slope data representing the Newton polygon, and by
  `Polynomial.exists_finiteSlopeData_heights_eq_iff` such data exists exactly when the
  polygon is nonempty.
* `Polynomial.card_newtonSlopes`: if only zero has infinite valuation, a polynomial of degree
  `d` and order of vanishing `a` at zero has `d - a` finite slopes.
* `Polynomial.sum_newtonSlopes`: their sum is the difference between the valuations of the
  leading and trailing coefficients.
* `Polynomial.den_dvd_card_newtonSlopes`: for a valuation taking integer values on nonzero
  elements, if every finite slope equals the rational `q`, then the denominator of `q` divides
  the number of finite slopes.
* `Polynomial.count_newtonSlopes_of_isFiniteFace`: the multiplicity of a slope `σ` is the
  width of the face of slope `σ`.
* `Polynomial.left_eq_natTrailingDegree_add_card_filter_newtonSlopes_lt` and
  `Polynomial.right_eq_natTrailingDegree_add_card_filter_newtonSlopes_le`: the absolute
  endpoints of the face of slope `σ` are the order of vanishing at zero plus the number of
  finite slopes below `σ`, respectively at most `σ`.
* `Polynomial.newtonSlopes_C_mul`, `Polynomial.newtonSlopes_X_pow_mul`,
  `Polynomial.newtonSlopes_comp_C_mul_X` and `Polynomial.newtonSlopes_map`: multiplication by
  a scalar of finite valuation and by `X ^ k` preserves the slopes, the substitution
  `X ↦ c X` adds the valuation of `c` to every slope, and an extension of coefficients
  compatible with the valuations preserves them.
* `Polynomial.newtonSlopes_monomial`: a monomial, in particular a constant, has no finite
  slopes.
* `Polynomial.newtonSlopes_X_sub_C`: the only finite slope of `X - C α` is `-v α`.

## References

* N. Koblitz, *p-adic Numbers, p-adic Analysis, and Zeta-Functions*, second edition,
  Graduate Texts in Mathematics 58, Springer, 1984, Chapter IV §3.
-/

public section

open TauCeti

namespace Polynomial

variable {R S : Type*} [Ring R] [Ring S] (f : R[X]) (v : AddValuation R (WithTop ℝ))

/-- The Newton polygon of a polynomial has only finitely many finite unit edges, all before
the degree. -/
theorem finite_finiteEdges_newtonPolygon : (finiteEdges (f.newtonPolygon v)).Finite :=
  (Set.finite_Iio f.natDegree).subset fun n hn => Set.mem_Iio.mpr <|
    lt_of_not_ge fun h : f.natDegree ≤ n =>
      (mem_finiteEdges.mp hn).2 (f.newtonPolygon_eq_top_of_natDegree_lt v (by omega))

/-- The finite slope multiset of the Newton polygon of a polynomial: the slopes of all of its
finite unit edges, counted with multiplicity. The zero polynomial has no finite slopes. -/
noncomputable def newtonSlopes : Multiset ℝ :=
  (f.finite_finiteEdges_newtonPolygon v).toFinset.val.map (unitSlope (f.newtonPolygon v))

/-- The finite slope multiset is the image of the finite unit edges under their slopes. -/
theorem newtonSlopes_def :
    f.newtonSlopes v =
      (f.finite_finiteEdges_newtonPolygon v).toFinset.val.map (unitSlope (f.newtonPolygon v)) :=
  (rfl)

/-- A real number is a finite slope exactly when it is the slope of a finite unit edge. -/
@[simp]
theorem mem_newtonSlopes {m : ℝ} :
    m ∈ f.newtonSlopes v ↔
      ∃ n ∈ finiteEdges (f.newtonPolygon v), unitSlope (f.newtonPolygon v) n = m := by
  simp [newtonSlopes_def]

variable {f v}

/-- Transport of finite slopes along a matching of finite unit edges. -/
private theorem newtonSlopes_eq_map {g : S[X]} {w : AddValuation S (WithTop ℝ)}
    {φ : ℕ → ℕ} (hφ : φ.Injective) {t : ℝ → ℝ}
    (hedges : finiteEdges (g.newtonPolygon w) = φ '' finiteEdges (f.newtonPolygon v))
    (hslope : ∀ n ∈ finiteEdges (f.newtonPolygon v),
      unitSlope (g.newtonPolygon w) (φ n) = t (unitSlope (f.newtonPolygon v) n)) :
    g.newtonSlopes w = (f.newtonSlopes v).map t := by
  have hfin : (g.finite_finiteEdges_newtonPolygon w).toFinset =
      (f.finite_finiteEdges_newtonPolygon v).toFinset.map ⟨φ, hφ⟩ := by
    ext n
    simp [hedges]
  rw [newtonSlopes_def, newtonSlopes_def, hfin, Finset.map_val, Multiset.map_map,
    Multiset.map_map]
  exact Multiset.map_congr rfl fun n hn => hslope n (by simpa using hn)

/-- The finite slope multiset depends only on the Newton polygon. -/
theorem newtonSlopes_congr {g : S[X]} {w : AddValuation S (WithTop ℝ)}
    (h : f.newtonPolygon v = g.newtonPolygon w) : f.newtonSlopes v = g.newtonSlopes w := by
  rw [newtonSlopes_eq_map (f := g) (v := w) (g := f) (w := v) Function.injective_id (t := id)
    (by rw [h, Set.image_id]) (fun n _ => by rw [h, id, id]), Multiset.map_id]

/-- The finite slope multiset is the slope multiset of any finite slope data representing the
Newton polygon. -/
theorem newtonSlopes_eq_slopeMultiset {d : FiniteSlopeData ℝ}
    (hd : d.heights = f.newtonPolygon v) : f.newtonSlopes v = d.slopeMultiset := by
  have hfin : (f.finite_finiteEdges_newtonPolygon v).toFinset =
      (Finset.univ : Finset (Fin d.length)).map
        (Fin.valEmbedding.trans (addLeftEmbedding d.start)) := by
    ext n
    simp only [Set.Finite.mem_toFinset, mem_finiteEdges, ← hd, ne_eq,
      FiniteSlopeData.heights_eq_top_iff, not_or, not_lt, Finset.mem_map, Finset.mem_univ,
      true_and, Function.Embedding.trans_apply, Fin.valEmbedding_apply, addLeftEmbedding_apply]
    constructor
    · rintro ⟨⟨h₁, -⟩, -, h₂⟩
      exact ⟨⟨n - d.start, by omega⟩, by dsimp only; omega⟩
    · rintro ⟨i, rfl⟩
      have := i.2
      omega
  rw [newtonSlopes_def, hfin, Finset.map_val, Multiset.map_map, d.slopeMultiset_def,
    ← Fin.univ_val_map, ← hd]
  exact Multiset.map_congr rfl fun i _ => d.unitSlope_heights i

variable (f v) in
/-- The Newton polygon of a polynomial is represented by finite slope data exactly when it is
nonempty. -/
theorem exists_finiteSlopeData_heights_eq_iff :
    (∃ d : FiniteSlopeData ℝ, d.heights = f.newtonPolygon v) ↔ f.newtonPolygon v ≠ ⊤ := by
  rw [FiniteSlopeData.exists_heights_eq_iff]
  refine ⟨?_, fun h => ⟨f.isConvexSeq_newtonPolygon v, ?_, ?_⟩⟩
  · rintro ⟨-, ⟨n, hn⟩, -⟩ h
    exact hn (by rw [h]; rfl)
  · obtain ⟨n, hn⟩ := Function.ne_iff.mp h
    exact ⟨n, hn⟩
  · exact (Set.finite_Iic f.natDegree).subset fun n hn =>
      Set.mem_Iic.mpr (le_of_not_gt fun h => hn (f.newtonPolygon_eq_top_of_natDegree_lt v h))

/-- The multiplicity of a real slope `σ` among the finite slopes is the width `u - l` of the
finite face of slope `σ`. The endpoints `l` and `u` are absolute indices, and a singleton face
contributes multiplicity zero. -/
theorem count_newtonSlopes_of_isFiniteFace {σ : ℝ} {l u : ℕ}
    (hface : IsFiniteFace (f.newtonPolygon v) σ l u) : (f.newtonSlopes v).count σ = u - l := by
  obtain ⟨d, hd⟩ := (exists_finiteSlopeData_heights_eq_iff f v).2 fun h =>
    hface.left_ne_top (by rw [h]; rfl)
  rw [newtonSlopes_eq_slopeMultiset hd]
  exact d.count_slopeMultiset_of_isFiniteFace (hd ▸ hface)

variable (f v) in
/-- The number of finite slopes satisfying a predicate is the number of finite unit edges whose
slope satisfies it. -/
private theorem card_filter_newtonSlopes (p : ℝ → Prop) [DecidablePred p] :
    ((f.newtonSlopes v).filter p).card =
      {i | i ∈ finiteEdges (f.newtonPolygon v) ∧ p (unitSlope (f.newtonPolygon v) i)}.ncard := by
  rw [newtonSlopes_def, Multiset.filter_map, Multiset.card_map, ← Finset.filter_val,
    Finset.card_val, ← Set.ncard_coe_finset]
  congr 1
  ext i
  simp

/-- If only zero has infinite valuation, the left endpoint of the finite face of slope `σ` is
the order of vanishing at zero plus the number of finite slopes strictly less than `σ`. The
endpoint is an absolute index. -/
theorem left_eq_natTrailingDegree_add_card_filter_newtonSlopes_lt (hv : ∀ x, v x = ⊤ → x = 0)
    {σ : ℝ} {l u : ℕ} (hface : IsFiniteFace (f.newtonPolygon v) σ l u) :
    l = f.natTrailingDegree + ((f.newtonSlopes v).filter (· < σ)).card := by
  have hf : f ≠ 0 := by
    rintro rfl
    exact hface.left_ne_top (by simp)
  rw [card_filter_newtonSlopes]
  exact hface.left_eq_start_add_ncard_unitSlope_lt (f.isConvexSeq_newtonPolygon v)
    ((newtonPolygon_ne_top_iff v hv hf).mpr ⟨le_rfl, natTrailingDegree_le_natDegree f⟩)
    fun n hn => ((newtonPolygon_ne_top_iff v hv hf).mp hn).1

/-- If only zero has infinite valuation, the right endpoint of the finite face of slope `σ` is
the order of vanishing at zero plus the number of finite slopes at most `σ`. The endpoint is an
absolute index. -/
theorem right_eq_natTrailingDegree_add_card_filter_newtonSlopes_le (hv : ∀ x, v x = ⊤ → x = 0)
    {σ : ℝ} {l u : ℕ} (hface : IsFiniteFace (f.newtonPolygon v) σ l u) :
    u = f.natTrailingDegree + ((f.newtonSlopes v).filter (· ≤ σ)).card := by
  have hf : f ≠ 0 := by
    rintro rfl
    exact hface.left_ne_top (by simp)
  rw [card_filter_newtonSlopes]
  exact hface.right_eq_start_add_ncard_unitSlope_le (f.isConvexSeq_newtonPolygon v)
    ((newtonPolygon_ne_top_iff v hv hf).mpr ⟨le_rfl, natTrailingDegree_le_natDegree f⟩)
    fun n hn => ((newtonPolygon_ne_top_iff v hv hf).mp hn).1

/-! ### Length and total height change -/

variable (f v)

/-- If only zero has infinite valuation, a polynomial of degree `d` and order of vanishing `a`
at zero has exactly `d - a` finite slopes, counted with multiplicity. -/
theorem card_newtonSlopes (hv : ∀ x, v x = ⊤ → x = 0) :
    (f.newtonSlopes v).card = f.natDegree - f.natTrailingDegree := by
  rw [newtonSlopes_def, Multiset.card_map, Finset.card_val,
    ← Set.ncard_eq_toFinset_card _ (f.finite_finiteEdges_newtonPolygon v),
    ncard_finiteEdges_newtonPolygon f v hv]

/-- If only zero has infinite valuation, the sum of the finite slopes of a polynomial is the
valuation of its leading coefficient minus that of its trailing coefficient. -/
theorem sum_newtonSlopes (hv : ∀ x, v x = ⊤ → x = 0) :
    (f.newtonSlopes v).sum = (v f.leadingCoeff).untop₀ - (v f.trailingCoeff).untop₀ := by
  rcases eq_or_ne f 0 with rfl | hf
  · simp [Multiset.card_eq_zero.mp (by simpa using card_newtonSlopes (0 : R[X]) v hv)]
  have hdom (n : ℕ) : f.newtonPolygon v n ≠ ⊤ ↔ f.natTrailingDegree ≤ n ∧
      n ≤ f.natTrailingDegree + (f.natDegree - f.natTrailingDegree) := by
    rw [newtonPolygon_ne_top_iff v hv hf]
    have := natTrailingDegree_le_natDegree f
    omega
  have hd := FiniteSlopeData.heights_ofIsConvexSeq (f.isConvexSeq_newtonPolygon v) hdom
  rw [newtonSlopes_eq_slopeMultiset hd, FiniteSlopeData.sum_slopeMultiset, hd,
    FiniteSlopeData.ofIsConvexSeq_start, FiniteSlopeData.ofIsConvexSeq_length,
    Nat.add_sub_cancel' (natTrailingDegree_le_natDegree f), newtonPolygon_natDegree,
    newtonPolygon_natTrailingDegree]

variable {f v} in
/-- If the valuation takes integer values on nonzero elements and every finite slope of `f`
equals the rational number `q`, then the denominator of `q` divides the number of finite slopes
of `f`, that is, the horizontal length of its Newton polygon. -/
theorem den_dvd_card_newtonSlopes (hint : ∀ x, x ≠ 0 → ∃ n : ℤ, v x = ((n : ℝ) : WithTop ℝ))
    {q : ℚ} (hf : ∀ m ∈ f.newtonSlopes v, m = q) :
    q.den ∣ (f.newtonSlopes v).card := by
  have hv := AddValuation.eq_zero_of_eq_top_of_forall_ne_zero hint
  rcases eq_or_ne f 0 with rfl | hf₀
  · simp [card_newtonSlopes (0 : R[X]) v hv]
  obtain ⟨a, ha⟩ := hint _ (leadingCoeff_ne_zero.mpr hf₀)
  obtain ⟨b, hb⟩ := hint _ (trailingCoeff_nonzero_iff_nonzero.mpr hf₀)
  have hsum := sum_newtonSlopes f v hv
  rw [Multiset.eq_replicate_card.mpr hf, Multiset.sum_replicate, nsmul_eq_mul,
    ha, hb, WithTop.untop₀_coe, WithTop.untop₀_coe] at hsum
  have hq : ((a - b : ℤ) : ℚ) = q * ((f.newtonSlopes v).card : ℤ) := by
    rw [mul_comm]
    exact_mod_cast hsum.symm
  exact Int.natCast_dvd_natCast.mp (Rat.den_dvd_of_intCast_eq_mul_intCast q hq)

/-! ### Elementary operations -/

/-- A monomial, in particular a constant, has no finite slopes. -/
@[simp]
theorem newtonSlopes_monomial (k : ℕ) (c : R) : (monomial k c).newtonSlopes v = 0 := by
  rw [newtonSlopes_def, Multiset.map_eq_zero, Finset.val_eq_zero,
    Set.Finite.toFinset_eq_empty]
  exact finiteEdges_newtonPolygon_monomial v k c

/-- The zero polynomial has no finite slopes. -/
@[simp]
theorem newtonSlopes_zero : (0 : R[X]).newtonSlopes v = 0 := by
  simpa using newtonSlopes_monomial v 0 (0 : R)

/-- A constant polynomial has no finite slopes. -/
@[simp]
theorem newtonSlopes_C (c : R) : (C c).newtonSlopes v = 0 := by
  simpa using newtonSlopes_monomial v 0 c

/-- Multiplying by a constant of finite valuation preserves the finite slopes. -/
theorem newtonSlopes_C_mul {c : R} (hc : v c ≠ ⊤) :
    (C c * f).newtonSlopes v = f.newtonSlopes v := by
  obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp hc
  have hpoly : (C c * f).newtonPolygon v =
      fun n => f.newtonPolygon v n + ((r + 0 * n : ℝ) : WithTop ℝ) := by
    simp [newtonPolygon_C_mul, ← hr, add_comm]
  rw [newtonSlopes_eq_map (f := f) (v := v) Function.injective_id (t := id)
    (by rw [hpoly, finiteEdges_add_affine, Set.image_id])
    (fun n hn => by rw [hpoly, id, id, unitSlope_add_affine hn, add_zero]), Multiset.map_id]

/-- Multiplying by a scalar of finite valuation preserves the finite slopes. -/
theorem newtonSlopes_smul {c : R} (hc : v c ≠ ⊤) :
    (c • f).newtonSlopes v = f.newtonSlopes v := by
  rw [smul_eq_C_mul, newtonSlopes_C_mul f v hc]

/-- Multiplying by `X ^ k` preserves the finite slopes. -/
@[simp]
theorem newtonSlopes_X_pow_mul (k : ℕ) : (X ^ k * f).newtonSlopes v = f.newtonSlopes v := by
  rw [newtonSlopes_eq_map (f := f) (v := v) (φ := (· + k)) (add_left_injective k) (t := id)
    (by rw [newtonPolygon_X_pow_mul, finiteEdges_shift])
    (fun n _ => by rw [newtonPolygon_X_pow_mul, unitSlope_shift, id]), Multiset.map_id]

/-- Substituting `c X` for `X` adds the valuation of `c` to every finite slope, provided that
valuation is finite. -/
theorem newtonSlopes_comp_C_mul_X {c : R} (hc : v c ≠ ⊤) :
    (f.comp (C c * X)).newtonSlopes v = (f.newtonSlopes v).map (· + (v c).untop₀) := by
  obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp hc
  have hpoly : (f.comp (C c * X)).newtonPolygon v =
      fun n => f.newtonPolygon v n + ((0 + r * n : ℝ) : WithTop ℝ) := by
    simp only [f.newtonPolygon_comp_C_mul_X v hc, ← hr, ← WithTop.coe_nsmul, nsmul_eq_mul,
      zero_add, mul_comm]
  refine newtonSlopes_eq_map (φ := id) Function.injective_id
    (by rw [hpoly, finiteEdges_add_affine, Set.image_id]) fun n hn => ?_
  rw [hpoly, id, unitSlope_add_affine hn, ← hr, WithTop.untop₀_coe]

/-- Mapping the coefficients along a ring homomorphism compatible with the valuations
preserves the finite slopes. -/
theorem newtonSlopes_map (φ : R →+* S) {w : AddValuation S (WithTop ℝ)}
    (hφ : ∀ x, w (φ x) = v x) : (f.map φ).newtonSlopes w = f.newtonSlopes v :=
  newtonSlopes_congr (f.newtonPolygon_map v φ hφ)

/-! ### Linear polynomials -/

/-- The polynomial `X - C α`, whose root `α` has finite valuation, has the single finite slope
`-v α`. -/
theorem newtonSlopes_X_sub_C {α : R} (hα : v α ≠ ⊤) :
    (X - C α).newtonSlopes v = {-(v α).untop₀} := by
  let d : FiniteSlopeData ℝ :=
    ⟨0, (v α).untop₀, 1, fun _ => -(v α).untop₀, monotone_const⟩
  have hd : d.heights = (X - C α).newtonPolygon v := by
    have ha : (fun n => v ((X - C α).coeff n)) = d.heights := by
      funext n
      rcases n with _ | _ | n
      · simp [d, FiniteSlopeData.heights_def, coeff_X, coeff_C, prefixSum_zero,
          WithTop.coe_untop₀_of_ne_top hα]
      · simp [d, FiniteSlopeData.heights_def, coeff_X, prefixSum_succ, prefixSum_zero]
      · simp [d, FiniteSlopeData.heights_def, coeff_X]
    rw [newtonPolygon_def, ha, d.isConvexSeq_heights.lowerConvexEnvelope_eq]
  rw [newtonSlopes_eq_slopeMultiset hd, FiniteSlopeData.slopeMultiset_def]
  simp [d]

end Polynomial
