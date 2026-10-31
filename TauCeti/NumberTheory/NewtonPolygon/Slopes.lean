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

A polynomial `f` is *pure of slope `m`* when every finite slope of its Newton polygon equals
`m`. Write `a` for the order of vanishing of `f` at zero and `d` for its degree. If the trailing
and leading coefficients have finite valuation, the polygon runs from the trailing point
`(a, v (coeff a f))` to the leading point `(d, v (coeff d f))`, so purity says that the polygon is
the segment joining these two points. Purity of slope `m` is therefore equivalent to two
conditions on the coefficients: the line of slope `m` through the trailing point passes through
the leading point, and every coefficient point lies on or above that line. Interior coefficient
points may lie on the line; for instance `1 + p X + p ^ 2 X ^ 2` is pure of slope `1` for the
`p`-adic valuation. The basic example is an Eisenstein polynomial: if the leading coefficient of
`f` has valuation zero, its constant coefficient has valuation one and its other coefficients
below the degree have valuation at least one, then its polygon is the segment from `(0, 1)` to
`(d, 0)` and every finite slope equals `-1 / d`.

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
* `Polynomial.newtonSlopes_reflect` and `Polynomial.newtonSlopes_reverse`: reversing the
  coefficients negates the finite slopes.
* `Polynomial.newtonSlopes_monomial`: a monomial, in particular a constant, has no finite
  slopes.
* `Polynomial.newtonSlopes_X_sub_C`: the only finite slope of `X - C α` is `-v α`.
* `Polynomial.forall_mem_newtonSlopes_eq_iff`: the purity criterion. If the trailing and leading
  coefficients have finite valuation, every finite slope equals `m` exactly when the leading
  point lies on the line of slope `m` through the trailing point and no coefficient point lies
  below that line.
* `Polynomial.newtonSlopes_eq_replicate_of_eisenstein`: an Eisenstein polynomial of degree `d`
  has `d` finite slopes, all equal to `-1 / d`.

## References

* J. Neukirch, *Algebraic Number Theory*, Grundlehren 322, Springer, 1999, Chapter II §6,
  Proposition 6.3 and its corollary.
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
    {φ : ℕ → ℕ} (hφ : Set.InjOn φ (finiteEdges (f.newtonPolygon v))) {t : ℝ → ℝ}
    (hedges : finiteEdges (g.newtonPolygon w) = φ '' finiteEdges (f.newtonPolygon v))
    (hslope : ∀ n ∈ finiteEdges (f.newtonPolygon v),
      unitSlope (g.newtonPolygon w) (φ n) = t (unitSlope (f.newtonPolygon v) n)) :
    g.newtonSlopes w = (f.newtonSlopes v).map t := by
  have hfin : (g.finite_finiteEdges_newtonPolygon w).toFinset =
      (f.finite_finiteEdges_newtonPolygon v).toFinset.image φ := by
    ext n
    simp [hedges]
  rw [newtonSlopes_def, newtonSlopes_def, hfin,
    Finset.image_val_of_injOn (by simpa using hφ), Multiset.map_map, Multiset.map_map]
  exact Multiset.map_congr rfl fun n hn => hslope n (by simpa using hn)

/-- The finite slope multiset depends only on the Newton polygon. -/
theorem newtonSlopes_congr {g : S[X]} {w : AddValuation S (WithTop ℝ)}
    (h : f.newtonPolygon v = g.newtonPolygon w) : f.newtonSlopes v = g.newtonSlopes w := by
  rw [newtonSlopes_eq_map (f := g) (v := w) (g := f) (w := v) Function.injective_id.injOn (t := id)
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
  rw [newtonSlopes_eq_map (f := f) (v := v) Function.injective_id.injOn (t := id)
    (by rw [hpoly, finiteEdges_add_affine, Set.image_id])
    (fun n hn => by rw [hpoly, id, id, unitSlope_add_affine hn, add_zero]), Multiset.map_id]

/-- Multiplying by a scalar of finite valuation preserves the finite slopes. -/
theorem newtonSlopes_smul {c : R} (hc : v c ≠ ⊤) :
    (c • f).newtonSlopes v = f.newtonSlopes v := by
  rw [smul_eq_C_mul, newtonSlopes_C_mul f v hc]

/-- Multiplying by `X ^ k` preserves the finite slopes. -/
@[simp]
theorem newtonSlopes_X_pow_mul (k : ℕ) : (X ^ k * f).newtonSlopes v = f.newtonSlopes v := by
  rw [newtonSlopes_eq_map (f := f) (v := v) (φ := (· + k)) (add_left_injective k).injOn (t := id)
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
  refine newtonSlopes_eq_map (φ := id) Function.injective_id.injOn
    (by rw [hpoly, finiteEdges_add_affine, Set.image_id]) fun n hn => ?_
  rw [hpoly, id, unitSlope_add_affine hn, ← hr, WithTop.untop₀_coe]

/-- Reflecting the coefficients in an index `N` at least the degree negates the finite slopes.
The order of the slopes is reversed, which a multiset does not record. -/
theorem newtonSlopes_reflect {N : ℕ} (hN : f.natDegree ≤ N) :
    (reflect N f).newtonSlopes v = (f.newtonSlopes v).map Neg.neg := by
  have hlt : ∀ n ∈ finiteEdges (f.newtonPolygon v), n < N := fun n hn =>
    lt_of_not_ge fun h => (mem_finiteEdges.mp hn).2
      (f.newtonPolygon_eq_top_of_natDegree_lt v (by omega))
  refine newtonSlopes_eq_map (φ := (N - 1 - ·))
    (fun m hm n hn hmn => by have := hlt m hm; have := hlt n hn; dsimp only at hmn; omega)
    ?_ fun n hn => ?_
  · rw [f.newtonPolygon_reflect v hN, finiteEdges_reflect fun n hn =>
      f.newtonPolygon_eq_top_of_natDegree_lt v (hN.trans_lt hn)]
  · have := hlt n hn
    rw [f.newtonPolygon_reflect v hN, unitSlope_reflect _ (by omega),
      show N - 1 - (N - 1 - n) = n by omega]

/-- Reversing a polynomial negates its finite slopes. -/
@[simp]
theorem newtonSlopes_reverse : f.reverse.newtonSlopes v = (f.newtonSlopes v).map Neg.neg :=
  f.newtonSlopes_reflect v le_rfl

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

/-! ### Pure polynomials -/

section Pure

variable {f v}

/-- If the trailing and leading coefficients of `f` have finite valuation and every finite slope
of `f` equals `m`, the Newton polygon of `f` lies on the line of slope `m` through the trailing
point, between the order of vanishing at zero and the degree. -/
private theorem newtonPolygon_eq_of_forall_mem_newtonSlopes_eq (htr : v f.trailingCoeff ≠ ⊤)
    (hld : v f.leadingCoeff ≠ ⊤) {m : ℝ} (hm : ∀ s ∈ f.newtonSlopes v, s = m) {n : ℕ}
    (han : f.natTrailingDegree ≤ n) (hnd : n ≤ f.natDegree) :
    f.newtonPolygon v n =
      (((v f.trailingCoeff).untop₀ + m * ((n : ℝ) - f.natTrailingDegree) : ℝ) : WithTop ℝ) := by
  have hn : f.newtonPolygon v n ≠ ⊤ :=
    (newtonPolygon_ne_top_iff_of_ne_top v htr hld).mpr ⟨han, hnd⟩
  have hsum : ∑ k ∈ Finset.Ico f.natTrailingDegree n, unitSlope (f.newtonPolygon v) k =
      ∑ _k ∈ Finset.Ico f.natTrailingDegree n, m := by
    refine Finset.sum_congr rfl fun k hk => hm _ ((mem_newtonSlopes f v).mpr ⟨k, ?_, rfl⟩)
    rw [finiteEdges_newtonPolygon_of_ne_top f v htr hld, Set.mem_Ico]
    have := Finset.mem_Ico.mp hk
    omega
  rw [eq_coe_add_sum_unitSlope hn han, newtonPolygon_natTrailingDegree, hsum, Finset.sum_const,
    Nat.card_Ico, nsmul_eq_mul, Nat.cast_sub han]
  ring_nf

/-- **Purity criterion.** If the trailing and leading coefficients of `f` have finite valuation,
every finite slope of `f` equals `m` exactly when the line of slope `m` through the trailing point
`(a, v (coeff a f))`, where `a` is the order of vanishing of `f` at zero, passes through the
leading point and lies on or below every coefficient point. -/
theorem forall_mem_newtonSlopes_eq_iff (htr : v f.trailingCoeff ≠ ⊤)
    (hld : v f.leadingCoeff ≠ ⊤) {m : ℝ} :
    (∀ s ∈ f.newtonSlopes v, s = m) ↔
      (v f.leadingCoeff).untop₀ =
          (v f.trailingCoeff).untop₀ + m * ((f.natDegree : ℝ) - f.natTrailingDegree) ∧
        ∀ n : ℕ, (((v f.trailingCoeff).untop₀ + m * ((n : ℝ) - f.natTrailingDegree) : ℝ) :
          WithTop ℝ) ≤ v (f.coeff n) := by
  constructor
  · intro hm
    refine ⟨?_, fun n => ?_⟩
    · rw [← WithTop.untop₀_coe (_ + _), ← newtonPolygon_eq_of_forall_mem_newtonSlopes_eq htr hld
        hm (natTrailingDegree_le_natDegree f) le_rfl, newtonPolygon_natDegree]
    · by_cases han : f.natTrailingDegree ≤ n
      · by_cases hnd : n ≤ f.natDegree
        · exact (newtonPolygon_eq_of_forall_mem_newtonSlopes_eq htr hld hm han hnd).symm.trans_le
            (f.newtonPolygon_le v n)
        · rw [coeff_eq_zero_of_natDegree_lt (not_le.mp hnd), v.map_zero]
          exact le_top
      · rw [coeff_eq_zero_of_lt_natTrailingDegree (not_le.mp han), v.map_zero]
        exact le_top
  · rintro ⟨hlead, hle⟩ s hs
    obtain ⟨k, hk, rfl⟩ := (mem_newtonSlopes f v).mp hs
    rw [finiteEdges_newtonPolygon_of_ne_top f v htr hld, Set.mem_Ico] at hk
    -- The line of slope `m` through the trailing point, in the form `c + m * n`.
    have hH : (fun n : ℕ => (((v f.trailingCoeff).untop₀ - m * f.natTrailingDegree + m * n : ℝ) :
        WithTop ℝ)) ≤ f.newtonPolygon v :=
      le_newtonPolygon (isConvexSeq_affine _ m) fun n => by
        convert hle n using 2
        ring
    have htrail : f.newtonPolygon v f.natTrailingDegree = (((v f.trailingCoeff).untop₀ -
        m * f.natTrailingDegree + m * f.natTrailingDegree : ℝ) : WithTop ℝ) := by
      rw [newtonPolygon_natTrailingDegree, sub_add_cancel, WithTop.coe_untop₀_of_ne_top htr]
    have hlead' : f.newtonPolygon v f.natDegree = (((v f.trailingCoeff).untop₀ -
        m * f.natTrailingDegree + m * f.natDegree : ℝ) : WithTop ℝ) := by
      rw [newtonPolygon_natDegree, ← WithTop.coe_untop₀_of_ne_top hld, hlead, WithTop.coe_eq_coe]
      ring
    have hon {n : ℕ} (han : f.natTrailingDegree ≤ n) (hnd : n ≤ f.natDegree) :=
      (f.isConvexSeq_newtonPolygon v).eq_affine_of_affine_le htrail hlead' han hnd (hH n)
    rw [unitSlope_def, hon (by omega) hk.2, hon hk.1 hk.2.le, WithTop.untop₀_coe,
      WithTop.untop₀_coe]
    push_cast
    ring

/-- **Eisenstein polygons.** If `f` has leading coefficient of valuation zero, constant
coefficient of valuation one, and all other coefficients below the degree of valuation at least
one, then the Newton polygon of `f` is the segment from `(0, 1)` to `(d, 0)`, where `d` is the
degree of `f`: it has `d` finite slopes, all equal to `-1 / d`. -/
theorem newtonSlopes_eq_replicate_of_eisenstein (hlead : v f.leadingCoeff = 0)
    (h0 : v (f.coeff 0) = 1) (hmem : ∀ n, 0 < n → n < f.natDegree → 1 ≤ v (f.coeff n)) :
    f.newtonSlopes v = Multiset.replicate f.natDegree (-(f.natDegree : ℝ)⁻¹) := by
  have hc0 : f.coeff 0 ≠ 0 := fun h => by simp [h] at h0
  have ha : f.natTrailingDegree = 0 := natTrailingDegree_eq_zero_of_constantCoeff_ne_zero hc0
  have hd : 0 < f.natDegree := Nat.pos_of_ne_zero fun hd => by
    rw [leadingCoeff, hd, h0] at hlead
    exact one_ne_zero hlead
  have htr : v f.trailingCoeff ≠ ⊤ := by
    rw [trailingCoeff, ha, h0]
    exact WithTop.one_ne_top
  have hld : v f.leadingCoeff ≠ ⊤ := by
    rw [hlead]
    exact WithTop.zero_ne_top
  have htrail : (v f.trailingCoeff).untop₀ = 1 := by
    rw [trailingCoeff, ha, h0, WithTop.untop₀_one]
  refine Multiset.eq_replicate.mpr ⟨?_, ?_⟩
  · rw [newtonSlopes_def, Multiset.card_map, Finset.card_val,
      ← Set.ncard_eq_toFinset_card _ (f.finite_finiteEdges_newtonPolygon v),
      finiteEdges_newtonPolygon_of_ne_top f v htr hld, Set.ncard_Ico_nat, ha, Nat.sub_zero]
  refine (forall_mem_newtonSlopes_eq_iff htr hld).mpr ⟨?_, fun n => ?_⟩
  · rw [hlead, htrail, ha, WithTop.untop₀_zero]
    field_simp
    ring
  rw [htrail, ha, Nat.cast_zero, sub_zero]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [h0]
  rcases lt_trichotomy n f.natDegree with hnd | rfl | hnd
  · refine le_trans ?_ (hmem n hn hnd)
    rw [← WithTop.coe_one, WithTop.coe_le_coe]
    have : (0 : ℝ) ≤ (f.natDegree : ℝ)⁻¹ * n := by positivity
    linarith
  · rw [← leadingCoeff, hlead, ← WithTop.coe_zero, WithTop.coe_le_coe]
    field_simp
    simp
  · rw [coeff_eq_zero_of_natDegree_lt hnd, v.map_zero]
    exact le_top

end Pure

end Polynomial
