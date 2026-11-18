/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Symbol.Parameter.Basic

/-!
# The formal resolvent parametrix of a parameter-elliptic symbol

The resolvent `(A - z)⁻¹` of an elliptic operator `A` is approximated by a pseudodifferential
operator whose symbol `q((x, ξ), z)` is a strongly parameter-dependent symbol
(`TauCeti.ParameterSymbol`). Its terms solve the equation "`q # (a - z) ∼ 1`" in the composition
calculus, with estimates uniform in the spectral parameter `z`. This file solves that equation
formally, at the level of terms, for an expansion `a ∼ ∑ⱼ aⱼ` with `aⱼ` of order `m - j` whose
leading term `a₀` is elliptic with parameter. For a differential operator `A` of order `2` with
symbol `a₂ + a₁ + a₀`, the expansion of the symbol of `A - z` is `(a₂ - z, a₁, a₀, 0, …)`.

* `TauCeti.ParameterSymbol.sharpTerm a b k`: the parameter-dependent symbol
  `((-i)ᵏ / k!) ∑_{|w| = k} ∂_ξ^w a ∘ ∂_x^w b` of order `m' + m - k`, the part of the formal
  composition `a # b` with `k` derivatives on each factor. The spectral parameter is not
  differentiated: it is a parameter of the calculus, not a variable of the operators.
* `TauCeti.ParameterSymbol.sharpTerms q p`: the terms `cₖ = ∑_{i + j + r = k} sharpTerm qᵢ pⱼ r`
  of the formal composition of two expansions.
* `TauCeti.ParameterSymbol.leftInverseTerms` and `TauCeti.ParameterSymbol.rightInverseTerms`: the
  formal left and right inverses, sequences of parameter-dependent symbols of orders `-m - k`
  starting from the inverse `a₀⁻¹` of order `-m`, whose formal composition with `a` is the
  identity (`ParameterSymbol.coefficient_sharpTerms_leftInverseTerms_zero`,
  `ParameterSymbol.sharpTerms_leftInverseTerms_succ` and their right-handed versions). They are
  the only such sequences (`ParameterSymbol.eq_leftInverseTerms_iff`,
  `ParameterSymbol.eq_rightInverseTerms_iff`).
* `TauCeti.ParameterSymbol.isHomogeneous_leftInverseTerms`,
  `TauCeti.ParameterSymbol.isHomogeneous_rightInverseTerms`: if each `aⱼ` is jointly homogeneous of
  degree `μ - j` under `(ξ, z) ↦ (t ξ, t² z)` (`TauCeti.ParameterSymbol.IsHomogeneous`), the
  `k`-th term of either formal inverse is homogeneous of degree `-μ - k`. The same holds for the
  composition terms (`ParameterSymbol.IsHomogeneous.sharpTerm`,
  `ParameterSymbol.IsHomogeneous.sharpTerms`).
* `TauCeti.ParameterSymbol.leftInverseTerms_succ_eq_zero`: if `a` is a single term independent of
  the position, such as the symbol `(s + ‖ξ‖²) - z` of `s - Δ - z`
  (`TauCeti.ParameterSymbol.spatialDeriv_shiftedLaplacian`), the formal left inverse is the
  pointwise inverse `a₀⁻¹` with no correction terms.

The orders `-m - k` of the terms hold uniformly in the spectral parameter, which counts as two
frequency orders. Everything here is a statement about terms; that `sharpTerms` gives the symbol of
the composed operators, uniformly in `z`, is the composition theorem of the parameter-dependent
calculus.

## References

* M. A. Shubin, *Pseudodifferential Operators and Spectral Theory*, Chapter II, §§9–11.
* R. T. Seeley, *Complex powers of an elliptic operator*, Proc. Sympos. Pure Math. 10 (1967),
  288–307.
-/

public section

noncomputable section

open Finset

namespace TauCeti

namespace ParameterSymbol

variable {n : ℕ} {Λ : TopologicalSpace.Opens ℂ} {V W U : Type*} [NormedAddCommGroup V]
  [NormedSpace ℂ V] [NormedAddCommGroup W] [NormedSpace ℂ W] [NormedAddCommGroup U]
  [NormedSpace ℂ U] {m m' : ℝ}

/-! ### The terms of the formal composition -/

/-- The parameter-dependent symbol `((-i)ᵏ / k!) ∑_{|w| = k} ∂_ξ^w a ∘ ∂_x^w b` of order
`m' + m - k`, the part of the formal composition `a # b` with `k` derivatives on each factor,
summed over the words `w` of length `k` in the coordinate directions. It is defined by the
recursion `sharpTerm a b 0 = a ∘ b` and
`sharpTerm a b (k + 1) = (-i / (k + 1)) ∑ⱼ sharpTerm (∂_{ξⱼ} a) (∂_{xⱼ} b) k`. -/
def sharpTerm : {m m' : ℝ} → ParameterSymbol n Λ W U m' → ParameterSymbol n Λ V W m → (k : ℕ) →
    ParameterSymbol n Λ V U (m' + m - k)
  | _, _, a, b, 0 => inclusion (by simp) (a.comp b)
  | _, _, a, b, k + 1 => inclusion (by push_cast; linarith)
      ((-Complex.I / (k + 1)) • ∑ j, sharpTerm (frequencyDeriv j a) (spatialDeriv j b) k)

theorem sharpTerm_zero (a : ParameterSymbol n Λ W U m') (b : ParameterSymbol n Λ V W m) :
    a.sharpTerm b 0 = inclusion (by simp) (a.comp b) := by
  rw [sharpTerm]

theorem sharpTerm_succ (a : ParameterSymbol n Λ W U m') (b : ParameterSymbol n Λ V W m) (k : ℕ) :
    a.sharpTerm b (k + 1) = inclusion (by push_cast; linarith)
      ((-Complex.I / (k + 1)) • ∑ j, (frequencyDeriv j a).sharpTerm (spatialDeriv j b) k) := by
  rw [sharpTerm]

@[simp]
theorem coefficient_sharpTerm_zero (a : ParameterSymbol n Λ W U m') (b : ParameterSymbol n Λ V W m)
    (p : (CoordinateSpace n × CoordinateSpace n) × ℂ) :
    (a.sharpTerm b 0).coefficient p = (a.coefficient p).comp (b.coefficient p) := by
  rw [sharpTerm_zero, coefficient_inclusion, coefficient_comp]

theorem coefficient_sharpTerm_succ (a : ParameterSymbol n Λ W U m')
    (b : ParameterSymbol n Λ V W m) (k : ℕ) (p : (CoordinateSpace n × CoordinateSpace n) × ℂ) :
    (a.sharpTerm b (k + 1)).coefficient p = (-Complex.I / (k + 1)) •
      ∑ j, ((frequencyDeriv j a).sharpTerm (spatialDeriv j b) k).coefficient p := by
  rw [sharpTerm_succ, coefficient_inclusion, coefficient_smul, Pi.smul_apply, coefficient_sum,
    Finset.sum_apply]

/-- With a zero right factor, every term of the formal composition vanishes. -/
private theorem sharpTerm_zero_right (a : ParameterSymbol n Λ W U m') (k : ℕ) :
    a.sharpTerm (0 : ParameterSymbol n Λ V W m) k = 0 := by
  induction k generalizing m' with
  | zero => exact ext_of_mem fun x ξ z _ => by simp
  | succ k ih => simp [sharpTerm_succ, ih]

/-- **Exact composition with a position-independent right factor.** If the right factor does not
depend on the position, all terms of the formal composition beyond the pointwise composition
vanish. -/
theorem sharpTerm_succ_eq_zero (a : ParameterSymbol n Λ W U m') {b : ParameterSymbol n Λ V W m}
    (hb : ∀ j, spatialDeriv j b = 0) (k : ℕ) : a.sharpTerm b (k + 1) = 0 := by
  simp [sharpTerm_succ, hb, sharpTerm_zero_right]

private theorem IsHomogeneous.congr_degree {μ μ' : ℝ} {a : ParameterSymbol n Λ V W m}
    (ha : a.IsHomogeneous μ) (h : μ = μ') : a.IsHomogeneous μ' :=
  h ▸ ha

/-- **Homogeneity of the composition terms.** If `a` and `b` are homogeneous of degrees `μ'` and
`μ` under `(ξ, z) ↦ (t ξ, t² z)`, the term `sharpTerm a b k` is homogeneous of degree
`μ' + μ - k`. -/
theorem IsHomogeneous.sharpTerm {μ μ' : ℝ} {a : ParameterSymbol n Λ W U m'}
    {b : ParameterSymbol n Λ V W m} (ha : a.IsHomogeneous μ') (hb : b.IsHomogeneous μ) (k : ℕ) :
    (a.sharpTerm b k).IsHomogeneous (μ' + μ - k) := by
  induction k generalizing m' μ' a m μ b with
  | zero =>
    rw [sharpTerm_zero]
    exact ((ha.comp hb).inclusion _).congr_degree (by simp)
  | succ k ih =>
    rw [sharpTerm_succ]
    exact (((IsHomogeneous.sum fun j _ => ih (ha.frequencyDeriv j) (hb.spatialDeriv j)).smul
      _).inclusion _).congr_degree (by push_cast; ring)

/-- Rewriting the index of a family of parameter-dependent symbols of varying orders. -/
private theorem coefficient_congr_index {μ : ℕ → ℝ} (f : (r : ℕ) → ParameterSymbol n Λ V W (μ r))
    {r r' : ℕ} (h : r = r') : (f r).coefficient = (f r').coefficient := by
  subst h
  rfl

/-! ### The formal composition of two expansions -/

section SharpTerms

/-- The terms `cₖ = ∑_{i + j + r = k} sharpTerm qᵢ pⱼ r` of the formal composition `q # p` of
two expansions, with the terms `qᵢ` of order `m' - i` and `pⱼ` of order `m - j`. The term `cₖ`
has order `m' + m - k`. -/
def sharpTerms (q : (i : ℕ) → ParameterSymbol n Λ W U (m' - i))
    (p : (j : ℕ) → ParameterSymbol n Λ V W (m - j)) (k : ℕ) :
    ParameterSymbol n Λ V U (m' + m - k) :=
  ∑ i ∈ range (k + 1), ∑ j ∈ range (k + 1),
    if h : i + j ≤ k then
      inclusion (by rw [Nat.cast_sub h]; push_cast; linarith) ((q i).sharpTerm (p j) (k - (i + j)))
    else 0

variable (q : (i : ℕ) → ParameterSymbol n Λ W U (m' - i))
  (p : (j : ℕ) → ParameterSymbol n Λ V W (m - j))

/-- The coefficient of `cₖ` is `∑_{i + j ≤ k} sharpTerm qᵢ pⱼ (k - i - j)`. -/
theorem coefficient_sharpTerms (k : ℕ) (x : (CoordinateSpace n × CoordinateSpace n) × ℂ) :
    (sharpTerms q p k).coefficient x =
      ∑ i ∈ range (k + 1), ∑ j ∈ range (k + 1),
        if i + j ≤ k then ((q i).sharpTerm (p j) (k - (i + j))).coefficient x else 0 := by
  simp only [sharpTerms, coefficient_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  split_ifs <;> simp

@[simp]
theorem coefficient_sharpTerms_zero (x : (CoordinateSpace n × CoordinateSpace n) × ℂ) :
    (sharpTerms q p 0).coefficient x = (q 0).coefficient x ∘L (p 0).coefficient x := by
  simp [coefficient_sharpTerms]

/-- The term `c_{k+1}` of the formal composition is `q_{k+1} ∘ p₀` plus terms involving only
`q₀, …, qₖ`. -/
theorem coefficient_sharpTerms_succ (k : ℕ) (x : (CoordinateSpace n × CoordinateSpace n) × ℂ) :
    (sharpTerms q p (k + 1)).coefficient x =
      (q (k + 1)).coefficient x ∘L (p 0).coefficient x +
        ∑ i ∈ range (k + 1), ∑ j ∈ range (k + 2),
          if i + j ≤ k + 1 then ((q i).sharpTerm (p j) (k + 1 - (i + j))).coefficient x
          else 0 := by
  rw [coefficient_sharpTerms, Finset.sum_range_succ, add_comm, Finset.sum_range_succ']
  congr 1
  rw [Finset.sum_eq_zero fun j _ => ite_eq_right (by omega), zero_add, ite_eq_left (by omega),
    coefficient_congr_index (fun r => (q (k + 1)).sharpTerm (p 0) r)
      (show k + 1 - (k + 1 + 0) = 0 by omega), coefficient_sharpTerm_zero]

/-- The term `c_{k+1}` of the formal composition is `q₀ ∘ p_{k+1}` plus terms involving only
`p₀, …, pₖ`. -/
theorem coefficient_sharpTerms_succ' (k : ℕ) (x : (CoordinateSpace n × CoordinateSpace n) × ℂ) :
    (sharpTerms q p (k + 1)).coefficient x =
      (q 0).coefficient x ∘L (p (k + 1)).coefficient x +
        ∑ j ∈ range (k + 1), ∑ i ∈ range (k + 2),
          if i + j ≤ k + 1 then ((q i).sharpTerm (p j) (k + 1 - (i + j))).coefficient x
          else 0 := by
  rw [coefficient_sharpTerms, Finset.sum_comm, Finset.sum_range_succ, add_comm,
    Finset.sum_range_succ']
  congr 1
  rw [Finset.sum_eq_zero fun i _ => ite_eq_right (by omega), zero_add, ite_eq_left (by omega),
    coefficient_congr_index (fun r => (q 0).sharpTerm (p (k + 1)) r)
      (show k + 1 - (0 + (k + 1)) = 0 by omega), coefficient_sharpTerm_zero]

/-- **Homogeneity of the formal composition.** If `qᵢ` and `pⱼ` are homogeneous of degrees
`μ' - i` and `μ - j`, the term `cₖ` of `sharpTerms q p` is homogeneous of degree `μ' + μ - k`. -/
theorem IsHomogeneous.sharpTerms {μ μ' : ℝ} (hq : ∀ i, (q i).IsHomogeneous (μ' - i))
    (hp : ∀ j, (p j).IsHomogeneous (μ - j)) (k : ℕ) :
    (sharpTerms q p k).IsHomogeneous (μ' + μ - k) := by
  refine IsHomogeneous.sum fun i _ => IsHomogeneous.sum fun j _ => ?_
  split_ifs with h
  · exact (((hq i).sharpTerm (hp j) _).inclusion _).congr_degree
      (by rw [Nat.cast_sub h]; push_cast; ring)
  · exact isHomogeneous_zero

end SharpTerms

/-! ### The formal left and right inverses -/

section Inverse

variable [CompleteSpace V] (a : (j : ℕ) → ParameterSymbol n Λ V W (m - j)) (ha : (a 0).IsElliptic)

/-- The terms `q_k` of order `-m - k` of a formal left inverse of an expansion `a ∼ ∑ⱼ aⱼ` whose
leading term is elliptic with parameter: `q₀ = a₀⁻¹` and, for `k ≥ 0`,
`q_{k+1} = -(∑' sharpTerm qᵢ aⱼ r) ∘ a₀⁻¹`, where the sum runs over the terms of `c_{k+1}` in
`sharpTerms q a` other than `q_{k+1} ∘ a₀`. -/
def leftInverseTerms : (k : ℕ) → ParameterSymbol n Λ W V (-m - k)
  | 0 => inclusion (by simp) ((a 0).inverse ha)
  | k + 1 => inclusion (by push_cast; linarith) (-((∑ i ∈ (range (k + 1)).attach,
      ∑ j ∈ range (k + 2), if h : (i : ℕ) + j ≤ k + 1 then
        inclusion (m' := -(k + 1 : ℕ)) (by rw [Nat.cast_sub h]; push_cast; linarith)
          ((leftInverseTerms i).sharpTerm (a j) (k + 1 - (i + j)))
      else 0).comp ((a 0).inverse ha)))
  decreasing_by exact Finset.mem_range.1 i.2

@[simp]
theorem coefficient_leftInverseTerms_zero (x : (CoordinateSpace n × CoordinateSpace n) × ℂ) :
    (leftInverseTerms a ha 0).coefficient x = ((a 0).coefficient x).inverse := by
  rw [leftInverseTerms]
  simp

/-- The recursion defining the formal left inverse. -/
theorem coefficient_leftInverseTerms_succ (k : ℕ)
    (x : (CoordinateSpace n × CoordinateSpace n) × ℂ) :
    (leftInverseTerms a ha (k + 1)).coefficient x =
      -((∑ i ∈ range (k + 1), ∑ j ∈ range (k + 2),
        if i + j ≤ k + 1 then ((leftInverseTerms a ha i).sharpTerm (a j)
          (k + 1 - (i + j))).coefficient x else 0) ∘L ((a 0).coefficient x).inverse) := by
  rw [leftInverseTerms]
  simp only [coefficient_inclusion, coefficient_neg, coefficient_comp, coefficient_inverse,
    Pi.neg_apply, coefficient_sum, Finset.sum_apply]
  congr 2
  rw [← Finset.sum_attach (range (k + 1)) fun i => ∑ j ∈ range (k + 2),
    if i + j ≤ k + 1 then
      ((leftInverseTerms a ha i).sharpTerm (a j) (k + 1 - (i + j))).coefficient x
    else 0]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  split_ifs <;> simp

/-- **The formal left inverse.** The leading term of `sharpTerms (leftInverseTerms a ha) a` is the
identity at every spectral parameter in `Λ`. -/
theorem coefficient_sharpTerms_leftInverseTerms_zero (x ξ : CoordinateSpace n) {z : ℂ}
    (hz : z ∈ Λ) :
    (sharpTerms (leftInverseTerms a ha) a 0).coefficient ((x, ξ), z) =
      ContinuousLinearMap.id ℂ V := by
  simp [(ha.isInvertible x ξ z hz).inverse_comp_self]

/-- **The formal left inverse.** All terms of `sharpTerms (leftInverseTerms a ha) a` after the
leading one vanish. -/
@[simp]
theorem sharpTerms_leftInverseTerms_succ (k : ℕ) :
    sharpTerms (leftInverseTerms a ha) a (k + 1) = 0 :=
  ext_of_mem fun x ξ z hz => by
    rw [coefficient_sharpTerms_succ, coefficient_leftInverseTerms_succ,
      ContinuousLinearMap.neg_comp, ContinuousLinearMap.comp_assoc,
      (ha.isInvertible x ξ z hz).inverse_comp_self]
    simp

/-- **Uniqueness of the formal left inverse.** A sequence `q` of parameter-dependent symbols is the
formal left inverse of `a` exactly when the formal composition `sharpTerms q a` is the
identity. -/
theorem eq_leftInverseTerms_iff {q : (i : ℕ) → ParameterSymbol n Λ W V (-m - i)} :
    q = leftInverseTerms a ha ↔
      (∀ x ξ, ∀ z ∈ Λ, (sharpTerms q a 0).coefficient ((x, ξ), z) = ContinuousLinearMap.id ℂ V) ∧
        ∀ k, sharpTerms q a (k + 1) = 0 := by
  refine ⟨?_, fun ⟨h0, hsucc⟩ => funext fun k => ?_⟩
  · rintro rfl
    exact ⟨fun x ξ z hz => coefficient_sharpTerms_leftInverseTerms_zero a ha x ξ hz,
      sharpTerms_leftInverseTerms_succ a ha⟩
  induction k using Nat.strong_induction_on with | _ k ih
  refine ext_of_mem fun x ξ z hz => ?_
  have hinv := ha.isInvertible x ξ z hz
  -- In both cases `q k ∘ a₀` is determined by the earlier terms; compose with `a₀⁻¹`.
  rw [← ContinuousLinearMap.comp_id ((q k).coefficient ((x, ξ), z)), ← hinv.self_comp_inverse,
    ← ContinuousLinearMap.comp_assoc]
  cases k with
  | zero =>
    have h := h0 x ξ z hz
    rw [coefficient_sharpTerms_zero] at h
    simp [h]
  | succ k =>
    have h := congrArg (fun c => c.coefficient ((x, ξ), z)) (hsucc k)
    simp only [coefficient_sharpTerms_succ, coefficient_zero, Pi.zero_apply] at h
    rw [eq_neg_of_add_eq_zero_left h, coefficient_leftInverseTerms_succ,
      ContinuousLinearMap.neg_comp]
    congr 2
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [ih i (by simpa using Finset.mem_range.1 hi)]

/-- **Position-independent symbols.** If the expansion `a` consists of a single term independent of
the position, its formal left inverse is the pointwise inverse `a₀⁻¹`: all later terms vanish.
This applies to the symbol `(s + ‖ξ‖²) - z` of `s - Δ - z`, by
`TauCeti.ParameterSymbol.spatialDeriv_shiftedLaplacian`. -/
theorem leftInverseTerms_succ_eq_zero (h₀ : ∀ j, spatialDeriv j (a 0) = 0)
    (h₁ : ∀ j, a (j + 1) = 0) (k : ℕ) : leftInverseTerms a ha (k + 1) = 0 := by
  refine ext_of_mem fun x ξ z _ => ?_
  rw [coefficient_leftInverseTerms_succ, coefficient_zero, Pi.zero_apply]
  -- Every term in the recursion vanishes: either `j ≥ 1`, so `aⱼ = 0`, or `j = 0`, so at least
  -- one derivative falls on the position-independent `a₀`.
  rw [Finset.sum_eq_zero fun i hi => Finset.sum_eq_zero fun j _ => ?_]
  · simp
  split_ifs with hij
  · rcases j with _ | j
    · obtain ⟨r, hr⟩ : ∃ r, k + 1 - (i + 0) = r + 1 :=
        ⟨k - i, by have := Finset.mem_range.1 hi; omega⟩
      rw [coefficient_congr_index (fun r => (leftInverseTerms a ha i).sharpTerm (a 0) r) hr,
        sharpTerm_succ_eq_zero _ h₀, coefficient_zero, Pi.zero_apply]
    · rw [h₁ j, sharpTerm_zero_right, coefficient_zero, Pi.zero_apply]
  · rfl

/-- **Homogeneity of the formal left inverse.** If each term `aⱼ` is homogeneous of degree
`μ - j` under `(ξ, z) ↦ (t ξ, t² z)`, the term `q_k` of the formal left inverse is homogeneous of
degree `-μ - k`. For `a = ‖ξ‖² - z` these are the jointly homogeneous terms of the resolvent
symbol. -/
theorem isHomogeneous_leftInverseTerms {μ : ℝ} (hhom : ∀ j, (a j).IsHomogeneous (μ - j))
    (k : ℕ) : (leftInverseTerms a ha k).IsHomogeneous (-μ - k) := by
  induction k using Nat.strong_induction_on with | _ k ih
  cases k with
  | zero =>
    rw [leftInverseTerms]
    exact (((hhom 0).inverse ha).inclusion _).congr_degree (by simp)
  | succ k =>
    rw [leftInverseTerms]
    refine IsHomogeneous.inclusion (IsHomogeneous.neg ?_) _
    refine (IsHomogeneous.comp (μ' := -((k + 1 : ℕ) : ℝ))
      (IsHomogeneous.sum fun i _ => IsHomogeneous.sum fun j _ => ?_)
      ((hhom 0).inverse ha)).congr_degree (by push_cast; ring)
    split_ifs with h
    · exact (((ih i (Finset.mem_range.1 i.2)).sharpTerm (hhom j) _).inclusion _).congr_degree
        (by rw [Nat.cast_sub h]; push_cast; ring)
    · exact isHomogeneous_zero

/-- The terms `q_k` of order `-m - k` of a formal right inverse of an expansion `a ∼ ∑ᵢ aᵢ` whose
leading term is elliptic with parameter: `q₀ = a₀⁻¹` and, for `k ≥ 0`,
`q_{k+1} = -a₀⁻¹ ∘ ∑' sharpTerm aᵢ qⱼ r`, where the sum runs over the terms of `c_{k+1}` in
`sharpTerms a q` other than `a₀ ∘ q_{k+1}`. -/
def rightInverseTerms : (k : ℕ) → ParameterSymbol n Λ W V (-m - k)
  | 0 => inclusion (by simp) ((a 0).inverse ha)
  | k + 1 => inclusion (by push_cast; linarith) (-(((a 0).inverse ha).comp
      (∑ j ∈ (range (k + 1)).attach, ∑ i ∈ range (k + 2), if h : i + (j : ℕ) ≤ k + 1 then
        inclusion (m' := -(k + 1 : ℕ)) (by rw [Nat.cast_sub h]; push_cast; linarith)
          ((a i).sharpTerm (rightInverseTerms j) (k + 1 - (i + j)))
      else 0)))
  decreasing_by exact Finset.mem_range.1 j.2

@[simp]
theorem coefficient_rightInverseTerms_zero (x : (CoordinateSpace n × CoordinateSpace n) × ℂ) :
    (rightInverseTerms a ha 0).coefficient x = ((a 0).coefficient x).inverse := by
  rw [rightInverseTerms]
  simp

/-- The recursion defining the formal right inverse. -/
theorem coefficient_rightInverseTerms_succ (k : ℕ)
    (x : (CoordinateSpace n × CoordinateSpace n) × ℂ) :
    (rightInverseTerms a ha (k + 1)).coefficient x =
      -(((a 0).coefficient x).inverse ∘L ∑ j ∈ range (k + 1), ∑ i ∈ range (k + 2),
        if i + j ≤ k + 1 then ((a i).sharpTerm (rightInverseTerms a ha j)
          (k + 1 - (i + j))).coefficient x else 0) := by
  rw [rightInverseTerms]
  simp only [coefficient_inclusion, coefficient_neg, coefficient_comp, coefficient_inverse,
    Pi.neg_apply, coefficient_sum, Finset.sum_apply]
  congr 2
  rw [← Finset.sum_attach (range (k + 1)) fun j => ∑ i ∈ range (k + 2),
    if i + j ≤ k + 1 then
      ((a i).sharpTerm (rightInverseTerms a ha j) (k + 1 - (i + j))).coefficient x
    else 0]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> simp

/-- **The formal right inverse.** The leading term of `sharpTerms a (rightInverseTerms a ha)` is the
identity at every spectral parameter in `Λ`. -/
theorem coefficient_sharpTerms_rightInverseTerms_zero (x ξ : CoordinateSpace n) {z : ℂ}
    (hz : z ∈ Λ) :
    (sharpTerms a (rightInverseTerms a ha) 0).coefficient ((x, ξ), z) =
      ContinuousLinearMap.id ℂ W := by
  simp [(ha.isInvertible x ξ z hz).self_comp_inverse]

/-- **The formal right inverse.** All terms of `sharpTerms a (rightInverseTerms a ha)` after the
leading one vanish. -/
@[simp]
theorem sharpTerms_rightInverseTerms_succ (k : ℕ) :
    sharpTerms a (rightInverseTerms a ha) (k + 1) = 0 :=
  ext_of_mem fun x ξ z hz => by
    rw [coefficient_sharpTerms_succ', coefficient_rightInverseTerms_succ,
      ContinuousLinearMap.comp_neg, ← ContinuousLinearMap.comp_assoc,
      (ha.isInvertible x ξ z hz).self_comp_inverse]
    simp

/-- **Uniqueness of the formal right inverse.** A sequence `q` of parameter-dependent symbols is the
formal right inverse of `a` exactly when the formal composition `sharpTerms a q` is the
identity. -/
theorem eq_rightInverseTerms_iff {q : (j : ℕ) → ParameterSymbol n Λ W V (-m - j)} :
    q = rightInverseTerms a ha ↔
      (∀ x ξ, ∀ z ∈ Λ, (sharpTerms a q 0).coefficient ((x, ξ), z) = ContinuousLinearMap.id ℂ W) ∧
        ∀ k, sharpTerms a q (k + 1) = 0 := by
  refine ⟨?_, fun ⟨h0, hsucc⟩ => funext fun k => ?_⟩
  · rintro rfl
    exact ⟨fun x ξ z hz => coefficient_sharpTerms_rightInverseTerms_zero a ha x ξ hz,
      sharpTerms_rightInverseTerms_succ a ha⟩
  induction k using Nat.strong_induction_on with | _ k ih
  refine ext_of_mem fun x ξ z hz => ?_
  have hinv := ha.isInvertible x ξ z hz
  -- In both cases `a₀ ∘ q k` is determined by the earlier terms; compose with `a₀⁻¹`.
  rw [← ContinuousLinearMap.id_comp ((q k).coefficient ((x, ξ), z)), ← hinv.inverse_comp_self,
    ContinuousLinearMap.comp_assoc]
  cases k with
  | zero =>
    have h := h0 x ξ z hz
    rw [coefficient_sharpTerms_zero] at h
    simp [h]
  | succ k =>
    have h := congrArg (fun c => c.coefficient ((x, ξ), z)) (hsucc k)
    simp only [coefficient_sharpTerms_succ', coefficient_zero, Pi.zero_apply] at h
    rw [eq_neg_of_add_eq_zero_left h, coefficient_rightInverseTerms_succ,
      ContinuousLinearMap.comp_neg]
    congr 2
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [ih j (by simpa using Finset.mem_range.1 hj)]

/-- **Homogeneity of the formal right inverse.** If each term `aᵢ` is homogeneous of degree
`μ - i` under `(ξ, z) ↦ (t ξ, t² z)`, the term `q_k` of the formal right inverse is homogeneous of
degree `-μ - k`. -/
theorem isHomogeneous_rightInverseTerms {μ : ℝ} (hhom : ∀ i, (a i).IsHomogeneous (μ - i))
    (k : ℕ) : (rightInverseTerms a ha k).IsHomogeneous (-μ - k) := by
  induction k using Nat.strong_induction_on with | _ k ih
  cases k with
  | zero =>
    rw [rightInverseTerms]
    exact (((hhom 0).inverse ha).inclusion _).congr_degree (by simp)
  | succ k =>
    rw [rightInverseTerms]
    refine IsHomogeneous.inclusion (IsHomogeneous.neg ?_) _
    refine (((hhom 0).inverse ha).comp (μ := -((k + 1 : ℕ) : ℝ))
      (IsHomogeneous.sum fun j _ => IsHomogeneous.sum fun i _ => ?_)).congr_degree
      (by push_cast; ring)
    split_ifs with h
    · exact (((hhom i).sharpTerm (ih j (Finset.mem_range.1 j.2)) _).inclusion _).congr_degree
        (by rw [Nat.cast_sub h]; push_cast; ring)
    · exact isHomogeneous_zero

end Inverse

end ParameterSymbol

end TauCeti
