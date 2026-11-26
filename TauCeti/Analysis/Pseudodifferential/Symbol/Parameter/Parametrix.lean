/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Symbol.Parameter.Homogeneous

/-!
# The formal composition and the parametrix of parameter-dependent symbols

The symbol of the composition of two pseudodifferential operators with symbols `b` and `a` has the
expansion `b # a ∼ ∑_α ((1/i)^|α| / α!) ∂_ξ^α b ∂_x^α a`. For strongly parameter-dependent symbols
(`TauCeti.ParameterSymbol`) the spectral parameter `z` is a passive variable of this expansion, and
the term with `k` derivatives on each factor loses `k` orders, uniformly in `z`. Solving the
expansion against a symbol `a` that is elliptic with parameter gives the formal parametrix of the
family of operators with symbols `a(·, ·, z)`. For the symbol of `A - z`, with `A` an elliptic
differential operator and `z` in a sector, these are the terms of Seeley's approximation of the
resolvent `(A - z)⁻¹`, before their asymptotic summation.

* `TauCeti.ParameterSymbol.sharpTerm b a k`: the parameter-dependent symbol
  `((-i)ᵏ / k!) ∑_{|w| = k} ∂_ξ^w b ∘ ∂_x^w a` of order `m' + m - k`, summed over the words `w` of
  length `k` in the coordinate directions (`TauCeti.ParameterSymbol.coefficient_sharpTerm`).
* `TauCeti.ParameterSymbol.coefficient_sharpTerm_eq_zero_of_coordinateDeriv_eq_zero`: if `b` is
  polynomial of degree less than `d` in the frequency, the terms `sharpTerm b a k` with `k ≥ d`
  vanish.
* `TauCeti.ParameterSymbol.leftInverseTerms`, `TauCeti.ParameterSymbol.rightInverseTerms`:
  for a symbol `a` of order `m` elliptic with parameter, symbols `bⱼ` of order `-m - j` with
  `b₀ = a⁻¹` that solve the formal composition equations
  `∑_{j + k = N} sharpTerm bⱼ a k = δ_{N,0}`
  (`TauCeti.ParameterSymbol.sum_coefficient_sharpTerm_leftInverseTerms`) and
  `∑_{j + k = N} sharpTerm a bⱼ k = δ_{N,0}`
  (`TauCeti.ParameterSymbol.sum_coefficient_sharpTerm_rightInverseTerms`).
* `TauCeti.ParameterSymbol.leftInverseTerms_succ_eq_zero_of_spatialDeriv_eq_zero`: for a symbol
  that does not depend on the position, such as the symbol of `s - Δ - z`
  (`TauCeti.ParameterSymbol.leftInverseTerms_shiftedLaplacian_succ_eq_zero`), the correction
  terms vanish and the left parametrix is the inverse symbol alone.
* `TauCeti.ParameterSymbol.sharpTerms q p`: the terms `cₖ = ∑_{i + j + r = k} sharpTerm qᵢ pⱼ r`
  of the formal composition of two expansions `q ∼ ∑ᵢ qᵢ` and `p ∼ ∑ⱼ pⱼ`.
* `TauCeti.ParameterSymbol.expansionLeftInverseTerms`,
  `TauCeti.ParameterSymbol.expansionRightInverseTerms`: the formal left and right inverses of an
  expansion `a ∼ ∑ⱼ aⱼ`, with `aⱼ` of order `m - j` and `a₀` elliptic with parameter. For a
  differential operator `A` of order `2` with symbol `a₂ + a₁ + a₀`, the expansion of the symbol of
  `A - z` is `(a₂ - z, a₁, a₀, 0, …)`. They are sequences of orders `-m - k` starting from `a₀⁻¹`
  whose formal composition with `a` is the identity
  (`TauCeti.ParameterSymbol.sharpTerms_expansionLeftInverseTerms_succ` and its right-handed
  version), and they are the only such sequences
  (`TauCeti.ParameterSymbol.eq_expansionLeftInverseTerms_iff`,
  `TauCeti.ParameterSymbol.eq_expansionRightInverseTerms_iff`).
* `TauCeti.ParameterSymbol.expansionLeftInverseTerms_eq_leftInverseTerms`,
  `TauCeti.ParameterSymbol.expansionRightInverseTerms_eq_rightInverseTerms`: for the one-term
  expansion `(a, 0, 0, …)` of a single symbol `a`, the formal inverses of the expansion are the
  parametrices `leftInverseTerms` and `rightInverseTerms` of `a`.
* `TauCeti.ParameterSymbol.isQuasiHomogeneous_expansionLeftInverseTerms`,
  `TauCeti.ParameterSymbol.isQuasiHomogeneous_expansionRightInverseTerms`: if each `aⱼ` is jointly
  homogeneous of degree `μ - j` under `(ξ, z) ↦ (t ξ, t² z)`
  (`TauCeti.ParameterSymbol.IsQuasiHomogeneous`), the `k`-th term of either formal inverse is
  homogeneous of degree `-μ - k`. These are the jointly homogeneous terms of Seeley's resolvent
  symbol. The same holds for the composition terms
  (`TauCeti.ParameterSymbol.IsQuasiHomogeneous.sharpTerm`,
  `TauCeti.ParameterSymbol.IsQuasiHomogeneous.sharpTerms`) and for the parametrix of a single
  homogeneous symbol (`TauCeti.ParameterSymbol.isQuasiHomogeneous_leftInverseTerms`,
  `TauCeti.ParameterSymbol.isQuasiHomogeneous_rightInverseTerms`).

The definition and closed form of `TauCeti.ParameterSymbol.sharpTerm` follow
`TauCeti.HomogeneousSymbol.sharpTerm` and `TauCeti.Symbol.sharpTerm`, the formal composition
of expansions `TauCeti.ParameterSymbol.sharpTerms` and its recursions
`TauCeti.ParameterSymbol.coefficient_sharpTerms_succ` and
`TauCeti.ParameterSymbol.coefficient_sharpTerms_succ'` follow `TauCeti.ClassicalSymbol.sharpTerms`,
and the parametrix recursions adapt `TauCeti.ClassicalSymbol.leftInverseTerms` and
`TauCeti.ClassicalSymbol.rightInverseTerms` to the parameter-dependent class.

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
  [NormedSpace ℂ U] {m : ℝ}

/-! ### The terms of the formal composition -/

/-- The parameter-dependent symbol `((-i)ᵏ / k!) ∑_{|w| = k} ∂_ξ^w b ∘ ∂_x^w a` of order
`m' + m - k`, the part of the formal composition `b # a` with `k` derivatives on each factor. It is
defined by the recursion `sharpTerm b a 0 = b ∘ a` and
`sharpTerm b a (k + 1) = (-i / (k + 1)) ∑ⱼ sharpTerm (∂_{ξⱼ} b) (∂_{xⱼ} a) k`; the closed form is
`TauCeti.ParameterSymbol.coefficient_sharpTerm`. -/
def sharpTerm : {m' : ℝ} → ParameterSymbol n Λ W U m' → ParameterSymbol n Λ V W m → (k : ℕ) →
    ParameterSymbol n Λ V U (m' + m - k)
  | _, b, a, 0 => inclusion (by simp) (b.comp a)
  | _, b, a, k + 1 => (-Complex.I / (k + 1 : ℂ)) • ∑ j : Fin n,
      inclusion (by push_cast; linarith)
        ((b.frequencyDeriv (EuclideanSpace.single j 1)).sharpTerm
          (a.spatialDeriv (EuclideanSpace.single j 1)) k)

variable {m' : ℝ}

theorem sharpTerm_zero (b : ParameterSymbol n Λ W U m') (a : ParameterSymbol n Λ V W m) :
    b.sharpTerm a 0 = inclusion (by simp) (b.comp a) :=
  (rfl)

theorem sharpTerm_succ (b : ParameterSymbol n Λ W U m') (a : ParameterSymbol n Λ V W m) (k : ℕ) :
    b.sharpTerm a (k + 1) = (-Complex.I / (k + 1 : ℂ)) • ∑ j : Fin n,
      inclusion (by push_cast; linarith)
        ((b.frequencyDeriv (EuclideanSpace.single j 1)).sharpTerm
          (a.spatialDeriv (EuclideanSpace.single j 1)) k) :=
  (rfl)

/-- The term without derivatives is the pointwise composition. -/
@[simp]
theorem coefficient_sharpTerm_zero (b : ParameterSymbol n Λ W U m')
    (a : ParameterSymbol n Λ V W m) (p : (CoordinateSpace n × CoordinateSpace n) × ℂ) :
    (b.sharpTerm a 0).coefficient p = b.coefficient p ∘L a.coefficient p := by
  simp [sharpTerm_zero]

/-- The coefficient of `sharpTerm b a k` only depends on the number `k` of derivatives, not on how
it is written. -/
private theorem coefficient_sharpTerm_congr {k k' : ℕ} (h : k = k')
    (b : ParameterSymbol n Λ W U m') (a : ParameterSymbol n Λ V W m) :
    (b.sharpTerm a k).coefficient = (b.sharpTerm a k').coefficient := by
  subst h
  rfl

/-- At a spectral parameter in `Λ`, a frequency derivative along a word of the frequency
derivative `∂_{ξ_j} b` is the frequency derivative of `b` along the word extended by `j`. -/
private theorem coordinateDeriv_frequencyDeriv (b : ParameterSymbol n Λ W U m')
    (w : List (Fin n)) (j : Fin n) {x : CoordinateSpace n} {z : ℂ} (hz : z ∈ Λ) :
    coordinateDeriv w
        (fun η => (b.frequencyDeriv (EuclideanSpace.single j 1)).coefficient ((x, η), z)) =
      coordinateDeriv (w ++ [j]) (fun η => b.coefficient ((x, η), z)) :=
  coordinateDeriv_eq_append_singleton w j fun η => coefficient_frequencyDeriv b _ x η hz

/-- At a spectral parameter in `Λ`, a spatial derivative along a word of the spatial derivative
`∂_{x_j} a` is the spatial derivative of `a` along the word extended by `j`. -/
private theorem coordinateDeriv_spatialDeriv (a : ParameterSymbol n Λ V W m) (w : List (Fin n))
    (j : Fin n) {ξ : CoordinateSpace n} {z : ℂ} (hz : z ∈ Λ) :
    coordinateDeriv w
        (fun y => (a.spatialDeriv (EuclideanSpace.single j 1)).coefficient ((y, ξ), z)) =
      coordinateDeriv (w ++ [j]) (fun y => a.coefficient ((y, ξ), z)) :=
  coordinateDeriv_eq_append_singleton w j fun y => coefficient_spatialDeriv a _ y ξ hz

/-- **Closed form of the composition terms.** At a spectral parameter in `Λ`, `sharpTerm b a k` is
`((-i)ᵏ / k!) ∑_{|w| = k} ∂_ξ^w b ∘ ∂_x^w a`, the sum over the words `w` of length `k` in the
coordinate directions. -/
theorem coefficient_sharpTerm (b : ParameterSymbol n Λ W U m') (a : ParameterSymbol n Λ V W m)
    (k : ℕ) (x ξ : CoordinateSpace n) {z : ℂ} (hz : z ∈ Λ) :
    (b.sharpTerm a k).coefficient ((x, ξ), z) =
      ((-Complex.I) ^ k / k.factorial : ℂ) • ∑ w : Fin k → Fin n,
        coordinateDeriv (List.ofFn w) (fun η => b.coefficient ((x, η), z)) ξ ∘L
          coordinateDeriv (List.ofFn w) (fun y => a.coefficient ((y, ξ), z)) x := by
  induction k generalizing m' b a with
  | zero => simp
  | succ k ih =>
    rw [sharpTerm_succ, coefficient_smul, Pi.smul_apply, coefficient_sum, Finset.sum_apply]
    simp only [coefficient_inclusion, ih, coordinateDeriv_frequencyDeriv _ _ _ hz,
      coordinateDeriv_spatialDeriv _ _ _ hz, Finset.smul_sum, smul_smul]
    rw [← (Fin.snocEquiv fun _ => Fin n).sum_comp, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun w _ => ?_
    simp only [Fin.snocEquiv_apply, List.ofFn_succ', Fin.snoc_castSucc, Fin.snoc_last,
      List.concat_eq_append]
    congr 1
    rw [Nat.factorial_succ]
    push_cast
    field_simp
    ring

/-- The composition terms vanish when the right factor is zero. -/
@[simp]
theorem sharpTerm_zero_right (b : ParameterSymbol n Λ W U m') (k : ℕ) :
    b.sharpTerm (0 : ParameterSymbol n Λ V W m) k = 0 := by
  induction k generalizing m' b with
  | zero => exact ext_of_mem fun x ξ z _ => by simp
  | succ k ih => simp [sharpTerm_succ, ih]

/-- The composition terms vanish when the left factor is zero. -/
@[simp]
theorem sharpTerm_zero_left (a : ParameterSymbol n Λ V W m) (k : ℕ) :
    (0 : ParameterSymbol n Λ W U m').sharpTerm a k = 0 := by
  induction k generalizing m' m a with
  | zero => exact ext_of_mem fun x ξ z _ => by simp
  | succ k ih => simp [sharpTerm_succ, ih]

/-- If the right factor does not depend on the position, the terms with derivatives vanish: only
the pointwise composition `sharpTerm b a 0 = b ∘ a` remains of the formal composition. -/
theorem sharpTerm_succ_eq_zero_of_spatialDeriv_eq_zero (b : ParameterSymbol n Λ W U m')
    {a : ParameterSymbol n Λ V W m} (ha : ∀ v, a.spatialDeriv v = 0) (k : ℕ) :
    b.sharpTerm a (k + 1) = 0 := by
  simp [sharpTerm_succ, ha]

/-- If `b` is polynomial of degree less than `d` in the frequency, that is, its frequency
derivatives along all words of length `d` vanish, then the composition terms `sharpTerm b a k`
with `k ≥ d` vanish. -/
theorem coefficient_sharpTerm_eq_zero_of_coordinateDeriv_eq_zero {b : ParameterSymbol n Λ W U m'}
    {d : ℕ} (hb : ∀ x, ∀ z ∈ Λ, ∀ w : List (Fin n), w.length = d →
      coordinateDeriv w (fun η => b.coefficient ((x, η), z)) = 0)
    (a : ParameterSymbol n Λ V W m) {k : ℕ} (hk : d ≤ k) (x ξ : CoordinateSpace n) {z : ℂ}
    (hz : z ∈ Λ) : (b.sharpTerm a k).coefficient ((x, ξ), z) = 0 := by
  rw [coefficient_sharpTerm b a k x ξ hz, Finset.sum_eq_zero fun w _ => ?_, smul_zero]
  rw [← List.take_append_drop (k - d) (List.ofFn w), coordinateDeriv_append,
    hb x z hz _ (by simp; omega), coordinateDeriv_zero, Pi.zero_apply,
    ContinuousLinearMap.zero_comp]

/-- **Homogeneity of the composition terms.** If `b` and `a` are homogeneous of degrees `μ'` and
`μ` under `(ξ, z) ↦ (t ξ, t² z)`, the term `sharpTerm b a k` is homogeneous of degree
`μ' + μ - k`. -/
theorem IsQuasiHomogeneous.sharpTerm {μ μ' : ℝ} {b : ParameterSymbol n Λ W U m'}
    {a : ParameterSymbol n Λ V W m} (hb : b.IsQuasiHomogeneous μ') (ha : a.IsQuasiHomogeneous μ)
    (k : ℕ) :
    (b.sharpTerm a k).IsQuasiHomogeneous (μ' + μ - k) := by
  induction k generalizing m' μ' b μ a with
  | zero =>
    rw [sharpTerm_zero]
    exact ((hb.comp ha).inclusion _).congr_degree (by simp)
  | succ k ih =>
    rw [sharpTerm_succ]
    refine (IsQuasiHomogeneous.sum fun j _ => ?_).smul _
    exact ((ih (hb.frequencyDeriv _) (ha.spatialDeriv _)).inclusion _).congr_degree
      (by push_cast; ring)

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
    coefficient_sharpTerm_congr (show k + 1 - (k + 1 + 0) = 0 by omega),
    coefficient_sharpTerm_zero]

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
    coefficient_sharpTerm_congr (show k + 1 - (0 + (k + 1)) = 0 by omega),
    coefficient_sharpTerm_zero]

/-- **Homogeneity of the formal composition.** If `qᵢ` and `pⱼ` are homogeneous of degrees
`μ' - i` and `μ - j`, the term `cₖ` of `sharpTerms q p` is homogeneous of degree `μ' + μ - k`. -/
theorem IsQuasiHomogeneous.sharpTerms {μ μ' : ℝ} (hq : ∀ i, (q i).IsQuasiHomogeneous (μ' - i))
    (hp : ∀ j, (p j).IsQuasiHomogeneous (μ - j)) (k : ℕ) :
    (sharpTerms q p k).IsQuasiHomogeneous (μ' + μ - k) := by
  refine IsQuasiHomogeneous.sum fun i _ => IsQuasiHomogeneous.sum fun j _ => ?_
  split_ifs with h
  · exact (((hq i).sharpTerm (hp j) _).inclusion _).congr_degree
      (by rw [Nat.cast_sub h]; push_cast; ring)
  · exact isQuasiHomogeneous_zero

end SharpTerms

/-! ### The formal parametrix -/

section Parametrix

variable [CompleteSpace V]

/-- The orders of the summands in the recursion for the left parametrix. -/
private theorem leftInverseTerms_order_le (N : ℕ) (j : Fin (N + 1)) :
    -m - (j : ℕ) + m - ((N + 1 - j : ℕ) : ℝ) ≤ -((N + 1 : ℕ) : ℝ) := by
  rw [Nat.cast_sub j.isLt.le]
  push_cast
  linarith

/-- The terms `b₀, b₁, …` of the formal left parametrix of a symbol `a` of order `m` elliptic with
parameter, with `bⱼ` of order `-m - j`: `b₀ = a⁻¹` and
`b_{N+1} = -(∑_{j ≤ N} sharpTerm bⱼ a (N + 1 - j)) ∘ a⁻¹`. They solve the formal composition
equations `∑_{j + k = N} sharpTerm bⱼ a k = δ_{N,0}`
(`TauCeti.ParameterSymbol.sum_coefficient_sharpTerm_leftInverseTerms`). -/
def leftInverseTerms (a : ParameterSymbol n Λ V W m) (ha : a.IsElliptic) :
    (N : ℕ) → ParameterSymbol n Λ W V (-m - N)
  | 0 => inclusion (by simp) (a.inverse ha)
  | N + 1 => inclusion (le_of_eq (by push_cast; ring))
      (-((∑ j : Fin (N + 1), inclusion (leftInverseTerms_order_le N j)
        ((leftInverseTerms a ha j).sharpTerm a (N + 1 - j))).comp (a.inverse ha)))
decreasing_by exact j.isLt

variable {a : ParameterSymbol n Λ V W m}

/-- The leading term of the left parametrix is the inverse symbol. -/
@[simp]
theorem coefficient_leftInverseTerms_zero (ha : a.IsElliptic)
    (p : (CoordinateSpace n × CoordinateSpace n) × ℂ) :
    (a.leftInverseTerms ha 0).coefficient p = (a.coefficient p).inverse := by
  simp [leftInverseTerms]

theorem coefficient_leftInverseTerms_succ (ha : a.IsElliptic) (N : ℕ)
    (p : (CoordinateSpace n × CoordinateSpace n) × ℂ) :
    (a.leftInverseTerms ha (N + 1)).coefficient p =
      -((∑ j ∈ range (N + 1),
          ((a.leftInverseTerms ha j).sharpTerm a (N + 1 - j)).coefficient p) ∘L
        (a.coefficient p).inverse) := by
  rw [leftInverseTerms]
  simp [Fin.sum_univ_eq_sum_range
    (fun j => ((a.leftInverseTerms ha j).sharpTerm a (N + 1 - j)).coefficient p)]

/-- **The formal left parametrix with parameter.** For a symbol `a` of order `m` elliptic with
parameter, the symbols `bⱼ = a.leftInverseTerms ha j` of order `-m - j` solve the formal
composition equations: `∑_{j + k = N} sharpTerm bⱼ a k` is the identity for `N = 0` and vanishes
for `N ≥ 1`, at every spectral parameter in `Λ`. -/
theorem sum_coefficient_sharpTerm_leftInverseTerms (ha : a.IsElliptic) (N : ℕ)
    (x ξ : CoordinateSpace n) {z : ℂ} (hz : z ∈ Λ) :
    ∑ j ∈ range (N + 1),
        ((a.leftInverseTerms ha j).sharpTerm a (N - j)).coefficient ((x, ξ), z) =
      if N = 0 then ContinuousLinearMap.id ℂ V else 0 := by
  have h := (ha.isInvertible x ξ z hz).inverse_comp_self
  rcases N with _ | N
  · simpa using h
  rw [Finset.sum_range_succ, coefficient_sharpTerm_congr (Nat.sub_self (N + 1))]
  simp [coefficient_leftInverseTerms_succ, ContinuousLinearMap.comp_assoc, h]

/-- The orders of the summands in the recursion for the right parametrix. -/
private theorem rightInverseTerms_order_le (N : ℕ) (j : Fin (N + 1)) :
    m + (-m - (j : ℕ)) - ((N + 1 - j : ℕ) : ℝ) ≤ -((N + 1 : ℕ) : ℝ) := by
  rw [Nat.cast_sub j.isLt.le]
  push_cast
  linarith

variable (a) in
/-- The terms `b₀, b₁, …` of the formal right parametrix of a symbol `a` of order `m` elliptic with
parameter, with `bⱼ` of order `-m - j`: `b₀ = a⁻¹` and
`b_{N+1} = -a⁻¹ ∘ ∑_{j ≤ N} sharpTerm a bⱼ (N + 1 - j)`. They solve the formal composition
equations `∑_{j + k = N} sharpTerm a bⱼ k = δ_{N,0}`
(`TauCeti.ParameterSymbol.sum_coefficient_sharpTerm_rightInverseTerms`). -/
def rightInverseTerms (ha : a.IsElliptic) : (N : ℕ) → ParameterSymbol n Λ W V (-m - N)
  | 0 => inclusion (by simp) (a.inverse ha)
  | N + 1 => inclusion (le_of_eq (by push_cast; ring))
      (-((a.inverse ha).comp (∑ j : Fin (N + 1), inclusion (rightInverseTerms_order_le N j)
        (a.sharpTerm (rightInverseTerms ha j) (N + 1 - j)))))
decreasing_by exact j.isLt

/-- The leading term of the right parametrix is the inverse symbol. -/
@[simp]
theorem coefficient_rightInverseTerms_zero (ha : a.IsElliptic)
    (p : (CoordinateSpace n × CoordinateSpace n) × ℂ) :
    (a.rightInverseTerms ha 0).coefficient p = (a.coefficient p).inverse := by
  simp [rightInverseTerms]

theorem coefficient_rightInverseTerms_succ (ha : a.IsElliptic) (N : ℕ)
    (p : (CoordinateSpace n × CoordinateSpace n) × ℂ) :
    (a.rightInverseTerms ha (N + 1)).coefficient p =
      -((a.coefficient p).inverse ∘L
        ∑ j ∈ range (N + 1),
          (a.sharpTerm (a.rightInverseTerms ha j) (N + 1 - j)).coefficient p) := by
  rw [rightInverseTerms]
  simp [Fin.sum_univ_eq_sum_range
    (fun j => (a.sharpTerm (a.rightInverseTerms ha j) (N + 1 - j)).coefficient p)]

/-- **The formal right parametrix with parameter.** For a symbol `a` of order `m` elliptic with
parameter, the symbols `bⱼ = a.rightInverseTerms ha j` of order `-m - j` solve the formal
composition equations: `∑_{j + k = N} sharpTerm a bⱼ k` is the identity for `N = 0` and vanishes
for `N ≥ 1`, at every spectral parameter in `Λ`. -/
theorem sum_coefficient_sharpTerm_rightInverseTerms (ha : a.IsElliptic) (N : ℕ)
    (x ξ : CoordinateSpace n) {z : ℂ} (hz : z ∈ Λ) :
    ∑ j ∈ range (N + 1),
        (a.sharpTerm (a.rightInverseTerms ha j) (N - j)).coefficient ((x, ξ), z) =
      if N = 0 then ContinuousLinearMap.id ℂ W else 0 := by
  have h := (ha.isInvertible x ξ z hz).self_comp_inverse
  rcases N with _ | N
  · simpa using h
  rw [Finset.sum_range_succ, coefficient_sharpTerm_congr (Nat.sub_self (N + 1))]
  simp [coefficient_rightInverseTerms_succ, ← ContinuousLinearMap.comp_assoc, h]

/-- For a symbol that does not depend on the position, the correction terms of the left
parametrix vanish: it consists of the inverse symbol alone. -/
theorem leftInverseTerms_succ_eq_zero_of_spatialDeriv_eq_zero (ha : a.IsElliptic)
    (h : ∀ v, a.spatialDeriv v = 0) (N : ℕ) : a.leftInverseTerms ha (N + 1) = 0 := by
  refine ext_of_mem fun x ξ z _ => ?_
  have hterm : ∀ j ∈ range (N + 1),
      ((a.leftInverseTerms ha j).sharpTerm a (N + 1 - j)).coefficient ((x, ξ), z) = 0 :=
    fun j hj => by
      rw [coefficient_sharpTerm_congr (show N + 1 - j = N - j + 1 by grind),
        sharpTerm_succ_eq_zero_of_spatialDeriv_eq_zero _ h]
      simp
  simp [coefficient_leftInverseTerms_succ, Finset.sum_eq_zero hterm]

/-- For the symbol of `s - Δ - z`, which does not depend on the position, the correction terms of
the left parametrix vanish: it consists of the resolvent symbol `((s + ‖ξ‖²) - z)⁻¹` alone
(`TauCeti.ParameterSymbol.coefficient_inverse_shiftedLaplacian`). -/
theorem leftInverseTerms_shiftedLaplacian_succ_eq_zero {s : ℝ}
    (h : (shiftedLaplacian V s : ParameterSymbol n Λ V V 2).IsElliptic) (N : ℕ) :
    (shiftedLaplacian V s).leftInverseTerms h (N + 1) = 0 :=
  leftInverseTerms_succ_eq_zero_of_spatialDeriv_eq_zero h (spatialDeriv_shiftedLaplacian s) N

end Parametrix

/-! ### The formal left and right inverses of an expansion -/

section ExpansionParametrix

variable [CompleteSpace V] (a : (j : ℕ) → ParameterSymbol n Λ V W (m - j)) (ha : (a 0).IsElliptic)

/-- The terms `q_k` of order `-m - k` of the formal left inverse of an expansion `a ∼ ∑ⱼ aⱼ`
whose leading term is elliptic with parameter: `q₀ = a₀⁻¹` and, for `k ≥ 0`,
`q_{k+1} = -(∑' sharpTerm qᵢ aⱼ r) ∘ a₀⁻¹`, where the sum runs over the terms of `c_{k+1}` in
`sharpTerms q a` other than `q_{k+1} ∘ a₀`. -/
def expansionLeftInverseTerms : (k : ℕ) → ParameterSymbol n Λ W V (-m - k)
  | 0 => inclusion (by simp) ((a 0).inverse ha)
  | k + 1 => inclusion (by push_cast; linarith) (-((∑ i ∈ (range (k + 1)).attach,
      ∑ j ∈ range (k + 2), if h : (i : ℕ) + j ≤ k + 1 then
        inclusion (m' := -(k + 1 : ℕ)) (by rw [Nat.cast_sub h]; push_cast; linarith)
          ((expansionLeftInverseTerms i).sharpTerm (a j) (k + 1 - (i + j)))
      else 0).comp ((a 0).inverse ha)))
  decreasing_by exact Finset.mem_range.1 i.property

@[simp]
theorem coefficient_expansionLeftInverseTerms_zero
    (x : (CoordinateSpace n × CoordinateSpace n) × ℂ) :
    (expansionLeftInverseTerms a ha 0).coefficient x = ((a 0).coefficient x).inverse := by
  rw [expansionLeftInverseTerms]
  simp

/-- The recursion defining the formal left inverse of an expansion. -/
theorem coefficient_expansionLeftInverseTerms_succ (k : ℕ)
    (x : (CoordinateSpace n × CoordinateSpace n) × ℂ) :
    (expansionLeftInverseTerms a ha (k + 1)).coefficient x =
      -((∑ i ∈ range (k + 1), ∑ j ∈ range (k + 2),
        if i + j ≤ k + 1 then ((expansionLeftInverseTerms a ha i).sharpTerm (a j)
          (k + 1 - (i + j))).coefficient x else 0) ∘L ((a 0).coefficient x).inverse) := by
  rw [expansionLeftInverseTerms]
  simp only [coefficient_inclusion, coefficient_neg, coefficient_comp, coefficient_inverse,
    Pi.neg_apply, coefficient_sum, Finset.sum_apply]
  congr 2
  rw [← Finset.sum_attach (range (k + 1)) fun i => ∑ j ∈ range (k + 2),
    if i + j ≤ k + 1 then
      ((expansionLeftInverseTerms a ha i).sharpTerm (a j) (k + 1 - (i + j))).coefficient x
    else 0]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  split_ifs <;> simp

/-- **The formal left inverse of an expansion.** The leading term of
`sharpTerms (expansionLeftInverseTerms a ha) a` is the identity at every spectral parameter in
`Λ`. -/
theorem coefficient_sharpTerms_expansionLeftInverseTerms_zero (x ξ : CoordinateSpace n) {z : ℂ}
    (hz : z ∈ Λ) :
    (sharpTerms (expansionLeftInverseTerms a ha) a 0).coefficient ((x, ξ), z) =
      ContinuousLinearMap.id ℂ V := by
  simp [(ha.isInvertible x ξ z hz).inverse_comp_self]

/-- **The formal left inverse of an expansion.** All terms of
`sharpTerms (expansionLeftInverseTerms a ha) a` after the leading one vanish. -/
@[simp]
theorem sharpTerms_expansionLeftInverseTerms_succ (k : ℕ) :
    sharpTerms (expansionLeftInverseTerms a ha) a (k + 1) = 0 :=
  ext_of_mem fun x ξ z hz => by
    rw [coefficient_sharpTerms_succ, coefficient_expansionLeftInverseTerms_succ,
      ContinuousLinearMap.neg_comp, ContinuousLinearMap.comp_assoc,
      (ha.isInvertible x ξ z hz).inverse_comp_self]
    simp

/-- **Uniqueness of the formal left inverse.** A sequence `q` of parameter-dependent symbols is the
formal left inverse of the expansion `a` exactly when the formal composition `sharpTerms q a` is
the identity. -/
theorem eq_expansionLeftInverseTerms_iff {q : (i : ℕ) → ParameterSymbol n Λ W V (-m - i)} :
    q = expansionLeftInverseTerms a ha ↔
      (∀ x ξ, ∀ z ∈ Λ, (sharpTerms q a 0).coefficient ((x, ξ), z) = ContinuousLinearMap.id ℂ V) ∧
        ∀ k, sharpTerms q a (k + 1) = 0 := by
  refine ⟨?_, fun ⟨h0, hsucc⟩ => funext fun k => ?_⟩
  · rintro rfl
    exact ⟨fun x ξ z hz => coefficient_sharpTerms_expansionLeftInverseTerms_zero a ha x ξ hz,
      sharpTerms_expansionLeftInverseTerms_succ a ha⟩
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
    rw [eq_neg_of_add_eq_zero_left h, coefficient_expansionLeftInverseTerms_succ,
      ContinuousLinearMap.neg_comp]
    congr 2
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [ih i (by simpa using Finset.mem_range.1 hi)]

/-- **Homogeneity of the formal left inverse.** If each term `aⱼ` is homogeneous of degree
`μ - j` under `(ξ, z) ↦ (t ξ, t² z)`, the term `q_k` of the formal left inverse is homogeneous of
degree `-μ - k`. For `a = ‖ξ‖² - z` these are the jointly homogeneous terms of the resolvent
symbol. -/
theorem isQuasiHomogeneous_expansionLeftInverseTerms {μ : ℝ}
    (hhom : ∀ j, (a j).IsQuasiHomogeneous (μ - j)) (k : ℕ) :
    (expansionLeftInverseTerms a ha k).IsQuasiHomogeneous (-μ - k) := by
  induction k using Nat.strong_induction_on with | _ k ih
  cases k with
  | zero =>
    rw [expansionLeftInverseTerms]
    exact (((hhom 0).inverse ha).inclusion _).congr_degree (by simp)
  | succ k =>
    rw [expansionLeftInverseTerms]
    refine IsQuasiHomogeneous.inclusion (IsQuasiHomogeneous.neg ?_) _
    refine (IsQuasiHomogeneous.comp (μ' := -((k + 1 : ℕ) : ℝ))
      (IsQuasiHomogeneous.sum fun i _ => IsQuasiHomogeneous.sum fun j _ => ?_)
      ((hhom 0).inverse ha)).congr_degree (by push_cast; ring)
    split_ifs with h
    · exact (((ih i (Finset.mem_range.1 i.property)).sharpTerm (hhom j) _).inclusion _).congr_degree
        (by rw [Nat.cast_sub h]; push_cast; ring)
    · exact isQuasiHomogeneous_zero

/-- The terms `q_k` of order `-m - k` of the formal right inverse of an expansion `a ∼ ∑ᵢ aᵢ`
whose leading term is elliptic with parameter: `q₀ = a₀⁻¹` and, for `k ≥ 0`,
`q_{k+1} = -a₀⁻¹ ∘ ∑' sharpTerm aᵢ qⱼ r`, where the sum runs over the terms of `c_{k+1}` in
`sharpTerms a q` other than `a₀ ∘ q_{k+1}`. -/
def expansionRightInverseTerms : (k : ℕ) → ParameterSymbol n Λ W V (-m - k)
  | 0 => inclusion (by simp) ((a 0).inverse ha)
  | k + 1 => inclusion (by push_cast; linarith) (-(((a 0).inverse ha).comp
      (∑ j ∈ (range (k + 1)).attach, ∑ i ∈ range (k + 2), if h : i + (j : ℕ) ≤ k + 1 then
        inclusion (m' := -(k + 1 : ℕ)) (by rw [Nat.cast_sub h]; push_cast; linarith)
          ((a i).sharpTerm (expansionRightInverseTerms j) (k + 1 - (i + j)))
      else 0)))
  decreasing_by exact Finset.mem_range.1 j.property

@[simp]
theorem coefficient_expansionRightInverseTerms_zero
    (x : (CoordinateSpace n × CoordinateSpace n) × ℂ) :
    (expansionRightInverseTerms a ha 0).coefficient x = ((a 0).coefficient x).inverse := by
  rw [expansionRightInverseTerms]
  simp

/-- The recursion defining the formal right inverse of an expansion. -/
theorem coefficient_expansionRightInverseTerms_succ (k : ℕ)
    (x : (CoordinateSpace n × CoordinateSpace n) × ℂ) :
    (expansionRightInverseTerms a ha (k + 1)).coefficient x =
      -(((a 0).coefficient x).inverse ∘L ∑ j ∈ range (k + 1), ∑ i ∈ range (k + 2),
        if i + j ≤ k + 1 then ((a i).sharpTerm (expansionRightInverseTerms a ha j)
          (k + 1 - (i + j))).coefficient x else 0) := by
  rw [expansionRightInverseTerms]
  simp only [coefficient_inclusion, coefficient_neg, coefficient_comp, coefficient_inverse,
    Pi.neg_apply, coefficient_sum, Finset.sum_apply]
  congr 2
  rw [← Finset.sum_attach (range (k + 1)) fun j => ∑ i ∈ range (k + 2),
    if i + j ≤ k + 1 then
      ((a i).sharpTerm (expansionRightInverseTerms a ha j) (k + 1 - (i + j))).coefficient x
    else 0]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> simp

/-- **The formal right inverse of an expansion.** The leading term of
`sharpTerms a (expansionRightInverseTerms a ha)` is the identity at every spectral parameter in
`Λ`. -/
theorem coefficient_sharpTerms_expansionRightInverseTerms_zero (x ξ : CoordinateSpace n) {z : ℂ}
    (hz : z ∈ Λ) :
    (sharpTerms a (expansionRightInverseTerms a ha) 0).coefficient ((x, ξ), z) =
      ContinuousLinearMap.id ℂ W := by
  simp [(ha.isInvertible x ξ z hz).self_comp_inverse]

/-- **The formal right inverse of an expansion.** All terms of
`sharpTerms a (expansionRightInverseTerms a ha)` after the leading one vanish. -/
@[simp]
theorem sharpTerms_expansionRightInverseTerms_succ (k : ℕ) :
    sharpTerms a (expansionRightInverseTerms a ha) (k + 1) = 0 :=
  ext_of_mem fun x ξ z hz => by
    rw [coefficient_sharpTerms_succ', coefficient_expansionRightInverseTerms_succ,
      ContinuousLinearMap.comp_neg, ← ContinuousLinearMap.comp_assoc,
      (ha.isInvertible x ξ z hz).self_comp_inverse]
    simp

/-- **Uniqueness of the formal right inverse.** A sequence `q` of parameter-dependent symbols is the
formal right inverse of the expansion `a` exactly when the formal composition `sharpTerms a q` is
the identity. -/
theorem eq_expansionRightInverseTerms_iff {q : (j : ℕ) → ParameterSymbol n Λ W V (-m - j)} :
    q = expansionRightInverseTerms a ha ↔
      (∀ x ξ, ∀ z ∈ Λ, (sharpTerms a q 0).coefficient ((x, ξ), z) = ContinuousLinearMap.id ℂ W) ∧
        ∀ k, sharpTerms a q (k + 1) = 0 := by
  refine ⟨?_, fun ⟨h0, hsucc⟩ => funext fun k => ?_⟩
  · rintro rfl
    exact ⟨fun x ξ z hz => coefficient_sharpTerms_expansionRightInverseTerms_zero a ha x ξ hz,
      sharpTerms_expansionRightInverseTerms_succ a ha⟩
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
    rw [eq_neg_of_add_eq_zero_left h, coefficient_expansionRightInverseTerms_succ,
      ContinuousLinearMap.comp_neg]
    congr 2
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [ih j (by simpa using Finset.mem_range.1 hj)]

/-- **Homogeneity of the formal right inverse.** If each term `aᵢ` is homogeneous of degree
`μ - i` under `(ξ, z) ↦ (t ξ, t² z)`, the term `q_k` of the formal right inverse is homogeneous of
degree `-μ - k`. -/
theorem isQuasiHomogeneous_expansionRightInverseTerms {μ : ℝ}
    (hhom : ∀ i, (a i).IsQuasiHomogeneous (μ - i)) (k : ℕ) :
    (expansionRightInverseTerms a ha k).IsQuasiHomogeneous (-μ - k) := by
  induction k using Nat.strong_induction_on with | _ k ih
  cases k with
  | zero =>
    rw [expansionRightInverseTerms]
    exact (((hhom 0).inverse ha).inclusion _).congr_degree (by simp)
  | succ k =>
    rw [expansionRightInverseTerms]
    refine IsQuasiHomogeneous.inclusion (IsQuasiHomogeneous.neg ?_) _
    refine (((hhom 0).inverse ha).comp (μ := -((k + 1 : ℕ) : ℝ))
      (IsQuasiHomogeneous.sum fun j _ => IsQuasiHomogeneous.sum fun i _ => ?_)).congr_degree
      (by push_cast; ring)
    split_ifs with h
    · exact (((hhom i).sharpTerm (ih j (Finset.mem_range.1 j.property)) _).inclusion _).congr_degree
        (by rw [Nat.cast_sub h]; push_cast; ring)
    · exact isQuasiHomogeneous_zero

end ExpansionParametrix

/-! ### Single symbols as one-term expansions -/

section OneTermExpansion

variable [CompleteSpace V] {a : ParameterSymbol n Λ V W m} (ha : a.IsElliptic)
  {e : (j : ℕ) → ParameterSymbol n Λ V W (m - j)} (he : (e 0).IsElliptic)

/-- **The parametrix of a single symbol.** For the one-term expansion `e = (a, 0, 0, …)` of a
symbol `a` elliptic with parameter, the formal left inverse of the expansion is the left
parametrix `TauCeti.ParameterSymbol.leftInverseTerms` of `a`. -/
theorem expansionLeftInverseTerms_eq_leftInverseTerms (h₀ : (e 0).coefficient = a.coefficient)
    (h₁ : ∀ j, e (j + 1) = 0) : expansionLeftInverseTerms e he = a.leftInverseTerms ha := by
  refine ((eq_expansionLeftInverseTerms_iff e he).2 ⟨fun x ξ z hz => ?_, fun k => ?_⟩).symm
  · simp [h₀, (ha.isInvertible x ξ z hz).inverse_comp_self]
  refine ext_of_mem fun x ξ z hz => ?_
  have h := sum_coefficient_sharpTerm_leftInverseTerms ha (k + 1) x ξ hz
  rw [ite_eq_right k.succ_ne_zero] at h
  rw [coefficient_sharpTerms, coefficient_zero, Pi.zero_apply]
  refine (Finset.sum_congr rfl fun i hi => ?_).trans h
  rw [Finset.sum_range_succ', Finset.sum_eq_zero fun j _ => by simp [h₁], zero_add,
    ite_eq_left (by have := Finset.mem_range.1 hi; omega), coefficient_sharpTerm _ _ _ _ _ hz,
    coefficient_sharpTerm _ _ _ _ _ hz, h₀, add_zero]

/-- **The parametrix of a single symbol.** For the one-term expansion `e = (a, 0, 0, …)` of a
symbol `a` elliptic with parameter, the formal right inverse of the expansion is the right
parametrix `TauCeti.ParameterSymbol.rightInverseTerms` of `a`. -/
theorem expansionRightInverseTerms_eq_rightInverseTerms (h₀ : (e 0).coefficient = a.coefficient)
    (h₁ : ∀ j, e (j + 1) = 0) : expansionRightInverseTerms e he = a.rightInverseTerms ha := by
  refine ((eq_expansionRightInverseTerms_iff e he).2 ⟨fun x ξ z hz => ?_, fun k => ?_⟩).symm
  · simp [h₀, (ha.isInvertible x ξ z hz).self_comp_inverse]
  refine ext_of_mem fun x ξ z hz => ?_
  have h := sum_coefficient_sharpTerm_rightInverseTerms ha (k + 1) x ξ hz
  rw [ite_eq_right k.succ_ne_zero] at h
  rw [coefficient_sharpTerms, coefficient_zero, Pi.zero_apply, Finset.sum_range_succ',
    Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => by simp [h₁], zero_add]
  refine (Finset.sum_congr rfl fun j hj => ?_).trans h
  rw [ite_eq_left (by have := Finset.mem_range.1 hj; omega), coefficient_sharpTerm _ _ _ _ _ hz,
    coefficient_sharpTerm _ _ _ _ _ hz, h₀, zero_add]

omit [CompleteSpace V] in
include ha in
/-- A symbol of order `m` is the one-term expansion `(a, 0, 0, …)`, elliptic with parameter and
homogeneous whenever `a` is. -/
private theorem exists_oneTermExpansion :
    ∃ (e : (j : ℕ) → ParameterSymbol n Λ V W (m - j)) (_ : (e 0).IsElliptic),
      (e 0).coefficient = a.coefficient ∧ (∀ j, e (j + 1) = 0) ∧
        ∀ μ, a.IsQuasiHomogeneous μ → ∀ j, (e j).IsQuasiHomogeneous (μ - j) := by
  refine ⟨fun j => if h : j = 0 then inclusion (by simp [h]) a else 0,
    ⟨fun x ξ z hz => by simpa using ha.isInvertible x ξ z hz,
      fun K hK => by simpa using ha.exists_bound K hK⟩, by simp, by simp, fun μ hμ j => ?_⟩
  rcases j with _ | j
  · simpa using hμ
  · simp

/-- **Homogeneity of the left parametrix.** If `a` is homogeneous of degree `μ` under
`(ξ, z) ↦ (t ξ, t² z)`, the term `bₖ` of its left parametrix is homogeneous of degree `-μ - k`. -/
theorem isQuasiHomogeneous_leftInverseTerms {μ : ℝ} (hμ : a.IsQuasiHomogeneous μ) (k : ℕ) :
    (a.leftInverseTerms ha k).IsQuasiHomogeneous (-μ - k) := by
  obtain ⟨e, he, h₀, h₁, hhom⟩ := exists_oneTermExpansion ha
  rw [← expansionLeftInverseTerms_eq_leftInverseTerms ha he h₀ h₁]
  exact isQuasiHomogeneous_expansionLeftInverseTerms e he (hhom μ hμ) k

/-- **Homogeneity of the right parametrix.** If `a` is homogeneous of degree `μ` under
`(ξ, z) ↦ (t ξ, t² z)`, the term `bₖ` of its right parametrix is homogeneous of degree `-μ - k`. -/
theorem isQuasiHomogeneous_rightInverseTerms {μ : ℝ} (hμ : a.IsQuasiHomogeneous μ) (k : ℕ) :
    (a.rightInverseTerms ha k).IsQuasiHomogeneous (-μ - k) := by
  obtain ⟨e, he, h₀, h₁, hhom⟩ := exists_oneTermExpansion ha
  rw [← expansionRightInverseTerms_eq_rightInverseTerms ha he h₀ h₁]
  exact isQuasiHomogeneous_expansionRightInverseTerms e he (hhom μ hμ) k

end OneTermExpansion

end ParameterSymbol

end TauCeti
