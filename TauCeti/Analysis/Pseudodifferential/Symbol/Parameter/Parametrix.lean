/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Symbol.Parameter.Basic

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

The definition and closed form of `TauCeti.ParameterSymbol.sharpTerm` follow
`TauCeti.HomogeneousSymbol.sharpTerm` and `TauCeti.Symbol.sharpTerm`, and the parametrix
recursions adapt `TauCeti.ClassicalSymbol.leftInverseTerms` and
`TauCeti.ClassicalSymbol.rightInverseTerms` to the parameter-dependent class.

## References

* M. A. Shubin, *Pseudodifferential Operators and Spectral Theory*, Chapter II, §9 and §11.
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

/-! ### The formal parametrix -/

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

end ParameterSymbol

end TauCeti
