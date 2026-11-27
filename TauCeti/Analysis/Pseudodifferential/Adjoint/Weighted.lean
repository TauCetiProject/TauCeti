/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Adjoint.Classical
public import TauCeti.Analysis.Pseudodifferential.Adjoint.Continuity
public import TauCeti.Analysis.Calculus.ContinuousLinearMapInverse

/-!
# Adjoints for weighted inner products

On sections of a vector bundle over a chart, written in a local frame, the `L²` inner product is
not the flat one: a fibre metric `h(x)` and a density `ρ(x) dx` give the pairing
`∫ ⟪u(x), ρ(x) h(x) v(x)⟫ dx`. This file computes formal adjoints of quantizations for such
pairings. A *weight* on `V`-valued functions is a smooth family `g(x)` of operators on `V`, and
the weighted pairing is `∫ ⟪u(x), g(x) v(x)⟫ dx`; for a metric and a density, `g = ρ h`.

Let `a` be a symbol of order `m` with compact spatial support, with values in operators between
complex Hilbert spaces `V` and `W`, and let `g` and `k` be smooth weights on `V` and `W`, with
`g(x)` invertible for every `x`. The **weighted adjoint symbol**

`a^♯ = g⁻¹ (k† a)*`  (`TauCeti.Symbol.weightedAdjoint`),

where `(k† a)(x, ξ) = k(x)† a(x, ξ)` and `*` is the adjoint symbol `TauCeti.Symbol.adjoint`, is a
symbol of order `m`, and its quantization is the formal adjoint of the quantization of `a` for the
two weighted pairings:

`∫ ⟪Op(a) u, k v⟫ = ∫ ⟪u, g Op(a^♯) v⟫`

(`TauCeti.Symbol.integral_inner_quantizeSchwartzValue_weightedAdjoint`). For the trivial weights it
is the adjoint symbol (`TauCeti.Symbol.weightedAdjoint_id`).

The adjoint expansion of `k† a` gives the **weighted adjoint expansion** with actual remainders:
for every `N`,

`a^♯ = ∑_{j < N} g⁻¹ ((-i)^j / j!) ∑_{|w| = j} (∂_x^w ∂_ξ^w (k† a))† + g⁻¹ R_N`

with `R_N` of order `m - N`
(`TauCeti.Symbol.weightedAdjoint_eq_sum_weightedAdjointTerm_add_weightedAdjointRemainder`). The
leading term is the pointwise adjoint of `a(x, ξ)` for the two weights, `g(x)⁻¹ a(x, ξ)† k(x)`
(`TauCeti.Symbol.coefficient_weightedAdjointTerm_zero`). The next term contains the derivatives of
the weight `k`:

`-i ∑ⱼ g(x)⁻¹ ((∂_{xⱼ} ∂_{ξⱼ} a)(x, ξ)† k(x) + (∂_{ξⱼ} a)(x, ξ)† ∂ⱼ k(x))`

(`TauCeti.Symbol.coefficient_weightedAdjointTerm_one`), so with a density `ρ` that is not constant
the weighted adjoint can differ from the flat one already at order `m - 1`, through the term
`(∂_{ξⱼ} a)† ∂ⱼ k`.

For fixed weights, the weighted adjoint symbol, the terms and the remainders of its expansion are
additive and conjugate-linear in `a`. The remainders satisfy the continuity estimates of the
unweighted expansion: for compact sets `K` and `L`, each seminorm `p_{L,α,β}` of the remainder
`R_N^♯(a)` after `N` terms, in the class of order `m - N`, is at most a constant times finitely
many seminorms of `a` on `K`, for all `a` vanishing at positions outside `K`
(`TauCeti.Symbol.exists_seminorm_weightedAdjointRemainder_le`). The constant depends on the
weights. So a continuous family of symbols vanishing outside one compact set has continuous
families of weighted adjoint symbols and of remainders, the latter in the class of order `m - N`
(`Continuous.symbol_weightedAdjoint`, `Continuous.symbol_weightedAdjointRemainder`).

For a classical symbol `a` the weighted adjoint symbol is classical, with principal symbol
`g(x)⁻¹ a_m(x, ξ)† k(x)`, and it is elliptic exactly when `a` is, if `k(x)` is invertible.

## Main declarations

* `TauCeti.Symbol.weightedAdjoint`: the weighted adjoint symbol `a^♯`.
* `TauCeti.Symbol.integral_inner_quantizeSchwartzValue_weightedAdjoint`: its quantization is the
  formal adjoint of `Op(a)` for the weighted pairings.
* `TauCeti.Symbol.weightedAdjoint_id`: for the trivial weights it is the adjoint symbol.
* `TauCeti.Symbol.weightedAdjointTerm` and `TauCeti.Symbol.weightedAdjointRemainder`: the terms of
  order `m - j` and the remainders of order `m - N` of its expansion, with
  `TauCeti.Symbol.weightedAdjoint_eq_sum_weightedAdjointTerm_add_weightedAdjointRemainder` and
  `TauCeti.Symbol.isAsymptoticSum_weightedAdjoint`.
* `TauCeti.Symbol.coefficient_weightedAdjointTerm_zero`,
  `TauCeti.Symbol.coefficient_weightedAdjointTerm_one`: the first two terms.
* `TauCeti.Symbol.weightedAdjoint_add`, `TauCeti.Symbol.weightedAdjoint_smul` and their analogues
  for the terms and remainders: additivity and conjugate-linearity in the symbol.
* `TauCeti.Symbol.exists_seminorm_weightedAdjointRemainder_le`,
  `TauCeti.Symbol.exists_seminorm_weightedAdjoint_le`: the seminorm estimates of the remainders and
  of the weighted adjoint symbol.
* `Continuous.symbol_weightedAdjoint`, `Continuous.symbol_weightedAdjointRemainder`: continuity in
  the symbol.
* `TauCeti.ClassicalSymbol.weightedAdjoint`: the weighted adjoint of a classical symbol, with
  `TauCeti.ClassicalSymbol.coefficient_principal_weightedAdjoint` and
  `TauCeti.ClassicalSymbol.isElliptic_weightedAdjoint_iff`.

## References

* M. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI* (2008), Lecture I, (2.3).
* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, Theorem 18.1.7.
-/

public section

noncomputable section

open MeasureTheory Real FourierTransform Finset
open TopologicalSpace (Compacts)
open scoped RealInnerProductSpace ContDiff SchwartzMap

namespace TauCeti

namespace Symbol

variable {n : ℕ} {m : ℝ} {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [CompleteSpace V] [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W]
  {g : CoordinateSpace n → V →L[ℂ] V} {k : CoordinateSpace n → W →L[ℂ] W}

open ContinuousLinearMap (adjointRealCLM adjointRealCLM_apply)

omit [CompleteSpace V] in
/-- The symbol `(x, ξ) ↦ k(x)† a(x, ξ)`, the composition of `a` with the pointwise adjoint of the
weight `k`, of order `m`. -/
private def weightComp (hk : ContDiff ℝ ∞ k) (a : Symbol n V W m) : Symbol n V W (0 + m) :=
  (ofSpatial _ hk.clm_adjoint).comp a

omit [CompleteSpace V] in
private theorem coefficient_weightComp (hk : ContDiff ℝ ∞ k) (a : Symbol n V W m) :
    (weightComp hk a).coefficient =
      fun p ↦ ContinuousLinearMap.adjoint (k p.1) ∘L a.coefficient p :=
  funext fun p ↦ by simp [weightComp]

omit [CompleteSpace V] in
private theorem HasCompactSpatialSupport.weightComp {a : Symbol n V W m}
    (ha : a.HasCompactSpatialSupport) (hk : ContDiff ℝ ∞ k) :
    (weightComp hk a).HasCompactSpatialSupport :=
  ha.comp_left _

/-- The symbol of multiplication by the pointwise inverse `g(x)⁻¹` of an invertible weight. -/
private def inverseWeight (hg : ContDiff ℝ ∞ g) (hgi : ∀ x, (g x).IsInvertible) :
    Symbol n V V 0 :=
  ofSpatial (fun x ↦ (g x).inverse) (hg.clm_inverse hgi)

/-! ### The weighted adjoint symbol -/

section WeightedAdjoint

variable (a : Symbol n V W m) (ha : a.HasCompactSpatialSupport) (hg : ContDiff ℝ ∞ g)
  (hgi : ∀ x, (g x).IsInvertible) (hk : ContDiff ℝ ∞ k)

/-- **The weighted adjoint symbol.** For a symbol `a` of order `m` with compact spatial support and
smooth weights `g` on `V` and `k` on `W`, with `g(x)` invertible, the symbol
`a^♯ = g⁻¹ (k† a)*` of order `m`, where `(k† a)(x, ξ) = k(x)† a(x, ξ)` and `*` is the adjoint
symbol. Its quantization is the formal adjoint of the quantization of `a` for the pairings
`∫ ⟪u, g v⟫` and `∫ ⟪w, k z⟫`
(`TauCeti.Symbol.integral_inner_quantizeSchwartzValue_weightedAdjoint`). -/
def weightedAdjoint : Symbol n W V m :=
  inclusion (by simp) ((inverseWeight hg hgi).comp (adjoint (weightComp hk a) (ha.weightComp hk)))

/-- The weighted adjoint symbol is `g(y)⁻¹` times the adjoint symbol of `k† a`:
`a^♯(y, ξ) = g(y)⁻¹ (∫ exp(2πi ⟪θ, y⟫) (k† a)^(θ, ξ - 2πθ) dθ)†`, where `(k† a)^(θ, ξ)` is the
Fourier transform of the position slice `x ↦ k(x)† a(x, ξ)` at `θ`. -/
theorem coefficient_weightedAdjoint (y ξ : CoordinateSpace n) :
    (weightedAdjoint a ha hg hgi hk).coefficient (y, ξ) = (g y).inverse ∘L
      ContinuousLinearMap.adjoint (∫ θ, (𝐞 ⟪θ, y⟫ : ℂ) • 𝓕 (fun x ↦
        ContinuousLinearMap.adjoint (k x) ∘L a.coefficient (x, ξ - (2 * π) • θ)) θ) := by
  simp [weightedAdjoint, inverseWeight, coefficient_adjoint, weightComp]

/-- **The weighted adjoint identity.** The quantization of the weighted adjoint symbol `a^♯` is
the formal adjoint of the quantization of `a` for the weighted pairings:
`∫ ⟪Op(a) u, k v⟫ = ∫ ⟪u, g Op(a^♯) v⟫` for all Schwartz functions `u` and `v`. -/
theorem integral_inner_quantizeSchwartzValue_weightedAdjoint (u : 𝓢(CoordinateSpace n, V))
    (v : 𝓢(CoordinateSpace n, W)) :
    ∫ x, inner ℂ (quantizeSchwartzValue a.coefficient u x) (k x (v x)) =
      ∫ x, inner ℂ (u x)
        (g x (quantizeSchwartzValue (weightedAdjoint a ha hg hgi hk).coefficient v x)) := by
  have hl (x : CoordinateSpace n) : inner ℂ (quantizeSchwartzValue a.coefficient u x) (k x (v x)) =
      inner ℂ (quantizeSchwartzValue (weightComp hk a).coefficient u x) (v x) := by
    rw [weightComp, quantizeSchwartzValue_ofSpatial_comp, ContinuousLinearMap.adjoint_inner_left]
  have hr (x : CoordinateSpace n) :
      g x (quantizeSchwartzValue (weightedAdjoint a ha hg hgi hk).coefficient v x) =
        quantizeSchwartzValue (adjoint (weightComp hk a) (ha.weightComp hk)).coefficient v x := by
    rw [weightedAdjoint, coefficient_inclusion, inverseWeight, quantizeSchwartzValue_ofSpatial_comp,
      (hgi x).self_apply_inverse]
  simp_rw [hl, hr]
  exact integral_inner_quantizeSchwartzValue_adjoint _ _ u v

/-- For the trivial weights `g = 1` and `k = 1` the weighted adjoint symbol is the adjoint
symbol. -/
theorem weightedAdjoint_id :
    weightedAdjoint (g := fun _ ↦ ContinuousLinearMap.id ℂ V)
      (k := fun _ ↦ ContinuousLinearMap.id ℂ W) a ha contDiff_const
      (fun _ ↦ ContinuousLinearEquiv.coe_refl (R₁ := ℂ) (M₁ := V) ▸
        ContinuousLinearMap.isInvertible_equiv) contDiff_const = adjoint a ha := by
  ext1
  funext p
  obtain ⟨y, ξ⟩ := p
  rw [coefficient_weightedAdjoint, coefficient_adjoint]
  simp [ContinuousLinearMap.adjoint_id]

end WeightedAdjoint

/-! ### The weighted adjoint expansion -/

section Expansion

variable (a : Symbol n V W m) (hg : ContDiff ℝ ∞ g) (hgi : ∀ x, (g x).IsInvertible)
  (hk : ContDiff ℝ ∞ k)

/-- The term of order `m - j` of the weighted adjoint expansion:
`g⁻¹ ((-i)^j / j!) ∑_{|w| = j} (∂_x^w ∂_ξ^w (k† a))†`, the term `TauCeti.Symbol.adjointTerm` of
the adjoint expansion of `k† a`, multiplied on the left by `g⁻¹`. -/
def weightedAdjointTerm (j : ℕ) : Symbol n W V (m - j) :=
  inclusion (by simp) ((inverseWeight hg hgi).comp ((weightComp hk a).adjointTerm j))

/-- **The terms of the weighted adjoint expansion** are
`g(x)⁻¹ ((-i)^j / j!) ∑_{|w| = j} (∂_x^w ∂_ξ^w (k† a))(x, ξ)†`, the sum running over the words `w`
of coordinate indices of length `j`. -/
theorem coefficient_weightedAdjointTerm (j : ℕ) (x ξ : CoordinateSpace n) :
    (weightedAdjointTerm a hg hgi hk j).coefficient (x, ξ) = (g x).inverse ∘L
      (((-Complex.I) ^ j / j.factorial) • ∑ w : Fin j → Fin n, ContinuousLinearMap.adjoint
        (mixedDeriv (List.ofFn w) (List.ofFn w)
          (fun p ↦ ContinuousLinearMap.adjoint (k p.1) ∘L a.coefficient p) x ξ)) := by
  rw [weightedAdjointTerm, coefficient_inclusion, coefficient_comp, coefficient_adjointTerm,
    coefficient_weightComp, inverseWeight, coefficient_ofSpatial]

/-- **The leading term of the weighted adjoint expansion** is the adjoint of `a(x, ξ)` for the
two weights, `g(x)⁻¹ a(x, ξ)† k(x)`. -/
@[simp]
theorem coefficient_weightedAdjointTerm_zero (p : CoordinateSpace n × CoordinateSpace n) :
    (weightedAdjointTerm a hg hgi hk 0).coefficient p =
      (g p.1).inverse ∘L ContinuousLinearMap.adjoint (a.coefficient p) ∘L k p.1 := by
  simp [weightedAdjointTerm, inverseWeight, weightComp, ContinuousLinearMap.adjoint_comp]

/-- **The second term of the weighted adjoint expansion**, of order `m - 1`, is
`-i ∑ⱼ g(x)⁻¹ ((∂_{xⱼ} ∂_{ξⱼ} a)(x, ξ)† k(x) + (∂_{ξⱼ} a)(x, ξ)† ∂ⱼ k(x))`. The derivatives of
the weight `k` enter through the second summand. -/
theorem coefficient_weightedAdjointTerm_one (x ξ : CoordinateSpace n) :
    (weightedAdjointTerm a hg hgi hk 1).coefficient (x, ξ) = -Complex.I • ∑ j,
      (g x).inverse ∘L
        (ContinuousLinearMap.adjoint ((spatialDeriv j (frequencyDeriv j a)).coefficient (x, ξ)) ∘L
            k x +
          ContinuousLinearMap.adjoint ((frequencyDeriv j a).coefficient (x, ξ)) ∘L
            coordinateDeriv [j] k x) := by
  -- The frequency derivative of `k† a` is `k† ∂_{ξⱼ} a`, since `k†` does not depend on `ξ`.
  have hfreq (j : Fin n) : (frequencyDeriv j (weightComp hk a)).coefficient =
      (weightComp hk (frequencyDeriv j a)).coefficient := by
    funext ⟨y, η⟩
    simp [weightComp, frequencyDeriv_comp, coefficient_frequencyDeriv,
      coordinateDeriv_const _ (List.cons_ne_nil j [])]
  -- The position derivative of the weight `k†` is `(∂ⱼ k)†`.
  have hdk (j : Fin n) : coordinateDeriv [j] (fun y ↦ ContinuousLinearMap.adjoint (k y)) x =
      ContinuousLinearMap.adjoint (coordinateDeriv [j] k x) := by
    simpa [Function.comp_def, adjointRealCLM_apply] using
      adjointRealCLM.coordinateDeriv_comp_left [j] (hk.of_le (by simp)) x
  have hspat (j : Fin n) :
      (spatialDeriv j (frequencyDeriv j (weightComp hk a))).coefficient (x, ξ) =
        ContinuousLinearMap.adjoint (coordinateDeriv [j] k x) ∘L
            (frequencyDeriv j a).coefficient (x, ξ) +
          ContinuousLinearMap.adjoint (k x) ∘L
            (spatialDeriv j (frequencyDeriv j a)).coefficient (x, ξ) := by
    rw [coefficient_spatialDeriv, hfreq, ← coefficient_spatialDeriv, weightComp, spatialDeriv_comp]
    simp [coefficient_spatialDeriv, hdk]
  have h1 := coefficient_adjointTerm_succ (weightComp hk a) 0 (x, ξ)
  simp only [Nat.cast_zero, zero_add, div_one, coefficient_adjointTerm_zero, hspat] at h1
  rw [weightedAdjointTerm, coefficient_inclusion, coefficient_comp, h1]
  simp [inverseWeight, ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.comp_finsetSum,
    add_comm]

end Expansion

section Remainder

variable (a : Symbol n V W m) (ha : a.HasCompactSpatialSupport) (hg : ContDiff ℝ ∞ g)
  (hgi : ∀ x, (g x).IsInvertible) (hk : ContDiff ℝ ∞ k)

/-- The remainder `a^♯ - ∑_{j < N} weightedAdjointTerm a j` of the weighted adjoint expansion after
`N` terms, a symbol of order `m - N`: the remainder `TauCeti.Symbol.adjointRemainder` of the adjoint
expansion of `k† a`, multiplied on the left by `g⁻¹`. -/
def weightedAdjointRemainder (N : ℕ) : Symbol n W V (m - N) :=
  inclusion (by simp)
    ((inverseWeight hg hgi).comp ((weightComp hk a).adjointRemainder (ha.weightComp hk) N))

@[simp]
theorem coefficient_weightedAdjointRemainder (N : ℕ) :
    (weightedAdjointRemainder a ha hg hgi hk N).coefficient =
      (weightedAdjoint a ha hg hgi hk).coefficient -
        ∑ j ∈ range N, (weightedAdjointTerm a hg hgi hk j).coefficient := by
  ext1 p
  simp [weightedAdjointRemainder, weightedAdjoint, weightedAdjointTerm,
    ContinuousLinearMap.comp_sub, ContinuousLinearMap.comp_finsetSum]

/-- **The weighted adjoint expansion.** For every `N`,
`a^♯ = ∑_{j < N} weightedAdjointTerm a j + weightedAdjointRemainder a N`, where the term of index
`j` has order `m - j` and the remainder has order `m - N`. -/
theorem weightedAdjoint_eq_sum_weightedAdjointTerm_add_weightedAdjointRemainder (N : ℕ) :
    weightedAdjoint a ha hg hgi hk =
      ∑ j ∈ range N, inclusion (sub_le_self _ (Nat.cast_nonneg j))
          (weightedAdjointTerm a hg hgi hk j) +
        inclusion (sub_le_self _ (Nat.cast_nonneg N))
          (weightedAdjointRemainder a ha hg hgi hk N) := by
  ext1
  funext p
  have h := congrArg (fun b ↦ b.coefficient p)
    (adjoint_eq_sum_adjointTerm_add_adjointRemainder (ha.weightComp hk) N)
  simp only [coefficient_add, coefficient_sum, coefficient_inclusion, Pi.add_apply,
    Finset.sum_apply] at h
  simp only [weightedAdjoint, weightedAdjointTerm, weightedAdjointRemainder, coefficient_add,
    coefficient_sum, coefficient_inclusion, coefficient_comp, Pi.add_apply, Finset.sum_apply, h,
    ContinuousLinearMap.comp_add, ContinuousLinearMap.comp_finsetSum]

/-- The weighted adjoint symbol is an asymptotic sum `a^♯ ∼ ∑ⱼ weightedAdjointTerm a j` of the
terms of its expansion, of orders `m - j`. In particular it is determined by the terms modulo
smoothing symbols (`TauCeti.Symbol.IsAsymptoticSum.isAsymptoticSum_iff_isSmoothing_sub`). -/
theorem isAsymptoticSum_weightedAdjoint :
    IsAsymptoticSum (m := fun j : ℕ ↦ m - j) (inclusion (by simp) (weightedAdjoint a ha hg hgi hk))
      (weightedAdjointTerm a hg hgi hk) := by
  refine isAsymptoticSum_iff.2 fun N ↦ ⟨weightedAdjointRemainder a ha hg hgi hk N, ?_⟩
  rw [coefficient_inclusion,
    weightedAdjoint_eq_sum_weightedAdjointTerm_add_weightedAdjointRemainder a ha hg hgi hk N]
  simp

end Remainder

/-! ### Linearity of the weighted adjoint expansion -/

section Linearity

variable (c : ℂ) (a b : Symbol n V W m) (ha : a.HasCompactSpatialSupport)
  (hb : b.HasCompactSpatialSupport) (hg : ContDiff ℝ ∞ g) (hgi : ∀ x, (g x).IsInvertible)
  (hk : ContDiff ℝ ∞ k)

omit [CompleteSpace V] in
private theorem weightComp_add : weightComp hk (a + b) = weightComp hk a + weightComp hk b :=
  comp_add _ a b

omit [CompleteSpace V] in
private theorem weightComp_smul : weightComp hk (c • a) = c • weightComp hk a :=
  comp_smul c _ a

/-- The weighted adjoint symbol is additive: `(a + b)^♯ = a^♯ + b^♯`. -/
@[simp]
theorem weightedAdjoint_add :
    weightedAdjoint (a + b) (ha.add hb) hg hgi hk =
      weightedAdjoint a ha hg hgi hk + weightedAdjoint b hb hg hgi hk := by
  have h : adjoint (weightComp hk (a + b)) ((ha.add hb).weightComp hk) =
      adjoint (weightComp hk a) (ha.weightComp hk) +
        adjoint (weightComp hk b) (hb.weightComp hk) := by
    rw [← adjoint_add]
    congr 1
    exact weightComp_add a b hk
  rw [weightedAdjoint, h, comp_add, map_add, weightedAdjoint, weightedAdjoint]

/-- The weighted adjoint symbol is conjugate-linear: `(c • a)^♯ = conj c • a^♯`. -/
@[simp]
theorem weightedAdjoint_smul :
    weightedAdjoint (c • a) (ha.smul c) hg hgi hk =
      (starRingEnd ℂ) c • weightedAdjoint a ha hg hgi hk := by
  have h : adjoint (weightComp hk (c • a)) ((ha.smul c).weightComp hk) =
      (starRingEnd ℂ) c • adjoint (weightComp hk a) (ha.weightComp hk) := by
    rw [← adjoint_smul]
    congr 1
    exact weightComp_smul c a hk
  rw [weightedAdjoint, h, comp_smul, map_smul, weightedAdjoint]

/-- The weighted adjoint symbol of a difference is the difference of the weighted adjoint
symbols. -/
@[simp]
theorem weightedAdjoint_sub :
    weightedAdjoint (a - b) (ha.sub hb) hg hgi hk =
      weightedAdjoint a ha hg hgi hk - weightedAdjoint b hb hg hgi hk := by
  rw [eq_sub_iff_add_eq, ← weightedAdjoint_add]
  congr 1
  exact sub_add_cancel a b

/-- The terms of the weighted adjoint expansion are additive in the symbol. -/
@[simp]
theorem weightedAdjointTerm_add (j : ℕ) :
    weightedAdjointTerm (a + b) hg hgi hk j =
      weightedAdjointTerm a hg hgi hk j + weightedAdjointTerm b hg hgi hk j := by
  rw [weightedAdjointTerm, weightComp_add, adjointTerm_add, comp_add, map_add, weightedAdjointTerm,
    weightedAdjointTerm]

/-- The terms of the weighted adjoint expansion are conjugate-linear in the symbol. -/
@[simp]
theorem weightedAdjointTerm_smul (j : ℕ) :
    weightedAdjointTerm (c • a) hg hgi hk j =
      (starRingEnd ℂ) c • weightedAdjointTerm a hg hgi hk j := by
  rw [weightedAdjointTerm, weightComp_smul, adjointTerm_smul, comp_smul, map_smul,
    weightedAdjointTerm]

/-- The terms of the weighted adjoint expansion of a difference are the differences of the
terms. -/
@[simp]
theorem weightedAdjointTerm_sub (j : ℕ) :
    weightedAdjointTerm (a - b) hg hgi hk j =
      weightedAdjointTerm a hg hgi hk j - weightedAdjointTerm b hg hgi hk j := by
  rw [eq_sub_iff_add_eq, ← weightedAdjointTerm_add, sub_add_cancel]

/-- The remainders of the weighted adjoint expansion are additive in the symbol. -/
@[simp]
theorem weightedAdjointRemainder_add (N : ℕ) :
    weightedAdjointRemainder (a + b) (ha.add hb) hg hgi hk N =
      weightedAdjointRemainder a ha hg hgi hk N + weightedAdjointRemainder b hb hg hgi hk N := by
  have h : (weightComp hk (a + b)).adjointRemainder ((ha.add hb).weightComp hk) N =
      (weightComp hk a).adjointRemainder (ha.weightComp hk) N +
        (weightComp hk b).adjointRemainder (hb.weightComp hk) N := by
    rw [← adjointRemainder_add]
    congr 1
    exact weightComp_add a b hk
  rw [weightedAdjointRemainder, h, comp_add, map_add, weightedAdjointRemainder,
    weightedAdjointRemainder]

/-- The remainders of the weighted adjoint expansion are conjugate-linear in the symbol. -/
@[simp]
theorem weightedAdjointRemainder_smul (N : ℕ) :
    weightedAdjointRemainder (c • a) (ha.smul c) hg hgi hk N =
      (starRingEnd ℂ) c • weightedAdjointRemainder a ha hg hgi hk N := by
  have h : (weightComp hk (c • a)).adjointRemainder ((ha.smul c).weightComp hk) N =
      (starRingEnd ℂ) c • (weightComp hk a).adjointRemainder (ha.weightComp hk) N := by
    rw [← adjointRemainder_smul]
    congr 1
    exact weightComp_smul c a hk
  rw [weightedAdjointRemainder, h, comp_smul, map_smul, weightedAdjointRemainder]

/-- The remainders of the weighted adjoint expansion of a difference are the differences of the
remainders. -/
@[simp]
theorem weightedAdjointRemainder_sub (N : ℕ) :
    weightedAdjointRemainder (a - b) (ha.sub hb) hg hgi hk N =
      weightedAdjointRemainder a ha hg hgi hk N - weightedAdjointRemainder b hb hg hgi hk N := by
  rw [eq_sub_iff_add_eq, ← weightedAdjointRemainder_add]
  congr 1
  exact sub_add_cancel a b

end Linearity

/-! ### Seminorm estimates and continuity -/

section Continuity

omit [CompleteSpace V] [CompleteSpace W] in
/-- A finite sum `∑ₑ cₑ Gₑ(a)` with nonnegative coefficients, over a list of indices, of functions
`Gₑ` of the symbols `a` vanishing at positions outside `K`, each of which is at most a constant
times finitely many seminorms of `a` on `K`, is itself at most a constant times finitely many
seminorms of `a` on `K`. -/
private theorem exists_listSum_le_sum_seminorm {ι : Type*} (K : Compacts (CoordinateSpace n))
    (l : List ι) (c : ι → ℝ) (hc : ∀ e ∈ l, 0 ≤ c e)
    (G : ι → {a : Symbol n V W m // ∀ x ∉ K, ∀ ξ, a.coefficient (x, ξ) = 0} → ℝ)
    (hG : ∀ e ∈ l, ∃ (s : Finset (List (Fin n) × List (Fin n))) (C : ℝ), 0 ≤ C ∧
      ∀ a, G e a ≤ C * ∑ i ∈ s, Symbol.seminorm K i.1 i.2 a.val) :
    ∃ (s : Finset (List (Fin n) × List (Fin n))) (C : ℝ), 0 ≤ C ∧
      ∀ a, (l.map fun e ↦ c e * G e a).sum ≤ C * ∑ i ∈ s, Symbol.seminorm K i.1 i.2 a.val := by
  classical
  induction l with
  | nil => exact ⟨∅, 0, le_rfl, fun a ↦ by simp⟩
  | cons e l ih =>
    obtain ⟨s, C, hC0, hC⟩ := hG e List.mem_cons_self
    obtain ⟨t, D, hD0, hD⟩ := ih (fun e' he' ↦ hc e' (List.mem_cons_of_mem e he'))
      fun e' he' ↦ hG e' (List.mem_cons_of_mem e he')
    have hce := hc e List.mem_cons_self
    refine ⟨s ∪ t, c e * C + D, by positivity, fun a ↦ ?_⟩
    have hs : ∑ i ∈ s, Symbol.seminorm K i.1 i.2 a.val ≤
        ∑ i ∈ s ∪ t, Symbol.seminorm K i.1 i.2 a.val :=
      Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left fun _ _ _ ↦ apply_nonneg _ _
    have ht : ∑ i ∈ t, Symbol.seminorm K i.1 i.2 a.val ≤
        ∑ i ∈ s ∪ t, Symbol.seminorm K i.1 i.2 a.val :=
      Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_right fun _ _ _ ↦ apply_nonneg _ _
    rw [List.map_cons, List.sum_cons, add_mul, mul_assoc]
    exact add_le_add
      (mul_le_mul_of_nonneg_left ((hC a).trans (mul_le_mul_of_nonneg_left hs hC0)) hce)
      ((hD a).trans (mul_le_mul_of_nonneg_left ht hD0))

omit [CompleteSpace V] [CompleteSpace W] in
/-- Composition on the left with a fixed symbol `b` preserves seminorm estimates: if every
seminorm on `L` of `x(a)` is at most a constant times finitely many seminorms of `a` on `K`, for
the symbols `a` vanishing at positions outside `K`, then so is every seminorm on `L` of
`b ∘ x(a)`, by the Leibniz estimate `TauCeti.Symbol.seminorm_comp_le`. -/
private theorem exists_seminorm_comp_le_sum_seminorm {E F G' : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedAddCommGroup G']
    [NormedSpace ℂ G'] {m₁ m₂ : ℝ} (K L : Compacts (CoordinateSpace n)) (b : Symbol n F G' m₂)
    (x : {a : Symbol n V W m // ∀ x ∉ K, ∀ ξ, a.coefficient (x, ξ) = 0} → Symbol n E F m₁)
    (hx : ∀ γ δ : List (Fin n), ∃ (s : Finset (List (Fin n) × List (Fin n))) (C : ℝ), 0 ≤ C ∧
      ∀ a, Symbol.seminorm L γ δ (x a) ≤ C * ∑ i ∈ s, Symbol.seminorm K i.1 i.2 a.val)
    (α β : List (Fin n)) :
    ∃ (s : Finset (List (Fin n) × List (Fin n))) (C : ℝ), 0 ≤ C ∧
      ∀ a, Symbol.seminorm L α β (b.comp (x a)) ≤ C * ∑ i ∈ s, Symbol.seminorm K i.1 i.2 a.val := by
  obtain ⟨s, C, hC0, hC⟩ := exists_listSum_le_sum_seminorm K β.sublists'.revzip (fun _ ↦ 1)
    (fun _ _ ↦ zero_le_one)
    (fun t a ↦ (α.sublists'.revzip.map fun s ↦
      Symbol.seminorm L s.1 t.1 b * Symbol.seminorm L s.2 t.2 (x a)).sum)
    fun t _ ↦ exists_listSum_le_sum_seminorm K α.sublists'.revzip
      (fun s ↦ Symbol.seminorm L s.1 t.1 b) (fun _ _ ↦ apply_nonneg _ _)
      (fun s a ↦ Symbol.seminorm L s.2 t.2 (x a)) fun s _ ↦ hx s.2 t.2
  exact ⟨s, C, hC0, fun a ↦ (seminorm_comp_le L α β b (x a)).trans (by simpa using hC a)⟩

variable (hg : ContDiff ℝ ∞ g) (hgi : ∀ x, (g x).IsInvertible) (hk : ContDiff ℝ ∞ k)

/-- Seminorm estimates pass from an operation `F` on symbols of order `0 + m` to
`a ↦ g⁻¹ F(k† a)`: if each seminorm on `L` of `F(b)` is at most a constant times finitely many
seminorms of `b` on `K`, for `b` vanishing outside `K`, then the same holds for `g⁻¹ F(k† a)`. -/
private theorem exists_seminorm_inverseWeight_comp_le {m₁ : ℝ} (K : Compacts (CoordinateSpace n))
    (F : (b : Symbol n V W (0 + m)) → b.HasCompactSpatialSupport → Symbol n W V m₁)
    (hF : ∀ (L : Compacts (CoordinateSpace n)) (γ δ : List (Fin n)),
      ∃ (s : Finset (List (Fin n) × List (Fin n))) (C : ℝ), 0 ≤ C ∧
        ∀ (b : Symbol n V W (0 + m)) (hb : b.HasCompactSpatialSupport),
          (∀ x ∉ K, ∀ ξ, b.coefficient (x, ξ) = 0) →
            Symbol.seminorm L γ δ (F b hb) ≤ C * ∑ i ∈ s, Symbol.seminorm K i.1 i.2 b)
    (L : Compacts (CoordinateSpace n)) (α β : List (Fin n)) :
    ∃ (s : Finset (List (Fin n) × List (Fin n))) (C : ℝ), 0 ≤ C ∧
      ∀ (a : Symbol n V W m) (ha : a.HasCompactSpatialSupport),
        (∀ x ∉ K, ∀ ξ, a.coefficient (x, ξ) = 0) →
          Symbol.seminorm L α β
              ((inverseWeight hg hgi).comp (F (weightComp hk a) (ha.weightComp hk))) ≤
            C * ∑ i ∈ s, Symbol.seminorm K i.1 i.2 a := by
  -- `k† a` vanishes outside `K` together with `a`.
  have hvan (a : {a : Symbol n V W m // ∀ x ∉ K, ∀ ξ, a.coefficient (x, ξ) = 0}) :
      ∀ x ∉ K, ∀ ξ, (weightComp hk a.val).coefficient (x, ξ) = 0 := fun x hx ξ ↦ by
    simp [coefficient_weightComp, a.property x hx ξ]
  have hsupp (a : {a : Symbol n V W m // ∀ x ∉ K, ∀ ξ, a.coefficient (x, ξ) = 0}) :
      a.val.HasCompactSpatialSupport :=
    hasCompactSpatialSupport_iff.2 ⟨K, K.isCompact, a.property⟩
  -- The seminorms of `k† a` on `K` are controlled by those of `a`.
  have hw := exists_seminorm_comp_le_sum_seminorm (m := m) K K (ofSpatial _ hk.clm_adjoint)
    (fun a : {a : Symbol n V W m // ∀ x ∉ K, ∀ ξ, a.coefficient (x, ξ) = 0} ↦ a.val)
    fun γ δ ↦ ⟨{(γ, δ)}, 1, zero_le_one, fun a ↦ by simp⟩
  -- Hence so are the seminorms of `F(k† a)`.
  have hFw (γ δ : List (Fin n)) : ∃ (s : Finset (List (Fin n) × List (Fin n))) (C : ℝ), 0 ≤ C ∧
      ∀ a, Symbol.seminorm L γ δ (F (weightComp hk a.val) ((hsupp a).weightComp hk)) ≤
        C * ∑ i ∈ s, Symbol.seminorm K i.1 i.2 a.val := by
    obtain ⟨s, C, hC0, hC⟩ := hF L γ δ
    obtain ⟨t, D, hD0, hD⟩ := exists_listSum_le_sum_seminorm K s.toList (fun _ ↦ C)
      (fun _ _ ↦ hC0) (fun i a ↦ Symbol.seminorm K i.1 i.2 (weightComp hk a.val))
      fun i _ ↦ hw i.1 i.2
    refine ⟨t, D, hD0, fun a ↦ (hC _ _ (hvan a)).trans ?_⟩
    simpa [Finset.mul_sum, Finset.sum_toList] using hD a
  obtain ⟨s, C, hC0, hC⟩ := exists_seminorm_comp_le_sum_seminorm K L (inverseWeight hg hgi)
    (fun a ↦ F (weightComp hk a.val) ((hsupp a).weightComp hk)) hFw α β
  exact ⟨s, C, hC0, fun a _ haK ↦ hC ⟨a, haK⟩⟩

/-- **Seminorm estimate for the remainder of the weighted adjoint expansion.** For smooth weights
`g` and `k`, with `g(x)` invertible, compact sets `K` and `L` of positions, every `N` and words
`α`, `β`, there are finitely many pairs of words and a constant `C` such that the remainder
`R_N^♯(a) = a^♯ - ∑_{j < N} weightedAdjointTerm a j`, a symbol of order `m - N`, satisfies

`p_{L,α,β}(R_N^♯(a)) ≤ C ∑ᵢ p_{K,αᵢ,βᵢ}(a)`

for every symbol `a` of order `m` vanishing at positions outside `K`. With
`TauCeti.Symbol.weightedAdjointRemainder_sub` this bounds `R_N^♯(a) - R_N^♯(b)` by the seminorms
of `a - b`. -/
theorem exists_seminorm_weightedAdjointRemainder_le (K L : Compacts (CoordinateSpace n)) (N : ℕ)
    (α β : List (Fin n)) :
    ∃ (s : Finset (List (Fin n) × List (Fin n))) (C : ℝ), 0 ≤ C ∧
      ∀ (a : Symbol n V W m) (ha : a.HasCompactSpatialSupport),
        (∀ x ∉ K, ∀ ξ, a.coefficient (x, ξ) = 0) →
          Symbol.seminorm L α β (weightedAdjointRemainder a ha hg hgi hk N) ≤
            C * ∑ i ∈ s, Symbol.seminorm K i.1 i.2 a := by
  obtain ⟨s, C, hC0, hC⟩ := exists_seminorm_inverseWeight_comp_le hg hgi hk K
    (fun b hb ↦ b.adjointRemainder hb N)
    (fun L γ δ ↦ exists_seminorm_adjointRemainder_le K L N γ δ) L α β
  exact ⟨s, C, hC0, fun a ha haK ↦ (seminorm_inclusion_le _ L α β _).trans (hC a ha haK)⟩

/-- **Seminorm estimate for the weighted adjoint symbol.** For smooth weights `g` and `k`, with
`g(x)` invertible, compact sets `K` and `L` of positions and words `α`, `β`, there are finitely
many pairs of words and a constant `C` such that

`p_{L,α,β}(a^♯) ≤ C ∑ᵢ p_{K,αᵢ,βᵢ}(a)`

for every symbol `a` of order `m` vanishing at positions outside `K`. -/
theorem exists_seminorm_weightedAdjoint_le (K L : Compacts (CoordinateSpace n))
    (α β : List (Fin n)) :
    ∃ (s : Finset (List (Fin n) × List (Fin n))) (C : ℝ), 0 ≤ C ∧
      ∀ (a : Symbol n V W m) (ha : a.HasCompactSpatialSupport),
        (∀ x ∉ K, ∀ ξ, a.coefficient (x, ξ) = 0) →
          Symbol.seminorm L α β (weightedAdjoint a ha hg hgi hk) ≤
            C * ∑ i ∈ s, Symbol.seminorm K i.1 i.2 a := by
  obtain ⟨s, C, hC0, hC⟩ := exists_seminorm_inverseWeight_comp_le hg hgi hk K adjoint
    (fun L γ δ ↦ exists_seminorm_adjoint_le K L γ δ) L α β
  exact ⟨s, C, hC0, fun a ha haK ↦ (seminorm_inclusion_le _ L α β _).trans (hC a ha haK)⟩

/-- **Continuity of the weighted adjoint symbol.** If `t ↦ a t` is a continuous family of symbols
of order `m`, all vanishing at positions outside one compact set `K`, then `t ↦ (a t)^♯` is a
continuous family of symbols of order `m`, for fixed smooth weights `g` and `k` with `g(x)`
invertible. -/
theorem _root_.Continuous.symbol_weightedAdjoint {X : Type*} [TopologicalSpace X]
    {a : X → Symbol n V W m} (ha : Continuous a) {K : Set (CoordinateSpace n)} (hK : IsCompact K)
    (haK : ∀ t, ∀ x ∉ K, ∀ ξ, (a t).coefficient (x, ξ) = 0) :
    Continuous fun t ↦
      weightedAdjoint (a t) (hasCompactSpatialSupport_iff.2 ⟨K, hK, haK t⟩) hg hgi hk := by
  have hw : Continuous fun t ↦ weightComp hk (a t) := continuous_const.symbol_comp ha
  exact (continuous_inclusion _).comp (continuous_const.symbol_comp
    (hw.symbol_adjoint hK fun t x hx ξ ↦ by simp [coefficient_weightComp, haK t x hx ξ]))

/-- **Continuity of the remainders of the weighted adjoint expansion.** If `t ↦ a t` is a
continuous family of symbols of order `m`, all vanishing at positions outside one compact set `K`,
then for every `N` the remainders `t ↦ (a t)^♯ - ∑_{j < N} weightedAdjointTerm (a t) j` form a
continuous family of symbols of order `m - N`, for fixed smooth weights `g` and `k` with `g(x)`
invertible. -/
theorem _root_.Continuous.symbol_weightedAdjointRemainder {X : Type*} [TopologicalSpace X]
    {a : X → Symbol n V W m} (ha : Continuous a) {K : Set (CoordinateSpace n)} (hK : IsCompact K)
    (haK : ∀ t, ∀ x ∉ K, ∀ ξ, (a t).coefficient (x, ξ) = 0) (N : ℕ) :
    Continuous fun t ↦ weightedAdjointRemainder (a t)
      (hasCompactSpatialSupport_iff.2 ⟨K, hK, haK t⟩) hg hgi hk N := by
  have hw : Continuous fun t ↦ weightComp hk (a t) := continuous_const.symbol_comp ha
  exact (continuous_inclusion _).comp (continuous_const.symbol_comp
    (hw.symbol_adjointRemainder hK (fun t x hx ξ ↦ by simp [coefficient_weightComp, haK t x hx ξ])
      N))

end Continuity

end Symbol

/-! ### The weighted adjoint of a classical symbol -/

namespace ClassicalSymbol

variable {n : ℕ} {m : ℝ} {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [CompleteSpace V] [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W]
  {g : CoordinateSpace n → V →L[ℂ] V} {k : CoordinateSpace n → W →L[ℂ] W}
  (a : ClassicalSymbol n V W m) (ha : a.toSymbol.HasCompactSpatialSupport) (hg : ContDiff ℝ ∞ g)
  (hgi : ∀ x, (g x).IsInvertible) (hk : ContDiff ℝ ∞ k)

/-- **The weighted adjoint of a classical symbol is classical.** For a classical symbol `a` of
order `m` with compact spatial support and smooth weights `g` and `k`, with `g(x)` invertible, the
weighted adjoint symbol `a^♯ = g⁻¹ (k† a)*` (`TauCeti.Symbol.weightedAdjoint`) is a classical symbol
of order `m` (`TauCeti.ClassicalSymbol.toSymbol_weightedAdjoint`), with principal symbol
`g(x)⁻¹ a_m(x, ξ)† k(x)` (`TauCeti.ClassicalSymbol.coefficient_principal_weightedAdjoint`). -/
def weightedAdjoint : ClassicalSymbol n W V m :=
  inclusion 0 (by simp) ((ofSpatial _ (hg.clm_inverse hgi)).comp
    (adjoint ((ofSpatial _ hk.clm_adjoint).comp a)
      (by rw [toSymbol_comp]; exact ha.comp_left _)))

@[simp]
theorem toSymbol_weightedAdjoint :
    (a.weightedAdjoint ha hg hgi hk).toSymbol = a.toSymbol.weightedAdjoint ha hg hgi hk := by
  ext1
  funext ⟨y, ξ⟩
  simp [weightedAdjoint, Symbol.coefficient_weightedAdjoint, Symbol.coefficient_adjoint]

/-- **The principal symbol of the weighted adjoint** is the adjoint of the principal symbol for
the two weights: `σ(a^♯)(x, ξ) = g(x)⁻¹ σ(a)(x, ξ)† k(x)`. -/
@[simp]
theorem coefficient_principal_weightedAdjoint (p : CoordinateSpace n × CoordinateSpace n) :
    (a.weightedAdjoint ha hg hgi hk).principal.coefficient p =
      (g p.1).inverse ∘L ContinuousLinearMap.adjoint (a.principal.coefficient p) ∘L k p.1 := by
  obtain ⟨x, ξ⟩ := p
  rcases eq_or_ne ξ 0 with rfl | hξ
  · simp [HomogeneousSymbol.zero_covector]
  rw [weightedAdjoint, principal_def, term_inclusion_zero]
  simp [← coefficient_principal, coefficient_principal_ofSpatial _ _ hξ,
    ContinuousLinearMap.adjoint_comp]

/-- **The weighted adjoint of an elliptic symbol is elliptic**, and conversely, when the weight
`k(x)` is invertible for every `x`. -/
theorem isElliptic_weightedAdjoint_iff (hki : ∀ x, (k x).IsInvertible) :
    (a.weightedAdjoint ha hg hgi hk).IsElliptic ↔ a.IsElliptic := by
  simp only [isElliptic_def, HomogeneousSymbol.isElliptic_iff,
    coefficient_principal_weightedAdjoint]
  refine forall_congr' fun x ↦ forall_congr' fun ξ ↦ imp_congr_right fun _ ↦ ?_
  obtain ⟨G, hG⟩ := (hgi x).inverse
  obtain ⟨K, hK⟩ := hki x
  rw [← hG, ← hK, ContinuousLinearMap.isInvertible_equiv_comp,
    ContinuousLinearMap.isInvertible_comp_equiv, ContinuousLinearMap.isInvertible_adjoint_iff]

end ClassicalSymbol

end TauCeti
