/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Amplitude.Comp
public import TauCeti.Analysis.Pseudodifferential.Amplitude.Expansion
public import TauCeti.Analysis.Pseudodifferential.Symbol.Classical.Basic
import TauCeti.Analysis.Normed.Operator.Basic

/-!
# Classical amplitudes and their left symbols

A *classical amplitude* of order `m` on `ℝⁿ` (`TauCeti.ClassicalAmplitude n V W m`) is an amplitude
`c(x, y, ξ)` with an expansion `c ∼ ∑ⱼ χ(ξ) c_{m-j}(x, y, ξ)` into terms homogeneous of degree
`m - j` in the frequency: for every `N` the remainder `c - ∑_{j<N} χ(ξ) c_{m-j}` is an amplitude of
order `m - N`. The terms are homogeneous symbols whose position is the pair `(x, y)`, and their
cut-off terms `χ(ξ) c_{m-j}(x, y, ξ)` are the amplitudes
`TauCeti.HomogeneousSymbol.cutoffAmplitude`.

The left symbol of an amplitude with proper input support has the asymptotic expansion
`∑ₖ ((-i)^k / k!) ∑_{|w| = k} (∂_y^w ∂_ξ^w c)(x, x, ξ)`
(`TauCeti.Amplitude.isAsymptoticSum_leftSymbol`). This file shows that **the left symbol of a
classical amplitude is a classical symbol** (`TauCeti.ClassicalAmplitude.leftSymbol`). Expanding
each term of the left symbol expansion into the homogeneous terms of `c`, the term of degree
`m - j` of the left symbol is

`∑_{k ≤ j} ((-i)^k / k!) ∑_{|w| = k} (∂_y^w ∂_ξ^w c_{m-j+k})(x, x, ξ)`

(`TauCeti.HomogeneousSymbol.leftTerms`), and its principal symbol is the restriction `c_m(x, x, ξ)`
of the leading term to the diagonal (`TauCeti.ClassicalAmplitude.principal_leftSymbol`).

The amplitudes `g(x, y) • b(κ x, M(x, y) ξ)` that express an operator in new coordinates are
classical when `b` is (`TauCeti.ClassicalSymbol.compAmplitude`), with the terms
`g(x, y) • b_{m-j}(κ x, M(x, y) ξ)`; so the left symbol of such an amplitude is classical, with
principal symbol `g(x, x) • σ(b)(κ x, M(x, x) ξ)`
(`TauCeti.ClassicalSymbol.coefficient_principal_leftSymbol_compAmplitude`). This is how classical
symbols are seen to be invariant under changes of coordinates.

## Main declarations

* `TauCeti.HomogeneousSymbol.cutoffAmplitude`: the cut-off term `χ(ξ) a(x, y, ξ)` of a homogeneous
  term, with its derivatives `TauCeti.HomogeneousSymbol.spatialDerivSnd_cutoffAmplitude` and
  `TauCeti.HomogeneousSymbol.coefficient_frequencyDeriv_cutoffAmplitude`.
* `TauCeti.HomogeneousSymbol.leftTerm` and `TauCeti.HomogeneousSymbol.leftTerms`: the homogeneous
  terms of the left symbol expansion.
* `TauCeti.ClassicalAmplitude`: classical amplitudes, with the remainders
  `TauCeti.ClassicalAmplitude.remainder` for every cutoff and the uniqueness of the terms
  (`TauCeti.ClassicalAmplitude.ext`); the restriction `TauCeti.ClassicalAmplitude.diagonal` to the
  diagonal and the derivatives `TauCeti.ClassicalAmplitude.spatialDerivSnd` and
  `TauCeti.ClassicalAmplitude.frequencyDeriv` are again classical.
* `TauCeti.ClassicalAmplitude.leftTerm`: each term of the left symbol expansion is a classical
  symbol.
* `TauCeti.ClassicalAmplitude.leftSymbol`: **the left symbol of a classical amplitude is
  classical**, with homogeneous terms `leftTerms c.term`.
* `TauCeti.ClassicalSymbol.compAmplitude`: the classical amplitude `g(x, y) • b(κ x, M(x, y) ξ)` of
  a classical symbol `b`.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, Theorem 18.1.17 and
  its proof, and Definition 18.1.5.
* M. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI* (2008), Lecture I, (1.21)–(1.28)
  and §8.
-/

public section

noncomputable section

open Finset Filter Topology
open scoped ContDiff

namespace TauCeti

variable {n : ℕ} {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W]
  [NormedSpace ℂ W] {m : ℝ}

namespace HomogeneousSymbol

variable (χ : FrequencyCutoff (CoordinateSpace n))

/-- The cut-off term `χ(ξ) a(x, y, ξ)` of a homogeneous term of degree `m` in the frequency,
smooth in the pair of positions `(x, y)`, satisfies the amplitude estimates of order `m`. -/
private theorem exists_bound_iteratedFDerivAlong_smul_coefficient
    (a : HomogeneousSymbol (CoordinateSpace n × CoordinateSpace n) (CoordinateSpace n) V W m)
    {K : Set (CoordinateSpace n × CoordinateSpace n)} (hK : IsCompact K) (α γ β : List (Fin n)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x y, (x, y) ∈ K → ∀ ξ,
      ‖iteratedFDerivAlong ℝ (amplitudeDirections α γ β)
          (fun p : CoordinateSpace n × CoordinateSpace n × CoordinateSpace n ↦
            χ p.2.2 • a.coefficient ((p.1, p.2.1), p.2.2)) (x, y, ξ)‖ ≤
        C * (1 + ‖ξ‖ ^ 2) ^ ((m - β.length) / 2) := by
  set L := (ContinuousLinearEquiv.prodAssoc ℝ (CoordinateSpace n) (CoordinateSpace n)
    (CoordinateSpace n)).symm
  -- The position directions, read in the pair of positions.
  set lu : List (CoordinateSpace n × CoordinateSpace n) :=
    α.map (fun j ↦ (EuclideanSpace.single j 1, 0)) ++ γ.map (fun j ↦ (0, EuclideanSpace.single j 1))
  have hF := a.contDiff_smul_coefficient χ
  obtain ⟨C, hC0, hC⟩ := a.exists_norm_iteratedFDeriv_smul_coefficient_le χ hK lu.length β.length
  refine ⟨C, hC0, fun x y hxy ξ ↦ ?_⟩
  have hdirs : (amplitudeDirections α γ β).map (L : _ →L[ℝ] _) = List.ofFn
      (Fin.append (fun i ↦ (lu.get i, (0 : CoordinateSpace n)))
        fun i ↦
          ((0 : CoordinateSpace n × CoordinateSpace n), EuclideanSpace.single (β.get i) 1)) := by
    rw [List.ofFn_fin_append, List.ofFn_comp' lu.get (fun v ↦ (v, (0 : CoordinateSpace n))),
      List.ofFn_get, List.ofFn_comp' β.get
        (fun j ↦ ((0 : CoordinateSpace n × CoordinateSpace n), EuclideanSpace.single j 1)),
      List.ofFn_get]
    simp only [amplitudeDirections_def, lu, L, List.map_append, List.map_map, List.append_assoc,
      Function.comp_def, Prod.zero_eq_mk, ContinuousLinearEquiv.coe_coe,
      ContinuousLinearEquiv.prodAssoc_symm_apply]
  have hcomp := iteratedFDerivAlong_comp_of_hasFDerivAt (φ := L) (L := (L : _ →L[ℝ] _))
    (fun z ↦ L.hasFDerivAt) hF (amplitudeDirections α γ β) (by simp) (x, y, ξ)
  have hnorm : ∀ v ∈ lu, ‖v‖ = 1 := by
    simp only [lu, List.mem_append, List.mem_map]
    rintro v (⟨j, -, rfl⟩ | ⟨j, -, rfl⟩) <;> simp [Prod.norm_def]
  have h := hC (x, y) hxy ξ (fun i ↦ lu.get i) fun i ↦ EuclideanSpace.single (β.get i) 1
  rw [Finset.prod_eq_one fun i _ ↦ hnorm _ (List.get_mem _ _),
    Finset.prod_eq_one fun i _ ↦ by simp, mul_one, mul_one] at h
  -- The coefficient is the cut-off term composed with the reassociation `L`.
  have e : (fun p : CoordinateSpace n × CoordinateSpace n × CoordinateSpace n ↦
      χ p.2.2 • a.coefficient ((p.1, p.2.1), p.2.2)) = fun z ↦ χ (L z).2 • a.coefficient (L z) := by
    funext ⟨_, _, _⟩
    simp [L]
  rw [e, hcomp, hdirs, iteratedFDerivAlong_ofFn_eq_iteratedFDeriv
    (hF.of_le (by exact_mod_cast le_top))]
  exact h

/-- The cut-off term `χ(ξ) a(x, y, ξ)` of a homogeneous term `a` of degree `m` in the frequency,
whose position is the pair `(x, y)` of an output and an input position, as an amplitude of order
`m`. The cutoff removes the singularity of `a` at `ξ = 0` and leaves `a` unchanged at frequencies
of norm at least `2`. -/
def cutoffAmplitude (χ : FrequencyCutoff (CoordinateSpace n))
    (a : HomogeneousSymbol (CoordinateSpace n × CoordinateSpace n) (CoordinateSpace n) V W m) :
    Amplitude n V W m where
  coefficient p := χ p.2.2 • a.coefficient ((p.1, p.2.1), p.2.2)
  contDiff_coefficient := (a.contDiff_smul_coefficient χ).comp
    ((contDiff_fst.prodMk (contDiff_fst.comp contDiff_snd)).prodMk (contDiff_snd.comp contDiff_snd))
  exists_bound _ hK α γ β := exists_bound_iteratedFDerivAlong_smul_coefficient χ a hK α γ β

@[simp]
theorem coefficient_cutoffAmplitude
    (a : HomogeneousSymbol (CoordinateSpace n × CoordinateSpace n) (CoordinateSpace n) V W m)
    (p : CoordinateSpace n × CoordinateSpace n × CoordinateSpace n) :
    (cutoffAmplitude χ a).coefficient p = χ p.2.2 • a.coefficient ((p.1, p.2.1), p.2.2) :=
  (rfl)

/-- At frequencies of norm at least `2` the cut-off term is the homogeneous term itself. -/
theorem coefficient_cutoffAmplitude_of_two_le_norm
    (a : HomogeneousSymbol (CoordinateSpace n × CoordinateSpace n) (CoordinateSpace n) V W m)
    {x y ξ : CoordinateSpace n} (hξ : 2 ≤ ‖ξ‖) :
    (cutoffAmplitude χ a).coefficient (x, y, ξ) = a.coefficient ((x, y), ξ) := by
  simp [χ.apply_eq_one_of_two_le_norm hξ]

/-- The derivative of the cut-off term at a nonzero frequency, by the product rule. -/
private theorem fderiv_coefficient_cutoffAmplitude
    (a : HomogeneousSymbol (CoordinateSpace n × CoordinateSpace n) (CoordinateSpace n) V W m)
    {p : CoordinateSpace n × CoordinateSpace n × CoordinateSpace n} (hp : p.2.2 ≠ 0)
    (v : CoordinateSpace n × CoordinateSpace n × CoordinateSpace n) :
    fderiv ℝ (cutoffAmplitude χ a).coefficient p v =
      χ p.2.2 • fderiv ℝ a.coefficient ((p.1, p.2.1), p.2.2) ((v.1, v.2.1), v.2.2) +
        fderiv ℝ χ p.2.2 v.2.2 • a.coefficient ((p.1, p.2.1), p.2.2) := by
  set L := (ContinuousLinearEquiv.prodAssoc ℝ (CoordinateSpace n) (CoordinateSpace n)
    (CoordinateSpace n)).symm
  have hχ : HasFDerivAt (fun q : (CoordinateSpace n × CoordinateSpace n) × CoordinateSpace n ↦
      χ q.2) ((fderiv ℝ χ p.2.2).comp (ContinuousLinearMap.snd ℝ _ _)) (L p) :=
    (((χ.contDiff (n := 1)).differentiable one_ne_zero (L p).2).hasFDerivAt).comp (L p)
      hasFDerivAt_snd
  have ha := (a.differentiableAt_coefficient (p := L p) hp).hasFDerivAt
  have h := (hχ.smul ha).comp p L.hasFDerivAt
  have e : (cutoffAmplitude χ a).coefficient =
      ((fun q : (CoordinateSpace n × CoordinateSpace n) × CoordinateSpace n ↦ χ q.2) •
        a.coefficient) ∘ L := by
    funext ⟨_, _, _⟩
    simp [L]
  rw [e, h.fderiv]
  obtain ⟨_, _, _⟩ := p
  obtain ⟨_, _, _⟩ := v
  simp [L]

/-- The input-position derivative of the cut-off term is the cut-off term of the input-position
derivative: the cutoff does not depend on the positions. -/
@[simp]
theorem spatialDerivSnd_cutoffAmplitude (j : Fin n)
    (a : HomogeneousSymbol (CoordinateSpace n × CoordinateSpace n) (CoordinateSpace n) V W m) :
    Amplitude.spatialDerivSnd j (cutoffAmplitude χ a) =
      cutoffAmplitude χ (a.spatialDeriv (0, EuclideanSpace.single j 1)) := by
  ext1
  funext ⟨x, y, ξ⟩
  rw [Amplitude.coefficient_spatialDerivSnd, coefficient_cutoffAmplitude]
  rcases eq_or_ne ξ 0 with rfl | hξ
  · -- Near the zero frequency the cut-off term vanishes identically.
    have hzero : (cutoffAmplitude χ a).coefficient =ᶠ[𝓝 (x, y, 0)] 0 := by
      filter_upwards [(isOpen_lt (continuous_norm.comp (continuous_snd.comp continuous_snd))
        continuous_const).mem_nhds (by simp : ‖((x, y, 0) : CoordinateSpace n × CoordinateSpace n ×
          CoordinateSpace n).2.2‖ < 1)] with q hq
      simp only [Function.comp_apply] at hq
      simp [χ.apply_eq_zero_of_norm_le_one hq.le]
    simp [hzero.fderiv_eq, χ.apply_zero]
  · rw [fderiv_coefficient_cutoffAmplitude χ a hξ, coefficient_spatialDeriv_eq_fderiv]
    simp

/-- A frequency derivative of the cut-off term agrees with the cut-off term of the frequency
derivative at all frequencies of norm greater than `2`, where the cutoff is identically `1`. -/
theorem coefficient_frequencyDeriv_cutoffAmplitude (j : Fin n)
    (a : HomogeneousSymbol (CoordinateSpace n × CoordinateSpace n) (CoordinateSpace n) V W m)
    {x y ξ : CoordinateSpace n} (hξ : 2 < ‖ξ‖) :
    (Amplitude.frequencyDeriv j (cutoffAmplitude χ a)).coefficient (x, y, ξ) =
      (cutoffAmplitude χ (a.frequencyDeriv (EuclideanSpace.single j 1))).coefficient (x, y, ξ) := by
  have hξ0 : ξ ≠ 0 := norm_pos_iff.1 (by linarith)
  rw [Amplitude.coefficient_frequencyDeriv, fderiv_coefficient_cutoffAmplitude χ a hξ0,
    coefficient_cutoffAmplitude, coefficient_frequencyDeriv_eq_fderiv _ _ hξ0,
    (χ.eventuallyEq_one_of_two_lt_norm hξ).fderiv_eq]
  simp [Prod.mk_zero_zero]

/-! ### The homogeneous terms of the left symbol -/

section LeftTerm

/-- The term of degree `m - k` of the left symbol expansion of a homogeneous term `a(x, y, ξ)` of
degree `m`: `((-i)^k / k!) ∑_{|w| = k} (∂_y^w ∂_ξ^w a)(x, x, ξ)`, a homogeneous symbol of degree
`m - k` in `(x, ξ)`. It is defined by the recursion of `TauCeti.Amplitude.leftTerm`:
`a.leftTerm 0` is the restriction `a(x, x, ξ)` of `a` to the diagonal and
`a.leftTerm (k + 1) = (-i / (k + 1)) ∑ⱼ (∂_{y_j} ∂_{ξ_j} a).leftTerm k`. -/
def leftTerm : {m : ℝ} →
    HomogeneousSymbol (CoordinateSpace n × CoordinateSpace n) (CoordinateSpace n) V W m →
    (k : ℕ) → HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W (m - k)
  | _, a, 0 => (a.compPosition (fun x ↦ (x, x)) (contDiff_id.prodMk contDiff_id)).castDegree
      (by simp)
  | _, a, k + 1 => (-Complex.I / (k + 1 : ℂ)) • ∑ j : Fin n,
      (leftTerm ((a.frequencyDeriv (EuclideanSpace.single j 1)).spatialDeriv
        (0, EuclideanSpace.single j 1)) k).castDegree (by push_cast; ring)

variable (a : HomogeneousSymbol (CoordinateSpace n × CoordinateSpace n) (CoordinateSpace n) V W m)

theorem leftTerm_zero :
    a.leftTerm 0 =
      (a.compPosition (fun x ↦ (x, x)) (contDiff_id.prodMk contDiff_id)).castDegree (by simp) :=
  (rfl)

theorem leftTerm_succ (k : ℕ) :
    a.leftTerm (k + 1) = (-Complex.I / (k + 1 : ℂ)) • ∑ j : Fin n,
      (((a.frequencyDeriv (EuclideanSpace.single j 1)).spatialDeriv
        (0, EuclideanSpace.single j 1)).leftTerm k).castDegree (by push_cast; ring) :=
  (rfl)

@[simp]
theorem coefficient_leftTerm_zero (x ξ : CoordinateSpace n) :
    (a.leftTerm 0).coefficient (x, ξ) = a.coefficient ((x, x), ξ) := by
  simp [leftTerm_zero]

theorem coefficient_leftTerm_succ (k : ℕ) (p : CoordinateSpace n × CoordinateSpace n) :
    (a.leftTerm (k + 1)).coefficient p = (-Complex.I / (k + 1 : ℂ)) • ∑ j : Fin n,
      (((a.frequencyDeriv (EuclideanSpace.single j 1)).spatialDeriv
        (0, EuclideanSpace.single j 1)).leftTerm k).coefficient p := by
  simp [leftTerm_succ, coefficient_smul, coefficient_sum]

/-- The homogeneous terms `cⱼ = ∑_{k ≤ j} (q_{j-k}).leftTerm k` of the left symbol of an amplitude
with homogeneous terms `qᵢ` of degree `m - i`; the term `cⱼ` has degree `m - j`. -/
def leftTerms
    (q : (i : ℕ) →
      HomogeneousSymbol (CoordinateSpace n × CoordinateSpace n) (CoordinateSpace n) V W (m - i))
    (j : ℕ) : HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W (m - j) :=
  ∑ k ∈ range (j + 1),
    if h : k ≤ j then ((q (j - k)).leftTerm k).castDegree (by rw [Nat.cast_sub h]; ring) else 0

/-- The coefficient of `cⱼ` is `∑_{k ≤ j} (q_{j-k}).leftTerm k`. -/
theorem coefficient_leftTerms
    (q : (i : ℕ) →
      HomogeneousSymbol (CoordinateSpace n × CoordinateSpace n) (CoordinateSpace n) V W (m - i))
    (j : ℕ) (p : CoordinateSpace n × CoordinateSpace n) :
    (leftTerms q j).coefficient p =
      ∑ k ∈ range (j + 1), ((q (j - k)).leftTerm k).coefficient p := by
  simp only [leftTerms, coefficient_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun k hk ↦ ?_
  simp [Nat.lt_succ_iff.1 (mem_range.1 hk)]

/-- The leading term of the left symbol is the restriction of the leading homogeneous term to the
diagonal. -/
@[simp]
theorem coefficient_leftTerms_zero
    (q : (i : ℕ) →
      HomogeneousSymbol (CoordinateSpace n × CoordinateSpace n) (CoordinateSpace n) V W (m - i))
    (x ξ : CoordinateSpace n) :
    (leftTerms q 0).coefficient (x, ξ) = (q 0).coefficient ((x, x), ξ) := by
  simp [coefficient_leftTerms]

end LeftTerm

/-- Transport along an equality of degrees commutes with the left terms. -/
@[simp]
theorem leftTerm_castDegree {m' : ℝ} (h : m = m')
    (a : HomogeneousSymbol (CoordinateSpace n × CoordinateSpace n) (CoordinateSpace n) V W m)
    (k : ℕ) : (a.castDegree h).leftTerm k = (a.leftTerm k).castDegree (by rw [h]) := by
  subst h
  simp only [castDegree_rfl]

end HomogeneousSymbol

open HomogeneousSymbol

variable (n V W m) in
/-- A **classical amplitude** of order `m` on `ℝⁿ`: an amplitude `c(x, y, ξ)` of order `m` together
with terms `c_{m-j}(x, y, ξ)`, smooth in the pair of positions `(x, y)` and homogeneous of degree
`m - j` in the frequency, such that for some frequency cutoff `χ` and every `N` the remainder
`c - ∑_{j<N} χ(ξ) c_{m-j}` is an amplitude of order `m - N`. The expansion then holds for every
cutoff (`TauCeti.ClassicalAmplitude.exists_remainder`), and the terms are determined by the
amplitude (`TauCeti.ClassicalAmplitude.ext`). -/
structure ClassicalAmplitude where
  /-- The full amplitude. -/
  toAmplitude : Amplitude n V W m
  /-- The term `c_{m-j}` of degree `m - j`, homogeneous in the frequency. -/
  term : (j : ℕ) →
    HomogeneousSymbol (CoordinateSpace n × CoordinateSpace n) (CoordinateSpace n) V W (m - j)
  /-- For some frequency cutoff `χ`, every remainder `c - ∑_{j<N} χ(ξ) c_{m-j}` has order `m - N`;
  use `TauCeti.ClassicalAmplitude.exists_remainder` for an arbitrary cutoff. -/
  exists_remainder' : ∃ χ : FrequencyCutoff (CoordinateSpace n), ∀ N : ℕ,
    ∃ r : Amplitude n V W (m - N), ∀ p,
      r.coefficient p =
        toAmplitude.coefficient p - ∑ j ∈ range N, (cutoffAmplitude χ (term j)).coefficient p

namespace ClassicalAmplitude

section Remainder

variable (c : ClassicalAmplitude n V W m) (χ : FrequencyCutoff (CoordinateSpace n))

/-- The truncated remainder `c - ∑_{j<N} χ(ξ) c_{m-j}` is smooth. -/
private theorem contDiff_sub_sum (N : ℕ) :
    ContDiff ℝ ∞ fun p ↦
      c.toAmplitude.coefficient p - ∑ j ∈ range N, (cutoffAmplitude χ (c.term j)).coefficient p :=
  c.toAmplitude.contDiff_coefficient.sub
    (ContDiff.sum fun j _ ↦ (cutoffAmplitude χ (c.term j)).contDiff_coefficient)

/-- **Independence of the cutoff.** For every frequency cutoff `χ` and every `N`, the remainder
`c - ∑_{j<N} χ(ξ) c_{m-j}` of a classical amplitude is an amplitude of order `m - N`. -/
theorem exists_remainder (N : ℕ) :
    ∃ r : Amplitude n V W (m - N), ∀ p, r.coefficient p = c.toAmplitude.coefficient p -
      ∑ j ∈ range N, (cutoffAmplitude χ (c.term j)).coefficient p := by
  obtain ⟨χ₀, h₀⟩ := c.exists_remainder'
  obtain ⟨r₀, hr₀⟩ := h₀ N
  -- The truncated expansions for `χ₀` and `χ` agree at all frequencies of norm at least `2`.
  obtain ⟨r, hr⟩ := Amplitude.exists_coefficient_eq_of_forall_le_norm (contDiff_sub_sum c χ N) r₀
    le_rfl 2 fun x y ξ hξ ↦ by
      simp [hr₀, χ.apply_eq_one_of_two_le_norm hξ, χ₀.apply_eq_one_of_two_le_norm hξ]
  exact ⟨r, fun p ↦ congrFun hr p⟩

/-- The remainder `c - ∑_{j<N} χ(ξ) c_{m-j}` of a classical amplitude after `N` terms, an
amplitude of order `m - N`. -/
def remainder (N : ℕ) : Amplitude n V W (m - N) :=
  (c.exists_remainder χ N).choose

@[simp]
theorem coefficient_remainder (N : ℕ)
    (p : CoordinateSpace n × CoordinateSpace n × CoordinateSpace n) :
    (c.remainder χ N).coefficient p =
      c.toAmplitude.coefficient p - ∑ j ∈ range N, (cutoffAmplitude χ (c.term j)).coefficient p :=
  (c.exists_remainder χ N).choose_spec p

/-- A derivative of the remainder after `N` terms is the derivative of the amplitude minus the
derivatives of the first `N` cut-off terms. -/
private theorem iteratedFDerivAlong_coefficient_remainder (N : ℕ)
    (d : CoordinateSpace n × CoordinateSpace n × CoordinateSpace n)
    (p : CoordinateSpace n × CoordinateSpace n × CoordinateSpace n) :
    iteratedFDerivAlong ℝ [d] (c.remainder χ N).coefficient p =
      iteratedFDerivAlong ℝ [d] c.toAmplitude.coefficient p - ∑ j ∈ range N,
        iteratedFDerivAlong ℝ [d] (cutoffAmplitude χ (c.term j)).coefficient p := by
  have e : (c.remainder χ N).coefficient = c.toAmplitude.coefficient -
      ∑ j ∈ range N, (cutoffAmplitude χ (c.term j)).coefficient :=
    funext fun q ↦ by simp
  have hs : ContDiff ℝ ∞ (∑ j ∈ range N, (cutoffAmplitude χ (c.term j)).coefficient) := by
    simpa only [Finset.sum_fn] using
      ContDiff.sum fun j _ ↦ (cutoffAmplitude χ (c.term j)).contDiff_coefficient
  rw [e, iteratedFDerivAlong_sub c.toAmplitude.contDiff_coefficient hs _ (by simp),
    iteratedFDerivAlong_sum _ (fun j _ ↦ (cutoffAmplitude χ (c.term j)).contDiff_coefficient) _
      (by simp)]
  simp

end Remainder

section Uniqueness

/-- **Uniqueness of the homogeneous terms.** Two classical amplitudes with the same full amplitude
have the same homogeneous terms. -/
theorem term_eq_of_toAmplitude_eq {a b : ClassicalAmplitude n V W m}
    (h : a.toAmplitude = b.toAmplitude) (j : ℕ) : a.term j = b.term j := by
  obtain ⟨χ, -⟩ := a.exists_remainder'
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    -- Given the equality of the earlier terms, at large frequencies `b_{m-j} - a_{m-j}` is the
    -- difference of the remainders after `j + 1` terms, of order `m - (j + 1) < m - j`.
    refine (sub_eq_zero.1 (ext_of_ne_zero fun q ξ _ ↦ ?_)).symm
    obtain ⟨C, -, hC⟩ := (a.remainder χ (j + 1)).exists_bound {q} isCompact_singleton [] [] []
    obtain ⟨D, -, hD⟩ := (b.remainder χ (j + 1)).exists_bound {q} isCompact_singleton [] [] []
    rw [coefficient_zero, Pi.zero_apply]
    refine coefficient_eq_zero_of_norm_le (m' := m - (j + 1 : ℕ)) (by push_cast; linarith) _
      (C := C + D) (R := 2) (fun η hη ↦ ?_) ξ
    have hsum : ∑ i ∈ range j, (cutoffAmplitude χ (a.term i)).coefficient (q.1, q.2, η) =
        ∑ i ∈ range j, (cutoffAmplitude χ (b.term i)).coefficient (q.1, q.2, η) :=
      Finset.sum_congr rfl fun i hi ↦ by rw [ih i (mem_range.1 hi)]
    have e : (b.term j - a.term j).coefficient (q, η) =
        (a.remainder χ (j + 1)).coefficient (q.1, q.2, η) -
          (b.remainder χ (j + 1)).coefficient (q.1, q.2, η) := by
      simp only [coefficient_remainder, sum_range_succ, h]
      rw [hsum]
      simp only [coefficient_cutoffAmplitude_of_two_le_norm χ _ hη, coefficient_sub, Pi.sub_apply]
      abel
    have hCq := hC q.1 q.2 rfl η
    have hDq := hD q.1 q.2 rfl η
    simp only [amplitudeDirections_def, List.map_nil, List.append_nil, iteratedFDerivAlong_nil,
      List.length_nil, Nat.cast_zero, sub_zero] at hCq hDq
    rw [e, add_mul]
    exact (norm_sub_le _ _).trans (add_le_add hCq hDq)

/-- A classical amplitude is determined by its full amplitude. -/
@[ext]
theorem ext {a b : ClassicalAmplitude n V W m} (h : a.toAmplitude = b.toAmplitude) : a = b := by
  have ht : a.term = b.term := funext (term_eq_of_toAmplitude_eq h)
  cases a
  cases b
  cases h
  cases ht
  rfl

end Uniqueness

/-! ### Restriction to the diagonal and derivatives -/

section Operations

/-- The restriction `(x, ξ) ↦ c(x, x, ξ)` of a classical amplitude to the diagonal is a classical
symbol, whose homogeneous terms are the restrictions of the terms of `c`. -/
def diagonal (c : ClassicalAmplitude n V W m) : ClassicalSymbol n V W m where
  toSymbol := c.toAmplitude.diagonal
  term j := (c.term j).compPosition (fun x ↦ (x, x)) (contDiff_id.prodMk contDiff_id)
  exists_remainder' := ⟨default, fun N ↦ ⟨(c.remainder default N).diagonal, fun ⟨_, _⟩ ↦ by simp⟩⟩

@[simp]
theorem toSymbol_diagonal (c : ClassicalAmplitude n V W m) :
    c.diagonal.toSymbol = c.toAmplitude.diagonal :=
  (rfl)

@[simp]
theorem term_diagonal (c : ClassicalAmplitude n V W m) (j : ℕ) :
    c.diagonal.term j = (c.term j).compPosition (fun x ↦ (x, x)) (contDiff_id.prodMk contDiff_id) :=
  (rfl)

/-- The derivative `∂_{y_j} c` of a classical amplitude in the input position is classical of the
same order, with the derivatives of the terms of `c` as its terms. -/
def spatialDerivSnd (j : Fin n) (c : ClassicalAmplitude n V W m) : ClassicalAmplitude n V W m where
  toAmplitude := Amplitude.spatialDerivSnd j c.toAmplitude
  term i := (c.term i).spatialDeriv (0, EuclideanSpace.single j 1)
  exists_remainder' := ⟨default, fun N ↦ ⟨Amplitude.spatialDerivSnd j (c.remainder default N),
    fun p ↦ by
      simp only [Amplitude.coefficient_spatialDerivSnd_eq_iteratedFDerivAlong,
        iteratedFDerivAlong_coefficient_remainder, ← spatialDerivSnd_cutoffAmplitude]⟩⟩

@[simp]
theorem toAmplitude_spatialDerivSnd (j : Fin n) (c : ClassicalAmplitude n V W m) :
    (spatialDerivSnd j c).toAmplitude = Amplitude.spatialDerivSnd j c.toAmplitude :=
  (rfl)

@[simp]
theorem term_spatialDerivSnd (j : Fin n) (c : ClassicalAmplitude n V W m) (i : ℕ) :
    (spatialDerivSnd j c).term i = (c.term i).spatialDeriv (0, EuclideanSpace.single j 1) :=
  (rfl)

/-- The frequency derivative of a classical amplitude has classical remainders: up to an
amplitude vanishing at large frequencies, the derivative of the remainder of `c` after `N` terms
is the remainder of `∂_{ξ_j} c` after `N` terms. -/
private theorem exists_remainder_frequencyDeriv (j : Fin n) (c : ClassicalAmplitude n V W m)
    (χ : FrequencyCutoff (CoordinateSpace n)) (N : ℕ) :
    ∃ r : Amplitude n V W (m - 1 - N), ∀ p, r.coefficient p =
      (Amplitude.frequencyDeriv j c.toAmplitude).coefficient p - ∑ i ∈ range N,
        (cutoffAmplitude χ (((c.term i).frequencyDeriv (EuclideanSpace.single j 1)).castDegree
          (by ring : m - i - 1 = m - 1 - i))).coefficient p := by
  have hf : ContDiff ℝ ∞ fun p ↦ (Amplitude.frequencyDeriv j c.toAmplitude).coefficient p -
      ∑ i ∈ range N, (cutoffAmplitude χ (((c.term i).frequencyDeriv
        (EuclideanSpace.single j 1)).castDegree (by ring : m - i - 1 = m - 1 - i))).coefficient p :=
    (Amplitude.frequencyDeriv j c.toAmplitude).contDiff_coefficient.sub
      (ContDiff.sum fun i _ ↦ (cutoffAmplitude χ _).contDiff_coefficient)
  obtain ⟨r, hr⟩ := Amplitude.exists_coefficient_eq_of_forall_le_norm (m := m - 1 - N) hf
    (Amplitude.frequencyDeriv j (c.remainder χ N)) (by linarith) 3 fun x y ξ hξ ↦ by
      have hξ2 : 2 < ‖ξ‖ := by linarith
      simp only [Amplitude.coefficient_frequencyDeriv_eq_iteratedFDerivAlong,
        iteratedFDerivAlong_coefficient_remainder]
      congr 1
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [← Amplitude.coefficient_frequencyDeriv_eq_iteratedFDerivAlong,
        coefficient_frequencyDeriv_cutoffAmplitude χ j _ hξ2]
      simp
  exact ⟨r, fun p ↦ congrFun hr p⟩

/-- The derivative `∂_{ξ_j} c` of a classical amplitude of order `m` in the frequency is
classical of order `m - 1`, with the derivatives of the terms of `c` as its terms. -/
def frequencyDeriv (j : Fin n) (c : ClassicalAmplitude n V W m) :
    ClassicalAmplitude n V W (m - 1) where
  toAmplitude := Amplitude.frequencyDeriv j c.toAmplitude
  term i := ((c.term i).frequencyDeriv (EuclideanSpace.single j 1)).castDegree (by ring)
  exists_remainder' := ⟨default, exists_remainder_frequencyDeriv j c default⟩

@[simp]
theorem toAmplitude_frequencyDeriv (j : Fin n) (c : ClassicalAmplitude n V W m) :
    (frequencyDeriv j c).toAmplitude = Amplitude.frequencyDeriv j c.toAmplitude :=
  (rfl)

@[simp]
theorem term_frequencyDeriv (j : Fin n) (c : ClassicalAmplitude n V W m) (i : ℕ) :
    (frequencyDeriv j c).term i =
      ((c.term i).frequencyDeriv (EuclideanSpace.single j 1)).castDegree (by ring) :=
  (rfl)

end Operations

/-! ### The terms of the left symbol expansion -/

section LeftTerm

/-- The remainder of the term `leftTerm c k` of the left symbol expansion of a classical amplitude
after `N` homogeneous terms has order `m - k - N`. -/
private theorem exists_remainder_leftTerm (χ : FrequencyCutoff (CoordinateSpace n)) (k : ℕ) :
    ∀ {m : ℝ} (c : ClassicalAmplitude n V W m) (N : ℕ), ∃ r : Symbol n V W (m - k - N), ∀ p,
      r.coefficient p = (c.toAmplitude.leftTerm k).coefficient p -
        ∑ j ∈ range N, χ p.2 • ((c.term j).leftTerm k).coefficient p := by
  induction k with
  | zero =>
    -- The restriction to the diagonal of the remainder of `c`.
    intro m c N
    refine ⟨Symbol.inclusion (by simp) (c.remainder χ N).diagonal, fun ⟨x, ξ⟩ ↦ ?_⟩
    simp
  | succ k ih =>
    -- The recursion of the terms, applied to the remainders of `∂_{y_l} ∂_{ξ_l} c`.
    intro m c N
    choose r hr using fun l : Fin n ↦ ih (spatialDerivSnd l (frequencyDeriv l c)) N
    refine ⟨Symbol.inclusion (le_of_eq (by push_cast; ring))
      ((-Complex.I / (k + 1)) • ∑ l, r l), fun p ↦ ?_⟩
    simp only [Symbol.coefficient_inclusion, Symbol.coefficient_smul, Symbol.coefficient_sum,
      Pi.smul_apply, Finset.sum_apply, hr, toAmplitude_spatialDerivSnd, toAmplitude_frequencyDeriv,
      term_spatialDerivSnd, term_frequencyDeriv, spatialDeriv_castDegree, leftTerm_castDegree,
      coefficient_castDegree, Amplitude.coefficient_leftTerm_succ, coefficient_leftTerm_succ,
      Finset.sum_sub_distrib, smul_sub, Finset.smul_sum]
    rw [Finset.sum_comm (s := range N)]
    simp only [smul_comm (χ p.2)]

/-- The term `((-i)^k / k!) ∑_{|w| = k} (∂_y^w ∂_ξ^w c)(x, x, ξ)` of order `m - k` of the left
symbol expansion of a classical amplitude `c` of order `m`, as a classical symbol: its full symbol
is `TauCeti.Amplitude.leftTerm` (`TauCeti.ClassicalAmplitude.toSymbol_leftTerm`) and its
homogeneous terms are the terms `(c_{m-j}).leftTerm k` of the homogeneous terms of `c`
(`TauCeti.ClassicalAmplitude.term_leftTerm`). -/
def leftTerm (c : ClassicalAmplitude n V W m) (k : ℕ) : ClassicalSymbol n V W (m - k) where
  toSymbol := c.toAmplitude.leftTerm k
  term j := ((c.term j).leftTerm k).castDegree (by ring)
  exists_remainder' := ⟨default, fun N ↦ by simpa using exists_remainder_leftTerm default k c N⟩

@[simp]
theorem toSymbol_leftTerm (c : ClassicalAmplitude n V W m) (k : ℕ) :
    (c.leftTerm k).toSymbol = c.toAmplitude.leftTerm k :=
  (rfl)

@[simp]
theorem term_leftTerm (c : ClassicalAmplitude n V W m) (k j : ℕ) :
    (c.leftTerm k).term j = ((c.term j).leftTerm k).castDegree (by ring) :=
  (rfl)

end LeftTerm

/-! ### The left symbol of a classical amplitude -/

section LeftSymbol

/-- **Classical remainders of the left symbol expansion.** If a symbol `b` of order `m` is an
asymptotic sum `b ∼ ∑ₖ leftTerm c k` of the terms of the left symbol expansion of a classical
amplitude `c`, then its remainder after the first `N` homogeneous terms `leftTerms c.term` has order
`m - N`: it is the remainder of the asymptotic sum after `N` terms, plus the remainder after
`N - k` homogeneous terms of each term `leftTerm c k`, `k < N`. -/
theorem exists_remainder_leftTerms_of_isAsymptoticSum (c : ClassicalAmplitude n V W m)
    {b : Symbol n V W m}
    (hb : (Symbol.inclusion (by simp) b : Symbol n V W (m - ((0 : ℕ) : ℝ))).IsAsymptoticSum
      c.toAmplitude.leftTerm)
    (χ : FrequencyCutoff (CoordinateSpace n)) (N : ℕ) :
    ∃ r : Symbol n V W (m - N), ∀ p, r.coefficient p =
      b.coefficient p - ∑ j ∈ range N, χ p.2 • (leftTerms c.term j).coefficient p := by
  obtain ⟨r, hr⟩ := ClassicalSymbol.exists_remainder_of_isAsymptoticSum c.leftTerm hb χ N
  exact ⟨r, fun p ↦ by simp [hr p, coefficient_leftTerms]⟩

variable [CompleteSpace W]

/-- **The left symbol of a classical amplitude is classical.** For a classical amplitude `c` of
order `m` with proper input support, the left symbol `c.toAmplitude.leftSymbol hc`, whose
quantization is that of `c`, is a classical symbol of order `m`. Its homogeneous terms are
`leftTerms c.term`: the term of degree `m - j` is
`∑_{k ≤ j} ((-i)^k / k!) ∑_{|w| = k} (∂_y^w ∂_ξ^w c_{m-j+k})(x, x, ξ)`. -/
def leftSymbol (c : ClassicalAmplitude n V W m) (hc : c.toAmplitude.HasProperInputSupport) :
    ClassicalSymbol n V W m where
  toSymbol := c.toAmplitude.leftSymbol hc
  term := leftTerms c.term
  exists_remainder' := ⟨default, exists_remainder_leftTerms_of_isAsymptoticSum c
    (Amplitude.isAsymptoticSum_leftSymbol hc) default⟩

variable (c : ClassicalAmplitude n V W m) (hc : c.toAmplitude.HasProperInputSupport)

@[simp]
theorem toSymbol_leftSymbol : (c.leftSymbol hc).toSymbol = c.toAmplitude.leftSymbol hc :=
  (rfl)

@[simp]
theorem term_leftSymbol (j : ℕ) : (c.leftSymbol hc).term j = leftTerms c.term j :=
  (rfl)

/-- **The principal symbol of the left symbol** of a classical amplitude is the restriction
`c_m(x, x, ξ)` of its leading term to the diagonal. -/
@[simp]
theorem principal_leftSymbol : (c.leftSymbol hc).principal = c.diagonal.principal := by
  ext1
  funext ⟨x, ξ⟩
  simp [ClassicalSymbol.coefficient_principal]

end LeftSymbol

end ClassicalAmplitude


/-! ### Classical amplitudes in moving frequency coordinates -/

section CompAmplitude

variable {κ : CoordinateSpace n → CoordinateSpace n}
  {M : CoordinateSpace n × CoordinateSpace n → CoordinateSpace n →L[ℝ] CoordinateSpace n}
  {g : CoordinateSpace n × CoordinateSpace n → ℝ}

/-- The term `g(x, y) • a(κ x, M(x, y) ξ)` of a homogeneous symbol `a` of degree `m`, for a smooth
map `κ`, a smooth family `M(x, y)` of linear maps and a smooth weight `g` such that `M(x, y)` is
invertible on the support of `g`; it is homogeneous of degree `m` in `ξ`. These are the terms of
the amplitude `TauCeti.ClassicalSymbol.compAmplitude` of a classical symbol. -/
def HomogeneousSymbol.compAmplitude
    (a : HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W m) (hκ : ContDiff ℝ ∞ κ)
    (hM : ContDiff ℝ ∞ M) (hg : ContDiff ℝ ∞ g) (hgM : ∀ w ∈ tsupport g, IsUnit (M w)) :
    HomogeneousSymbol (CoordinateSpace n × CoordinateSpace n) (CoordinateSpace n) V W m where
  coefficient q := g q.1 • a.coefficient (κ q.1.1, M q.1 q.2)
  zero_covector w := by simp
  contDiffOn_coefficient q hq := by
    by_cases hw : q.1 ∈ tsupport g
    · -- On the support of `g`, `M q.1` is invertible, so `M q.1 q.2 ≠ 0`.
      have hne : M q.1 q.2 ≠ 0 := fun h ↦ hq (by
        obtain ⟨u, hu⟩ := hgM q.1 hw
        simpa [← hu, ← mul_apply_eq_comp] using
          congrArg (↑u⁻¹ : CoordinateSpace n →L[ℝ] CoordinateSpace n) h)
      have hs : ContDiff ℝ ∞ fun q : (CoordinateSpace n × CoordinateSpace n) × CoordinateSpace n ↦
          (κ q.1.1, M q.1 q.2) :=
        (hκ.comp (contDiff_fst.comp contDiff_fst)).prodMk
          ((hM.comp contDiff_fst).clm_apply contDiff_snd)
      exact ((hg.comp contDiff_fst).contDiffAt.smul
        ((a.contDiffAt_coefficient (p := (κ q.1.1, M q.1 q.2)) hne).comp q
          hs.contDiffAt)).contDiffWithinAt
    · -- Off the support of `g` the term vanishes near `q`.
      have h0 : (fun q : (CoordinateSpace n × CoordinateSpace n) × CoordinateSpace n ↦
          g q.1 • a.coefficient (κ q.1.1, M q.1 q.2)) =ᶠ[𝓝 q] 0 := by
        filter_upwards [continuous_fst.continuousAt.preimage_mem_nhds
          ((isClosed_tsupport g).isOpen_compl.mem_nhds hw)] with q' hq'
        simp [image_eq_zero_of_notMem_tsupport hq']
      exact (contDiffAt_const.congr_of_eventuallyEq h0).contDiffWithinAt
  homogeneous q ξ t ht := by
    simp only [map_smul, a.homogeneous _ _ t ht]
    exact smul_comm _ _ _

@[simp]
theorem HomogeneousSymbol.coefficient_compAmplitude
    (a : HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W m) (hκ : ContDiff ℝ ∞ κ)
    (hM : ContDiff ℝ ∞ M) (hg : ContDiff ℝ ∞ g) (hgM : ∀ w ∈ tsupport g, IsUnit (M w))
    (q : (CoordinateSpace n × CoordinateSpace n) × CoordinateSpace n) :
    (a.compAmplitude hκ hM hg hgM).coefficient q = g q.1 • a.coefficient (κ q.1.1, M q.1 q.2) :=
  (rfl)

/-- The remainders of the amplitude `g(x, y) • b(κ x, M(x, y) ξ)` of a classical symbol `b`: at
large frequencies, the remainder after `N` terms is the amplitude of the remainder of `b`, since
`χ(M(x, y) ξ) = χ(ξ) = 1` there on the support of `g`. -/
private theorem exists_remainder_compAmplitude (b : ClassicalSymbol n V W m)
    (hκ : ContDiff ℝ ∞ κ) (hM : ContDiff ℝ ∞ M) (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g)
    (hgM : ∀ w ∈ tsupport g, IsUnit (M w)) (χ : FrequencyCutoff (CoordinateSpace n)) (N : ℕ) :
    ∃ r : Amplitude n V W (m - N), ∀ p, r.coefficient p =
      (b.toSymbol.compAmplitude hκ hM hg hgc hgM).coefficient p - ∑ j ∈ range N,
        (cutoffAmplitude χ ((b.term j).compAmplitude hκ hM hg hgM)).coefficient p := by
  obtain ⟨c, hc, hcS⟩ :=
    exists_norm_clm_apply_le_and_norm_le_of_isUnit hgc hM.continuous.continuousOn hgM
  have hf : ContDiff ℝ ∞ fun p ↦ (b.toSymbol.compAmplitude hκ hM hg hgc hgM).coefficient p -
      ∑ j ∈ range N, (cutoffAmplitude χ ((b.term j).compAmplitude hκ hM hg hgM)).coefficient p :=
    (b.toSymbol.compAmplitude hκ hM hg hgc hgM).contDiff_coefficient.sub
      (ContDiff.sum fun j _ ↦ (cutoffAmplitude χ _).contDiff_coefficient)
  obtain ⟨r, hr⟩ := Amplitude.exists_coefficient_eq_of_forall_le_norm hf
    ((b.remainder χ N).compAmplitude hκ hM hg hgc hgM) le_rfl (2 * c) fun x y ξ hξ ↦ by
      by_cases hw : (x, y) ∈ tsupport g
      · have hξ2 : 2 ≤ ‖ξ‖ := le_trans (by linarith) hξ
        have hMξ : 2 ≤ ‖M (x, y) ξ‖ := by
          -- `2 c ≤ ‖ξ‖ ≤ c ‖M ξ‖` with `c ≥ 1`.
          have h := (hcS _ hw ξ).2
          by_contra hlt
          nlinarith
        simp [χ.apply_eq_one_of_two_le_norm hξ2, χ.apply_eq_one_of_two_le_norm hMξ, smul_sub,
          Finset.smul_sum]
      · simp [image_eq_zero_of_notMem_tsupport hw]
  exact ⟨r, fun p ↦ congrFun hr p⟩

/-- The amplitude `g(x, y) • b(κ x, M(x, y) ξ)` of a classical symbol `b` of order `m`
(`TauCeti.Symbol.compAmplitude`) is a classical amplitude of order `m`, whose terms are the
amplitudes `g(x, y) • b_{m-j}(κ x, M(x, y) ξ)` of the homogeneous terms of `b`. These amplitudes
arise from changes of coordinates (Kuranishi's trick). -/
def ClassicalSymbol.compAmplitude (b : ClassicalSymbol n V W m)
    (hκ : ContDiff ℝ ∞ κ) (hM : ContDiff ℝ ∞ M) (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g)
    (hgM : ∀ w ∈ tsupport g, IsUnit (M w)) : ClassicalAmplitude n V W m where
  toAmplitude := b.toSymbol.compAmplitude hκ hM hg hgc hgM
  term j := (b.term j).compAmplitude hκ hM hg hgM
  exists_remainder' := ⟨default, exists_remainder_compAmplitude b hκ hM hg hgc hgM default⟩

variable (b : ClassicalSymbol n V W m) (hκ : ContDiff ℝ ∞ κ) (hM : ContDiff ℝ ∞ M)
  (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g) (hgM : ∀ w ∈ tsupport g, IsUnit (M w))

@[simp]
theorem ClassicalSymbol.toAmplitude_compAmplitude :
    (b.compAmplitude hκ hM hg hgc hgM).toAmplitude = b.toSymbol.compAmplitude hκ hM hg hgc hgM :=
  (rfl)

@[simp]
theorem ClassicalSymbol.term_compAmplitude (j : ℕ) :
    (b.compAmplitude hκ hM hg hgc hgM).term j = (b.term j).compAmplitude hκ hM hg hgM :=
  (rfl)

/-- The amplitude `g(x, y) • b(κ x, M(x, y) ξ)` has proper input support. -/
theorem ClassicalSymbol.hasProperInputSupport_compAmplitude :
    (b.compAmplitude hκ hM hg hgc hgM).toAmplitude.HasProperInputSupport := by
  rw [ClassicalSymbol.toAmplitude_compAmplitude]
  exact b.toSymbol.hasProperInputSupport_compAmplitude hκ hM hg hgc hgM

/-- **The principal symbol in moving frequency coordinates.** The left symbol of the amplitude
`g(x, y) • b(κ x, M(x, y) ξ)` of a classical symbol `b` is a classical symbol whose principal
symbol is `g(x, x) • σ(b)(κ x, M(x, x) ξ)`. -/
theorem ClassicalSymbol.coefficient_principal_leftSymbol_compAmplitude
    [CompleteSpace W] (x ξ : CoordinateSpace n) :
    ((b.compAmplitude hκ hM hg hgc hgM).leftSymbol
        (b.hasProperInputSupport_compAmplitude hκ hM hg hgc hgM)).principal.coefficient (x, ξ) =
      g (x, x) • b.principal.coefficient (κ x, M (x, x) ξ) := by
  rw [ClassicalAmplitude.principal_leftSymbol]
  simp [ClassicalSymbol.coefficient_principal]

end CompAmplitude

end TauCeti
