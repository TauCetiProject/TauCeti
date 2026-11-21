/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.DifferentialSymbol
public import TauCeti.Analysis.Pseudodifferential.Sobolev
public import TauCeti.Analysis.Pseudodifferential.Symbol.Classical
public import TauCeti.Geometry.Manifold.DifferentialOperator.Coordinates
import TauCeti.Algebra.Order.Antidiag.Pi
import TauCeti.Analysis.Distribution.TemperedDistribution.Deriv
import TauCeti.Analysis.Distribution.TemperedDistribution.SmulLeft

/-!
# Differential operators as classical pseudodifferential operators

A differential operator `P u = ∑ i ∈ s, bᵢ(x) (∂^{vᵢ} u)(x)` on `ℝⁿ` with smooth coefficients
`bᵢ : ℝⁿ → (V →L[ℂ] W)` has the polynomial left Fourier symbol
`TauCeti.differentialSymbol s v b (x, ξ) = ∑ i ∈ s, (∏ j, i ⟪ξ, vᵢⱼ⟫) • bᵢ(x)`. This file shows
that this symbol is a classical symbol of order `m` as soon as every summand has order at most
`m`, so that differential operators belong to the classical calculus: ellipticity, the
composition expansion and the parametrix construction apply to them. Only the local symbol
estimates are claimed; no bound on the coefficients uniform in the position is required.

The summands have homogeneous degrees, so each is a classical symbol with a single homogeneous
term (`TauCeti.ClassicalSymbol.ofContDiffHomogeneous`), and the operator is their sum after the
integer-step order inclusions.

For the differential symbol of order `m`:

* `TauCeti.ClassicalSymbol.ofDifferentialSymbol`: the classical symbol of order `m`, with full
  symbol `differentialSymbol s v b`
  (`TauCeti.ClassicalSymbol.coefficient_toSymbol_ofDifferentialSymbol`);
* `TauCeti.ClassicalSymbol.quantizeSchwartzValue_ofDifferentialSymbol`: its quantization is the
  differential operator itself on Schwartz input, with no smoothing remainder;
* `TauCeti.ClassicalSymbol.coefficient_term_ofDifferentialSymbol`: its homogeneous term of degree
  `m - j` is the part of the symbol made of the summands of order `m - j`; in particular the
  principal symbol (`TauCeti.ClassicalSymbol.coefficient_principal_ofDifferentialSymbol`) is the
  sum of the top-order summands, in the angular-frequency convention `σ(∂_v) = i ⟪ξ, v⟫`;
* `TauCeti.ClassicalSymbol.isElliptic_ofDifferentialSymbol_iff`: the operator is elliptic exactly
  when the symbol of its top-order summands is invertible at every nonzero frequency; for scalar
  coefficients, `TauCeti.isInvertible_differentialSymbol_filter_smul_id` reduces this to the
  nonvanishing of the geometric top-order symbol `∑ bᵢ ∏ⱼ ⟪ξ, vᵢⱼ⟫`;
* `TauCeti.ClassicalSymbol.hasCompactSpatialSupport_toSymbol_ofDifferentialSymbol`: compactly
  supported coefficients give a symbol with compact spatial support;
* `TauCeti.ClassicalSymbol.toDistr_quantizeSobolev_ofDifferentialSymbol`: for scalar coefficients
  of temperate growth whose symbol has compact spatial support, the extension of the quantization
  to the Bessel-potential space `H^r` is the differential operator acting on tempered
  distributions;
* `TauCeti.ClassicalSymbol.ofDifferentialOperator`: the classical symbol of a differential
  operator `D` of order at most `m` on the smooth real functions on `ℝⁿ` in Grothendieck's sense
  (`TauCeti.differentialOperators`, defined by iterated commutators with multiplication operators,
  with no continuity assumed), through its coordinate expression `D = ∑_{|α| ≤ m} c_α ∂^α`
  (`Module.Basis.eq_coordinateOperator_coordinateCoeff`). Its full symbol is
  `∑_{|α| ≤ m} c_α(x) (i ξ)^α`
  (`TauCeti.ClassicalSymbol.coefficient_toSymbol_ofDifferentialOperator`), and on Schwartz input
  its quantization is `D` itself, acting on `V`-valued functions componentwise
  (`TauCeti.ClassicalSymbol.map_quantizeSchwartzValue_ofDifferentialOperator`) and on
  complex-valued functions through their real and imaginary parts
  (`TauCeti.ClassicalSymbol.quantizeSchwartzValue_ofDifferentialOperator`). Its principal symbol is
  `i ^ m` times the geometric principal symbol `TauCeti.smoothPrincipalSymbol` of `D` at the
  covector `⟪ξ, ·⟫` (`TauCeti.ClassicalSymbol.coefficient_principal_ofDifferentialOperator`), so
  the two notions of ellipticity agree
  (`TauCeti.ClassicalSymbol.isElliptic_ofDifferentialOperator_iff`);
* `TauCeti.ClassicalSymbol.negLaplacian`: the classical symbol of the negative Laplacian
  `-∑ⱼ ∂ⱼ²`, with full symbol `‖ξ‖²` (`TauCeti.ClassicalSymbol.coefficient_toSymbol_negLaplacian`)
  and principal symbol `HomogeneousSymbol.normRpow _ _ V 2`
  (`TauCeti.ClassicalSymbol.principal_negLaplacian`); it is elliptic
  (`TauCeti.ClassicalSymbol.isElliptic_negLaplacian`), and its quantization is Mathlib's `-Δ` on
  Schwartz input (`TauCeti.ClassicalSymbol.quantizeSchwartzValue_negLaplacian`);
* `TauCeti.ClassicalSymbol.ofLinear`: the classical symbol of order `1` of a first-order operator
  `u ↦ -i ∑ⱼ L(eⱼ) ∂ⱼ u` with constant coefficients, given by a real-linear `L` of the frequency,
  with full and principal symbol `L ξ` (`TauCeti.ClassicalSymbol.principal_ofLinear`); its
  quantization is this operator on Schwartz input
  (`TauCeti.ClassicalSymbol.quantizeSchwartzValue_ofLinear`), and it is elliptic exactly when `L ξ`
  is invertible at every nonzero frequency (`TauCeti.ClassicalSymbol.isElliptic_ofLinear_iff`).

## References

* M. E. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI*, September 2008,
  Lecture I, (1.1)–(1.4) and (1.17).
* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, §18.1.
-/

public section

noncomputable section

open scoped ContDiff RealInnerProductSpace LineDeriv SchwartzMap

namespace TauCeti

variable {n : ℕ} {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W]
  [NormedSpace ℂ W] {m : ℝ}

open HomogeneousSymbol

/-! ### Differential operators -/

/-- The differential symbol of the summands of order exactly `m` of an operator with scalar
coefficients `bᵢ` is invertible wherever their geometric symbol `∑ bᵢ ∏ⱼ ⟪ξ, vᵢⱼ⟫` is nonzero: the
two differ by the factor `i ^ m`. With `TauCeti.ClassicalSymbol.isElliptic_ofDifferentialSymbol_iff`
this reduces the ellipticity of a scalar differential operator to the nonvanishing of its geometric
top-order symbol. -/
theorem isInvertible_differentialSymbol_filter_smul_id {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {ι : Type*} {k : ι → ℕ} (s : Finset ι) (v : ∀ i, Fin (k i) → E)
    (b : ι → E → ℂ) (m : ℕ) {x ξ : E}
    (h : ∑ i ∈ s with k i = m, b i x * ∏ j, (⟪ξ, v i j⟫ : ℂ) ≠ 0) :
    (differentialSymbol {i ∈ s | k i = m} v (fun i x ↦ b i x • ContinuousLinearMap.id ℂ V)
      (x, ξ)).IsInvertible := by
  have hsum : ∑ i ∈ s with k i = m, Complex.I ^ k i * (∏ j, (⟪ξ, v i j⟫ : ℂ)) * b i x =
      Complex.I ^ m * ∑ i ∈ s with k i = m, b i x * ∏ j, (⟪ξ, v i j⟫ : ℂ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    rw [show Complex.I ^ k i = Complex.I ^ m by rw [(Finset.mem_filter.1 hi).2]]
    ring
  rw [differentialSymbol_eq_sum_pow_mul]
  simp_rw [smul_smul]
  rw [← Finset.sum_smul, hsum, ContinuousLinearMap.isInvertible_smul_iff
    (mul_ne_zero (pow_ne_zero _ Complex.I_ne_zero) h)]
  simpa using ContinuousLinearMap.isInvertible_equiv (f := ContinuousLinearEquiv.refl ℂ V)

namespace ClassicalSymbol

variable {ι : Type*} {k : ι → ℕ}

/-- The classical symbol of order `m` of the differential operator
`u ↦ ∑ i ∈ s, bᵢ(x) (∂^{vᵢ} u)(x)` with smooth coefficients `bᵢ`, where the summand `i` has order
`k i ≤ m`. Its full symbol is the polynomial `TauCeti.differentialSymbol s v b`
(`TauCeti.ClassicalSymbol.coefficient_toSymbol_ofDifferentialSymbol`), and its homogeneous term of
degree `m - j` collects the summands of order `m - j`
(`TauCeti.ClassicalSymbol.coefficient_term_ofDifferentialSymbol`). -/
def ofDifferentialSymbol (m : ℕ) (s : Finset ι) (v : ∀ i, Fin (k i) → CoordinateSpace n)
    (b : ι → CoordinateSpace n → V →L[ℂ] W) (hb : ∀ i ∈ s, ContDiff ℝ ∞ (b i))
    (hk : ∀ i ∈ s, k i ≤ m) : ClassicalSymbol n V W m :=
  ∑ i ∈ s.attach, inclusion (m - k i) (by rw [Nat.cast_sub (hk i i.property)]; ring)
    (ofContDiffHomogeneous (m := k i) (differentialSymbol {i.val} v b)
      (contDiff_differentialSymbol _ v fun j hj ↦ Finset.mem_singleton.1 hj ▸ hb i i.property)
      fun x ξ _ t _ ↦ by
        rw [Real.rpow_natCast]
        exact differentialSymbol_smul_snd _ v b (fun j hj ↦ by rw [Finset.mem_singleton.1 hj])
          x ξ t)

variable (m : ℕ) (s : Finset ι) (v : ∀ i, Fin (k i) → CoordinateSpace n)
  (b : ι → CoordinateSpace n → V →L[ℂ] W) (hb : ∀ i ∈ s, ContDiff ℝ ∞ (b i))
  (hk : ∀ i ∈ s, k i ≤ m)

/-- The full symbol of `ClassicalSymbol.ofDifferentialSymbol` is the polynomial differential
symbol. -/
@[simp]
theorem coefficient_toSymbol_ofDifferentialSymbol :
    (ofDifferentialSymbol m s v b hb hk).toSymbol.coefficient = differentialSymbol s v b := by
  funext p
  simp only [ofDifferentialSymbol, toSymbol_sum, Symbol.coefficient_sum, Finset.sum_apply,
    toSymbol_inclusion,
    Symbol.coefficient_inclusion, toSymbol_ofContDiffHomogeneous,
    Symbol.coefficient_ofContDiffHomogeneous]
  rw [Finset.sum_attach s fun i ↦ differentialSymbol {i} v b p, differentialSymbol_def]
  exact Finset.sum_congr rfl fun i _ ↦ differentialSymbol_singleton i v b p

/-- **Differential operators are pseudodifferential operators.** On Schwartz input, the
quantization of the classical symbol of a differential operator is the differential operator,
with no smoothing remainder. -/
theorem quantizeSchwartzValue_ofDifferentialSymbol [CompleteSpace V] [CompleteSpace W]
    (u : 𝓢(CoordinateSpace n, V)) (x : CoordinateSpace n) :
    quantizeSchwartzValue (ofDifferentialSymbol m s v b hb hk).toSymbol.coefficient u x =
      ∑ i ∈ s, b i x (∂^{v i} u x) := by
  rw [coefficient_toSymbol_ofDifferentialSymbol, quantizeSchwartzValue_differentialSymbol]

/-- The homogeneous term of degree `m - j` of the classical symbol of a differential operator is,
away from `ξ = 0`, the differential symbol of its summands of order `m - j`. -/
theorem coefficient_term_ofDifferentialSymbol (j : ℕ) {x ξ : CoordinateSpace n} (hξ : ξ ≠ 0) :
    ((ofDifferentialSymbol m s v b hb hk).term j).coefficient (x, ξ) =
      differentialSymbol {i ∈ s | k i + j = m} v b (x, ξ) := by
  simp only [ofDifferentialSymbol, term_sum, coefficient_sum, Finset.sum_apply]
  rw [differentialSymbol_def, Finset.sum_filter, ← Finset.sum_attach s]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have hki := hk i i.property
  rw [term_inclusion]
  split_ifs with hj hkj hkj
  · -- The summand `i` has order `m - j`: its term of degree `m - j` is its principal symbol.
    rw [coefficient_castDegree, coefficient_congr_index (ofContDiffHomogeneous _ _ _).term
      (show j - (m - k i) = 0 by omega), ← coefficient_principal, principal_ofContDiffHomogeneous,
      coefficient_mk'_of_ne_zero _ _ _ hξ, differentialSymbol_singleton]
  · -- Otherwise the summand only contributes to the terms of other degrees.
    obtain ⟨l, hl⟩ : ∃ l, j - (m - k i) = l + 1 := ⟨j - (m - k i) - 1, by omega⟩
    rw [coefficient_castDegree, coefficient_congr_index (ofContDiffHomogeneous _ _ _).term hl,
      term_ofContDiffHomogeneous_succ, coefficient_zero, Pi.zero_apply]
  · omega
  · rw [coefficient_zero, Pi.zero_apply]

/-- The principal symbol of the classical symbol of a differential operator of order `m` is,
away from `ξ = 0`, the differential symbol of its summands of order exactly `m`. In particular
`σ(∂_v)(ξ) = i ⟪ξ, v⟫`. -/
theorem coefficient_principal_ofDifferentialSymbol {x ξ : CoordinateSpace n} (hξ : ξ ≠ 0) :
    (ofDifferentialSymbol m s v b hb hk).principal.coefficient (x, ξ) =
      differentialSymbol {i ∈ s | k i = m} v b (x, ξ) := by
  rw [coefficient_principal, coefficient_term_ofDifferentialSymbol m s v b hb hk 0 hξ]
  simp

/-- **Ellipticity of a differential operator.** The classical symbol of a differential operator
of order `m` is elliptic exactly when the differential symbol of its summands of order exactly
`m` is invertible at every position and every nonzero frequency. -/
theorem isElliptic_ofDifferentialSymbol_iff :
    (ofDifferentialSymbol m s v b hb hk).IsElliptic ↔
      ∀ x ξ, ξ ≠ 0 → (differentialSymbol {i ∈ s | k i = m} v b (x, ξ)).IsInvertible := by
  rw [isElliptic_iff]
  refine forall_congr' fun x ↦ forall_congr' fun ξ ↦ forall_congr' fun hξ ↦ ?_
  rw [coefficient_principal_ofDifferentialSymbol m s v b hb hk hξ]

/-- Compactly supported coefficients give a classical symbol with compact spatial support. -/
theorem hasCompactSpatialSupport_toSymbol_ofDifferentialSymbol
    (hbc : ∀ i ∈ s, HasCompactSupport (b i)) :
    (ofDifferentialSymbol m s v b hb hk).toSymbol.HasCompactSpatialSupport := by
  refine Symbol.hasCompactSpatialSupport_iff.2
    ⟨⋃ i ∈ s, tsupport (b i), s.isCompact_biUnion fun i hi ↦ hbc i hi, fun x hx ξ ↦ ?_⟩
  rw [coefficient_toSymbol_ofDifferentialSymbol, differentialSymbol_def]
  refine Finset.sum_eq_zero fun i hi ↦ ?_
  rw [image_eq_zero_of_notMem_tsupport fun h ↦ hx (Set.mem_biUnion hi h), smul_zero]

section Sobolev

open MeasureTheory
open scoped BesselPotentialSpace

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- **Differential operators on Bessel-potential spaces.** For scalar coefficients `hᵢ` of
temperate growth whose symbol has compact spatial support (for example compactly supported smooth
`hᵢ`), the extension `H^r → H^{r - m}` of the quantization of the classical symbol of
`u ↦ ∑ i ∈ s, hᵢ ∂^{vᵢ} u` is this differential operator acting on tempered distributions: for
every `u ∈ H^r` it is `∑ i ∈ s, hᵢ ∂^{vᵢ} u`, with the distributional derivatives of `u`. -/
theorem toDistr_quantizeSobolev_ofDifferentialSymbol {h : ι → CoordinateSpace n → ℂ}
    (hh : ∀ i ∈ s, (h i).HasTemperateGrowth)
    (hc : (ofDifferentialSymbol m s v (fun i x ↦ h i x • ContinuousLinearMap.id ℂ F)
      (fun i hi ↦ (hh i hi).1.smul contDiff_const) hk).toSymbol.HasCompactSpatialSupport)
    (r : ℝ) (u : H^{r}(CoordinateSpace n, F)) :
    ((ofDifferentialSymbol m s v _ _ hk).toSymbol.quantizeSobolev hc r u).toDistr =
      ∑ i ∈ s, TemperedDistribution.smulLeftCLM F (h i) (∂^{v i} u.toDistr) := by
  -- Both sides are continuous in `u ∈ H^r`, and they agree on the dense Schwartz functions.
  refine congrFun ((SchwartzMap.denseRange_toBesselPotentialSpaceCLM (p := 2) r
    ENNReal.ofNat_ne_top).equalizer
    (BesselPotentialSpace.continuous_toDistr.comp (ContinuousLinearMap.continuous _))
    (continuous_finsetSum _ fun i _ ↦ (ContinuousLinearMap.continuous _).comp
      ((LineDeriv.continuous_iteratedLineDerivOp _).comp BesselPotentialSpace.continuous_toDistr))
    (funext fun u ↦ ?_)) u
  ext φ
  simp only [Function.comp_apply, Symbol.toDistr_quantizeSobolev_toBesselPotentialSpaceCLM_apply,
    quantizeSchwartzValue_ofDifferentialSymbol, SchwartzMap.toDistr_toBesselPotentialSpaceCLM]
  rw [sum_apply]
  simp only [TemperedDistribution.iteratedLineDerivOp_toTemperedDistributionCLM_eq,
    TemperedDistribution.smulLeftCLM_toTemperedDistributionCLM_eq,
    SchwartzMap.toTemperedDistributionCLM_apply_apply]
  have hint (i : ι) (_ : i ∈ s) :
      Integrable fun x ↦ φ x • SchwartzMap.smulLeftCLM F (h i) (∂^{v i} u) x :=
    (SchwartzMap.integrable _).smul_of_top_right (φ.memLp ⊤)
  rw [← integral_finsetSum s hint]
  refine integral_congr_ae (.of_forall fun x ↦ ?_)
  simp only [Finset.smul_sum]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  rw [SchwartzMap.smulLeftCLM_apply_apply (hh i hi),
    _root_.smul_apply, ContinuousLinearMap.id_apply]

end Sobolev

/-! ### The Laplacian -/

variable (n V) in
/-- The classical symbol of order `2` of the negative Laplacian `-Δ = -∑ⱼ ∂ⱼ²` on `V`-valued
functions on `ℝⁿ`. -/
def negLaplacian : ClassicalSymbol n V V 2 :=
  ofDifferentialSymbol (k := fun _ : Fin n ↦ 2) 2 Finset.univ
    (fun j _ ↦ EuclideanSpace.single j 1) (fun _ _ ↦ -ContinuousLinearMap.id ℂ V)
    (fun _ _ ↦ contDiff_const) fun _ _ ↦ le_rfl

/-- The differential symbol of `-∑ⱼ ∂ⱼ²` is `‖ξ‖²`. -/
private theorem differentialSymbol_negLaplacian (p : CoordinateSpace n × CoordinateSpace n) :
    differentialSymbol (k := fun _ : Fin n ↦ 2) Finset.univ (fun j _ ↦ EuclideanSpace.single j 1)
      (fun _ _ ↦ -ContinuousLinearMap.id ℂ V) p = ‖p.2‖ ^ 2 • ContinuousLinearMap.id ℂ V := by
  rw [differentialSymbol_def, EuclideanSpace.real_norm_sq_eq, Finset.sum_smul]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [← Complex.coe_smul, smul_neg, ← neg_smul]
  congr 1
  simp only [EuclideanSpace.inner_single_right, one_mul, RCLike.conj_to_real, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin, mul_pow, Complex.I_sq]
  push_cast
  ring

/-- The full symbol of the negative Laplacian is `‖ξ‖²`. -/
@[simp]
theorem coefficient_toSymbol_negLaplacian (p : CoordinateSpace n × CoordinateSpace n) :
    (negLaplacian n V).toSymbol.coefficient p = ‖p.2‖ ^ 2 • ContinuousLinearMap.id ℂ V := by
  rw [negLaplacian, coefficient_toSymbol_ofDifferentialSymbol, differentialSymbol_negLaplacian]

open Laplacian in
/-- The quantization of `negLaplacian` is the negative Laplacian `-Δ` on Schwartz input. -/
theorem quantizeSchwartzValue_negLaplacian [CompleteSpace V] (u : 𝓢(CoordinateSpace n, V))
    (x : CoordinateSpace n) :
    quantizeSchwartzValue (negLaplacian n V).toSymbol.coefficient u x = -Δ u x := by
  rw [negLaplacian, quantizeSchwartzValue_ofDifferentialSymbol,
    SchwartzMap.laplacian_eq_sum (EuclideanSpace.basisFun (Fin n) ℝ)]
  simp [LineDeriv.iteratedLineDerivOp_succ_left, EuclideanSpace.basisFun_apply, Fin.tail]

/-- The principal symbol of the negative Laplacian is `‖ξ‖²`. -/
@[simp]
theorem principal_negLaplacian :
    (negLaplacian n V).principal = normRpow (CoordinateSpace n) (CoordinateSpace n) V 2 :=
  ext_of_ne_zero fun x ξ hξ ↦ by
    rw [negLaplacian, coefficient_principal_ofDifferentialSymbol _ _ _ _ _ _ hξ,
      Finset.filter_true_of_mem fun _ _ ↦ rfl, differentialSymbol_negLaplacian,
      coefficient_normRpow_of_ne_zero _ _ _ hξ, Real.rpow_two]

/-- **The Laplacian is elliptic.** -/
theorem isElliptic_negLaplacian : (negLaplacian n V).IsElliptic := by
  rw [isElliptic_def, principal_negLaplacian]
  exact HomogeneousSymbol.isElliptic_normRpow _ _ _ _

/-! ### First-order operators with constant coefficients -/

/-- The classical symbol of order `1` with full symbol `L ξ`, for a continuous real-linear function
`L` of the frequency: the symbol of the first-order operator `u ↦ -i ∑ⱼ L(eⱼ) ∂ⱼ u` with constant
coefficients (`TauCeti.ClassicalSymbol.quantizeSchwartzValue_ofLinear`). Its principal symbol is
`HomogeneousSymbol.ofLinear L` (`TauCeti.ClassicalSymbol.principal_ofLinear`). -/
def ofLinear (L : CoordinateSpace n →L[ℝ] (V →L[ℂ] W)) : ClassicalSymbol n V W 1 :=
  ofContDiffHomogeneous (fun p ↦ L p.2) (L.contDiff.comp contDiff_snd)
    fun _ _ _ _ _ ↦ by rw [Real.rpow_one, map_smul]

/-- The full symbol of `ClassicalSymbol.ofLinear L` is `L ξ`. -/
@[simp]
theorem coefficient_toSymbol_ofLinear (L : CoordinateSpace n →L[ℝ] (V →L[ℂ] W))
    (p : CoordinateSpace n × CoordinateSpace n) :
    (ofLinear L).toSymbol.coefficient p = L p.2 := by
  rw [ofLinear, toSymbol_ofContDiffHomogeneous, Symbol.coefficient_ofContDiffHomogeneous]

/-- The principal symbol of `ClassicalSymbol.ofLinear L` is the homogeneous symbol `L ξ`. -/
@[simp]
theorem principal_ofLinear (L : CoordinateSpace n →L[ℝ] (V →L[ℂ] W)) :
    (ofLinear L).principal = HomogeneousSymbol.ofLinear _ L :=
  HomogeneousSymbol.ext_of_ne_zero fun x ξ hξ ↦ by
    rw [ofLinear, principal_ofContDiffHomogeneous,
      HomogeneousSymbol.coefficient_mk'_of_ne_zero _ _ _ hξ, HomogeneousSymbol.coefficient_ofLinear]

/-- The full symbol `L ξ` is the differential symbol of `u ↦ -i ∑ⱼ L(eⱼ) ∂ⱼ u`. -/
private theorem differentialSymbol_ofLinear (L : CoordinateSpace n →L[ℝ] (V →L[ℂ] W))
    (p : CoordinateSpace n × CoordinateSpace n) :
    differentialSymbol (k := fun _ : Fin n ↦ 1) Finset.univ (fun j _ ↦ EuclideanSpace.single j 1)
      (fun j _ ↦ -Complex.I • L (EuclideanSpace.single j 1)) p = L p.2 := by
  rw [differentialSymbol_def]
  conv_rhs => rw [← (EuclideanSpace.basisFun (Fin n) ℝ).sum_repr p.2]
  simp only [map_sum, map_smul, EuclideanSpace.basisFun_apply, EuclideanSpace.basisFun_repr]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [smul_smul, ← Complex.coe_smul]
  congr 1
  simp only [EuclideanSpace.inner_single_right, one_mul, RCLike.conj_to_real, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin, pow_one]
  rw [mul_right_comm, mul_neg, Complex.I_mul_I, neg_neg, one_mul]

/-- **First-order operators with constant coefficients are pseudodifferential operators.** On
Schwartz input, the quantization of `ClassicalSymbol.ofLinear L` is `u ↦ -i ∑ⱼ L(eⱼ) ∂ⱼ u`, with no
smoothing remainder. -/
theorem quantizeSchwartzValue_ofLinear [CompleteSpace V] [CompleteSpace W]
    (L : CoordinateSpace n →L[ℝ] (V →L[ℂ] W)) (u : 𝓢(CoordinateSpace n, V))
    (x : CoordinateSpace n) :
    quantizeSchwartzValue (ofLinear L).toSymbol.coefficient u x =
      -Complex.I • ∑ j, L (EuclideanSpace.single j 1)
        (∂_{(EuclideanSpace.single j 1 : CoordinateSpace n)} u x) := by
  have h : (ofLinear L).toSymbol.coefficient =
      differentialSymbol (k := fun _ : Fin n ↦ 1) Finset.univ
        (fun j _ ↦ EuclideanSpace.single j 1)
        (fun j _ ↦ -Complex.I • L (EuclideanSpace.single j 1)) :=
    funext fun p ↦ by rw [coefficient_toSymbol_ofLinear, differentialSymbol_ofLinear]
  rw [h, quantizeSchwartzValue_differentialSymbol, Finset.smul_sum]
  simp [LineDeriv.iteratedLineDerivOp_one]

/-- **Ellipticity of a first-order operator with constant coefficients.** The classical symbol
`ClassicalSymbol.ofLinear L` is elliptic exactly when `L ξ` is invertible at every nonzero
frequency. -/
theorem isElliptic_ofLinear_iff (L : CoordinateSpace n →L[ℝ] (V →L[ℂ] W)) :
    (ofLinear L).IsElliptic ↔ ∀ ξ, ξ ≠ 0 → (L ξ).IsInvertible := by
  rw [isElliptic_def, principal_ofLinear, HomogeneousSymbol.isElliptic_iff]
  simp only [HomogeneousSymbol.coefficient_ofLinear]
  exact ⟨fun h ξ hξ ↦ h 0 ξ hξ, fun h _ ξ hξ ↦ h ξ hξ⟩

end ClassicalSymbol

/-! ### Differential operators in Grothendieck's sense -/

namespace ClassicalSymbol

open Finset
open scoped _root_.Manifold

/-- The standard basis of `ℝⁿ`, along which differential operators are written in coordinates. -/
private abbrev coordinateBasis (n : ℕ) : Module.Basis (Fin n) ℝ (CoordinateSpace n) :=
  (EuclideanSpace.basisFun (Fin n) ℝ).toBasis

private theorem coordinateBasis_apply (i : Fin n) :
    coordinateBasis n i = EuclideanSpace.single i 1 := by
  simp [EuclideanSpace.basisFun_apply]

variable (V) in
/-- A smooth real coefficient `c`, acting on `V` by `c(x) • id`, is smooth. -/
private theorem contDiff_ofReal_smul_id
    (c : C^∞⟮𝓘(ℝ, CoordinateSpace n), CoordinateSpace n; ℝ⟯) :
    ContDiff ℝ ∞ fun x ↦ (c x : ℂ) • ContinuousLinearMap.id ℂ V :=
  (Complex.ofRealCLM.contDiff.comp c.contMDiff.contDiff).smul contDiff_const

variable (V) in
/-- The classical symbol of order `m` of a differential operator `D` of order at most `m` on the
smooth real functions on `ℝⁿ`, in Grothendieck's sense of iterated commutators with multiplication
operators, acting on `V`-valued functions componentwise. Writing `D = ∑_{|α| ≤ m} c_α ∂^α` in the
coordinates of `ℝⁿ` (`Module.Basis.eq_coordinateOperator_coordinateCoeff`), it is the polynomial
symbol `∑_{|α| ≤ m} c_α(x) (i ξ)^α`
(`TauCeti.ClassicalSymbol.coefficient_toSymbol_ofDifferentialOperator`), whose quantization on
Schwartz input is `D`
(`TauCeti.ClassicalSymbol.map_quantizeSchwartzValue_ofDifferentialOperator`). Only the local
symbol estimates hold: the coefficients need not be bounded. -/
def ofDifferentialOperator {m : ℕ}
    (D : differentialOperators ℝ C^∞⟮𝓘(ℝ, CoordinateSpace n), CoordinateSpace n; ℝ⟯
      C^∞⟮𝓘(ℝ, CoordinateSpace n), CoordinateSpace n; ℝ⟯
      C^∞⟮𝓘(ℝ, CoordinateSpace n), CoordinateSpace n; ℝ⟯ m) :
    ClassicalSymbol n V V m :=
  ofDifferentialSymbol (k := fun α ↦ ∑ i, α i) m ((range (m + 1)).biUnion (piAntidiag univ))
    (fun α j ↦ coordinateBasis n (multiIndexWord α j))
    (fun α x ↦ (coordinateCoeff (coordinateBasis n).smoothCoord D.val α x : ℂ) •
      ContinuousLinearMap.id ℂ V)
    (fun α _ ↦ contDiff_ofReal_smul_id V _)
    fun α hα ↦ by
      obtain ⟨k, hk, hαk⟩ := mem_biUnion.1 hα
      exact (mem_piAntidiag.1 hαk).1.trans_le (Nat.lt_succ_iff.1 (mem_range.1 hk))

variable {m : ℕ}
  (D : differentialOperators ℝ C^∞⟮𝓘(ℝ, CoordinateSpace n), CoordinateSpace n; ℝ⟯
    C^∞⟮𝓘(ℝ, CoordinateSpace n), CoordinateSpace n; ℝ⟯
    C^∞⟮𝓘(ℝ, CoordinateSpace n), CoordinateSpace n; ℝ⟯ m)

/-- The differential symbol of the coordinate expression `∑_{α ∈ t} c_α ∂^α` with smooth real
coefficients `c_α` is `∑_{α ∈ t} c_α(x) (i ξ)^α`. -/
private theorem differentialSymbol_multiIndexWord (t : Finset (Fin n → ℕ))
    (c : (Fin n → ℕ) → C^∞⟮𝓘(ℝ, CoordinateSpace n), CoordinateSpace n; ℝ⟯)
    (x ξ : CoordinateSpace n) :
    differentialSymbol (k := fun α ↦ ∑ i, α i) t (fun α j ↦ coordinateBasis n (multiIndexWord α j))
        (fun α x ↦ (c α x : ℂ) • ContinuousLinearMap.id ℂ V) (x, ξ) =
      ∑ α ∈ t, ((c α x : ℂ) * ∏ i, (Complex.I * ξ i) ^ α i) • ContinuousLinearMap.id ℂ V := by
  rw [differentialSymbol_def]
  refine sum_congr rfl fun α _ ↦ ?_
  rw [smul_smul, prod_multiIndexWord α fun i ↦ Complex.I * (⟪ξ, coordinateBasis n i⟫ : ℂ),
    mul_comm]
  simp [coordinateBasis_apply, EuclideanSpace.inner_single_right]

/-- **The symbol of a differential operator in coordinates.** The full symbol of
`ofDifferentialOperator V D` is the polynomial `∑_{|α| ≤ m} c_α(x) (i ξ)^α`, where
`c = coordinateCoeff` are the coefficients of `D` in the coordinates of `ℝⁿ`. -/
@[simp]
theorem coefficient_toSymbol_ofDifferentialOperator (x ξ : CoordinateSpace n) :
    (ofDifferentialOperator V D).toSymbol.coefficient (x, ξ) =
      ∑ k ∈ range (m + 1), ∑ α ∈ piAntidiag univ k,
        ((coordinateCoeff (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.smoothCoord D.val α x : ℂ) *
          ∏ i, (Complex.I * ξ i) ^ α i) • ContinuousLinearMap.id ℂ V := by
  rw [ofDifferentialOperator, coefficient_toSymbol_ofDifferentialSymbol,
    differentialSymbol_multiIndexWord, sum_biUnion_piAntidiag]

/-- **Differential operators are pseudodifferential operators.** On Schwartz input `u`, the
quantization of `ofDifferentialOperator V D` is the differential operator `D` acting on `V`-valued
functions componentwise: for every real-linear functional `ℓ` on `V`, its image under `ℓ` is `D`
applied to the smooth function `ℓ ∘ u`. -/
theorem map_quantizeSchwartzValue_ofDifferentialOperator [CompleteSpace V] (ℓ : V →L[ℝ] ℝ)
    (u : 𝓢(CoordinateSpace n, V)) (x : CoordinateSpace n) :
    ℓ (quantizeSchwartzValue (ofDifferentialOperator V D).toSymbol.coefficient u x) =
      D.val ⟨fun y ↦ ℓ (u y), (ℓ.contDiff.comp (u.smooth ⊤)).contMDiff⟩ x := by
  set g : C^∞⟮𝓘(ℝ, CoordinateSpace n), CoordinateSpace n; ℝ⟯ :=
    ⟨fun y ↦ ℓ (u y), (ℓ.contDiff.comp (u.smooth ⊤)).contMDiff⟩
  rw [congr($((coordinateBasis n).eq_coordinateOperator_coordinateCoeff D.property) g x),
    ofDifferentialOperator, quantizeSchwartzValue_ofDifferentialSymbol, sum_biUnion_piAntidiag]
  simp only [coordinateOperator_apply, ContMDiffMap.coe_sum, Finset.sum_apply, map_sum]
  refine sum_congr rfl fun k _ ↦ sum_congr rfl fun α _ ↦ ?_
  -- `ℓ` commutes with the derivative `∂^α`, taken along the word listing each coordinate `i`
  -- exactly `αᵢ` times.
  have hu := ℓ.iteratedFDeriv_comp_left (u.smooth ⊤).contDiffAt (x := x)
    (i := ∑ i, α i) (by exact_mod_cast le_top)
  have hu' : ℓ (iteratedFDeriv ℝ (∑ i, α i) u x fun j ↦ coordinateBasis n (multiIndexWord α j)) =
      iteratedFDeriv ℝ (∑ i, α i) g x fun j ↦ coordinateBasis n (multiIndexWord α j) := by
    rw [ContMDiffMap.coeFn_mk]
    exact congr($hu _).symm
  simp only [_root_.smul_apply, ContinuousLinearMap.id_apply, Complex.coe_smul, map_smul,
    SchwartzMap.iteratedLineDerivOp_eq_iteratedFDeriv, hu', smul_eq_mul, ContMDiffMap.coe_mul,
    Pi.mul_apply, multiIndexDeriv_apply_eq_iteratedFDeriv_multiIndexWord, Function.comp_def]
  exact mul_comm _ _

/-- **Scalar differential operators are pseudodifferential operators.** On complex-valued
Schwartz input `u`, the quantization of `ofDifferentialOperator ℂ D` is `D` applied separately to
the real and imaginary parts of `u`. -/
theorem quantizeSchwartzValue_ofDifferentialOperator (u : 𝓢(CoordinateSpace n, ℂ))
    (x : CoordinateSpace n) :
    quantizeSchwartzValue (ofDifferentialOperator ℂ D).toSymbol.coefficient u x =
      D.val ⟨fun y ↦ (u y).re, (Complex.reCLM.contDiff.comp (u.smooth ⊤)).contMDiff⟩ x +
        D.val ⟨fun y ↦ (u y).im, (Complex.imCLM.contDiff.comp (u.smooth ⊤)).contMDiff⟩ x *
          Complex.I := by
  refine Complex.ext ?_ ?_
  · simpa using map_quantizeSchwartzValue_ofDifferentialOperator D Complex.reCLM u x
  · simpa using map_quantizeSchwartzValue_ofDifferentialOperator D Complex.imCLM u x

/-- **The principal symbol of a differential operator.** Away from `ξ = 0`, the principal symbol
of `ofDifferentialOperator V D` is `i ^ m` times the geometric principal symbol of `D`, defined by
iterated commutators (`TauCeti.smoothPrincipalSymbol`), at the covector `⟪ξ, ·⟫`. This is the
angular-frequency convention `σ(∂ⱼ) = i ξⱼ`. -/
theorem coefficient_principal_ofDifferentialOperator {x ξ : CoordinateSpace n} (hξ : ξ ≠ 0) :
    (ofDifferentialOperator V D).principal.coefficient (x, ξ) =
      (Complex.I ^ m * smoothPrincipalSymbol 𝓘(ℝ, CoordinateSpace n) (x := x)
        BoundarylessManifold.isInteriorPoint D (innerSL ℝ ξ) : ℂ) • ContinuousLinearMap.id ℂ V := by
  -- The covector `⟪ξ, ·⟫` as a cotangent vector at `x`.
  obtain ⟨η, hη⟩ : ∃ η : TangentSpace 𝓘(ℝ, CoordinateSpace n) x →L[ℝ] ℝ, η = innerSL ℝ ξ :=
    ⟨_, rfl⟩
  have hinner (i : Fin n) : η (coordinateBasis n i) = ξ i := by
    rw [hη, coordinateBasis_apply]
    exact (EuclideanSpace.inner_single_right i (1 : ℝ) ξ).trans (by simp)
  have hσ := (coordinateBasis n).smoothPrincipalSymbol_eq_sum_coordinateCoeff D x η
  simp only [hinner] at hσ
  rw [← hη, ofDifferentialOperator, coefficient_principal_ofDifferentialSymbol _ _ _ _ _ _ hξ,
    differentialSymbol_multiIndexWord, hσ, Complex.ofReal_sum, mul_sum, sum_smul]
  refine sum_congr ?_ fun α hα ↦ ?_
  · ext α
    simp only [mem_filter, mem_biUnion, mem_range, mem_piAntidiag, mem_univ, ne_eq,
      implies_true, and_true]
    exact ⟨fun h ↦ h.2, fun h ↦ ⟨⟨m, Nat.lt_succ_self m, h⟩, h⟩⟩
  · have hαm : ∑ i, α i = m := (mem_piAntidiag.1 hα).1
    congr 1
    simp only [mul_pow, prod_mul_distrib, prod_pow_eq_pow_sum, hαm, Complex.ofReal_mul,
      Complex.ofReal_prod, Complex.ofReal_pow]
    ring

/-- **Ellipticity of a differential operator.** On a nonzero space `V`, the classical symbol of
a differential operator `D` of order at most `m` is elliptic exactly when the geometric principal
symbol of `D` vanishes at no nonzero covector. -/
theorem isElliptic_ofDifferentialOperator_iff [Nontrivial V] :
    (ofDifferentialOperator V D).IsElliptic ↔
      ∀ x ξ : CoordinateSpace n, ξ ≠ 0 → smoothPrincipalSymbol 𝓘(ℝ, CoordinateSpace n) (x := x)
        BoundarylessManifold.isInteriorPoint D (innerSL ℝ ξ) ≠ 0 := by
  rw [isElliptic_iff]
  refine forall_congr' fun x ↦ forall_congr' fun ξ ↦ forall_congr' fun hξ ↦ ?_
  rw [coefficient_principal_ofDifferentialOperator D hξ]
  constructor
  · rintro h h0
    rw [h0, Complex.ofReal_zero, mul_zero, zero_smul,
      ContinuousLinearMap.isInvertible_zero_iff] at h
    exact not_subsingleton V h.1
  · intro h
    rw [ContinuousLinearMap.isInvertible_smul_iff (mul_ne_zero (pow_ne_zero _ Complex.I_ne_zero)
      (Complex.ofReal_ne_zero.2 h))]
    simpa using ContinuousLinearMap.isInvertible_equiv (f := ContinuousLinearEquiv.refl ℂ V)

end ClassicalSymbol

end TauCeti
