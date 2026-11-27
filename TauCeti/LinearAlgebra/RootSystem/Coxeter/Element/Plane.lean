/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.LinearAlgebra.RootSystem.Irreducible
public import TauCeti.LinearAlgebra.RootSystem.Chamber
public import TauCeti.LinearAlgebra.RootSystem.Coxeter.Bipartite
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.LinearAlgebra.Eigenspace.Charpoly
import Mathlib.RingTheory.RootsOfUnity.Complex
import TauCeti.GroupTheory.Coxeter.CoxeterElement
import TauCeti.LinearAlgebra.Matrix.PerronFrobenius.Positive
import TauCeti.LinearAlgebra.RootSystem.Coxeter.Element.ActsBy
import TauCeti.LinearAlgebra.RootSystem.Coxeter.Element.BaseChange
import TauCeti.LinearAlgebra.RootSystem.Coxeter.Element.Regular
import TauCeti.LinearAlgebra.RootSystem.Coxeter.FixedPoints
import TauCeti.LinearAlgebra.RootSystem.FiniteType.Irreducible
import TauCeti.LinearAlgebra.RootSystem.FiniteType.Perron
import TauCeti.LinearAlgebra.RootSystem.Weyl.Chamber
import TauCeti.RingTheory.Polynomial.Cyclotomic.Roots

/-!
# The Coxeter plane and the primitive eigenvalue `exp (-2πi / h)`

`TauCeti.LinearAlgebra.RootSystem.Coxeter.Element.Regular` constructs the colour-part action of
the bipartite colour-class products (`RootPairing.colorClassProd_smul_colorPart`), shows that the
bipartite Coxeter element acts by scalar multiplication on `(1 + μ) u₀ + (2 - κ) u₁` for any
quadratic root `μ` (`RootPairing.bipartiteCoxeterElement_smul_one_add_smul_colorPart_add_smul`),
and proves that this vector is regular
(`RootPairing.isRegularWeight_one_add_smul_colorPart_add_smul`) with eigenvalue `μ` a primitive
`h`-th root of unity (`RootPairing.isPrimitiveRoot_bipartiteCoxeterElement_of_quadratic`), where `h`
is the order of the bipartite Coxeter element. However, those results do not identify which
primitive `h`-th root of unity corresponds to the Perron–Frobenius eigenvalue `κ` of the Cartan
matrix.

This file combines that colour-part construction with the Perron–Frobenius spectral bound
(`Matrix.norm_le_of_mulVec_le_smul`) to identify `2 - κ = 2 * Real.cos (π / h)`, and deduces:

## Main results

* `RootPairing.exists_coxeterPlane_bipartite`: over `ℝ`, for a base of rank at least two
  (`[Nontrivial b.support]`), a bipartite Coxeter element `wordProd P b l₁ * wordProd P b l₂`
  admits linearly independent vectors `v₁, v₂` spanning the Coxeter plane, with `v₁ + v₂` in the
  open dominant chamber and dihedral action parameter `2 * Real.cos (Real.pi / h)`.
* `RootPairing.exists_dihedral_colorPart_bipartite`: the same dihedral action formulas without the
  rank-two hypothesis (in rank one, one of `v₁, v₂` vanishes and `2 * Real.cos (Real.pi / 2) = 0`).
* `RootPairing.exists_isRegularWeight_wordProd_smul_eq_inv_exp_smul`: over `ℂ`, every Coxeter
  element `wordProd P b l` admits a regular weight `v` with eigenvalue
  `(Complex.exp (2 * Real.pi * Complex.I / orderOf (wordProd P b l)))⁻¹`.

## References

* R. Steinberg, *Finite reflection groups*, Trans. Amer. Math. Soc. **91** (1959), 493–504.
* A. J. Coleman, *The Betti numbers of the simple Lie groups*, Canad. J. Math. **10** (1958),
  349–356.
* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4–6*, Springer (2002), Ch. V, §6, no. 2.
* J. E. Humphreys, *Reflection Groups and Coxeter Groups*, Cambridge University Press (1990),
  §§3.17–3.18.
-/

public section

open Matrix Polynomial TauCeti

namespace RootPairing

section SpectralHelpers

private lemma one_add_exp_sq_div_exp_eq (h : ℕ) :
    (1 + Complex.exp (2 * Real.pi * Complex.I / h)) ^ 2 /
        Complex.exp (2 * Real.pi * Complex.I / h) =
      (((2 * Real.cos (Real.pi / h)) ^ 2 : ℝ) : ℂ) := by
  set ξ : ℂ := Complex.exp (((Real.pi / h : ℝ) : ℂ) * Complex.I)
  have hω : Complex.exp (2 * Real.pi * Complex.I / h) = ξ ^ 2 := by
    simp only [ξ, sq, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hdiv : (1 + ξ ^ 2) ^ 2 / ξ ^ 2 = (ξ + ξ⁻¹) ^ 2 := by
    field_simp [Complex.exp_ne_zero _]
    ring
  rw [hω, hdiv]
  dsimp only [ξ]
  rw [← Complex.exp_neg, ← neg_mul, ← Complex.two_cos]
  push_cast
  ring

private lemma pi_div_le_of_exp_sq_pow_eq_one {θ : ℝ} {h : ℕ} (hθ_pos : 0 < θ) (hh_pos : 0 < h)
    (hζ_pow : (Complex.exp ((θ : ℂ) * Complex.I) ^ 2) ^ h = 1) : Real.pi / h ≤ θ := by
  have hh_real : (0 : ℝ) < h := Nat.cast_pos.mpr hh_pos
  have hexp1 : Complex.exp (((2 * (h : ℝ) * θ : ℝ) : ℂ) * Complex.I) = 1 := by
    simp only [← Complex.exp_natCast_mul] at hζ_pow
    convert hζ_pow using 2
    push_cast
    ring
  obtain ⟨m, hm⟩ := Complex.exp_eq_one_iff.1 hexp1
  have hre : 2 * (h : ℝ) * θ = (m : ℝ) * (2 * Real.pi) := Complex.ofReal_injective
    (mul_right_cancel₀ Complex.I_ne_zero (by simpa [mul_assoc] using hm))
  have hm_real : (0 : ℝ) < m := by nlinarith [Real.pi_pos, mul_pos hh_real hθ_pos]
  have hm_pos : (0 : ℤ) < m := by exact_mod_cast hm_real
  have hm_one : (1 : ℤ) ≤ m := hm_pos
  have hm_ge : (1 : ℝ) ≤ m := by exact_mod_cast hm_one
  rw [div_le_iff₀ hh_real]
  nlinarith [Real.pi_pos]

private lemma eq_two_mul_cos_pi_div_of_norm_one_add_sq_div_le (lam : ℝ) {h : ℕ}
    (hlam_nonneg : 0 ≤ lam) (hlam_lt : lam < 2) (h2le : 2 ≤ h)
    (hζ_pow : (Complex.exp ((Real.arccos (lam / 2) : ℂ) * Complex.I) ^ 2) ^ h = 1)
    (hbound : ‖(1 + Complex.exp (2 * Real.pi * Complex.I / h)) ^ 2 /
      Complex.exp (2 * Real.pi * Complex.I / h)‖ ≤ lam ^ 2) :
    lam = 2 * Real.cos (Real.pi / h) := by
  set θ : ℝ := Real.arccos (lam / 2)
  have hcosθ : Real.cos θ = lam / 2 := Real.cos_arccos (by linarith) (by linarith)
  have hlam_eq : lam = 2 * Real.cos θ := by linarith
  have hθ_pos : 0 < θ := by
    rw [← Real.arccos_one]
    exact Real.arccos_lt_arccos (by linarith) (by linarith) le_rfl
  have hθ_le : θ ≤ Real.pi / 2 := by
    rw [← Real.arccos_zero]
    exact Real.arccos_le_arccos (by linarith : (0 : ℝ) ≤ lam / 2)
  rw [one_add_exp_sq_div_exp_eq h, Complex.norm_real, Real.norm_of_nonneg (sq_nonneg _)] at hbound
  have hh_pos : 0 < h := lt_of_lt_of_le (by norm_num) h2le
  have hh_real : (0 : ℝ) < h := Nat.cast_pos.mpr hh_pos
  have hpi_le_θ : Real.pi / h ≤ θ := pi_div_le_of_exp_sq_pow_eq_one hθ_pos hh_pos hζ_pow
  have hcos_le : Real.cos (Real.pi / h) ≤ Real.cos θ := by
    have hcos_nonneg_pi : 0 ≤ Real.cos (Real.pi / h) := by
      refine Real.cos_nonneg_of_mem_Icc
        ⟨by linarith [Real.pi_pos, div_nonneg Real.pi_pos.le hh_real.le], ?_⟩
      have h2 : (2 : ℝ) ≤ h := by exact_mod_cast h2le
      rw [div_le_div_iff₀ hh_real (by norm_num)]
      nlinarith [Real.pi_pos]
    have : Real.cos (Real.pi / h) ^ 2 ≤ Real.cos θ ^ 2 := by
      rw [hlam_eq] at hbound
      nlinarith
    nlinarith
  have hcos_ge : Real.cos θ ≤ Real.cos (Real.pi / h) := Real.strictAntiOn_cos.antitoneOn
    ⟨by positivity, le_trans hpi_le_θ (le_trans hθ_le (by linarith [Real.pi_pos]))⟩
    ⟨hθ_pos.le, le_trans hθ_le (by linarith [Real.pi_pos])⟩ hpi_le_θ
  linarith [le_antisymm hcos_ge hcos_le]

private lemma mulVec_sq_map_of_bipartite_mulVec_eq_smul {n : Type*} [Fintype n]
    (A : Matrix n n ℝ) {M₁ M₂ : Matrix n n ℂ} {col : n → Bool}
    (hA_same : ∀ i j, col i = col j → A i j = 0)
    (hM₁_mul : ∀ (z : n → ℂ) (i : n), (M₁ *ᵥ z) i = if col i = true then
        -z i + ∑ j : n, (if col j = false then (A i j : ℂ) * z j else 0) else z i)
    (hM₂_mul : ∀ (z : n → ℂ) (i : n), (M₂ *ᵥ z) i = if col i = false then
        -z i + ∑ j : n, (if col j = true then (A i j : ℂ) * z j else 0) else z i)
    {ω : ℂ} {z : n → ℂ} (hω : ω ≠ 0) (heig : (M₁ * M₂) *ᵥ z = ω • z) :
    (A * A).map Complex.ofReal *ᵥ z = ((1 + ω) ^ 2 / ω) • z := by
  classical
  set AC : Matrix n n ℂ := A.map Complex.ofReal
  -- Step 1: `M₁` is an involution (`M₁² = 1`), so `(M₁ * M₂) z = ω z` yields `M₂ z = ω M₁ z`.
  have hM₁_invol : ∀ y : n → ℂ, M₁ *ᵥ (M₁ *ᵥ y) = y := fun y ↦ by
    ext i
    rw [hM₁_mul]
    cases hci : col i
    · simp [hM₁_mul, hci]
    · have hsum : (∑ j : n, if col j = false then (A i j : ℂ) * (M₁ *ᵥ y) j else 0) =
          ∑ j : n, if col j = false then (A i j : ℂ) * y j else 0 :=
        Finset.sum_congr rfl fun j _ ↦ by
          split_ifs with hcj
          · simp [hM₁_mul, hcj]
          · rfl
      rw [hM₁_mul]
      simp only [hci, ite_true, hsum]
      ring
  have hM₂_eq : M₂ *ᵥ z = ω • (M₁ *ᵥ z) := by
    have h1 := congrArg (M₁ *ᵥ ·) heig
    rwa [← mulVec_mulVec, hM₁_invol, mulVec_smul] at h1
  -- Step 2: Split `z = z₁ + z₂` by colour; `M₂ z = ω M₁ z` decouples into two equations
  -- `(1 + ω) z₁ = ω A z₂` and `A z₁ = (1 + ω) z₂`.
  set z₁ : n → ℂ := fun i ↦ if col i = true then z i else 0
  set z₂ : n → ℂ := fun i ↦ if col i = false then z i else 0
  have hz_split : z = z₁ + z₂ := by
    ext i
    simp only [z₁, z₂, Pi.add_apply]
    cases col i <;> simp
  have hAz_color (b0 : Bool) (i : n) :
      (AC *ᵥ fun j ↦ if col j = b0 then z j else 0) i = if col i = !b0 then
        ∑ j : n, (if col j = b0 then (A i j : ℂ) * z j else 0) else 0 := by
    simp only [mulVec, dotProduct, AC, Matrix.map_apply]
    split_ifs with hci
    · exact Finset.sum_congr rfl fun j _ ↦ by split_ifs <;> simp
    · have hsame : col i = b0 := by cases h1 : col i <;> cases b0 <;> simp_all
      exact Finset.sum_eq_zero fun j _ ↦ by
        split_ifs with hcj
        · simp [hA_same i j (hsame.trans hcj.symm)]
        · simp
  have heq₁ : (1 + ω) • z₁ = ω • (AC *ᵥ z₂) := by
    ext i
    have hi := congrFun hM₂_eq i
    have hAz := hAz_color false i
    simp only [Bool.not_false, z₁, z₂, Pi.smul_apply, smul_eq_mul, hM₂_mul, hM₁_mul] at hi hAz ⊢
    rw [hAz]
    cases hci : col i <;> simp [hci] at hi ⊢
    linear_combination hi
  have heq₂ : AC *ᵥ z₁ = (1 + ω) • z₂ := by
    ext i
    have hi := congrFun hM₂_eq i
    have hAz := hAz_color true i
    simp only [Bool.not_true, z₁, z₂, Pi.smul_apply, smul_eq_mul, hM₂_mul, hM₁_mul] at hi hAz ⊢
    rw [hAz]
    cases hci : col i <;> simp [hci] at hi ⊢
    linear_combination hi
  -- Step 3: Compose the two colour equations to get `ω A² z = (1 + ω)² z` and divide by `ω`.
  have h1 : ω • (AC *ᵥ (AC *ᵥ z₁)) = (1 + ω) ^ 2 • z₁ := by
    rw [heq₂, mulVec_smul, smul_comm, ← heq₁, smul_smul, sq]
  have h2 : ω • (AC *ᵥ (AC *ᵥ z₂)) = (1 + ω) ^ 2 • z₂ := by
    have := congrArg (AC *ᵥ ·) heq₁
    rw [mulVec_smul, mulVec_smul, heq₂, smul_smul, ← sq] at this
    exact this.symm
  have hsum : ω • ((AC * AC) *ᵥ z) = (1 + ω) ^ 2 • z := by
    rw [hz_split, mulVec_add, ← mulVec_mulVec, ← mulVec_mulVec, smul_add, h1, h2, ← smul_add]
  have hA2_map : (A * A).map Complex.ofReal = AC * AC := by
    ext i j
    simp [AC, Matrix.mul_apply]
  rw [hA2_map]
  ext i
  have hi := congrFun hsum i
  simp only [Pi.smul_apply, smul_eq_mul] at hi ⊢
  exact mul_left_cancel₀ hω (by rw [hi]; field_simp [hω])

private lemma norm_one_add_sq_div_le_sq_of_mulVec_eq_smul {n : Type*} [Fintype n]
    (A : Matrix n n ℝ) {M₁ M₂ : Matrix n n ℂ} {col : n → Bool} {a : n → ℝ} {r : ℝ}
    (hA_nonneg : ∀ i j, 0 ≤ A i j) (hA_same : ∀ i j, col i = col j → A i j = 0)
    (ha_pos : ∀ i, 0 < a i) (ha_eig : A *ᵥ a = r • a)
    (hM₁_mul : ∀ (z : n → ℂ) (i : n), (M₁ *ᵥ z) i = if col i = true then
        -z i + ∑ j : n, (if col j = false then (A i j : ℂ) * z j else 0) else z i)
    (hM₂_mul : ∀ (z : n → ℂ) (i : n), (M₂ *ᵥ z) i = if col i = false then
        -z i + ∑ j : n, (if col j = true then (A i j : ℂ) * z j else 0) else z i)
    {ω : ℂ} {z : n → ℂ} (hω : ω ≠ 0) (hz : z ≠ 0) (heig : (M₁ * M₂) *ᵥ z = ω • z) :
    ‖(1 + ω) ^ 2 / ω‖ ≤ r ^ 2 := by
  have hA2_eig := mulVec_sq_map_of_bipartite_mulVec_eq_smul A hA_same hM₁_mul hM₂_mul hω heig
  have hA2_nonneg : ∀ i j, 0 ≤ (A * A) i j := fun i j ↦ by
    rw [Matrix.mul_apply]
    exact Finset.sum_nonneg fun k _ ↦ mul_nonneg (hA_nonneg i k) (hA_nonneg k j)
  exact norm_le_of_mulVec_le_smul hA2_nonneg ha_pos
    (le_of_eq (by rw [← mulVec_mulVec, ha_eig, mulVec_smul, ha_eig, smul_smul, sq]))
    hz hA2_eig

/-- If `c = 2 * Real.cos t`, both `exp (2 * t * I)` and `(exp (2 * t * I))⁻¹` satisfy the quadratic
`w ^ 2 + (2 - c ^ 2) * w + 1 = 0`. -/
private lemma exp_pm_two_mul_I_quad {c t : ℝ} (hc : c = 2 * Real.cos t) :
    let ζ : ℂ := Complex.exp (2 * (t : ℂ) * Complex.I)
    (ζ ^ 2 + (2 - algebraMap ℝ ℂ c ^ 2) * ζ + 1 = 0) ∧
      ((ζ⁻¹) ^ 2 + (2 - algebraMap ℝ ℂ c ^ 2) * ζ⁻¹ + 1 = 0) := by
  let μ : ℂ := Complex.exp ((t : ℂ) * Complex.I)
  have hμ_ne : μ ≠ 0 := Complex.exp_ne_zero _
  have hμ_sum : μ + μ⁻¹ = (c : ℂ) := by
    rw [show μ⁻¹ = Complex.exp (-(t : ℂ) * Complex.I) by
      simp [μ, ← Complex.exp_neg, neg_mul], ← Complex.two_cos, ← Complex.ofReal_cos, hc]
    push_cast; ring
  have hζ_eq : Complex.exp (2 * (t : ℂ) * Complex.I) = μ ^ 2 := by
    simp only [μ, sq, ← Complex.exp_add]; congr 1; ring
  have hζ_ne : μ ^ 2 ≠ 0 := pow_ne_zero 2 hμ_ne
  have hsum : μ ^ 2 + (μ ^ 2)⁻¹ = algebraMap ℝ ℂ c ^ 2 - 2 := by
    have h1 : μ ^ 2 + (μ⁻¹) ^ 2 = (μ + μ⁻¹) ^ 2 - 2 := by field_simp [hμ_ne]; ring
    rw [hμ_sum] at h1
    simpa [inv_pow, Complex.coe_algebraMap] using h1
  rw [hζ_eq]
  refine ⟨?_, ?_⟩
  · have h := congrArg (· * μ ^ 2) hsum
    rw [add_mul, inv_mul_cancel₀ hζ_ne, ← sq] at h
    linear_combination h
  · have h := congrArg (· * (μ ^ 2)⁻¹) hsum
    rw [add_mul, mul_inv_cancel₀ hζ_ne, ← sq] at h
    linear_combination h

private lemma wordProd_eq_colorClassProd_of_mem_iff
    {ι K M N : Type*} [Field K] [CharZero K] [AddCommGroup M] [Module K M]
    [AddCommGroup N] [Module K N] (P : RootPairing ι K M N) [Finite ι]
    [P.IsCrystallographic] [P.IsReduced] (b : P.Base)
    (col : (coxeterMatrixOfBase P b).graph.Coloring Bool)
    (x : Bool) {l : List b.support} (hl : l.Nodup) (hcol : ∀ i : b.support, i ∈ l ↔ col i = x) :
    wordProd P b l = (weylCoxeterSystem P b).colorClassProd col x := by
  rw [← weylCoxeterSystem_wordProd P b l]
  exact (weylCoxeterSystem P b).wordProd_eq_colorClassProd col hl hcol

private noncomputable def coloringBaseChangeRat
    {ι K M N : Type*} [Field K] [CharZero K] [AddCommGroup M] [Module K M]
    [AddCommGroup N] [Module K N] (P : RootPairing ι K M N) [Finite ι]
    [P.IsCrystallographic] [P.IsRootSystem] (b : P.Base)
    (col : (coxeterMatrixOfBase P b).graph.Coloring Bool) :
    (coxeterMatrixOfBase
      (rootPairingBaseChange ℂ b.rationalModel b.rationalModel_toLinearMap)
      (rootPairingBaseChangeBase ℂ b.rationalModel b.rationalModel_toLinearMap
        b.rationalModelBase)).graph.Coloring Bool :=
  SimpleGraph.Coloring.mk
    (fun i ↦ col (b.supportEquivRootPairingBaseChangeRationalModel ℂ i)) fun {i j} hadj ↦ by
    rw [graph_coxeterMatrixOfBase, diagramGraph_adj] at hadj
    have h1 := b.cartanMatrix_rootPairingBaseChangeRationalModel ℂ i j
    have h2 := b.cartanMatrix_rootPairingBaseChangeRationalModel ℂ j i
    exact col.valid (by
      rw [graph_coxeterMatrixOfBase, diagramGraph_adj]
      exact ⟨(b.supportEquivRootPairingBaseChangeRationalModel ℂ).injective.ne hadj.1,
        h1 ▸ hadj.2.1, h2 ▸ hadj.2.2⟩)

@[simp]
private lemma coloringBaseChangeRat_apply
    {ι K M N : Type*} [Field K] [CharZero K] [AddCommGroup M] [Module K M]
    [AddCommGroup N] [Module K N] (P : RootPairing ι K M N) [Finite ι]
    [P.IsCrystallographic] [P.IsRootSystem] (b : P.Base)
    (col : (coxeterMatrixOfBase P b).graph.Coloring Bool)
    (i : (rootPairingBaseChangeBase ℂ b.rationalModel b.rationalModel_toLinearMap
      b.rationalModelBase).support) :
    coloringBaseChangeRat P b col i =
      col (b.supportEquivRootPairingBaseChangeRationalModel ℂ i) := rfl

private lemma wordProd_mul_wordProd_eq_bipartiteCoxeterElement
    {ι K M N : Type*} [Field K] [CharZero K] [AddCommGroup M] [Module K M]
    [AddCommGroup N] [Module K N] (P : RootPairing ι K M N) [Finite ι]
    [P.IsCrystallographic] [P.IsReduced] (b : P.Base)
    (col : (coxeterMatrixOfBase P b).graph.Coloring Bool)
    {l₁ l₂ : List b.support} (hl₁ : l₁.Nodup) (hl₂ : l₂.Nodup)
    (hcol₁ : ∀ i : b.support, i ∈ l₁ ↔ col i = true)
    (hcol₂ : ∀ i : b.support, i ∈ l₂ ↔ col i = false) :
    wordProd P b l₁ * wordProd P b l₂ =
      (weylCoxeterSystem P b).bipartiteCoxeterElement col := by
  rw [wordProd_eq_colorClassProd_of_mem_iff P b col true hl₁ hcol₁,
    wordProd_eq_colorClassProd_of_mem_iff P b col false hl₂ hcol₂,
    CoxeterSystem.bipartiteCoxeterElement_def]

private lemma bipartiteCoxeterElement_coloringBaseChangeRat
    {ι K M N : Type*} [Field K] [CharZero K] [AddCommGroup M] [Module K M]
    [AddCommGroup N] [Module K N] (P : RootPairing ι K M N) [Finite ι]
    [P.IsCrystallographic] [P.IsReduced] [P.IsRootSystem] (b : P.Base)
    (col : (coxeterMatrixOfBase P b).graph.Coloring Bool)
    {l₁ l₂ : List b.support} (hl₁ : l₁.Nodup) (hl₂ : l₂.Nodup)
    (hmem₁ : ∀ i : b.support, i ∈ l₁ ↔ col i = true)
    (hmem₂ : ∀ i : b.support, i ∈ l₂ ↔ col i = false) :
    (weylCoxeterSystem
        (rootPairingBaseChange ℂ b.rationalModel b.rationalModel_toLinearMap)
        (rootPairingBaseChangeBase ℂ b.rationalModel b.rationalModel_toLinearMap
          b.rationalModelBase)).bipartiteCoxeterElement (coloringBaseChangeRat P b col) =
      wordProd (rootPairingBaseChange ℂ b.rationalModel b.rationalModel_toLinearMap)
        (rootPairingBaseChangeBase ℂ b.rationalModel b.rationalModel_toLinearMap
          b.rationalModelBase)
        ((l₁ ++ l₂).map (b.supportEquivRootPairingBaseChangeRationalModel ℂ).symm) := by
  let PC := rootPairingBaseChange ℂ b.rationalModel b.rationalModel_toLinearMap
  let bC := rootPairingBaseChangeBase ℂ b.rationalModel b.rationalModel_toLinearMap
    b.rationalModelBase
  let eCB := b.supportEquivRootPairingBaseChangeRationalModel ℂ
  have hl₁C : (l₁.map eCB.symm).Nodup := hl₁.map eCB.symm.injective
  have hl₂C : (l₂.map eCB.symm).Nodup := hl₂.map eCB.symm.injective
  have hmemC (x : Bool) {l : List b.support} (hlx : ∀ j, j ∈ l ↔ col j = x) (i : bC.support) :
      i ∈ l.map eCB.symm ↔ coloringBaseChangeRat P b col i = x := by
    rw [b.mem_map_supportEquivRootPairingBaseChangeRationalModel_symm_iff ℂ,
      coloringBaseChangeRat_apply, hlx]
  rw [CoxeterSystem.bipartiteCoxeterElement_def,
    ← wordProd_eq_colorClassProd_of_mem_iff PC bC (coloringBaseChangeRat P b col) true hl₁C
      (hmemC true hmem₁),
    ← wordProd_eq_colorClassProd_of_mem_iff PC bC (coloringBaseChangeRat P b col) false hl₂C
      (hmemC false hmem₂),
    List.map_append, wordProd_append]

open Classical in
/-- Matrix entry of the integer matrix `W` representing a colour-class product
`colorClassProd col b0`, expressed via the non-negative adjacency matrix
`A i j = -(b.cartanMatrix j i : ℝ)` (`i ≠ j`). -/
private lemma colorClassProd_matrix_entry
    {ι K M N : Type*} [Field K] [CharZero K] [AddCommGroup M] [Module K M]
    [AddCommGroup N] [Module K N] (P : RootPairing ι K M N) [Finite ι]
    [P.IsCrystallographic] [P.IsReduced] [P.IsRootSystem] (b : P.Base)
    (col : (coxeterMatrixOfBase P b).graph.Coloring Bool)
    (A : Matrix b.support b.support ℝ)
    (hA : ∀ i j : b.support, A i j = if i = j then 0 else -(b.cartanMatrix j i : ℝ))
    (b0 : Bool) {W : Matrix b.support b.support ℤ}
    (hW : b.ActsBy ((weylCoxeterSystem P b).colorClassProd col b0) W)
    (i j : b.support) :
    (W i j : ℂ) = if col i = b0 then
        if i = j then (-1 : ℂ) else if col j = !b0 then (A i j : ℂ) else 0
      else if i = j then 1 else 0 := by
  have hact := congrArg (fun m ↦ b.toWeightBasis.repr m i) (Base.actsBy_iff.1 hW j)
  have hlhs : b.toWeightBasis.repr
      ((weylCoxeterSystem P b).colorClassProd col b0 • P.root j) i =
      (if i = j then 1 else 0) - if col i = b0 then P.coroot' i (P.root j) else 0 := by
    rw [colorClassProd_smul, map_sub, map_sum, Finsupp.sub_apply, Finset.sum_apply',
      b.toWeightBasis_repr_root, Finsupp.single_apply]
    congr 1
    · simp only [eq_comm]
    · rw [Finset.sum_eq_single i (fun k _ hki ↦ by
          by_cases hck : col k = b0
          · simp [hck, b.toWeightBasis_repr_root, hki]
          · simp [hck])
        (by simp)]
      by_cases hci : col i = b0
      · simp [hci, b.toWeightBasis_repr_root]
      · simp [hci]
  have hrhs : b.toWeightBasis.repr (∑ k : b.support, W k j • P.root k) i = (W i j : K) := by
    simp [b.toWeightBasis_repr_root, Finsupp.single_apply, eq_comm]
  rw [hlhs, hrhs] at hact
  by_cases hci : col i = b0
  · rw [ite_eq_left hci] at hact; rw [ite_eq_left hci]
    by_cases hij : i = j
    · subst hij
      rw [ite_eq_left rfl, P.root_coroot'_eq_pairing, P.pairing_same] at hact
      have hW_int : W i i = -1 :=
        Int.cast_injective (α := K) (by push_cast; linear_combination hact.symm)
      simp [hW_int]
    · rw [ite_eq_right hij] at hact ⊢
      rw [P.root_coroot'_eq_pairing, ← P.algebraMap_pairingIn ℤ] at hact
      have hW_int : W i j = -b.cartanMatrix j i :=
        Int.cast_injective (α := K)
          (by push_cast; simpa [Base.cartanMatrix, Base.cartanMatrixIn_def] using hact.symm)
      by_cases hcj : col j = !b0
      · simp [hcj, hW_int, hA i j, hij]
      · have hsame : col j = col i := by cases h1 : col j <;> cases b0 <;> simp_all
        have h0 : b.cartanMatrix j i = 0 := by
          simpa [Base.cartanMatrix, Base.cartanMatrixIn_def] using
            pairingIn_eq_zero_of_color_eq P b col (Ne.symm hij) hsame
        simp [hcj, hW_int, h0]
  · rw [ite_eq_right hci] at hact ⊢
    by_cases hij : i = j
    · subst hij; rw [ite_eq_left rfl, sub_zero] at hact
      have hW_int : W i i = 1 := Int.cast_injective (α := K) (by push_cast; exact hact.symm)
      simp [hW_int]
    · rw [ite_eq_right hij, sub_zero] at hact
      have hW_int : W i j = 0 := Int.cast_injective (α := K) (by push_cast; exact hact.symm)
      simp [hij, hW_int]

open Classical in
/-- Matrix-vector action of a colour-class product `colorClassProd col b0` on `b.support → ℂ`
in terms of the non-negative adjacency matrix `A i j = -(b.cartanMatrix j i : ℝ)` (`i ≠ j`). -/
private lemma colorClassProd_matrix_mulVec
    {ι K M N : Type*} [Field K] [CharZero K] [AddCommGroup M] [Module K M]
    [AddCommGroup N] [Module K N] (P : RootPairing ι K M N) [Finite ι]
    [P.IsCrystallographic] [P.IsReduced] [P.IsRootSystem] (b : P.Base)
    (col : (coxeterMatrixOfBase P b).graph.Coloring Bool)
    (A : Matrix b.support b.support ℝ)
    (hA : ∀ i j : b.support, A i j = if i = j then 0 else -(b.cartanMatrix j i : ℝ))
    (b0 : Bool) {W : Matrix b.support b.support ℤ}
    (hW : b.ActsBy ((weylCoxeterSystem P b).colorClassProd col b0) W)
    (z : b.support → ℂ) (i : b.support) :
    (W.map (algebraMap ℤ ℂ) *ᵥ z) i = if col i = b0 then
        -z i + ∑ j : b.support, (if col j = !b0 then (A i j : ℂ) * z j else 0)
      else z i := by
  simp only [mulVec, dotProduct, Matrix.map_apply, eq_intCast]
  by_cases hci : col i = b0
  · rw [ite_eq_left hci]
    trans ∑ j : b.support,
        ((if i = j then -z i else 0) + (if col j = !b0 then (A i j : ℂ) * z j else 0))
    · refine Finset.sum_congr rfl fun j _ ↦ ?_
      rw [colorClassProd_matrix_entry P b col A hA b0 hW i j, ite_eq_left hci]
      by_cases hij : i = j
      · subst hij; simp [hci]
      · by_cases hcj : col j = !b0 <;> simp [hij, hcj]
    · simp [Finset.sum_add_distrib]
  · rw [ite_eq_right hci, Finset.sum_eq_single i (fun j _ hij ↦ by
        rw [colorClassProd_matrix_entry P b col A hA b0 hW i j,
          ite_eq_right hci, ite_eq_right hij.symm, zero_mul]) (by simp),
      colorClassProd_matrix_entry P b col A hA b0 hW i i, ite_eq_right hci, ite_eq_left rfl,
      one_mul]

open Classical in
/-- Properties of the off-diagonal negated Cartan matrix `A i j = -(b.cartanMatrix j i : ℝ)`
(`i ≠ j`): non-negativity, vanishing on same-colour pairs, and `A *ᵥ y = (2 - κ) • y` for a
`κ`-left-eigenvector `y` of `P.pairingIn ℤ`. -/
private lemma offDiagNegCartanMatrix_spec
    {ι K M N : Type*} [Field K] [CharZero K] [AddCommGroup M] [Module K M]
    [AddCommGroup N] [Module K N] (P : RootPairing ι K M N) [Finite ι]
    [P.IsCrystallographic] (b : P.Base)
    (col : (coxeterMatrixOfBase P b).graph.Coloring Bool)
    {κ : ℝ} {y : b.support → ℝ}
    (hy : ∀ j : b.support, ∑ i : b.support, y i * P.pairingIn ℤ i j = κ * y j) :
    let A : Matrix b.support b.support ℝ :=
      fun i j ↦ if i = j then 0 else -(b.cartanMatrix j i : ℝ)
    (∀ i j, 0 ≤ A i j) ∧ (∀ i j, col i = col j → A i j = 0) ∧ A *ᵥ y = (2 - κ) • y := by
  let := Fintype.ofFinite ι
  intro A
  refine ⟨fun i j ↦ ?_, fun i j hsame ↦ ?_, ?_⟩
  · by_cases hij : i = j
    · simp [A, hij]
    · simp only [A, ite_eq_right hij, neg_nonneg]
      exact_mod_cast b.cartanMatrix_le_zero_of_ne j i (Ne.symm hij)
  · by_cases hij : i = j
    · simp [A, hij]
    · dsimp only [A, Base.cartanMatrix]
      rw [ite_eq_right hij, Base.cartanMatrixIn_def,
        pairingIn_eq_zero_of_color_eq P b col (Ne.symm hij) hsame.symm, Int.cast_zero, neg_zero]
  · ext i
    simp only [mulVec, dotProduct, Pi.smul_apply, smul_eq_mul, A]
    have h2 : ∑ j : b.support, (if i = j then (b.cartanMatrix j i : ℝ) else 0) * y j =
        2 * y i := by
      rw [Finset.sum_eq_single i (fun j _ hj ↦ by simp [hj.symm]) (by simp), ite_eq_left rfl,
        b.cartanMatrix_apply_same i]
      norm_num
    have hsum : ∑ j : b.support, (if i = j then 0 else -(b.cartanMatrix j i : ℝ)) * y j =
        2 * y i - ∑ j : b.support, y j * (b.cartanMatrix j i : ℝ) := by
      rw [← h2, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun j _ ↦ by by_cases hij : i = j <;> simp [hij, mul_comm]
    rw [hsum, show ∑ j : b.support, y j * (b.cartanMatrix j i : ℝ) = κ * y i from hy i]
    ring

/-- Identifying the Perron–Frobenius dihedral parameter `2 - κ` with `2 cos (π / h)`, where `h`
is the order of the bipartite Coxeter element, shared between the real Coxeter plane and complex
regular-eigenvector constructions. -/
private lemma two_sub_eq_two_mul_cos_pi_div_orderOf_bipartiteCoxeterElement
    {ι K M N : Type*} [Field K] [CharZero K]
    [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]
    (P : RootPairing ι K M N) [Finite ι] [P.IsCrystallographic] [P.IsReduced] [P.IsRootSystem]
    (b : P.Base) [Nontrivial b.support]
    (col : (coxeterMatrixOfBase P b).graph.Coloring Bool)
    {κ : ℝ} {y : b.support → ℝ}
    (hy : ∀ j : b.support, ∑ i : b.support, y i * P.pairingIn ℤ i j = κ * y j)
    (hy0 : ∀ i, 0 < y i) (hκ : 0 < κ) (hκ2 : κ < 2) :
    2 - κ = 2 * Real.cos
      (Real.pi / orderOf ((weylCoxeterSystem P b).bipartiteCoxeterElement col)) := by
  classical
  let := Fintype.ofFinite ι
  have : Nonempty ι := ⟨(Classical.arbitrary b.support : ι)⟩
  have : Nontrivial M := b.toWeightBasis.equivFun.symm.injective.nontrivial
  -- Phase 1: Bipartite decomposition and Coxeter-element order lower bound `2 ≤ h`.
  obtain ⟨l₁, l₂, hcol₁, hcol₂, hl_nodup, hl_all, hl_eq⟩ :=
    (weylCoxeterSystem P b).exists_wordProd_eq_bipartiteCoxeterElement col
  have hmem₁ (i : b.support) : i ∈ l₁ ↔ col i = true :=
    ⟨hcol₁ i, fun hi ↦ (List.mem_append.1 (hl_all i)).resolve_right fun h2 ↦ by
      simp [hcol₂ i h2] at hi⟩
  have hmem₂ (i : b.support) : i ∈ l₂ ↔ col i = false :=
    ⟨hcol₂ i, fun hi ↦ (List.mem_append.1 (hl_all i)).resolve_left fun h1 ↦ by
      simp [hcol₁ i h1] at hi⟩
  have hl₁ : l₁.Nodup := (List.nodup_append.1 hl_nodup).1
  have hl₂ : l₂.Nodup := (List.nodup_append.1 hl_nodup).2.1
  set c₁ := (weylCoxeterSystem P b).colorClassProd col true
  set c₂ := (weylCoxeterSystem P b).colorClassProd col false
  set c := (weylCoxeterSystem P b).bipartiteCoxeterElement col
  have hc₁_eq : wordProd P b l₁ = c₁ := wordProd_eq_colorClassProd_of_mem_iff P b col true hl₁ hmem₁
  have hc₂_eq : wordProd P b l₂ = c₂ :=
    wordProd_eq_colorClassProd_of_mem_iff P b col false hl₂ hmem₂
  have hc_eq : wordProd P b (l₁ ++ l₂) = c := by
    rw [← weylCoxeterSystem_wordProd]; exact hl_eq
  set h : ℕ := orderOf c
  have h2le : 2 ≤ h := by dsimp [h]; rw [← hc_eq]; exact P.two_le_orderOf_wordProd b hl_nodup hl_all
  have hh_pos : 0 < h := by omega
  -- Phase 2: Angle `θ = arccos ((2 - κ) / 2)` and quadratic equation for `ζ⁻¹ = exp(-2iθ)`.
  set lam : ℝ := 2 - κ
  have hlam_nonneg : 0 ≤ lam := by linarith
  have hlam_lt : lam < 2 := by linarith
  set θ : ℝ := Real.arccos (lam / 2)
  have hlam_cos : lam = 2 * Real.cos θ := by
    linarith [Real.cos_arccos (by linarith : (-1 : ℝ) ≤ lam / 2) (by linarith : lam / 2 ≤ 1)]
  set ζ : ℂ := Complex.exp (2 * (θ : ℂ) * Complex.I)
  have hζ_sq : Complex.exp ((θ : ℂ) * Complex.I) ^ 2 = ζ := by
    simp only [ζ, sq, ← Complex.exp_add]; congr 1; ring
  have hζinv_quad : (ζ⁻¹) ^ 2 + (2 - algebraMap ℝ ℂ (2 - κ) ^ 2) * ζ⁻¹ + 1 = 0 :=
    (exp_pm_two_mul_I_quad hlam_cos).2
  -- Phase 3: Transport to `rootPairingBaseChange ℂ b.rationalModel` to invoke `Regular.lean`.
  let PC := rootPairingBaseChange ℂ b.rationalModel b.rationalModel_toLinearMap
  let bC := rootPairingBaseChangeBase ℂ b.rationalModel b.rationalModel_toLinearMap
    b.rationalModelBase
  let eCB := b.supportEquivRootPairingBaseChangeRationalModel ℂ
  let colC := coloringBaseChangeRat P b col
  let yC : bC.support → ℝ := fun i ↦ y (eCB i)
  have hyC0 : ∀ i, 0 < yC i := fun i ↦ hy0 (eCB i)
  have hyC (j : bC.support) : ∑ i : bC.support, yC i * PC.pairingIn ℤ i j = κ * yC j := by
    have hpair (i : bC.support) : PC.pairingIn ℤ i j = P.pairingIn ℤ (eCB i) (eCB j) :=
      b.cartanMatrix_rootPairingBaseChangeRationalModel ℂ i j
    simp_rw [yC, hpair]
    exact (Fintype.sum_equiv eCB _ _ fun _ ↦ rfl).trans (hy (eCB j))
  have hcolC_word :=
    bipartiteCoxeterElement_coloringBaseChangeRat P b col hl₁ hl₂ hmem₁ hmem₂
  have hordC : orderOf ((weylCoxeterSystem PC bC).bipartiteCoxeterElement colC) = h := by
    dsimp only [h]
    rw [hcolC_word, ← b.orderOf_wordProd_rootPairingBaseChange_rationalModel ℂ (l₁ ++ l₂), hc_eq]
  have hζinv_prim : IsPrimitiveRoot ζ⁻¹ h :=
    hordC ▸ PC.isPrimitiveRoot_bipartiteCoxeterElement_of_quadratic hyC hyC0 hκ hκ2 hζinv_quad
  have hζ_prim : IsPrimitiveRoot ζ h := by simpa using hζinv_prim.inv
  -- Phase 4: Transfer the root `ζ⁻¹` of `charpoly` to `ω₀ = exp (2πi / h)` and apply Perron bound.
  set W₁ : Matrix b.support b.support ℤ := (l₁.map (reflMatrix b.cartanMatrix)).prod
  set W₂ : Matrix b.support b.support ℤ := (l₂.map (reflMatrix b.cartanMatrix)).prod
  have hW_word : W₁ * W₂ = ((l₁ ++ l₂).map (reflMatrix b.cartanMatrix)).prod := by
    simp [W₁, W₂]
  set p : ℚ[X] := ((W₁ * W₂).map (Int.castRingHom ℚ)).charpoly
  have hp_PC : p.map (algebraMap ℚ ℂ) =
      (PC.weylGroupRootRep ((weylCoxeterSystem PC bC).bipartiteCoxeterElement colC)).charpoly := by
    dsimp only [p]
    rw [hcolC_word,
      ← b.charpoly_weylGroupRootRep_wordProd_rootPairingBaseChange_rationalModel ℂ (l₁ ++ l₂),
      hW_word]
  have hζinv_root : (p.map (algebraMap ℚ ℂ)).IsRoot ζ⁻¹ := by
    rw [hp_PC, ← Module.End.hasEigenvalue_iff_isRoot_charpoly]
    have hreg := PC.isRegularWeight_one_add_smul_colorPart_add_smul (c := colC) hyC hyC0 hκ hκ2
      hζinv_quad
    have heig := PC.bipartiteCoxeterElement_smul_one_add_smul_colorPart_add_smul (c := colC)
      hyC hζinv_quad
    exact Module.End.hasEigenvalue_of_hasEigenvector (Module.End.hasEigenvector_iff.2
      ⟨Module.End.mem_eigenspace_iff.2 (by rw [weylGroupRootRep_apply]; exact heig), hreg.ne_zero⟩)
  set ω₀ : ℂ := Complex.exp (2 * Real.pi * Complex.I / h)
  have hω₀_prim : IsPrimitiveRoot ω₀ h := Complex.isPrimitiveRoot_exp h hh_pos.ne'
  have hω₀_root_p : (p.map (algebraMap ℚ ℂ)).IsRoot ω₀ :=
    hζinv_prim.isRoot_map_of_isRoot_map hh_pos hω₀_prim hζinv_root
  set M₁C : Matrix b.support b.support ℂ := W₁.map (algebraMap ℤ ℂ)
  set M₂C : Matrix b.support b.support ℂ := W₂.map (algebraMap ℤ ℂ)
  have hM_mul_map : M₁C * M₂C = (W₁ * W₂).map (algebraMap ℤ ℂ) := by
    dsimp only [M₁C, M₂C]; rw [← Matrix.map_mul]
  have hp_M : p.map (algebraMap ℚ ℂ) = (M₁C * M₂C).charpoly := by
    dsimp only [p]
    rw [hM_mul_map, Matrix.charpoly_map, Matrix.charpoly_map, Polynomial.map_map]
    congr 1
  rw [hp_M, ← Matrix.charpoly_toLin' (M₁C * M₂C),
    ← Module.End.hasEigenvalue_iff_isRoot_charpoly] at hω₀_root_p
  obtain ⟨z, hz⟩ := hω₀_root_p.exists_hasEigenvector
  -- Phase 5: Combine with the off-diagonal negated Cartan matrix `A` for the spectral bound.
  set A : Matrix b.support b.support ℝ :=
    fun i j ↦ if i = j then 0 else -(b.cartanMatrix j i : ℝ)
  obtain ⟨hA_nonneg, hA_same, hA_eig⟩ := offDiagNegCartanMatrix_spec P b col hy
  have hW₁_acts : b.ActsBy c₁ W₁ := hc₁_eq ▸ b.actsBy_wordProd l₁
  have hW₂_acts : b.ActsBy c₂ W₂ := hc₂_eq ▸ b.actsBy_wordProd l₂
  have hM₁C_mul := colorClassProd_matrix_mulVec P b col A (fun _ _ ↦ rfl) true hW₁_acts
  have hM₂C_mul := colorClassProd_matrix_mulVec P b col A (fun _ _ ↦ rfl) false hW₂_acts
  simp only [Bool.not_true, Bool.not_false] at hM₁C_mul hM₂C_mul
  exact eq_two_mul_cos_pi_div_of_norm_one_add_sq_div_le lam hlam_nonneg hlam_lt h2le
    (hζ_sq ▸ hζ_prim.pow_eq_one)
    (norm_one_add_sq_div_le_sq_of_mulVec_eq_smul A hA_nonneg hA_same hy0 hA_eig
      hM₁C_mul hM₂C_mul (Complex.exp_ne_zero _) hz.2 (Module.End.mem_eigenspace_iff.1 hz.1))

/-- For a rank-1 root system, every bipartite Coxeter element has order `2`. -/
private theorem orderOf_bipartiteCoxeterElement_eq_two_of_subsingleton
    {ι K M N : Type*} [Field K] [CharZero K] [AddCommGroup M] [Module K M]
    [AddCommGroup N] [Module K N] (P : RootPairing ι K M N) [Finite ι]
    [P.IsCrystallographic] [P.IsReduced] (b : P.Base)
    [Nonempty b.support] [Subsingleton b.support]
    (col : (coxeterMatrixOfBase P b).graph.Coloring Bool) :
    orderOf ((weylCoxeterSystem P b).bipartiteCoxeterElement col) = 2 := by
  let := Fintype.ofFinite ι
  obtain ⟨l₁, l₂, -, -, hl_nodup, hl_all, hl_eq⟩ :=
    (weylCoxeterSystem P b).exists_wordProd_eq_bipartiteCoxeterElement col
  obtain ⟨i₀⟩ := ‹Nonempty b.support›
  have hl_len : (l₁ ++ l₂).length = 1 := by
    have h1 := List.Nodup.length_le_card hl_nodup
    have h2 : 0 < (l₁ ++ l₂).length := List.length_pos_of_mem (hl_all i₀)
    have h3 := Fintype.card_le_one_iff_subsingleton.2 ‹Subsingleton b.support›
    omega
  rcases List.length_eq_one_iff.1 hl_len with ⟨a, ha⟩
  rw [← hl_eq, ha, CoxeterSystem.wordProd_singleton]
  exact (weylCoxeterSystem P b).orderOf_simple a

end SpectralHelpers

section RealCoxeterPlane

variable {ι M N : Type*} [AddCommGroup M] [Module ℝ M] [AddCommGroup N] [Module ℝ N]
  (P : RootPairing ι ℝ M N) [Finite ι] [P.IsCrystallographic] [P.IsReduced] [P.IsRootSystem]

omit [P.IsRootSystem] in
/-- Helper giving the dihedral colour-part action for arbitrary `(κ, y)` satisfying the Cartan
left-eigenvector equation and `2 - κ = 2 cos (π / h)`. -/
private lemma dihedral_colorPart_of_eig
    (b : P.Base) (col : (coxeterMatrixOfBase P b).graph.Coloring Bool)
    {l₁ l₂ : List b.support} (hl₁ : l₁.Nodup) (hl₂ : l₂.Nodup)
    (hcol₁ : ∀ i : b.support, i ∈ l₁ ↔ col i = true)
    (hcol₂ : ∀ i : b.support, i ∈ l₂ ↔ col i = false)
    {κ : ℝ} {y : b.support → ℝ} (hy0 : ∀ i, 0 < y i) (hκ : 0 < κ)
    (hy : ∀ j : b.support, ∑ i : b.support, y i * P.pairingIn ℤ i j = κ * y j)
    (hlam : 2 - κ = 2 * Real.cos (Real.pi / orderOf (wordProd P b l₁ * wordProd P b l₂))) :
    colorPart P b col y true + colorPart P b col y false ∈ openDominantChamber P b ∧
      wordProd P b l₁ • colorPart P b col y true = -colorPart P b col y true ∧
      wordProd P b l₁ • colorPart P b col y false = colorPart P b col y false +
        (2 * Real.cos (Real.pi / orderOf (wordProd P b l₁ * wordProd P b l₂))) •
          colorPart P b col y true ∧
      wordProd P b l₂ • colorPart P b col y false = -colorPart P b col y false ∧
      wordProd P b l₂ • colorPart P b col y true = colorPart P b col y true +
        (2 * Real.cos (Real.pi / orderOf (wordProd P b l₁ * wordProd P b l₂))) •
          colorPart P b col y false := by
  have hc₁_eq : wordProd P b l₁ = (weylCoxeterSystem P b).colorClassProd col true :=
    wordProd_eq_colorClassProd_of_mem_iff P b col true hl₁ hcol₁
  have hc₂_eq : wordProd P b l₂ = (weylCoxeterSystem P b).colorClassProd col false :=
    wordProd_eq_colorClassProd_of_mem_iff P b col false hl₂ hcol₂
  have hv_dom : colorPart P b col y true + colorPart P b col y false ∈ openDominantChamber P b := by
    rw [mem_openDominantChamber]; intro i hi
    simpa [P.coroot'_colorPart_add (c := col) hy ⟨i, hi⟩] using mul_pos hκ (hy0 ⟨i, hi⟩)
  have hc₁_v₁ : wordProd P b l₁ • colorPart P b col y true = -colorPart P b col y true := by
    rw [hc₁_eq, P.colorClassProd_smul_colorPart (c := col) hy true true]
    simp only [↓reduceIte, Algebra.algebraMap_self, RingHom.id_apply, two_smul]; abel
  have hc₁_v₂ : wordProd P b l₁ • colorPart P b col y false =
      colorPart P b col y false + (2 - κ) • colorPart P b col y true := by
    rw [hc₁_eq, P.colorClassProd_smul_colorPart (c := col) hy true false]
    simp only [Bool.false_eq_true, ↓reduceIte, Algebra.algebraMap_self, RingHom.id_apply]
    rw [sub_eq_add_neg, ← neg_smul, neg_sub]
  have hc₂_v₂ : wordProd P b l₂ • colorPart P b col y false = -colorPart P b col y false := by
    rw [hc₂_eq, P.colorClassProd_smul_colorPart (c := col) hy false false]
    simp only [↓reduceIte, Algebra.algebraMap_self, RingHom.id_apply, two_smul]; abel
  have hc₂_v₁ : wordProd P b l₂ • colorPart P b col y true =
      colorPart P b col y true + (2 - κ) • colorPart P b col y false := by
    rw [hc₂_eq, P.colorClassProd_smul_colorPart (c := col) hy false true]
    simp only [Bool.true_eq_false, ↓reduceIte, Algebra.algebraMap_self, RingHom.id_apply]
    rw [sub_eq_add_neg, ← neg_smul, neg_sub]
  exact ⟨hv_dom, hc₁_v₁, hlam ▸ hc₁_v₂, hc₂_v₂, hlam ▸ hc₂_v₁⟩

/-- **The Steinberg–Coleman Coxeter plane over `ℝ`.** For a base `b` of rank at least two
(`[Nontrivial b.support]`) of an irreducible finite reduced crystallographic root system, every
bipartite Coxeter element `wordProd P b l₁ * wordProd P b l₂` admits linearly independent vectors
`v₁, v₂ : M` (spanning the Coxeter plane) with `v₁ + v₂` in the open dominant chamber on which
`wordProd P b l₁`, `wordProd P b l₂` act by dihedral formulas with parameter
`2 cos (π / orderOf (wordProd P b l₁ * wordProd P b l₂))`. -/
theorem exists_coxeterPlane_bipartite [P.IsIrreducible] (b : P.Base) [Nontrivial b.support]
    (col : (coxeterMatrixOfBase P b).graph.Coloring Bool)
    {l₁ l₂ : List b.support} (hl₁ : l₁.Nodup) (hl₂ : l₂.Nodup)
    (hcol₁ : ∀ i : b.support, i ∈ l₁ ↔ col i = true)
    (hcol₂ : ∀ i : b.support, i ∈ l₂ ↔ col i = false) :
    ∃ v₁ v₂ : M,
      LinearIndependent ℝ ![v₁, v₂] ∧
      v₁ + v₂ ∈ openDominantChamber P b ∧
      wordProd P b l₁ • v₁ = -v₁ ∧
      wordProd P b l₁ • v₂ = v₂ +
        (2 * Real.cos (Real.pi / orderOf (wordProd P b l₁ * wordProd P b l₂))) • v₁ ∧
      wordProd P b l₂ • v₂ = -v₂ ∧
      wordProd P b l₂ • v₁ = v₁ +
        (2 * Real.cos (Real.pi / orderOf (wordProd P b l₁ * wordProd P b l₂))) • v₂ := by
  classical
  let := Fintype.ofFinite ι
  have : Nonempty b.support := b.nonempty_support_of_isIrreducible
  obtain ⟨κ, hκ, hκ2, y, hy0, hyC⟩ :=
    (isFiniteType_cartanMatrix b).exists_pos_vecMul_eq_smul b.cartanMatrix_isIndecomposable
  have hy := P.sum_mul_pairingIn_eq_of_vecMul_eq_smul b hyC
  have hc_bip := wordProd_mul_wordProd_eq_bipartiteCoxeterElement P b col hl₁ hl₂ hcol₁ hcol₂
  have hlam : 2 - κ = 2 * Real.cos (Real.pi / orderOf (wordProd P b l₁ * wordProd P b l₂)) := by
    rw [hc_bip]
    exact two_sub_eq_two_mul_cos_pi_div_orderOf_bipartiteCoxeterElement P b col hy hy0 hκ hκ2
  set v₁ : M := colorPart P b col y true
  set v₂ : M := colorPart P b col y false
  have hli : LinearIndependent ℝ ![v₁, v₂] := by
    obtain ⟨i₀⟩ := ‹Nonempty b.support›
    obtain ⟨i₁, hi₁⟩ := exists_ne i₀
    obtain ⟨w⟩ := preconnected_graph_coxeterMatrixOfBase P b i₀ i₁
    have hdiff : ∃ j : b.support, col j ≠ col i₀ := by
      cases w with
      | nil => exact absurd rfl hi₁
      | @cons _ u _ hadj _ => exact ⟨u, (col.valid hadj).symm⟩
    obtain ⟨i_true, hi_true⟩ : ∃ i : b.support, col i = true := by
      cases hci : col i₀
      · rcases hdiff with ⟨j, hj⟩
        exact ⟨j, by cases hcj : col j <;> simp_all⟩
      · exact ⟨i₀, hci⟩
    obtain ⟨i_false, hi_false⟩ : ∃ i : b.support, col i = false := by
      cases hci : col i₀
      · exact ⟨i₀, hci⟩
      · rcases hdiff with ⟨j, hj⟩
        exact ⟨j, by cases hcj : col j <;> simp_all⟩
    refine Fintype.linearIndependent_iff.2 fun f hf ↦ ?_
    have hsum : f 0 • v₁ + f 1 • v₂ = 0 := by simpa [Fin.sum_univ_two] using hf
    have hf0 : f 0 = 0 := by
      have h0 := congrArg (fun m ↦ b.toWeightBasis.repr m i_true) hsum
      simp only [map_add, map_smul, map_zero, Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul,
        v₁, v₂, P.toWeightBasis_repr_colorPart b, hi_true, ↓reduceIte, Bool.true_eq_false,
        mul_zero, add_zero] at h0
      exact (mul_eq_zero.1 h0).resolve_right (hy0 i_true).ne'
    have hf1 : f 1 = 0 := by
      have h0 := congrArg (fun m ↦ b.toWeightBasis.repr m i_false) hsum
      simp only [map_add, map_smul, map_zero, Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul,
        v₁, v₂, P.toWeightBasis_repr_colorPart b, hi_false, ↓reduceIte, Bool.false_eq_true,
        mul_zero, zero_add] at h0
      exact (mul_eq_zero.1 h0).resolve_right (hy0 i_false).ne'
    intro k
    fin_cases k <;> assumption
  exact ⟨v₁, v₂, hli, dihedral_colorPart_of_eig P b col hl₁ hl₂ hcol₁ hcol₂ hy0 hκ hy hlam⟩

/-- **Dihedral colour-part action for a bipartite Coxeter element over `ℝ`.** For any base `b`
(of arbitrary rank `≥ 1`) of an irreducible finite reduced crystallographic root system, there
exist `v₁, v₂ : M` with `v₁ + v₂` in the open dominant chamber on which `wordProd P b l₁` and
`wordProd P b l₂` act by dihedral formulas with parameter
`2 cos (π / orderOf (wordProd P b l₁ * wordProd P b l₂))`.

When `b.support` is nontrivial (rank `≥ 2`), `exists_coxeterPlane_bipartite` further certifies
that `v₁` and `v₂` are linearly independent; in rank one (`Subsingleton b.support`), one of
`v₁, v₂` is zero and `2 cos (π / 2) = 0`. -/
theorem exists_dihedral_colorPart_bipartite [P.IsIrreducible] (b : P.Base)
    (col : (coxeterMatrixOfBase P b).graph.Coloring Bool)
    {l₁ l₂ : List b.support} (hl₁ : l₁.Nodup) (hl₂ : l₂.Nodup)
    (hcol₁ : ∀ i : b.support, i ∈ l₁ ↔ col i = true)
    (hcol₂ : ∀ i : b.support, i ∈ l₂ ↔ col i = false) :
    ∃ v₁ v₂ : M,
      v₁ + v₂ ∈ openDominantChamber P b ∧
      wordProd P b l₁ • v₁ = -v₁ ∧
      wordProd P b l₁ • v₂ = v₂ +
        (2 * Real.cos (Real.pi / orderOf (wordProd P b l₁ * wordProd P b l₂))) • v₁ ∧
      wordProd P b l₂ • v₂ = -v₂ ∧
      wordProd P b l₂ • v₁ = v₁ +
        (2 * Real.cos (Real.pi / orderOf (wordProd P b l₁ * wordProd P b l₂))) • v₂ := by
  classical
  let := Fintype.ofFinite ι
  have : Nonempty b.support := b.nonempty_support_of_isIrreducible
  rcases subsingleton_or_nontrivial b.support with hsub | _
  · have hy := P.sum_pairingIn_eq_two_of_subsingleton b
    have hc_bip := wordProd_mul_wordProd_eq_bipartiteCoxeterElement P b col hl₁ hl₂ hcol₁ hcol₂
    have hlam : 2 - (2 : ℝ) =
        2 * Real.cos (Real.pi / orderOf (wordProd P b l₁ * wordProd P b l₂)) := by
      rw [hc_bip, orderOf_bipartiteCoxeterElement_eq_two_of_subsingleton P b col, sub_self,
        show Real.pi / ((2 : ℕ) : ℝ) = Real.pi / 2 by norm_num, Real.cos_pi_div_two, mul_zero]
    exact ⟨_, _, dihedral_colorPart_of_eig P b col hl₁ hl₂ hcol₁ hcol₂ (fun _ ↦ one_pos) two_pos
      hy hlam⟩
  · obtain ⟨v₁, v₂, -, h⟩ := P.exists_coxeterPlane_bipartite b col hl₁ hl₂ hcol₁ hcol₂
    exact ⟨v₁, v₂, h⟩

end RealCoxeterPlane

section ComplexRegularEigenvector

/-- **Regular eigenvector of a Coxeter element over `ℂ`.** Every Coxeter element `wordProd P b l`
of a finite irreducible reduced crystallographic root system over `ℂ` admits a regular weight `v`
with eigenvalue `(Complex.exp (2 * Real.pi * Complex.I / orderOf (wordProd P b l)))⁻¹`. -/
theorem exists_isRegularWeight_wordProd_smul_eq_inv_exp_smul
    {ι M N : Type*} [AddCommGroup M] [Module ℂ M] [AddCommGroup N] [Module ℂ N]
    (P : RootPairing ι ℂ M N) [Finite ι] [P.IsCrystallographic] [P.IsReduced]
    [P.IsRootSystem] [P.IsIrreducible] (b : P.Base)
    {l : List b.support} (hl : l.Nodup) (hall : ∀ i, i ∈ l) :
    ∃ v : M, IsRegularWeight P v ∧
      wordProd P b l • v =
        (Complex.exp (2 * Real.pi * Complex.I / orderOf (wordProd P b l)))⁻¹ • v := by
  classical
  let := Fintype.ofFinite ι
  have : Nonempty ι := P.nonempty_of_isIrreducible
  have : Nonempty b.support := b.nonempty_support_of_isIrreducible
  obtain ⟨col⟩ := nonempty_coloring_graph_coxeterMatrixOfBase P b
  set c := (weylCoxeterSystem P b).bipartiteCoxeterElement col
  have hc_eig : ∃ v : M, IsRegularWeight P v ∧
      c • v = (Complex.exp (2 * Real.pi * Complex.I / orderOf c))⁻¹ • v := by
    rcases subsingleton_or_nontrivial b.support with hsub | _
    · obtain ⟨v, μ, hv_reg, hv_eig, hμ_prim⟩ :=
        P.exists_isRegularWeight_bipartiteCoxeterElement_smul_eq_smul_isPrimitiveRoot b col
      have hord : orderOf c = 2 :=
        orderOf_bipartiteCoxeterElement_eq_two_of_subsingleton P b col
      have hμ_sq : μ ^ 2 = 1 := hord ▸ hμ_prim.pow_eq_one
      have hμ_ne_one : μ ≠ 1 := hμ_prim.ne_one (hord ▸ by norm_num)
      have hμ_eq_neg_one : μ = -1 := (sq_eq_one_iff.1 hμ_sq).resolve_left hμ_ne_one
      have hexp_eq : (Complex.exp (2 * Real.pi * Complex.I / orderOf c))⁻¹ = -1 := by
        rw [hord, show (2 : ℂ) * Real.pi * Complex.I / ((2 : ℕ) : ℂ) = Real.pi * Complex.I by
          push_cast; ring, Complex.exp_pi_mul_I, inv_neg, inv_one]
      exact ⟨v, hv_reg, by rwa [hμ_eq_neg_one, ← hexp_eq] at hv_eig⟩
    · obtain ⟨κ, hκ, hκ2, y, hy0, hyC⟩ :=
        (isFiniteType_cartanMatrix b).exists_pos_vecMul_eq_smul b.cartanMatrix_isIndecomposable
      have hy := P.sum_mul_pairingIn_eq_of_vecMul_eq_smul b hyC
      have hlam : 2 - κ = 2 * Real.cos (Real.pi / orderOf c) :=
        two_sub_eq_two_mul_cos_pi_div_orderOf_bipartiteCoxeterElement P b col hy hy0 hκ hκ2
      have hν := (exp_pm_two_mul_I_quad hlam).2
      rw [show (2 * ((Real.pi / orderOf c : ℝ) : ℂ) * Complex.I) =
        2 * Real.pi * Complex.I / orderOf c by push_cast; ring] at hν
      exact ⟨_, P.isRegularWeight_one_add_smul_colorPart_add_smul (c := col) hy hy0 hκ hκ2 hν,
        P.bipartiteCoxeterElement_smul_one_add_smul_colorPart_add_smul (c := col) hy hν⟩
  obtain ⟨v, hv_reg, hv_eig⟩ := hc_eig
  have hconj : IsConj (wordProd P b l) c := by
    rw [← weylCoxeterSystem_wordProd]
    exact (weylCoxeterSystem P b).isConj_wordProd_bipartiteCoxeterElement
      (isAcyclic_graph_coxeterMatrixOfBase P b) col hl hall
  obtain ⟨u, hu⟩ := hconj.symm
  have hconj_eq : MulAut.conj (u : P.weylGroup) c = wordProd P b l := by
    rw [MulAut.conj_apply]; exact mul_inv_eq_of_eq_mul hu.eq
  have hord : orderOf (wordProd P b l) = orderOf c := by
    rw [← hconj_eq]; exact MulEquiv.orderOf_eq _ _
  refine ⟨(u : P.weylGroup) • v, (isRegularWeight_smul P (u : P.weylGroup) v).2 hv_reg, ?_⟩
  rw [← mul_smul, ← hu.eq, mul_smul, hv_eig, hord]
  exact smul_comm (u : P.weylGroup) _ v

end ComplexRegularEigenvector

end RootPairing
