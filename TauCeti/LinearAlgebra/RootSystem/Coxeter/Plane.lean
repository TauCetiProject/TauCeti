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
public import TauCeti.LinearAlgebra.RootSystem.SimpleReflections
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.LinearAlgebra.Eigenspace.Charpoly
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.RingTheory.RootsOfUnity.Complex
import TauCeti.GroupTheory.Coxeter.CoxeterElement
import TauCeti.LinearAlgebra.Matrix.PerronFrobenius.Irreducible
import TauCeti.LinearAlgebra.RootSystem.Coxeter.Element.ActsBy
import TauCeti.LinearAlgebra.RootSystem.Coxeter.Element.Regular
import TauCeti.LinearAlgebra.RootSystem.Coxeter.FixedPoints
import TauCeti.LinearAlgebra.RootSystem.FiniteType.Perron
import TauCeti.LinearAlgebra.RootSystem.Weyl.Chamber

/-!
# The Coxeter plane and regular eigenvectors of Coxeter elements

For a finite irreducible reduced crystallographic root system `P` with base `b` and two-colouring
`col` of its Dynkin diagram, Perron–Frobenius on the Cartan matrix and the shared colour-part
machinery of `Coxeter.Element.Regular` give the Steinberg–Coleman Coxeter plane with dihedral
parameter `2 cos (π / orderOf (c₁ * c₂))`. Over `ℝ` this yields `v₁ + v₂ ∈ openDominantChamber P b`,
and over `ℂ` applying `bipartiteCoxeterElement_smul_eigen` and conjugating along
`CoxeterSystem.isConj_wordProd_bipartiteCoxeterElement` yields a regular eigenvector of eigenvalue
`exp (2πi / orderOf c)⁻¹` for every Coxeter element `c = wordProd P b l`.
-/

public section

open Matrix Polynomial TauCeti

namespace RootPairing

section OrderLowerBound

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] (P : RootPairing ι R M N) [Finite ι] [P.IsRootSystem]

/-- Every Coxeter element of a nontrivial finite root system has order at least `2`. -/
theorem two_le_orderOf_wordProd [Nontrivial M] (b : P.Base)
    {l : List b.support} (hl : l.Nodup) (hall : ∀ i, i ∈ l) :
    2 ≤ orderOf (wordProd P b l) := by
  have : Finite P.weylGroup := P.finite_weylGroup
  have hpos : 0 < orderOf (wordProd P b l) := orderOf_pos_iff.2 (isOfFinOrder_of_finite _)
  have hne : orderOf (wordProd P b l) ≠ 1 := fun h1 ↦ by
    obtain ⟨x, hx⟩ := exists_ne (0 : M)
    exact hx ((wordProd_smul_eq_self_iff_eq_zero b hl hall).1
      (by rw [orderOf_eq_one_iff.1 h1, one_smul]))
  omega

end OrderLowerBound

section SpectralHelpers

private lemma exp_mul_I_add_inv (φ : ℝ) :
    Complex.exp ((φ : ℂ) * Complex.I) + (Complex.exp ((φ : ℂ) * Complex.I))⁻¹ =
      ((2 * Real.cos φ : ℝ) : ℂ) := by
  rw [show (Complex.exp ((φ : ℂ) * Complex.I))⁻¹ =
      Complex.exp ((-(φ : ℝ) : ℂ) * Complex.I) by rw [← Complex.exp_neg]; congr 1; ring]
  simp only [Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg, ← Complex.ofReal_cos]
  push_cast; ring

private lemma dihedral_eigenvector {V : Type*} [AddCommGroup V] [Module ℂ V]
    (f₁ f₂ : V →ₗ[ℂ] V) {x₁ x₂ : V} {μ : ℂ} (hμ : μ ≠ 0)
    (hf₁₁ : f₁ x₁ = -x₁) (hf₁₂ : f₁ x₂ = x₂ + (μ + μ⁻¹) • x₁)
    (hf₂₂ : f₂ x₂ = -x₂) (hf₂₁ : f₂ x₁ = x₁ + (μ + μ⁻¹) • x₂) :
    f₁ (f₂ (x₁ + μ • x₂)) = (μ ^ 2)⁻¹ • (x₁ + μ • x₂) := by
  have h2 : f₂ (x₁ + μ • x₂) = x₁ + μ⁻¹ • x₂ := by
    rw [map_add, map_smul, hf₂₁, hf₂₂, add_smul, smul_neg]; abel
  calc f₁ (f₂ (x₁ + μ • x₂))
      = -x₁ + μ⁻¹ • (x₂ + (μ + μ⁻¹) • x₁) := by
          rw [h2, map_add, map_smul, hf₁₁, hf₁₂]
    _ = (μ ^ 2)⁻¹ • (x₁ + μ • x₂) := by
        rw [smul_add, add_smul, smul_add, smul_smul, smul_smul, inv_mul_cancel₀ hμ, one_smul,
          ← mul_inv, ← sq, smul_add, smul_smul,
          show (μ ^ 2)⁻¹ * μ = μ⁻¹ by field_simp [hμ]]
        abel

private lemma spectral_bound_of_bipartite_eigenvector {κ : Type*} [Fintype κ] [DecidableEq κ]
    {A : Matrix κ κ ℝ} {M₁C M₂C : Matrix κ κ ℂ} {col : κ → Bool} {a : κ → ℝ}
    {lam : ℝ} (hA_nonneg : ∀ i j, 0 ≤ A i j)
    (hA_same : ∀ i j, col i = col j → A i j = 0)
    (ha_pos : ∀ i, 0 < a i) (ha_eig : A *ᵥ a = lam • a) (hM₁C_sq : M₁C * M₁C = 1)
    (hM₁C_mul : ∀ (z : κ → ℂ) (i : κ), (M₁C *ᵥ z) i = if col i = true then
        -z i + ∑ j : κ, (if col j = false then (A i j : ℂ) * z j else 0) else z i)
    (hM₂C_mul : ∀ (z : κ → ℂ) (i : κ), (M₂C *ᵥ z) i = if col i = false then
        -z i + ∑ j : κ, (if col j = true then (A i j : ℂ) * z j else 0) else z i)
    {ω : ℂ} {z : κ → ℂ} (hω : ω ≠ 0) (hz : z ≠ 0)
    (heig : (M₁C * M₂C) *ᵥ z = ω • z) :
    ‖(1 + ω) ^ 2 / ω‖ ≤ lam ^ 2 := by
  set AC : Matrix κ κ ℂ := A.map Complex.ofReal
  have hM₂_eq : M₂C *ᵥ z = ω • (M₁C *ᵥ z) := by
    have h1 := congrArg (M₁C *ᵥ ·) heig
    rwa [mulVec_mulVec, ← Matrix.mul_assoc, hM₁C_sq, Matrix.one_mul, mulVec_smul] at h1
  set z₁ : κ → ℂ := fun i ↦ if col i = true then z i else 0
  set z₂ : κ → ℂ := fun i ↦ if col i = false then z i else 0
  have hz_split : z = z₁ + z₂ := by
    ext i; simp only [z₁, z₂, Pi.add_apply]; cases col i <;> simp
  have hAz_color (b0 : Bool) (i : κ) :
      (AC *ᵥ fun j ↦ if col j = b0 then z j else 0) i = if col i = !b0 then
        ∑ j : κ, (if col j = b0 then (A i j : ℂ) * z j else 0) else 0 := by
    simp only [mulVec, dotProduct, AC, Matrix.map_apply]
    split_ifs with hci
    · exact Finset.sum_congr rfl fun j _ ↦ by split_ifs <;> simp
    · have hsame : col i = b0 := by cases h1 : col i <;> cases b0 <;> simp_all
      exact Finset.sum_eq_zero fun j _ ↦ by
        split_ifs with hcj
        · simp [hA_same i j (hsame.trans hcj.symm)]
        · simp
  have heq₁ : (1 + ω) • z₁ = ω • (AC *ᵥ z₂) := by
    ext i; have hi := congrFun hM₂_eq i; have hAz := hAz_color false i
    simp only [Bool.not_false, z₁, z₂, Pi.smul_apply, smul_eq_mul, hM₂C_mul,
      hM₁C_mul] at hi hAz ⊢
    rw [hAz]; cases hci : col i <;> simp [hci] at hi ⊢; linear_combination hi
  have heq₂ : AC *ᵥ z₁ = (1 + ω) • z₂ := by
    ext i; have hi := congrFun hM₂_eq i; have hAz := hAz_color true i
    simp only [Bool.not_true, z₁, z₂, Pi.smul_apply, smul_eq_mul, hM₂C_mul,
      hM₁C_mul] at hi hAz ⊢
    rw [hAz]; cases hci : col i <;> simp [hci] at hi ⊢; linear_combination hi
  have hA2_eig : (A ^ 2).map Complex.ofReal *ᵥ z = ((1 + ω) ^ 2 / ω) • z := by
    have h1 : ω • (AC *ᵥ (AC *ᵥ z₁)) = (1 + ω) ^ 2 • z₁ := by
      rw [heq₂, mulVec_smul, smul_comm, ← heq₁, smul_smul, sq]
    have h2 : ω • (AC *ᵥ (AC *ᵥ z₂)) = (1 + ω) ^ 2 • z₂ := by
      have := congrArg (AC *ᵥ ·) heq₁
      rw [mulVec_smul, mulVec_smul, heq₂, smul_smul, ← sq] at this; exact this.symm
    have hsum : ω • ((AC * AC) *ᵥ z) = (1 + ω) ^ 2 • z := by
      rw [hz_split, mulVec_add, ← mulVec_mulVec, ← mulVec_mulVec, smul_add, h1, h2,
        ← smul_add]
    rw [show (A ^ 2).map Complex.ofReal = AC * AC by ext i j; simp [AC, sq, Matrix.mul_apply]]
    ext i; have hi := congrFun hsum i; simp only [Pi.smul_apply, smul_eq_mul] at hi ⊢
    exact mul_left_cancel₀ hω (by rw [hi]; field_simp [hω])
  have hA2_nonneg : ∀ i j, 0 ≤ (A ^ 2) i j := fun i j ↦ by
    rw [sq, Matrix.mul_apply]
    exact Finset.sum_nonneg fun k _ ↦ mul_nonneg (hA_nonneg i k) (hA_nonneg k j)
  exact Matrix.norm_le_of_mulVec_le_smul hA2_nonneg ha_pos
    (le_of_eq (by rw [sq, ← mulVec_mulVec, ha_eig, mulVec_smul, ha_eig, smul_smul, sq]))
    hz hA2_eig

private lemma eq_two_mul_cos_pi_div_of_spectral_bound {lam : ℝ} {h : ℕ}
    (hlam_nonneg : 0 ≤ lam) (hlam_lt : lam < 2) (h2le : 2 ≤ h)
    (hζ_pow : (Complex.exp ((Real.arccos (lam / 2) : ℂ) * Complex.I) ^ 2) ^ h = 1)
    (hbound : ‖(1 + Complex.exp (2 * Real.pi * Complex.I / h)) ^ 2 /
      Complex.exp (2 * Real.pi * Complex.I / h)‖ ≤ lam ^ 2) :
    lam = 2 * Real.cos (Real.pi / h) := by
  set θ : ℝ := Real.arccos (lam / 2)
  have hcosθ : Real.cos θ = lam / 2 := Real.cos_arccos (by linarith) (by linarith)
  have hθ_pos : 0 < θ := by
    rw [← Real.arccos_one]; exact Real.arccos_lt_arccos (by linarith) (by linarith) le_rfl
  have hθ_le : θ ≤ Real.pi / 2 := by
    rw [← Real.arccos_zero]; exact Real.arccos_le_arccos (by linarith : (0 : ℝ) ≤ lam / 2)
  set ω₀ : ℂ := Complex.exp (2 * Real.pi * Complex.I / h)
  have hval_ω₀ : (1 + ω₀) ^ 2 / ω₀ = (((2 * Real.cos (Real.pi / h)) ^ 2 : ℝ) : ℂ) := by
    set ξ : ℂ := Complex.exp (((Real.pi / h : ℝ) : ℂ) * Complex.I)
    rw [show ω₀ = ξ ^ 2 by
        simp only [ω₀, ξ, sq, ← Complex.exp_add]; congr 1; push_cast; ring,
      show (1 + ξ ^ 2) ^ 2 / ξ ^ 2 = (ξ + ξ⁻¹) ^ 2 by
        field_simp [Complex.exp_ne_zero _]; ring,
      exp_mul_I_add_inv]; push_cast; ring
  rw [hval_ω₀, Complex.norm_real, Real.norm_of_nonneg (sq_nonneg _)] at hbound
  have hh_pos : (0 : ℝ) < h := by exact_mod_cast (show 0 < h by omega)
  have hpi_le_θ : Real.pi / h ≤ θ := by
    have hexp1 : Complex.exp (((2 * (h : ℝ) * θ : ℝ) : ℂ) * Complex.I) = 1 := by
      simp only [← Complex.exp_natCast_mul] at hζ_pow; convert hζ_pow using 2; push_cast; ring
    obtain ⟨m, hm⟩ := Complex.exp_eq_one_iff.1 hexp1
    have hre : 2 * (h : ℝ) * θ = (m : ℝ) * (2 * Real.pi) := Complex.ofReal_injective
      (mul_right_cancel₀ Complex.I_ne_zero (by simpa [mul_assoc] using hm))
    have hm_pos : (0 : ℤ) < m := by
      exact_mod_cast (show (0 : ℝ) < m by nlinarith [Real.pi_pos, mul_pos hh_pos hθ_pos])
    have hm_ge : (1 : ℝ) ≤ m := by exact_mod_cast (show (1 : ℤ) ≤ m by omega)
    rw [div_le_iff₀ hh_pos]; nlinarith [Real.pi_pos]
  have hcos_le : Real.cos (Real.pi / h) ≤ Real.cos θ := by
    have hcos_nonneg_pi : 0 ≤ Real.cos (Real.pi / h) := by
      refine Real.cos_nonneg_of_mem_Icc
        ⟨by linarith [Real.pi_pos, div_nonneg Real.pi_pos.le hh_pos.le], ?_⟩
      have h2 : (2 : ℝ) ≤ h := by exact_mod_cast h2le
      rw [div_le_div_iff₀ hh_pos (by norm_num)]; nlinarith [Real.pi_pos]
    have : Real.cos (Real.pi / h) ^ 2 ≤ Real.cos θ ^ 2 := by
      rw [show lam = 2 * Real.cos θ by linarith] at hbound; nlinarith
    nlinarith
  have hcos_ge : Real.cos θ ≤ Real.cos (Real.pi / h) := Real.strictAntiOn_cos.antitoneOn
    ⟨by positivity, le_trans hpi_le_θ (le_trans hθ_le (by linarith [Real.pi_pos]))⟩
    ⟨hθ_pos.le, le_trans hθ_le (by linarith [Real.pi_pos])⟩ hpi_le_θ
  linarith [le_antisymm hcos_ge hcos_le]

/-- Identifying the Perron–Frobenius dihedral parameter `2 - κ` with `2 cos (π / h)`, where `h`
is the order of the bipartite Coxeter element, shared between the real Coxeter plane and complex
regular-eigenvector constructions. -/
private lemma two_sub_eq_two_mul_cos_pi_div_orderOf_bipartiteCoxeterElement
    {ι K M N : Type*} [Field K] [CharZero K] [Algebra ℝ K]
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
  have : Nontrivial M := b.toWeightBasis.equivFun.symm.injective.nontrivial
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
  have hc₁_eq : wordProd P b l₁ = c₁ := by
    rw [← weylCoxeterSystem_wordProd]
    exact (weylCoxeterSystem P b).wordProd_eq_colorClassProd col hl₁ hmem₁
  have hc₂_eq : wordProd P b l₂ = c₂ := by
    rw [← weylCoxeterSystem_wordProd]
    exact (weylCoxeterSystem P b).wordProd_eq_colorClassProd col hl₂ hmem₂
  have hc_eq : wordProd P b (l₁ ++ l₂) = c := by
    rw [← weylCoxeterSystem_wordProd]; exact hl_eq
  set h : ℕ := orderOf c
  have h2le : 2 ≤ h := by dsimp [h]; rw [← hc_eq]; exact P.two_le_orderOf_wordProd b hl_nodup hl_all
  have hh_pos : 0 < h := by omega
  set lam : ℝ := 2 - κ
  have hlam_nonneg : 0 ≤ lam := by linarith
  have hlam_lt : lam < 2 := by linarith
  set θ : ℝ := Real.arccos (lam / 2)
  have hcosθ : Real.cos θ = lam / 2 := Real.cos_arccos (by linarith) (by linarith)
  have hsinθ_pos : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi
    (by rw [← Real.arccos_one]; exact Real.arccos_lt_arccos (by linarith) (by linarith) le_rfl)
    (lt_of_le_of_lt (show θ ≤ Real.pi / 2 by
      rw [← Real.arccos_zero]; exact Real.arccos_le_arccos (by linarith))
      (by linarith [Real.pi_pos]))
  set μ : ℂ := Complex.exp ((θ : ℂ) * Complex.I); set ζ : ℂ := μ ^ 2
  have hμ_ne : μ ≠ 0 := Complex.exp_ne_zero _
  have hμ_add_inv : μ + μ⁻¹ = (lam : ℂ) := by
    rw [exp_mul_I_add_inv θ, hcosθ]; push_cast; ring
  set A : Matrix b.support b.support ℝ :=
    fun i j ↦ if i = j then 0 else -(b.cartanMatrix j i : ℝ)
  have hA_nonneg : ∀ i j, 0 ≤ A i j := fun i j ↦ by
    by_cases hij : i = j
    · simp [A, hij]
    · simp only [A, ite_eq_right hij, neg_nonneg]
      exact_mod_cast b.cartanMatrix_le_zero_of_ne j i (Ne.symm hij)
  have hA_same : ∀ i j, col i = col j → A i j = 0 := fun i j hsame ↦ by
    by_cases hij : i = j
    · simp [A, hij]
    · dsimp only [A, Base.cartanMatrix]; rw [ite_eq_right hij, Base.cartanMatrixIn_def,
        pairingIn_eq_zero_of_color_eq P b col (Ne.symm hij) hsame.symm]; simp
  have hA_eig : A *ᵥ y = lam • y := by
    ext i; simp only [mulVec, dotProduct, Pi.smul_apply, smul_eq_mul, A]
    have h2 : ∑ j : b.support, (if i = j then (b.cartanMatrix j i : ℝ) else 0) * y j =
        2 * y i := by
      rw [Finset.sum_eq_single i (fun j _ hj ↦ by simp [hj.symm]) (by simp), ite_eq_left rfl,
        show b.cartanMatrix i i = 2 from P.pairingIn_same ℤ i]; norm_num
    have hsum : ∑ j : b.support, (if i = j then 0 else -(b.cartanMatrix j i : ℝ)) * y j =
        2 * y i - ∑ j : b.support, y j * (b.cartanMatrix j i : ℝ) := by
      rw [← h2, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun j _ ↦ by by_cases hij : i = j <;> simp [hij, mul_comm]
    rw [hsum, show ∑ j : b.support, y j * (b.cartanMatrix j i : ℝ) = κ * y i from hy i]; ring
  set W₁ : Matrix b.support b.support ℤ := (l₁.map (reflMatrix b.cartanMatrix)).prod
  set W₂ : Matrix b.support b.support ℤ := (l₂.map (reflMatrix b.cartanMatrix)).prod
  have hW₁_acts : b.ActsBy c₁ W₁ := hc₁_eq ▸ b.actsBy_wordProd l₁
  have hW₂_acts : b.ActsBy c₂ W₂ := hc₂_eq ▸ b.actsBy_wordProd l₂
  have hW_acts : b.ActsBy c (W₁ * W₂) := by
    rw [show c = c₁ * c₂ from CoxeterSystem.bipartiteCoxeterElement_def _ _]
    exact hW₁_acts.mul hW₂_acts
  have hW₁_sq : W₁ * W₁ = 1 := (hW₁_acts.mul hW₁_acts).unique (by
    rw [show c₁ * c₁ = 1 from (weylCoxeterSystem P b).colorClassProd_mul_self col true]
    exact Base.actsBy_one b)
  set M₁ : Matrix b.support b.support ℝ := W₁.map (algebraMap ℤ ℝ)
  set M₂ : Matrix b.support b.support ℝ := W₂.map (algebraMap ℤ ℝ)
  set M₁C : Matrix b.support b.support ℂ := W₁.map (algebraMap ℤ ℂ)
  set M₂C : Matrix b.support b.support ℂ := W₂.map (algebraMap ℤ ℂ)
  have hM₁C_sq : M₁C * M₁C = 1 := by
    change (RingHom.mapMatrix (algebraMap ℤ ℂ)) W₁ * (RingHom.mapMatrix (algebraMap ℤ ℂ)) W₁ = 1
    rw [← map_mul, hW₁_sq, map_one]
  have hM_color_mul (b0 : Bool) (c' : P.weylGroup) (W : Matrix b.support b.support ℤ)
      (hc_eq' : c' = (weylCoxeterSystem P b).colorClassProd col b0)
      (hW' : b.ActsBy c' W) (z : b.support → ℂ) (i : b.support) :
      (W.map (algebraMap ℤ ℂ) *ᵥ z) i = if col i = b0 then
          -z i + ∑ j : b.support, (if col j = !b0 then (A i j : ℂ) * z j else 0)
        else z i := by
    have hEntry (j : b.support) : (W i j : ℂ) = if col i = b0 then
        if i = j then (-1 : ℂ) else if col j = !b0 then (A i j : ℂ) else 0
      else if i = j then 1 else 0 := by
      have hact := congrArg (fun m ↦ b.toWeightBasis.repr m i) (Base.actsBy_iff.1 hW' j)
      have hlhs : b.toWeightBasis.repr (c' • P.root j) i =
          (if i = j then 1 else 0) - if col i = b0 then P.coroot' i (P.root j) else 0 := by
        rw [hc_eq', colorClassProd_smul, map_sub, map_sum, Finsupp.sub_apply, Finset.sum_apply']
        have h1 : b.toWeightBasis.repr (P.root j) i = if i = j then 1 else 0 := by
          rw [← b.toWeightBasis_apply, b.toWeightBasis.repr_self, Finsupp.single_apply]
          exact if_congr eq_comm rfl rfl
        rw [h1]; congr 1
        rw [Finset.sum_eq_single i (fun k _ hk ↦ by
            by_cases hck : col k = b0
            · rw [ite_eq_left hck, map_smul, Finsupp.smul_apply, smul_eq_mul,
                show b.toWeightBasis.repr (P.root k) i = 0 by
                  rw [← b.toWeightBasis_apply, b.toWeightBasis.repr_self, Finsupp.single_apply,
                    ite_eq_right hk],
                mul_zero]
            · simp [ite_eq_right hck])
          (by simp)]
        by_cases hci : col i = b0
        · rw [ite_eq_left hci, map_smul, Finsupp.smul_apply, smul_eq_mul,
            show b.toWeightBasis.repr (P.root i) i = 1 by
              rw [← b.toWeightBasis_apply, b.toWeightBasis.repr_self, Finsupp.single_eq_same],
            mul_one]
        · simp [ite_eq_right hci]
      have hrhs : b.toWeightBasis.repr (∑ k : b.support, W k j • P.root k) i = (W i j : K) := by
        simp_rw [map_sum, map_zsmul, ← b.toWeightBasis_apply, b.toWeightBasis.repr_self]
        simp [Finsupp.single_apply, eq_comm]
      rw [hlhs, hrhs] at hact
      by_cases hci : col i = b0
      · rw [ite_eq_left hci] at hact
        rw [ite_eq_left hci]
        by_cases hij : i = j
        · subst hij
          rw [ite_eq_left rfl, P.root_coroot'_eq_pairing, P.pairing_same] at hact
          have hW_int : W i i = -1 :=
            Int.cast_injective (α := K) (by push_cast; linear_combination hact.symm)
          simp [hW_int]
        · rw [ite_eq_right hij] at hact
          rw [ite_eq_right hij]
          rw [P.root_coroot'_eq_pairing, ← P.algebraMap_pairingIn ℤ] at hact
          have hW_int : W i j = -b.cartanMatrix j i :=
            Int.cast_injective (α := K)
              (by push_cast; simpa [Base.cartanMatrix, Base.cartanMatrixIn_def] using hact.symm)
          by_cases hcj : col j = !b0
          · simp [hcj, hW_int, A, hij]
          · have hsame : col j = col i := by cases h1 : col j <;> cases b0 <;> simp_all
            have h0 : b.cartanMatrix j i = 0 := by
              simpa [Base.cartanMatrix, Base.cartanMatrixIn_def] using
                pairingIn_eq_zero_of_color_eq P b col (Ne.symm hij) hsame
            simp [hcj, hW_int, h0]
      · rw [ite_eq_right hci] at hact
        rw [ite_eq_right hci]
        by_cases hij : i = j
        · subst hij
          rw [ite_eq_left rfl, sub_zero] at hact
          have hW_int : W i i = 1 := Int.cast_injective (α := K) (by push_cast; exact hact.symm)
          simp [hW_int]
        · rw [ite_eq_right hij, sub_zero] at hact
          have hW_int : W i j = 0 := Int.cast_injective (α := K) (by push_cast; exact hact.symm)
          simp [hij, hW_int]
    simp only [mulVec, dotProduct, Matrix.map_apply, eq_intCast]
    by_cases hci : col i = b0
    · rw [ite_eq_left hci, show ∑ j : b.support, (W i j : ℂ) * z j = ∑ j : b.support,
          ((if i = j then -z i else 0) + (if col j = !b0 then (A i j : ℂ) * z j else 0)) from
        Finset.sum_congr rfl fun j _ ↦ by
          rw [hEntry j, ite_eq_left hci]
          by_cases hij : i = j
          · subst hij; simp [hci]
          · by_cases hcj : col j = !b0 <;> simp [hij, hcj]]
      simp [Finset.sum_add_distrib]
    · rw [ite_eq_right hci, Finset.sum_eq_single i (fun j _ hij ↦ by
          rw [hEntry j, ite_eq_right hci, ite_eq_right hij.symm, zero_mul]) (by simp),
        hEntry i, ite_eq_right hci, ite_eq_left rfl, one_mul]
  have hM₁C_mul := hM_color_mul true c₁ W₁ rfl hW₁_acts
  have hM₂C_mul := hM_color_mul false c₂ W₂ rfl hW₂_acts
  simp only [Bool.not_true, Bool.not_false] at hM₁C_mul hM₂C_mul
  have hmulVec_ofReal (W : Matrix b.support b.support ℤ) (x : b.support → ℝ) :
      W.map (algebraMap ℤ ℂ) *ᵥ (fun i ↦ (x i : ℂ)) =
        fun i ↦ ((W.map (algebraMap ℤ ℝ) *ᵥ x) i : ℂ) := by
    ext i; simp [mulVec, dotProduct]
  have hW_smul {g : P.weylGroup} {W : Matrix b.support b.support ℤ} (hgW : b.ActsBy g W)
      (x : b.support → ℝ) :
      g • (∑ i : b.support, algebraMap ℝ K (x i) • P.root i) =
        ∑ i : b.support, algebraMap ℝ K ((W.map (algebraMap ℤ ℝ) *ᵥ x) i) • P.root i := by
    rw [Finset.smul_sum]
    simp_rw [smul_comm g, Base.actsBy_iff.1 hgW, Finset.smul_sum, smul_comm (algebraMap ℝ K _)]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    simp only [← Int.cast_smul_eq_zsmul K, smul_smul, ← Finset.sum_smul, mulVec, dotProduct,
      Matrix.map_apply, eq_intCast, map_sum, map_mul, map_intCast, mul_comm]
  have hM_mulVec {g : P.weylGroup} {W : Matrix b.support b.support ℤ} (hgW : b.ActsBy g W)
      {x w : b.support → ℝ}
      (hgx : g • (∑ i : b.support, algebraMap ℝ K (x i) • P.root i) =
        ∑ i : b.support, algebraMap ℝ K (w i) • P.root i) :
      W.map (algebraMap ℤ ℝ) *ᵥ x = w := by
    rw [hW_smul hgW x] at hgx
    ext i
    apply (algebraMap ℝ K).injective
    have h1 := congrArg (fun m ↦ b.toWeightBasis.repr m i) hgx
    simp only [map_sum, map_smul, ← b.toWeightBasis_apply, b.toWeightBasis.repr_self] at h1
    simpa [Finsupp.single_apply] using h1
  set y₁ : b.support → ℝ := fun i ↦ if col i = true then y i else 0
  set y₂ : b.support → ℝ := fun i ↦ if col i = false then y i else 0
  have hM₁y₁ : M₁ *ᵥ y₁ = -y₁ := hM_mulVec hW₁_acts <| by
    have h := colorClassProd_smul_colorPart (P := P) (b := b) (c := col) hy true true
    simp only [↓reduceIte, map_ofNat, two_smul] at h
    rw [show (weylCoxeterSystem P b).colorClassProd col true = c₁ from rfl, colorPart_def] at h
    have h' : c₁ • ∑ i : b.support, algebraMap ℝ K (if col i = true then y i else 0) • P.root i =
        -(∑ i : b.support, algebraMap ℝ K (if col i = true then y i else 0) • P.root i) :=
      h.trans (by abel)
    simpa [y₁, neg_smul, Finset.sum_neg_distrib] using h'
  have hM₁y₂ : M₁ *ᵥ y₂ = y₂ + lam • y₁ := hM_mulVec hW₁_acts <| by
    have h := colorClassProd_smul_colorPart (P := P) (b := b) (c := col) hy true false
    simp only [Bool.false_eq_true, ↓reduceIte, map_sub, map_ofNat] at h
    rw [show (weylCoxeterSystem P b).colorClassProd col true = c₁ from rfl,
      show colorPart P b col y false - (algebraMap ℝ K κ - 2) • colorPart P b col y true =
        colorPart P b col y false + algebraMap ℝ K (2 - κ) • colorPart P b col y true by
      rw [map_sub, map_ofNat]; module, colorPart_def, colorPart_def] at h
    simpa [y₁, y₂, lam, Finset.smul_sum, ← Finset.sum_add_distrib, add_smul,
      smul_smul, map_mul, map_sub, map_ofNat, apply_ite (algebraMap ℝ K), map_zero] using h
  have hM₂y₂ : M₂ *ᵥ y₂ = -y₂ := hM_mulVec hW₂_acts <| by
    have h := colorClassProd_smul_colorPart (P := P) (b := b) (c := col) hy false false
    simp only [↓reduceIte, map_ofNat, two_smul] at h
    rw [show (weylCoxeterSystem P b).colorClassProd col false = c₂ from rfl, colorPart_def] at h
    have h' : c₂ • ∑ i : b.support, algebraMap ℝ K (if col i = false then y i else 0) • P.root i =
        -(∑ i : b.support, algebraMap ℝ K (if col i = false then y i else 0) • P.root i) :=
      h.trans (by abel)
    simpa [y₂, neg_smul, Finset.sum_neg_distrib] using h'
  have hM₂y₁ : M₂ *ᵥ y₁ = y₁ + lam • y₂ := hM_mulVec hW₂_acts <| by
    have h := colorClassProd_smul_colorPart (P := P) (b := b) (c := col) hy false true
    simp only [Bool.true_eq_false, ↓reduceIte, map_sub, map_ofNat] at h
    rw [show (weylCoxeterSystem P b).colorClassProd col false = c₂ from rfl,
      show colorPart P b col y true - (algebraMap ℝ K κ - 2) • colorPart P b col y false =
        colorPart P b col y true + algebraMap ℝ K (2 - κ) • colorPart P b col y false by
      rw [map_sub, map_ofNat]; module, colorPart_def, colorPart_def] at h
    simpa [y₁, y₂, lam, Finset.smul_sum, ← Finset.sum_add_distrib, add_smul,
      smul_smul, map_mul, map_sub, map_ofNat, apply_ite (algebraMap ℝ K), map_zero] using h
  set y₁C : b.support → ℂ := fun i ↦ (y₁ i : ℂ)
  set y₂C : b.support → ℂ := fun i ↦ (y₂ i : ℂ)
  set z₀ : b.support → ℂ := y₁C + μ • y₂C
  have hz₀_ne : z₀ ≠ 0 := fun h0 ↦ by
    have hne : Nonempty b.support := inferInstance
    obtain ⟨i₀⟩ := hne
    have hi0 : (y₁ i₀ : ℂ) + μ * (y₂ i₀ : ℂ) = 0 := by
      simpa [z₀, y₁C, y₂C] using congrFun h0 i₀
    cases hci : col i₀
    · have h0' : μ * (y i₀ : ℂ) = 0 := by simpa [y₁, y₂, hci] using hi0
      exact (mul_eq_zero.1 h0').elim hμ_ne (Complex.ofReal_ne_zero.2 (hy0 i₀).ne')
    · have h0' : (y i₀ : ℂ) = 0 := by simpa [y₁, y₂, hci] using hi0
      exact (hy0 i₀).ne' (Complex.ofReal_eq_zero.1 h0')
  have hz₀_eig : (M₁C * M₂C) *ᵥ z₀ = ζ⁻¹ • z₀ := by
    rw [← mulVec_mulVec]
    have hmul_c (W : Matrix b.support b.support ℤ) (x w : b.support → ℝ)
        (h : W.map (algebraMap ℤ ℝ) *ᵥ x = w) :
        W.map (algebraMap ℤ ℂ) *ᵥ (fun i ↦ (x i : ℂ)) = fun i ↦ (w i : ℂ) := by
      rw [hmulVec_ofReal, h]
    have hd := dihedral_eigenvector (Matrix.toLin' M₁C) (Matrix.toLin' M₂C) (x₁ := y₁C)
      (x₂ := y₂C) hμ_ne
      (by ext i; simpa [Matrix.toLin'_apply, M₁C, y₁C] using
        congrFun (hmul_c W₁ y₁ (-y₁) hM₁y₁) i)
      (by ext i; rw [hμ_add_inv]; simpa [Matrix.toLin'_apply, M₁C, y₁C, y₂C, Complex.real_smul]
        using congrFun (hmul_c W₁ y₂ (y₂ + lam • y₁) hM₁y₂) i)
      (by ext i; simpa [Matrix.toLin'_apply, M₂C, y₂C] using
        congrFun (hmul_c W₂ y₂ (-y₂) hM₂y₂) i)
      (by ext i; rw [hμ_add_inv]; simpa [Matrix.toLin'_apply, M₂C, y₁C, y₂C, Complex.real_smul]
        using congrFun (hmul_c W₂ y₁ (y₁ + lam • y₂) hM₂y₁) i)
    simpa [Matrix.toLin'_apply, z₀, ζ] using hd
  have hM_mul_map : M₁C * M₂C = (W₁ * W₂).map (algebraMap ℤ ℂ) :=
    ((RingHom.mapMatrix (algebraMap ℤ ℂ)).map_mul W₁ W₂).symm
  have hMR_mul_map : M₁ * M₂ = (W₁ * W₂).map (algebraMap ℤ ℝ) :=
    ((RingHom.mapMatrix (algebraMap ℤ ℝ)).map_mul W₁ W₂).symm
  have hM_pow_map (k : ℕ) : (M₁C * M₂C) ^ k = ((W₁ * W₂) ^ k).map (algebraMap ℤ ℂ) := by
    rw [hM_mul_map]; exact ((RingHom.mapMatrix (algebraMap ℤ ℂ)).map_pow (W₁ * W₂) k).symm
  have hMR_pow_map (k : ℕ) : (M₁ * M₂) ^ k = ((W₁ * W₂) ^ k).map (algebraMap ℤ ℝ) := by
    rw [hMR_mul_map]; exact ((RingHom.mapMatrix (algebraMap ℤ ℝ)).map_pow (W₁ * W₂) k).symm
  have hM_pow_eig (k : ℕ) : ((M₁C * M₂C) ^ k) *ᵥ z₀ = (ζ⁻¹) ^ k • z₀ := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', ← mulVec_mulVec, ih, mulVec_smul, hz₀_eig, smul_smul, mul_comm,
        ← pow_succ']
  have hζ_prim : IsPrimitiveRoot ζ h := by
    rw [IsPrimitiveRoot.iff_def]; refine ⟨?_, fun k hk ↦ ?_⟩
    · have hWh : (W₁ * W₂) ^ h = 1 := (hW_acts.pow h).unique (by
        rw [pow_orderOf_eq_one]; exact Base.actsBy_one b)
      have hchC : (M₁C * M₂C) ^ h = 1 := by
        rw [hM_pow_map, hWh]; exact (RingHom.mapMatrix (algebraMap ℤ ℂ)).map_one
      have h1 := hM_pow_eig h; rw [hchC, one_mulVec] at h1
      obtain ⟨i₀, hi₀⟩ := Function.ne_iff.1 hz₀_ne
      have hinv1 : (ζ⁻¹) ^ h = 1 := mul_right_cancel₀ hi₀
        (by simpa [Pi.smul_apply, smul_eq_mul] using (congrFun h1 i₀).symm)
      rwa [inv_pow, inv_eq_one] at hinv1
    · have h1 := hM_pow_eig k
      rw [inv_pow, hk, inv_one, one_smul, hM_pow_map, show z₀ = y₁C + μ • y₂C from rfl,
        mulVec_add, mulVec_smul, hmulVec_ofReal, hmulVec_ofReal, ← hMR_pow_map] at h1
      have hy₂_fix : ((M₁ * M₂) ^ k) *ᵥ y₂ = y₂ := by
        ext i; have him := congrArg Complex.im (congrFun h1 i)
        simp only [y₁C, y₂C, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Complex.add_im,
          Complex.ofReal_im, zero_add, Complex.mul_im, Complex.ofReal_re, mul_zero, μ,
          Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin] at him
        exact mul_left_cancel₀ hsinθ_pos.ne' (by simpa using him)
      have hy₁_fix : ((M₁ * M₂) ^ k) *ᵥ y₁ = y₁ := by
        ext i; have hre := congrArg Complex.re (congrFun h1 i)
        simp only [y₁C, y₂C, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Complex.add_re,
          Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, mul_zero, sub_zero,
          hy₂_fix] at hre
        linarith
      have hy_fix : (((W₁ * W₂) ^ k).map (algebraMap ℤ ℝ)) *ᵥ (y₁ + y₂) = y₁ + y₂ := by
        rw [← hMR_pow_map, mulVec_add, hy₁_fix, hy₂_fix]
      have hsum_vec : ∑ i : b.support, algebraMap ℝ K ((y₁ + y₂) i) • P.root i =
          colorPart P b col y true + colorPart P b col y false := by
        rw [colorPart_def, colorPart_def, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        simp [y₁, y₂, add_smul]
      have hck_fix : c ^ k • (colorPart P b col y true + colorPart P b col y false) =
          colorPart P b col y true + colorPart P b col y false := by
        rw [← hsum_vec, hW_smul (hW_acts.pow k), hy_fix]
      have hreg : P.IsRegularWeight (colorPart P b col y true + colorPart P b col y false) :=
        isRegularWeight_of_forall_exists_pos_coroot'_eq P b _ (algebraMap ℝ K).injective
          (exists_pos_coroot'_colorPart_add hy hy0 hκ)
      exact orderOf_dvd_of_pow_eq_one (P.eq_one_of_isRegularWeight_of_smul_eq b hreg hck_fix)
  let p : ℚ[X] := (W₁ * W₂).charpoly.map (algebraMap ℤ ℚ)
  have hp_map : p.map (algebraMap ℚ ℂ) = (M₁C * M₂C).charpoly := by
    rw [hM_mul_map, Matrix.charpoly_map, Polynomial.map_map,
      RingHom.ext_int ((algebraMap ℚ ℂ).comp (algebraMap ℤ ℚ)) (algebraMap ℤ ℂ)]
  set ω₀ : ℂ := Complex.exp (2 * Real.pi * Complex.I / h)
  have hω₀_root : (M₁C * M₂C).charpoly.IsRoot ω₀ := by
    have hζinv_root : (p.map (algebraMap ℚ ℂ)).IsRoot ζ⁻¹ := by
      rw [hp_map, ← Matrix.charpoly_toLin' (M₁C * M₂C),
        ← Module.End.hasEigenvalue_iff_isRoot_charpoly]
      exact Module.End.hasEigenvalue_of_hasEigenvector (Module.End.hasEigenvector_iff.2
        ⟨Module.End.mem_eigenspace_iff.2 hz₀_eig, hz₀_ne⟩)
    rw [← hp_map]
    have : NeZero (h : ℚ) := ⟨Nat.cast_ne_zero.2 hh_pos.ne'⟩
    obtain ⟨q, hq⟩ : cyclotomic h ℚ ∣ p := by
      rw [hζ_prim.inv.minpoly_eq_cyclotomic_of_irreducible (cyclotomic.irreducible_rat hh_pos)]
      exact minpoly.dvd ℚ ζ⁻¹ (by rw [aeval_def, eval₂_eq_eval_map]; exact hζinv_root)
    rw [hq, Polynomial.map_mul, map_cyclotomic, IsRoot.def, eval_mul,
      ((Complex.isPrimitiveRoot_exp h hh_pos.ne').isRoot_cyclotomic hh_pos).eq_zero, zero_mul]
  rw [← Matrix.charpoly_toLin' (M₁C * M₂C),
    ← Module.End.hasEigenvalue_iff_isRoot_charpoly] at hω₀_root
  obtain ⟨z, hz⟩ := hω₀_root.exists_hasEigenvector
  exact eq_two_mul_cos_pi_div_of_spectral_bound hlam_nonneg hlam_lt h2le hζ_prim.pow_eq_one
    (spectral_bound_of_bipartite_eigenvector hA_nonneg hA_same hy0 hA_eig
      hM₁C_sq hM₁C_mul hM₂C_mul (Complex.exp_ne_zero _) hz.2
      (Module.End.mem_eigenspace_iff.1 hz.1))

end SpectralHelpers

section RealCoxeterPlane

variable {ι M N : Type*} [AddCommGroup M] [Module ℝ M] [AddCommGroup N] [Module ℝ N]
  (P : RootPairing ι ℝ M N) [Finite ι] [P.IsCrystallographic] [P.IsReduced] [P.IsRootSystem]

/-- Over `ℝ`, the Steinberg–Coleman Coxeter plane of a bipartite Coxeter element `c₁ * c₂`
of an irreducible finite reduced crystallographic root system: there exist `v₁, v₂ : M` such
that `v₁ + v₂` lies in the open dominant chamber and `c₁, c₂` act on `span {v₁, v₂}` by
dihedral formulas with parameter `2 cos (π / orderOf (c₁ * c₂))`. -/
theorem exists_coxeterPlane_bipartite [P.IsIrreducible] (b : P.Base)
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
  have := IsIrreducible.nontrivial P
  have hne_supp : Nonempty b.support := by
    by_contra h; rw [not_nonempty_iff] at h
    exact not_subsingleton M b.toWeightBasis.equivFun.subsingleton
  have hc₁_eq : wordProd P b l₁ = (weylCoxeterSystem P b).colorClassProd col true := by
    rw [← weylCoxeterSystem_wordProd P b l₁]
    exact (weylCoxeterSystem P b).wordProd_eq_colorClassProd col hl₁ hcol₁
  have hc₂_eq : wordProd P b l₂ = (weylCoxeterSystem P b).colorClassProd col false := by
    rw [← weylCoxeterSystem_wordProd P b l₂]
    exact (weylCoxeterSystem P b).wordProd_eq_colorClassProd col hl₂ hcol₂
  have hc_bip : wordProd P b l₁ * wordProd P b l₂ =
      (weylCoxeterSystem P b).bipartiteCoxeterElement col := by
    rw [hc₁_eq, hc₂_eq, CoxeterSystem.bipartiteCoxeterElement_def]
  have hl_nodup : (l₁ ++ l₂).Nodup := by
    rw [List.nodup_append]; refine ⟨hl₁, hl₂, fun i hi₁ j hi₂ hij ↦ ?_⟩; subst hij
    exact absurd ((hcol₁ i).1 hi₁) (by simp [(hcol₂ i).1 hi₂])
  have hl_all : ∀ i : b.support, i ∈ l₁ ++ l₂ := fun i ↦ by
    rw [List.mem_append, hcol₁, hcol₂]; cases col i <;> simp
  obtain ⟨κ, hκ, hκ_le, hκ_iff, y, hy0, hy⟩ :
      ∃ κ : ℝ, 0 < κ ∧ κ ≤ 2 ∧ (κ = 2 ↔ Subsingleton b.support) ∧
        ∃ y : b.support → ℝ, (∀ i, 0 < y i) ∧
          ∀ j : b.support, ∑ i : b.support, y i * P.pairingIn ℤ i j = κ * y j := by
    rcases subsingleton_or_nontrivial b.support with hsub | _
    · refine ⟨2, two_pos, le_rfl, ⟨fun _ ↦ hsub, fun _ ↦ rfl⟩,
        fun _ ↦ 1, fun _ ↦ one_pos, fun j ↦ ?_⟩
      rw [Finset.sum_eq_single j (fun i _ hij ↦ absurd (Subsingleton.elim i j) hij) (by simp),
        P.pairingIn_same ℤ j]; norm_num
    · obtain ⟨κ, hκ, hκ2, y, hy0, hyC⟩ :=
        (isFiniteType_cartanMatrix b).exists_pos_vecMul_eq_smul b.cartanMatrix_isIndecomposable
      refine ⟨κ, hκ, hκ2.le,
        ⟨fun h2 ↦ (hκ2.ne h2).elim, fun hsub ↦ absurd hsub (not_subsingleton _)⟩,
        y, hy0, fun j ↦ by
          simpa [Matrix.vecMul, dotProduct, Base.cartanMatrixIn_def] using congrFun hyC j⟩
  set v₁ : M := colorPart P b col y true
  set v₂ : M := colorPart P b col y false
  have hv_dom : v₁ + v₂ ∈ openDominantChamber P b := by
    rw [mem_openDominantChamber]; intro i hi
    simpa [v₁, v₂, coroot'_colorPart_add (c := col) hy ⟨i, hi⟩] using mul_pos hκ (hy0 ⟨i, hi⟩)
  have hc₁_v₁ : wordProd P b l₁ • v₁ = -v₁ := by
    rw [hc₁_eq, colorClassProd_smul_colorPart (P := P) (b := b) (c := col) hy true true]
    simp only [↓reduceIte, Algebra.algebraMap_self, RingHom.id_apply, two_smul]; abel
  have hc₁_v₂ : wordProd P b l₁ • v₂ = v₂ + (2 - κ) • v₁ := by
    rw [hc₁_eq, colorClassProd_smul_colorPart (P := P) (b := b) (c := col) hy true false]
    simp only [Bool.false_eq_true, ↓reduceIte, Algebra.algebraMap_self, RingHom.id_apply]
    rw [sub_eq_add_neg, ← neg_smul, neg_sub]
  have hc₂_v₂ : wordProd P b l₂ • v₂ = -v₂ := by
    rw [hc₂_eq, colorClassProd_smul_colorPart (P := P) (b := b) (c := col) hy false false]
    simp only [↓reduceIte, Algebra.algebraMap_self, RingHom.id_apply, two_smul]; abel
  have hc₂_v₁ : wordProd P b l₂ • v₁ = v₁ + (2 - κ) • v₂ := by
    rw [hc₂_eq, colorClassProd_smul_colorPart (P := P) (b := b) (c := col) hy false true]
    simp only [Bool.true_eq_false, ↓reduceIte, Algebra.algebraMap_self, RingHom.id_apply]
    rw [sub_eq_add_neg, ← neg_smul, neg_sub]
  have hlam_eq : 2 - κ = 2 * Real.cos (Real.pi / orderOf (wordProd P b l₁ * wordProd P b l₂)) := by
    rw [hc_bip]
    rcases subsingleton_or_nontrivial b.support with hsub | _
    · have hκ2 : κ = 2 := hκ_iff.2 hsub
      have h2le : 2 ≤ orderOf ((weylCoxeterSystem P b).bipartiteCoxeterElement col) := by
        rw [← hc_bip, ← wordProd_append]; exact P.two_le_orderOf_wordProd b hl_nodup hl_all
      have hc_sq : (weylCoxeterSystem P b).bipartiteCoxeterElement col *
          (weylCoxeterSystem P b).bipartiteCoxeterElement col = 1 := by
        obtain ⟨i₀⟩ := hne_supp
        have hl_len : (l₁ ++ l₂).length = 1 := by
          have h1 := List.Nodup.length_le_card hl_nodup
          have h2 : 0 < (l₁ ++ l₂).length := List.length_pos_of_mem (hl_all i₀)
          have h3 := Fintype.card_le_one_iff_subsingleton.2 hsub; omega
        rcases List.length_eq_one_iff.1 hl_len with ⟨a, ha⟩
        rw [← hc_bip, ← wordProd_append, ha, wordProd_cons, wordProd_nil, mul_one,
          weylGroup.ofIdx_mul_self]
      have hh2 : orderOf ((weylCoxeterSystem P b).bipartiteCoxeterElement col) = 2 :=
        le_antisymm (orderOf_le_of_pow_eq_one two_pos hc_sq) h2le
      rw [hκ2, sub_self, hh2, show Real.pi / ((2 : ℕ) : ℝ) = Real.pi / 2 by norm_num,
        Real.cos_pi_div_two, mul_zero]
    · exact two_sub_eq_two_mul_cos_pi_div_orderOf_bipartiteCoxeterElement P b col hy hy0 hκ
        (lt_of_le_of_ne hκ_le fun h2 ↦ absurd (hκ_iff.1 h2) (not_subsingleton _))
  refine ⟨v₁, v₂, hv_dom, hc₁_v₁, ?_, hc₂_v₂, ?_⟩ <;> rwa [← hlam_eq]

end RealCoxeterPlane

section ComplexRegularEigenvector

/-- **Regular eigenvector of a Coxeter element over `ℂ`.** Every Coxeter element `wordProd P b l`
of a finite irreducible reduced crystallographic root system over `ℂ` admits a regular weight `v`
with eigenvalue `(Complex.exp (2 * Real.pi * Complex.I / orderOf (wordProd P b l)))⁻¹`. -/
theorem exists_isRegularWeight_smul_eq_exp_neg_wordProd
    {ι M N : Type*} [AddCommGroup M] [Module ℂ M] [AddCommGroup N] [Module ℂ N]
    (P : RootPairing ι ℂ M N) [Finite ι] [P.IsCrystallographic] [P.IsReduced]
    [P.IsRootSystem] [P.IsIrreducible] (b : P.Base)
    {l : List b.support} (hl : l.Nodup) (hall : ∀ i, i ∈ l) :
    ∃ v : M, IsRegularWeight P v ∧
      wordProd P b l • v =
        (Complex.exp (2 * Real.pi * Complex.I / orderOf (wordProd P b l)))⁻¹ • v := by
  classical
  let := Fintype.ofFinite ι
  have := IsIrreducible.nontrivial P
  have : Nonempty b.support := by
    by_contra h; rw [not_nonempty_iff] at h
    exact not_subsingleton M b.toWeightBasis.equivFun.subsingleton
  have : Nonempty ι := ⟨(Classical.arbitrary b.support : ι)⟩
  obtain ⟨col⟩ := nonempty_coloring_graph_coxeterMatrixOfBase P b
  set c := (weylCoxeterSystem P b).bipartiteCoxeterElement col
  have hc_eig : ∃ v : M, IsRegularWeight P v ∧
      c • v = (Complex.exp (2 * Real.pi * Complex.I / orderOf c))⁻¹ • v := by
    rcases subsingleton_or_nontrivial b.support with hsub | _
    · obtain ⟨v, μ, hv_reg, hv_eig, hμ_prim⟩ :=
        P.exists_isRegularWeight_bipartiteCoxeterElement_smul_eq_smul_isPrimitiveRoot b col
      have hord : orderOf c = 2 := by
        obtain ⟨l₁, l₂, -, -, hl_nodup, hl_all, hl_eq⟩ :=
          (weylCoxeterSystem P b).exists_wordProd_eq_bipartiteCoxeterElement col
        have hc_word : c = wordProd P b (l₁ ++ l₂) := by
          rw [show c = (weylCoxeterSystem P b).bipartiteCoxeterElement col from rfl,
            ← hl_eq, weylCoxeterSystem_wordProd]
        have h2le : 2 ≤ orderOf c := by
          rw [hc_word]; exact P.two_le_orderOf_wordProd b hl_nodup hl_all
        have hl_len : (l₁ ++ l₂).length = 1 := by
          have h1 := List.Nodup.length_le_card hl_nodup
          have h2 : 0 < (l₁ ++ l₂).length :=
            List.length_pos_of_mem (hl_all (Classical.arbitrary b.support))
          have h3 := Fintype.card_le_one_iff_subsingleton.2 hsub; omega
        rcases List.length_eq_one_iff.1 hl_len with ⟨a, ha⟩
        have hc_sq : c * c = 1 := by
          rw [hc_word, ha, wordProd_cons, wordProd_nil, mul_one, weylGroup.ofIdx_mul_self]
        exact le_antisymm (orderOf_le_of_pow_eq_one two_pos hc_sq) h2le
      have hμ_sq : μ ^ 2 = 1 := hord ▸ hμ_prim.pow_eq_one
      have hμ_ne_one : μ ≠ 1 := hμ_prim.ne_one (hord ▸ by norm_num)
      have hμ_eq_neg_one : μ = -1 := (sq_eq_one_iff.1 hμ_sq).resolve_left hμ_ne_one
      have hexp_eq : (Complex.exp (2 * Real.pi * Complex.I / orderOf c))⁻¹ = -1 := by
        rw [hord, show (2 : ℂ) * Real.pi * Complex.I / ((2 : ℕ) : ℂ) = Real.pi * Complex.I by
          push_cast; ring, Complex.exp_pi_mul_I, inv_neg, inv_one]
      exact ⟨v, hv_reg, by rwa [hμ_eq_neg_one, ← hexp_eq] at hv_eig⟩
    · obtain ⟨κ, hκ, hκ2, y, hy0, hyC⟩ :=
        (isFiniteType_cartanMatrix b).exists_pos_vecMul_eq_smul b.cartanMatrix_isIndecomposable
      have hy : ∀ j : b.support, ∑ i : b.support, y i * P.pairingIn ℤ i j = κ * y j := fun j ↦ by
        simpa [Matrix.vecMul, dotProduct, Base.cartanMatrixIn_def] using congrFun hyC j
      have hlam : 2 - κ = 2 * Real.cos (Real.pi / orderOf c) :=
        two_sub_eq_two_mul_cos_pi_div_orderOf_bipartiteCoxeterElement P b col hy hy0 hκ hκ2
      set ν : ℂ := (Complex.exp (2 * Real.pi * Complex.I / orderOf c))⁻¹
      have hν_ne : ν ≠ 0 := inv_ne_zero (Complex.exp_ne_zero _)
      have hν_add : ν + ν⁻¹ = algebraMap ℝ ℂ (2 - κ) ^ 2 - 2 := by
        have h1 : ν + ν⁻¹ =
            ((2 * Real.cos (2 * (Real.pi / orderOf c)) : ℝ) : ℂ) := by
          have h := exp_mul_I_add_inv (2 * (Real.pi / orderOf c))
          have harg : ((2 * (Real.pi / orderOf c) : ℝ) : ℂ) * Complex.I =
              2 * Real.pi * Complex.I / orderOf c := by push_cast; ring
          rw [harg, add_comm] at h
          simpa [ν] using h
        rw [h1, Real.cos_two_mul,
          show 2 * (2 * Real.cos (Real.pi / orderOf c) ^ 2 - 1) =
            (2 * Real.cos (Real.pi / orderOf c)) ^ 2 - 2 by ring,
          ← hlam]
        simp only [Complex.coe_algebraMap]; push_cast; ring
      have hν : ν ^ 2 + (2 - algebraMap ℝ ℂ (2 - κ) ^ 2) * ν + 1 = 0 := by
        have h := congrArg (· * ν) hν_add
        rw [add_mul, inv_mul_cancel₀ hν_ne, ← sq] at h
        linear_combination h
      exact ⟨_, isRegularWeight_one_add_smul_colorPart_add_smul (c := col) hy hy0 hκ hκ2 hν,
        bipartiteCoxeterElement_smul_eigen (c := col) hy hν⟩
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
