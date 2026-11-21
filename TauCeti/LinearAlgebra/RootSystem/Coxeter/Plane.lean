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
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.LinearAlgebra.Eigenspace.Charpoly
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.RingTheory.RootsOfUnity.Complex
import TauCeti.LinearAlgebra.Matrix.PerronFrobenius.Irreducible
import TauCeti.LinearAlgebra.RootSystem.BaseChange.Rational
import TauCeti.LinearAlgebra.RootSystem.Coxeter.Element.Conj
import TauCeti.LinearAlgebra.RootSystem.Coxeter.FixedPoints
import TauCeti.LinearAlgebra.RootSystem.FiniteType.Perron
import TauCeti.LinearAlgebra.RootSystem.Weyl.BaseChange
import TauCeti.LinearAlgebra.RootSystem.Weyl.Chamber
import TauCeti.LinearAlgebra.RootSystem.Weyl.Pseudoreflection
import TauCeti.LinearAlgebra.RootSystem.Weyl.Transport

/-!
# The Coxeter plane and regular eigenvectors of Coxeter elements

For a finite irreducible reduced crystallographic root system `P` over `ℝ` with base `b` and
two-colouring `col` of its Dynkin diagram, Perron–Frobenius on the Cartan matrix constructs the
Steinberg–Coleman Coxeter plane `ℝ v₁ + ℝ v₂`, `v₁ + v₂ ∈ openDominantChamber P b`,
and dihedral parameter `2 cos (π / orderOf (c₁ * c₂))`. Transporting via
`b.equivBaseChangeRationalModel` to `ℂ` and conjugating yields a regular eigenvector of
eigenvalue `exp (2πi / orderOf c)⁻¹` for every Coxeter element `c = wordProd P b l` over `ℂ`.
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
  set c₁ := wordProd P b l₁; set c₂ := wordProd P b l₂; set c := c₁ * c₂
  have hc₁_eq : c₁ = (weylCoxeterSystem P b).colorClassProd col true := by
    dsimp only [c₁]; rw [← weylCoxeterSystem_wordProd P b l₁]
    exact (weylCoxeterSystem P b).wordProd_eq_colorClassProd col hl₁ hcol₁
  have hc₂_eq : c₂ = (weylCoxeterSystem P b).colorClassProd col false := by
    dsimp only [c₂]; rw [← weylCoxeterSystem_wordProd P b l₂]
    exact (weylCoxeterSystem P b).wordProd_eq_colorClassProd col hl₂ hcol₂
  have hc_word : c = wordProd P b (l₁ ++ l₂) := (wordProd_append b l₁ l₂).symm
  have hl_nodup : (l₁ ++ l₂).Nodup := by
    rw [List.nodup_append]; refine ⟨hl₁, hl₂, fun i hi₁ j hi₂ hij ↦ ?_⟩; subst hij
    exact absurd ((hcol₁ i).1 hi₁) (by simp [(hcol₂ i).1 hi₂])
  have hl_all : ∀ i : b.support, i ∈ l₁ ++ l₂ := fun i ↦ by
    rw [List.mem_append, hcol₁, hcol₂]; cases col i <;> simp
  set h : ℕ := orderOf c
  have h2le : 2 ≤ h := by
    dsimp only [h]; rw [hc_word]; exact P.two_le_orderOf_wordProd b hl_nodup hl_all
  have hh_pos : 0 < h := by omega
  have hc₁_sq : c₁ * c₁ = 1 := by
    rw [hc₁_eq]; exact (weylCoxeterSystem P b).colorClassProd_mul_self col true
  obtain ⟨κ, hκ, hκ_le, hκ_iff, y, hy_pos, hy_eig⟩ :
      ∃ κ : ℝ, 0 < κ ∧ κ ≤ 2 ∧ (κ = 2 ↔ Subsingleton b.support) ∧
        ∃ y : b.support → ℝ, (∀ i, 0 < y i) ∧
          ∀ j : b.support, ∑ i : b.support, y i * (b.cartanMatrix i j : ℝ) = κ * y j := by
    rcases subsingleton_or_nontrivial b.support with hsub | _
    · refine ⟨2, two_pos, le_rfl, ⟨fun _ ↦ hsub, fun _ ↦ rfl⟩,
        fun _ ↦ 1, fun _ ↦ one_pos, fun j ↦ ?_⟩
      rw [Finset.sum_eq_single j (fun i _ hij ↦ absurd (Subsingleton.elim i j) hij) (by simp),
        show b.cartanMatrix j j = 2 from P.pairingIn_same ℤ j]; norm_num
    · obtain ⟨κ, hκ, hκ2, y, hy_pos, hyC⟩ :=
        (isFiniteType_cartanMatrix b).exists_pos_vecMul_eq_smul b.cartanMatrix_isIndecomposable
      refine ⟨κ, hκ, hκ2.le,
        ⟨fun h2 ↦ (hκ2.ne h2).elim, fun hsub ↦ absurd hsub (not_subsingleton _)⟩,
        y, hy_pos, fun j ↦ by simpa [Matrix.vecMul, dotProduct] using congrFun hyC j⟩
  set lam : ℝ := 2 - κ
  set yPart : Bool → b.support → ℝ := fun b0 i ↦ if col i = b0 then y i else 0
  set u : Bool → M := fun b0 ↦ ∑ i : b.support, yPart b0 i • P.root i
  set y₁ := yPart true; set y₂ := yPart false; set v₁ := u true; set v₂ := u false
  have hcor_part (b0 : Bool) (j : b.support) :
      P.coroot' j (u b0) = if col j = b0 then 2 * y j else -(lam * y j) := by
    dsimp only [u, yPart]; rw [map_sum]
    simp_rw [map_smul, smul_eq_mul, P.root_coroot'_eq_pairing, ← P.algebraMap_pairingIn ℤ]
    change ∑ i : b.support, (if col i = b0 then y i else 0) * (b.cartanMatrix i j : ℝ) = _
    have hsame (b' : Bool) (hb' : col j = b') :
        ∑ i : b.support, (if col i = b' then y i else 0) * (b.cartanMatrix i j : ℝ) =
          2 * y j := by
      rw [Finset.sum_eq_single j (fun i _ hij ↦ ?_) (by simp), ite_eq_left hb']
      · rw [show b.cartanMatrix j j = 2 from P.pairingIn_same ℤ j]; norm_num; ring
      · split_ifs with hi
        · simp [Base.cartanMatrix, Base.cartanMatrixIn_def,
            pairingIn_eq_zero_of_color_eq P b col hij (hi.trans hb'.symm)]
        · simp
    by_cases hj : col j = b0
    · rw [ite_eq_left hj]; exact hsame b0 hj
    · rw [ite_eq_right hj]
      have hother : col j = !b0 := by cases h1 : col j <;> cases b0 <;> simp_all
      have htot : ∑ i : b.support, (if col i = b0 then y i else 0) * (b.cartanMatrix i j : ℝ) +
          ∑ i : b.support, (if col i = !b0 then y i else 0) * (b.cartanMatrix i j : ℝ) =
            κ * y j := by
        rw [← Finset.sum_add_distrib, ← hy_eig j]
        exact Finset.sum_congr rfl fun i _ ↦ by cases col i <;> cases b0 <;> simp
      rw [hsame (!b0) hother] at htot; linarith
  have hv_dom : v₁ + v₂ ∈ openDominantChamber P b := by
    rw [mem_openDominantChamber]; intro i hi; let j : b.support := ⟨i, hi⟩
    change 0 < P.coroot' j (v₁ + v₂); rw [map_add, hcor_part true j, hcor_part false j]
    cases col j <;> simp <;> linarith [mul_pos hκ (hy_pos j)]
  have hc_action (b0 : Bool) (c' : P.weylGroup)
      (hc_eq : c' = (weylCoxeterSystem P b).colorClassProd col b0) :
      c' • u b0 = -u b0 ∧ c' • u (!b0) = u (!b0) + lam • u b0 := by
    rw [hc_eq, colorClassProd_smul, colorClassProd_smul]; constructor
    · have hsum : ∑ j : b.support, (if col j = b0 then P.coroot' j (u b0) else 0) • P.root j =
          2 • u b0 := by
        dsimp only [u]; rw [Finset.smul_sum]; refine Finset.sum_congr rfl fun j _ ↦ ?_
        by_cases hj : col j = b0
        · rw [ite_eq_left hj, hcor_part b0 j, ite_eq_left hj]
          dsimp only [yPart]; rw [ite_eq_left hj, two_mul, add_smul, two_smul]
        · simp [hj, yPart]
      rw [hsum, two_smul]; abel
    · have hsum : ∑ j : b.support,
          (if col j = b0 then P.coroot' j (u (!b0)) else 0) • P.root j = -(lam • u b0) := by
        dsimp only [u]; rw [Finset.smul_sum, ← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun j _ ↦ ?_
        by_cases hj : col j = b0
        · have hne : col j ≠ !b0 := by cases b0 <;> simp_all
          rw [ite_eq_left hj, hcor_part (!b0) j, ite_eq_right hne]
          dsimp only [yPart]; rw [ite_eq_left hj, neg_smul, mul_smul]
        · simp [hj, yPart]
      rw [hsum, sub_neg_eq_add]
  obtain ⟨hc₁_v₁, hc₁_v₂⟩ := hc_action true c₁ hc₁_eq
  obtain ⟨hc₂_v₂, hc₂_v₁⟩ := hc_action false c₂ hc₂_eq
  simp only [Bool.not_true, Bool.not_false] at hc₁_v₂ hc₂_v₁
  have hlam_eq : lam = 2 * Real.cos (Real.pi / h) := by
    rcases subsingleton_or_nontrivial b.support with hsub | _
    · have hκ2 : κ = 2 := hκ_iff.2 hsub
      have hc_sq : c * c = 1 := by
        obtain ⟨i₀⟩ := hne_supp
        have hl_len : (l₁ ++ l₂).length = 1 := by
          have h1 := List.Nodup.length_le_card hl_nodup
          have h2 : 0 < (l₁ ++ l₂).length := List.length_pos_of_mem (hl_all i₀)
          have h3 := Fintype.card_le_one_iff_subsingleton.2 hsub; omega
        rcases List.length_eq_one_iff.1 hl_len with ⟨a, ha⟩
        rw [hc_word, ha, wordProd_cons, wordProd_nil, mul_one, weylGroup.ofIdx_mul_self]
      have hh2 : h = 2 := le_antisymm (orderOf_le_of_pow_eq_one two_pos hc_sq) h2le
      rw [show lam = 0 by linarith, hh2, show Real.pi / ((2 : ℕ) : ℝ) = Real.pi / 2 by norm_num,
        Real.cos_pi_div_two, mul_zero]
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
      rw [hsum, hy_eig i]; ring
    let M₁ := LinearMap.toMatrix b.toWeightBasis b.toWeightBasis (P.weylGroupRootRep c₁)
    let M₂ := LinearMap.toMatrix b.toWeightBasis b.toWeightBasis (P.weylGroupRootRep c₂)
    set M₁C : Matrix b.support b.support ℂ := M₁.map Complex.ofRealHom
    set M₂C : Matrix b.support b.support ℂ := M₂.map Complex.ofRealHom
    have hM_mul : M₁ * M₂ =
        LinearMap.toMatrix b.toWeightBasis b.toWeightBasis (P.weylGroupRootRep c) := by
      simp only [M₁, M₂, c, map_mul, LinearMap.toMatrix_mul]
    have hM₁C_sq : M₁C * M₁C = 1 := by
      have hM₁_sq : M₁ * M₁ = 1 := by
        simp only [M₁, ← LinearMap.toMatrix_mul, ← map_mul, hc₁_sq, map_one,
          LinearMap.toMatrix_one]
      change (RingHom.mapMatrix Complex.ofRealHom) M₁ *
        (RingHom.mapMatrix Complex.ofRealHom) M₁ = 1
      rw [← map_mul, hM₁_sq, map_one]
    have hrep_vec (x : b.support → ℝ) :
        (b.toWeightBasis.repr (∑ i : b.support, x i • P.root i) : b.support → ℝ) = x := by
      ext j; simp_rw [map_sum, map_smul, ← b.toWeightBasis_apply, b.toWeightBasis.repr_self]
      simp [Finsupp.single_apply]
    have hM_color_mul (b0 : Bool) (c' : P.weylGroup)
        (hc_eq : c' = (weylCoxeterSystem P b).colorClassProd col b0) (z : b.support → ℂ)
        (i : b.support) :
        ((LinearMap.toMatrix b.toWeightBasis b.toWeightBasis
            (P.weylGroupRootRep c')).map Complex.ofRealHom *ᵥ z) i = if col i = b0 then
            -z i + ∑ j : b.support, (if col j = !b0 then (A i j : ℂ) * z j else 0)
          else z i := by
      have hEntry (j : b.support) :
          (LinearMap.toMatrix b.toWeightBasis b.toWeightBasis (P.weylGroupRootRep c') i j : ℂ) =
            if col i = b0 then
              if i = j then (-1 : ℂ) else if col j = !b0 then (A i j : ℂ) else 0
            else if i = j then 1 else 0 := by
        rw [LinearMap.toMatrix_apply, b.toWeightBasis_apply]
        change (b.toWeightBasis.repr (c' • P.root j) i : ℂ) = _
        have hsum_repr : ∑ k : b.support, b.toWeightBasis.repr
            ((if col k = b0 then P.coroot' k (P.root j) else 0) • P.root k) i =
            if col i = b0 then P.coroot' i (P.root j) else 0 := by
          simpa [map_sum, Finset.sum_apply'] using
            congrFun (hrep_vec fun k ↦ if col k = b0 then P.coroot' k (P.root j) else 0) i
        rw [hc_eq, colorClassProd_smul, map_sub, map_sum, Finsupp.sub_apply, Finset.sum_apply',
          hsum_repr, show b.toWeightBasis.repr (P.root j) = Finsupp.single j 1 by
            rw [← b.toWeightBasis_apply j, b.toWeightBasis.repr_self], Finsupp.single_apply]
        by_cases hci : col i = b0
        · rw [ite_eq_left hci, ite_eq_left hci]
          by_cases hij : i = j
          · subst hij; simp [P.root_coroot'_eq_pairing]; norm_num
          · rw [ite_eq_right (Ne.symm hij), ite_eq_right hij, P.root_coroot'_eq_pairing,
              ← P.algebraMap_pairingIn ℤ]
            change (((0 - (b.cartanMatrix j i : ℝ)) : ℝ) : ℂ) = _
            by_cases hcj : col j = !b0
            · simp [hcj, A, hij]
            · have hsame : col j = col i := by cases h1 : col j <;> cases b0 <;> simp_all
              simp [hcj, Base.cartanMatrix, Base.cartanMatrixIn_def,
                pairingIn_eq_zero_of_color_eq P b col (Ne.symm hij) hsame]
        · rw [ite_eq_right hci, ite_eq_right hci]; by_cases hij : i = j <;> simp [hij, eq_comm]
      simp only [mulVec, dotProduct, Matrix.map_apply, Complex.ofRealHom_eq_coe]
      by_cases hci : col i = b0
      · rw [ite_eq_left hci, show ∑ j : b.support,
            (LinearMap.toMatrix b.toWeightBasis b.toWeightBasis (P.weylGroupRootRep c') i j : ℂ) *
              z j = ∑ j : b.support,
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
    have hM₁C_mul := hM_color_mul true c₁ hc₁_eq
    have hM₂C_mul := hM_color_mul false c₂ hc₂_eq
    simp only [Bool.not_true, Bool.not_false] at hM₁C_mul hM₂C_mul
    have hmulVec_ofReal (M : Matrix b.support b.support ℝ) (x : b.support → ℝ) :
        M.map Complex.ofRealHom *ᵥ (fun i ↦ (x i : ℂ)) = fun i ↦ ((M *ᵥ x) i : ℂ) := by
      ext i; simp [mulVec, dotProduct]
    have hM_apply (g : P.weylGroup) (x : b.support → ℝ) :
        LinearMap.toMatrix b.toWeightBasis b.toWeightBasis (P.weylGroupRootRep g) *ᵥ x =
          b.toWeightBasis.repr (g • ∑ i : b.support, x i • P.root i) := by
      have h1 := LinearMap.toMatrix_mulVec_repr b.toWeightBasis b.toWeightBasis
        (P.weylGroupRootRep g) (∑ i : b.support, x i • P.root i)
      rwa [hrep_vec] at h1
    have hM_col {g : P.weylGroup} {x w : b.support → ℝ}
        (hw : g • ∑ i : b.support, x i • P.root i = ∑ i : b.support, w i • P.root i) :
        LinearMap.toMatrix b.toWeightBasis b.toWeightBasis (P.weylGroupRootRep g) *ᵥ x = w := by
      rw [hM_apply, hw]; exact hrep_vec w
    have hsum_add (r : ℝ) (a1 a2 : b.support → ℝ) :
        (∑ i : b.support, a1 i • P.root i) + r • (∑ i : b.support, a2 i • P.root i) =
          ∑ i : b.support, (a1 + r • a2) i • P.root i := by
      simp only [Finset.smul_sum, ← Finset.sum_add_distrib, Pi.add_apply, Pi.smul_apply,
        smul_eq_mul, add_smul, smul_smul]
    have hM₁y₁ : M₁ *ᵥ y₁ = -y₁ :=
      hM_col (by simpa [v₁, u, y₁, neg_smul, Finset.sum_neg_distrib] using hc₁_v₁)
    have hM₁y₂ : M₁ *ᵥ y₂ = y₂ + lam • y₁ :=
      hM_col (by rw [← hsum_add]; exact hc₁_v₂)
    have hM₂y₂ : M₂ *ᵥ y₂ = -y₂ :=
      hM_col (by simpa [v₂, u, y₂, neg_smul, Finset.sum_neg_distrib] using hc₂_v₂)
    have hM₂y₁ : M₂ *ᵥ y₁ = y₁ + lam • y₂ :=
      hM_col (by rw [← hsum_add]; exact hc₂_v₁)
    set y₁C : b.support → ℂ := fun i ↦ (y₁ i : ℂ)
    set y₂C : b.support → ℂ := fun i ↦ (y₂ i : ℂ)
    set z₀ : b.support → ℂ := y₁C + μ • y₂C
    have hz₀_ne : z₀ ≠ 0 := fun h0 ↦ by
      obtain ⟨i₀⟩ := hne_supp
      have hi0 : (y₁ i₀ : ℂ) + μ * (y₂ i₀ : ℂ) = 0 := by
        simpa [z₀, y₁C, y₂C] using congrFun h0 i₀
      cases hci : col i₀
      · have h0' : μ * (y i₀ : ℂ) = 0 := by simpa [y₁, y₂, yPart, hci] using hi0
        exact (mul_eq_zero.1 h0').elim hμ_ne (Complex.ofReal_ne_zero.2 (hy_pos i₀).ne')
      · have h0' : (y i₀ : ℂ) = 0 := by simpa [y₁, y₂, yPart, hci] using hi0
        exact (hy_pos i₀).ne' (Complex.ofReal_eq_zero.1 h0')
    have hz₀_eig : (M₁C * M₂C) *ᵥ z₀ = ζ⁻¹ • z₀ := by
      rw [← mulVec_mulVec]
      have hd := dihedral_eigenvector (Matrix.toLin' M₁C) (Matrix.toLin' M₂C) (x₁ := y₁C)
        (x₂ := y₂C) hμ_ne
        (by ext i; simpa [M₁C, y₁C, hM₁y₁] using congrFun (hmulVec_ofReal M₁ y₁) i)
        (by ext i; rw [hμ_add_inv]
            simpa [M₁C, y₁C, y₂C, hM₁y₂] using congrFun (hmulVec_ofReal M₁ y₂) i)
        (by ext i; simpa [M₂C, y₂C, hM₂y₂] using congrFun (hmulVec_ofReal M₂ y₂) i)
        (by ext i; rw [hμ_add_inv]
            simpa [M₂C, y₁C, y₂C, hM₂y₁] using congrFun (hmulVec_ofReal M₂ y₁) i)
      simpa [Matrix.toLin'_apply, z₀, ζ] using hd
    have hM_pow (k : ℕ) : (M₁ * M₂) ^ k =
        LinearMap.toMatrix b.toWeightBasis b.toWeightBasis (P.weylGroupRootRep (c ^ k)) := by
      induction k with
      | zero => simp [LinearMap.toMatrix_one]
      | succ k ih => rw [pow_succ, pow_succ, ih, hM_mul, ← LinearMap.toMatrix_mul, ← map_mul]
    have hM_mul_map : M₁C * M₂C = (M₁ * M₂).map Complex.ofRealHom :=
      ((RingHom.mapMatrix Complex.ofRealHom).map_mul M₁ M₂).symm
    have hM_pow_map (k : ℕ) :
        (M₁C * M₂C) ^ k = ((M₁ * M₂) ^ k).map Complex.ofRealHom := by
      rw [hM_mul_map]; exact ((RingHom.mapMatrix Complex.ofRealHom).map_pow (M₁ * M₂) k).symm
    have hM_pow_eig (k : ℕ) : ((M₁C * M₂C) ^ k) *ᵥ z₀ = (ζ⁻¹) ^ k • z₀ := by
      induction k with
      | zero => simp
      | succ k ih =>
        rw [pow_succ', ← mulVec_mulVec, ih, mulVec_smul, hz₀_eig, smul_smul, mul_comm,
          ← pow_succ']
    have hζ_prim : IsPrimitiveRoot ζ h := by
      rw [IsPrimitiveRoot.iff_def]; refine ⟨?_, fun k hk ↦ ?_⟩
      · have hchC : (M₁C * M₂C) ^ h = 1 := by
          rw [hM_pow_map, hM_pow, pow_orderOf_eq_one, map_one, LinearMap.toMatrix_one]
          exact (RingHom.mapMatrix Complex.ofRealHom).map_one
        have h1 := hM_pow_eig h; rw [hchC, one_mulVec] at h1
        obtain ⟨i₀, hi₀⟩ := Function.ne_iff.1 hz₀_ne
        have hinv1 : (ζ⁻¹) ^ h = 1 := mul_right_cancel₀ hi₀
          (by simpa [Pi.smul_apply, smul_eq_mul] using (congrFun h1 i₀).symm)
        rwa [inv_pow, inv_eq_one] at hinv1
      · have h1 := hM_pow_eig k; rw [inv_pow, hk, inv_one, one_smul, hM_pow_map] at h1
        rw [show z₀ = y₁C + μ • y₂C from rfl, mulVec_add, mulVec_smul, hmulVec_ofReal,
          hmulVec_ofReal] at h1
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
        have hck_fix : c ^ k • (v₁ + v₂) = v₁ + v₂ := by
          apply b.toWeightBasis.repr.injective; ext i
          have hsum_vec : ∑ j : b.support, (y₁ + y₂) j • P.root j = v₁ + v₂ := by
            simp [v₁, v₂, u, y₁, y₂, add_smul, Finset.sum_add_distrib]
          have hact := congrFun (hM_apply (c ^ k) (y₁ + y₂)) i
          rw [← hM_pow, mulVec_add, hy₁_fix, hy₂_fix, hsum_vec] at hact
          exact hact.symm.trans (by rw [← hsum_vec, hrep_vec])
        exact orderOf_dvd_of_pow_eq_one
          (eq_one_of_smul_eq_self_of_mem_openDominantChamber P b _ hv_dom hck_fix)
    have : Module.Finite ℝ M := Module.Finite.of_basis b.toWeightBasis
    obtain ⟨p, hp⟩ := P.exists_map_rat_eq_charpoly_weylGroupRootRep_of_base b c
    have hp_map : p.map (algebraMap ℚ ℂ) = (M₁C * M₂C).charpoly := by
      rw [hM_mul_map, Matrix.charpoly_map, hM_mul, LinearMap.charpoly_toMatrix, ← hp,
        Polynomial.map_map]; congr 1
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
      (spectral_bound_of_bipartite_eigenvector hA_nonneg hA_same hy_pos hA_eig
        hM₁C_sq hM₁C_mul hM₂C_mul (Complex.exp_ne_zero _) hz.2
        (Module.End.mem_eigenspace_iff.1 hz.1))
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
  set Q := b.rationalModel; set hQ := b.rationalModel_toLinearMap
  set PR := rootPairingBaseChange ℝ Q hQ; set PC := rootPairingBaseChange ℂ Q hQ
  let bR : PR.Base := rootPairingBaseChangeBase ℝ Q hQ b.rationalModelBase
  let bC : PC.Base := rootPairingBaseChangeBase ℂ Q hQ b.rationalModelBase
  obtain ⟨col⟩ := nonempty_coloring_graph_coxeterMatrixOfBase PR bR
  let l₁R : List bR.support := (Finset.univ.filter fun i : bR.support ↦ col i = true).toList
  let l₂R : List bR.support := (Finset.univ.filter fun i : bR.support ↦ col i = false).toList
  have hcol₁ (i : bR.support) : i ∈ l₁R ↔ col i = true := by simp [l₁R]
  have hcol₂ (i : bR.support) : i ∈ l₂R ↔ col i = false := by simp [l₂R]
  have hlR_nodup : (l₁R ++ l₂R).Nodup := List.nodup_append.2 ⟨Finset.nodup_toList _,
    Finset.nodup_toList _, fun i hi₁ j hi₂ hij ↦
      absurd ((hcol₁ i).1 hi₁) (by subst hij; simp [(hcol₂ i).1 hi₂])⟩
  have hallR (i : bR.support) : i ∈ l₁R ++ l₂R := by
    rw [List.mem_append, hcol₁, hcol₂]; cases col i <;> simp
  obtain ⟨v₁, v₂, hv_dom, hc₁_v₁, hc₁_v₂, hc₂_v₂, hc₂_v₁⟩ :=
    PR.exists_coxeterPlane_bipartite bR col (Finset.nodup_toList _) (Finset.nodup_toList _)
      hcol₁ hcol₂
  let eRC : bR.support ≃ bC.support :=
    (supportEquivRootPairingBaseChangeBase ℝ Q hQ b.rationalModelBase).trans
      (supportEquivRootPairingBaseChangeBase ℂ Q hQ b.rationalModelBase).symm
  have heRC_coe (i : bR.support) : ((eRC i : ι)) = (i : ι) := by
    have h1 := coe_supportEquivRootPairingBaseChangeBase ℂ Q hQ b.rationalModelBase (eRC i)
    simp only [eRC, _root_.Equiv.trans_apply, _root_.Equiv.apply_symm_apply] at h1
    exact h1.symm.trans (coe_supportEquivRootPairingBaseChangeBase ℝ Q hQ b.rationalModelBase i)
  set c₁R := wordProd PR bR l₁R; set c₂R := wordProd PR bR l₂R; set cR := c₁R * c₂R
  set c₁C := wordProd PC bC (l₁R.map eRC)
  set c₂C := wordProd PC bC (l₂R.map eRC); set cC := c₁C * c₂C
  let toC := Pi.algebraMap b.support ℝ ℂ
  have hcoroot'_ofReal (j : ι) (x : b.support → ℝ) :
      PC.coroot' j (toC x) = (PR.coroot' j x : ℂ) := by
    simp only [coroot', LinearMap.flip_apply, toLinearMap_rootPairingBaseChange,
      coroot_rootPairingBaseChange, piAlgebraMap_apply, dotProduct, toC, PC, PR]; push_cast; simp
  have hword_ofReal (m : List bR.support) (x : b.support → ℝ) :
      wordProd PC bC (m.map eRC) • toC x = toC (wordProd PR bR m • x) := by
    induction m with
    | nil => simp
    | cons a t ih =>
      rw [List.map_cons, wordProd_cons, wordProd_cons, mul_smul, mul_smul, ih, heRC_coe,
        weylGroup.ofIdx_smul, weylGroup.ofIdx_smul, Equiv.reflection_smul, Equiv.reflection_smul,
        reflection_apply, reflection_apply, hcoroot'_ofReal]
      ext k; simp [toC, root_rootPairingBaseChange, piAlgebraMap_apply, PC, PR]
  let eRC_W : PR.weylGroup ≃* PC.weylGroup :=
    (weylGroupBaseChangeEquiv ℝ Q hQ).symm.trans (weylGroupBaseChangeEquiv ℂ Q hQ)
  have heRC_W_word (m : List bR.support) :
      eRC_W (wordProd PR bR m) = wordProd PC bC (m.map eRC) := by
    induction m with
    | nil => simp
    | cons a t ih =>
      rw [List.map_cons, wordProd_cons, wordProd_cons, map_mul, ih, heRC_coe]
      dsimp only [eRC_W, PR, PC]
      rw [MulEquiv.trans_apply, weylGroupBaseChangeEquiv_symm_ofIdx, weylGroupBaseChangeEquiv_ofIdx]
  have horder_eq : orderOf cC = orderOf cR := by
    rw [show cC = eRC_W cR by simp [cC, cR, c₁C, c₂C, c₁R, c₂R, map_mul, heRC_W_word]]
    exact orderOf_injective eRC_W.toMonoidHom eRC_W.injective cR
  set h : ℕ := orderOf cR
  have h2le : 2 ≤ h := by
    have := IsIrreducible.nontrivial PR
    rw [show h = orderOf (wordProd PR bR (l₁R ++ l₂R)) by
      simp [h, cR, c₁R, c₂R, wordProd_append]]
    exact PR.two_le_orderOf_wordProd bR hlR_nodup hallR
  have _ : 0 < h := by omega
  set φ : ℝ := Real.pi / h; set μ : ℂ := Complex.exp ((φ : ℂ) * Complex.I)
  have hsinφ_pos : 0 < Real.sin φ := Real.sin_pos_of_pos_of_lt_pi (by positivity) (by
    have h2 : (2 : ℝ) ≤ h := by exact_mod_cast h2le
    linarith [Real.pi_pos, div_le_div_of_nonneg_left Real.pi_pos.le (by norm_num) h2])
  have hμ_ne : μ ≠ 0 := Complex.exp_ne_zero _
  have hμ_add : μ + μ⁻¹ = ((2 * Real.cos φ : ℝ) : ℂ) := exp_mul_I_add_inv φ
  have hμ_sq : μ ^ 2 = Complex.exp (2 * Real.pi * Complex.I / h) := by
    simp only [μ, φ, sq, ← Complex.exp_add]; congr 1; push_cast; ring
  set vC : b.support → ℂ := toC v₁ + μ • toC v₂
  have hvC_reg : IsRegularWeight PC vC := (isRegularWeight_iff PC vC).2 fun j hj ↦ by
    have hdom_reg := isRegularWeight_of_mem_openDominantChamber PR bR hv_dom
    simp only [vC, map_add, map_smul, smul_eq_mul, hcoroot'_ofReal] at hj
    have h2 : PR.coroot' j v₂ = 0 := (mul_eq_zero.1 (by
      simpa [μ, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin] using
        congrArg Complex.im hj)).resolve_left hsinφ_pos.ne'
    have h1 : PR.coroot' j v₁ = 0 := by simpa [h2] using congrArg Complex.re hj
    exact (isRegularWeight_iff PR _).1 hdom_reg j (by simp [map_add, h1, h2])
  have hvC_eig : cC • vC = (Complex.exp (2 * Real.pi * Complex.I / orderOf cC))⁻¹ • vC := by
    have htoC_neg (x : b.support → ℝ) : toC (-x) = -toC x := map_neg toC x
    have htoC_add (x y : b.support → ℝ) : toC (x + y) = toC x + toC y := map_add toC x y
    have htoC_smul (r : ℝ) (x : b.support → ℝ) : toC (r • x) = (r : ℂ) • toC x := by
      ext; simp [toC, piAlgebraMap_apply]
    have hc_ofReal (m : List bR.support) {x y : b.support → ℝ}
        (hxy : wordProd PR bR m • x = y) :
        PC.weylGroupRootRep (wordProd PC bC (m.map eRC)) (toC x) = toC y := by
      change wordProd PC bC (m.map eRC) • toC x = toC y; rw [hword_ofReal, hxy]
    have hd := dihedral_eigenvector (PC.weylGroupRootRep c₁C) (PC.weylGroupRootRep c₂C)
      (x₁ := toC v₁) (x₂ := toC v₂) hμ_ne ((hc_ofReal l₁R hc₁_v₁).trans (htoC_neg _))
      ((hc_ofReal l₁R hc₁_v₂).trans (by rw [htoC_add, htoC_smul, ← hμ_add]))
      ((hc_ofReal l₂R hc₂_v₂).trans (htoC_neg _))
      ((hc_ofReal l₂R hc₂_v₁).trans (by rw [htoC_add, htoC_smul, ← hμ_add]))
    change PC.weylGroupRootRep (c₁C * c₂C) vC = _
    rw [map_mul, mul_apply_eq_comp, hd, hμ_sq, horder_eq]
  let eqv := b.equivBaseChangeRationalModel
  let eCB : bC.support ≃ b.support :=
    (supportEquivRootPairingBaseChangeBase ℂ Q hQ b.rationalModelBase).trans
      b.supportEquivRationalModelBase
  have heCB_coe (i : bC.support) : ((eCB i : ι)) = (i : ι) :=
    (b.coe_supportEquivRationalModelBase _).trans
      (coe_supportEquivRootPairingBaseChangeBase ℂ Q hQ b.rationalModelBase i)
  let lBip : List b.support := (l₁R ++ l₂R).map (eRC.trans eCB)
  have hlBip_nodup : lBip.Nodup := hlR_nodup.map (eRC.trans eCB).injective
  have hword_eqv : eqv.weylGroupEquiv (wordProd P b lBip) = cC := by
    rw [show cC = wordProd PC bC ((l₁R ++ l₂R).map eRC) by
        simp [cC, c₁C, c₂C, ← wordProd_append, List.map_append],
      show lBip = ((l₁R ++ l₂R).map eRC).map eCB by simp [lBip, List.map_map]]
    induction (l₁R ++ l₂R).map eRC with
    | nil => simp
    | cons a t ih =>
      rw [List.map_cons, wordProd_cons, wordProd_cons, map_mul, ih, Equiv.weylGroupEquiv_ofIdx,
        b.equivBaseChangeRationalModel_indexEquiv, _root_.Equiv.refl_apply, heCB_coe]
  set vBip : M := eqv.weightEquiv.symm vC
  have hvBip_reg : IsRegularWeight P vBip := (isRegularWeight_iff P _).2 fun j hj ↦ by
    have h1 := eqv.coroot'_weightEquiv j vBip
    rw [show eqv.indexEquiv j = j by simp [eqv], eqv.weightEquiv.apply_symm_apply] at h1
    exact (isRegularWeight_iff PC vC).1 hvC_reg j (h1.trans hj)
  have horder_bip : orderOf (wordProd P b lBip) = orderOf cC :=
    (orderOf_injective eqv.weylGroupEquiv.toMonoidHom eqv.weylGroupEquiv.injective _).symm.trans
      (congrArg orderOf hword_eqv)
  have hvBip_eig : wordProd P b lBip • vBip =
      (Complex.exp (2 * Real.pi * Complex.I / orderOf (wordProd P b lBip)))⁻¹ • vBip := by
    apply eqv.weightEquiv.injective
    rw [← eqv.weylGroupEquiv_smul, hword_eqv, map_smul]; simpa [vBip, horder_bip] using hvC_eig
  have hperm : lBip.Perm l := (List.perm_ext_iff_of_nodup hlBip_nodup hl).2 fun i ↦ by
    simp only [lBip, List.mem_map, hall, iff_true]
    exact ⟨(eRC.trans eCB).symm i, hallR _, (eRC.trans eCB).apply_symm_apply i⟩
  obtain ⟨u, hu⟩ := P.isConj_wordProd_of_perm b hlBip_nodup hperm
  have hconj : (MulAut.conj (u : P.weylGroup)) (wordProd P b lBip) = wordProd P b l := by
    rw [MulAut.conj_apply, hu.eq, mul_assoc, mul_inv_cancel, mul_one]
  have hord_conj : orderOf (wordProd P b l) = orderOf (wordProd P b lBip) := by
    rw [← hconj]; exact orderOf_injective (MulAut.conj (u : P.weylGroup)).toMonoidHom
      (MulAut.conj (u : P.weylGroup)).injective _
  refine ⟨(u : P.weylGroup) • vBip,
    (isRegularWeight_smul P (u : P.weylGroup) vBip).2 hvBip_reg, ?_⟩
  rw [hord_conj, ← mul_smul, ← hu.eq, mul_smul, hvBip_eig]
  change (P.weylGroupRootRep (u : P.weylGroup)) _ = _; rw [map_smul]; rfl

end ComplexRegularEigenvector

end RootPairing
