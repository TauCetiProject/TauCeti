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
import Mathlib.LinearAlgebra.Eigenspace.Charpoly
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.RingTheory.RootsOfUnity.Complex
import TauCeti.Analysis.Complex.Angle
import TauCeti.GroupTheory.Coxeter.CoxeterElement
import TauCeti.LinearAlgebra.Eigenspace.Comp
import TauCeti.LinearAlgebra.Matrix.PerronFrobenius.Irreducible
import TauCeti.LinearAlgebra.Matrix.PerronFrobenius.Positive
import TauCeti.LinearAlgebra.RootSystem.Coxeter.Element.ActsBy
import TauCeti.LinearAlgebra.RootSystem.Coxeter.Element.Regular
import TauCeti.LinearAlgebra.RootSystem.Coxeter.FixedPoints
import TauCeti.LinearAlgebra.RootSystem.FiniteType.Irreducible
import TauCeti.LinearAlgebra.RootSystem.FiniteType.Perron
import TauCeti.LinearAlgebra.RootSystem.Weyl.Chamber

/-!
# The Coxeter plane and regular eigenvectors of Coxeter elements

This file constructs the Steinberg–Coleman Coxeter plane of an irreducible finite reduced
crystallographic root system and produces regular eigenvectors of its Coxeter elements over `ℂ`.

## Main results

* `RootPairing.exists_coxeterPlane_bipartite`: over `ℝ`, every bipartite Coxeter element
  `wordProd P b l₁ * wordProd P b l₂` admits vectors `v₁, v₂` with `v₁ + v₂` in the open
  dominant chamber on which `wordProd P b l₁` and `wordProd P b l₂` act by dihedral formulas
  with parameter `2 * Real.cos (Real.pi / orderOf (wordProd P b l₁ * wordProd P b l₂))`.
* `RootPairing.exists_isRegularWeight_wordProd_smul_eq_inv_exp_smul`: over `ℂ`, every Coxeter
  element `wordProd P b l` admits a regular eigenvector with eigenvalue
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

/-- Pushing a real linear combination of simple roots by a Weyl-group element acting by an
integer matrix `W` multiplies its coefficient vector on the left by `W`. -/
private lemma actsBy_smul_sum_algebraMap_root
    {ι K M N : Type*} [CommRing K] [Algebra ℝ K] [AddCommGroup M] [Module K M]
    [AddCommGroup N] [Module K N] {P : RootPairing ι K M N} {b : P.Base}
    {g : P.weylGroup} {W : Matrix b.support b.support ℤ} (hgW : b.ActsBy g W)
    (x : b.support → ℝ) :
    g • (∑ i : b.support, algebraMap ℝ K (x i) • P.root i) =
      ∑ i : b.support, algebraMap ℝ K ((W.map (algebraMap ℤ ℝ) *ᵥ x) i) • P.root i := by
  rw [Finset.smul_sum]
  simp_rw [smul_comm g, Base.actsBy_iff.1 hgW, Finset.smul_sum, smul_comm (algebraMap ℝ K _)]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  simp only [← Int.cast_smul_eq_zsmul K, smul_smul, ← Finset.sum_smul, mulVec, dotProduct,
    Matrix.map_apply, eq_intCast, map_sum, map_mul, map_intCast, mul_comm]

/-- Extracting matrix-vector equality from a Weyl-group action on a real combination of simple
roots over an `ℝ`-algebra `K` of characteristic zero. -/
private lemma mulVec_eq_of_actsBy_smul_sum
    {ι K M N : Type*} [Field K] [Algebra ℝ K] [AddCommGroup M] [Module K M]
    [AddCommGroup N] [Module K N] {P : RootPairing ι K M N} {b : P.Base}
    [P.IsRootSystem] {g : P.weylGroup} {W : Matrix b.support b.support ℤ} (hgW : b.ActsBy g W)
    {x w : b.support → ℝ}
    (hgx : g • (∑ i : b.support, algebraMap ℝ K (x i) • P.root i) =
      ∑ i : b.support, algebraMap ℝ K (w i) • P.root i) :
    W.map (algebraMap ℤ ℝ) *ᵥ x = w := by
  rw [actsBy_smul_sum_algebraMap_root hgW x] at hgx
  ext i
  apply (algebraMap ℝ K).injective
  classical
  have h1 := congrArg (fun m ↦ b.toWeightBasis.repr m i) hgx
  simp_rw [map_sum, map_smul, ← b.toWeightBasis_apply, b.toWeightBasis.repr_self] at h1
  simpa [Finset.sum_apply', Finsupp.single_apply] using h1

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
  classical
  have hEntry (j : b.support) : (W i j : ℂ) = if col i = b0 then
      if i = j then (-1 : ℂ) else if col j = !b0 then (A i j : ℂ) else 0
    else if i = j then 1 else 0 := by
    have hact := congrArg (fun m ↦ b.toWeightBasis.repr m i) (Base.actsBy_iff.1 hW j)
    have hlhs : b.toWeightBasis.repr
        ((weylCoxeterSystem P b).colorClassProd col b0 • P.root j) i =
        (if i = j then 1 else 0) - if col i = b0 then P.coroot' i (P.root j) else 0 := by
      rw [colorClassProd_smul, map_sub, map_sum, Finsupp.sub_apply, Finset.sum_apply']
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
    · rw [ite_eq_left hci] at hact; rw [ite_eq_left hci]
      by_cases hij : i = j
      · subst hij
        rw [ite_eq_left rfl, P.root_coroot'_eq_pairing, P.pairing_same] at hact
        have hW_int : W i i = -1 :=
          Int.cast_injective (α := K) (by push_cast; linear_combination hact.symm)
        simp [hW_int]
      · rw [ite_eq_right hij] at hact; rw [ite_eq_right hij]
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
    · rw [ite_eq_right hci] at hact; rw [ite_eq_right hci]
      by_cases hij : i = j
      · subst hij; rw [ite_eq_left rfl, sub_zero] at hact
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

/-- Matrix action of the colour-class product `colorClassProd col b0` on the colour part of `y` of
colour `z`. -/
private lemma colorClassProd_matrix_mulVec_colorPart
    {ι K M N : Type*} [Field K] [CharZero K] [Algebra ℝ K] [AddCommGroup M] [Module K M]
    [AddCommGroup N] [Module K N] (P : RootPairing ι K M N) [Finite ι]
    [P.IsCrystallographic] [P.IsReduced] [P.IsRootSystem] (b : P.Base)
    (col : (coxeterMatrixOfBase P b).graph.Coloring Bool) {κ : ℝ} {y : b.support → ℝ}
    (hy : ∀ j : b.support, ∑ i : b.support, y i * P.pairingIn ℤ i j = κ * y j)
    (b0 z : Bool) {W : Matrix b.support b.support ℤ}
    (hW : b.ActsBy ((weylCoxeterSystem P b).colorClassProd col b0) W) :
    W.map (algebraMap ℤ ℝ) *ᵥ (fun i ↦ if col i = z then y i else 0) =
      if z = b0 then -(fun i ↦ if col i = b0 then y i else 0)
      else (fun i ↦ if col i = z then y i else 0) +
        (2 - κ) • (fun i ↦ if col i = b0 then y i else 0) := by
  classical
  refine mulVec_eq_of_actsBy_smul_sum hW ?_
  have h := colorClassProd_smul_colorPart (P := P) (b := b) (c := col) hy b0 z
  rw [colorPart_def, colorPart_def] at h
  by_cases hzb : z = b0
  · subst hzb
    rw [ite_eq_left rfl] at h ⊢
    have h2 : (∑ i : b.support, algebraMap ℝ K (if col i = z then y i else 0) • P.root i) -
        algebraMap ℝ K 2 •
          (∑ i : b.support, algebraMap ℝ K (if col i = z then y i else 0) • P.root i) =
        ∑ i : b.support,
          algebraMap ℝ K ((-(fun i ↦ if col i = z then y i else 0)) i) • P.root i := by
      simp only [Pi.neg_apply, map_neg, neg_smul, Finset.sum_neg_distrib, map_ofNat]
      module
    exact h.trans h2
  · rw [ite_eq_right hzb] at h ⊢
    have h2 : (∑ i : b.support, algebraMap ℝ K (if col i = z then y i else 0) • P.root i) -
        algebraMap ℝ K (κ - 2) •
          (∑ i : b.support, algebraMap ℝ K (if col i = b0 then y i else 0) • P.root i) =
        ∑ i : b.support,
          algebraMap ℝ K (((fun i ↦ if col i = z then y i else 0) +
            (2 - κ) • (fun i ↦ if col i = b0 then y i else 0)) i) • P.root i := by
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add, map_mul, map_sub, map_ofNat,
        add_smul, mul_smul, Finset.sum_add_distrib, ← Finset.smul_sum]
      module
    exact h.trans h2

/-- The Coxeter-plane eigenvalue `ζ = exp(2iθ)` has exact multiplicative order equal to the order
`h` of the bipartite Coxeter element `c`: any `c ^ k` fixing `z₀ = y₁C + exp(iθ) • y₂C` fixes the
real dominant vector `y₁ + y₂`, hence `c ^ k = 1`. -/
private lemma isPrimitiveRoot_coxeterPlane_eigenvalue
    {ι K M N : Type*} [Field K] [CharZero K] [Algebra ℝ K] [AddCommGroup M] [Module K M]
    [AddCommGroup N] [Module K N] (P : RootPairing ι K M N) [Finite ι]
    [P.IsCrystallographic] [P.IsReduced] (b : P.Base)
    (col : (coxeterMatrixOfBase P b).graph.Coloring Bool) {κ : ℝ} {y : b.support → ℝ}
    (hy : ∀ j : b.support, ∑ i : b.support, y i * P.pairingIn ℤ i j = κ * y j)
    (hy0 : ∀ i, 0 < y i) (hκ : 0 < κ) {θ : ℝ} (hsinθ_pos : 0 < Real.sin θ)
    {W : Matrix b.support b.support ℤ}
    (hW : b.ActsBy ((weylCoxeterSystem P b).bipartiteCoxeterElement col) W)
    (hz₀_ne : (fun i : b.support ↦ ((if col i = true then y i else 0 : ℝ) : ℂ)) +
      Complex.exp ((θ : ℂ) * Complex.I) •
        (fun i : b.support ↦ ((if col i = false then y i else 0 : ℝ) : ℂ)) ≠ 0)
    (hz₀_eig : W.map (algebraMap ℤ ℂ) *ᵥ
        ((fun i : b.support ↦ ((if col i = true then y i else 0 : ℝ) : ℂ)) +
          Complex.exp ((θ : ℂ) * Complex.I) •
            (fun i : b.support ↦ ((if col i = false then y i else 0 : ℝ) : ℂ))) =
      (Complex.exp ((θ : ℂ) * Complex.I) ^ 2)⁻¹ •
        ((fun i : b.support ↦ ((if col i = true then y i else 0 : ℝ) : ℂ)) +
          Complex.exp ((θ : ℂ) * Complex.I) •
            (fun i : b.support ↦ ((if col i = false then y i else 0 : ℝ) : ℂ)))) :
    IsPrimitiveRoot (Complex.exp ((θ : ℂ) * Complex.I) ^ 2)
      (orderOf ((weylCoxeterSystem P b).bipartiteCoxeterElement col)) := by
  classical
  set c := (weylCoxeterSystem P b).bipartiteCoxeterElement col
  set h : ℕ := orderOf c
  set μ : ℂ := Complex.exp ((θ : ℂ) * Complex.I)
  set ζ : ℂ := μ ^ 2
  set y₁ : b.support → ℝ := fun i ↦ if col i = true then y i else 0
  set y₂ : b.support → ℝ := fun i ↦ if col i = false then y i else 0
  set y₁C : b.support → ℂ := fun i ↦ (y₁ i : ℂ)
  set y₂C : b.support → ℂ := fun i ↦ (y₂ i : ℂ)
  set z₀ : b.support → ℂ := y₁C + μ • y₂C
  have hmulVec_ofReal (V : Matrix b.support b.support ℤ) (x : b.support → ℝ) :
      V.map (algebraMap ℤ ℂ) *ᵥ (fun i ↦ (x i : ℂ)) =
        fun i ↦ ((V.map (algebraMap ℤ ℝ) *ᵥ x) i : ℂ) := by
    ext i; simp [mulVec, dotProduct]
  have hpow_eig (k : ℕ) : ((W.map (algebraMap ℤ ℂ)) ^ k) *ᵥ z₀ = (ζ⁻¹) ^ k • z₀ := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', ← mulVec_mulVec, ih, mulVec_smul, hz₀_eig, smul_smul, mul_comm, ← pow_succ']
  rw [IsPrimitiveRoot.iff_def]; refine ⟨?_, fun k hk ↦ ?_⟩
  · have hWh : W ^ h = 1 := (hW.pow h).unique (by
      rw [pow_orderOf_eq_one]; exact Base.actsBy_one b)
    have hchC : (W.map (algebraMap ℤ ℂ)) ^ h = 1 := by
      change ((RingHom.mapMatrix (algebraMap ℤ ℂ)) W) ^ h = 1
      rw [← map_pow, hWh, map_one]
    have h1 := hpow_eig h; rw [hchC, one_mulVec] at h1
    obtain ⟨i₀, hi₀⟩ := Function.ne_iff.1 hz₀_ne
    have hinv1 : (ζ⁻¹) ^ h = 1 := mul_right_cancel₀ hi₀
      (by simpa [Pi.smul_apply, smul_eq_mul] using (congrFun h1 i₀).symm)
    rwa [inv_pow, inv_eq_one] at hinv1
  · have h1 := hpow_eig k
    have hC_pow : (W.map (algebraMap ℤ ℂ)) ^ k = (W ^ k).map (algebraMap ℤ ℂ) :=
      ((RingHom.mapMatrix (algebraMap ℤ ℂ)).map_pow W k).symm
    have hR_pow : (W.map (algebraMap ℤ ℝ)) ^ k = (W ^ k).map (algebraMap ℤ ℝ) :=
      ((RingHom.mapMatrix (algebraMap ℤ ℝ)).map_pow W k).symm
    rw [inv_pow, hk, inv_one, one_smul, hC_pow, mulVec_add, mulVec_smul,
      hmulVec_ofReal, hmulVec_ofReal, ← hR_pow] at h1
    have hy₂_fix : ((W.map (algebraMap ℤ ℝ)) ^ k) *ᵥ y₂ = y₂ := by
      ext i; have him := congrArg Complex.im (congrFun h1 i)
      simp only [z₀, y₁C, y₂C, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Complex.add_im,
        Complex.ofReal_im, zero_add, Complex.mul_im, Complex.ofReal_re, mul_zero, μ,
        Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin] at him
      exact mul_left_cancel₀ hsinθ_pos.ne' (by simpa using him)
    have hy₁_fix : ((W.map (algebraMap ℤ ℝ)) ^ k) *ᵥ y₁ = y₁ := by
      ext i; have hre := congrArg Complex.re (congrFun h1 i)
      simp only [z₀, y₁C, y₂C, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Complex.add_re,
        Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, mul_zero, sub_zero,
        hy₂_fix] at hre
      linarith
    have hy_fix : ((W ^ k).map (algebraMap ℤ ℝ)) *ᵥ (y₁ + y₂) = y₁ + y₂ := by
      rw [← hR_pow, mulVec_add, hy₁_fix, hy₂_fix]
    have hsum_vec : ∑ i : b.support, algebraMap ℝ K ((y₁ + y₂) i) • P.root i =
        colorPart P b col y true + colorPart P b col y false := by
      rw [colorPart_def, colorPart_def, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      simp [y₁, y₂, add_smul]
    have hck_fix : c ^ k • (colorPart P b col y true + colorPart P b col y false) =
        colorPart P b col y true + colorPart P b col y false := by
      rw [← hsum_vec, actsBy_smul_sum_algebraMap_root (hW.pow k), hy_fix]
    have hreg : P.IsRegularWeight (colorPart P b col y true + colorPart P b col y false) :=
      isRegularWeight_of_forall_exists_pos_coroot'_eq P b _ (algebraMap ℝ K).injective
        (exists_pos_coroot'_colorPart_add hy hy0 hκ)
    exact orderOf_dvd_of_pow_eq_one (P.eq_one_of_isRegularWeight_of_smul_eq b hreg hck_fix)

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
  -- Phase 2: Complex angle `θ = arccos ((2 - κ) / 2)` and Perron adjacency matrix `A`.
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
  set μ : ℂ := Complex.exp ((θ : ℂ) * Complex.I)
  set ζ : ℂ := μ ^ 2
  have hμ_ne : μ ≠ 0 := Complex.exp_ne_zero _
  have hμ_add_inv : μ + μ⁻¹ = (lam : ℂ) := by
    rw [← Complex.exp_neg, ← neg_mul, ← Complex.two_cos, ← Complex.ofReal_cos, hcosθ]
    push_cast; ring
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
  -- Phase 3: Integer matrices `W₁, W₂` of `c₁, c₂` and their dihedral action on the colour parts.
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
  set M₁C : Matrix b.support b.support ℂ := W₁.map (algebraMap ℤ ℂ)
  set M₂C : Matrix b.support b.support ℂ := W₂.map (algebraMap ℤ ℂ)
  have hM₁C_sq : M₁C * M₁C = 1 := by
    change (RingHom.mapMatrix (algebraMap ℤ ℂ)) W₁ * (RingHom.mapMatrix (algebraMap ℤ ℂ)) W₁ = 1
    rw [← map_mul, hW₁_sq, map_one]
  have hM₁C_mul := colorClassProd_matrix_mulVec P b col A (fun _ _ ↦ rfl) true hW₁_acts
  have hM₂C_mul := colorClassProd_matrix_mulVec P b col A (fun _ _ ↦ rfl) false hW₂_acts
  simp only [Bool.not_true, Bool.not_false] at hM₁C_mul hM₂C_mul
  set y₁ : b.support → ℝ := fun i ↦ if col i = true then y i else 0
  set y₂ : b.support → ℝ := fun i ↦ if col i = false then y i else 0
  have hM₁y₁ : W₁.map (algebraMap ℤ ℝ) *ᵥ y₁ = -y₁ := by
    simpa [y₁] using colorClassProd_matrix_mulVec_colorPart P b col hy true true hW₁_acts
  have hM₁y₂ : W₁.map (algebraMap ℤ ℝ) *ᵥ y₂ = y₂ + lam • y₁ := by
    simpa [y₁, y₂, lam] using colorClassProd_matrix_mulVec_colorPart P b col hy true false hW₁_acts
  have hM₂y₂ : W₂.map (algebraMap ℤ ℝ) *ᵥ y₂ = -y₂ := by
    simpa [y₂] using colorClassProd_matrix_mulVec_colorPart P b col hy false false hW₂_acts
  have hM₂y₁ : W₂.map (algebraMap ℤ ℝ) *ᵥ y₁ = y₁ + lam • y₂ := by
    simpa [y₁, y₂, lam] using colorClassProd_matrix_mulVec_colorPart P b col hy false true hW₂_acts
  -- Phase 4: Build complex eigenvector `z₀` for `ζ⁻¹` and show `ζ` is a primitive `h`-th root.
  set y₁C : b.support → ℂ := fun i ↦ (y₁ i : ℂ)
  set y₂C : b.support → ℂ := fun i ↦ (y₂ i : ℂ)
  set z₀ : b.support → ℂ := y₁C + μ • y₂C
  have hz₀_ne : z₀ ≠ 0 := fun h0 ↦ by
    obtain ⟨i₀⟩ := (inferInstance : Nonempty b.support)
    have hi0 : (y₁ i₀ : ℂ) + μ * (y₂ i₀ : ℂ) = 0 := by
      simpa [z₀, y₁C, y₂C] using congrFun h0 i₀
    cases hci : col i₀
    · have h0' : μ * (y i₀ : ℂ) = 0 := by simpa [y₁, y₂, hci] using hi0
      exact (mul_eq_zero.1 h0').elim hμ_ne (Complex.ofReal_ne_zero.2 (hy0 i₀).ne')
    · have h0' : (y i₀ : ℂ) = 0 := by simpa [y₁, y₂, hci] using hi0
      exact (hy0 i₀).ne' (Complex.ofReal_eq_zero.1 h0')
  have hmul_c (W : Matrix b.support b.support ℤ) (x w : b.support → ℝ)
      (h : W.map (algebraMap ℤ ℝ) *ᵥ x = w) :
      W.map (algebraMap ℤ ℂ) *ᵥ (fun i ↦ (x i : ℂ)) = fun i ↦ (w i : ℂ) := by
    rw [← h]; ext i; simp [mulVec, dotProduct]
  have hz₀_eig : (M₁C * M₂C) *ᵥ z₀ = ζ⁻¹ • z₀ := by
    rw [← mulVec_mulVec]
    have hd := LinearMap.apply_apply_add_smul_eq_inv_sq_smul (Matrix.toLin' M₁C)
      (Matrix.toLin' M₂C) hμ_ne
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
  have hζ_prim : IsPrimitiveRoot ζ h :=
    isPrimitiveRoot_coxeterPlane_eigenvalue P b col hy hy0 hκ hsinθ_pos hW_acts hz₀_ne
      (by rw [← hM_mul_map]; exact hz₀_eig)
  -- Phase 5: Galois transfer via `cyclotomic h ℚ` gives eigenvalue `ω₀ = exp(2πi/h)` and bound.
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
  exact Real.eq_two_mul_cos_pi_div_of_norm_one_add_sq_div_le hlam_nonneg hlam_lt h2le
    hζ_prim.pow_eq_one (Matrix.norm_one_add_sq_div_le_sq_of_mulVec_eq_smul hA_nonneg hA_same hy0
      hA_eig hM₁C_sq hM₁C_mul hM₂C_mul (Complex.exp_ne_zero _) hz.2
      (Module.End.mem_eigenspace_iff.1 hz.1))

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

/-- **The Steinberg–Coleman Coxeter plane over `ℝ`.** For a bipartite Coxeter element
`wordProd P b l₁ * wordProd P b l₂` of an irreducible finite reduced crystallographic root system,
there exist `v₁, v₂ : M` such that `v₁ + v₂` lies in the open dominant chamber and
`wordProd P b l₁`, `wordProd P b l₂` act on `span {v₁, v₂}` by dihedral formulas with parameter
`2 cos (π / orderOf (wordProd P b l₁ * wordProd P b l₂))`. -/
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
  have : Nonempty b.support := b.nonempty_support_of_isIrreducible
  have hc₁_eq : wordProd P b l₁ = (weylCoxeterSystem P b).colorClassProd col true := by
    rw [← weylCoxeterSystem_wordProd P b l₁]
    exact (weylCoxeterSystem P b).wordProd_eq_colorClassProd col hl₁ hcol₁
  have hc₂_eq : wordProd P b l₂ = (weylCoxeterSystem P b).colorClassProd col false := by
    rw [← weylCoxeterSystem_wordProd P b l₂]
    exact (weylCoxeterSystem P b).wordProd_eq_colorClassProd col hl₂ hcol₂
  have hc_bip : wordProd P b l₁ * wordProd P b l₂ =
      (weylCoxeterSystem P b).bipartiteCoxeterElement col := by
    rw [hc₁_eq, hc₂_eq, CoxeterSystem.bipartiteCoxeterElement_def]
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
    · rw [hκ_iff.2 hsub, orderOf_bipartiteCoxeterElement_eq_two_of_subsingleton P b col,
        sub_self, show Real.pi / ((2 : ℕ) : ℝ) = Real.pi / 2 by norm_num,
        Real.cos_pi_div_two, mul_zero]
    · exact two_sub_eq_two_mul_cos_pi_div_orderOf_bipartiteCoxeterElement P b col hy hy0 hκ
        (lt_of_le_of_ne hκ_le fun h2 ↦ absurd (hκ_iff.1 h2) (not_subsingleton _))
  refine ⟨v₁, v₂, hv_dom, hc₁_v₁, ?_, hc₂_v₂, ?_⟩ <;> rwa [← hlam_eq]

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
  have : Nonempty b.support := b.nonempty_support_of_isIrreducible
  have : Nonempty ι := ⟨(Classical.arbitrary b.support : ι)⟩
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
      have hy : ∀ j : b.support, ∑ i : b.support, y i * P.pairingIn ℤ i j = κ * y j := fun j ↦ by
        simpa [Matrix.vecMul, dotProduct, Base.cartanMatrixIn_def] using congrFun hyC j
      have hlam : 2 - κ = 2 * Real.cos (Real.pi / orderOf c) :=
        two_sub_eq_two_mul_cos_pi_div_orderOf_bipartiteCoxeterElement P b col hy hy0 hκ hκ2
      set ν : ℂ := (Complex.exp (2 * Real.pi * Complex.I / orderOf c))⁻¹
      have hν_ne : ν ≠ 0 := inv_ne_zero (Complex.exp_ne_zero _)
      have hν_add : ν + ν⁻¹ = algebraMap ℝ ℂ (2 - κ) ^ 2 - 2 := by
        have h1 : ν + ν⁻¹ = ((2 * Real.cos (2 * (Real.pi / orderOf c)) : ℝ) : ℂ) := by
          have hcos := Complex.two_cos ((2 * (Real.pi / orderOf c) : ℝ) : ℂ)
          have harg : ((2 * (Real.pi / orderOf c) : ℝ) : ℂ) * Complex.I =
              2 * Real.pi * Complex.I / orderOf c := by push_cast; ring
          rw [← Complex.ofReal_cos, neg_mul, Complex.exp_neg, harg, add_comm] at hcos
          simpa [ν] using hcos.symm
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
        bipartiteCoxeterElement_smul_one_add_smul_colorPart_add_smul (c := col) hy hν⟩
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
