/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.Coxeter.Element.Plane
public import TauCeti.LinearAlgebra.RootSystem.Inversions.Length
public import TauCeti.RepresentationTheory.SymmetricAlgebra.Weyl

import Mathlib.LinearAlgebra.Eigenspace.Charpoly
import Mathlib.LinearAlgebra.RootSystem.BaseExists
import Mathlib.RingTheory.RootsOfUnity.Complex
import TauCeti.LinearAlgebra.Matrix.Cartan.Coxeter.Basic
import TauCeti.LinearAlgebra.RootSystem.CoweightLattice.Basis
import TauCeti.LinearAlgebra.RootSystem.Coxeter.Element.ActsBy
import TauCeti.LinearAlgebra.RootSystem.Coxeter.FixedPoints
import TauCeti.LinearAlgebra.RootSystem.Inversions.Subword
import TauCeti.RepresentationTheory.SymmetricAlgebra.Weyl.BaseChange
import TauCeti.RingTheory.Polynomial.Cyclotomic.Roots

/-!
# Coxeter number, Coxeter eigenvalues, and exponents of Weyl groups

For a finite reduced crystallographic root system `P` with base `b` of rank `r = b.support.card`
and Coxeter element `c = wordProd P b l` of order `h = orderOf c`:

* Without irreducibility: `|Φ| ≤ #(inversions c) * h ≤ r * h`, and `#(inversions c) = r`.
* For irreducible `P` over a characteristic-zero domain: `|Φ| = r * h` and `2 * |Φ⁺| = r * h`.
* For irreducible `P` over a characteristic-zero field and homogeneous basic invariant degrees
  `d`: `2 ≤ d i ≤ h`, duality `d i - 1 ↦ h - (d i - 1)`, the coprime-exponent theorem
  (including `2` and `h`), and `(P.weylGroupRootRep c).charpoly = ∏ i, (X - C (ζ ^ (d i - 1)))`
  for any primitive `h`-th root of unity `ζ`.

## References

* A. J. Coleman, *The Betti numbers of the simple Lie groups*, Canad. J. Math. 10 (1958), 349–356.
* R. Steinberg, *Finite reflection groups*, Trans. Amer. Math. Soc. 91 (1959), 493–504.
* T. A. Springer, *Regular elements of finite reflection groups*, Invent. Math. 25 (1974), §4.
-/

public section

open Matrix Polynomial SymmetricAlgebra TauCeti TauCeti.SymmetricAlgebra

namespace RootPairing

section OrbitAndInversions

variable {ι R M N : Type*} [CommRing R] [IsDomain R] [CharZero R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (P : RootPairing ι R M N) [Finite ι] [P.IsCrystallographic] [P.IsReduced] [P.IsRootSystem]

/-- Every `⟨c⟩`-orbit of roots for a Coxeter element `c = wordProd P b l` meets the inversion set
`inversions P b c`. -/
private lemma exists_pow_weylGroupToPerm_mem_inversions (b : P.Base)
    {l : List b.support} (hl : l.Nodup) (hall : ∀ i, i ∈ l) (i : ι) :
    ∃ j ∈ inversions P b (wordProd P b l),
      ∃ k : Fin (orderOf (wordProd P b l)),
        (P.weylGroupToPerm (wordProd P b l) ^ (k : ℕ)) j = i := by
  classical
  have : Finite P.weylGroup := P.finite_weylGroup_of_base b
  set c : P.weylGroup := wordProd P b l
  set h : ℕ := orderOf c
  have hh_pos : 0 < h := orderOf_pos c
  let f : Equiv.Perm ι := P.weylGroupToPerm c
  have hf_pow : f ^ h = 1 := by dsimp only [f]; rw [← map_pow, pow_orderOf_eq_one, map_one]
  let S : Finset ι := Finset.univ.image fun k : Fin h ↦ (f ^ (k : ℕ)) i
  have hS_ne : S.Nonempty :=
    ⟨i, Finset.mem_image.2 ⟨⟨0, hh_pos⟩, Finset.mem_univ _, by simp⟩⟩
  have hS_img : S.image f = S := by
    refine Finset.eq_of_subset_of_card_le (fun y hy ↦ ?_)
      (by rw [Finset.card_image_of_injective _ f.injective])
    rcases Finset.mem_image.1 hy with ⟨x, hx, rfl⟩
    rcases Finset.mem_image.1 hx with ⟨k, -, rfl⟩
    refine Finset.mem_image.2
      ⟨⟨((k : ℕ) + 1) % h, Nat.mod_lt _ hh_pos⟩, Finset.mem_univ _, ?_⟩
    rw [pow_eq_pow_of_modEq (Nat.mod_modEq ((k : ℕ) + 1) h) hf_pow, pow_succ', Equiv.Perm.mul_apply]
  have hsum_zero : ∑ j ∈ S, P.root j = 0 := by
    rw [← wordProd_smul_eq_self_iff_eq_zero b hl hall, Finset.smul_sum]
    simp_rw [P.weylGroup_apply_root]
    rw [← Finset.sum_image (g := f) fun _ _ _ _ h ↦ f.injective h]
    exact congrArg (fun T : Finset ι ↦ ∑ j ∈ T, P.root j) hS_img
  have hex_neg : ∃ j ∈ S, ¬ b.IsPos j := by
    by_contra hpos; push Not at hpos
    exact sum_root_ne_zero_of_mem_posRoots P b hS_ne
      (fun j hj ↦ (mem_posRoots P b j).2 (hpos j hj)) hsum_zero
  have hex_pos : ∃ j ∈ S, b.IsPos j := by
    by_contra hneg; push Not at hneg
    exact sum_root_ne_zero_of_mem_posRoots P b hS_ne
      (fun j hj ↦ (mem_posRoots P b _).2 ((isPos_reflectionPerm_self_iff_mem_negRoots P b j).2
        ((mem_negRoots P b j).2 (hneg j hj))))
      (by simp [root_reflectionPerm, reflection_apply_self, hsum_zero])
  rcases hex_pos with ⟨j₂, hj₂S, hj₂_pos⟩
  rcases hex_neg with ⟨j₁, hj₁S, hj₁_neg⟩
  rcases Finset.mem_image.1 hj₂S with ⟨a, -, rfl⟩
  rcases Finset.mem_image.1 hj₁S with ⟨b', -, rfl⟩
  have hex_step : ∃ m : ℕ, ¬ b.IsPos ((f ^ m) ((f ^ (a : ℕ)) i)) := by
    refine ⟨(b' : ℕ) + (h - (a : ℕ)), ?_⟩
    rw [← Equiv.Perm.mul_apply, ← pow_add,
      show (b' : ℕ) + (h - (a : ℕ)) + (a : ℕ) = (b' : ℕ) + h by omega,
      pow_add, hf_pow, mul_one]
    exact hj₁_neg
  set m₀ : ℕ := Nat.find hex_step
  have hm₀_spec : ¬ b.IsPos ((f ^ m₀) ((f ^ (a : ℕ)) i)) := Nat.find_spec hex_step
  have hm₀_ne : m₀ ≠ 0 := fun h0 ↦ hm₀_spec (h0 ▸ hj₂_pos)
  set n : ℕ := m₀ - 1
  have hn_inv : (f ^ n) ((f ^ (a : ℕ)) i) ∈ inversions P b c := by
    rw [mem_inversions]
    refine ⟨by by_contra hneg; exact Nat.find_min hex_step (by omega) hneg, ?_⟩
    have hm₀_eq : P.weylGroupToPerm c ((f ^ n) ((f ^ (a : ℕ)) i)) =
        (f ^ m₀) ((f ^ (a : ℕ)) i) := by
      dsimp only [f]
      rw [← Equiv.Perm.mul_apply, ← pow_succ', Nat.sub_add_cancel (Nat.pos_of_ne_zero hm₀_ne)]
    rw [hm₀_eq]
    exact hm₀_spec
  let k : Fin h := ⟨(h - (n + (a : ℕ)) % h) % h, Nat.mod_lt _ hh_pos⟩
  refine ⟨(f ^ n) ((f ^ (a : ℕ)) i), hn_inv, k, ?_⟩
  rw [← Equiv.Perm.mul_apply, ← Equiv.Perm.mul_apply, ← pow_add, ← pow_add,
    pow_eq_pow_of_modEq (Nat.mod_modEq _ h).symm hf_pow]
  have hmod0 : ((k : ℕ) + n + (a : ℕ)) % h = 0 := by
    dsimp only [k]; rw [add_assoc, Nat.mod_add_mod, ← Nat.add_mod_mod,
      Nat.sub_add_cancel (Nat.mod_lt _ hh_pos).le, Nat.mod_self]
  rw [hmod0, pow_zero, Equiv.Perm.one_apply]

/-- **Coxeter-orbit inversion bound.** Every `⟨c⟩`-orbit of roots meets the inversion set of a
Coxeter element `c`, so `Nat.card ι ≤ (inversions P b c).ncard * orderOf c`. -/
theorem natCard_le_ncard_inversions_mul_orderOf_wordProd (b : P.Base)
    {l : List b.support} (hl : l.Nodup) (hall : ∀ i, i ∈ l) :
    Nat.card ι ≤ (inversions P b (wordProd P b l)).ncard * orderOf (wordProd P b l) := by
  classical
  have : Finite P.weylGroup := P.finite_weylGroup_of_base b
  set c : P.weylGroup := wordProd P b l
  set h : ℕ := orderOf c
  have hsurj : Function.Surjective
      (fun p : (inversions P b c) × Fin h ↦ (P.weylGroupToPerm c ^ (p.2 : ℕ)) p.1.val) := by
    intro i
    obtain ⟨j, hj_inv, k, hk⟩ := P.exists_pow_weylGroupToPerm_mem_inversions b hl hall i
    exact ⟨(⟨j, hj_inv⟩, k), hk⟩
  calc Nat.card ι
      ≤ Nat.card ((inversions P b c) × Fin h) := Nat.card_le_card_of_surjective _ hsurj
    _ = (inversions P b c).ncard * h := by rw [Nat.card_prod, Nat.card_coe_set_eq, Nat.card_fin]

/-- **Rank times Coxeter order bounds the number of roots.** -/
theorem natCard_le_card_support_mul_orderOf_wordProd (b : P.Base)
    {l : List b.support} (hl : l.Nodup) (hall : ∀ i, i ∈ l) :
    Nat.card ι ≤ b.support.card * orderOf (wordProd P b l) := by
  have hinv : (inversions P b (wordProd P b l)).ncard ≤ b.support.card :=
    (ncard_inversions_wordProd_le_length P b l).trans
      (by simpa [Fintype.card_coe] using hl.length_le_card)
  exact (P.natCard_le_ncard_inversions_mul_orderOf_wordProd b hl hall).trans
    (Nat.mul_le_mul_right _ hinv)

/-- **Every Coxeter element is a reduced word**:
`#(inversions (wordProd P b l)) = b.support.card`. -/
theorem ncard_inversions_wordProd_eq_card_support (b : P.Base)
    {l : List b.support} (hl : l.Nodup) (hall : ∀ i, i ∈ l) :
    (inversions P b (wordProd P b l)).ncard = b.support.card := by
  classical
  have hle : (inversions P b (wordProd P b l)).ncard ≤ b.support.card :=
    (ncard_inversions_wordProd_le_length P b l).trans
      (by simpa [Fintype.card_coe] using hl.length_le_card)
  refine le_antisymm hle ?_; by_contra hlt; push Not at hlt
  obtain ⟨l', hsub, hl'eq, hl'len⟩ :=
    exists_sublist_wordProd_eq_and_length_eq_ncard_inversions P b l
  have hcard_lt : l'.toFinset.card < (Finset.univ : Finset b.support).card := by
    rw [Finset.card_univ, Fintype.card_coe]
    exact (List.toFinset_card_le l').trans_lt (hl'len.trans_lt hlt)
  obtain ⟨i₀, -, hi₀⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard_lt
  rw [List.mem_toFinset] at hi₀
  let j₀ : b.flip.support := ⟨i₀.val, i₀.property⟩
  let x : M := b.flip.fundamentalCoweightBasis j₀
  have hx_ne : x ≠ 0 := b.flip.fundamentalCoweightBasis.ne_zero j₀
  have hx_coroot (j : b.support) (hj : j ∈ l') : P.coroot' j x = 0 := by
    let j' : b.flip.support := ⟨j.val, j.property⟩
    have hne : j' ≠ j₀ := fun heq ↦ hi₀ ((Subtype.ext (congrArg Subtype.val heq) : j = i₀) ▸ hj)
    have h0 := b.flip.root'_fundamentalCoweightBasis j' j₀
    rw [ite_eq_right hne] at h0
    exact h0
  have hx_fix : wordProd P b l' • x = x :=
    (wordProd_smul_eq_self_iff b (hl.sublist hsub)).2 hx_coroot
  rw [hl'eq] at hx_fix
  exact hx_ne ((wordProd_smul_eq_self_iff_eq_zero b hl hall).1 hx_fix)

end OrbitAndInversions

section BaseChangeSetup

variable {ι R M N : Type*} [CommRing R] [IsDomain R] [CharZero R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N} [Finite ι] [P.IsCrystallographic] [P.IsRootSystem]

private noncomputable abbrev baseChangeRat (b : P.Base) (S : Type*) [Field S] [CharZero S] :=
  rootPairingBaseChange S b.rationalModel b.rationalModel_toLinearMap

private noncomputable abbrev baseChangeRatBase (b : P.Base) (S : Type*) [Field S] [CharZero S] :=
  rootPairingBaseChangeBase S b.rationalModel b.rationalModel_toLinearMap b.rationalModelBase

private noncomputable def baseChangeRatSupportEquiv (b : P.Base) (S : Type*)
    [Field S] [CharZero S] :
    (baseChangeRatBase b S).support ≃ b.support :=
  (supportEquivRootPairingBaseChangeBase S b.rationalModel b.rationalModel_toLinearMap
    b.rationalModelBase).trans b.supportEquivRationalModelBase

omit [IsDomain R] [Finite ι] in
private lemma baseChangeRatBase_cartanMatrix (b : P.Base) (S : Type*) [Field S] [CharZero S] :
    (baseChangeRatBase b S).cartanMatrix =
      b.cartanMatrix.submatrix (baseChangeRatSupportEquiv b S)
        (baseChangeRatSupportEquiv b S) := by
  ext i j; simp [baseChangeRatBase, baseChangeRatSupportEquiv]

private theorem orderOf_wordProd_baseChangeRat (b : P.Base) (S : Type*) [Field S] [CharZero S]
    (l : List b.support) :
    orderOf (wordProd P b l) =
      orderOf (wordProd (baseChangeRat b S) (baseChangeRatBase b S)
        (l.map (baseChangeRatSupportEquiv b S).symm)) := by
  classical
  let e := baseChangeRatSupportEquiv b S
  rw [(b.actsBy_wordProd l).orderOf_eq, ((baseChangeRatBase b S).actsBy_wordProd _).orderOf_eq,
    baseChangeRatBase_cartanMatrix b S, Matrix.prod_map_reflMatrix_submatrix b.cartanMatrix e l]
  exact (orderOf_injective
    (Matrix.reindexAlgEquiv ℤ ℤ e.symm).toRingEquiv.toMulEquiv.toMonoidHom
    (Matrix.reindexAlgEquiv ℤ ℤ e.symm).injective _).symm

private theorem charpoly_weylGroupRootRep_wordProd_eq_map_rat
    {ι K M N : Type*} [DecidableEq ι] [Field K] [CharZero K] [AddCommGroup M] [Module K M]
    [Module.Finite K M] [AddCommGroup N] [Module K N] (P : RootPairing ι K M N)
    [P.IsCrystallographic] [P.IsRootSystem] (b : P.Base) (l : List b.support) :
    (((l.map (reflMatrix b.cartanMatrix)).prod.map (Int.castRingHom ℚ)).charpoly).map
        (algebraMap ℚ K) =
      (P.weylGroupRootRep (wordProd P b l)).charpoly := by
  rw [(b.actsBy_wordProd l).charpoly_weylGroupRootRep,
    Matrix.charpoly_map, Polynomial.map_map]
  congr 1; exact RingHom.ext_int _ _

omit [IsDomain R] in
private theorem charpoly_weylGroupRootRep_wordProd_baseChangeRat [DecidableEq ι]
    (b : P.Base) (S : Type*) [Field S] [CharZero S] (l : List b.support) :
    (((l.map (reflMatrix b.cartanMatrix)).prod.map (Int.castRingHom ℚ)).charpoly).map
        (algebraMap ℚ S) =
      ((baseChangeRat b S).weylGroupRootRep
        (wordProd (baseChangeRat b S) (baseChangeRatBase b S)
          (l.map (baseChangeRatSupportEquiv b S).symm))).charpoly := by
  classical
  let e := baseChangeRatSupportEquiv b S
  rw [← charpoly_weylGroupRootRep_wordProd_eq_map_rat (baseChangeRat b S)
    (baseChangeRatBase b S) (l.map e.symm)]
  congr 1
  have hcast :
      (Matrix.reindexAlgEquiv ℤ ℤ e.symm
          (l.map (reflMatrix b.cartanMatrix)).prod).map (Int.castRingHom ℚ) =
        Matrix.reindexAlgEquiv ℚ ℚ e.symm
          ((l.map (reflMatrix b.cartanMatrix)).prod.map (Int.castRingHom ℚ)) := by
    ext i j; simp
  rw [baseChangeRatBase_cartanMatrix b S, Matrix.prod_map_reflMatrix_submatrix b.cartanMatrix e l,
    hcast]
  exact (Matrix.charpoly_reindex e.symm _).symm

private lemma map_aeval_map_C {A : Type*} [CommRing A] [Algebra ℚ A] (p : ℚ[X]) (r : A) :
    (p.map Polynomial.C).map (Polynomial.aeval r).toRingHom = p.map (algebraMap ℚ A) := by
  rw [Polynomial.map_map]; congr 1; exact RingHom.ext_rat _ _

end BaseChangeSetup

section ComplexExponents

variable {ι M N : Type*} [AddCommGroup M] [Module ℂ M] [Module.Finite ℂ M]
  [AddCommGroup N] [Module ℂ N]
  (P : RootPairing ι ℂ M N) [Finite ι] [P.IsCrystallographic] [P.IsReduced]
  [P.IsRootSystem] [P.IsIrreducible]

/-- Over `ℂ`, the characteristic polynomial of a Coxeter element `wordProd P b l` factors in terms
of the basic invariant degrees `d i` and `ζ = Complex.exp (2 * Real.pi * Complex.I / h)`. -/
private theorem charpoly_weylGroupRootRep_wordProd_complex (b : P.Base)
    {l : List b.support} (hl : l.Nodup) (hall : ∀ i, i ∈ l)
    {κ : Type*} [Fintype κ]
    {f : κ → P.weylGroupRootRep.dual.symmetricAlgebraInvariants} {d : κ → ℕ}
    (hf : ∀ i, (f i : SymmetricAlgebra ℂ (Module.Dual ℂ M)) ∈
      homogeneousSubmodule ℂ (Module.Dual ℂ M) (d i))
    (hbij : Function.Bijective (MvPolynomial.aeval (R := ℂ) f)) :
    let h := orderOf (wordProd P b l)
    (P.weylGroupRootRep (wordProd P b l)).charpoly =
      ∏ i : κ, (X - C (Complex.exp (2 * Real.pi * Complex.I / h) ^ (d i - 1))) := by
  obtain ⟨v, hv_reg, hv_eig⟩ := P.exists_isRegularWeight_wordProd_smul_eq_inv_exp_smul b hl hall
  let ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / orderOf (wordProd P b l))
  let uζ : ℂˣ := Units.mk0 ζ⁻¹ (inv_ne_zero (Complex.exp_ne_zero _))
  simpa [uζ, ζ] using
    P.charpoly_weylGroupRootRep_eq_prod_of_isRegularWeight hf hbij (wordProd P b l) v uζ hv_reg
      hv_eig

/-- Over `ℂ`, every reduced exponent `(d i - 1) % h` is positive (because `1` is not an eigenvalue
of `wordProd P b l`). -/
private theorem one_le_mod_orderOf_wordProd_complex (b : P.Base)
    {l : List b.support} (hl : l.Nodup) (hall : ∀ i, i ∈ l)
    {κ : Type*} [Finite κ]
    {f : κ → P.weylGroupRootRep.dual.symmetricAlgebraInvariants} {d : κ → ℕ}
    (hf : ∀ i, (f i : SymmetricAlgebra ℂ (Module.Dual ℂ M)) ∈
      homogeneousSubmodule ℂ (Module.Dual ℂ M) (d i))
    (hbij : Function.Bijective (MvPolynomial.aeval (R := ℂ) f)) (i : κ) :
    1 ≤ (d i - 1) % orderOf (wordProd P b l) := by
  let := Fintype.ofFinite κ
  have : Nontrivial M := IsIrreducible.nontrivial P
  have hh2 : 2 ≤ orderOf (wordProd P b l) := P.two_le_orderOf_wordProd b hl hall
  have hh_pos : 0 < orderOf (wordProd P b l) := by omega
  let ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / orderOf (wordProd P b l))
  have hζ_pow : ζ ^ orderOf (wordProd P b l) = 1 :=
    (Complex.isPrimitiveRoot_exp _ hh_pos.ne').pow_eq_one
  by_contra hlt
  have he0 : (d i - 1) % orderOf (wordProd P b l) = 0 := by omega
  have hroot1 : (P.weylGroupRootRep (wordProd P b l)).charpoly.IsRoot 1 := by
    rw [Polynomial.IsRoot, P.charpoly_weylGroupRootRep_wordProd_complex b hl hall hf hbij,
      Polynomial.eval_prod]
    refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
    rw [pow_eq_pow_of_modEq (Nat.mod_modEq (d i - 1) (orderOf (wordProd P b l))).symm hζ_pow,
      he0, pow_zero]
    simp
  exact not_hasEigenvalue_one_wordProd b hl hall
    ((Module.End.hasEigenvalue_iff_isRoot_charpoly _ 1).2 hroot1)

/-- Conjugation invariance of the rational characteristic polynomial makes the reduced exponents
`(d i - 1) % h` self-dual under `m ↦ h - m`. -/
private theorem map_mod_orderOf_wordProd_eq_map_sub_complex (b : P.Base)
    {l : List b.support} (hl : l.Nodup) (hall : ∀ i, i ∈ l)
    {κ : Type*} [Fintype κ]
    {f : κ → P.weylGroupRootRep.dual.symmetricAlgebraInvariants} {d : κ → ℕ}
    (hf : ∀ i, (f i : SymmetricAlgebra ℂ (Module.Dual ℂ M)) ∈
      homogeneousSubmodule ℂ (Module.Dual ℂ M) (d i))
    (hbij : Function.Bijective (MvPolynomial.aeval (R := ℂ) f)) :
    let h := orderOf (wordProd P b l)
    Finset.univ.val.map (fun i ↦ (d i - 1) % h) =
      Finset.univ.val.map (fun i ↦ h - (d i - 1) % h) := by
  classical
  have : Nontrivial M := IsIrreducible.nontrivial P
  have : Finite P.weylGroup := P.finite_weylGroup
  set c : P.weylGroup := wordProd P b l
  set h : ℕ := orderOf c
  have hh_pos : 0 < h := orderOf_pos c
  let e : κ → ℕ := fun i ↦ (d i - 1) % h
  have he_lt (i : κ) : e i < h := Nat.mod_lt _ hh_pos
  have he_pos (i : κ) : 1 ≤ e i := P.one_le_mod_orderOf_wordProd_complex b hl hall hf hbij i
  have hhe_lt (i : κ) : h - e i < h := by have := he_pos i; omega
  set ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / h)
  have hζ_prim : IsPrimitiveRoot ζ h := Complex.isPrimitiveRoot_exp h hh_pos.ne'
  have hζ_pow : ζ ^ h = 1 := hζ_prim.pow_eq_one
  have hζ_ne : ζ ≠ 0 := Complex.exp_ne_zero _
  have hconj_ζ : starRingEnd ℂ ζ = ζ⁻¹ := by
    dsimp only [ζ]; rw [← Complex.exp_conj, ← Complex.exp_neg]
    congr 1; simp [map_div₀, map_mul, Complex.conj_ofReal, Complex.conj_I, map_ofNat]; ring
  have hconj_pow (i : κ) : starRingEnd ℂ (ζ ^ e i) = ζ ^ (h - e i) := by
    rw [map_pow, hconj_ζ]; refine mul_right_cancel₀ (pow_ne_zero (e i) hζ_ne) ?_
    rw [← mul_pow, inv_mul_cancel₀ hζ_ne, one_pow, ← pow_add,
      Nat.sub_add_cancel (le_of_lt (he_lt i)), hζ_pow]
  have hchar_e : (P.weylGroupRootRep c).charpoly = ∏ i : κ, (X - C (ζ ^ e i)) := by
    rw [P.charpoly_weylGroupRootRep_wordProd_complex b hl hall hf hbij]
    exact Finset.prod_congr rfl fun i _ ↦ by
      rw [pow_eq_pow_of_modEq (Nat.mod_modEq (d i - 1) h).symm hζ_pow]
  have hchar_conj : (P.weylGroupRootRep c).charpoly.map (starRingEnd ℂ) =
      (P.weylGroupRootRep c).charpoly := by
    rw [← charpoly_weylGroupRootRep_wordProd_eq_map_rat P b l, Polynomial.map_map]
    congr 1; exact RingHom.ext_rat _ _
  have hprod_eq : (∏ i : κ, (X - C (ζ ^ e i))) = ∏ i : κ, (X - C (ζ ^ (h - e i))) := by
    rw [← hchar_e, ← hchar_conj, hchar_e, Polynomial.map_prod]
    exact Finset.prod_congr rfl fun i _ ↦ by
      rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, hconj_pow i]
  have hroots (g : κ → ℕ) : (∏ i : κ, (X - C (ζ ^ g i))).roots =
      Finset.univ.val.map (fun i : κ ↦ ζ ^ g i) := by
    rw [Finset.prod_eq_multiset_prod,
      show (Finset.univ.val.map fun i : κ ↦ X - C (ζ ^ g i)) =
        (Finset.univ.val.map fun i : κ ↦ ζ ^ g i).map fun a : ℂ ↦ X - C a by
        simp [Multiset.map_map],
      Polynomial.roots_multiset_prod_X_sub_C]
  have hroots_eq : Finset.univ.val.map (fun i : κ ↦ ζ ^ e i) =
      Finset.univ.val.map (fun i : κ ↦ ζ ^ (h - e i)) := by
    rw [← hroots e, ← hroots (fun i ↦ h - e i), hprod_eq]
  have hcount_pow (g : κ → ℕ) (hg : ∀ i, g i < h) (a : ℕ) (ha : a < h) :
      Multiset.count (ζ ^ a) (Finset.univ.val.map (fun i : κ ↦ ζ ^ g i)) =
        Multiset.count a (Finset.univ.val.map g) := by
    rw [Multiset.count_map, Multiset.count_map]; congr 1; exact Multiset.filter_congr fun i _ ↦
      ⟨fun heq ↦ hζ_prim.pow_inj ha (hg i) heq, fun heq ↦ heq ▸ rfl⟩
  refine Multiset.ext.2 fun a ↦ ?_
  by_cases ha : a < h
  · rw [← hcount_pow e he_lt a ha, ← hcount_pow (fun i ↦ h - e i) hhe_lt a ha, hroots_eq]
  · have hnot {g : κ → ℕ} (hg : ∀ i, g i < h) : a ∉ Finset.univ.val.map g :=
      fun hmem ↦ by rcases Multiset.mem_map.1 hmem with ⟨i, _, hi⟩; exact ha (hi ▸ hg i)
    rw [Multiset.count_eq_zero.2 (hnot he_lt), Multiset.count_eq_zero.2 (hnot hhe_lt)]

/-- Twice the sum of the reduced exponents `(d i - 1) % h` equals `b.support.card * h`. -/
private theorem two_mul_sum_mod_orderOf_eq_complex (b : P.Base)
    {l : List b.support} (hl : l.Nodup) (hall : ∀ i, i ∈ l)
    {κ : Type*} [Fintype κ]
    {f : κ → P.weylGroupRootRep.dual.symmetricAlgebraInvariants} {d : κ → ℕ}
    (hf : ∀ i, (f i : SymmetricAlgebra ℂ (Module.Dual ℂ M)) ∈
      homogeneousSubmodule ℂ (Module.Dual ℂ M) (d i))
    (hbij : Function.Bijective (MvPolynomial.aeval (R := ℂ) f)) :
    2 * ∑ i : κ, (d i - 1) % orderOf (wordProd P b l) =
      b.support.card * orderOf (wordProd P b l) := by
  have : Nontrivial M := IsIrreducible.nontrivial P
  have : Finite P.weylGroup := P.finite_weylGroup
  set h := orderOf (wordProd P b l)
  have hh_pos : 0 < h := orderOf_pos _
  have hcard_κ : Fintype.card κ = b.support.card := by
    rw [← Nat.card_eq_fintype_card,
      P.natCard_eq_card_support_of_bijective_aeval_weylGroupRootRep_dual b hbij]
  have hdual := P.map_mod_orderOf_wordProd_eq_map_sub_complex b hl hall hf hbij
  have hsum_eq : ∑ i : κ, (h - (d i - 1) % h) = ∑ i : κ, (d i - 1) % h :=
    congrArg Multiset.sum hdual.symm
  have hadd : ∑ i : κ, (d i - 1) % h + ∑ i : κ, (h - (d i - 1) % h) = Fintype.card κ * h := by
    rw [← Finset.sum_add_distrib]
    exact (Finset.sum_congr rfl fun i _ ↦ Nat.add_sub_of_le (Nat.mod_lt _ hh_pos).le).trans
      (by simp)
  rwa [hsum_eq, ← two_mul, hcard_κ] at hadd

/-- Over `ℂ`, the root-count equality `Nat.card ι = b.support.card * orderOf (wordProd P b l)`. -/
private theorem natCard_eq_card_support_mul_orderOf_wordProd_complex (b : P.Base)
    {l : List b.support} (hl : l.Nodup) (hall : ∀ i, i ∈ l)
    {κ : Type*} [Finite κ]
    {f : κ → P.weylGroupRootRep.dual.symmetricAlgebraInvariants} {d : κ → ℕ}
    (hf : ∀ i, (f i : SymmetricAlgebra ℂ (Module.Dual ℂ M)) ∈
      homogeneousSubmodule ℂ (Module.Dual ℂ M) (d i))
    (hbij : Function.Bijective (MvPolynomial.aeval (R := ℂ) f)) :
    Nat.card ι = b.support.card * orderOf (wordProd P b l) := by
  let := Fintype.ofFinite κ
  have h1 := P.two_mul_sum_mod_orderOf_eq_complex b hl hall hf hbij
  have hsum_le : ∑ i : κ, (d i - 1) % orderOf (wordProd P b l) ≤ ∑ i : κ, (d i - 1) :=
    Finset.sum_le_sum fun i _ ↦ Nat.mod_le _ _
  have h2 := P.two_mul_sum_sub_one_eq_natCard_of_bijective_aeval_weylGroupRootRep_dual hf hbij
  have h3 := P.natCard_le_card_support_mul_orderOf_wordProd b hl hall
  omega

/-- Over `ℂ`, every exponent satisfies `(d i - 1) % h = d i - 1`. -/
private theorem mod_orderOf_wordProd_eq_self_complex (b : P.Base)
    {l : List b.support} (hl : l.Nodup) (hall : ∀ i, i ∈ l)
    {κ : Type*} [Finite κ]
    {f : κ → P.weylGroupRootRep.dual.symmetricAlgebraInvariants} {d : κ → ℕ}
    (hf : ∀ i, (f i : SymmetricAlgebra ℂ (Module.Dual ℂ M)) ∈
      homogeneousSubmodule ℂ (Module.Dual ℂ M) (d i))
    (hbij : Function.Bijective (MvPolynomial.aeval (R := ℂ) f)) (i : κ) :
    (d i - 1) % orderOf (wordProd P b l) = d i - 1 := by
  let := Fintype.ofFinite κ
  have h1 := P.two_mul_sum_mod_orderOf_eq_complex b hl hall hf hbij
  have h2 := P.two_mul_sum_sub_one_eq_natCard_of_bijective_aeval_weylGroupRootRep_dual hf hbij
  have h3 := P.natCard_eq_card_support_mul_orderOf_wordProd_complex b hl hall hf hbij
  exact (Finset.sum_eq_sum_iff_of_le fun j _ ↦ Nat.mod_le (d j - 1) _).1 (by omega) i
    (Finset.mem_univ i)

/-- Over `ℂ`, every basic invariant degree satisfies `2 ≤ d i ≤ orderOf (wordProd P b l)`. -/
private theorem two_le_and_le_orderOf_wordProd_complex (b : P.Base)
    {l : List b.support} (hl : l.Nodup) (hall : ∀ i, i ∈ l)
    {κ : Type*} [Finite κ]
    {f : κ → P.weylGroupRootRep.dual.symmetricAlgebraInvariants} {d : κ → ℕ}
    (hf : ∀ i, (f i : SymmetricAlgebra ℂ (Module.Dual ℂ M)) ∈
      homogeneousSubmodule ℂ (Module.Dual ℂ M) (d i))
    (hbij : Function.Bijective (MvPolynomial.aeval (R := ℂ) f)) (i : κ) :
    2 ≤ d i ∧ d i ≤ orderOf (wordProd P b l) := by
  have : Nontrivial M := IsIrreducible.nontrivial P
  have hh2 := P.two_le_orderOf_wordProd b hl hall
  have h1 := P.one_le_mod_orderOf_wordProd_complex b hl hall hf hbij i
  have h2 : (d i - 1) % orderOf (wordProd P b l) < orderOf (wordProd P b l) :=
    Nat.mod_lt _ (by omega)
  rw [P.mod_orderOf_wordProd_eq_self_complex b hl hall hf hbij i] at h1 h2
  omega

/-- Over `ℂ`, the multiset of exponents `d i - 1` is invariant under `m ↦ h - m`. -/
private theorem map_sub_one_eq_map_orderOf_sub_complex (b : P.Base)
    {l : List b.support} (hl : l.Nodup) (hall : ∀ i, i ∈ l)
    {κ : Type*} [Fintype κ]
    {f : κ → P.weylGroupRootRep.dual.symmetricAlgebraInvariants} {d : κ → ℕ}
    (hf : ∀ i, (f i : SymmetricAlgebra ℂ (Module.Dual ℂ M)) ∈
      homogeneousSubmodule ℂ (Module.Dual ℂ M) (d i))
    (hbij : Function.Bijective (MvPolynomial.aeval (R := ℂ) f)) :
    Finset.univ.val.map (fun i ↦ d i - 1) =
      Finset.univ.val.map (fun i ↦ orderOf (wordProd P b l) - (d i - 1)) := by
  have h := P.map_mod_orderOf_wordProd_eq_map_sub_complex b hl hall hf hbij
  simpa only [P.mod_orderOf_wordProd_eq_self_complex b hl hall hf hbij] using h

/-- Over `ℂ`, every `a < h` coprime to `h` occurs as an exponent `d i - 1`. -/
private theorem exists_degree_sub_one_eq_of_coprime_orderOf_wordProd_complex (b : P.Base)
    {l : List b.support} (hl : l.Nodup) (hall : ∀ i, i ∈ l)
    {κ : Type*} [Finite κ]
    {f : κ → P.weylGroupRootRep.dual.symmetricAlgebraInvariants} {d : κ → ℕ}
    (hf : ∀ i, (f i : SymmetricAlgebra ℂ (Module.Dual ℂ M)) ∈
      homogeneousSubmodule ℂ (Module.Dual ℂ M) (d i))
    (hbij : Function.Bijective (MvPolynomial.aeval (R := ℂ) f))
    {a : ℕ} (ha : a < orderOf (wordProd P b l)) (hcop : a.Coprime (orderOf (wordProd P b l))) :
    ∃ i : κ, d i - 1 = a := by
  have : Nontrivial M := IsIrreducible.nontrivial P
  have : Nonempty b.support := b.nonempty_support_of_isIrreducible
  have : Nonempty ι := ⟨(Classical.arbitrary b.support : ι)⟩
  have hh_pos : 0 < orderOf (wordProd P b l) := by
    have := P.two_le_orderOf_wordProd b hl hall; omega
  obtain ⟨v, hv_reg, hv_eig⟩ := P.exists_isRegularWeight_wordProd_smul_eq_inv_exp_smul b hl hall
  let ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / orderOf (wordProd P b l))
  have hζ_prim : IsPrimitiveRoot ζ (orderOf (wordProd P b l)) :=
    Complex.isPrimitiveRoot_exp _ hh_pos.ne'
  let uζ : ℂˣ := Units.mk0 ζ⁻¹ (inv_ne_zero (Complex.exp_ne_zero _))
  have huζ_prim : IsPrimitiveRoot (uζ : ℂ) (orderOf (wordProd P b l)) := by
    simpa [uζ] using hζ_prim.inv
  have hd_lt (i : κ) : d i - 1 < orderOf (wordProd P b l) := by
    have := P.two_le_and_le_orderOf_wordProd_complex b hl hall hf hbij i; omega
  exact P.exists_degree_sub_one_eq_of_isRegularWeight hf hbij (wordProd P b l) v uζ huζ_prim
    hv_reg hv_eig hv_reg.ne_zero hd_lt ha hcop

end ComplexExponents

section CoxeterNumber

variable {ι R M N : Type*} [CommRing R] [IsDomain R] [CharZero R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (P : RootPairing ι R M N) [Finite ι] [P.IsCrystallographic] [P.IsReduced]
  [P.IsRootSystem] [P.IsIrreducible]

/-- **Number of roots equals rank times Coxeter number.** -/
theorem natCard_eq_card_support_mul_orderOf_wordProd (b : P.Base)
    {l : List b.support} (hl : l.Nodup) (hall : ∀ i, i ∈ l) :
    Nat.card ι = b.support.card * orderOf (wordProd P b l) := by
  let PC := baseChangeRat b ℂ
  let bC := baseChangeRatBase b ℂ
  let eCB := baseChangeRatSupportEquiv b ℂ
  let lC : List bC.support := l.map eCB.symm
  have hlC : lC.Nodup := hl.map eCB.symm.injective
  have hallC : ∀ j : bC.support, j ∈ lC := fun j ↦
    List.mem_map.2 ⟨eCB j, hall (eCB j), eCB.symm_apply_apply j⟩
  obtain ⟨g, hg_ex, hgbij⟩ := PC.exists_bijective_aeval_weylGroupRootRep_dual_of_isRootSystem
  let e : Fin (Module.finrank ℂ (b.support → ℂ)) → ℕ := fun j ↦ (hg_ex j).choose
  have hg : ∀ j, (g j : SymmetricAlgebra ℂ (Module.Dual ℂ (b.support → ℂ))) ∈
      homogeneousSubmodule ℂ (Module.Dual ℂ (b.support → ℂ)) (e j) := fun j ↦
    (hg_ex j).choose_spec.2
  have hcardC := PC.natCard_eq_card_support_mul_orderOf_wordProd_complex bC hlC hallC hg hgbij
  have hcard_supp : bC.support.card = b.support.card := by
    rw [← Fintype.card_coe, ← Fintype.card_coe]; exact Fintype.card_congr eCB
  rwa [hcard_supp, ← orderOf_wordProd_baseChangeRat b ℂ l] at hcardC

/-- **Twice the number of positive roots equals rank times Coxeter number.** -/
theorem two_mul_ncard_posRoots_eq_card_support_mul_orderOf_wordProd (b : P.Base)
    {l : List b.support} (hl : l.Nodup) (hall : ∀ i, i ∈ l) :
    2 * (posRoots P b).ncard = b.support.card * orderOf (wordProd P b l) := by
  rw [two_mul_ncard_posRoots P b, P.natCard_eq_card_support_mul_orderOf_wordProd b hl hall]

end CoxeterNumber

section ExponentsAndEigenvalues

variable {ι K M N : Type*} [Field K] [CharZero K]
  [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]
  (P : RootPairing ι K M N) [Finite ι] [P.IsCrystallographic] [P.IsReduced]
  [P.IsRootSystem] [P.IsIrreducible]

omit [CharZero K] [P.IsCrystallographic] [P.IsReduced] in
private lemma finite_of_bijective_aeval_weylGroupRootRep_dual (b : P.Base) {κ : Type*}
    {f : κ → P.weylGroupRootRep.dual.symmetricAlgebraInvariants}
    (hbij : Function.Bijective (MvPolynomial.aeval (R := K) f)) : Finite κ := by
  have : Nontrivial M := IsIrreducible.nontrivial P
  have : Module.Finite K M := Module.Finite.of_basis b.toWeightBasis
  have : 0 < b.support.card := by
    rw [← Fintype.card_coe, ← Module.finrank_eq_card_basis b.toWeightBasis]
    exact Module.finrank_pos
  exact Nat.finite_of_card_ne_zero
    ((P.natCard_eq_card_support_of_bijective_aeval_weylGroupRootRep_dual b hbij).symm ▸
      this.ne')

omit [P.IsReduced] [P.IsIrreducible] in
private lemma exists_complex_bijective_aeval_degrees_eq (b : P.Base)
    {κ : Type*} [Fintype κ]
    {f : κ → P.weylGroupRootRep.dual.symmetricAlgebraInvariants} {d : κ → ℕ}
    (hf : ∀ i, (f i : SymmetricAlgebra K (Module.Dual K M)) ∈
      homogeneousSubmodule K (Module.Dual K M) (d i))
    (hbij : Function.Bijective (MvPolynomial.aeval (R := K) f)) :
    ∃ (g : Fin (Module.finrank ℂ (b.support → ℂ)) →
        (baseChangeRat b ℂ).weylGroupRootRep.dual.symmetricAlgebraInvariants)
      (e : Fin (Module.finrank ℂ (b.support → ℂ)) → ℕ),
      (∀ j, (g j : SymmetricAlgebra ℂ (Module.Dual ℂ (b.support → ℂ))) ∈
        homogeneousSubmodule ℂ (Module.Dual ℂ (b.support → ℂ)) (e j)) ∧
      Function.Bijective (MvPolynomial.aeval (R := ℂ) g) ∧
      Finset.univ.val.map d = Finset.univ.val.map e := by
  have : Module.Finite K M := Module.Finite.of_basis b.toWeightBasis
  obtain ⟨g, hg_ex, hgbij⟩ :=
    (baseChangeRat b ℂ).exists_bijective_aeval_weylGroupRootRep_dual_of_isRootSystem
  refine ⟨g, fun j ↦ (hg_ex j).choose, fun j ↦ (hg_ex j).choose_spec.2, hgbij, ?_⟩
  exact b.map_univ_eq_of_bijective_aeval_weylGroupRootRep_dual_rootPairingBaseChange_rationalModel
    ℂ hf hbij (fun j ↦ (hg_ex j).choose_spec.2) hgbij

/-- **Degree bounds for basic invariants of an irreducible crystallographic Weyl group.**
Every basic invariant degree `d i` satisfies `2 ≤ d i ≤ orderOf (wordProd P b l)`. -/
theorem two_le_and_le_orderOf_wordProd_of_bijective_aeval_weylGroupRootRep_dual (b : P.Base)
    {l : List b.support} (hl : l.Nodup) (hall : ∀ i, i ∈ l)
    {κ : Type*}
    {f : κ → P.weylGroupRootRep.dual.symmetricAlgebraInvariants} {d : κ → ℕ}
    (hf : ∀ i, (f i : SymmetricAlgebra K (Module.Dual K M)) ∈
      homogeneousSubmodule K (Module.Dual K M) (d i))
    (hbij : Function.Bijective (MvPolynomial.aeval (R := K) f)) (i : κ) :
    2 ≤ d i ∧ d i ≤ orderOf (wordProd P b l) := by
  have : Finite κ := P.finite_of_bijective_aeval_weylGroupRootRep_dual b hbij
  let := Fintype.ofFinite κ
  let eCB := baseChangeRatSupportEquiv b ℂ
  let lC := l.map eCB.symm
  have hlC : lC.Nodup := hl.map eCB.symm.injective
  have hallC : ∀ j, j ∈ lC := fun j ↦ List.mem_map.2 ⟨eCB j, hall (eCB j), eCB.symm_apply_apply j⟩
  obtain ⟨g, e, hg, hgbij, hmult⟩ := P.exists_complex_bijective_aeval_degrees_eq b hf hbij
  rcases Multiset.mem_map.1 (hmult ▸ Multiset.mem_map.2 ⟨i, Finset.mem_univ i, rfl⟩)
    with ⟨j, -, hj⟩
  rw [orderOf_wordProd_baseChangeRat b ℂ l, ← hj]
  exact (baseChangeRat b ℂ).two_le_and_le_orderOf_wordProd_complex (baseChangeRatBase b ℂ) hlC hallC
    hg hgbij j

/-- **Exponent duality for irreducible crystallographic Weyl groups.** The multiset of exponents
`d i - 1` is invariant under `m ↦ orderOf (wordProd P b l) - m`. -/
theorem map_sub_one_eq_map_orderOf_sub_of_bijective_aeval_weylGroupRootRep_dual (b : P.Base)
    {l : List b.support} (hl : l.Nodup) (hall : ∀ i, i ∈ l)
    {κ : Type*} [Fintype κ]
    {f : κ → P.weylGroupRootRep.dual.symmetricAlgebraInvariants} {d : κ → ℕ}
    (hf : ∀ i, (f i : SymmetricAlgebra K (Module.Dual K M)) ∈
      homogeneousSubmodule K (Module.Dual K M) (d i))
    (hbij : Function.Bijective (MvPolynomial.aeval (R := K) f)) :
    Finset.univ.val.map (fun i ↦ d i - 1) =
      Finset.univ.val.map (fun i ↦ orderOf (wordProd P b l) - (d i - 1)) := by
  let eCB := baseChangeRatSupportEquiv b ℂ
  let lC := l.map eCB.symm
  have hlC : lC.Nodup := hl.map eCB.symm.injective
  have hallC : ∀ j, j ∈ lC := fun j ↦ List.mem_map.2 ⟨eCB j, hall (eCB j), eCB.symm_apply_apply j⟩
  obtain ⟨g, e, hg, hgbij, hmult⟩ := P.exists_complex_bijective_aeval_degrees_eq b hf hbij
  have hdualC := (baseChangeRat b ℂ).map_sub_one_eq_map_orderOf_sub_complex (baseChangeRatBase b ℂ)
    hlC hallC hg hgbij
  rw [← orderOf_wordProd_baseChangeRat b ℂ l] at hdualC
  have h1 := congrArg (Multiset.map (· - 1)) hmult
  have h2 := congrArg (Multiset.map (fun m ↦ orderOf (wordProd P b l) - (m - 1))) hmult
  simp only [Multiset.map_map, Function.comp_def] at h1 h2
  exact h1.trans (hdualC.trans h2.symm)

/-- **Crystallographic coprime-exponent theorem.** Every `a < orderOf (wordProd P b l)` coprime to
`orderOf (wordProd P b l)` occurs as an exponent `d i - 1`. -/
theorem exists_degree_sub_one_eq_of_coprime_orderOf_wordProd (b : P.Base)
    {l : List b.support} (hl : l.Nodup) (hall : ∀ i, i ∈ l)
    {κ : Type*}
    {f : κ → P.weylGroupRootRep.dual.symmetricAlgebraInvariants} {d : κ → ℕ}
    (hf : ∀ i, (f i : SymmetricAlgebra K (Module.Dual K M)) ∈
      homogeneousSubmodule K (Module.Dual K M) (d i))
    (hbij : Function.Bijective (MvPolynomial.aeval (R := K) f))
    {a : ℕ} (ha : a < orderOf (wordProd P b l)) (hcop : a.Coprime (orderOf (wordProd P b l))) :
    ∃ i : κ, d i - 1 = a := by
  have : Finite κ := P.finite_of_bijective_aeval_weylGroupRootRep_dual b hbij
  let := Fintype.ofFinite κ
  let eCB := baseChangeRatSupportEquiv b ℂ
  let lC := l.map eCB.symm
  have hlC : lC.Nodup := hl.map eCB.symm.injective
  have hallC : ∀ j, j ∈ lC := fun j ↦ List.mem_map.2 ⟨eCB j, hall (eCB j), eCB.symm_apply_apply j⟩
  obtain ⟨g, e, hg, hgbij, hmult⟩ := P.exists_complex_bijective_aeval_degrees_eq b hf hbij
  rw [orderOf_wordProd_baseChangeRat b ℂ l] at ha hcop
  obtain ⟨j, hj⟩ :=
    (baseChangeRat b ℂ).exists_degree_sub_one_eq_of_coprime_orderOf_wordProd_complex
      (baseChangeRatBase b ℂ) hlC hallC hg hgbij ha hcop
  rcases Multiset.mem_map.1 (hmult.symm ▸ Multiset.mem_map.2 ⟨j, Finset.mem_univ j, rfl⟩)
    with ⟨i, -, hi⟩
  exact ⟨i, hi ▸ hj⟩

/-- **Existence of a quadratic basic invariant.** -/
theorem exists_degree_eq_two_of_bijective_aeval_weylGroupRootRep_dual
    {κ : Type*}
    {f : κ → P.weylGroupRootRep.dual.symmetricAlgebraInvariants} {d : κ → ℕ}
    (hf : ∀ i, (f i : SymmetricAlgebra K (Module.Dual K M)) ∈
      homogeneousSubmodule K (Module.Dual K M) (d i))
    (hbij : Function.Bijective (MvPolynomial.aeval (R := K) f)) :
    ∃ i : κ, d i = 2 := by
  obtain ⟨b⟩ := P.nonempty_base; have : Nontrivial M := IsIrreducible.nontrivial P
  have hl := Finset.nodup_toList (Finset.univ : Finset b.support)
  have hh2 := P.two_le_orderOf_wordProd b hl (fun j ↦ by simp)
  obtain ⟨i, hi⟩ := P.exists_degree_sub_one_eq_of_coprime_orderOf_wordProd b hl
    (fun j ↦ by simp) hf hbij (a := 1) (by omega) (Nat.coprime_one_left _)
  exact ⟨i, by omega⟩

/-- **The Coxeter number is a basic invariant degree.** Some `d i` equals
`orderOf (wordProd P b l)`; together with
`two_le_and_le_orderOf_wordProd_of_bijective_aeval_weylGroupRootRep_dual` it is the largest. -/
theorem exists_degree_eq_orderOf_wordProd_of_bijective_aeval_weylGroupRootRep_dual (b : P.Base)
    {l : List b.support} (hl : l.Nodup) (hall : ∀ i, i ∈ l)
    {κ : Type*}
    {f : κ → P.weylGroupRootRep.dual.symmetricAlgebraInvariants} {d : κ → ℕ}
    (hf : ∀ i, (f i : SymmetricAlgebra K (Module.Dual K M)) ∈
      homogeneousSubmodule K (Module.Dual K M) (d i))
    (hbij : Function.Bijective (MvPolynomial.aeval (R := K) f)) :
    ∃ i : κ, d i = orderOf (wordProd P b l) := by
  have : Nontrivial M := IsIrreducible.nontrivial P
  have hh2 : 2 ≤ orderOf (wordProd P b l) := P.two_le_orderOf_wordProd b hl hall
  have hcop : (orderOf (wordProd P b l) - 1).Coprime (orderOf (wordProd P b l)) :=
    (Nat.coprime_self_sub_left (by omega)).2 (Nat.coprime_one_left _)
  obtain ⟨i, hi⟩ := P.exists_degree_sub_one_eq_of_coprime_orderOf_wordProd b hl hall hf hbij
    (a := orderOf (wordProd P b l) - 1) (by omega) hcop
  exact ⟨i, by omega⟩

/-- **Characteristic polynomial of a Coxeter element from basic invariant degrees.** Over any
characteristic-zero field `K` and any primitive `h`-th root of unity `ζ : K` where
`h = orderOf (wordProd P b l)`, the characteristic polynomial of
`P.weylGroupRootRep (wordProd P b l)` is `∏ i, (X - C (ζ ^ (d i - 1)))`. -/
theorem charpoly_weylGroupRootRep_wordProd_eq_prod [Module.Finite K M] (b : P.Base)
    {l : List b.support} (hl : l.Nodup) (hall : ∀ i, i ∈ l)
    {κ : Type*} [Fintype κ]
    {f : κ → P.weylGroupRootRep.dual.symmetricAlgebraInvariants} {d : κ → ℕ}
    (hf : ∀ i, (f i : SymmetricAlgebra K (Module.Dual K M)) ∈
      homogeneousSubmodule K (Module.Dual K M) (d i))
    (hbij : Function.Bijective (MvPolynomial.aeval (R := K) f))
    {ζ : K} (hζ : IsPrimitiveRoot ζ (orderOf (wordProd P b l))) :
    (P.weylGroupRootRep (wordProd P b l)).charpoly = ∏ i : κ, (X - C (ζ ^ (d i - 1))) := by
  classical
  have : Nontrivial M := IsIrreducible.nontrivial P
  have : Finite P.weylGroup := P.finite_weylGroup
  set h : ℕ := orderOf (wordProd P b l)
  have hh_pos : 0 < h := orderOf_pos _
  let PC := baseChangeRat b ℂ
  let bC := baseChangeRatBase b ℂ
  let eCB := baseChangeRatSupportEquiv b ℂ
  let lC : List bC.support := l.map eCB.symm
  have hlC : lC.Nodup := hl.map eCB.symm.injective
  have hallC : ∀ j, j ∈ lC := fun j ↦ List.mem_map.2 ⟨eCB j, hall (eCB j), eCB.symm_apply_apply j⟩
  obtain ⟨g, e, hg, hgbij, hmult⟩ := P.exists_complex_bijective_aeval_degrees_eq b hf hbij
  have hcharC := PC.charpoly_weylGroupRootRep_wordProd_complex bC hlC hallC hg hgbij
  rw [← orderOf_wordProd_baseChangeRat b ℂ l] at hcharC
  set ζC : ℂ := Complex.exp (2 * Real.pi * Complex.I / h)
  have hζC_prim : IsPrimitiveRoot ζC h := Complex.isPrimitiveRoot_exp h hh_pos.ne'
  let p : ℚ[X] := ((l.map (reflMatrix b.cartanMatrix)).prod.map (Int.castRingHom ℚ)).charpoly
  have hprodC : p.map (algebraMap ℚ ℂ) = ∏ i : κ, (X - C (ζC ^ (d i - 1))) := by
    rw [charpoly_weylGroupRootRep_wordProd_baseChangeRat b ℂ l, hcharC,
      Finset.prod_eq_multiset_prod, Finset.prod_eq_multiset_prod]
    have hmap := congrArg (Multiset.map (fun m ↦ X - C (ζC ^ (m - 1)))) hmult
    simp only [Multiset.map_map, Function.comp_def] at hmap
    exact congrArg Multiset.prod hmap.symm
  let F₁ : Polynomial ℚ[X] := p.map Polynomial.C
  let F₂ : Polynomial ℚ[X] := ∏ i : κ, (X - C ((X : ℚ[X]) ^ (d i - 1)))
  have heqC : F₁.map (Polynomial.aeval ζC).toRingHom = F₂.map (Polynomial.aeval ζC).toRingHom := by
    dsimp only [F₁, F₂]
    rw [map_aeval_map_C, Polynomial.map_prod, hprodC]
    simp
  have heqK := Polynomial.map_aeval_eq_of_isPrimitiveRoot hh_pos hζC_prim hζ heqC
  rw [← charpoly_weylGroupRootRep_wordProd_eq_map_rat P b l, ← map_aeval_map_C p ζ]
  dsimp only [F₁, F₂] at heqK
  rw [Polynomial.map_prod] at heqK
  simpa using heqK

end ExponentsAndEigenvalues

end RootPairing
