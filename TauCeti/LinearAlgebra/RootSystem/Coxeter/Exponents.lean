/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.Coxeter.Plane
public import TauCeti.LinearAlgebra.RootSystem.Inversions.Length
public import TauCeti.RepresentationTheory.SymmetricAlgebra.Weyl

import Mathlib.LinearAlgebra.Eigenspace.Charpoly
import Mathlib.LinearAlgebra.RootSystem.BaseExists
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.RingTheory.RootsOfUnity.Complex
import TauCeti.LinearAlgebra.Matrix.Cartan.Coxeter.Basic
import TauCeti.LinearAlgebra.RootSystem.CoweightLattice.Basis
import TauCeti.LinearAlgebra.RootSystem.Coxeter.Element.ActsBy
import TauCeti.LinearAlgebra.RootSystem.Coxeter.FixedPoints
import TauCeti.LinearAlgebra.RootSystem.Inversions.Subword
import TauCeti.LinearAlgebra.RootSystem.Weyl.Pseudoreflection
import TauCeti.LinearAlgebra.RootSystem.Weyl.ReflectionPerm
import TauCeti.RepresentationTheory.SymmetricAlgebra.Weyl.BaseChange

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

omit [IsDomain R] [CharZero R] [Finite ι] [P.IsCrystallographic] [P.IsReduced]
  [P.IsRootSystem] in
private lemma length_eq_card_support {b : P.Base} {l : List b.support}
    (hl : l.Nodup) (hall : ∀ i, i ∈ l) : l.length = b.support.card := by
  classical
  have htoFinset : l.toFinset = Finset.univ := by ext i; simp [hall]
  rw [← List.toFinset_card_of_nodup hl, htoFinset, Finset.card_univ, Fintype.card_coe]

/-- **Coxeter-orbit inversion bound.** Every `⟨c⟩`-orbit of roots meets the inversion set of a
Coxeter element `c`, so `Nat.card ι ≤ (inversions P b c).ncard * orderOf c`. -/
theorem natCard_le_ncard_inversions_mul_orderOf_wordProd (b : P.Base)
    {l : List b.support} (hl : l.Nodup) (hall : ∀ i, i ∈ l) :
    Nat.card ι ≤ (inversions P b (wordProd P b l)).ncard * orderOf (wordProd P b l) := by
  classical
  have : Finite P.weylGroup := P.finite_weylGroup_of_base b
  set c : P.weylGroup := wordProd P b l; set h : ℕ := orderOf c
  have hh_pos : 0 < h := orderOf_pos c
  set f : Equiv.Perm ι := P.weylGroupToPerm c
  have hf_pow : f ^ h = 1 := by dsimp only [f]; rw [← map_pow, pow_orderOf_eq_one, map_one]
  have hsurj : Function.Surjective
      (fun p : (inversions P b c) × Fin h ↦ (f ^ (p.2 : ℕ)) p.1.val) := by
    intro i
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
      change (f ^ (((k : ℕ) + 1) % h)) i = f ((f ^ (k : ℕ)) i)
      rw [pow_eq_pow_of_modEq (Nat.mod_modEq ((k : ℕ) + 1) h) hf_pow, pow_succ']; rfl
    have hsum_zero : ∑ j ∈ S, P.root j = 0 := by
      rw [← wordProd_smul_eq_self_iff_eq_zero b hl hall]
      change c • ∑ j ∈ S, P.root j = ∑ j ∈ S, P.root j
      rw [Finset.smul_sum]; simp_rw [P.weylGroup_apply_root]
      change ∑ j ∈ S, P.root (f j) = ∑ j ∈ S, P.root j
      rw [← Finset.sum_image (g := f) fun _ _ _ _ h ↦ f.injective h, hS_img]
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
      change ¬ b.IsPos ((f ^ ((b' : ℕ) + (h - (a : ℕ))) * f ^ (a : ℕ)) i)
      rw [← pow_add, show (b' : ℕ) + (h - (a : ℕ)) + (a : ℕ) = (b' : ℕ) + h by omega,
        pow_add, hf_pow, mul_one]; exact hj₁_neg
    set m₀ : ℕ := Nat.find hex_step
    have hm₀_spec : ¬ b.IsPos ((f ^ m₀) ((f ^ (a : ℕ)) i)) := Nat.find_spec hex_step
    have hm₀_ne : m₀ ≠ 0 := fun h0 ↦ hm₀_spec (h0 ▸ hj₂_pos)
    set n : ℕ := m₀ - 1
    have hn_inv : (f ^ n) ((f ^ (a : ℕ)) i) ∈ inversions P b c := by
      rw [mem_inversions]
      refine ⟨by by_contra hneg; exact Nat.find_min hex_step (by omega) hneg, ?_⟩
      change ¬ b.IsPos (f ((f ^ n) ((f ^ (a : ℕ)) i)))
      rw [show f ((f ^ n) ((f ^ (a : ℕ)) i)) = (f ^ m₀) ((f ^ (a : ℕ)) i) by
        rw [← Nat.sub_add_cancel (Nat.pos_of_ne_zero hm₀_ne), pow_succ']; rfl]
      exact hm₀_spec
    let k : Fin h := ⟨(h - (n + (a : ℕ)) % h) % h, Nat.mod_lt _ hh_pos⟩
    refine ⟨(⟨(f ^ n) ((f ^ (a : ℕ)) i), hn_inv⟩, k), ?_⟩
    change (f ^ (k : ℕ) * f ^ n * f ^ (a : ℕ)) i = i
    rw [← pow_add, ← pow_add, pow_eq_pow_of_modEq (Nat.mod_modEq _ h).symm hf_pow]
    have hmod0 : ((k : ℕ) + n + (a : ℕ)) % h = 0 := by
      dsimp only [k]; rw [add_assoc, Nat.mod_add_mod, ← Nat.add_mod_mod,
        Nat.sub_add_cancel (Nat.mod_lt _ hh_pos).le, Nat.mod_self]
    rw [hmod0, pow_zero]; rfl
  calc Nat.card ι
      ≤ Nat.card ((inversions P b c) × Fin h) := Nat.card_le_card_of_surjective _ hsurj
    _ = (inversions P b c).ncard * h := by rw [Nat.card_prod, Nat.card_coe_set_eq, Nat.card_fin]

/-- **Rank times Coxeter order bounds the number of roots.** -/
theorem natCard_le_card_support_mul_orderOf_wordProd (b : P.Base)
    {l : List b.support} (hl : l.Nodup) (hall : ∀ i, i ∈ l) :
    Nat.card ι ≤ b.support.card * orderOf (wordProd P b l) := by
  have hinv : (inversions P b (wordProd P b l)).ncard ≤ b.support.card := by
    rw [← P.length_eq_card_support hl hall]; exact ncard_inversions_wordProd_le_length P b l
  exact (P.natCard_le_ncard_inversions_mul_orderOf_wordProd b hl hall).trans
    (Nat.mul_le_mul_right _ hinv)

/-- **Every Coxeter element is a reduced word**:
`#(inversions (wordProd P b l)) = b.support.card`. -/
theorem ncard_inversions_wordProd_eq_card_support (b : P.Base)
    {l : List b.support} (hl : l.Nodup) (hall : ∀ i, i ∈ l) :
    (inversions P b (wordProd P b l)).ncard = b.support.card := by
  classical
  have hle : (inversions P b (wordProd P b l)).ncard ≤ b.support.card := by
    rw [← P.length_eq_card_support hl hall]; exact ncard_inversions_wordProd_le_length P b l
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

omit [IsDomain R] [Finite ι] [P.IsReduced] in
private theorem orderOf_wordProd_eq_baseChange (S : Type*) [Field S] [CharZero S]
    (b : P.Base) (l : List b.support) :
    orderOf (wordProd P b l) =
      orderOf (wordProd (rootPairingBaseChange S b.rationalModel b.rationalModel_toLinearMap)
        (rootPairingBaseChangeBase S b.rationalModel b.rationalModel_toLinearMap
          b.rationalModelBase)
        (l.map ((supportEquivRootPairingBaseChangeBase S b.rationalModel
          b.rationalModel_toLinearMap b.rationalModelBase).trans
          b.supportEquivRationalModelBase).symm)) := by
  let PS := rootPairingBaseChange S b.rationalModel b.rationalModel_toLinearMap
  let bS := rootPairingBaseChangeBase S b.rationalModel b.rationalModel_toLinearMap
    b.rationalModelBase
  let e : bS.support ≃ b.support :=
    (supportEquivRootPairingBaseChangeBase S b.rationalModel b.rationalModel_toLinearMap
      b.rationalModelBase).trans b.supportEquivRationalModelBase
  let φ : P.weylGroup ≃* PS.weylGroup :=
    weylGroupEquivOfReflectionPermEq P PS
      (by
        rw [show PS = rootPairingBaseChange S b.rationalModel b.rationalModel_toLinearMap from rfl,
          reflectionPerm_rootPairingBaseChange, b.rationalModel_reflectionPerm])
      P.weylGroupToPerm_injective PS.weylGroupToPerm_injective
  have he_coe (i : b.support) : ((e.symm i : bS.support) : ι) = (i : ι) := by
    conv_rhs => rw [← e.apply_symm_apply i]
    dsimp only [e]
    rw [Equiv.trans_apply, Base.coe_supportEquivRationalModelBase,
      coe_supportEquivRootPairingBaseChangeBase]
  have hφ_word (m : List b.support) :
      φ (wordProd P b m) = wordProd PS bS (m.map e.symm) := by
    induction m with
    | nil => simp [wordProd_nil]
    | cons i t ih =>
      simp only [wordProd_cons, map_mul, ih, List.map_cons, φ,
        weylGroupEquivOfReflectionPermEq_ofIdx, he_coe]
  rw [← hφ_word l]
  exact (φ.orderOf_eq (wordProd P b l)).symm

end OrbitAndInversions

section ComplexSandwich

private theorem charpoly_weylGroupRootRep_wordProd_eq_map_rat
    {ι K M N : Type*} [DecidableEq ι] [Field K] [CharZero K] [AddCommGroup M] [Module K M]
    [Module.Finite K M] [AddCommGroup N] [Module K N] (P : RootPairing ι K M N)
    [P.IsCrystallographic] [P.IsRootSystem] (b : P.Base) (l : List b.support) :
    (((l.map (reflMatrix b.cartanMatrix)).prod.map (Int.castRingHom ℚ)).charpoly).map
        (algebraMap ℚ K) =
      (P.weylGroupRootRep (wordProd P b l)).charpoly := by
  rw [← (b.actsBy_wordProd l).map_charpoly_eq_charpoly_weylGroupRootRep,
    Matrix.charpoly_map, Polynomial.map_map]
  congr 1; exact RingHom.ext_int _ _

private theorem complex_coxeter_exponents_package
    {ι M N : Type*} [AddCommGroup M] [Module ℂ M] [Module.Finite ℂ M]
    [AddCommGroup N] [Module ℂ N]
    (P : RootPairing ι ℂ M N) [Finite ι] [P.IsCrystallographic] [P.IsReduced]
    [P.IsRootSystem] [P.IsIrreducible] (b : P.Base)
    {l : List b.support} (hl : l.Nodup) (hall : ∀ i, i ∈ l)
    {κ : Type*} [Fintype κ]
    {f : κ → P.weylGroupRootRep.dual.symmetricAlgebraInvariants} {d : κ → ℕ}
    (hf : ∀ i, (f i : SymmetricAlgebra ℂ (Module.Dual ℂ M)) ∈
      homogeneousSubmodule ℂ (Module.Dual ℂ M) (d i))
    (hbij : Function.Bijective (MvPolynomial.aeval (R := ℂ) f)) :
    let h := orderOf (wordProd P b l)
    Nat.card ι = b.support.card * h ∧
    (∀ i, 2 ≤ d i ∧ d i ≤ h) ∧
    Finset.univ.val.map (fun i ↦ d i - 1) = Finset.univ.val.map (fun i ↦ h - (d i - 1)) ∧
    (P.weylGroupRootRep (wordProd P b l)).charpoly =
      ∏ i : κ, (X - C (Complex.exp (2 * Real.pi * Complex.I / h) ^ (d i - 1))) ∧
    (∀ {a : ℕ}, a < h → a.Coprime h → ∃ i : κ, d i - 1 = a) := by
  classical
  have : Nontrivial M := IsIrreducible.nontrivial P
  have : Finite P.weylGroup := P.finite_weylGroup
  set c : P.weylGroup := wordProd P b l; set h : ℕ := orderOf c
  have hh2 : 2 ≤ h := P.two_le_orderOf_wordProd b hl hall
  have hh_pos : 0 < h := by omega
  set ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / h)
  have hζ_prim : IsPrimitiveRoot ζ h := Complex.isPrimitiveRoot_exp h hh_pos.ne'
  have hζ_pow : ζ ^ h = 1 := hζ_prim.pow_eq_one
  have hζ_ne : ζ ≠ 0 := Complex.exp_ne_zero _
  let uζ : ℂˣ := Units.mk0 ζ⁻¹ (inv_ne_zero hζ_ne)
  have huζ_inv : (↑(uζ⁻¹) : ℂ) = ζ := by simp [uζ]
  have huζ_prim : IsPrimitiveRoot (uζ : ℂ) h := by
    have hinv : IsPrimitiveRoot (↑(uζ⁻¹) : ℂ) h := by simpa [huζ_inv] using hζ_prim
    simpa using IsPrimitiveRoot.coe_units_iff.mpr (IsPrimitiveRoot.coe_units_iff.mp hinv).inv
  have hcard_κ : Fintype.card κ = b.support.card := by
    rw [← Nat.card_eq_fintype_card,
      P.natCard_eq_card_support_of_bijective_aeval_weylGroupRootRep_dual b hbij]
  obtain ⟨v, hv_reg, hv_eig⟩ := P.exists_isRegularWeight_smul_eq_exp_neg_wordProd b hl hall
  have hv_ne : v ≠ 0 := fun h0 ↦ by
    have : Nonempty b.support := by_contra fun hne ↦ by
      rw [not_nonempty_iff] at hne; exact not_subsingleton M b.toWeightBasis.equivFun.subsingleton
    exact (isRegularWeight_iff P v).1 hv_reg this.some (by rw [h0, map_zero])
  have hcharpoly : (P.weylGroupRootRep c).charpoly = ∏ i : κ, (X - C (ζ ^ (d i - 1))) := by
    simpa [huζ_inv] using
      P.charpoly_weylGroupRootRep_eq_prod_of_isRegularWeight hf hbij c v uζ hv_reg hv_eig
  let p : ℚ[X] := ((l.map (reflMatrix b.cartanMatrix)).prod.map (Int.castRingHom ℚ)).charpoly
  have hp : p.map (algebraMap ℚ ℂ) = (P.weylGroupRootRep c).charpoly :=
    P.charpoly_weylGroupRootRep_wordProd_eq_map_rat b l
  let e : κ → ℕ := fun i ↦ (d i - 1) % h
  have he_lt (i : κ) : e i < h := Nat.mod_lt _ hh_pos
  have he_pos (i : κ) : 1 ≤ e i := by
    by_contra hlt; have he0 : e i = 0 := by omega
    have hroot1 : (P.weylGroupRootRep c).charpoly.IsRoot 1 := by
      rw [Polynomial.IsRoot, hcharpoly, Polynomial.eval_prod]
      exact Finset.prod_eq_zero (Finset.mem_univ i) (by
        rw [pow_eq_pow_of_modEq (Nat.mod_modEq (d i - 1) h).symm hζ_pow,
          show (d i - 1) % h = 0 from he0, pow_zero]; simp)
    exact not_hasEigenvalue_one_wordProd b hl hall
      ((Module.End.hasEigenvalue_iff_isRoot_charpoly (P.weylGroupRootRep c) 1).2 hroot1)
  have hhe_lt (i : κ) : h - e i < h := by have := he_pos i; omega
  have hconj_ζ : starRingEnd ℂ ζ = ζ⁻¹ := by
    dsimp only [ζ]; rw [← Complex.exp_conj, ← Complex.exp_neg]
    congr 1; simp [map_div₀, map_mul, Complex.conj_ofReal, Complex.conj_I, map_ofNat]; ring
  have hconj_pow (i : κ) : starRingEnd ℂ (ζ ^ e i) = ζ ^ (h - e i) := by
    rw [map_pow, hconj_ζ]; refine mul_right_cancel₀ (pow_ne_zero (e i) hζ_ne) ?_
    rw [← mul_pow, inv_mul_cancel₀ hζ_ne, one_pow, ← pow_add,
      Nat.sub_add_cancel (le_of_lt (he_lt i)), hζ_pow]
  have hchar_e : (P.weylGroupRootRep c).charpoly = ∏ i : κ, (X - C (ζ ^ e i)) :=
    hcharpoly.trans (Finset.prod_congr rfl fun i _ ↦ by
      rw [pow_eq_pow_of_modEq (Nat.mod_modEq (d i - 1) h).symm hζ_pow])
  have hchar_conj : (P.weylGroupRootRep c).charpoly.map (starRingEnd ℂ) =
      (P.weylGroupRootRep c).charpoly := by
    rw [← hp, Polynomial.map_map]; congr 1; exact RingHom.ext_rat _ _
  have hprod_eq : (∏ i : κ, (X - C (ζ ^ e i))) = ∏ i : κ, (X - C (ζ ^ (h - e i))) := by
    rw [← hchar_e, ← hchar_conj, hchar_e, Polynomial.map_prod]
    exact Finset.prod_congr rfl fun i _ ↦ by
      rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, hconj_pow i]
  have hroots_eq : Finset.univ.val.map (fun i : κ ↦ ζ ^ e i) =
      Finset.univ.val.map (fun i : κ ↦ ζ ^ (h - e i)) := by
    have hroots (g : κ → ℕ) : (∏ i : κ, (X - C (ζ ^ g i))).roots =
        Finset.univ.val.map (fun i : κ ↦ ζ ^ g i) := by
      rw [Finset.prod_eq_multiset_prod]
      change (Finset.univ.val.map ((fun a : ℂ ↦ X - C a) ∘ fun i ↦ ζ ^ g i)).prod.roots = _
      rw [← Multiset.map_map, Polynomial.roots_multiset_prod_X_sub_C]
    rw [← hroots e, ← hroots (fun i ↦ h - e i), hprod_eq]
  have hcount_pow (g : κ → ℕ) (hg : ∀ i, g i < h) (a : ℕ) (ha : a < h) :
      Multiset.count (ζ ^ a) (Finset.univ.val.map (fun i : κ ↦ ζ ^ g i)) =
        Multiset.count a (Finset.univ.val.map g) := by
    rw [Multiset.count_map, Multiset.count_map]; congr 1; exact Multiset.filter_congr fun i _ ↦
      ⟨fun heq ↦ hζ_prim.pow_inj ha (hg i) heq, fun heq ↦ heq ▸ rfl⟩
  have hdual_e : Finset.univ.val.map e = Finset.univ.val.map (fun i ↦ h - e i) := by
    refine Multiset.ext.2 fun a ↦ ?_
    by_cases ha : a < h
    · rw [← hcount_pow e he_lt a ha, ← hcount_pow (fun i ↦ h - e i) hhe_lt a ha, hroots_eq]
    · have hnot {g : κ → ℕ} (hg : ∀ i, g i < h) : a ∉ Finset.univ.val.map g :=
        fun hmem ↦ by rcases Multiset.mem_map.1 hmem with ⟨i, _, hi⟩; exact ha (hi ▸ hg i)
      rw [Multiset.count_eq_zero.2 (hnot he_lt), Multiset.count_eq_zero.2 (hnot hhe_lt)]
  have h2sum_e : 2 * ∑ i : κ, e i = b.support.card * h := by
    have hadd : ∑ i : κ, e i + ∑ i : κ, (h - e i) = Fintype.card κ * h := by
      rw [← Finset.sum_add_distrib]
      exact (Finset.sum_congr rfl fun i _ ↦ Nat.add_sub_of_le (he_lt i).le).trans (by simp)
    have hsum_eq : ∑ i : κ, (h - e i) = ∑ i : κ, e i := congrArg Multiset.sum hdual_e.symm
    rwa [hsum_eq, ← two_mul, hcard_κ] at hadd
  have hsum_le : ∑ i : κ, e i ≤ ∑ i : κ, (d i - 1) :=
    Finset.sum_le_sum fun i _ ↦ Nat.mod_le (d i - 1) h
  have h2sum_d : 2 * ∑ i : κ, (d i - 1) = Nat.card ι :=
    P.two_mul_sum_sub_one_eq_natCard_of_bijective_aeval_weylGroupRootRep_dual hf hbij
  have hcard_le : Nat.card ι ≤ b.support.card * h :=
    P.natCard_le_card_support_mul_orderOf_wordProd b hl hall
  have hnatCard : Nat.card ι = b.support.card * h := by omega
  have he_eq (i : κ) : e i = d i - 1 := (Finset.sum_eq_sum_iff_of_le
    fun j _ ↦ Nat.mod_le (d j - 1) h).1
    (show ∑ i : κ, e i = ∑ i : κ, (d i - 1) from by omega) i (Finset.mem_univ i)
  have hd_bounds (i : κ) : 2 ≤ d i ∧ d i ≤ h := by
    have h1 := he_pos i; have h2 := he_lt i; rw [he_eq i] at h1 h2; omega
  have hd_lt (i : κ) : d i - 1 < h := by rw [← he_eq i]; exact he_lt i
  have hdual_d : Finset.univ.val.map (fun i ↦ d i - 1) =
      Finset.univ.val.map (fun i ↦ h - (d i - 1)) := by simp_rw [← he_eq]; exact hdual_e
  exact ⟨hnatCard, hd_bounds, hdual_d, hcharpoly, fun {a} ha hcop ↦
    P.exists_degree_sub_one_eq_of_isRegularWeight hf hbij c v uζ huζ_prim hv_reg hv_eig hv_ne
      hd_lt ha hcop⟩

end ComplexSandwich

section BaseChangePackage

variable {ι R M N : Type*} [CommRing R] [IsDomain R] [CharZero R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (P : RootPairing ι R M N) [Finite ι] [P.IsCrystallographic] [P.IsReduced]
  [P.IsRootSystem] [P.IsIrreducible]

private theorem baseChange_complex_package (b : P.Base)
    {l : List b.support} (hl : l.Nodup) (hall : ∀ i, i ∈ l) :
    let PC := rootPairingBaseChange ℂ b.rationalModel b.rationalModel_toLinearMap
    let bC := rootPairingBaseChangeBase ℂ b.rationalModel b.rationalModel_toLinearMap
      b.rationalModelBase
    let eCB : bC.support ≃ b.support :=
      (supportEquivRootPairingBaseChangeBase ℂ b.rationalModel b.rationalModel_toLinearMap
        b.rationalModelBase).trans b.supportEquivRationalModelBase
    let lC : List bC.support := l.map eCB.symm
    let h := orderOf (wordProd P b l)
    Nat.card ι = b.support.card * h ∧
    ∃ (g : Fin (Module.finrank ℂ (b.support → ℂ)) →
        PC.weylGroupRootRep.dual.symmetricAlgebraInvariants)
      (e : Fin (Module.finrank ℂ (b.support → ℂ)) → ℕ),
      (∀ j, (g j : SymmetricAlgebra ℂ (Module.Dual ℂ (b.support → ℂ))) ∈
        homogeneousSubmodule ℂ (Module.Dual ℂ (b.support → ℂ)) (e j)) ∧
      Function.Bijective (MvPolynomial.aeval (R := ℂ) g) ∧
      (∀ j, 2 ≤ e j ∧ e j ≤ h) ∧
      Finset.univ.val.map (fun j ↦ e j - 1) =
        Finset.univ.val.map (fun j ↦ h - (e j - 1)) ∧
      (PC.weylGroupRootRep (wordProd PC bC lC)).charpoly =
        ∏ j, (X - C (Complex.exp (2 * Real.pi * Complex.I / h) ^ (e j - 1))) ∧
      (∀ {a : ℕ}, a < h → a.Coprime h → ∃ j, e j - 1 = a) := by
  let PC := rootPairingBaseChange ℂ b.rationalModel b.rationalModel_toLinearMap
  let bC := rootPairingBaseChangeBase ℂ b.rationalModel b.rationalModel_toLinearMap
    b.rationalModelBase
  let eCB : bC.support ≃ b.support :=
    (supportEquivRootPairingBaseChangeBase ℂ b.rationalModel b.rationalModel_toLinearMap
      b.rationalModelBase).trans b.supportEquivRationalModelBase
  let lC : List bC.support := l.map eCB.symm
  have hlC : lC.Nodup := hl.map eCB.symm.injective
  have hallC : ∀ j : bC.support, j ∈ lC := fun j ↦
    List.mem_map.2 ⟨eCB j, hall (eCB j), eCB.symm_apply_apply j⟩
  obtain ⟨g, hg_ex, hgbij⟩ :=
    PC.exists_bijective_aeval_weylGroupRootRep_dual_of_isRootSystem
  let e : Fin (Module.finrank ℂ (b.support → ℂ)) → ℕ := fun j ↦ (hg_ex j).choose
  have hg : ∀ j, (g j : SymmetricAlgebra ℂ (Module.Dual ℂ (b.support → ℂ))) ∈
      homogeneousSubmodule ℂ (Module.Dual ℂ (b.support → ℂ)) (e j) := fun j ↦
    (hg_ex j).choose_spec.2
  have hpkg := PC.complex_coxeter_exponents_package bC hlC hallC hg hgbij
  have hcard_supp : bC.support.card = b.support.card := by
    rw [← Fintype.card_coe, ← Fintype.card_coe]; exact Fintype.card_congr eCB
  rw [hcard_supp, ← P.orderOf_wordProd_eq_baseChange ℂ b l] at hpkg
  exact ⟨hpkg.1, g, e, hg, hgbij, hpkg.2.1, hpkg.2.2.1, hpkg.2.2.2.1, hpkg.2.2.2.2⟩

end BaseChangePackage

section CoxeterNumber

variable {ι R M N : Type*} [CommRing R] [IsDomain R] [CharZero R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (P : RootPairing ι R M N) [Finite ι] [P.IsCrystallographic] [P.IsReduced]
  [P.IsRootSystem] [P.IsIrreducible]

/-- **Number of roots equals rank times Coxeter number.** -/
theorem natCard_eq_card_support_mul_orderOf_wordProd (b : P.Base)
    {l : List b.support} (hl : l.Nodup) (hall : ∀ i, i ∈ l) :
    Nat.card ι = b.support.card * orderOf (wordProd P b l) :=
  (P.baseChange_complex_package b hl hall).1

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

private theorem exponents_package_over_field (b : P.Base)
    {l : List b.support} (hl : l.Nodup) (hall : ∀ i, i ∈ l)
    {κ : Type*} [Fintype κ]
    {f : κ → P.weylGroupRootRep.dual.symmetricAlgebraInvariants} {d : κ → ℕ}
    (hf : ∀ i, (f i : SymmetricAlgebra K (Module.Dual K M)) ∈
      homogeneousSubmodule K (Module.Dual K M) (d i))
    (hbij : Function.Bijective (MvPolynomial.aeval (R := K) f)) :
    let h := orderOf (wordProd P b l)
    (∀ i, 2 ≤ d i ∧ d i ≤ h) ∧
    Finset.univ.val.map (fun i ↦ d i - 1) = Finset.univ.val.map (fun i ↦ h - (d i - 1)) ∧
    (∀ {a : ℕ}, a < h → a.Coprime h → ∃ i : κ, d i - 1 = a) := by
  have : Module.Finite K M := Module.Finite.of_basis b.toWeightBasis
  obtain ⟨-, g, e, hg, hgbij, hbounds, hdualC, -, hcopC⟩ :=
    P.baseChange_complex_package b hl hall
  have hmult : Finset.univ.val.map d = Finset.univ.val.map e :=
    b.map_univ_eq_of_bijective_aeval_weylGroupRootRep_dual ℂ hf hbij hg hgbij
  refine ⟨fun i ↦ ?_, ?_, fun {a} ha hcop ↦ ?_⟩
  · rcases Multiset.mem_map.1 (hmult ▸ Multiset.mem_map.2 ⟨i, Finset.mem_univ i, rfl⟩)
      with ⟨j, -, hj⟩
    exact hj ▸ hbounds j
  · have h1 := congrArg (Multiset.map (· - 1)) hmult
    have h2 := congrArg (Multiset.map (fun m ↦ orderOf (wordProd P b l) - (m - 1))) hmult
    simp only [Multiset.map_map, Function.comp_def] at h1 h2
    exact h1.trans (hdualC.trans h2.symm)
  · obtain ⟨j, hj⟩ := hcopC ha hcop
    rcases Multiset.mem_map.1 (hmult.symm ▸ Multiset.mem_map.2 ⟨j, Finset.mem_univ j, rfl⟩)
      with ⟨i, -, hi⟩
    exact ⟨i, hi ▸ hj⟩

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
  exact (P.exponents_package_over_field b hl hall hf hbij).1 i

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
      Finset.univ.val.map (fun i ↦ orderOf (wordProd P b l) - (d i - 1)) :=
  (P.exponents_package_over_field b hl hall hf hbij).2.1

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
  exact (P.exponents_package_over_field b hl hall hf hbij).2.2 ha hcop

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

/-- **The Coxeter number is the largest basic invariant degree.** -/
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
  set h : ℕ := orderOf (wordProd P b l)
  have hh_pos : 0 < h := by have := P.two_le_orderOf_wordProd b hl hall; omega
  let PC := rootPairingBaseChange ℂ b.rationalModel b.rationalModel_toLinearMap
  let bC := rootPairingBaseChangeBase ℂ b.rationalModel b.rationalModel_toLinearMap
    b.rationalModelBase
  let eCB : bC.support ≃ b.support :=
    (supportEquivRootPairingBaseChangeBase ℂ b.rationalModel b.rationalModel_toLinearMap
      b.rationalModelBase).trans b.supportEquivRationalModelBase
  let lC : List bC.support := l.map eCB.symm
  obtain ⟨-, g, e, hg, hgbij, -, -, hcharC, -⟩ := P.baseChange_complex_package b hl hall
  set ζC : ℂ := Complex.exp (2 * Real.pi * Complex.I / h)
  have hζC_prim : IsPrimitiveRoot ζC h := Complex.isPrimitiveRoot_exp h hh_pos.ne'
  let p : ℚ[X] := ((l.map (reflMatrix b.cartanMatrix)).prod.map (Int.castRingHom ℚ)).charpoly
  have hpK : p.map (algebraMap ℚ K) = (P.weylGroupRootRep (wordProd P b l)).charpoly :=
    P.charpoly_weylGroupRootRep_wordProd_eq_map_rat b l
  have hpC : p.map (algebraMap ℚ ℂ) = (PC.weylGroupRootRep (wordProd PC bC lC)).charpoly := by
    rw [← PC.charpoly_weylGroupRootRep_wordProd_eq_map_rat bC lC]; congr 1
    rw [show (lC.map (reflMatrix bC.cartanMatrix)).prod =
        Matrix.reindexAlgEquiv ℤ ℤ eCB.symm (l.map (reflMatrix b.cartanMatrix)).prod from
      (show bC.cartanMatrix = b.cartanMatrix.submatrix eCB eCB by ext i j; simp [bC, eCB]) ▸
        Matrix.prod_map_reflMatrix_submatrix b.cartanMatrix eCB l]
    rw [show (Matrix.reindexAlgEquiv ℤ ℤ eCB.symm
        (l.map (reflMatrix b.cartanMatrix)).prod).map (Int.castRingHom ℚ) =
        Matrix.reindexAlgEquiv ℚ ℚ eCB.symm
          ((l.map (reflMatrix b.cartanMatrix)).prod.map (Int.castRingHom ℚ)) by ext i j; simp]
    exact (Matrix.charpoly_reindex eCB.symm _).symm
  have hmult : Finset.univ.val.map d = Finset.univ.val.map e :=
    b.map_univ_eq_of_bijective_aeval_weylGroupRootRep_dual ℂ hf hbij hg hgbij
  have hprodC : p.map (algebraMap ℚ ℂ) = ∏ i : κ, (X - C (ζC ^ (d i - 1))) := by
    rw [hpC, hcharC, Finset.prod_eq_multiset_prod, Finset.prod_eq_multiset_prod]
    have hmap := congrArg (Multiset.map (fun m ↦ X - C (ζC ^ (m - 1)))) hmult
    simp only [Multiset.map_map, Function.comp_def] at hmap
    exact congrArg Multiset.prod hmap.symm
  let F₁ : Polynomial ℚ[X] := p.map Polynomial.C
  let F₂ : Polynomial ℚ[X] := ∏ i : κ, (X - C ((X : ℚ[X]) ^ (d i - 1)))
  have hF₁K : F₁.map (Polynomial.aeval ζ).toRingHom = p.map (algebraMap ℚ K) := by
    rw [show F₁ = p.map Polynomial.C from rfl, Polynomial.map_map]
    congr 1; exact RingHom.ext_rat _ _
  have hF₁C : F₁.map (Polynomial.aeval ζC).toRingHom = p.map (algebraMap ℚ ℂ) := by
    rw [show F₁ = p.map Polynomial.C from rfl, Polynomial.map_map]
    congr 1; exact RingHom.ext_rat _ _
  have hF₂K : F₂.map (Polynomial.aeval ζ).toRingHom =
      ∏ i : κ, (X - C (ζ ^ (d i - 1))) := by simp [F₂, Polynomial.map_prod]
  have hF₂C : F₂.map (Polynomial.aeval ζC).toRingHom =
      ∏ i : κ, (X - C (ζC ^ (d i - 1))) := by simp [F₂, Polynomial.map_prod]
  rw [← hpK, ← hF₁K, ← hF₂K]; ext k
  have hC_k : Polynomial.aeval ζC (F₁.coeff k - F₂.coeff k) = 0 := by
    rw [map_sub]; change (Polynomial.aeval ζC).toRingHom _ - (Polynomial.aeval ζC).toRingHom _ = 0
    rw [← Polynomial.coeff_map, ← Polynomial.coeff_map, hF₁C, hF₂C, hprodC, sub_self]
  obtain ⟨q, hq⟩ : Polynomial.cyclotomic h ℚ ∣ (F₁.coeff k - F₂.coeff k) := by
    rw [Polynomial.cyclotomic_eq_minpoly_rat hζC_prim hh_pos]; exact minpoly.dvd ℚ ζC hC_k
  have hcyc : Polynomial.aeval ζ (Polynomial.cyclotomic h ℚ) = 0 := by
    rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, Polynomial.map_cyclotomic]
    exact hζ.isRoot_cyclotomic hh_pos
  have hK_k : Polynomial.aeval ζ (F₁.coeff k - F₂.coeff k) = 0 := by
    rw [hq, map_mul, hcyc, zero_mul]
  rw [map_sub] at hK_k
  exact (Polynomial.coeff_map _ _).trans
    ((sub_eq_zero.1 hK_k).trans (Polynomial.coeff_map _ _).symm)

end ExponentsAndEigenvalues

end RootPairing
