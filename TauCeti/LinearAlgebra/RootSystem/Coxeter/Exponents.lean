/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.Coxeter.Plane
public import TauCeti.LinearAlgebra.RootSystem.Inversions.Length
public import TauCeti.RepresentationTheory.SymmetricAlgebra.Weyl

import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.LinearAlgebra.Eigenspace.Charpoly
import Mathlib.LinearAlgebra.RootSystem.BaseExists
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.RingTheory.RootsOfUnity.Complex
import TauCeti.LinearAlgebra.RootSystem.Coxeter.Element.ActsBy
import TauCeti.LinearAlgebra.RootSystem.Coxeter.FixedPoints
import TauCeti.RepresentationTheory.SymmetricAlgebra.CoprimeExponents
import TauCeti.RepresentationTheory.SymmetricAlgebra.Degrees

/-!
# Coxeter number, Coxeter eigenvalues, and exponents of Weyl groups

Let `P` be a finite reduced crystallographic root system with base `b` of rank `r = b.support.card`,
and let `c = wordProd P b l` be a Coxeter element of order `h = orderOf c`.

For any root `α`, the sum of the roots in its `⟨c⟩`-orbit is `c`-invariant and thus vanishes
because `c` has no nonzero fixed vector. Consequently every `⟨c⟩`-orbit meets both the positive
and negative roots, so it contains an inversion of `c`. This yields the orbit lower bound
`|Φ| ≤ #(inversions P b c) * h ≤ r * h` with no irreducibility hypothesis. Moreover, `c` has
exactly `r` inversions (it is a reduced word of length `r`).

When `P` is irreducible, combining the complex regular eigenvector for `c` of eigenvalue
`exp (-2πi / h)` (`RootPairing.exists_isRegularWeight_smul_eq_exp_neg_wordProd`) with the
regular-eigenvector Jacobian calculation
(`Representation.charpoly_eq_prod_of_eigenvector_of_jacobian_ne_zero`) identifies the
characteristic polynomial of `c` as `∏ i, (X - ζ ^ (d i - 1))`, where `d i` are the degrees of
any homogeneous system of basic invariants of `P.weylGroupRootRep.dual`. Since `c` acts by an
integer matrix on the simple roots, its characteristic polynomial is defined over `ℚ`, so complex
conjugation pairs the reduced exponents `e i = (d i - 1) % h ∈ {1, …, h - 1}` via `e ↦ h - e`.
Summing gives `r * h = 2 * ∑ e i ≤ 2 * ∑ (d i - 1) = |Φ| ≤ r * h`, forcing equality:

* `|Φ| = r * h` (and `2 * |Φ⁺| = r * h`);
* `e i = d i - 1`, so `2 ≤ d i ≤ h` for every `i`, and the exponents `m i = d i - 1` satisfy the
  duality `m ↦ h - m` as multisets;
* every `a < h` coprime to `h` occurs as an exponent `d i - 1` (in particular, `2` and `h` occur
  as basic invariant degrees);
* over every characteristic-zero field `K` and every primitive `h`-th root of unity `ζ : K`, the
  characteristic polynomial of `c` equals `∏ i, (X - C (ζ ^ (d i - 1)))`.

## Main results

* `RootPairing.natCard_le_ncard_inversions_mul_orderOf_wordProd` and
  `RootPairing.natCard_le_card_support_mul_orderOf_wordProd`: for any finite reduced
  crystallographic root system over a characteristic-zero domain, `|Φ| ≤ #(inversions c) * h` and
  `|Φ| ≤ r * h`.
* `RootPairing.ncard_inversions_wordProd_eq_card_support`: every Coxeter element has exactly `r`
  inversions.
* `RootPairing.natCard_eq_card_support_mul_orderOf_wordProd` and
  `RootPairing.two_mul_ncard_posRoots_eq_card_support_mul_orderOf_wordProd`: for an irreducible
  root system over any characteristic-zero domain, `|Φ| = r * h` and `2 * |Φ⁺| = r * h`.
* `RootPairing.two_le_and_le_orderOf_wordProd_of_bijective_aeval_weylGroupRootRep_dual`: every
  basic invariant degree of an irreducible crystallographic Weyl group satisfies `2 ≤ d i ≤ h`.
* `RootPairing.map_sub_one_eq_map_orderOf_sub_of_bijective_aeval_weylGroupRootRep_dual`: duality
  `m ↦ h - m` of the multiset of exponents `d i - 1`.
* `RootPairing.exists_degree_sub_one_eq_of_coprime_orderOf_wordProd`: crystallographic
  coprime-exponent theorem — every `a < h` coprime to `h` occurs among `d i - 1`.
* `RootPairing.exists_degree_eq_two_of_bijective_aeval_weylGroupRootRep_dual` and
  `RootPairing.exists_degree_eq_orderOf_wordProd_of_bijective_aeval_weylGroupRootRep_dual`:
  `2` and `h` occur among the basic invariant degrees.
* `RootPairing.charpoly_weylGroupRootRep_wordProd_eq_prod`: over any characteristic-zero field `K`
  containing a primitive `h`-th root of unity `ζ`, `(P.weylGroupRootRep c).charpoly` equals
  `∏ i, (X - C (ζ ^ (d i - 1)))`.

## References

* A. J. Coleman, *The Betti numbers of the simple Lie groups*, Canad. J. Math. 10 (1958), 349–356.
* R. Steinberg, *Finite reflection groups*, Trans. Amer. Math. Soc. 91 (1959), 493–504.
* T. A. Springer, *Regular elements of finite reflection groups*, Invent. Math. 25 (1974),
  159–198, §4.
* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4–6*, Ch. V, §6, no. 2.
* J. E. Humphreys, *Reflection Groups and Coxeter Groups*, Cambridge (1990), §§3.16–3.19.
* R. Kane, *Reflection Groups and Invariant Theory*, Springer (2001), §§18–20.
-/

public section

open Matrix Polynomial SymmetricAlgebra TauCeti TauCeti.SymmetricAlgebra

namespace RootPairing

private lemma prod_map_reflMatrix_submatrix {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] (A : Matrix α α ℤ) (e : β ≃ α) (l : List α) :
    ((l.map e.symm).map (reflMatrix (A.submatrix e e))).prod =
      Matrix.reindexAlgEquiv ℤ ℤ e.symm (l.map (reflMatrix A)).prod := by
  rw [map_list_prod, List.map_map, List.map_map]
  congr 1
  refine List.map_congr_left fun j _ ↦ ?_
  ext u v
  simp only [Function.comp_apply, reflMatrix_apply, Matrix.submatrix_apply,
    Matrix.coe_reindexAlgEquiv, Matrix.reindex_apply, _root_.Equiv.symm_symm,
    _root_.Equiv.apply_symm_apply]
  have hiff : u = e.symm j ↔ e u = j :=
    ⟨fun h ↦ by rw [h, e.apply_symm_apply], fun h ↦ by rw [← h, e.symm_apply_apply]⟩
  have hiff2 : u = v ↔ e u = e v := e.injective.eq_iff.symm
  simp only [hiff, hiff2]

section OrbitAndInversions

variable {ι R M N : Type*} [CommRing R] [IsDomain R] [CharZero R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (P : RootPairing ι R M N) [Finite ι] [P.IsCrystallographic] [P.IsReduced] [P.IsRootSystem]

omit [IsDomain R] [CharZero R] [Finite ι] [P.IsCrystallographic] [P.IsReduced]
  [P.IsRootSystem] in
private lemma length_eq_card_support {b : P.Base} {l : List b.support}
    (hl : l.Nodup) (hall : ∀ i, i ∈ l) : l.length = b.support.card := by
  classical
  have htoFinset : l.toFinset = Finset.univ := by
    ext i
    simp [hall]
  rw [← List.toFinset_card_of_nodup hl, htoFinset, Finset.card_univ, Fintype.card_coe]

/-- **Coxeter-orbit inversion bound.** Every `⟨c⟩`-orbit of roots meets the inversion set of a
Coxeter element `c`, so the total number of roots is at most `#(inversions c) * orderOf c`. -/
theorem natCard_le_ncard_inversions_mul_orderOf_wordProd (b : P.Base)
    {l : List b.support} (hl : l.Nodup) (hall : ∀ i, i ∈ l) :
    Nat.card ι ≤ (inversions P b (wordProd P b l)).ncard * orderOf (wordProd P b l) := by
  classical
  have : Finite P.weylGroup := P.finite_weylGroup_of_base b
  set c : P.weylGroup := wordProd P b l
  set h : ℕ := orderOf c
  have hh_pos : 0 < h := orderOf_pos c
  have hc_pow : c ^ h = 1 := pow_orderOf_eq_one c
  set f : Equiv.Perm ι := P.weylGroupToPerm c
  have hf_pow : f ^ h = 1 := by
    simp only [f, ← map_pow, hc_pow, map_one]
  have hf_mod (n : ℕ) : f ^ n = f ^ (n % h) := by
    conv_lhs => rw [← Nat.div_add_mod n h]
    rw [pow_add, pow_mul, hf_pow, one_pow, one_mul]
  -- Every root lies in the `⟨c⟩`-orbit of an inversion of `c`.
  have hsurj : Function.Surjective
      (fun p : (inversions P b c) × Fin h ↦ (f ^ (p.2 : ℕ)) p.1.1) := by
    intro i
    let S : Finset ι := Finset.univ.image fun k : Fin h ↦ (f ^ (k : ℕ)) i
    have hS_ne : S.Nonempty :=
      ⟨i, Finset.mem_image.2 ⟨⟨0, hh_pos⟩, Finset.mem_univ _, by simp⟩⟩
    have hS_img : S.image f = S := by
      refine Finset.eq_of_subset_of_card_le ?_
        (by rw [Finset.card_image_of_injective _ f.injective])
      intro y hy
      rcases Finset.mem_image.1 hy with ⟨x, hx, rfl⟩
      rcases Finset.mem_image.1 hx with ⟨k, -, rfl⟩
      refine Finset.mem_image.2
        ⟨⟨((k : ℕ) + 1) % h, Nat.mod_lt _ hh_pos⟩, Finset.mem_univ _, ?_⟩
      change (f ^ (((k : ℕ) + 1) % h)) i = f ((f ^ (k : ℕ)) i)
      rw [← hf_mod, pow_succ']
      rfl
    have hsum_zero : ∑ j ∈ S, P.root j = 0 := by
      rw [← wordProd_smul_eq_self_iff_eq_zero b hl hall]
      change c • ∑ j ∈ S, P.root j = ∑ j ∈ S, P.root j
      rw [Finset.smul_sum]
      simp_rw [P.weylGroup_apply_root]
      change ∑ j ∈ S, P.root (f j) = ∑ j ∈ S, P.root j
      rw [← Finset.sum_image (g := f) fun _ _ _ _ h ↦ f.injective h, hS_img]
    have hex_neg : ∃ j ∈ S, ¬ b.IsPos j := by
      by_contra hpos
      push Not at hpos
      exact sum_root_ne_zero_of_mem_posRoots P b hS_ne
        (fun j hj ↦ (mem_posRoots P b j).2 (hpos j hj)) hsum_zero
    have hex_pos : ∃ j ∈ S, b.IsPos j := by
      by_contra hneg
      push Not at hneg
      have hpos' : ∀ j ∈ S, P.reflectionPerm j j ∈ posRoots P b := fun j hj ↦
        (mem_posRoots P b _).2 ((isPos_reflectionPerm_self_iff_mem_negRoots P b j).2
          ((mem_negRoots P b j).2 (hneg j hj)))
      have hsum_neg : ∑ j ∈ S, P.root (P.reflectionPerm j j) = 0 := by
        have hroot (j : ι) : P.root (P.reflectionPerm j j) = -P.root j := by
          rw [root_reflectionPerm, reflection_apply_self]
        simp [hroot, hsum_zero]
      exact sum_root_ne_zero_of_mem_posRoots P b hS_ne hpos' hsum_neg
    rcases hex_pos with ⟨j₂, hj₂S, hj₂_pos⟩
    rcases hex_neg with ⟨j₁, hj₁S, hj₁_neg⟩
    rcases Finset.mem_image.1 hj₂S with ⟨a, -, rfl⟩
    rcases Finset.mem_image.1 hj₁S with ⟨b', -, rfl⟩
    have hex_step : ∃ m : ℕ, ¬ b.IsPos ((f ^ m) ((f ^ (a : ℕ)) i)) := by
      refine ⟨(b' : ℕ) + (h - (a : ℕ)), ?_⟩
      change ¬ b.IsPos ((f ^ ((b' : ℕ) + (h - (a : ℕ))) * f ^ (a : ℕ)) i)
      rw [← pow_add, show (b' : ℕ) + (h - (a : ℕ)) + (a : ℕ) = (b' : ℕ) + h by omega,
        pow_add, hf_pow, mul_one]
      exact hj₁_neg
    set m₀ : ℕ := Nat.find hex_step
    have hm₀_spec : ¬ b.IsPos ((f ^ m₀) ((f ^ (a : ℕ)) i)) := Nat.find_spec hex_step
    have hm₀_ne : m₀ ≠ 0 := by
      intro h0
      rw [h0] at hm₀_spec
      exact hm₀_spec hj₂_pos
    set n : ℕ := m₀ - 1
    have hn_succ : n + 1 = m₀ := Nat.sub_add_cancel (Nat.pos_of_ne_zero hm₀_ne)
    have hn_pos : b.IsPos ((f ^ n) ((f ^ (a : ℕ)) i)) := by
      by_contra hneg
      exact Nat.find_min hex_step (by omega) hneg
    have hn_inv : (f ^ n) ((f ^ (a : ℕ)) i) ∈ inversions P b c := by
      rw [mem_inversions]
      refine ⟨hn_pos, ?_⟩
      change ¬ b.IsPos (f ((f ^ n) ((f ^ (a : ℕ)) i)))
      have hstep : f ((f ^ n) ((f ^ (a : ℕ)) i)) = (f ^ m₀) ((f ^ (a : ℕ)) i) := by
        rw [← hn_succ, pow_succ']
        rfl
      rw [hstep]
      exact hm₀_spec
    let k : Fin h := ⟨(h - (n + (a : ℕ)) % h) % h, Nat.mod_lt _ hh_pos⟩
    refine ⟨(⟨(f ^ n) ((f ^ (a : ℕ)) i), hn_inv⟩, k), ?_⟩
    change (f ^ (k : ℕ) * f ^ n * f ^ (a : ℕ)) i = i
    rw [← pow_add, ← pow_add, hf_mod]
    have hmod0 : ((k : ℕ) + n + (a : ℕ)) % h = 0 := by
      have h1 : ((h - (n + (a : ℕ)) % h) % h + (n + (a : ℕ))) % h =
          ((h - (n + (a : ℕ)) % h) + (n + (a : ℕ)) % h) % h := by
        simp only [Nat.add_mod, Nat.mod_mod]
      have h2 : (h - (n + (a : ℕ)) % h) + (n + (a : ℕ)) % h = h :=
        Nat.sub_add_cancel (le_of_lt (Nat.mod_lt _ hh_pos))
      have h3 : (k : ℕ) + n + (a : ℕ) = (h - (n + (a : ℕ)) % h) % h + (n + (a : ℕ)) := by
        simp [k, add_assoc]
      rw [h3, h1, h2, Nat.mod_self]
    rw [hmod0, pow_zero]
    rfl
  calc Nat.card ι
      ≤ Nat.card ((inversions P b c) × Fin h) := Nat.card_le_card_of_surjective _ hsurj
    _ = Nat.card (inversions P b c) * Nat.card (Fin h) := Nat.card_prod _ _
    _ = (inversions P b c).ncard * h := by rw [Nat.card_coe_set_eq, Nat.card_fin]

/-- **Rank times Coxeter order bounds the number of roots.** For any finite reduced
crystallographic root system over a characteristic-zero domain, `|Φ| ≤ r * orderOf c` where `r`
is the rank and `c` is any Coxeter element. -/
theorem natCard_le_card_support_mul_orderOf_wordProd (b : P.Base)
    {l : List b.support} (hl : l.Nodup) (hall : ∀ i, i ∈ l) :
    Nat.card ι ≤ b.support.card * orderOf (wordProd P b l) := by
  have hinv : (inversions P b (wordProd P b l)).ncard ≤ b.support.card := by
    rw [← P.length_eq_card_support hl hall]
    exact ncard_inversions_wordProd_le_length P b l
  exact (P.natCard_le_ncard_inversions_mul_orderOf_wordProd b hl hall).trans
    (Nat.mul_le_mul_right _ hinv)

/-- **Every Coxeter element is a reduced word**: the number of inversions of `wordProd P b l`
equals the rank `b.support.card`. -/
theorem ncard_inversions_wordProd_eq_card_support (b : P.Base)
    {l : List b.support} (hl : l.Nodup) (hall : ∀ i, i ∈ l) :
    (inversions P b (wordProd P b l)).ncard = b.support.card := by
  classical
  have hle : (inversions P b (wordProd P b l)).ncard ≤ b.support.card := by
    rw [← P.length_eq_card_support hl hall]
    exact ncard_inversions_wordProd_le_length P b l
  refine le_antisymm hle ?_
  by_contra hlt
  push Not at hlt
  obtain ⟨l', hl'eq, hl'len⟩ :=
    exists_wordProd_eq_and_length_eq_ncard_inversions P b (wordProd P b l)
  -- Since `l'.length < b.support.card`, some simple reflection is omitted from `l'`.
  have hcard_lt : l'.toFinset.card < (Finset.univ : Finset b.support).card := by
    rw [Finset.card_univ, Fintype.card_coe]
    exact (List.toFinset_card_le l').trans_lt (hl'len.trans_lt hlt)
  obtain ⟨i₀, -, hi₀⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard_lt
  rw [List.mem_toFinset] at hi₀
  -- Transfer the word identity `wordProd P b l' = wordProd P b l` to `b.rationalModel`.
  let Q := b.rationalModel
  let bQ := b.rationalModelBase
  let e : bQ.support ≃ b.support := b.supportEquivRationalModelBase
  have hmat_eq : (l'.map (reflMatrix b.cartanMatrix)).prod =
      (l.map (reflMatrix b.cartanMatrix)).prod := by
    have h1 := b.actsBy_wordProd l'
    rw [hl'eq] at h1
    exact h1.unique (b.actsBy_wordProd l)
  have hC : bQ.cartanMatrix = b.cartanMatrix.submatrix e e := by
    ext j k
    simp [bQ, e]
  have hmap_prod (m : List b.support) :
      ((m.map e.symm).map (reflMatrix bQ.cartanMatrix)).prod =
        Matrix.reindexAlgEquiv ℤ ℤ e.symm (m.map (reflMatrix b.cartanMatrix)).prod := by
    rw [hC]
    exact prod_map_reflMatrix_submatrix b.cartanMatrix e m
  have hQ_eq : wordProd Q bQ (l'.map e.symm) = wordProd Q bQ (l.map e.symm) := by
    have hacts_l := bQ.actsBy_wordProd (l.map e.symm)
    have hacts_l' := bQ.actsBy_wordProd (l'.map e.symm)
    rw [hmap_prod, hmat_eq, ← hmap_prod] at hacts_l'
    have hsimple : ∀ j : bQ.support,
        wordProd Q bQ (l'.map e.symm) • Q.root j = wordProd Q bQ (l.map e.symm) • Q.root j :=
      fun j ↦ (RootPairing.Base.actsBy_iff.1 hacts_l' j).trans
        (RootPairing.Base.actsBy_iff.1 hacts_l j).symm
    refine weylGroup.ext fun x ↦ ?_
    have hspan : x ∈ Submodule.span ℚ (Set.range fun j : bQ.support ↦ Q.root j) := by
      have hrange : (Set.range fun j : bQ.support ↦ Q.root j) = Set.range bQ.toWeightBasis := by
        ext y
        simp [Q, bQ.toWeightBasis_apply]
      rw [hrange, bQ.toWeightBasis.span_eq]
      trivial
    induction hspan using Submodule.span_induction with
    | mem _ h =>
      rcases h with ⟨j, rfl⟩
      exact hsimple j
    | zero => simp
    | add a c _ _ ha hc => simp [smul_add, ha, hc]
    | smul r a _ ha =>
      change (Q.weylGroupRootRep _) (r • a) = (Q.weylGroupRootRep _) (r • a)
      rw [map_smul, map_smul]
      exact congrArg (r • ·) ha
  -- Construct a nonzero fundamental weight fixed by every simple reflection in `l'.map e.symm`.
  let j₀ : bQ.flip.support := ⟨(e.symm i₀ : ι), (e.symm i₀).2⟩
  let x : b.support → ℚ := Q.toPerfPair.symm (bQ.flip.toWeightBasis.dualBasis j₀)
  have hx_coroot (j : bQ.support) : Q.coroot' j x = if (j₀ : ι) = (j : ι) then 1 else 0 := by
    let jf : bQ.flip.support := ⟨j.1, j.2⟩
    have h1 : Q.coroot' j x = Q.toPerfPair x (Q.flip.root jf) := rfl
    rw [h1, LinearEquiv.apply_symm_apply, ← bQ.flip.toWeightBasis_apply jf,
      Module.Basis.dualBasis_apply_self]
    exact if_congr (eq_comm.trans Subtype.ext_iff) rfl rfl
  have hx_ne : x ≠ 0 := by
    intro h0
    have := hx_coroot (e.symm i₀)
    rw [h0, map_zero] at this
    simp [j₀] at this
  have hx_fix : wordProd Q bQ (l'.map e.symm) • x = x := by
    have hmem : ∀ j ∈ l'.map e.symm, Q.coroot' j x = 0 := by
      intro j hj
      rcases List.mem_map.1 hj with ⟨k, hk, rfl⟩
      have hne : (j₀ : ι) ≠ (e.symm k : ι) := fun heq ↦
        hi₀ (e.symm.injective (Subtype.ext heq) ▸ hk)
      simp [hx_coroot, hne]
    have hfix_word : ∀ m : List bQ.support, (∀ j ∈ m, Q.coroot' j x = 0) →
        wordProd Q bQ m • x = x := by
      intro m
      induction m with
      | nil => intro _; simp
      | cons j t ih =>
        intro hm
        rw [wordProd_cons, mul_smul, ih fun k hk ↦ hm k (List.mem_cons_of_mem _ hk),
          weylGroup.ofIdx_smul, Equiv.reflection_smul, reflection_apply, hm j (by simp)]
        simp
    exact hfix_word _ hmem
  rw [hQ_eq] at hx_fix
  have hlQ_nodup : (l.map e.symm).Nodup := hl.map e.symm.injective
  have hlQ_all : ∀ j : bQ.support, j ∈ l.map e.symm := fun j ↦
    List.mem_map.2 ⟨e j, hall (e j), e.symm_apply_apply j⟩
  exact hx_ne ((wordProd_smul_eq_self_iff_eq_zero bQ hlQ_nodup hlQ_all).1 hx_fix)

omit [P.IsReduced] in
/-- Base-changing a crystallographic root system to any characteristic-zero field `S` preserves
the order of every word in the simple reflections. -/
private theorem orderOf_wordProd_eq_baseChange (S : Type*) [Field S] [CharZero S]
    (b : P.Base) (l : List b.support) :
    orderOf (wordProd P b l) =
      orderOf (wordProd (rootPairingBaseChange S b.rationalModel b.rationalModel_toLinearMap)
        (rootPairingBaseChangeBase S b.rationalModel b.rationalModel_toLinearMap
          b.rationalModelBase)
        (l.map ((supportEquivRootPairingBaseChangeBase S b.rationalModel
          b.rationalModel_toLinearMap b.rationalModelBase).trans
          b.supportEquivRationalModelBase).symm)) := by
  classical
  let bS := rootPairingBaseChangeBase S b.rationalModel b.rationalModel_toLinearMap
    b.rationalModelBase
  let e : bS.support ≃ b.support :=
    (supportEquivRootPairingBaseChangeBase S b.rationalModel b.rationalModel_toLinearMap
      b.rationalModelBase).trans b.supportEquivRationalModelBase
  have hC : bS.cartanMatrix = b.cartanMatrix.submatrix e e := by
    ext i j
    simp [bS, e]
  rw [(b.actsBy_wordProd l).orderOf_eq, (bS.actsBy_wordProd (l.map e.symm)).orderOf_eq, hC,
    prod_map_reflMatrix_submatrix]
  exact (orderOf_injective
    (Matrix.reindexAlgEquiv ℤ ℤ e.symm).toRingEquiv.toMulEquiv.toMonoidHom
    (Matrix.reindexAlgEquiv ℤ ℤ e.symm).injective _).symm

end OrbitAndInversions

section ComplexSandwich

/-- On any crystallographic root system over a characteristic-zero field `K`, the matrix of
`wordProd P b l` in the simple-root basis `b.toWeightBasis` is the integer reflection product
cast to `K`, so its characteristic polynomial is the image of a rational polynomial. -/
private theorem charpoly_weylGroupRootRep_wordProd_eq_map_rat
    {ι K M N : Type*} [DecidableEq ι] [Field K] [CharZero K] [AddCommGroup M] [Module K M]
    [Module.Finite K M] [AddCommGroup N] [Module K N] (P : RootPairing ι K M N)
    [Finite ι] [P.IsCrystallographic] [P.IsRootSystem] (b : P.Base) (l : List b.support) :
    (((l.map (reflMatrix b.cartanMatrix)).prod.map (Int.castRingHom ℚ)).charpoly).map
        (algebraMap ℚ K) =
      (P.weylGroupRootRep (wordProd P b l)).charpoly := by
  let W : Matrix b.support b.support ℤ := (l.map (reflMatrix b.cartanMatrix)).prod
  have htoMat : LinearMap.toMatrix b.toWeightBasis b.toWeightBasis
      (P.weylGroupRootRep (wordProd P b l)) = W.map (Int.castRingHom K) := by
    ext k j
    rw [LinearMap.toMatrix_apply, Matrix.map_apply, Int.coe_castRingHom, b.toWeightBasis_apply]
    change b.toWeightBasis.repr (wordProd P b l • P.root j) k = (W k j : K)
    rw [(RootPairing.Base.actsBy_iff.1 (b.actsBy_wordProd l)) j, map_sum, Finset.sum_apply']
    simp only [map_zsmul, ← b.toWeightBasis_apply, b.toWeightBasis.repr_self]
    simp [Finsupp.single_apply, W]
  rw [← LinearMap.charpoly_toMatrix (P.weylGroupRootRep (wordProd P b l)) b.toWeightBasis, htoMat,
    Matrix.charpoly_map, Matrix.charpoly_map, Polynomial.map_map]
  congr 1
  exact RingHom.ext_int _ _

/-- **Complex Steinberg–Coleman–Springer sandwich.** For an irreducible finite reduced
crystallographic root system over `ℂ` and any system of homogeneous basic invariants of degrees
`d`, matching the regular-eigenvector characteristic polynomial against complex conjugation and
the orbit-inversion bound simultaneously establishes `|Φ| = r * h`, `2 ≤ d i ≤ h`, exponent
duality `m ↦ h - m`, the characteristic polynomial formula, and the coprime-exponent property. -/
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
  set c : P.weylGroup := wordProd P b l
  set h : ℕ := orderOf c
  have hh2 : 2 ≤ h := P.two_le_orderOf_wordProd b hl hall
  have hh_pos : 0 < h := by omega
  have hh_ne : h ≠ 0 := hh_pos.ne'
  set ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / h)
  have hζ_prim : IsPrimitiveRoot ζ h := Complex.isPrimitiveRoot_exp h hh_ne
  have hζ_pow : ζ ^ h = 1 := hζ_prim.pow_eq_one
  have hζ_ne : ζ ≠ 0 := Complex.exp_ne_zero _
  let uζ : ℂˣ := Units.mk0 ζ⁻¹ (inv_ne_zero hζ_ne)
  have huζ_inv : (↑(uζ⁻¹) : ℂ) = ζ := by simp [uζ]
  have huζ_prim : IsPrimitiveRoot (uζ : ℂ) h := by
    have hinv : IsPrimitiveRoot (↑(uζ⁻¹) : ℂ) h := by simpa [huζ_inv] using hζ_prim
    simpa using IsPrimitiveRoot.coe_units_iff.mpr (IsPrimitiveRoot.coe_units_iff.mp hinv).inv
  -- Reindex `b.toWeightBasis.dualBasis` to a `κ`-indexed basis of `Module.Dual ℂ M`.
  have hcard_κ : Fintype.card κ = b.support.card := by
    rw [← Nat.card_eq_fintype_card,
      P.weylGroupRootRep.dual.card_eq_finrank_of_bijective_aeval_symmetricAlgebraInvariants hbij,
      Subspace.dual_finrank_eq, Module.finrank_eq_card_basis b.toWeightBasis, Fintype.card_coe]
  let eκ : b.support ≃ κ := Fintype.equivOfCardEq (by rw [Fintype.card_coe, hcard_κ])
  let eDual : Module.Basis κ ℂ (Module.Dual ℂ M) := b.toWeightBasis.dualBasis.reindex eκ
  -- Apply the regular-eigenvector Jacobian theorem to the complex Coxeter eigenvector.
  obtain ⟨v, hv_reg, hv_eig⟩ := P.exists_isRegularWeight_smul_eq_exp_neg_wordProd b hl hall
  have hv_ne : v ≠ 0 := by
    have hsupp_ne : Nonempty b.support := by
      by_contra hne
      rw [not_nonempty_iff] at hne
      exact not_subsingleton M b.toWeightBasis.equivFun.subsingleton
    obtain ⟨i₀⟩ := hsupp_ne
    intro h0
    exact (isRegularWeight_iff P v).1 hv_reg i₀ (by rw [h0, map_zero])
  have hJ : lift (Module.Dual.eval ℂ M v)
      (jacobian eDual (fun i ↦ (f i : SymmetricAlgebra ℂ (Module.Dual ℂ M)))) ≠ 0 :=
    (P.lift_jacobian_ne_zero_iff_isRegularWeight eDual hf hbij v).2 hv_reg
  have hcharpoly : (P.weylGroupRootRep c).charpoly = ∏ i : κ, (X - C (ζ ^ (d i - 1))) := by
    have hprod := P.weylGroupRootRep.charpoly_eq_prod_of_eigenvector_of_jacobian_ne_zero
      eDual d hf (fun i ↦ (f i).2) c v uζ hv_eig hJ
    simpa [huζ_inv] using hprod
  -- Rationality of the characteristic polynomial via the integer matrix on simple roots.
  let p : ℚ[X] := ((l.map (reflMatrix b.cartanMatrix)).prod.map (Int.castRingHom ℚ)).charpoly
  have hp : p.map (algebraMap ℚ ℂ) = (P.weylGroupRootRep c).charpoly :=
    P.charpoly_weylGroupRootRep_wordProd_eq_map_rat b l
  -- Reduce the exponents modulo `h`; `1` is not an eigenvalue, so every `e i` lies in `[1, h)`.
  let e : κ → ℕ := fun i ↦ (d i - 1) % h
  have he_lt (i : κ) : e i < h := Nat.mod_lt _ hh_pos
  have hζ_mod (i : κ) : ζ ^ (d i - 1) = ζ ^ (e i) := by
    conv_lhs => rw [← Nat.div_add_mod (d i - 1) h]
    rw [pow_add, pow_mul, hζ_pow, one_pow, one_mul]
  have he_pos (i : κ) : 1 ≤ e i := by
    by_contra hlt
    have he0 : e i = 0 := by omega
    have hroot1 : (P.weylGroupRootRep c).charpoly.IsRoot 1 := by
      rw [Polynomial.IsRoot, hcharpoly, Polynomial.eval_prod]
      refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
      rw [hζ_mod i, he0, pow_zero]
      simp
    exact not_hasEigenvalue_one_wordProd b hl hall
      ((Module.End.hasEigenvalue_iff_isRoot_charpoly (P.weylGroupRootRep c) 1).2 hroot1)
  have hhe_lt (i : κ) : h - e i < h := by
    have := he_pos i
    omega
  -- Complex conjugation preserves the rational polynomial and sends `ζ ^ e i` to `ζ ^ (h - e i)`.
  have hconj_ζ : starRingEnd ℂ ζ = ζ⁻¹ := by
    change starRingEnd ℂ (Complex.exp (2 * Real.pi * Complex.I / h)) =
      (Complex.exp (2 * Real.pi * Complex.I / h))⁻¹
    rw [← Complex.exp_conj, ← Complex.exp_neg]
    congr 1
    simp only [map_div₀, map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I, map_natCast]
    ring
  have hconj_pow (i : κ) : starRingEnd ℂ (ζ ^ e i) = ζ ^ (h - e i) := by
    rw [map_pow, hconj_ζ]
    refine mul_right_cancel₀ (pow_ne_zero (e i) hζ_ne) ?_
    rw [← mul_pow, inv_mul_cancel₀ hζ_ne, one_pow, ← pow_add,
      Nat.sub_add_cancel (le_of_lt (he_lt i)), hζ_pow]
  have hchar_e : (P.weylGroupRootRep c).charpoly = ∏ i : κ, (X - C (ζ ^ e i)) := by
    rw [hcharpoly]
    exact Finset.prod_congr rfl fun i _ ↦ by rw [hζ_mod i]
  have hchar_conj : (P.weylGroupRootRep c).charpoly.map (starRingEnd ℂ) =
      (P.weylGroupRootRep c).charpoly := by
    rw [← hp, Polynomial.map_map]
    congr 1
    exact RingHom.ext_rat _ _
  have hprod_eq : (∏ i : κ, (X - C (ζ ^ e i))) = ∏ i : κ, (X - C (ζ ^ (h - e i))) := by
    have h1 : (∏ i : κ, (X - C (ζ ^ e i))).map (starRingEnd ℂ) =
        ∏ i : κ, (X - C (ζ ^ (h - e i))) := by
      rw [Polynomial.map_prod]
      refine Finset.prod_congr rfl fun i _ ↦ ?_
      rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, hconj_pow i]
    rw [← h1, ← hchar_e, hchar_conj]
  have hroots_eq :
      Finset.univ.val.map (fun i : κ ↦ ζ ^ e i) =
        Finset.univ.val.map (fun i : κ ↦ ζ ^ (h - e i)) := by
    have hL : (∏ i : κ, (X - C (ζ ^ e i))).roots =
        Finset.univ.val.map (fun i : κ ↦ ζ ^ e i) := by
      rw [Finset.prod_eq_multiset_prod]
      change (Finset.univ.val.map ((fun a : ℂ ↦ X - C a) ∘ fun i ↦ ζ ^ e i)).prod.roots = _
      rw [← Multiset.map_map, Polynomial.roots_multiset_prod_X_sub_C]
    have hR : (∏ i : κ, (X - C (ζ ^ (h - e i)))).roots =
        Finset.univ.val.map (fun i : κ ↦ ζ ^ (h - e i)) := by
      rw [Finset.prod_eq_multiset_prod]
      change (Finset.univ.val.map
        ((fun a : ℂ ↦ X - C a) ∘ fun i ↦ ζ ^ (h - e i))).prod.roots = _
      rw [← Multiset.map_map, Polynomial.roots_multiset_prod_X_sub_C]
    rw [← hL, ← hR, hprod_eq]
  -- Extract multiset duality of `e` using injectivity of `m ↦ ζ ^ m` on `[0, h)`.
  have hcount_pow (g : κ → ℕ) (hg : ∀ i, g i < h) (a : ℕ) (ha : a < h) :
      Multiset.count (ζ ^ a) (Finset.univ.val.map (fun i : κ ↦ ζ ^ g i)) =
        Multiset.count a (Finset.univ.val.map g) := by
    rw [Multiset.count_map, Multiset.count_map]
    congr 1
    refine Multiset.filter_congr fun i _ ↦ ?_
    exact ⟨fun heq ↦ hζ_prim.pow_inj ha (hg i) heq, fun heq ↦ heq ▸ rfl⟩
  have hdual_e : Finset.univ.val.map e = Finset.univ.val.map (fun i ↦ h - e i) := by
    refine Multiset.ext.2 fun a ↦ ?_
    by_cases ha : a < h
    · rw [← hcount_pow e he_lt a ha, ← hcount_pow (fun i ↦ h - e i) hhe_lt a ha, hroots_eq]
    · have h1 : a ∉ Finset.univ.val.map e := by
        simp only [Multiset.mem_map, Finset.mem_val, Finset.mem_univ, true_and, not_exists]
        intro i hi
        exact ha (hi ▸ he_lt i)
      have h2 : a ∉ Finset.univ.val.map (fun i ↦ h - e i) := by
        simp only [Multiset.mem_map, Finset.mem_val, Finset.mem_univ, true_and, not_exists]
        intro i hi
        exact ha (hi ▸ hhe_lt i)
      rw [Multiset.count_eq_zero.2 h1, Multiset.count_eq_zero.2 h2]
  -- Sandwich: `r * h = 2 * ∑ e i ≤ 2 * ∑ (d i - 1) = |Φ| ≤ r * h`.
  have hsum_dual : ∑ i : κ, e i = ∑ i : κ, (h - e i) := congrArg Multiset.sum hdual_e
  have h2sum_e : 2 * ∑ i : κ, e i = b.support.card * h := by
    have hadd : ∑ i : κ, e i + ∑ i : κ, (h - e i) = Fintype.card κ * h := by
      rw [← Finset.sum_add_distrib]
      trans ∑ _i : κ, h
      · refine Finset.sum_congr rfl fun i _ ↦ Nat.add_sub_of_le (le_of_lt (he_lt i))
      · simp
    rw [← hsum_dual, ← two_mul, hcard_κ] at hadd
    exact hadd
  have hsum_le : ∑ i : κ, e i ≤ ∑ i : κ, (d i - 1) :=
    Finset.sum_le_sum fun i _ ↦ Nat.mod_le (d i - 1) h
  have h2sum_d : 2 * ∑ i : κ, (d i - 1) = Nat.card ι :=
    P.two_mul_sum_sub_one_eq_natCard_of_bijective_aeval_weylGroupRootRep_dual hf hbij
  have hcard_le : Nat.card ι ≤ b.support.card * h :=
    P.natCard_le_card_support_mul_orderOf_wordProd b hl hall
  have hnatCard : Nat.card ι = b.support.card * h := by omega
  have hsum_eq : ∑ i : κ, e i = ∑ i : κ, (d i - 1) := by omega
  have he_eq (i : κ) : e i = d i - 1 :=
    (Finset.sum_eq_sum_iff_of_le fun j _ ↦ Nat.mod_le (d j - 1) h).1 hsum_eq i (Finset.mem_univ i)
  have hd_bounds (i : κ) : 2 ≤ d i ∧ d i ≤ h := by
    have h1 := he_pos i
    have h2 := he_lt i
    rw [he_eq i] at h1 h2
    omega
  have hd_lt (i : κ) : d i - 1 < h := by
    rw [← he_eq i]
    exact he_lt i
  have hdual_d : Finset.univ.val.map (fun i ↦ d i - 1) =
      Finset.univ.val.map (fun i ↦ h - (d i - 1)) := by
    have hfun1 : (fun i : κ ↦ d i - 1) = e := funext fun i ↦ (he_eq i).symm
    have hfun2 : (fun i : κ ↦ h - (d i - 1)) = (fun i ↦ h - e i) :=
      funext fun i ↦ by rw [he_eq i]
    rw [hfun1, hfun2, hdual_e]
  refine ⟨hnatCard, hd_bounds, hdual_d, hcharpoly, fun {a} ha hcop ↦ ?_⟩
  exact P.weylGroupRootRep.exists_degree_sub_one_eq_of_eigenvector_of_jacobian_ne_zero
    eDual d hf (fun i ↦ (f i).2) c v uζ huζ_prim hv_eig hv_ne hJ hd_lt hp ha hcop

end ComplexSandwich

section CoxeterNumber

variable {ι R M N : Type*} [CommRing R] [IsDomain R] [CharZero R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (P : RootPairing ι R M N) [Finite ι] [P.IsCrystallographic] [P.IsReduced]
  [P.IsRootSystem] [P.IsIrreducible]

/-- **Number of roots equals rank times Coxeter number.** For any irreducible finite reduced
crystallographic root system over a characteristic-zero domain, `Nat.card ι` equals
`b.support.card * orderOf (wordProd P b l)` for every base `b` and Coxeter element
`wordProd P b l`. -/
theorem natCard_eq_card_support_mul_orderOf_wordProd (b : P.Base)
    {l : List b.support} (hl : l.Nodup) (hall : ∀ i, i ∈ l) :
    Nat.card ι = b.support.card * orderOf (wordProd P b l) := by
  let PC := rootPairingBaseChange ℂ b.rationalModel b.rationalModel_toLinearMap
  let bC := rootPairingBaseChangeBase ℂ b.rationalModel b.rationalModel_toLinearMap
    b.rationalModelBase
  let eCB : bC.support ≃ b.support :=
    (supportEquivRootPairingBaseChangeBase ℂ b.rationalModel b.rationalModel_toLinearMap
      b.rationalModelBase).trans b.supportEquivRationalModelBase
  let lC : List bC.support := l.map eCB.symm
  have hlC : lC.Nodup := hl.map eCB.symm.injective
  have hallC : ∀ i : bC.support, i ∈ lC := fun i ↦
    List.mem_map.2 ⟨eCB i, hall (eCB i), eCB.symm_apply_apply i⟩
  obtain ⟨g, hg_ex, hgbij⟩ :=
    PC.exists_bijective_aeval_symmetricAlgebraInvariants_weylGroupRootRep_dual
  let e : Fin (Module.finrank ℂ (b.support → ℂ)) → ℕ := fun j ↦ (hg_ex j).choose
  have hg : ∀ j, (g j : SymmetricAlgebra ℂ (Module.Dual ℂ (b.support → ℂ))) ∈
      homogeneousSubmodule ℂ (Module.Dual ℂ (b.support → ℂ)) (e j) := fun j ↦
    (hg_ex j).choose_spec.2
  have hpkg := (PC.complex_coxeter_exponents_package bC hlC hallC hg hgbij).1
  have hcard_supp : bC.support.card = b.support.card := by
    rw [← Fintype.card_coe, ← Fintype.card_coe]
    exact Fintype.card_congr eCB
  rw [hcard_supp, ← P.orderOf_wordProd_eq_baseChange ℂ b l] at hpkg
  exact hpkg

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
/-- For an irreducible root system, any index type of basic invariants is automatically finite. -/
private lemma finite_of_bijective_aeval_weylGroupRootRep_dual (b : P.Base) {κ : Type*}
    {f : κ → P.weylGroupRootRep.dual.symmetricAlgebraInvariants}
    (hbij : Function.Bijective (MvPolynomial.aeval (R := K) f)) : Finite κ := by
  have : FiniteDimensional K M := Module.Finite.of_basis b.toWeightBasis
  have : Finite P.weylGroup := P.finite_weylGroup
  have : Nontrivial M := IsIrreducible.nontrivial P
  have hcard : Nat.card κ = Module.finrank K (Module.Dual K M) :=
    P.weylGroupRootRep.dual.card_eq_finrank_of_bijective_aeval_symmetricAlgebraInvariants hbij
  have hpos : 0 < Module.finrank K (Module.Dual K M) := by
    rw [Subspace.dual_finrank_eq]
    exact Module.finrank_pos
  exact Nat.finite_of_card_ne_zero (hcard ▸ hpos.ne')

/-- Transfer the complex degree bounds, exponent duality, and coprime-exponent property to any
characteristic-zero field `K` via `b.rationalModel`. -/
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
    PC.exists_bijective_aeval_symmetricAlgebraInvariants_weylGroupRootRep_dual
  let e : Fin (Module.finrank ℂ (b.support → ℂ)) → ℕ := fun j ↦ (hg_ex j).choose
  have hg : ∀ j, (g j : SymmetricAlgebra ℂ (Module.Dual ℂ (b.support → ℂ))) ∈
      homogeneousSubmodule ℂ (Module.Dual ℂ (b.support → ℂ)) (e j) := fun j ↦
    (hg_ex j).choose_spec.2
  have hord : orderOf (wordProd P b l) = orderOf (wordProd PC bC lC) :=
    P.orderOf_wordProd_eq_baseChange ℂ b l
  have hmult : Finset.univ.val.map d = Finset.univ.val.map e :=
    b.map_univ_eq_of_bijective_aeval_weylGroupRootRep_dual ℂ hf hbij hg hgbij
  have hpkg := PC.complex_coxeter_exponents_package bC hlC hallC hg hgbij
  refine ⟨fun i ↦ ?_, ?_, fun {a} ha hcop ↦ ?_⟩
  · have hmem : d i ∈ Finset.univ.val.map e := by
      rw [← hmult]
      exact Multiset.mem_map.2 ⟨i, Finset.mem_univ i, rfl⟩
    rcases Multiset.mem_map.1 hmem with ⟨j, -, hj⟩
    have hbounds := hpkg.2.1 j
    rwa [hj, ← hord] at hbounds
  · have hdualC := hpkg.2.2.1
    rw [← hord] at hdualC
    calc Finset.univ.val.map (fun i ↦ d i - 1)
        = (Finset.univ.val.map d).map (· - 1) := by rw [Multiset.map_map]; rfl
      _ = (Finset.univ.val.map e).map (· - 1) := by rw [hmult]
      _ = Finset.univ.val.map (fun j ↦ e j - 1) := by rw [Multiset.map_map]; rfl
      _ = Finset.univ.val.map (fun j ↦ orderOf (wordProd P b l) - (e j - 1)) := hdualC
      _ = (Finset.univ.val.map e).map (fun m ↦ orderOf (wordProd P b l) - (m - 1)) := by
            rw [Multiset.map_map]; rfl
      _ = (Finset.univ.val.map d).map (fun m ↦ orderOf (wordProd P b l) - (m - 1)) := by
            rw [hmult]
      _ = Finset.univ.val.map (fun i ↦ orderOf (wordProd P b l) - (d i - 1)) := by
            rw [Multiset.map_map]; rfl
  · obtain ⟨j, hj⟩ := hpkg.2.2.2.2 (hord ▸ ha) (hord ▸ hcop)
    have hmem : e j ∈ Finset.univ.val.map d := by
      rw [hmult]
      exact Multiset.mem_map.2 ⟨j, Finset.mem_univ j, rfl⟩
    rcases Multiset.mem_map.1 hmem with ⟨i, -, hi⟩
    exact ⟨i, by rw [hi, hj]⟩

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

/-- **Crystallographic coprime-exponent theorem.** For any irreducible finite reduced
crystallographic root system over a characteristic-zero field, every natural number `a` less than
and coprime to the Coxeter number `h = orderOf (wordProd P b l)` occurs as an exponent `d i - 1`
of any system of homogeneous basic invariants. -/
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

/-- **Existence of a quadratic basic invariant.** Every irreducible finite reduced crystallographic
Weyl group has a basic invariant of degree `2`. -/
theorem exists_degree_eq_two_of_bijective_aeval_weylGroupRootRep_dual
    {κ : Type*}
    {f : κ → P.weylGroupRootRep.dual.symmetricAlgebraInvariants} {d : κ → ℕ}
    (hf : ∀ i, (f i : SymmetricAlgebra K (Module.Dual K M)) ∈
      homogeneousSubmodule K (Module.Dual K M) (d i))
    (hbij : Function.Bijective (MvPolynomial.aeval (R := K) f)) :
    ∃ i : κ, d i = 2 := by
  obtain ⟨b⟩ := P.nonempty_base
  have : Nontrivial M := IsIrreducible.nontrivial P
  let l : List b.support := (Finset.univ : Finset b.support).toList
  have hl : l.Nodup := Finset.nodup_toList _
  have hall : ∀ j : b.support, j ∈ l := fun j ↦ by simp [l]
  have hh2 : 2 ≤ orderOf (wordProd P b l) := P.two_le_orderOf_wordProd b hl hall
  obtain ⟨i, hi⟩ := P.exists_degree_sub_one_eq_of_coprime_orderOf_wordProd b hl hall hf hbij
    (a := 1) (by omega) (Nat.coprime_one_left _)
  exact ⟨i, by omega⟩

/-- **The Coxeter number is the largest basic invariant degree.** Every irreducible finite reduced
crystallographic Weyl group has a basic invariant of degree `orderOf (wordProd P b l)`. -/
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
  have hh2 : 2 ≤ h := P.two_le_orderOf_wordProd b hl hall
  have hh_pos : 0 < h := by omega
  -- Transfer to `PC` over `ℂ`, where the charpoly splits at `ζC = exp (2πi / h)`.
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
    PC.exists_bijective_aeval_symmetricAlgebraInvariants_weylGroupRootRep_dual
  let e : Fin (Module.finrank ℂ (b.support → ℂ)) → ℕ := fun j ↦ (hg_ex j).choose
  have hg : ∀ j, (g j : SymmetricAlgebra ℂ (Module.Dual ℂ (b.support → ℂ))) ∈
      homogeneousSubmodule ℂ (Module.Dual ℂ (b.support → ℂ)) (e j) := fun j ↦
    (hg_ex j).choose_spec.2
  have hord : h = orderOf (wordProd PC bC lC) := P.orderOf_wordProd_eq_baseChange ℂ b l
  set ζC : ℂ := Complex.exp (2 * Real.pi * Complex.I / h)
  have hζC_prim : IsPrimitiveRoot ζC h := Complex.isPrimitiveRoot_exp h hh_pos.ne'
  have hcharC : (PC.weylGroupRootRep (wordProd PC bC lC)).charpoly =
      ∏ j, (X - C (ζC ^ (e j - 1))) := by
    simpa [ζC, hord] using (PC.complex_coxeter_exponents_package bC hlC hallC hg hgbij).2.2.2.1
  -- Both `P` and `PC` share the same rational characteristic polynomial `p : ℚ[X]`.
  let p : ℚ[X] := ((l.map (reflMatrix b.cartanMatrix)).prod.map (Int.castRingHom ℚ)).charpoly
  have hpK : p.map (algebraMap ℚ K) = (P.weylGroupRootRep (wordProd P b l)).charpoly :=
    P.charpoly_weylGroupRootRep_wordProd_eq_map_rat b l
  have hpC : p.map (algebraMap ℚ ℂ) = (PC.weylGroupRootRep (wordProd PC bC lC)).charpoly := by
    rw [← PC.charpoly_weylGroupRootRep_wordProd_eq_map_rat bC lC]
    congr 1
    have hC : bC.cartanMatrix = b.cartanMatrix.submatrix eCB eCB := by
      ext i j
      simp [bC, eCB]
    have hprod : (lC.map (reflMatrix bC.cartanMatrix)).prod =
        Matrix.reindexAlgEquiv ℤ ℤ eCB.symm (l.map (reflMatrix b.cartanMatrix)).prod := by
      rw [hC]
      exact prod_map_reflMatrix_submatrix b.cartanMatrix eCB l
    rw [hprod]
    have hmat_map : (Matrix.reindexAlgEquiv ℤ ℤ eCB.symm
        (l.map (reflMatrix b.cartanMatrix)).prod).map (Int.castRingHom ℚ) =
        Matrix.reindexAlgEquiv ℚ ℚ eCB.symm
          ((l.map (reflMatrix b.cartanMatrix)).prod.map (Int.castRingHom ℚ)) := by
      ext i j
      simp
    rw [hmat_map]
    exact (Matrix.charpoly_reindex eCB.symm _).symm
  -- Rewrite the `ℂ` product in terms of `d` using the multiset equality `map d = map e`.
  have hmult : Finset.univ.val.map d = Finset.univ.val.map e :=
    b.map_univ_eq_of_bijective_aeval_weylGroupRootRep_dual ℂ hf hbij hg hgbij
  have hprodC : p.map (algebraMap ℚ ℂ) = ∏ i : κ, (X - C (ζC ^ (d i - 1))) := by
    rw [hpC, hcharC, Finset.prod_eq_multiset_prod, Finset.prod_eq_multiset_prod]
    have h1 : Finset.univ.val.map (fun j ↦ X - C (ζC ^ (e j - 1))) =
        (Finset.univ.val.map e).map (fun m ↦ X - C (ζC ^ (m - 1))) := by
      rw [Multiset.map_map]; rfl
    have h2 : Finset.univ.val.map (fun i : κ ↦ X - C (ζC ^ (d i - 1))) =
        (Finset.univ.val.map d).map (fun m ↦ X - C (ζC ^ (m - 1))) := by
      rw [Multiset.map_map]; rfl
    rw [h1, h2, hmult]
  -- Descend from `ζC : ℂ` to `ζ : K` via the common minimal polynomial `cyclotomic h ℚ`.
  let F₁ : Polynomial ℚ[X] := p.map Polynomial.C
  let F₂ : Polynomial ℚ[X] := ∏ i : κ, (X - C ((X : ℚ[X]) ^ (d i - 1)))
  have hmap_F₁_K : F₁.map (Polynomial.aeval ζ).toRingHom = p.map (algebraMap ℚ K) := by
    rw [show F₁ = p.map Polynomial.C from rfl, Polynomial.map_map]
    congr 1
    exact RingHom.ext_rat _ _
  have hmap_F₁_C : F₁.map (Polynomial.aeval ζC).toRingHom = p.map (algebraMap ℚ ℂ) := by
    rw [show F₁ = p.map Polynomial.C from rfl, Polynomial.map_map]
    congr 1
    exact RingHom.ext_rat _ _
  have hmap_F₂_K :
      F₂.map (Polynomial.aeval ζ).toRingHom = ∏ i : κ, (X - C (ζ ^ (d i - 1))) := by
    simp [F₂, Polynomial.map_prod]
  have hmap_F₂_C :
      F₂.map (Polynomial.aeval ζC).toRingHom = ∏ i : κ, (X - C (ζC ^ (d i - 1))) := by
    simp [F₂, Polynomial.map_prod]
  rw [← hpK, ← hmap_F₁_K, ← hmap_F₂_K]
  ext k
  rw [Polynomial.coeff_map (Polynomial.aeval ζ).toRingHom,
    Polynomial.coeff_map (Polynomial.aeval ζ).toRingHom]
  have hC_k : Polynomial.aeval ζC (F₁.coeff k - F₂.coeff k) = 0 := by
    rw [map_sub]
    have h1 : Polynomial.aeval ζC (F₁.coeff k) =
        (F₁.map (Polynomial.aeval ζC).toRingHom).coeff k :=
      (Polynomial.coeff_map (Polynomial.aeval ζC).toRingHom k).symm
    have h2 : Polynomial.aeval ζC (F₂.coeff k) =
        (F₂.map (Polynomial.aeval ζC).toRingHom).coeff k :=
      (Polynomial.coeff_map (Polynomial.aeval ζC).toRingHom k).symm
    rw [h1, h2, hmap_F₁_C, hmap_F₂_C, hprodC, sub_self]
  have hdvd : Polynomial.cyclotomic h ℚ ∣ (F₁.coeff k - F₂.coeff k) := by
    rw [Polynomial.cyclotomic_eq_minpoly_rat hζC_prim hh_pos]
    exact minpoly.dvd ℚ ζC hC_k
  rcases hdvd with ⟨q, hq⟩
  have hcyc : Polynomial.aeval ζ (Polynomial.cyclotomic h ℚ) = 0 := by
    rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, Polynomial.map_cyclotomic]
    exact hζ.isRoot_cyclotomic hh_pos
  have hK_k : Polynomial.aeval ζ (F₁.coeff k - F₂.coeff k) = 0 := by
    rw [hq, map_mul, hcyc, zero_mul]
  rw [map_sub] at hK_k
  exact sub_eq_zero.1 hK_k

end ExponentsAndEigenvalues

end RootPairing
