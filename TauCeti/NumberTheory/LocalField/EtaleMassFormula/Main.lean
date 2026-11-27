/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.Enumerative.Partition.Basic
public import TauCeti.NumberTheory.LocalField.EtaleMassFormula.EtaleAlgebra
public import TauCeti.NumberTheory.LocalField.EtaleMassFormula.SplittingSymbol
public import TauCeti.NumberTheory.LocalField.EtaleMassFormula.Transitive
import Mathlib.Algebra.BigOperators.Fin
import TauCeti.Data.Fintype.Fiber
import TauCeti.Logic.Equiv.Basic
import TauCeti.Topology.Algebra.InfiniteSum.ENNReal

/-!
# Bhargava's mass formulas for étale algebras over a local field

This file proves Bhargava's local mass formulas for étale algebras of degree `n` over a
nonarchimedean local field `K` with residue cardinality `q = Nat.card 𝓀[K]`, in arbitrary
characteristic ([Bhargava 2007, Thm. 1.1, Props. 2.1–2.3, §8]). Masses are summed over labelled
Galois sets `TauCeti.GaloisSet K n` in `ℝ≥0∞`, accommodating infinitely many Galois sets in equal
characteristic. Decomposing a Galois set into transitive invariant blocks via
`TauCeti.GaloisSet.sigma` and `TauCeti.GaloisSet.restrictBlock` reduces the mass for a fixed
splitting symbol to the transitive formula `TauCeti.etaleMass_isTransitive_splittingSymbol`;
summing over symbols with a prescribed ramification partition and then over all partitions yields
`TauCeti.etaleMass_eq`, which `TauCeti.tsum_etaleDiscriminantExponent` transfers to isomorphism
classes of étale `K`-algebras.

## Main results

* `TauCeti.etaleMass_splittingSymbol` ([Bhargava 2007, Prop. 2.1]): for a splitting symbol `σ` of
  degree `n` (pairs `(f, e)` of positive integers with `∑ f * e = n`), the Galois sets of size `n`
  with splitting symbol `σ` have mass `1 / (#Aut(σ) · q ^ splittingSymbolExponent σ)`.
* `TauCeti.etaleMass_ramificationPartition` ([Bhargava 2007, Prop. 2.2]): for a partition `π` of
  `k` into at most `n - k` parts, the Galois sets of size `n` whose splitting symbol has
  ramification partition `π` have mass `q ^ (-k)`. With more than `n - k` parts the mass is `0`
  (`TauCeti.etaleMass_ramificationPartition_eq_zero`), and for `π = ∅` it is the unramified mass
  `1` (`TauCeti.etaleMass_unramified`, [Bhargava 2007, (2.4)]).
* `TauCeti.etaleMass_eq` ([Bhargava 2007, Thm. 1.1 and Prop. 2.3]):
  `M_n(K) = ∑_{k ≤ n} q(k, n - k) · q ^ (-k)`, where `q(k, m)` is the number of partitions of
  `k` into at most `m` parts.
* `TauCeti.tsum_etaleDiscriminantExponent_eq`: the same formula written directly over a family of
  representatives of the `K`-isomorphism classes of étale `K`-algebras of degree `n`.
* `TauCeti.etaleMass_two`, `TauCeti.etaleMass_three` and `TauCeti.etaleMass_four`:
  `M_2(K) = 1 + q⁻¹`, `M_3(K) = 1 + q⁻¹ + q⁻²` and `M_4(K) = 1 + q⁻¹ + 2 q⁻² + q⁻³`, even in
  equal characteristic where there are infinitely many isomorphism classes of extensions.

## References

* M. Bhargava, *Mass formulae for extensions of local fields, and conjectures on the density of
  number field discriminants*, IMRN **2007**, rnm052, Thm. 1.1, Props. 2.1–2.3, §8.
* K. S. Kedlaya, *Mass formulas for local Galois representations*, IMRN **2007**, rnm021.
-/

public section

noncomputable section

open ValuativeRel _root_.MulAction
open scoped ENNReal Nat

namespace TauCeti

section Helpers

private theorem toList_getElem_pos {σ : Multiset (ℕ × ℕ)}
    (hσ : ∀ x ∈ σ, 0 < x.1 ∧ 0 < x.2) (i : Fin σ.toList.length) :
    0 < σ.toList[i].1 ∧ 0 < σ.toList[i].2 :=
  hσ _ (Multiset.mem_toList.1 (List.getElem_mem i.isLt))

private theorem toList_getElem_mul_pos {σ : Multiset (ℕ × ℕ)}
    (hσ : ∀ x ∈ σ, 0 < x.1 ∧ 0 < x.2) (i : Fin σ.toList.length) :
    0 < σ.toList[i].1 * σ.toList[i].2 :=
  Nat.mul_pos (toList_getElem_pos hσ i).1 (toList_getElem_pos hσ i).2

end Helpers

section SplittingSymbolFiber

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] {n : ℕ}

private def splittingBlockTotal (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (n : ℕ) (σ : Multiset (ℕ × ℕ)) :=
  (Fin n ≃ Σ i : Fin σ.toList.length, Fin (σ.toList[i].1 * σ.toList[i].2)) ×
    (∀ i : Fin σ.toList.length,
      {ρᵢ : GaloisSet K (σ.toList[i].1 * σ.toList[i].2) //
        ρᵢ.splittingSymbol = {σ.toList[i]}})

private def splittingBlockMap (n : ℕ) (σ : Multiset (ℕ × ℕ))
    (p : splittingBlockTotal K n σ) :
    {ρ : GaloisSet K n // ρ.splittingSymbol = σ} :=
  ⟨GaloisSet.sigma p.1 (fun i ↦ (p.2 i).val), by
    rw [GaloisSet.splittingSymbol_sigma, Finset.sum_congr rfl fun i _ ↦ (p.2 i).property]
    simp⟩

@[simp]
private theorem coe_splittingBlockMap (n : ℕ) (σ : Multiset (ℕ × ℕ))
    (p : splittingBlockTotal K n σ) :
    (splittingBlockMap n σ p).val = GaloisSet.sigma p.1 (fun i ↦ (p.2 i).val) :=
  rfl

private theorem splittingBlock_hQ_mk {n : ℕ} {σ : Multiset (ℕ × ℕ)}
    (hσ : ∀ x ∈ σ, 0 < x.1 ∧ 0 < x.2)
    (ρ₀ : {ρ : GaloisSet K n // ρ.splittingSymbol = σ})
    {p : splittingBlockTotal K n σ} (hΦ : splittingBlockMap n σ p = ρ₀)
    (i : Fin σ.toList.length) (x : Fin (σ.toList[i].1 * σ.toList[i].2)) :
    let := ρ₀.val.mulAction
    (Quotient.mk'' (p.1.symm ⟨i, x⟩) : orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n)) =
      Quotient.mk'' (p.1.symm ⟨i, ⟨0, toList_getElem_mul_pos hσ i⟩⟩) := by
  let := ρ₀.val.mulAction
  have htrans := GaloisSet.isTransitive_of_splittingSymbol_eq_singleton (p.2 i).property
  obtain ⟨g, hg⟩ := (GaloisSet.isTransitive_iff _).1 htrans
    ⟨0, toList_getElem_mul_pos hσ i⟩ x
  apply Quotient.sound'
  refine ⟨g, ?_⟩
  dsimp only
  rw [GaloisSet.smul_def]
  apply p.1.injective
  rw [p.1.apply_symm_apply, ← congrArg Subtype.val hΦ, coe_splittingBlockMap,
    GaloisSet.sigma_val_apply, p.1.apply_symm_apply, p.1.apply_symm_apply, hg]

private def splittingBlockToE {n : ℕ} {σ : Multiset (ℕ × ℕ)}
    (hσ : ∀ x ∈ σ, 0 < x.1 ∧ 0 < x.2)
    (ρ₀ : {ρ : GaloisSet K n // ρ.splittingSymbol = σ})
    (p : splittingBlockTotal K n σ) (hΦ : splittingBlockMap n σ p = ρ₀) :
    {e : Fin σ.toList.length ≃
        (let := ρ₀.val.mulAction; orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n)) //
        ∀ i, ρ₀.val.orbitSymbol (e i) = σ.toList[i]} :=
  let := ρ₀.val.mulAction
  let x₀ (i : Fin σ.toList.length) : Fin (σ.toList[i].1 * σ.toList[i].2) :=
    ⟨0, toList_getElem_mul_pos hσ i⟩
  let fQ : Fin σ.toList.length → orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n) :=
    fun i ↦ Quotient.mk'' (p.1.symm ⟨i, x₀ i⟩)
  have hfQ : Function.Bijective fQ := by
    refine ⟨fun i₁ i₂ h ↦ ?_, fun O ↦ ?_⟩
    · obtain ⟨g, hg⟩ := Quotient.exact' h
      dsimp only at hg
      rw [GaloisSet.smul_def, ← congrArg Subtype.val hΦ, coe_splittingBlockMap] at hg
      have hb := congrArg (fun j ↦ (p.1 j).1) hg
      simpa only [GaloisSet.sigma_val_apply, p.1.apply_symm_apply] using hb.symm
    · refine ⟨(p.1 O.out).1, ?_⟩
      calc fQ (p.1 O.out).1
          = Quotient.mk'' (p.1.symm ⟨(p.1 O.out).1, (p.1 O.out).2⟩) :=
              (splittingBlock_hQ_mk hσ ρ₀ hΦ _ _).symm
        _ = O := by simp [Sigma.eta]
  ⟨Equiv.ofBijective fQ hfQ, fun i ↦ by
    have hsym := (p.2 i).property
    rw [GaloisSet.splittingSymbol_of_isTransitive _
      (GaloisSet.isTransitive_of_splittingSymbol_eq_singleton hsym) (x₀ i),
      Multiset.singleton_inj] at hsym
    have hstab := GaloisSet.stabilizer_sigma_symm_apply p.1 (fun j ↦ (p.2 j).val) i (x₀ i)
    rw [← coe_splittingBlockMap, congrArg Subtype.val hΦ] at hstab
    dsimp only [Equiv.ofBijective, Equiv.coe_fn_mk, fQ]
    rw [ρ₀.val.orbitSymbol_mk]
    dsimp only at hstab ⊢
    rw [hstab]
    exact hsym⟩

private theorem splittingBlockToE_apply {n : ℕ} {σ : Multiset (ℕ × ℕ)}
    (hσ : ∀ x ∈ σ, 0 < x.1 ∧ 0 < x.2)
    (ρ₀ : {ρ : GaloisSet K n // ρ.splittingSymbol = σ})
    (p : splittingBlockTotal K n σ) (hΦ : splittingBlockMap n σ p = ρ₀)
    (i : Fin σ.toList.length) :
    (let := ρ₀.val.mulAction; (splittingBlockToE hσ ρ₀ p hΦ).val i) =
      (let := ρ₀.val.mulAction;
        Quotient.mk'' (p.1.symm ⟨i, ⟨0, toList_getElem_mul_pos hσ i⟩⟩)) :=
  rfl

private theorem splittingBlock_fib_eq {n : ℕ} {σ : Multiset (ℕ × ℕ)}
    (hσ : ∀ x ∈ σ, 0 < x.1 ∧ 0 < x.2)
    (ρ₀ : {ρ : GaloisSet K n // ρ.splittingSymbol = σ})
    (p : splittingBlockTotal K n σ) (hΦ : splittingBlockMap n σ p = ρ₀) (j : Fin n) :
    (p.1 j).1 = (splittingBlockToE hσ ρ₀ p hΦ).val.symm
      (let := ρ₀.val.mulAction; Quotient.mk'' j) := by
  let := ρ₀.val.mulAction
  refine (Equiv.eq_symm_apply _).2 ?_
  rw [splittingBlockToE_apply]
  calc (Quotient.mk'' (p.1.symm ⟨(p.1 j).1, ⟨0, _⟩⟩) :
          orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n))
      = Quotient.mk'' (p.1.symm ⟨(p.1 j).1, (p.1 j).2⟩) :=
          (splittingBlock_hQ_mk hσ ρ₀ hΦ _ _).symm
    _ = Quotient.mk'' j := by simp [Sigma.eta]

private theorem restrictBlock_eq_of_splittingBlockMap_eq {n : ℕ} {σ : Multiset (ℕ × ℕ)}
    {ρ₀ : {ρ : GaloisSet K n // ρ.splittingSymbol = σ}}
    {p : splittingBlockTotal K n σ} (hΦ : splittingBlockMap n σ p = ρ₀)
    {b' : Fin n ≃ Σ i : Fin σ.toList.length, Fin (σ.toList[i].1 * σ.toList[i].2)}
    (hb' : b' = p.1)
    (hb : ∀ (g : Gal(SeparableClosure K/K)) (j : Fin n), (b' (ρ₀.val.val g j)).1 = (b' j).1)
    (i : Fin σ.toList.length) :
    ρ₀.val.restrictBlock b' hb i = (p.2 i).val := by
  subst hb'
  subst hΦ
  simp

private theorem splittingBlockToE_eq_of_fib {n : ℕ} {σ : Multiset (ℕ × ℕ)}
    (hσ : ∀ x ∈ σ, 0 < x.1 ∧ 0 < x.2)
    (ρ₀ : {ρ : GaloisSet K n // ρ.splittingSymbol = σ})
    (e : {e : Fin σ.toList.length ≃
        (let := ρ₀.val.mulAction; orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n)) //
        ∀ i, ρ₀.val.orbitSymbol (e i) = σ.toList[i]})
    {p : splittingBlockTotal K n σ} {hΦ : splittingBlockMap n σ p = ρ₀}
    (hbp : ∀ j, (p.1 j).1 = e.val.symm (letI := ρ₀.val.mulAction; Quotient.mk'' j)) :
    splittingBlockToE hσ ρ₀ p hΦ = e := by
  let := ρ₀.val.mulAction
  refine Subtype.ext (Equiv.ext fun i ↦ ?_)
  rw [splittingBlockToE_apply]
  exact e.val.symm_apply_eq.1 ((hbp _).symm.trans (by simp))

private theorem sigma_fiberEquivSigma_eq {n : ℕ} {σ : Multiset (ℕ × ℕ)}
    (ρ₀ : {ρ : GaloisSet K n // ρ.splittingSymbol = σ})
    {e' e : {e : Fin σ.toList.length ≃
        (let := ρ₀.val.mulAction; orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n)) //
        ∀ i, ρ₀.val.orbitSymbol (e i) = σ.toList[i]}}
    (he : e' = e)
    (β : ∀ i : Fin σ.toList.length,
      {j : Fin n // e.val.symm (let := ρ₀.val.mulAction; Quotient.mk'' j) = i} ≃
        Fin (σ.toList[i].1 * σ.toList[i].2))
    {b : Fin n ≃ Σ i : Fin σ.toList.length, Fin (σ.toList[i].1 * σ.toList[i].2)}
    (hfib' : ∀ j, (b j).1 = e'.val.symm (letI := ρ₀.val.mulAction; Quotient.mk'' j))
    (hb : b = ((Equiv.fiberEquivSigma
        (fun j ↦ e.val.symm (letI := ρ₀.val.mulAction; Quotient.mk'' j))).symm β).val) :
    (⟨e', Equiv.fiberEquivSigma
        (fun j ↦ e'.val.symm (letI := ρ₀.val.mulAction; Quotient.mk'' j)) ⟨b, hfib'⟩⟩ :
      Σ e : {e : Fin σ.toList.length ≃
          (let := ρ₀.val.mulAction; orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n)) //
          ∀ i, ρ₀.val.orbitSymbol (e i) = σ.toList[i]},
        ∀ i : Fin σ.toList.length,
          {j : Fin n // e.val.symm (let := ρ₀.val.mulAction; Quotient.mk'' j) = i} ≃
            Fin (σ.toList[i].1 * σ.toList[i].2)) = ⟨e, β⟩ := by
  subst he
  subst hb
  exact congrArg (Sigma.mk e')
    ((Equiv.fiberEquivSigma
      (fun j ↦ e'.val.symm (letI := ρ₀.val.mulAction; Quotient.mk'' j))).apply_symm_apply β)

-- A block decomposition `(b, ρᵢ)` of `ρ₀` determines an orbit-symbol-preserving bijection `e`
-- from block indices to orbits of `ρ₀` (`splittingBlockToE`) together with bijections `β i` on
-- each orbit fibre (`Equiv.fiberEquivSigma`); conversely, `(e, β)` reconstructs `b` and restricts
-- `ρ₀` to each block via `GaloisSet.restrictBlock`.
private def splittingBlockFiberEquiv {n : ℕ} {σ : Multiset (ℕ × ℕ)}
    (hσ : ∀ x ∈ σ, 0 < x.1 ∧ 0 < x.2)
    (ρ₀ : {ρ : GaloisSet K n // ρ.splittingSymbol = σ}) :
    {p : splittingBlockTotal K n σ // splittingBlockMap n σ p = ρ₀} ≃
      Σ e : {e : Fin σ.toList.length ≃
          (let := ρ₀.val.mulAction; orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n)) //
          ∀ i, ρ₀.val.orbitSymbol (e i) = σ.toList[i]},
        ∀ i : Fin σ.toList.length,
          {j : Fin n // e.val.symm (let := ρ₀.val.mulAction; Quotient.mk'' j) = i} ≃
            Fin (σ.toList[i].1 * σ.toList[i].2) :=
  letI := ρ₀.val.mulAction
  let d (i : Fin σ.toList.length) : ℕ := σ.toList[i].1 * σ.toList[i].2
  let hd (i : Fin σ.toList.length) : 0 < d i := toList_getElem_mul_pos hσ i
  { toFun := fun ⟨p, hΦ⟩ ↦
      ⟨splittingBlockToE hσ ρ₀ p hΦ,
        Equiv.fiberEquivSigma (fun j ↦ (splittingBlockToE hσ ρ₀ p hΦ).val.symm (Quotient.mk'' j))
          ⟨p.1, splittingBlock_fib_eq hσ ρ₀ p hΦ⟩⟩
    invFun := fun ⟨e, β⟩ ↦
      let ⟨b, hb_fib⟩ := (Equiv.fiberEquivSigma (fun j ↦ e.val.symm (Quotient.mk'' j))).symm β
      have hb : ∀ (g : Gal(SeparableClosure K/K)) (j : Fin n),
          (b (ρ₀.val.val g j)).1 = (b j).1 := fun g j ↦ by
        rw [hb_fib, hb_fib]
        exact congrArg e.val.symm (Quotient.sound' ⟨g, rfl⟩)
      let ρᵢ : ∀ i : Fin σ.toList.length,
          {r : GaloisSet K (d i) // r.splittingSymbol = {σ.toList[i]}} := fun i ↦
        ⟨ρ₀.val.restrictBlock b hb i, by
          have htrans := ρ₀.val.isTransitive_restrictBlock_of_injective b hb e.val.symm
            e.val.symm.injective hb_fib i
          have hq : Quotient.mk'' (b.symm ⟨i, ⟨0, hd i⟩⟩) = e.val i :=
            e.val.symm_apply_eq.1 ((hb_fib _).symm.trans (by simp))
          have hstab := ρ₀.val.stabilizer_restrictBlock b hb i ⟨0, hd i⟩
          rw [(ρ₀.val.restrictBlock b hb i).splittingSymbol_of_isTransitive htrans ⟨0, hd i⟩,
            Multiset.singleton_inj]
          dsimp only at hstab ⊢
          rw [hstab]
          exact (ρ₀.val.orbitSymbol_mk (b.symm ⟨i, ⟨0, hd i⟩⟩)).symm.trans
              (by rw [hq, e.property i])⟩
      ⟨⟨b, ρᵢ⟩, Subtype.ext (ρ₀.val.sigma_restrictBlock b hb)⟩
    left_inv := fun ⟨p, hΦ⟩ ↦ by
      have hleft := congrArg Subtype.val
        ((Equiv.fiberEquivSigma
            (fun j ↦ (splittingBlockToE hσ ρ₀ p hΦ).val.symm (Quotient.mk'' j))).symm_apply_apply
          ⟨p.1, splittingBlock_fib_eq hσ ρ₀ p hΦ⟩)
      exact Subtype.ext (Prod.ext hleft
        (funext fun i ↦ Subtype.ext (restrictBlock_eq_of_splittingBlockMap_eq hΦ hleft _ i)))
    right_inv := fun ⟨e, β⟩ ↦
      sigma_fiberEquivSigma_eq ρ₀
        (splittingBlockToE_eq_of_fib hσ ρ₀ e
          ((Equiv.fiberEquivSigma (fun j ↦ e.val.symm (Quotient.mk'' j))).symm β).property)
        β _ rfl }

private theorem natCard_splittingBlockFiber {n : ℕ} {σ : Multiset (ℕ × ℕ)}
    (hσ : ∀ x ∈ σ, 0 < x.1 ∧ 0 < x.2)
    (ρ₀ : {ρ : GaloisSet K n // ρ.splittingSymbol = σ}) :
    Nat.card {p : splittingBlockTotal K n σ // splittingBlockMap n σ p = ρ₀} =
      (∏ x ∈ σ.toFinset, (σ.count x)!) *
        ∏ i : Fin σ.toList.length, (σ.toList[i].1 * σ.toList[i].2)! := by
  classical
  -- Under `splittingBlockFiberEquiv`, each orbit-matching bijection `e` has `∏ i, (f_i * e_i)!`
  -- fibre labellings, and there are `∏ x, (σ.count x)!` such bijections `e`.
  let := ρ₀.val.mulAction
  let := Fintype.ofFinite (orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n))
  rw [Nat.card_congr (splittingBlockFiberEquiv hσ ρ₀), Nat.card_sigma]
  have hfib_card : ∀ e : {e : Fin σ.toList.length ≃
        orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n) //
        ∀ i, ρ₀.val.orbitSymbol (e i) = σ.toList[i]},
      Nat.card (∀ i : Fin σ.toList.length,
        {j : Fin n // e.val.symm (Quotient.mk'' j) = i} ≃
          Fin (σ.toList[i].1 * σ.toList[i].2)) =
        ∏ i : Fin σ.toList.length, (σ.toList[i].1 * σ.toList[i].2)! := by
    intro e
    rw [Nat.card_eq_fintype_card, Fintype.card_pi]
    refine Finset.prod_congr rfl fun i _ ↦ ?_
    have hc : Fintype.card {j : Fin n // e.val.symm (Quotient.mk'' j) = i} =
        σ.toList[i].1 * σ.toList[i].2 := by
      rw [Fintype.card_congr (Equiv.subtypeEquivRight fun _ ↦ e.val.symm_apply_eq),
        ← Nat.card_eq_fintype_card, ← ρ₀.val.fst_mul_snd_orbitSymbol_eq_card_fiber, e.property i]
    rw [Fintype.card_equiv (Fintype.equivFinOfCardEq hc), hc]
  simp_rw [hfib_card, Finset.sum_const, Finset.card_univ, smul_eq_mul,
    ← Nat.card_eq_fintype_card]
  congr 1
  have hu : (Finset.univ : Finset (Fin σ.toList.length)).val.map (fun i ↦ σ.toList[i]) = σ := by
    simp [Fin.univ_def]
  have ho : (Finset.univ : Finset (orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n))).val.map
      ρ₀.val.orbitSymbol = σ :=
    ρ₀.val.splittingSymbol_eq_map_orbitSymbol.symm.trans ρ₀.property
  exact Nat.card_subtype_equiv_of_map_univ_eq hu ho

end SplittingSymbolFiber

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

private theorem splittingBlockMap_weight_eq_prod {n : ℕ} {σ : Multiset (ℕ × ℕ)}
    (p : splittingBlockTotal K n σ) :
    1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ (splittingBlockMap n σ p).val.discriminantExponent =
      ∏ i : Fin σ.toList.length,
        1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ (p.2 i).val.discriminantExponent := by
  simp only [coe_splittingBlockMap, GaloisSet.discriminantExponent_sigma,
    ← Finset.prod_pow_eq_pow_sum, one_div]
  exact ENNReal.prod_inv_distrib
    (fun _ _ _ _ _ ↦ Or.inr (ENNReal.pow_ne_top (ENNReal.natCast_ne_top _)))

private theorem card_blockEquiv {n : ℕ} {σ : Multiset (ℕ × ℕ)}
    (hn : (σ.map fun x => x.1 * x.2).sum = n) :
    Fintype.card (Fin n ≃ Σ i : Fin σ.toList.length, Fin (σ.toList[i].1 * σ.toList[i].2)) =
      n ! := by
  have hcard_sig :
      Fintype.card (Σ i : Fin σ.toList.length, Fin (σ.toList[i].1 * σ.toList[i].2)) = n := by
    rw [← Multiset.sum_map_toList, ← Fin.sum_univ_fun_getElem] at hn
    simpa [Fintype.card_sigma, Fintype.card_fin] using hn
  rw [Fintype.card_equiv (Fintype.equivFinOfCardEq hcard_sig).symm, Fintype.card_fin]

private theorem tsum_splittingSymbol_singleton_eq {f e : ℕ} (hf : 0 < f) (he : 0 < e) :
    (∑' r : {r : GaloisSet K (f * e) // r.splittingSymbol = {(f, e)}},
        1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ r.val.discriminantExponent) =
      ((f * e)! : ℝ≥0∞) *
        (1 / ((f : ℝ≥0∞) * (Nat.card 𝓀[K] : ℝ≥0∞) ^ (f * (e - 1)))) := by
  rw [← etaleMass_isTransitive_splittingSymbol f e hf he,
    ENNReal.mul_inv_cancel_left (by exact_mod_cast (Nat.factorial_pos _).ne')
      (ENNReal.natCast_ne_top _)]

private theorem tsum_splittingBlockTotal_direct (n : ℕ) (σ : Multiset (ℕ × ℕ))
    (hσ : ∀ x ∈ σ, 0 < x.1 ∧ 0 < x.2) (hn : (σ.map fun x => x.1 * x.2).sum = n) :
    ∑' p : splittingBlockTotal K n σ,
        1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ (splittingBlockMap n σ p).val.discriminantExponent =
      (n ! : ℝ≥0∞) *
        (∏ i : Fin σ.toList.length, ((σ.toList[i].1 * σ.toList[i].2)! : ℝ≥0∞)) *
        (1 / ((σ.map Prod.fst).prod *
          (Nat.card 𝓀[K] : ℝ≥0∞) ^ splittingSymbolExponent σ)) := by
  -- Factor the weight across blocks, sum over the `n!` block bijections and apply Fubini
  -- (`ENNReal.prod_tsum`), then evaluate each block factor by `tsum_splittingSymbol_singleton_eq`.
  simp_rw [splittingBlockMap_weight_eq_prod]
  dsimp only [splittingBlockTotal]
  rw [tsum_prod']
  dsimp only
  rw [tsum_fintype, Finset.sum_const, Finset.card_univ, card_blockEquiv hn, nsmul_eq_mul,
    ← ENNReal.prod_tsum (fun (i : Fin σ.toList.length)
      (r : {ρᵢ : GaloisSet K (σ.toList[i].1 * σ.toList[i].2) //
        ρᵢ.splittingSymbol = {σ.toList[i]}}) ↦
      1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ r.val.discriminantExponent)]
  have hfac : ∀ i : Fin σ.toList.length,
      (∑' r : {r : GaloisSet K (σ.toList[i].1 * σ.toList[i].2) //
          r.splittingSymbol = {σ.toList[i]}},
          1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ r.val.discriminantExponent) =
        ((σ.toList[i].1 * σ.toList[i].2)! : ℝ≥0∞) *
          (1 / ((σ.toList[i].1 : ℝ≥0∞) *
            (Nat.card 𝓀[K] : ℝ≥0∞) ^ (σ.toList[i].1 * (σ.toList[i].2 - 1)))) :=
    fun i ↦ tsum_splittingSymbol_singleton_eq (K := K)
      (toList_getElem_pos hσ i).1 (toList_getElem_pos hσ i).2
  simp_rw [hfac, Finset.prod_mul_distrib]
  rw [← mul_assoc]
  congr 1
  simp only [one_div]
  rw [← ENNReal.prod_inv_distrib
    (fun _ _ _ _ _ ↦ Or.inr (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _)
      (ENNReal.pow_ne_top (ENNReal.natCast_ne_top _))))]
  congr 1
  rw [Finset.prod_mul_distrib, ← Nat.cast_prod, Finset.prod_pow_eq_pow_sum,
    splittingSymbolExponent_def, ← Multiset.sum_map_toList, ← Fin.sum_univ_fun_getElem]
  simp

private theorem tsum_splittingBlockTotal_fiber (n : ℕ) (σ : Multiset (ℕ × ℕ))
    (hσ : ∀ x ∈ σ, 0 < x.1 ∧ 0 < x.2) :
    ∑' p : splittingBlockTotal K n σ,
        1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ (splittingBlockMap n σ p).val.discriminantExponent =
      (∏ x ∈ σ.toFinset, ((σ.count x)! : ℝ≥0∞)) *
        (∏ i : Fin σ.toList.length, ((σ.toList[i].1 * σ.toList[i].2)! : ℝ≥0∞)) *
        ∑' ρ₀ : {ρ : GaloisSet K n // ρ.splittingSymbol = σ},
          1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ ρ₀.val.discriminantExponent := by
  let w : GaloisSet K n → ℝ≥0∞ :=
    fun ρ ↦ 1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ ρ.discriminantExponent
  let Φ := splittingBlockMap (K := K) n σ
  rw [← (Equiv.sigmaFiberEquiv Φ).tsum_eq (fun p ↦ w (Φ p).val), tsum_sigma']
  simp only [Equiv.sigmaFiberEquiv_apply]
  have hconst : ∀ ρ₀ : {ρ : GaloisSet K n // ρ.splittingSymbol = σ},
      (∑' p : {p : splittingBlockTotal K n σ // Φ p = ρ₀}, w (Φ p.val).val) =
        (∏ x ∈ σ.toFinset, ((σ.count x)! : ℝ≥0∞)) *
          (∏ i : Fin σ.toList.length, ((σ.toList[i].1 * σ.toList[i].2)! : ℝ≥0∞)) *
          w ρ₀.val := by
    intro ρ₀
    have hsub :
        ∀ p : {p : splittingBlockTotal K n σ // Φ p = ρ₀}, w (Φ p.val).val = w ρ₀.val :=
      fun p ↦ by rw [p.property]
    simp_rw [hsub]
    let _ : Finite {p : splittingBlockTotal K n σ // Φ p = ρ₀} :=
      Finite.of_injective (splittingBlockFiberEquiv hσ ρ₀) (Equiv.injective _)
    let _ : Fintype {p : splittingBlockTotal K n σ // Φ p = ρ₀} := Fintype.ofFinite _
    rw [tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      ← Nat.card_eq_fintype_card, natCard_splittingBlockFiber hσ ρ₀, Nat.cast_mul,
      Nat.cast_prod, Nat.cast_prod]
  rw [tsum_congr hconst, ENNReal.tsum_mul_left]

/-- **Mass formula for a fixed splitting type** ([Bhargava 2007, Prop. 2.1]): for a splitting
symbol `σ` of degree `n`, the Galois sets of size `n` with splitting symbol `σ` have mass
`1 / (#Aut(σ) · q ^ splittingSymbolExponent σ)`, where `q` is the residue cardinality of `K`. -/
theorem etaleMass_splittingSymbol (n : ℕ) (σ : Multiset (ℕ × ℕ))
    (hσ : ∀ x ∈ σ, 0 < x.1 ∧ 0 < x.2) (hn : (σ.map fun x => x.1 * x.2).sum = n) :
    (n ! : ℝ≥0∞)⁻¹ *
        ∑' ρ : {ρ : GaloisSet K n // ρ.splittingSymbol = σ},
          1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ ρ.val.discriminantExponent =
      1 / ((splittingSymbolAut σ : ℝ≥0∞) *
        (Nat.card 𝓀[K] : ℝ≥0∞) ^ splittingSymbolExponent σ) := by
  -- Double-count `splittingBlockTotal K n σ`: equating `tsum_splittingBlockTotal_fiber` and
  -- `tsum_splittingBlockTotal_direct`, cancel the finite nonzero factor `∏ i, (f_i * e_i)!`, and
  -- divide by `n!` and `∏ x, (σ.count x)!`.
  let w : GaloisSet K n → ℝ≥0∞ :=
    fun ρ ↦ 1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ ρ.discriminantExponent
  have hD_ne0 :
      (∏ i : Fin σ.toList.length, ((σ.toList[i].1 * σ.toList[i].2)! : ℝ≥0∞)) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun i _ ↦ by exact_mod_cast (Nat.factorial_pos _).ne'
  have hD_netop :
      (∏ i : Fin σ.toList.length, ((σ.toList[i].1 * σ.toList[i].2)! : ℝ≥0∞)) ≠ ⊤ :=
    ENNReal.prod_ne_top fun i _ ↦ ENNReal.natCast_ne_top _
  have hC_ne0 : (∏ x ∈ σ.toFinset, ((σ.count x)! : ℝ≥0∞)) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun x _ ↦ by exact_mod_cast (Nat.factorial_pos _).ne'
  have hC_netop : (∏ x ∈ σ.toFinset, ((σ.count x)! : ℝ≥0∞)) ≠ ⊤ :=
    ENNReal.prod_ne_top fun x _ ↦ ENNReal.natCast_ne_top _
  have hn_ne0 : (n ! : ℝ≥0∞) ≠ 0 := by exact_mod_cast (Nat.factorial_pos n).ne'
  have hn_netop : (n ! : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  have heq_cancel :
      (∏ x ∈ σ.toFinset, ((σ.count x)! : ℝ≥0∞)) *
          ∑' ρ₀ : {ρ : GaloisSet K n // ρ.splittingSymbol = σ}, w ρ₀.val =
        (n ! : ℝ≥0∞) *
          (1 / ((σ.map Prod.fst).prod *
            (Nat.card 𝓀[K] : ℝ≥0∞) ^ splittingSymbolExponent σ)) := by
    have h := (tsum_splittingBlockTotal_fiber (K := K) n σ hσ).symm.trans
      (tsum_splittingBlockTotal_direct (K := K) n σ hσ hn)
    rw [mul_comm (∏ x ∈ σ.toFinset, ((σ.count x)! : ℝ≥0∞)), mul_assoc,
      mul_comm (n ! : ℝ≥0∞), mul_assoc] at h
    exact (ENNReal.mul_right_inj hD_ne0 hD_netop).1 h
  have hS :
      (∑' ρ : {ρ : GaloisSet K n // ρ.splittingSymbol = σ}, w ρ.val) =
        (n ! : ℝ≥0∞) * ((∏ x ∈ σ.toFinset, ((σ.count x)! : ℝ≥0∞))⁻¹ *
          (1 / ((σ.map Prod.fst).prod *
            (Nat.card 𝓀[K] : ℝ≥0∞) ^ splittingSymbolExponent σ))) := by
    rw [← mul_left_comm, ← heq_cancel, ENNReal.inv_mul_cancel_left hC_ne0 hC_netop]
  dsimp only [w] at hS
  rw [hS, ENNReal.inv_mul_cancel_left hn_ne0 hn_netop, one_div, one_div,
    ← ENNReal.mul_inv (Or.inl hC_ne0) (Or.inl hC_netop), splittingSymbolAut_def,
    Nat.cast_mul, Nat.cast_prod]
  congr 1
  ring

/-- **Mass formula for a fixed ramification partition** ([Bhargava 2007, Prop. 2.2]): for a
partition `π` of `k` into at most `n - k` parts, the Galois sets of size `n` whose splitting symbol
has ramification partition `π` have mass `q ^ (-k)`, where `q` is the residue cardinality of
`K`. -/
theorem etaleMass_ramificationPartition (n k : ℕ) (π : k.Partition)
    (hπ : Multiset.card π.parts ≤ n - k) :
    (n ! : ℝ≥0∞)⁻¹ *
        ∑' ρ : {ρ : GaloisSet K n // ramificationPartition ρ.splittingSymbol = π.parts},
          1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ ρ.val.discriminantExponent =
      1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ k := by
  -- Group Galois sets with ramification partition `π` by their splitting symbol `σ`, apply
  -- `etaleMass_splittingSymbol` on each fibre, and sum `1 / #Aut(σ)` via `SplittingSymbol.lean`.
  let Sym := {σ : Multiset (ℕ × ℕ) // (∀ x ∈ σ, 0 < x.1 ∧ 0 < x.2) ∧
    (σ.map fun x => x.1 * x.2).sum = n ∧ ramificationPartition σ = π.parts}
  have hsum :
      (∑' ρ : {ρ : GaloisSet K n // ramificationPartition ρ.splittingSymbol = π.parts},
          1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ ρ.val.discriminantExponent) =
        ∑' σ : Sym, ∑' ρ : {ρ : GaloisSet K n // ρ.splittingSymbol = σ.val},
          1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ ρ.val.discriminantExponent := by
    rw [← (Equiv.sigmaSubtypeFiberEquivSubtype GaloisSet.splittingSymbol
      (p := fun ρ : GaloisSet K n ↦ ramificationPartition ρ.splittingSymbol = π.parts)
      (q := fun σ ↦ (∀ x ∈ σ, 0 < x.1 ∧ 0 < x.2) ∧
        (σ.map fun x => x.1 * x.2).sum = n ∧ ramificationPartition σ = π.parts)
      fun ρ ↦ ⟨fun h ↦ ⟨fun _ hx ↦ GaloisSet.pos_of_mem_splittingSymbol hx,
        ρ.sum_map_mul_splittingSymbol, h⟩, fun h ↦ h.2.2⟩).tsum_eq
      (fun ρ ↦ 1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ ρ.val.discriminantExponent), tsum_sigma']
    exact tsum_congr fun _ ↦ tsum_congr fun _ ↦ by
      simp [Equiv.sigmaSubtypeFiberEquivSubtype]
  rw [hsum, ← ENNReal.tsum_mul_left]
  have hterm : ∀ σ : Sym,
      (n ! : ℝ≥0∞)⁻¹ *
          ∑' ρ : {ρ : GaloisSet K n // ρ.splittingSymbol = σ.val},
            1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ ρ.val.discriminantExponent =
        (1 / (splittingSymbolAut σ : ℝ≥0∞)) * (1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ k) := by
    intro σ
    rw [etaleMass_splittingSymbol n σ.val σ.property.1 σ.property.2.1,
      ← sum_ramificationPartition, σ.property.2.2, π.parts_sum]
    have haut0 : (splittingSymbolAut σ.val : ℝ≥0∞) ≠ 0 := by
      exact_mod_cast (splittingSymbolAut_pos fun x hx ↦ (σ.property.1 x hx).1).ne'
    rw [one_div, one_div, one_div,
      ENNReal.mul_inv (Or.inl haut0) (Or.inl (ENNReal.natCast_ne_top _))]
  simp_rw [hterm, ENNReal.tsum_mul_right]
  dsimp only [Sym]
  rw [tsum_one_div_splittingSymbolAut_ramificationPartition n k π hπ, one_mul]

/-- The ramification partition of a Galois set of size `n` is a partition of some `k` into at most
`n - k` parts: its sum and its number of parts add up to at most `n`. -/
theorem GaloisSet.sum_add_card_ramificationPartition_splittingSymbol_le {n : ℕ}
    (ρ : GaloisSet K n) :
    (ramificationPartition ρ.splittingSymbol).sum +
        Multiset.card (ramificationPartition ρ.splittingSymbol) ≤ n :=
  (sum_add_card_ramificationPartition_le _).trans_eq ρ.sum_map_mul_splittingSymbol

/-- **The bound on the number of parts in `etaleMass_ramificationPartition` is necessary**: for a
partition `π` of `k` into more than `n - k` parts, no Galois set of size `n` has ramification
partition `π`, so their mass is `0`. -/
theorem etaleMass_ramificationPartition_eq_zero (n k : ℕ) (π : k.Partition)
    (hπ : n - k < Multiset.card π.parts) :
    (n ! : ℝ≥0∞)⁻¹ *
        ∑' ρ : {ρ : GaloisSet K n // ramificationPartition ρ.splittingSymbol = π.parts},
          1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ ρ.val.discriminantExponent = 0 := by
  have : IsEmpty {ρ : GaloisSet K n // ramificationPartition ρ.splittingSymbol = π.parts} :=
    ⟨fun ρ ↦ by
      have h := ρ.val.sum_add_card_ramificationPartition_splittingSymbol_le
      rw [ρ.property, π.parts_sum] at h
      omega⟩
  rw [tsum_empty, mul_zero]

/-- **The unramified mass** ([Bhargava 2007, (2.4)]): the Galois sets of size `n` all of whose
orbits are unramified, with ramification index `e = 1`, have mass `1`. -/
theorem etaleMass_unramified (n : ℕ) :
    (n ! : ℝ≥0∞)⁻¹ *
        ∑' ρ : {ρ : GaloisSet K n // ∀ x ∈ ρ.splittingSymbol, x.2 = 1},
          1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ ρ.val.discriminantExponent = 1 := by
  have key : ∀ ρ : GaloisSet K n,
      ramificationPartition ρ.splittingSymbol = (default : (0 : ℕ).Partition).parts ↔
        ∀ x ∈ ρ.splittingSymbol, x.2 = 1 := fun ρ ↦ by
    rw [Nat.Partition.partition_zero_parts, ramificationPartition_eq_zero_iff]
    refine forall₂_congr fun x hx ↦ ?_
    have := GaloisSet.pos_of_mem_splittingSymbol hx
    constructor <;> intro h <;> omega
  rw [← (Equiv.subtypeEquivRight key).tsum_eq
    (fun ρ ↦ 1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ ρ.val.discriminantExponent)]
  simpa using etaleMass_ramificationPartition (K := K) n 0 default (by simp)

private theorem partIdx_ext {n : ℕ}
    {p₁ p₂ : Σ k : Finset.range (n + 1),
      {π : k.val.Partition // Multiset.card π.parts ≤ n - k.val}}
    (h : p₁.2.val.parts = p₂.2.val.parts) : p₁ = p₂ := by
  have hk : p₁.1.val = p₂.1.val := by rw [← p₁.2.val.parts_sum, ← p₂.2.val.parts_sum, h]
  rcases p₁ with ⟨⟨k₁, _⟩, ⟨π₁, _⟩⟩
  rcases p₂ with ⟨⟨k₂, _⟩, ⟨π₂, _⟩⟩
  dsimp at hk h
  subst hk
  congr 2
  exact Nat.Partition.ext h

variable (K) in
/-- **Bhargava's mass formula** ([Bhargava 2007, Thm. 1.1, Prop. 2.3, and §8 for an arbitrary
nonarchimedean local field]): `M_n(K) = ∑_{k ≤ n} q(k, n - k) · q ^ (-k)`, where `q` is the
residue cardinality of `K` and `q(k, m)` is the number of partitions of `k` into at most `m`
parts. The term `k = n` is `q(n, 0) = 0` for `n > 0`, so this agrees with `∑_{k < n}`, while at
`n = 0` both sides are `1`. -/
theorem etaleMass_eq (n : ℕ) :
    etaleMass K n =
      ∑ k ∈ Finset.range (n + 1),
        (((Finset.univ : Finset k.Partition).filter fun π =>
            Multiset.card π.parts ≤ n - k).card : ℝ≥0∞) /
          (Nat.card 𝓀[K] : ℝ≥0∞) ^ k := by
  classical
  -- Partition `GaloisSet K n` by `(k, π)` where `π = ramificationPartition ρ.splittingSymbol` has
  -- sum `k ≤ n` and `#π ≤ n - k`, then apply `etaleMass_ramificationPartition` on each fibre.
  let PartIdx := Σ k : Finset.range (n + 1),
    {π : k.val.Partition // Multiset.card π.parts ≤ n - k.val}
  let partOf : GaloisSet K n → PartIdx := fun ρ ↦
    have := ρ.sum_add_card_ramificationPartition_splittingSymbol_le
    have hk_le : (ramificationPartition ρ.splittingSymbol).sum ≤ n := by omega
    have hcard_le : Multiset.card (ramificationPartition ρ.splittingSymbol) ≤
        n - (ramificationPartition ρ.splittingSymbol).sum := by omega
    ⟨⟨(ramificationPartition ρ.splittingSymbol).sum,
        Finset.mem_range.2 (Nat.lt_succ_of_le hk_le)⟩,
      ⟨{ parts := ramificationPartition ρ.splittingSymbol
         parts_pos := fun ht ↦ Nat.pos_of_ne_zero (mem_ramificationPartition.1 ht).1
         parts_sum := rfl }, hcard_le⟩⟩
  let Efib (idx : PartIdx) :
      {ρ : GaloisSet K n // partOf ρ = idx} ≃
        {ρ : GaloisSet K n // ramificationPartition ρ.splittingSymbol = idx.2.val.parts} :=
    { toFun := fun ρ ↦ ⟨ρ.val, congrArg (fun x ↦ x.2.val.parts) ρ.property⟩
      invFun := fun ρ ↦ ⟨ρ.val, partIdx_ext (by simpa [partOf] using ρ.property)⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  rw [etaleMass_def, ← (Equiv.sigmaFiberEquiv partOf).tsum_eq
    (fun ρ ↦ 1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ ρ.discriminantExponent), tsum_sigma',
    ← ENNReal.tsum_mul_left]
  simp only [Equiv.sigmaFiberEquiv_apply]
  have hterm : ∀ idx : PartIdx,
      (n ! : ℝ≥0∞)⁻¹ * ∑' ρ : {ρ : GaloisSet K n // partOf ρ = idx},
          1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ ρ.val.discriminantExponent =
        1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ idx.1.val := by
    intro idx
    have heq := (Efib idx).tsum_eq
      (fun ρ ↦ 1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ ρ.val.discriminantExponent)
    dsimp only [Efib, Equiv.coe_fn_mk] at heq
    rw [heq]
    exact etaleMass_ramificationPartition n idx.1.val idx.2.val idx.2.property
  rw [tsum_congr hterm]
  dsimp only [PartIdx]
  rw [tsum_fintype, Fintype.sum_sigma]
  dsimp only
  simp_rw [Finset.sum_const, Finset.card_univ, Fintype.card_subtype, nsmul_eq_mul, mul_one_div]
  exact Finset.sum_coe_sort (Finset.range (n + 1))
    (fun k ↦ (((Finset.univ : Finset k.Partition).filter fun π ↦
      Multiset.card π.parts ≤ n - k).card : ℝ≥0∞) / (Nat.card 𝓀[K] : ℝ≥0∞) ^ k)

universe u

variable (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] in
/-- **Bhargava's mass formula over étale algebras** ([Bhargava 2007, Thm. 1.1 and §8]): for any
family `A` in the universe of `K` of étale `K`-algebras of degree `n` containing exactly one
member of each `K`-isomorphism class,
`∑ 1 / (#Aut_K(A i) · q ^ d(A i)) = ∑_{k ≤ n} q(k, n - k) · q ^ (-k)`, where `q` is the residue
cardinality of `K`, `d(A i) = etaleDiscriminantExponent K (A i)` is the discriminant exponent, and
`q(k, m)` is the number of partitions of `k` into at most `m` parts. -/
theorem tsum_etaleDiscriminantExponent_eq (n : ℕ) {ι : Type*} (A : ι → Type u)
    [∀ i, CommRing (A i)] [∀ i, Algebra K (A i)] [∀ i, Algebra.Etale K (A i)]
    (hdeg : ∀ i, Module.finrank K (A i) = n)
    (hinj : ∀ i j, Nonempty (A i ≃ₐ[K] A j) → i = j)
    (hsurj : ∀ (B : Type u) [CommRing B] [Algebra K B] [Algebra.Etale K B],
      Module.finrank K B = n → ∃ i, Nonempty (B ≃ₐ[K] A i)) :
    ∑' i, 1 / ((Nat.card (A i ≃ₐ[K] A i) : ℝ≥0∞) *
        (Nat.card 𝓀[K] : ℝ≥0∞) ^ etaleDiscriminantExponent K (A i)) =
      ∑ k ∈ Finset.range (n + 1),
        (((Finset.univ : Finset k.Partition).filter fun π =>
            Multiset.card π.parts ≤ n - k).card : ℝ≥0∞) /
          (Nat.card 𝓀[K] : ℝ≥0∞) ^ k :=
  (tsum_etaleDiscriminantExponent K n A hdeg hinj hsurj).trans (etaleMass_eq K n)

/-! ### Small-degree evaluations -/

variable (K) in
/-- In degree `2`, `M_2(K) = 1 + q⁻¹`. -/
theorem etaleMass_two :
    etaleMass K 2 = 1 + 1 / (Nat.card 𝓀[K] : ℝ≥0∞) := by
  classical
  rw [etaleMass_eq, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
  simp [Finset.univ_unique]

variable (K) in
/-- In degree `3`, `M_3(K) = 1 + q⁻¹ + q⁻²`. -/
theorem etaleMass_three :
    etaleMass K 3 =
      1 + 1 / (Nat.card 𝓀[K] : ℝ≥0∞) + 1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ 2 := by
  classical
  rw [etaleMass_eq, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_one]
  simp [Finset.univ_unique, Finset.filter_eq']

variable (K) in
/-- In degree `4`, `M_4(K) = 1 + q⁻¹ + 2 q⁻² + q⁻³`: the term `q⁻²` counts the two partitions `(2)`
and `(1, 1)` of `2`. -/
theorem etaleMass_four :
    etaleMass K 4 =
      1 + 1 / (Nat.card 𝓀[K] : ℝ≥0∞) + 2 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ 2 +
        1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ 3 := by
  classical
  -- The partitions of `2` are `(2)` and `(1, 1)`, both into at most `4 - 2` parts.
  have hcases (μ : (2 : ℕ).Partition) :
      μ = _root_.Nat.Partition.indiscrete 2 ∨ μ = Nat.Partition.ones 2 := by
    rcases le_or_gt (Multiset.card μ.parts) 1 with h | h
    · exact Or.inl ((Nat.Partition.card_parts_le_one_iff μ).1 h)
    refine Or.inr (_root_.Nat.Partition.ext ?_)
    obtain ⟨a, b, hab⟩ := Multiset.card_eq_two.1 (le_antisymm μ.card_parts_le h)
    have ha := μ.parts_pos (i := a) (by simp [hab])
    have hb := μ.parts_pos (i := b) (by simp [hab])
    have hsum : a + b = 2 := by simpa [hab] using μ.parts_sum
    rw [hab, Nat.Partition.ones_parts, show a = 1 by omega, show b = 1 by omega]
    simp [Multiset.replicate_succ]
  have h2 : ((Finset.univ : Finset (2 : ℕ).Partition).filter fun π ↦
      Multiset.card π.parts ≤ 4 - 2).card = 2 := by
    rw [Finset.filter_true_of_mem fun μ _ ↦ μ.card_parts_le, Finset.card_eq_two]
    refine ⟨_, _, fun h ↦ ?_, (Finset.eq_univ_of_forall fun μ ↦ by simpa using hcases μ).symm⟩
    simpa using congrArg _root_.Nat.Partition.parts h
  rw [etaleMass_eq, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_one, h2]
  simp [Finset.univ_unique, Finset.filter_eq']

end TauCeti
