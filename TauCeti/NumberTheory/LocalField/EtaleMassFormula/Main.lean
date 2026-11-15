/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.Enumerative.Partition.Basic
public import TauCeti.NumberTheory.LocalField.EtaleMassFormula.EtaleAlgebra
public import TauCeti.NumberTheory.LocalField.EtaleMassFormula.Transitive
import TauCeti.Data.Fin.Basic
import TauCeti.Data.Fintype.Fiber
import TauCeti.Data.Multiset.Fintype
import TauCeti.FieldTheory.Galois.FixedField
import TauCeti.Logic.Equiv.Basic
import TauCeti.Topology.Algebra.InfiniteSum.ENNReal

/-!
# Bhargava's mass formulas for étale algebras over a local field

This file proves Bhargava's local mass formulas for étale algebras of degree `n` over a
nonarchimedean local field `K`, in arbitrary characteristic
([Bhargava 2007, Thm. 1.1, Props. 2.1–2.3, §8]):

* `TauCeti.etaleMass_splittingSymbol` ([Bhargava 2007, Prop. 2.1]): the Galois sets of size `n`
  with splitting symbol `σ` have mass `1 / (#Aut(σ) · q ^ splittingSymbolExponent σ)`.
* `TauCeti.etaleMass_ramificationPartition` ([Bhargava 2007, Prop. 2.2]): for a partition `π` of
  `k` into at most `n - k` parts, the Galois sets of size `n` whose splitting symbol has
  ramification partition `π` have mass `q ^ (-k)`.
* `TauCeti.etaleMass_eq` ([Bhargava 2007, Thm. 1.1 and Prop. 2.3]):
  `M_n(K) = ∑_{k ≤ n} q(k, n - k) · q ^ (-k)`, where `q(k, m)` is the number of partitions of
  `k` into at most `m` parts.
* `TauCeti.tsum_etaleDiscriminantExponent_eq`: the same formula written directly over a set of
  representatives of the `K`-isomorphism classes of étale `K`-algebras of degree `n`.

## References

* M. Bhargava, *Mass formulae for extensions of local fields, and conjectures on the density of
  number field discriminants*, IMRN **2007**, rnm052, Thm. 1.1, Props. 2.1–2.3, §8.
-/

public section

noncomputable section

open ValuativeRel _root_.MulAction
open scoped ENNReal Nat

namespace TauCeti

section Helpers

private theorem b_symm_cast {n m : ℕ} {d : Fin m → ℕ} (b : Fin n ≃ Σ i, Fin (d i))
    {i : Fin m} (j : Fin n) (h : (b j).1 = i) :
    b.symm ⟨i, (b j).2.cast (congrArg d h)⟩ = j := by
  rw [Fin.sigma_mk_cast h, b.symm_apply_apply]

private theorem sigma_fiber_ext {α β : Type*} {m : ℕ} {d : Fin m → ℕ} {p : β → α}
    {P : (Fin m ≃ α) → Prop} {e₁ e₂ : {e : Fin m ≃ α // P e}}
    {f₁ : ∀ i, {j : β // p j = e₁.1 i} ≃ Fin (d i)}
    {f₂ : ∀ i, {j : β // p j = e₂.1 i} ≃ Fin (d i)}
    (he : e₁ = e₂) (hf : ∀ i j h₁ h₂, f₁ i ⟨j, h₁⟩ = f₂ i ⟨j, h₂⟩) :
    (⟨e₁, f₁⟩ :
        Σ e : {e : Fin m ≃ α // P e}, ∀ i, {j : β // p j = e.1 i} ≃ Fin (d i)) =
      ⟨e₂, f₂⟩ := by
  cases he
  congr 1
  funext i
  exact Equiv.ext fun ⟨j, h⟩ ↦ hf i j h h

private theorem toList_getElem_pos {σ : Multiset (ℕ × ℕ)}
    (hσ : ∀ x ∈ σ, 0 < x.1 ∧ 0 < x.2) (i : Fin σ.toList.length) :
    0 < σ.toList[i].1 ∧ 0 < σ.toList[i].2 :=
  hσ _ (Multiset.mem_toList.1 (List.getElem_mem i.isLt))

private theorem toList_getElem_mul_pos {σ : Multiset (ℕ × ℕ)}
    (hσ : ∀ x ∈ σ, 0 < x.1 ∧ 0 < x.2) (i : Fin σ.toList.length) :
    0 < σ.toList[i].1 * σ.toList[i].2 :=
  Nat.mul_pos (toList_getElem_pos hσ i).1 (toList_getElem_pos hσ i).2

private theorem ennreal_eq_mul_of_inv_mul_eq {a x y : ℝ≥0∞} (ha0 : a ≠ 0) (hat : a ≠ ⊤)
    (h : a⁻¹ * x = y) : x = a * y := by
  rw [← h, ← mul_assoc, ENNReal.mul_inv_cancel ha0 hat, one_mul]

private theorem ennreal_inv_mul_eq_of_eq_mul {a x y : ℝ≥0∞} (ha0 : a ≠ 0) (hat : a ≠ ⊤)
    (h : x = a * y) : a⁻¹ * x = y := by
  rw [h, ← mul_assoc, ENNReal.inv_mul_cancel ha0 hat, one_mul]

end Helpers

section SplittingSymbolFiber

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] {n : ℕ}

private def orbitSymbol (ρ : GaloisSet K n)
    (O : let := ρ.mulAction; orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n)) : ℕ × ℕ :=
  let := ρ.mulAction
  let F := IntermediateField.fixedField (stabilizer Gal(SeparableClosure K/K) O.out)
  (F.inertiaDegree, Module.finrank K F / F.inertiaDegree)

private theorem orbitSymbol_mk (ρ : GaloisSet K n) (j : Fin n) :
    let := ρ.mulAction
    orbitSymbol ρ (Quotient.mk'' j) =
      let F := IntermediateField.fixedField (stabilizer Gal(SeparableClosure K/K) j)
      (F.inertiaDegree, Module.finrank K F / F.inertiaDegree) := by
  let := ρ.mulAction
  dsimp only [orbitSymbol]
  have hj : (Quotient.mk'' j : orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n)) =
      Quotient.mk'' j := rfl
  rw [inertiaDegree_fixedField_stabilizer_out K hj, finrank_fixedField_stabilizer_out K hj]

private theorem natCard_fiber_orbit_eq (ρ : GaloisSet K n)
    (O : let := ρ.mulAction; orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n)) :
    let := ρ.mulAction
    Nat.card {j : Fin n // (Quotient.mk'' j :
        orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n)) = O} =
      (orbitSymbol ρ O).1 * (orbitSymbol ρ O).2 := by
  let := ρ.mulAction
  dsimp only
  have : FiniteDimensional K (IntermediateField.fixedField
      (stabilizer Gal(SeparableClosure K/K) O.out)) :=
    ρ.finiteDimensional_fixedField_stabilizer O.out
  rw [← ρ.finrank_fixedField_stabilizer_eq_card_fiber O]
  exact (Nat.mul_div_cancel' (IntermediateField.inertiaDegree_dvd_finrank _)).symm

private def restrictBlock {m : ℕ} {d : Fin m → ℕ} (ρ₀ : GaloisSet K n)
    (b : Fin n ≃ Σ i : Fin m, Fin (d i))
    (hb : ∀ (σ : Gal(SeparableClosure K/K)) (j : Fin n), (b (ρ₀.val σ j)).1 = (b j).1)
    (i : Fin m) : GaloisSet K (d i) where
  val :=
    { toFun := fun σ ↦
        { toFun := fun x ↦
            (b (ρ₀.val σ (b.symm ⟨i, x⟩))).2.cast
              (congrArg d ((hb σ (b.symm ⟨i, x⟩)).trans (by simp)))
          invFun := fun x ↦
            (b (ρ₀.val σ⁻¹ (b.symm ⟨i, x⟩))).2.cast
              (congrArg d ((hb σ⁻¹ (b.symm ⟨i, x⟩)).trans (by simp)))
          left_inv := fun x ↦ by
            apply Fin.ext
            simp only [Fin.val_cast]
            rw [b_symm_cast b _ ((hb σ (b.symm ⟨i, x⟩)).trans (by simp)),
              ← Equiv.Perm.mul_apply, ← map_mul, inv_mul_cancel, map_one,
              Equiv.Perm.one_apply, b.apply_symm_apply]
          right_inv := fun x ↦ by
            apply Fin.ext
            simp only [Fin.val_cast]
            rw [b_symm_cast b _ ((hb σ⁻¹ (b.symm ⟨i, x⟩)).trans (by simp)),
              ← Equiv.Perm.mul_apply, ← map_mul, mul_inv_cancel, map_one,
              Equiv.Perm.one_apply, b.apply_symm_apply] }
      map_one' := Equiv.ext fun x ↦ Fin.ext <| by
        simp only [Equiv.coe_fn_mk, Equiv.Perm.coe_one, id_eq, Fin.val_cast]
        rw [MonoidHom.map_one, Equiv.Perm.one_apply, b.apply_symm_apply]
      map_mul' := fun σ τ ↦ Equiv.ext fun x ↦ Fin.ext <| by
        simp only [Equiv.Perm.coe_mul, Function.comp_apply, Equiv.coe_fn_mk, Fin.val_cast]
        rw [b_symm_cast b _ ((hb τ (b.symm ⟨i, x⟩)).trans (by simp)),
          map_mul, Equiv.Perm.mul_apply] }
  property := Subgroup.isOpen_mono (H₁ := ρ₀.val.ker) (fun σ hσ ↦ by
    rw [MonoidHom.mem_ker] at hσ ⊢
    ext x
    simp only [MonoidHom.coe_mk, OneHom.coe_mk, Equiv.coe_fn_mk, Equiv.Perm.coe_one, id_eq,
      Fin.val_cast]
    rw [hσ, Equiv.Perm.one_apply, b.apply_symm_apply]) ρ₀.property

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
private theorem sigma_restrictBlock_eq {m : ℕ} {d : Fin m → ℕ} (ρ₀ : GaloisSet K n)
    (b : Fin n ≃ Σ i : Fin m, Fin (d i))
    (hb : ∀ (σ : Gal(SeparableClosure K/K)) (j : Fin n), (b (ρ₀.val σ j)).1 = (b j).1) :
    GaloisSet.sigma b (fun i ↦ restrictBlock ρ₀ b hb i) = ρ₀ := by
  refine Subtype.ext (MonoidHom.ext fun σ ↦ Equiv.ext fun j ↦ b.injective ?_)
  simp only [GaloisSet.sigma_val_apply, restrictBlock, MonoidHom.coe_mk, OneHom.coe_mk,
    Equiv.coe_fn_mk, b.apply_symm_apply]
  rw [Fin.sigma_mk_cast ((hb σ _).trans (by simp)), Sigma.eta, b.symm_apply_apply]

private theorem restrictBlock_splittingSymbol_eq {m : ℕ} {d : Fin m → ℕ}
    (ρ₀ : GaloisSet K n) (b : Fin n ≃ Σ i : Fin m, Fin (d i))
    (hb : ∀ (σ : Gal(SeparableClosure K/K)) (j : Fin n), (b (ρ₀.val σ j)).1 = (b j).1)
    (hd : ∀ i, 0 < d i)
    (hfib : ∀ (i : Fin m) (j₁ j₂ : Fin n),
      (b j₁).1 = i → (b j₂).1 = i →
        ∃ σ : Gal(SeparableClosure K/K), ρ₀.val σ j₁ = j₂)
    (i : Fin m) :
    (restrictBlock ρ₀ b hb i).splittingSymbol =
      {(let := ρ₀.mulAction
        orbitSymbol ρ₀ (Quotient.mk'' (b.symm ⟨i, ⟨0, hd i⟩⟩)))} := by
  let x₀ : Fin (d i) := ⟨0, hd i⟩
  have htrans : (restrictBlock ρ₀ b hb i).IsTransitive := by
    rw [GaloisSet.isTransitive_iff]
    intro x y
    obtain ⟨σ, hσ⟩ := hfib i (b.symm ⟨i, x⟩) (b.symm ⟨i, y⟩) (by simp) (by simp)
    refine ⟨σ, Fin.ext ?_⟩
    simp only [restrictBlock, MonoidHom.coe_mk, OneHom.coe_mk, Equiv.coe_fn_mk, Fin.val_cast]
    exact (congrArg (fun j : Fin n ↦ (b j).2.val) hσ).trans (by rw [b.apply_symm_apply])
  rw [(restrictBlock ρ₀ b hb i).splittingSymbol_of_isTransitive htrans x₀, orbitSymbol_mk]
  have hstab := GaloisSet.stabilizer_sigma_symm_apply b (fun j ↦ restrictBlock ρ₀ b hb j) i x₀
  rw [sigma_restrictBlock_eq ρ₀ b hb] at hstab
  dsimp only at hstab ⊢
  rw [← hstab]

private def splittingBlockTotal (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (n : ℕ) (σ : Multiset (ℕ × ℕ)) :=
  (Fin n ≃ Σ i : Fin σ.toList.length, Fin (σ.toList[i].1 * σ.toList[i].2)) ×
    (∀ i : Fin σ.toList.length,
      {ρᵢ : GaloisSet K (σ.toList[i].1 * σ.toList[i].2) //
        ρᵢ.splittingSymbol = {σ.toList[i]}})

private def splittingBlockMap (n : ℕ) (σ : Multiset (ℕ × ℕ))
    (p : splittingBlockTotal K n σ) :
    {ρ : GaloisSet K n // ρ.splittingSymbol = σ} :=
  ⟨GaloisSet.sigma p.1 (fun i ↦ (p.2 i).1), by
    rw [GaloisSet.splittingSymbol_sigma, Finset.sum_congr rfl fun i _ ↦ (p.2 i).2,
      Multiset.sum_toList_getElem σ fun x ↦ ({x} : Multiset (ℕ × ℕ)),
      Multiset.sum_map_singleton]⟩

private def blockFiberEquiv {m : ℕ} {d : Fin m → ℕ} {Q : Type*} (q : Fin n → Q)
    (e : Fin m ≃ Q) :
    {b : Fin n ≃ Σ i : Fin m, Fin (d i) // ∀ j, (b j).1 = e.symm (q j)} ≃
      ∀ i : Fin m, {j : Fin n // q j = e i} ≃ Fin (d i) :=
  (Equiv.fiberEquiv (fun j ↦ e.symm (q j)) Sigma.fst).trans <|
    Equiv.piCongrRight fun i ↦
      Equiv.equivCongr
        (Equiv.subtypeEquivRight fun _ ↦ e.symm_apply_eq)
        { toFun := fun p ↦ p.1.2.cast (congrArg d p.2)
          invFun := fun x ↦ ⟨⟨i, x⟩, rfl⟩
          left_inv := fun ⟨⟨_, _⟩, h⟩ ↦ Subtype.ext (Fin.sigma_mk_cast h)
          right_inv := fun _ ↦ Fin.ext rfl }

private theorem coe_blockFiberEquiv_apply {m : ℕ} {d : Fin m → ℕ} {Q : Type*}
    (q : Fin n → Q) (e : Fin m ≃ Q)
    (b : {b : Fin n ≃ Σ i : Fin m, Fin (d i) // ∀ j, (b j).1 = e.symm (q j)})
    (i : Fin m) (j : Fin n) (h : q j = e i) :
    (blockFiberEquiv q e b i ⟨j, h⟩).val = (b.1 j).2.val := by
  simp only [blockFiberEquiv, Equiv.trans_apply, Equiv.piCongrRight_apply, Pi.map_apply,
    Equiv.equivCongr_apply_apply, Equiv.coe_fn_mk, Fin.val_cast,
    Equiv.subtypeEquivRight_symm_apply]
  rw [Equiv.coe_fiberEquiv_apply]

private theorem splittingBlock_hQ_mk {n : ℕ} {σ : Multiset (ℕ × ℕ)}
    (hσ : ∀ x ∈ σ, 0 < x.1 ∧ 0 < x.2)
    (ρ₀ : {ρ : GaloisSet K n // ρ.splittingSymbol = σ})
    {p : splittingBlockTotal K n σ} (hΦ : splittingBlockMap n σ p = ρ₀)
    (i : Fin σ.toList.length) (x : Fin (σ.toList[i].1 * σ.toList[i].2)) :
    let := ρ₀.1.mulAction
    (Quotient.mk'' (p.1.symm ⟨i, x⟩) : orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n)) =
      Quotient.mk'' (p.1.symm ⟨i, ⟨0, toList_getElem_mul_pos hσ i⟩⟩) := by
  let := ρ₀.1.mulAction
  have htrans := GaloisSet.isTransitive_of_splittingSymbol_eq_singleton (p.2 i).2
  obtain ⟨g, hg⟩ := (GaloisSet.isTransitive_iff _).1 htrans
    ⟨0, toList_getElem_mul_pos hσ i⟩ x
  apply Quotient.sound'
  refine ⟨g, ?_⟩
  dsimp only
  rw [GaloisSet.smul_def]
  apply p.1.injective
  rw [p.1.apply_symm_apply, ← congrArg Subtype.val hΦ, splittingBlockMap,
    GaloisSet.sigma_val_apply, p.1.apply_symm_apply, p.1.apply_symm_apply]
  dsimp only
  rw [hg]

private def splittingBlockToE {n : ℕ} {σ : Multiset (ℕ × ℕ)}
    (hσ : ∀ x ∈ σ, 0 < x.1 ∧ 0 < x.2)
    (ρ₀ : {ρ : GaloisSet K n // ρ.splittingSymbol = σ})
    (p : splittingBlockTotal K n σ) (hΦ : splittingBlockMap n σ p = ρ₀) :
    {e : Fin σ.toList.length ≃
        (let := ρ₀.1.mulAction; orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n)) //
        ∀ i, orbitSymbol ρ₀.1 (e i) = σ.toList[i]} :=
  let := ρ₀.1.mulAction
  let x₀ (i : Fin σ.toList.length) : Fin (σ.toList[i].1 * σ.toList[i].2) :=
    ⟨0, toList_getElem_mul_pos hσ i⟩
  let fQ : Fin σ.toList.length → orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n) :=
    fun i ↦ Quotient.mk'' (p.1.symm ⟨i, x₀ i⟩)
  have hfQ : Function.Bijective fQ := by
    refine ⟨fun i₁ i₂ h ↦ ?_, fun O ↦ ?_⟩
    · obtain ⟨g, hg⟩ := Quotient.exact' h
      dsimp only at hg
      rw [GaloisSet.smul_def, ← congrArg Subtype.val hΦ] at hg
      have hb := congrArg (fun j ↦ (p.1 j).1) hg
      simp only [splittingBlockMap, GaloisSet.sigma_val_apply, p.1.apply_symm_apply] at hb
      exact hb.symm
    · refine ⟨(p.1 O.out).1, ?_⟩
      calc fQ (p.1 O.out).1
          = Quotient.mk'' (p.1.symm ⟨(p.1 O.out).1, (p.1 O.out).2⟩) :=
              (splittingBlock_hQ_mk hσ ρ₀ hΦ _ _).symm
        _ = O := by simp [Sigma.eta]
  ⟨Equiv.ofBijective fQ hfQ, fun i ↦ by
    have hsym := (p.2 i).2
    rw [GaloisSet.splittingSymbol_of_isTransitive _
      (GaloisSet.isTransitive_of_splittingSymbol_eq_singleton hsym) (x₀ i),
      Multiset.singleton_inj] at hsym
    have hstab := GaloisSet.stabilizer_sigma_symm_apply p.1 (fun j ↦ (p.2 j).1) i (x₀ i)
    rw [show GaloisSet.sigma p.1 (fun j ↦ (p.2 j).1) = ρ₀.1 from congrArg Subtype.val hΦ]
      at hstab
    dsimp only [Equiv.ofBijective, Equiv.coe_fn_mk, fQ]
    rw [orbitSymbol_mk]
    dsimp only at hstab ⊢
    rw [hstab]
    exact hsym⟩

private theorem splittingBlockToE_apply {n : ℕ} {σ : Multiset (ℕ × ℕ)}
    (hσ : ∀ x ∈ σ, 0 < x.1 ∧ 0 < x.2)
    (ρ₀ : {ρ : GaloisSet K n // ρ.splittingSymbol = σ})
    (p : splittingBlockTotal K n σ) (hΦ : splittingBlockMap n σ p = ρ₀)
    (i : Fin σ.toList.length) :
    (let := ρ₀.1.mulAction; (splittingBlockToE hσ ρ₀ p hΦ).1 i) =
      (let := ρ₀.1.mulAction;
        Quotient.mk'' (p.1.symm ⟨i, ⟨0, toList_getElem_mul_pos hσ i⟩⟩)) :=
  rfl

private theorem splittingBlock_fib_eq {n : ℕ} {σ : Multiset (ℕ × ℕ)}
    (hσ : ∀ x ∈ σ, 0 < x.1 ∧ 0 < x.2)
    (ρ₀ : {ρ : GaloisSet K n // ρ.splittingSymbol = σ})
    (p : splittingBlockTotal K n σ) (hΦ : splittingBlockMap n σ p = ρ₀) (j : Fin n) :
    (p.1 j).1 = (splittingBlockToE hσ ρ₀ p hΦ).1.symm
      (let := ρ₀.1.mulAction; Quotient.mk'' j) := by
  let := ρ₀.1.mulAction
  refine (Equiv.eq_symm_apply _).2 ?_
  rw [splittingBlockToE_apply]
  calc (Quotient.mk'' (p.1.symm ⟨(p.1 j).1, ⟨0, _⟩⟩) :
          orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n))
      = Quotient.mk'' (p.1.symm ⟨(p.1 j).1, (p.1 j).2⟩) :=
          (splittingBlock_hQ_mk hσ ρ₀ hΦ _ _).symm
    _ = Quotient.mk'' j := by simp [Sigma.eta]

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
private theorem block_preserve_of_orbit_eq {m : ℕ} {d : Fin m → ℕ} (ρ : GaloisSet K n)
    (e : Fin m ≃ let := ρ.mulAction; orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n))
    (b : Fin n ≃ Σ i : Fin m, Fin (d i))
    (hb_fib : ∀ j, (b j).1 = e.symm (let := ρ.mulAction; Quotient.mk'' j))
    (g : Gal(SeparableClosure K/K)) (j : Fin n) :
    (b (ρ.val g j)).1 = (b j).1 := by
  let := ρ.mulAction
  rw [hb_fib, hb_fib]
  congr 1
  exact Quotient.sound' ⟨g, rfl⟩

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
private theorem exists_smul_of_block_eq {m : ℕ} {d : Fin m → ℕ} (ρ : GaloisSet K n)
    (e : Fin m ≃ let := ρ.mulAction; orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n))
    (b : Fin n ≃ Σ i : Fin m, Fin (d i))
    (hb_fib : ∀ j, (b j).1 = e.symm (let := ρ.mulAction; Quotient.mk'' j))
    (i : Fin m) (j₁ j₂ : Fin n) (h₁ : (b j₁).1 = i) (h₂ : (b j₂).1 = i) :
    ∃ g : Gal(SeparableClosure K/K), ρ.val g j₁ = j₂ := by
  let := ρ.mulAction
  have hq : (Quotient.mk'' j₁ : orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n)) =
      Quotient.mk'' j₂ := by
    rw [e.symm_apply_eq.1 ((hb_fib j₁).symm.trans h₁),
      e.symm_apply_eq.1 ((hb_fib j₂).symm.trans h₂)]
  obtain ⟨g, hg⟩ := Quotient.exact' hq
  dsimp only at hg
  rw [GaloisSet.smul_def] at hg
  exact ⟨g⁻¹, by
    rw [← hg, ← Equiv.Perm.mul_apply, ← map_mul, inv_mul_cancel,
      map_one, Equiv.Perm.one_apply]⟩

-- A block decomposition `(b, ρᵢ)` of `ρ₀` determines an orbit-symbol-preserving bijection `e`
-- from block indices to orbits of `ρ₀` (`splittingBlockToE`) together with bijections `β i` on
-- each orbit fibre (`blockFiberEquiv`); conversely, `(e, β)` reconstructs `b` and restricts `ρ₀`
-- to each block via `restrictBlock`.
private def splittingBlockFiberEquiv {n : ℕ} {σ : Multiset (ℕ × ℕ)}
    (hσ : ∀ x ∈ σ, 0 < x.1 ∧ 0 < x.2)
    (ρ₀ : {ρ : GaloisSet K n // ρ.splittingSymbol = σ}) :
    {p : splittingBlockTotal K n σ // splittingBlockMap n σ p = ρ₀} ≃
      Σ e : {e : Fin σ.toList.length ≃
          (let := ρ₀.1.mulAction; orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n)) //
          ∀ i, orbitSymbol ρ₀.1 (e i) = σ.toList[i]},
        ∀ i : Fin σ.toList.length,
          {j : Fin n // (let := ρ₀.1.mulAction; Quotient.mk'' j) = e.1 i} ≃
            Fin (σ.toList[i].1 * σ.toList[i].2) :=
  let := ρ₀.1.mulAction
  let d (i : Fin σ.toList.length) : ℕ := σ.toList[i].1 * σ.toList[i].2
  let hd (i : Fin σ.toList.length) : 0 < d i := toList_getElem_mul_pos hσ i
  { toFun := fun ⟨p, hΦ⟩ ↦
      ⟨splittingBlockToE hσ ρ₀ p hΦ,
        blockFiberEquiv Quotient.mk'' (splittingBlockToE hσ ρ₀ p hΦ).1
          ⟨p.1, splittingBlock_fib_eq hσ ρ₀ p hΦ⟩⟩
    invFun := fun ⟨e, β⟩ ↦
      let ⟨b, hb_fib⟩ := (blockFiberEquiv Quotient.mk'' e.1).symm β
      have hb := block_preserve_of_orbit_eq ρ₀.1 e.1 b hb_fib
      have hfib := exists_smul_of_block_eq ρ₀.1 e.1 b hb_fib
      let ρᵢ : ∀ i : Fin σ.toList.length,
          {r : GaloisSet K (d i) // r.splittingSymbol = {σ.toList[i]}} := fun i ↦
        ⟨restrictBlock ρ₀.1 b hb i, by
          rw [restrictBlock_splittingSymbol_eq ρ₀.1 b hb hd hfib i]
          have hq : Quotient.mk'' (b.symm ⟨i, ⟨0, hd i⟩⟩) = e.1 i :=
            e.1.symm_apply_eq.1 ((hb_fib _).symm.trans (by simp))
          dsimp only at hq ⊢
          rw [hq, e.2 i]⟩
      ⟨⟨b, ρᵢ⟩, Subtype.ext (sigma_restrictBlock_eq ρ₀.1 b hb)⟩
    left_inv := fun ⟨⟨b, ρᵢ⟩, hΦ⟩ ↦ by
      let b_fib : {b' : Fin n ≃ Σ i, Fin (d i) //
          ∀ j, (b' j).1 =
            (splittingBlockToE hσ ρ₀ ⟨b, ρᵢ⟩ hΦ).1.symm (Quotient.mk'' j)} :=
        ⟨b, splittingBlock_fib_eq hσ ρ₀ ⟨b, ρᵢ⟩ hΦ⟩
      have hleft := congrArg Subtype.val
        ((blockFiberEquiv Quotient.mk''
          (splittingBlockToE hσ ρ₀ ⟨b, ρᵢ⟩ hΦ).1).symm_apply_apply b_fib)
      refine Subtype.ext (Prod.ext hleft ?_)
      refine funext fun i ↦
        Subtype.ext (Subtype.ext (MonoidHom.ext fun g ↦ Equiv.ext fun x ↦ Fin.ext ?_))
      simp only [restrictBlock, MonoidHom.coe_mk, OneHom.coe_mk, Equiv.coe_fn_mk, Fin.val_cast]
      dsimp only [b_fib] at hleft
      rw [hleft]
      have hpair : b (ρ₀.1.1 g (b.symm ⟨i, x⟩)) = ⟨i, (ρᵢ i).1.1 g x⟩ := by
        rw [← congrArg Subtype.val hΦ]
        dsimp only [splittingBlockMap]
        rw [GaloisSet.sigma_val_apply, b.apply_symm_apply, b.apply_symm_apply]
      exact congrArg (fun p : (i : Fin σ.toList.length) × Fin (d i) ↦ p.2.val) hpair
    right_inv := fun ⟨e, β⟩ ↦ by
      dsimp only
      let b_pair := (blockFiberEquiv Quotient.mk'' e.1).symm β
      have he_eq : ∀ p hΦ, p.1 = b_pair.1 → splittingBlockToE hσ ρ₀ p hΦ = e := by
        intro p hΦ hbp
        refine Subtype.ext (Equiv.ext fun i ↦ ?_)
        rw [splittingBlockToE_apply, hbp]
        exact e.1.symm_apply_eq.1 ((b_pair.2 _).symm.trans (by simp))
      refine sigma_fiber_ext (he_eq _ _ rfl) fun i j h₁ h₂ ↦ ?_
      apply Fin.ext
      have hR := congrArg (fun f ↦ (f i ⟨j, h₂⟩).val)
        ((blockFiberEquiv Quotient.mk'' e.1).apply_symm_apply β)
      rw [coe_blockFiberEquiv_apply] at hR ⊢
      exact hR }

private theorem natCard_splittingBlockFiber {n : ℕ} {σ : Multiset (ℕ × ℕ)}
    (hσ : ∀ x ∈ σ, 0 < x.1 ∧ 0 < x.2)
    (ρ₀ : {ρ : GaloisSet K n // ρ.splittingSymbol = σ}) :
    Nat.card {p : splittingBlockTotal K n σ // splittingBlockMap n σ p = ρ₀} =
      (∏ x ∈ σ.toFinset, (σ.count x)!) *
        ∏ i : Fin σ.toList.length, (σ.toList[i].1 * σ.toList[i].2)! := by
  classical
  -- Under `splittingBlockFiberEquiv`, each orbit-matching bijection `e` has `∏ i, (f_i * e_i)!`
  -- fibre labellings, and there are `∏ x, (σ.count x)!` such bijections `e`.
  let := ρ₀.1.mulAction
  let := Fintype.ofFinite (orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n))
  rw [Nat.card_congr (splittingBlockFiberEquiv hσ ρ₀), Nat.card_sigma]
  have hfib_card : ∀ e : {e : Fin σ.toList.length ≃
        orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n) //
        ∀ i, orbitSymbol ρ₀.1 (e i) = σ.toList[i]},
      Nat.card (∀ i : Fin σ.toList.length,
        {j : Fin n // Quotient.mk'' j = e.1 i} ≃
          Fin (σ.toList[i].1 * σ.toList[i].2)) =
        ∏ i : Fin σ.toList.length, (σ.toList[i].1 * σ.toList[i].2)! := by
    intro e
    rw [Nat.card_eq_fintype_card, Fintype.card_pi]
    refine Finset.prod_congr rfl fun i _ ↦ ?_
    have hc : Fintype.card {j : Fin n // Quotient.mk'' j = e.1 i} =
        σ.toList[i].1 * σ.toList[i].2 := by
      rw [← Nat.card_eq_fintype_card, natCard_fiber_orbit_eq, e.2 i]
    rw [Fintype.card_equiv (Fintype.equivFinOfCardEq hc), hc]
  simp_rw [hfib_card, Finset.sum_const, Finset.card_univ, smul_eq_mul,
    ← Nat.card_eq_fintype_card]
  congr 1
  have ho : (Finset.univ : Finset (orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n))).val.map
      (orbitSymbol ρ₀.1) = σ := by
    refine Eq.trans ?_ ρ₀.2
    rw [GaloisSet.splittingSymbol_def]
    congr 1
  exact Nat.card_subtype_equiv_of_map_univ_eq (Multiset.map_univ_toList σ) ho

end SplittingSymbolFiber

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

private theorem splittingBlockMap_weight_eq_prod {n : ℕ} {σ : Multiset (ℕ × ℕ)}
    (p : splittingBlockTotal K n σ) :
    1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ (splittingBlockMap n σ p).1.discriminantExponent =
      ∏ i : Fin σ.toList.length,
        1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ (p.2 i).1.discriminantExponent := by
  rcases p with ⟨b, ρᵢ⟩
  simp only [splittingBlockMap, GaloisSet.discriminantExponent_sigma,
    ← Finset.prod_pow_eq_pow_sum, one_div]
  exact ENNReal.prod_inv_distrib
    (fun _ _ _ _ _ ↦ Or.inr (ENNReal.pow_ne_top (ENNReal.natCast_ne_top _)))

private theorem card_blockEquiv {n : ℕ} {σ : Multiset (ℕ × ℕ)}
    (hn : (σ.map fun x => x.1 * x.2).sum = n) :
    Fintype.card (Fin n ≃ Σ i : Fin σ.toList.length, Fin (σ.toList[i].1 * σ.toList[i].2)) =
      n ! := by
  have hcard_sig :
      Fintype.card (Σ i : Fin σ.toList.length, Fin (σ.toList[i].1 * σ.toList[i].2)) = n := by
    simpa [Fintype.card_sigma, Fintype.card_fin] using
      (Multiset.sum_toList_getElem σ fun x ↦ x.1 * x.2).trans hn
  rw [Fintype.card_equiv (Fintype.equivFinOfCardEq hcard_sig).symm, Fintype.card_fin]

private theorem tsum_splittingSymbol_singleton_eq {f e : ℕ} (hf : 0 < f) (he : 0 < e) :
    (∑' r : {r : GaloisSet K (f * e) // r.splittingSymbol = {(f, e)}},
        1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ r.1.discriminantExponent) =
      ((f * e)! : ℝ≥0∞) *
        (1 / ((f : ℝ≥0∞) * (Nat.card 𝓀[K] : ℝ≥0∞) ^ (f * (e - 1)))) :=
  ennreal_eq_mul_of_inv_mul_eq (by exact_mod_cast (Nat.factorial_pos _).ne')
    (ENNReal.natCast_ne_top _) (etaleMass_isTransitive_splittingSymbol f e hf he)

private theorem tsum_splittingBlockTotal_direct (n : ℕ) (σ : Multiset (ℕ × ℕ))
    (hσ : ∀ x ∈ σ, 0 < x.1 ∧ 0 < x.2) (hn : (σ.map fun x => x.1 * x.2).sum = n) :
    ∑' p : splittingBlockTotal K n σ,
        1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ (splittingBlockMap n σ p).1.discriminantExponent =
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
      1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ r.1.discriminantExponent)]
  have hfac : ∀ i : Fin σ.toList.length,
      (∑' r : {r : GaloisSet K (σ.toList[i].1 * σ.toList[i].2) //
          r.splittingSymbol = {σ.toList[i]}},
          1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ r.1.discriminantExponent) =
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
    Multiset.prod_toList_getElem σ Prod.fst,
    (Multiset.sum_toList_getElem σ fun x ↦ x.1 * (x.2 - 1)).trans
      (splittingSymbolExponent_def σ).symm]

private theorem tsum_splittingBlockTotal_fiber (n : ℕ) (σ : Multiset (ℕ × ℕ))
    (hσ : ∀ x ∈ σ, 0 < x.1 ∧ 0 < x.2) :
    ∑' p : splittingBlockTotal K n σ,
        1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ (splittingBlockMap n σ p).1.discriminantExponent =
      (∏ x ∈ σ.toFinset, ((σ.count x)! : ℝ≥0∞)) *
        (∏ i : Fin σ.toList.length, ((σ.toList[i].1 * σ.toList[i].2)! : ℝ≥0∞)) *
        ∑' ρ₀ : {ρ : GaloisSet K n // ρ.splittingSymbol = σ},
          1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ ρ₀.1.discriminantExponent := by
  let w : GaloisSet K n → ℝ≥0∞ :=
    fun ρ ↦ 1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ ρ.discriminantExponent
  let Φ := splittingBlockMap (K := K) n σ
  rw [← (Equiv.sigmaFiberEquiv Φ).tsum_eq (fun p ↦ w (Φ p).1), tsum_sigma']
  simp only [Equiv.sigmaFiberEquiv_apply]
  have hconst : ∀ ρ₀ : {ρ : GaloisSet K n // ρ.splittingSymbol = σ},
      (∑' p : {p : splittingBlockTotal K n σ // Φ p = ρ₀}, w (Φ p.1).1) =
        (∏ x ∈ σ.toFinset, ((σ.count x)! : ℝ≥0∞)) *
          (∏ i : Fin σ.toList.length, ((σ.toList[i].1 * σ.toList[i].2)! : ℝ≥0∞)) *
          w ρ₀.1 := by
    intro ρ₀
    have hsub :
        ∀ p : {p : splittingBlockTotal K n σ // Φ p = ρ₀}, w (Φ p.1).1 = w ρ₀.1 :=
      fun p ↦ by rw [p.2]
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
          1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ ρ.1.discriminantExponent =
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
          ∑' ρ₀ : {ρ : GaloisSet K n // ρ.splittingSymbol = σ}, w ρ₀.1 =
        (n ! : ℝ≥0∞) *
          (1 / ((σ.map Prod.fst).prod *
            (Nat.card 𝓀[K] : ℝ≥0∞) ^ splittingSymbolExponent σ)) := by
    have h := (tsum_splittingBlockTotal_fiber (K := K) n σ hσ).symm.trans
      (tsum_splittingBlockTotal_direct (K := K) n σ hσ hn)
    rw [mul_comm (∏ x ∈ σ.toFinset, ((σ.count x)! : ℝ≥0∞)), mul_assoc,
      mul_comm (n ! : ℝ≥0∞), mul_assoc] at h
    exact (ENNReal.mul_right_inj hD_ne0 hD_netop).1 h
  have hS :
      (∑' ρ : {ρ : GaloisSet K n // ρ.splittingSymbol = σ}, w ρ.1) =
        (n ! : ℝ≥0∞) * ((∏ x ∈ σ.toFinset, ((σ.count x)! : ℝ≥0∞))⁻¹ *
          (1 / ((σ.map Prod.fst).prod *
            (Nat.card 𝓀[K] : ℝ≥0∞) ^ splittingSymbolExponent σ))) := by
    rw [← ennreal_inv_mul_eq_of_eq_mul hC_ne0 hC_netop heq_cancel.symm, mul_left_comm]
  change (n ! : ℝ≥0∞)⁻¹ * ∑' ρ : {ρ : GaloisSet K n // ρ.splittingSymbol = σ}, w ρ.1 = _
  rw [ennreal_inv_mul_eq_of_eq_mul hn_ne0 hn_netop hS, one_div, one_div,
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
          1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ ρ.1.discriminantExponent =
      1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ k := by
  -- Group Galois sets with ramification partition `π` by their splitting symbol `σ`, apply
  -- `etaleMass_splittingSymbol` on each fibre, and sum `1 / #Aut(σ)` via `SplittingSymbol.lean`.
  let Sym := {σ : Multiset (ℕ × ℕ) // (∀ x ∈ σ, 0 < x.1 ∧ 0 < x.2) ∧
    (σ.map fun x => x.1 * x.2).sum = n ∧ ramificationPartition σ = π.parts}
  let Ψ : {ρ : GaloisSet K n // ramificationPartition ρ.splittingSymbol = π.parts} → Sym :=
    fun ρ ↦ ⟨ρ.1.splittingSymbol,
      fun _ hx ↦ GaloisSet.pos_of_mem_splittingSymbol hx,
      ρ.1.sum_map_mul_splittingSymbol, ρ.2⟩
  let Efib (σ : Sym) :
      {ρ : {ρ : GaloisSet K n // ramificationPartition ρ.splittingSymbol = π.parts} //
          Ψ ρ = σ} ≃
        {ρ : GaloisSet K n // ρ.splittingSymbol = σ.1} :=
    { toFun := fun ρ ↦ ⟨ρ.1.1, congrArg Subtype.val ρ.2⟩
      invFun := fun ρ ↦ ⟨⟨ρ.1, by rw [ρ.2, σ.2.2.2]⟩, Subtype.ext ρ.2⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  have hsum :
      (∑' ρ : {ρ : GaloisSet K n // ramificationPartition ρ.splittingSymbol = π.parts},
          1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ ρ.1.discriminantExponent) =
        ∑' σ : Sym, ∑' ρ : {ρ : GaloisSet K n // ρ.splittingSymbol = σ.1},
          1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ ρ.1.discriminantExponent := by
    rw [← (Equiv.sigmaFiberEquiv Ψ).tsum_eq
      (fun ρ ↦ 1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ ρ.1.discriminantExponent), tsum_sigma']
    exact tsum_congr fun σ ↦ (Efib σ).tsum_eq
      (fun ρ ↦ 1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ ρ.1.discriminantExponent)
  rw [hsum, ← ENNReal.tsum_mul_left]
  have hterm : ∀ σ : Sym,
      (n ! : ℝ≥0∞)⁻¹ *
          ∑' ρ : {ρ : GaloisSet K n // ρ.splittingSymbol = σ.1},
            1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ ρ.1.discriminantExponent =
        (1 / (splittingSymbolAut σ : ℝ≥0∞)) * (1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ k) := by
    intro σ
    rw [etaleMass_splittingSymbol n σ.1 σ.2.1 σ.2.2.1,
      ← sum_ramificationPartition, σ.2.2.2, π.parts_sum]
    have haut0 : (splittingSymbolAut σ.1 : ℝ≥0∞) ≠ 0 := by
      exact_mod_cast (splittingSymbolAut_pos fun x hx ↦ (σ.2.1 x hx).1).ne'
    rw [one_div, one_div, one_div,
      ENNReal.mul_inv (Or.inl haut0) (Or.inl (ENNReal.natCast_ne_top _))]
  simp_rw [hterm, ENNReal.tsum_mul_right]
  dsimp only [Sym]
  rw [tsum_one_div_splittingSymbolAut_ramificationPartition n k π hπ, one_mul]

private theorem partIdx_ext {n : ℕ}
    {p₁ p₂ : Σ k : Finset.range (n + 1),
      {π : k.1.Partition // Multiset.card π.parts ≤ n - k.1}}
    (h : p₁.2.1.parts = p₂.2.1.parts) : p₁ = p₂ := by
  have hk : p₁.1.1 = p₂.1.1 := by rw [← p₁.2.1.parts_sum, ← p₂.2.1.parts_sum, h]
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
    {π : k.1.Partition // Multiset.card π.parts ≤ n - k.1}
  let partOf : GaloisSet K n → PartIdx := fun ρ ↦
    have hdeg := sum_map_mul_eq_sum_ramificationPartition_add ρ.splittingSymbol
      fun x hx ↦ (GaloisSet.pos_of_mem_splittingSymbol hx).2
    let _ := ρ.sum_map_mul_splittingSymbol
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
        {ρ : GaloisSet K n // ramificationPartition ρ.splittingSymbol = idx.2.1.parts} :=
    { toFun := fun ρ ↦ ⟨ρ.1, congrArg (fun x ↦ x.2.1.parts) ρ.2⟩
      invFun := fun ρ ↦ ⟨ρ.1, partIdx_ext (by simpa [partOf] using ρ.2)⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  rw [etaleMass_def, ← (Equiv.sigmaFiberEquiv partOf).tsum_eq
    (fun ρ ↦ 1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ ρ.discriminantExponent), tsum_sigma',
    ← ENNReal.tsum_mul_left]
  simp only [Equiv.sigmaFiberEquiv_apply]
  have hterm : ∀ idx : PartIdx,
      (n ! : ℝ≥0∞)⁻¹ * ∑' ρ : {ρ : GaloisSet K n // partOf ρ = idx},
          1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ ρ.1.discriminantExponent =
        1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ idx.1.1 := by
    intro idx
    have heq := (Efib idx).tsum_eq
      (fun ρ ↦ 1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ ρ.1.discriminantExponent)
    dsimp only [Efib, Equiv.coe_fn_mk] at heq
    rw [heq]
    exact etaleMass_ramificationPartition n idx.1.1 idx.2.1 idx.2.2
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
/-- **Bhargava's mass formula over étale algebras** ([Bhargava 2007, Thm. 1.1]): for any family
`A` of étale `K`-algebras of degree `n` containing exactly one member of each `K`-isomorphism
class, `∑ 1 / (#Aut_K(A i) · q ^ d(A i)) = ∑_{k ≤ n} q(k, n - k) · q ^ (-k)`. -/
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

end TauCeti
