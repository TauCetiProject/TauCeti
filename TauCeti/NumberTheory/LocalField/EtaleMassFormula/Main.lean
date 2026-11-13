/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.Enumerative.Partition.Basic
public import TauCeti.NumberTheory.LocalField.EtaleMassFormula.EtaleAlgebra
public import TauCeti.NumberTheory.LocalField.EtaleMassFormula.Transitive
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

private theorem natCard_equiv_of_eq {α β : Type*} [Finite α] [Finite β]
    (h : Nat.card α = Nat.card β) :
    Nat.card (α ≃ β) = (Nat.card α)! := by
  classical
  let _ := Fintype.ofFinite α
  let _ := Fintype.ofFinite β
  have he : Fintype.card α = Fintype.card β := by simpa [Nat.card_eq_fintype_card] using h
  rw [Nat.card_eq_fintype_card, Fintype.card_equiv (Fintype.equivOfCardEq he),
    Nat.card_eq_fintype_card]

private theorem multiset_map_finRange_toList (σ : Multiset (ℕ × ℕ)) :
    (Finset.univ : Finset (Fin σ.toList.length)).val.map (fun i ↦ σ.toList[i]) = σ := by
  rw [Fin.univ_def, Multiset.map_coe]
  exact (congrArg Multiset.ofList (List.map_getElem_finRange σ.toList)).trans
    (Multiset.coe_toList σ)

private theorem natCard_equiv_fiber_eq_prod_factorial (σ : Multiset (ℕ × ℕ)) :
    Nat.card {e : Fin σ.toList.length ≃ Fin σ.toList.length //
        ∀ i, σ.toList[e i] = σ.toList[i]} =
      ∏ x ∈ σ.toFinset, (σ.count x)! := by
  classical
  let s : Fin σ.toList.length → ℕ × ℕ := fun i ↦ σ.toList[i]
  have hs : (Finset.univ : Finset (Fin σ.toList.length)).val.map s = σ :=
    multiset_map_finRange_toList σ
  have hcount : ∀ x : ℕ × ℕ,
      Fintype.card {i : Fin σ.toList.length // s i = x} = σ.count x := by
    intro x
    rw [Fintype.card_subtype, ← Finset.card_val, Finset.filter_val]
    have hfilt : (Finset.univ : Finset (Fin σ.toList.length)).val.filter (fun i ↦ s i = x) =
        Finset.univ.val.filter (fun i ↦ x = s i) :=
      Multiset.filter_congr fun _ _ ↦ eq_comm
    rw [hfilt, ← Multiset.count_map s Finset.univ.val x, hs]
  let E₁ := Equiv.fiberEquiv s s
  let E₂ : (∀ x : ℕ × ℕ, {i // s i = x} ≃ {i // s i = x}) ≃
      (∀ x : σ.toFinset, Equiv.Perm {i // s i = x.1}) :=
    { toFun := fun f x ↦ f x.1
      invFun := fun g x ↦ if hx : x ∈ σ.toFinset then g ⟨x, hx⟩ else Equiv.refl _
      left_inv := fun f ↦ funext fun x ↦ by
        dsimp only
        by_cases hx : x ∈ σ.toFinset
        · simp [hx]
        · have hzero : Fintype.card {i : Fin σ.toList.length // s i = x} = 0 := by
            rw [hcount, Multiset.count_eq_zero]
            simpa using hx
          have : IsEmpty {i : Fin σ.toList.length // s i = x} := Fintype.card_eq_zero_iff.mp hzero
          simp [hx, Subsingleton.elim (Equiv.refl _) (f x)]
      right_inv := fun g ↦ funext fun ⟨x, hx⟩ ↦ by simp [hx] }
  rw [Nat.card_congr (E₁.trans E₂), Nat.card_eq_fintype_card, Fintype.card_pi,
    ← Finset.prod_coe_sort σ.toFinset]
  refine Finset.prod_congr rfl fun x _ ↦ ?_
  rw [Fintype.card_perm, hcount x]

private theorem sigma_mk_finCast {ι : Type*} {d : ι → ℕ} {i : ι} (p : Σ j, Fin (d j))
    (h : p.1 = i) : (⟨i, p.2.cast (congrArg d h)⟩ : Σ j, Fin (d j)) = p := by
  cases p
  subst h
  rfl

private theorem b_symm_cast {n m : ℕ} {d : Fin m → ℕ} (b : Fin n ≃ Σ i, Fin (d i))
    {i : Fin m} (j : Fin n) (h : (b j).1 = i) :
    b.symm ⟨i, (b j).2.cast (congrArg d h)⟩ = j := by
  rw [sigma_mk_finCast (b j) h, b.symm_apply_apply]

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
  rw [sigma_mk_finCast (b (ρ₀.val σ (b.symm ⟨(b j).1, (b j).2⟩)))
      ((hb σ _).trans (by simp)), Sigma.eta, b.symm_apply_apply]

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
  have hstab :
      (let := (restrictBlock ρ₀ b hb i).mulAction;
        stabilizer Gal(SeparableClosure K/K) x₀) =
      (let := ρ₀.mulAction;
        stabilizer Gal(SeparableClosure K/K) (b.symm ⟨i, x₀⟩)) := by
    ext σ
    simp only [MulAction.mem_stabilizer_iff, GaloisSet.smul_def]
    constructor
    · intro h
      apply b.injective
      calc b (ρ₀.val σ (b.symm ⟨i, x₀⟩))
          = ⟨i, (restrictBlock ρ₀ b hb i).val σ x₀⟩ := by
              dsimp only [restrictBlock, MonoidHom.coe_mk, OneHom.coe_mk, Equiv.coe_fn_mk]
              rw [sigma_mk_finCast (b (ρ₀.val σ (b.symm ⟨i, x₀⟩)))
                ((hb σ (b.symm ⟨i, x₀⟩)).trans (by simp))]
        _ = ⟨i, x₀⟩ := by rw [h]
        _ = b (b.symm ⟨i, x₀⟩) := (b.apply_symm_apply _).symm
    · intro h
      apply Fin.ext
      simp only [restrictBlock, MonoidHom.coe_mk, OneHom.coe_mk, Equiv.coe_fn_mk, Fin.val_cast]
      exact (congrArg (fun j : Fin n ↦ (b j).2.val) h).trans (by rw [b.apply_symm_apply])
  dsimp only
  rw [hstab]

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
    rw [GaloisSet.splittingSymbol_sigma]
    have h1 : (∑ i : Fin σ.toList.length, (p.2 i).1.splittingSymbol) =
        ∑ i : Fin σ.toList.length, ({σ.toList[i]} : Multiset (ℕ × ℕ)) :=
      Finset.sum_congr rfl fun i _ ↦ (p.2 i).2
    have h2 : ((Finset.univ : Finset (Fin σ.toList.length)).val.map
        fun i ↦ ({σ.toList[i]} : Multiset (ℕ × ℕ))) =
        ((Finset.univ : Finset (Fin σ.toList.length)).val.map fun i ↦ σ.toList[i]).map
          fun x : ℕ × ℕ ↦ ({x} : Multiset (ℕ × ℕ)) := by
      rw [Multiset.map_map]
      rfl
    rw [h1, Finset.sum_eq_multiset_sum, h2, multiset_map_finRange_toList,
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
          left_inv := fun ⟨⟨_, _⟩, h⟩ ↦ Subtype.ext (sigma_mk_finCast _ h)
          right_inv := fun _ ↦ Fin.ext rfl }

private theorem coe_blockFiberEquiv_apply {m : ℕ} {d : Fin m → ℕ} {Q : Type*}
    (q : Fin n → Q) (e : Fin m ≃ Q)
    (b : {b : Fin n ≃ Σ i : Fin m, Fin (d i) // ∀ j, (b j).1 = e.symm (q j)})
    (i : Fin m) (j : Fin n) (h : q j = e i) :
    (blockFiberEquiv q e b i ⟨j, h⟩).val = (b.1 j).2.val := by
  dsimp only [blockFiberEquiv, Equiv.equivCongr, Equiv.piCongrRight, Pi.map,
    Equiv.trans_apply, Equiv.coe_fn_mk]
  rw [Fin.val_cast, Equiv.coe_fiberEquiv_apply]
  rfl

private theorem splittingBlock_hQ_mk {n : ℕ} {σ : Multiset (ℕ × ℕ)}
    (hσ : ∀ x ∈ σ, 0 < x.1 ∧ 0 < x.2)
    (ρ₀ : {ρ : GaloisSet K n // ρ.splittingSymbol = σ})
    {p : splittingBlockTotal K n σ} (hΦ : splittingBlockMap n σ p = ρ₀)
    (i : Fin σ.toList.length) (x : Fin (σ.toList[i].1 * σ.toList[i].2)) :
    let := ρ₀.1.mulAction
    let hd : 0 < σ.toList[i].1 * σ.toList[i].2 :=
      have hmem : σ.toList[i] ∈ σ := Multiset.mem_toList.1 (List.getElem_mem i.isLt)
      Nat.mul_pos (hσ _ hmem).1 (hσ _ hmem).2
    (Quotient.mk'' (p.1.symm ⟨i, x⟩) : orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n)) =
      Quotient.mk'' (p.1.symm ⟨i, ⟨0, hd⟩⟩) := by
  let := ρ₀.1.mulAction
  have hmem : σ.toList[i] ∈ σ := Multiset.mem_toList.1 (List.getElem_mem i.isLt)
  let hd : 0 < σ.toList[i].1 * σ.toList[i].2 := Nat.mul_pos (hσ _ hmem).1 (hσ _ hmem).2
  have htrans := GaloisSet.isTransitive_of_splittingSymbol_eq_singleton (p.2 i).2
  obtain ⟨g, hg⟩ := (GaloisSet.isTransitive_iff _).1 htrans ⟨0, hd⟩ x
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
  let hd (i : Fin σ.toList.length) : 0 < σ.toList[i].1 * σ.toList[i].2 :=
    have hmem : σ.toList[i] ∈ σ := Multiset.mem_toList.1 (List.getElem_mem i.isLt)
    Nat.mul_pos (hσ _ hmem).1 (hσ _ hmem).2
  let x₀ (i : Fin σ.toList.length) : Fin (σ.toList[i].1 * σ.toList[i].2) := ⟨0, hd i⟩
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
    have hstab :
        (let := (p.2 i).1.mulAction;
          stabilizer Gal(SeparableClosure K/K) (x₀ i)) =
        stabilizer Gal(SeparableClosure K/K) (p.1.symm ⟨i, x₀ i⟩) := by
      ext g
      simp only [MulAction.mem_stabilizer_iff, GaloisSet.smul_def]
      constructor
      · intro h
        rw [← congrArg Subtype.val hΦ]
        apply p.1.injective
        rw [splittingBlockMap, GaloisSet.sigma_val_apply, p.1.apply_symm_apply,
          p.1.apply_symm_apply]
        dsimp only
        rw [h]
      · intro h
        rw [← congrArg Subtype.val hΦ] at h
        have hb := congrArg p.1 h
        rw [splittingBlockMap, GaloisSet.sigma_val_apply, p.1.apply_symm_apply,
          p.1.apply_symm_apply] at hb
        exact eq_of_heq (Sigma.ext_iff.1 hb).2
    dsimp only [Equiv.ofBijective, Equiv.coe_fn_mk, fQ]
    rw [orbitSymbol_mk]
    dsimp only
    rw [← hstab]
    exact hsym⟩

private theorem splittingBlockToE_apply {n : ℕ} {σ : Multiset (ℕ × ℕ)}
    (hσ : ∀ x ∈ σ, 0 < x.1 ∧ 0 < x.2)
    (ρ₀ : {ρ : GaloisSet K n // ρ.splittingSymbol = σ})
    (p : splittingBlockTotal K n σ) (hΦ : splittingBlockMap n σ p = ρ₀)
    (i : Fin σ.toList.length) :
    (let := ρ₀.1.mulAction; (splittingBlockToE hσ ρ₀ p hΦ).1 i) =
      (let := ρ₀.1.mulAction;
        have hd : 0 < σ.toList[i].1 * σ.toList[i].2 :=
          have hmem : σ.toList[i] ∈ σ := Multiset.mem_toList.1 (List.getElem_mem i.isLt)
          Nat.mul_pos (hσ _ hmem).1 (hσ _ hmem).2
        Quotient.mk'' (p.1.symm ⟨i, ⟨0, hd⟩⟩)) :=
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
  let hd (i : Fin σ.toList.length) : 0 < d i :=
    have hmem : σ.toList[i] ∈ σ := Multiset.mem_toList.1 (List.getElem_mem i.isLt)
    Nat.mul_pos (hσ _ hmem).1 (hσ _ hmem).2
  let x₀ (i : Fin σ.toList.length) : Fin (d i) := ⟨0, hd i⟩
  { toFun := fun ⟨p, hΦ⟩ ↦
      ⟨splittingBlockToE hσ ρ₀ p hΦ,
        blockFiberEquiv Quotient.mk'' (splittingBlockToE hσ ρ₀ p hΦ).1
          ⟨p.1, splittingBlock_fib_eq hσ ρ₀ p hΦ⟩⟩
    invFun := fun ⟨e, β⟩ ↦
      let ⟨b, hb_fib⟩ := (blockFiberEquiv Quotient.mk'' e.1).symm β
      have hb : ∀ (g : Gal(SeparableClosure K/K)) (j : Fin n),
          (b (ρ₀.1.val g j)).1 = (b j).1 := fun g j ↦ by
        rw [hb_fib, hb_fib]
        congr 1
        exact Quotient.sound' ⟨g, rfl⟩
      have hfib : ∀ (i : Fin σ.toList.length) (j₁ j₂ : Fin n), (b j₁).1 = i →
          (b j₂).1 = i → ∃ g : Gal(SeparableClosure K/K), ρ₀.1.val g j₁ = j₂ := by
        intro i j₁ j₂ h₁ h₂
        have hq : (Quotient.mk'' j₁ : orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n)) =
            Quotient.mk'' j₂ := by
          rw [e.1.symm_apply_eq.1 ((hb_fib j₁).symm.trans h₁),
            e.1.symm_apply_eq.1 ((hb_fib j₂).symm.trans h₂)]
        obtain ⟨g, hg⟩ := Quotient.exact' hq
        dsimp only at hg ⊢
        rw [GaloisSet.smul_def] at hg
        exact ⟨g⁻¹, by
          rw [← hg, ← Equiv.Perm.mul_apply, ← map_mul, inv_mul_cancel,
            map_one, Equiv.Perm.one_apply]⟩
      let ρᵢ : ∀ i : Fin σ.toList.length,
          {r : GaloisSet K (d i) // r.splittingSymbol = {σ.toList[i]}} := fun i ↦
        ⟨restrictBlock ρ₀.1 b hb i, by
          rw [restrictBlock_splittingSymbol_eq ρ₀.1 b hb hd hfib i]
          have hq : Quotient.mk'' (b.symm ⟨i, x₀ i⟩) = e.1 i :=
            e.1.symm_apply_eq.1 ((hb_fib _).symm.trans (by simp))
          dsimp only [x₀] at hq ⊢
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
    have hc : Nat.card {j : Fin n // Quotient.mk'' j = e.1 i} =
        Nat.card (Fin (σ.toList[i].1 * σ.toList[i].2)) := by
      rw [natCard_fiber_orbit_eq, e.2 i, Nat.card_fin]
    rw [← Nat.card_eq_fintype_card, natCard_equiv_of_eq hc, hc, Nat.card_fin]
  simp_rw [hfib_card, Finset.sum_const, Finset.card_univ, smul_eq_mul,
    ← Nat.card_eq_fintype_card]
  congr 1
  let s : Fin σ.toList.length → ℕ × ℕ := fun i ↦ σ.toList[i]
  have hs : (Finset.univ : Finset (Fin σ.toList.length)).val.map s = σ :=
    multiset_map_finRange_toList σ
  have ho : (Finset.univ : Finset (orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n))).val.map
      (orbitSymbol ρ₀.1) = σ := by
    refine (Eq.trans ?_ ρ₀.2)
    rw [GaloisSet.splittingSymbol_def]
    congr 1
  have hcount : ∀ x : ℕ × ℕ,
      Nat.card {i : Fin σ.toList.length // s i = x} =
        Nat.card {O : orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n) //
          orbitSymbol ρ₀.1 O = x} := by
    intro x
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
      Fintype.card_subtype, Fintype.card_subtype, ← Finset.card_val, ← Finset.card_val,
      Finset.filter_val, Finset.filter_val]
    have h1 : (Finset.univ : Finset (Fin σ.toList.length)).val.filter (fun i ↦ s i = x) =
        Finset.univ.val.filter (fun i ↦ x = s i) :=
      Multiset.filter_congr fun _ _ ↦ eq_comm
    have h2 : (Finset.univ : Finset
          (orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n))).val.filter
          (fun O ↦ orbitSymbol ρ₀.1 O = x) =
        Finset.univ.val.filter (fun O ↦ x = orbitSymbol ρ₀.1 O) :=
      Multiset.filter_congr fun _ _ ↦ eq_comm
    rw [h1, h2, ← Multiset.count_map s _ x, ← Multiset.count_map (orbitSymbol ρ₀.1) _ x,
      hs, ho]
  have hfix : ∀ x : ℕ × ℕ,
      {i : Fin σ.toList.length // s i = x} ≃
        {O : orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n) // orbitSymbol ρ₀.1 O = x} :=
    fun x ↦ Fintype.equivOfCardEq (by simpa [Nat.card_eq_fintype_card] using hcount x)
  let E_base : {e : Fin σ.toList.length ≃
        orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n) //
        ∀ i, orbitSymbol ρ₀.1 (e i) = s i} ≃
      {e : Fin σ.toList.length ≃ Fin σ.toList.length // ∀ i, s (e i) = s i} :=
    (Equiv.fiberEquiv s (orbitSymbol ρ₀.1)).trans <|
      (Equiv.piCongrRight fun x ↦ Equiv.equivCongr (Equiv.refl _) (hfix x).symm).trans
        (Equiv.fiberEquiv s s).symm
  rw [Nat.card_congr E_base, natCard_equiv_fiber_eq_prod_factorial]

end SplittingSymbolFiber

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

private theorem tsum_splittingBlockTotal_direct (n : ℕ) (σ : Multiset (ℕ × ℕ))
    (hσ : ∀ x ∈ σ, 0 < x.1 ∧ 0 < x.2) (hn : (σ.map fun x => x.1 * x.2).sum = n) :
    ∑' p : splittingBlockTotal K n σ,
        1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ (splittingBlockMap n σ p).1.discriminantExponent =
      (n ! : ℝ≥0∞) *
        (∏ i : Fin σ.toList.length, ((σ.toList[i].1 * σ.toList[i].2)! : ℝ≥0∞)) *
        (1 / ((σ.map Prod.fst).prod *
          (Nat.card 𝓀[K] : ℝ≥0∞) ^ splittingSymbolExponent σ)) := by
  let s : Fin σ.toList.length → ℕ × ℕ := fun i ↦ σ.toList[i]
  have hs : (Finset.univ : Finset (Fin σ.toList.length)).val.map s = σ :=
    multiset_map_finRange_toList σ
  have hpos : ∀ i, 0 < (s i).1 ∧ 0 < (s i).2 := fun i ↦
    hσ (s i) (Multiset.mem_toList.1 (List.getElem_mem i.isLt))
  have hsum_d : (∑ i : Fin σ.toList.length, σ.toList[i].1 * σ.toList[i].2) = n := by
    calc ∑ i : Fin σ.toList.length, (s i).1 * (s i).2
        = (Finset.univ.val.map fun i ↦ (s i).1 * (s i).2).sum :=
            Finset.sum_eq_multiset_sum Finset.univ _
      _ = ((Finset.univ.val.map s).map fun x ↦ x.1 * x.2).sum := by rw [Multiset.map_map]; rfl
      _ = (σ.map fun x ↦ x.1 * x.2).sum :=
            congrArg (fun m ↦ (m.map fun x ↦ x.1 * x.2).sum) hs
      _ = n := hn
  have hprod_f : (∏ i : Fin σ.toList.length, σ.toList[i].1) = (σ.map Prod.fst).prod := by
    calc ∏ i : Fin σ.toList.length, (s i).1
        = (Finset.univ.val.map fun i ↦ (s i).1).prod := Finset.prod_eq_multiset_prod Finset.univ _
      _ = ((Finset.univ.val.map s).map Prod.fst).prod := by rw [Multiset.map_map]; rfl
      _ = (σ.map Prod.fst).prod := congrArg (fun m ↦ (m.map Prod.fst).prod) hs
  have hsum_exp : (∑ i : Fin σ.toList.length, σ.toList[i].1 * (σ.toList[i].2 - 1)) =
      splittingSymbolExponent σ := by
    rw [splittingSymbolExponent_def]
    calc ∑ i : Fin σ.toList.length, (s i).1 * ((s i).2 - 1)
        = (Finset.univ.val.map fun i ↦ (s i).1 * ((s i).2 - 1)).sum :=
            Finset.sum_eq_multiset_sum Finset.univ _
      _ = ((Finset.univ.val.map s).map fun x ↦ x.1 * (x.2 - 1)).sum := by
            rw [Multiset.map_map]; rfl
      _ = (σ.map fun x ↦ x.1 * (x.2 - 1)).sum :=
            congrArg (fun m ↦ (m.map fun x ↦ x.1 * (x.2 - 1)).sum) hs
  have hw : ∀ p : splittingBlockTotal K n σ,
      1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ (splittingBlockMap n σ p).1.discriminantExponent =
        ∏ i : Fin σ.toList.length,
          1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ (p.2 i).1.discriminantExponent := by
    rintro ⟨b, ρᵢ⟩
    simp only [splittingBlockMap, GaloisSet.discriminantExponent_sigma,
      ← Finset.prod_pow_eq_pow_sum, one_div]
    exact ENNReal.prod_inv_distrib
      (fun _ _ _ _ _ ↦ Or.inr (ENNReal.pow_ne_top (ENNReal.natCast_ne_top _)))
  simp_rw [hw]
  dsimp only [splittingBlockTotal]
  rw [tsum_prod']
  dsimp only
  have hcard_b :
      Fintype.card (Fin n ≃ Σ i : Fin σ.toList.length, Fin (σ.toList[i].1 * σ.toList[i].2)) =
        n ! := by
    have hcard_sig :
        Fintype.card (Σ i : Fin σ.toList.length, Fin (σ.toList[i].1 * σ.toList[i].2)) = n := by
      simpa [Fintype.card_sigma, Fintype.card_fin] using hsum_d
    rw [Fintype.card_equiv ((Fintype.equivFinOfCardEq hcard_sig).symm), Fintype.card_fin]
  rw [tsum_fintype, Finset.sum_const, Finset.card_univ, hcard_b, nsmul_eq_mul,
    ENNReal.tsum_prod_pi (fun (i : Fin σ.toList.length)
      (r : {ρᵢ : GaloisSet K (σ.toList[i].1 * σ.toList[i].2) //
        ρᵢ.splittingSymbol = {σ.toList[i]}}) ↦
      1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ r.1.discriminantExponent)]
  have hfac : ∀ i : Fin σ.toList.length,
      (∑' r : {r : GaloisSet K (σ.toList[i].1 * σ.toList[i].2) //
          r.splittingSymbol = {σ.toList[i]}},
          1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ r.1.discriminantExponent) =
        (((σ.toList[i].1 * σ.toList[i].2)! : ℝ≥0∞)) *
          (1 / (((σ.toList[i].1 : ℝ≥0∞)) *
            (Nat.card 𝓀[K] : ℝ≥0∞) ^ (σ.toList[i].1 * (σ.toList[i].2 - 1)))) := by
    intro i
    have hi := etaleMass_isTransitive_splittingSymbol (K := K)
      (s i).1 (s i).2 (hpos i).1 (hpos i).2
    have hne0 : (((s i).1 * (s i).2)! : ℝ≥0∞) ≠ 0 := by
      exact_mod_cast (Nat.factorial_pos _).ne'
    have hnetop : (((s i).1 * (s i).2)! : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
    dsimp only [s] at hi hne0 hnetop
    calc (∑' r : {r : GaloisSet K (σ.toList[i].1 * σ.toList[i].2) //
            r.splittingSymbol = {σ.toList[i]}},
            1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ r.1.discriminantExponent)
        = ((σ.toList[i].1 * σ.toList[i].2)! : ℝ≥0∞) *
            (((σ.toList[i].1 * σ.toList[i].2)! : ℝ≥0∞)⁻¹ *
              ∑' r : {r : GaloisSet K (σ.toList[i].1 * σ.toList[i].2) //
                  r.splittingSymbol = {σ.toList[i]}},
                1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ r.1.discriminantExponent) := by
            rw [← mul_assoc, ENNReal.mul_inv_cancel hne0 hnetop, one_mul]
      _ = _ := by rw [hi]
  simp_rw [hfac, Finset.prod_mul_distrib]
  rw [← mul_assoc]
  congr 1
  simp only [one_div]
  rw [← ENNReal.prod_inv_distrib
    (fun _ _ _ _ _ ↦ Or.inr (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _)
      (ENNReal.pow_ne_top (ENNReal.natCast_ne_top _))))]
  congr 1
  rw [Finset.prod_mul_distrib, ← Nat.cast_prod, Finset.prod_pow_eq_pow_sum, hprod_f, hsum_exp]

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
  calc (n ! : ℝ≥0∞)⁻¹ *
        ∑' ρ : {ρ : GaloisSet K n // ρ.splittingSymbol = σ}, w ρ.1
      = ((n ! : ℝ≥0∞)⁻¹ * (∏ x ∈ σ.toFinset, ((σ.count x)! : ℝ≥0∞))⁻¹) *
          ((∏ x ∈ σ.toFinset, ((σ.count x)! : ℝ≥0∞)) *
            ∑' ρ : {ρ : GaloisSet K n // ρ.splittingSymbol = σ}, w ρ.1) := by
          rw [mul_assoc, ← mul_assoc ((∏ x ∈ σ.toFinset, ((σ.count x)! : ℝ≥0∞))⁻¹),
            ENNReal.inv_mul_cancel hC_ne0 hC_netop, one_mul]
    _ = ((n ! : ℝ≥0∞)⁻¹ * (n ! : ℝ≥0∞)) *
          ((∏ x ∈ σ.toFinset, ((σ.count x)! : ℝ≥0∞))⁻¹ *
            (1 / ((σ.map Prod.fst).prod *
              (Nat.card 𝓀[K] : ℝ≥0∞) ^ splittingSymbolExponent σ))) := by
          rw [heq_cancel]; ring
    _ = (∏ x ∈ σ.toFinset, ((σ.count x)! : ℝ≥0∞))⁻¹ *
          (1 / ((σ.map Prod.fst).prod *
            (Nat.card 𝓀[K] : ℝ≥0∞) ^ splittingSymbolExponent σ)) := by
          rw [ENNReal.inv_mul_cancel hn_ne0 hn_netop, one_mul]
    _ = 1 / ((splittingSymbolAut σ : ℝ≥0∞) *
          (Nat.card 𝓀[K] : ℝ≥0∞) ^ splittingSymbolExponent σ) := by
          rw [splittingSymbolAut_def, Nat.cast_mul, Nat.cast_prod, one_div, one_div]
          have hP_ne0 : ((σ.map Prod.fst).prod : ℝ≥0∞) ≠ 0 := by
            exact_mod_cast (Multiset.prod_pos fun a ha ↦ by
              obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.1 ha
              exact (hσ x hx).1).ne'
          have hP_netop : ((σ.map Prod.fst).prod : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
          rw [ENNReal.mul_inv (Or.inl hP_ne0) (Or.inl hP_netop),
            ENNReal.mul_inv (Or.inl (mul_ne_zero hP_ne0 hC_ne0))
              (Or.inl (ENNReal.mul_ne_top hP_netop hC_netop)),
            ENNReal.mul_inv (Or.inl hP_ne0) (Or.inl hP_netop)]
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
      splittingSymbolExponent_eq_sum_ramificationPartition, σ.2.2.2, π.parts_sum]
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
