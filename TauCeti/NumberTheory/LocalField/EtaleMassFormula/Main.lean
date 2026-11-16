/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.EtaleMassFormula.EtaleAlgebra
public import TauCeti.NumberTheory.LocalField.EtaleMassFormula.SplittingSymbol
public import TauCeti.NumberTheory.LocalField.Unramified.IntermediateField
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Sort
import TauCeti.FieldTheory.Galois.FixedField
import TauCeti.NumberTheory.LocalField.EtaleMassFormula.SubfieldCount

/-!
# Bhargava's mass formulas for étale algebras over a local field

Let `K` be a nonarchimedean local field with `q` residue classes. Each labelled Galois set `ρ` of
size `n` decomposes into orbits, and recording for each orbit the pair `(f, e)` of residue degree
and ramification index of a point stabilizer's fixed field produces its splitting symbol
`TauCeti.GaloisSet.splittingSymbol ρ : Multiset (ℕ × ℕ)` [Bhargava 2007, (2.1)].

This file proves Bhargava's hierarchy of mass formulas for every nonarchimedean local field `K`:

1. **Transitive mass by residue degree** (`TauCeti.etaleMass_isTransitive_splittingSymbol`):
   the Galois sets of size `f * e` with splitting symbol `{(f, e)}` have mass
   `q ^ (-f(e - 1)) / f`, combining the transitive bridge `TauCeti.GaloisSet.tsum_isTransitive`
   with the subfield count by residue degree `TauCeti.tsum_inertiaDegree_eq`.
2. **Mass formula for a fixed splitting type** (`TauCeti.etaleMass_splittingSymbol`,
   [Bhargava 2007, Prop. 2.1]): for any splitting symbol `σ` of degree `n`, the Galois sets with
   symbol `σ` have mass `1 / (#Aut(σ) · q ^ (∑ f_i (e_i - 1)))`. The proof inducts on `σ` by
   splitting off a single orbit of type `x ∈ σ` via `TauCeti.GaloisSet.orbitSplitEquiv`.
3. **Mass formula for a fixed ramification partition** (`TauCeti.etaleMass_ramificationPartition`,
   [Bhargava 2007, Prop. 2.2]): for a partition `π` of `k` into at most `n - k` parts, the Galois
   sets of size `n` with ramification partition `π` have mass `q ^ (-k)`, obtained by summing
   Proposition 2.1 against the combinatorial identity
   `TauCeti.tsum_one_div_splittingSymbolAut_ramificationPartition`.
4. **Bhargava's mass formula** (`TauCeti.etaleMass_eq` and
   `TauCeti.tsum_etaleDiscriminantExponent_eq`, [Bhargava 2007, Thm. 1.1, Prop. 2.3, §8]):
   `M_n(K) = ∑_{k = 0}^n q(k, n - k) · q ^ (-k)`, where `q(k, m)` is the number of partitions of
   `k` into at most `m` parts. For `n ≥ 1` the `k = n` term vanishes, recovering Bhargava's
   `∑_{k = 0}^{n - 1}`; at `n = 0` both sides equal `1`.

All sums are taken in `ℝ≥0∞`, so the formulas hold in equal characteristic as well, where
infinitely many Galois sets of size `n` exist once `n` is at least the characteristic.

## Main definitions and results

* `TauCeti.GaloisSet.splittingSymbol`: the splitting symbol of a labelled Galois set.
* `TauCeti.etaleMass_isTransitive_splittingSymbol`: mass of Galois sets with symbol `{(f, e)}`.
* `TauCeti.etaleMass_splittingSymbol`: mass of Galois sets with splitting symbol `σ`
  ([Bhargava 2007, Prop. 2.1]).
* `TauCeti.etaleMass_ramificationPartition`: mass of Galois sets with ramification partition `π`
  ([Bhargava 2007, Prop. 2.2]).
* `TauCeti.etaleMass_eq`: Bhargava's mass formula for `etaleMass K n`
  ([Bhargava 2007, Thm. 1.1, Prop. 2.3, §8]).
* `TauCeti.tsum_etaleDiscriminantExponent_eq`: Bhargava's mass formula over isomorphism classes
  of étale `K`-algebras of degree `n`.

## References

* M. Bhargava, *Mass formulae for extensions of local fields, and conjectures on the density of
  number field discriminants*, IMRN **2007**, rnm052, Theorem 1.1, Propositions 2.1–2.3, (2.1),
  and §8.
* K. S. Kedlaya, *Mass formulas for local Galois representations*, IMRN **2007**, rnm021.
-/

public section

noncomputable section

open ValuativeRel
open scoped ENNReal

namespace TauCeti

universe u

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-! ### Splitting symbols of Galois sets -/

section OrbitPair

variable {X Y : Type*} [MulAction Gal(SeparableClosure K/K) X]
  [MulAction Gal(SeparableClosure K/K) Y]

private theorem inertiaDegree_finrank_fixedField_stabilizer_smul
    (σ : Gal(SeparableClosure K/K)) (x : X) :
    (let F := IntermediateField.fixedField
        (MulAction.stabilizer Gal(SeparableClosure K/K) (σ • x));
      (F.inertiaDegree, Module.finrank K F / F.inertiaDegree)) =
    (let F := IntermediateField.fixedField
        (MulAction.stabilizer Gal(SeparableClosure K/K) x);
      (F.inertiaDegree, Module.finrank K F / F.inertiaDegree)) := by
  dsimp only
  rw [MulAction.stabilizer_smul_eq_stabilizer_map_conj, MulEquiv.toMonoidHom_eq_coe,
    Subgroup.fixedField_map_conj]
  let e := (IntermediateField.fixedField
    (MulAction.stabilizer Gal(SeparableClosure K/K) x)).equivMap σ.toAlgHom
  rw [IntermediateField.inertiaDegree_eq_of_algEquiv e.symm, e.symm.toLinearEquiv.finrank_eq]

private theorem inertiaDegree_finrank_fixedField_stabilizer_out
    {ω : MulAction.orbitRel.Quotient Gal(SeparableClosure K/K) X} {x : X}
    (hx : (Quotient.mk'' x : MulAction.orbitRel.Quotient Gal(SeparableClosure K/K) X) = ω) :
    (let F := IntermediateField.fixedField
        (MulAction.stabilizer Gal(SeparableClosure K/K) ω.out);
      (F.inertiaDegree, Module.finrank K F / F.inertiaDegree)) =
    (let F := IntermediateField.fixedField
        (MulAction.stabilizer Gal(SeparableClosure K/K) x);
      (F.inertiaDegree, Module.finrank K F / F.inertiaDegree)) := by
  obtain ⟨σ, rfl⟩ := MulAction.exists_smul_out_eq hx
  exact (inertiaDegree_finrank_fixedField_stabilizer_smul (K := K) σ ω.out).symm

private theorem inertiaDegree_finrank_fixedField_stabilizer_out_of_injective
    (f : X → Y) (hf : Function.Injective f)
    (he : ∀ (σ : Gal(SeparableClosure K/K)) (x : X), f (σ • x) = σ • f x)
    {ω : MulAction.orbitRel.Quotient Gal(SeparableClosure K/K) Y} {x : X}
    (hx : (Quotient.mk'' (f x) : MulAction.orbitRel.Quotient Gal(SeparableClosure K/K) Y) = ω) :
    (let F := IntermediateField.fixedField
        (MulAction.stabilizer Gal(SeparableClosure K/K) ω.out);
      (F.inertiaDegree, Module.finrank K F / F.inertiaDegree)) =
    (let F := IntermediateField.fixedField
        (MulAction.stabilizer Gal(SeparableClosure K/K) x);
      (F.inertiaDegree, Module.finrank K F / F.inertiaDegree)) := by
  rw [inertiaDegree_finrank_fixedField_stabilizer_out (K := K) hx,
    MulAction.stabilizer_eq_of_injective f hf he]

end OrbitPair

namespace GaloisSet

variable {n : ℕ}

/-- The **splitting symbol** of a labelled Galois set ([Bhargava 2007, (2.1)]): the multiset, over
its orbits, of the pair `(f, e)` of residue degree and ramification index of the fixed field of
the stabilizer of a point of the orbit. -/
def splittingSymbol (ρ : GaloisSet K n) : Multiset (ℕ × ℕ) :=
  letI := ρ.mulAction
  letI := Fintype.ofFinite
    (MulAction.orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n))
  (Finset.univ : Finset
      (MulAction.orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n))).val.map
    fun ω ↦
      let F := IntermediateField.fixedField
        (MulAction.stabilizer Gal(SeparableClosure K/K) ω.out)
      (F.inertiaDegree, Module.finrank K F / F.inertiaDegree)

/-- Computing `splittingSymbol` with any `Fintype` instance on the orbit space. -/
theorem splittingSymbol_eq_map_univ (ρ : GaloisSet K n)
    [Fintype (letI := ρ.mulAction; MulAction.orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n))] :
    ρ.splittingSymbol =
      letI := ρ.mulAction
      (Finset.univ : Finset
          (MulAction.orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n))).val.map
        fun ω ↦
          let F := IntermediateField.fixedField
            (MulAction.stabilizer Gal(SeparableClosure K/K) ω.out)
          (F.inertiaDegree, Module.finrank K F / F.inertiaDegree) := by
  let := ρ.mulAction
  rw [splittingSymbol]
  congr 1
  exact congrArg Finset.val (congrArg (@Finset.univ _) (Subsingleton.elim _ _))

/-- Equivariant bijections preserve the splitting symbol of labelled Galois sets. -/
theorem splittingSymbol_eq_of_equiv {m : ℕ} (ρ : GaloisSet K n) (τ : GaloisSet K m)
    (e : Fin n ≃ Fin m)
    (he : ∀ (σ : Gal(SeparableClosure K/K)) (i : Fin n),
      e (ρ.val σ i) = τ.val σ (e i)) :
    ρ.splittingSymbol = τ.splittingSymbol := by
  let := ρ.mulAction
  let := τ.mulAction
  let := Fintype.ofFinite (MulAction.orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n))
  let := Fintype.ofFinite (MulAction.orbitRel.Quotient Gal(SeparableClosure K/K) (Fin m))
  let E := MulAction.orbitRelQuotientCongr (MulEquiv.refl Gal(SeparableClosure K/K)) e he
  rw [splittingSymbol_eq_map_univ, splittingSymbol_eq_map_univ]
  have huniv : (Finset.univ.val.map E : Multiset _) = Finset.univ.val :=
    (Finset.map_val E.toEmbedding Finset.univ).symm.trans
      (congrArg Finset.val (Finset.map_univ_equiv E))
  rw [← huniv, Multiset.map_map]
  refine Multiset.map_congr rfl fun ω _ ↦ ?_
  have hE : (Quotient.mk'' (e ω.out) :
      MulAction.orbitRel.Quotient Gal(SeparableClosure K/K) (Fin m)) = E ω := by
    rw [← MulAction.orbitRelQuotientCongr_mk (MulEquiv.refl _) e he, Quotient.out_eq']
  exact (inertiaDegree_finrank_fixedField_stabilizer_out_of_injective (K := K) e e.injective he
    hE).symm

/-- Relabelling a Galois set does not change its splitting symbol. -/
@[simp]
theorem splittingSymbol_smul (ρ : GaloisSet K n) (e : Equiv.Perm (Fin n)) :
    (e • ρ).splittingSymbol = ρ.splittingSymbol :=
  (ρ.splittingSymbol_eq_of_equiv (e • ρ) e (by simp)).symm

/-- The splitting symbol is additive on disjoint unions of labelled Galois sets. -/
@[simp]
theorem splittingSymbol_sumCongr {n₁ n₂ : ℕ} (e : Fin n₁ ⊕ Fin n₂ ≃ Fin n)
    (ρ₁ : GaloisSet K n₁) (ρ₂ : GaloisSet K n₂) :
    (sumCongr e ρ₁ ρ₂).splittingSymbol = ρ₁.splittingSymbol + ρ₂.splittingSymbol := by
  let := ρ₁.mulAction
  let := ρ₂.mulAction
  let := (sumCongr e ρ₁ ρ₂).mulAction
  let := Fintype.ofFinite (MulAction.orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n₁))
  let := Fintype.ofFinite (MulAction.orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n₂))
  let := Fintype.ofFinite (MulAction.orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n))
  let E : MulAction.orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n₁) ⊕
      MulAction.orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n₂) ≃
      MulAction.orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n) :=
    MulAction.orbitRelQuotientSumEquiv.symm.trans
      (MulAction.orbitRelQuotientCongr (MulEquiv.refl _) e
        (fun σ x ↦ by simpa using sumCongr_map_smul e ρ₁ ρ₂ σ x))
  rw [splittingSymbol_eq_map_univ, splittingSymbol_eq_map_univ, splittingSymbol_eq_map_univ]
  have huniv : (Finset.univ.val.map E : Multiset _) = Finset.univ.val :=
    (Finset.map_val E.toEmbedding Finset.univ).symm.trans
      (congrArg Finset.val (Finset.map_univ_equiv E))
  rw [← huniv, ← Finset.univ_disjSum_univ, Finset.val_disjSum, Multiset.map_map,
    Multiset.map_disjSum]
  congr 1
  · refine Multiset.map_congr rfl fun ω _ ↦ ?_
    have hE : (Quotient.mk'' (e (Sum.inl ω.out)) :
        MulAction.orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n)) = E (Sum.inl ω) := by
      dsimp only [E, Equiv.trans_apply]
      conv_rhs => rw [← Quotient.out_eq' ω]
      rw [MulAction.orbitRelQuotientSumEquiv_symm_inl_mk, MulAction.orbitRelQuotientCongr_mk]
    exact inertiaDegree_finrank_fixedField_stabilizer_out_of_injective (K := K)
      (fun i ↦ e (Sum.inl i)) (e.injective.comp Sum.inl_injective)
      (fun σ i ↦ (sumCongr_val_apply_inl e ρ₁ ρ₂ σ i).symm) hE
  · refine Multiset.map_congr rfl fun ω _ ↦ ?_
    have hE : (Quotient.mk'' (e (Sum.inr ω.out)) :
        MulAction.orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n)) = E (Sum.inr ω) := by
      dsimp only [E, Equiv.trans_apply]
      conv_rhs => rw [← Quotient.out_eq' ω]
      rw [MulAction.orbitRelQuotientSumEquiv_symm_inr_mk, MulAction.orbitRelQuotientCongr_mk]
    exact inertiaDegree_finrank_fixedField_stabilizer_out_of_injective (K := K)
      (fun j ↦ e (Sum.inr j)) (e.injective.comp Sum.inr_injective)
      (fun σ j ↦ (sumCongr_val_apply_inr e ρ₁ ρ₂ σ j).symm) hE

/-- The empty Galois set has the empty splitting symbol. -/
@[simp]
theorem splittingSymbol_zero (ρ : GaloisSet K 0) : ρ.splittingSymbol = 0 := by
  let := ρ.mulAction
  have : IsEmpty (MulAction.orbitRel.Quotient Gal(SeparableClosure K/K) (Fin 0)) :=
    ⟨Quotient.ind' fun i ↦ i.elim0⟩
  let := Fintype.ofIsEmpty (α := MulAction.orbitRel.Quotient Gal(SeparableClosure K/K) (Fin 0))
  rw [splittingSymbol_eq_map_univ]
  simp

/-- The trivial Galois set of size `n` has splitting symbol `n` copies of `(1, 1)`. -/
@[simp]
theorem splittingSymbol_trivial (n : ℕ) :
    (trivial K n).splittingSymbol = Multiset.replicate n (1, 1) := by
  let := (trivial K n).mulAction
  let := Fintype.ofFinite (MulAction.orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n))
  rw [splittingSymbol_eq_map_univ]
  have hconst : ∀ ω : MulAction.orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n),
      (let F := IntermediateField.fixedField
          (MulAction.stabilizer Gal(SeparableClosure K/K) ω.out);
        (F.inertiaDegree, Module.finrank K F / F.inertiaDegree)) = (1, 1) := fun ω ↦ by
    simp [fixedField_stabilizer_trivial]
  rw [Multiset.map_congr rfl fun ω _ ↦ hconst ω, Multiset.map_const', Finset.card_val,
    Finset.card_univ]
  congr 1
  have hbij : Function.Bijective
      (Quotient.mk'' : Fin n → MulAction.orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n)) :=
    ⟨fun i j h ↦ by
      obtain ⟨σ, hσ⟩ := MulAction.mem_orbit_iff.1 (MulAction.orbitRel_apply.1 (Quotient.exact' h))
      simpa using hσ.symm, Quotient.mk''_surjective⟩
  rw [← Fintype.card_of_bijective hbij, Fintype.card_fin]

/-- The splitting symbol of a transitive nonempty Galois set is the singleton of the `(f, e)`
pair of the fixed field of any point stabilizer. -/
theorem splittingSymbol_of_isTransitive (ρ : GaloisSet K n) (hρ : ρ.IsTransitive) (i : Fin n) :
    ρ.splittingSymbol =
      letI := ρ.mulAction
      let F := IntermediateField.fixedField
        (MulAction.stabilizer Gal(SeparableClosure K/K) i)
      {(F.inertiaDegree, Module.finrank K F / F.inertiaDegree)} := by
  let := ρ.mulAction
  have : MulAction.IsPretransitive Gal(SeparableClosure K/K) (Fin n) := ρ.isTransitive_def.1 hρ
  have : Nonempty (Fin n) := ⟨i⟩
  let := ((MulAction.pretransitive_iff_unique_quotient_of_nonempty
    Gal(SeparableClosure K/K) (Fin n)).mp inferInstance).some
  rw [splittingSymbol_eq_map_univ, Finset.univ_unique, Finset.singleton_val,
    Multiset.map_singleton]
  have hq : (Quotient.mk'' i :
      MulAction.orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n)) = default :=
    Subsingleton.elim _ _
  rw [inertiaDegree_finrank_fixedField_stabilizer_out (K := K) hq]

/-- A Galois set whose splitting symbol is a singleton is transitive. -/
theorem isTransitive_of_splittingSymbol_eq_singleton {ρ : GaloisSet K n} {x : ℕ × ℕ}
    (h : ρ.splittingSymbol = {x}) : ρ.IsTransitive := by
  let := ρ.mulAction
  let := Fintype.ofFinite (MulAction.orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n))
  have hcard :
      Fintype.card (MulAction.orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n)) = 1 := by
    have hc := congrArg Multiset.card h
    rw [splittingSymbol_eq_map_univ] at hc
    simpa using hc
  have : Subsingleton (MulAction.orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n)) :=
    Fintype.card_le_one_iff_subsingleton.1 hcard.le
  exact ρ.isTransitive_def.2 ((MulAction.pretransitive_iff_subsingleton_quotient _ _).2 this)

/-- A Galois set of size `f * e` (with `0 < f`, `0 < e`) has splitting symbol `{(f, e)}` exactly
when it is transitive and the fixed field of the stabilizer of `0` has residue degree `f`. -/
theorem splittingSymbol_eq_singleton_iff {f e : ℕ} (hf : 0 < f) (he : 0 < e)
    (ρ : GaloisSet K (f * e)) :
    ρ.splittingSymbol = {(f, e)} ↔
      ρ.IsTransitive ∧
        (letI := ρ.mulAction
        (IntermediateField.fixedField
          (MulAction.stabilizer Gal(SeparableClosure K/K)
            (⟨0, mul_pos hf he⟩ : Fin (f * e)))).inertiaDegree = f) := by
  constructor
  · intro h
    have htrans := isTransitive_of_splittingSymbol_eq_singleton h
    refine ⟨htrans, ?_⟩
    rw [splittingSymbol_of_isTransitive ρ htrans ⟨0, mul_pos hf he⟩, Multiset.singleton_inj] at h
    exact congrArg Prod.fst h
  · rintro ⟨htrans, hf_eq⟩
    rw [splittingSymbol_of_isTransitive ρ htrans ⟨0, mul_pos hf he⟩]
    let := ρ.mulAction
    have hdeg := ρ.finrank_fixedField_stabilizer_of_isTransitive htrans ⟨0, mul_pos hf he⟩
    simp only [hf_eq, hdeg, Nat.mul_div_cancel_left e hf]

/-- Every factor `(f, e)` in the splitting symbol of a Galois set has positive residue degree and
positive ramification index. -/
theorem pos_of_mem_splittingSymbol (ρ : GaloisSet K n) {x : ℕ × ℕ} (hx : x ∈ ρ.splittingSymbol) :
    0 < x.1 ∧ 0 < x.2 := by
  let := ρ.mulAction
  let := Fintype.ofFinite (MulAction.orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n))
  rw [splittingSymbol_eq_map_univ] at hx
  obtain ⟨ω, -, rfl⟩ := Multiset.mem_map.1 hx
  have := ρ.finiteDimensional_fixedField_stabilizer ω.out
  set F := IntermediateField.fixedField (MulAction.stabilizer Gal(SeparableClosure K/K) ω.out)
  refine ⟨F.inertiaDegree_pos, Nat.div_pos ?_ F.inertiaDegree_pos⟩
  exact Nat.le_of_dvd Module.finrank_pos F.inertiaDegree_dvd_finrank

/-- The degrees `f * e` of the factors of the splitting symbol sum to the size `n` of the Galois
set. -/
theorem sum_map_mul_splittingSymbol (ρ : GaloisSet K n) :
    (ρ.splittingSymbol.map fun x ↦ x.1 * x.2).sum = n := by
  let := ρ.mulAction
  let := Fintype.ofFinite (MulAction.orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n))
  classical
  rw [splittingSymbol_eq_map_univ, Multiset.map_map]
  have hterm : ∀ ω : MulAction.orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n),
      ((fun x : ℕ × ℕ ↦ x.1 * x.2) ∘ fun ω ↦
        let F := IntermediateField.fixedField
          (MulAction.stabilizer Gal(SeparableClosure K/K) ω.out)
        (F.inertiaDegree, Module.finrank K F / F.inertiaDegree)) ω =
      (Finset.univ.filter fun i : Fin n ↦
        (Quotient.mk'' i :
          MulAction.orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n)) = ω).card := by
    intro ω
    dsimp only [Function.comp_apply]
    rw [Nat.mul_div_cancel' (IntermediateField.inertiaDegree_dvd_finrank _),
      ρ.finrank_fixedField_stabilizer]
    have hset : (MulAction.orbit Gal(SeparableClosure K/K) ω.out : Set (Fin n)) =
        ((Finset.univ.filter fun i : Fin n ↦
          (Quotient.mk'' i :
            MulAction.orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n)) = ω) : Set (Fin n)) := by
      ext i
      rw [← MulAction.orbitRel.Quotient.orbit_eq_orbit_out ω Quotient.out_eq',
        MulAction.orbitRel.Quotient.mem_orbit]
      simp
    rw [hset, Nat.card_coe_set_eq, Set.ncard_coe_finset]
  rw [Multiset.map_congr rfl fun ω _ ↦ hterm ω, ← Finset.sum_eq_multiset_sum,
    ← Finset.card_eq_sum_card_fiberwise (f := (Quotient.mk'' : Fin n →
      MulAction.orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n))) (fun _ _ ↦ Finset.mem_univ _),
    Finset.card_univ, Fintype.card_fin]

/-- The multiplicity of `x` in `ρ.splittingSymbol` is the number of orbits of `ρ` whose stabilizer
fixed field has `(f, e) = x`. -/
theorem count_splittingSymbol (ρ : GaloisSet K n) (x : ℕ × ℕ) :
    ρ.splittingSymbol.count x =
      letI := ρ.mulAction
      Nat.card {ω : MulAction.orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n) //
        let F := IntermediateField.fixedField
          (MulAction.stabilizer Gal(SeparableClosure K/K) ω.out)
        (F.inertiaDegree, Module.finrank K F / F.inertiaDegree) = x} := by
  let := ρ.mulAction
  let := Fintype.ofFinite (MulAction.orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n))
  classical
  rw [splittingSymbol_eq_map_univ, Multiset.count_map, ← Finset.filter_val, Finset.card_val,
    Nat.card_eq_fintype_card, Fintype.card_subtype]
  congr 1
  ext ω
  simp [eq_comm]

/-- The number of factors in `ρ.splittingSymbol` is the number of orbits of `ρ`. -/
theorem card_splittingSymbol (ρ : GaloisSet K n) :
    ρ.splittingSymbol.card =
      letI := ρ.mulAction
      Nat.card (MulAction.orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n)) := by
  let := ρ.mulAction
  let := Fintype.ofFinite (MulAction.orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n))
  rw [splittingSymbol_eq_map_univ, Multiset.card_map, Finset.card_val, Finset.card_univ,
    Nat.card_eq_fintype_card]

/-- A Galois set has empty splitting symbol if and only if its size is zero. -/
@[simp]
theorem splittingSymbol_eq_zero_iff (ρ : GaloisSet K n) :
    ρ.splittingSymbol = 0 ↔ n = 0 := by
  constructor
  · intro h
    have hsum := ρ.sum_map_mul_splittingSymbol
    rw [h, Multiset.map_zero, Multiset.sum_zero] at hsum
    exact hsum.symm
  · rintro rfl
    exact splittingSymbol_zero ρ

end GaloisSet

/-! ### Transitive mass by residue degree -/

private theorem tsum_splittingSymbol_singleton (f e : ℕ) (hf : 0 < f) (he : 0 < e) :
    ∑' ρ : {ρ : GaloisSet K (f * e) // ρ.splittingSymbol = {(f, e)}},
        1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ ρ.1.discriminantExponent =
      ((f * e - 1).factorial : ℝ≥0∞) *
        ∑' L : {L : IntermediateField K (SeparableClosure K) //
            Module.finrank K L = f * e ∧ L.inertiaDegree = f},
          1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ L.1.discriminantExponent := by
  classical
  let i₀ : Fin (f * e) := ⟨0, mul_pos hf he⟩
  let g : IntermediateField K (SeparableClosure K) → ℝ≥0∞ :=
    fun L ↦ if L.inertiaDegree = f then 1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ L.discriminantExponent else 0
  have hsum : ∑' ρ : {ρ : GaloisSet K (f * e) // ρ.splittingSymbol = {(f, e)}},
        1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ ρ.1.discriminantExponent =
      ∑' ρ : {ρ : GaloisSet K (f * e) // ρ.IsTransitive},
        letI := ρ.1.mulAction
        g (IntermediateField.fixedField
          (MulAction.stabilizer Gal(SeparableClosure K/K) i₀)) := by
    let s₁ : Set {ρ : GaloisSet K (f * e) // ρ.IsTransitive} :=
      {ρ | letI := ρ.1.mulAction
        (IntermediateField.fixedField
          (MulAction.stabilizer Gal(SeparableClosure K/K) i₀)).inertiaDegree = f}
    let e₁ : {ρ : GaloisSet K (f * e) // ρ.splittingSymbol = {(f, e)}} ≃ s₁ :=
      { toFun ρ :=
          have h := (GaloisSet.splittingSymbol_eq_singleton_iff hf he ρ.1).1 ρ.2
          ⟨⟨ρ.1, h.1⟩, h.2⟩
        invFun ρ := ⟨ρ.1.1, (GaloisSet.splittingSymbol_eq_singleton_iff hf he ρ.1.1).2 ⟨ρ.1.2, ρ.2⟩⟩
        left_inv _ := rfl
        right_inv _ := rfl }
    rw [← tsum_subtype_eq_of_support_subset (s := s₁)
      (fun ρ hρ ↦ by by_contra h; exact hρ (ite_eq_right_iff.2 fun heq ↦ (h heq).elim)),
      ← e₁.tsum_eq]
    refine tsum_congr fun ρ ↦ ?_
    have h := (GaloisSet.splittingSymbol_eq_singleton_iff hf he ρ.1).1 ρ.2
    rw [ρ.1.discriminantExponent_of_isTransitive h.1 i₀]
    simp only [g, i₀, h.2, ↓reduceIte]
  have hsub : ∑' L : {L : IntermediateField K (SeparableClosure K) // Module.finrank K L = f * e},
        g L.1 =
      ∑' L : {L : IntermediateField K (SeparableClosure K) //
          Module.finrank K L = f * e ∧ L.inertiaDegree = f},
        1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ L.1.discriminantExponent := by
    let s₂ : Set {L : IntermediateField K (SeparableClosure K) // Module.finrank K L = f * e} :=
      {L | L.1.inertiaDegree = f}
    let e₂ : {L : IntermediateField K (SeparableClosure K) //
        Module.finrank K L = f * e ∧ L.inertiaDegree = f} ≃ s₂ :=
      { toFun L := ⟨⟨L.1, L.2.1⟩, L.2.2⟩
        invFun L := ⟨L.1.1, L.1.2, L.2⟩
        left_inv _ := rfl
        right_inv _ := rfl }
    rw [← tsum_subtype_eq_of_support_subset (s := s₂)
      (fun L hL ↦ by by_contra h; exact hL (ite_eq_right_iff.2 fun heq ↦ (h heq).elim)),
      ← e₂.tsum_eq]
    exact tsum_congr fun L ↦ by simp [g, L.2.2, e₂]
  rw [hsum, GaloisSet.tsum_isTransitive i₀ g, hsub]

/-- **The transitive mass by residue degree**: the Galois sets of size `f * e` with splitting
symbol `{(f, e)}` have mass `q ^ (-f(e - 1)) / f`. -/
theorem etaleMass_isTransitive_splittingSymbol (f e : ℕ) (hf : 0 < f) (he : 0 < e) :
    ((f * e).factorial : ℝ≥0∞)⁻¹ *
        ∑' ρ : {ρ : GaloisSet K (f * e) // ρ.splittingSymbol = {(f, e)}},
          1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ ρ.1.discriminantExponent =
      1 / ((f : ℝ≥0∞) * (Nat.card 𝓀[K] : ℝ≥0∞) ^ (f * (e - 1))) := by
  rw [tsum_splittingSymbol_singleton f e hf he, tsum_inertiaDegree_eq hf.ne' e]
  have hfac : (f * e).factorial = f * e * (f * e - 1).factorial :=
    (Nat.mul_factorial_pred (mul_pos hf he).ne').symm
  have hfe : ((f * e - 1).factorial : ℝ≥0∞) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  have he0 : (e : ℝ≥0∞) ≠ 0 := by exact_mod_cast he.ne'
  rw [hfac, Nat.cast_mul, Nat.cast_mul, one_div, div_eq_mul_inv,
    ENNReal.mul_inv (Or.inr (by simp)) (Or.inl (ENNReal.mul_ne_top (by simp) (by simp))),
    ENNReal.mul_inv (Or.inr (by simp)) (Or.inl (by simp)),
    ENNReal.mul_inv (Or.inr (ENNReal.pow_ne_top (by simp))) (Or.inl (by simp))]
  calc (f : ℝ≥0∞)⁻¹ * (e : ℝ≥0∞)⁻¹ * ((f * e - 1).factorial : ℝ≥0∞)⁻¹ *
        (((f * e - 1).factorial : ℝ≥0∞) * ((e : ℝ≥0∞) *
          ((Nat.card 𝓀[K] : ℝ≥0∞) ^ (f * (e - 1)))⁻¹))
      = (f : ℝ≥0∞)⁻¹ * ((e : ℝ≥0∞)⁻¹ * (e : ℝ≥0∞)) *
          (((f * e - 1).factorial : ℝ≥0∞)⁻¹ * ((f * e - 1).factorial : ℝ≥0∞)) *
          ((Nat.card 𝓀[K] : ℝ≥0∞) ^ (f * (e - 1)))⁻¹ := by ring
    _ = (f : ℝ≥0∞)⁻¹ * ((Nat.card 𝓀[K] : ℝ≥0∞) ^ (f * (e - 1)))⁻¹ := by
        rw [ENNReal.inv_mul_cancel he0 (by simp), ENNReal.inv_mul_cancel hfe (by simp),
          mul_one, mul_one]

/-! ### Mass formula by splitting type -/

section SplittingType

/-- A labelled Galois set with splitting symbol `σ` paired with an orbit of splitting type `x`. -/
private abbrev MarkedOrbit (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] {n : ℕ} (σ : Multiset (ℕ × ℕ)) (x : ℕ × ℕ) :=
  Σ ρ : {ρ : GaloisSet K n // ρ.splittingSymbol = σ},
    letI := ρ.1.mulAction
    {ω : MulAction.orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n) //
      let F := IntermediateField.fixedField
        (MulAction.stabilizer Gal(SeparableClosure K/K) ω.out)
      (F.inertiaDegree, Module.finrank K F / F.inertiaDegree) = x}

/-- The underlying finset of labels belonging to the marked orbit. -/
private def markedOrbitFinset {n : ℕ} {σ : Multiset (ℕ × ℕ)} {x : ℕ × ℕ}
    (p : MarkedOrbit K (n := n) σ x) : Finset (Fin n) := by
  classical
  let := p.1.1.mulAction
  exact Finset.univ.filter fun i : Fin n ↦
    (Quotient.mk'' i : MulAction.orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n)) = p.2.1

private theorem card_markedOrbitFinset {n : ℕ} {σ : Multiset (ℕ × ℕ)} {x : ℕ × ℕ}
    (p : MarkedOrbit K (n := n) σ x) :
    (markedOrbitFinset p).card = x.1 * x.2 := by
  classical
  let := p.1.1.mulAction
  have hset : (MulAction.orbit Gal(SeparableClosure K/K) p.2.1.out : Set (Fin n)) =
      (markedOrbitFinset p : Set (Fin n)) := by
    ext i
    rw [← MulAction.orbitRel.Quotient.orbit_eq_orbit_out p.2.1 Quotient.out_eq',
      MulAction.orbitRel.Quotient.mem_orbit]
    simp [markedOrbitFinset]
  have hcard : (markedOrbitFinset p).card =
      Module.finrank K (IntermediateField.fixedField
        (MulAction.stabilizer Gal(SeparableClosure K/K) p.2.1.out)) := by
    rw [p.1.1.finrank_fixedField_stabilizer, hset, Nat.card_coe_set_eq, Set.ncard_coe_finset]
  have hx1 : (IntermediateField.fixedField
      (MulAction.stabilizer Gal(SeparableClosure K/K) p.2.1.out)).inertiaDegree = x.1 :=
    congrArg Prod.fst p.2.2
  have hx2 : Module.finrank K (IntermediateField.fixedField
      (MulAction.stabilizer Gal(SeparableClosure K/K) p.2.1.out)) /
      (IntermediateField.fixedField
        (MulAction.stabilizer Gal(SeparableClosure K/K) p.2.1.out)).inertiaDegree = x.2 :=
    congrArg Prod.snd p.2.2
  rw [hcard, ← hx1, ← hx2, Nat.mul_div_cancel' (IntermediateField.inertiaDegree_dvd_finrank _)]

private theorem pair_sumCongr_inl {n₁ n₂ n : ℕ} (e : Fin n₁ ⊕ Fin n₂ ≃ Fin n)
    (ρ₁ : GaloisSet K n₁) (ρ₂ : GaloisSet K n₂) (i : Fin n₁) :
    (letI := (GaloisSet.sumCongr e ρ₁ ρ₂).mulAction;
      let F := IntermediateField.fixedField
        (MulAction.stabilizer Gal(SeparableClosure K/K) (e (Sum.inl i)));
      (F.inertiaDegree, Module.finrank K F / F.inertiaDegree)) =
    (letI := ρ₁.mulAction;
      let F := IntermediateField.fixedField
        (MulAction.stabilizer Gal(SeparableClosure K/K) i);
      (F.inertiaDegree, Module.finrank K F / F.inertiaDegree)) := by
  let := ρ₁.mulAction
  let := (GaloisSet.sumCongr e ρ₁ ρ₂).mulAction
  have hstab : MulAction.stabilizer Gal(SeparableClosure K/K) (e (Sum.inl i)) =
      MulAction.stabilizer Gal(SeparableClosure K/K) i := by
    ext σ
    simp [MulAction.mem_stabilizer_iff]
  dsimp only
  rw [hstab]

private theorem finSumEquivOfFinset_mem_iff {n₁ n₂ n : ℕ} (S : Finset (Fin n))
    (hS : S.card = n₁) (hSc : Sᶜ.card = n₂) (i : Fin n) :
    (∃ j : Fin n₁, finSumEquivOfFinset hS hSc (Sum.inl j) = i) ↔ i ∈ S := by
  rw [← Finset.mem_coe, ← Finset.range_orderEmbOfFin S hS, Set.mem_range]
  simp

private def markedOrbitFiberToFun {n₁ n₂ n : ℕ} {x : ℕ × ℕ} {τ : Multiset (ℕ × ℕ)}
    (hn₁ : 0 < n₁) (S : Finset (Fin n)) (hS : S.card = n₁) (hSc : Sᶜ.card = n₂)
    (p : {ρ₁ : GaloisSet K n₁ // ρ₁.splittingSymbol = {x}} ×
      {ρ₂ : GaloisSet K n₂ // ρ₂.splittingSymbol = τ}) :
    {q : MarkedOrbit K (n := n) (x ::ₘ τ) x // markedOrbitFinset q = S} := by
  classical
  let eS : Fin n₁ ⊕ Fin n₂ ≃ Fin n := finSumEquivOfFinset hS hSc
  let htrans : p.1.1.IsTransitive := GaloisSet.isTransitive_of_splittingSymbol_eq_singleton p.1.2
  let hsym : (GaloisSet.sumCongr eS p.1.1 p.2.1).splittingSymbol = x ::ₘ τ := by
    rw [GaloisSet.splittingSymbol_sumCongr, p.1.2, p.2.2, Multiset.singleton_add]
  let ω : letI := (GaloisSet.sumCongr eS p.1.1 p.2.1).mulAction
      MulAction.orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n) :=
    letI := (GaloisSet.sumCongr eS p.1.1 p.2.1).mulAction
    Quotient.mk'' (eS (Sum.inl ⟨0, hn₁⟩))
  have hpair : (letI := (GaloisSet.sumCongr eS p.1.1 p.2.1).mulAction;
      let F := IntermediateField.fixedField
        (MulAction.stabilizer Gal(SeparableClosure K/K) ω.out);
      (F.inertiaDegree, Module.finrank K F / F.inertiaDegree)) = x := by
    let := (GaloisSet.sumCongr eS p.1.1 p.2.1).mulAction
    rw [inertiaDegree_finrank_fixedField_stabilizer_out (K := K) (x := eS (Sum.inl ⟨0, hn₁⟩)) rfl,
      pair_sumCongr_inl eS p.1.1 p.2.1 ⟨0, hn₁⟩]
    have h1 := GaloisSet.splittingSymbol_of_isTransitive p.1.1 htrans ⟨0, hn₁⟩
    rw [p.1.2] at h1
    exact (Multiset.singleton_inj.1 h1).symm
  refine ⟨⟨⟨GaloisSet.sumCongr eS p.1.1 p.2.1, hsym⟩, ⟨ω, hpair⟩⟩, ?_⟩
  ext i
  simp only [markedOrbitFinset, Finset.mem_filter, Finset.mem_univ, true_and]
  exact (GaloisSet.mk_eq_mk_sumCongr_inl_iff eS p.1.1 htrans p.2.1 ⟨0, hn₁⟩ i).trans
    (finSumEquivOfFinset_mem_iff S hS hSc i)

/-- Fixing the underlying finset `S` of the marked orbit identifies the fibre over `S` with pairs
of a Galois set of symbol `{x}` on `Fin n₁` and a Galois set of symbol `τ` on `Fin n₂`. -/
private def markedOrbitFiberEquiv {n₁ n₂ n : ℕ} {x : ℕ × ℕ} {τ : Multiset (ℕ × ℕ)}
    (hx₁ : 0 < x.1) (hx₂ : 0 < x.2) (hn₁ : x.1 * x.2 = n₁) (hn : n₁ + n₂ = n)
    (S : {S : Finset (Fin n) // S.card = n₁}) :
    {ρ₁ : GaloisSet K n₁ // ρ₁.splittingSymbol = {x}} ×
        {ρ₂ : GaloisSet K n₂ // ρ₂.splittingSymbol = τ} ≃
      {p : MarkedOrbit K (n := n) (x ::ₘ τ) x // markedOrbitFinset p = S.1} := by
  classical
  have hn₁_pos : 0 < n₁ := hn₁ ▸ mul_pos hx₁ hx₂
  have hSc : S.1ᶜ.card = n₂ := by
    rw [Finset.card_compl, Fintype.card_fin, S.2]
    omega
  let eS : Fin n₁ ⊕ Fin n₂ ≃ Fin n := finSumEquivOfFinset S.2 hSc
  refine Equiv.ofBijective (markedOrbitFiberToFun hn₁_pos S.1 S.2 hSc) ⟨?_, ?_⟩
  · rintro ⟨⟨ρ₁, hρ₁⟩, ⟨ρ₂, hρ₂⟩⟩ ⟨⟨τ₁, hτ₁⟩, ⟨τ₂, hτ₂⟩⟩ h
    have hsum : GaloisSet.sumCongr eS ρ₁ ρ₂ = GaloisSet.sumCongr eS τ₁ τ₂ :=
      congrArg (fun p ↦ p.1.1.1) h
    obtain ⟨rfl, rfl⟩ := (GaloisSet.sumCongr_eq_iff eS ρ₁ τ₁ ρ₂ τ₂).1 hsum
    rfl
  · rintro ⟨⟨⟨ρ, hρ⟩, ⟨ω, hω⟩⟩, hS⟩
    have hcond : letI := ρ.mulAction
        ∀ i : Fin n,
          (Quotient.mk'' i : MulAction.orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n)) = ω ↔
            ∃ j : Fin n₁, eS (Sum.inl j) = i := fun i ↦ by
      rw [finSumEquivOfFinset_mem_iff S.1 S.2 hSc, ← hS]
      simp [markedOrbitFinset]
    obtain ⟨⟨⟨ρ₁, htrans⟩, ρ₂⟩, hsplit⟩ :=
      (GaloisSet.orbitSplitEquiv eS hn₁_pos).surjective ⟨⟨ρ, ω⟩, hcond⟩
    have hsum : GaloisSet.sumCongr eS ρ₁ ρ₂ = ρ :=
      (GaloisSet.orbitSplitEquiv_apply_fst eS hn₁_pos (⟨ρ₁, htrans⟩, ρ₂)).symm.trans
        (congrArg (fun q ↦ q.1.1) hsplit)
    subst hsum
    have hωeq : (letI := (GaloisSet.sumCongr eS ρ₁ ρ₂).mulAction
        (Quotient.mk'' (eS (Sum.inl ⟨0, hn₁_pos⟩)) :
          MulAction.orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n))) = ω :=
      (hcond (eS (Sum.inl ⟨0, hn₁_pos⟩))).2 ⟨⟨0, hn₁_pos⟩, rfl⟩
    have hρ₁ : ρ₁.splittingSymbol = {x} := by
      let := (GaloisSet.sumCongr eS ρ₁ ρ₂).mulAction
      rw [GaloisSet.splittingSymbol_of_isTransitive ρ₁ htrans ⟨0, hn₁_pos⟩, Multiset.singleton_inj,
        ← pair_sumCongr_inl eS ρ₁ ρ₂ ⟨0, hn₁_pos⟩,
        ← inertiaDegree_finrank_fixedField_stabilizer_out (K := K) hωeq]
      exact hω
    have hρ₂ : ρ₂.splittingSymbol = τ := by
      have h1 := hρ
      rw [GaloisSet.splittingSymbol_sumCongr, hρ₁, Multiset.singleton_add] at h1
      exact (Multiset.cons_inj_right x).1 h1
    refine ⟨(⟨ρ₁, hρ₁⟩, ⟨ρ₂, hρ₂⟩), Subtype.ext ?_⟩
    exact Sigma.ext (Subtype.ext rfl) (heq_of_eq (Subtype.ext hωeq))

private theorem tsum_markedOrbit_eq_count_mul {n : ℕ} (x : ℕ × ℕ) (τ : Multiset (ℕ × ℕ)) :
    ∑' p : MarkedOrbit K (n := n) (x ::ₘ τ) x,
        1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ p.1.1.discriminantExponent =
      (((x ::ₘ τ).count x : ℕ) : ℝ≥0∞) *
        ∑' ρ : {ρ : GaloisSet K n // ρ.splittingSymbol = x ::ₘ τ},
          1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ ρ.1.discriminantExponent := by
  rw [tsum_sigma', ← ENNReal.tsum_mul_left]
  refine tsum_congr fun ρ ↦ ?_
  dsimp only
  rw [ENNReal.tsum_const, ENat.card_eq_coe_natCard, ENat.toENNReal_coe,
    ← GaloisSet.count_splittingSymbol, ρ.2]

private theorem tsum_markedOrbit_eq_choose_mul
    {n₁ n₂ n : ℕ} {x : ℕ × ℕ} {τ : Multiset (ℕ × ℕ)}
    (hx₁ : 0 < x.1) (hx₂ : 0 < x.2) (hn₁ : x.1 * x.2 = n₁) (hn : n₁ + n₂ = n) :
    ∑' p : MarkedOrbit K (n := n) (x ::ₘ τ) x,
        1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ p.1.1.discriminantExponent =
      (n.choose n₁ : ℝ≥0∞) *
        ((∑' ρ₁ : {ρ₁ : GaloisSet K n₁ // ρ₁.splittingSymbol = {x}},
            1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ ρ₁.1.discriminantExponent) *
          ∑' ρ₂ : {ρ₂ : GaloisSet K n₂ // ρ₂.splittingSymbol = τ},
            1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ ρ₂.1.discriminantExponent) := by
  classical
  let ψ : MarkedOrbit K (n := n) (x ::ₘ τ) x → {S : Finset (Fin n) // S.card = n₁} :=
    fun p ↦ ⟨markedOrbitFinset p, (card_markedOrbitFinset p).trans hn₁⟩
  rw [← tsum_fiberwise _ ψ]
  have hfib : ∀ S : {S : Finset (Fin n) // S.card = n₁},
      ∑' p : ψ ⁻¹' {S}, 1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ p.1.1.1.discriminantExponent =
        (∑' ρ₁ : {ρ₁ : GaloisSet K n₁ // ρ₁.splittingSymbol = {x}},
            1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ ρ₁.1.discriminantExponent) *
          ∑' ρ₂ : {ρ₂ : GaloisSet K n₂ // ρ₂.splittingSymbol = τ},
            1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ ρ₂.1.discriminantExponent := by
    intro S
    let eF : {ρ₁ : GaloisSet K n₁ // ρ₁.splittingSymbol = {x}} ×
        {ρ₂ : GaloisSet K n₂ // ρ₂.splittingSymbol = τ} ≃ (ψ ⁻¹' {S}) :=
      (markedOrbitFiberEquiv (K := K) (τ := τ) hx₁ hx₂ hn₁ hn S).trans
        (Equiv.subtypeEquivRight fun p ↦ by
          simp only [Set.mem_preimage, Set.mem_singleton_iff, Subtype.ext_iff, ψ])
    rw [← eF.tsum_eq, tsum_prod']
    have hterm : ∀ (ρ₁ : {ρ₁ : GaloisSet K n₁ // ρ₁.splittingSymbol = {x}})
        (ρ₂ : {ρ₂ : GaloisSet K n₂ // ρ₂.splittingSymbol = τ}),
        1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ (eF (ρ₁, ρ₂)).1.1.1.discriminantExponent =
          (1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ ρ₁.1.discriminantExponent) *
            (1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ ρ₂.1.discriminantExponent) := by
      intro ρ₁ ρ₂
      have hd : (eF (ρ₁, ρ₂)).1.1.1.discriminantExponent =
          ρ₁.1.discriminantExponent + ρ₂.1.discriminantExponent :=
        GaloisSet.discriminantExponent_sumCongr _ ρ₁.1 ρ₂.1
      rw [hd, pow_add, one_div, one_div, one_div,
        ENNReal.mul_inv (Or.inr (ENNReal.pow_ne_top (by simp)))
          (Or.inl (ENNReal.pow_ne_top (by simp)))]
    simp_rw [hterm, ENNReal.tsum_mul_left, ENNReal.tsum_mul_right]
  simp_rw [hfib, ENNReal.tsum_const, ENat.card_eq_coe_natCard, ENat.toENNReal_coe,
    Nat.card_eq_fintype_card]
  congr 1
  have hcard : Fintype.card {S : Finset (Fin n) // S.card = n₁} = n.choose n₁ := by
    calc Fintype.card {S : Finset (Fin n) // S.card = n₁}
        = Fintype.card (Finset.powersetCard n₁ (Finset.univ : Finset (Fin n))) :=
          Fintype.card_congr (Equiv.subtypeEquivRight fun S ↦ by simp [Finset.mem_powersetCard])
      _ = n.choose n₁ := by
          rw [Fintype.card_coe, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
  exact_mod_cast hcard

private theorem inv_factorial_mul_choose {n₁ n₂ n : ℕ} (hn : n₁ + n₂ = n) :
    (n.factorial : ℝ≥0∞)⁻¹ * (n.choose n₁ : ℝ≥0∞) =
      (n₁.factorial : ℝ≥0∞)⁻¹ * (n₂.factorial : ℝ≥0∞)⁻¹ := by
  have hnat : n.choose n₁ * n₁.factorial * n₂.factorial = n.factorial := by
    rw [← hn, mul_right_comm]
    simpa [add_comm] using Nat.add_choose_mul_factorial_mul_factorial n₂ n₁
  have hcast : (n.choose n₁ : ℝ≥0∞) * (n₁.factorial : ℝ≥0∞) * (n₂.factorial : ℝ≥0∞) =
      (n.factorial : ℝ≥0∞) := by exact_mod_cast hnat
  have hc0 : (n.choose n₁ : ℝ≥0∞) ≠ 0 := by
    have : 0 < n.choose n₁ := Nat.choose_pos (by omega)
    exact_mod_cast this.ne'
  rw [← hcast,
    ENNReal.mul_inv (Or.inr (by simp)) (Or.inl (ENNReal.mul_ne_top (by simp) (by simp))),
    ENNReal.mul_inv (Or.inr (by simp)) (Or.inl (by simp))]
  calc (n.choose n₁ : ℝ≥0∞)⁻¹ * (n₁.factorial : ℝ≥0∞)⁻¹ * (n₂.factorial : ℝ≥0∞)⁻¹ *
        (n.choose n₁ : ℝ≥0∞)
      = ((n.choose n₁ : ℝ≥0∞)⁻¹ * (n.choose n₁ : ℝ≥0∞)) *
          ((n₁.factorial : ℝ≥0∞)⁻¹ * (n₂.factorial : ℝ≥0∞)⁻¹) := by ring
    _ = (n₁.factorial : ℝ≥0∞)⁻¹ * (n₂.factorial : ℝ≥0∞)⁻¹ := by
        rw [ENNReal.inv_mul_cancel hc0 (by simp), one_mul]

/-- Double-counting marked orbits of type `x` gives the recursion
`((x ::ₘ τ).count x) * W(x ::ₘ τ) = W({x}) * W(τ)` for the normalized splitting-type masses. -/
private theorem count_mul_etaleMass_splittingSymbol_cons
    {n₁ n₂ n : ℕ} {x : ℕ × ℕ} {τ : Multiset (ℕ × ℕ)}
    (hx₁ : 0 < x.1) (hx₂ : 0 < x.2) (hn₁ : x.1 * x.2 = n₁) (hn : n₁ + n₂ = n) :
    (((x ::ₘ τ).count x : ℕ) : ℝ≥0∞) *
      ((n.factorial : ℝ≥0∞)⁻¹ *
        ∑' ρ : {ρ : GaloisSet K n // ρ.splittingSymbol = x ::ₘ τ},
          1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ ρ.1.discriminantExponent) =
      ((n₁.factorial : ℝ≥0∞)⁻¹ *
        ∑' ρ₁ : {ρ₁ : GaloisSet K n₁ // ρ₁.splittingSymbol = {x}},
          1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ ρ₁.1.discriminantExponent) *
      ((n₂.factorial : ℝ≥0∞)⁻¹ *
        ∑' ρ₂ : {ρ₂ : GaloisSet K n₂ // ρ₂.splittingSymbol = τ},
          1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ ρ₂.1.discriminantExponent) := by
  have heq := congrArg ((n.factorial : ℝ≥0∞)⁻¹ * ·)
    ((tsum_markedOrbit_eq_count_mul (K := K) x τ).symm.trans
      (tsum_markedOrbit_eq_choose_mul (K := K) hx₁ hx₂ hn₁ hn))
  calc (((x ::ₘ τ).count x : ℕ) : ℝ≥0∞) *
        ((n.factorial : ℝ≥0∞)⁻¹ *
          ∑' ρ : {ρ : GaloisSet K n // ρ.splittingSymbol = x ::ₘ τ},
            1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ ρ.1.discriminantExponent)
      = (n.factorial : ℝ≥0∞)⁻¹ * ((((x ::ₘ τ).count x : ℕ) : ℝ≥0∞) *
          ∑' ρ : {ρ : GaloisSet K n // ρ.splittingSymbol = x ::ₘ τ},
            1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ ρ.1.discriminantExponent) := by ring
    _ = (n.factorial : ℝ≥0∞)⁻¹ * (n.choose n₁ : ℝ≥0∞) *
          ((∑' ρ₁ : {ρ₁ : GaloisSet K n₁ // ρ₁.splittingSymbol = {x}},
              1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ ρ₁.1.discriminantExponent) *
            ∑' ρ₂ : {ρ₂ : GaloisSet K n₂ // ρ₂.splittingSymbol = τ},
              1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ ρ₂.1.discriminantExponent) := by
        rw [heq, mul_assoc]
    _ = ((n₁.factorial : ℝ≥0∞)⁻¹ *
          ∑' ρ₁ : {ρ₁ : GaloisSet K n₁ // ρ₁.splittingSymbol = {x}},
            1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ ρ₁.1.discriminantExponent) *
        ((n₂.factorial : ℝ≥0∞)⁻¹ *
          ∑' ρ₂ : {ρ₂ : GaloisSet K n₂ // ρ₂.splittingSymbol = τ},
            1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ ρ₂.1.discriminantExponent) := by
        rw [inv_factorial_mul_choose hn]
        ring

end SplittingType

/-- **Mass formula for a fixed splitting type** ([Bhargava 2007, Prop. 2.1]): for a splitting
symbol `σ` of degree `n` (pairs `(f, e)` of positive integers with `∑ f * e = n`), the Galois
sets with symbol `σ` have mass `1 / (#Aut(σ) · q ^ (∑ f_i (e_i - 1)))`. -/
theorem etaleMass_splittingSymbol (n : ℕ) (σ : Multiset (ℕ × ℕ))
    (hσ : ∀ x ∈ σ, 0 < x.1 ∧ 0 < x.2) (hn : (σ.map fun x ↦ x.1 * x.2).sum = n) :
    (n.factorial : ℝ≥0∞)⁻¹ *
        ∑' ρ : {ρ : GaloisSet K n // ρ.splittingSymbol = σ},
          1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ ρ.1.discriminantExponent =
      1 / ((splittingSymbolAut σ : ℝ≥0∞) *
        (Nat.card 𝓀[K] : ℝ≥0∞) ^ splittingSymbolExponent σ) := by
  induction σ using Multiset.induction generalizing n with
  | empty =>
    simp only [Multiset.map_zero, Multiset.sum_zero] at hn
    subst hn
    rw [tsum_eq_single ⟨GaloisSet.trivial K 0, GaloisSet.splittingSymbol_zero _⟩
      (fun ρ hρ ↦ (hρ (Subtype.ext (Subsingleton.elim _ _))).elim)]
    simp
  | cons x τ ih =>
    have hx := hσ x (Multiset.mem_cons_self x τ)
    have hτ : ∀ y ∈ τ, 0 < y.1 ∧ 0 < y.2 := fun y hy ↦ hσ y (Multiset.mem_cons_of_mem hy)
    set n₁ := x.1 * x.2
    set n₂ := (τ.map fun y ↦ y.1 * y.2).sum
    have hsum : n₁ + n₂ = n := by simpa [n₁, n₂] using hn
    have hrec := count_mul_etaleMass_splittingSymbol_cons (K := K) (τ := τ) hx.1 hx.2 rfl hsum
    rw [etaleMass_isTransitive_splittingSymbol x.1 x.2 hx.1 hx.2, ih n₂ hτ rfl] at hrec
    have hc0 : (((x ::ₘ τ).count x : ℕ) : ℝ≥0∞) ≠ 0 := by
      exact_mod_cast (Multiset.count_pos.2 (Multiset.mem_cons_self x τ)).ne'
    have hden : (splittingSymbolAut (x ::ₘ τ) : ℝ≥0∞) *
          (Nat.card 𝓀[K] : ℝ≥0∞) ^ splittingSymbolExponent (x ::ₘ τ) =
        (((x ::ₘ τ).count x : ℕ) : ℝ≥0∞) *
          (((x.1 : ℝ≥0∞) * (Nat.card 𝓀[K] : ℝ≥0∞) ^ (x.1 * (x.2 - 1))) *
            ((splittingSymbolAut τ : ℝ≥0∞) *
              (Nat.card 𝓀[K] : ℝ≥0∞) ^ splittingSymbolExponent τ)) := by
      rw [splittingSymbolAut_cons, splittingSymbolExponent_cons, Nat.cast_mul, Nat.cast_mul,
        pow_add]
      ring
    have htop : ∀ a b : ℕ, (a : ℝ≥0∞) * (Nat.card 𝓀[K] : ℝ≥0∞) ^ b ≠ ⊤ :=
      fun _ _ ↦ ENNReal.mul_ne_top (by simp) (ENNReal.pow_ne_top (by simp))
    have hrhs : (((x ::ₘ τ).count x : ℕ) : ℝ≥0∞) *
          (1 / ((splittingSymbolAut (x ::ₘ τ) : ℝ≥0∞) *
            (Nat.card 𝓀[K] : ℝ≥0∞) ^ splittingSymbolExponent (x ::ₘ τ))) =
        1 / ((x.1 : ℝ≥0∞) * (Nat.card 𝓀[K] : ℝ≥0∞) ^ (x.1 * (x.2 - 1))) *
          (1 / ((splittingSymbolAut τ : ℝ≥0∞) *
            (Nat.card 𝓀[K] : ℝ≥0∞) ^ splittingSymbolExponent τ)) := by
      rw [hden, one_div, one_div, one_div, ENNReal.mul_inv (Or.inl hc0) (Or.inl (by simp)),
        ← mul_assoc, ENNReal.mul_inv_cancel hc0 (by simp), one_mul,
        ENNReal.mul_inv (Or.inr (htop _ _)) (Or.inl (htop _ _))]
    exact (ENNReal.mul_right_inj hc0 (by simp)).1 (hrec.trans hrhs.symm)

/-! ### Mass formula by ramification partition -/

/-- **Mass formula for a fixed ramification partition** ([Bhargava 2007, Prop. 2.2]): for a
partition `π` of `k` into at most `n - k` parts, the Galois sets of size `n` whose splitting
symbol has ramification partition `π` have mass `q ^ (-k)`. -/
theorem etaleMass_ramificationPartition (n k : ℕ) (π : k.Partition)
    (hπ : π.parts.card ≤ n - k) :
    (n.factorial : ℝ≥0∞)⁻¹ *
        ∑' ρ : {ρ : GaloisSet K n // ramificationPartition ρ.splittingSymbol = π.parts},
          1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ ρ.1.discriminantExponent =
      1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ k := by
  let Φ : {ρ : GaloisSet K n // ramificationPartition ρ.splittingSymbol = π.parts} →
      {σ : Multiset (ℕ × ℕ) // (∀ x ∈ σ, 0 < x.1 ∧ 0 < x.2) ∧
        (σ.map fun x ↦ x.1 * x.2).sum = n ∧ ramificationPartition σ = π.parts} :=
    fun ρ ↦ ⟨ρ.1.splittingSymbol, fun _ hx ↦ ρ.1.pos_of_mem_splittingSymbol hx,
      ρ.1.sum_map_mul_splittingSymbol, ρ.2⟩
  rw [← tsum_fiberwise _ Φ, ← ENNReal.tsum_mul_left]
  have hfib : ∀ σ : {σ : Multiset (ℕ × ℕ) // (∀ x ∈ σ, 0 < x.1 ∧ 0 < x.2) ∧
        (σ.map fun x ↦ x.1 * x.2).sum = n ∧ ramificationPartition σ = π.parts},
      (n.factorial : ℝ≥0∞)⁻¹ *
          ∑' ρ : Φ ⁻¹' {σ}, 1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ ρ.1.1.discriminantExponent =
        1 / (splittingSymbolAut σ.1 : ℝ≥0∞) * (1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ k) := by
    intro σ
    let e : {ρ : GaloisSet K n // ρ.splittingSymbol = σ.1} ≃ (Φ ⁻¹' {σ}) :=
      { toFun ρ := ⟨⟨ρ.1, ρ.2.symm ▸ σ.2.2.2⟩,
          Set.mem_preimage.2 (Set.mem_singleton_iff.2 (Subtype.ext ρ.2))⟩
        invFun ρ := ⟨ρ.1.1, congrArg Subtype.val (Set.mem_singleton_iff.1 (Set.mem_preimage.1 ρ.2))⟩
        left_inv _ := rfl
        right_inv _ := rfl }
    have he : ∀ ρ : {ρ : GaloisSet K n // ρ.splittingSymbol = σ.1}, (e ρ).1.1 = ρ.1 := fun _ ↦ rfl
    rw [← e.tsum_eq]
    simp_rw [he]
    rw [etaleMass_splittingSymbol n σ.1 σ.2.1 σ.2.2.1,
      splittingSymbolExponent_eq_sum_ramificationPartition, σ.2.2.2, π.parts_sum,
      one_div, one_div, one_div,
      ENNReal.mul_inv (Or.inr (ENNReal.pow_ne_top (by simp))) (Or.inl (by simp))]
  simp_rw [hfib, ENNReal.tsum_mul_right]
  rw [tsum_one_div_splittingSymbolAut_ramificationPartition n k π hπ, one_mul]

/-! ### Bhargava's mass formula -/

private theorem sigma_partition_ext {n : ℕ}
    {a b : Σ k : Finset.range (n + 1), {π : k.1.Partition // π.parts.card ≤ n - k.1}}
    (h : a.2.1.parts = b.2.1.parts) : a = b := by
  rcases a with ⟨⟨k₁, hk₁⟩, ⟨π₁, hπ₁⟩⟩
  rcases b with ⟨⟨k₂, hk₂⟩, ⟨π₂, hπ₂⟩⟩
  dsimp only at π₁ π₂ h
  have hk : k₁ = k₂ := by rw [← π₁.parts_sum, h, π₂.parts_sum]
  subst hk
  exact Sigma.ext rfl (heq_of_eq (Subtype.ext (Nat.Partition.ext h)))

variable (K)

/-- **Bhargava's mass formula** ([Bhargava 2007, Thm. 1.1, Prop. 2.3, and §8 for an arbitrary
nonarchimedean local field]): `M_n(K) = ∑_{k ≤ n} q(k, n - k) · q ^ (-k)`, where `q(k, m)` is
the number of partitions of `k` into at most `m` parts. For `n ≥ 1` the `k = n` term vanishes,
recovering Bhargava's `∑_{k < n}`, while at `n = 0` both sides equal `1`. -/
theorem etaleMass_eq (n : ℕ) :
    etaleMass K n =
      ∑ k ∈ Finset.range (n + 1),
        (((Finset.univ : Finset k.Partition).filter fun π ↦ π.parts.card ≤ n - k).card :
            ℝ≥0∞) / (Nat.card 𝓀[K] : ℝ≥0∞) ^ k := by
  let Ψ : GaloisSet K n →
      Σ k : Finset.range (n + 1), {π : k.1.Partition // π.parts.card ≤ n - k.1} := fun ρ ↦
    let p := ramificationPartition ρ.splittingSymbol
    have hdeg := sum_map_mul_eq_sum_ramificationPartition_add ρ.splittingSymbol
      fun x hx ↦ (ρ.pos_of_mem_splittingSymbol hx).2
    have hsum : p.sum + p.card +
        (ρ.splittingSymbol.map fun x ↦ if x.2 = 1 then x.1 else 0).sum = n :=
      hdeg.symm.trans ρ.sum_map_mul_splittingSymbol
    let π : p.sum.Partition :=
      { parts := p
        parts_pos := fun hx ↦ Nat.pos_of_ne_zero (mem_ramificationPartition.1 hx).1
        parts_sum := rfl }
    ⟨⟨p.sum, Finset.mem_range.2 (by omega)⟩, ⟨π, by simp only [π]; omega⟩⟩
  rw [etaleMass_def, ← tsum_fiberwise _ Ψ, ← ENNReal.tsum_mul_left]
  have hfib : ∀ idx : Σ k : Finset.range (n + 1), {π : k.1.Partition // π.parts.card ≤ n - k.1},
      (n.factorial : ℝ≥0∞)⁻¹ *
          ∑' ρ : Ψ ⁻¹' {idx}, 1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ ρ.1.discriminantExponent =
        1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ idx.1.1 := by
    rintro ⟨⟨k, hk⟩, ⟨π, hπ⟩⟩
    let e : {ρ : GaloisSet K n // ramificationPartition ρ.splittingSymbol = π.parts} ≃
        (Ψ ⁻¹' {⟨⟨k, hk⟩, ⟨π, hπ⟩⟩}) :=
      { toFun ρ := ⟨ρ.1, Set.mem_preimage.2 (Set.mem_singleton_iff.2 (sigma_partition_ext ρ.2))⟩
        invFun ρ := ⟨ρ.1,
          congrArg (fun x ↦ x.2.1.parts) (Set.mem_singleton_iff.1 (Set.mem_preimage.1 ρ.2))⟩
        left_inv _ := rfl
        right_inv _ := rfl }
    have he : ∀ ρ : {ρ : GaloisSet K n // ramificationPartition ρ.splittingSymbol = π.parts},
        (e ρ).1 = ρ.1 := fun _ ↦ rfl
    rw [← e.tsum_eq]
    simp_rw [he]
    exact etaleMass_ramificationPartition n k π hπ
  simp_rw [hfib, tsum_sigma', tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    Fintype.card_subtype, mul_one_div]
  exact Finset.sum_coe_sort (Finset.range (n + 1)) fun k ↦
    (((Finset.univ : Finset k.Partition).filter fun π ↦ π.parts.card ≤ n - k).card : ℝ≥0∞) /
      (Nat.card 𝓀[K] : ℝ≥0∞) ^ k

/-- **Bhargava's mass formula over étale algebras** ([Bhargava 2007, Thm. 1.1, §8]): for any
family `A` of étale `K`-algebras of degree `n` containing exactly one member of each
`K`-isomorphism class,
`∑ 1 / (#Aut_K(A i) · q ^ d(A i)) = ∑_{k ≤ n} q(k, n - k) · q ^ (-k)`. -/
theorem tsum_etaleDiscriminantExponent_eq (n : ℕ) {ι : Type*} (A : ι → Type u)
    [∀ i, CommRing (A i)] [∀ i, Algebra K (A i)] [∀ i, Algebra.Etale K (A i)]
    (hdeg : ∀ i, Module.finrank K (A i) = n)
    (hinj : ∀ i j, Nonempty (A i ≃ₐ[K] A j) → i = j)
    (hsurj : ∀ (B : Type u) [CommRing B] [Algebra K B] [Algebra.Etale K B],
      Module.finrank K B = n → ∃ i, Nonempty (B ≃ₐ[K] A i)) :
    ∑' i, 1 / ((Nat.card (A i ≃ₐ[K] A i) : ℝ≥0∞) *
        (Nat.card 𝓀[K] : ℝ≥0∞) ^ etaleDiscriminantExponent K (A i)) =
      ∑ k ∈ Finset.range (n + 1),
        (((Finset.univ : Finset k.Partition).filter fun π ↦ π.parts.card ≤ n - k).card :
            ℝ≥0∞) / (Nat.card 𝓀[K] : ℝ≥0∞) ^ k :=
  (tsum_etaleDiscriminantExponent K n A hdeg hinj hsurj).trans (etaleMass_eq K n)

end TauCeti
