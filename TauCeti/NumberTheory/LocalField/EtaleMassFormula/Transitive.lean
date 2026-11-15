/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.EtaleMassFormula.Relabelling
public import TauCeti.NumberTheory.LocalField.EtaleMassFormula.SubfieldCount
import Mathlib.Tactic.FieldSimp
import TauCeti.Algebra.BigOperators.Group.Finset.Defs
import TauCeti.Algebra.GroupAction.OrbitRelQuotient
import TauCeti.FieldTheory.Galois.FixedField

/-!
# Splitting symbols of Galois sets and the transitive mass

For a Galois set `ρ : TauCeti.GaloisSet K n` over a nonarchimedean local field `K`, its
*splitting symbol* `TauCeti.GaloisSet.splittingSymbol ρ : Multiset (ℕ × ℕ)` records the pair
`(f, e)` of residue degree and ramification index of the fixed field of a point stabilizer on
each orbit [Bhargava 2007, (2.1)].

For `0 < f` and `0 < e`, the Galois sets of size `f * e` with splitting symbol `{(f, e)}` are the
transitive ones whose point stabilizers fix a field of degree `f * e` and residue degree `f`.
Combining the transitive bridge `TauCeti.GaloisSet.tsum_isTransitive` with the subfield count by
residue degree `TauCeti.tsum_inertiaDegree_eq` gives their mass `1 / (f · q ^ (f * (e - 1)))`,
where `q` is the residue cardinality of `K` (`TauCeti.etaleMass_isTransitive_splittingSymbol`).

## Main definitions and results

* `TauCeti.GaloisSet.splittingSymbol`: the splitting symbol of a labelled Galois set, with
  `TauCeti.GaloisSet.mem_splittingSymbol` and `TauCeti.GaloisSet.card_splittingSymbol`.
* `TauCeti.GaloisSet.splittingSymbol_eq_of_equiv`: invariance under equivariant bijection.
* `TauCeti.GaloisSet.splittingSymbol_sigma`: additivity on disjoint unions of Galois sets.
* `TauCeti.etaleMass_isTransitive_splittingSymbol`: the mass of the Galois sets of size `f * e`
  with splitting symbol `{(f, e)}`.

## References

* M. Bhargava, *Mass formulae for extensions of local fields, and conjectures on the density of
  number field discriminants*, IMRN **2007**, rnm052, §2.
-/

public section

noncomputable section

open ValuativeRel _root_.MulAction
open scoped ENNReal NNReal Nat

namespace TauCeti

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] {n : ℕ}

namespace GaloisSet

open scoped Classical in
/-- The **splitting symbol** of a labelled Galois set ([Bhargava 2007, (2.1)]): the multiset,
over its orbits, of the pair `(f, e)` of residue degree and ramification index of the fixed field
of a point stabilizer. -/
def splittingSymbol (ρ : GaloisSet K n) : Multiset (ℕ × ℕ) :=
  letI := ρ.mulAction
  haveI := Fintype.ofFinite
    (orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n))
  (Finset.univ : Finset
      (orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n))).val.map
    fun O => (fun F : IntermediateField K (SeparableClosure K) =>
      (F.inertiaDegree, Module.finrank K F / F.inertiaDegree))
        (IntermediateField.fixedField
          (stabilizer Gal(SeparableClosure K/K) (Quotient.out O : Fin n)))

/-- The defining formula of `GaloisSet.splittingSymbol`. -/
theorem splittingSymbol_def (ρ : GaloisSet K n) :
    ρ.splittingSymbol =
      (letI := ρ.mulAction
      letI := Fintype.ofFinite (orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n))
      (Finset.univ : Finset
          (orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n))).val.map
        fun O => (fun F : IntermediateField K (SeparableClosure K) =>
          (F.inertiaDegree, Module.finrank K F / F.inertiaDegree))
            (IntermediateField.fixedField
              (stabilizer Gal(SeparableClosure K/K) (Quotient.out O : Fin n)))) :=
  (rfl)

/-- A pair `(f, e)` belongs to `ρ.splittingSymbol` iff some label's stabilizer fixes a field of
residue degree `f` and ramification index `e`. -/
@[simp]
theorem mem_splittingSymbol {ρ : GaloisSet K n} {x : ℕ × ℕ} :
    x ∈ ρ.splittingSymbol ↔
      letI := ρ.mulAction
      ∃ i : Fin n,
        let F := IntermediateField.fixedField (stabilizer Gal(SeparableClosure K/K) i)
        (F.inertiaDegree, Module.finrank K F / F.inertiaDegree) = x := by
  let := ρ.mulAction
  let := Fintype.ofFinite (orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n))
  rw [splittingSymbol_def, Multiset.mem_map]
  constructor
  · rintro ⟨O, _, rfl⟩
    exact ⟨O.out, rfl⟩
  · rintro ⟨i, rfl⟩
    refine ⟨Quotient.mk'' i, Finset.mem_univ _, ?_⟩
    have hi : (Quotient.mk'' i : orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n)) =
        Quotient.mk'' i := rfl
    dsimp only
    rw [inertiaDegree_fixedField_stabilizer_out K hi, finrank_fixedField_stabilizer_out K hi]

/-- The number of factors in `ρ.splittingSymbol` is the number of Galois orbits of `ρ`. -/
@[simp]
theorem card_splittingSymbol (ρ : GaloisSet K n) :
    Multiset.card ρ.splittingSymbol =
      letI := ρ.mulAction
      Nat.card (orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n)) := by
  let := ρ.mulAction
  let := Fintype.ofFinite (orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n))
  rw [splittingSymbol_def, Multiset.card_map, Finset.card_val, Finset.card_univ,
    Nat.card_eq_fintype_card]

/-- Any section choosing one label per orbit computes the splitting symbol. -/
theorem splittingSymbol_eq_map (ρ : GaloisSet K n)
    [Fintype (let := ρ.mulAction; orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n))]
    (s : (let := ρ.mulAction; orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n)) → Fin n)
    (hs : ∀ O, (let := ρ.mulAction;
      (Quotient.mk'' (s O) : orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n)) = O)) :
    ρ.splittingSymbol =
      (let := ρ.mulAction
      (Finset.univ : Finset
          (orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n))).val.map
        fun O => (fun F : IntermediateField K (SeparableClosure K) =>
          (F.inertiaDegree, Module.finrank K F / F.inertiaDegree))
            (IntermediateField.fixedField (stabilizer Gal(SeparableClosure K/K) (s O)))) := by
  let := ρ.mulAction
  rw [splittingSymbol_def]
  rw [Subsingleton.elim (Fintype.ofFinite (orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n)))
    inferInstance]
  refine Multiset.map_congr rfl fun O _ ↦ ?_
  have hsO : (Quotient.mk'' (s O) : orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n)) = O := hs O
  dsimp only
  rw [inertiaDegree_fixedField_stabilizer_out K hsO,
    finrank_fixedField_stabilizer_out K hsO]

/-- Equivariant bijections preserve the splitting symbol of labelled Galois sets. -/
theorem splittingSymbol_eq_of_equiv {m : ℕ} (ρ : GaloisSet K n) (τ : GaloisSet K m)
    (e : Fin n ≃ Fin m)
    (he : ∀ (σ : Gal(SeparableClosure K/K)) (i : Fin n),
      e (ρ.val σ i) = τ.val σ (e i)) :
    ρ.splittingSymbol = τ.splittingSymbol := by
  let := ρ.mulAction
  let := τ.mulAction
  let := Fintype.ofFinite (orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n))
  let := Fintype.ofFinite (orbitRel.Quotient Gal(SeparableClosure K/K) (Fin m))
  let E : orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n) ≃
      orbitRel.Quotient Gal(SeparableClosure K/K) (Fin m) :=
    MulAction.orbitRelQuotientCongr (MulEquiv.refl Gal(SeparableClosure K/K)) e he
  rw [splittingSymbol_def, splittingSymbol_def]
  have hmap :
      (Finset.univ (α := orbitRel.Quotient Gal(SeparableClosure K/K) (Fin m))).val =
        ((Finset.univ (α := orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n))).map
          E.toEmbedding).val :=
    congrArg Finset.val (Finset.map_univ_equiv E).symm
  rw [hmap, Finset.map_val, Multiset.map_map]
  refine Multiset.map_congr rfl fun O _ ↦ ?_
  have hE : (Quotient.mk'' (e O.out) :
      orbitRel.Quotient Gal(SeparableClosure K/K) (Fin m)) = E O := by
    rw [← MulAction.orbitRelQuotientCongr_mk (MulEquiv.refl _) e he, Quotient.out_eq']
  dsimp only [Function.comp_def, Equiv.coe_toEmbedding]
  rw [inertiaDegree_fixedField_stabilizer_out K hE,
    finrank_fixedField_stabilizer_out K hE,
    MulAction.stabilizer_eq_of_injective e e.injective he]

/-- Relabelling a Galois set does not change its splitting symbol. -/
@[simp]
theorem splittingSymbol_smul (ρ : GaloisSet K n) (e : Equiv.Perm (Fin n)) :
    (e • ρ).splittingSymbol = ρ.splittingSymbol :=
  (ρ.splittingSymbol_eq_of_equiv (e • ρ) e (by simp)).symm

/-- The trivial Galois set of size `n` has splitting symbol `n` copies of `(1, 1)`. -/
@[simp]
theorem splittingSymbol_trivial (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (n : ℕ) :
    (trivial K n).splittingSymbol = Multiset.replicate n (1, 1) := by
  let := (trivial K n).mulAction
  let := Fintype.ofFinite (orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n))
  have hmk : Function.Bijective
      (Quotient.mk'' : Fin n → orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n)) :=
    ⟨fun i j h ↦ by
      obtain ⟨σ, hσ⟩ := Quotient.exact' h
      simpa using hσ.symm, Quotient.mk''_surjective⟩
  rw [splittingSymbol_def]
  have hconst : ∀ O : orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n),
      (fun F : IntermediateField K (SeparableClosure K) =>
        (F.inertiaDegree, Module.finrank K F / F.inertiaDegree))
          (IntermediateField.fixedField
            (stabilizer Gal(SeparableClosure K/K) (Quotient.out O : Fin n))) = (1, 1) := by
    intro O
    dsimp only
    rw [fixedField_stabilizer_trivial, IntermediateField.inertiaDegree_bot,
      IntermediateField.finrank_bot, Nat.div_self one_pos]
  rw [Multiset.map_congr rfl fun O _ ↦ hconst O, Multiset.map_const',
    Finset.card_val, Finset.card_univ, ← Nat.card_eq_fintype_card,
    ← Nat.card_congr (Equiv.ofBijective _ hmk), Nat.card_fin]

/-- A Galois set on at most one label has splitting symbol `Multiset.replicate n (1, 1)`. -/
@[simp]
theorem splittingSymbol_of_subsingleton [Subsingleton (Fin n)] (ρ : GaloisSet K n) :
    ρ.splittingSymbol = Multiset.replicate n (1, 1) :=
  Subsingleton.elim ρ (trivial K n) ▸ splittingSymbol_trivial K n

/-- Every pair `(f, e)` in the splitting symbol of a Galois set has positive residue degree and
positive ramification index. -/
theorem pos_of_mem_splittingSymbol {ρ : GaloisSet K n} {x : ℕ × ℕ}
    (hx : x ∈ ρ.splittingSymbol) : 0 < x.1 ∧ 0 < x.2 := by
  let := ρ.mulAction
  obtain ⟨i, rfl⟩ := mem_splittingSymbol.1 hx
  have : FiniteDimensional K (IntermediateField.fixedField
      (stabilizer Gal(SeparableClosure K/K) i)) :=
    ρ.finiteDimensional_fixedField_stabilizer i
  exact ⟨IntermediateField.inertiaDegree_pos _, Nat.div_pos
    (Nat.le_of_dvd Module.finrank_pos (IntermediateField.inertiaDegree_dvd_finrank _))
    (IntermediateField.inertiaDegree_pos _)⟩

/-- The degrees `f * e` of the factors of the splitting symbol add up to the size `n` of the
Galois set. -/
theorem sum_map_mul_splittingSymbol (ρ : GaloisSet K n) :
    (ρ.splittingSymbol.map fun x => x.1 * x.2).sum = n := by
  let := ρ.mulAction
  let := Fintype.ofFinite (orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n))
  rw [splittingSymbol_def, Multiset.map_map]
  have hmul : ∀ O : orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n),
      ((fun x : ℕ × ℕ => x.1 * x.2) ∘ fun O =>
        (fun F : IntermediateField K (SeparableClosure K) =>
          (F.inertiaDegree, Module.finrank K F / F.inertiaDegree))
            (IntermediateField.fixedField
              (stabilizer Gal(SeparableClosure K/K) (Quotient.out O : Fin n)))) O =
        Nat.card {i : Fin n // (Quotient.mk'' i :
          orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n)) = O} := fun O ↦
    (Nat.mul_div_cancel' (IntermediateField.inertiaDegree_dvd_finrank _)).trans
      (ρ.finrank_fixedField_stabilizer_eq_card_fiber O)
  rw [Multiset.map_congr rfl fun O _ ↦ hmul O, ← Finset.sum_eq_multiset_sum,
    ← Nat.card_sigma, Nat.card_congr (Equiv.sigmaFiberEquiv _), Nat.card_eq_fintype_card,
    Fintype.card_fin]

/-- A transitive Galois set of positive size has a singleton splitting symbol, given by any
point stabilizer's fixed field. -/
theorem splittingSymbol_of_isTransitive (ρ : GaloisSet K n) (hρ : ρ.IsTransitive) (i : Fin n) :
    ρ.splittingSymbol =
      {(let := ρ.mulAction
        let F := IntermediateField.fixedField (stabilizer Gal(SeparableClosure K/K) i)
        (F.inertiaDegree, Module.finrank K F / F.inertiaDegree))} := by
  let := ρ.mulAction
  have : Nonempty (Fin n) := ⟨i⟩
  have : MulAction.IsPretransitive Gal(SeparableClosure K/K) (Fin n) := ρ.isTransitive_def.1 hρ
  obtain ⟨_⟩ := (MulAction.pretransitive_iff_unique_quotient_of_nonempty _ _).mp ‹_›
  rw [splittingSymbol_eq_map ρ (fun _ ↦ i) fun O ↦ Subsingleton.elim _ _]
  simp

/-- A Galois set whose splitting symbol is a singleton is transitive. -/
theorem isTransitive_of_splittingSymbol_eq_singleton {ρ : GaloisSet K n} {x : ℕ × ℕ}
    (h : ρ.splittingSymbol = {x}) : ρ.IsTransitive := by
  let := ρ.mulAction
  let := Fintype.ofFinite (orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n))
  have hcard := congrArg Multiset.card h
  rw [card_splittingSymbol, Multiset.card_singleton, Nat.card_eq_fintype_card] at hcard
  exact ρ.isTransitive_def.2 <| (MulAction.pretransitive_iff_subsingleton_quotient _ _).2
    (Fintype.card_le_one_iff_subsingleton.mp hcard.le)

/-- A labelled Galois set of size `f * e` has splitting symbol `{(f, e)}` iff it is transitive
and the stabilizer of `i` fixes a field of residue degree `f`. -/
theorem splittingSymbol_eq_singleton_iff {f e : ℕ} (ρ : GaloisSet K (f * e))
    (i : Fin (f * e)) :
    ρ.splittingSymbol = {(f, e)} ↔
      ρ.IsTransitive ∧
        (let := ρ.mulAction
        (IntermediateField.fixedField
          (stabilizer Gal(SeparableClosure K/K) i)).inertiaDegree = f) := by
  constructor
  · intro h
    have htrans := isTransitive_of_splittingSymbol_eq_singleton h
    refine ⟨htrans, ?_⟩
    rw [ρ.splittingSymbol_of_isTransitive htrans i, Multiset.singleton_inj] at h
    exact (Prod.ext_iff.1 h).1
  · rintro ⟨htrans, hdeg⟩
    rw [ρ.splittingSymbol_of_isTransitive htrans i]
    let := ρ.mulAction
    dsimp only
    rw [ρ.finrank_fixedField_stabilizer_of_isTransitive htrans i, hdeg,
      Nat.mul_div_cancel_left e (Nat.pos_of_mul_pos_right i.pos)]

/-- The splitting symbol of a disjoint union of Galois sets is the sum of their splitting
symbols. -/
@[simp]
theorem splittingSymbol_sigma {ι : Type*} [Fintype ι] {d : ι → ℕ}
    (b : Fin n ≃ Σ i, Fin (d i)) (ρ : ∀ i, GaloisSet K (d i)) :
    (sigma b ρ).splittingSymbol = ∑ i, (ρ i).splittingSymbol := by
  classical
  -- Identify the orbits of `sigma b ρ` with `Σ i, orbitRel.Quotient _ (Fin (d i))` along `b`,
  -- choose `b.symm ⟨i, O.out⟩` on each orbit, and transport stabilizers via
  -- `stabilizer_sigma_symm_apply`.
  let : ∀ i, MulAction Gal(SeparableClosure K/K) (Fin (d i)) := fun i ↦ (ρ i).mulAction
  let := (sigma b ρ).mulAction
  let : ∀ i, Fintype (orbitRel.Quotient Gal(SeparableClosure K/K) (Fin (d i))) :=
    fun i ↦ Fintype.ofFinite _
  let := Fintype.ofFinite (orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n))
  have he' (g : Gal(SeparableClosure K/K)) (j : Fin n) :
      b (g • j) = (MulEquiv.refl Gal(SeparableClosure K/K)) g • b j :=
    sigma_smul_apply b ρ g j
  let E : orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n) ≃
      Σ i : ι, orbitRel.Quotient Gal(SeparableClosure K/K) (Fin (d i)) :=
    (MulAction.orbitRelQuotientCongr (MulEquiv.refl _) b he').trans
      MulAction.orbitRelQuotientSigmaEquiv
  have hs : ∀ p : Σ i : ι, orbitRel.Quotient Gal(SeparableClosure K/K) (Fin (d i)),
      (Quotient.mk'' (b.symm ⟨p.1, p.2.out⟩) :
        orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n)) = E.symm p := by
    rintro ⟨i, O⟩
    apply E.injective
    rw [E.apply_symm_apply, Equiv.trans_apply, MulAction.orbitRelQuotientCongr_mk,
      b.apply_symm_apply, MulAction.orbitRelQuotientSigmaEquiv_mk, Quotient.out_eq']
  have hterm : ∀ p : Σ i : ι, orbitRel.Quotient Gal(SeparableClosure K/K) (Fin (d i)),
      (fun F : IntermediateField K (SeparableClosure K) =>
        (F.inertiaDegree, Module.finrank K F / F.inertiaDegree))
          (IntermediateField.fixedField
            (stabilizer Gal(SeparableClosure K/K) (Quotient.out (E.symm p)))) =
        (fun F : IntermediateField K (SeparableClosure K) =>
          (F.inertiaDegree, Module.finrank K F / F.inertiaDegree))
            (IntermediateField.fixedField
              (stabilizer Gal(SeparableClosure K/K) p.2.out)) := by
    rintro ⟨i, O⟩
    dsimp only
    rw [inertiaDegree_fixedField_stabilizer_out K (hs ⟨i, O⟩),
      finrank_fixedField_stabilizer_out K (hs ⟨i, O⟩),
      stabilizer_sigma_symm_apply b ρ i O.out]
  rw [splittingSymbol_def, ← Finset.sum_multiset_map_singleton]
  have hrhs : ∑ i : ι, (ρ i).splittingSymbol =
      ∑ p : Σ i : ι, orbitRel.Quotient Gal(SeparableClosure K/K) (Fin (d i)),
        ({(fun F : IntermediateField K (SeparableClosure K) =>
          (F.inertiaDegree, Module.finrank K F / F.inertiaDegree))
            (IntermediateField.fixedField
              (stabilizer Gal(SeparableClosure K/K) p.2.out))} : Multiset (ℕ × ℕ)) := by
    rw [Fintype.sum_sigma]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [splittingSymbol_def, ← Finset.sum_multiset_map_singleton]
  rw [hrhs]
  exact (Fintype.sum_equiv E.symm _ _ fun p ↦
    congrArg (fun x ↦ ({x} : Multiset (ℕ × ℕ))) (hterm p).symm).symm

end GaloisSet

/-- Via label `0` and `GaloisSet.tsum_isTransitive`, summing over Galois sets of size `f * e` with
splitting symbol `{(f, e)}` reduces to `(f * e - 1)!` times an inertia-degree-`f` sum over
degree-`f * e` subextensions. -/
private theorem tsum_splittingSymbol_singleton_eq_tsum_finrank {f e : ℕ}
    (hf : 0 < f) (he : 0 < e) :
    ∑' ρ : {ρ : GaloisSet K (f * e) // ρ.splittingSymbol = {(f, e)}},
        1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ ρ.1.discriminantExponent =
      ((f * e - 1)! : ℝ≥0∞) *
        ∑' L : {L : IntermediateField K (SeparableClosure K) // Module.finrank K L = f * e},
          (if L.1.inertiaDegree = f then
            1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ L.1.discriminantExponent else 0) := by
  let i₀ : Fin (f * e) := ⟨0, Nat.mul_pos hf he⟩
  let g : IntermediateField K (SeparableClosure K) → ℝ≥0∞ := fun L ↦
    if L.inertiaDegree = f then 1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ L.discriminantExponent else 0
  let S : Set {ρ : GaloisSet K (f * e) // ρ.IsTransitive} :=
    {ρ | let := ρ.1.mulAction
      (IntermediateField.fixedField (stabilizer Gal(SeparableClosure K/K) i₀)).inertiaDegree = f}
  let E₁ : {ρ : GaloisSet K (f * e) // ρ.splittingSymbol = {(f, e)}} ≃ S :=
    (Equiv.subtypeEquivRight fun ρ ↦ ρ.splittingSymbol_eq_singleton_iff i₀).trans
      (Equiv.subtypeSubtypeEquivSubtypeInter _ _).symm
  have hind :
      (fun ρ : {ρ : GaloisSet K (f * e) // ρ.IsTransitive} ↦
        let := ρ.1.mulAction
        g (IntermediateField.fixedField (stabilizer Gal(SeparableClosure K/K) i₀))) =
      S.indicator (fun ρ ↦ 1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ ρ.1.discriminantExponent) := by
    ext ρ
    let := ρ.1.mulAction
    dsimp [g, S, Set.indicator]
    split_ifs with h
    · exact (congrArg (fun d ↦ 1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ d)
        (ρ.1.discriminantExponent_of_isTransitive ρ.2 i₀)).symm
    · rfl
  refine (E₁.tsum_eq fun ρ ↦
      1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ ρ.1.1.discriminantExponent).trans ?_
  refine ((tsum_subtype S fun ρ : {ρ : GaloisSet K (f * e) // ρ.IsTransitive} ↦
      1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ ρ.1.discriminantExponent).trans ?_).trans
    (GaloisSet.tsum_isTransitive i₀ g)
  exact congrArg tsum hind.symm

/-- Summing the inertia-degree-`f` discriminant weight over degree-`f * e` subextensions evaluates
via `tsum_inertiaDegree_eq`. -/
private theorem tsum_finrank_inertiaDegree_indicator {f e : ℕ} (hf : 0 < f) :
    ∑' L : {L : IntermediateField K (SeparableClosure K) // Module.finrank K L = f * e},
        (if L.1.inertiaDegree = f then
          1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ L.1.discriminantExponent else 0) =
      (e : ℝ≥0∞) / (Nat.card 𝓀[K] : ℝ≥0∞) ^ (f * (e - 1)) := by
  let E₂ : {L : IntermediateField K (SeparableClosure K) // Module.finrank K L = f * e ∧
      L.inertiaDegree = f} ≃
      {L : {L : IntermediateField K (SeparableClosure K) // Module.finrank K L = f * e} //
        L.1.inertiaDegree = f} :=
    (Equiv.subtypeSubtypeEquivSubtypeInter _ _).symm
  have hind :
      (fun L : {L : IntermediateField K (SeparableClosure K) // Module.finrank K L = f * e} ↦
        if L.1.inertiaDegree = f then
          1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ L.1.discriminantExponent else 0) =
      Set.indicator
        {L : {L : IntermediateField K (SeparableClosure K) // Module.finrank K L = f * e} |
          L.1.inertiaDegree = f}
        (fun L ↦ 1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ L.1.discriminantExponent) := by
    ext L
    dsimp [Set.indicator]
    split_ifs <;> rfl
  rw [hind, ← tsum_subtype _ fun L : {L : IntermediateField K (SeparableClosure K) //
      Module.finrank K L = f * e} ↦
    1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ L.1.discriminantExponent]
  exact (E₂.tsum_eq fun L ↦ 1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ L.1.1.discriminantExponent).symm.trans
    (tsum_inertiaDegree_eq (K := K) hf.ne' e)

private theorem ennreal_factorial_mul_cancel {f e : ℕ} (hf : 0 < f) (he : 0 < e) :
    ((f * e)! : ℝ≥0∞)⁻¹ * (((f * e - 1)! : ℝ≥0∞) * (e : ℝ≥0∞)) = (f : ℝ≥0∞)⁻¹ := by
  have hfe : (f * e)! = f * e * (f * e - 1)! :=
    (Nat.mul_factorial_pred (Nat.mul_pos hf he).ne').symm
  have hnn : (((f * e)! : ℝ≥0)⁻¹ * (((f * e - 1)! : ℝ≥0) * (e : ℝ≥0))) = (f : ℝ≥0)⁻¹ := by
    rw [hfe]
    push_cast
    have : (f : ℝ≥0) ≠ 0 := Nat.cast_ne_zero.2 hf.ne'
    have : (e : ℝ≥0) ≠ 0 := Nat.cast_ne_zero.2 he.ne'
    have : ((f * e - 1)! : ℝ≥0) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
    field_simp
  simpa [ENNReal.coe_inv (Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)),
    ENNReal.coe_inv (Nat.cast_ne_zero.2 hf.ne')] using congrArg (↑· : ℝ≥0 → ℝ≥0∞) hnn

/-- **The transitive mass by residue degree** ([Bhargava 2007, §2]): for `0 < f` and `0 < e`, the
Galois sets of size `f * e` with splitting symbol `{(f, e)}` have mass
`1 / (f · q ^ (f * (e - 1)))`, where `q` is the residue cardinality of `K`. -/
theorem etaleMass_isTransitive_splittingSymbol (f e : ℕ) (hf : 0 < f) (he : 0 < e) :
    ((f * e)! : ℝ≥0∞)⁻¹ *
        ∑' ρ : {ρ : GaloisSet K (f * e) // ρ.splittingSymbol = {(f, e)}},
          1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ ρ.1.discriminantExponent =
      1 / ((f : ℝ≥0∞) * (Nat.card 𝓀[K] : ℝ≥0∞) ^ (f * (e - 1))) := by
  -- Double-count via label `0`: each degree-`f * e` subextension of residue degree `f` arises from
  -- `(f * e - 1)!` transitive Galois sets (`tsum_splittingSymbol_singleton_eq_tsum_finrank`), and
  -- Serre's formula (`tsum_finrank_inertiaDegree_indicator`) sums their weights to
  -- `e / q ^ (f * (e - 1))`.
  rw [tsum_splittingSymbol_singleton_eq_tsum_finrank hf he,
    tsum_finrank_inertiaDegree_indicator hf,
    div_eq_mul_inv, ← mul_assoc ((f * e - 1)! : ℝ≥0∞), ← mul_assoc,
    ennreal_factorial_mul_cancel hf he, one_div,
    ENNReal.mul_inv (Or.inl (Nat.cast_ne_zero.2 hf.ne')) (Or.inl (ENNReal.natCast_ne_top f))]

end TauCeti
