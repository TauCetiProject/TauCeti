/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.EtaleMassFormula.Relabelling
public import TauCeti.NumberTheory.LocalField.EtaleMassFormula.SplittingSymbol
public import TauCeti.NumberTheory.LocalField.EtaleMassFormula.SubfieldCount
import TauCeti.Algebra.GroupAction.OrbitRelQuotient
import TauCeti.FieldTheory.Galois.FixedField

/-!
# Splitting symbols of Galois sets and the transitive mass

For a Galois set `ρ : TauCeti.GaloisSet K n` over a nonarchimedean local field `K`, its
*splitting symbol* `TauCeti.GaloisSet.splittingSymbol ρ : Multiset (ℕ × ℕ)` records the pair
`(f, e)` of residue degree and ramification index of the fixed field of a point stabilizer on
each orbit [Bhargava 2007, (2.1)].

The Galois sets of size `f * e` with splitting symbol `{(f, e)}` are the transitive ones whose
point stabilizers fix a field of degree `f * e` and residue degree `f`. Combining the transitive
bridge `TauCeti.GaloisSet.tsum_isTransitive` with the subfield count by residue degree
`TauCeti.tsum_inertiaDegree_eq` gives their mass `1 / (f · q ^ (f * (e - 1)))`
(`TauCeti.etaleMass_isTransitive_splittingSymbol`).

## Main definitions and results

* `TauCeti.GaloisSet.splittingSymbol`: the splitting symbol of a labelled Galois set.
* `TauCeti.GaloisSet.splittingSymbol_eq_of_equiv`: invariance under equivariant bijection.
* `TauCeti.GaloisSet.splittingSymbol_sigma` and `TauCeti.GaloisSet.discriminantExponent_sigma`:
  behaviour on disjoint unions of Galois sets.
* `TauCeti.etaleMass_isTransitive_splittingSymbol`: the mass of the Galois sets of size `f * e`
  with splitting symbol `{(f, e)}`.

## References

* M. Bhargava, *Mass formulae for extensions of local fields, and conjectures on the density of
  number field discriminants*, IMRN **2007**, rnm052, §2.
-/

public section

noncomputable section

open ValuativeRel _root_.MulAction
open scoped ENNReal Nat

namespace TauCeti

section FinrankOrbit

variable (K : Type*) [Field K] {X : Type*} [MulAction Gal(SeparableClosure K/K) X]

/-- Translating a point does not change the degree of its stabilizer's fixed field. -/
@[simp]
theorem finrank_fixedField_stabilizer_smul
    (σ : Gal(SeparableClosure K/K)) (x : X) :
    Module.finrank K (IntermediateField.fixedField
      (stabilizer Gal(SeparableClosure K/K) (σ • x))) =
        Module.finrank K (IntermediateField.fixedField
          (stabilizer Gal(SeparableClosure K/K) x)) := by
  rw [stabilizer_smul_eq_stabilizer_map_conj, MulEquiv.toMonoidHom_eq_coe,
    Subgroup.fixedField_map_conj]
  exact ((IntermediateField.fixedField (stabilizer Gal(SeparableClosure K/K) x)).equivMap
    σ.toAlgHom).toLinearEquiv.finrank_eq.symm

/-- The degree of an orbit's representative fixed field can be computed at any point of the
orbit. -/
theorem finrank_fixedField_stabilizer_out
    {ω : orbitRel.Quotient Gal(SeparableClosure K/K) X} {x : X}
    (hx : (Quotient.mk'' x : orbitRel.Quotient Gal(SeparableClosure K/K) X) = ω) :
    Module.finrank K (IntermediateField.fixedField
      (stabilizer Gal(SeparableClosure K/K) ω.out)) =
        Module.finrank K (IntermediateField.fixedField
          (stabilizer Gal(SeparableClosure K/K) x)) := by
  obtain ⟨σ, rfl⟩ := MulAction.exists_smul_out_eq hx
  exact (finrank_fixedField_stabilizer_smul K σ ω.out).symm

end FinrankOrbit

section FieldGaloisSet

variable {K : Type*} [Field K] {n : ℕ}

/-- The cardinality of an orbit equals the degree of its stabilizer's fixed field. -/
theorem GaloisSet.finrank_fixedField_stabilizer_eq_card_fiber (ρ : GaloisSet K n)
    (ω : let := ρ.mulAction; orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n)) :
    let := ρ.mulAction
    Module.finrank K (IntermediateField.fixedField
      (stabilizer Gal(SeparableClosure K/K) (Quotient.out ω : Fin n))) =
        Nat.card {i : Fin n // (Quotient.mk'' i :
          orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n)) = ω} := by
  let := ρ.mulAction
  dsimp only
  rw [ρ.finrank_fixedField_stabilizer ω.out]
  refine Nat.card_congr (Equiv.subtypeEquivRight fun i ↦ ?_).symm
  conv_lhs => rw [← Quotient.out_eq' ω]
  rw [Quotient.eq'', MulAction.orbitRel_apply]

end FieldGaloisSet

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] {n : ℕ}

section InertiaOrbit

variable (K) {X : Type*} [MulAction Gal(SeparableClosure K/K) X]

/-- Translating a point does not change the residue degree of its stabilizer's fixed field. -/
@[simp]
theorem inertiaDegree_fixedField_stabilizer_smul
    (σ : Gal(SeparableClosure K/K)) (x : X) :
    (IntermediateField.fixedField
      (stabilizer Gal(SeparableClosure K/K) (σ • x))).inertiaDegree =
        (IntermediateField.fixedField
          (stabilizer Gal(SeparableClosure K/K) x)).inertiaDegree := by
  rw [stabilizer_smul_eq_stabilizer_map_conj, MulEquiv.toMonoidHom_eq_coe,
    Subgroup.fixedField_map_conj]
  exact (IntermediateField.inertiaDegree_eq_of_algEquiv
    ((IntermediateField.fixedField (stabilizer Gal(SeparableClosure K/K) x)).equivMap
      σ.toAlgHom)).symm

/-- The residue degree of an orbit's representative fixed field can be computed at any point of the
orbit. -/
theorem inertiaDegree_fixedField_stabilizer_out
    {ω : orbitRel.Quotient Gal(SeparableClosure K/K) X} {x : X}
    (hx : (Quotient.mk'' x : orbitRel.Quotient Gal(SeparableClosure K/K) X) = ω) :
    (IntermediateField.fixedField
      (stabilizer Gal(SeparableClosure K/K) ω.out)).inertiaDegree =
        (IntermediateField.fixedField
          (stabilizer Gal(SeparableClosure K/K) x)).inertiaDegree := by
  obtain ⟨σ, rfl⟩ := MulAction.exists_smul_out_eq hx
  exact (inertiaDegree_fixedField_stabilizer_smul K σ ω.out).symm

end InertiaOrbit

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

/-- A Galois set of size zero has the empty splitting symbol. -/
@[simp]
theorem splittingSymbol_zero (ρ : GaloisSet K 0) : ρ.splittingSymbol = 0 := by
  let := ρ.mulAction
  let := Fintype.ofFinite (orbitRel.Quotient Gal(SeparableClosure K/K) (Fin 0))
  have : IsEmpty (orbitRel.Quotient Gal(SeparableClosure K/K) (Fin 0)) :=
    ⟨Quotient.ind' fun i ↦ i.elim0⟩
  rw [splittingSymbol_def, Finset.univ_eq_empty, Finset.empty_val, Multiset.map_zero]

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

/-- Every pair `(f, e)` in the splitting symbol of a Galois set has positive residue degree and
positive ramification index. -/
theorem pos_of_mem_splittingSymbol {ρ : GaloisSet K n} {x : ℕ × ℕ}
    (hx : x ∈ ρ.splittingSymbol) : 0 < x.1 ∧ 0 < x.2 := by
  let := ρ.mulAction
  rw [splittingSymbol_def, Multiset.mem_map] at hx
  obtain ⟨O, _, rfl⟩ := hx
  have : FiniteDimensional K (IntermediateField.fixedField
      (stabilizer Gal(SeparableClosure K/K) (Quotient.out O : Fin n))) :=
    ρ.finiteDimensional_fixedField_stabilizer O.out
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
          orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n)) = O} := by
    intro O
    have : FiniteDimensional K (IntermediateField.fixedField
        (stabilizer Gal(SeparableClosure K/K) (Quotient.out O : Fin n))) :=
      ρ.finiteDimensional_fixedField_stabilizer O.out
    exact (Nat.mul_div_cancel' (IntermediateField.inertiaDegree_dvd_finrank _)).trans
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
  rw [splittingSymbol_def] at h
  have hcard := congrArg Multiset.card h
  simp only [Multiset.card_map, Finset.card_val, Finset.card_univ, Multiset.card_singleton]
    at hcard
  have hne : Nonempty (orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n)) :=
    Fintype.card_pos_iff.1 (hcard ▸ one_pos)
  have : Subsingleton (orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n)) :=
    Fintype.card_le_one_iff_subsingleton.mp hcard.le
  have : Nonempty (Fin n) := ⟨hne.some.out⟩
  rw [isTransitive_def, MulAction.pretransitive_iff_unique_quotient_of_nonempty]
  exact ⟨uniqueOfSubsingleton hne.some⟩

/-- A labelled Galois set of size `f * e` (with `0 < f`, `0 < e`) has splitting symbol
`{(f, e)}` iff it is transitive and the stabilizer of `0` fixes a field of residue degree `f`. -/
theorem splittingSymbol_eq_singleton_iff {f e : ℕ} (hf : 0 < f) (he : 0 < e)
    (ρ : GaloisSet K (f * e)) :
    ρ.splittingSymbol = {(f, e)} ↔
      ρ.IsTransitive ∧
        (let := ρ.mulAction
        (IntermediateField.fixedField
          (stabilizer Gal(SeparableClosure K/K)
            (⟨0, Nat.mul_pos hf he⟩ : Fin (f * e)))).inertiaDegree = f) := by
  let i₀ : Fin (f * e) := ⟨0, Nat.mul_pos hf he⟩
  constructor
  · intro h
    have htrans := isTransitive_of_splittingSymbol_eq_singleton h
    refine ⟨htrans, ?_⟩
    rw [ρ.splittingSymbol_of_isTransitive htrans i₀, Multiset.singleton_inj] at h
    exact (Prod.ext_iff.1 h).1
  · rintro ⟨htrans, hdeg⟩
    rw [ρ.splittingSymbol_of_isTransitive htrans i₀]
    let := ρ.mulAction
    dsimp only
    rw [ρ.finrank_fixedField_stabilizer_of_isTransitive htrans i₀, hdeg,
      Nat.mul_div_cancel_left e hf]

/-- The discriminant exponent of a disjoint union of Galois sets is the sum of their
discriminant exponents. -/
@[simp]
theorem discriminantExponent_sigma {ι : Type*} [Fintype ι] {d : ι → ℕ}
    (b : Fin n ≃ Σ i, Fin (d i)) (ρ : ∀ i, GaloisSet K (d i)) :
    (sigma b ρ).discriminantExponent = ∑ i, (ρ i).discriminantExponent := by
  let : ∀ i, MulAction Gal(SeparableClosure K/K) (Fin (d i)) := fun i ↦ (ρ i).mulAction
  let := (sigma b ρ).mulAction
  have he (σ : Gal(SeparableClosure K/K)) (j : Fin n) : b (σ • j) = σ • b j := by
    rw [GaloisSet.smul_def, GaloisSet.sigma_val_apply, b.apply_symm_apply]
    rfl
  rw [discriminantExponent_def, orbitDiscriminantExponent_eq_of_equiv K b he,
    orbitDiscriminantExponent_sigma K]
  exact Finset.sum_congr rfl fun i _ ↦ (ρ i).discriminantExponent_def.symm

private theorem map_val_eq_sum_singleton {α β : Type*} (s : Finset α) (g : α → β) :
    s.val.map g = ∑ a ∈ s, ({g a} : Multiset β) := by
  rw [Finset.sum_eq_multiset_sum]
  exact (Multiset.sum_map_singleton (s.val.map g)).symm.trans
    (by rw [Multiset.map_map]; rfl)

/-- The splitting symbol of a disjoint union of Galois sets is the sum of their splitting
symbols. -/
@[simp]
theorem splittingSymbol_sigma {ι : Type*} [Fintype ι] {d : ι → ℕ}
    (b : Fin n ≃ Σ i, Fin (d i)) (ρ : ∀ i, GaloisSet K (d i)) :
    (sigma b ρ).splittingSymbol = ∑ i, (ρ i).splittingSymbol := by
  classical
  let : ∀ i, MulAction Gal(SeparableClosure K/K) (Fin (d i)) := fun i ↦ (ρ i).mulAction
  let := (sigma b ρ).mulAction
  let : ∀ i, Fintype (orbitRel.Quotient Gal(SeparableClosure K/K) (Fin (d i))) :=
    fun i ↦ Fintype.ofFinite _
  let := Fintype.ofFinite (orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n))
  have he (σ : Gal(SeparableClosure K/K)) (j : Fin n) : b (σ • j) = σ • b j := by
    rw [GaloisSet.smul_def, GaloisSet.sigma_val_apply, b.apply_symm_apply]
    rfl
  have he' (g : Gal(SeparableClosure K/K)) (j : Fin n) :
      b (g • j) = (MulEquiv.refl Gal(SeparableClosure K/K)) g • b j := he g j
  let E : orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n) ≃
      Σ i : ι, orbitRel.Quotient Gal(SeparableClosure K/K) (Fin (d i)) :=
    (MulAction.orbitRelQuotientCongr (MulEquiv.refl _) b he').trans
      MulAction.orbitRelQuotientSigmaEquiv
  have hs : ∀ p : Σ i : ι, orbitRel.Quotient Gal(SeparableClosure K/K) (Fin (d i)),
      (Quotient.mk'' (b.symm ⟨p.1, p.2.out⟩) :
        orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n)) = E.symm p := by
    rintro ⟨i, O⟩
    apply E.injective
    rw [E.apply_symm_apply]
    calc MulAction.orbitRelQuotientSigmaEquiv
          (MulAction.orbitRelQuotientCongr (MulEquiv.refl _) b he'
            (Quotient.mk'' (b.symm ⟨i, O.out⟩)))
        = MulAction.orbitRelQuotientSigmaEquiv (Quotient.mk'' (b (b.symm ⟨i, O.out⟩))) := by
            rw [MulAction.orbitRelQuotientCongr_mk]
      _ = ⟨i, O⟩ := by
            rw [b.apply_symm_apply, MulAction.orbitRelQuotientSigmaEquiv_mk, Quotient.out_eq']
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
      finrank_fixedField_stabilizer_out K (hs ⟨i, O⟩)]
    have hstab : stabilizer Gal(SeparableClosure K/K) (b.symm ⟨i, O.out⟩) =
        stabilizer Gal(SeparableClosure K/K) O.out :=
      (MulAction.stabilizer_eq_of_injective b b.injective he _).symm.trans (by simp)
    rw [hstab]
  rw [splittingSymbol_def, map_val_eq_sum_singleton]
  have hrhs : ∑ i : ι, (ρ i).splittingSymbol =
      ∑ p : Σ i : ι, orbitRel.Quotient Gal(SeparableClosure K/K) (Fin (d i)),
        ({(fun F : IntermediateField K (SeparableClosure K) =>
          (F.inertiaDegree, Module.finrank K F / F.inertiaDegree))
            (IntermediateField.fixedField
              (stabilizer Gal(SeparableClosure K/K) p.2.out))} : Multiset (ℕ × ℕ)) := by
    rw [Fintype.sum_sigma]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [splittingSymbol_def, map_val_eq_sum_singleton]
  rw [hrhs]
  exact (Fintype.sum_equiv E.symm _ _ fun p ↦
    congrArg (fun x ↦ ({x} : Multiset (ℕ × ℕ))) (hterm p).symm).symm

end GaloisSet

/-- **The transitive mass by residue degree** ([Bhargava 2007, §2]): for `0 < f` and `0 < e`, the
Galois sets of size `f * e` with splitting symbol `{(f, e)}` have mass
`1 / (f · q ^ (f * (e - 1)))`, where `q` is the residue cardinality of `K`. -/
theorem etaleMass_isTransitive_splittingSymbol (f e : ℕ) (hf : 0 < f) (he : 0 < e) :
    ((f * e)! : ℝ≥0∞)⁻¹ *
        ∑' ρ : {ρ : GaloisSet K (f * e) // ρ.splittingSymbol = {(f, e)}},
          1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ ρ.1.discriminantExponent =
      1 / ((f : ℝ≥0∞) * (Nat.card 𝓀[K] : ℝ≥0∞) ^ (f * (e - 1))) := by
  let i₀ : Fin (f * e) := ⟨0, Nat.mul_pos hf he⟩
  let g : IntermediateField K (SeparableClosure K) → ℝ≥0∞ := fun L ↦
    if L.inertiaDegree = f then 1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ L.discriminantExponent else 0
  have hbridge := GaloisSet.tsum_isTransitive (K := K) i₀ g
  let E₁ : {ρ : GaloisSet K (f * e) // ρ.splittingSymbol = {(f, e)}} ≃
      {ρ : {ρ : GaloisSet K (f * e) // ρ.IsTransitive} //
        (let := ρ.1.mulAction
        (IntermediateField.fixedField (stabilizer Gal(SeparableClosure K/K) i₀)).inertiaDegree =
          f)} :=
    (Equiv.subtypeEquivRight fun ρ ↦ GaloisSet.splittingSymbol_eq_singleton_iff hf he ρ).trans
      (Equiv.subtypeSubtypeEquivSubtypeInter _ _).symm
  have hlhs :
      ∑' ρ : {ρ : GaloisSet K (f * e) // ρ.splittingSymbol = {(f, e)}},
          1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ ρ.1.discriminantExponent =
        ∑' ρ : {ρ : GaloisSet K (f * e) // ρ.IsTransitive},
          (let := ρ.1.mulAction
          g (IntermediateField.fixedField (stabilizer Gal(SeparableClosure K/K) i₀))) := by
    have h₁ :
        (fun ρ : {ρ : GaloisSet K (f * e) // ρ.IsTransitive} ↦
          let := ρ.1.mulAction
          g (IntermediateField.fixedField (stabilizer Gal(SeparableClosure K/K) i₀))) =
        Set.indicator
          {ρ : {ρ : GaloisSet K (f * e) // ρ.IsTransitive} |
            let := ρ.1.mulAction
            (IntermediateField.fixedField
              (stabilizer Gal(SeparableClosure K/K) i₀)).inertiaDegree = f}
          (fun ρ ↦ 1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ ρ.1.discriminantExponent) := by
      ext ρ
      let := ρ.1.mulAction
      dsimp [g, Set.indicator]
      split_ifs with h
      · rw [ρ.1.discriminantExponent_of_isTransitive ρ.2 i₀]
      · rfl
    rw [h₁, ← tsum_subtype _ fun ρ : {ρ : GaloisSet K (f * e) // ρ.IsTransitive} ↦
      1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ ρ.1.discriminantExponent]
    exact E₁.tsum_eq fun ρ ↦ 1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ ρ.1.1.discriminantExponent
  let E₂ : {L : IntermediateField K (SeparableClosure K) // Module.finrank K L = f * e ∧
      L.inertiaDegree = f} ≃
      {L : {L : IntermediateField K (SeparableClosure K) // Module.finrank K L = f * e} //
        L.1.inertiaDegree = f} :=
    (Equiv.subtypeSubtypeEquivSubtypeInter _ _).symm
  have hrhs :
      ∑' L : {L : IntermediateField K (SeparableClosure K) // Module.finrank K L = f * e},
          g L.1 =
        (e : ℝ≥0∞) / (Nat.card 𝓀[K] : ℝ≥0∞) ^ (f * (e - 1)) := by
    have h₂ :
        (fun L : {L : IntermediateField K (SeparableClosure K) // Module.finrank K L = f * e} ↦
          g L.1) =
        Set.indicator
          {L : {L : IntermediateField K (SeparableClosure K) // Module.finrank K L = f * e} |
            L.1.inertiaDegree = f}
          (fun L ↦ 1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ L.1.discriminantExponent) := by
      ext L
      dsimp [g, Set.indicator]
      split_ifs <;> rfl
    rw [h₂, ← tsum_subtype _ fun L : {L : IntermediateField K (SeparableClosure K) //
        Module.finrank K L = f * e} ↦
      1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ L.1.discriminantExponent]
    calc
      (∑' L : {L : {L : IntermediateField K (SeparableClosure K) //
          Module.finrank K L = f * e} | L.1.inertiaDegree = f},
          1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ L.1.1.discriminantExponent)
        = ∑' L : {L : IntermediateField K (SeparableClosure K) //
            Module.finrank K L = f * e ∧ L.inertiaDegree = f},
            1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ L.1.discriminantExponent :=
          (E₂.tsum_eq
            fun L ↦ 1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ L.1.1.discriminantExponent).symm
      _ = (e : ℝ≥0∞) / (Nat.card 𝓀[K] : ℝ≥0∞) ^ (f * (e - 1)) :=
          tsum_inertiaDegree_eq (K := K) hf.ne' e
  rw [hlhs, hbridge, hrhs]
  have hfe : (f * e)! = (f * e) * (f * e - 1)! :=
    (Nat.mul_factorial_pred (Nat.mul_pos hf he).ne').symm
  have hfac_ne_zero : (((f * e - 1)! : ℕ) : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast (Nat.factorial_pos _).ne'
  have hfac_ne_top : (((f * e - 1)! : ℕ) : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  have hf_ne_zero : (f : ℝ≥0∞) ≠ 0 := by exact_mod_cast hf.ne'
  have he_ne_zero : (e : ℝ≥0∞) ≠ 0 := by exact_mod_cast he.ne'
  have hf_ne_top : (f : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  have he_ne_top : (e : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  rw [hfe, Nat.cast_mul, ENNReal.mul_inv (Or.inl (by simp [hf.ne', he.ne']))
    (Or.inl (ENNReal.natCast_ne_top (f * e)))]
  calc
    (((f * e : ℕ) : ℝ≥0∞)⁻¹ * ((f * e - 1)! : ℝ≥0∞)⁻¹) *
        (((f * e - 1)! : ℝ≥0∞) *
          ((e : ℝ≥0∞) / (Nat.card 𝓀[K] : ℝ≥0∞) ^ (f * (e - 1))))
      = ((f * e : ℕ) : ℝ≥0∞)⁻¹ *
          ((((f * e - 1)! : ℝ≥0∞)⁻¹ * ((f * e - 1)! : ℝ≥0∞)) *
            ((e : ℝ≥0∞) / (Nat.card 𝓀[K] : ℝ≥0∞) ^ (f * (e - 1)))) := by ring
    _ = ((f : ℝ≥0∞) * (e : ℝ≥0∞))⁻¹ *
          ((e : ℝ≥0∞) / (Nat.card 𝓀[K] : ℝ≥0∞) ^ (f * (e - 1))) := by
        rw [ENNReal.inv_mul_cancel hfac_ne_zero hfac_ne_top, one_mul, Nat.cast_mul]
    _ = ((f : ℝ≥0∞)⁻¹ * ((e : ℝ≥0∞)⁻¹ * (e : ℝ≥0∞))) /
          (Nat.card 𝓀[K] : ℝ≥0∞) ^ (f * (e - 1)) := by
        rw [ENNReal.mul_inv (Or.inl hf_ne_zero) (Or.inl hf_ne_top)]
        simp only [div_eq_mul_inv]
        ring
    _ = 1 / ((f : ℝ≥0∞) * (Nat.card 𝓀[K] : ℝ≥0∞) ^ (f * (e - 1))) := by
        rw [ENNReal.inv_mul_cancel he_ne_zero he_ne_top, mul_one, div_eq_mul_inv, div_eq_mul_inv,
          one_mul, ENNReal.mul_inv (Or.inl hf_ne_zero) (Or.inl hf_ne_top)]

end TauCeti
