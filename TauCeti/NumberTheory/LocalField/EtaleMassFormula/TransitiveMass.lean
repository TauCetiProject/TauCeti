/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.Galois.GaloisSet.Relabelling
public import TauCeti.FieldTheory.Galois.GaloisSet.Sum
public import TauCeti.NumberTheory.LocalField.EtaleMassFormula.Mass
public import TauCeti.NumberTheory.LocalField.Unramified.IntermediateField
import TauCeti.FieldTheory.Galois.FixedField
import TauCeti.NumberTheory.LocalField.EtaleMassFormula.SubfieldCount

/-!
# Splitting symbols of Galois sets and the transitive mass by residue degree

For a nonarchimedean local field `K` with `q` residue classes, the *splitting symbol*
`GaloisSet.splittingSymbol ρ` of a labelled Galois set `ρ : GaloisSet K n` is the multiset, over
the orbits of `ρ`, of the pair `(f, e)` of residue degree and ramification index of the fixed field
of a point stabilizer ([Bhargava 2007, (2.1)]). Conjugate stabilizers fix `K`-isomorphic fields, so
each orbit contributes a well-defined pair of positive integers, and their products `f · e` add up
to `n`.

Both the discriminant exponent and the splitting symbol are invariant under equivariant bijection
and additive on disjoint unions (`GaloisSet.discriminantExponent_sumCongr` and
`GaloisSet.splittingSymbol_sumCongr`). A labelled Galois set of size `f * e` with a label `i` has
splitting symbol `{(f, e)}` precisely when it is transitive and its point stabilizers fix
subextensions of residue degree `f` (`GaloisSet.splittingSymbol_eq_singleton_iff`).

Combining the transitive Galois-set bridge `GaloisSet.tsum_isTransitive` with the subfield count by
residue degree `TauCeti.tsum_inertiaDegree_eq` gives the mass of the Galois sets with splitting
symbol `{(f, e)}` (`TauCeti.etaleMass_isTransitive_splittingSymbol`):
`((f * e)!)⁻¹ ∑_{ρ : σ(ρ) = {(f, e)}} q ^ (-d(ρ)) = 1 / (f · q ^ (f(e - 1)))`.

## Main definitions and results

* `TauCeti.GaloisSet.splittingSymbol`: the multiset of pairs `(f, e)` over the orbits of a labelled
  Galois set.
* `TauCeti.GaloisSet.splittingSymbol_eq_of_equiv`, `TauCeti.GaloisSet.splittingSymbol_smul`:
  invariance under equivariant bijection and relabelling.
* `TauCeti.GaloisSet.pos_of_mem_splittingSymbol`, `TauCeti.GaloisSet.sum_map_mul_splittingSymbol`:
  positivity of `(f, e)` and the degree identity `∑ f · e = n`.
* `TauCeti.GaloisSet.discriminantExponent_sumCongr`, `TauCeti.GaloisSet.splittingSymbol_sumCongr`:
  additivity of discriminant exponent and splitting symbol under `GaloisSet.sumCongr`.
* `TauCeti.GaloisSet.splittingSymbol_eq_singleton_iff`: characterisation of transitive Galois sets
  with splitting symbol `{(f, e)}`.
* `TauCeti.etaleMass_isTransitive_splittingSymbol`: the mass of the Galois sets of size `f * e`
  with splitting symbol `{(f, e)}` is `1 / (f · q ^ (f(e - 1)))`.

## References

* M. Bhargava, *Mass formulae for extensions of local fields, and conjectures on the density of
  number field discriminants*, IMRN **2007**, rnm052, §2.
* K. S. Kedlaya, *Mass formulas for local Galois representations*, IMRN **2007**, rnm021.
-/

public section

noncomputable section

open ValuativeRel
open scoped Nat ENNReal

namespace TauCeti

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

private theorem inertiaDegree_dvd_finrank (L : IntermediateField K (SeparableClosure K)) :
    L.inertiaDegree ∣ Module.finrank K L := by
  by_cases h : Module.Finite K L
  · rw [L.inertiaDegree_eq]
    let _ := finiteIntermediateFieldValuativeRel K (SeparableClosure K) L
    let _ := finiteIntermediateFieldTopology K (SeparableClosure K) L
    have := finiteIntermediateField_isNonarchimedeanLocalField K (SeparableClosure K) L
    have := finiteIntermediateField_valuativeExtension K (SeparableClosure K) L
    exact ⟨ramificationIndex K L,
      (ramificationIndex_mul_inertiaDegree K L).symm.trans (mul_comm _ _)⟩
  · rw [L.inertiaDegree_of_not_finite h, Module.finrank_of_not_finite h]

private theorem pair_fixedField_stabilizer_smul {X : Type*}
    [MulAction Gal(SeparableClosure K/K) X] (σ : Gal(SeparableClosure K/K)) (x : X) :
    (let F := IntermediateField.fixedField (MulAction.stabilizer Gal(SeparableClosure K/K) (σ • x));
      (F.inertiaDegree, Module.finrank K F / F.inertiaDegree)) =
      (let F := IntermediateField.fixedField (MulAction.stabilizer Gal(SeparableClosure K/K) x);
        (F.inertiaDegree, Module.finrank K F / F.inertiaDegree)) := by
  have heq : IntermediateField.fixedField
        (MulAction.stabilizer Gal(SeparableClosure K/K) (σ • x)) =
      (IntermediateField.fixedField
        (MulAction.stabilizer Gal(SeparableClosure K/K) x)).map σ.toAlgHom := by
    rw [MulAction.stabilizer_smul_eq_stabilizer_map_conj, MulEquiv.toMonoidHom_eq_coe,
      Subgroup.fixedField_map_conj]
  let e := (IntermediateField.fixedField
    (MulAction.stabilizer Gal(SeparableClosure K/K) x)).equivMap σ.toAlgHom
  have hf : ((IntermediateField.fixedField
      (MulAction.stabilizer Gal(SeparableClosure K/K) x)).map σ.toAlgHom).inertiaDegree =
      (IntermediateField.fixedField
        (MulAction.stabilizer Gal(SeparableClosure K/K) x)).inertiaDegree :=
    (IntermediateField.inertiaDegree_eq_of_algEquiv e).symm
  have hd : Module.finrank K ((IntermediateField.fixedField
      (MulAction.stabilizer Gal(SeparableClosure K/K) x)).map σ.toAlgHom) =
      Module.finrank K (IntermediateField.fixedField
        (MulAction.stabilizer Gal(SeparableClosure K/K) x)) :=
    e.symm.toLinearEquiv.finrank_eq
  dsimp only
  rw [heq, hf, hd]

private theorem pair_fixedField_stabilizer_out {X : Type*}
    [MulAction Gal(SeparableClosure K/K) X]
    {ω : MulAction.orbitRel.Quotient Gal(SeparableClosure K/K) X} {x : X}
    (hx : (Quotient.mk'' x : MulAction.orbitRel.Quotient Gal(SeparableClosure K/K) X) = ω) :
    (let F := IntermediateField.fixedField (MulAction.stabilizer Gal(SeparableClosure K/K) ω.out);
      (F.inertiaDegree, Module.finrank K F / F.inertiaDegree)) =
      (let F := IntermediateField.fixedField (MulAction.stabilizer Gal(SeparableClosure K/K) x);
        (F.inertiaDegree, Module.finrank K F / F.inertiaDegree)) := by
  obtain ⟨σ, rfl⟩ := MulAction.exists_smul_out_eq hx
  exact (pair_fixedField_stabilizer_smul σ ω.out).symm

namespace GaloisSet

variable {n : ℕ}

open Classical in
/-- The **splitting symbol** of a labelled Galois set ([Bhargava 2007, (2.1)]): the multiset,
over its orbits, of the pair `(f, e)` of residue degree and ramification index of the fixed field
of the stabilizer of a point of the orbit. -/
def splittingSymbol (ρ : GaloisSet K n) : Multiset (ℕ × ℕ) :=
  letI := ρ.mulAction
  haveI := Fintype.ofFinite (MulAction.orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n))
  (Finset.univ : Finset (MulAction.orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n))).val.map
    fun ω ↦
      let F := IntermediateField.fixedField (MulAction.stabilizer Gal(SeparableClosure K/K) ω.out)
      (F.inertiaDegree, Module.finrank K F / F.inertiaDegree)

open Classical in
/-- Defining formula of `GaloisSet.splittingSymbol`. -/
theorem splittingSymbol_def (ρ : GaloisSet K n) :
    ρ.splittingSymbol =
      (letI := ρ.mulAction
      haveI := Fintype.ofFinite (MulAction.orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n))
      (Finset.univ :
        Finset (MulAction.orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n))).val.map fun ω ↦
        let F := IntermediateField.fixedField (MulAction.stabilizer Gal(SeparableClosure K/K) ω.out)
        (F.inertiaDegree, Module.finrank K F / F.inertiaDegree)) :=
  (rfl)

/-- Equivariant bijections preserve the splitting symbol of labelled Galois sets. -/
theorem splittingSymbol_eq_of_equiv {m : ℕ} (ρ : GaloisSet K n) (τ : GaloisSet K m)
    (e : Fin n ≃ Fin m)
    (he : ∀ (σ : Gal(SeparableClosure K/K)) (i : Fin n), e (ρ.val σ i) = τ.val σ (e i)) :
    ρ.splittingSymbol = τ.splittingSymbol := by
  classical
  rw [splittingSymbol_def, splittingSymbol_def]
  let := ρ.mulAction
  let := τ.mulAction
  let := Fintype.ofFinite (MulAction.orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n))
  let := Fintype.ofFinite (MulAction.orbitRel.Quotient Gal(SeparableClosure K/K) (Fin m))
  let E := MulAction.orbitRelQuotientCongr (MulEquiv.refl Gal(SeparableClosure K/K)) e he
  rw [← congrArg Finset.val (Finset.map_univ_equiv E), Finset.map_val, Equiv.coe_toEmbedding,
    Multiset.map_map]
  refine Multiset.map_congr rfl fun ω _ ↦ ?_
  dsimp only [Function.comp_apply]
  have hE : (Quotient.mk'' (e ω.out) :
      MulAction.orbitRel.Quotient Gal(SeparableClosure K/K) (Fin m)) = E ω := by
    rw [← MulAction.orbitRelQuotientCongr_mk (MulEquiv.refl _) e he, Quotient.out_eq']
  rw [pair_fixedField_stabilizer_out hE,
    MulAction.stabilizer_eq_of_injective e e.injective he ω.out]

/-- Relabelling a Galois set does not change its splitting symbol. -/
@[simp]
theorem splittingSymbol_smul (ρ : GaloisSet K n) (e : Equiv.Perm (Fin n)) :
    (e • ρ).splittingSymbol = ρ.splittingSymbol :=
  (ρ.splittingSymbol_eq_of_equiv (e • ρ) e (by simp)).symm

/-- The number of factors of `ρ.splittingSymbol` is the number of orbits of `ρ`. -/
@[simp]
theorem card_splittingSymbol (ρ : GaloisSet K n) :
    Multiset.card ρ.splittingSymbol =
      (letI := ρ.mulAction
      Nat.card (MulAction.orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n))) := by
  classical
  rw [splittingSymbol_def]
  let := ρ.mulAction
  let := Fintype.ofFinite (MulAction.orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n))
  rw [Multiset.card_map, Finset.card_val, Finset.card_univ, Nat.card_eq_fintype_card]

/-- Every factor `(f, e)` of `ρ.splittingSymbol` is a pair of positive integers. -/
theorem pos_of_mem_splittingSymbol (ρ : GaloisSet K n) {x : ℕ × ℕ}
    (hx : x ∈ ρ.splittingSymbol) : 0 < x.1 ∧ 0 < x.2 := by
  classical
  rw [splittingSymbol_def] at hx
  let := ρ.mulAction
  let := Fintype.ofFinite (MulAction.orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n))
  obtain ⟨ω, -, rfl⟩ := Multiset.mem_map.1 hx
  set F := IntermediateField.fixedField (MulAction.stabilizer Gal(SeparableClosure K/K) ω.out)
  have : FiniteDimensional K F := ρ.finiteDimensional_fixedField_stabilizer ω.out
  have hf : 0 < F.inertiaDegree := F.inertiaDegree_pos
  have hmul : F.inertiaDegree * (Module.finrank K F / F.inertiaDegree) = Module.finrank K F :=
    Nat.mul_div_cancel' (inertiaDegree_dvd_finrank F)
  have hpos : 0 < Module.finrank K F := Module.finrank_pos
  refine ⟨hf, Nat.pos_of_ne_zero fun h0 ↦ ?_⟩
  dsimp only at h0
  rw [h0, mul_zero] at hmul
  exact hpos.ne hmul

/-- The degree `(ρ.splittingSymbol.map fun x ↦ x.1 * x.2).sum` of the splitting symbol of `ρ`
is `n`. -/
@[simp]
theorem sum_map_mul_splittingSymbol (ρ : GaloisSet K n) :
    (ρ.splittingSymbol.map fun x ↦ x.1 * x.2).sum = n := by
  classical
  let := ρ.mulAction
  let := Fintype.ofFinite (MulAction.orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n))
  have hsum : (ρ.splittingSymbol.map fun x ↦ x.1 * x.2).sum =
      ∑ ω : MulAction.orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n),
        Nat.card (MulAction.orbit Gal(SeparableClosure K/K) ω.out) := by
    rw [splittingSymbol_def, Multiset.map_map]
    refine congrArg Multiset.sum (Multiset.map_congr rfl fun ω _ ↦ ?_)
    dsimp only [Function.comp_apply]
    rw [Nat.mul_div_cancel' (inertiaDegree_dvd_finrank _), ρ.finrank_fixedField_stabilizer]
  rw [hsum]
  let e : Fin n ≃ Σ ω : MulAction.orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n),
      MulAction.orbit Gal(SeparableClosure K/K) ω.out :=
    (MulAction.selfEquivSigmaOrbitsQuotientStabilizer Gal(SeparableClosure K/K) (Fin n)).trans
      (Equiv.sigmaCongrRight fun ω ↦
        (MulAction.orbitEquivQuotientStabilizer Gal(SeparableClosure K/K) ω.out).symm)
  have hcard := Fintype.card_congr e
  simpa [Nat.card_eq_fintype_card, Fintype.card_sigma] using hcard.symm

/-- A Galois set of size zero has the empty splitting symbol. -/
@[simp]
theorem splittingSymbol_zero (ρ : GaloisSet K 0) : ρ.splittingSymbol = 0 := by
  rw [← Multiset.card_eq_zero, card_splittingSymbol]
  let := ρ.mulAction
  exact Nat.card_eq_zero.2 (.inl inferInstance)

/-- The trivial Galois set of size `n` has splitting symbol `n • {(1, 1)}`. -/
@[simp]
theorem splittingSymbol_trivial :
    (trivial K n).splittingSymbol = Multiset.replicate n (1, 1) := by
  refine Multiset.eq_replicate.2 ⟨?_, fun x hx ↦ ?_⟩
  · rw [card_splittingSymbol]
    let := (trivial K n).mulAction
    have hbij : Function.Bijective
        (Quotient.mk'' : Fin n →
          MulAction.orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n)) :=
      ⟨fun i j h ↦ by
        obtain ⟨σ, hσ⟩ := Quotient.exact h
        dsimp only at hσ
        rw [smul_def, trivial_val_apply] at hσ
        exact hσ.symm, Quotient.mk''_surjective⟩
    simpa using (Nat.card_eq_of_bijective _ hbij).symm
  · classical
    rw [splittingSymbol_def] at hx
    let := (trivial K n).mulAction
    let := Fintype.ofFinite (MulAction.orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n))
    obtain ⟨ω, -, rfl⟩ := Multiset.mem_map.1 hx
    dsimp only
    rw [fixedField_stabilizer_trivial]
    simp

/-- A transitive Galois set has a singleton splitting symbol `(f, n / f)`, computed at any label
`i`. -/
theorem splittingSymbol_of_isTransitive (ρ : GaloisSet K n) (hρ : ρ.IsTransitive) (i : Fin n) :
    ρ.splittingSymbol =
      {letI := ρ.mulAction
        let F := IntermediateField.fixedField (MulAction.stabilizer Gal(SeparableClosure K/K) i)
        (F.inertiaDegree, n / F.inertiaDegree)} := by
  classical
  rw [splittingSymbol_def]
  let := ρ.mulAction
  have : Nonempty (Fin n) := ⟨i⟩
  have : MulAction.IsPretransitive Gal(SeparableClosure K/K) (Fin n) := ρ.isTransitive_def.1 hρ
  let := ((MulAction.pretransitive_iff_unique_quotient_of_nonempty
    Gal(SeparableClosure K/K) (Fin n)).mp inferInstance).some
  let := Fintype.ofFinite (MulAction.orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n))
  have huniv : (Finset.univ :
      Finset (MulAction.orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n))).val =
      {Quotient.mk'' i} := by
    have : (Finset.univ :
        Finset (MulAction.orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n))) =
        {Quotient.mk'' i} := by
      ext ω
      simp only [Finset.mem_univ, Finset.mem_singleton, true_iff]
      exact Subsingleton.elim _ _
    exact congrArg Finset.val this
  rw [huniv, Multiset.map_singleton,
    pair_fixedField_stabilizer_out (ω := Quotient.mk'' i) (x := i) rfl]
  dsimp only
  rw [ρ.finrank_fixedField_stabilizer_of_isTransitive hρ i]

/-- A Galois set whose splitting symbol has at most one factor has at most one orbit, hence is
transitive. -/
theorem isTransitive_of_card_splittingSymbol_le_one (ρ : GaloisSet K n)
    (h : Multiset.card ρ.splittingSymbol ≤ 1) : ρ.IsTransitive := by
  classical
  rw [card_splittingSymbol] at h
  let := ρ.mulAction
  let := Fintype.ofFinite (MulAction.orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n))
  rw [Nat.card_eq_fintype_card, Fintype.card_le_one_iff_subsingleton] at h
  rw [ρ.isTransitive_def]
  exact (MulAction.pretransitive_iff_subsingleton_quotient Gal(SeparableClosure K/K) (Fin n)).2 h

/-- A Galois set `ρ` of size `f * e` with a label `i` has splitting symbol `{(f, e)}` if and only
if `ρ` is transitive and the fixed field of the stabilizer of `i` has residue degree `f`. -/
theorem splittingSymbol_eq_singleton_iff {f e : ℕ} (ρ : GaloisSet K (f * e)) (i : Fin (f * e)) :
    ρ.splittingSymbol = {(f, e)} ↔
      ρ.IsTransitive ∧
        (letI := ρ.mulAction
        (IntermediateField.fixedField
          (MulAction.stabilizer Gal(SeparableClosure K/K) i)).inertiaDegree = f) := by
  have hf : 0 < f := Nat.pos_of_ne_zero fun h0 ↦ by simp [h0] at i; exact i.elim0
  constructor
  · intro h
    have htr : ρ.IsTransitive :=
      ρ.isTransitive_of_card_splittingSymbol_le_one (by rw [h]; simp)
    refine ⟨htr, ?_⟩
    rw [ρ.splittingSymbol_of_isTransitive htr i, Multiset.singleton_inj, Prod.mk.injEq] at h
    exact h.1
  · rintro ⟨htr, hdeg⟩
    rw [ρ.splittingSymbol_of_isTransitive htr i]
    dsimp only at hdeg ⊢
    rw [hdeg, Nat.mul_div_right e hf]

/-- Combining two labelled Galois sets along a bijection adds their discriminant exponents. -/
@[simp]
theorem discriminantExponent_sumCongr {m k : ℕ} (e : Fin m ⊕ Fin k ≃ Fin n)
    (ρ₁ : GaloisSet K m) (ρ₂ : GaloisSet K k) :
    (sumCongr e ρ₁ ρ₂).discriminantExponent =
      ρ₁.discriminantExponent + ρ₂.discriminantExponent := by
  let := ρ₁.mulAction
  let := ρ₂.mulAction
  have heq : (sumCongr e ρ₁ ρ₂).discriminantExponent =
      orbitDiscriminantExponent K (Fin m ⊕ Fin k) := by
    rw [discriminantExponent_def]
    let := (sumCongr e ρ₁ ρ₂).mulAction
    exact (orbitDiscriminantExponent_eq_of_equiv K e fun σ x ↦ by
      rcases x with i | j
      · exact (sumCongr_val_apply_inl e ρ₁ ρ₂ σ i).symm
      · exact (sumCongr_val_apply_inr e ρ₁ ρ₂ σ j).symm).symm
  rw [heq, orbitDiscriminantExponent_sum, ← discriminantExponent_def, ← discriminantExponent_def]

/-- Combining two labelled Galois sets along a bijection adds their splitting symbols. -/
@[simp]
theorem splittingSymbol_sumCongr {m k : ℕ} (e : Fin m ⊕ Fin k ≃ Fin n)
    (ρ₁ : GaloisSet K m) (ρ₂ : GaloisSet K k) :
    (sumCongr e ρ₁ ρ₂).splittingSymbol = ρ₁.splittingSymbol + ρ₂.splittingSymbol := by
  classical
  rw [splittingSymbol_def, splittingSymbol_def, splittingSymbol_def]
  let E := orbitRelQuotientSumCongr e ρ₁ ρ₂
  let := ρ₁.mulAction
  let := ρ₂.mulAction
  let := Fintype.ofFinite (MulAction.orbitRel.Quotient Gal(SeparableClosure K/K) (Fin m))
  let := Fintype.ofFinite (MulAction.orbitRel.Quotient Gal(SeparableClosure K/K) (Fin k))
  let := (sumCongr e ρ₁ ρ₂).mulAction
  let := Fintype.ofFinite (MulAction.orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n))
  rw [← congrArg Finset.val (Finset.map_univ_equiv E), Finset.map_val, Equiv.coe_toEmbedding,
    ← Finset.univ_disjSum_univ, Finset.val_disjSum, Multiset.map_map, Multiset.map_disjSum]
  congr 1
  · refine Multiset.map_congr rfl fun ω₁ _ ↦ ?_
    dsimp only [Function.comp_apply]
    have hE : (Quotient.mk'' (e (Sum.inl ω₁.out)) :
        MulAction.orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n)) = E (Sum.inl ω₁) := by
      rw [← orbitRelQuotientSumCongr_inl_mk e ρ₁ ρ₂ ω₁.out, Quotient.out_eq']
    rw [pair_fixedField_stabilizer_out hE, stabilizer_sumCongr_inl]
  · refine Multiset.map_congr rfl fun ω₂ _ ↦ ?_
    dsimp only [Function.comp_apply]
    have hE : (Quotient.mk'' (e (Sum.inr ω₂.out)) :
        MulAction.orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n)) = E (Sum.inr ω₂) := by
      rw [← orbitRelQuotientSumCongr_inr_mk e ρ₁ ρ₂ ω₂.out, Quotient.out_eq']
    rw [pair_fixedField_stabilizer_out hE, stabilizer_sumCongr_inr]

end GaloisSet

/-- **The transitive mass by residue degree** ([Bhargava 2007, §2]): for `f, e > 0`, the labelled
Galois sets of size `f * e` with splitting symbol `{(f, e)}` have mass
`1 / (f · q ^ (f(e - 1)))`, where `q` is the residue cardinality of `K`. -/
theorem etaleMass_isTransitive_splittingSymbol (f e : ℕ) (hf : 0 < f) (he : 0 < e) :
    ((f * e)! : ℝ≥0∞)⁻¹ *
        ∑' ρ : {ρ : GaloisSet K (f * e) // ρ.splittingSymbol = {(f, e)}},
          1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ ρ.1.discriminantExponent =
      1 / ((f : ℝ≥0∞) * (Nat.card 𝓀[K] : ℝ≥0∞) ^ (f * (e - 1))) := by
  classical
  let i₀ : Fin (f * e) := ⟨0, Nat.mul_pos hf he⟩
  -- Rewrite the subtype sum via `splittingSymbol_eq_singleton_iff` as a sum over transitive
  -- Galois sets with an indicator on the residue degree of the fixed field of `stabilizer G i₀`.
  let g : IntermediateField K (SeparableClosure K) → ℝ≥0∞ := fun L ↦
    if L.inertiaDegree = f then 1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ L.discriminantExponent else 0
  have htsum₁ : ∑' ρ : {ρ : GaloisSet K (f * e) // ρ.splittingSymbol = {(f, e)}},
        1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ ρ.1.discriminantExponent =
      ∑' ρ : {ρ : GaloisSet K (f * e) // ρ.IsTransitive},
        (letI := ρ.1.mulAction
        g (IntermediateField.fixedField (MulAction.stabilizer Gal(SeparableClosure K/K) i₀))) := by
    let ε : {ρ : GaloisSet K (f * e) // ρ.splittingSymbol = {(f, e)}} ≃
        {ρ : {ρ : GaloisSet K (f * e) // ρ.IsTransitive} //
          letI := ρ.1.mulAction
          (IntermediateField.fixedField
            (MulAction.stabilizer Gal(SeparableClosure K/K) i₀)).inertiaDegree = f} :=
      (Equiv.subtypeEquivRight fun ρ ↦
        GaloisSet.splittingSymbol_eq_singleton_iff ρ i₀).trans
        (Equiv.subtypeSubtypeEquivSubtypeInter
          (fun ρ : GaloisSet K (f * e) ↦ ρ.IsTransitive)
          (fun ρ ↦ letI := ρ.mulAction
            (IntermediateField.fixedField
              (MulAction.stabilizer Gal(SeparableClosure K/K) i₀)).inertiaDegree = f)).symm
    rw [← ε.symm.tsum_eq]
    have hsub := _root_.tsum_subtype
      (s := {ρ : {ρ : GaloisSet K (f * e) // ρ.IsTransitive} |
        letI := ρ.1.mulAction
        (IntermediateField.fixedField
          (MulAction.stabilizer Gal(SeparableClosure K/K) i₀)).inertiaDegree = f})
      (fun ρ : {ρ : GaloisSet K (f * e) // ρ.IsTransitive} ↦
        1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ ρ.1.discriminantExponent)
    refine (tsum_congr fun ρ ↦ ?_).trans (hsub.trans (tsum_congr fun ρ ↦ ?_))
    · rfl
    · simp only [Set.indicator_apply, Set.mem_ofPred_eq, g]
      rw [ρ.1.discriminantExponent_of_isTransitive ρ.2 i₀]
  have htsum₂ : ∑' L : {L : IntermediateField K (SeparableClosure K) //
        Module.finrank K L = f * e}, g L.1 =
      e / (Nat.card 𝓀[K] : ℝ≥0∞) ^ (f * (e - 1)) := by
    let δ : {L : {L : IntermediateField K (SeparableClosure K) // Module.finrank K L = f * e} //
        L.1.inertiaDegree = f} ≃
        {L : IntermediateField K (SeparableClosure K) //
          Module.finrank K L = f * e ∧ L.inertiaDegree = f} :=
      Equiv.subtypeSubtypeEquivSubtypeInter
        (fun L : IntermediateField K (SeparableClosure K) ↦ Module.finrank K L = f * e)
        (fun L ↦ L.inertiaDegree = f)
    have hsub := (_root_.tsum_subtype
      (s := {L : {L : IntermediateField K (SeparableClosure K) // Module.finrank K L = f * e} |
        L.1.inertiaDegree = f})
      (fun L : {L : IntermediateField K (SeparableClosure K) // Module.finrank K L = f * e} ↦
        1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ L.1.discriminantExponent)).symm
    refine (tsum_congr fun L ↦ ?_).trans (hsub.trans ?_)
    · simp [Set.indicator_apply, g]
    · exact (δ.tsum_eq (fun L ↦ 1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ L.1.discriminantExponent)).trans
        (tsum_inertiaDegree_eq hf.ne' e)
  rw [htsum₁, GaloisSet.tsum_isTransitive i₀ g, htsum₂]
  -- Cancel `(f * e - 1)! * e` against `((f * e)!)⁻¹ = (f * (e * (f * e - 1)!))⁻¹`.
  have hfac : (f * e)! = f * (e * (f * e - 1)!) := by
    have h := Nat.mul_factorial_pred (Nat.mul_pos hf he).ne'
    linarith [mul_assoc f e (f * e - 1)!]
  have hf0 : (f : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.2 hf.ne'
  have hm0 : ((e * (f * e - 1)! : ℕ) : ℝ≥0∞) ≠ 0 :=
    Nat.cast_ne_zero.2 (Nat.mul_ne_zero he.ne' (Nat.factorial_ne_zero _))
  have hmtop : ((e * (f * e - 1)! : ℕ) : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  rw [hfac, Nat.cast_mul, ENNReal.mul_inv (.inl hf0) (.inr hm0), mul_assoc]
  have hmid : ((e * (f * e - 1)! : ℕ) : ℝ≥0∞)⁻¹ *
      (((f * e - 1)! : ℝ≥0∞) * ((e : ℝ≥0∞) / (Nat.card 𝓀[K] : ℝ≥0∞) ^ (f * (e - 1)))) =
      1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ (f * (e - 1)) := by
    rw [div_eq_mul_inv, ← mul_assoc (((f * e - 1)! : ℝ≥0∞)),
      mul_comm (((f * e - 1)! : ℝ≥0∞)) (e : ℝ≥0∞),
      ← Nat.cast_mul, ← mul_assoc, ENNReal.inv_mul_cancel hm0 hmtop, one_mul, one_div]
  rw [hmid, one_div, one_div]
  exact (ENNReal.mul_inv (.inl hf0) (.inr (pow_ne_zero _ (Nat.cast_ne_zero.2 (NeZero.ne _))))).symm

end TauCeti
