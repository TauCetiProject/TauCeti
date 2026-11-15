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

For a nonarchimedean local field `K` with residue cardinality `q`, a labelled Galois set
`ρ : TauCeti.GaloisSet K n` decomposes into finitely many `Gal(SeparableClosure K / K)`-orbits, and
the fixed field `F` of a point stabilizer in an orbit is a finite separable extension of `K` whose
`K`-isomorphism class depends only on the orbit. Its *splitting symbol*
`TauCeti.GaloisSet.splittingSymbol ρ` [Bhargava 2007, (2.1)] is the multiset, over the orbits, of
the pairs `(f, e)` of residue degree `f = F.inertiaDegree` and ramification index
`e = [F : K] / f`.

The splitting symbol is invariant under equivariant bijections and relabellings, additive on
disjoint unions `TauCeti.GaloisSet.sumCongr`, consists of pairs of positive integers with
`∑ f e = n`, and has a single element `{(f, e)}` precisely when `n = f * e`, `ρ` is transitive, and
the stabilizer fixed fields have residue degree `f`.

Combining the transitive Galois-set bridge `TauCeti.GaloisSet.tsum_isTransitive` with the subfield
count `TauCeti.tsum_inertiaDegree_eq` gives the transitive mass formula for a prescribed splitting
symbol (`TauCeti.etaleMass_isTransitive_splittingSymbol`): for `f, e > 0`, the labelled Galois sets
of size `f * e` with splitting symbol `{(f, e)}` have mass `1 / (f · q ^ (f (e - 1)))`.

## Main definitions and results

* `TauCeti.GaloisSet.discriminantExponent_sumCongr`: additivity of discriminant exponents on
  disjoint unions of Galois sets.
* `TauCeti.GaloisSet.splittingSymbol`: the multiset of `(f, e)` pairs over the orbits of a Galois
  set.
* `TauCeti.GaloisSet.splittingSymbol_sumCongr`: additivity of splitting symbols on disjoint unions.
* `TauCeti.GaloisSet.pos_of_mem_splittingSymbol` and
  `TauCeti.GaloisSet.sum_map_mul_splittingSymbol`: every pair in `ρ.splittingSymbol` has positive
  entries and `∑ f e = n`.
* `TauCeti.GaloisSet.splittingSymbol_eq_singleton_iff`: characterization of Galois sets with
  singleton splitting symbol `{(f, e)}`.
* `TauCeti.etaleMass_isTransitive_splittingSymbol`: the mass of Galois sets of size `f * e` with
  splitting symbol `{(f, e)}` equals `1 / (f · q ^ (f (e - 1)))`.

## References

* M. Bhargava, *Mass formulae for extensions of local fields, and conjectures on the density of
  number field discriminants*, IMRN **2007**, rnm052, §2.
* K. S. Kedlaya, *Mass formulas for local Galois representations*, IMRN **2007**, rnm021.
-/

public section

noncomputable section

open ValuativeRel
open scoped ENNReal Nat

namespace TauCeti

universe u

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

namespace GaloisSet

variable {n : ℕ}

/-- The discriminant exponent of a disjoint union `sumCongr e ρ₁ ρ₂` is the sum of the discriminant
exponents of `ρ₁` and `ρ₂`. -/
@[simp]
theorem discriminantExponent_sumCongr {m l : ℕ} (e : Fin m ⊕ Fin l ≃ Fin n)
    (ρ₁ : GaloisSet K m) (ρ₂ : GaloisSet K l) :
    (sumCongr e ρ₁ ρ₂).discriminantExponent =
      ρ₁.discriminantExponent + ρ₂.discriminantExponent := by
  let := ρ₁.mulAction
  let := ρ₂.mulAction
  let := (sumCongr e ρ₁ ρ₂).mulAction
  rw [discriminantExponent_def,
    ← orbitDiscriminantExponent_eq_of_equiv K e fun σ x ↦ by rcases x with j | j <;> simp,
    orbitDiscriminantExponent_sum, discriminantExponent_def, discriminantExponent_def]

/-! ### The splitting symbol of a Galois set -/

private def fieldFactor (F : IntermediateField K (SeparableClosure K)) : ℕ × ℕ :=
  (F.inertiaDegree, Module.finrank K F / F.inertiaDegree)

private theorem fieldFactor_eq_of_algEquiv {L M : IntermediateField K (SeparableClosure K)}
    (e : L ≃ₐ[K] M) : fieldFactor L = fieldFactor M := by
  simp only [fieldFactor, IntermediateField.inertiaDegree_eq_of_algEquiv e,
    e.toLinearEquiv.finrank_eq]

private theorem fieldFactor_fixedField_stabilizer_smul {X : Type*}
    [MulAction Gal(SeparableClosure K/K) X] (σ : Gal(SeparableClosure K/K)) (x : X) :
    fieldFactor (IntermediateField.fixedField
      (MulAction.stabilizer Gal(SeparableClosure K/K) (σ • x))) =
    fieldFactor (IntermediateField.fixedField
      (MulAction.stabilizer Gal(SeparableClosure K/K) x)) := by
  rw [MulAction.stabilizer_smul_eq_stabilizer_map_conj, MulEquiv.toMonoidHom_eq_coe,
    Subgroup.fixedField_map_conj]
  exact (fieldFactor_eq_of_algEquiv
    ((IntermediateField.fixedField
      (MulAction.stabilizer Gal(SeparableClosure K/K) x)).equivMap σ.toAlgHom)).symm

private theorem fieldFactor_fixedField_stabilizer_out {X : Type*}
    [MulAction Gal(SeparableClosure K/K) X]
    {ω : MulAction.orbitRel.Quotient Gal(SeparableClosure K/K) X} {x : X}
    (hx : (Quotient.mk'' x : MulAction.orbitRel.Quotient Gal(SeparableClosure K/K) X) = ω) :
    fieldFactor (IntermediateField.fixedField
      (MulAction.stabilizer Gal(SeparableClosure K/K) ω.out)) =
    fieldFactor (IntermediateField.fixedField
      (MulAction.stabilizer Gal(SeparableClosure K/K) x)) := by
  obtain ⟨σ, rfl⟩ := TauCeti.MulAction.exists_smul_out_eq hx
  exact (fieldFactor_fixedField_stabilizer_smul σ ω.out).symm

open Classical in
/-- The **splitting symbol** of a labelled Galois set ([Bhargava 2007, (2.1)]): the multiset, over
its orbits, of the pair `(f, e)` of residue degree and ramification index of the fixed field of the
stabilizer of a point of the orbit. -/
def splittingSymbol (ρ : GaloisSet K n) : Multiset (ℕ × ℕ) :=
  letI := ρ.mulAction
  haveI := Fintype.ofFinite (MulAction.orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n))
  (Finset.univ :
      Finset (MulAction.orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n))).val.map
    fun ω ↦
      let F := IntermediateField.fixedField
        (MulAction.stabilizer Gal(SeparableClosure K/K) (Quotient.out ω : Fin n))
      (F.inertiaDegree, Module.finrank K F / F.inertiaDegree)

open Classical in
/-- The defining formula of `GaloisSet.splittingSymbol`. -/
theorem splittingSymbol_def (ρ : GaloisSet K n) :
    ρ.splittingSymbol =
      (letI := ρ.mulAction
       haveI := Fintype.ofFinite (MulAction.orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n))
       (Finset.univ :
           Finset (MulAction.orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n))).val.map
         fun ω ↦
           let F := IntermediateField.fixedField
             (MulAction.stabilizer Gal(SeparableClosure K/K) (Quotient.out ω : Fin n))
           (F.inertiaDegree, Module.finrank K F / F.inertiaDegree)) :=
  (rfl)

/-- Any `Fintype` instance on the orbit quotient and any choice of one representative per orbit
compute the same splitting symbol. -/
theorem splittingSymbol_eq_map_univ (ρ : GaloisSet K n)
    (hF : letI := ρ.mulAction
      Fintype (MulAction.orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n)))
    (s : (letI := ρ.mulAction
      MulAction.orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n)) → Fin n)
    (hs : ∀ ω, (letI := ρ.mulAction
      (Quotient.mk'' (s ω) :
        MulAction.orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n))) = ω) :
    ρ.splittingSymbol =
      (letI := ρ.mulAction
       (@Finset.univ _ hF).val.map fun ω ↦
         let F := IntermediateField.fixedField
           (MulAction.stabilizer Gal(SeparableClosure K/K) (s ω))
         (F.inertiaDegree, Module.finrank K F / F.inertiaDegree)) := by
  classical
  let := ρ.mulAction
  have hinst : Fintype.ofFinite
      (MulAction.orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n)) = hF :=
    Subsingleton.elim _ _
  rw [splittingSymbol, hinst]
  exact Multiset.map_congr rfl fun ω _ ↦ fieldFactor_fixedField_stabilizer_out (hs ω)

/-- Equivariant bijections preserve the splitting symbol of labelled Galois sets. -/
theorem splittingSymbol_eq_of_equiv {m : ℕ} (ρ : GaloisSet K n) (τ : GaloisSet K m)
    (e : Fin n ≃ Fin m)
    (he : ∀ (σ : Gal(SeparableClosure K/K)) (i : Fin n), e (ρ.val σ i) = τ.val σ (e i)) :
    ρ.splittingSymbol = τ.splittingSymbol := by
  classical
  let := ρ.mulAction
  let := τ.mulAction
  let _ := Fintype.ofFinite (MulAction.orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n))
  let _ := Fintype.ofFinite (MulAction.orbitRel.Quotient Gal(SeparableClosure K/K) (Fin m))
  let E := TauCeti.MulAction.orbitRelQuotientCongr (MulEquiv.refl Gal(SeparableClosure K/K)) e he
  rw [splittingSymbol, splittingSymbol,
    ← congrArg Finset.val (Finset.map_univ_equiv E), Finset.map_val, Equiv.coe_toEmbedding,
    Multiset.map_map]
  refine Multiset.map_congr rfl fun ω _ ↦ ?_
  have hE : (Quotient.mk'' (e ω.out) :
      MulAction.orbitRel.Quotient Gal(SeparableClosure K/K) (Fin m)) = E ω := by
    rw [← TauCeti.MulAction.orbitRelQuotientCongr_mk (MulEquiv.refl _) e he, Quotient.out_eq']
  change fieldFactor _ = fieldFactor _
  rw [fieldFactor_fixedField_stabilizer_out hE,
    TauCeti.MulAction.stabilizer_eq_of_injective e e.injective he]

/-- Relabelling a Galois set does not change its splitting symbol. -/
@[simp]
theorem splittingSymbol_smul (ρ : GaloisSet K n) (e : Equiv.Perm (Fin n)) :
    (e • ρ).splittingSymbol = ρ.splittingSymbol :=
  (ρ.splittingSymbol_eq_of_equiv (e • ρ) e (by simp)).symm

/-- The splitting symbol of a disjoint union `sumCongr e ρ₁ ρ₂` is the sum of the splitting symbols
of `ρ₁` and `ρ₂`. -/
@[simp]
theorem splittingSymbol_sumCongr {m l : ℕ} (e : Fin m ⊕ Fin l ≃ Fin n)
    (ρ₁ : GaloisSet K m) (ρ₂ : GaloisSet K l) :
    (sumCongr e ρ₁ ρ₂).splittingSymbol = ρ₁.splittingSymbol + ρ₂.splittingSymbol := by
  classical
  let := ρ₁.mulAction
  let := ρ₂.mulAction
  let := (sumCongr e ρ₁ ρ₂).mulAction
  let _ := Fintype.ofFinite (MulAction.orbitRel.Quotient Gal(SeparableClosure K/K) (Fin m))
  let _ := Fintype.ofFinite (MulAction.orbitRel.Quotient Gal(SeparableClosure K/K) (Fin l))
  let _ := Fintype.ofFinite (MulAction.orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n))
  have heq : ∀ (σ : Gal(SeparableClosure K/K)) (x : Fin m ⊕ Fin l),
      e (σ • x) = σ • e x := fun σ x ↦ by rcases x with j | j <;> simp
  let E₁ := TauCeti.MulAction.orbitRelQuotientCongr (MulEquiv.refl Gal(SeparableClosure K/K)) e heq
  let E₂ := TauCeti.MulAction.orbitRelQuotientSumEquiv
    (G := Gal(SeparableClosure K/K)) (X := Fin m) (Y := Fin l)
  let E := E₂.symm.trans E₁
  rw [splittingSymbol, ← congrArg Finset.val (Finset.map_univ_equiv E),
    Finset.map_val, Equiv.coe_toEmbedding, Multiset.map_map, ← Finset.univ_disjSum_univ]
  change Multiset.map _ (Finset.univ.val.disjSum Finset.univ.val) = _
  rw [Multiset.map_disjSum, splittingSymbol, splittingSymbol]
  congr 1
  · refine Multiset.map_congr rfl fun ω _ ↦ ?_
    have hE : (Quotient.mk'' (e (Sum.inl ω.out)) :
        MulAction.orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n)) = E (Sum.inl ω) := by
      rw [← MulAction.orbitRelQuotientCongr_mk (MulEquiv.refl _) e heq,
        ← MulAction.orbitRelQuotientSumEquiv_symm_inl_mk, Quotient.out_eq']
      rfl
    change fieldFactor _ = fieldFactor _
    rw [fieldFactor_fixedField_stabilizer_out hE, stabilizer_sumCongr_inl]
  · refine Multiset.map_congr rfl fun ω _ ↦ ?_
    have hE : (Quotient.mk'' (e (Sum.inr ω.out)) :
        MulAction.orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n)) = E (Sum.inr ω) := by
      rw [← MulAction.orbitRelQuotientCongr_mk (MulEquiv.refl _) e heq,
        ← MulAction.orbitRelQuotientSumEquiv_symm_inr_mk, Quotient.out_eq']
      rfl
    change fieldFactor _ = fieldFactor _
    rw [fieldFactor_fixedField_stabilizer_out hE, stabilizer_sumCongr_inr]

/-- The `(f, e)` pair of the fixed field of any point stabilizer belongs to `ρ.splittingSymbol`. -/
theorem mem_splittingSymbol_of_fixedField_stabilizer (ρ : GaloisSet K n) (i : Fin n) :
    (letI := ρ.mulAction
     let F := IntermediateField.fixedField (MulAction.stabilizer Gal(SeparableClosure K/K) i)
     (F.inertiaDegree, Module.finrank K F / F.inertiaDegree)) ∈ ρ.splittingSymbol := by
  classical
  let := ρ.mulAction
  let _ := Fintype.ofFinite (MulAction.orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n))
  rw [splittingSymbol, Multiset.mem_map]
  exact ⟨Quotient.mk'' i, Finset.mem_univ _, fieldFactor_fixedField_stabilizer_out rfl⟩

/-- The number of factors in `ρ.splittingSymbol` is the number of orbits of `ρ`. -/
@[simp]
theorem card_splittingSymbol (ρ : GaloisSet K n) :
    Multiset.card ρ.splittingSymbol =
      (letI := ρ.mulAction
       Nat.card (MulAction.orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n))) := by
  classical
  let := ρ.mulAction
  let _ := Fintype.ofFinite (MulAction.orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n))
  rw [splittingSymbol, Multiset.card_map, Finset.card_val, Finset.card_univ,
    Nat.card_eq_fintype_card]

/-- Every pair `(f, e)` in the splitting symbol of a Galois set has `0 < f` and `0 < e`. -/
theorem pos_of_mem_splittingSymbol (ρ : GaloisSet K n) {x : ℕ × ℕ}
    (hx : x ∈ ρ.splittingSymbol) : 0 < x.1 ∧ 0 < x.2 := by
  classical
  let := ρ.mulAction
  let _ := Fintype.ofFinite (MulAction.orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n))
  rw [splittingSymbol, Multiset.mem_map] at hx
  obtain ⟨ω, -, rfl⟩ := hx
  let F := IntermediateField.fixedField (MulAction.stabilizer Gal(SeparableClosure K/K) ω.out)
  have : FiniteDimensional K F := ρ.finiteDimensional_fixedField_stabilizer ω.out
  have hf : 0 < F.inertiaDegree := F.inertiaDegree_pos
  have hmul : F.inertiaDegree * (Module.finrank K F / F.inertiaDegree) = Module.finrank K F :=
    Nat.mul_div_cancel' F.inertiaDegree_dvd_finrank
  have hdeg : 0 < Module.finrank K F := Module.finrank_pos
  exact ⟨hf, Nat.pos_of_mul_pos_left (hmul.symm ▸ hdeg)⟩

/-- The degree sum `∑ f e` over the pairs `(f, e)` in `ρ.splittingSymbol` equals `n`. -/
@[simp]
theorem sum_map_mul_splittingSymbol (ρ : GaloisSet K n) :
    (ρ.splittingSymbol.map fun x ↦ x.1 * x.2).sum = n := by
  classical
  let := ρ.mulAction
  let _ := Fintype.ofFinite (MulAction.orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n))
  let (ω : MulAction.orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n)) :=
    Fintype.ofFinite (MulAction.orbit Gal(SeparableClosure K/K) ω.out)
  rw [splittingSymbol, Multiset.map_map]
  change (Finset.univ.sum fun ω : MulAction.orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n) ↦
    (let F := IntermediateField.fixedField
      (MulAction.stabilizer Gal(SeparableClosure K/K) ω.out)
     F.inertiaDegree * (Module.finrank K F / F.inertiaDegree))) = n
  have hterm : ∀ ω : MulAction.orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n),
      (let F := IntermediateField.fixedField
        (MulAction.stabilizer Gal(SeparableClosure K/K) ω.out)
       F.inertiaDegree * (Module.finrank K F / F.inertiaDegree)) =
      Fintype.card (MulAction.orbit Gal(SeparableClosure K/K) ω.out) := fun ω ↦ by
    rw [Nat.mul_div_cancel' (IntermediateField.inertiaDegree_dvd_finrank _),
      ρ.finrank_fixedField_stabilizer, Nat.card_eq_fintype_card]
  simp_rw [hterm, ← Fintype.card_sigma]
  exact (Fintype.card_congr
    (MulAction.selfEquivSigmaOrbits Gal(SeparableClosure K/K) (Fin n))).symm.trans
    (Fintype.card_fin n)

/-- On an empty label set, the splitting symbol is empty. -/
@[simp]
theorem splittingSymbol_of_isEmpty [IsEmpty (Fin n)] (ρ : GaloisSet K n) :
    ρ.splittingSymbol = 0 := by
  classical
  let := ρ.mulAction
  have : IsEmpty (MulAction.orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n)) :=
    ⟨Quotient.ind' isEmptyElim⟩
  let _ := Fintype.ofFinite (MulAction.orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n))
  rw [splittingSymbol, Finset.univ_eq_empty]
  simp

/-- The trivial Galois set of size `n` has splitting symbol `(1, 1)` repeated `n` times. -/
@[simp]
theorem splittingSymbol_trivial :
    (trivial K n).splittingSymbol = Multiset.replicate n (1, 1) := by
  classical
  let := (trivial K n).mulAction
  let E : Fin n ≃ MulAction.orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n) :=
    { toFun := Quotient.mk''
      invFun := Quotient.lift id fun i j ⟨σ, hσ⟩ ↦ hσ.symm.trans (trivial_val_apply σ j)
      left_inv _ := rfl
      right_inv q := Quotient.inductionOn' q fun _ ↦ rfl }
  let instF : Fintype (MulAction.orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n)) :=
    Fintype.ofEquiv (Fin n) E
  rw [(trivial K n).splittingSymbol_eq_map_univ instF E.symm (fun ω ↦ E.apply_symm_apply ω),
    ← congrArg Finset.val (Finset.map_univ_equiv E), Finset.map_val, Equiv.coe_toEmbedding,
    Multiset.map_map]
  have hconst :
      (fun x : Fin n ↦
        let F := IntermediateField.fixedField
          (MulAction.stabilizer Gal(SeparableClosure K/K) (E.symm (E x)))
        (F.inertiaDegree, Module.finrank K F / F.inertiaDegree)) =
      fun _ : Fin n ↦ (1, 1) := by
    funext x
    simp [E.symm_apply_apply]
  rw [Function.comp_def, hconst]
  simp

/-- A transitive Galois set on a nonempty label set has singleton splitting symbol given by the
fixed field of any point stabilizer. -/
theorem splittingSymbol_of_isTransitive (ρ : GaloisSet K n) (hρ : ρ.IsTransitive) (i : Fin n) :
    ρ.splittingSymbol =
      (letI := ρ.mulAction
       let F := IntermediateField.fixedField (MulAction.stabilizer Gal(SeparableClosure K/K) i)
       {(F.inertiaDegree, Module.finrank K F / F.inertiaDegree)}) := by
  classical
  let := ρ.mulAction
  have : Nonempty (Fin n) := ⟨i⟩
  have : MulAction.IsPretransitive Gal(SeparableClosure K/K) (Fin n) := ρ.isTransitive_def.1 hρ
  let _ : Unique (MulAction.orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n)) :=
    ((MulAction.pretransitive_iff_unique_quotient_of_nonempty
      Gal(SeparableClosure K/K) (Fin n)).mp inferInstance).some
  rw [ρ.splittingSymbol_eq_map_univ inferInstance (fun _ ↦ i) (fun _ ↦ Subsingleton.elim _ _)]
  simp [Finset.univ_unique]

/-- A Galois set whose splitting symbol has at most one factor is transitive. -/
theorem isTransitive_of_card_splittingSymbol_le_one {ρ : GaloisSet K n}
    (h : Multiset.card ρ.splittingSymbol ≤ 1) : ρ.IsTransitive := by
  let := ρ.mulAction
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [isTransitive_iff]
    exact fun i ↦ Fin.elim0 i
  · have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    have : Nonempty (MulAction.orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n)) :=
      ⟨Quotient.mk'' ⟨0, hn⟩⟩
    rw [card_splittingSymbol] at h
    have hcard : Nat.card (MulAction.orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n)) = 1 :=
      le_antisymm h Nat.card_pos
    obtain ⟨u⟩ := Nat.card_eq_one_iff_unique.mp hcard
    have : Unique (MulAction.orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n)) :=
      { default := Quotient.mk'' ⟨0, hn⟩, uniq := fun _ ↦ u.elim _ _ }
    exact ρ.isTransitive_def.2
      ((MulAction.pretransitive_iff_unique_quotient_of_nonempty
        Gal(SeparableClosure K/K) (Fin n)).mpr ⟨this⟩)

/-- A Galois set with a singleton splitting symbol is transitive on a nonempty label set. -/
theorem isTransitive_of_splittingSymbol_eq_singleton {ρ : GaloisSet K n} {x : ℕ × ℕ}
    (h : ρ.splittingSymbol = {x}) : ρ.IsTransitive :=
  isTransitive_of_card_splittingSymbol_le_one (by simp [h])

/-- On a nonempty Galois set, the splitting symbol equals `{(f, e)}` (with `f ≠ 0`) if and only if
the action is transitive, the stabilizer fixed field at `i` has residue degree `f`, and
`n = f * e`. -/
theorem splittingSymbol_eq_singleton_iff (ρ : GaloisSet K n) (i : Fin n)
    {f e : ℕ} (hf : f ≠ 0) :
    ρ.splittingSymbol = {(f, e)} ↔
      ρ.IsTransitive ∧
        (letI := ρ.mulAction
         (IntermediateField.fixedField
           (MulAction.stabilizer Gal(SeparableClosure K/K) i)).inertiaDegree = f) ∧
        n = f * e := by
  let := ρ.mulAction
  constructor
  · intro h
    have htr : ρ.IsTransitive := isTransitive_of_splittingSymbol_eq_singleton h
    have hdeg : n = f * e := by
      have hsum := ρ.sum_map_mul_splittingSymbol
      rw [h, Multiset.map_singleton, Multiset.sum_singleton] at hsum
      exact hsum.symm
    rw [ρ.splittingSymbol_of_isTransitive htr i, Multiset.singleton_inj, Prod.mk.injEq] at h
    exact ⟨htr, h.1, hdeg⟩
  · rintro ⟨htr, hf', rfl⟩
    rw [ρ.splittingSymbol_of_isTransitive htr i, Multiset.singleton_inj, Prod.mk.injEq]
    refine ⟨hf', ?_⟩
    rw [ρ.finrank_fixedField_stabilizer_of_isTransitive htr i, hf',
      Nat.mul_div_cancel_left e (Nat.pos_of_ne_zero hf)]

end GaloisSet

/-! ### The transitive mass by residue degree -/

/-- **The transitive mass by residue degree** ([Bhargava 2007, §2]): for `f, e > 0`, the labelled
Galois sets of size `f * e` with splitting symbol `{(f, e)}` satisfy
`((f * e)!)⁻¹ ∑_ρ q ^ (-d(ρ)) = 1 / (f · q ^ (f (e - 1)))`, where `q` is the residue cardinality of
`K`. -/
theorem etaleMass_isTransitive_splittingSymbol (f e : ℕ) (hf : 0 < f) (he : 0 < e) :
    ((f * e)! : ℝ≥0∞)⁻¹ *
        ∑' ρ : {ρ : GaloisSet K (f * e) // ρ.splittingSymbol = {(f, e)}},
          1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ ρ.1.discriminantExponent =
      1 / ((f : ℝ≥0∞) * (Nat.card 𝓀[K] : ℝ≥0∞) ^ (f * (e - 1))) := by
  classical
  have hn : 0 < f * e := Nat.mul_pos hf he
  let i₀ : Fin (f * e) := ⟨0, hn⟩
  set q : ℝ≥0∞ := (Nat.card 𝓀[K] : ℝ≥0∞)
  let g : IntermediateField K (SeparableClosure K) → ℝ≥0∞ :=
    fun L ↦ if L.inertiaDegree = f then 1 / q ^ L.discriminantExponent else 0
  -- Step 1: Identify `{ρ // ρ.splittingSymbol = {(f, e)}}` inside `{ρ // ρ.IsTransitive}`.
  let S₁ : Set {ρ : GaloisSet K (f * e) // ρ.IsTransitive} :=
    {ρ | letI := ρ.1.mulAction
      (IntermediateField.fixedField
        (MulAction.stabilizer Gal(SeparableClosure K/K) i₀)).inertiaDegree = f}
  let ε₁ : {ρ : GaloisSet K (f * e) // ρ.splittingSymbol = {(f, e)}} ≃ S₁ :=
    { toFun := fun ρ ↦
        let h := (ρ.1.splittingSymbol_eq_singleton_iff i₀ hf.ne').1 ρ.2
        ⟨⟨ρ.1, h.1⟩, h.2.1⟩
      invFun := fun ρ ↦
        ⟨ρ.1.1, (ρ.1.1.splittingSymbol_eq_singleton_iff i₀ hf.ne').2 ⟨ρ.1.2, ρ.2, rfl⟩⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  have hsum₁ :
      (∑' ρ : {ρ : GaloisSet K (f * e) // ρ.splittingSymbol = {(f, e)}},
        1 / q ^ ρ.1.discriminantExponent) =
      ∑' ρ : {ρ : GaloisSet K (f * e) // ρ.IsTransitive},
        (letI := ρ.1.mulAction
         g (IntermediateField.fixedField
           (MulAction.stabilizer Gal(SeparableClosure K/K) i₀))) := by
    rw [← ε₁.symm.tsum_eq]
    have hcongr : ∀ x : S₁,
        1 / q ^ (ε₁.symm x).1.discriminantExponent =
          (letI := x.1.1.mulAction
           1 / q ^ (IntermediateField.fixedField
             (MulAction.stabilizer Gal(SeparableClosure K/K) i₀)).discriminantExponent) :=
      fun x ↦ by
        change 1 / q ^ x.1.1.discriminantExponent = _
        rw [x.1.1.discriminantExponent_of_isTransitive x.1.2 i₀]
    rw [tsum_congr hcongr,
      tsum_subtype S₁ (fun ρ ↦
        letI := ρ.1.mulAction
        1 / q ^ (IntermediateField.fixedField
          (MulAction.stabilizer Gal(SeparableClosure K/K) i₀)).discriminantExponent)]
    exact tsum_congr fun ρ ↦ Set.indicator_apply S₁ _ ρ
  -- Step 2: Apply the transitive Galois-set bridge and the subfield count by residue degree.
  let S₂ : Set {L : IntermediateField K (SeparableClosure K) // Module.finrank K L = f * e} :=
    {L | L.1.inertiaDegree = f}
  let ε₂ : {L : IntermediateField K (SeparableClosure K) //
      Module.finrank K L = f * e ∧ L.inertiaDegree = f} ≃ S₂ :=
    { toFun := fun L ↦ ⟨⟨L.1, L.2.1⟩, L.2.2⟩
      invFun := fun L ↦ ⟨L.1.1, L.1.2, L.2⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  have hsum₂ :
      (∑' L : {L : IntermediateField K (SeparableClosure K) // Module.finrank K L = f * e},
        g L.1) =
      (e : ℝ≥0∞) / q ^ (f * (e - 1)) := by
    rw [← tsum_inertiaDegree_eq (K := K) hf.ne' e, ← ε₂.symm.tsum_eq]
    have hsub := tsum_subtype S₂ (fun L ↦ 1 / q ^ L.1.discriminantExponent)
    exact (tsum_congr fun L ↦ (Set.indicator_apply S₂ _ L).symm).trans hsub.symm
  rw [hsum₁, GaloisSet.tsum_isTransitive i₀ g, hsum₂]
  -- Step 3: Cancel `(f * e - 1)! * e` against `((f * e)!)⁻¹`.
  have hfact : (f * e)! = f * (e * (f * e - 1)!) := by
    rw [← mul_assoc, ← Nat.mul_factorial_pred hn.ne']
  have hf0 : (f : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.2 hf.ne'
  have hft : (f : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  have hc0 : (e : ℝ≥0∞) * ((f * e - 1)! : ℝ≥0∞) ≠ 0 :=
    mul_ne_zero (Nat.cast_ne_zero.2 he.ne') (Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _))
  have hc_top : (e : ℝ≥0∞) * ((f * e - 1)! : ℝ≥0∞) ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (ENNReal.natCast_ne_top _)
  rw [hfact, Nat.cast_mul, Nat.cast_mul, div_eq_mul_inv, one_div,
    ENNReal.mul_inv (.inl hf0) (.inl hft), ENNReal.mul_inv (.inl hf0) (.inl hft)]
  calc
    ((f : ℝ≥0∞)⁻¹ * ((e : ℝ≥0∞) * ((f * e - 1)! : ℝ≥0∞))⁻¹) *
        (((f * e - 1)! : ℝ≥0∞) * ((e : ℝ≥0∞) * (q ^ (f * (e - 1)))⁻¹))
      = (f : ℝ≥0∞)⁻¹ *
          (((e : ℝ≥0∞) * ((f * e - 1)! : ℝ≥0∞))⁻¹ * ((e : ℝ≥0∞) * ((f * e - 1)! : ℝ≥0∞))) *
          (q ^ (f * (e - 1)))⁻¹ := by ring
    _ = (f : ℝ≥0∞)⁻¹ * (q ^ (f * (e - 1)))⁻¹ := by
      rw [ENNReal.inv_mul_cancel hc0 hc_top, mul_one]

end TauCeti
