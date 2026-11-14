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
# Splitting symbols of Galois sets and the transitive mass

For a labelled Galois set `ρ : GaloisSet K n` over a nonarchimedean local field `K`, its
*splitting symbol* `ρ.splittingSymbol` is the multiset, over the orbits of `ρ`, of the pair
`(f, e)` of residue degree and ramification index of the fixed field `F` of a point stabilizer,
with `f = F.inertiaDegree` and `e = [F : K] / f` [Bhargava 2007, (2.1)]. Conjugate stabilizers have
`K`-isomorphic fixed fields, so the pair does not depend on the chosen point of the orbit.

Every entry `(f, e)` of `ρ.splittingSymbol` has positive components, and the products `f * e` sum
to `n` (`GaloisSet.sum_map_mul_splittingSymbol`). Equivariant bijections preserve the splitting
symbol, and gluing along a sum bijection adds the splitting symbols and the discriminant exponents
(`GaloisSet.splittingSymbol_ofSum`, `GaloisSet.discriminantExponent_ofSum`).

For `f, e ≥ 1`, a Galois set of size `f * e` has splitting symbol `{(f, e)}` precisely when it is
transitive and the fixed field of a point stabilizer has residue degree `f`
(`GaloisSet.splittingSymbol_eq_singleton_iff`). Combining the transitive bridge
`GaloisSet.tsum_isTransitive` with the subfield count `TauCeti.tsum_inertiaDegree_eq` gives the
mass of the Galois sets with a single-factor splitting symbol `{(f, e)}`:
`((f * e)!)⁻¹ ∑_{ρ : symbol = {(f, e)}} q ^ (-d(ρ)) = 1 / (f · q ^ (f (e - 1)))`
(`TauCeti.etaleMass_isTransitive_splittingSymbol`).

## References

* M. Bhargava, *Mass formulae for extensions of local fields, and conjectures on the density of
  number field discriminants*, IMRN **2007**, rnm052, §2.
* K. S. Kedlaya, *Mass formulas for local Galois representations*, IMRN **2007**, rnm021.
-/

public section

noncomputable section

open ValuativeRel IntermediateField
open scoped ENNReal Nat

namespace TauCeti

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

namespace GaloisSet

variable {n : ℕ}

/-- The pair `(f(F / K), [F : K] / f(F / K))` of residue degree and ramification index of a
subextension `F` of `SeparableClosure K`. -/
private def fieldSymbol (F : IntermediateField K (SeparableClosure K)) : ℕ × ℕ :=
  (F.inertiaDegree, Module.finrank K F / F.inertiaDegree)

private theorem fieldSymbol_eq_of_algEquiv {L M : IntermediateField K (SeparableClosure K)}
    (e : L ≃ₐ[K] M) : fieldSymbol L = fieldSymbol M := by
  simp only [fieldSymbol, IntermediateField.inertiaDegree_eq_of_algEquiv e,
    e.toLinearEquiv.finrank_eq]

private theorem fieldSymbol_fixedField_stabilizer_smul {X : Type*}
    [MulAction Gal(SeparableClosure K/K) X] (σ : Gal(SeparableClosure K/K)) (x : X) :
    fieldSymbol (IntermediateField.fixedField
        (MulAction.stabilizer Gal(SeparableClosure K/K) (σ • x))) =
      fieldSymbol (IntermediateField.fixedField
        (MulAction.stabilizer Gal(SeparableClosure K/K) x)) := by
  rw [MulAction.stabilizer_smul_eq_stabilizer_map_conj, MulEquiv.toMonoidHom_eq_coe,
    Subgroup.fixedField_map_conj]
  exact (fieldSymbol_eq_of_algEquiv
    ((IntermediateField.fixedField (MulAction.stabilizer Gal(SeparableClosure K/K) x)).equivMap
      σ.toAlgHom)).symm

private theorem fieldSymbol_fixedField_stabilizer_out {X : Type*}
    [MulAction Gal(SeparableClosure K/K) X]
    {ω : MulAction.orbitRel.Quotient Gal(SeparableClosure K/K) X} {x : X}
    (hx : (Quotient.mk'' x : MulAction.orbitRel.Quotient Gal(SeparableClosure K/K) X) = ω) :
    fieldSymbol (IntermediateField.fixedField
        (MulAction.stabilizer Gal(SeparableClosure K/K) ω.out)) =
      fieldSymbol (IntermediateField.fixedField
        (MulAction.stabilizer Gal(SeparableClosure K/K) x)) := by
  obtain ⟨σ, rfl⟩ := MulAction.exists_smul_out_eq hx
  exact (fieldSymbol_fixedField_stabilizer_smul σ ω.out).symm

open scoped Classical in
/-- The **splitting symbol** of a labelled Galois set ([Bhargava 2007, (2.1)]): the multiset, over
its orbits, of the pair `(f, e)` of residue degree and ramification index of the fixed field of a
point stabilizer. -/
def splittingSymbol (ρ : GaloisSet K n) : Multiset (ℕ × ℕ) :=
  letI := ρ.mulAction
  haveI := Fintype.ofFinite (MulAction.orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n))
  (Finset.univ : Finset (MulAction.orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n))).val.map
    fun ω ↦
      let F := IntermediateField.fixedField
        (MulAction.stabilizer Gal(SeparableClosure K/K) (Quotient.out ω : Fin n))
      (F.inertiaDegree, Module.finrank K F / F.inertiaDegree)

open scoped Classical in
/-- The defining formula of `GaloisSet.splittingSymbol`. -/
theorem splittingSymbol_def (ρ : GaloisSet K n) :
    ρ.splittingSymbol =
      (letI := ρ.mulAction
      haveI := Fintype.ofFinite (MulAction.orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n))
      (Finset.univ : Finset (MulAction.orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n))).val.map
        fun ω ↦
          let F := IntermediateField.fixedField
            (MulAction.stabilizer Gal(SeparableClosure K/K) (Quotient.out ω : Fin n))
          (F.inertiaDegree, Module.finrank K F / F.inertiaDegree)) :=
  (rfl)

private theorem splittingSymbol_eq_sum (ρ : GaloisSet K n)
    [inst : Fintype (letI := ρ.mulAction;
      MulAction.orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n))] :
    ρ.splittingSymbol =
      ∑ ω : (letI := ρ.mulAction; MulAction.orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n)),
        ({letI := ρ.mulAction
          fieldSymbol (IntermediateField.fixedField
            (MulAction.stabilizer Gal(SeparableClosure K/K) ω.out))} : Multiset (ℕ × ℕ)) := by
  classical
  let := ρ.mulAction
  have huniv : @Finset.univ (MulAction.orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n))
      (Fintype.ofFinite _) = @Finset.univ _ inst :=
    congrArg (@Finset.univ _) (Subsingleton.elim _ _)
  rw [splittingSymbol_def]
  dsimp only
  rw [huniv, ← Multiset.sum_map_singleton (Finset.univ.val.map _), Multiset.map_map]
  rfl

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
  let E := MulAction.orbitRelQuotientCongr (MulEquiv.refl Gal(SeparableClosure K/K)) e he
  rw [ρ.splittingSymbol_eq_sum, τ.splittingSymbol_eq_sum, ← E.sum_comp]
  refine Finset.sum_congr rfl fun ω _ ↦ congrArg ({·} : ℕ × ℕ → Multiset (ℕ × ℕ)) ?_
  have hE : (Quotient.mk'' (e ω.out) :
      MulAction.orbitRel.Quotient Gal(SeparableClosure K/K) (Fin m)) = E ω := by
    rw [← MulAction.orbitRelQuotientCongr_mk (MulEquiv.refl _) e he, Quotient.out_eq']
  rw [fieldSymbol_fixedField_stabilizer_out hE,
    MulAction.stabilizer_eq_of_injective e e.injective he]

/-- Relabelling a Galois set preserves its splitting symbol. -/
@[simp]
theorem splittingSymbol_smul (ρ : GaloisSet K n) (e : Equiv.Perm (Fin n)) :
    (e • ρ).splittingSymbol = ρ.splittingSymbol :=
  (ρ.splittingSymbol_eq_of_equiv (e • ρ) e (by simp)).symm

/-- Gluing two Galois sets along a sum bijection adds their discriminant exponents. -/
@[simp]
theorem discriminantExponent_ofSum {a b : ℕ} (e : Fin a ⊕ Fin b ≃ Fin n)
    (ρ₁ : GaloisSet K a) (ρ₂ : GaloisSet K b) :
    (ofSum e ρ₁ ρ₂).discriminantExponent = ρ₁.discriminantExponent + ρ₂.discriminantExponent := by
  let := ρ₁.mulAction
  let := ρ₂.mulAction
  let := (ofSum e ρ₁ ρ₂).mulAction
  rw [discriminantExponent_def, discriminantExponent_def, discriminantExponent_def,
    ← orbitDiscriminantExponent_sum,
    orbitDiscriminantExponent_eq_of_equiv K e]
  rintro σ (i | j)
  · exact (ofSum_val_apply_inl e ρ₁ ρ₂ σ i).symm
  · exact (ofSum_val_apply_inr e ρ₁ ρ₂ σ j).symm

/-- Gluing two Galois sets along a sum bijection adds their splitting symbols. -/
@[simp]
theorem splittingSymbol_ofSum {a b : ℕ} (e : Fin a ⊕ Fin b ≃ Fin n)
    (ρ₁ : GaloisSet K a) (ρ₂ : GaloisSet K b) :
    (ofSum e ρ₁ ρ₂).splittingSymbol = ρ₁.splittingSymbol + ρ₂.splittingSymbol := by
  classical
  let := ρ₁.mulAction
  let := ρ₂.mulAction
  let := (ofSum e ρ₁ ρ₂).mulAction
  let _ := Fintype.ofFinite (MulAction.orbitRel.Quotient Gal(SeparableClosure K/K) (Fin a))
  let _ := Fintype.ofFinite (MulAction.orbitRel.Quotient Gal(SeparableClosure K/K) (Fin b))
  let _ := Fintype.ofFinite (MulAction.orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n))
  have he : ∀ (σ : Gal(SeparableClosure K/K)) (x : Fin a ⊕ Fin b),
      e (σ • x) = (ofSum e ρ₁ ρ₂).val σ (e x) := by
    rintro σ (i | j)
    · exact (ofSum_val_apply_inl e ρ₁ ρ₂ σ i).symm
    · exact (ofSum_val_apply_inr e ρ₁ ρ₂ σ j).symm
  let E : MulAction.orbitRel.Quotient Gal(SeparableClosure K/K) (Fin a) ⊕
        MulAction.orbitRel.Quotient Gal(SeparableClosure K/K) (Fin b) ≃
      MulAction.orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n) :=
    MulAction.orbitRelQuotientSumEquiv.symm.trans
      (MulAction.orbitRelQuotientCongr (MulEquiv.refl Gal(SeparableClosure K/K)) e he)
  rw [(ofSum e ρ₁ ρ₂).splittingSymbol_eq_sum, ρ₁.splittingSymbol_eq_sum, ρ₂.splittingSymbol_eq_sum,
    ← E.sum_comp, Fintype.sum_sum_type]
  congr 1
  · refine Finset.sum_congr rfl fun ω _ ↦ congrArg ({·} : ℕ × ℕ → Multiset (ℕ × ℕ)) ?_
    have hE : (Quotient.mk'' (e (.inl ω.out)) :
        MulAction.orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n)) = E (.inl ω) := by
      dsimp only [E, Equiv.trans_apply]
      conv_rhs => rw [← Quotient.out_eq' ω]
      rw [MulAction.orbitRelQuotientSumEquiv_symm_inl_mk,
        MulAction.orbitRelQuotientCongr_mk (MulEquiv.refl _) e he]
    rw [fieldSymbol_fixedField_stabilizer_out hE,
      MulAction.stabilizer_eq_of_injective (fun i ↦ e (.inl i))
        (e.injective.comp Sum.inl_injective)
        (fun σ i ↦ (ofSum_val_apply_inl e ρ₁ ρ₂ σ i).symm) ω.out]
  · refine Finset.sum_congr rfl fun ω _ ↦ congrArg ({·} : ℕ × ℕ → Multiset (ℕ × ℕ)) ?_
    have hE : (Quotient.mk'' (e (.inr ω.out)) :
        MulAction.orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n)) = E (.inr ω) := by
      dsimp only [E, Equiv.trans_apply]
      conv_rhs => rw [← Quotient.out_eq' ω]
      rw [MulAction.orbitRelQuotientSumEquiv_symm_inr_mk,
        MulAction.orbitRelQuotientCongr_mk (MulEquiv.refl _) e he]
    rw [fieldSymbol_fixedField_stabilizer_out hE,
      MulAction.stabilizer_eq_of_injective (fun j ↦ e (.inr j))
        (e.injective.comp Sum.inr_injective)
        (fun σ j ↦ (ofSum_val_apply_inr e ρ₁ ρ₂ σ j).symm) ω.out]

/-- The number of factors in `ρ.splittingSymbol` is the number of orbits of `ρ`. -/
@[simp]
theorem card_splittingSymbol (ρ : GaloisSet K n) :
    Multiset.card ρ.splittingSymbol =
      Nat.card (letI := ρ.mulAction;
        MulAction.orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n)) := by
  classical
  let := ρ.mulAction
  let _ := Fintype.ofFinite (MulAction.orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n))
  rw [ρ.splittingSymbol_eq_sum, Nat.card_eq_fintype_card]
  simp

/-- A Galois set on an empty label type has the empty splitting symbol. -/
@[simp]
theorem splittingSymbol_of_isEmpty [IsEmpty (Fin n)] (ρ : GaloisSet K n) :
    ρ.splittingSymbol = 0 := by
  rw [← Multiset.card_eq_zero, ρ.card_splittingSymbol]
  let := ρ.mulAction
  exact Nat.card_of_isEmpty

/-- The splitting symbol of `ρ : GaloisSet K n` is empty precisely when `n = 0`. -/
@[simp]
theorem splittingSymbol_eq_zero_iff (ρ : GaloisSet K n) :
    ρ.splittingSymbol = 0 ↔ n = 0 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact ⟨fun _ ↦ rfl, fun _ ↦ ρ.splittingSymbol_of_isEmpty⟩
  · refine iff_of_false ?_ hn.ne'
    rw [← Multiset.card_eq_zero, ρ.card_splittingSymbol]
    let := ρ.mulAction
    have : Nonempty (MulAction.orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n)) :=
      ⟨Quotient.mk'' ⟨0, hn⟩⟩
    exact Nat.card_pos.ne'

/-- The trivial Galois set of size `n` has splitting symbol `n • {(1, 1)}`. -/
@[simp]
theorem splittingSymbol_trivial :
    (trivial K n).splittingSymbol = Multiset.replicate n (1, 1) := by
  classical
  let := (trivial K n).mulAction
  let _ := Fintype.ofFinite (MulAction.orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n))
  have heq : Function.Bijective
      (Quotient.mk'' : Fin n → MulAction.orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n)) :=
    ⟨fun i j h ↦ by
      obtain ⟨σ, hσ⟩ := Quotient.exact' h
      simpa using hσ.symm,
      Quotient.mk''_surjective⟩
  rw [(trivial K n).splittingSymbol_eq_sum, ← heq.sum_comp]
  simp_rw [fixedField_stabilizer_trivial]
  simp [fieldSymbol, IntermediateField.finrank_bot, Multiset.nsmul_singleton]

/-- A transitive Galois set has a single-factor splitting symbol computed at any point. -/
theorem splittingSymbol_of_isTransitive (ρ : GaloisSet K n) (hρ : ρ.IsTransitive) (i : Fin n) :
    ρ.splittingSymbol =
      {letI := ρ.mulAction
        let F := IntermediateField.fixedField (MulAction.stabilizer Gal(SeparableClosure K/K) i)
        (F.inertiaDegree, Module.finrank K F / F.inertiaDegree)} := by
  classical
  let := ρ.mulAction
  have : MulAction.IsPretransitive Gal(SeparableClosure K/K) (Fin n) := ρ.isTransitive_def.1 hρ
  have : Nonempty (Fin n) := ⟨i⟩
  let _ := ((MulAction.pretransitive_iff_unique_quotient_of_nonempty
    Gal(SeparableClosure K/K) (Fin n)).mp inferInstance).some
  rw [ρ.splittingSymbol_eq_sum, Fintype.sum_unique]
  exact congrArg ({·} : ℕ × ℕ → Multiset (ℕ × ℕ))
    (fieldSymbol_fixedField_stabilizer_out (Subsingleton.elim _ _))

/-- Every factor `(f, e)` in the splitting symbol of a Galois set has `0 < f` and `0 < e`. -/
theorem pos_of_mem_splittingSymbol {ρ : GaloisSet K n} {x : ℕ × ℕ} (hx : x ∈ ρ.splittingSymbol) :
    0 < x.1 ∧ 0 < x.2 := by
  classical
  let := ρ.mulAction
  rw [splittingSymbol_def] at hx
  obtain ⟨ω, -, rfl⟩ := Multiset.mem_map.1 hx
  set F := IntermediateField.fixedField (MulAction.stabilizer Gal(SeparableClosure K/K) ω.out)
  have : FiniteDimensional K F := ρ.finiteDimensional_fixedField_stabilizer ω.out
  have hf : 0 < F.inertiaDegree := F.inertiaDegree_pos
  exact ⟨hf, Nat.div_pos (Nat.le_of_dvd Module.finrank_pos F.inertiaDegree_dvd_finrank) hf⟩

/-- The products `f * e` over the factors `(f, e)` of `ρ.splittingSymbol` add up to `n`. -/
@[simp]
theorem sum_map_mul_splittingSymbol (ρ : GaloisSet K n) :
    (ρ.splittingSymbol.map fun x ↦ x.1 * x.2).sum = n := by
  classical
  let := ρ.mulAction
  let _ := Fintype.ofFinite (MulAction.orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n))
  rw [splittingSymbol_def]
  dsimp only
  rw [Multiset.map_map]
  have horb : ∀ ω : MulAction.orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n),
      (let F := IntermediateField.fixedField
          (MulAction.stabilizer Gal(SeparableClosure K/K) ω.out);
        F.inertiaDegree * (Module.finrank K F / F.inertiaDegree)) =
        ((Finset.univ : Finset (Fin n)).filter fun i ↦ Quotient.mk'' i = ω).card := by
    intro ω
    dsimp only
    rw [Nat.mul_div_cancel' (IntermediateField.inertiaDegree_dvd_finrank _),
      ρ.finrank_fixedField_stabilizer, Nat.card_coe_set_eq, Set.ncard_eq_toFinset_card']
    refine congrArg Finset.card (Finset.ext fun i ↦ ?_)
    simp only [Set.mem_toFinset, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun ⟨σ, hσ⟩ ↦ hσ ▸ MulAction.orbitRel.Quotient.quotient_smul_eq.trans ω.out_eq',
      MulAction.exists_smul_out_eq⟩
  calc
    (Finset.univ.val.map
        ((fun x : ℕ × ℕ ↦ x.1 * x.2) ∘ fun ω ↦
          let F := IntermediateField.fixedField
            (MulAction.stabilizer Gal(SeparableClosure K/K) ω.out)
          (F.inertiaDegree, Module.finrank K F / F.inertiaDegree))).sum =
      ∑ ω : MulAction.orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n),
        ((Finset.univ : Finset (Fin n)).filter fun i ↦ Quotient.mk'' i = ω).card :=
      congrArg Multiset.sum (Multiset.map_congr rfl fun ω _ ↦ by
        dsimp only [Function.comp_apply]
        exact horb ω)
    _ = n := by
      rw [← Finset.card_eq_sum_card_fiberwise
        (f := (Quotient.mk'' :
          Fin n → MulAction.orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n)))
        fun _ _ ↦ Finset.mem_univ _, Finset.card_fin]

/-- A nonempty Galois set is transitive precisely when its splitting symbol has a single factor. -/
theorem isTransitive_iff_card_splittingSymbol_eq_one (ρ : GaloisSet K n) (hn : 0 < n) :
    ρ.IsTransitive ↔ Multiset.card ρ.splittingSymbol = 1 := by
  let := ρ.mulAction
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  rw [ρ.card_splittingSymbol, isTransitive_def]
  refine ⟨fun _ ↦ MulAction.card_orbitRelQuotient_eq_one, fun h ↦ ?_⟩
  have : Subsingleton (MulAction.orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n)) :=
    Nat.card_eq_one_iff_unique.1 h |>.1
  exact (MulAction.pretransitive_iff_subsingleton_quotient _ _).2 inferInstance

/-- For `f ≥ 1` and a label `i : Fin (f * e)`, a Galois set of size `f * e` has splitting symbol
`{(f, e)}` precisely when it is transitive and the fixed field of the stabilizer of `i` has residue
degree `f`. -/
theorem splittingSymbol_eq_singleton_iff {f e : ℕ} (hf : 0 < f) (i : Fin (f * e))
    (ρ : GaloisSet K (f * e)) :
    ρ.splittingSymbol = {(f, e)} ↔
      ρ.IsTransitive ∧
        (letI := ρ.mulAction
        (IntermediateField.fixedField
          (MulAction.stabilizer Gal(SeparableClosure K/K) i)).inertiaDegree = f) := by
  constructor
  · intro h
    have htr : ρ.IsTransitive :=
      (ρ.isTransitive_iff_card_splittingSymbol_eq_one i.pos).2 (by simp [h])
    rw [ρ.splittingSymbol_of_isTransitive htr i, Multiset.singleton_inj, Prod.mk.injEq] at h
    exact ⟨htr, h.1⟩
  · rintro ⟨htr, hi⟩
    rw [ρ.splittingSymbol_of_isTransitive htr i, Multiset.singleton_inj]
    dsimp only
    rw [ρ.finrank_fixedField_stabilizer_of_isTransitive htr i, hi, Nat.mul_div_cancel_left _ hf]

end GaloisSet

/-- Summed over the labelled Galois sets of size `f * e` with splitting symbol `{(f, e)}`, the
weights `q ^ (-d(ρ))` equal `(f * e - 1)! · e · q ^ (-f(e - 1))`. -/
private theorem tsum_splittingSymbol_singleton_eq (f e : ℕ) (hf : 0 < f) (he : 0 < e) :
    ∑' ρ : {ρ : GaloisSet K (f * e) // ρ.splittingSymbol = {(f, e)}},
        1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ ρ.1.discriminantExponent =
      ((f * e - 1)! : ℝ≥0∞) * (e / (Nat.card 𝓀[K] : ℝ≥0∞) ^ (f * (e - 1))) := by
  classical
  let i₀ : Fin (f * e) := ⟨0, Nat.mul_pos hf he⟩
  let g : IntermediateField K (SeparableClosure K) → ℝ≥0∞ := fun L ↦
    if L.inertiaDegree = f then 1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ L.discriminantExponent else 0
  -- Rewrite the subtype sum as an indicator sum over transitive Galois sets (`tsum_isTransitive`).
  let S₁ : Set {ρ : GaloisSet K (f * e) // ρ.IsTransitive} :=
    {ρ | letI := ρ.1.mulAction
      (IntermediateField.fixedField
        (MulAction.stabilizer Gal(SeparableClosure K/K) i₀)).inertiaDegree = f}
  let h₁ : {ρ : GaloisSet K (f * e) // ρ.IsTransitive} → ℝ≥0∞ := fun ρ ↦
    1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ ρ.1.discriminantExponent
  let E₁ : {ρ : GaloisSet K (f * e) // ρ.splittingSymbol = {(f, e)}} ≃ S₁ :=
    (Equiv.subtypeEquivRight fun ρ ↦ ρ.splittingSymbol_eq_singleton_iff hf i₀).trans
      (Equiv.subtypeSubtypeEquivSubtypeInter GaloisSet.IsTransitive fun ρ ↦
        letI := ρ.mulAction
        (IntermediateField.fixedField
          (MulAction.stabilizer Gal(SeparableClosure K/K) i₀)).inertiaDegree = f).symm
  have hE₁ : ∑' ρ : {ρ : GaloisSet K (f * e) // ρ.splittingSymbol = {(f, e)}},
        1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ ρ.1.discriminantExponent =
      ∑' ρ : S₁, h₁ ρ := E₁.tsum_eq fun ρ ↦ h₁ ρ
  have hind : ∀ ρ : {ρ : GaloisSet K (f * e) // ρ.IsTransitive},
      S₁.indicator h₁ ρ =
        (letI := ρ.1.mulAction
        g (IntermediateField.fixedField
          (MulAction.stabilizer Gal(SeparableClosure K/K) i₀))) := fun ρ ↦ by
    by_cases h : ρ ∈ S₁
    · have hfρ : (letI := ρ.1.mulAction
          (IntermediateField.fixedField
            (MulAction.stabilizer Gal(SeparableClosure K/K) i₀)).inertiaDegree) = f := h
      simp [Set.indicator_of_mem h, h₁, g, hfρ, ρ.1.discriminantExponent_of_isTransitive ρ.2 i₀]
    · have hfρ : (letI := ρ.1.mulAction
          (IntermediateField.fixedField
            (MulAction.stabilizer Gal(SeparableClosure K/K) i₀)).inertiaDegree) ≠ f := h
      simp [Set.indicator_of_notMem h, g, hfρ]
  rw [hE₁, tsum_subtype S₁ h₁, tsum_congr hind, GaloisSet.tsum_isTransitive i₀ g]
  congr 1
  -- Restrict the subextension sum to residue degree `f` and evaluate by `tsum_inertiaDegree_eq`.
  let S₂ : Set {L : IntermediateField K (SeparableClosure K) // Module.finrank K L = f * e} :=
    {L | L.1.inertiaDegree = f}
  let h₂ : {L : IntermediateField K (SeparableClosure K) // Module.finrank K L = f * e} → ℝ≥0∞ :=
    fun L ↦ 1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ L.1.discriminantExponent
  let E₂ : S₂ ≃ {L : IntermediateField K (SeparableClosure K) //
        Module.finrank K L = f * e ∧ L.inertiaDegree = f} :=
    Equiv.subtypeSubtypeEquivSubtypeInter
      (fun L : IntermediateField K (SeparableClosure K) ↦ Module.finrank K L = f * e)
      (fun L ↦ L.inertiaDegree = f)
  have hE₂ : ∑' L : S₂, h₂ L =
      ∑' L : {L : IntermediateField K (SeparableClosure K) //
          Module.finrank K L = f * e ∧ L.inertiaDegree = f},
        1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ L.1.discriminantExponent :=
    E₂.tsum_eq fun L ↦ 1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ L.1.discriminantExponent
  have hg : ∀ L : {L : IntermediateField K (SeparableClosure K) // Module.finrank K L = f * e},
      g L.1 = S₂.indicator h₂ L := fun L ↦ by
    by_cases h : L ∈ S₂
    · have hfL : L.1.inertiaDegree = f := h
      simp [Set.indicator_of_mem h, h₂, g, hfL]
    · have hfL : L.1.inertiaDegree ≠ f := h
      simp [Set.indicator_of_notMem h, g, hfL]
  rw [tsum_congr hg, ← tsum_subtype S₂ h₂, hE₂, tsum_inertiaDegree_eq hf.ne' e]

/-- **The transitive mass by residue degree**: for `f, e ≥ 1`, the labelled Galois sets of size
`f * e` with splitting symbol `{(f, e)}` satisfy
`((f * e)!)⁻¹ ∑_ρ q ^ (-d(ρ)) = 1 / (f · q ^ (f (e - 1)))`, where `q` is the residue cardinality of
`K`. -/
theorem etaleMass_isTransitive_splittingSymbol (f e : ℕ) (hf : 0 < f) (he : 0 < e) :
    ((f * e)! : ℝ≥0∞)⁻¹ *
        ∑' ρ : {ρ : GaloisSet K (f * e) // ρ.splittingSymbol = {(f, e)}},
          1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ ρ.1.discriminantExponent =
      1 / ((f : ℝ≥0∞) * (Nat.card 𝓀[K] : ℝ≥0∞) ^ (f * (e - 1))) := by
  rw [tsum_splittingSymbol_singleton_eq f e hf he]
  set q : ℝ≥0∞ := (Nat.card 𝓀[K] : ℝ≥0∞) ^ (f * (e - 1))
  have hfact : ((f * e)! : ℝ≥0∞) = (f : ℝ≥0∞) * ((e : ℝ≥0∞) * ((f * e - 1)! : ℝ≥0∞)) := by
    have := Nat.mul_factorial_pred (Nat.mul_pos hf he).ne'
    exact_mod_cast this.symm.trans (mul_assoc _ _ _)
  have hf0 : (f : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.2 hf.ne'
  have hftop : (f : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top f
  have he0 : (e : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.2 he.ne'
  have hetop : (e : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top e
  have hfac0 : ((f * e - 1)! : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
  have hfactop : ((f * e - 1)! : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  rw [hfact, ENNReal.mul_inv (.inl hf0) (.inl hftop),
    ENNReal.mul_inv (.inl he0) (.inl hetop), div_eq_mul_inv, one_div,
    ENNReal.mul_inv (.inl hf0) (.inl hftop)]
  calc
    (f : ℝ≥0∞)⁻¹ * ((e : ℝ≥0∞)⁻¹ * ((f * e - 1)! : ℝ≥0∞)⁻¹) *
        (((f * e - 1)! : ℝ≥0∞) * ((e : ℝ≥0∞) * q⁻¹)) =
      (f : ℝ≥0∞)⁻¹ * (((e : ℝ≥0∞)⁻¹ * (e : ℝ≥0∞)) *
        (((f * e - 1)! : ℝ≥0∞)⁻¹ * ((f * e - 1)! : ℝ≥0∞))) * q⁻¹ := by ring
    _ = (f : ℝ≥0∞)⁻¹ * q⁻¹ := by
      rw [ENNReal.inv_mul_cancel he0 hetop, ENNReal.inv_mul_cancel hfac0 hfactop, mul_one, mul_one]

end TauCeti
