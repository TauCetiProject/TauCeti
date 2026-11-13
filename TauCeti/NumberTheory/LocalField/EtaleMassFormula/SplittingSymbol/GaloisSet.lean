/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.Galois.GaloisSet.Relabelling
public import TauCeti.FieldTheory.Galois.GaloisSet.Sum
public import TauCeti.NumberTheory.LocalField.Unramified.IntermediateField
import TauCeti.Algebra.GroupAction.OrbitRelQuotient
import TauCeti.FieldTheory.Galois.FixedField

/-!
# Splitting symbols of labelled Galois sets

For a labelled Galois set `ρ : TauCeti.GaloisSet K n` over a nonarchimedean local field `K`,
`TauCeti.GaloisSet.splittingSymbol` records the multiset, over the orbits of `ρ`, of the pair
`(f, e)` of residue degree and ramification index of the fixed field of a point stabilizer
[Bhargava 2007, (2.1)]. Conjugate stabilizers have `K`-isomorphic fixed fields, so neither the
residue degree nor the degree depends on the chosen representative of each orbit.

Every factor `(f, e)` of `ρ.splittingSymbol` has positive `f` and `e`, and the products `f * e` add
up to `n`, since `f * e` is the degree of the fixed field of the orbit, namely the orbit size. The
splitting symbol is invariant under equivariant bijection (in particular under relabelling) and
additive on disjoint unions. On a nonempty Galois set, `ρ.splittingSymbol = {(f, e)}` holds
precisely when `ρ` is transitive and the fixed field of a point stabilizer has degree `f * e` and
residue degree `f`.

## Main definitions and results

* `TauCeti.GaloisSet.splittingSymbol`: the splitting symbol of a labelled Galois set.
* `TauCeti.GaloisSet.mem_splittingSymbol_iff`: characterization of the factors of
  `ρ.splittingSymbol` by labels in `Fin n`.
* `TauCeti.GaloisSet.pos_of_mem_splittingSymbol`: every factor `(f, e)` satisfies `0 < f` and
  `0 < e`.
* `TauCeti.GaloisSet.sum_map_mul_splittingSymbol`: `∑ f * e = n`.
* `TauCeti.GaloisSet.splittingSymbol_eq_of_equiv`, `TauCeti.GaloisSet.splittingSymbol_smul`, and
  `TauCeti.GaloisSet.splittingSymbol_sum`: invariance under equivariant bijection and additivity on
  disjoint unions.
* `TauCeti.GaloisSet.splittingSymbol_of_isTransitive` and
  `TauCeti.GaloisSet.splittingSymbol_eq_singleton_iff`: the transitive case.
* `TauCeti.GaloisSet.splittingSymbol_trivial`: the trivial Galois set of size `n` has splitting
  symbol `n · {(1, 1)}`.

## References

* M. Bhargava, *Mass formulae for extensions of local fields, and conjectures on the density of
  number field discriminants*, IMRN **2007**, rnm052, (2.1) and §2.
* K. S. Kedlaya, *Mass formulas for local Galois representations*, IMRN **2007**, rnm021.
-/

public section

noncomputable section

namespace TauCeti.GaloisSet

open _root_.MulAction

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] {n : ℕ}

/-! ### Invariance of the `(f, e)` pair along an orbit -/

/-- The pair `(f(F/K), [F : K] / f(F/K))` of a subextension `F` of `SeparableClosure K`. -/
private def fixedFieldSplittingPair (F : IntermediateField K (SeparableClosure K)) : ℕ × ℕ :=
  (F.inertiaDegree, Module.finrank K F / F.inertiaDegree)

/-- `fixedFieldSplittingPair` is invariant under `K`-algebra equivalence. -/
private theorem fixedFieldSplittingPair_eq_of_algEquiv
    {L M : IntermediateField K (SeparableClosure K)} (e : L ≃ₐ[K] M) :
    fixedFieldSplittingPair L = fixedFieldSplittingPair M := by
  rw [fixedFieldSplittingPair, fixedFieldSplittingPair,
    IntermediateField.inertiaDegree_eq_of_algEquiv e, e.toLinearEquiv.finrank_eq]

/-- Translating a point along a Galois orbit preserves `fixedFieldSplittingPair` of its
stabilizer's fixed field. -/
private theorem fixedFieldSplittingPair_fixedField_stabilizer_smul
    {X : Type*} [MulAction Gal(SeparableClosure K/K) X]
    (σ : Gal(SeparableClosure K/K)) (x : X) :
    fixedFieldSplittingPair (IntermediateField.fixedField
        (stabilizer Gal(SeparableClosure K/K) (σ • x))) =
      fixedFieldSplittingPair (IntermediateField.fixedField
        (stabilizer Gal(SeparableClosure K/K) x)) := by
  rw [stabilizer_smul_eq_stabilizer_map_conj, MulEquiv.toMonoidHom_eq_coe,
    Subgroup.fixedField_map_conj]
  exact (fixedFieldSplittingPair_eq_of_algEquiv
    ((IntermediateField.fixedField (stabilizer Gal(SeparableClosure K/K) x)).equivMap
      σ.toAlgHom)).symm

/-- Replacing `ω.out` by any point `x` in the orbit `ω` preserves `fixedFieldSplittingPair`. -/
private theorem fixedFieldSplittingPair_fixedField_stabilizer_out
    {X : Type*} [MulAction Gal(SeparableClosure K/K) X]
    {ω : orbitRel.Quotient Gal(SeparableClosure K/K) X} {x : X}
    (hx : (Quotient.mk'' x : orbitRel.Quotient Gal(SeparableClosure K/K) X) = ω) :
    fixedFieldSplittingPair (IntermediateField.fixedField
        (stabilizer Gal(SeparableClosure K/K) ω.out)) =
      fixedFieldSplittingPair (IntermediateField.fixedField
        (stabilizer Gal(SeparableClosure K/K) x)) := by
  obtain ⟨σ, rfl⟩ := TauCeti.MulAction.exists_smul_out_eq hx
  exact (fixedFieldSplittingPair_fixedField_stabilizer_smul σ ω.out).symm

/-- Along an equivariant injection, the orbit representative of `f x` has the same
`fixedFieldSplittingPair` as `x`. -/
private theorem fixedFieldSplittingPair_fixedField_stabilizer_out_of_injective
    {X Y : Type*} [MulAction Gal(SeparableClosure K/K) X]
    [MulAction Gal(SeparableClosure K/K) Y]
    (f : X → Y) (hf : Function.Injective f)
    (he : ∀ (σ : Gal(SeparableClosure K/K)) (x : X), f (σ • x) = σ • f x)
    {ω : orbitRel.Quotient Gal(SeparableClosure K/K) Y} {x : X}
    (hx : (Quotient.mk'' (f x) : orbitRel.Quotient Gal(SeparableClosure K/K) Y) = ω) :
    fixedFieldSplittingPair (IntermediateField.fixedField
        (stabilizer Gal(SeparableClosure K/K) ω.out)) =
      fixedFieldSplittingPair (IntermediateField.fixedField
        (stabilizer Gal(SeparableClosure K/K) x)) := by
  rw [fixedFieldSplittingPair_fixedField_stabilizer_out hx,
    TauCeti.MulAction.stabilizer_eq_of_injective f hf he]

/-! ### Definition and characteristic properties -/

open scoped Classical in
/-- The **splitting symbol** of a labelled Galois set [Bhargava 2007, (2.1)]: the multiset, over
its orbits, of the pair `(f, e)` of residue degree and ramification index of the fixed field of the
stabilizer of a point of the orbit. -/
def splittingSymbol (ρ : GaloisSet K n) : Multiset (ℕ × ℕ) :=
  letI := ρ.mulAction
  haveI := Fintype.ofFinite
    (orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n))
  (Finset.univ : Finset
      (orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n))).val.map
    fun O ↦ (fun F : IntermediateField K (SeparableClosure K) ↦
      (F.inertiaDegree, Module.finrank K F / F.inertiaDegree))
        (IntermediateField.fixedField
          (stabilizer Gal(SeparableClosure K/K) (Quotient.out O : Fin n)))

open scoped Classical in
/-- The defining formula of `GaloisSet.splittingSymbol`. -/
theorem splittingSymbol_def (ρ : GaloisSet K n) :
    ρ.splittingSymbol =
      (letI := ρ.mulAction
      haveI := Fintype.ofFinite
        (orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n))
      (Finset.univ : Finset
          (orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n))).val.map
        fun O ↦ (fun F : IntermediateField K (SeparableClosure K) ↦
          (F.inertiaDegree, Module.finrank K F / F.inertiaDegree))
            (IntermediateField.fixedField
              (stabilizer Gal(SeparableClosure K/K) (Quotient.out O : Fin n)))) :=
  (rfl)

/-- The `(f, e)` pair of the fixed field of the stabilizer of any label `i : Fin n` belongs to
`ρ.splittingSymbol`. -/
theorem mem_splittingSymbol_of_label (ρ : GaloisSet K n) (i : Fin n) :
    (letI := ρ.mulAction;
    let F := IntermediateField.fixedField (stabilizer Gal(SeparableClosure K/K) i);
    (F.inertiaDegree, Module.finrank K F / F.inertiaDegree)) ∈ ρ.splittingSymbol := by
  classical
  let := ρ.mulAction
  let := Fintype.ofFinite (orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n))
  rw [splittingSymbol_def, Multiset.mem_map]
  refine ⟨Quotient.mk'' i, Finset.mem_univ_val _, ?_⟩
  exact fixedFieldSplittingPair_fixedField_stabilizer_out (K := K) rfl

/-- A pair `x` belongs to `ρ.splittingSymbol` if and only if it is the `(f, e)` pair of the fixed
field of the stabilizer of some label `i : Fin n`. -/
theorem mem_splittingSymbol_iff {ρ : GaloisSet K n} {x : ℕ × ℕ} :
    x ∈ ρ.splittingSymbol ↔
      ∃ i : Fin n,
        letI := ρ.mulAction
        let F := IntermediateField.fixedField (stabilizer Gal(SeparableClosure K/K) i)
        (F.inertiaDegree, Module.finrank K F / F.inertiaDegree) = x := by
  classical
  let := ρ.mulAction
  let := Fintype.ofFinite (orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n))
  constructor
  · intro hx
    rw [splittingSymbol_def, Multiset.mem_map] at hx
    obtain ⟨O, _, rfl⟩ := hx
    exact ⟨O.out, rfl⟩
  · rintro ⟨i, rfl⟩
    exact ρ.mem_splittingSymbol_of_label i

/-- Every factor `(f, e)` of a splitting symbol of a Galois set has positive residue degree and
positive ramification index. -/
theorem pos_of_mem_splittingSymbol {ρ : GaloisSet K n} {x : ℕ × ℕ} (hx : x ∈ ρ.splittingSymbol) :
    0 < x.1 ∧ 0 < x.2 := by
  obtain ⟨i, rfl⟩ := mem_splittingSymbol_iff.1 hx
  let := ρ.mulAction
  have := ρ.finiteDimensional_fixedField_stabilizer i
  exact ⟨IntermediateField.inertiaDegree_pos _, IntermediateField.finrank_div_inertiaDegree_pos _⟩

/-- The number of factors in `ρ.splittingSymbol`, counted with multiplicity, is the number of
orbits of `ρ`. -/
@[simp]
theorem card_splittingSymbol (ρ : GaloisSet K n) :
    Multiset.card ρ.splittingSymbol =
      (letI := ρ.mulAction
      Nat.card (orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n))) := by
  classical
  let := ρ.mulAction
  let := Fintype.ofFinite (orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n))
  rw [splittingSymbol_def, Multiset.card_map, Finset.card_val, Finset.card_univ,
    Nat.card_eq_fintype_card]

/-- The degree `∑ f * e` of the splitting symbol of a Galois set of size `n` is `n`. -/
@[simp]
theorem sum_map_mul_splittingSymbol (ρ : GaloisSet K n) :
    (ρ.splittingSymbol.map fun x ↦ x.1 * x.2).sum = n := by
  classical
  let := ρ.mulAction
  let := Fintype.ofFinite (orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n))
  rw [splittingSymbol_def, Multiset.map_map]
  have horb : ∀ O : orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n),
      (let F := IntermediateField.fixedField (stabilizer Gal(SeparableClosure K/K) O.out)
      F.inertiaDegree * (Module.finrank K F / F.inertiaDegree)) =
        Fintype.card (orbit Gal(SeparableClosure K/K) O.out) := by
    intro O
    rw [Nat.mul_div_cancel' (IntermediateField.inertiaDegree_dvd_finrank _),
      ρ.finrank_fixedField_stabilizer O.out, Nat.card_eq_fintype_card]
  have hmap :
      ((Finset.univ : Finset (orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n))).val.map
        ((fun x : ℕ × ℕ ↦ x.1 * x.2) ∘ fun O ↦
          let F := IntermediateField.fixedField (stabilizer Gal(SeparableClosure K/K) O.out)
          (F.inertiaDegree, Module.finrank K F / F.inertiaDegree))).sum =
        ∑ O : orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n),
          Fintype.card (orbit Gal(SeparableClosure K/K) O.out) := by
    rw [Finset.sum_eq_multiset_sum]
    exact congrArg Multiset.sum (Multiset.map_congr rfl fun O _ ↦ horb O)
  rw [hmap, ← Fintype.card_sigma,
    ← Fintype.card_congr (MulAction.selfEquivSigmaOrbits Gal(SeparableClosure K/K) (Fin n)),
    Fintype.card_fin]

/-! ### Functoriality and disjoint unions -/

/-- Equivariant bijections preserve the splitting symbol of labelled Galois sets. -/
theorem splittingSymbol_eq_of_equiv {m : ℕ} (ρ : GaloisSet K n) (τ : GaloisSet K m)
    (e : Fin n ≃ Fin m)
    (he : ∀ (σ : Gal(SeparableClosure K/K)) (i : Fin n),
      e (ρ.val σ i) = τ.val σ (e i)) :
    ρ.splittingSymbol = τ.splittingSymbol := by
  classical
  let := ρ.mulAction
  let := τ.mulAction
  let := Fintype.ofFinite (orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n))
  let := Fintype.ofFinite (orbitRel.Quotient Gal(SeparableClosure K/K) (Fin m))
  let E := TauCeti.MulAction.orbitRelQuotientCongr (MulEquiv.refl Gal(SeparableClosure K/K)) e he
  rw [splittingSymbol_def, splittingSymbol_def, ← Multiset.map_univ_val_equiv E, Multiset.map_map]
  refine Multiset.map_congr rfl fun ω _ ↦ ?_
  have hE : (Quotient.mk'' (e ω.out) : orbitRel.Quotient Gal(SeparableClosure K/K) (Fin m)) =
      E ω := by
    rw [← TauCeti.MulAction.orbitRelQuotientCongr_mk (MulEquiv.refl _) e he, Quotient.out_eq']
  exact (fixedFieldSplittingPair_fixedField_stabilizer_out_of_injective (K := K)
    e e.injective he hE).symm

/-- Relabelling a Galois set leaves its splitting symbol unchanged. -/
@[simp]
theorem splittingSymbol_smul (ρ : GaloisSet K n) (e : Equiv.Perm (Fin n)) :
    (e • ρ).splittingSymbol = ρ.splittingSymbol :=
  (ρ.splittingSymbol_eq_of_equiv (e • ρ) e (by simp)).symm

/-- The splitting symbol of a disjoint union of labelled Galois sets is the sum of their splitting
symbols. -/
@[simp]
theorem splittingSymbol_sum {m l : ℕ} (ρ₁ : GaloisSet K m) (ρ₂ : GaloisSet K l)
    (e : Fin m ⊕ Fin l ≃ Fin n) :
    (sum ρ₁ ρ₂ e).splittingSymbol = ρ₁.splittingSymbol + ρ₂.splittingSymbol := by
  classical
  let := ρ₁.mulAction
  let := ρ₂.mulAction
  let := (sum ρ₁ ρ₂ e).mulAction
  let := Fintype.ofFinite (orbitRel.Quotient Gal(SeparableClosure K/K) (Fin m))
  let := Fintype.ofFinite (orbitRel.Quotient Gal(SeparableClosure K/K) (Fin l))
  let := Fintype.ofFinite (orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n))
  let E₁ := TauCeti.MulAction.orbitRelQuotientCongr (MulEquiv.refl Gal(SeparableClosure K/K)) e
    (fun σ x ↦ by rcases x with i | j <;> simp)
  let E₂ := (TauCeti.MulAction.orbitRelQuotientSumEquiv
    (G := Gal(SeparableClosure K/K)) (X := Fin m) (Y := Fin l)).symm
  let E := E₂.trans E₁
  rw [splittingSymbol_def, splittingSymbol_def, splittingSymbol_def,
    ← Multiset.map_univ_val_equiv E, ← Finset.univ_disjSum_univ, Finset.val_disjSum,
    Multiset.disjSum, Multiset.map_add, Multiset.map_map, Multiset.map_map,
    Multiset.map_add, Multiset.map_map, Multiset.map_map]
  congr 1
  · refine Multiset.map_congr rfl fun ω _ ↦ ?_
    have hE : (Quotient.mk'' (e (Sum.inl ω.out)) :
        orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n)) = E (Sum.inl ω) := by
      apply E.symm.injective
      simp [E, E₁, E₂]
    exact fixedFieldSplittingPair_fixedField_stabilizer_out_of_injective (K := K)
      (e ∘ Sum.inl) (e.injective.comp Sum.inl_injective) (fun σ i ↦ by simp) hE
  · refine Multiset.map_congr rfl fun ω _ ↦ ?_
    have hE : (Quotient.mk'' (e (Sum.inr ω.out)) :
        orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n)) = E (Sum.inr ω) := by
      apply E.symm.injective
      simp [E, E₁, E₂]
    exact fixedFieldSplittingPair_fixedField_stabilizer_out_of_injective (K := K)
      (e ∘ Sum.inr) (e.injective.comp Sum.inr_injective) (fun σ j ↦ by simp) hE

/-! ### Empty, transitive, and trivial Galois sets -/

/-- An action on an empty label set has the empty splitting symbol. -/
@[simp]
theorem splittingSymbol_of_isEmpty [IsEmpty (Fin n)] (ρ : GaloisSet K n) :
    ρ.splittingSymbol = 0 := by
  rw [← Multiset.card_eq_zero, card_splittingSymbol]
  let := ρ.mulAction
  have : IsEmpty (orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n)) :=
    ⟨Quotient.ind' isEmptyElim⟩
  exact Nat.card_eq_zero.mpr (Or.inl inferInstance)

/-- A transitive labelled Galois set has a singleton splitting symbol, computed at any label `i`. -/
theorem splittingSymbol_of_isTransitive (ρ : GaloisSet K n) (hρ : ρ.IsTransitive) (i : Fin n) :
    ρ.splittingSymbol =
      {(letI := ρ.mulAction;
        (fun F : IntermediateField K (SeparableClosure K) ↦
          (F.inertiaDegree, Module.finrank K F / F.inertiaDegree))
          (IntermediateField.fixedField (stabilizer Gal(SeparableClosure K/K) i)))} := by
  classical
  let := ρ.mulAction
  have : Nonempty (Fin n) := ⟨i⟩
  have : MulAction.IsPretransitive Gal(SeparableClosure K/K) (Fin n) := ρ.isTransitive_def.1 hρ
  let := ((MulAction.pretransitive_iff_unique_quotient_of_nonempty
    Gal(SeparableClosure K/K) (Fin n)).mp inferInstance).some
  let := Fintype.ofFinite (orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n))
  have huniv : (Finset.univ : Finset (orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n))) =
      {Quotient.mk'' i} := by
    ext ω
    exact iff_of_true (Finset.mem_univ _) (Finset.mem_singleton.mpr (Subsingleton.elim _ _))
  rw [splittingSymbol_def, huniv, Finset.singleton_val, Multiset.map_singleton]
  exact congrArg (· ::ₘ 0) (fixedFieldSplittingPair_fixedField_stabilizer_out (K := K) rfl)

/-- On a nonempty Galois set (witnessed by `i : Fin n`), the splitting symbol is `{(f, e)}` if and
only if the action is transitive and the fixed field at `i` has degree `f * e` and residue degree
`f`. -/
theorem splittingSymbol_eq_singleton_iff (ρ : GaloisSet K n) (i : Fin n) (f e : ℕ) :
    ρ.splittingSymbol = {(f, e)} ↔
      ρ.IsTransitive ∧
        letI := ρ.mulAction
        let F := IntermediateField.fixedField (stabilizer Gal(SeparableClosure K/K) i)
        Module.finrank K F = f * e ∧ F.inertiaDegree = f := by
  let := ρ.mulAction
  have : Nonempty (Fin n) := ⟨i⟩
  have := ρ.finiteDimensional_fixedField_stabilizer i
  constructor
  · intro h
    have hcard : Nat.card (orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n)) = 1 := by
      rw [← ρ.card_splittingSymbol, h, Multiset.card_singleton]
    have : Subsingleton (orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n)) :=
      Finite.card_le_one_iff_subsingleton.mp hcard.le
    have htrans : ρ.IsTransitive :=
      ρ.isTransitive_def.2 <|
        (MulAction.pretransitive_iff_unique_quotient_of_nonempty
          Gal(SeparableClosure K/K) (Fin n)).mpr
          ⟨{ default := Quotient.mk'' i, uniq := fun _ ↦ Subsingleton.elim _ _ }⟩
    have hsym := (ρ.splittingSymbol_of_isTransitive htrans i).symm.trans h
    obtain ⟨hf, he⟩ := Prod.mk.inj (Multiset.singleton_inj.mp hsym)
    refine ⟨htrans, ?_, hf⟩
    rw [← hf, ← he, Nat.mul_div_cancel' (IntermediateField.inertiaDegree_dvd_finrank _)]
  · rintro ⟨htrans, hrank, hf⟩
    have hf_pos : 0 < f := hf ▸ IntermediateField.inertiaDegree_pos
      (IntermediateField.fixedField (stabilizer Gal(SeparableClosure K/K) i))
    rw [ρ.splittingSymbol_of_isTransitive htrans i]
    dsimp only
    rw [hrank, hf, Nat.mul_div_right e hf_pos]

/-- The trivial Galois set of size `n` has splitting symbol `n · {(1, 1)}`. -/
@[simp]
theorem splittingSymbol_trivial :
    (trivial K n).splittingSymbol = Multiset.replicate n (1, 1) := by
  classical
  let := (trivial K n).mulAction
  let := Fintype.ofFinite (orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n))
  have hbij : Function.Bijective
      (fun i : Fin n ↦ (Quotient.mk'' i : orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n))) :=
    ⟨fun i j h ↦ by
      obtain ⟨σ, hσ⟩ := Quotient.exact' h
      simpa using hσ.symm,
      Quotient.mk''_surjective⟩
  let E : Fin n ≃ orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n) := Equiv.ofBijective _ hbij
  rw [splittingSymbol_def, ← Multiset.map_univ_val_equiv E, Multiset.map_map]
  have hconst : ∀ i : Fin n,
      (fun F : IntermediateField K (SeparableClosure K) ↦
        (F.inertiaDegree, Module.finrank K F / F.inertiaDegree))
        (IntermediateField.fixedField (stabilizer Gal(SeparableClosure K/K) (E i).out)) =
        (1, 1) := by
    intro i
    have hEi : (Quotient.mk'' i : orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n)) = E i :=
      (Equiv.ofBijective_apply _ hbij i).symm
    refine (fixedFieldSplittingPair_fixedField_stabilizer_out (K := K) hEi).trans ?_
    rw [fixedFieldSplittingPair, fixedField_stabilizer_trivial,
      IntermediateField.inertiaDegree_bot, IntermediateField.finrank_bot]
  have hmap :
      (Finset.univ : Finset (Fin n)).val.map
        ((fun O : orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n) ↦
          (fun F : IntermediateField K (SeparableClosure K) ↦
            (F.inertiaDegree, Module.finrank K F / F.inertiaDegree))
            (IntermediateField.fixedField (stabilizer Gal(SeparableClosure K/K) O.out))) ∘ E) =
        (Finset.univ : Finset (Fin n)).val.map (Function.const _ (1, 1)) :=
    Multiset.map_congr rfl fun i _ ↦ hconst i
  rw [hmap, Multiset.map_const, Finset.card_val, Finset.card_univ, Fintype.card_fin]

end TauCeti.GaloisSet
