/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.Galois.GaloisSet.Relabelling
public import TauCeti.FieldTheory.Galois.GaloisSet.Sum
public import TauCeti.NumberTheory.LocalField.EtaleMassFormula.Mass
public import TauCeti.NumberTheory.LocalField.EtaleMassFormula.SubfieldCount
import TauCeti.FieldTheory.Galois.FixedField

/-!
# Splitting symbols of labelled Galois sets and the transitive mass

For a nonarchimedean local field `K` with `q` residue classes, the *splitting symbol*
`TauCeti.GaloisSet.splittingSymbol ρ` of a labelled Galois set `ρ : TauCeti.GaloisSet K n` is the
multiset, over the orbits of `ρ`, of the pair `(f, e)` consisting of the residue degree and
ramification index of the fixed field of a point stabilizer in that orbit ([Bhargava 2007, (2.1)]).
Because conjugate stabilizers have `K`-isomorphic fixed fields, the pair depends only on the orbit
and the splitting symbol is invariant under equivariant bijections and relabellings, and additive
under disjoint unions (`TauCeti.GaloisSet.splittingSymbol_ofSumEquiv`). Every entry `(f, e)` has
positive coordinates and the products `f * e` sum to `n`.

A labelled Galois set of size `f * e` (with `f, e > 0`) has singleton splitting symbol `{(f, e)}`
precisely when it is transitive and its stabilizer fixed field has residue degree `f`
(`TauCeti.GaloisSet.splittingSymbol_eq_singleton_iff`). Combining the transitive bridge
`TauCeti.GaloisSet.tsum_isTransitive` with the weighted subfield count
`TauCeti.tsum_inertiaDegree_eq` gives the transitive mass by residue degree:
`(1 / (f * e)!) ∑_{ρ.splittingSymbol = {(f, e)}} q ^ (-d(ρ)) = 1 / (f · q ^ (f (e - 1)))`
(`TauCeti.etaleMass_isTransitive_splittingSymbol`).

## Main definitions and results

* `TauCeti.GaloisSet.splittingSymbol`: the splitting symbol of a labelled Galois set.
* `TauCeti.GaloisSet.splittingSymbol_eq_of_equiv`, `TauCeti.GaloisSet.splittingSymbol_smul`:
  invariance under equivariant bijections and relabelling.
* `TauCeti.GaloisSet.splittingSymbol_ofSumEquiv` and
  `TauCeti.GaloisSet.discriminantExponent_ofSumEquiv`: additivity on disjoint unions.
* `TauCeti.GaloisSet.pos_of_mem_splittingSymbol` and
  `TauCeti.GaloisSet.sum_map_mul_splittingSymbol`: positivity of coordinates and degree sum.
* `TauCeti.GaloisSet.splittingSymbol_eq_singleton_iff`: characterization of singleton symbols.
* `TauCeti.etaleMass_isTransitive_splittingSymbol`: the transitive mass for symbol `{(f, e)}`.

## References

* M. Bhargava, *Mass formulae for extensions of local fields, and conjectures on the density of
  number field discriminants*, IMRN **2007**, rnm052, §2.
-/

public section

noncomputable section

open ValuativeRel
open scoped ENNReal Nat

namespace TauCeti

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] {n : ℕ}

section OrbitInertiaDegree

variable {X : Type*} [MulAction Gal(SeparableClosure K/K) X]

/-- Translating a point does not change the residue degree of its stabilizer's fixed field,
since the two fixed fields are conjugate. -/
@[simp]
theorem inertiaDegree_fixedField_stabilizer_smul (σ : Gal(SeparableClosure K/K)) (x : X) :
    (IntermediateField.fixedField
      (MulAction.stabilizer Gal(SeparableClosure K/K) (σ • x))).inertiaDegree =
        (IntermediateField.fixedField
          (MulAction.stabilizer Gal(SeparableClosure K/K) x)).inertiaDegree := by
  rw [MulAction.stabilizer_smul_eq_stabilizer_map_conj, MulEquiv.toMonoidHom_eq_coe,
    Subgroup.fixedField_map_conj]
  exact (IntermediateField.inertiaDegree_eq_of_algEquiv
    ((IntermediateField.fixedField (MulAction.stabilizer Gal(SeparableClosure K/K) x)).equivMap
      σ.toAlgHom)).symm

/-- The residue degree of an orbit's stabilizer fixed field can be computed at any point in that
orbit. -/
theorem inertiaDegree_fixedField_stabilizer_out
    {ω : MulAction.orbitRel.Quotient Gal(SeparableClosure K/K) X} {x : X}
    (hx : (Quotient.mk'' x : MulAction.orbitRel.Quotient Gal(SeparableClosure K/K) X) = ω) :
    (IntermediateField.fixedField
      (MulAction.stabilizer Gal(SeparableClosure K/K) ω.out)).inertiaDegree =
        (IntermediateField.fixedField
          (MulAction.stabilizer Gal(SeparableClosure K/K) x)).inertiaDegree := by
  obtain ⟨σ, rfl⟩ := MulAction.exists_smul_out_eq hx
  exact (inertiaDegree_fixedField_stabilizer_smul σ ω.out).symm

end OrbitInertiaDegree

namespace GaloisSet

/-- The pair `(f, e)` of an orbit's stabilizer fixed field in a labelled Galois set can be computed
at any point of the orbit. -/
private theorem orbitPair_fixedField_stabilizer_out (ρ : GaloisSet K n)
    {ω : letI := ρ.mulAction; MulAction.orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n)}
    {x : Fin n}
    (hx : (letI := ρ.mulAction;
      (Quotient.mk'' x : MulAction.orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n))) = ω) :
    letI := ρ.mulAction
    let F₁ := IntermediateField.fixedField (MulAction.stabilizer Gal(SeparableClosure K/K) ω.out)
    let F₂ := IntermediateField.fixedField (MulAction.stabilizer Gal(SeparableClosure K/K) x)
    (F₁.inertiaDegree, Module.finrank K F₁ / F₁.inertiaDegree) =
      (F₂.inertiaDegree, Module.finrank K F₂ / F₂.inertiaDegree) := by
  let := ρ.mulAction
  obtain ⟨σ, rfl⟩ := MulAction.exists_smul_out_eq hx
  have hf := (inertiaDegree_fixedField_stabilizer_smul (K := K) σ ω.out).symm
  have hd : Module.finrank K (IntermediateField.fixedField
        (MulAction.stabilizer Gal(SeparableClosure K/K) ω.out)) =
      Module.finrank K (IntermediateField.fixedField
        (MulAction.stabilizer Gal(SeparableClosure K/K) (σ • ω.out))) := by
    rw [ρ.finrank_fixedField_stabilizer, ρ.finrank_fixedField_stabilizer, MulAction.orbit_smul]
  exact Prod.ext hf (by rw [hf, hd])

open scoped Classical in
/-- The **splitting symbol** of a labelled Galois set ([Bhargava 2007, (2.1)]): the multiset, over
its orbits, of the pair `(f, e)` of residue degree and ramification index of the fixed field of a
point stabilizer in that orbit. -/
def splittingSymbol (ρ : GaloisSet K n) : Multiset (ℕ × ℕ) :=
  letI := ρ.mulAction
  haveI := Fintype.ofFinite
    (MulAction.orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n))
  (Finset.univ : Finset
      (MulAction.orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n))).val.map
    fun O =>
      let F := IntermediateField.fixedField
        (MulAction.stabilizer Gal(SeparableClosure K/K) (Quotient.out O : Fin n))
      (F.inertiaDegree, Module.finrank K F / F.inertiaDegree)

/-- The splitting symbol can be computed using any `Fintype` instance on the orbit space and any
choice of one representative per orbit. -/
theorem splittingSymbol_eq_map (ρ : GaloisSet K n)
    [Fintype (letI := ρ.mulAction;
      MulAction.orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n))]
    (s : (letI := ρ.mulAction;
      MulAction.orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n)) → Fin n)
    (hs : ∀ O, (letI := ρ.mulAction;
      (Quotient.mk'' (s O) :
        MulAction.orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n))) = O) :
    ρ.splittingSymbol =
      (Finset.univ : Finset (letI := ρ.mulAction;
        MulAction.orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n))).val.map
        fun O =>
          letI := ρ.mulAction
          let F := IntermediateField.fixedField
            (MulAction.stabilizer Gal(SeparableClosure K/K) (s O))
          (F.inertiaDegree, Module.finrank K F / F.inertiaDegree) := by
  let := ρ.mulAction
  unfold splittingSymbol
  rw [Subsingleton.elim (Fintype.ofFinite _) ‹Fintype _›]
  exact Multiset.map_congr rfl fun O _ ↦ ρ.orbitPair_fixedField_stabilizer_out (hs O)

/-- Equivariant bijections preserve the splitting symbol of labelled Galois sets. -/
theorem splittingSymbol_eq_of_equiv {m : ℕ} (ρ : GaloisSet K n) (τ : GaloisSet K m)
    (e : Fin n ≃ Fin m)
    (he : ∀ (σ : Gal(SeparableClosure K/K)) (i : Fin n),
      e (ρ.val σ i) = τ.val σ (e i)) :
    ρ.splittingSymbol = τ.splittingSymbol := by
  classical
  let := ρ.mulAction
  let := τ.mulAction
  have := Fintype.ofFinite
    (letI := ρ.mulAction; MulAction.orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n))
  have := Fintype.ofFinite
    (letI := τ.mulAction; MulAction.orbitRel.Quotient Gal(SeparableClosure K/K) (Fin m))
  let E := @MulAction.orbitRelQuotientCongr _ _ _ ρ.mulAction _ _ _ τ.mulAction
    (MulEquiv.refl Gal(SeparableClosure K/K)) e he
  rw [splittingSymbol_eq_map ρ Quotient.out (fun O ↦ Quotient.out_eq' O),
    splittingSymbol_eq_map τ Quotient.out (fun O ↦ Quotient.out_eq' O)]
  have hval : (Finset.univ : Finset (letI := τ.mulAction;
      MulAction.orbitRel.Quotient Gal(SeparableClosure K/K) (Fin m))).val =
      (Finset.univ : Finset (letI := ρ.mulAction;
        MulAction.orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n))).val.map E := by
    simp
  rw [hval, Multiset.map_map]
  refine Multiset.map_congr rfl fun O _ ↦ ?_
  have hE : (letI := τ.mulAction;
      (Quotient.mk'' (e O.out) :
        MulAction.orbitRel.Quotient Gal(SeparableClosure K/K) (Fin m))) = E O := by
    rw [← @MulAction.orbitRelQuotientCongr_mk _ _ _ ρ.mulAction _ _ _ τ.mulAction
      (MulEquiv.refl _) e he, Quotient.out_eq']
  have hout := τ.orbitPair_fixedField_stabilizer_out hE
  have hstab :
      (letI := τ.mulAction; MulAction.stabilizer Gal(SeparableClosure K/K) (e O.out)) =
      (letI := ρ.mulAction; MulAction.stabilizer Gal(SeparableClosure K/K) O.out) :=
    @MulAction.stabilizer_eq_of_injective _ _ _ ρ.mulAction _ τ.mulAction e e.injective he O.out
  dsimp only [Function.comp_apply] at hout ⊢
  rw [hout, hstab]

/-- Relabelling a Galois set does not change its splitting symbol. -/
@[simp]
theorem splittingSymbol_smul (ρ : GaloisSet K n) (e : Equiv.Perm (Fin n)) :
    (e • ρ).splittingSymbol = ρ.splittingSymbol :=
  (ρ.splittingSymbol_eq_of_equiv (e • ρ) e (by simp)).symm

/-- The unique Galois set of size zero has the empty splitting symbol. -/
@[simp]
theorem splittingSymbol_zero (ρ : GaloisSet K 0) : ρ.splittingSymbol = 0 := by
  classical
  let := ρ.mulAction
  have := Fintype.ofFinite (MulAction.orbitRel.Quotient Gal(SeparableClosure K/K) (Fin 0))
  rw [splittingSymbol_eq_map ρ Quotient.out (fun O ↦ Quotient.out_eq' O)]
  have : IsEmpty (MulAction.orbitRel.Quotient Gal(SeparableClosure K/K) (Fin 0)) :=
    ⟨fun O ↦ Fin.elim0 O.out⟩
  simp

/-- The trivial Galois set of size `n` has splitting symbol consisting of `n` copies of `(1, 1)`. -/
@[simp]
theorem splittingSymbol_trivial :
    (trivial K n).splittingSymbol = Multiset.replicate n (1, 1) := by
  classical
  let := (trivial K n).mulAction
  have := Fintype.ofFinite (MulAction.orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n))
  rw [splittingSymbol_eq_map (trivial K n) Quotient.out (fun O ↦ Quotient.out_eq' O)]
  have hconst : ∀ O : MulAction.orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n),
      (let F := IntermediateField.fixedField
          (MulAction.stabilizer Gal(SeparableClosure K/K) O.out);
        (F.inertiaDegree, Module.finrank K F / F.inertiaDegree)) = (1, 1) := by
    intro O
    simp [fixedField_stabilizer_trivial]
  rw [Multiset.map_congr rfl fun O _ ↦ hconst O, Multiset.map_const', Finset.card_val]
  congr 1
  have hbij : Function.Bijective (Quotient.mk'' : Fin n →
      MulAction.orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n)) := by
    refine ⟨fun i j h ↦ ?_, Quotient.mk''_surjective⟩
    obtain ⟨σ, hσ⟩ := Quotient.exact h
    simpa [GaloisSet.smul_def, GaloisSet.trivial_val_apply] using hσ.symm
  simpa using (Fintype.card_of_bijective hbij).symm

/-- A transitive labelled Galois set has singleton splitting symbol `{(f, n / f)}`, where `f` is
the residue degree of the fixed field of any point stabilizer. -/
theorem splittingSymbol_of_isTransitive (ρ : GaloisSet K n) (hρ : ρ.IsTransitive) (i : Fin n) :
    ρ.splittingSymbol =
      {(letI := ρ.mulAction
        let F := IntermediateField.fixedField (MulAction.stabilizer Gal(SeparableClosure K/K) i)
        (F.inertiaDegree, n / F.inertiaDegree))} := by
  classical
  let := ρ.mulAction
  have : Nonempty (Fin n) := ⟨i⟩
  have : MulAction.IsPretransitive Gal(SeparableClosure K/K) (Fin n) := ρ.isTransitive_def.1 hρ
  let := ((MulAction.pretransitive_iff_unique_quotient_of_nonempty
    Gal(SeparableClosure K/K) (Fin n)).mp inferInstance).some
  rw [splittingSymbol_eq_map ρ (fun _ ↦ i) (fun O ↦ Subsingleton.elim _ O)]
  have huniv : (Finset.univ :
      Finset (MulAction.orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n))) = {default} :=
    Finset.univ_unique
  rw [huniv, Finset.singleton_val, Multiset.map_singleton]
  dsimp only
  rw [ρ.finrank_fixedField_stabilizer_of_isTransitive hρ i]

/-- A labelled Galois set of size `f * e` (with a label `i`, which forces `f, e > 0`) has singleton
splitting symbol `{(f, e)}` if and only if it is transitive and the fixed field of the stabilizer
of `i` has residue degree `f`. -/
theorem splittingSymbol_eq_singleton_iff {f e : ℕ} (ρ : GaloisSet K (f * e)) (i : Fin (f * e)) :
    ρ.splittingSymbol = {(f, e)} ↔
      ρ.IsTransitive ∧
        (letI := ρ.mulAction;
          (IntermediateField.fixedField
            (MulAction.stabilizer Gal(SeparableClosure K/K) i)).inertiaDegree = f) := by
  have hfe : 0 < f * e := i.pos
  have hf : 0 < f := Nat.pos_of_mul_pos_right hfe
  constructor
  · intro h
    let := ρ.mulAction
    have := Fintype.ofFinite
      (MulAction.orbitRel.Quotient Gal(SeparableClosure K/K) (Fin (f * e)))
    have hcard :
        Fintype.card (MulAction.orbitRel.Quotient Gal(SeparableClosure K/K) (Fin (f * e))) = 1 := by
      have hc := congrArg Multiset.card h
      rw [splittingSymbol_eq_map ρ Quotient.out (fun O ↦ Quotient.out_eq' O),
        Multiset.card_map, Finset.card_val, Multiset.card_singleton] at hc
      exact hc
    have htr : ρ.IsTransitive := by
      have : Subsingleton
          (MulAction.orbitRel.Quotient Gal(SeparableClosure K/K) (Fin (f * e))) :=
        Fintype.card_le_one_iff_subsingleton.mp hcard.le
      exact ρ.isTransitive_def.2 <| (MulAction.pretransitive_iff_subsingleton_quotient
        Gal(SeparableClosure K/K) (Fin (f * e))).mpr inferInstance
    rw [ρ.splittingSymbol_of_isTransitive htr i, Multiset.singleton_inj] at h
    exact ⟨htr, congrArg Prod.fst h⟩
  · rintro ⟨htr, hdeg⟩
    rw [ρ.splittingSymbol_of_isTransitive htr i]
    congr 1
    exact Prod.ext hdeg (by dsimp only; rw [hdeg, Nat.mul_div_right e hf])

/-- Every pair `(f, e)` in the splitting symbol of a labelled Galois set has positive residue degree
and positive ramification index. -/
theorem pos_of_mem_splittingSymbol (ρ : GaloisSet K n) {x : ℕ × ℕ} (hx : x ∈ ρ.splittingSymbol) :
    0 < x.1 ∧ 0 < x.2 := by
  classical
  let := ρ.mulAction
  have := Fintype.ofFinite (MulAction.orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n))
  rw [splittingSymbol_eq_map ρ Quotient.out (fun O ↦ Quotient.out_eq' O), Multiset.mem_map] at hx
  obtain ⟨O, _, rfl⟩ := hx
  have : FiniteDimensional K (IntermediateField.fixedField
      (MulAction.stabilizer Gal(SeparableClosure K/K) O.out)) :=
    ρ.finiteDimensional_fixedField_stabilizer O.out
  have hf : 0 < (IntermediateField.fixedField
      (MulAction.stabilizer Gal(SeparableClosure K/K) O.out)).inertiaDegree :=
    IntermediateField.inertiaDegree_pos _
  have hmul : (IntermediateField.fixedField
      (MulAction.stabilizer Gal(SeparableClosure K/K) O.out)).inertiaDegree *
      (Module.finrank K (IntermediateField.fixedField
        (MulAction.stabilizer Gal(SeparableClosure K/K) O.out)) /
        (IntermediateField.fixedField
          (MulAction.stabilizer Gal(SeparableClosure K/K) O.out)).inertiaDegree) =
      Module.finrank K (IntermediateField.fixedField
        (MulAction.stabilizer Gal(SeparableClosure K/K) O.out)) :=
    Nat.mul_div_cancel' (IntermediateField.inertiaDegree_dvd_finrank _)
  have hpos : 0 < Module.finrank K (IntermediateField.fixedField
      (MulAction.stabilizer Gal(SeparableClosure K/K) O.out)) := Module.finrank_pos
  exact ⟨hf, Nat.pos_of_mul_pos_left (hmul.symm ▸ hpos)⟩

/-- The products `f * e` over the splitting symbol of a labelled Galois set of size `n` sum to
`n`. -/
@[simp]
theorem sum_map_mul_splittingSymbol (ρ : GaloisSet K n) :
    (ρ.splittingSymbol.map fun x => x.1 * x.2).sum = n := by
  classical
  let := ρ.mulAction
  have := Fintype.ofFinite (MulAction.orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n))
  rw [splittingSymbol_eq_map ρ Quotient.out (fun O ↦ Quotient.out_eq' O), Multiset.map_map]
  have hterm : ∀ O : MulAction.orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n),
      ((fun x : ℕ × ℕ => x.1 * x.2) ∘ fun O =>
        let F := IntermediateField.fixedField
          (MulAction.stabilizer Gal(SeparableClosure K/K) O.out)
        (F.inertiaDegree, Module.finrank K F / F.inertiaDegree)) O =
        (Finset.univ.filter fun i : Fin n =>
          (Quotient.mk'' i :
            MulAction.orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n)) = O).card := by
    intro O
    dsimp only [Function.comp_apply]
    rw [Nat.mul_div_cancel' (IntermediateField.inertiaDegree_dvd_finrank _),
      ρ.finrank_fixedField_stabilizer O.out]
    have hset : (Finset.univ.filter fun i : Fin n =>
        (Quotient.mk'' i :
          MulAction.orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n)) = O) =
        (MulAction.orbit Gal(SeparableClosure K/K) O.out).toFinset := by
      ext i
      rw [Finset.mem_filter, Set.mem_toFinset,
        ← MulAction.orbitRel.Quotient.orbit_eq_orbit_out O Quotient.out_eq',
        MulAction.orbitRel.Quotient.mem_orbit]
      simp
    rw [hset, Set.toFinset_card, Nat.card_eq_fintype_card]
  rw [Multiset.map_congr rfl fun O _ ↦ hterm O, Finset.sum_map_val,
    ← Finset.card_eq_sum_card_fiberwise (f := (Quotient.mk'' : Fin n → _))
      (fun _ _ ↦ Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]

/-- The discriminant exponent of a disjoint union of labelled Galois sets is the sum of their
discriminant exponents. -/
@[simp]
theorem discriminantExponent_ofSumEquiv {m n k : ℕ} (e : Fin m ⊕ Fin n ≃ Fin k)
    (ρ₁ : GaloisSet K m) (ρ₂ : GaloisSet K n) :
    (ofSumEquiv e ρ₁ ρ₂).discriminantExponent =
      ρ₁.discriminantExponent + ρ₂.discriminantExponent := by
  let := ρ₁.mulAction
  let := ρ₂.mulAction
  have heq :
      orbitDiscriminantExponent K (Fin m ⊕ Fin n) =
        (letI := (ofSumEquiv e ρ₁ ρ₂).mulAction; orbitDiscriminantExponent K (Fin k)) :=
    @orbitDiscriminantExponent_eq_of_equiv K _ _ _ _ (Fin m ⊕ Fin n) (Fin k)
      inferInstance (ofSumEquiv e ρ₁ ρ₂).mulAction e
      (fun σ x ↦ ofSumEquiv_val_apply_eq_smul e ρ₁ ρ₂ σ x)
  rw [discriminantExponent_def, ← heq, orbitDiscriminantExponent_sum, discriminantExponent_def,
    discriminantExponent_def]

/-- The splitting symbol of a disjoint union of labelled Galois sets is the sum of their splitting
symbols. -/
@[simp]
theorem splittingSymbol_ofSumEquiv {m n k : ℕ} (e : Fin m ⊕ Fin n ≃ Fin k)
    (ρ₁ : GaloisSet K m) (ρ₂ : GaloisSet K n) :
    (ofSumEquiv e ρ₁ ρ₂).splittingSymbol = ρ₁.splittingSymbol + ρ₂.splittingSymbol := by
  classical
  let := ρ₁.mulAction
  let := ρ₂.mulAction
  have := Fintype.ofFinite
    (letI := ρ₁.mulAction; MulAction.orbitRel.Quotient Gal(SeparableClosure K/K) (Fin m))
  have := Fintype.ofFinite
    (letI := ρ₂.mulAction; MulAction.orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n))
  have := Fintype.ofFinite
    (letI := (ofSumEquiv e ρ₁ ρ₂).mulAction;
      MulAction.orbitRel.Quotient Gal(SeparableClosure K/K) (Fin k))
  have he : ∀ (σ : Gal(SeparableClosure K/K)) (x : Fin m ⊕ Fin n),
      e (σ • x) = (letI := (ofSumEquiv e ρ₁ ρ₂).mulAction; (MulEquiv.refl _) σ • e x) :=
    fun σ x ↦ by simpa [GaloisSet.smul_def] using ofSumEquiv_val_apply_eq_smul e ρ₁ ρ₂ σ x
  let E := (@MulAction.orbitRelQuotientCongr _ _ _
      (inferInstance : MulAction Gal(SeparableClosure K/K) (Fin m ⊕ Fin n)) _ _ _
      (ofSumEquiv e ρ₁ ρ₂).mulAction
      (MulEquiv.refl Gal(SeparableClosure K/K)) e he).symm.trans
    (MulAction.orbitRelQuotientSumEquiv (G := Gal(SeparableClosure K/K)) (X := Fin m) (Y := Fin n))
  rw [splittingSymbol_eq_map (ofSumEquiv e ρ₁ ρ₂) Quotient.out (fun O ↦ Quotient.out_eq' O),
    splittingSymbol_eq_map ρ₁ Quotient.out (fun O ↦ Quotient.out_eq' O),
    splittingSymbol_eq_map ρ₂ Quotient.out (fun O ↦ Quotient.out_eq' O)]
  have hval : (Finset.univ : Finset (letI := (ofSumEquiv e ρ₁ ρ₂).mulAction;
      MulAction.orbitRel.Quotient Gal(SeparableClosure K/K) (Fin k))).val =
      (Finset.univ : Finset ((letI := ρ₁.mulAction;
          MulAction.orbitRel.Quotient Gal(SeparableClosure K/K) (Fin m)) ⊕
        (letI := ρ₂.mulAction;
          MulAction.orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n)))).val.map E.symm := by
    simp
  rw [hval, ← Finset.univ_disjSum_univ, Finset.val_disjSum, Multiset.map_map,
    Multiset.map_disjSum]
  congr 1
  · refine Multiset.map_congr rfl fun O _ ↦ ?_
    have hE : (letI := (ofSumEquiv e ρ₁ ρ₂).mulAction;
        (Quotient.mk'' (e (.inl O.out)) :
          MulAction.orbitRel.Quotient Gal(SeparableClosure K/K) (Fin k))) =
        E.symm (.inl O) :=
      E.eq_symm_apply.mpr <| by
        rw [Equiv.trans_apply,
          @MulAction.orbitRelQuotientCongr_symm_mk _ _ _
            (inferInstance : MulAction Gal(SeparableClosure K/K) (Fin m ⊕ Fin n)) _ _ _
            (ofSumEquiv e ρ₁ ρ₂).mulAction,
          Equiv.symm_apply_apply, MulAction.orbitRelQuotientSumEquiv_mk, Sum.map_inl,
          Quotient.out_eq']
    have hout := (ofSumEquiv e ρ₁ ρ₂).orbitPair_fixedField_stabilizer_out hE
    dsimp only [Function.comp_apply] at hout ⊢
    rw [hout, stabilizer_ofSumEquiv_inl]
  · refine Multiset.map_congr rfl fun O _ ↦ ?_
    have hE : (letI := (ofSumEquiv e ρ₁ ρ₂).mulAction;
        (Quotient.mk'' (e (.inr O.out)) :
          MulAction.orbitRel.Quotient Gal(SeparableClosure K/K) (Fin k))) =
        E.symm (.inr O) :=
      E.eq_symm_apply.mpr <| by
        rw [Equiv.trans_apply,
          @MulAction.orbitRelQuotientCongr_symm_mk _ _ _
            (inferInstance : MulAction Gal(SeparableClosure K/K) (Fin m ⊕ Fin n)) _ _ _
            (ofSumEquiv e ρ₁ ρ₂).mulAction,
          Equiv.symm_apply_apply, MulAction.orbitRelQuotientSumEquiv_mk, Sum.map_inr,
          Quotient.out_eq']
    have hout := (ofSumEquiv e ρ₁ ρ₂).orbitPair_fixedField_stabilizer_out hE
    dsimp only [Function.comp_apply] at hout ⊢
    rw [hout, stabilizer_ofSumEquiv_inr]

end GaloisSet

/-- **The transitive mass by residue degree** ([Bhargava 2007, §2]): for `f, e > 0`, the labelled
Galois sets of size `f * e` with splitting symbol `{(f, e)}` (which are transitive) have mass
`1 / (f · q ^ (f (e - 1)))`, where `q` is the residue cardinality of `K`. -/
theorem etaleMass_isTransitive_splittingSymbol {f e : ℕ} (hf : 0 < f) (he : 0 < e) :
    (((f * e)! : ℝ≥0∞))⁻¹ *
        ∑' ρ : {ρ : GaloisSet K (f * e) // ρ.splittingSymbol = {(f, e)}},
          1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ ρ.1.discriminantExponent =
      1 / ((f : ℝ≥0∞) * (Nat.card 𝓀[K] : ℝ≥0∞) ^ (f * (e - 1))) := by
  classical
  let i₀ : Fin (f * e) := ⟨0, Nat.mul_pos hf he⟩
  -- Rewrite the sum over symbol `{(f, e)}` as the transitive bridge applied to the indicator of
  -- residue degree `f`.
  let g : IntermediateField K (SeparableClosure K) → ℝ≥0∞ :=
    fun L ↦ if L.inertiaDegree = f then 1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ L.discriminantExponent else 0
  have htr := GaloisSet.tsum_isTransitive (K := K) i₀ g
  have hlhs :
      ∑' ρ : {ρ : GaloisSet K (f * e) // ρ.splittingSymbol = {(f, e)}},
          1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ ρ.1.discriminantExponent =
        ∑' ρ : {ρ : GaloisSet K (f * e) // ρ.IsTransitive},
          (letI := ρ.1.mulAction
          g (IntermediateField.fixedField
            (MulAction.stabilizer Gal(SeparableClosure K/K) i₀))) := by
    let s₁ : Set {ρ : GaloisSet K (f * e) // ρ.IsTransitive} :=
      {ρ | letI := ρ.1.mulAction
        (IntermediateField.fixedField
          (MulAction.stabilizer Gal(SeparableClosure K/K) i₀)).inertiaDegree = f}
    let e₁ : {ρ : GaloisSet K (f * e) // ρ.splittingSymbol = {(f, e)}} ≃ s₁ :=
      (Equiv.subtypeEquivRight fun ρ ↦ ρ.splittingSymbol_eq_singleton_iff i₀).trans
        (Equiv.subtypeSubtypeEquivSubtypeInter
          (fun ρ : GaloisSet K (f * e) ↦ ρ.IsTransitive)
          (fun ρ ↦ letI := ρ.mulAction;
            (IntermediateField.fixedField
              (MulAction.stabilizer Gal(SeparableClosure K/K) i₀)).inertiaDegree = f)).symm
    calc
      ∑' ρ : {ρ : GaloisSet K (f * e) // ρ.splittingSymbol = {(f, e)}},
          1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ ρ.1.discriminantExponent
        = ∑' ρ : s₁, 1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ ρ.1.1.discriminantExponent :=
          e₁.tsum_eq (fun ρ ↦ 1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ ρ.1.1.discriminantExponent)
      _ = ∑' ρ : {ρ : GaloisSet K (f * e) // ρ.IsTransitive},
            s₁.indicator (fun ρ ↦ 1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ ρ.1.discriminantExponent) ρ :=
          tsum_subtype s₁ (fun ρ ↦ 1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ ρ.1.discriminantExponent)
      _ = ∑' ρ : {ρ : GaloisSet K (f * e) // ρ.IsTransitive},
            (letI := ρ.1.mulAction
            g (IntermediateField.fixedField
              (MulAction.stabilizer Gal(SeparableClosure K/K) i₀))) := by
          refine tsum_congr fun ρ ↦ ?_
          simp only [Set.indicator_apply, s₁, Set.mem_ofPred_eq, g]
          split_ifs
          · rw [ρ.1.discriminantExponent_of_isTransitive ρ.2 i₀]
          · rfl
  have hrhs :
      ∑' L : {L : IntermediateField K (SeparableClosure K) // Module.finrank K L = f * e}, g L.1 =
        (e : ℝ≥0∞) / (Nat.card 𝓀[K] : ℝ≥0∞) ^ (f * (e - 1)) := by
    let s₂ : Set {L : IntermediateField K (SeparableClosure K) // Module.finrank K L = f * e} :=
      {L | L.1.inertiaDegree = f}
    let e₂ : s₂ ≃
        {L : IntermediateField K (SeparableClosure K) //
          Module.finrank K L = f * e ∧ L.inertiaDegree = f} :=
      Equiv.subtypeSubtypeEquivSubtypeInter
        (fun L : IntermediateField K (SeparableClosure K) ↦ Module.finrank K L = f * e)
        (fun L ↦ L.inertiaDegree = f)
    calc
      ∑' L : {L : IntermediateField K (SeparableClosure K) // Module.finrank K L = f * e}, g L.1
        = ∑' L : {L : IntermediateField K (SeparableClosure K) // Module.finrank K L = f * e},
            s₂.indicator (fun L ↦ 1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ L.1.discriminantExponent) L := by
          refine tsum_congr fun L ↦ ?_
          simp only [Set.indicator_apply, s₂, Set.mem_ofPred_eq, g]
      _ = ∑' L : s₂, 1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ L.1.1.discriminantExponent :=
          (tsum_subtype s₂ (fun L ↦ 1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ L.1.discriminantExponent)).symm
      _ = ∑' L : {L : IntermediateField K (SeparableClosure K) //
            Module.finrank K L = f * e ∧ L.inertiaDegree = f},
            1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ L.1.discriminantExponent :=
          e₂.tsum_eq (fun L ↦ 1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ L.1.discriminantExponent)
      _ = (e : ℝ≥0∞) / (Nat.card 𝓀[K] : ℝ≥0∞) ^ (f * (e - 1)) :=
          tsum_inertiaDegree_eq hf.ne' e
  rw [hlhs, htr, hrhs]
  have hfac : (f * e)! = f * e * (f * e - 1)! :=
    (Nat.mul_factorial_pred (Nat.mul_pos hf he).ne').symm
  have hfac_ne : ((f * e - 1)! : ℝ≥0∞) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  have he_ne : (e : ℝ≥0∞) ≠ 0 := by exact_mod_cast he.ne'
  rw [hfac, Nat.cast_mul,
    ENNReal.mul_inv (.inr (ENNReal.natCast_ne_top _)) (.inl (ENNReal.natCast_ne_top _)),
    mul_assoc, ← mul_assoc ((f * e - 1)! : ℝ≥0∞)⁻¹,
    ENNReal.inv_mul_cancel hfac_ne (ENNReal.natCast_ne_top _), one_mul, Nat.cast_mul,
    ENNReal.mul_inv (.inr (ENNReal.natCast_ne_top _)) (.inl (ENNReal.natCast_ne_top _)),
    div_eq_mul_inv, mul_assoc, ← mul_assoc (e : ℝ≥0∞)⁻¹,
    ENNReal.inv_mul_cancel he_ne (ENNReal.natCast_ne_top _), one_mul, one_div,
    ENNReal.mul_inv (.inr (by simp)) (.inl (ENNReal.natCast_ne_top _))]

end TauCeti
