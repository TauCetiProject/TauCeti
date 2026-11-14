/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Finprod
public import TauCeti.Algebra.GroupAction.OrbitRelQuotient
public import TauCeti.FieldTheory.Galois.GaloisSet.Etale
public import TauCeti.NumberTheory.LocalField.Unramified.IntermediateField
import TauCeti.Algebra.Algebra.Pi
import TauCeti.FieldTheory.Galois.FixedField
import TauCeti.FieldTheory.Normal.Embeddings

/-!
# Splitting symbols of Galois actions and labelled Galois sets

For a nonarchimedean local field `K` and a set `X` acted on by `Gal(SeparableClosure K/K)`,
`TauCeti.orbitSplittingSymbol K X` records, as a multiset over the orbits, the pair `(f, e)` of
residue degree `F.inertiaDegree` and ramification index `Module.finrank K F / F.inertiaDegree` of
the fixed field `F` of a point stabilizer ([Bhargava 2007, (2.1)]). Conjugate stabilizers have
`K`-isomorphic fixed fields, so the summands do not depend on the orbit representatives.

Two zero conventions match `TauCeti.orbitDiscriminantExponent`: an orbit whose stabilizer fixes an
infinite extension of `K` contributes `(0, 0)`, and an action with infinitely many orbits has
splitting symbol `0`. For a labelled Galois set `ρ : TauCeti.GaloisSet K n`, there are finitely
many orbits and every point stabilizer has a finite fixed field whose degree is the orbit size, so
every entry `(f, e)` of `ρ.splittingSymbol` has positive components and `∑ (f, e), f * e = n`.

## Main definitions and results

* `TauCeti.orbitSplittingSymbol`: the splitting symbol of an action of `Gal(SeparableClosure K/K)`.
* `TauCeti.orbitSplittingSymbol_eq_of_equiv`: invariance under equivariant bijections.
* `TauCeti.orbitSplittingSymbol_of_isPretransitive`, `TauCeti.orbitSplittingSymbol_quotient`,
  `TauCeti.orbitSplittingSymbol_of_isEmpty`, and `TauCeti.orbitSplittingSymbol_of_trivial`.
* `TauCeti.orbitSplittingSymbol_sum` and `TauCeti.orbitSplittingSymbol_sigma`: additivity on finite
  disjoint unions.
* `TauCeti.orbitSplittingSymbol_algHom_eq_of_algEquiv`,
  `TauCeti.orbitSplittingSymbol_intermediateField`, and
  `TauCeti.orbitSplittingSymbol_pi_algHom`: algebra-isomorphism invariance and the splitting symbols
  of the embedding actions of a subextension and of a finite product of subextensions.
* `TauCeti.GaloisSet.splittingSymbol`: the splitting symbol of a labelled Galois set, with explicit
  orbit-map formula `TauCeti.GaloisSet.splittingSymbol_eq_map_univ`, relabelling invariance
  `TauCeti.GaloisSet.splittingSymbol_smul`, and étale-algebra compatibility
  `TauCeti.GaloisSet.splittingSymbol_ofAlgebra`.
* `TauCeti.GaloisSet.mem_splittingSymbol_iff`, `TauCeti.GaloisSet.pos_of_mem_splittingSymbol`,
  `TauCeti.GaloisSet.card_splittingSymbol`, and `TauCeti.GaloisSet.sum_map_mul_splittingSymbol`.
* `TauCeti.GaloisSet.splittingSymbol_eq_singleton_iff` and
  `TauCeti.GaloisSet.splittingSymbol_eq_singleton_iff_of_mul`: a singleton symbol `{(f, e)}`
  characterizes transitive Galois sets whose stabilizer fixed field has residue degree `f`.

## References

* M. Bhargava, *Mass formulae for extensions of local fields, and conjectures on the density of
  number field discriminants*, IMRN **2007**, rnm052, §2.
* K. S. Kedlaya, *Mass formulas for local Galois representations*, IMRN **2007**, rnm021.
-/

public section

noncomputable section

namespace TauCeti

open _root_.MulAction

section OrbitSplittingSymbol

/-- Translating a point does not change the degree `[F : K]` of its stabilizer's fixed field `F`,
since the two fixed fields are conjugate. -/
@[simp]
theorem finrank_fixedField_stabilizer_smul (K : Type*) [Field K] {X : Type*}
    [MulAction Gal(SeparableClosure K/K) X] (σ : Gal(SeparableClosure K/K)) (x : X) :
    Module.finrank K
        (IntermediateField.fixedField (stabilizer Gal(SeparableClosure K/K) (σ • x))) =
      Module.finrank K
        (IntermediateField.fixedField (stabilizer Gal(SeparableClosure K/K) x)) := by
  rw [stabilizer_smul_eq_stabilizer_map_conj, MulEquiv.toMonoidHom_eq_coe,
    Subgroup.fixedField_map_conj]
  exact ((IntermediateField.fixedField (stabilizer Gal(SeparableClosure K/K) x)).equivMap
    σ.toAlgHom).symm.toLinearEquiv.finrank_eq

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
variable {X Y : Type*} [MulAction Gal(SeparableClosure K/K) X]
  [MulAction Gal(SeparableClosure K/K) Y]

/-- Translating a point does not change the residue degree of its stabilizer's fixed field, since
the two fixed fields are conjugate. -/
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

/-- Translating a point does not change the ramification-index quotient `[F : K] / f(F/K)` of its
stabilizer's fixed field `F`. -/
theorem finrank_div_inertiaDegree_fixedField_stabilizer_smul
    (σ : Gal(SeparableClosure K/K)) (x : X) :
    Module.finrank K
        (IntermediateField.fixedField (stabilizer Gal(SeparableClosure K/K) (σ • x))) /
      (IntermediateField.fixedField
        (stabilizer Gal(SeparableClosure K/K) (σ • x))).inertiaDegree =
      Module.finrank K
          (IntermediateField.fixedField (stabilizer Gal(SeparableClosure K/K) x)) /
        (IntermediateField.fixedField
          (stabilizer Gal(SeparableClosure K/K) x)).inertiaDegree := by
  rw [finrank_fixedField_stabilizer_smul K σ x, inertiaDegree_fixedField_stabilizer_smul K σ x]

/-- The pair `(f, e)` of an orbit can be computed at any point in that orbit. -/
theorem splittingSymbolPair_fixedField_stabilizer_out
    {ω : orbitRel.Quotient Gal(SeparableClosure K/K) X} {x : X}
    (hx : (Quotient.mk'' x : orbitRel.Quotient Gal(SeparableClosure K/K) X) = ω) :
    ((IntermediateField.fixedField (stabilizer Gal(SeparableClosure K/K) ω.out)).inertiaDegree,
      Module.finrank K
          (IntermediateField.fixedField (stabilizer Gal(SeparableClosure K/K) ω.out)) /
        (IntermediateField.fixedField
          (stabilizer Gal(SeparableClosure K/K) ω.out)).inertiaDegree) =
      ((IntermediateField.fixedField (stabilizer Gal(SeparableClosure K/K) x)).inertiaDegree,
        Module.finrank K
            (IntermediateField.fixedField (stabilizer Gal(SeparableClosure K/K) x)) /
          (IntermediateField.fixedField
            (stabilizer Gal(SeparableClosure K/K) x)).inertiaDegree) := by
  obtain ⟨σ, rfl⟩ := MulAction.exists_smul_out_eq hx
  exact Prod.ext (inertiaDegree_fixedField_stabilizer_smul K σ ω.out).symm
    (finrank_div_inertiaDegree_fixedField_stabilizer_smul K σ ω.out).symm

private theorem splittingSymbolPair_fixedField_stabilizer_out_of_injective
    (f : X → Y) (hf : Function.Injective f)
    (he : ∀ (σ : Gal(SeparableClosure K/K)) (x : X), f (σ • x) = σ • f x)
    {ω : orbitRel.Quotient Gal(SeparableClosure K/K) Y} {x : X}
    (hx : (Quotient.mk'' (f x) : orbitRel.Quotient Gal(SeparableClosure K/K) Y) = ω) :
    ((IntermediateField.fixedField (stabilizer Gal(SeparableClosure K/K) ω.out)).inertiaDegree,
      Module.finrank K
          (IntermediateField.fixedField (stabilizer Gal(SeparableClosure K/K) ω.out)) /
        (IntermediateField.fixedField
          (stabilizer Gal(SeparableClosure K/K) ω.out)).inertiaDegree) =
      ((IntermediateField.fixedField (stabilizer Gal(SeparableClosure K/K) x)).inertiaDegree,
        Module.finrank K
            (IntermediateField.fixedField (stabilizer Gal(SeparableClosure K/K) x)) /
          (IntermediateField.fixedField
            (stabilizer Gal(SeparableClosure K/K) x)).inertiaDegree) := by
  rw [splittingSymbolPair_fixedField_stabilizer_out K hx,
    MulAction.stabilizer_eq_of_injective f hf he]

/-- The **splitting symbol** of an action of `Gal(SeparableClosure K/K)` ([Bhargava 2007, (2.1)]):
the multiset, over the orbits, of the pair `(f, e)` of residue degree and ramification index of the
fixed field of a point stabilizer. An orbit with an infinite fixed field contributes `(0, 0)`, and
an action with infinitely many orbits has value `0`. -/
def orbitSplittingSymbol (X : Type*) [MulAction Gal(SeparableClosure K/K) X] :
    Multiset (ℕ × ℕ) :=
  ∑ᶠ ω : orbitRel.Quotient Gal(SeparableClosure K/K) X,
    {((IntermediateField.fixedField (stabilizer Gal(SeparableClosure K/K) ω.out)).inertiaDegree,
      Module.finrank K
          (IntermediateField.fixedField (stabilizer Gal(SeparableClosure K/K) ω.out)) /
        (IntermediateField.fixedField
          (stabilizer Gal(SeparableClosure K/K) ω.out)).inertiaDegree)}

/-- The defining finite-support sum for `orbitSplittingSymbol`. -/
theorem orbitSplittingSymbol_def :
    orbitSplittingSymbol K X =
      ∑ᶠ ω : orbitRel.Quotient Gal(SeparableClosure K/K) X,
        {((IntermediateField.fixedField (stabilizer Gal(SeparableClosure K/K) ω.out)).inertiaDegree,
          Module.finrank K
              (IntermediateField.fixedField (stabilizer Gal(SeparableClosure K/K) ω.out)) /
            (IntermediateField.fixedField
              (stabilizer Gal(SeparableClosure K/K) ω.out)).inertiaDegree)} :=
  (rfl)

/-- Any choice of one point per orbit gives the same splitting symbol. -/
theorem orbitSplittingSymbol_eq_finsum
    (s : orbitRel.Quotient Gal(SeparableClosure K/K) X → X)
    (hs : ∀ ω, (Quotient.mk'' (s ω) : orbitRel.Quotient Gal(SeparableClosure K/K) X) = ω) :
    orbitSplittingSymbol K X =
      ∑ᶠ ω,
        {((IntermediateField.fixedField (stabilizer Gal(SeparableClosure K/K) (s ω))).inertiaDegree,
          Module.finrank K
              (IntermediateField.fixedField (stabilizer Gal(SeparableClosure K/K) (s ω))) /
            (IntermediateField.fixedField
              (stabilizer Gal(SeparableClosure K/K) (s ω))).inertiaDegree)} :=
  finsum_congr fun ω ↦ congrArg ({·}) (splittingSymbolPair_fixedField_stabilizer_out K (hs ω))

/-- On a finite orbit space, `orbitSplittingSymbol` is the finite sum of singleton pairs over the
orbits. -/
theorem orbitSplittingSymbol_eq_sum [Fintype (orbitRel.Quotient Gal(SeparableClosure K/K) X)] :
    orbitSplittingSymbol K X =
      ∑ ω : orbitRel.Quotient Gal(SeparableClosure K/K) X,
        {((IntermediateField.fixedField (stabilizer Gal(SeparableClosure K/K) ω.out)).inertiaDegree,
          Module.finrank K
              (IntermediateField.fixedField (stabilizer Gal(SeparableClosure K/K) ω.out)) /
            (IntermediateField.fixedField
              (stabilizer Gal(SeparableClosure K/K) ω.out)).inertiaDegree)} :=
  finsum_eq_sum_of_fintype _

/-- On a finite orbit space, `orbitSplittingSymbol` is `Finset.univ.val.map` of the orbit pair. -/
theorem orbitSplittingSymbol_eq_map_univ
    [Fintype (orbitRel.Quotient Gal(SeparableClosure K/K) X)] :
    orbitSplittingSymbol K X =
      (Finset.univ : Finset (orbitRel.Quotient Gal(SeparableClosure K/K) X)).val.map fun ω ↦
        ((IntermediateField.fixedField (stabilizer Gal(SeparableClosure K/K) ω.out)).inertiaDegree,
          Module.finrank K
              (IntermediateField.fixedField (stabilizer Gal(SeparableClosure K/K) ω.out)) /
            (IntermediateField.fixedField
              (stabilizer Gal(SeparableClosure K/K) ω.out)).inertiaDegree) := by
  rw [orbitSplittingSymbol_eq_sum, Finset.sum_eq_multiset_sum]
  exact (congrArg Multiset.sum (Multiset.map_map ({·}) _ Finset.univ.val).symm).trans
    (Multiset.sum_map_singleton _)

/-- An equivariant bijection preserves the splitting symbol. -/
theorem orbitSplittingSymbol_eq_of_equiv (e : X ≃ Y)
    (he : ∀ (σ : Gal(SeparableClosure K/K)) (x : X), e (σ • x) = σ • e x) :
    orbitSplittingSymbol K X = orbitSplittingSymbol K Y := by
  let E := MulAction.orbitRelQuotientCongr (MulEquiv.refl Gal(SeparableClosure K/K)) e he
  rw [orbitSplittingSymbol_def, orbitSplittingSymbol_def, ← finsum_comp_equiv E]
  refine finsum_congr fun ω ↦ congrArg ({·}) ?_
  have hE : (Quotient.mk'' (e ω.out) : orbitRel.Quotient Gal(SeparableClosure K/K) Y) = E ω := by
    rw [← MulAction.orbitRelQuotientCongr_mk (MulEquiv.refl _) e he, Quotient.out_eq']
  exact (splittingSymbolPair_fixedField_stabilizer_out_of_injective K e e.injective he hE).symm

/-- A transitive action has singleton splitting symbol given by the fixed field of any point
stabilizer. The point supplies nonemptiness. -/
theorem orbitSplittingSymbol_of_isPretransitive
    [MulAction.IsPretransitive Gal(SeparableClosure K/K) X] (x : X) :
    orbitSplittingSymbol K X =
      {((IntermediateField.fixedField (stabilizer Gal(SeparableClosure K/K) x)).inertiaDegree,
        Module.finrank K
            (IntermediateField.fixedField (stabilizer Gal(SeparableClosure K/K) x)) /
          (IntermediateField.fixedField
            (stabilizer Gal(SeparableClosure K/K) x)).inertiaDegree)} := by
  have : Nonempty X := ⟨x⟩
  let := ((MulAction.pretransitive_iff_unique_quotient_of_nonempty
    Gal(SeparableClosure K/K) X).mp inferInstance).some
  rw [orbitSplittingSymbol_def, finsum_eq_single _ (Quotient.mk'' x)
    (fun ω hω ↦ (hω (Subsingleton.elim _ _)).elim)]
  exact congrArg ({·}) (splittingSymbolPair_fixedField_stabilizer_out K rfl)

/-- The coset action on `Gal(SeparableClosure K/K) ⧸ H` has singleton splitting symbol given by the
fixed field of `H`. -/
@[simp]
theorem orbitSplittingSymbol_quotient (H : Subgroup Gal(SeparableClosure K/K)) :
    orbitSplittingSymbol K (Gal(SeparableClosure K/K) ⧸ H) =
      {((IntermediateField.fixedField H).inertiaDegree,
        Module.finrank K (IntermediateField.fixedField H) /
          (IntermediateField.fixedField H).inertiaDegree)} := by
  rw [orbitSplittingSymbol_of_isPretransitive K
    ((1 : Gal(SeparableClosure K/K)) : Gal(SeparableClosure K/K) ⧸ H), stabilizer_quotient]

/-- An action on an empty carrier has empty splitting symbol. -/
@[simp]
theorem orbitSplittingSymbol_of_isEmpty [IsEmpty X] :
    orbitSplittingSymbol K X = 0 :=
  finsum_eq_zero_of_forall_eq_zero fun ω ↦ isEmptyElim ω.out

/-- A trivial action on `X` has splitting symbol `Nat.card X • {(1, 1)}`, including on infinite
carriers where both sides vanish. -/
theorem orbitSplittingSymbol_of_trivial
    (htriv : ∀ (σ : Gal(SeparableClosure K/K)) (x : X), σ • x = x) :
    orbitSplittingSymbol K X = Multiset.replicate (Nat.card X) (1, 1) := by
  have hstab (x : X) : stabilizer Gal(SeparableClosure K/K) x = ⊤ := by
    ext σ
    simp [mem_stabilizer_iff, htriv]
  let E : X ≃ orbitRel.Quotient Gal(SeparableClosure K/K) X :=
    Equiv.ofBijective Quotient.mk'' ⟨fun x y h ↦ by
      obtain ⟨σ, hσ⟩ := MulAction.mem_orbit_iff.mp (Quotient.exact' h)
      exact hσ.symm.trans (htriv σ y), Quotient.mk''_surjective⟩
  rw [orbitSplittingSymbol_def, ← finsum_comp_equiv E]
  have hconst : (fun x : X ↦
      {((IntermediateField.fixedField
          (stabilizer Gal(SeparableClosure K/K) (E x).out)).inertiaDegree,
        Module.finrank K
            (IntermediateField.fixedField (stabilizer Gal(SeparableClosure K/K) (E x).out)) /
          (IntermediateField.fixedField
            (stabilizer Gal(SeparableClosure K/K) (E x).out)).inertiaDegree)}) =
      fun _ ↦ ({(1, 1)} : Multiset (ℕ × ℕ)) := by
    funext x
    rw [hstab, InfiniteGalois.fixedField_bot, IntermediateField.inertiaDegree_bot,
      IntermediateField.finrank_bot, Nat.div_one]
  rw [hconst]
  by_cases hX : Finite X
  · let := Fintype.ofFinite X
    rw [finsum_eq_sum_of_fintype, Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card,
      Multiset.nsmul_singleton]
  · have := not_finite_iff_infinite.mp hX
    have hsupp : Function.support (fun _ : X ↦ ({(1, 1)} : Multiset (ℕ × ℕ))) = Set.univ :=
      Set.eq_univ_of_forall fun _ ↦ Multiset.singleton_ne_zero _
    rw [finsum_of_infinite_support, Nat.card_eq_zero_of_infinite, Multiset.replicate_zero]
    rw [hsupp]
    exact Set.infinite_univ

/-- Splitting symbols are additive on disjoint unions with finitely many orbits. -/
@[simp]
theorem orbitSplittingSymbol_sum
    [Finite (orbitRel.Quotient Gal(SeparableClosure K/K) X)]
    [Finite (orbitRel.Quotient Gal(SeparableClosure K/K) Y)] :
    orbitSplittingSymbol K (X ⊕ Y) =
      orbitSplittingSymbol K X + orbitSplittingSymbol K Y := by
  classical
  let := Fintype.ofFinite (orbitRel.Quotient Gal(SeparableClosure K/K) X)
  let := Fintype.ofFinite (orbitRel.Quotient Gal(SeparableClosure K/K) Y)
  let E := MulAction.orbitRelQuotientSumEquiv
    (G := Gal(SeparableClosure K/K)) (X := X) (Y := Y)
  rw [orbitSplittingSymbol_def, ← finsum_comp_equiv E.symm, finsum_eq_sum_of_fintype,
    Fintype.sum_sum_type]
  congr 1
  · rw [orbitSplittingSymbol_eq_sum]
    refine Finset.sum_congr rfl fun ω _ ↦ congrArg ({·})
      (splittingSymbolPair_fixedField_stabilizer_out_of_injective K
        Sum.inl Sum.inl_injective (fun _ _ ↦ rfl) ?_)
    apply E.injective
    simp [E]
  · rw [orbitSplittingSymbol_eq_sum]
    refine Finset.sum_congr rfl fun ω _ ↦ congrArg ({·})
      (splittingSymbolPair_fixedField_stabilizer_out_of_injective K
        Sum.inr Sum.inr_injective (fun _ _ ↦ rfl) ?_)
    apply E.injective
    simp [E]

/-- Splitting symbols are additive over a finite family of actions with finitely many orbits. -/
@[simp]
theorem orbitSplittingSymbol_sigma {ι : Type*} [Fintype ι] {Y : ι → Type*}
    [∀ i, MulAction Gal(SeparableClosure K/K) (Y i)]
    [∀ i, Finite (orbitRel.Quotient Gal(SeparableClosure K/K) (Y i))] :
    orbitSplittingSymbol K (Σ i, Y i) = ∑ i, orbitSplittingSymbol K (Y i) := by
  classical
  let (i : ι) := Fintype.ofFinite (orbitRel.Quotient Gal(SeparableClosure K/K) (Y i))
  let E := MulAction.orbitRelQuotientSigmaEquiv
    (G := Gal(SeparableClosure K/K)) (Y := Y)
  rw [orbitSplittingSymbol_def, ← finsum_comp_equiv E.symm, finsum_eq_sum_of_fintype,
    Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [orbitSplittingSymbol_eq_sum]
  refine Finset.sum_congr rfl fun ω _ ↦ congrArg ({·}) ?_
  rw [splittingSymbolPair_fixedField_stabilizer_out K
    (x := Sigma.mk i ω.out) (by simp [E, ← MulAction.orbitRelQuotientSigmaEquiv_symm_mk]),
    MulAction.stabilizer_sigma_mk]

/-- Isomorphic `K`-algebras have the same embedding-action splitting symbol. -/
theorem orbitSplittingSymbol_algHom_eq_of_algEquiv {A B : Type*}
    [Semiring A] [Algebra K A] [Semiring B] [Algebra K B] (e : A ≃ₐ[K] B) :
    orbitSplittingSymbol K (A →ₐ[K] SeparableClosure K) =
      orbitSplittingSymbol K (B →ₐ[K] SeparableClosure K) :=
  orbitSplittingSymbol_eq_of_equiv K
    (e.arrowCongr (AlgEquiv.refl : SeparableClosure K ≃ₐ[K] SeparableClosure K))
    fun _ _ ↦ AlgHom.ext fun _ ↦ rfl

/-- On a subextension `L` of `SeparableClosure K`, the embedding action has singleton splitting
symbol `{(f(L/K), [L : K] / f(L/K))}`, including on infinite subextensions where the pair is
`(0, 0)`. -/
@[simp]
theorem orbitSplittingSymbol_intermediateField
    (L : IntermediateField K (SeparableClosure K)) :
    orbitSplittingSymbol K (L →ₐ[K] SeparableClosure K) =
      {(L.inertiaDegree, Module.finrank K L / L.inertiaDegree)} := by
  rw [orbitSplittingSymbol_of_isPretransitive K L.val,
    FieldTheory.stabilizer_algHom_eq_fixingSubgroup, IntermediateField.fieldRange_val,
    InfiniteGalois.fixedField_fixingSubgroup]

/-- For a finite product of subextensions, the embedding action has splitting symbol equal to the
sum of the singleton pairs of the factors. -/
@[simp]
theorem orbitSplittingSymbol_pi_algHom {ι : Type*} [Fintype ι]
    (L : ι → IntermediateField K (SeparableClosure K)) :
    orbitSplittingSymbol K ((Π i, L i) →ₐ[K] SeparableClosure K) =
      ∑ i, {((L i).inertiaDegree, Module.finrank K (L i) / (L i).inertiaDegree)} := by
  have (i : ι) : Finite (orbitRel.Quotient
      Gal(SeparableClosure K/K) (L i →ₐ[K] SeparableClosure K)) := by
    have := (MulAction.pretransitive_iff_subsingleton_quotient
      Gal(SeparableClosure K/K) (L i →ₐ[K] SeparableClosure K)).mp inferInstance
    exact Finite.of_subsingleton
  rw [← orbitSplittingSymbol_eq_of_equiv K
    (AlgHom.sigmaEquivPi (fun i ↦ L i) (SeparableClosure K)) (by
      intro σ φ
      rcases φ with ⟨i, φ⟩
      ext a
      simp), orbitSplittingSymbol_sigma]
  exact Finset.sum_congr rfl fun i _ ↦ orbitSplittingSymbol_intermediateField K (L i)

end OrbitSplittingSymbol

namespace GaloisSet

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] {n : ℕ}

/-- The **splitting symbol** of a labelled Galois set ([Bhargava 2007, (2.1)]): the multiset, over
its orbits, of the pair `(f, e)` of residue degree and ramification index of the fixed field of the
stabilizer of a point of the orbit. -/
def splittingSymbol (ρ : GaloisSet K n) : Multiset (ℕ × ℕ) :=
  letI := ρ.mulAction
  orbitSplittingSymbol K (Fin n)

/-- The splitting symbol of a labelled Galois set is `orbitSplittingSymbol` for its action. -/
theorem splittingSymbol_def (ρ : GaloisSet K n) :
    ρ.splittingSymbol = (letI := ρ.mulAction; orbitSplittingSymbol K (Fin n)) :=
  (rfl)

open Classical in
/-- As a multiset over the finite orbit quotient of `Fin n`, `ρ.splittingSymbol` maps each orbit to
the `(f, e)` pair of the fixed field of its chosen representative's stabilizer. -/
theorem splittingSymbol_eq_map_univ (ρ : GaloisSet K n) :
    ρ.splittingSymbol =
      (letI := ρ.mulAction
      haveI := Fintype.ofFinite (orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n))
      (Finset.univ : Finset (orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n))).val.map fun ω ↦
        ((IntermediateField.fixedField (stabilizer Gal(SeparableClosure K/K) ω.out)).inertiaDegree,
          Module.finrank K
              (IntermediateField.fixedField (stabilizer Gal(SeparableClosure K/K) ω.out)) /
            (IntermediateField.fixedField
              (stabilizer Gal(SeparableClosure K/K) ω.out)).inertiaDegree)) := by
  classical
  let := ρ.mulAction
  let := Fintype.ofFinite (orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n))
  rw [splittingSymbol_def, orbitSplittingSymbol_eq_map_univ]

/-- Equivariant bijections preserve the splitting symbol of labelled Galois sets. -/
theorem splittingSymbol_eq_of_equiv {m : ℕ} (ρ : GaloisSet K n) (τ : GaloisSet K m)
    (e : Fin n ≃ Fin m)
    (he : ∀ (σ : Gal(SeparableClosure K/K)) (i : Fin n), e (ρ.val σ i) = τ.val σ (e i)) :
    ρ.splittingSymbol = τ.splittingSymbol := by
  let := ρ.mulAction
  let := τ.mulAction
  exact orbitSplittingSymbol_eq_of_equiv K e he

/-- Relabelling a Galois set does not change its splitting symbol. -/
@[simp]
theorem splittingSymbol_smul (ρ : GaloisSet K n) (e : Equiv.Perm (Fin n)) :
    (e • ρ).splittingSymbol = ρ.splittingSymbol :=
  (ρ.splittingSymbol_eq_of_equiv (e • ρ) e (by simp)).symm

/-- The labelled Galois set of an étale algebra has the splitting symbol of the algebra's embedding
action. -/
@[simp]
theorem splittingSymbol_ofAlgebra (A : Type*) [CommRing A] [Algebra K A] [Algebra.Etale K A]
    (ℓ : Fin n ≃ (A →ₐ[K] SeparableClosure K)) :
    (ofAlgebra A ℓ).splittingSymbol = orbitSplittingSymbol K (A →ₐ[K] SeparableClosure K) := by
  let := (ofAlgebra A ℓ).mulAction
  exact orbitSplittingSymbol_eq_of_equiv K ℓ fun σ i ↦ by simp

/-- A transitive labelled Galois set has singleton splitting symbol `{(f, n / f)}`, where `f` is
the residue degree of the fixed field of the stabilizer of any of its labels. -/
theorem splittingSymbol_of_isTransitive (ρ : GaloisSet K n) (hρ : ρ.IsTransitive) (i : Fin n) :
    ρ.splittingSymbol =
      (letI := ρ.mulAction
      {((IntermediateField.fixedField (stabilizer Gal(SeparableClosure K/K) i)).inertiaDegree,
        n / (IntermediateField.fixedField
          (stabilizer Gal(SeparableClosure K/K) i)).inertiaDegree)}) := by
  let := ρ.mulAction
  have : MulAction.IsPretransitive Gal(SeparableClosure K/K) (Fin n) := ρ.isTransitive_def.1 hρ
  rw [splittingSymbol_def, orbitSplittingSymbol_of_isPretransitive K i,
    ρ.finrank_fixedField_stabilizer_of_isTransitive hρ i]

/-- The trivial labelled Galois set of size `n` has splitting symbol `n • {(1, 1)}`. -/
@[simp]
theorem splittingSymbol_trivial :
    (trivial K n).splittingSymbol = Multiset.replicate n (1, 1) := by
  let := (trivial K n).mulAction
  rw [splittingSymbol_def, orbitSplittingSymbol_of_trivial K fun σ i ↦ trivial_val_apply σ i,
    Nat.card_fin]

/-- A Galois set on an empty carrier has empty splitting symbol. -/
@[simp]
theorem splittingSymbol_of_isEmpty [IsEmpty (Fin n)] (ρ : GaloisSet K n) :
    ρ.splittingSymbol = 0 := by
  let := ρ.mulAction
  exact orbitSplittingSymbol_of_isEmpty K

/-- The number of parts of `ρ.splittingSymbol` is the number of orbits of `ρ`. -/
@[simp]
theorem card_splittingSymbol (ρ : GaloisSet K n) :
    Multiset.card ρ.splittingSymbol =
      (letI := ρ.mulAction
      Nat.card (orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n))) := by
  classical
  let := ρ.mulAction
  let := Fintype.ofFinite (orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n))
  rw [splittingSymbol_def, orbitSplittingSymbol_eq_map_univ, Multiset.card_map,
    Finset.card_val, Finset.card_univ, Nat.card_eq_fintype_card]

/-- The splitting symbol of a Galois set of size `n` vanishes if and only if `n = 0`. -/
@[simp]
theorem splittingSymbol_eq_zero_iff (ρ : GaloisSet K n) :
    ρ.splittingSymbol = 0 ↔ n = 0 := by
  rcases n with _ | n
  · simp
  · refine iff_of_false (fun h ↦ ?_) (Nat.succ_ne_zero n)
    let := ρ.mulAction
    have : Nonempty (orbitRel.Quotient Gal(SeparableClosure K/K) (Fin (n + 1))) :=
      ⟨Quotient.mk'' 0⟩
    have hcard := ρ.card_splittingSymbol
    rw [h, Multiset.card_zero] at hcard
    exact (Nat.card_pos (α := orbitRel.Quotient Gal(SeparableClosure K/K) (Fin (n + 1)))).ne'
      hcard.symm

/-- A pair `x` belongs to `ρ.splittingSymbol` if and only if it is the `(f, e)` pair of the fixed
field of the stabilizer of some label `i : Fin n`. -/
theorem mem_splittingSymbol_iff (ρ : GaloisSet K n) {x : ℕ × ℕ} :
    x ∈ ρ.splittingSymbol ↔
      ∃ i : Fin n,
        (letI := ρ.mulAction
        ((IntermediateField.fixedField (stabilizer Gal(SeparableClosure K/K) i)).inertiaDegree,
          Module.finrank K
              (IntermediateField.fixedField (stabilizer Gal(SeparableClosure K/K) i)) /
            (IntermediateField.fixedField
              (stabilizer Gal(SeparableClosure K/K) i)).inertiaDegree)) = x := by
  classical
  let := ρ.mulAction
  let := Fintype.ofFinite (orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n))
  rw [splittingSymbol_def, orbitSplittingSymbol_eq_map_univ, Multiset.mem_map]
  constructor
  · rintro ⟨ω, -, rfl⟩
    exact ⟨ω.out, rfl⟩
  · rintro ⟨i, rfl⟩
    exact ⟨Quotient.mk'' i, Finset.mem_univ _,
      splittingSymbolPair_fixedField_stabilizer_out K rfl⟩

/-- Every pair `(f, e)` in the splitting symbol of a Galois set has positive residue degree `f` and
positive ramification index `e`. -/
theorem pos_of_mem_splittingSymbol (ρ : GaloisSet K n) {x : ℕ × ℕ} (hx : x ∈ ρ.splittingSymbol) :
    0 < x.1 ∧ 0 < x.2 := by
  let := ρ.mulAction
  obtain ⟨i, rfl⟩ := ρ.mem_splittingSymbol_iff.1 hx
  have := ρ.finiteDimensional_fixedField_stabilizer i
  exact ⟨IntermediateField.inertiaDegree_pos _, IntermediateField.finrank_div_inertiaDegree_pos _⟩

/-- **Degree of a Galois set's splitting symbol**: the products `f * e` over the entries `(f, e)`
of `ρ.splittingSymbol` add up to `n`. -/
@[simp]
theorem sum_map_mul_splittingSymbol (ρ : GaloisSet K n) :
    (ρ.splittingSymbol.map fun x ↦ x.1 * x.2).sum = n := by
  classical
  let := ρ.mulAction
  let := Fintype.ofFinite (orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n))
  rw [splittingSymbol_def, orbitSplittingSymbol_eq_map_univ, Multiset.map_map, Finset.sum_map_val,
    Function.comp_def]
  have hsum :
      (∑ ω : orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n),
        (IntermediateField.fixedField (stabilizer Gal(SeparableClosure K/K) ω.out)).inertiaDegree *
          (Module.finrank K
              (IntermediateField.fixedField (stabilizer Gal(SeparableClosure K/K) ω.out)) /
            (IntermediateField.fixedField
              (stabilizer Gal(SeparableClosure K/K) ω.out)).inertiaDegree)) =
        ∑ ω : orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n),
          Nat.card (orbit Gal(SeparableClosure K/K) ω.out) := by
    refine Finset.sum_congr rfl fun ω _ ↦ ?_
    rw [Nat.mul_div_cancel' (IntermediateField.inertiaDegree_dvd_finrank _),
      ρ.finrank_fixedField_stabilizer ω.out]
  rw [hsum, ← Nat.card_sigma,
    ← Nat.card_congr (MulAction.selfEquivSigmaOrbits Gal(SeparableClosure K/K) (Fin n)),
    Nat.card_fin]

/-- A Galois set whose splitting symbol is a singleton is transitive: it has a single orbit. -/
theorem isTransitive_of_splittingSymbol_eq_singleton (ρ : GaloisSet K n) {x : ℕ × ℕ}
    (h : ρ.splittingSymbol = {x}) : ρ.IsTransitive := by
  let := ρ.mulAction
  have hcard : Nat.card (orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n)) = 1 := by
    rw [← ρ.card_splittingSymbol, h, Multiset.card_singleton]
  have : Subsingleton (orbitRel.Quotient Gal(SeparableClosure K/K) (Fin n)) :=
    Finite.card_le_one_iff_subsingleton.1 hcard.le
  exact ρ.isTransitive_def.2
    ((MulAction.pretransitive_iff_subsingleton_quotient Gal(SeparableClosure K/K) (Fin n)).2
      inferInstance)

/-- At any label `i : Fin n`, the splitting symbol of `ρ` is the singleton `{x}` if and only if `ρ`
is transitive and the fixed field `F` of the stabilizer of `i` has residue degree `x.1` and
`n / f(F/K) = x.2`. -/
theorem splittingSymbol_eq_singleton_iff (ρ : GaloisSet K n) (i : Fin n) (x : ℕ × ℕ) :
    ρ.splittingSymbol = {x} ↔
      ρ.IsTransitive ∧
        (letI := ρ.mulAction
        (IntermediateField.fixedField (stabilizer Gal(SeparableClosure K/K) i)).inertiaDegree =
            x.1 ∧
          n / (IntermediateField.fixedField
            (stabilizer Gal(SeparableClosure K/K) i)).inertiaDegree = x.2) := by
  rcases x with ⟨f, e⟩
  constructor
  · intro h
    have htr := ρ.isTransitive_of_splittingSymbol_eq_singleton h
    rw [ρ.splittingSymbol_of_isTransitive htr i, Multiset.singleton_inj, Prod.ext_iff] at h
    exact ⟨htr, h⟩
  · rintro ⟨htr, rfl, rfl⟩
    exact ρ.splittingSymbol_of_isTransitive htr i

/-- For `f ≠ 0` and a label `i : Fin (f * e)`, a Galois set of size `f * e` has splitting symbol
`{(f, e)}` if and only if it is transitive and the fixed field of the stabilizer of `i` has residue
degree `f`. -/
theorem splittingSymbol_eq_singleton_iff_of_mul {f e : ℕ} (hf : f ≠ 0)
    (ρ : GaloisSet K (f * e)) (i : Fin (f * e)) :
    ρ.splittingSymbol = {(f, e)} ↔
      ρ.IsTransitive ∧
        (letI := ρ.mulAction
        (IntermediateField.fixedField (stabilizer Gal(SeparableClosure K/K) i)).inertiaDegree =
          f) := by
  rw [ρ.splittingSymbol_eq_singleton_iff i (f, e)]
  refine and_congr_right fun _ ↦ ⟨And.left, fun h ↦ ⟨h, ?_⟩⟩
  rw [h, Nat.mul_div_right _ (Nat.pos_of_ne_zero hf)]

end GaloisSet

end TauCeti
