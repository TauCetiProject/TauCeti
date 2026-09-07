/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.RepresentationTheory.Homological.TateCohomology.LowDegree
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.RepresentationTheory.Homological.FiniteCyclic

/-!
# Herbrand quotients of finite cyclic group representations

For a representation `M` of a finite cyclic group, its Herbrand quotient is the quotient of the
orders of `H-hat^0(G, M)` and `H-hat^(-1)(G, M)`. This file defines it directly on Mathlib's
Tate-cohomology carrier, on top of the low-degree descriptions

`H-hat^0(G, M) = M^G / N M` and `H-hat^(-1)(G, M) = ker(N) / I_G M`,

and proves its two base calculations: the quotient is `1` for a finite module, and it is `|G|`
for the trivial integral representation. It also proves that the Herbrand quotient is
multiplicative in a short exact sequence whenever the three quotients are defined, by folding the
Tate long exact sequence into an exact six-term cycle using cyclic two-periodicity.

The proofs are adapted to Mathlib's current Tate complex from the corresponding calculations in
`ClassFieldTheory/Cohomology/FiniteCyclic/HerbrandQuotient/{Defs,Finite,Trivial,SES}.lean` in
`kbuzzard/ClassFieldTheory`, commit `ccc3323c6750abca25b49b35106f54eb3a398509`.
The multiplicativity proof packages the norm and augmentation maps into a two-periodic complex,
so its homology sequence is circular without requiring a separate naturality theorem for
periodicity. The trivial integral calculation reads off the low-degree evaluations
`natCard_tateCohomology_zero_trivial_int_eq_card` and
`subsingleton_tateCohomology_negOne_trivial_int`.

## Main definitions

* `TauCeti.TateCohomology.herbrandQuotient` is the Herbrand quotient.
* `TauCeti.TateCohomology.herbrandQuotient_eq_one_of_finite` computes it for a finite module.
* `TauCeti.TateCohomology.herbrandQuotient_trivial_int_eq_card` computes it for trivial integral
  coefficients.
* `TauCeti.TateCohomology.herbrandQuotient_eq_mul_of_shortExact` proves multiplicativity in a
  short exact sequence.

## References

* J.-P. Serre, *Local Fields*, Chapter VIII, section 4.
* E. Artin and J. Tate, *Class Field Theory*, Chapter IX, section 4.
-/

public noncomputable section

universe u

open CategoryTheory groupCohomology groupHomology LinearMap Rep

namespace TauCeti.TateCohomology

variable {R G : Type u} [CommRing R] [Group G] [Fintype G]

/-- The Herbrand quotient, the order of degree-zero Tate cohomology divided by the order of
degree `-1` Tate cohomology. Classically the invariant is only defined when both Tate groups are
finite; this definition is totalized by `Nat.card`, which is `0` on an infinite type, so together
with division by zero it returns `0` as soon as either group is infinite. The definition makes
sense for any finite group; periodicity makes it useful for cyclic groups. -/
def herbrandQuotient (M : Rep R G) : ℚ :=
  Nat.card (tateCohomology M 0) / Nat.card (tateCohomology M (-1))

/-- The Herbrand quotient is the ratio of the orders of degree zero and degree `-1` Tate
cohomology. This unfolding equation is deliberately not `@[simp]`: the terminating evaluations
below keep `herbrandQuotient` as their left-hand side, and unfolding it first would make each of
them non-simp-normal. -/
theorem herbrandQuotient_def (M : Rep R G) :
    herbrandQuotient M =
      Nat.card (tateCohomology M 0) / Nat.card (tateCohomology M (-1)) := by
  simp [herbrandQuotient]

/-- The Herbrand quotient vanishes exactly when one of its two defining Tate groups is infinite. -/
@[simp]
theorem herbrandQuotient_eq_zero_iff {M : Rep R G} :
    herbrandQuotient M = 0 ↔
      Infinite (tateCohomology M 0) ∨ Infinite (tateCohomology M (-1)) := by
  simp [herbrandQuotient_def, Nat.card_eq_zero]

/-- The Herbrand quotient of a finite representation of a finite cyclic group is one. -/
@[simp]
theorem herbrandQuotient_eq_one_of_finite [IsCyclic G] (M : Rep R G) [Finite M] :
    herbrandQuotient M = 1 := by
  let hgen := isCyclic_iff_exists_zpowers_eq_top.mp (inferInstance : IsCyclic G)
  let g := hgen.choose
  have hg : ∀ x : G, x ∈ Subgroup.zpowers g := fun x ↦
    hgen.choose_spec.ge (Subgroup.mem_top x)
  let D : Module.End R M := M.ρ g - LinearMap.id
  have hinv : M.ρ.invariants = ker D := by
    ext x
    simpa only [D, mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero] using
      (Representation.mem_invariants_iff_of_forall_mem_zpowers M.ρ g hg x)
  have hcoinv : Representation.Coinvariants.ker M.ρ = range D := by
    simpa only [D] using Representation.FiniteCyclicGroup.coinvariantsKer_eq_range M.ρ g hg
  have hnorm_le : range M.ρ.norm ≤ M.ρ.invariants := by
    rintro _ ⟨x, rfl⟩
    exact fun a ↦ M.ρ.self_norm_apply a x
  have hzero :
      Nat.card M.ρ.invariants =
        Nat.card (range M.ρ.norm) * Nat.card (tateCohomology M 0) := by
    calc
      Nat.card M.ρ.invariants =
          Nat.card ((range M.ρ.norm).submoduleOf M.ρ.invariants) *
            Nat.card (M.ρ.invariants ⧸
              (range M.ρ.norm).submoduleOf M.ρ.invariants) :=
        Submodule.card_eq_card_quotient_mul_card _
      _ = Nat.card (range M.ρ.norm) * Nat.card (tateCohomology M 0) := by
        rw [Nat.card_congr (Submodule.submoduleOfEquivOfLe hnorm_le).toEquiv,
          ← Nat.card_congr (H0IsoNormQuotient M).toLinearEquiv.toEquiv]
  have hnegone :
      Nat.card (ker M.ρ.norm) =
        Nat.card (Representation.Coinvariants.ker M.ρ) *
          Nat.card (tateCohomology M (-1)) := by
    calc
      Nat.card (ker M.ρ.norm) =
          Nat.card ((Representation.Coinvariants.ker M.ρ).submoduleOf (ker M.ρ.norm)) *
            Nat.card (ker M.ρ.norm ⧸
              (Representation.Coinvariants.ker M.ρ).submoduleOf (ker M.ρ.norm)) :=
        Submodule.card_eq_card_quotient_mul_card _
      _ = Nat.card (Representation.Coinvariants.ker M.ρ) *
          Nat.card (tateCohomology M (-1)) := by
        rw [Nat.card_congr (Submodule.submoduleOfEquivOfLe (by
          rw [← range_d₁₀_eq_coinvariantsKer]
          exact LinearMap.range_le_ker_iff.mpr
            (ModuleCat.hom_ext_iff.mp (Rep.comp_eq_zero M)))).toEquiv,
          ← Nat.card_congr (HNegOneIsoNormKernelQuotient M).toLinearEquiv.toEquiv]
  have hcard (f : Module.End R M) :
      Nat.card M = Nat.card (ker f) * Nat.card (range f) := by
    calc
      Nat.card M = Nat.card (ker f) * Nat.card (M ⧸ ker f) :=
        Submodule.card_eq_card_quotient_mul_card _
      _ = Nat.card (ker f) * Nat.card (range f) := by
        rw [Nat.card_congr f.quotKerEquivRange.toEquiv]
  have hnorm := hcard M.ρ.norm
  have hdiff := hcard D
  have hrangeNorm : 0 < Nat.card (range M.ρ.norm) :=
    Nat.card_pos_iff.mpr ⟨⟨0⟩, inferInstance⟩
  have hrangeDiff : 0 < Nat.card (range D) :=
    Nat.card_pos_iff.mpr ⟨⟨0⟩, inferInstance⟩
  have hcard : Nat.card (tateCohomology M 0) = Nat.card (tateCohomology M (-1)) := by
    apply Nat.mul_right_cancel (Nat.mul_pos hrangeNorm hrangeDiff)
    calc
      Nat.card (tateCohomology M 0) *
          (Nat.card (range M.ρ.norm) * Nat.card (range D)) =
          (Nat.card (range M.ρ.norm) * Nat.card (tateCohomology M 0)) *
            Nat.card (range D) := by ac_rfl
      _ = Nat.card (ker D) * Nat.card (range D) := by rw [← hzero, hinv]
      _ = Nat.card M := hdiff.symm
      _ = Nat.card (ker M.ρ.norm) * Nat.card (range M.ρ.norm) := hnorm
      _ = (Nat.card (range D) * Nat.card (tateCohomology M (-1))) *
          Nat.card (range M.ρ.norm) := by rw [hnegone, hcoinv]
      _ = Nat.card (tateCohomology M (-1)) *
          (Nat.card (range M.ρ.norm) * Nat.card (range D)) := by ac_rfl
  have hfiniteQuotient : Finite (ker M.ρ.norm ⧸
      (Representation.Coinvariants.ker M.ρ).submoduleOf (ker M.ρ.norm)) :=
    Finite.of_surjective (Submodule.mkQ _ ) (Submodule.mkQ_surjective _)
  have hfiniteNegOne : Finite (tateCohomology M (-1)) :=
    (HNegOneIsoNormKernelQuotient M).toLinearEquiv.toEquiv.finite_iff.mpr hfiniteQuotient
  rw [herbrandQuotient_def, hcard]
  exact div_self (Nat.cast_ne_zero.mpr (Nat.card_ne_zero.mpr ⟨⟨0⟩, hfiniteNegOne⟩))

section TrivialInt

variable (H : Type) [Group H] [Fintype H]

/-- The Herbrand quotient of the trivial integral representation is the order of the finite
group. -/
@[simp]
theorem herbrandQuotient_trivial_int_eq_card :
    herbrandQuotient (Rep.trivial ℤ H ℤ) = Nat.card H := by
  let hsub := subsingleton_tateCohomology_negOne_trivial_int H
  rw [herbrandQuotient_def, natCard_tateCohomology_zero_trivial_int_eq_card]
  rw [@Nat.card_of_subsingleton _ 0 hsub]
  simp

end TrivialInt

end TauCeti.TateCohomology

namespace TauCeti.TateCohomology

section Multiplicativity

variable {R G : Type u} [CommRing R] [CommGroup G] [Fintype G]

/-- The two-periodic norm-and-augmentation complex of a finite cyclic group representation. -/
private noncomputable def cyclicComplex (M : Rep R G) (g : G) :
    CochainComplex (ModuleCat R) (Fin 2) where
  X _ := ModuleCat.of R M
  d i j := match i, j with
    | 0, 1 => M.norm.toModuleCatHom
    | 1, 0 => ModuleCat.ofHom (Rep.applyAsHom M g - 𝟙 M).hom.toLinearMap
    | _, _ => 0
  shape := by rintro i j hij; fin_cases i <;> fin_cases j <;> simp_all
  d_comp_d' := by
    rintro i _ _ hij hjk
    simp only [ComplexShape.up_Rel] at hij hjk
    subst hij hjk
    fin_cases i
    · ext x
      simp [Rep.sub_hom, Rep.applyAsHom, Rep.norm]
    · ext x
      simp [Rep.sub_hom, Rep.applyAsHom, Rep.norm]

/-- The two-periodic complex is functorial in the coefficient representation. -/
private noncomputable def cyclicComplexFunctor (g : G) :
    Rep R G ⥤ CochainComplex (ModuleCat R) (Fin 2) where
  obj M := cyclicComplex M g
  map {M N} f :=
    { f := fun _ ↦ (forget₂ (Rep R G) (ModuleCat R)).map f
      comm' := by
        rintro i j hij
        simp only [ComplexShape.up_Rel] at hij
        subst hij
        fin_cases i
        · exact congrArg (forget₂ (Rep R G) (ModuleCat R)).map (Rep.norm_comm f)
        · dsimp only [cyclicComplex, Fin.reduceFinMk, Fin.reduceAdd]
          change (forget₂ (Rep R G) (ModuleCat R)).map f ≫
              ModuleCat.ofHom (Rep.applyAsHom N g - 𝟙 N).hom.toLinearMap =
            ModuleCat.ofHom (Rep.applyAsHom M g - 𝟙 M).hom.toLinearMap ≫
              (forget₂ (Rep R G) (ModuleCat R)).map f
          rw [ModuleCat.hom_ext_iff]
          ext x
          simpa [Rep.sub_hom] using (congr($(Rep.applyAsHom_comm f g).hom x)).symm }
  map_id _ := by ext i; rfl
  map_comp _ _ := by ext i; rfl

private instance (g : G) :
    (cyclicComplexFunctor (R := R) (G := G) g).PreservesZeroMorphisms where
  map_zero _ _ := by ext i; rfl

/-- Applying the two-periodic complex functor preserves short exact sequences. -/
private lemma cyclicComplexFunctor_map_shortExact {S : ShortComplex (Rep R G)}
    (hS : S.ShortExact) (g : G) : (S.map (cyclicComplexFunctor g)).ShortExact := by
  rw [HomologicalComplex.shortExact_iff_degreewise_shortExact]
  intro i
  exact {
    exact := hS.exact.map (forget₂ (Rep R G) (ModuleCat R))
    mono_f := ModuleCat.mono_iff_injective _|>.2
      (Rep.mono_iff_injective S.f |>.1 hS.mono_f)
    epi_g := ModuleCat.epi_iff_surjective _|>.2
      (Rep.epi_iff_surjective S.g |>.1 hS.epi_g) }

/-- The circular six-term homology sequence associated to a short exact sequence. -/
private noncomputable def sixTermSequence {S : ShortComplex (Rep R G)}
    (hS : S.ShortExact) (g : G) : CochainComplex (ModuleCat R) (Fin 6) := by
  let T := S.map (cyclicComplexFunctor g)
  let hT := cyclicComplexFunctor_map_shortExact hS g
  exact
    { X := fun i ↦ match i with
        | 0 => T.X₁.homology 0
        | 1 => T.X₂.homology 0
        | 2 => T.X₃.homology 0
        | 3 => T.X₁.homology 1
        | 4 => T.X₂.homology 1
        | 5 => T.X₃.homology 1
      d := fun i j ↦ match i, j with
        | 0, 1 => HomologicalComplex.homologyMap T.f 0
        | 1, 2 => HomologicalComplex.homologyMap T.g 0
        | 2, 3 => hT.δ 0 1 rfl
        | 3, 4 => HomologicalComplex.homologyMap T.f 1
        | 4, 5 => HomologicalComplex.homologyMap T.g 1
        | 5, 0 => hT.δ 1 0 rfl
        | _, _ => 0
      shape := by rintro i j hij; fin_cases i <;> fin_cases j <;> simp_all
      d_comp_d' := by
        rintro i _ _ hij hjk
        simp only [ComplexShape.up_Rel] at hij hjk
        subst hij hjk
        fin_cases i
        · simp only [Fin.reduceFinMk, Fin.reduceAdd]
          rw [← HomologicalComplex.homologyMap_comp, T.zero,
            HomologicalComplex.homologyMap_zero]
        · simpa only [Fin.reduceFinMk, Fin.reduceAdd] using hT.comp_δ 0 1 rfl
        · simpa only [Fin.reduceFinMk, Fin.reduceAdd] using hT.δ_comp 0 1 rfl
        · simp only [Fin.reduceFinMk, Fin.reduceAdd]
          rw [← HomologicalComplex.homologyMap_comp, T.zero,
            HomologicalComplex.homologyMap_zero]
        · simpa only [Fin.reduceFinMk, Fin.reduceAdd] using hT.comp_δ 1 0 rfl
        · simpa only [Fin.reduceFinMk, Fin.reduceAdd] using hT.δ_comp 1 0 rfl }

private lemma sixTermSequence_exactAt {S : ShortComplex (Rep R G)}
    (hS : S.ShortExact) (g : G) (i : Fin 6) : (sixTermSequence hS g).ExactAt i := by
  let T := S.map (cyclicComplexFunctor g)
  let hT := cyclicComplexFunctor_map_shortExact hS g
  fin_cases i <;>
      change ShortComplex.Exact (ShortComplex.mk ..) <;>
      erw [CochainComplex.prev, CochainComplex.next]
  · exact hT.homology_exact₁ 1 0 rfl
  · exact hT.homology_exact₂ 0
  · exact hT.homology_exact₃ 0 1 rfl
  · exact hT.homology_exact₁ 0 1 rfl
  · exact hT.homology_exact₂ 1
  · exact hT.homology_exact₃ 1 0 rfl

/-- Degree `-1` Tate cohomology is the even homology of the two-periodic complex. -/
private noncomputable def negOneIsoCyclicHomology (M : Rep R G) (g : G)
    (hg : ∀ x, x ∈ Subgroup.zpowers g) :
    tateCohomology M (-1) ≅ (cyclicComplex M g).homology 0 := by
  let T := Rep.FiniteCyclicGroup.subCompNormHom M g
  refine HNegOneIsoNormKernelQuotient M ≪≫ ?_
  refine (Submodule.Quotient.equiv _ T.moduleCatToCycles.range
    (LinearEquiv.refl R _) ?_).toModuleIso ≪≫ ?_
  · ext x
    rw [Representation.FiniteCyclicGroup.coinvariantsKer_eq_range M.ρ g hg]
    constructor
    · rintro ⟨y, ⟨z, hz⟩, hy⟩
      refine ⟨z, Subtype.ext ?_⟩
      exact hz.trans (congrArg Subtype.val hy)
    · rintro ⟨z, hz⟩
      refine ⟨x, ⟨z, ?_⟩, rfl⟩
      exact (congrArg Subtype.val hz).trans (by rfl)
  · exact (ShortComplex.moduleCatHomologyIso T).symm ≪≫
      ((cyclicComplex M g).homologyIsoSc' 1 0 1
        (by erw [CochainComplex.prev]; rfl) (by erw [CochainComplex.next]; rfl)).symm

/-- Degree-zero Tate cohomology is the odd homology of the two-periodic complex. -/
private noncomputable def zeroIsoCyclicHomology (M : Rep R G) (g : G)
    (hg : ∀ x, x ∈ Subgroup.zpowers g) :
    tateCohomology M 0 ≅ (cyclicComplex M g).homology 1 := by
  let hker : M.ρ.invariants = ker (Rep.applyAsHom M g - 𝟙 M).hom.toLinearMap := by
    ext x
    simpa [Rep.sub_hom, sub_eq_zero] using
      (Representation.mem_invariants_iff_of_forall_mem_zpowers M.ρ g hg x)
  let T := Rep.FiniteCyclicGroup.normHomCompSub M g
  refine H0IsoNormQuotient M ≪≫ ?_
  refine (Submodule.Quotient.equiv _ T.moduleCatToCycles.range
    (LinearEquiv.ofEq _ _ hker) ?_).toModuleIso ≪≫ ?_
  · ext x
    constructor
    · rintro ⟨y, ⟨z, hz⟩, hy⟩
      refine ⟨z, Subtype.ext ?_⟩
      exact hz.trans (congrArg Subtype.val hy)
    · rintro ⟨z, hz⟩
      refine ⟨(LinearEquiv.ofEq _ _ hker).symm x, ⟨z, ?_⟩, ?_⟩
      · exact (congrArg Subtype.val hz).trans (by rfl)
      · exact (LinearEquiv.ofEq _ _ hker).apply_symm_apply x
  · exact (ShortComplex.moduleCatHomologyIso T).symm ≪≫
      ((cyclicComplex M g).homologyIsoSc' 0 1 0
        (by erw [CochainComplex.prev]; rfl) (by erw [CochainComplex.next]; rfl)).symm

/-- **Multiplicativity of the Herbrand quotient.** In a short exact sequence of representations
of a finite cyclic group, the quotient of the middle term is the product of the quotients of the
outer terms, provided all three quotients are nonzero. -/
theorem herbrandQuotient_eq_mul_of_shortExact {S : ShortComplex (Rep R G)}
    (hS : S.ShortExact) [IsCyclic G]
    (h₁ : herbrandQuotient S.X₁ ≠ 0) (h₂ : herbrandQuotient S.X₂ ≠ 0)
    (h₃ : herbrandQuotient S.X₃ ≠ 0) :
    herbrandQuotient S.X₂ = herbrandQuotient S.X₁ * herbrandQuotient S.X₃ := by
  let hgen := isCyclic_iff_exists_zpowers_eq_top.mp (inferInstance : IsCyclic G)
  let g := hgen.choose
  have hg : ∀ x : G, x ∈ Subgroup.zpowers g := fun x ↦
    hgen.choose_spec.ge (Subgroup.mem_top x)
  unfold herbrandQuotient at h₁ h₂ h₃ ⊢
  rw [ne_eq, div_eq_zero_iff, Rat.natCast_eq_zero_iff, not_or] at h₁ h₂ h₃
  rcases h₁ with ⟨h₁₀, h₁₁⟩
  rcases h₂ with ⟨h₂₀, h₂₁⟩
  rcases h₃ with ⟨h₃₀, h₃₁⟩
  field_simp
  suffices h :
      Nat.card ((sixTermSequence hS g).X 0) *
        Nat.card ((sixTermSequence hS g).X 2) *
        Nat.card ((sixTermSequence hS g).X 4) =
      Nat.card ((sixTermSequence hS g).X 1) *
        Nat.card ((sixTermSequence hS g).X 3) *
        Nat.card ((sixTermSequence hS g).X 5) by
    change Nat.card ((cyclicComplex S.X₁ g).homology 0) *
        Nat.card ((cyclicComplex S.X₃ g).homology 0) *
        Nat.card ((cyclicComplex S.X₂ g).homology 1) =
      Nat.card ((cyclicComplex S.X₂ g).homology 0) *
        Nat.card ((cyclicComplex S.X₁ g).homology 1) *
        Nat.card ((cyclicComplex S.X₃ g).homology 1) at h
    rw [← Nat.card_congr (negOneIsoCyclicHomology S.X₁ g hg).toLinearEquiv.toEquiv,
      ← Nat.card_congr (negOneIsoCyclicHomology S.X₂ g hg).toLinearEquiv.toEquiv,
      ← Nat.card_congr (negOneIsoCyclicHomology S.X₃ g hg).toLinearEquiv.toEquiv,
      ← Nat.card_congr (zeroIsoCyclicHomology S.X₁ g hg).toLinearEquiv.toEquiv,
      ← Nat.card_congr (zeroIsoCyclicHomology S.X₂ g hg).toLinearEquiv.toEquiv,
      ← Nat.card_congr (zeroIsoCyclicHomology S.X₃ g hg).toLinearEquiv.toEquiv] at h
    norm_cast at h ⊢
    ac_nf at h ⊢
  have hcard (i : Fin 6) :=
    Nat.card_congr (quotKerEquivRange ((sixTermSequence hS g).d i (i + 1)).hom).toEquiv ▸
      Submodule.card_eq_card_quotient_mul_card
        (ker ((sixTermSequence hS g).d i (i + 1)).hom)
  have hexact (i : Fin 6) :
      range ((sixTermSequence hS g).d (i - 1) i).hom =
        ker ((sixTermSequence hS g).d i (i + 1)).hom :=
    CochainComplex.prev (Fin 6) i ▸ CochainComplex.next (Fin 6) i ▸
      (sixTermSequence_exactAt hS g i).moduleCat_range_eq_ker
  rw [hcard 0, hcard 1, hcard 2, hcard 3, hcard 4, hcard 5]
  erw [hexact 0, hexact 1, hexact 2, hexact 3, hexact 4, hexact 5]
  dsimp only [Fin.reduceAdd]
  ac_rfl

end Multiplicativity

end TauCeti.TateCohomology
