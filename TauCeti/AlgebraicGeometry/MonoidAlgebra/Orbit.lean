/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import TauCeti.Algebra.MonoidAlgebra.Face.Coaction
import Mathlib.RingTheory.Spectrum.Prime.RingHom
import TauCeti.RingTheory.Spectrum.Prime.Topology

/-!
# Closed face subschemes, localized orbits, and the orbit closure order

For an additive submonoid `S` of an abelian group `G` and a commutative ring `R`, this file
constructs the scheme-level face and diagonalizable-group orbit morphisms on `Spec R[S]` (which
are torus orbits when `AddSubgroup.closure S` is finite-rank free abelian, e.g. when `S.FG` and
`G` is torsion-free):

1. **Closed face immersions.** Each face `F : SaturatedAddSubmonoid S` induces a closed immersion
   `F.closedFaceHom R : Spec R[F] ⟶ Spec R[S]` with image
   `PrimeSpectrum.zeroLocus (F.toAddSubmonoid.faceIdeal R)`.
2. **Orbit localizations and Zariski closures.** Passing to `F.faceSubgroup` gives
   `F.orbitLocalizationHom R : Spec R[F.faceSubgroup] ⟶ Spec R[F]` (an open immersion for `S.FG`)
   and `F.orbitHom R : Spec R[F.faceSubgroup] ⟶ Spec R[S]` (`range_orbitHom`), with Zariski
   closure `Set.range (F.closedFaceHom R)` over any commutative ring `R`. In particular,
   `S.diagonalizableGroupHom R : Spec R[AddSubgroup.closure S] ⟶ Spec R[S]` has dense image and is
   an open immersion when `S.FG`.
3. **Closure order on orbits.** Over any nontrivial commutative ring `R` and any abelian group `G`,
   `Set.range (F₁.orbitHom R) ⊆ closure (Set.range (F₂.orbitHom R)) ↔ F₁ ≤ F₂`.

## References

* W. Bruns and J. Gubeladze, *Polytopes, Rings, and K-Theory*, §4.F.
* D. Cox, J. Little and H. Schenck, *Toric Varieties*, Proposition 3.2.7.
* W. Fulton, *Introduction to Toric Varieties*, §3.1.
-/

public section

open AlgebraicGeometry CategoryTheory AddMonoidAlgebra

universe u

namespace SaturatedAddSubmonoid

section CommRing

variable {G : Type u} [AddCommGroup G] {S : AddSubmonoid G} (F : SaturatedAddSubmonoid S)
  (R : Type u) [CommRing R]

/-- The closed face morphism `Spec R[F] ⟶ Spec R[S]` induced by `faceRestriction`. -/
noncomputable def closedFaceHom :
    Spec (.of (AddMonoidAlgebra R F)) ⟶ Spec (.of (AddMonoidAlgebra R S)) :=
  Spec.map (CommRingCat.ofHom (F.toAddSubmonoid.faceRestriction F.addSaturated R).toRingHom)

/-- Explicit definition of `SaturatedAddSubmonoid.closedFaceHom`. -/
theorem closedFaceHom_def :
    F.closedFaceHom R =
      Spec.map (CommRingCat.ofHom (F.toAddSubmonoid.faceRestriction F.addSaturated R).toRingHom) :=
  (rfl)

/-- Every closed face morphism `F.closedFaceHom R` is a closed immersion of schemes. -/
instance instIsClosedImmersionClosedFaceHom : IsClosedImmersion (F.closedFaceHom R) :=
  IsClosedImmersion.spec_of_surjective _
    (F.toAddSubmonoid.faceRestriction_surjective F.addSaturated)

/-- The set-theoretic image of `F.closedFaceHom R` is the zero locus of `F.faceIdeal R`. -/
theorem range_closedFaceHom :
    Set.range (F.closedFaceHom R) =
      PrimeSpectrum.zeroLocus (F.toAddSubmonoid.faceIdeal R : Set (AddMonoidAlgebra R S)) := by
  rw [← F.toAddSubmonoid.ker_faceRestriction F.addSaturated]
  -- `Spec.map (CommRingCat.ofHom f)` has underlying map `PrimeSpectrum.comap f` (`Spec.map_apply`).
  exact range_comap_of_surjective _ _ (F.toAddSubmonoid.faceRestriction_surjective F.addSaturated)

/-- The canonical morphism `Spec R[F.faceSubgroup] ⟶ Spec R[F]` from the localized `F`-orbit into
its closed face scheme. -/
noncomputable def orbitLocalizationHom :
    Spec (.of (AddMonoidAlgebra R F.faceSubgroup)) ⟶ Spec (.of (AddMonoidAlgebra R F)) :=
  Spec.map (CommRingCat.ofHom (mapDomainRingHom R F.toFaceSubgroup))

/-- Explicit definition of `SaturatedAddSubmonoid.orbitLocalizationHom`. -/
theorem orbitLocalizationHom_def :
    F.orbitLocalizationHom R = Spec.map (CommRingCat.ofHom (mapDomainRingHom R F.toFaceSubgroup)) :=
  (rfl)

/-- When `S` is finitely generated, `F.orbitLocalizationHom R : Spec R[F.faceSubgroup] ⟶ Spec R[F]`
is an open immersion over any commutative ring `R`. -/
theorem isOpenImmersion_orbitLocalizationHom (hS : S.FG) :
    IsOpenImmersion (F.orbitLocalizationHom R) := by
  let := (mapDomainRingHom R F.toFaceSubgroup).toAlgebra
  obtain ⟨u, _⟩ := F.exists_isLocalization_away_faceSubgroup hS R
  exact IsOpenImmersion.of_isLocalization (single u (1 : R))

/-- The set-theoretic image of `F.orbitLocalizationHom R` consists of all primes of `R[F]`
avoiding every coefficient-one monomial `single a 1`. -/
theorem range_orbitLocalizationHom :
    Set.range (F.orbitLocalizationHom R) = {p | ∀ a : F, single a (1 : R) ∉ p.asIdeal} := by
  let := (mapDomainRingHom R F.toFaceSubgroup).toAlgebra
  have := F.isLocalization_addMonoidAlgebra_faceSubgroup R
  refine (PrimeSpectrum.localization_comap_range
    (AddMonoidAlgebra R F.faceSubgroup) (MonoidHom.mrange (of R F))).trans (Set.ext fun p ↦ ?_)
  simp only [Set.disjoint_left, SetLike.mem_coe, MonoidHom.mem_mrange, of_apply, Set.mem_ofPred_eq]
  exact ⟨fun h a ↦ h ⟨.ofAdd a, by simp⟩, fun h _ ⟨a, ha⟩ ↦ ha ▸ h a.toAdd⟩

/-- The orbit morphism `Spec R[F.faceSubgroup] ⟶ Spec R[S]` induced by `F.orbitMap R` (which is a
locally closed immersion when `S.FG`, factoring through the open immersion
`isOpenImmersion_orbitLocalizationHom` and the closed immersion `closedFaceHom`). -/
noncomputable def orbitHom :
    Spec (.of (AddMonoidAlgebra R F.faceSubgroup)) ⟶ Spec (.of (AddMonoidAlgebra R S)) :=
  Spec.map (CommRingCat.ofHom (F.orbitMap R).toRingHom)

/-- Explicit definition of `SaturatedAddSubmonoid.orbitHom`. -/
theorem orbitHom_def :
    F.orbitHom R = Spec.map (CommRingCat.ofHom (F.orbitMap R).toRingHom) := (rfl)

/-- `F.orbitHom R` factors as `F.orbitLocalizationHom R` followed by `F.closedFaceHom R`. -/
@[reassoc (attr := simp)]
theorem orbitLocalizationHom_comp_closedFaceHom :
    F.orbitLocalizationHom R ≫ F.closedFaceHom R = F.orbitHom R := by
  have h : (F.orbitMap R).toRingHom = (mapDomainRingHom R F.toFaceSubgroup).comp
      (F.toAddSubmonoid.faceRestriction F.addSaturated R).toRingHom :=
    RingHom.ext fun x ↦ by simp [F.orbitMap_def R]
  rw [orbitLocalizationHom, closedFaceHom, orbitHom, h, CommRingCat.ofHom_comp, Spec.map_comp]

/-- Over any commutative ring `R`, the image of `F.orbitHom R` in `Spec R[S]` consists of all
primes containing the coefficient-one monomials outside `F` and avoiding those in `F`. -/
theorem range_orbitHom :
    Set.range (F.orbitHom R) =
      {p | (∀ s : S, s ∉ F → single s (1 : R) ∈ p.asIdeal) ∧
        (∀ s : S, s ∈ F → single s (1 : R) ∉ p.asIdeal)} := by
  have hmem (q : ↥(Spec (.of (AddMonoidAlgebra R F)))) (x : AddMonoidAlgebra R S) :
      x ∈ ((F.closedFaceHom R) q).asIdeal ↔
        (F.toAddSubmonoid.faceRestriction F.addSaturated R) x ∈ q.asIdeal := by
    rw [F.closedFaceHom_def R, Spec.map_apply]; rfl
  ext p
  rw [← F.orbitLocalizationHom_comp_closedFaceHom R, Scheme.Hom.comp_base, TopCat.coe_comp,
    Set.range_comp]
  refine ⟨fun ⟨q, hq, hp⟩ ↦ hp ▸ ?_, fun ⟨hout, hin⟩ ↦ ?_⟩
  · rw [F.range_orbitLocalizationHom R, Set.mem_ofPred_eq] at hq
    refine ⟨fun s hs ↦ (hmem q _).2 (by simp [hs]), fun s hs hs' ↦ hq ⟨s, hs⟩ ?_⟩
    simpa [F.toAddSubmonoid.faceRestriction_single_of_mem F.addSaturated hs] using (hmem q _).1 hs'
  · obtain ⟨q, rfl⟩ : p ∈ Set.range (F.closedFaceHom R) := by
      rw [F.range_closedFaceHom R]
      exact (PrimeSpectrum.mem_zeroLocus _ _).2 <| by
        rw [F.toAddSubmonoid.faceIdeal_def, SetLike.coe_subset_coe, Ideal.span_le]
        rintro _ ⟨s, hs, rfl⟩; exact hout s hs
    refine ⟨q, ?_, rfl⟩
    rw [F.range_orbitLocalizationHom R, Set.mem_ofPred_eq]
    intro ⟨s, hs⟩ hq
    exact hin s hs ((hmem q _).2 (by
      rwa [F.toAddSubmonoid.faceRestriction_single_of_mem F.addSaturated hs]))

/-- Over any commutative ring `R`, the Zariski closure of the `F`-orbit in `Spec R[S]` is the
zero locus of `F.faceIdeal R`. -/
theorem closure_range_orbitHom_eq_zeroLocus :
    closure (Set.range (F.orbitHom R)) =
      PrimeSpectrum.zeroLocus (F.toAddSubmonoid.faceIdeal R : Set (AddMonoidAlgebra R S)) := by
  rw [← F.ker_orbitMap R]
  -- `Spec.map (CommRingCat.ofHom f)` has underlying map `PrimeSpectrum.comap f` (`Spec.map_apply`).
  exact PrimeSpectrum.closure_range_comap (F.orbitMap R).toRingHom

/-- Over any commutative ring `R`, the Zariski closure of the `F`-orbit in `Spec R[S]` equals the
image of the closed face subscheme `F.closedFaceHom R`. -/
theorem closure_range_orbitHom :
    closure (Set.range (F.orbitHom R)) = Set.range (F.closedFaceHom R) :=
  (F.closure_range_orbitHom_eq_zeroLocus R).trans (F.range_closedFaceHom R).symm

end CommRing

section ClosureOrder

variable {G : Type u} [AddCommGroup G] {S : AddSubmonoid G} (R : Type u) [CommRing R] [Nontrivial R]

/-- Over any nontrivial commutative ring `R` and any abelian group `G`, inclusion of orbit closures
in `Spec R[S]` is equivalent to inclusion of semigroup faces. -/
@[simp]
theorem closure_range_orbitHom_subset_iff (F₁ F₂ : SaturatedAddSubmonoid S) :
    closure (Set.range (F₁.orbitHom R)) ⊆ closure (Set.range (F₂.orbitHom R)) ↔ F₁ ≤ F₂ := by
  rw [F₁.closure_range_orbitHom_eq_zeroLocus R, F₂.closure_range_orbitHom_eq_zeroLocus R]
  refine (PrimeSpectrum.zeroLocus_subset_zeroLocus_iff (F₁.toAddSubmonoid.faceIdeal R)
    (F₂.toAddSubmonoid.faceIdeal R)).trans ⟨fun h s hs₁ ↦ by_contra fun hs₂ ↦ ?_, fun h ↦ ?_⟩
  · obtain ⟨n, hn⟩ :=
      h ((F₂.toAddSubmonoid.single_mem_faceIdeal_iff F₂.addSaturated s 1).2 (Or.inr hs₂))
    rw [show (single s (1 : R)) ^ n = single (n • s) (1 : R) by rw [single_pow, one_pow],
      F₁.toAddSubmonoid.single_mem_faceIdeal_iff F₁.addSaturated] at hn
    exact hn.elim one_ne_zero (· <| nsmul_mem hs₁ n)
  · exact ((F₂.toAddSubmonoid.faceIdeal_le_faceIdeal_iff F₁.toAddSubmonoid F₁.addSaturated).2
      (SaturatedAddSubmonoid.toAddSubmonoid_le_iff.2 h)).trans Ideal.le_radical

/-- Over any nontrivial commutative ring `R` and any abelian group `G`, the `F₁`-orbit lies in the
Zariski closure of the `F₂`-orbit if and only if `F₁ ≤ F₂`. -/
@[simp]
theorem range_orbitHom_subset_closure_iff (F₁ F₂ : SaturatedAddSubmonoid S) :
    Set.range (F₁.orbitHom R) ⊆ closure (Set.range (F₂.orbitHom R)) ↔ F₁ ≤ F₂ := by
  rw [← isClosed_closure.closure_subset_iff, closure_range_orbitHom_subset_iff]

end ClosureOrder

end SaturatedAddSubmonoid

namespace AddSubmonoid

variable {G : Type u} [AddCommGroup G] (S : AddSubmonoid G) (R : Type u) [CommRing R]

/-- The canonical morphism `Spec R[AddSubgroup.closure S] ⟶ Spec R[S]` from the diagonalizable
group scheme `Spec R[AddSubgroup.closure S]` into the affine semigroup scheme `Spec R[S]` (a
split-torus immersion when `AddSubgroup.closure S` is finite-rank free abelian, e.g. when `S.FG`
and `G` is torsion-free). -/
noncomputable def diagonalizableGroupHom :
    Spec (.of (AddMonoidAlgebra R (AddSubgroup.closure (S : Set G)))) ⟶
      Spec (.of (AddMonoidAlgebra R S)) :=
  Spec.map (CommRingCat.ofHom (mapDomainRingHom R S.toGroupClosure))

/-- Explicit definition of `AddSubmonoid.diagonalizableGroupHom`. -/
theorem diagonalizableGroupHom_def :
    S.diagonalizableGroupHom R =
      Spec.map (CommRingCat.ofHom (mapDomainRingHom R S.toGroupClosure)) := (rfl)

/-- When `S` is finitely generated, `S.diagonalizableGroupHom R` is an open immersion of schemes. -/
theorem isOpenImmersion_diagonalizableGroupHom (hS : S.FG) :
    IsOpenImmersion (S.diagonalizableGroupHom R) := by
  let := (mapDomainRingHom R S.toGroupClosure).toAlgebra
  obtain ⟨s, _⟩ := hS.exists_isLocalization_away_addMonoidAlgebra_groupClosure R
  exact IsOpenImmersion.of_isLocalization (single s (1 : R))

/-- The set-theoretic image of `S.diagonalizableGroupHom R` consists of all primes of `R[S]`
avoiding every coefficient-one monomial `single s 1`. -/
theorem range_diagonalizableGroupHom :
    Set.range (S.diagonalizableGroupHom R) = {p | ∀ s : S, single s (1 : R) ∉ p.asIdeal} := by
  let := (mapDomainRingHom R S.toGroupClosure).toAlgebra
  have := S.isLocalization_addMonoidAlgebra_groupClosure R
  refine (PrimeSpectrum.localization_comap_range
    (AddMonoidAlgebra R (AddSubgroup.closure (S : Set G)))
    (MonoidHom.mrange (of R S))).trans (Set.ext fun p ↦ ?_)
  simp only [Set.disjoint_left, SetLike.mem_coe, MonoidHom.mem_mrange, of_apply, Set.mem_ofPred_eq]
  exact ⟨fun h s ↦ h ⟨.ofAdd s, by simp⟩, fun h _ ⟨s, hs⟩ ↦ hs ▸ h s.toAdd⟩

/-- Over every commutative ring `R`, the diagonalizable group scheme
`Spec R[AddSubgroup.closure S]` has dense image in `Spec R[S]`. -/
theorem denseRange_diagonalizableGroupHom : DenseRange (S.diagonalizableGroupHom R) :=
  RingHom.denseRange_comap_of_injective _ (mapDomain_injective S.toGroupClosure_injective)

end AddSubmonoid
