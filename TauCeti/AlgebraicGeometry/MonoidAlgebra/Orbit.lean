/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import TauCeti.Algebra.MonoidAlgebra.Face.Localization
import TauCeti.Algebra.MonoidAlgebra.GroupCompletion
import TauCeti.Algebra.MonoidAlgebra.Localization
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
2. **Orbit localizations, stratification, and Zariski closures.** Passing to `F.faceSubgroup` gives
   `F.orbitLocalizationHom R : Spec R[F.faceSubgroup] ⟶ Spec R[F]` (an open immersion when
   `F.toAddSubmonoid.FG`) and `F.orbitHom R : Spec R[F.faceSubgroup] ⟶ Spec R[S]`
   (`range_orbitHom`), with Zariski closure `Set.range (F.closedFaceHom R)` over any commutative
   ring `R`. Every prime of `Spec R[S]` lies in a unique orbit image
   (`AddSubmonoid.existsUnique_mem_range_orbitHom`), corresponding to `S.primeFace p`, and orbit
   closures decompose into unions of orbit strata
   (`SaturatedAddSubmonoid.closure_range_orbitHom_eq_iUnion`). In particular,
   `S.diagonalizableGroupInclusion R : Spec R[AddSubgroup.closure S] ⟶ Spec R[S]` has dense image
   and is an open immersion when `S.FG`.
3. **Normalization square.** The saturation morphism `S.nsmulSaturationHom R : Spec R[S_sat] ⟶`
   `Spec R[S]` and orbit saturation morphism `F.orbitSaturationHom R` form a commuting square with
   the orbit morphisms (`SaturatedAddSubmonoid.orbitSaturationHom_comp_orbitHom`).
4. **Closure order on orbits.** Over any nontrivial commutative ring `R` and any abelian group `G`,
   `Set.range (F₁.orbitHom R) ⊆ closure (Set.range (F₂.orbitHom R)) ↔ F₁ ≤ F₂`.

## References

* W. Bruns and J. Gubeladze, *Polytopes, Rings, and K-Theory*, §4.F.
* D. Cox, J. Little and H. Schenck, *Toric Varieties*, Proposition 3.2.7.
* W. Fulton, *Introduction to Toric Varieties*, §3.1.
-/

public section

open AlgebraicGeometry CategoryTheory AddMonoidAlgebra

universe u

private theorem range_specMap_mapDomainRingHom {M H : Type u} [AddCommMonoid M] [AddCommGroup H]
    (R : Type u) [CommRing R] {f : M →+ H} (hf : Function.Injective f)
    (hshift : ∀ g : H, ∃ a b : M, g + f b = f a) :
    Set.range (Spec.map (CommRingCat.ofHom (mapDomainRingHom R f))) =
      {p | ∀ m : M, single m (1 : R) ∉ p.asIdeal} := by
  let := (mapDomainRingHom R f).toAlgebra
  have := isLocalization_mrange_of_of_exists_add_eq hf hshift R
  have halg : mapDomainRingHom R f = algebraMap (AddMonoidAlgebra R M) (AddMonoidAlgebra R H) :=
    (RingHom.algebraMap_toAlgebra (mapDomainRingHom R f)).symm
  have hrange : Set.range (Spec.map (CommRingCat.ofHom (mapDomainRingHom R f))) =
      Set.range (PrimeSpectrum.comap
        (algebraMap (AddMonoidAlgebra R M) (AddMonoidAlgebra R H))) := by
    rw [halg]
    exact congrArg Set.range <| funext fun y ↦ by rw [Spec.map_apply]; rfl
  rw [hrange, PrimeSpectrum.localization_comap_range
    (AddMonoidAlgebra R H) (MonoidHom.mrange (of R M))]
  ext p
  simp only [Set.disjoint_left, SetLike.mem_coe, MonoidHom.mem_mrange, of_apply, Set.mem_ofPred_eq]
  exact ⟨fun h m ↦ h ⟨.ofAdd m, by simp⟩, fun h _ ⟨m, hm⟩ ↦ hm ▸ h m.toAdd⟩

namespace AddSubmonoid

variable {G : Type u} [AddCommGroup G] (S : AddSubmonoid G) (R : Type u) [CommRing R]

/-- The saturation morphism `Spec R[S.nsmulSaturation ⊓ AddSubgroup.closure S] ⟶ Spec R[S]`
induced by the canonical inclusion `S →+ S.nsmulSaturation ⊓ AddSubgroup.closure S`. -/
noncomputable def nsmulSaturationHom :
    Spec (.of (AddMonoidAlgebra R
        ↥(S.nsmulSaturation ⊓ (AddSubgroup.closure (S : Set G)).toAddSubmonoid))) ⟶
      Spec (.of (AddMonoidAlgebra R S)) :=
  Spec.map (CommRingCat.ofHom (mapDomainRingHom R
    (inclusion (le_inf S.le_nsmulSaturation AddSubgroup.subset_closure))))

/-- Explicit definition of `AddSubmonoid.nsmulSaturationHom`. -/
theorem nsmulSaturationHom_def :
    S.nsmulSaturationHom R = Spec.map (CommRingCat.ofHom (mapDomainRingHom R
      (inclusion (le_inf S.le_nsmulSaturation AddSubgroup.subset_closure)))) := (rfl)

/-- The face of `S` formed by the exponents of coefficient-one monomials outside `p.asIdeal`. -/
def primeFace (p : PrimeSpectrum (AddMonoidAlgebra R S)) : SaturatedAddSubmonoid S where
  carrier := {s : S | single s (1 : R) ∉ p.asIdeal}
  zero_mem' := by rw [Set.mem_ofPred_eq, ← one_def]; exact p.isPrime.one_notMem
  add_mem' {a b} ha hb := by
    rw [Set.mem_ofPred_eq, ← one_mul (1 : R), ← single_mul_single]
    exact p.isPrime.mul_notMem ha hb
  addSaturated {a b} hab := by
    simp only [mem_mk, AddSubsemigroup.mem_mk, Set.mem_ofPred_eq] at hab ⊢
    rw [← one_mul (1 : R), ← single_mul_single] at hab
    exact ⟨fun h ↦ hab (p.asIdeal.mul_mem_right _ h), fun h ↦ hab (p.asIdeal.mul_mem_left _ h)⟩

/-- An element `s : S` belongs to `S.primeFace p` iff `single s (1 : R) ∉ p.asIdeal`. -/
@[simp]
theorem mem_primeFace_iff {R : Type u} [CommRing R] (p : PrimeSpectrum (AddMonoidAlgebra R S))
    {s : S} : s ∈ S.primeFace R p ↔ single s (1 : R) ∉ p.asIdeal := Iff.rfl

end AddSubmonoid

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
instance instIsClosedImmersionClosedFaceHom : IsClosedImmersion (F.closedFaceHom R) := by
  rw [closedFaceHom_def]
  exact IsClosedImmersion.spec_of_surjective _
    (F.toAddSubmonoid.faceRestriction_surjective F.addSaturated)

/-- The set-theoretic image of `F.closedFaceHom R` is the zero locus of `F.faceIdeal R`. -/
theorem range_closedFaceHom :
    Set.range (F.closedFaceHom R) =
      PrimeSpectrum.zeroLocus (F.toAddSubmonoid.faceIdeal R : Set (AddMonoidAlgebra R S)) := by
  have hrange : Set.range (F.closedFaceHom R) =
      Set.range (PrimeSpectrum.comap
        (F.toAddSubmonoid.faceRestriction F.addSaturated R).toRingHom) :=
    congrArg Set.range <| funext fun y ↦ by rw [closedFaceHom_def, Spec.map_apply]; rfl
  rw [hrange, ← F.toAddSubmonoid.ker_faceRestriction F.addSaturated]
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

/-- When `F` is finitely generated, `F.orbitLocalizationHom R : Spec R[F.faceSubgroup] ⟶ Spec R[F]`
is an open immersion over any commutative ring `R`. -/
theorem isOpenImmersion_orbitLocalizationHom (hF : F.toAddSubmonoid.FG) :
    IsOpenImmersion (F.orbitLocalizationHom R) := by
  rw [orbitLocalizationHom_def]
  let := (mapDomainRingHom R F.toFaceSubgroup).toAlgebra
  obtain ⟨u, _⟩ := F.exists_isLocalization_away_faceSubgroup hF R
  have h := IsOpenImmersion.of_isLocalization (S := AddMonoidAlgebra R F.faceSubgroup)
    (single u (1 : R))
  rwa [RingHom.algebraMap_toAlgebra] at h

/-- The set-theoretic image of `F.orbitLocalizationHom R` consists of all primes of `R[F]`
avoiding every coefficient-one monomial `single a 1`. -/
theorem range_orbitLocalizationHom :
    Set.range (F.orbitLocalizationHom R) = {p | ∀ a : F, single a (1 : R) ∉ p.asIdeal} := by
  rw [orbitLocalizationHom_def]
  exact range_specMap_mapDomainRingHom R F.toFaceSubgroup_injective F.exists_add_toFaceSubgroup_eq

/-- The orbit morphism `Spec R[F.faceSubgroup] ⟶ Spec R[S]` induced by `F.orbitMap R` (which is a
locally closed immersion when `F.toAddSubmonoid.FG`, factoring through the open immersion
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

/-- The orbit saturation morphism
`Spec R[(S.nsmulSaturationInfClosureFaceOrderIso.symm F).faceSubgroup] ⟶`
`Spec R[F.faceSubgroup]` induced by `F.faceSubgroupNSMulSaturationEquiv` and
`F.faceSubgroup ≤ F.faceSubgroup.nsmulSaturation`. -/
noncomputable def orbitSaturationHom :
    Spec (.of (AddMonoidAlgebra R
        ((S.nsmulSaturationInfClosureFaceOrderIso).symm F).faceSubgroup)) ⟶
      Spec (.of (AddMonoidAlgebra R F.faceSubgroup)) :=
  Spec.map (CommRingCat.ofHom (mapDomainRingHom R
    (F.faceSubgroupNSMulSaturationEquiv.symm.toAddMonoidHom.comp
      (AddSubgroup.inclusion F.faceSubgroup.le_nsmulSaturation))))

/-- Explicit definition of `SaturatedAddSubmonoid.orbitSaturationHom`. -/
theorem orbitSaturationHom_def :
    F.orbitSaturationHom R = Spec.map (CommRingCat.ofHom (mapDomainRingHom R
      (F.faceSubgroupNSMulSaturationEquiv.symm.toAddMonoidHom.comp
        (AddSubgroup.inclusion F.faceSubgroup.le_nsmulSaturation)))) := (rfl)

/-- On orbit schemes, `F.orbitSaturationHom R` intertwines `F.orbitHom R` with the saturated orbit
morphism and `S.nsmulSaturationHom R`. -/
@[reassoc]
theorem orbitSaturationHom_comp_orbitHom :
    F.orbitSaturationHom R ≫ F.orbitHom R =
      ((S.nsmulSaturationInfClosureFaceOrderIso).symm F).orbitHom R ≫ S.nsmulSaturationHom R := by
  have hring : (mapDomainRingHom R
      (F.faceSubgroupNSMulSaturationEquiv.symm.toAddMonoidHom.comp
        (AddSubgroup.inclusion F.faceSubgroup.le_nsmulSaturation))).comp
        (F.orbitMap R).toRingHom =
      (((S.nsmulSaturationInfClosureFaceOrderIso).symm F).orbitMap R).toRingHom.comp
        (mapDomainRingHom R
          (AddSubmonoid.inclusion (le_inf S.le_nsmulSaturation AddSubgroup.subset_closure))) :=
    congrArg AlgHom.toRingHom
      (F.orbitMap_comp_mapDomainAlgHom_inclusion_nsmulSaturation R).symm
  rw [orbitSaturationHom_def, orbitHom_def, orbitHom_def, AddSubmonoid.nsmulSaturationHom_def,
    ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hring]

/-- Over any commutative ring `R`, the image of `F.orbitHom R` in `Spec R[S]` consists of all
primes containing the coefficient-one monomials outside `F` and avoiding those in `F`. -/
theorem range_orbitHom :
    Set.range (F.orbitHom R) =
      {p | (∀ s : S, s ∉ F → single s (1 : R) ∈ p.asIdeal) ∧
        (∀ s : S, s ∈ F → single s (1 : R) ∉ p.asIdeal)} := by
  have hmem (q : ↥(Spec (.of (AddMonoidAlgebra R F)))) (x : AddMonoidAlgebra R S) :
      x ∈ ((F.closedFaceHom R) q).asIdeal ↔
        (F.toAddSubmonoid.faceRestriction F.addSaturated R) x ∈ q.asIdeal :=
    Iff.rfl
  ext p
  refine ⟨?_, fun ⟨hout, hin⟩ ↦ ?_⟩
  · rintro ⟨y, rfl⟩
    rw [← F.orbitLocalizationHom_comp_closedFaceHom R, Scheme.Hom.comp_apply]
    have hq : F.orbitLocalizationHom R y ∈ Set.range (F.orbitLocalizationHom R) := ⟨y, rfl⟩
    rw [F.range_orbitLocalizationHom R, Set.mem_ofPred_eq] at hq
    refine ⟨fun s hs ↦ (hmem _ _).2 (by simp [hs]), fun s hs hs' ↦ hq ⟨s, hs⟩ ?_⟩
    simpa [F.toAddSubmonoid.faceRestriction_single_of_mem F.addSaturated hs] using (hmem _ _).1 hs'
  · obtain ⟨q, rfl⟩ : p ∈ Set.range (F.closedFaceHom R) := by
      rw [F.range_closedFaceHom R]
      exact (PrimeSpectrum.mem_zeroLocus (x := (p : PrimeSpectrum (AddMonoidAlgebra R S))) _).2 <|
        by
          rw [F.toAddSubmonoid.faceIdeal_def, SetLike.coe_subset_coe, Ideal.span_le]
          rintro _ ⟨s, hs, rfl⟩; exact hout s hs
    have hq : q ∈ Set.range (F.orbitLocalizationHom R) := by
      rw [F.range_orbitLocalizationHom R, Set.mem_ofPred_eq]
      intro ⟨s, hs⟩ hq
      exact hin s hs ((hmem q _).2 (by
        rwa [F.toAddSubmonoid.faceRestriction_single_of_mem F.addSaturated hs]))
    obtain ⟨y, hy⟩ := hq
    exact ⟨y, by rw [← F.orbitLocalizationHom_comp_closedFaceHom R, Scheme.Hom.comp_apply, hy]⟩

/-- Over any commutative ring `R`, a prime `p` of `Spec R[S]` lies in `Set.range (F.orbitHom R)`
if and only if `S.primeFace R p = F`. -/
theorem _root_.AddSubmonoid.mem_range_orbitHom_iff_primeFace_eq
    (p : Spec (.of (AddMonoidAlgebra R S))) :
    p ∈ Set.range (F.orbitHom R) ↔ S.primeFace R p = F := by
  rw [F.range_orbitHom R, Set.mem_ofPred_eq, SetLike.ext_iff]
  refine ⟨fun ⟨hout, hin⟩ s ↦ ?_, fun h ↦ ⟨fun s hs ↦ ?_, fun s hs ↦ ?_⟩⟩
  · exact ⟨fun hs ↦ by_contra fun hnot ↦ hs (hout s hnot), fun hs ↦ hin s hs⟩
  · by_contra hnot; exact hs ((h s).1 hnot)
  · exact (h s).2 hs

/-- Over any commutative ring `R`, every prime `p` of `Spec R[S]` lies in the image of
`F.orbitHom R` for a unique face `F : SaturatedAddSubmonoid S`, namely `S.primeFace R p`. -/
theorem _root_.AddSubmonoid.existsUnique_mem_range_orbitHom
    (p : Spec (.of (AddMonoidAlgebra R S))) :
    ∃! F : SaturatedAddSubmonoid S, p ∈ Set.range (F.orbitHom R) :=
  ⟨S.primeFace R p, (S.mem_range_orbitHom_iff_primeFace_eq _ R p).2 rfl,
    fun F hF ↦ ((S.mem_range_orbitHom_iff_primeFace_eq F R p).1 hF).symm⟩

/-- Over any commutative ring `R`, the Zariski closure of the `F`-orbit in `Spec R[S]` is the
zero locus of `F.faceIdeal R`. -/
theorem closure_range_orbitHom_eq_zeroLocus :
    closure (Set.range (F.orbitHom R)) =
      PrimeSpectrum.zeroLocus (F.toAddSubmonoid.faceIdeal R : Set (AddMonoidAlgebra R S)) := by
  have hrange : Set.range (F.orbitHom R) =
      Set.range (PrimeSpectrum.comap (F.orbitMap R).toRingHom) :=
    congrArg Set.range <| funext fun y ↦ by rw [orbitHom_def, Spec.map_apply]; rfl
  rw [hrange, ← F.ker_orbitMap R]
  exact PrimeSpectrum.closure_range_comap (F.orbitMap R).toRingHom

/-- Over any commutative ring `R`, the Zariski closure of the `F`-orbit in `Spec R[S]` equals the
image of the closed face subscheme `F.closedFaceHom R`. -/
theorem closure_range_orbitHom :
    closure (Set.range (F.orbitHom R)) = Set.range (F.closedFaceHom R) :=
  (F.closure_range_orbitHom_eq_zeroLocus R).trans (F.range_closedFaceHom R).symm

/-- Over any commutative ring `R`, the Zariski closure of the `F`-orbit in `Spec R[S]` is the
union of the orbit images `Set.range (G.orbitHom R)` over all faces `G ≤ F`. -/
theorem closure_range_orbitHom_eq_iUnion :
    closure (Set.range (F.orbitHom R)) = ⋃ (G : SaturatedAddSubmonoid S) (_ : G ≤ F),
      Set.range (G.orbitHom R) := by
  ext p
  rw [F.closure_range_orbitHom_eq_zeroLocus R, Set.mem_iUnion₂]
  refine ⟨fun hp ↦ ⟨S.primeFace R p, ?_⟩, fun ⟨G, hGF, hpG⟩ ↦ ?_⟩
  · refine ⟨fun s hs ↦ by_contra fun hnot ↦ hs ?_,
        (S.mem_range_orbitHom_iff_primeFace_eq _ R p).2 rfl⟩
    exact ((PrimeSpectrum.mem_zeroLocus (x := (p : PrimeSpectrum (AddMonoidAlgebra R S))) _).1 hp)
      ((F.toAddSubmonoid.single_mem_faceIdeal_iff F.addSaturated s 1).2 (Or.inr hnot))
  · refine (PrimeSpectrum.mem_zeroLocus (x := (p : PrimeSpectrum (AddMonoidAlgebra R S))) _).2 ?_
    rw [F.toAddSubmonoid.faceIdeal_def, SetLike.coe_subset_coe, Ideal.span_le]
    rintro _ ⟨s, hs, rfl⟩
    rw [S.mem_range_orbitHom_iff_primeFace_eq G R p] at hpG
    by_contra hnot
    exact hs (hGF (hpG ▸ hnot))

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
    rw [single_pow, one_pow,
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

/-- The canonical inclusion morphism `Spec R[AddSubgroup.closure S] ⟶ Spec R[S]` from the
diagonalizable group scheme `Spec R[AddSubgroup.closure S]` into the affine semigroup scheme
`Spec R[S]` (a split-torus open immersion when `AddSubgroup.closure S` is finite-rank free abelian,
e.g. when `S.FG` and `G` is torsion-free). -/
noncomputable def diagonalizableGroupInclusion :
    Spec (.of (AddMonoidAlgebra R (AddSubgroup.closure (S : Set G)))) ⟶
      Spec (.of (AddMonoidAlgebra R S)) :=
  Spec.map (CommRingCat.ofHom (mapDomainRingHom R S.toGroupClosure))

/-- Explicit definition of `AddSubmonoid.diagonalizableGroupInclusion`. -/
theorem diagonalizableGroupInclusion_def :
    S.diagonalizableGroupInclusion R =
      Spec.map (CommRingCat.ofHom (mapDomainRingHom R S.toGroupClosure)) := (rfl)

/-- When `S` is finitely generated, `S.diagonalizableGroupInclusion R` is an open immersion of
schemes. -/
theorem isOpenImmersion_diagonalizableGroupInclusion (hS : S.FG) :
    IsOpenImmersion (S.diagonalizableGroupInclusion R) := by
  rw [diagonalizableGroupInclusion_def]
  let := (mapDomainRingHom R S.toGroupClosure).toAlgebra
  obtain ⟨s, _⟩ := hS.exists_isLocalization_away_addMonoidAlgebra_groupClosure R
  have h := IsOpenImmersion.of_isLocalization
    (S := AddMonoidAlgebra R (AddSubgroup.closure (S : Set G))) (single s (1 : R))
  rwa [RingHom.algebraMap_toAlgebra] at h

/-- The set-theoretic image of `S.diagonalizableGroupInclusion R` consists of all primes of `R[S]`
avoiding every coefficient-one monomial `single s 1`. -/
theorem range_diagonalizableGroupInclusion :
    Set.range (S.diagonalizableGroupInclusion R) = {p | ∀ s : S, single s (1 : R) ∉ p.asIdeal} := by
  rw [diagonalizableGroupInclusion_def]
  exact range_specMap_mapDomainRingHom R S.toGroupClosure_injective S.exists_add_toGroupClosure_eq

/-- Over every commutative ring `R`, the diagonalizable group scheme
`Spec R[AddSubgroup.closure S]` has dense image in `Spec R[S]`. -/
theorem denseRange_diagonalizableGroupInclusion :
    DenseRange (S.diagonalizableGroupInclusion R) := by
  have h : (S.diagonalizableGroupInclusion R : _ → _) =
      PrimeSpectrum.comap (mapDomainRingHom R S.toGroupClosure) :=
    funext fun p ↦ by rw [diagonalizableGroupInclusion_def, Spec.map_apply]; rfl
  rw [DenseRange, h]
  exact RingHom.denseRange_comap_of_injective _ (mapDomain_injective S.toGroupClosure_injective)

end AddSubmonoid
