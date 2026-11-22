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

/-!
# Closed face subschemes, localized orbits, and the orbit closure order

For an additive submonoid `S` of an abelian group `G` and a commutative ring `R`, this file
constructs the scheme-level face and diagonalizable-group orbit morphisms on `Spec R[S]` (which
are torus orbits when `AddSubgroup.closure S` is finite-rank free abelian, e.g. when `S.FG` and
`G` is torsion-free):

1. **Closed face immersions.** Each face `F : SaturatedAddSubmonoid S` induces a closed immersion
   `F.closedFaceHom R : Spec R[F] ⟶ Spec R[S]` with set-theoretic image
   `PrimeSpectrum.zeroLocus (F.toAddSubmonoid.faceIdeal R)`.
2. **Open orbit immersions and Zariski closures.** Passing from `F` to `F.faceSubgroup` gives
   `F.orbitOpenHom R : Spec R[F.faceSubgroup] ⟶ Spec R[F]`, which is an open immersion whenever
   `S` is finitely generated, and composites to `F.orbitHom R : Spec R[F.faceSubgroup] ⟶ Spec R[S]`.
   Over *any* commutative ring `R`, the Zariski closure of `Set.range (F.orbitHom R)` equals
   `Set.range (F.closedFaceHom R) = PrimeSpectrum.zeroLocus (F.toAddSubmonoid.faceIdeal R)`. In
   particular, the diagonalizable-group morphism `S.torusHom R : Spec R[AddSubgroup.closure S] ⟶
   Spec R[S]` has dense image over every commutative ring `R` and is an open immersion when `S.FG`
   (and a split-torus immersion when `AddSubgroup.closure S` is finite-rank free abelian).
3. **Closure order on orbits.** Over any nontrivial commutative ring `R` and any abelian group `G`,
   for any faces `F₁, F₂` of `S`,
   `Set.range (F₁.orbitHom R) ⊆ closure (Set.range (F₂.orbitHom R)) ↔ F₁ ≤ F₂`
   (matching the exponent-semigroup face order, dual to the fan cone order).

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
noncomputable def orbitOpenHom :
    Spec (.of (AddMonoidAlgebra R F.faceSubgroup)) ⟶ Spec (.of (AddMonoidAlgebra R F)) :=
  Spec.map (CommRingCat.ofHom (mapDomainRingHom R F.toFaceSubgroup))

/-- Explicit definition of `SaturatedAddSubmonoid.orbitOpenHom`. -/
theorem orbitOpenHom_def :
    F.orbitOpenHom R = Spec.map (CommRingCat.ofHom (mapDomainRingHom R F.toFaceSubgroup)) :=
  (rfl)

/-- When `S` is finitely generated, `F.orbitOpenHom R : Spec R[F.faceSubgroup] ⟶ Spec R[F]` is an
open immersion over any commutative ring `R`. -/
theorem isOpenImmersion_orbitOpenHom (hS : S.FG) : IsOpenImmersion (F.orbitOpenHom R) := by
  let := (mapDomainRingHom R F.toFaceSubgroup).toAlgebra
  obtain ⟨u, _⟩ := F.exists_isLocalization_away_faceSubgroup hS R
  exact IsOpenImmersion.of_isLocalization (single u (1 : R))

/-- The orbit morphism `Spec R[F.faceSubgroup] ⟶ Spec R[S]` induced by `F.orbitMap R` (which is a
locally closed immersion when `S.FG`, factoring through the open immersion
`isOpenImmersion_orbitOpenHom` and the closed immersion `closedFaceHom`). -/
noncomputable def orbitHom :
    Spec (.of (AddMonoidAlgebra R F.faceSubgroup)) ⟶ Spec (.of (AddMonoidAlgebra R S)) :=
  Spec.map (CommRingCat.ofHom (F.orbitMap R).toRingHom)

/-- Explicit definition of `SaturatedAddSubmonoid.orbitHom`. -/
theorem orbitHom_def :
    F.orbitHom R = Spec.map (CommRingCat.ofHom (F.orbitMap R).toRingHom) :=
  (rfl)

/-- `F.orbitHom R` factors as `F.orbitOpenHom R` followed by `F.closedFaceHom R`. -/
@[reassoc (attr := simp)]
theorem orbitOpenHom_comp_closedFaceHom :
    F.orbitOpenHom R ≫ F.closedFaceHom R = F.orbitHom R := by
  rw [orbitOpenHom, closedFaceHom, orbitHom, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    F.orbitMap_def R]
  congr 2

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
    (F₂.toAddSubmonoid.faceIdeal R)).trans ?_
  refine ⟨fun h s hs₁ ↦ by_contra fun hs₂ ↦ ?_, fun h ↦ ?_⟩
  · have hmem : single s (1 : R) ∈ (F₁.toAddSubmonoid.faceIdeal R).radical :=
      h ((F₂.toAddSubmonoid.single_mem_faceIdeal_iff F₂.addSaturated s 1).2 (Or.inr hs₂))
    obtain ⟨n, hn⟩ := hmem
    have hpow : (single s (1 : R)) ^ n = single (n • s) (1 : R) := by rw [single_pow, one_pow]
    rw [hpow, F₁.toAddSubmonoid.single_mem_faceIdeal_iff F₁.addSaturated] at hn
    rcases hn with h0 | hnot
    · exact one_ne_zero h0
    · exact hnot (nsmul_mem hs₁ n)
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
noncomputable def torusHom :
    Spec (.of (AddMonoidAlgebra R (AddSubgroup.closure (S : Set G)))) ⟶
      Spec (.of (AddMonoidAlgebra R S)) :=
  Spec.map (CommRingCat.ofHom (mapDomainRingHom R S.toGroupClosure))

/-- Explicit definition of `AddSubmonoid.torusHom`. -/
theorem torusHom_def :
    S.torusHom R = Spec.map (CommRingCat.ofHom (mapDomainRingHom R S.toGroupClosure)) :=
  (rfl)

/-- When `S` is finitely generated, `S.torusHom R` is an open immersion of schemes. -/
theorem isOpenImmersion_torusHom (hS : S.FG) : IsOpenImmersion (S.torusHom R) := by
  let := (mapDomainRingHom R S.toGroupClosure).toAlgebra
  obtain ⟨s, _⟩ := hS.exists_isLocalization_away_addMonoidAlgebra_groupClosure R
  exact IsOpenImmersion.of_isLocalization (single s (1 : R))

/-- Over every commutative ring `R`, the diagonalizable group scheme
`Spec R[AddSubgroup.closure S]` has dense image in `Spec R[S]`. -/
theorem denseRange_torusHom : DenseRange (S.torusHom R) := by
  -- `Spec.map (CommRingCat.ofHom f)` has underlying map `PrimeSpectrum.comap f` (`Spec.map_apply`).
  refine (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical
    (f := mapDomainRingHom R S.toGroupClosure)).2 fun p hp ↦ ?_
  have hp0 : p = 0 := mapDomain_injective S.toGroupClosure_injective (by
    rw [← mapDomainRingHom_apply R S.toGroupClosure, RingHom.mem_ker.1 hp, mapDomain_zero])
  exact hp0 ▸ zero_mem _

end AddSubmonoid
