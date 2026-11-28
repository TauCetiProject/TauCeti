/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
public import TauCeti.AlgebraicGeometry.AbelianVariety.Isogeny
public import TauCeti.AlgebraicGeometry.GroupScheme.Kernel
public import TauCeti.AlgebraicGeometry.Morphisms.Dominant
import TauCeti.AlgebraicGeometry.AbelianVariety.DimensionZero
import TauCeti.AlgebraicGeometry.AbelianVariety.FaithfullyFlat
import TauCeti.AlgebraicGeometry.Descent.MorphismProperty
import TauCeti.AlgebraicGeometry.GroupScheme.Rank
import TauCeti.AlgebraicGeometry.Morphisms.Finite.Flat.Degree
import TauCeti.AlgebraicGeometry.Morphisms.Flat.Basic
import TauCeti.AlgebraicGeometry.Morphisms.Flat.Descent
import TauCeti.AlgebraicGeometry.Morphisms.Flat.Rank
import TauCeti.CategoryTheory.Comma.Over

/-!
# Degrees of homomorphisms of abelian varieties

The degree of an isogeny is its rank at the identity of the target. This rank is constant and
equals both the rank of the scheme-theoretic kernel and the degree of the induced extension of
function fields, including its inseparable part.
We extend the degree to all homomorphisms by assigning degree zero to non-isogenies.

The resulting degree is multiplicative on isogenies and invariant under field extension.
On endomorphisms, the identity and inversion have degree one. The zero endomorphism has degree
zero in positive dimension and one in dimension zero.

## References

* J. S. Milne, [*Abelian Varieties*, §8](https://www.jmilne.org/math/xnotes/AVs.pdf#page=12).
* J. S. Milne, [*Abelian Varieties*, course notes, §10](https://www.jmilne.org/math/CourseNotes/AV.pdf#page=52).
-/

public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace TauCeti.AlgebraicGeometry.AbelianVariety

universe u

variable {K : Type u} [Field K] {A B C : AbelianVariety K}

/-- The degree of a homomorphism of abelian varieties. For an isogeny this is the rank
of its underlying finite flat morphism at the identity of the target. For every other
homomorphism the degree is zero. -/
noncomputable def deg (f : A ⟶ B) : ℕ := by
  classical
  exact if IsIsogeny f then (Hom.toSchemeHom f).finrank B.zeroPoint else 0

/-- The degree of an isogeny is the degree of the function field of the source over the
image of the pullback of rational functions from the target. -/
theorem deg_eq_finrank_fieldRange_functionFieldMap
    {f : A ⟶ B} (hf : IsIsogeny f) :
    letI := hf.surjective
    deg f = Module.finrank (Hom.toSchemeHom f).functionFieldMap.hom.fieldRange
      A.toScheme.functionField := by
  have := hf.surjective
  have := hf.isFinite
  have := hf.flat
  rw [deg, ite_eq_left hf]
  exact (Hom.toSchemeHom f).finrank_eq_finrank_fieldRange_functionFieldMap B.zeroPoint

/-- The degree of an isogeny equals its rank at every point of the target. -/
theorem deg_eq_finrank {f : A ⟶ B} (hf : IsIsogeny f) (b : B.toScheme) :
    deg f = (Hom.toSchemeHom f).finrank b := by
  have := hf.surjective
  have := hf.isFinite
  have := hf.flat
  exact (deg_eq_finrank_fieldRange_functionFieldMap hf).trans
    ((Hom.toSchemeHom f).finrank_eq_finrank_fieldRange_functionFieldMap b).symm

/-- The degree of an isogeny is the rank of its scheme-theoretic kernel over the base field. -/
theorem deg_eq_finrank_kernel {f : A ⟶ B} (hf : IsIsogeny f) :
    deg f = (kernel ((CommGrp.forget₂Grp _).map f.hom)).X.hom.finrank
      (IsLocalRing.closedPoint K) := by
  have h := (isIsogeny_iff_groupScheme_isIsogeny f).mp hf
  have := h.isFinite
  have := h.flat
  rw [deg_eq_finrank hf B.zeroPoint, B.zeroPoint_def]
  exact (GroupScheme.finrank_kernel_hom ((CommGrp.forget₂Grp _).map f.hom) _).symm

/-- The degree of an isogeny is positive. -/
theorem deg_pos {f : A ⟶ B} (hf : IsIsogeny f) : 0 < deg f := by
  have := hf.isFinite
  have := hf.flat
  rw [deg_eq_finrank hf ((Hom.toSchemeHom f) A.zeroPoint)]
  exact (Hom.toSchemeHom f).one_le_finrank_map A.zeroPoint

/-- A homomorphism has degree zero exactly when it is not an isogeny. -/
@[simp]
theorem deg_eq_zero_iff (f : A ⟶ B) : deg f = 0 ↔ ¬ IsIsogeny f :=
  ⟨fun h hf ↦ (deg_pos hf).ne' h, fun hf ↦ by rw [deg, ite_eq_right hf]⟩

/-- The degree of a composite of isogenies is the product of their degrees. -/
theorem deg_comp_of_isIsogeny {f : A ⟶ B} {g : B ⟶ C} (hf : IsIsogeny f) (hg : IsIsogeny g) :
    deg (f ≫ g) = deg f * deg g := by
  have := hf.isFinite
  have := hf.flat
  have := hg.isFinite
  have := hg.flat
  rw [deg_eq_finrank (hf.comp hg) C.zeroPoint, Hom.toSchemeHom_comp,
    deg_eq_finrank hg C.zeroPoint]
  exact (Hom.toSchemeHom f).finrank_comp_of_fiber (Hom.toSchemeHom g)
    (fun b _ ↦ (deg_eq_finrank hf b).symm)

/-- An isomorphism of abelian varieties has degree one. -/
@[simp]
theorem deg_eq_one_of_isIso (f : A ⟶ B) [IsIso f] : deg f = 1 := by
  have : IsIso (Hom.toSchemeHom f) := by
    have h : IsIso (isoToScheme (asIso f)).hom := inferInstance
    rwa [isoToScheme_hom] at h
  rw [deg_eq_finrank (isIsogeny_of_isIso f) B.zeroPoint, Scheme.Hom.finrank_eq_one_of_isIso]
  rfl

open scoped Hom in
/-- The zero endomorphism, written as the unit of the pointwise group law, has degree one in
dimension zero and degree zero otherwise. -/
@[simp]
theorem deg_one (A : AbelianVariety K) :
    deg (1 : A ⟶ A) = if A.dim = 0 then 1 else 0 := by
  rw [← mulBy_zero]
  split_ifs with h
  · rw [mulBy_eq_id_of_dim_eq_zero h, deg_eq_one_of_isIso]
  · exact (deg_eq_zero_iff _).mpr (fun hf ↦ h ((isIsogeny_mulBy_zero_iff A).mp hf))

open scoped Hom in
/-- Inversion has degree one. -/
@[simp]
theorem deg_inv_id (A : AbelianVariety K) : deg ((𝟙 A)⁻¹) = 1 := by
  rw [← mulBy_one A, ← mulBy_neg]
  have h := deg_comp_of_isIsogeny (isIsogeny_mulBy_neg_one A) (isIsogeny_mulBy_neg_one A)
  rw [← mulBy_mul, neg_mul_neg, one_mul, mulBy_one, deg_eq_one_of_isIso] at h
  exact Nat.eq_one_of_mul_eq_one_right h.symm

/-- The degree of a homomorphism of abelian varieties is unchanged by any extension of the
ground field. -/
@[simp]
theorem deg_baseChange (f : A ⟶ B) (L : Type u) [Field L] [Algebra K L] :
    deg (Hom.baseChange f L) = deg f := by
  let p := Spec.map (CommRingCat.ofHom (algebraMap K L))
  let g := ((Over.pullback p).map (Hom.toOverHom f)).left
  let eA := eqToIso (congrArg Over.left (AbelianVariety.baseChange_toOver A L))
  let eB := eqToIso (congrArg Over.left (AbelianVariety.baseChange_toOver B L))
  have hpb := Over.isPullback_pullback_map_left p (Hom.toOverHom f)
  have h : Hom.toSchemeHom (Hom.baseChange f L) = eA.hom ≫ g ≫ eB.inv := by
    rw [Hom.toSchemeHom_baseChange]
    simp only [Over.comp_left, Over.eqToHom_left, eA, eB, eqToIso.hom, eqToIso.inv, g, p]
  -- Finiteness and surjectivity descend along the pullback of the field extension.
  have hdesc (hf : IsIsogeny (Hom.baseChange f L)) : IsIsogeny f := by
    let P : MorphismProperty Scheme.{u} := @IsFinite ⊓ @Surjective
    have : P.RespectsIso := MorphismProperty.RespectsIso.inf _ _
    have : P.DescendsAlong (@Surjective ⊓ @Flat ⊓ @QuasiCompact) :=
      MorphismProperty.DescendsAlong.inf (P := @IsFinite) (W := @Surjective)
    have hg : P (Hom.toSchemeHom (Hom.baseChange f L)) := (isIsogeny_iff _).mp hf
    rw [h, P.cancel_left_of_respectsIso, P.cancel_right_of_respectsIso] at hg
    exact (isIsogeny_iff f).mpr
      (MorphismProperty.of_isPullback_of_surjective_of_flat_of_quasiCompact hpb hg)
  by_cases hf : IsIsogeny f
  · have := hf.isFinite
    have := hf.flat
    have : IsFinite g := MorphismProperty.of_isPullback hpb.flip hf.isFinite
    have : Flat g := MorphismProperty.of_isPullback hpb.flip hf.flat
    let b := eB.hom (B.baseChange L).zeroPoint
    rw [deg_eq_finrank (hf.baseChange L) (eB.inv b), h, Scheme.Hom.finrank_comp_left_of_isIso,
      Scheme.Hom.finrank_comp_right_of_isIso,
      Scheme.Hom.finrank_of_isPullback _ _ _ _ hpb.flip]
    exact (deg_eq_finrank hf _).symm
  · rw [(deg_eq_zero_iff _).mpr (hf ∘ hdesc), (deg_eq_zero_iff _).mpr hf]

end TauCeti.AlgebraicGeometry.AbelianVariety
