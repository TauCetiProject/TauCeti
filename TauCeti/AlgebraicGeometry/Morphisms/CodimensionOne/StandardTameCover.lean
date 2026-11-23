/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Morphisms.CodimensionOne.Ramification
public import TauCeti.RingTheory.AdjoinRoot.StandardTameCover.Basic

import TauCeti.AlgebraicGeometry.ResidueField
import TauCeti.AlgebraicGeometry.Scheme.DiscreteValuationStalk
import TauCeti.AlgebraicGeometry.Scheme.StalkSpecializes
import TauCeti.RingTheory.AdjoinRoot.Basic
import TauCeti.RingTheory.DiscreteValuationRing.Kummer.Basic
import TauCeti.RingTheory.DiscreteValuationRing.MinimalPrime

/-!
# Standard covers are tamely ramified in codimension one

Let `f` be a nonzerodivisor in a Noetherian ring `A` with `A/(f)` reduced. Adjoining
an `e`-th root of `f` for an exponent invertible in `A` gives a cover of
`D(f)` that is tamely ramified in codimension one over `Spec A`.

* [Stacks Project, Example 58.31.4](https://stacks.math.columbia.edu/tag/0EYF).
-/

public section

open CategoryTheory AlgebraicGeometry Polynomial IntermediateField

namespace TauCeti.AlgebraicGeometry

universe u

variable {A : Type u} [CommRing A]

/-- If `f` is a nonzerodivisor with reduced principal quotient and `e` is invertible in `A`,
the standard root cover restricted to `D(f)` is tamely ramified over `Spec A` in codimension
one. -/
@[stacks 0EYF "tameness in codimension one"]
theorem standardTameCover_isTamelyRamifiedInCodimOne [IsNoetherianRing A]
    {f : A} (hf : f ∈ nonZeroDivisors A) [IsReduced (A ⧸ Ideal.span {f})]
    {e : ℕ} (heunit : IsUnit (e : A)) :
    (Spec.map (CommRingCat.ofHom (algebraMap A (standardTameCover A f e))) ∣_
      PrimeSpectrum.basicOpen f).IsTamelyRamifiedInCodimOne := by
  let S := Spec (.of A)
  let p := Spec.map (CommRingCat.ofHom (algebraMap A (standardTameCover A f e)))
  let U : S.Opens := PrimeSpectrum.basicOpen f
  refine (Scheme.Hom.isTamelyRamifiedInCodimOne_def (p ∣_ U)).mpr ?_
  intro ξ hξ y sp
  let q := (p ∣_ U) ≫ U.ι
  let g := (p ⁻¹ᵁ U).ι
  have hq : g ≫ p = q := (morphismRestrict_ι p U).symm
  let R := S.presheaf.stalk ξ
  let : Algebra A R := StructureSheaf.stalkAlgebra A ξ.val
  have : (ξ : Spec (.of A)).asIdeal.IsPrime := ξ.val.isPrime
  have : IsLocalization.AtPrime R ξ.val.asIdeal := StructureSheaf.IsLocalization.to_stalk A ξ.val
  have hmin : ξ.val.asIdeal ∈ (Ideal.span {f}).minimalPrimes :=
    Ideal.mem_minimalPrimes_of_height_le ((Ideal.span_singleton_le_iff_mem _).2 (not_not.mp hξ))
      (by rw [(idealHeight_eq_coheight (.of A) ξ).trans ξ.property]
          exact Ideal.one_le_height_span_singleton_of_mem_nonZeroDivisors hf)
  have : IsRegularLocalRing R := isRegularLocalRing_of_mem_minimalPrimes R hf hmin
  have : IsDiscreteValuationRing R := CodimensionOnePoint.isDiscreteValuationRing_stalk ξ
  let K := S.residueField (q y)
  let L := (p ⁻¹ᵁ U : Scheme).residueField y
  let : Algebra R K := (S.presheaf.stalkSpecializes sp ≫ S.residue _).hom.toAlgebra
  let : Algebra K L := (q.residueFieldMap y).hom.toAlgebra
  let : Algebra R L :=
    (S.presheaf.stalkSpecializes sp ≫ S.residue _ ≫ q.residueFieldMap y).hom.toAlgebra
  have : IsScalarTower R K L := .of_algebraMap_eq fun _ ↦ by
    simp only [RingHom.algebraMap_toAlgebra, CommRingCat.hom_comp, RingHom.comp_apply]
  have hne : q y ≠ ξ := fun eq ↦ hξ (eq ▸ ((p ∣_ U) y).property)
  have : IsFractionRing R K := Scheme.isFractionRing_residueField_of_specializes sp hne
  let φ := ((Scheme.ΓSpecIso _).inv ≫ (Spec _).Γevaluation (g y) ≫ g.residueFieldMap y).hom
  have hα : φ (AdjoinRoot.root (X ^ e - C f)) ^ e = algebraMap R L (algebraMap A R f) := by
    rw [← map_pow, AdjoinRoot.root_X_pow_sub_C_pow, ← AdjoinRoot.algebraMap_eq]
    have hmap := g.Γevaluation_naturality_of_Spec _ hq y
    have hs := StructureSheaf.toStalk_stalkSpecializes_assoc sp (S.residue _ ≫ q.residueFieldMap y)
    simp only [StructureSheaf.toStalk] at hs
    simp only [Scheme.Γevaluation, Scheme.ΓSpecIso_inv] at hmap
    have hvalue := congrArg (fun t : CommRingCat.of A ⟶ CommRingCat.of L ↦ t f)
      (hmap.trans hs.symm)
    rw [CommRingCat.comp_apply] at hvalue
    simp only [φ, RingHom.algebraMap_toAlgebra, Scheme.ΓSpecIso_inv,
      show algebraMap A R = (StructureSheaf.toStalk A ξ.val).hom from
        RingHom.algebraMap_toAlgebra _, StructureSheaf.toStalk]
    -- Identify the scheme presheaf with the affine structure sheaf in the specialization map.
    convert hvalue using 1; rfl
  have hgen : K⟮φ (AdjoinRoot.root (X ^ e - C f))⟯ = ⊤ := by
    simpa only [Set.image_singleton] using
      g.adjoin_residueField_eq_top_of_isIso_residueFieldMap hq y
        (AdjoinRoot.adjoinRoot_eq_top (f := X ^ e - C f))
  exact (IsDiscreteValuationRing.isTamelyRamifiedWRT_iff_of_pow_eq_of_irreducible
    (irreducible_algebraMap_of_mem_minimalPrimes R hf hmin) hα hgen).mpr <| by
      simpa only [map_natCast] using
        (heunit.map (algebraMap A R)).map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R))

end TauCeti.AlgebraicGeometry
