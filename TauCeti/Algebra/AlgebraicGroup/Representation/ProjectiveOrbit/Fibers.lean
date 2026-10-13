/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Representation.ProjectiveOrbit.ChartFibers
public import TauCeti.Algebra.AlgebraicGroup.Representation.ProjectiveOrbit.LocalFibers
import TauCeti.LinearAlgebra.Unimodular
import Mathlib.RingTheory.LocalProperties.Basic

/-!
# Fibers of projective orbit morphisms

Two algebra-valued group points have the same image under a projective orbit morphism
exactly when their matrix coefficients at the chosen vector differ by one *global* unit
of the value algebra. Combined with Chevalley's coset criterion, which detects the left
cosets of a closed subgroup by exactly this unit proportionality, the fibers of the orbit
map of a Chevalley line are the left cosets of the subgroup. This is the fiber half of the
comparison between the projective orbit and the homogeneous quotient.

Equality of scheme morphisms is local, so the chart criterion only gives unit
proportionality locally. The local proportionality says that all `2 × 2` minors of the
two coordinate families vanish, which is a condition on the value algebra itself; two
coordinate families generating the unit ideal with vanishing minors are unit multiples of
one another (`TauCeti.forall_mul_eq_mul_iff_exists_units`). The value algebra may be
nonreduced, and no field hypothesis is imposed on the base ring.

## Main declarations

* `Comodule.SpecMap_projectiveOrbitMap_preimage_basicOpen_ι`: the pullback of a standard
  chart along an algebra-valued orbit map is the principal open of the evaluated matrix
  coefficient.
* `Comodule.projectiveOrbitMap_SpecMap_eq_iff_exists_units_matrixCoefficient`: equality of
  algebra-valued orbit maps is global unit proportionality of matrix coefficients.

## References

* J. S. Milne, *Algebraic Groups* (2017), §§7.d–7.f.
-/

public section

open CategoryTheory AlgebraicGeometry

namespace TauCeti.Comodule

universe u

variable {R H M A : Type u} [CommRing R] [CommRing H] [HopfAlgebra R H]
  [AddCommMonoid M] [Module R M] [Comodule R H M]
  [Module.Finite R M] [Module.Projective R M] [CommRing A] [Algebra R A]

/-- The standard chart of a linear coordinate pulls back along an algebra-valued orbit map
to the principal open of the evaluated matrix coefficient. -/
theorem SpecMap_projectiveOrbitMap_preimage_basicOpen_ι (m : M)
    (hm : Module.IsUnimodular R m) (g : H →ₐ[R] A) (φ : Module.Dual R M) :
    (Spec.map (CommRingCat.ofHom g.toRingHom) ≫ projectiveOrbitMap (H := H) m hm) ⁻¹ᵁ
        Proj.basicOpen _ (SymmetricAlgebra.ι R (Module.Dual R M) φ) =
      (Spec (.of A)).basicOpen ((Scheme.ΓSpecIso (.of A)).inv
        (g (matrixCoefficient (C := H) φ m))) := by
  rw [Scheme.Hom.comp_preimage, projectiveOrbitMap_preimage_basicOpen_ι,
    Scheme.preimage_basicOpen]
  congr 1
  exact congrArg (fun e : CommRingCat.of H ⟶ Γ(Spec (.of A), ⊤) ↦
    e.hom (matrixCoefficient (C := H) φ m))
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom g.toRingHom)).symm

/-- Over a local value ring, algebra-valued orbit maps with the same image agree on which
evaluated matrix coefficients are units: both conditions say that the closed point maps into
the same standard chart. -/
private theorem isUnit_of_SpecMap_projectiveOrbitMap_eq [IsLocalRing A] (m : M)
    (hm : Module.IsUnimodular R m) {g h : H →ₐ[R] A}
    (heq : Spec.map (CommRingCat.ofHom g.toRingHom) ≫ projectiveOrbitMap (H := H) m hm =
      Spec.map (CommRingCat.ofHom h.toRingHom) ≫ projectiveOrbitMap (H := H) m hm)
    {φ : Module.Dual R M} (hg : IsUnit (g (matrixCoefficient (C := H) φ m))) :
    IsUnit (h (matrixCoefficient (C := H) φ m)) := by
  have hopen := SpecMap_projectiveOrbitMap_preimage_basicOpen_ι m hm h φ
  rw [← heq, SpecMap_projectiveOrbitMap_preimage_basicOpen_ι, basicOpen_eq_of_affine,
    basicOpen_eq_of_affine] at hopen
  have hmem : IsLocalRing.closedPoint A ∈ PrimeSpectrum.basicOpen
      (g (matrixCoefficient (C := H) φ m)) :=
    (PrimeSpectrum.mem_basicOpen _ _).mpr ((IsLocalRing.notMem_maximalIdeal).mpr hg)
  rw [hopen, PrimeSpectrum.mem_basicOpen] at hmem
  exact IsLocalRing.notMem_maximalIdeal.mp hmem

/-- **Fibers of algebra-valued orbit maps.** Two algebra-valued group points have the same
image in projective space exactly when their matrix coefficients at the chosen vector differ
by one global unit of the value algebra. The value algebra may be nonreduced. -/
theorem projectiveOrbitMap_SpecMap_eq_iff_exists_units_matrixCoefficient (m : M)
    (hm : Module.IsUnimodular R m) (g h : H →ₐ[R] A) :
    Spec.map (CommRingCat.ofHom g.toRingHom) ≫ projectiveOrbitMap (H := H) m hm =
        Spec.map (CommRingCat.ofHom h.toRingHom) ≫ projectiveOrbitMap (H := H) m hm ↔
      ∃ c : Aˣ, ∀ φ : Module.Dual R M,
        h (matrixCoefficient (C := H) φ m) = c * g (matrixCoefficient (C := H) φ m) := by
  have hspan {B : Type u} [CommRing B] [Algebra R B] (q : H →ₐ[R] B) :
      Ideal.span (Set.range fun φ : Module.Dual R M ↦ q (matrixCoefficient (C := H) φ m)) = ⊤ := by
    have himage : (Set.range fun φ : Module.Dual R M ↦ q (matrixCoefficient (C := H) φ m)) =
        q '' Set.range fun φ : Module.Dual R M ↦ matrixCoefficient (C := H) φ m := by
      rw [← Set.range_comp]
      rfl
    rw [himage, ← Ideal.map_span, (span_matrixCoefficient_eq_top_iff_isUnimodular m).mpr hm,
      Ideal.map_top]
  rw [← forall_mul_eq_mul_iff_exists_units (hspan g) (hspan h)]
  constructor
  · intro heq φ ψ
    rw [← sub_eq_zero]
    refine eq_zero_of_localization _ fun J hJ ↦ ?_
    -- Over each local ring of `A`, some coordinate is a unit and the chart criterion applies.
    let L := Localization.AtPrime J
    let ι : A →ₐ[R] L := IsScalarTower.toAlgHom R A L
    have heqL : Spec.map (CommRingCat.ofHom (ι.comp g).toRingHom) ≫
          projectiveOrbitMap (H := H) m hm =
        Spec.map (CommRingCat.ofHom (ι.comp h).toRingHom) ≫
          projectiveOrbitMap (H := H) m hm := by
      have hcomp (q : H →ₐ[R] A) : CommRingCat.ofHom (ι.comp q).toRingHom =
          CommRingCat.ofHom q.toRingHom ≫ CommRingCat.ofHom ι.toRingHom := rfl
      rw [hcomp, hcomp, Spec.map_comp, Spec.map_comp, Category.assoc, Category.assoc, heq]
    obtain ⟨t, ht⟩ : ∃ t : Module.Dual R M,
        IsUnit ((ι.comp g) (matrixCoefficient (C := H) t m)) := by
      by_contra hne
      push Not at hne
      refine (IsLocalRing.maximalIdeal.isMaximal L).ne_top (top_le_iff.mp ?_)
      rw [← hspan (ι.comp g), Ideal.span_le]
      rintro _ ⟨t, rfl⟩
      exact (IsLocalRing.mem_maximalIdeal _).mpr (hne t)
    obtain ⟨c, hc⟩ := (projectiveOrbitMap_SpecMap_eq_iff_exists_unit m hm _ _ t ht
      (isUnit_of_SpecMap_projectiveOrbitMap_eq m hm heqL ht)).mp heqL
    have hφ := hc φ
    have hψ := hc ψ
    simp only [AlgHom.comp_apply, ι, IsScalarTower.coe_toAlgHom'] at hφ hψ
    rw [map_sub, map_mul, map_mul, hφ, hψ]
    ring
  · intro hminor
    obtain ⟨c, hc⟩ := (forall_mul_eq_mul_iff_exists_units (hspan g) (hspan h)).mp hminor
    -- A global unit restricts to every member of the trivial cover.
    let 𝒰 : (Spec (.of A)).OpenCover := Scheme.coverOfIsIso (𝟙 (Spec (.of A)))
    refine (projectiveOrbitMap_SpecMap_eq_iff_exists_affineOpenCover_unit m hm g h).mpr
      ⟨𝒰, fun _ ↦ inferInstanceAs (IsAffine (Spec _)), fun i ↦
        ⟨Units.map ((𝒰.f i).appTop.hom.comp (Scheme.ΓSpecIso (.of A)).inv.hom).toMonoidHom c,
          fun φ ↦ ?_⟩⟩
    simp [hc φ]

end TauCeti.Comodule
