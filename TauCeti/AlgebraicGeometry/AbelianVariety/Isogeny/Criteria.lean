/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.AlgebraicGeometry.AbelianVariety.Isogeny.Basic
public import TauCeti.AlgebraicGeometry.GroupScheme.Kernel.Finite
import TauCeti.AlgebraicGeometry.Morphisms.LocallyQuasiFinite
import TauCeti.AlgebraicGeometry.Scheme.KrullDimension

/-!
# Isogeny criteria over a field

A finite homomorphism of abelian varieties of the same dimension is an isogeny. The finiteness
criterion for proper homomorphisms then tests for an isogeny by the scheme-theoretic kernel.
For a composite of homomorphisms, if the first source and target have the same dimension, the
composite is an isogeny exactly when both factors are. These criteria apply over any field.

## References

* J. S. Milne, *Abelian Varieties*, §8, Proposition 8.1.
-/

public section

open CategoryTheory Limits AlgebraicGeometry

namespace TauCeti.AlgebraicGeometry.AbelianVariety

universe u

variable {K : Type u} [Field K] {A B C : AbelianVariety K}

/-- The source and target of an isogeny have the same dimension. -/
theorem IsIsogeny.dim_eq {f : A ⟶ B} (hf : IsIsogeny f) : A.dim = B.dim := by
  have := hf.isFinite
  have := hf.surjective
  exact (Hom.toSchemeHom f).topologicalKrullDim_eq_of_isClosedMap_of_surjective
    (Hom.toSchemeHom f).isClosedMap

/-- A homomorphism between abelian varieties of the same dimension is an isogeny if its
underlying scheme morphism is finite. -/
theorem isIsogeny_of_isFinite (f : A ⟶ B) [IsFinite (Hom.toSchemeHom f)]
    (hdim : A.dim = B.dim) : IsIsogeny f := by
  have : CompactSpace B.toScheme := QuasiCompact.compactSpace_of_compactSpace B.toOver.hom
  exact (isIsogeny_iff f).mpr ⟨inferInstance,
    (Hom.toSchemeHom f).surjective_of_isClosed_range_of_topologicalKrullDim_le
      (Hom.toSchemeHom f).isClosedMap.isClosed_range
      (topologicalKrullDim_ne_top_of_locallyOfFiniteType B.toOver.hom) hdim.ge⟩

/-- A homomorphism of abelian varieties is an isogeny exactly when the dimensions agree and
its scheme-theoretic kernel is finite over the base field. -/
theorem isIsogeny_iff_dim_eq_and_isFinite_kernel (f : A ⟶ B) :
    IsIsogeny f ↔ A.dim = B.dim ∧ IsFinite (kernel (Hom.homMulEquiv A B f)).X.hom := by
  let g := Hom.homMulEquiv A B f
  have hg : g.hom.hom.left = Hom.toSchemeHom f := by
    simp only [g, Hom.homMulEquiv_apply, Hom.toSchemeHom, toOverHom_eq_forget₂Grp_map,
      CommGrp.forget₂Grp_map_hom]
  have hproper : IsProper g.hom.hom.left := hg.symm ▸
    (IsProper.comp_iff (g := B.toOver.hom)).mp ((Hom.toSchemeHom_comp_hom f).symm ▸ A.isProper)
  have hfin := Grp.isFinite_iff_isFinite_kernel g
  rw [hg] at hfin
  exact ⟨fun hf ↦ ⟨hf.dim_eq, hfin.mp hf.isFinite⟩, fun ⟨hdim, hk⟩ ↦
    have := hfin.mpr hk
    isIsogeny_of_isFinite f hdim⟩

/-- If the intermediate abelian variety has the same dimension as the source, a composite
is an isogeny exactly when both factors are isogenies. -/
theorem isIsogeny_comp_iff (f : A ⟶ B) (g : B ⟶ C) (hdim : A.dim = B.dim) :
    IsIsogeny (f ≫ g) ↔ IsIsogeny f ∧ IsIsogeny g := by
  refine ⟨fun hfg ↦ ?_, fun ⟨hf, hg⟩ ↦ hf.comp hg⟩
  have hcomp := hfg.isFinite
  rw [Hom.toSchemeHom_comp] at hcomp
  have : IsProper (Hom.toSchemeHom g) :=
    (IsProper.comp_iff (g := C.toOver.hom)).mp ((Hom.toSchemeHom_comp_hom g).symm ▸ B.isProper)
  have : IsFinite (Hom.toSchemeHom f) := IsFinite.of_comp _ (Hom.toSchemeHom g)
  have hf := isIsogeny_of_isFinite f hdim
  have := hf.surjective
  have : LocallyQuasiFinite (Hom.toSchemeHom g) :=
    LocallyQuasiFinite.of_comp_surjective (Hom.toSchemeHom f) (Hom.toSchemeHom g)
  have : IsFinite (Hom.toSchemeHom g) := IsFinite.of_isProper_of_locallyQuasiFinite _
  have hsurj := hfg.surjective
  rw [Hom.toSchemeHom_comp] at hsurj
  exact ⟨hf, (isIsogeny_iff g).mpr ⟨inferInstance, Surjective.of_comp (Hom.toSchemeHom f) _⟩⟩

end TauCeti.AlgebraicGeometry.AbelianVariety
