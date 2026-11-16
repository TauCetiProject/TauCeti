/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Jie Xu, Shitan Xu
-/
module

public import TauCeti.AlgebraicGeometry.AffineScheme
public import TauCeti.RingTheory.Norm.Projective
public import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-!
# Basic opens defined by norms

For a finite morphism of schemes, on an affine open where the algebra of sections is
projective, the norm of a section is nonvanishing exactly on the fibres where the section
never vanishes. The norm open is the complement, within the affine open, of the image of
the section's vanishing locus.

Both formulas use the finite projective norm and do not require a basis.

## References

* The Stacks Project, Tag 0BIF, norms of finite locally free algebras.
-/

public section

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Hom

universe u

/-- The norm of a section is nonvanishing precisely on fibres where the section never
vanishes. -/
theorem mem_basicOpen_projectiveNorm_iff {X Y : Scheme.{u}} (f : Y ⟶ X) [IsFinite f]
    {U : X.Opens} (hU : IsAffineOpen U)
    (hproj : letI := (f.app U).hom.toAlgebra; Module.Projective Γ(X, U) Γ(Y, f ⁻¹ᵁ U))
    (s : Γ(Y, f ⁻¹ᵁ U)) {x : X} (hx : x ∈ U) :
    letI := (f.app U).hom.toAlgebra
    letI : Module.Finite Γ(X, U) Γ(Y, f ⁻¹ᵁ U) := f.finite_app U hU
    letI := hproj
    x ∈ X.basicOpen (Algebra.projectiveNorm Γ(X, U) s) ↔
      ∀ y, f y = x → y ∈ Y.basicOpen s := by
  let := (f.app U).hom.toAlgebra
  let : Module.Finite Γ(X, U) Γ(Y, f ⁻¹ᵁ U) := f.finite_app U hU
  let := hproj
  have hV : IsAffineOpen (f ⁻¹ᵁ U) := hU.preimage f
  let p := hU.primeIdealOf ⟨x, hx⟩
  have hnorm := not_congr (Algebra.projectiveNorm_mem_iff (p := p.asIdeal) (x := s))
  rw [hU.mem_basicOpen_iff_notMem_primeIdealOf ⟨x, hx⟩]
  refine hnorm.trans ⟨?_, ?_⟩
  · intro h y hy
    have hyU : y ∈ f ⁻¹ᵁ U := (Scheme.Hom.mem_preimage (f := f)).mpr (hy.symm ▸ hx)
    rw [hV.mem_basicOpen_iff_notMem_primeIdealOf ⟨y, hyU⟩]
    intro hs
    apply h
    refine ⟨(hV.primeIdealOf ⟨y, hyU⟩).asIdeal, ⟨inferInstance, ⟨?_⟩⟩, hs⟩
    have hcomap := IsAffineOpen.comap_primeIdealOf_appLE U hU (f ⁻¹ᵁ U) hV le_rfl hyU
    have hcomap' : (hV.primeIdealOf ⟨y, hyU⟩).comap (f.app U).hom = p := by
      convert! hcomap using 1
      · rw [Scheme.Hom.app_eq_appLE]
      · exact congrArg hU.primeIdealOf (Subtype.ext hy.symm)
    exact (congrArg PrimeSpectrum.asIdeal hcomap').symm
  · intro h
    rintro ⟨q, ⟨hq, hqp⟩, hs⟩
    let q' : Spec Γ(Y, f ⁻¹ᵁ U) := ⟨q, hq⟩
    have hqp' : PrimeSpectrum.comap (f.app U).hom q' = p :=
      PrimeSpectrum.ext hqp.over.symm
    have hmap : f (hV.fromSpec q') = x := by
      have hm := congrArg (fun g ↦ g q')
        (IsAffineOpen.SpecMap_appLE_fromSpec f hU hV le_rfl)
      simpa only [Scheme.Hom.comp_apply, Spec.map_apply, ← Scheme.Hom.app_eq_appLE,
        hqp', p, hU.fromSpec_primeIdealOf] using hm.symm
    have hmem := h (hV.fromSpec q') hmap
    -- `erw` crosses the semireducible identification of scheme opens with spectrum opens.
    erw [← Scheme.Hom.mem_preimage, hV.fromSpec_preimage_basicOpen,
      PrimeSpectrum.mem_basicOpen] at hmem
    exact hmem hs

/-- The norm open is the complement, within the affine open, of the image of the section's
vanishing locus. -/
theorem basicOpen_projectiveNorm_eq {X Y : Scheme.{u}} (f : Y ⟶ X) [IsFinite f]
    {U : X.Opens} (hU : IsAffineOpen U)
    (hproj : letI := (f.app U).hom.toAlgebra; Module.Projective Γ(X, U) Γ(Y, f ⁻¹ᵁ U))
    (s : Γ(Y, f ⁻¹ᵁ U)) :
    letI := (f.app U).hom.toAlgebra
    letI : Module.Finite Γ(X, U) Γ(Y, f ⁻¹ᵁ U) := f.finite_app U hU
    letI := hproj
    (X.basicOpen (Algebra.projectiveNorm Γ(X, U) s) : Set X) =
      (U : Set X) \ f '' ((f ⁻¹ᵁ U : Set Y) \ (Y.basicOpen s : Set Y)) := by
  let := (f.app U).hom.toAlgebra
  let : Module.Finite Γ(X, U) Γ(Y, f ⁻¹ᵁ U) := f.finite_app U hU
  let := hproj
  ext x
  constructor
  · intro hx
    have hxU := X.basicOpen_le (Algebra.projectiveNorm Γ(X, U) s) hx
    refine ⟨hxU, ?_⟩
    rintro ⟨y, ⟨_, hy⟩, hxy⟩
    exact hy ((f.mem_basicOpen_projectiveNorm_iff hU hproj s hxU).mp hx y hxy)
  · rintro ⟨hxU, hx⟩
    apply (f.mem_basicOpen_projectiveNorm_iff hU hproj s hxU).mpr
    intro y hy
    by_contra hs
    apply hx
    exact ⟨y, ⟨(Scheme.Hom.mem_preimage (f := f)).mpr (hy.symm ▸ hxU), hs⟩, hy⟩

end AlgebraicGeometry.Scheme.Hom
