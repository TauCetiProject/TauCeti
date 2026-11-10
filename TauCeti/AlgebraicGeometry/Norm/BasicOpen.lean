/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Jie Xu, Shitan Xu
-/
module

public import TauCeti.RingTheory.Norm.Projective
public import TauCeti.AlgebraicGeometry.Morphisms.Finite.Basic

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
    letI := f.moduleFinite_app_of_isAffineOpen hU
    letI := hproj
    x ∈ X.basicOpen (Algebra.projectiveNorm Γ(X, U) s) ↔
      ∀ y, f y = x → y ∈ Y.basicOpen s := by
  let := (f.app U).hom.toAlgebra
  let := f.moduleFinite_app_of_isAffineOpen hU
  let := hproj
  have hV : IsAffineOpen (f ⁻¹ᵁ U) := hU.preimage f
  obtain ⟨p, rfl⟩ : x ∈ Set.range hU.fromSpec := by rwa [hU.range_fromSpec]
  have hxU : hU.fromSpec p ∈ U := hx
  let : p.asIdeal.IsPrime := p.isPrime
  have hmap (q : Spec Γ(Y, f ⁻¹ᵁ U)) :
      f (hV.fromSpec q) = hU.fromSpec (PrimeSpectrum.comap (f.app U).hom q) := by
    have h := congrArg (fun g ↦ g q) (IsAffineOpen.SpecMap_appLE_fromSpec f hU hV le_rfl)
    simpa only [Scheme.Hom.comp_apply, Spec.map_apply, ← Scheme.Hom.app_eq_appLE] using h.symm
  have hnorm := not_congr (Algebra.projectiveNorm_mem_iff (p := p.asIdeal) (x := s))
  -- `erw` identifies the opens on `Spec` with their prime-spectrum model.
  erw [← Scheme.Hom.mem_preimage, hU.fromSpec_preimage_basicOpen,
    PrimeSpectrum.mem_basicOpen]
  refine hnorm.trans ⟨?_, ?_⟩
  · intro h y hy
    obtain ⟨q, rfl⟩ : y ∈ Set.range hV.fromSpec := by
      rw [hV.range_fromSpec]
      exact (Scheme.Hom.mem_preimage (f := f)).mpr (hy.symm ▸ hxU)
    erw [← Scheme.Hom.mem_preimage, hV.fromSpec_preimage_basicOpen,
      PrimeSpectrum.mem_basicOpen]
    intro hs
    apply h
    -- The norm criterion asks for a prime above `p` containing `s`.
    refine ⟨q.asIdeal, ⟨q.isPrime, ⟨?_⟩⟩, hs⟩
    rw [hmap] at hy
    exact (congrArg PrimeSpectrum.asIdeal (hU.fromSpec.isOpenEmbedding.injective hy)).symm
  · intro h
    rintro ⟨q, ⟨hq, hqp⟩, hs⟩
    let q' : Spec Γ(Y, f ⁻¹ᵁ U) := ⟨q, hq⟩
    have hqp' : PrimeSpectrum.comap (f.app U).hom q' = p :=
      PrimeSpectrum.ext hqp.over.symm
    have hmem := h (hV.fromSpec q') (by rw [hmap, hqp'])
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
    letI := f.moduleFinite_app_of_isAffineOpen hU
    letI := hproj
    (X.basicOpen (Algebra.projectiveNorm Γ(X, U) s) : Set X) =
      (U : Set X) \ f '' ((f ⁻¹ᵁ U : Set Y) \ (Y.basicOpen s : Set Y)) := by
  let := (f.app U).hom.toAlgebra
  let := f.moduleFinite_app_of_isAffineOpen hU
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
