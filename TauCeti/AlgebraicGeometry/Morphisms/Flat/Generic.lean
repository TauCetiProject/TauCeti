/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.AlgebraicGeometry.Morphisms.Flat.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Noetherian
public import TauCeti.RingTheory.Spectrum.Prime.GenericFreeness

/-!
# Generic flatness

A finite-type morphism to a reduced locally Noetherian scheme is flat over a dense open
subset of the target. The source need not be reduced. This provides the initial open set
from which flatness of a homogeneous orbit morphism can be propagated by translations.

The argument uses `Module.freeLocus_mem_nhds_of_mem_minimalPrimes` on a finite affine cover
of the source above each affine open of the target. Freeness over the base at a prime
implies flatness of all source stalks above that prime.

## References

* The Stacks Project, Tag 0529, generic flatness.
* H. Matsumura, *Commutative Ring Theory*, Theorem 24.1, generic freeness.
-/

public section

open CategoryTheory TopologicalSpace Topology

namespace AlgebraicGeometry

universe u

/-- Freeness of an algebra at a base prime implies flatness of the corresponding
scheme morphism at every source prime above it. -/
theorem _root_.PrimeSpectrum.flat_stalkMap_specMap_of_comap_mem_freeLocus
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (q : PrimeSpectrum S) (hq : q.comap (algebraMap R S) ∈ Module.freeLocus R S) :
    ((Spec.map (CommRingCat.ofHom (algebraMap R S))).stalkMap q).hom.Flat := by
  have hflat := PrimeSpectrum.flat_localization_of_comap_mem_freeLocus q hq
  let φ := Localization.localRingHom (q.comap (algebraMap R S)).asIdeal
    q.asIdeal (algebraMap R S) rfl
  let := φ.toAlgebra
  have : IsScalarTower R (Localization.AtPrime (q.comap (algebraMap R S)).asIdeal)
      (Localization.AtPrime q.asIdeal) :=
    .of_algebraMap_eq fun r ↦ (Localization.localRingHom_to_map _ _ _ rfl r).symm
  have hφ : φ.Flat := by
    rw [RingHom.Flat, Module.flat_iff_of_isLocalization
      (S := Localization.AtPrime (q.comap (algebraMap R S)).asIdeal)
      (p := (q.comap (algebraMap R S)).asIdeal.primeCompl)]
    exact hflat
  exact (CommRingCat.flat.arrow_mk_iso_iff
    (Scheme.arrowStalkMapSpecIso (CommRingCat.ofHom (algebraMap R S)) q)).mpr hφ

namespace Scheme.Hom

/-- A finite-type morphism to the spectrum of a reduced Noetherian ring is flat
over a dense open subset of the spectrum. -/
theorem exists_dense_open_flat_of_target_spec
    {X : Scheme.{u}} {R : CommRingCat.{u}} [IsNoetherianRing R] [_root_.IsReduced R]
    (f : X ⟶ Spec R) [QuasiCompact f] [LocallyOfFiniteType f] :
    ∃ U : (Spec R).Opens, Dense (U : Set (Spec R)) ∧ Flat (f ∣_ U) := by
  classical
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  let C := X.affineCover.finiteSubcover
  have : Fintype C.I₀ := inferInstance
  have (i : C.I₀) : IsAffine (C.X i) := by
    exact (OpenCover.finiteSubcover_X X.affineCover i).symm ▸ inferInstance
  let a (i : C.I₀) := (C.X i).isoSpec.inv ≫ C.f i
  let φ (i : C.I₀) := Spec.preimage (a i ≫ f)
  let B (i : C.I₀) := Γ(C.X i, ⊤)
  let (i : C.I₀) : Algebra R (B i) := (φ i).hom.toAlgebra
  have (i : C.I₀) : IsOpenImmersion (a i) := by dsimp only [a]; infer_instance
  have (i : C.I₀) : Algebra.FiniteType R (B i) := by
    have : LocallyOfFiniteType (a i ≫ f) := inferInstance
    have hφ : (φ i).hom.FiniteType := by
      apply (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mp
      rw [Spec.map_preimage]
      infer_instance
    exact hφ
  -- A finite intersection of the free neighbourhoods still contains every minimal prime.
  let U : (Spec R).Opens :=
    ⟨⋂ i : C.I₀, interior (Module.freeLocus R (B i)),
      isOpen_iInter_of_finite fun _ ↦ isOpen_interior⟩
  have hU : Dense (U : Set (Spec R)) := by
    apply PrimeSpectrum.dense_of_forall_mem_minimalPrimes
    intro p hp
    exact Set.mem_iInter.mpr fun i ↦ mem_interior_iff_mem_nhds.mpr
      (Module.freeLocus_mem_nhds_of_mem_minimalPrimes (B := B i) (B i) hp)
  refine ⟨U, hU, (flat_restrict_iff f U).mpr ?_⟩
  -- Check flatness on source stalks using the affine cover and cancel its open immersions.
  intro x hx
  obtain ⟨i, y, rfl⟩ := C.exists_eq x
  obtain ⟨q, rfl⟩ := (C.X i).isoSpec.inv.homeomorph.surjective y
  have heq : Spec.map (CommRingCat.ofHom (algebraMap R (B i))) = a i ≫ f :=
    Spec.map_preimage _
  have hq : q.comap (algebraMap R (B i)) ∈ Module.freeLocus R (B i) := by
    have hi := (Set.mem_iInter.mp hx) i
    have hi' : (a i ≫ f) q ∈ interior (Module.freeLocus R (B i)) := hi
    rw [← heq] at hi'
    exact interior_subset hi'
  have hflat : CommRingCat.flat ((a i ≫ f).stalkMap q) := by
    rw [← heq]
    exact PrimeSpectrum.flat_stalkMap_specMap_of_comap_mem_freeLocus q hq
  have hflat' : CommRingCat.flat (f.stalkMap ((a i) q) ≫ (a i).stalkMap q) := by
    simpa only [Scheme.Hom.stalkMap_comp] using! hflat
  have : IsOpenImmersion (a i) := inferInstance
  have : IsIso ((a i).stalkMap q) := inferInstance
  exact (CommRingCat.flat.cancel_right_of_respectsIso
    (f.stalkMap ((a i) q)) ((a i).stalkMap q)).mp hflat'

/-- A finite-type morphism to a reduced locally Noetherian affine scheme is flat
over a dense open subset of the target. -/
theorem exists_dense_open_flat_of_isAffine
    {X Y : Scheme.{u}} [IsAffine Y] [IsLocallyNoetherian Y] [IsReduced Y]
    (f : X ⟶ Y) [QuasiCompact f] [LocallyOfFiniteType f] :
    ∃ U : Y.Opens, Dense (U : Set Y) ∧ Flat (f ∣_ U) := by
  have : IsNoetherianRing Γ(Y, ⊤) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top Y⟩
  obtain ⟨U, hU, hflat⟩ := exists_dense_open_flat_of_target_spec (f ≫ Y.isoSpec.hom)
  let V := Y.isoSpec.hom ⁻¹ᵁ U
  refine ⟨V, hU.preimage Y.isoSpec.hom.homeomorph.isOpenMap, (flat_restrict_iff f V).mpr ?_⟩
  intro x hx
  have h := (flat_restrict_iff (f ≫ Y.isoSpec.hom) U).mp hflat x hx
  have h' : CommRingCat.flat (Y.isoSpec.hom.stalkMap (f x) ≫ f.stalkMap x) := by
    simpa only [Scheme.Hom.stalkMap_comp, CommRingCat.flat_iff] using! h
  exact (CommRingCat.flat.cancel_left_of_respectsIso
    (Y.isoSpec.hom.stalkMap (f x)) (f.stalkMap x)).mp h'

/-- **Generic flatness.** A finite-type morphism to a reduced locally Noetherian scheme
is flat over a dense open subset of its target. Neither reducedness of the source nor
separatedness of the morphism is required. -/
theorem exists_dense_open_flat
    {X Y : Scheme.{u}} [IsLocallyNoetherian Y] [IsReduced Y]
    (f : X ⟶ Y) [QuasiCompact f] [LocallyOfFiniteType f] :
    ∃ U : Y.Opens, Dense (U : Set Y) ∧ Flat (f ∣_ U) := by
  classical
  have h (A : Y.affineOpens) :
      ∃ V : A.1.toScheme.Opens, Dense (V : Set A.1.toScheme) ∧ Flat (f ∣_ A.1 ∣_ V) := by
    have : IsAffine A.1.toScheme := A.2
    exact exists_dense_open_flat_of_isAffine (f ∣_ A.1)
  choose V hV hflat using h
  let U : Y.Opens := ⨆ A : Y.affineOpens, A.1.ι ''ᵁ V A
  have hU : Dense (U : Set Y) := by
    intro y
    obtain ⟨A, hA, hy, -⟩ := exists_isAffineOpen_mem_and_subset (x := y) (U := ⊤) trivial
    have hcl := mem_closure_image A.ι.continuous.continuousAt (hV ⟨A, hA⟩ ⟨y, hy⟩)
    exact closure_mono (le_iSup (fun A : Y.affineOpens ↦ A.1.ι ''ᵁ V A) ⟨A, hA⟩) hcl
  refine ⟨U, hU, (flat_restrict_iff f U).mpr ?_⟩
  intro x hx
  obtain ⟨A, y, hy, hxy⟩ := Opens.mem_iSup.mp hx
  have : MorphismProperty.RespectsIso (@Flat : MorphismProperty Scheme.{u}) := by
    rw [HasRingHomProperty.eq_affineLocally (P := @Flat)]
    exact affineLocally_respectsIso _ RingHom.Flat.respectsIso
  have hflatA : Flat (f ∣_ A.1.ι ''ᵁ V A) :=
    (MorphismProperty.arrow_mk_iso_iff (@Flat : MorphismProperty Scheme.{u})
      (morphismRestrictRestrict f A.1 (V A))).mp (hflat A)
  exact (flat_restrict_iff f (A.1.ι ''ᵁ V A)).mp hflatA x ⟨y, hy, hxy⟩

end Scheme.Hom

end AlgebraicGeometry
