/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Curved.Module.Right.ClosedCategory
public import TauCeti.Algebra.Homology.DG.Module.Right.DGCategory
public import TauCeti.CategoryTheory.DG.QuasiEquivalence

/-!
# Differential graded right modules as curved modules of curvature zero

An ordinary differential graded algebra `(A, d)` is a curved differential graded algebra of
curvature `w = 0`, and its differential graded right modules are exactly its curved right modules:
the curved equation `d_M² (m) = m * w` becomes `d_M² = 0`. This file makes that identification
functorial. Regarding a DG right module as a curved one changes no data, so it is a
differential graded functor

`DGRightModuleCat h ⥤ CurvedDGRightModuleCat h.isCurvedDGAlgebra_zero`

acting on homogeneous morphisms by the identity of underlying right-module cochains. Its maps on
Hom complexes are isomorphisms, because the curved Hom differential at curvature zero is the
ordinary DG Hom differential, and every curved module of curvature zero is the image of a DG
module. Consequently:

* the functor is a quasi-equivalence of differential graded categories, and it induces an
  equivalence between the homotopy category of DG right modules and the curved homotopy category
  at curvature zero;
* on closed degree-zero morphisms it gives an additive, linear equivalence between the ordinary
  category of DG right modules and the closed degree-zero category of curved modules of
  curvature zero.

The comparison is specific to curvature zero. For nonzero curvature a curved module has no
cohomology and no underlying DG module, and nothing here compares the two kinds of module.

## Main definitions

* `TauCeti.DGRightModuleCat.toCurved`: a DG right module regarded as a curved right module of
  curvature zero.
* `TauCeti.CurvedDGRightModuleCat.toDG`: a curved right module of curvature zero regarded as a DG
  right module; it is inverse to `toCurved` on objects.
* `TauCeti.DGRightModuleCat.dgToCurvedFunctor`: the differential graded functor.
* `TauCeti.DGRightModuleCat.homotopyToCurvedEquivalence`: the induced equivalence of homotopy
  categories.
* `TauCeti.DGRightModuleCat.closedToCurvedFunctor` and
  `TauCeti.DGRightModuleCat.closedToCurvedEquivalence`: the functor and equivalence on closed
  degree-zero morphisms.

## Main results

* `TauCeti.DGRightModuleCat.isIso_dgToCurvedFunctor_map`: the functor is an isomorphism on every
  Hom complex.
* `TauCeti.DGRightModuleCat.isQuasiEquivalence_dgToCurvedFunctor`: the functor is a
  quasi-equivalence.
* `TauCeti.DGRightModuleCat.dgClosedHom_closedToCurvedFunctor_map`: the functor on closed
  degree-zero morphisms is the degree-zero part of the differential graded functor.

## References

* L. Positselski, *Differential graded Koszul duality: an introductory survey*, Section 6.2,
  for curved DG modules and the zero-curvature specialization.
* B. Keller, *Deriving DG categories*, Sections 1 and 2, for DG functors and homotopy
  categories.
-/

public section

open CategoryTheory

namespace TauCeti

-- The closed category keeps the original enriched object carrier.
attribute [local implicit_reducible] ForgetEnrichment

universe u uR uA uM

section Objects

variable {R : Type uR} {A : Type uA} [CommRing R] [Ring A] [Algebra R A]
  {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜] {d : A →ₗ[R] A} {h : IsDGAlgebra 𝒜 d}

/-- A differential graded right module regarded as a curved differential graded right module of
curvature zero. The carrier, grading, action and differential are unchanged. -/
abbrev DGRightModuleCat.toCurved (M : DGRightModuleCat.{uR, uA, uM} h) :
    CurvedDGRightModuleCat.{uR, uA, uM} h.isCurvedDGAlgebra_zero :=
  CurvedDGRightModuleCat.of M.isDGRightModule.isCurvedDGRightModule_zero

/-- A curved differential graded right module of curvature zero regarded as a differential graded
right module. The carrier, grading, action and differential are unchanged. -/
abbrev CurvedDGRightModuleCat.toDG {h₀ : IsCurvedDGAlgebra 𝒜 d 0}
    (M : CurvedDGRightModuleCat.{uR, uA, uM} h₀) :
    DGRightModuleCat.{uR, uA, uM} (isCurvedDGAlgebra_zero_iff.mp h₀) :=
  DGRightModuleCat.of (M.isCurvedDGRightModule.toIsDGRightModule_of_curvature_eq_zero rfl)

/-- Regarding a DG module as curved and back returns the original module. -/
@[simp]
theorem DGRightModuleCat.toCurved_toDG (M : DGRightModuleCat.{uR, uA, uM} h) :
    M.toCurved.toDG = M :=
  (rfl)

/-- Regarding a curved module of curvature zero as a DG module and back returns the original
module. -/
@[simp]
theorem CurvedDGRightModuleCat.toDG_toCurved {h₀ : IsCurvedDGAlgebra 𝒜 d 0}
    (M : CurvedDGRightModuleCat.{uR, uA, uM} h₀) :
    M.toDG.toCurved = M :=
  (rfl)

end Objects

variable {R : Type u} {A : Type u} [CommRing R] [Ring A] [Algebra R A]
  {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜] {d : A →ₗ[R] A} {h : IsDGAlgebra 𝒜 d}

namespace DGRightModuleCat

/-! ### The differential graded functor -/

/-- Homogeneous morphisms of DG right modules are the homogeneous morphisms of the corresponding
curved modules of curvature zero: both are the right-module cochains of the given degree. -/
noncomputable def toCurvedDGHomLinearEquiv (M N : DGRightModuleCat.{u, u, u} h) (n : ℤ) :
    DGHom R n M N ≃ₗ[R] DGHom R n M.toCurved N.toCurved :=
  (dgHomLinearEquivCochains M N n).trans
    (CurvedDGRightModuleCat.dgHomLinearEquivCochains M.toCurved N.toCurved n).symm

/-- The comparison of homogeneous morphisms keeps the underlying cochain. -/
@[simp]
theorem dgHomLinearEquivCochains_toCurvedDGHomLinearEquiv {M N : DGRightModuleCat.{u, u, u} h}
    {n : ℤ} (f : DGHom R n M N) :
    CurvedDGRightModuleCat.dgHomLinearEquivCochains M.toCurved N.toCurved n
        (toCurvedDGHomLinearEquiv M N n f) =
      dgHomLinearEquivCochains M N n f :=
  LinearEquiv.apply_symm_apply _ _

/-- The comparison of homogeneous morphisms commutes with the differentials: at curvature zero the
curved Hom differential is the ordinary DG Hom differential. -/
theorem toCurvedDGHomLinearEquiv_dgDifferential {M N : DGRightModuleCat.{u, u, u} h} (n : ℤ)
    (f : DGHom R n M N) :
    toCurvedDGHomLinearEquiv M N (n + 1) (dgDifferential R n f) =
      dgDifferential R n (toCurvedDGHomLinearEquiv M N n f) := by
  apply (CurvedDGRightModuleCat.dgHomLinearEquivCochains M.toCurved N.toCurved (n + 1)).injective
  rw [CurvedDGRightModuleCat.dgDifferential_eq, dgHomLinearEquivCochains_toCurvedDGHomLinearEquiv,
    dgHomLinearEquivCochains_toCurvedDGHomLinearEquiv, dgDifferential_eq]
  exact (LinearMap.congr_fun
    (dgRightModuleCochains.curvedDifferential_isCurvedDGRightModule_zero
      (hM := M.isDGRightModule) (hN := N.isDGRightModule) n) _).symm

/-- The comparison of homogeneous morphisms preserves identities. -/
theorem toCurvedDGHomLinearEquiv_dgId (M : DGRightModuleCat.{u, u, u} h) :
    toCurvedDGHomLinearEquiv M M 0 (dgId R M) = dgId R M.toCurved := by
  apply (CurvedDGRightModuleCat.dgHomLinearEquivCochains M.toCurved M.toCurved 0).injective
  rw [CurvedDGRightModuleCat.dgId_eq, dgHomLinearEquivCochains_toCurvedDGHomLinearEquiv, dgId_eq]

/-- The comparison of homogeneous morphisms preserves composition. -/
theorem toCurvedDGHomLinearEquiv_dgComp {M N P : DGRightModuleCat.{u, u, u} h} {p q n : ℤ}
    (f : DGHom R p M N) (g : DGHom R q N P) (hpq : p + q = n) :
    toCurvedDGHomLinearEquiv M P n (dgComp R f g hpq) =
      dgComp R (toCurvedDGHomLinearEquiv M N p f) (toCurvedDGHomLinearEquiv N P q g) hpq := by
  apply (CurvedDGRightModuleCat.dgHomLinearEquivCochains M.toCurved P.toCurved n).injective
  rw [CurvedDGRightModuleCat.dgComp_eq, dgHomLinearEquivCochains_toCurvedDGHomLinearEquiv,
    dgHomLinearEquivCochains_toCurvedDGHomLinearEquiv,
    dgHomLinearEquivCochains_toCurvedDGHomLinearEquiv, dgComp_eq]

/-- **Differential graded right modules are curved modules of curvature zero.** The differential
graded functor regarding a DG right module over `h` as a curved right module over `h` with
curvature zero; it keeps the underlying cochain of every homogeneous morphism. -/
@[expose, implicit_reducible]
noncomputable def dgToCurvedFunctor :
    EnrichedFunctor (CochainComplex (ModuleCat.{u} R) ℤ) (DGRightModuleCat.{u, u, u} h)
      (CurvedDGRightModuleCat.{u, u, u} h.isCurvedDGAlgebra_zero) :=
  EnrichedFunctor.ofDGMap toCurved
    (fun {M N} n ↦ (toCurvedDGHomLinearEquiv M N n).toLinearMap)
    (fun n f ↦ toCurvedDGHomLinearEquiv_dgDifferential n f) toCurvedDGHomLinearEquiv_dgId
    (fun f g hpq ↦ toCurvedDGHomLinearEquiv_dgComp f g hpq)

/-- The differential graded functor sends a DG module to the same module regarded as curved. -/
@[simp]
theorem dgToCurvedFunctor_obj (M : DGRightModuleCat.{u, u, u} h) :
    (dgToCurvedFunctor (h := h)).obj M = M.toCurved :=
  (rfl)

/-- The differential graded functor acts on homogeneous morphisms by the comparison of
homogeneous morphisms. -/
@[simp]
theorem dgToCurvedFunctor_dgMap {M N : DGRightModuleCat.{u, u, u} h} (n : ℤ)
    (f : DGHom R n M N) :
    (dgToCurvedFunctor (h := h)).dgMap n f = toCurvedDGHomLinearEquiv M N n f :=
  EnrichedFunctor.dgMap_ofDGMap _ _ _ _ _ n f

/-- The differential graded functor is an isomorphism on every Hom complex. -/
instance isIso_dgToCurvedFunctor_map (M N : DGRightModuleCat.{u, u, u} h) :
    IsIso ((dgToCurvedFunctor (h := h)).map M N) := by
  have (n : ℤ) : IsIso (((dgToCurvedFunctor (h := h)).map M N).f n) :=
    (toCurvedDGHomLinearEquiv M N n).toModuleIso.isIso_hom
  exact HomologicalComplex.Hom.isIso_of_components _

/-- **The zero-curvature comparison is a quasi-equivalence.** It is an isomorphism on Hom
complexes, and every curved module of curvature zero is the image of a DG module. -/
theorem isQuasiEquivalence_dgToCurvedFunctor :
    (dgToCurvedFunctor (h := h)).IsQuasiEquivalence :=
  (EnrichedFunctor.isQuasiEquivalence_iff_isQuasiFullyFaithful_and_essSurj _).mpr
    ⟨EnrichedFunctor.isQuasiFullyFaithful_of_isIso_map fun _ _ ↦ inferInstance,
      -- `CurvedDGRightModuleCat.toDG_toCurved` holds by structure eta, so the identity applies.
      ⟨fun M ↦ ⟨DGHomotopyCategory.of R (DGHomotopyCategory.underlying R M).toDG,
        ⟨Iso.refl _⟩⟩⟩⟩

instance : (dgToCurvedFunctor (h := h)).mapDGHomotopyCategory.IsEquivalence :=
  isQuasiEquivalence_dgToCurvedFunctor.isEquivalence_mapDGHomotopyCategory

/-- **The homotopy category of DG right modules is the curved homotopy category at curvature
zero.** The equivalence is induced by the zero-curvature differential graded functor. -/
noncomputable def homotopyToCurvedEquivalence :
    DGHomotopyCategory R (DGRightModuleCat.{u, u, u} h) ≌
      DGHomotopyCategory R (CurvedDGRightModuleCat.{u, u, u} h.isCurvedDGAlgebra_zero) :=
  (dgToCurvedFunctor (h := h)).mapDGHomotopyCategory.asEquivalence

/-- The homotopy equivalence sends a DG module to the same module regarded as curved. -/
@[simp]
theorem homotopyToCurvedEquivalence_functor_obj (M : DGRightModuleCat.{u, u, u} h) :
    (homotopyToCurvedEquivalence (h := h)).functor.obj (DGHomotopyCategory.of R M) =
      DGHomotopyCategory.of R M.toCurved :=
  (rfl)

/-! ### Closed degree-zero morphisms -/

/-- The zero-curvature comparison on the ordinary category of DG right modules: a morphism of DG
modules is a closed morphism of the corresponding curved modules with the same underlying map. -/
@[expose, implicit_reducible]
noncomputable def closedToCurvedFunctor :
    DGRightModuleCat.{u, u, u} h ⥤
      ForgetEnrichment (CochainComplex (ModuleCat.{u} R) ℤ)
        (CurvedDGRightModuleCat.{u, u, u} h.isCurvedDGAlgebra_zero) where
  obj M := ForgetEnrichment.of _ M.toCurved
  map f := CurvedDGRightModuleCat.closedHomOf f.toLinearMap (fun _ _ hx ↦ f.map_mem' hx) f.map_d'
  map_id M := CurvedDGRightModuleCat.closedHom_ext fun x ↦ by
    simp only [CurvedDGRightModuleCat.closedHom_closedHomOf, CurvedDGRightModuleCat.closedHom_id,
      DGRightModuleHom.coe_toLinearMap, LinearMap.id_apply]
    exact id_apply M x
  map_comp f g := CurvedDGRightModuleCat.closedHom_ext fun x ↦ by
    simp only [CurvedDGRightModuleCat.closedHom_closedHomOf, CurvedDGRightModuleCat.closedHom_comp,
      DGRightModuleHom.coe_toLinearMap, LinearMap.comp_apply]
    exact comp_apply f g x

/-- The closed comparison sends a DG module to the same module regarded as curved. -/
@[simp]
theorem closedToCurvedFunctor_obj (M : DGRightModuleCat.{u, u, u} h) :
    (closedToCurvedFunctor (h := h)).obj M = ForgetEnrichment.of _ M.toCurved :=
  (rfl)

/-- The closed comparison keeps the underlying map of a morphism. -/
@[simp]
theorem closedHom_closedToCurvedFunctor_map {M N : DGRightModuleCat.{u, u, u} h} (f : M ⟶ N) :
    CurvedDGRightModuleCat.closedHom ((closedToCurvedFunctor (h := h)).map f) = f.toLinearMap :=
  CurvedDGRightModuleCat.closedHom_closedHomOf _ _ _

/-- The closed comparison is the degree-zero part of the differential graded functor: on the
closed degree-zero morphism attached to a morphism of DG modules, the two agree. -/
theorem dgClosedHom_closedToCurvedFunctor_map {M N : DGRightModuleCat.{u, u, u} h} (f : M ⟶ N) :
    dgClosedHom R ((closedToCurvedFunctor (h := h)).map f) =
      (dgToCurvedFunctor (h := h)).dgMap 0 (homLinearEquivDGCycles M N f : DGHom R 0 M N) := by
  apply (CurvedDGRightModuleCat.dgHomLinearEquivCochains M.toCurved N.toCurved 0).injective
  rw [dgToCurvedFunctor_dgMap, dgHomLinearEquivCochains_toCurvedDGHomLinearEquiv]
  refine Subtype.ext (LinearMap.ext fun x ↦ ?_)
  rw [coe_homLinearEquivDGCycles_apply, ← CurvedDGRightModuleCat.closedHom_eq,
    closedHom_closedToCurvedFunctor_map, DGRightModuleHom.coe_toLinearMap]

/-- A closed morphism of curved modules of curvature zero is a morphism of the underlying DG
modules. -/
noncomputable def ofClosedHom {M N : DGRightModuleCat.{u, u, u} h}
    (f : ForgetEnrichment.of (CochainComplex (ModuleCat.{u} R) ℤ) M.toCurved ⟶
      ForgetEnrichment.of (CochainComplex (ModuleCat.{u} R) ℤ) N.toCurved) :
    M ⟶ N where
  toLinearMap := CurvedDGRightModuleCat.closedHom f
  map_mem' hx := CurvedDGRightModuleCat.closedHom_mem f hx
  map_d' x := CurvedDGRightModuleCat.differential_closedHom f x

/-- The morphism of DG modules attached to a closed morphism has the same underlying map. -/
@[simp]
theorem ofClosedHom_apply {M N : DGRightModuleCat.{u, u, u} h}
    (f : ForgetEnrichment.of (CochainComplex (ModuleCat.{u} R) ℤ) M.toCurved ⟶
      ForgetEnrichment.of (CochainComplex (ModuleCat.{u} R) ℤ) N.toCurved) (x : M) :
    ofClosedHom f x = CurvedDGRightModuleCat.closedHom f x :=
  (rfl)

/-- The closed comparison is fully faithful: closed morphisms of curved modules of curvature zero
are exactly the morphisms of the underlying DG modules. -/
noncomputable def fullyFaithfulClosedToCurvedFunctor :
    (closedToCurvedFunctor (h := h)).FullyFaithful where
  preimage f := ofClosedHom f
  map_preimage f := CurvedDGRightModuleCat.closedHom_ext fun x ↦ by
    rw [closedHom_closedToCurvedFunctor_map]
    exact ofClosedHom_apply f x
  preimage_map f := hom_ext fun x ↦ by
    rw [ofClosedHom_apply, closedHom_closedToCurvedFunctor_map, DGRightModuleHom.coe_toLinearMap]

instance : (closedToCurvedFunctor (h := h)).Full :=
  fullyFaithfulClosedToCurvedFunctor.full

instance : (closedToCurvedFunctor (h := h)).Faithful :=
  fullyFaithfulClosedToCurvedFunctor.faithful

instance : (closedToCurvedFunctor (h := h)).EssSurj where
  -- `CurvedDGRightModuleCat.toDG_toCurved` holds by structure eta, so the identity applies.
  mem_essImage M := ⟨(ForgetEnrichment.to _ M).toDG, ⟨Iso.refl _⟩⟩

instance : (closedToCurvedFunctor (h := h)).IsEquivalence where

instance : (closedToCurvedFunctor (h := h)).Additive where
  map_add {_ _ f g} := CurvedDGRightModuleCat.closedHom_injective <| calc
    _ = (f + g).toLinearMap := closedHom_closedToCurvedFunctor_map (f + g)
    _ = f.toLinearMap + g.toLinearMap := LinearMap.ext fun x ↦ add_apply f g x
    _ = _ := by
      rw [← closedHom_closedToCurvedFunctor_map f, ← closedHom_closedToCurvedFunctor_map g]
      exact (CurvedDGRightModuleCat.closedHom_add _ _).symm

instance : (closedToCurvedFunctor (h := h)).Linear R where
  map_smul {_ _} f r := CurvedDGRightModuleCat.closedHom_injective <| calc
    _ = (r • f).toLinearMap := closedHom_closedToCurvedFunctor_map (r • f)
    _ = r • f.toLinearMap := LinearMap.ext fun x ↦ smul_apply r f x
    _ = _ := by
      rw [← closedHom_closedToCurvedFunctor_map f]
      exact (CurvedDGRightModuleCat.closedHom_smul _ _).symm

/-- **The category of DG right modules is the closed degree-zero category of curved modules of
curvature zero.** The equivalence is the closed zero-curvature comparison; it is additive and
linear over the ground ring. -/
noncomputable def closedToCurvedEquivalence :
    DGRightModuleCat.{u, u, u} h ≌
      ForgetEnrichment (CochainComplex (ModuleCat.{u} R) ℤ)
        (CurvedDGRightModuleCat.{u, u, u} h.isCurvedDGAlgebra_zero) :=
  (closedToCurvedFunctor (h := h)).asEquivalence

end DGRightModuleCat

end TauCeti
