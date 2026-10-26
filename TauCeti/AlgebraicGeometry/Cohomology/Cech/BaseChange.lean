/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Descent
public import TauCeti.Algebra.Category.ModuleCat.ChangeOfRings
public import TauCeti.AlgebraicGeometry.Cohomology.Cech.Linear
public import TauCeti.AlgebraicGeometry.Modules.Pullback.BaseChange
public import TauCeti.CategoryTheory.Limits.Lattice
public import TauCeti.CategoryTheory.Sites.SheafCohomology.Cech.Functor

/-!
# Flat base change for the cohomology of quasi-coherent sheaves

Let `X` be a scheme over a commutative ring `R`, let `R → R'` be a flat ring map and let
`Y = X ×_R R'` be the base change, given as a pullback square `H` with projection `g : Y ⟶ X`.
For a quasi-coherent sheaf `M` on `X`, this file proves `Hⁿ(Y, g^* M) ≅ R' ⊗_R Hⁿ(X, M)` in every
degree `n`, when `X` and `Y` are locally Noetherian and `X` is covered by finitely many opens
whose nonempty finite intersections are affine; for instance when `X` is Noetherian with affine
diagonal. Over a field `k` and a field extension `K / k` this says that the dimension of
`Hⁿ(X, M)` does not change when `k` is extended to `K`.

The proof computes both sides by Čech complexes. Let `U` be such a cover of `X`; the inverse images
`g⁻¹ U` form such a cover of `Y`, because `g` is affine. By Leray's theorem, `Hⁿ(X, M)` is the
cohomology of the Čech complex `Č(U, M)` of `R`-modules of sections, and likewise on `Y`
(`AlgebraicGeometry.Scheme.Modules.homologyCechComplexLinearEquiv`). On an affine open `W` of `X`,
the sections of `g^* M` over `g⁻¹ W` are the base change of the sections of `M` over `W`
(`AlgebraicGeometry.Scheme.Hom.isBaseChange_pullbackSections`), with no flatness hypothesis. As
the finite intersections of `U` are affine, `R' ⊗_R Č(U, M)` is therefore the Čech complex of
`g^* M` for `g⁻¹ U`. Finally, extension of scalars along the flat map `R → R'` is exact, so it
commutes with taking cohomology.

The isomorphisms are stated as `Nonempty` linear equivalences: their construction depends on the
chosen cover, and no naturality is claimed. Flat base change in degrees zero and one on a
two-affine cover, without Noetherian hypotheses in degree zero and along any base-ring map in
degree one, is in `TauCeti.AlgebraicGeometry.Cohomology.BaseChange`.

## Main results

* `TauCeti.AlgebraicGeometry.nonempty_linearEquiv_tensor_cohomology_pullback_of_iSup_eq_top`:
  flat base change for a finite cover with affine intersections.
* `TauCeti.AlgebraicGeometry.nonempty_linearEquiv_tensor_cohomology_pullback`: flat base change
  for a Noetherian scheme with affine diagonal.
* `TauCeti.AlgebraicGeometry.nonempty_linearEquiv_tensor_cohomology_pullback_of_field`: flat base
  change along a field extension, for a quasi-compact scheme locally of finite type with affine
  diagonal.
* `TauCeti.AlgebraicGeometry.finrank_cohomology_pullback_eq_of_isPullback` and
  `TauCeti.AlgebraicGeometry.finiteDimensional_cohomology_pullback_of_isPullback`: invariance of
  the dimension and finite-dimensionality of `Hⁿ(X, M)` under extension of the base field.

## References

* R. Hartshorne, *Algebraic Geometry*, Proposition III.9.3 (flat base change).
* [The Stacks Project, Lemma 30.5.2](https://stacks.math.columbia.edu/tag/02KH), flat base change.
-/

public section

noncomputable section

open CategoryTheory Limits TopologicalSpace AlgebraicGeometry Opposite TensorProduct
open TauCeti.CategoryTheory TauCeti.AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules

universe u

namespace TauCeti.AlgebraicGeometry

section FlatBaseChange

variable {R : Type u} [CommRing R] {X : Scheme.{u}} [X.Over (Spec (.of R))]
  {R' : Type u} [CommRing R'] [Algebra R R'] {Y : Scheme.{u}} [Y.Over (Spec (.of R'))]
  {g : Y ⟶ X}
  (H : IsPullback g (Y ↘ Spec (.of R')) (X ↘ Spec (.of R))
    (Spec.map (CommRingCat.ofHom (algebraMap R R'))))

/-- The presheaf of `R'`-modules of sections of `g^* M` over the inverse images of the opens of
`X`. -/
private abbrev pullbackSectionsPresheaf (g : Y ⟶ X) (M : X.Modules) :
    X.Opensᵒᵖ ⥤ ModuleCat.{u} R' :=
  (Opens.map g.base).op ⋙ (sectionsBasePresheafFunctor R').obj ((Scheme.Modules.pullback g).obj M)

section SectionsPullback

variable (M : X.Modules) (W : X.Opens)

include H in
/-- Pulling back sections over `W` along `g`, as an `R`-linear map: this is
`Scheme.Hom.pullbackSectionsBaseLinear`, for the actions of `R` and `R'` on sections through
`Scheme.baseRingToStructurePresheaf`. -/
private def sectionsPullbackApp :
    ((sectionsBasePresheafFunctor R).obj M).obj (op W) ⟶
      (pullbackSectionsPresheaf (R' := R') g M ⋙
        ModuleCat.restrictScalars (algebraMap R R')).obj (op W) := by
  letI : Algebra R Γ(X, W) := ((X.baseRingToStructurePresheaf R).app (op W)).hom.toAlgebra
  letI : Algebra R' Γ(Y, g ⁻¹ᵁ W) :=
    ((Y.baseRingToStructurePresheaf R').app (op (g ⁻¹ᵁ W))).hom.toAlgebra
  letI := sectionsBaseModule R M W
  letI := sectionsBaseModule R' ((Scheme.Modules.pullback g).obj M) (g ⁻¹ᵁ W)
  letI : Module R Γ((Scheme.Modules.pullback g).obj M, g ⁻¹ᵁ W) :=
    Module.compHom _ (algebraMap R R')
  letI : Module R ((pullbackSectionsPresheaf (R' := R') g M).obj (op W)) :=
    Module.compHom _ (algebraMap R R')
  haveI : IsScalarTower R Γ(X, W) Γ(M, W) := .of_algebraMap_smul fun _ _ ↦ rfl
  haveI : IsScalarTower R' Γ(Y, g ⁻¹ᵁ W) Γ((Scheme.Modules.pullback g).obj M, g ⁻¹ᵁ W) :=
    .of_algebraMap_smul fun _ _ ↦ rfl
  haveI : IsScalarTower R R' Γ((Scheme.Modules.pullback g).obj M, g ⁻¹ᵁ W) :=
    .of_algebraMap_smul fun _ _ ↦ rfl
  exact ModuleCat.ofHom (g.pullbackSectionsBaseLinear M W H.toCommSq)

private lemma sectionsPullbackApp_hom_apply (x : Γ(M, W)) :
    (sectionsPullbackApp H M W).hom x = g.pullbackSections M W x := by
  let : Algebra R Γ(X, W) := ((X.baseRingToStructurePresheaf R).app (op W)).hom.toAlgebra
  let : Algebra R' Γ(Y, g ⁻¹ᵁ W) :=
    ((Y.baseRingToStructurePresheaf R').app (op (g ⁻¹ᵁ W))).hom.toAlgebra
  let := sectionsBaseModule R M W
  let := sectionsBaseModule R' ((Scheme.Modules.pullback g).obj M) (g ⁻¹ᵁ W)
  let : Module R Γ((Scheme.Modules.pullback g).obj M, g ⁻¹ᵁ W) :=
    Module.compHom _ (algebraMap R R')
  have : IsScalarTower R Γ(X, W) Γ(M, W) := .of_algebraMap_smul fun _ _ ↦ rfl
  have : IsScalarTower R' Γ(Y, g ⁻¹ᵁ W) Γ((Scheme.Modules.pullback g).obj M, g ⁻¹ᵁ W) :=
    .of_algebraMap_smul fun _ _ ↦ rfl
  have : IsScalarTower R R' Γ((Scheme.Modules.pullback g).obj M, g ⁻¹ᵁ W) :=
    .of_algebraMap_smul fun _ _ ↦ rfl
  exact g.pullbackSectionsBaseLinear_apply M W H.toCommSq x

end SectionsPullback

/-- Pulling back sections along `g`, as a morphism of presheaves of `R`-modules on `X`. -/
private def sectionsPullback (M : X.Modules) :
    (sectionsBasePresheafFunctor R).obj M ⟶
      pullbackSectionsPresheaf (R' := R') g M ⋙ ModuleCat.restrictScalars (algebraMap R R') where
  app W := sectionsPullbackApp H M W.unop
  naturality _ _ i := by
    ext (x : Γ(M, _))
    exact (sectionsPullbackApp_hom_apply H M _ _).trans
      ((g.pullbackSections_restrict M _ i.unop x).symm.trans
        (congrArg _ (sectionsPullbackApp_hom_apply H M _ x).symm))

/-- The morphism of presheaves of `R'`-modules `R' ⊗[R] Γ(M, -) ⟶ Γ(g^* M, g⁻¹ -)` adjoint to
`sectionsPullback`, `s ⊗ m ↦ s • g^* m`. -/
private def sectionsPullbackExtend (M : X.Modules) :
    (sectionsBasePresheafFunctor R).obj M ⋙ ModuleCat.extendScalars (algebraMap R R') ⟶
      pullbackSectionsPresheaf (R' := R') g M where
  app W := ((ModuleCat.extendRestrictScalarsAdj (algebraMap R R')).homEquiv _ _).symm
    ((sectionsPullback H M).app W)
  naturality W V i := by
    rw [Functor.comp_map, ← Adjunction.homEquiv_naturality_left_symm,
      (sectionsPullback H M).naturality, Functor.comp_map,
      Adjunction.homEquiv_naturality_right_symm]

/-- On an affine open, sections of `g^* M` are the base change of sections of `M`, so the
adjoint of the pullback of sections is an isomorphism. -/
private lemma isIso_sectionsPullbackExtend_app (M : X.Modules) [M.IsQuasicoherent] {W : X.Opens}
    (hW : IsAffineOpen W) : IsIso ((sectionsPullbackExtend H M).app (op W)) := by
  let : Algebra R Γ(X, W) := ((X.baseRingToStructurePresheaf R).app (op W)).hom.toAlgebra
  let : Algebra R' Γ(Y, g ⁻¹ᵁ W) :=
    ((Y.baseRingToStructurePresheaf R').app (op (g ⁻¹ᵁ W))).hom.toAlgebra
  let := sectionsBaseModule R M W
  let := sectionsBaseModule R' ((Scheme.Modules.pullback g).obj M) (g ⁻¹ᵁ W)
  let : Module R Γ((Scheme.Modules.pullback g).obj M, g ⁻¹ᵁ W) :=
    Module.compHom _ (algebraMap R R')
  have : IsScalarTower R Γ(X, W) Γ(M, W) := .of_algebraMap_smul fun _ _ ↦ rfl
  have : IsScalarTower R' Γ(Y, g ⁻¹ᵁ W) Γ((Scheme.Modules.pullback g).obj M, g ⁻¹ᵁ W) :=
    .of_algebraMap_smul fun _ _ ↦ rfl
  have : IsScalarTower R R' Γ((Scheme.Modules.pullback g).obj M, g ⁻¹ᵁ W) :=
    .of_algebraMap_smul fun _ _ ↦ rfl
  have h := ModuleCat.isIso_extendRestrictScalarsAdj_homEquiv_symm_of_isBaseChange
    (g.isBaseChange_pullbackSections M W H hW)
  have e : (sectionsPullback H M).app (op W) = ModuleCat.ofHom
      (g.pullbackSectionsBaseLinear M W H.toCommSq) ≫
        (ModuleCat.restrictScalarsAlgebraMapIso _).inv :=
    ModuleCat.hom_ext (LinearMap.ext fun x ↦ (sectionsPullbackApp_hom_apply H M W x).trans
      ((g.pullbackSectionsBaseLinear_apply M W H.toCommSq x).symm.trans
        (ModuleCat.restrictScalarsAlgebraMapIso_inv_apply (R := R) (S := R')
          Γ((Scheme.Modules.pullback g).obj M, g ⁻¹ᵁ W) _).symm))
  -- The component of `sectionsPullbackExtend` is the adjoint of that of `sectionsPullback`.
  dsimp only [sectionsPullbackExtend]
  rw [e]
  exact h

include H in
/-- **Flat base change for the cohomology of quasi-coherent sheaves**, for a finite cover with
affine intersections. Let `X` be a locally Noetherian scheme over `R`, let `R → R'` be a flat ring
map and let `Y = X ×_R R'`, given as a pullback square, be locally Noetherian. Let `M` be a
quasi-coherent sheaf on `X` and suppose that `X` is covered by finitely many opens whose nonempty
finite intersections are affine. Then `Hⁿ(Y, g^* M) ≅ R' ⊗_R Hⁿ(X, M)` for every `n`. -/
theorem nonempty_linearEquiv_tensor_cohomology_pullback_of_iSup_eq_top [Module.Flat R R']
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] (M : X.Modules) [M.IsQuasicoherent]
    {ι : Type u} [Finite ι] (U : ι → X.Opens)
    (hU : ∀ s : Finset ι, s.Nonempty → IsAffineOpen (s.inf U)) (hcover : ⨆ i, U i = ⊤) (n : ℕ) :
    Nonempty (R' ⊗[R] Cohomology M n ≃ₗ[R'] Cohomology ((Scheme.Modules.pullback g).obj M) n) := by
  classical
  have : IsAffineHom g := MorphismProperty.of_isPullback H.flip inferInstance
  -- The cover of `Y` by the inverse images of the members of `U`.
  let V : ι → Y.Opens := fun i ↦ (Opens.map g.base).obj (U i)
  have hinf (s : Finset ι) : s.inf V = g ⁻¹ᵁ s.inf U :=
    (Finset.apply_inf_eq_inf_comp (g ⁻¹ᵁ ·) (fun _ _ ↦ rfl) rfl).symm
  have hV (s : Finset ι) (hs : s.Nonempty) : IsAffineOpen (s.inf V) :=
    hinf s ▸ (hU s hs).preimage g
  have hcoverV : ⨆ i, V i = ⊤ := by
    rw [← Scheme.Hom.preimage_iSup, hcover, Scheme.Hom.preimage_top]
  -- Extension of scalars along the flat map `R → R'` is exact.
  let E := ModuleCat.extendScalars.{u, u, u} (algebraMap R R')
  have := (ModuleCat.extendRestrictScalarsAdj.{u, u, u}
    (algebraMap R R')).leftAdjoint_preservesColimits.{u, u}
  have := ModuleCat.preservesFiniteLimits_extendScalars_of_flat
    (RingHom.flat_algebraMap_iff.mpr ‹Module.Flat R R'›)
  have : E.PreservesHomology := Functor.preservesHomology_of_preservesEpis_and_kernels E
  -- On the finite intersections of `U`, which are affine, sections of `g^* M` are the base
  -- change of sections of `M`.
  have : IsIso ((cechComplexFunctor U).map (sectionsPullbackExtend H M)) := by
    have (k : ℕ) : IsIso (((cechComplexFunctor U).map (sectionsPullbackExtend H M)).f k) := by
      have (a : Fin (k + 1) → ι) :
          IsIso ((sectionsPullbackExtend H M).app (op (∏ᶜ fun j ↦ U (a j)))) :=
        isIso_sectionsPullbackExtend_app H M
          (CompleteLattice.finite_product_eq_finset_image_inf U a ▸
            hU _ (Finset.univ_nonempty.image a))
      -- In each degree the map of Čech complexes is the product of the components.
      change IsIso (Limits.Pi.map fun a : Fin (k + 1) → ι ↦
        (sectionsPullbackExtend H M).app (op (∏ᶜ fun j ↦ U (a j))))
      infer_instance
    exact HomologicalComplex.Hom.isIso_of_components _
  have hG (k : ℕ) (a : Fin (k + 1) → ι) : Nonempty ((∏ᶜ fun j ↦ (Opens.map g.base).obj (U (a j))) ⟶
      (Opens.map g.base).obj (∏ᶜ fun j ↦ U (a j))) := by
    have hV : (∏ᶜ fun j ↦ V (a j)) = (Finset.univ.image a).inf V :=
      CompleteLattice.finite_product_eq_finset_image_inf V a
    have hU : (∏ᶜ fun j ↦ U (a j)) = (Finset.univ.image a).inf U :=
      CompleteLattice.finite_product_eq_finset_image_inf U a
    refine ⟨homOfLE ?_⟩
    rw [hV, hU, hinf]
  let C := (cechComplexFunctor U).obj ((sectionsBasePresheafFunctor R).obj M)
  -- `R' ⊗[R] Hⁿ(Č(U, M)) ≅ Hⁿ(R' ⊗[R] Č(U, M)) ≅ Hⁿ(Č(U, R' ⊗[R] M)) ≅ Hⁿ(Č(g⁻¹ U, g^* M))`.
  let e : E.obj (C.homology n) ≅ ((cechComplexFunctor V).obj
      ((sectionsBasePresheafFunctor R').obj ((Scheme.Modules.pullback g).obj M))).homology n :=
    ((C.sc n).mapHomologyIso E).symm ≪≫
      HomologicalComplex.homologyMapIso ((cechComplexFunctorMapIso U E).app _) n ≪≫
      HomologicalComplex.homologyMapIso (asIso ((cechComplexFunctor U).map
        (sectionsPullbackExtend H M))) n ≪≫
      HomologicalComplex.homologyMapIso (cechComplexCompIso (Opens.map g.base) U _ hG).symm n
  exact ⟨LinearEquiv.baseChange R R' _ _ (homologyCechComplexLinearEquiv U hU hcover M n).symm ≪≫ₗ
    (ModuleCat.extendScalarsAlgebraMapIso _).symm.toLinearEquiv ≪≫ₗ e.toLinearEquiv ≪≫ₗ
    homologyCechComplexLinearEquiv V hV hcoverV _ n⟩

include H in
/-- **Flat base change for the cohomology of quasi-coherent sheaves.** Let `X` be a Noetherian
scheme with affine diagonal over `R`, for instance a separated one, let `R → R'` be a flat ring
map and let `Y = X ×_R R'`, given as a pullback square, be locally Noetherian. Then for every
quasi-coherent sheaf `M` on `X`, `Hⁿ(Y, g^* M) ≅ R' ⊗_R Hⁿ(X, M)` for every `n`. -/
theorem nonempty_linearEquiv_tensor_cohomology_pullback [Module.Flat R R']
    [IsLocallyNoetherian X] [CompactSpace X] [IsAffineHom (pullback.diagonal (terminal.from X))]
    [IsLocallyNoetherian Y] (M : X.Modules) [M.IsQuasicoherent] (n : ℕ) :
    Nonempty (R' ⊗[R] Cohomology M n ≃ₗ[R'] Cohomology ((Scheme.Modules.pullback g).obj M) n) := by
  let 𝒰 := X.affineCover.finiteSubcover
  refine nonempty_linearEquiv_tensor_cohomology_pullback_of_iSup_eq_top H M
    (fun i : 𝒰.I₀ ↦ (𝒰.f i).opensRange) (fun s hs ↦ ?_) 𝒰.iSup_opensRange n
  rw [Finset.inf_eq_iInf]
  exact IsAffineOpen.biInf _ s.finite_toSet hs fun i _ ↦ isAffineOpen_opensRange (𝒰.f i)

end FlatBaseChange

section Field

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of K))] {g : Y ⟶ X}
  (H : IsPullback g (Y ↘ Spec (.of K)) (X ↘ Spec (.of k))
    (Spec.map (CommRingCat.ofHom (algebraMap k K))))

include H in
/-- Over a field, `Hⁿ(X_K, M_K) ≅ K ⊗_k Hⁿ(X, M)` for a quasi-compact scheme `X` locally of finite
type over `k` with affine diagonal, a quasi-coherent sheaf `M` on `X` and a field extension
`K / k`. -/
theorem nonempty_linearEquiv_tensor_cohomology_pullback_of_field
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [CompactSpace X]
    [IsAffineHom (pullback.diagonal (terminal.from X))] (M : X.Modules) [M.IsQuasicoherent]
    (n : ℕ) :
    Nonempty (K ⊗[k] Cohomology M n ≃ₗ[K] Cohomology ((Scheme.Modules.pullback g).obj M) n) := by
  have : LocallyOfFiniteType (Y ↘ Spec (.of K)) := MorphismProperty.of_isPullback H inferInstance
  have := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  have := LocallyOfFiniteType.isLocallyNoetherian (Y ↘ Spec (.of K))
  exact nonempty_linearEquiv_tensor_cohomology_pullback H M n

include H in
/-- The dimension of `Hⁿ(X, M)` does not change under extension of the base field, for a
quasi-coherent sheaf `M` on a quasi-compact scheme locally of finite type over a field with affine
diagonal, for instance a separated scheme of finite type. The coefficients after base change are
the canonical pullback sheaf. -/
theorem finrank_cohomology_pullback_eq_of_isPullback [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [CompactSpace X] [IsAffineHom (pullback.diagonal (terminal.from X))] (M : X.Modules)
    [M.IsQuasicoherent] (n : ℕ) :
    Module.finrank K (Cohomology ((Scheme.Modules.pullback g).obj M) n) =
      Module.finrank k (Cohomology M n) := by
  obtain ⟨e⟩ := nonempty_linearEquiv_tensor_cohomology_pullback_of_field H M n
  rw [← e.finrank_eq, Module.finrank_baseChange]

include H in
/-- The cohomology `Hⁿ(X, M)` of a quasi-coherent sheaf stays finite-dimensional under extension of
the base field, on a quasi-compact scheme locally of finite type over a field with affine diagonal.
-/
theorem finiteDimensional_cohomology_pullback_of_isPullback
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [CompactSpace X]
    [IsAffineHom (pullback.diagonal (terminal.from X))] (M : X.Modules) [M.IsQuasicoherent]
    (n : ℕ) [FiniteDimensional k (Cohomology M n)] :
    FiniteDimensional K (Cohomology ((Scheme.Modules.pullback g).obj M) n) := by
  obtain ⟨e⟩ := nonempty_linearEquiv_tensor_cohomology_pullback_of_field H M n
  exact Module.Finite.equiv e

end Field

end TauCeti.AlgebraicGeometry
