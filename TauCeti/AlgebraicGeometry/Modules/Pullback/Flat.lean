/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.Tilde.Basic
public import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.Kernels
public import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.Cokernels
public import Mathlib.Algebra.Category.ModuleCat.Descent
public import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-!
# Exactness of flat pullback

Pullback along a flat morphism of schemes preserves monomorphisms and kernels between
quasicoherent module sheaves. Together with right exactness of pullback, this transports exact
complexes with quasicoherent second and third terms, and short exact sequences whose first
two terms are quasicoherent, under flat base change.

The affine calculation uses `tildeFunctorCompPullbackIso` and Mathlib's finite-limit
preservation theorem for flat extension of scalars. No finiteness or Noetherian hypothesis
is needed.

## References

* [The Stacks Project, Tag 0250](https://stacks.math.columbia.edu/tag/0250),
  exactness of flat pullback on quasicoherent modules.
-/

public section

open CategoryTheory Limits AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules

universe u

noncomputable section

variable {R S : CommRingCat.{u}} (φ : R ⟶ S)

/-- Flat pullback preserves monomorphisms of quasicoherent modules on a spectrum. -/
private theorem mono_pullback_specMap_of_flat (hφ : φ.hom.Flat)
    {M N : (Spec R).Modules} (g : M ⟶ N) [M.IsQuasicoherent] [N.IsQuasicoherent] [Mono g] :
    Mono ((pullback (Spec.map φ)).map g) := by
  let F := pullback (Spec.map φ)
  let G := moduleSpecΓFunctor (R := R)
  let c := fromTildeΓNatTrans (R := R)
  have : G.IsRightAdjoint := (tilde.adjunction (R := R)).isRightAdjoint
  have : PreservesFiniteLimits (ModuleCat.extendScalars φ.hom) :=
    ModuleCat.preservesFiniteLimits_extendScalars_of_flat hφ
  have : Mono ((ModuleCat.extendScalars φ.hom ⋙ tilde.functor S).map (G.map g)) :=
    inferInstance
  let e := TauCeti.AlgebraicGeometry.tildeFunctorCompPullbackIso φ
  have hm : Mono ((tilde.functor R ⋙ F).map (G.map g)) := by
    apply mono_of_mono_fac (e.hom.naturality (G.map g))
  have : IsIso (c.app M) := isIso_fromTildeΓ_of_isQuasicoherent M
  have : IsIso (c.app N) := isIso_fromTildeΓ_of_isQuasicoherent N
  have : IsIso (F.map (c.app N)) := inferInstance
  have hN : Mono (F.map (c.app N)) := IsIso.mono_of_iso _
  have hn : (tilde.functor R).map (G.map g) ≫ c.app N = c.app M ≫ g :=
    c.naturality g
  have : Mono (F.map (c.app M) ≫ F.map g) := by
    rw [← F.map_comp, ← hn]
    rw [F.map_comp]
    exact mono_comp' hm hN
  exact (mono_comp_iff_of_isIso (F.map (c.app M)) (F.map g)).mp inferInstance

variable {X Y : Scheme.{u}}

private theorem mono_pullback_map_of_flat_of_isAffine [IsAffine X] [IsAffine Y]
    (f : X ⟶ Y) [Flat f] {M N : Y.Modules} (g : M ⟶ N)
    [M.IsQuasicoherent] [N.IsQuasicoherent] [Mono g] : Mono ((pullback f).map g) := by
  let A := pullback Y.isoSpec.inv
  let B := pullback (Spec.map f.appTop)
  let C := pullback X.isoSpec.hom
  have : PreservesLimits C := X.isoSpec.hom.preservesLimits_pullback_of_isOpenImmersion
  have : Mono (B.map (A.map g)) :=
    mono_pullback_specMap_of_flat f.appTop f.flat_appTop (A.map g)
  have : Mono ((A ⋙ B ⋙ C).map g) :=
    inferInstanceAs (Mono (C.map (B.map (A.map g))))
  let e : A ⋙ B ⋙ C ≅ pullback f :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (pullbackComp (Spec.map f.appTop) Y.isoSpec.inv) C ≪≫
      pullbackComp X.isoSpec.hom _ ≪≫ pullbackCongr (by
        rw [← Category.assoc, Scheme.isoSpec_hom_naturality, Category.assoc,
          Iso.hom_inv_id, Category.comp_id])
  exact mono_of_mono_fac (e.inv.naturality g)

private theorem mono_pullback_map_of_flat_of_isAffineTarget [IsAffine Y]
    (f : X ⟶ Y) [Flat f] {M N : Y.Modules} (g : M ⟶ N)
    [M.IsQuasicoherent] [N.IsQuasicoherent] [Mono g] : Mono ((pullback f).map g) := by
  apply (mono_iff_of_isOpenCover X.isBasis_affineOpens.isOpenCover _).mpr
  intro U
  let V : X.Opens := U.1
  have : IsAffine V.toScheme := U.2
  have : Mono ((pullback (V.ι ≫ f)).map g) :=
    mono_pullback_map_of_flat_of_isAffine (V.ι ≫ f) g
  exact mono_of_mono_fac ((pullbackComp V.ι f).hom.naturality g)

/-- Pullback along a flat morphism preserves monomorphisms between quasicoherent sheaves.
Neither scheme needs to be affine or Noetherian. -/
theorem _root_.AlgebraicGeometry.Scheme.Hom.mono_pullback_map_of_flat
    (f : X ⟶ Y) [Flat f] {M N : Y.Modules} (g : M ⟶ N)
    [M.IsQuasicoherent] [N.IsQuasicoherent] [Mono g] : Mono ((pullback f).map g) := by
  apply (mono_iff_of_isOpenCover (Y.isBasis_affineOpens.isOpenCover.comap f.base.hom) _).mpr
  intro U
  let V : Y.Opens := U.1
  have : IsAffine V.toScheme := U.2
  have hm : Mono ((pullback V.ι ⋙ pullback (f ∣_ V)).map g) :=
    mono_pullback_map_of_flat_of_isAffineTarget (f ∣_ V) ((pullback V.ι).map g)
  let e : pullback f ⋙ pullback (f ⁻¹ᵁ V).ι ≅
      pullback V.ι ⋙ pullback (f ∣_ V) :=
    pullbackComp _ f ≪≫ pullbackCongr (morphismRestrict_ι f V).symm ≪≫
      (pullbackComp (f ∣_ V) V.ι).symm
  have : IsIso (e.hom.app M) := inferInstance
  have hm' : Mono (e.hom.app M ≫ (pullback V.ι ⋙ pullback (f ∣_ V)).map g) :=
    mono_comp' (IsIso.mono_of_iso _) hm
  have hn : Mono ((pullback f ⋙ pullback (f ⁻¹ᵁ V).ι).map g ≫ e.hom.app N) :=
    (e.hom.naturality g).symm ▸ hm'
  exact @mono_of_mono _ _ _ _ _ _ _ hn

/-- Flat pullback carries a short exact sequence to a short exact sequence when its first two
terms are quasicoherent. No quasicoherence hypothesis on the third term is needed. -/
theorem _root_.AlgebraicGeometry.Scheme.Hom.shortExact_map_pullback_of_flat
    (f : X ⟶ Y) [Flat f] (S : ShortComplex Y.Modules) (hS : S.ShortExact)
    [S.X₁.IsQuasicoherent] [S.X₂.IsQuasicoherent] : (S.map (pullback f)).ShortExact := by
  have := hS.mono_f
  have h := (Functor.preservesFiniteColimits_iff_forall_exact_map_and_epi (pullback f)).mp
    inferInstance S hS
  exact ShortComplex.ShortExact.mk' h.1 (f.mono_pullback_map_of_flat S.f) h.2

/-- Flat pullback preserves an exact complex when its second and third terms are quasicoherent.
No condition on the first term, finiteness, or Noetherian hypothesis is required. -/
theorem _root_.AlgebraicGeometry.Scheme.Hom.exact_map_pullback_of_flat
    (f : X ⟶ Y) [Flat f] (S : ShortComplex Y.Modules) (hS : S.Exact)
    [S.X₂.IsQuasicoherent] [S.X₃.IsQuasicoherent] :
    (S.map (pullback f)).Exact := by
  let F := pullback f
  -- As in Mathlib's `preservesHomology_of_preservesMonos_and_cokernels`, factor the
  -- second arrow through its coimage. All objects here remain quasicoherent.
  have : (Abelian.coimage S.g).IsQuasicoherent :=
    inferInstanceAs (cokernel (kernel.ι S.g)).IsQuasicoherent
  have : Mono (F.map (Abelian.factorThruCoimage S.g)) :=
    f.mono_pullback_map_of_flat (Abelian.factorThruCoimage S.g)
  let φ : (ShortComplex.mk _ _ (Abelian.comp_coimage_π_eq_zero S.zero)).map F ⟶
      S.map F :=
    { τ₁ := 𝟙 _
      τ₂ := 𝟙 _
      τ₃ := F.map (Abelian.factorThruCoimage S.g)
      comm₂₃ := by
        dsimp
        rw [Category.id_comp, ← F.map_comp, cokernel.π_desc] }
  apply (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).1
  apply ShortComplex.exact_of_g_is_cokernel
  exact CokernelCofork.mapIsColimit _ ((S.exact_iff_exact_coimage_π).1 hS).gIsCokernel F

/-- Pullback along a flat morphism preserves the ambient kernel of a morphism between
quasicoherent module sheaves. -/
theorem _root_.AlgebraicGeometry.Scheme.Hom.preservesKernel_pullback_of_flat
    (f : X ⟶ Y) [Flat f] {M N : Y.Modules} (g : M ⟶ N)
    [M.IsQuasicoherent] [N.IsQuasicoherent] :
    PreservesLimit (parallelPair g 0) (pullback f) := by
  apply preservesLimit_of_preserves_limit_cone (kernelIsKernel g)
  apply (KernelFork.isLimitMapConeEquiv _ (pullback f)).2
  have : Mono (((ShortComplex.mk _ _ (kernel.condition g)).map (pullback f)).f) :=
    f.mono_pullback_map_of_flat (kernel.ι g)
  exact (f.exact_map_pullback_of_flat (ShortComplex.mk _ _ (kernel.condition g))
    (ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel g))).fIsKernel

end

end AlgebraicGeometry.Scheme.Modules
