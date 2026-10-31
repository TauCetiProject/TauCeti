/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Sheaf.Free.Basic
public import TauCeti.Algebra.Module.PseudoCoherent.ChainComplex
public import TauCeti.AlgebraicGeometry.Modules.Restriction.Basic
public import TauCeti.AlgebraicGeometry.Modules.Tilde.Basic

/-!
# Pseudo-coherent modules on a scheme

An `𝒪_X`-module `F` on a scheme `X` is *pseudo-coherent* when every point of `X` has an open
neighbourhood `U` on which `F` has a resolution
`⋯ → 𝒪_U^{a₂} → 𝒪_U^{a₁} → 𝒪_U^{a₀} → F|_U → 0` by free modules of finite rank. Resolutions
are chain complexes `P` in nonnegative degrees with a quasi-isomorphism `P ⟶ F[0]`, as in
Mathlib's `ProjectiveResolution`. Pseudo-coherence is the sheaf version of the module notion
`TauCeti.Huber.IsPseudoCoherentOver R M ⊤`, and is the finiteness condition for modules and
complexes on schemes that are not Noetherian.

Exact functors into `X.Modules` that send the terms of a resolution to free modules of finite
rank carry it to a finite free resolution. Restriction along an open immersion is exact, being
both a left and a right adjoint, and sends free modules to free modules; hence finite free
resolutions restrict to open subschemes, and pseudo-coherence is local on `X`. The functor
`M ↦ M~` is exact as well, so pseudo-coherent modules over a ring `R` give pseudo-coherent
sheaves on `Spec R`.

## Main definitions

* `AlgebraicGeometry.Scheme.Modules.HasFiniteFreeResolution F`: `F` has a resolution by free
  modules of finite rank.
* `AlgebraicGeometry.Scheme.Modules.IsPseudoCoherent F`: `F` has such a resolution locally.

## Main results

* `AlgebraicGeometry.Scheme.Modules.HasFiniteFreeResolution.of_quasiIso_map`: exact functors
  carry resolutions to finite free resolutions when they send the terms to finite free modules.
* `AlgebraicGeometry.Scheme.Modules.isPseudoCoherent_iff_exists_isOpenImmersion`: the local
  resolutions may be taken on arbitrary open immersions into `X`.
* `AlgebraicGeometry.Scheme.Modules.IsPseudoCoherent.restrict`: pseudo-coherence is preserved by
  restriction along open immersions.
* `AlgebraicGeometry.Scheme.Modules.isPseudoCoherent_iff_of_isOpenCover`: pseudo-coherence is
  local on `X`.
* `AlgebraicGeometry.Scheme.Modules.isPseudoCoherent_free`: free modules of finite rank are
  pseudo-coherent.
* `AlgebraicGeometry.Scheme.Modules.isPseudoCoherent_tilde`: the sheaf `M~` on `Spec R`
  associated with a pseudo-coherent `R`-module `M` is pseudo-coherent.

## References

* The Stacks Project, Definition 15.66.1 (Tag 064Q) for modules, and Section 36.10
  (Tag 08E4) for the comparison between pseudo-coherent modules and sheaves on schemes.
-/

public section

open CategoryTheory Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Modules

noncomputable section

variable {X Y : Scheme.{u}}

/-- `F` has a *finite free resolution* when there are a chain complex `P` in nonnegative degrees
whose terms are free modules of finite rank and a quasi-isomorphism `P ⟶ F[0]`, that is, an exact
sequence `⋯ → 𝒪_X^{a₁} → 𝒪_X^{a₀} → F → 0` with every `aᵢ` finite. -/
def HasFiniteFreeResolution (F : X.Modules) : Prop :=
  ∃ (P : ChainComplex X.Modules ℕ) (π : P ⟶ (ChainComplex.single₀ X.Modules).obj F),
    (∀ n, ∃ ι : Type u, Finite ι ∧ Nonempty (P.X n ≅ SheafOfModules.free (R := X.ringCatSheaf) ι))
      ∧ QuasiIso π

/-- An `𝒪_X`-module `F` is *pseudo-coherent* when every point of `X` has an open neighbourhood
`U` on which `F` has a resolution `⋯ → 𝒪_U^{a₁} → 𝒪_U^{a₀} → F|_U → 0` by free modules of finite
rank (Stacks, Section 36.10, Tag 08E4). -/
def IsPseudoCoherent (F : X.Modules) : Prop :=
  ∀ x : X, ∃ U : X.Opens, x ∈ U ∧ (F.restrict U.ι).HasFiniteFreeResolution

variable {F G : X.Modules}

/-- Unfolding of `HasFiniteFreeResolution`: a chain complex of free modules of finite rank with a
quasi-isomorphism to `F[0]`. -/
theorem hasFiniteFreeResolution_iff : F.HasFiniteFreeResolution ↔
    ∃ (P : ChainComplex X.Modules ℕ) (π : P ⟶ (ChainComplex.single₀ X.Modules).obj F),
      (∀ n, ∃ ι : Type u, Finite ι ∧
        Nonempty (P.X n ≅ SheafOfModules.free (R := X.ringCatSheaf) ι)) ∧ QuasiIso π :=
  Iff.rfl

/-- Unfolding of `IsPseudoCoherent`: every point has an open neighbourhood `U` on which `F` has a
finite free resolution. -/
theorem isPseudoCoherent_iff : F.IsPseudoCoherent ↔
    ∀ x : X, ∃ U : X.Opens, x ∈ U ∧ (F.restrict U.ι).HasFiniteFreeResolution :=
  Iff.rfl

namespace HasFiniteFreeResolution

/-- Having a finite free resolution is invariant under isomorphism. -/
theorem of_iso (e : F ≅ G) (h : F.HasFiniteFreeResolution) : G.HasFiniteFreeResolution := by
  obtain ⟨P, π, hP, hπ⟩ := h
  exact ⟨P, π ≫ (ChainComplex.single₀ X.Modules).map e.hom, hP, inferInstance⟩

/-- An exact functor `T` into `X.Modules` carries a resolution `P ⟶ A[0]` whose terms `T` sends to
free modules of finite rank to a finite free resolution of `T A`. The construction follows Mathlib's
`CategoryTheory.Functor.mapProjectiveResolution`. -/
theorem of_quasiIso_map {C : Type*} [Category* C] [Abelian C] (T : C ⥤ X.Modules) [T.Additive]
    [T.PreservesHomology] {P : ChainComplex C ℕ} {A : C}
    (π : P ⟶ (ChainComplex.single₀ C).obj A) [QuasiIso π]
    (hP : ∀ n, ∃ ι : Type u, Finite ι ∧
      Nonempty (T.obj (P.X n) ≅ SheafOfModules.free (R := X.ringCatSheaf) ι)) :
    (T.obj A).HasFiniteFreeResolution := by
  -- The comparison `ι` with the single complex on `T A` is an isomorphism. Its quasi-isomorphism
  -- instance is passed explicitly, since instance search does not unfold the local definition.
  let ι := (HomologicalComplex.singleMapHomologicalComplex T (ComplexShape.down ℕ) 0).hom.app A
  have hι : QuasiIso ι := quasiIso_of_isIso _
  exact ⟨(T.mapHomologicalComplex _).obj P, (T.mapHomologicalComplex _).map π ≫ ι, hP,
    quasiIso_comp (hφ' := hι) _ _⟩

/-- A finite free resolution restricts to a finite free resolution along an open immersion. -/
theorem restrict (h : F.HasFiniteFreeResolution) (f : Y ⟶ X) [IsOpenImmersion f] :
    (F.restrict f).HasFiniteFreeResolution := by
  obtain ⟨P, π, hP, hπ⟩ := h
  refine of_quasiIso_map (restrictFunctor f) π fun n ↦ ?_
  obtain ⟨ι, hι, ⟨e⟩⟩ := hP n
  exact ⟨ι, hι, ⟨(restrictFunctor f).mapIso e ≪≫ restrictFreeIso f ι⟩⟩

end HasFiniteFreeResolution

/-- A free module of finite rank has a finite free resolution, concentrated in degree zero. -/
@[simp]
theorem hasFiniteFreeResolution_free (ι : Type u) [Finite ι] :
    HasFiniteFreeResolution (SheafOfModules.free (R := X.ringCatSheaf) ι) := by
  refine ⟨_, 𝟙 _, fun n ↦ ?_, inferInstance⟩
  cases n with
  | zero => exact ⟨ι, inferInstance, ⟨HomologicalComplex.singleObjXSelf _ _ _⟩⟩
  | succ n =>
    exact ⟨PEmpty, inferInstance, ⟨(HomologicalComplex.isZero_single_obj_X _ _ _ _
      n.succ_ne_zero).iso (TauCeti.SheafOfModules.isZero_free PEmpty)⟩⟩

/-- A zero module has a finite free resolution, by the zero complex. -/
theorem HasFiniteFreeResolution.of_isZero (hF : IsZero F) : F.HasFiniteFreeResolution :=
  (hasFiniteFreeResolution_free PEmpty).of_iso
    ((TauCeti.SheafOfModules.isZero_free PEmpty).iso hF)

/-- The pseudo-coherence of `F` may be tested on open immersions into `X`: every point lies in
the image of an open immersion `g` such that the restriction of `F` along `g` has a finite free
resolution. -/
theorem isPseudoCoherent_iff_exists_isOpenImmersion :
    F.IsPseudoCoherent ↔ ∀ x : X, ∃ (V : Scheme.{u}) (g : V ⟶ X) (_ : IsOpenImmersion g),
      x ∈ g.opensRange ∧ (F.restrict g).HasFiniteFreeResolution := by
  refine ⟨fun h x ↦ ?_, fun h x ↦ ?_⟩
  · obtain ⟨U, hx, hU⟩ := h x
    exact ⟨U, U.ι, inferInstance, by rwa [Scheme.Opens.opensRange_ι], hU⟩
  · obtain ⟨V, g, _, hx, hg⟩ := h x
    -- Transport the resolution along the isomorphism of `V` with the open image of `g`.
    exact ⟨g.opensRange, hx, (hg.restrict g.isoOpensRange.inv).of_iso
      (((restrictFunctorComp g.isoOpensRange.inv g).app F).symm ≪≫
        (restrictFunctorCongr g.isoOpensRange_inv_comp).app F)⟩

namespace IsPseudoCoherent

/-- Pseudo-coherence is invariant under isomorphism. -/
theorem of_iso (e : F ≅ G) (h : F.IsPseudoCoherent) : G.IsPseudoCoherent := fun x ↦
  (h x).imp fun U ⟨hx, hU⟩ ↦ ⟨hx, hU.of_iso ((restrictFunctor U.ι).mapIso e)⟩

/-- The restriction of a pseudo-coherent module along an open immersion is pseudo-coherent. -/
theorem restrict (h : F.IsPseudoCoherent) (f : Y ⟶ X) [IsOpenImmersion f] :
    (F.restrict f).IsPseudoCoherent := by
  intro y
  obtain ⟨U, hU, hres⟩ := h (f y)
  -- Both restrictions of `F` to `f ⁻¹ᵁ U` factor through `U`, along `f ∣_ U`.
  exact ⟨f ⁻¹ᵁ U, hU, (hres.restrict (f ∣_ U)).of_iso
    (((restrictFunctorComp (f ∣_ U) U.ι).app F).symm ≪≫
      (restrictFunctorCongr (morphismRestrict_ι f U)).app F ≪≫
      (restrictFunctorComp (f ⁻¹ᵁ U).ι f).app F)⟩

end IsPseudoCoherent

/-- A module with a global finite free resolution is pseudo-coherent. -/
theorem HasFiniteFreeResolution.isPseudoCoherent (h : F.HasFiniteFreeResolution) :
    F.IsPseudoCoherent :=
  fun _ ↦ ⟨⊤, trivial, h.restrict _⟩

/-- Pseudo-coherence is local: for an open cover `U` of `X`, a module is pseudo-coherent exactly
when its restriction to every `U i` is. -/
theorem isPseudoCoherent_iff_of_isOpenCover {ι : Type*} {U : ι → X.Opens} (hU : IsOpenCover U) :
    F.IsPseudoCoherent ↔ ∀ i, (F.restrict (U i).ι).IsPseudoCoherent := by
  refine ⟨fun h i ↦ h.restrict _, fun h ↦ isPseudoCoherent_iff_exists_isOpenImmersion.mpr
    fun x ↦ ?_⟩
  obtain ⟨i, hi⟩ := hU.exists_mem x
  obtain ⟨V, hV, hres⟩ := h i ⟨x, hi⟩
  exact ⟨V, V.ι ≫ (U i).ι, inferInstance, ⟨⟨⟨x, hi⟩, hV⟩, rfl⟩,
    hres.of_iso ((restrictFunctorComp V.ι (U i).ι).app F).symm⟩

/-- A free module of finite rank is pseudo-coherent. -/
@[simp]
theorem isPseudoCoherent_free (ι : Type u) [Finite ι] :
    IsPseudoCoherent (SheafOfModules.free (R := X.ringCatSheaf) ι) :=
  (hasFiniteFreeResolution_free ι).isPseudoCoherent

/-- A zero module is pseudo-coherent. -/
theorem IsPseudoCoherent.of_isZero (hF : IsZero F) : F.IsPseudoCoherent :=
  (HasFiniteFreeResolution.of_isZero hF).isPseudoCoherent

section Tilde

variable {R : CommRingCat.{u}} {M : ModuleCat.{u} R}

/-- The sheaf `M~` associated with a pseudo-coherent `R`-module `M` has a finite free resolution
on `Spec R`: the exact functor `M ↦ M~` carries a resolution of `M` by coordinate modules to a
resolution of `M~` by free modules of finite rank. -/
theorem hasFiniteFreeResolution_tilde (h : TauCeti.Huber.IsPseudoCoherentOver R M ⊤) :
    (tilde M).HasFiniteFreeResolution := by
  obtain ⟨P, π, hP, hπ⟩ := h.exists_quasiIso_single₀
  refine HasFiniteFreeResolution.of_quasiIso_map (tilde.functor R) π fun n ↦ ?_
  obtain ⟨k, ⟨e⟩⟩ := hP n
  -- The coordinate module `Fin k → R` is the free module on `ULift (Fin k)`.
  let e' : (Fin k → R) ≃ₗ[R] (ULift.{u} (Fin k) →₀ R) :=
    (Finsupp.linearEquivFunOnFinite R R (Fin k)).symm.trans
      (Finsupp.domLCongr Equiv.ulift.symm)
  exact ⟨ULift (Fin k), inferInstance,
    ⟨(tilde.functor R).mapIso (e ≪≫ e'.toModuleIso) ≪≫ tildeFinsupp (ULift (Fin k))⟩⟩

/-- The sheaf `M~` associated with a pseudo-coherent `R`-module `M` is pseudo-coherent. -/
theorem isPseudoCoherent_tilde (h : TauCeti.Huber.IsPseudoCoherentOver R M ⊤) :
    (tilde M).IsPseudoCoherent :=
  (hasFiniteFreeResolution_tilde h).isPseudoCoherent

end Tilde

end

end AlgebraicGeometry.Scheme.Modules
