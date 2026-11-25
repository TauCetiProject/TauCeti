/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.PreAdicSpace.Adic
public import TauCeti.AlgebraicGeometry.AdicSpace.PreAdicSpace.Affinoid.Complete
public import TauCeti.AlgebraicGeometry.AdicSpace.PreAdicSpace.Affinoid.PairEquiv
public import TauCeti.AlgebraicGeometry.AdicSpace.PreAdicSpace.GlueMorphisms

/-!
# Morphisms from an adic space into an affinoid spectrum

Let `X` be an adic space and `(A, A⁺)` a complete Hausdorff Huber pair. A morphism
`f : X ⟶ Spa(A, A⁺)` has a global-sections map `f^♯ : A → 𝒪_X(X)`
(`TauCeti.ValuationSpectrum.presentationLimitAppTop`), which is continuous and carries `A⁺` into
the integral sections `𝒪_X⁺(X)`; it determines `f` (`presentationLimitAppTop_injective`). This
file proves the converse: every continuous ring map `A → 𝒪_X(X)` carrying `A⁺` into `𝒪_X⁺(X)` is
`f^♯` for a morphism `f`. On an open affinoid `U ≅ Spa(B, B⁺)` the map gives a morphism of Huber
pairs `(A, A⁺) → (B, B⁺)` and hence a morphism `U ⟶ Spa(A, A⁺)`; these agree on overlaps
because morphisms into `Spa(A, A⁺)` from sheafy sources are determined by their global-sections
maps, so they glue. Together this is the bijection `TauCeti.AdicSpace.homSpaEquiv`.

No sheaf condition on `Spa(A, A⁺)` is needed.

For degenerate targets the bijection gives everything: if `A` is discrete and isomorphic to `ℤ`,
every adic space has exactly one morphism to `Spa(A, A⁺)`; if `A` is the zero ring, only the empty
adic space has one, and it is unique.

## Main definitions

* `TauCeti.AdicSpace.homSpaEquiv`: morphisms `X ⟶ Spa(A, A⁺)` from an adic space correspond to
  continuous ring maps `A → 𝒪_X(X)` carrying `A⁺` into `𝒪_X⁺(X)`.
* `TauCeti.AdicSpace.uniqueHomSpaOfRingEquivInt`: the unique morphism to `Spa(ℤ, ℤ)`, for a
  discrete `A` isomorphic to `ℤ`.

## Main results

* `TauCeti.ValuationSpectrum.exists_presentationLimitAppTop_eq_of_iso`: the construction for a
  source isomorphic to the spectrum `Spa(B, B⁺)` of a sheafy complete Hausdorff Huber pair.
* `TauCeti.ValuationSpectrum.exists_presentationLimitAppTop_eq`: the construction for an adic
  source, by gluing over the open affinoid subspaces.
* `TauCeti.AdicSpace.homSpaEquiv_comp`: naturality in the source. Naturality in the Huber pair is
  `TauCeti.ValuationSpectrum.presentationLimitAppTop_comp_pairComap`.
* `TauCeti.AdicSpace.subsingleton_homSpa_of_intCast_surjective`: if `ℤ → A` is surjective,
  morphisms to `Spa(A, A⁺)` are unique.
* `TauCeti.AdicSpace.subsingleton_homSpa_of_subsingleton`,
  `TauCeti.AdicSpace.nonempty_homSpa_iff_isEmpty_of_subsingleton`: morphisms to `Spa(0, 0)` are
  unique, and exist exactly from the empty adic space.

## References

* R. Huber, *A generalization of formal schemes and rigid analytic varieties*, Math. Z. 217
  (1994), 513–551, §2, Proposition 2.1(ii).
-/

public section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace

namespace TauCeti

universe u

namespace ValuationSpectrum

open Huber

variable {A : Type u} [CommRing A] [UniformSpace A] [IsUniformAddGroup A]
  [IsTopologicalRing A] [CompleteSpace A] [T0Space A] [IsHuberRing A]
  {B : Type u} [CommRing B] [UniformSpace B] [IsUniformAddGroup B]
  [IsTopologicalRing B] [CompleteSpace B] [T0Space B] [IsHuberRing B]
  (P : PairOfDefinition A) (P' : PairOfDefinition B) (S : Pair A) (T : Pair B)
  (hS : P.ringOfDefinition ≤ S.plus) (hT : P'.ringOfDefinition ≤ T.plus)

/-- **Morphisms from an affinoid into `Spa(A, A⁺)` from global sections.** If `X` is isomorphic to
the spectrum of a complete Hausdorff Huber pair with sheafy structure presheaf, every continuous
ring map `A → 𝒪_X(X)` carrying `A⁺` into `𝒪_X⁺(X)` is the global-sections map of a morphism
`X ⟶ Spa(A, A⁺)`. -/
theorem exists_presentationLimitAppTop_eq_of_iso {X : PreAdicSpace.{u}}
    (hsheaf : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa T.plus))
      (presentationLimitPresheaf P' T.plus))
    (e : X ≅ presentationLimitPreAdicSpace P' T.plus
      T.isRingOfIntegralElements.isPowerBounded_of_mem hT)
    (φ : A →+* (X.toPresheafedSpace.presheaf.obj (Opposite.op ⊤)).obj) (hφ : Continuous φ)
    (hplus : ∀ a ∈ S.plus, φ a ∈ X.plusSubring ⊤) :
    ∃ f : X ⟶ presentationLimitPreAdicSpace P S.plus
        S.isRingOfIntegralElements.isPowerBounded_of_mem hS,
      presentationLimitAppTop P S.plus S.isRingOfIntegralElements.isPowerBounded_of_mem hS f =
        φ := by
  let I := presentationLimitPreAdicSpaceTopIso P' T.plus
    T.isRingOfIntegralElements.isPowerBounded_of_mem hT
  let ψ₀ := e.inv.appTop.comp φ
  let χ : Pair.Hom S T :=
    { toRingHom := I.hom.val.comp ψ₀
      continuous_toRingHom :=
        I.hom.property.comp (e.inv.continuous_appTop.comp hφ)
      map_mem_plus a ha := by
        have := T.isRingOfIntegralElements.isIntegrallyClosedIn
        exact presentationLimitPreAdicSpaceTopIso_hom_mem P' T.plus
          T.isRingOfIntegralElements.isPowerBounded_of_mem hT T.isRingOfIntegralElements.isOpen
          (e.inv.appTop_mem_plusSubring (hplus a ha)) }
  refine ⟨e.hom ≫ presentationLimitPreAdicSpacePairComap P P' hS hT hsheaf χ, ?_⟩
  rw [presentationLimitAppTop_comp, presentationLimitAppTop_pairComap]
  ext a
  simp only [χ, ψ₀, I, RingHom.comp_apply]
  rw [presentationLimitPreAdicSpaceTopIso_hom_inv_id_apply, ← RingHom.comp_apply,
    ← PreAdicSpace.Hom.appTop_comp, Iso.hom_inv_id, PreAdicSpace.Hom.appTop_id, RingHom.id_apply]

/-- **Morphisms from an adic space into an affinoid spectrum from global sections** (Huber 1994,
Proposition 2.1(ii)): for an adic space `X` and a complete Hausdorff Huber pair `(A, A⁺)`, every
continuous ring map `A → 𝒪_X(X)` carrying `A⁺` into `𝒪_X⁺(X)` is the global-sections map of a
morphism `X ⟶ Spa(A, A⁺)`. -/
theorem exists_presentationLimitAppTop_eq {X : PreAdicSpace.{u}} (hX : PreAdicSpace.isAdic X)
    (φ : A →+* (X.toPresheafedSpace.presheaf.obj (Opposite.op ⊤)).obj) (hφ : Continuous φ)
    (hplus : ∀ a ∈ S.plus, φ a ∈ X.plusSubring ⊤) :
    ∃ f : X ⟶ presentationLimitPreAdicSpace P S.plus
        S.isRingOfIntegralElements.isPowerBounded_of_mem hS,
      presentationLimitAppTop P S.plus S.isRingOfIntegralElements.isPowerBounded_of_mem hS f =
        φ := by
  let U : X.affinoidOpens → Opens X := fun i ↦ i.val
  have hU : ⨆ i, U i = ⊤ := by
    rw [← sSup_eq_iSup']
    exact (PreAdicSpace.isLocallyAffinoid_iff_sSup_eq_top X).mp hX.isLocallyAffinoid
  have hloc (i : X.affinoidOpens) : ∃ f : X.restrict (U i).isOpenEmbedding ⟶
      presentationLimitPreAdicSpace P S.plus S.isRingOfIntegralElements.isPowerBounded_of_mem hS,
      presentationLimitAppTop P S.plus S.isRingOfIntegralElements.isPowerBounded_of_mem hS f =
        (X.ofRestrict (U i).isOpenEmbedding).appTop.comp φ := by
    obtain ⟨B, _, _, _, _, _, _, _, T, P', hT, hsheaf, ⟨e⟩⟩ :=
      hX.isSheafy.exists_complete_isSheaf_of_mem_affinoidOpens i.property
    exact exists_presentationLimitAppTop_eq_of_iso P P' S T hS hT hsheaf e _
      ((X.ofRestrict (U i).isOpenEmbedding).continuous_appTop.comp hφ)
      fun a ha ↦ (X.ofRestrict (U i).isOpenEmbedding).appTop_mem_plusSubring (hplus a ha)
  choose f hf using hloc
  -- The morphisms on the open affinoid subspaces agree on overlaps, since morphisms into
  -- `Spa(A, A⁺)` from sheafy sources are determined by their global-sections maps, so they glue.
  have hcompat (i j : X.affinoidOpens) :
      pullback.fst (X.ofRestrict (U i).isOpenEmbedding) (X.ofRestrict (U j).isOpenEmbedding) ≫
        f i = pullback.snd _ _ ≫ f j := by
    have hP : PreAdicSpace.isSheafy (pullback (X.ofRestrict (U i).isOpenEmbedding)
        (X.ofRestrict (U j).isOpenEmbedding)) :=
      PreAdicSpace.isSheafy_of_isOpenImmersion hX.isSheafy
        (pullback.fst (X.ofRestrict (U i).isOpenEmbedding)
          (X.ofRestrict (U j).isOpenEmbedding) ≫ X.ofRestrict (U i).isOpenEmbedding)
    refine presentationLimitAppTop_injective P S.plus
      S.isRingOfIntegralElements.isPowerBounded_of_mem hS hP ?_
    rw [presentationLimitAppTop_comp, presentationLimitAppTop_comp, hf, hf, ← RingHom.comp_assoc,
      ← RingHom.comp_assoc, ← PreAdicSpace.Hom.appTop_comp, ← PreAdicSpace.Hom.appTop_comp,
      pullback.condition]
  refine ⟨PreAdicSpace.glueMorphisms hX.isSheafy U hU f hcompat, ?_⟩
  ext a
  refine PreAdicSpace.ext_of_appTop_ofRestrict hX.isSheafy U hU fun i ↦ ?_
  rw [← RingHom.comp_apply, ← presentationLimitAppTop_comp, PreAdicSpace.ofRestrict_glueMorphisms,
    hf, RingHom.comp_apply]

end ValuationSpectrum

namespace AdicSpace

open Huber ValuationSpectrum

variable {A : Type u} [CommRing A] [UniformSpace A] [IsUniformAddGroup A]
  [IsTopologicalRing A] [CompleteSpace A] [T0Space A] [IsHuberRing A]
  (P : PairOfDefinition A) (S : Pair A) (hS : P.ringOfDefinition ≤ S.plus)

/-- **Morphisms from an adic space into `Spa(A, A⁺)`** (Huber 1994, Proposition 2.1(ii)): for an
adic space `X` and a complete Hausdorff Huber pair `(A, A⁺)`, morphisms `X ⟶ Spa(A, A⁺)`
correspond bijectively to continuous ring maps `A → 𝒪_X(X)` carrying `A⁺` into `𝒪_X⁺(X)`, by
taking global sections. -/
noncomputable def homSpaEquiv (X : AdicSpace.{u}) :
    (X.obj ⟶ presentationLimitPreAdicSpace P S.plus
      S.isRingOfIntegralElements.isPowerBounded_of_mem hS) ≃
      {φ : A →+* (X.obj.toPresheafedSpace.presheaf.obj (Opposite.op ⊤)).obj //
        Continuous φ ∧ ∀ a ∈ S.plus, φ a ∈ X.obj.plusSubring ⊤} :=
  Equiv.ofBijective
    (fun f ↦ ⟨presentationLimitAppTop P S.plus S.isRingOfIntegralElements.isPowerBounded_of_mem hS
      f, continuous_presentationLimitAppTop _ _ _ _ f,
      fun _ ha ↦ presentationLimitAppTop_mem_plus _ _ _ _ f ha⟩)
    ⟨fun _ _ h ↦ presentationLimitAppTop_injective _ _ _ _ X.property.isSheafy
      (congrArg Subtype.val h),
     fun φ ↦ (exists_presentationLimitAppTop_eq P S hS X.property φ.val φ.property.1
      φ.property.2).imp fun _ hf ↦ Subtype.ext hf⟩

/-- The bijection `homSpaEquiv` is the global-sections map. -/
@[simp]
theorem coe_homSpaEquiv_apply (X : AdicSpace.{u})
    (f : X.obj ⟶ presentationLimitPreAdicSpace P S.plus
      S.isRingOfIntegralElements.isPowerBounded_of_mem hS) :
    (homSpaEquiv P S hS X f : A →+* (X.obj.toPresheafedSpace.presheaf.obj (Opposite.op ⊤)).obj) =
      presentationLimitAppTop P S.plus S.isRingOfIntegralElements.isPowerBounded_of_mem hS f :=
  (rfl)

/-- The global-sections map of the morphism corresponding to `φ` under `homSpaEquiv` is `φ`. -/
@[simp]
theorem presentationLimitAppTop_homSpaEquiv_symm (X : AdicSpace.{u})
    (φ : {φ : A →+* (X.obj.toPresheafedSpace.presheaf.obj (Opposite.op ⊤)).obj //
      Continuous φ ∧ ∀ a ∈ S.plus, φ a ∈ X.obj.plusSubring ⊤}) :
    presentationLimitAppTop P S.plus S.isRingOfIntegralElements.isPowerBounded_of_mem hS
      ((homSpaEquiv P S hS X).symm φ) = φ.val := by
  rw [← coe_homSpaEquiv_apply, Equiv.apply_symm_apply]

/-- **Naturality in the adic space**: precomposing with a morphism `h : W ⟶ X` of adic spaces
composes the global-sections map with `h^♯`. -/
theorem homSpaEquiv_comp {W X : AdicSpace.{u}} (h : W ⟶ X)
    (f : X.obj ⟶ presentationLimitPreAdicSpace P S.plus
      S.isRingOfIntegralElements.isPowerBounded_of_mem hS) :
    (homSpaEquiv P S hS W (h.hom ≫ f) :
        A →+* (W.obj.toPresheafedSpace.presheaf.obj (Opposite.op ⊤)).obj) =
      h.hom.appTop.comp (homSpaEquiv P S hS X f) :=
  presentationLimitAppTop_comp _ _ _ _ h.hom f

/-- **Morphisms to `Spa(A, A⁺)` for a quotient of `ℤ`.** If the canonical ring map `ℤ → A` is
surjective, every adic space has at most one morphism to `Spa(A, A⁺)`. -/
theorem subsingleton_homSpa_of_intCast_surjective (h : Function.Surjective (Int.castRingHom A))
    (X : AdicSpace.{u}) :
    Subsingleton (X.obj ⟶ presentationLimitPreAdicSpace P S.plus
      S.isRingOfIntegralElements.isPowerBounded_of_mem hS) :=
  (homSpaEquiv P S hS X).subsingleton_congr.mpr
    ⟨fun _ _ ↦ Subtype.ext <| (RingHom.cancel_right h).mp (RingHom.ext_int _ _)⟩

/-- **Morphisms to `Spa(ℤ, ℤ)`**: if `A` is discrete and isomorphic to `ℤ` as a ring, every adic
space has exactly one morphism to `Spa(A, A⁺)`. -/
@[instance_reducible]
noncomputable def uniqueHomSpaOfRingEquivInt [DiscreteTopology A] (e : A ≃+* ℤ)
    (X : AdicSpace.{u}) :
    Unique (X.obj ⟶ presentationLimitPreAdicSpace P S.plus
      S.isRingOfIntegralElements.isPowerBounded_of_mem hS) :=
  -- the only ring map `A → 𝒪_X(X)` is the one through `ℤ`; it is continuous because `A` is
  -- discrete, and it lands in the integral sections because they form a subring
  haveI := subsingleton_homSpa_of_intCast_surjective P S hS
    (fun a ↦ ⟨e a, (map_intCast e.symm (e a)).symm.trans (e.symm_apply_apply a)⟩) X
  uniqueOfSubsingleton <| (homSpaEquiv P S hS X).symm
    ⟨(Int.castRingHom _).comp e.toRingHom, continuous_of_discreteTopology,
      fun a _ ↦ intCast_mem _ (e a)⟩

/-- **Morphisms to `Spa(0, 0)` are unique.** If `A` is the zero ring, every adic space has at
most one morphism to `Spa(A, A⁺)`. -/
theorem subsingleton_homSpa_of_subsingleton [Subsingleton A] (X : AdicSpace.{u}) :
    Subsingleton (X.obj ⟶ presentationLimitPreAdicSpace P S.plus
      S.isRingOfIntegralElements.isPowerBounded_of_mem hS) :=
  subsingleton_homSpa_of_intCast_surjective P S hS (fun _ ↦ ⟨0, Subsingleton.elim _ _⟩) X

/-- **Only the empty adic space maps to `Spa(0, 0)`**: if `A` is the zero ring, an adic space `X`
has a morphism to `Spa(A, A⁺)` exactly when it is empty. -/
theorem nonempty_homSpa_iff_isEmpty_of_subsingleton [Subsingleton A] (X : AdicSpace.{u}) :
    Nonempty (X.obj ⟶ presentationLimitPreAdicSpace P S.plus
      S.isRingOfIntegralElements.isPowerBounded_of_mem hS) ↔ IsEmpty X.obj := by
  -- a ring map `A → 𝒪_X(X)` exists exactly when `𝒪_X(X) = 0`, which happens exactly when `X` is
  -- empty
  rw [(homSpaEquiv P S hS X).nonempty_congr]
  refine Iff.trans ⟨fun ⟨φ⟩ ↦ φ.val.codomain_trivial, fun hs ↦ ?_⟩
    (SheafyPreAdicSpace.subsingleton_presheaf_obj_top_iff_isEmpty ⟨X.obj, X.property.isSheafy⟩)
  -- `hs` is stated for the sheafy pre-adic space `⟨X.obj, _⟩`, whose `obj` projection is
  -- `X.obj` by definition; restate it in terms of `X.obj`
  have : Subsingleton (X.obj.toPresheafedSpace.presheaf.obj (Opposite.op ⊤)).obj := hs
  let φ : A →+* (X.obj.toPresheafedSpace.presheaf.obj (Opposite.op ⊤)).obj :=
    { toFun := 0
      map_one' := Subsingleton.elim _ _
      map_mul' _ _ := Subsingleton.elim _ _
      map_zero' := rfl
      map_add' _ _ := Subsingleton.elim _ _ }
  exact ⟨⟨φ, continuous_of_const fun _ _ ↦ Subsingleton.elim _ _, fun a _ ↦ by
    rw [Subsingleton.elim (φ a) 0]
    exact zero_mem _⟩⟩

end AdicSpace

end TauCeti
