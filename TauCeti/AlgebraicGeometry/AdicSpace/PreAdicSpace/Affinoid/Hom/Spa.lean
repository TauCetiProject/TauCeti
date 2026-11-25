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
* `TauCeti.AdicSpace.subsingleton_homSpa_of_subsingleton`,
  `TauCeti.AdicSpace.nonempty_homSpa_iff_isEmpty_of_subsingleton`: morphisms to `Spa(0, 0)` are
  unique, and exist exactly from the empty adic space.
* `TauCeti.AdicSpace.subsingleton_presheaf_obj_top_of_isEmpty`: the global sections of an empty
  adic space vanish.

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

/-- **Global sections of an empty adic space vanish.** The structure presheaf of an adic space is
a sheaf, so its value on the empty open, which is `⊤` here, is a terminal complete separated ring;
the map to it from the zero ring forces `1 = 0`. -/
theorem subsingleton_presheaf_obj_top_of_isEmpty (X : AdicSpace.{u}) [IsEmpty X.obj] :
    Subsingleton (X.obj.toPresheafedSpace.presheaf.obj (Opposite.op ⊤)).obj := by
  let F : TopCat.Sheaf CompleteSeparatedTopCommRingCat.{u} X.obj.toTopCat :=
    ⟨X.obj.toPresheafedSpace.presheaf, X.property.isSheafy⟩
  have h : (⊤ : Opens X.obj.toTopCat) = ⊥ := by
    ext x
    exact isEmptyElim x
  let t := (F.isTerminalOfEqEmpty h).from (⟨TopCommRingCat.of PUnit.{u + 1},
    (TopCommRingCat.isCompleteSeparated_iff _).mpr
      (TopCommRingCat.isCompleteSeparated_of_completeSpace_of_t0Space _)⟩ :
      CompleteSeparatedTopCommRingCat.{u})
  have h01 : (1 : (X.obj.toPresheafedSpace.presheaf.obj (Opposite.op ⊤)).obj) = 0 := by
    have := congrArg t.hom.val (Subsingleton.elim (α := PUnit.{u + 1}) 1 0)
    exact (map_one t.hom.val).symm.trans (this.trans (map_zero t.hom.val))
  exact ⟨fun a b ↦ by rw [← mul_one a, ← mul_one b, h01, mul_zero, mul_zero]⟩

/-- **Morphisms to `Spa(ℤ, ℤ)`** (the discrete-target Check of `homSpaEquiv`): if `A` is discrete
and isomorphic to `ℤ` as a ring, every adic space has exactly one morphism to `Spa(A, A⁺)`. The
only ring map `A → 𝒪_X(X)` is the one through `ℤ`; it is continuous because `A` is discrete, and
it lands in the integral sections because they form a subring. -/
@[instance_reducible]
noncomputable def uniqueHomSpaOfRingEquivInt [DiscreteTopology A] (e : A ≃+* ℤ)
    (X : AdicSpace.{u}) :
    Unique (X.obj ⟶ presentationLimitPreAdicSpace P S.plus
      S.isRingOfIntegralElements.isPowerBounded_of_mem hS) :=
  letI : Unique {φ : A →+* (X.obj.toPresheafedSpace.presheaf.obj (Opposite.op ⊤)).obj //
      Continuous φ ∧ ∀ a ∈ S.plus, φ a ∈ X.obj.plusSubring ⊤} :=
    { default := ⟨(Int.castRingHom _).comp e.toRingHom, continuous_of_discreteTopology,
        fun a _ ↦ intCast_mem _ (e a)⟩
      uniq φ := Subtype.ext <| RingHom.ext fun a ↦ by
        have h := RingHom.congr_fun
          (RingHom.ext_int (φ.val.comp e.symm.toRingHom) (Int.castRingHom _)) (e a)
        rw [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
          e.symm_apply_apply] at h
        exact h }
  (homSpaEquiv P S hS X).unique

/-- **Morphisms to `Spa(0, 0)` are unique.** If `A` is the zero ring, every adic space has at
most one morphism to `Spa(A, A⁺)`. -/
theorem subsingleton_homSpa_of_subsingleton [Subsingleton A] (X : AdicSpace.{u}) :
    Subsingleton (X.obj ⟶ presentationLimitPreAdicSpace P S.plus
      S.isRingOfIntegralElements.isPowerBounded_of_mem hS) :=
  (homSpaEquiv P S hS X).subsingleton_congr.mpr
    ⟨fun φ ψ ↦ Subtype.ext <| RingHom.ext fun a ↦ by
      rw [Subsingleton.elim a 0, map_zero, map_zero]⟩

/-- **Only the empty adic space maps to `Spa(0, 0)`** (the zero-target Check of `homSpaEquiv`): if
`A` is the zero ring, an adic space `X` has a morphism to `Spa(A, A⁺)` exactly when it is empty.
A ring map `A → 𝒪_X(X)` forces `𝒪_X(X) = 0`, which fails at any point since the stalks are local
rings; conversely the global sections of the empty space are zero. -/
theorem nonempty_homSpa_iff_isEmpty_of_subsingleton [Subsingleton A] (X : AdicSpace.{u}) :
    Nonempty (X.obj ⟶ presentationLimitPreAdicSpace P S.plus
      S.isRingOfIntegralElements.isPowerBounded_of_mem hS) ↔ IsEmpty X.obj := by
  rw [(homSpaEquiv P S hS X).nonempty_congr]
  refine ⟨fun ⟨φ⟩ ↦ ⟨fun x ↦ ?_⟩, fun _ ↦ ?_⟩
  · have : Nontrivial (X.obj.toPresheafedSpace.presheaf.obj (Opposite.op ⊤)).obj :=
      (X.obj.toRingPresheafedSpace.presheaf.germ ⊤ x (Opens.mem_top x)).hom.domain_nontrivial
    exact one_ne_zero <| (map_one φ.val).symm.trans <|
      (congrArg φ.val (Subsingleton.elim 1 0)).trans (map_zero φ.val)
  · have := subsingleton_presheaf_obj_top_of_isEmpty X
    let φ : A →+* (X.obj.toPresheafedSpace.presheaf.obj (Opposite.op ⊤)).obj :=
      ⟨⟨⟨0, Subsingleton.elim _ _⟩, fun _ _ ↦ Subsingleton.elim _ _⟩, Subsingleton.elim _ _,
        fun _ _ ↦ Subsingleton.elim _ _⟩
    exact ⟨⟨φ, continuous_of_const fun _ _ ↦ Subsingleton.elim _ _, fun a _ ↦ by
      rw [Subsingleton.elim (φ a) 0]
      exact zero_mem _⟩⟩

end AdicSpace

end TauCeti
