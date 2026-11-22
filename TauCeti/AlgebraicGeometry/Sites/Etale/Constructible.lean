/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.CategoryTheory.ObjectProperty.ContainsZero
public import TauCeti.AlgebraicGeometry.Scheme.ConstructibleStratification
public import TauCeti.AlgebraicGeometry.Sites.Etale.ModuleSheaf

/-!
# Constructible étale sheaves of modules

Let `X` be a scheme and `Λ` a ring. An étale sheaf of `Λ`-modules `F` on `X` is *constructible*
when every affine open `U` of `X` admits a constructible stratification
(`AlgebraicGeometry.Scheme.ConstructibleStratification`) on each of whose strata the pullback of
`F` is locally constant with finitely generated values, that is finite lisse
(`CategoryTheory.Sheaf.IsFiniteLisse`). This affine-local form is the definition of Stacks,
Tag 03RW; no Noetherian hypothesis on `X` or `Λ` enters it.

## Main declarations

* `CategoryTheory.Sheaf.IsConstructibleOn F U`: some constructible stratification of the open `U`
  has strata on which `F` is finite lisse.
* `CategoryTheory.Sheaf.IsConstructibleOn.mono`,
  `CategoryTheory.Sheaf.IsConstructibleOn.of_iSup_eq` and
  `CategoryTheory.Sheaf.isConstructibleOn_of_isCompact`: the condition passes to smaller opens,
  and on a quasi-compact quasi-separated open it can be checked locally.
* `CategoryTheory.Sheaf.IsConstructibleOn.smallEtalePullback` and
  `CategoryTheory.Sheaf.isConstructibleOn_image_iff`: the condition is stable under pullback along
  any morphism of schemes, and transported along open immersions.
* `AlgebraicGeometry.Scheme.constructibleSheaf X Λ`: the constructible étale sheaves of
  `Λ`-modules on `X`, as a property of objects closed under isomorphisms and containing zero.
* `AlgebraicGeometry.Scheme.constructibleSheaf_iff_isConstructibleOn_top`: on a quasi-compact
  quasi-separated scheme, a sheaf is constructible exactly when one constructible stratification
  of the whole scheme works (Stacks, Tag 095E and Tag 09YR).
* `AlgebraicGeometry.Scheme.constructibleSheaf_smallEtalePullback` and
  `AlgebraicGeometry.Scheme.constructibleSheaf_iff_of_openCover`: constructible sheaves are stable
  under pullback, and constructibility can be checked on an open cover.
* `AlgebraicGeometry.Scheme.constructibleSheaf_of_isFiniteLisse`: finite lisse sheaves, in
  particular constant sheaves on finitely generated modules, are constructible.

## References

* M. Artin, A. Grothendieck, J.-L. Verdier, *SGA 4*, Exposé IX, §2.
* The Stacks Project, Section 59.71, Constructible sheaves, Tag 03RW, Tag 095E and Tag 09YR.
-/

public section

universe u

open CategoryTheory Limits Topology Set.Notation AlgebraicGeometry Scheme

namespace CategoryTheory.Sheaf

variable {X Y : Scheme.{u}} {Λ : Type u} [Ring Λ]

/-- An étale sheaf of `Λ`-modules `F` on `X` is *constructible on* an open `U` when some
constructible stratification of `U` has strata on each of which the pullback of `F` is finite
lisse. -/
def IsConstructibleOn (F : Sheaf (smallEtaleTopology X) (ModuleCat.{u} Λ)) (U : X.Opens) : Prop :=
  ∃ S : X.ConstructibleStratification U,
    ∀ i, (((S.f i).smallEtalePullback (ModuleCat.{u} Λ)).obj F).IsFiniteLisse

variable {F G : Sheaf (smallEtaleTopology X) (ModuleCat.{u} Λ)} {U V : X.Opens}

lemma isConstructibleOn_iff :
    F.IsConstructibleOn U ↔ ∃ S : X.ConstructibleStratification U,
      ∀ i, (((S.f i).smallEtalePullback (ModuleCat.{u} Λ)).obj F).IsFiniteLisse :=
  Iff.rfl

lemma IsConstructibleOn.of_iso (e : F ≅ G) (hF : F.IsConstructibleOn U) :
    G.IsConstructibleOn U := by
  obtain ⟨S, hS⟩ := hF
  exact ⟨S, fun i ↦ (hS i).of_iso (((S.f i).smallEtalePullback _).mapIso e)⟩

/-- A finite lisse sheaf is constructible on every open, through the stratification with the
single stratum. -/
lemma IsFiniteLisse.isConstructibleOn (hF : F.IsFiniteLisse) (U : X.Opens) :
    F.IsConstructibleOn U :=
  ⟨.single U, fun _ ↦ hF.smallEtalePullback _⟩

/-- A sheaf constructible on `U` is constructible on every open `V ≤ U`. -/
lemma IsConstructibleOn.mono (hF : F.IsConstructibleOn U) (hVU : V ≤ U) :
    F.IsConstructibleOn V := by
  obtain ⟨S, hS⟩ := hF
  refine ⟨S.restrict hVU, fun i ↦ ?_⟩
  exact ((hS i).smallEtalePullback (Limits.pullback.fst (S.f i) V.ι)).of_iso
    ((Hom.smallEtalePullbackComp (Limits.pullback.fst (S.f i) V.ι) (S.f i) _).app F).symm

/-- **Pullback of constructibility.** If `F` is constructible on `U ⊆ X`, then its pullback along
`g : Y ⟶ X` is constructible on `g ⁻¹ᵁ U`. -/
lemma IsConstructibleOn.smallEtalePullback (hF : F.IsConstructibleOn U) (g : Y ⟶ X) :
    ((g.smallEtalePullback (ModuleCat.{u} Λ)).obj F).IsConstructibleOn (g ⁻¹ᵁ U) := by
  obtain ⟨S, hS⟩ := hF
  refine ⟨S.pullback g, fun i ↦ ?_⟩
  exact ((hS i).smallEtalePullback (Limits.pullback.fst (S.f i) g)).of_iso
    (((Hom.smallEtalePullbackComp (Limits.pullback.fst (S.f i) g) (S.f i) _).app F).symm ≪≫
      (Hom.smallEtalePullbackCongr Limits.pullback.condition _).app F ≪≫
        (Hom.smallEtalePullbackComp (Limits.pullback.snd (S.f i) g) g _).app F)

/-- Along an open immersion `j : Y ⟶ X`, a sheaf `F` on `X` is constructible on the image
`j ''ᵁ W` of an open `W` of `Y` if and only if its pullback to `Y` is constructible on `W`. -/
lemma isConstructibleOn_image_iff (j : Y ⟶ X) [IsOpenImmersion j] (W : Y.Opens) :
    F.IsConstructibleOn (j ''ᵁ W) ↔
      ((j.smallEtalePullback (ModuleCat.{u} Λ)).obj F).IsConstructibleOn W := by
  refine ⟨fun hF ↦ j.preimage_image_eq W ▸ hF.smallEtalePullback j, fun ⟨S, hS⟩ ↦ ?_⟩
  refine ⟨S.map j, fun i ↦ ?_⟩
  exact (hS i).of_iso ((Hom.smallEtalePullbackComp (S.f i) j _).app F).symm

/-- **Gluing constructibility.** A sheaf constructible on each member of a finite cover of `U` by
opens whose traces on `U` are retrocompact is constructible on `U`. -/
lemma IsConstructibleOn.of_iSup_eq {κ : Type*} [Finite κ] {V : κ → X.Opens}
    (hVU : ⨆ k, V k = U) (hV : ∀ k, IsRetrocompact ((U : Set X) ↓∩ (V k : Set X)))
    (hF : ∀ k, F.IsConstructibleOn (V k)) : F.IsConstructibleOn U := by
  choose S hS using hF
  obtain ⟨T, hT⟩ := ConstructibleStratification.exists_of_iSup_eq hVU hV S
  refine ⟨T, fun j ↦ ?_⟩
  obtain ⟨k, i, h, hh⟩ := hT j
  exact ((hS k i).smallEtalePullback h).of_iso
    (((Hom.smallEtalePullbackComp h ((S k).f i) _).app F).symm ≪≫
      (Hom.smallEtalePullbackCongr hh _).app F)

/-- **Constructibility is local on a quasi-compact quasi-separated open.** If every point of the
quasi-compact quasi-separated open `U` has an open neighbourhood inside `U` on which `F` is
constructible, then `F` is constructible on `U`. -/
theorem isConstructibleOn_of_isCompact (hU : IsCompact (U : Set X))
    (hU' : IsQuasiSeparated (U : Set X))
    (h : ∀ x ∈ U, ∃ W : X.Opens, x ∈ W ∧ W ≤ U ∧ F.IsConstructibleOn W) :
    F.IsConstructibleOn U := by
  have h' (x : U) : ∃ W : X.Opens, IsAffineOpen W ∧ x.val ∈ W ∧ W ≤ U ∧ F.IsConstructibleOn W := by
    obtain ⟨W, hxW, hWU, hW⟩ := h x x.property
    obtain ⟨W', hW', hxW', hW'W⟩ := exists_isAffineOpen_mem_and_subset hxW
    exact ⟨W', hW', hxW', hW'W.trans hWU, hW.mono hW'W⟩
  choose W hWa hxW hWU hW using h'
  obtain ⟨t, ht⟩ := hU.elim_finite_subcover (fun x : U ↦ (W x : Set X)) (fun x ↦ (W x).isOpen)
    fun x hx ↦ Set.mem_iUnion.mpr ⟨⟨x, hx⟩, hxW _⟩
  have : QuasiSeparatedSpace (U : Set X) :=
    (isQuasiSeparated_iff_quasiSeparatedSpace _ U.isOpen).mp hU'
  refine IsConstructibleOn.of_iSup_eq (V := fun x : t ↦ W x)
    (le_antisymm (iSup_le fun x ↦ hWU x) fun y hy ↦ ?_) (fun x ↦ ?_) fun x ↦ hW x
  · obtain ⟨x, hx, hyx⟩ := Set.mem_iUnion₂.mp (ht hy)
    exact (le_iSup (fun x : t ↦ W x) ⟨x, hx⟩) hyx
  · refine IsCompact.isRetrocompact ?_ ((W x).isOpen.preimage continuous_subtypeVal)
    rw [Subtype.isCompact_iff, Subtype.image_preimage_coe, Set.inter_eq_right.mpr (hWU x)]
    exact (hWa x).isCompact

end CategoryTheory.Sheaf

namespace AlgebraicGeometry.Scheme

open CategoryTheory.Sheaf

variable (X : Scheme.{u}) (Λ : Type u) [Ring Λ]

/-- The *constructible* étale sheaves of `Λ`-modules on `X` (Stacks, Tag 03RW): those sheaves
which are constructible on every affine open of `X`, that is, every affine open admits a
constructible stratification on whose strata the sheaf is locally constant with finitely generated
values. -/
def constructibleSheaf : ObjectProperty (Sheaf (smallEtaleTopology X) (ModuleCat.{u} Λ)) :=
  fun F ↦ ∀ U : X.Opens, IsAffineOpen U → F.IsConstructibleOn U

variable {X Λ} {Y : Scheme.{u}} {F : Sheaf (smallEtaleTopology X) (ModuleCat.{u} Λ)}

lemma constructibleSheaf_iff :
    X.constructibleSheaf Λ F ↔ ∀ U : X.Opens, IsAffineOpen U → F.IsConstructibleOn U :=
  Iff.rfl

instance : (X.constructibleSheaf Λ).IsClosedUnderIsomorphisms where
  of_iso e hF U hU := (hF U hU).of_iso e

/-- Finite lisse sheaves are constructible. -/
lemma constructibleSheaf_of_isFiniteLisse (hF : F.IsFiniteLisse) : X.constructibleSheaf Λ F :=
  fun U _ ↦ hF.isConstructibleOn U

/-- The constant sheaf on a finitely generated `Λ`-module is constructible. -/
lemma constructibleSheaf_constantSheaf (M : ModuleCat.{u} Λ) [Module.Finite Λ M] :
    X.constructibleSheaf Λ ((constantSheaf (smallEtaleTopology X) (ModuleCat.{u} Λ)).obj M) :=
  constructibleSheaf_of_isFiniteLisse (isFiniteLisse_constantSheaf M)

/-- The zero sheaf, the constant sheaf on the zero module, is constructible. -/
instance : (X.constructibleSheaf Λ).ContainsZero where
  exists_zero := ⟨_, Functor.map_isZero (constantSheaf (smallEtaleTopology X) (ModuleCat.{u} Λ))
    (ModuleCat.isZero_of_subsingleton (ModuleCat.of Λ PUnit)),
    constructibleSheaf_constantSheaf (ModuleCat.of Λ PUnit)⟩

/-- **Global stratifications on a quasi-compact quasi-separated scheme.** On a quasi-compact
quasi-separated scheme `X`, an étale sheaf of `Λ`-modules is constructible if and only if a single
constructible stratification of `X` has strata on which it is finite lisse (Stacks, Tag 095E and
Tag 09YR). -/
theorem constructibleSheaf_iff_isConstructibleOn_top [CompactSpace X] [QuasiSeparatedSpace X] :
    X.constructibleSheaf Λ F ↔ F.IsConstructibleOn ⊤ := by
  refine ⟨fun hF ↦ isConstructibleOn_of_isCompact (by simpa using isCompact_univ)
    (by simpa using IsQuasiSeparated.of_quasiSeparatedSpace (Set.univ : Set X)) fun x _ ↦ ?_,
    fun hF U _ ↦ hF.mono le_top⟩
  obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset (TopologicalSpace.Opens.mem_top x)
  exact ⟨U, hxU, le_top, hF U hU⟩

/-- **Pullback of constructible sheaves.** The pullback of a constructible étale sheaf of
`Λ`-modules along any morphism of schemes `g : Y ⟶ X` is constructible. -/
theorem constructibleSheaf_smallEtalePullback (hF : X.constructibleSheaf Λ F) (g : Y ⟶ X) :
    Y.constructibleSheaf Λ ((g.smallEtalePullback (ModuleCat.{u} Λ)).obj F) := by
  refine fun V hV ↦ isConstructibleOn_of_isCompact hV.isCompact hV.isQuasiSeparated fun y hy ↦ ?_
  obtain ⟨U, hU, hgyU, -⟩ :=
    exists_isAffineOpen_mem_and_subset (TopologicalSpace.Opens.mem_top (g y))
  exact ⟨g ⁻¹ᵁ U ⊓ V, ⟨hgyU, hy⟩, inf_le_right, ((hF U hU).smallEtalePullback g).mono inf_le_left⟩

/-- **Zariski descent for constructible sheaves.** An étale sheaf of `Λ`-modules on `X` is
constructible if and only if its restrictions to the pieces of an open cover `𝒰` of `X` are
constructible. -/
theorem constructibleSheaf_iff_of_openCover (𝒰 : X.OpenCover) :
    X.constructibleSheaf Λ F ↔
      ∀ i, (𝒰.X i).constructibleSheaf Λ (((𝒰.f i).smallEtalePullback (ModuleCat.{u} Λ)).obj F) := by
  refine ⟨fun hF i ↦ constructibleSheaf_smallEtalePullback hF (𝒰.f i), fun h U hU ↦ ?_⟩
  refine isConstructibleOn_of_isCompact hU.isCompact hU.isQuasiSeparated fun x hx ↦ ?_
  obtain ⟨y, hy⟩ := 𝒰.covers x
  obtain ⟨W, hW, hyW, hWU⟩ :=
    exists_isAffineOpen_mem_and_subset (x := y) (U := 𝒰.f (𝒰.idx x) ⁻¹ᵁ U)
      (by simpa [hy] using hx)
  refine ⟨𝒰.f (𝒰.idx x) ''ᵁ W, ⟨y, hyW, hy⟩, ?_, (isConstructibleOn_image_iff _ W).mpr (h _ W hW)⟩
  rintro _ ⟨z, hz, rfl⟩
  exact hWU hz

end AlgebraicGeometry.Scheme
