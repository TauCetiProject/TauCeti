/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.Extension.Basic
public import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.FinitePresentation
public import TauCeti.AlgebraicGeometry.Modules.Restriction.FinitePresentation

/-!
# Extension of finitely presented modules

On a quasi-compact quasi-separated scheme, a quasi-coherent module that is finitely presented on
a quasi-compact open receives a morphism from a finitely presented module that is an isomorphism
there. Consequently, along a quasi-compact open immersion `j : U ⟶ X` into a quasi-compact
quasi-separated scheme, a morphism `F ⟶ j^* H` from a finitely presented `𝒪_U`-module to the
restriction of a quasi-coherent `𝒪_X`-module is the restriction of a morphism `G ⟶ H` from a
finitely presented `𝒪_X`-module, and every finitely presented `𝒪_U`-module is the restriction of a
finitely presented `𝒪_X`-module.

The construction covers `X` by finitely many affine opens and enlarges the open of finite
presentation one affine `W` at a time. On `W` it applies the affine approximation
`Scheme.Modules.exists_isFinitePresentation_isIso_restrict`, and it extends the result along
`W ⟶ X` by `Scheme.Modules.exists_isQuasicoherent_restrictFunctor_map_eq`, which changes nothing
over the region already treated.

## References

* The Stacks Project, Lemmas 28.23.4 (Tag 01PI) and 28.23.5 (Tag 0G41).
-/

public section

open CategoryTheory TopologicalSpace
open TauCeti.AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

-- This is the affine enlargement step in the finite-cover construction below.
private theorem exists_finitePresentation_restrict_sup [QuasiSeparatedSpace X]
    {N : X.Modules} [N.IsQuasicoherent] (V : X.Opens) (hV : IsCompact (V : Set X))
    [(N.restrict V.ι).IsFinitePresentation] (U : X.affineOpens) :
    ∃ (N' : X.Modules) (_ : N'.IsQuasicoherent) (i : N' ⟶ N),
      IsIso ((restrictFunctor V.ι).map i) ∧ (N'.restrict (V ⊔ U.1).ι).IsFinitePresentation := by
  have : IsAffine U.1.toScheme := U.2
  have : QuasiCompact U.1.ι := inferInstance
  let W := U.1.ι ⁻¹ᵁ V
  let f := U.1.ι.resLE V W le_rfl
  have : IsOpenImmersion f := by dsimp [f, Scheme.Hom.resLE]; infer_instance
  have : ((N.restrict V.ι).restrict f).IsFinitePresentation := inferInstance
  have : ((N.restrict U.1.ι).restrict W.ι).IsFinitePresentation :=
    (SheafOfModules.isFinitePresentation W.toScheme.ringCatSheaf).prop_of_iso
      (((restrictFunctorComp f V.ι).app N).symm ≪≫
        (restrictFunctorCongr (U.1.ι.resLE_comp_ι le_rfl)).app N ≪≫
        (restrictFunctorComp W.ι U.1.ι).app N) this
  obtain ⟨Q, _, q, hq⟩ :=
    exists_isFinitePresentation_isIso_restrict (N := N.restrict U.1.ι) W
      (U.1.ι.isCompact_preimage hV)
  have : Q.IsQuasicoherent := SheafOfModules.instIsQuasicoherentOfIsFinitePresentation Q
  obtain ⟨N', _, i, e, -, hkeep⟩ := exists_isQuasicoherent_restrictFunctor_map_eq U.1.ι q
  have hi : IsIso ((restrictFunctor V.ι).map i) := hkeep V hq
  have : (N'.restrict V.ι).IsFinitePresentation :=
    (SheafOfModules.isFinitePresentation V.toScheme.ringCatSheaf).prop_of_iso
      (asIso ((restrictFunctor V.ι).map i)).symm inferInstance
  have : (N'.restrict U.1.ι).IsFinitePresentation :=
    (SheafOfModules.isFinitePresentation U.1.toScheme.ringCatSheaf).prop_of_iso e.symm
      inferInstance
  refine ⟨N', inferInstance, i, hi, ?_⟩
  rw [sup_eq_iSup V U.1]
  exact isFinitePresentation_restrict_iSup N' (fun b : Bool ↦ cond b V U.1)
    (by intro b; cases b <;> assumption)

/-- On a quasi-compact quasi-separated scheme, a quasi-coherent module `N` that is finitely
presented on a quasi-compact open `V` receives a morphism from a finitely presented module that
is an isomorphism over `V`. No finiteness condition is imposed on `N` away from `V`. -/
theorem exists_isFinitePresentation_isIso_restrict_of_quasiSeparatedSpace
    [CompactSpace X] [QuasiSeparatedSpace X] {N : X.Modules} [N.IsQuasicoherent]
    (V : X.Opens) (hV : IsCompact (V : Set X)) [(N.restrict V.ι).IsFinitePresentation] :
    ∃ (N' : X.Modules) (_ : N'.IsFinitePresentation) (i : N' ⟶ N),
      IsIso ((restrictFunctor V.ι).map i) := by
  classical
  -- The invariant retains finite presentation on `V` and the affine opens already visited.
  have aux (s : Finset X.affineOpens) :
      ∃ (N' : X.Modules) (_ : N'.IsQuasicoherent) (i : N' ⟶ N),
        IsIso ((restrictFunctor V.ι).map i) ∧
          (N'.restrict (V ⊔ ⨆ U ∈ s, U.1).ι).IsFinitePresentation := by
    induction s using Finset.induction_on with
    | empty =>
      refine ⟨N, inferInstance, 𝟙 N, ?_, ?_⟩
      · rw [CategoryTheory.Functor.map_id]
        infer_instance
      · have h : V ⊔ ⨆ U ∈ (∅ : Finset X.affineOpens), U.1 = V := by simp
        rw [h]
        infer_instance
    | insert U s _ ih =>
      obtain ⟨M, _, i, hi, hM⟩ := ih
      let W := V ⊔ ⨆ U ∈ s, U.1
      have hW : IsCompact (W : Set X) :=
        hV.union (by simpa using s.finite_toSet.isCompact_biUnion (fun U _ ↦ U.2.isCompact))
      have : (M.restrict W.ι).IsFinitePresentation := hM
      obtain ⟨M', _, a, ha, hM'⟩ := exists_finitePresentation_restrict_sup (N := M) W hW U
      have : IsIso ((restrictFunctor V.ι).map a) :=
        isIso_restrictFunctor_map_of_le a (W := W) le_sup_left
      refine ⟨M', inferInstance, a ≫ i, ?_, ?_⟩
      · rw [CategoryTheory.Functor.map_comp]
        infer_instance
      · rw [Finset.iSup_insert, ← sup_assoc, sup_right_comm]
        exact hM'
  have hX : IsCompact ((⊤ : X.Opens) : Set X) := isCompact_univ
  obtain ⟨s, hs, hcover⟩ := isCompact_iff_finite_and_eq_biUnion_affineOpens.mp hX
  obtain ⟨N', _, i, hi, hN'⟩ := aux hs.toFinset
  have htop : V ⊔ ⨆ U ∈ hs.toFinset, U.1 = ⊤ := by simpa using congrArg (V ⊔ ·) hcover.symm
  rw [htop] at hN'
  have : ((N'.restrict (⊤ : X.Opens).ι).restrict X.topIso.inv).IsFinitePresentation :=
    inferInstance
  have : N'.IsFinitePresentation :=
    (SheafOfModules.isFinitePresentation X.ringCatSheaf).prop_of_iso
      (((restrictFunctorComp X.topIso.inv (⊤ : X.Opens).ι).app N').symm ≪≫
        (restrictFunctorCongr (X.toIso_inv_ι)).app N' ≪≫ restrictFunctorId.app N') this
  exact ⟨N', this, i, hi⟩

/-- **Extension of morphisms from finitely presented modules.** Let `j : U ⟶ X` be a
quasi-compact open immersion into a quasi-compact quasi-separated scheme, `H` a quasi-coherent
`𝒪_X`-module and `φ : F ⟶ j^* H` a morphism from a finitely presented `𝒪_U`-module. Then `φ` is
the restriction of a morphism `ψ : G ⟶ H` from a finitely presented `𝒪_X`-module: there is an
isomorphism `j^* G ≅ F` carrying `j^* ψ` to `φ`. -/
theorem exists_isFinitePresentation_restrictFunctor_map_eq [CompactSpace X]
    [QuasiSeparatedSpace X] {U : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    {H : X.Modules} [H.IsQuasicoherent] {F : U.Modules} [F.IsFinitePresentation]
    (φ : F ⟶ H.restrict j) :
    ∃ (G : X.Modules) (_ : G.IsFinitePresentation) (ψ : G ⟶ H) (e : G.restrict j ≅ F),
      (restrictFunctor j).map ψ = e.hom ≫ φ := by
  have : F.IsQuasicoherent := SheafOfModules.instIsQuasicoherentOfIsFinitePresentation F
  obtain ⟨P, _, p, e, he, -⟩ := exists_isQuasicoherent_restrictFunctor_map_eq j φ
  have : (P.restrict j).IsFinitePresentation :=
    (SheafOfModules.isFinitePresentation U.ringCatSheaf).prop_of_iso e.symm inferInstance
  have : ((P.restrict j).restrict j.isoOpensRange.inv).IsFinitePresentation := inferInstance
  have : (P.restrict j.opensRange.ι).IsFinitePresentation :=
    (SheafOfModules.isFinitePresentation j.opensRange.toScheme.ringCatSheaf).prop_of_iso
      (((restrictFunctorComp j.isoOpensRange.inv j).app P).symm ≪≫
        (restrictFunctorCongr j.isoOpensRange_inv_comp).app P) this
  have : CompactSpace U := QuasiCompact.compactSpace_of_compactSpace j
  have hV : IsCompact (j.opensRange : Set X) := isCompact_range j.continuous
  obtain ⟨G, _, b, hb⟩ :=
    exists_isFinitePresentation_isIso_restrict_of_quasiSeparatedSpace (N := P) j.opensRange hV
  have : IsIso ((restrictFunctor j).map b) := (isIso_restrictFunctor_map_iff_opensRange j b).mpr hb
  refine ⟨G, inferInstance, b ≫ p, asIso ((restrictFunctor j).map b) ≪≫ e, ?_⟩
  simp [CategoryTheory.Functor.map_comp, he]

/-- A finitely presented module on a quasi-compact open subscheme of a quasi-compact
quasi-separated scheme extends to a finitely presented module on the whole scheme. -/
theorem exists_isFinitePresentation_restrict_iso [CompactSpace X] [QuasiSeparatedSpace X]
    {U : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    (F : U.Modules) [F.IsFinitePresentation] :
    ∃ (G : X.Modules) (_ : G.IsFinitePresentation), Nonempty (G.restrict j ≅ F) := by
  have : F.IsQuasicoherent := SheafOfModules.instIsQuasicoherentOfIsFinitePresentation F
  let φ : F ⟶ ((pushforward j).obj F).restrict j := inv ((restrictAdjunction j).counit.app F)
  obtain ⟨G, _, -, e, -⟩ := exists_isFinitePresentation_restrictFunctor_map_eq j φ
  exact ⟨G, inferInstance, ⟨e⟩⟩

end AlgebraicGeometry.Scheme.Modules
