/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.Extension.Basic
public import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.FiniteType

/-!
# Extension of finite-type quasi-coherent modules

On a quasi-compact quasi-separated scheme, a quasi-coherent module that is of finite type on a
quasi-compact open contains a finite-type quasi-coherent submodule agreeing with it there.
Consequently, finite-type quasi-coherent modules and submodules extend from quasi-compact opens.
The submodule extension includes the isomorphism identifying the restricted inclusion with the
original inclusion.
These extensions provide the finite-type input to extension of coherent modules.

The construction uses affine finite-type approximation on compact overlaps and the kernel
construction of `Scheme.Modules.exists_mono_restrict_iso_of_isQuasicoherent`. Shrinking the module
one affine open at a time preserves its restriction on the region already treated; a finite
affine cover then gives finite type everywhere.

## References

* The Stacks Project, Lemmas 28.23.2 (Tag 01PF) and 28.23.5, part (1) (Tag 0G41).
-/

public section

open CategoryTheory TopologicalSpace
open TauCeti.AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

-- This is the affine enlargement step in the finite-cover construction below.
private theorem exists_mono_finiteType_restrict_sup [QuasiSeparatedSpace X]
    {N : X.Modules} [N.IsQuasicoherent] (V : X.Opens) (hV : IsCompact (V : Set X))
    [(N.restrict V.ι).IsFiniteType] (U : X.affineOpens) :
    ∃ (N' : X.Modules) (_ : N'.IsQuasicoherent) (i : N' ⟶ N) (_ : Mono i),
      IsIso ((restrictFunctor V.ι).map i) ∧ (N'.restrict (V ⊔ U.1).ι).IsFiniteType := by
  have : IsAffine U.1.toScheme := U.2
  have : QuasiCompact U.1.ι := inferInstance
  let W := U.1.ι ⁻¹ᵁ V
  let f := U.1.ι.resLE V W le_rfl
  have : IsOpenImmersion f := by dsimp [f, Scheme.Hom.resLE]; infer_instance
  have : ((N.restrict U.1.ι).restrict W.ι).IsFiniteType :=
    SheafOfModules.IsFiniteType.of_iso (R := W.toScheme.ringCatSheaf)
      (M := (N.restrict V.ι).restrict f)
      (((restrictFunctorComp f V.ι).app N).symm ≪≫
        (restrictFunctorCongr (U.1.ι.resLE_comp_ι le_rfl)).app N ≪≫
        (restrictFunctorComp W.ι U.1.ι).app N)
  obtain ⟨F, _, _, a, _, ha⟩ :=
    exists_isFiniteType_mono_isIso_restrict (N := N.restrict U.1.ι) W
      (U.1.ι.isCompact_preimage hV)
  obtain ⟨N', _, i, _, e, -, hkeep⟩ :=
    exists_mono_restrict_iso_of_isQuasicoherent U.1.ι a
  have hi : IsIso ((restrictFunctor V.ι).map i) := hkeep V ha
  have : (N'.restrict V.ι).IsFiniteType :=
    SheafOfModules.IsFiniteType.of_iso (R := V.toScheme.ringCatSheaf)
      (asIso ((restrictFunctor V.ι).map i)).symm
  have : (N'.restrict U.1.ι).IsFiniteType :=
    SheafOfModules.IsFiniteType.of_iso (R := U.1.toScheme.ringCatSheaf) e.symm
  refine ⟨N', inferInstance, i, inferInstance, hi, ?_⟩
  rw [sup_eq_iSup V U.1]
  exact isFiniteType_restrict_iSup N' (fun b : Bool ↦ cond b V U.1)
    (by intro b; cases b <;> assumption)

/-- On a quasi-compact quasi-separated scheme, a quasi-coherent module that is of finite type on
a quasi-compact open contains a finite-type quasi-coherent submodule agreeing with it there.
No finiteness condition is imposed on the ambient module away from that open. -/
theorem exists_isFiniteType_mono_isIso_restrict_of_quasiSeparatedSpace
    [CompactSpace X] [QuasiSeparatedSpace X] {N : X.Modules} [N.IsQuasicoherent]
    (V : X.Opens) (hV : IsCompact (V : Set X)) [(N.restrict V.ι).IsFiniteType] :
    ∃ (N' : X.Modules) (_ : N'.IsQuasicoherent) (_ : N'.IsFiniteType) (i : N' ⟶ N) (_ : Mono i),
      IsIso ((restrictFunctor V.ι).map i) := by
  classical
  -- The invariant retains finite type on `V` and the affine opens already visited.
  have aux (s : Finset X.affineOpens) :
      ∃ (N' : X.Modules) (_ : N'.IsQuasicoherent) (i : N' ⟶ N) (_ : Mono i),
        IsIso ((restrictFunctor V.ι).map i) ∧
          (N'.restrict (V ⊔ ⨆ U ∈ s, U.1).ι).IsFiniteType := by
    induction s using Finset.induction_on with
    | empty =>
      refine ⟨N, inferInstance, 𝟙 N, inferInstance, ?_, ?_⟩
      · rw [CategoryTheory.Functor.map_id]
        infer_instance
      · have h : V ⊔ ⨆ U ∈ (∅ : Finset X.affineOpens), U.1 = V := by simp
        rw [h]
        infer_instance
    | insert U s _ ih =>
      obtain ⟨M, _, i, _, hi, hM⟩ := ih
      let W := V ⊔ ⨆ U ∈ s, U.1
      have hW : IsCompact (W : Set X) :=
        hV.union (by simpa using s.finite_toSet.isCompact_biUnion (fun U _ ↦ U.2.isCompact))
      have : (M.restrict W.ι).IsFiniteType := hM
      obtain ⟨M', _, j, _, hj, hM'⟩ := exists_mono_finiteType_restrict_sup (N := M) W hW U
      -- Restrict the isomorphism on `W` further to `V` using the canonical composition comparison.
      let k : V.toScheme ⟶ W.toScheme := X.homOfLE le_sup_left
      have : IsIso ((restrictFunctor k).map ((restrictFunctor W.ι).map j)) :=
        Functor.map_isIso _ _
      have hjV : IsIso ((restrictFunctor V.ι).map j) := by
        have h : IsIso ((restrictFunctor W.ι ⋙ restrictFunctor k).map j) := by
          rw [CategoryTheory.Functor.comp_map]
          infer_instance
        have := (NatIso.isIso_map_iff (restrictFunctorComp k W.ι) j).mpr h
        exact (NatIso.isIso_map_iff (restrictFunctorCongr (X.homOfLE_ι le_sup_left)) j).mp this
      refine ⟨M', inferInstance, j ≫ i, inferInstance, ?_, ?_⟩
      · rw [CategoryTheory.Functor.map_comp]
        infer_instance
      · rw [Finset.iSup_insert, ← sup_assoc, sup_right_comm]
        exact hM'
  have hX : IsCompact ((⊤ : X.Opens) : Set X) := isCompact_univ
  obtain ⟨s, hs, hcover⟩ := isCompact_iff_finite_and_eq_biUnion_affineOpens.mp hX
  obtain ⟨N', _, i, _, hi, hN'⟩ := aux hs.toFinset
  have htop : V ⊔ ⨆ U ∈ hs.toFinset, U.1 = ⊤ := by simpa using congrArg (V ⊔ ·) hcover.symm
  rw [htop] at hN'
  have : ((N'.restrict (⊤ : X.Opens).ι).restrict X.topIso.inv).IsFiniteType := inferInstance
  have : N'.IsFiniteType :=
    SheafOfModules.IsFiniteType.of_iso (R := X.ringCatSheaf)
      (M := (N'.restrict (⊤ : X.Opens).ι).restrict X.topIso.inv)
      (((restrictFunctorComp X.topIso.inv (⊤ : X.Opens).ι).app N').symm ≪≫
        (restrictFunctorCongr (X.toIso_inv_ι)).app N' ≪≫ restrictFunctorId.app N')
  exact ⟨N', inferInstance, inferInstance, i, inferInstance, hi⟩

/-- A finite-type quasi-coherent submodule of the restriction of a quasi-coherent module along
a quasi-compact open immersion into a quasi-compact quasi-separated scheme extends to a
finite-type quasi-coherent submodule, with the given inclusion recovered on restriction. -/
theorem exists_isFiniteType_mono_restrict_iso [CompactSpace X] [QuasiSeparatedSpace X]
    {U : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    {G : X.Modules} [G.IsQuasicoherent] {F : U.Modules} [F.IsQuasicoherent] [F.IsFiniteType]
    (i : F ⟶ G.restrict j) [Mono i] :
    ∃ (G' : X.Modules) (_ : G'.IsQuasicoherent) (_ : G'.IsFiniteType)
      (i' : G' ⟶ G) (_ : Mono i') (e : G'.restrict j ≅ F),
        (restrictFunctor j).map i' = e.hom ≫ i := by
  obtain ⟨M, _, a, _, e, he, -⟩ := exists_mono_restrict_iso_of_isQuasicoherent j i
  have : (M.restrict j).IsFiniteType :=
    SheafOfModules.IsFiniteType.of_iso (R := U.ringCatSheaf) e.symm
  have : ((M.restrict j).restrict j.isoOpensRange.inv).IsFiniteType := inferInstance
  have : (M.restrict j.opensRange.ι).IsFiniteType :=
    SheafOfModules.IsFiniteType.of_iso (R := j.opensRange.toScheme.ringCatSheaf)
      (M := (M.restrict j).restrict j.isoOpensRange.inv)
      (((restrictFunctorComp j.isoOpensRange.inv j).app M).symm ≪≫
        (restrictFunctorCongr j.isoOpensRange_inv_comp).app M)
  have : CompactSpace U := QuasiCompact.compactSpace_of_compactSpace j
  have hV : IsCompact (j.opensRange : Set X) := isCompact_range j.continuous
  obtain ⟨G', _, _, b, _, hb⟩ :=
    exists_isFiniteType_mono_isIso_restrict_of_quasiSeparatedSpace (N := M) j.opensRange hV
  have : IsIso ((restrictFunctor j.isoOpensRange.hom).map
      ((restrictFunctor j.opensRange.ι).map b)) := Functor.map_isIso _ _
  have hb' : IsIso ((restrictFunctor j).map b) := by
    have hcomp : IsIso ((restrictFunctor j.opensRange.ι ⋙
        restrictFunctor j.isoOpensRange.hom).map b) := by
      rw [CategoryTheory.Functor.comp_map]
      infer_instance
    have h := (NatIso.isIso_map_iff
      (restrictFunctorComp j.isoOpensRange.hom j.opensRange.ι) b).mpr
      hcomp
    exact (NatIso.isIso_map_iff (restrictFunctorCongr j.isoOpensRange_hom_ι) b).mp h
  refine ⟨G', inferInstance, inferInstance, b ≫ a, inferInstance,
    asIso ((restrictFunctor j).map b) ≪≫ e, ?_⟩
  simp [CategoryTheory.Functor.map_comp, he, Category.assoc]

/-- A finite-type quasi-coherent module on a quasi-compact open subscheme of a quasi-compact
quasi-separated scheme extends to a finite-type quasi-coherent module on the whole scheme. -/
theorem exists_isFiniteType_restrict_iso [CompactSpace X] [QuasiSeparatedSpace X]
    {U : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    (F : U.Modules) [F.IsQuasicoherent] [F.IsFiniteType] :
    ∃ (G : X.Modules) (_ : G.IsQuasicoherent) (_ : G.IsFiniteType),
      Nonempty (G.restrict j ≅ F) := by
  obtain ⟨M, _, ⟨e⟩⟩ := exists_isQuasicoherent_restrict_iso j F
  obtain ⟨G, _, _, i, _, e', -⟩ := exists_isFiniteType_mono_restrict_iso j e.inv
  exact ⟨G, inferInstance, inferInstance, ⟨e'⟩⟩

end AlgebraicGeometry.Scheme.Modules
