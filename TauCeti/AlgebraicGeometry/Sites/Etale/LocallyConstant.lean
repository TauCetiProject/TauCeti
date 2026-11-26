/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Sites.Etale.Pullback
public import TauCeti.CategoryTheory.Sites.LocallyConstant.Basic

/-!
# Locally constant sheaves on the small étale site

Using the localization equivalence `Over V ≌ V.left.Etale` and `smallEtalePullback`, this file
characterizes locally constant étale sheaves (`CategoryTheory.Sheaf.IsLocallyConstantIn`)
geometrically and establishes their stability properties:

* `CategoryTheory.Sheaf.locallyConstantSieve_smallEtaleTopology_iff` and
  `CategoryTheory.Sheaf.isLocallyConstantIn_smallEtaleTopology_iff`: geometric characterization via
  jointly surjective étale families trivializing `F`.
* `CategoryTheory.Sheaf.IsLocallyConstantIn.smallEtalePullback`: stability under base change.
* `CategoryTheory.Sheaf.isLocallyConstantIn_smallEtaleTopology_iff_of_etaleCover` (and
  specializations to surjective étale maps and open covers): étale and Zariski descent.

## References

* M. Artin, A. Grothendieck, J.-L. Verdier, *SGA 4*, Exposé IX, §2.1.
* The Stacks Project, Section 59.64, Locally constant sheaves.
-/

public section

universe u

open CategoryTheory Limits AlgebraicGeometry Scheme

namespace CategoryTheory.Sheaf

section EtaleCharacterization

variable {S : Scheme.{u}} {A : Type*} [Category* A]

/-- On the small étale site of `S`, a morphism `g : V ⟶ U` belongs to `F.locallyConstantSieve P U`
if and only if the étale inverse image of `F` along `V.hom : V.left ⟶ S` is isomorphic to a
constant sheaf with value `M` satisfying `P`. -/
lemma locallyConstantSieve_smallEtaleTopology_iff
    (F : Sheaf (smallEtaleTopology S) A) (P : ObjectProperty A) {U V : S.Etale} (g : V ⟶ U)
    [HasWeakSheafify (smallEtaleTopology S) A] [HasWeakSheafify (smallEtaleTopology V.left) A] :
    F.locallyConstantSieve P U g ↔
      ∃ M, P M ∧ Nonempty (((V.hom : V.left ⟶ S).smallEtalePullback A).obj F ≅
        (constantSheaf (smallEtaleTopology V.left) A).obj M) := by
  rw [locallyConstantSieve_apply]
  refine exists_congr fun M ↦ and_congr_right fun _ ↦ ?_
  have e₁ := V.smallEtalePullbackObjIsoOver A F
  have e₂ := (V.smallEtalePullbackObjIsoOver A ((constantSheaf _ A).obj M)).symm
    ≪≫ Hom.smallEtalePullbackConstantSheafIso (X := V.left) (Y := S) V.hom A M
  exact ⟨fun ⟨e⟩ ↦ ⟨e₁ ≪≫ (V.overSheafEquiv A).functor.mapIso e ≪≫ e₂⟩,
    fun ⟨e⟩ ↦ ⟨(V.overSheafEquiv A).fullyFaithfulFunctor.preimageIso (e₁.symm ≪≫ e ≪≫ e₂.symm)⟩⟩

/-- An étale sheaf `F` on `S` is locally constant with values in `P` as soon as it becomes
isomorphic to constant sheaves with values in `P` along a jointly surjective family of étale
morphisms `u : ∀ i, U i ⟶ S`. -/
theorem IsLocallyConstantIn.of_etaleCover_constantSheaf {P : ObjectProperty A}
    {F : Sheaf (smallEtaleTopology S) A}
    {ι : Type*} {U : ι → Scheme.{u}} (u : ∀ i, U i ⟶ S) [∀ i, Etale (u i)]
    [HasWeakSheafify (smallEtaleTopology S) A]
    [∀ i, HasWeakSheafify (smallEtaleTopology (U i)) A]
    (hu : ⋃ i, Set.range (u i) = .univ)
    (h : ∀ i, ∃ M, P M ∧ Nonempty (((u i).smallEtalePullback A).obj F ≅
      (constantSheaf (smallEtaleTopology (U i)) A).obj M)) :
    F.IsLocallyConstantIn (smallEtaleTopology S) P := by
  have hterm : IsTerminal (Etale.mk (𝟙 S)) :=
    IsTerminal.isTerminalOfObj (Etale.forget S) _ CategoryTheory.Over.mkIdTerminal
  rw [F.isLocallyConstantIn_iff_of_isTerminal P hterm]
  let g (i : ι) : Etale.mk (u i) ⟶ Etale.mk (𝟙 S) :=
    MorphismProperty.Over.homMk (u i) (Category.comp_id (u i))
  refine (smallEtaleTopology S).superset_covering ?_
    ((ofArrows_mem_smallEtaleTopology_iff g).mpr hu)
  rw [Sieve.ofArrows, Sieve.generate_le_iff]
  rintro _ _ ⟨i⟩
  have : HasWeakSheafify (smallEtaleTopology (Etale.mk (u i)).left) A :=
    inferInstanceAs (HasWeakSheafify (smallEtaleTopology (U i)) A)
  exact (F.locallyConstantSieve_smallEtaleTopology_iff P (g i)).mpr (h i)

variable [∀ X : Scheme.{u}, HasWeakSheafify (smallEtaleTopology X) A]

/-- **Geometric characterization of étale local constancy.** An étale sheaf `F` on `S` is locally
constant with values in `P` if and only if there exists a `Type u`-indexed jointly surjective
family of étale morphisms `u : ∀ i, U i ⟶ S` over each of which `(u i)^* F` is isomorphic to a
constant sheaf with value `M` satisfying `P`. -/
theorem isLocallyConstantIn_smallEtaleTopology_iff
    (F : Sheaf (smallEtaleTopology S) A) (P : ObjectProperty A) :
    F.IsLocallyConstantIn (smallEtaleTopology S) P ↔
      ∃ (ι : Type u) (U : ι → Scheme.{u}) (u : ∀ i, U i ⟶ S) (_ : ∀ i, Etale (u i)),
        (⋃ i, Set.range (u i) = .univ) ∧
          ∀ i, ∃ M, P M ∧ Nonempty (((u i).smallEtalePullback A).obj F ≅
            (constantSheaf (smallEtaleTopology (U i)) A).obj M) := by
  refine ⟨fun hF ↦ ?_, fun ⟨_, _, u, _, hu, h⟩ ↦ .of_etaleCover_constantSheaf u hu h⟩
  obtain ⟨ι', V, g, hR⟩ := (F.locallyConstantSieve P (Etale.mk (𝟙 S))).exists_eq_ofArrows
  have hcov := (ofArrows_mem_smallEtaleTopology_iff g).mp
    (hR ▸ (F.isLocallyConstantIn_iff P).mp hF (Etale.mk (𝟙 S)))
  choose idx hidx using fun s : S ↦ Set.mem_iUnion.mp (hcov ▸ Set.mem_univ s)
  have hg (j : ι') : ((g j).left : (V j).left ⟶ S) = (V j).hom :=
    (Category.comp_id _).symm.trans (CategoryTheory.Over.w ((Etale.forget S).map (g j)))
  refine ⟨S, fun s ↦ (V (idx s)).left, fun s ↦ (V (idx s)).hom, inferInstance,
    Set.eq_univ_of_forall fun s ↦ ?_, fun s ↦ (F.locallyConstantSieve_smallEtaleTopology_iff P
      (g (idx s))).mp (hR.symm ▸ Sieve.ofArrows_mk V g (idx s))⟩
  obtain ⟨z, hz⟩ := hidx s
  exact Set.mem_iUnion.mpr ⟨s, z, (congrArg (fun f : (V (idx s)).left ⟶ S ↦ f z)
    (hg (idx s)).symm).trans hz⟩

/-- **Stability of locally constant étale sheaves under base change.** For a morphism of schemes
`f : X ⟶ Y` such that `f_*` and `(pullback.fst v f)_*` (for étale `v : V ⟶ Y`) admit left adjoints,
`f.smallEtalePullback A` preserves locally constant étale sheaves with values in `P`. -/
theorem IsLocallyConstantIn.smallEtalePullback {P : ObjectProperty A}
    {X Y : Scheme.{u}} {F : Sheaf (smallEtaleTopology Y) A}
    (hF : F.IsLocallyConstantIn (smallEtaleTopology Y) P) (f : X ⟶ Y)
    [(f.smallEtalePushforward A).IsRightAdjoint]
    [∀ {V : Scheme.{u}} (v : V ⟶ Y) [Etale v],
      ((pullback.fst v f).smallEtalePushforward A).IsRightAdjoint] :
    ((f.smallEtalePullback A).obj F).IsLocallyConstantIn (smallEtaleTopology X) P := by
  obtain ⟨ι, U, u, _, hu, h⟩ := (F.isLocallyConstantIn_smallEtaleTopology_iff P).mp hF
  refine .of_etaleCover_constantSheaf (fun i ↦ pullback.snd (u i) f) ?_ fun i ↦ ?_
  · simp_rw [Scheme.Pullback.range_snd, ← Set.preimage_iUnion, hu, Set.preimage_univ]
  · obtain ⟨M, hM, ⟨e⟩⟩ := h i
    have := Hom.isRightAdjoint_smallEtalePushforward_comp (pullback.snd (u i) f) f A
    have := Hom.isRightAdjoint_smallEtalePushforward_comp (pullback.fst (u i) f) (u i) A
    exact ⟨M, hM,
      ⟨((Hom.smallEtalePullbackComp (pullback.snd (u i) f) f A).app F).symm ≪≫
        (Hom.smallEtalePullbackCongr pullback.condition.symm A).app F ≪≫
        (Hom.smallEtalePullbackComp (pullback.fst (u i) f) (u i) A).app F ≪≫
        ((pullback.fst (u i) f).smallEtalePullback A).mapIso e ≪≫
        (pullback.fst (u i) f).smallEtalePullbackConstantSheafIso A M⟩⟩

section Descent

variable (F : Sheaf (smallEtaleTopology S) A) (P : ObjectProperty A)

/-- **Étale descent for locally constant sheaves.** An étale sheaf `F` on `S` is locally constant
with values in `P` if and only if its inverse images along a jointly surjective family of étale
morphisms `u : ∀ i, U i ⟶ S` are locally constant with values in `P`. -/
theorem isLocallyConstantIn_smallEtaleTopology_iff_of_etaleCover {ι : Type*} {U : ι → Scheme.{u}}
    (u : ∀ i, U i ⟶ S) [∀ i, Etale (u i)] (hu : ⋃ i, Set.range (u i) = .univ) :
    F.IsLocallyConstantIn (smallEtaleTopology S) P ↔
      ∀ i, (((u i).smallEtalePullback A).obj F).IsLocallyConstantIn
        (smallEtaleTopology (U i)) P := by
  refine ⟨fun hF i ↦ hF.smallEtalePullback (u i), fun h ↦ ?_⟩
  choose κ W w hw hcov htriv using fun i ↦
    (((u i).smallEtalePullback A).obj F).isLocallyConstantIn_smallEtaleTopology_iff P |>.mp (h i)
  refine .of_etaleCover_constantSheaf (fun p : Σ i, κ i ↦ w p.1 p.2 ≫ u p.1)
    (Set.eq_univ_of_forall fun s ↦ ?_) fun p ↦ ?_
  · obtain ⟨i, x, rfl⟩ := Set.mem_iUnion.mp (hu ▸ Set.mem_univ s)
    obtain ⟨k, z, rfl⟩ := Set.mem_iUnion.mp (hcov i ▸ Set.mem_univ x)
    exact Set.mem_iUnion.mpr ⟨⟨i, k⟩, z, Scheme.Hom.comp_apply (w i k) (u i) z⟩
  · obtain ⟨M, hM, ⟨e⟩⟩ := htriv p.1 p.2
    exact ⟨M, hM, ⟨(Hom.smallEtalePullbackComp (w p.1 p.2) (u p.1) A).app F ≪≫ e⟩⟩

/-- An étale sheaf `F` on `S` is locally constant with values in `P` if and only if its pullback
along a surjective étale morphism `u : U ⟶ S` is locally constant. -/
theorem isLocallyConstantIn_smallEtaleTopology_iff_of_etale_of_surjective
    {U : Scheme.{u}} (u : U ⟶ S) [Etale u] [Surjective u] :
    F.IsLocallyConstantIn (smallEtaleTopology S) P ↔
      ((u.smallEtalePullback A).obj F).IsLocallyConstantIn (smallEtaleTopology U) P :=
  (F.isLocallyConstantIn_smallEtaleTopology_iff_of_etaleCover P (fun _ : PUnit.{1} ↦ u)
    ((Set.iUnion_const _).trans u.surjective.range_eq)).trans ⟨fun h ↦ h ⟨⟩, fun h _ ↦ h⟩

/-- An étale sheaf `F` on `S` is locally constant with values in `P` if and only if its
restrictions to the pieces of an open cover `𝒰 : S.OpenCover` are locally constant. -/
theorem isLocallyConstantIn_smallEtaleTopology_iff_of_openCover (𝒰 : S.OpenCover) :
    F.IsLocallyConstantIn (smallEtaleTopology S) P ↔
      ∀ i, (((𝒰.f i).smallEtalePullback A).obj F).IsLocallyConstantIn
        (smallEtaleTopology (𝒰.X i)) P :=
  F.isLocallyConstantIn_smallEtaleTopology_iff_of_etaleCover P 𝒰.f 𝒰.iUnion_range

end Descent

end EtaleCharacterization

end CategoryTheory.Sheaf
