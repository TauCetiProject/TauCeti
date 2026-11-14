/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Sites.Etale.Pullback
public import TauCeti.CategoryTheory.Sites.LocallyConstant

/-!
# Locally constant sheaves on the small étale site

Let `S` be a scheme, `A` a category in which weak sheafification exists on small étale sites, and
`P` a property of objects of `A`. In `TauCeti.CategoryTheory.Sites.LocallyConstant`, a sheaf
`F : Sheaf (smallEtaleTopology S) A` is locally constant with values in `P`
(`CategoryTheory.Sheaf.IsLocallyConstantIn`) if every `U : S.Etale` is covered in
`smallEtaleTopology S` by morphisms `V ⟶ U` over which `F.over V` is isomorphic to the restriction
to `Over V` of a constant sheaf with value `M` satisfying `P`.

Using the localization equivalence `Over V ≌ V.left.Etale`
(`TauCeti.AlgebraicGeometry.Sites.Etale.Over`) and the inverse image functor `smallEtalePullback`
(`TauCeti.AlgebraicGeometry.Sites.Etale.Pullback`), this file translates site-theoretic local
constancy into geometric terms and proves its stability properties:

* `CategoryTheory.Sheaf.locallyConstantSieve_smallEtaleTopology_iff`: a morphism `g : V ⟶ U` in
  `S.Etale` belongs to `F.locallyConstantSieve P U` if and only if `(V.hom)^* F` is isomorphic on
  `V.left` to `(constantSheaf (smallEtaleTopology V.left) A).obj M` for some `M` satisfying `P`.
* `CategoryTheory.Sheaf.isLocallyConstantIn_smallEtaleTopology_iff`: `F` is locally constant with
  values in `P` if and only if there exists a jointly surjective `Type u`-indexed family of étale
  morphisms `u : ∀ i, U i ⟶ S` over each of which `(u i)^* F` is isomorphic to a constant sheaf
  with value in `P`.
* `CategoryTheory.Sheaf.IsLocallyConstantIn.smallEtalePullback`: local constancy with values in `P`
  is preserved under `f.smallEtalePullback A` along any morphism of schemes `f : X ⟶ Y`.
* `CategoryTheory.Sheaf.isLocallyConstantIn_smallEtaleTopology_iff_of_etaleCover`: local constancy
  with values in `P` satisfies étale descent — `F` is locally constant on `S` if and only if
  `(u i)^* F` is locally constant on `U i` for a jointly surjective étale family `u : ∀ i, U i ⟶ S`
  (with specializations to a single surjective étale morphism and an open cover `S.OpenCover`).

## References

* M. Artin, A. Grothendieck, J.-L. Verdier, *SGA 4*, Exposé IX, §2.1, locally constant étale
  sheaves and stability under inverse image and étale descent.
* The Stacks Project, Section 59.64, Locally constant sheaves.
-/

public section

universe u

open CategoryTheory Limits AlgebraicGeometry Scheme

namespace CategoryTheory.Sheaf

section EtaleCharacterization

variable {S : Scheme.{u}} {A : Type*} [Category* A]
  [∀ X : Scheme.{u}, HasWeakSheafify (smallEtaleTopology X) A]

/-- On the small étale site of `S`, a morphism `g : V ⟶ U` belongs to `F.locallyConstantSieve P U`
if and only if the étale inverse image of `F` along `V.hom : V.left ⟶ S` is isomorphic to a
constant sheaf with value `M` satisfying `P`. -/
lemma locallyConstantSieve_smallEtaleTopology_iff
    (F : Sheaf (smallEtaleTopology S) A) (P : ObjectProperty A) {U V : S.Etale} (g : V ⟶ U) :
    F.locallyConstantSieve P U g ↔
      ∃ M, P M ∧ Nonempty (((V.hom : V.left ⟶ S).smallEtalePullback A).obj F ≅
        (constantSheaf (smallEtaleTopology V.left) A).obj M) := by
  rw [locallyConstantSieve_apply]
  refine exists_congr fun M ↦ and_congr_right fun _ ↦ ?_
  have e₁ := V.smallEtalePullbackObjIsoOver A F
  have e₂ :=
    (V.smallEtalePullbackObjIsoOver A ((constantSheaf (smallEtaleTopology S) A).obj M)).symm ≪≫
      (V.hom : V.left ⟶ S).smallEtalePullbackConstantSheafIso A M
  exact ⟨fun ⟨e⟩ ↦ ⟨e₁ ≪≫ (V.overSheafEquiv A).functor.mapIso e ≪≫ e₂⟩,
    fun ⟨e⟩ ↦ ⟨(V.overSheafEquiv A).fullyFaithfulFunctor.preimageIso (e₁.symm ≪≫ e ≪≫ e₂.symm)⟩⟩

/-- An étale sheaf `F` on `S` is locally constant with values in `P` as soon as it becomes
isomorphic to constant sheaves with values in `P` along a jointly surjective family of étale
morphisms `u : ∀ i, U i ⟶ S`. -/
theorem IsLocallyConstantIn.of_etaleCover {P : ObjectProperty A}
    {F : Sheaf (smallEtaleTopology S) A}
    {ι : Type*} {U : ι → Scheme.{u}} (u : ∀ i, U i ⟶ S) [∀ i, Etale (u i)]
    (hu : ⋃ i, Set.range (u i) = .univ)
    (h : ∀ i, ∃ M, P M ∧ Nonempty (((u i).smallEtalePullback A).obj F ≅
      (constantSheaf (smallEtaleTopology (U i)) A).obj M)) :
    F.IsLocallyConstantIn (smallEtaleTopology S) P := by
  rw [F.isLocallyConstantIn_iff_of_isTerminal P (Etale.mkIdTerminal S)]
  let g (i : ι) : Etale.mk (u i) ⟶ Etale.mk (𝟙 S) :=
    MorphismProperty.Over.homMk (u i) (Category.comp_id (u i))
  have hg : Sieve.ofArrows _ g ∈ smallEtaleTopology S (Etale.mk (𝟙 S)) :=
    (ofArrows_mem_smallEtaleTopology_iff g).mpr hu
  refine (smallEtaleTopology S).superset_covering ?_ hg
  rw [Sieve.ofArrows, Sieve.generate_le_iff]
  rintro _ _ ⟨i⟩
  exact (F.locallyConstantSieve_smallEtaleTopology_iff P (g i)).mpr (h i)

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
  refine ⟨fun hF ↦ ?_, fun ⟨_, _, u, _, hu, h⟩ ↦ .of_etaleCover u hu h⟩
  have hT := (F.isLocallyConstantIn_iff P).mp hF (Etale.mk (𝟙 S))
  obtain ⟨ι', V, g, hR⟩ := (F.locallyConstantSieve P (Etale.mk (𝟙 S))).exists_eq_ofArrows
  have hcov : ⋃ j, Set.range (g j).left = .univ :=
    (ofArrows_mem_smallEtaleTopology_iff g).mp (hR ▸ hT)
  have hex (s : S) : ∃ j : ι', s ∈ Set.range (g j).left :=
    Set.mem_iUnion.mp (hcov ▸ Set.mem_univ s)
  choose idx hidx using hex
  have hg (j : ι') : ((g j).left : (V j).left ⟶ S) = (V j).hom :=
    (Category.comp_id _).symm.trans (CategoryTheory.Over.w ((Etale.forget S).map (g j)))
  refine ⟨S, fun s ↦ (V (idx s)).left, fun s ↦ (V (idx s)).hom, inferInstance, ?_, fun s ↦ ?_⟩
  · refine Set.eq_univ_of_forall fun s ↦ ?_
    obtain ⟨z, hz⟩ := hidx s
    exact Set.mem_iUnion.mpr ⟨s, z, (congrArg (fun f : (V (idx s)).left ⟶ S ↦ f z)
      (hg (idx s)).symm).trans hz⟩
  · have hmem : F.locallyConstantSieve P (Etale.mk (𝟙 S)) (g (idx s)) :=
      hR.symm ▸ Sieve.ofArrows_mk V g (idx s)
    exact (F.locallyConstantSieve_smallEtaleTopology_iff P (g (idx s))).mp hmem

/-- Pulling back a locally constant étale sheaf along an étale morphism preserves local constancy
(without requiring sheaf inverse images along arbitrary non-étale morphisms). -/
theorem IsLocallyConstantIn.smallEtalePullback_of_etale {P : ObjectProperty A}
    {X Y : Scheme.{u}} {F : Sheaf (smallEtaleTopology Y) A}
    (hF : F.IsLocallyConstantIn (smallEtaleTopology Y) P) (j : X ⟶ Y) [Etale j] :
    ((j.smallEtalePullback A).obj F).IsLocallyConstantIn (smallEtaleTopology X) P := by
  obtain ⟨ι, U, u, _, hu, h⟩ := (F.isLocallyConstantIn_smallEtaleTopology_iff P).mp hF
  refine .of_etaleCover (fun i ↦ pullback.snd (u i) j) ?_ fun i ↦ ?_
  · simp_rw [Scheme.Pullback.range_snd, ← Set.preimage_iUnion, hu, Set.preimage_univ]
  · obtain ⟨M, hM, ⟨e⟩⟩ := h i
    exact ⟨M, hM,
      ⟨((Hom.smallEtalePullbackComp (pullback.snd (u i) j) j A).app F).symm ≪≫
        (Hom.smallEtalePullbackCongr pullback.condition.symm A).app F ≪≫
        (Hom.smallEtalePullbackComp (pullback.fst (u i) j) (u i) A).app F ≪≫
        ((pullback.fst (u i) j).smallEtalePullback A).mapIso e ≪≫
        (pullback.fst (u i) j).smallEtalePullbackConstantSheafIso A M⟩⟩

/-- **Étale descent for locally constant sheaves.** An étale sheaf `F` on `S` is locally constant
with values in `P` if and only if its inverse images along a jointly surjective family of étale
morphisms `u : ∀ i, U i ⟶ S` are locally constant with values in `P`. -/
theorem isLocallyConstantIn_smallEtaleTopology_iff_of_etaleCover
    (F : Sheaf (smallEtaleTopology S) A) (P : ObjectProperty A) {ι : Type*} {U : ι → Scheme.{u}}
    (u : ∀ i, U i ⟶ S) [∀ i, Etale (u i)] (hu : ⋃ i, Set.range (u i) = .univ) :
    F.IsLocallyConstantIn (smallEtaleTopology S) P ↔
      ∀ i, (((u i).smallEtalePullback A).obj F).IsLocallyConstantIn
        (smallEtaleTopology (U i)) P := by
  refine ⟨fun hF i ↦ hF.smallEtalePullback_of_etale (u i), fun h ↦ ?_⟩
  choose κ W w hw hcov htriv using fun i ↦
    (((u i).smallEtalePullback A).obj F).isLocallyConstantIn_smallEtaleTopology_iff P |>.mp (h i)
  refine .of_etaleCover (fun p : Σ i, κ i ↦ w p.1 p.2 ≫ u p.1) ?_ fun p ↦ ?_
  · refine Set.eq_univ_of_forall fun s ↦ ?_
    obtain ⟨i, x, rfl⟩ := Set.mem_iUnion.mp (hu ▸ Set.mem_univ s)
    obtain ⟨k, z, rfl⟩ := Set.mem_iUnion.mp (hcov i ▸ Set.mem_univ x)
    exact Set.mem_iUnion.mpr ⟨⟨i, k⟩, z, Scheme.Hom.comp_apply (w i k) (u i) z⟩
  · obtain ⟨M, hM, ⟨e⟩⟩ := htriv p.1 p.2
    exact ⟨M, hM, ⟨(Hom.smallEtalePullbackComp (w p.1 p.2) (u p.1) A).app F ≪≫ e⟩⟩

/-- An étale sheaf `F` on `S` is locally constant with values in `P` if and only if its pullback
along a surjective étale morphism `u : U ⟶ S` is locally constant. -/
theorem isLocallyConstantIn_smallEtaleTopology_iff_of_surjective
    (F : Sheaf (smallEtaleTopology S) A) (P : ObjectProperty A)
    {U : Scheme.{u}} (u : U ⟶ S) [Etale u] [Surjective u] :
    F.IsLocallyConstantIn (smallEtaleTopology S) P ↔
      ((u.smallEtalePullback A).obj F).IsLocallyConstantIn (smallEtaleTopology U) P :=
  have hu : (⋃ _ : PUnit.{1}, Set.range u) = .univ :=
    (Set.iUnion_const _).trans u.surjective.range_eq
  (F.isLocallyConstantIn_smallEtaleTopology_iff_of_etaleCover P (fun _ : PUnit.{1} ↦ u) hu).trans
    ⟨fun h ↦ h ⟨⟩, fun h _ ↦ h⟩

/-- An étale sheaf `F` on `S` is locally constant with values in `P` if and only if its
restrictions to the pieces of an open cover `𝒰 : S.OpenCover` are locally constant. -/
theorem isLocallyConstantIn_smallEtaleTopology_iff_of_openCover
    (F : Sheaf (smallEtaleTopology S) A) (P : ObjectProperty A) (𝒰 : S.OpenCover) :
    F.IsLocallyConstantIn (smallEtaleTopology S) P ↔
      ∀ i, (((𝒰.f i).smallEtalePullback A).obj F).IsLocallyConstantIn
        (smallEtaleTopology (𝒰.X i)) P :=
  F.isLocallyConstantIn_smallEtaleTopology_iff_of_etaleCover P 𝒰.f 𝒰.iUnion_range

end EtaleCharacterization

section BaseChange

variable {A : Type*} [Category* A]
  [∀ X : Scheme.{u}, HasWeakSheafify (smallEtaleTopology X) A]
  [∀ {W Z : Scheme.{u}} (g : W ⟶ Z), (g.smallEtalePushforward A).IsRightAdjoint]
  {P : ObjectProperty A}

/-- **Stability of locally constant étale sheaves under base change.** For any morphism of schemes
`f : X ⟶ Y`, `f.smallEtalePullback A` sends locally constant étale sheaves with values in `P` on `Y`
to locally constant étale sheaves with values in `P` on `X`. -/
theorem IsLocallyConstantIn.smallEtalePullback {X Y : Scheme.{u}}
    {F : Sheaf (smallEtaleTopology Y) A} (hF : F.IsLocallyConstantIn (smallEtaleTopology Y) P)
    (f : X ⟶ Y) :
    ((f.smallEtalePullback A).obj F).IsLocallyConstantIn (smallEtaleTopology X) P := by
  obtain ⟨ι, U, u, _, hu, h⟩ := (F.isLocallyConstantIn_smallEtaleTopology_iff P).mp hF
  refine .of_etaleCover (fun i ↦ pullback.snd (u i) f) ?_ fun i ↦ ?_
  · simp_rw [Scheme.Pullback.range_snd, ← Set.preimage_iUnion, hu, Set.preimage_univ]
  · obtain ⟨M, hM, ⟨e⟩⟩ := h i
    exact ⟨M, hM,
      ⟨((Hom.smallEtalePullbackComp (pullback.snd (u i) f) f A).app F).symm ≪≫
        (Hom.smallEtalePullbackCongr pullback.condition.symm A).app F ≪≫
        (Hom.smallEtalePullbackComp (pullback.fst (u i) f) (u i) A).app F ≪≫
        ((pullback.fst (u i) f).smallEtalePullback A).mapIso e ≪≫
        (pullback.fst (u i) f).smallEtalePullbackConstantSheafIso A M⟩⟩

end BaseChange

end CategoryTheory.Sheaf
