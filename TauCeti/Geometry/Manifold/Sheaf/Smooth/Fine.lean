/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.Grp.EquivalenceGroupAddGroup
public import Mathlib.Geometry.Manifold.PartitionOfUnity
public import Mathlib.Geometry.Manifold.Sheaf.Smooth
public import TauCeti.Geometry.Manifold.Algebra.TypeTags
public import TauCeti.Geometry.Manifold.Sheaf.Smooth.Restrict
public import TauCeti.Topology.Sheaves.Fine

/-!
# Fineness and sheaf-cohomological acyclicity of smooth vector-valued functions

Let `M` be a real `C^∞` manifold modelled on a finite-dimensional space `E` with corners `I`, and
let `V` be a real normed vector space in the same universe as `M`. On a Hausdorff `σ`-compact
manifold `M` (in particular, on any Hausdorff second-countable manifold), every open cover admits a
subordinate smooth partition of unity (`SmoothPartitionOfUnity.exists_isSubordinate`). Pointwise
scalar multiplication of smooth `V`-valued sections by the functions of that partition makes
`smoothSheafAddCommGroup I 𝓘(ℝ, V) M V` a fine sheaf of abelian groups (`TopCat.Sheaf.IsFine`), so
its derived-functor sheaf cohomology `Sheaf.H` vanishes in every positive degree
(`TauCeti.subsingleton_H_smoothSheafAddCommGroup`).

When `M` is Hausdorff and second-countable, every open subset `U` of `M` is again a Hausdorff
second-countable manifold, and restricting `smoothSheafAddCommGroup` to `U` identifies with the
sheaf of smooth `V`-valued functions on `U` (`TauCeti.smoothSheafAddCommGroup.restrictIso` in
`TauCeti.Geometry.Manifold.Sheaf.Smooth.Restrict`). Hence the local sheaf cohomology `Sheaf.H'` of
`smoothSheafAddCommGroup I 𝓘(ℝ, V) M V` also vanishes in positive degrees over every open subset `U`
(`TauCeti.subsingleton_H'_smoothSheafAddCommGroup`).

We also record the comparison isomorphism
`TauCeti.smoothSheafCommGroup.sheafComposeToAddCommGrpIso` relating `smoothSheafCommGroup IM I M A`
pushed forward along `CommGrpCat.toAddCommGrp` with `smoothSheafAddCommGroup IM I M (Additive A)`.
For coverwise Čech acyclicity of the module sheaf `TauCeti.smoothSheafModule`, see
`TauCeti.Geometry.Manifold.Sheaf.Smooth.Cech`.

## Main definitions and results

* `TauCeti.smoothSheafCommGroup.sheafComposeToAddCommGrpIso`: comparison between pushing
  `smoothSheafCommGroup IM I M A` along `CommGrpCat.toAddCommGrp` and
  `smoothSheafAddCommGroup IM I M (Additive A)`.
* `TauCeti.smoothSheafAddCommGroup.smulEnd`: multiplication of smooth `V`-valued sections by a
  global smooth scalar function `g : C^∞⟮IM, M; 𝓘(𝕜), 𝕜⟯`.
* `TauCeti.isFine_smoothSheafAddCommGroup`,
  `TauCeti.isFine_smoothSheafAddCommGroup_of_secondCountableTopology`: fineness of
  `smoothSheafAddCommGroup I 𝓘(ℝ, V) M V`.
* `TauCeti.subsingleton_H_smoothSheafAddCommGroup_of_sigmaCompactSpace`,
  `TauCeti.subsingleton_H_smoothSheafAddCommGroup`,
  `TauCeti.subsingleton_H'_smoothSheafAddCommGroup`: vanishing of global and open-subset sheaf
  cohomology in positive degrees.

## References

* R. Godement, *Topologie algébrique et théorie des faisceaux*, Hermann, 1958, Chapitre II, §3.7,
  Exemple 3.7.1, and §4.4, Théorème 4.4.3.
* L. I. Nicolaescu, *Lectures on the Geometry of Manifolds*, 3rd ed., World Scientific, 2021,
  §7.5.4, Example 7.5.31 and Proposition 7.5.32, p. 327.
* The smooth sheaves are those of `Mathlib/Geometry/Manifold/Sheaf/Smooth.lean`, by Heather Macbeth
  and Adam Topaz.
-/

public noncomputable section

open CategoryTheory Opposite TopologicalSpace
open scoped ContDiff Manifold

universe u

namespace TauCeti

section Additive

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {EM : Type*} [NormedAddCommGroup EM] [NormedSpace 𝕜 EM]
  {HM : Type*} [TopologicalSpace HM] (IM : ModelWithCorners 𝕜 EM HM)
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H)
  {M : Type u} [TopologicalSpace M] [ChartedSpace HM M]
  (A : Type u) [TopologicalSpace A] [ChartedSpace H A]

/-- `CommGrpCat.toAddCommGrp` is an equivalence of categories and therefore preserves sheaves on any
Grothendieck site. -/
instance hasSheafCompose_commGrpToAddCommGrp {C : Type*} [Category* C]
    (J : GrothendieckTopology C) : J.HasSheafCompose CommGrpCat.toAddCommGrp.{u} := by
  have : Limits.PreservesLimitsOfSize CommGrpCat.toAddCommGrp.{u} :=
    commGroupAddCommGroupEquivalence.symm.toAdjunction.rightAdjoint_preservesLimits
  infer_instance

private def sectionsAdditiveAddEquiv [CommGroup A] [LieGroup I ∞ A]
    (W : Opens (TopCat.of M)) :
    Additive C^∞⟮IM, W; I, A⟯ ≃+ C^∞⟮IM, W; I, Additive A⟯ where
  toFun f := ⟨fun x ↦ Additive.ofMul ((Additive.toMul f : C^∞⟮IM, W; I, A⟯) x),
    Additive.contMDiff_ofMul.comp (Additive.toMul f : C^∞⟮IM, W; I, A⟯).contMDiff⟩
  invFun g := Additive.ofMul ⟨fun x ↦ Additive.toMul (g x),
    Additive.contMDiff_toMul.comp g.contMDiff⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

variable (M) in
/-- Pushing `smoothSheafCommGroup IM I M A` along `CommGrpCat.toAddCommGrp` identifies canonically
with `smoothSheafAddCommGroup IM I M (Additive A)`. -/
def smoothSheafCommGroup.sheafComposeToAddCommGrpIso [CommGroup A] [LieGroup I ∞ A] :
    (sheafCompose (Opens.grothendieckTopology (TopCat.of M)) CommGrpCat.toAddCommGrp).obj
      (smoothSheafCommGroup IM I M A) ≅
    smoothSheafAddCommGroup IM I M (Additive A) :=
  ObjectProperty.isoMk _ <| NatIso.ofComponents
    (fun W ↦ AddEquiv.toAddCommGrpIso
      (X := ((sheafCompose (Opens.grothendieckTopology (TopCat.of M))
        CommGrpCat.toAddCommGrp).obj (smoothSheafCommGroup IM I M A)).obj.obj W)
      (Y := (smoothSheafAddCommGroup IM I M (Additive A)).obj.obj W)
      (sectionsAdditiveAddEquiv IM I A W.unop))
    (fun _ ↦ by ext f; exact ContMDiffMap.ext fun _ ↦ rfl)

-- Stored simp keys keep the carrier of `TopCat.of M` unreduced, so keep the section and point
-- arguments out of the index.
@[simp]
theorem smoothSheafCommGroup.sheafComposeToAddCommGrpIso_hom_app_apply
    [CommGroup A] [LieGroup I ∞ A] (W : Opens (TopCat.of M))
    (f : Additive C^∞⟮IM, W; I, A⟯) (x : W) :
    @DFunLike.coe (no_index C^∞⟮IM, W; I, Additive A⟯) (no_index ↥W) (fun _ ↦ Additive A) _
        (no_index
          ((smoothSheafCommGroup.sheafComposeToAddCommGrpIso IM I M A).hom.hom.app (op W) f)) x =
      Additive.ofMul ((Additive.toMul f : C^∞⟮IM, W; I, A⟯) x) :=
  (rfl)

@[simp]
theorem smoothSheafCommGroup.sheafComposeToAddCommGrpIso_inv_app_apply
    [CommGroup A] [LieGroup I ∞ A] (W : Opens (TopCat.of M))
    (g : C^∞⟮IM, W; I, Additive A⟯) (x : W) :
    @DFunLike.coe (no_index C^∞⟮IM, W; I, A⟯) (no_index ↥W) (fun _ ↦ A) _
        (no_index (Additive.toMul
          ((smoothSheafCommGroup.sheafComposeToAddCommGrpIso IM I M A).inv.hom.app (op W) g))) x =
      Additive.toMul (g x) :=
  (rfl)

end Additive

section SmulEnd

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {EM : Type*} [NormedAddCommGroup EM] [NormedSpace 𝕜 EM]
  {HM : Type*} [TopologicalSpace HM] (IM : ModelWithCorners 𝕜 EM HM)
  {M : Type u} [TopologicalSpace M] [ChartedSpace HM M]
  (V : Type u) [NormedAddCommGroup V] [NormedSpace 𝕜 V]

private def smulSectionAddMonoidHom (g : C^∞⟮IM, M; 𝓘(𝕜), 𝕜⟯) (W : Opens (TopCat.of M)) :
    C^∞⟮IM, W; 𝓘(𝕜, V), V⟯ →+ C^∞⟮IM, W; 𝓘(𝕜, V), V⟯ where
  toFun f := ⟨fun x ↦ g x.1 • f x, (g.contMDiff.comp contMDiff_subtype_val).smul f.contMDiff⟩
  map_zero' := ContMDiffMap.ext fun x ↦ smul_zero (g x.1)
  map_add' f₁ f₂ := ContMDiffMap.ext fun x ↦ smul_add (g x.1) (f₁ x) (f₂ x)

/-- Pointwise scalar multiplication by a global smooth function `g : C^∞⟮IM, M; 𝓘(𝕜), 𝕜⟯`, viewed
as a sheaf endomorphism of `smoothSheafAddCommGroup IM 𝓘(𝕜, V) M V`. -/
def smoothSheafAddCommGroup.smulEnd (g : C^∞⟮IM, M; 𝓘(𝕜), 𝕜⟯) :
    smoothSheafAddCommGroup IM 𝓘(𝕜, V) M V ⟶ smoothSheafAddCommGroup IM 𝓘(𝕜, V) M V :=
  ObjectProperty.homMk
    { app := fun W ↦ AddCommGrpCat.ofHom (smulSectionAddMonoidHom IM V g W.unop)
      naturality := fun {_ _} _ ↦ by ext f; exact ContMDiffMap.ext fun _ ↦ rfl }

@[simp]
theorem smoothSheafAddCommGroup.smulEnd_hom_app_apply (g : C^∞⟮IM, M; 𝓘(𝕜), 𝕜⟯)
    (W : Opens (TopCat.of M)) (f : C^∞⟮IM, W; 𝓘(𝕜, V), V⟯) (x : W) :
    @DFunLike.coe (no_index C^∞⟮IM, W; 𝓘(𝕜, V), V⟯) (no_index ↥W) (fun _ ↦ V) _
        (no_index ((smoothSheafAddCommGroup.smulEnd IM V g).hom.app (op W) f)) x =
      g x.1 • f x :=
  (rfl)

@[simp]
theorem smoothSheafAddCommGroup.smulEnd_zero :
    smoothSheafAddCommGroup.smulEnd IM V (0 : C^∞⟮IM, M; 𝓘(𝕜), 𝕜⟯) = 0 := by
  ext W f
  let f' : C^∞⟮IM, W.unop; 𝓘(𝕜, V), V⟯ := f
  exact ContMDiffMap.ext fun x ↦ zero_smul 𝕜 (f' x)

@[simp]
theorem smoothSheafAddCommGroup.smulEnd_one :
    smoothSheafAddCommGroup.smulEnd IM V (1 : C^∞⟮IM, M; 𝓘(𝕜), 𝕜⟯) = 𝟙 _ := by
  ext W f
  let f' : C^∞⟮IM, W.unop; 𝓘(𝕜, V), V⟯ := f
  exact ContMDiffMap.ext fun x ↦ one_smul 𝕜 (f' x)

theorem smoothSheafAddCommGroup.smulEnd_add (g₁ g₂ : C^∞⟮IM, M; 𝓘(𝕜), 𝕜⟯) :
    smoothSheafAddCommGroup.smulEnd IM V (g₁ + g₂) =
      smoothSheafAddCommGroup.smulEnd IM V g₁ + smoothSheafAddCommGroup.smulEnd IM V g₂ := by
  ext W f
  let f' : C^∞⟮IM, W.unop; 𝓘(𝕜, V), V⟯ := f
  exact ContMDiffMap.ext fun x ↦ add_smul (g₁ x.1) (g₂ x.1) (f' x)

end SmulEnd

section FineAndCohomology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H]

/-- **Smooth vector-valued functions form a fine sheaf.** On a Hausdorff `σ`-compact manifold
modelled on a finite-dimensional real normed space, `smoothSheafAddCommGroup I 𝓘(ℝ, V) M V` is a
fine sheaf of abelian groups via smooth partitions of unity. -/
instance isFine_smoothSheafAddCommGroup {I : ModelWithCorners ℝ E H}
    {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [FiniteDimensional ℝ E] [T2Space M] [SigmaCompactSpace M]
    {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V] :
    TopCat.Sheaf.IsFine (smoothSheafAddCommGroup I 𝓘(ℝ, V) M V) where
  exists_partition {ι} U hU := by
    have hU_univ : (Set.univ : Set M) ⊆ ⋃ i, (U i : Set M) := fun x _ ↦ by
      have hx : x ∈ (⊤ : Opens (TopCat.of M)) := trivial
      rw [← hU] at hx
      obtain ⟨i, hxi⟩ := Opens.mem_iSup.mp hx
      exact Set.mem_iUnion.mpr ⟨i, hxi⟩
    obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate I isClosed_univ
      (fun i ↦ (U i : Set M)) (fun i ↦ (U i).isOpen) hU_univ
    refine ⟨fun i ↦ tsupport (ρ i), fun i ↦ smoothSheafAddCommGroup.smulEnd I V (ρ i),
      ρ.locallyFinite.closure, fun i ↦ isClosed_tsupport (ρ i), hρ, ?_, ?_⟩
    · intro i W hdisj
      ext f
      let f' : C^∞⟮I, W; 𝓘(ℝ, V), V⟯ := f
      refine ContMDiffMap.ext fun x ↦ ?_
      have hxK : x.1 ∉ tsupport (ρ i) := Set.disjoint_left.mp hdisj x.2
      have hρ0 : ρ i x.1 = 0 := Function.notMem_support.mp fun hs ↦ hxK (subset_tsupport _ hs)
      exact (congrArg (· • f' x) hρ0).trans (zero_smul ℝ (f' x))
    · intro W s hs
      apply AddCommGrpCat.hom_ext
      ext f
      let f' : C^∞⟮I, W; 𝓘(ℝ, V), V⟯ := f
      refine ContMDiffMap.ext fun x ↦ ?_
      have hsub : ρ.finsupport x.1 ⊆ s := fun i hi ↦ by
        by_contra hns
        have hne : ρ i x.1 ≠ 0 := ρ.mem_finsupport x.1 |>.mp hi
        exact Set.disjoint_left.mp (hs i hns) x.2 (subset_tsupport _ hne)
      let evalSum (t : Finset ι) : C^∞⟮I, W; 𝓘(ℝ, V), V⟯ :=
        (∑ i ∈ t, (smoothSheafAddCommGroup.smulEnd I V (ρ i)).hom.app (op W)).hom f
      have heval (t : Finset ι) : evalSum t x = ∑ i ∈ t, ρ i x.1 • f' x := by
        induction t using Finset.cons_induction with
        | empty =>
          have h0 := congrArg (fun η ↦ (η.hom f : C^∞⟮I, W; 𝓘(ℝ, V), V⟯) x)
            (Finset.sum_empty (f := fun i : ι ↦
              (smoothSheafAddCommGroup.smulEnd I V (ρ i)).hom.app (op W)))
          exact h0.trans Finset.sum_empty.symm
        | cons a t ha ih =>
          have hcons := congrArg (fun η ↦ (η.hom f : C^∞⟮I, W; 𝓘(ℝ, V), V⟯) x)
            (Finset.sum_cons ha (f := fun i : ι ↦
              (smoothSheafAddCommGroup.smulEnd I V (ρ i)).hom.app (op W)))
          exact hcons.trans ((congrArg₂ (· + ·) rfl ih).trans (Finset.sum_cons ha).symm)
      exact (heval s).trans <|
        (Finset.sum_smul.symm).trans <|
          (congrArg (· • f' x) (ρ.sum_finsupport' x.1 (Set.mem_univ x.1) hsub)).trans
            (one_smul ℝ (f' x))

/-- Every Hausdorff second-countable manifold modelled on a finite-dimensional real normed space is
locally compact and therefore `σ`-compact, so its sheaf of smooth vector-valued functions is
fine. -/
instance (priority := 100) isFine_smoothSheafAddCommGroup_of_secondCountableTopology
    {I : ModelWithCorners ℝ E H} {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [FiniteDimensional ℝ E] [T2Space M] [SecondCountableTopology M]
    {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V] :
    TopCat.Sheaf.IsFine (smoothSheafAddCommGroup I 𝓘(ℝ, V) M V) := by
  have : LocallyCompactSpace H := I.locallyCompactSpace
  have : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace H M
  infer_instance

/-- On a Hausdorff `σ`-compact manifold modelled on a finite-dimensional real normed space, the
sheaf cohomology of `smoothSheafAddCommGroup I 𝓘(ℝ, V) M V` vanishes in every positive degree. -/
theorem subsingleton_H_smoothSheafAddCommGroup_of_sigmaCompactSpace
    (I : ModelWithCorners ℝ E H) {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [FiniteDimensional ℝ E] [T2Space M] [SigmaCompactSpace M]
    {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V] (n : ℕ) (hn : 0 < n) :
    Subsingleton ((smoothSheafAddCommGroup I 𝓘(ℝ, V) M V).H n) :=
  TopCat.Sheaf.subsingleton_H_of_isFine (smoothSheafAddCommGroup I 𝓘(ℝ, V) M V) n hn

/-- **Acyclicity of smooth vector-valued functions.** On a Hausdorff second-countable manifold `M`
modelled on a finite-dimensional real normed space, the sheaf cohomology `Hⁿ(M, C^∞_M(V))` of
`smoothSheafAddCommGroup I 𝓘(ℝ, V) M V` vanishes in every positive degree `n > 0`. -/
theorem subsingleton_H_smoothSheafAddCommGroup
    (I : ModelWithCorners ℝ E H) {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [FiniteDimensional ℝ E] [T2Space M] [SecondCountableTopology M]
    {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V] (n : ℕ) (hn : 0 < n) :
    Subsingleton ((smoothSheafAddCommGroup I 𝓘(ℝ, V) M V).H n) :=
  TopCat.Sheaf.subsingleton_H_of_isFine (smoothSheafAddCommGroup I 𝓘(ℝ, V) M V) n hn

/-- On a Hausdorff second-countable manifold `M` modelled on a finite-dimensional real normed
space, the local sheaf cohomology `Hⁿ(U, C^∞_M(V))` of `smoothSheafAddCommGroup I 𝓘(ℝ, V) M V`
vanishes in every positive degree over every open subset `U` of `M`. -/
theorem subsingleton_H'_smoothSheafAddCommGroup
    (I : ModelWithCorners ℝ E H) {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [FiniteDimensional ℝ E] [T2Space M] [SecondCountableTopology M]
    {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (U : Opens (TopCat.of M)) (n : ℕ) (hn : 0 < n) :
    Subsingleton ((smoothSheafAddCommGroup I 𝓘(ℝ, V) M V).H' n U) := by
  have : TopCat.Sheaf.IsFine (X := TopCat.of U)
      (U.sheafRestrict.obj (smoothSheafAddCommGroup I 𝓘(ℝ, V) M V)) :=
    TopCat.Sheaf.IsFine.of_iso (smoothSheafAddCommGroup.restrictIso I 𝓘(ℝ, V) V U).symm
  exact TopCat.Sheaf.subsingleton_H'_of_isFine_sheafRestrict
    (smoothSheafAddCommGroup I 𝓘(ℝ, V) M V) U n hn

end FineAndCohomology

end TauCeti
