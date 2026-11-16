/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.PartitionOfUnity
public import TauCeti.Geometry.Manifold.Sheaf.Smooth.Restrict
public import TauCeti.Topology.Sheaves.Fine
import Mathlib.Topology.Sets.OpenCover
import TauCeti.Geometry.Manifold.Algebra.SmoothFunctions

/-!
# Fineness and sheaf cohomology of smooth functions on a manifold

Smooth partitions of unity make the sheaf of smooth vector-valued functions
`smoothSheafAddCommGroup I 𝓘(ℝ, V) M V` on a Hausdorff, `σ`-compact finite-dimensional real
manifold *fine* (`TopCat.Sheaf.IsFine`). By the general acyclicity of fine sheaves
(`TauCeti.Topology.Sheaves.Fine`), its sheaf cohomology vanishes in every positive degree, with no
boundarylessness assumption on the model with corners `I`.

When `M` is Hausdorff and second countable, every open subset `U` of `M` is itself a Hausdorff,
`σ`-compact smooth manifold whose restricted sheaf `U.sheafRestrict.obj _` is isomorphic to the
sheaf of smooth functions on `U` (`TauCeti.smoothSheafAddCommGroup.restrictIso`). Consequently the
cohomology `Sheaf.H'` vanishes in positive degrees over every open subset `U` of `M` as well as
globally (`TauCeti.subsingleton_H'_smoothSheafAddCommGroup`,
`TauCeti.subsingleton_H_smoothSheafAddCommGroup`).

## Main declarations

* `TauCeti.smoothSheafAddCommGroup.smulEnd`: pointwise scalar multiplication of smooth
  vector-valued sections by a global smooth scalar function.
* `SmoothPartitionOfUnity.isPartitionOfUnity_smoothSheafAddCommGroup`: a subordinate smooth
  partition of unity induces a sheaf partition of unity on `smoothSheafAddCommGroup I 𝓘(ℝ, V) M V`.
* `TauCeti.smoothSheafAddCommGroup.isFine` and
  `TauCeti.smoothSheafAddCommGroup.subsingleton_H_of_pos`: fineness and global positive-degree
  cohomology vanishing on Hausdorff, `σ`-compact finite-dimensional smooth real manifolds.
* `TauCeti.smoothSheafAddCommGroup.subsingleton_H'_of_sigmaCompactSpace`,
  `TauCeti.subsingleton_H'_smoothSheafAddCommGroup`, and
  `TauCeti.subsingleton_H_smoothSheafAddCommGroup`: positive-degree sheaf cohomology of
  `smoothSheafAddCommGroup I 𝓘(ℝ, V) M V` vanishes over Hausdorff `σ`-compact open subsets, and
  over all open subsets and globally on any Hausdorff, second-countable finite-dimensional smooth
  real manifold.

## References

* R. Godement, *Topologie algébrique et théorie des faisceaux*, Hermann, Paris, 1958, Chapitre II,
  §3.7 and §4.4.
* Frank W. Warner, *Foundations of Differentiable Manifolds and Lie Groups*, Graduate Texts in
  Mathematics 94, Springer, 1983, Chapter 5, §5.11 and §5.25.
-/

public noncomputable section

open CategoryTheory Limits Opposite TopologicalSpace Topology
open scoped ContDiff Manifold

universe u

namespace TauCeti

/-! ### Scalar multiplication by global smooth functions -/

namespace smoothSheafAddCommGroup

section ScalarField

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {EM : Type*} [NormedAddCommGroup EM] [NormedSpace 𝕜 EM]
  {HM : Type*} [TopologicalSpace HM] (IM : ModelWithCorners 𝕜 EM HM)
  {M : Type u} [TopologicalSpace M] [ChartedSpace HM M]

/-- The inclusion of an open subset `W` of `M`, as a smooth map `C^∞⟮IM, W; IM, M⟯`. -/
private def subtypeValMap (W : Opens M) : C^∞⟮IM, W; IM, M⟯ :=
  ⟨Subtype.val, contMDiff_subtype_val⟩

private theorem subtypeValMap_apply (W : Opens M) (x : W) :
    subtypeValMap IM W x = x.1 :=
  rfl

variable (V : Type u) [NormedAddCommGroup V] [NormedSpace 𝕜 V]

/-- Pointwise multiplication on sections over `W` as an additive homomorphism from smooth scalar
functions on `W` to endomorphisms of `(smoothSheafAddCommGroup IM 𝓘(𝕜, V) M V).obj.obj (op W)`. -/
private def smulAppHom (W : Opens (TopCat.of M)) :
    C^∞⟮IM, W; 𝓘(𝕜), 𝕜⟯ →+
      ((smoothSheafAddCommGroup IM 𝓘(𝕜, V) M V).obj.obj (op W) ⟶
        (smoothSheafAddCommGroup IM 𝓘(𝕜, V) M V).obj.obj (op W)) :=
  (AddCommGrpCat.homAddEquiv
    (M := (smoothSheafAddCommGroup IM 𝓘(𝕜, V) M V).obj.obj (op W))
    (N := (smoothSheafAddCommGroup IM 𝓘(𝕜, V) M V).obj.obj (op W))).symm.toAddMonoidHom.comp
      (Module.toAddMonoidEnd C^∞⟮IM, W; 𝓘(𝕜), 𝕜⟯ C^∞⟮IM, W; 𝓘(𝕜, V), V⟯).toAddMonoidHom

private theorem smulAppHom_apply (W : Opens (TopCat.of M)) (c : C^∞⟮IM, W; 𝓘(𝕜), 𝕜⟯)
    (f : C^∞⟮IM, W; 𝓘(𝕜, V), V⟯) :
    smulAppHom IM V W c f = c • f :=
  rfl

private theorem map_apply {U₁ U₂ : (Opens (TopCat.of M))ᵒᵖ} (h : U₁ ⟶ U₂)
    (f : C^∞⟮IM, U₁.unop; 𝓘(𝕜, V), V⟯) :
    (smoothSheafAddCommGroup IM 𝓘(𝕜, V) M V).obj.map h f =
      ContMDiffMap.restrictAddMonoidHom IM 𝓘(𝕜, V) V (leOfHom h.unop) f :=
  rfl

private theorem smulAppHom_map_apply (g : C^∞⟮IM, M; 𝓘(𝕜), 𝕜⟯)
    {U₁ U₂ : (Opens (TopCat.of M))ᵒᵖ} (h : U₁ ⟶ U₂) (f : C^∞⟮IM, U₁.unop; 𝓘(𝕜, V), V⟯) :
    smulAppHom IM V U₂.unop (ContMDiffMap.compRightAlgHom 𝕜 𝕜 (subtypeValMap IM U₂.unop) g)
        ((smoothSheafAddCommGroup IM 𝓘(𝕜, V) M V).obj.map h f) =
      (smoothSheafAddCommGroup IM 𝓘(𝕜, V) M V).obj.map h
        (smulAppHom IM V U₁.unop (ContMDiffMap.compRightAlgHom 𝕜 𝕜 (subtypeValMap IM U₁.unop) g)
          f) := by
  rw [map_apply, smulAppHom_apply, smulAppHom_apply, map_apply]
  refine ContMDiffMap.ext fun x ↦ ?_
  simp [subtypeValMap_apply]

private theorem smulAppHom_one (W : Opens (TopCat.of M)) :
    smulAppHom IM V W 1 = 𝟙 ((smoothSheafAddCommGroup IM 𝓘(𝕜, V) M V).obj.obj (op W)) :=
  congrArg
    (AddCommGrpCat.homAddEquiv
      (M := (smoothSheafAddCommGroup IM 𝓘(𝕜, V) M V).obj.obj (op W))
      (N := (smoothSheafAddCommGroup IM 𝓘(𝕜, V) M V).obj.obj (op W))).symm
    (map_one (Module.toAddMonoidEnd C^∞⟮IM, W; 𝓘(𝕜), 𝕜⟯ C^∞⟮IM, W; 𝓘(𝕜, V), V⟯))

/-- Pointwise multiplication by a global smooth scalar function `g : C^∞⟮IM, M; 𝓘(𝕜), 𝕜⟯` as an
endomorphism of `smoothSheafAddCommGroup IM 𝓘(𝕜, V) M V`. -/
def smulEnd (g : C^∞⟮IM, M; 𝓘(𝕜), 𝕜⟯) :
    smoothSheafAddCommGroup IM 𝓘(𝕜, V) M V ⟶ smoothSheafAddCommGroup IM 𝓘(𝕜, V) M V :=
  ObjectProperty.homMk
    { app U := smulAppHom IM V U.unop
        (ContMDiffMap.compRightAlgHom 𝕜 𝕜 (subtypeValMap IM U.unop) g)
      naturality {U₁ U₂} h := ConcreteCategory.hom_ext _ _ fun f ↦ by
        rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply]
        exact smulAppHom_map_apply IM V g h f }

private theorem smulEnd_hom_app (g : C^∞⟮IM, M; 𝓘(𝕜), 𝕜⟯) (W : Opens (TopCat.of M)) :
    (smulEnd IM V g).hom.app (op W) =
      smulAppHom IM V W
        (ContMDiffMap.compRightAlgHom 𝕜 𝕜 (subtypeValMap IM W) g) :=
  rfl

/-- Evaluating `smulEnd IM V g` at a section over `W` multiplies pointwise by `g`. -/
@[simp]
theorem smulEnd_hom_app_apply (g : C^∞⟮IM, M; 𝓘(𝕜), 𝕜⟯) (W : Opens (TopCat.of M))
    (f : C^∞⟮IM, W; 𝓘(𝕜, V), V⟯) (x : W) :
    @DFunLike.coe (no_index C^∞⟮IM, W; 𝓘(𝕜, V), V⟯) (no_index ↥W) (fun _ ↦ V) _
        (no_index ((smulEnd IM V g).hom.app (op W) f)) x =
      g x.1 • f x := by
  rw [smulEnd_hom_app, smulAppHom_apply]
  simp [subtypeValMap_apply]

/-- Pointwise multiplication by `g₁ + g₂` is the sum of the corresponding sheaf endomorphisms. -/
theorem smulEnd_add (g₁ g₂ : C^∞⟮IM, M; 𝓘(𝕜), 𝕜⟯) :
    smulEnd IM V (g₁ + g₂) = smulEnd IM V g₁ + smulEnd IM V g₂ :=
  Sheaf.hom_ext <| NatTrans.ext <| funext fun ⟨W⟩ ↦ by
    rw [Sheaf.Hom.add_app, smulEnd_hom_app, map_add, map_add, smulEnd_hom_app, smulEnd_hom_app]

/-- Multiplication by the zero smooth function is the zero sheaf endomorphism. -/
@[simp]
theorem smulEnd_zero :
    smulEnd IM V (0 : C^∞⟮IM, M; 𝓘(𝕜), 𝕜⟯) = 0 :=
  Sheaf.hom_ext <| NatTrans.ext <| funext fun ⟨W⟩ ↦ by
    rw [smulEnd_hom_app, map_zero, map_zero]
    simp

/-- Multiplication by the constant smooth function `1` is the identity sheaf endomorphism. -/
@[simp]
theorem smulEnd_one :
    smulEnd IM V (1 : C^∞⟮IM, M; 𝓘(𝕜), 𝕜⟯) = 𝟙 (smoothSheafAddCommGroup IM 𝓘(𝕜, V) M V) :=
  Sheaf.hom_ext <| NatTrans.ext <| funext fun ⟨W⟩ ↦ by
    rw [smulEnd_hom_app, map_one, smulAppHom_one, TopCat.Sheaf.id_app]

end ScalarField

end smoothSheafAddCommGroup

end TauCeti

/-! ### Sheaf partitions of unity from smooth partitions of unity -/

namespace SmoothPartitionOfUnity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  {ι : Type*} {U : ι → Opens (TopCat.of M)}

/-- The open complement `(tsupport (ρ i))ᶜ` of the topological support of the `i`-th function in a
smooth partition of unity `ρ`. -/
private def complSupport (ρ : SmoothPartitionOfUnity ι I M) (i : ι) : Opens (TopCat.of M) :=
  ⟨(tsupport (ρ i))ᶜ, (isClosed_tsupport _).isOpen_compl⟩

private theorem sup_complSupport_eq_top {ρ : SmoothPartitionOfUnity ι I M}
    (hρ : ρ.IsSubordinate fun i ↦ (U i : Set M)) (i : ι) :
    U i ⊔ complSupport ρ i = ⊤ := by
  ext x
  simp only [Opens.coe_sup, Opens.coe_top, Set.mem_union, Set.mem_univ, iff_true]
  by_cases hx : x ∈ tsupport (ρ i)
  · exact Or.inl (hρ i hx)
  · exact Or.inr hx

private theorem restrict_eq_zero_of_le_complSupport (ρ : SmoothPartitionOfUnity ι I M) (i : ι)
    {W : Opens (TopCat.of M)} (hW : W ≤ complSupport ρ i) :
    ContMDiffMap.compRightAlgHom ℝ ℝ
        (TauCeti.smoothSheafAddCommGroup.subtypeValMap I W) (ρ i) = 0 := by
  ext y
  simpa [TauCeti.smoothSheafAddCommGroup.subtypeValMap_apply] using
    image_eq_zero_of_notMem_tsupport (f := ρ i) (hW y.2)

private theorem sum_restrict_eq_one (ρ : SmoothPartitionOfUnity ι I M) {s : Finset ι}
    {W : Opens (TopCat.of M)} (hsum : ∀ y : W, ∑ i ∈ s, ρ i y.1 = 1) :
    ∑ i ∈ s,
      ContMDiffMap.compRightAlgHom ℝ ℝ
        (TauCeti.smoothSheafAddCommGroup.subtypeValMap I W) (ρ i) = 1 := by
  ext y
  simpa [TauCeti.smoothSheafAddCommGroup.subtypeValMap_apply] using hsum y

private theorem exists_local_finset (ρ : SmoothPartitionOfUnity ι I M) (x : M) :
    ∃ (N : Opens (TopCat.of M)) (_ : x ∈ N) (s : Finset ι),
      (∀ i, i ∉ s → N ≤ complSupport ρ i) ∧
      ∀ ⦃W : Opens (TopCat.of M)⦄, W ≤ N → ∀ y : W, ∑ i ∈ s, ρ i y.1 = 1 := by
  obtain ⟨O, hO_sub, hO_open, hxO⟩ := mem_nhds_iff.1 (ρ.eventually_fintsupport_subset x)
  refine ⟨⟨O, hO_open⟩, hxO, ρ.fintsupport x,
    fun i hi y hy hmem ↦ hi (hO_sub hy ((ρ.mem_fintsupport_iff y i).2 hmem)), fun W hW y ↦ ?_⟩
  exact ρ.sum_finsupport' y.1 (Set.mem_univ y.1)
    ((ρ.finsupport_subset_fintsupport y.1).trans (hO_sub (hW y.2)))

/-- A smooth partition of unity `ρ` subordinate to an open family `U` induces a sheaf partition of
unity on `smoothSheafAddCommGroup I 𝓘(ℝ, V) M V` by pointwise multiplication. -/
theorem isPartitionOfUnity_smoothSheafAddCommGroup (ρ : SmoothPartitionOfUnity ι I M)
    (hρ : ρ.IsSubordinate fun i ↦ (U i : Set M))
    (V : Type u) [NormedAddCommGroup V] [NormedSpace ℝ V] :
    (smoothSheafAddCommGroup I 𝓘(ℝ, V) M V).IsPartitionOfUnity U
      (fun i ↦ TauCeti.smoothSheafAddCommGroup.smulEnd I V (ρ i)) := by
  refine TopCat.Sheaf.isPartitionOfUnity_iff.2
    ⟨complSupport ρ, sup_complSupport_eq_top hρ, fun i W hW ↦ ?_, fun x ↦ ?_⟩
  · rw [TauCeti.smoothSheafAddCommGroup.smulEnd_hom_app,
      restrict_eq_zero_of_le_complSupport ρ i hW, map_zero]
  · obtain ⟨N, hxN, s, hs, hsum⟩ := exists_local_finset ρ x
    refine ⟨N, hxN, s, hs, fun W hW ↦ ?_⟩
    rw [Finset.sum_congr rfl fun i _ ↦
        TauCeti.smoothSheafAddCommGroup.smulEnd_hom_app I V (ρ i) W,
      ← map_sum, sum_restrict_eq_one ρ (hsum hW),
      TauCeti.smoothSheafAddCommGroup.smulAppHom_one]

end SmoothPartitionOfUnity

/-! ### Fineness and positive-degree sheaf cohomology vanishing -/

namespace TauCeti

section SigmaCompact

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

namespace smoothSheafAddCommGroup

/-- On a Hausdorff, `σ`-compact finite-dimensional smooth real manifold (possibly with boundary or
corners), the sheaf `smoothSheafAddCommGroup I 𝓘(ℝ, V) M V` of smooth `V`-valued functions is
fine. -/
instance isFine (V : Type u) [NormedAddCommGroup V] [NormedSpace ℝ V] :
    (smoothSheafAddCommGroup I 𝓘(ℝ, V) M V).IsFine where
  exists_isPartitionOfUnity _ U hU := by
    obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate I isClosed_univ
      (fun i ↦ (U i : Set M)) (fun i ↦ (U i).isOpen) (IsOpenCover.mk hU).iSup_set_eq_univ.ge
    exact ⟨_, ρ.isPartitionOfUnity_smoothSheafAddCommGroup hρ V⟩

/-- On a Hausdorff, `σ`-compact finite-dimensional smooth real manifold, the sheaf cohomology of
`smoothSheafAddCommGroup I 𝓘(ℝ, V) M V` vanishes in every positive degree. -/
theorem subsingleton_H_of_pos {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (n : ℕ) (hn : 0 < n) :
    Subsingleton ((smoothSheafAddCommGroup I 𝓘(ℝ, V) M V).H n) :=
  TopCat.Sheaf.IsFine.subsingleton_H_of_pos n hn

end smoothSheafAddCommGroup

end SigmaCompact

section OpenSubset

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- Over any Hausdorff, `σ`-compact open subset `U` of a finite-dimensional smooth real manifold
`M` (without requiring `M` itself to be Hausdorff or `σ`-compact), the sheaf cohomology
`Sheaf.H'` of `smoothSheafAddCommGroup I 𝓘(ℝ, V) M V` vanishes in every positive degree. -/
theorem smoothSheafAddCommGroup.subsingleton_H'_of_sigmaCompactSpace
    {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (U : Opens (TopCat.of M)) [T2Space U] [SigmaCompactSpace U] (n : ℕ) (hn : 0 < n) :
    Subsingleton ((smoothSheafAddCommGroup I 𝓘(ℝ, V) M V).H' n U) := by
  have : TopCat.Sheaf.IsFine (X := TopCat.of U)
      (U.sheafRestrict.obj (smoothSheafAddCommGroup I 𝓘(ℝ, V) M V)) :=
    TopCat.Sheaf.IsFine.of_iso (X := TopCat.of U)
      (smoothSheafAddCommGroup.restrictIso I 𝓘(ℝ, V) V U).symm
  exact TopCat.Sheaf.IsFine.subsingleton_H'_of_sheafRestrict_of_pos n hn

end OpenSubset

section SecondCountable

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SecondCountableTopology M]
  {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- **Open-subset acyclicity of smooth functions.** On a Hausdorff, second-countable
finite-dimensional smooth real manifold (possibly with boundary or corners), the sheaf cohomology
`Sheaf.H'` of `smoothSheafAddCommGroup I 𝓘(ℝ, V) M V` vanishes in every positive degree over every
open subset `U` of `M`. -/
theorem subsingleton_H'_smoothSheafAddCommGroup (U : Opens (TopCat.of M)) (n : ℕ) (hn : 0 < n) :
    Subsingleton ((smoothSheafAddCommGroup I 𝓘(ℝ, V) M V).H' n U) := by
  have : LocallyCompactSpace U := Manifold.locallyCompact_of_finiteDimensional I
  exact smoothSheafAddCommGroup.subsingleton_H'_of_sigmaCompactSpace I U n hn

/-- **Acyclicity of the sheaf of smooth functions.** On a Hausdorff, second-countable
finite-dimensional smooth real manifold (possibly with boundary or corners), the sheaf cohomology
`Sheaf.H` of `smoothSheafAddCommGroup I 𝓘(ℝ, V) M V` vanishes in every positive degree. -/
theorem subsingleton_H_smoothSheafAddCommGroup (n : ℕ) (hn : 0 < n) :
    Subsingleton ((smoothSheafAddCommGroup I 𝓘(ℝ, V) M V).H n) := by
  have : LocallyCompactSpace M := Manifold.locallyCompact_of_finiteDimensional I
  exact smoothSheafAddCommGroup.subsingleton_H_of_pos I n hn

end SecondCountable

end TauCeti
