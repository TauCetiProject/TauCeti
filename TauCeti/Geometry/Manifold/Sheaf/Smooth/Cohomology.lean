/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.PartitionOfUnity
public import TauCeti.Geometry.Manifold.Sheaf.Smooth.Restrict
public import TauCeti.Geometry.Manifold.Sheaf.Smooth.ScalarAction
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

private theorem exists_local_finset (ρ : SmoothPartitionOfUnity ι I M) (x : M) :
    ∃ (N : Opens (TopCat.of M)) (_ : x ∈ N) (s : Finset ι),
      (∀ i, i ∉ s → N ≤ complSupport ρ i) ∧
      ∀ ⦃W : Opens (TopCat.of M)⦄, W ≤ N → ∀ y : W, ∑ i ∈ s, ρ i y.val = 1 := by
  obtain ⟨O, hO_sub, hO_open, hxO⟩ := mem_nhds_iff.1 (ρ.eventually_fintsupport_subset x)
  refine ⟨⟨O, hO_open⟩, hxO, ρ.fintsupport x,
    fun i hi y hy hmem ↦ hi (hO_sub hy ((ρ.mem_fintsupport_iff y i).2 hmem)), fun W hW y ↦ ?_⟩
  exact ρ.sum_finsupport' y.val (Set.mem_univ y.val)
    ((ρ.finsupport_subset_fintsupport y.val).trans (hO_sub (hW y.property)))

/-- A smooth partition of unity `ρ` subordinate to an open family `U` induces a sheaf partition of
unity on `smoothSheafAddCommGroup I 𝓘(ℝ, V) M V` by pointwise multiplication. -/
theorem isPartitionOfUnity_smoothSheafAddCommGroup (ρ : SmoothPartitionOfUnity ι I M)
    (hρ : ρ.IsSubordinate fun i ↦ (U i : Set M))
    (V : Type u) [NormedAddCommGroup V] [NormedSpace ℝ V] :
    (smoothSheafAddCommGroup I 𝓘(ℝ, V) M V).IsPartitionOfUnity U
      (fun i ↦ TauCeti.smoothSheafAddCommGroup.smulEnd I V (ρ i)) := by
  refine TopCat.Sheaf.isPartitionOfUnity_iff.2
    ⟨complSupport ρ, sup_complSupport_eq_top hρ, fun i W hW ↦ ?_, fun x ↦ ?_⟩
  · have hEq : Set.EqOn (ρ i) (0 : C^∞⟮I, M; 𝓘(ℝ), ℝ⟯) W :=
      fun y hy ↦ image_eq_zero_of_notMem_tsupport (f := ρ i) (hW hy)
    rw [TauCeti.smoothSheafAddCommGroup.smulEnd_hom_app_eq_of_eqOn I V hEq,
      TauCeti.smoothSheafAddCommGroup.smulEnd_zero]
    simp
  · obtain ⟨N, hxN, s, hs, hsum⟩ := exists_local_finset ρ x
    refine ⟨N, hxN, s, hs, fun W hW ↦ ?_⟩
    have hEq : Set.EqOn (∑ i ∈ s, ρ i : C^∞⟮I, M; 𝓘(ℝ), ℝ⟯) (1 : C^∞⟮I, M; 𝓘(ℝ), ℝ⟯) W :=
      fun y hy ↦ by
        simpa [ContMDiffMap.coe_sum] using hsum hW ⟨y, hy⟩
    have hsum_app :
        (∑ i ∈ s, TauCeti.smoothSheafAddCommGroup.smulEnd I V (ρ i)).hom.app (op W) =
          ∑ i ∈ s, (TauCeti.smoothSheafAddCommGroup.smulEnd I V (ρ i)).hom.app (op W) := by
      rw [← InducedCategory.homAddEquiv_apply, map_sum]
      simp
    rw [← hsum_app, ← TauCeti.smoothSheafAddCommGroup.smulEnd_sum,
      TauCeti.smoothSheafAddCommGroup.smulEnd_hom_app_eq_of_eqOn I V hEq,
      TauCeti.smoothSheafAddCommGroup.smulEnd_one, TopCat.Sheaf.id_app]

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
