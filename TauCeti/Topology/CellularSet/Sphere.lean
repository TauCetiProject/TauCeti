/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Compactification.OnePoint.Basic
public import TauCeti.Topology.CellularSet.Basic
import Mathlib.Topology.Compactification.OnePoint.Sphere
import Mathlib.Topology.Order.IntermediateValue
import TauCeti.Analysis.Normed.Module.Ball.Homeomorph
import TauCeti.Topology.CellularSet.InverseSet
import TauCeti.Topology.Compactness.Normed
import TauCeti.Topology.Compactification.OnePoint.Collapse

/-!
# A compact space covered by two Euclidean open sets is a sphere

Let `X` be a compact Hausdorff space covered by two open sets `U` and `V`, each homeomorphic to a
real normed space `E` of dimension `m > 0`. Then `X` is homeomorphic to the sphere `Sᵐ`
(`TauCeti.nonempty_homeomorph_sphere_of_two_euclidean_opens`). This is the topological form of
Milnor's recognition of spheres (Milnor 1959, Theorem 1 (3) and Corollary 1; Rosen 1960, Lemma 1),
and it is what identifies a closed manifold carrying a function with exactly two critical points,
possibly degenerate, with a sphere.

The proof collapses the complement `C = X \ U` to a point. The collapse `X → OnePoint U` is
continuous, and `OnePoint U ≃ₜ OnePoint E` is the sphere `Sᵐ`. Since `C` is a compact subset of
`V ≃ₜ E`, it lies in the open unit ball of suitably scaled coordinates `κ : E → V`. It remains to
see that `C` is cellular in these coordinates, for then collapsing it does not change `X`
(`TauCeti.IsCellularSet.nonempty_homeomorph_onePoint`).

* For `m ≥ 2`, the collapse restricted to the closed unit ball of `E`, read through `κ`, maps the
  ball into `Sᵐ` and is injective off `C`; so `C` is the only inverse set of a map of an `m`-cell
  into `Sᵐ`, and it is cellular by M. Brown's theorem on inverse sets
  (`TauCeti.isCellularSet_closedBall_inter_preimage`).
* For `m = 1`, `C` is a compact subset of the line, and it is an interval: a bounded gap
  `(s, u)` of `C` would be open and closed in the connected set `U`, hence all of `U`, and then
  `X` would be covered by the coordinate line. A closed interval is cellular.

## Main results

* `TauCeti.IsCellularSet.nonempty_homeomorph_onePoint`: if the complement of an open set `U` of a
  compact Hausdorff space `X` is cellular in Euclidean coordinates, then `X` is the one-point
  compactification of `U`.
* `TauCeti.nonempty_homeomorph_sphere_of_two_euclidean_opens`: a compact Hausdorff space covered
  by two open sets homeomorphic to `ℝᵐ`, `m > 0`, is homeomorphic to `Sᵐ`.

## References

* J. Milnor, *Sommes de variétés différentiables et structures différentiables des sphères*,
  Bull. Soc. Math. France 87 (1959), 439–444, Theorem 1 and Corollary 1.
* R. H. Rosen, *A weak form of the star conjecture for manifolds*, Notices Amer. Math. Soc. 7
  (1960), abstract 570-28, p. 380, Lemma 1.
* M. Brown, *A proof of the generalized Schoenflies theorem*, Bull. Amer. Math. Soc. 66 (1960),
  74–76, Theorems 2 and 3.
-/

public section

open Function Metric Module OnePoint Set Topology

namespace TauCeti

variable {X E : Type*} [TopologicalSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **A cellular complement of an open set.** Let `U` be an open subset of a compact Hausdorff
space `X` whose complement is the image of a cellular set `A ⊆ E` under an open embedding
`κ : E → X` of a finite-dimensional real normed space. Then `X` is homeomorphic to the one-point
compactification of `U`: collapsing `X \ U` to a point does not change `X`. -/
theorem IsCellularSet.nonempty_homeomorph_onePoint [FiniteDimensional ℝ E] [CompactSpace X]
    [T2Space X] {U : Set X} (hU : IsOpen U) {A : Set E} (hA : IsCellularSet E A) {κ : E → X}
    (hκ : IsOpenEmbedding κ) (hAU : κ '' A = Uᶜ) : Nonempty (X ≃ₜ OnePoint U) := by
  have := hU.locallyCompactSpace
  refine hA.nonempty_homeomorph_of_isOpenEmbedding hκ
    (continuous_onePointCollapse hU.isOpenEmbedding_subtypeVal isProperMap_id) (fun z ↦ ?_)
    fun x y ↦ by
      rw [hAU, onePointCollapse_eq_onePointCollapse_iff Subtype.val_injective injective_id,
        Subtype.range_coe]
      rfl
  induction z using OnePoint.rec with
  | infty =>
    obtain ⟨x, hx⟩ := hA.nonempty.image κ
    rw [hAU] at hx
    exact ⟨x, onePointCollapse_of_notMem_range (by rwa [Subtype.range_coe])⟩
  | coe u => exact ⟨u, onePointCollapse_apply Subtype.val_injective id u⟩

/-- In dimension at least `2`, the complement of `U` read in coordinates `κ` which carry the open
unit ball over it is cellular. It is the only inverse set of the collapse of `X \ U` to `∞`,
restricted to the closed unit ball, so this is M. Brown's theorem on inverse sets. -/
private theorem exists_isCellularSet_image_eq_compl_of_two_le [FiniteDimensional ℝ E] [T2Space X]
    (hE : 2 ≤ finrank ℝ E) {U : Set X} (hU : IsOpen U) (eU : U ≃ₜ E) {κ : E → X}
    (hκ : IsOpenEmbedding κ) (hUκ : Uᶜ ⊆ κ '' ball 0 1) (hne : Uᶜ.Nonempty) :
    ∃ A : Set E, IsCellularSet E A ∧ κ '' A = Uᶜ := by
  set j : OnePoint U ≃ₜ sphere (0 : EuclideanSpace ℝ (Fin (finrank ℝ E + 1))) 1 :=
    eU.onePointCongr.trans (onePointEquivSphereOfFinrankEq (by simp))
  set f := j ∘ onePointCollapse ((↑) : U → X) id ∘ κ
  have hf : Continuous f := j.continuous.comp
    ((continuous_onePointCollapse hU.isOpenEmbedding_subtypeVal isProperMap_id).comp hκ.continuous)
  have hfy (v : E) : f v = j ∞ ↔ κ v ∉ U := by
    simp only [f, comp_apply, j.injective.eq_iff]
    rw [onePointCollapse_eq_infty_iff Subtype.val_injective, Subtype.range_coe]
  have hball {v : E} (hv : κ v ∉ U) : v ∈ ball 0 1 := by
    obtain ⟨w, hw, hwv⟩ := hUκ hv
    rwa [← hκ.injective hwv]
  refine ⟨closedBall 0 1 ∩ f ⁻¹' {j ∞}, isCellularSet_closedBall_inter_preimage hE (by simp)
    hf.continuousOn (fun v hv w _ hvw ↦ ?_) ?_ ?_, ?_⟩
  · -- `f` is injective off the fibre over `∞`.
    have := (onePointCollapse_eq_onePointCollapse_iff Subtype.val_injective injective_id).1
      (j.injective hvw)
    rw [Subtype.range_coe] at this
    exact hκ.injective (this.resolve_right fun h ↦ hv.2 ((hfy v).2 h.1))
  · rintro ⟨v, hv, hfv⟩
    exact sphere_disjoint_ball.ne_of_mem hv (hball ((hfy v).1 hfv)) rfl
  · obtain ⟨x, hx⟩ := hne
    obtain ⟨v, hv, rfl⟩ := hUκ hx
    exact ⟨v, ball_subset_closedBall hv, (hfy v).2 hx⟩
  · ext x
    refine ⟨fun ⟨v, ⟨_, hv⟩, hvx⟩ ↦ hvx ▸ (hfy v).1 hv, fun hx ↦ ?_⟩
    obtain ⟨v, hv, rfl⟩ := hUκ hx
    exact ⟨v, ⟨ball_subset_closedBall hv, (hfy v).2 hx⟩, rfl⟩

/-- In dimension `1`, the complement of a connected open set `U` of a compact Hausdorff space,
read in line coordinates `κ` which carry a compact set over it, is a closed interval, hence
cellular. A bounded gap `(s, u)` of it would be open and closed in `U`, so `U` and then `X` would
be covered by the line. -/
private theorem isCellularSet_preimage_compl_of_real [CompactSpace X] [T2Space X] {U : Set X}
    (hU : IsOpen U) (hUc : IsPreconnected U) {κ : ℝ → X} (hκ : IsOpenEmbedding κ) {K : Set ℝ}
    (hK : IsCompact K) (hUK : Uᶜ ⊆ κ '' K) (hne : Uᶜ.Nonempty) :
    IsCellularSet ℝ (κ ⁻¹' Uᶜ) := by
  set A := κ ⁻¹' Uᶜ
  have hAK : A ⊆ K := fun v hv ↦ by
    obtain ⟨w, hw, hwv⟩ := hUK hv
    rwa [← hκ.injective hwv]
  have hAc : IsCompact A :=
    hK.of_isClosed_subset (hU.isClosed_compl.preimage hκ.continuous) hAK
  have hAne : A.Nonempty := by
    obtain ⟨x, hx⟩ := hne
    obtain ⟨v, -, rfl⟩ := hUK hx
    exact ⟨v, hx⟩
  -- `A` has no gaps.
  have hAo : A.OrdConnected := by
    refine ⟨fun s hs u hu t ht ↦ by_contra fun htA ↦ ?_⟩
    -- The points of `U` over `[s, u]` are those over `(s, u) \ A`, an open and closed part of `U`.
    have hS : IsOpen (κ '' (Ioo s u ∩ Aᶜ)) := hκ.isOpenMap _
      (isOpen_Ioo.inter (hU.isClosed_compl.preimage hκ.continuous).isOpen_compl)
    have hI : IsClosed (κ '' Icc s u) := (isCompact_Icc.image hκ.continuous).isClosed
    have hSI : κ '' (Ioo s u ∩ Aᶜ) ⊆ κ '' Icc s u := image_mono fun v hv ↦ Ioo_subset_Icc_self hv.1
    have hcover : U ⊆ κ '' (Ioo s u ∩ Aᶜ) ∪ (κ '' Icc s u)ᶜ := fun x hx ↦ by
      by_cases hxI : x ∈ κ '' Icc s u
      · obtain ⟨v, hv, rfl⟩ := hxI
        have hvA : v ∉ A := fun h ↦ h hx
        refine .inl ⟨v, ⟨⟨hv.1.lt_of_ne ?_, hv.2.lt_of_ne ?_⟩, hvA⟩, rfl⟩
        · rintro rfl; exact hvA hs
        · rintro rfl; exact hvA hu
      · exact .inr hxI
    have hUS := hUc.subset_left_of_subset_union hS hI.isOpen_compl
      (disjoint_compl_right_iff_subset.2 hSI) hcover
      ⟨κ t, not_not.1 htA, t, ⟨⟨(ht.1.lt_of_ne ?_), ht.2.lt_of_ne ?_⟩, htA⟩, rfl⟩
    · -- Then the line covers `X`, which is impossible since `X` is compact.
      have hrange : range κ = univ := eq_univ_of_forall fun x ↦ by
        by_cases hx : x ∈ U
        · exact image_subset_range _ _ (hUS hx)
        · exact image_subset_range _ _ (hUK hx)
      exact noncompact_univ ℝ (hκ.isEmbedding.isCompact_iff.2 (by
        rw [image_univ, hrange]; exact isCompact_univ))
    · rintro rfl; exact htA hs
    · rintro rfl; exact htA hu
  -- A nonempty compact interval is a closed ball.
  have hA : A = Icc (sInf A) (sSup A) := eq_Icc_of_connected_compact ⟨hAne, hAo.isPreconnected⟩ hAc
  have hle : sInf A ≤ sSup A := csInf_le_csSup hAne hAc.bddBelow hAc.bddAbove
  rw [hA, Real.Icc_eq_closedBall]
  exact isCellularSet_closedBall _ (by linarith)

/-- **A compact space covered by two Euclidean open sets is a sphere.** Let `X` be a compact
Hausdorff space covered by two open sets `U` and `V`, each homeomorphic to a real normed space `E`
of dimension `m > 0`. Then `X` is homeomorphic to the unit sphere of any real normed space of
dimension `m + 1` (Milnor 1959, Corollary 1; Rosen 1960, Lemma 1).

Neither `m > 0` nor compactness can be dropped: a point is covered twice by `ℝ⁰` and is not `S⁰`,
and `ℝᵐ` is covered by two copies of itself but is not compact. -/
theorem nonempty_homeomorph_sphere_of_two_euclidean_opens [CompactSpace X] [T2Space X]
    {U V : Set X} (hU : IsOpen U) (hV : IsOpen V) (hUV : U ∪ V = univ) (eU : U ≃ₜ E)
    (eV : V ≃ₜ E) (hE : 0 < finrank ℝ E) {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (hEF : finrank ℝ F = finrank ℝ E + 1) : Nonempty (X ≃ₜ sphere (0 : F) 1) := by
  have : FiniteDimensional ℝ E := Module.finite_of_finrank_pos hE
  have : FiniteDimensional ℝ F := Module.finite_of_finrank_pos (by omega)
  have : Nontrivial E := Module.nontrivial_of_finrank_pos hE
  -- The one-point compactification of `U` is the sphere.
  suffices Nonempty (X ≃ₜ OnePoint U) from this.map fun h ↦ h.trans <| eU.onePointCongr.trans <|
    (onePointEquivSphereOfFinrankEq (ι := Fin (finrank ℝ E + 1)) (by simp)).trans
      (sphereHomeomorphOfFinrankEq (by simp [hEF]))
  -- The complement of `U` is nonempty, since `E` is not compact.
  have hne : Uᶜ.Nonempty := by
    by_contra h
    have : CompactSpace U := isCompact_iff_compactSpace.1 (by
      rw [compl_empty_iff.1 (not_nonempty_iff_eq_empty.1 h)]; exact isCompact_univ)
    exact noncompact_univ E (eU.compactSpace.isCompact_univ)
  -- Coordinates `κ` on `V`, scaled so that the open unit ball covers the complement of `U`.
  obtain ⟨S, hS0, hS⟩ := exists_nonneg_forall_notMem_norm_lt hU (by rwa [union_comm]) eV
  set κ : E → X := fun v ↦ (eV.symm ((S + 1) • v) : X)
  have hS1 : S + 1 ≠ 0 := by positivity
  have hκ : IsOpenEmbedding κ := hV.isOpenEmbedding_subtypeVal.comp
    (eV.symm.isOpenEmbedding.comp (Homeomorph.smulOfNeZero (S + 1) hS1).isOpenEmbedding)
  have hUκ : Uᶜ ⊆ κ '' ball 0 1 := fun x hx ↦ by
    have hxV : x ∈ V := (eq_univ_iff_forall.1 hUV x).resolve_left hx
    refine ⟨(S + 1)⁻¹ • eV ⟨x, hxV⟩, ?_, by simp [κ, smul_smul, hS1]⟩
    rw [mem_ball_zero_iff, norm_smul, Real.norm_of_nonneg (by positivity),
      inv_mul_lt_one₀ (by positivity)]
    linarith [hS ⟨x, hxV⟩ hx]
  rcases (by omega : 2 ≤ finrank ℝ E ∨ finrank ℝ E = 1) with h2 | h1
  · obtain ⟨A, hA, hAU⟩ :=
      exists_isCellularSet_image_eq_compl_of_two_le h2 hU eU hκ hUκ hne
    exact hA.nonempty_homeomorph_onePoint hU hκ hAU
  · -- In dimension `1`, use line coordinates.
    set L : E ≃L[ℝ] ℝ := ContinuousLinearEquiv.ofFinrankEq (by simp [← h1])
    have hκL : IsOpenEmbedding (κ ∘ L.symm) := hκ.comp L.symm.toHomeomorph.isOpenEmbedding
    have hUK : Uᶜ ⊆ (κ ∘ L.symm) '' (L '' closedBall 0 1) := by
      rw [image_comp, L.symm_image_image]
      exact hUκ.trans (image_mono ball_subset_closedBall)
    have hUc : IsPreconnected U := by
      rw [isPreconnected_iff_preconnectedSpace]
      exact eU.symm.surjective.denseRange.preconnectedSpace eU.symm.continuous
    refine (isCellularSet_preimage_compl_of_real hU hUc hκL
      ((isCompact_closedBall 0 1).image L.continuous) hUK hne).nonempty_homeomorph_onePoint hU hκL
      (image_preimage_eq_of_subset (hUK.trans (image_subset_range _ _)))

end TauCeti
