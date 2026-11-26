/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.SmoothSingular.DeRham.MayerVietoris
import TauCeti.Geometry.Manifold.MayerVietoris
import TauCeti.Geometry.Manifold.Metrizable
import TauCeti.Geometry.Manifold.SmoothSingular.DeRham.Theorem

/-!
# The de Rham theorem

Let `M` be a Hausdorff `σ`-compact smooth manifold modelled on a finite-dimensional real model
with corners, possibly with boundary or corners. **The de Rham theorem** says that the de Rham
homomorphism `TauCeti.deRhamHom I M k : H^k_dR(M) → Hᵏ(M; ℝ)`, integration of closed forms over
smooth singular simplices, is bijective in every degree (`TauCeti.bijective_deRhamHom`). This
gives the **de Rham isomorphism** `TauCeti.deRhamEquiv I M k : H^k_dR(M) ≃ₗ[ℝ] Hᵏ(M; ℝ)` between
de Rham cohomology and singular cohomology with real coefficients: every real singular class is
the image of the class of a closed form, and a closed form whose class has zero image is exact.

**The proof** is a Mayer–Vietoris induction over the open subsets `U` of `M`
(`TauCeti.mayerVietoris_induction_extChartAt`), for the property that the de Rham homomorphism of
`U` is bijective in every degree. Every open subset of `M` is again a Hausdorff `σ`-compact
manifold (`TauCeti.Manifold.sigmaCompactSpace_opens`), and `M` is second countable and locally
compact, so the induction applies. Its hypotheses are the following.

* **The empty set**: both cohomologies vanish (`TauCeti.bijective_deRhamHom_of_isEmpty`).
* **Convex chart domains**: the extended chart at `x` maps the open set
  `(chartAt H x).source ∩ (extChartAt I x)⁻¹' C`, for a convex open `C` with
  `C ∩ range I ⊆ (extChartAt I x).target`, onto the convex set `C ∩ range I`. Contracting along
  straight lines in the chart, the de Rham homomorphism is bijective there
  (`TauCeti.bijective_deRhamHom_of_starConvex_image_extChartAt`).
* **Binary unions**: if it is bijective on `U`, on `V` and on `U ⊓ V`, the five lemma applied to
  the two Mayer–Vietoris sequences gives bijectivity on `U ⊔ V`
  (`TauCeti.bijective_deRhamHom_of_sup_eq_top`). That step is stated for a cover of the whole
  manifold, so it is applied to the manifold `U ⊔ V`, whose open subsets lying over `U`, `V` and
  `U ⊓ V` are diffeomorphic to them (`Diffeomorph.nestedOpen`); bijectivity of the de Rham
  homomorphism is invariant under diffeomorphisms
  (`Diffeomorph.bijective_deRhamHom_iff`).
* **Countable disjoint unions**: both cohomologies of a disjoint union of open sets are the
  products of those of the pieces (`TauCeti.bijective_deRhamHom_iSup`).

Taking `U = M` proves the theorem.

## Main results

* `TauCeti.bijective_deRhamHom`: the de Rham theorem, that the de Rham homomorphism is bijective
  in every degree.
* `TauCeti.deRhamEquiv`: the de Rham isomorphism `H^k_dR(M) ≃ₗ[ℝ] Hᵏ(M; ℝ)`.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Theorem 18.14 and its proof.
* R. Bott and L. W. Tu, *Differential Forms in Algebraic Topology*, Graduate Texts in Mathematics
  82, Springer, 1982, Theorem 8.9 and §5.
-/

public section

noncomputable section

open Set TopologicalSpace
open scoped Manifold ContDiff

namespace TauCeti

variable {E H : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] (I : ModelWithCorners ℝ E H) (M : Type) [TopologicalSpace M]
  [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]

variable {M} in
/-- The de Rham homomorphism is bijective in every degree on a nonempty convex chart domain
`U = (chartAt H x).source ∩ (extChartAt I x)⁻¹' C`, for a convex set `C` with
`C ∩ range I ⊆ (extChartAt I x).target`: the extended chart maps `U` onto the convex set
`C ∩ range I`. -/
private theorem bijective_deRhamHom_of_eq_inter_preimage_extChartAt {x : M} {C : Set E}
    {U : Opens M} [SigmaCompactSpace U] (hC : Convex ℝ C)
    (hCt : C ∩ range I ⊆ (extChartAt I x).target)
    (hU : (U : Set M) = (chartAt H x).source ∩ extChartAt I x ⁻¹' C) (hne : (U : Set M).Nonempty)
    (k : ℕ) : Function.Bijective (deRhamHom I U k) := by
  obtain ⟨c, hc⟩ := hne
  have himg : extChartAt I x '' (U : Set M) = C ∩ range I := by
    rw [hU, ← extChartAt_source I, image_inter_preimage, (extChartAt I x).image_source_eq_target]
    exact Subset.antisymm (fun y hy ↦ ⟨hy.2, extChartAt_target_subset_range x hy.1⟩)
      fun y hy ↦ ⟨hCt hy, hy.1⟩
  have hsub : (U : Set M) ⊆ (extChartAt I x).source := by
    rw [hU, extChartAt_source]
    exact inter_subset_left
  refine bijective_deRhamHom_of_starConvex_image_extChartAt I M hsub ⟨c, hc⟩ ?_ k
  rw [himg]
  exact (hC.inter I.convex_range).starConvex (himg ▸ mem_image_of_mem _ hc)

variable [SigmaCompactSpace M]

/-- **The Mayer–Vietoris step of the de Rham theorem for open subsets**: if the de Rham
homomorphism is bijective in every degree on open subsets `U`, `V` and `U ⊓ V` of `M`, it is
bijective in every degree on `U ⊔ V`. -/
private theorem bijective_deRhamHom_sup {U V : Opens M} [SigmaCompactSpace (U ⊔ V : Opens M)]
    (hU : ∀ [SigmaCompactSpace U] k, Function.Bijective (deRhamHom I U k))
    (hV : ∀ [SigmaCompactSpace V] k, Function.Bijective (deRhamHom I V k))
    (hUV : ∀ [SigmaCompactSpace (U ⊓ V : Opens M)] k,
      Function.Bijective (deRhamHom I (U ⊓ V : Opens M) k)) (k : ℕ) :
    Function.Bijective (deRhamHom I (U ⊔ V : Opens M) k) := by
  -- The open subsets of the manifold `U ⊔ V` lying over `U` and `V` cover it.
  let f : C((U ⊔ V : Opens M), M) := ⟨Subtype.val, continuous_subtypeVal⟩
  have hcov : Opens.comap f U ⊔ Opens.comap f V = ⊤ := by
    rw [← map_sup]
    exact eq_top_iff.2 fun x _ ↦ x.property
  have := Manifold.sigmaCompactSpace_opens I U
  have := Manifold.sigmaCompactSpace_opens I V
  have := Manifold.sigmaCompactSpace_opens I (U ⊓ V)
  have := Manifold.sigmaCompactSpace_opens I (Opens.comap f U)
  have := Manifold.sigmaCompactSpace_opens I (Opens.comap f V)
  have := Manifold.sigmaCompactSpace_opens I (Opens.comap f U ⊓ Opens.comap f V)
  -- Each of these open subsets, and their intersection, is diffeomorphic to the corresponding
  -- open subset of `M`.
  have hnested {A : Opens M} (hA : A ≤ U ⊔ V) [SigmaCompactSpace A]
      [SigmaCompactSpace (Opens.comap f A)] (h : ∀ k, Function.Bijective (deRhamHom I A k))
      (k : ℕ) :
      Function.Bijective (deRhamHom I (Opens.comap f A) k) :=
    ((Diffeomorph.nestedOpen (I := I) (n := ∞) hA).bijective_deRhamHom_iff k).2 (h k)
  have hinf : ∀ [SigmaCompactSpace (Opens.comap f U ⊓ Opens.comap f V : Opens _)] k,
      Function.Bijective (deRhamHom I (Opens.comap f U ⊓ Opens.comap f V : Opens _) k) := by
    rw [← map_inf]
    exact hnested (inf_le_left.trans le_sup_left) fun k ↦ hUV k
  exact bijective_deRhamHom_of_sup_eq_top I _ _ hcov (hnested le_sup_left fun k ↦ hU k)
    (hnested le_sup_right fun k ↦ hV k) (fun k ↦ hinf k) k

/-- **The de Rham theorem**: on a Hausdorff `σ`-compact smooth manifold `M` modelled on a
finite-dimensional real model with corners, the de Rham homomorphism
`H^k_dR(M) → Hᵏ(M; ℝ)`, integration of closed forms over smooth singular simplices, is bijective
in every degree. Boundary and corners are allowed. -/
theorem bijective_deRhamHom (k : ℕ) : Function.Bijective (deRhamHom I M k) := by
  have := I.locallyCompactSpace
  have := I.secondCountableTopology
  have : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace H M
  have := ChartedSpace.secondCountable_of_sigmaCompact H M
  -- Mayer–Vietoris induction over the open subsets of `M`.
  have key : ∀ U : Opens M, ∀ [SigmaCompactSpace U] k, Function.Bijective (deRhamHom I U k) := by
    refine mayerVietoris_induction_extChartAt I _ ?_ ?_ ?_ ?_
    · intro _ k
      have : IsEmpty (⊥ : Opens M) := ⟨fun x ↦ x.property⟩
      exact bijective_deRhamHom_of_isEmpty I _ k
    · intro x C U _ hC hCt hU hne _ k
      exact bijective_deRhamHom_of_eq_inter_preimage_extChartAt I hC hCt hU hne k
    · intro U V hU hV hUV _ k
      exact bijective_deRhamHom_sup I M hU hV hUV k
    · intro s hs h _ k
      have := fun n ↦ Manifold.sigmaCompactSpace_opens I (s n)
      exact bijective_deRhamHom_iSup I M (fun i j hij ↦ hs i j hij) k fun n ↦ h n k
  have := Manifold.sigmaCompactSpace_opens I (⊤ : Opens M)
  exact ((Diffeomorph.ofTop (I := I) (n := ∞) ⊤ rfl).bijective_deRhamHom_iff k).1 (key ⊤ k)

/-- **The de Rham isomorphism** `H^k_dR(M) ≃ₗ[ℝ] Hᵏ(M; ℝ)` of a Hausdorff `σ`-compact smooth
manifold modelled on a finite-dimensional real model with corners: the de Rham homomorphism
`TauCeti.deRhamHom`, which is bijective by the de Rham theorem `TauCeti.bijective_deRhamHom`. -/
def deRhamEquiv (k : ℕ) :
    deRhamCohomology I M k ≃ₗ[ℝ]
      (TopCat.of M).singularCohomology (ModuleCat.of ℝ ℝ) ℝ (ModuleCat.of ℝ ℝ) k :=
  LinearEquiv.ofBijective (deRhamHom I M k) (bijective_deRhamHom I M k)

/-- The de Rham isomorphism is the de Rham homomorphism. -/
@[simp]
theorem deRhamEquiv_apply (k : ℕ) (c : deRhamCohomology I M k) :
    deRhamEquiv I M k c = deRhamHom I M k c :=
  (rfl)

/-- The de Rham isomorphism, as a linear map, is the de Rham homomorphism. -/
@[simp]
theorem coe_deRhamEquiv (k : ℕ) :
    (deRhamEquiv I M k : deRhamCohomology I M k →ₗ[ℝ] _) = deRhamHom I M k :=
  (rfl)

end TauCeti
