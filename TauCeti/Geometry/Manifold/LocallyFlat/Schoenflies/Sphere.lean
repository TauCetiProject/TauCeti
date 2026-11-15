/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.LocallyFlat.Brown
public import TauCeti.Topology.Schoenflies.Standard
import TauCeti.Analysis.Normed.Module.Ball.Homeomorph

/-!
# The generalized Schoenflies theorem for locally flat spheres in spheres

By M. Brown's bicollaring theorem (`TauCeti.brownBicollaring`) and generalized Schoenflies theorem
(`TauCeti.IsBicollar.exists_homeomorph_closure_connectedComponentIn_compl_range`), every locally
flat codimension-one embedding `σ : S(E) → S(F)` between unit spheres of finite-dimensional real
normed spaces (`dim E = dim G + 1`, `dim F = dim E + 1`) admits a global bicollar and cuts `S(F)`
into two complementary domains whose closures are closed balls bounded by `range σ`.

Because both local flatness (`TauCeti.IsLocallyFlat`) and bicollars (`TauCeti.IsBicollar`)
transport across radial homeomorphisms of unit spheres (`TauCeti.sphereHomeomorphOfFinrankEq`) and
linear equivalences of tangential models, the bicollaring and disc theorems hold for arbitrary real
normed spaces `E`, `F`, `G` in any universes without requiring inner product structures on `E` or
`F`. When `F` is a real inner product space, simultaneous straightening to the equator around any
chosen pole `p` holds as well
(`TauCeti.IsLocallyFlat.exists_homeomorph_eq_equatorInclusion_of_connectedComponentIn_ne`).

## Main results

* `TauCeti.IsLocallyFlat.isBicollared_sphere`: every locally flat codimension-one sphere `S(E)` in
  `S(F)` is globally bicollared.
* `TauCeti.IsLocallyFlat.closure_connectedComponentIn_compl_range`,
  `TauCeti.IsLocallyFlat.frontier_connectedComponentIn_compl_range`: the closure and frontier of
  each complementary domain of `range σ`.
* `TauCeti.IsLocallyFlat.exists_homeomorph_closure_connectedComponentIn_compl_range`: **the
  generalized Schoenflies theorem on spheres**: the closure of each complementary domain of a
  locally flat codimension-one sphere is homeomorphic to the closed unit ball of `E`, inverting
  `σ` on `range σ` and sending `range σ` onto `S(E)`.
* `TauCeti.IsLocallyFlat.exists_isClosedEmbedding_closedBall_sphere`: each complementary closure is
  the range of a closed embedding `closedBall (0 : E) 1 → S(F)` extending `σ`.
* `TauCeti.IsLocallyFlat.exists_homeomorph_eq_equatorInclusion_of_connectedComponentIn_ne`:
  simultaneous ambient straightening of `σ` and both complementary closures to the equator and
  standard hemispheres of an inner product space `F`.

## References

* M. Brown, *A proof of the generalized Schoenflies theorem*, Bull. Amer. Math. Soc. 66 (1960),
  74–76.
* M. Brown, *Locally flat imbeddings of topological manifolds*, Annals of Mathematics 75 (1962),
  331–341.
* R. J. Daverman and G. A. Venema, *Embeddings in Manifolds*, AMS Graduate Studies in Mathematics
  106 (2009), Chapter 2.
-/

public section

namespace TauCeti.IsLocallyFlat

open Function Metric Module Set Topology
open scoped RealInnerProductSpace

section Normed

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  {σ : sphere (0 : E) 1 → sphere (0 : F) 1}

/-- **Brown's bicollaring theorem for arbitrary normed spheres.** Every locally flat embedding
`σ : S(E) → S(F)` with tangential model `G` of finite dimension `dim G`, where
`dim E = dim G + 1` and `dim F = dim E + 1`, admits a global bicollar. -/
theorem isBicollared_sphere (hf : IsLocallyFlat G ℝ σ)
    (hEG : finrank ℝ E = finrank ℝ G + 1) (hEF : finrank ℝ F = finrank ℝ E + 1) :
    IsBicollared σ := by
  set n := finrank ℝ G
  have : FiniteDimensional ℝ E := .of_finrank_pos (by omega)
  have : FiniteDimensional ℝ F := .of_finrank_pos (by omega)
  let eG : G ≃ₜ EuclideanSpace ℝ (Fin n) :=
    (ContinuousLinearEquiv.ofFinrankEq (𝕜 := ℝ) (by simp [n])).toHomeomorph
  let eE : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 ≃ₜ sphere (0 : E) 1 :=
    sphereHomeomorphOfFinrankEq (by simp [hEG, n])
  let eF : sphere (0 : F) 1 ≃ₜ sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1 :=
    sphereHomeomorphOfFinrankEq (by simp [hEF, hEG, n])
  have hf₀ : IsLocallyFlat (EuclideanSpace ℝ (Fin n)) ℝ (eF ∘ σ ∘ eE) :=
    ((hf.transIsOpenEmbedding eG.isOpenEmbedding).comp_homeomorph eE).homeomorph_comp eF
  have hb₀ : IsBicollared (eF ∘ σ ∘ eE) := brownBicollaring_iff.1 (brownBicollaring n) _ hf₀
  have hcomp : eF.symm ∘ (eF ∘ σ ∘ eE) ∘ eE.symm = σ := by
    ext x
    simp
  exact hcomp ▸ (hb₀.comp_homeomorph eE.symm).isOpenEmbedding_comp eF.symm.isOpenEmbedding

/-- The closure of each complementary domain of a locally flat codimension-one sphere `σ` in `S(F)`
is that domain together with `range σ`. -/
theorem closure_connectedComponentIn_compl_range (hf : IsLocallyFlat G ℝ σ)
    (hEG : finrank ℝ E = finrank ℝ G + 1) (hEF : finrank ℝ F = finrank ℝ E + 1)
    {y : sphere (0 : F) 1} (hy : y ∉ range σ) :
    closure (connectedComponentIn (range σ)ᶜ y) = connectedComponentIn (range σ)ᶜ y ∪ range σ := by
  obtain ⟨b, hb⟩ := isBicollared_iff.1 (hf.isBicollared_sphere hEG hEF)
  exact hb.closure_connectedComponentIn_compl_range hEF hy

/-- The frontier of each complementary domain of a locally flat codimension-one sphere `σ` in
`S(F)` is `range σ`. -/
theorem frontier_connectedComponentIn_compl_range (hf : IsLocallyFlat G ℝ σ)
    (hEG : finrank ℝ E = finrank ℝ G + 1) (hEF : finrank ℝ F = finrank ℝ E + 1)
    {y : sphere (0 : F) 1} (hy : y ∉ range σ) :
    frontier (connectedComponentIn (range σ)ᶜ y) = range σ := by
  obtain ⟨b, hb⟩ := isBicollared_iff.1 (hf.isBicollared_sphere hEG hEF)
  exact hb.frontier_connectedComponentIn_compl_range hEF hy

/-- **The generalized Schoenflies theorem on spheres.** Let `σ : S(E) → S(F)` be a locally flat
embedding with finite-dimensional tangential model `G` (`dim E = dim G + 1`, `dim F = dim E + 1`).
For every point `y ∉ range σ`, the closure of the connected component of `y` in `(range σ)ᶜ` is
homeomorphic to `closedBall (0 : E) 1` by a homeomorphism inverting `σ` on `range σ` and mapping
`range σ` onto `sphere (0 : E) 1`. -/
theorem exists_homeomorph_closure_connectedComponentIn_compl_range (hf : IsLocallyFlat G ℝ σ)
    (hEG : finrank ℝ E = finrank ℝ G + 1) (hEF : finrank ℝ F = finrank ℝ E + 1)
    {y : sphere (0 : F) 1} (hy : y ∉ range σ) :
    ∃ h : closure (connectedComponentIn (range σ)ᶜ y) ≃ₜ closedBall (0 : E) 1,
      (∀ (z : closure (connectedComponentIn (range σ)ᶜ y)) x,
        (z : sphere (0 : F) 1) = σ x → (h z : E) = x) ∧
      ∀ z, (h z : E) ∈ sphere (0 : E) 1 ↔ (z : sphere (0 : F) 1) ∈ range σ := by
  obtain ⟨b, hb⟩ := isBicollared_iff.1 (hf.isBicollared_sphere hEG hEF)
  exact hb.exists_homeomorph_closure_connectedComponentIn_compl_range hEF hy

/-- Every complementary closure of a locally flat codimension-one sphere `σ : S(E) → S(F)` is the
range of a closed embedding `g : closedBall (0 : E) 1 → S(F)` extending `σ`. -/
theorem exists_isClosedEmbedding_closedBall_sphere (hf : IsLocallyFlat G ℝ σ)
    (hEG : finrank ℝ E = finrank ℝ G + 1) (hEF : finrank ℝ F = finrank ℝ E + 1)
    {y : sphere (0 : F) 1} (hy : y ∉ range σ) :
    ∃ g : closedBall (0 : E) 1 → sphere (0 : F) 1, IsClosedEmbedding g ∧
      range g = closure (connectedComponentIn (range σ)ᶜ y) ∧
      ∀ x : sphere (0 : E) 1, g ⟨x, sphere_subset_closedBall x.2⟩ = σ x := by
  obtain ⟨h, hh, -⟩ :=
    hf.exists_homeomorph_closure_connectedComponentIn_compl_range hEG hEF hy
  have hcl := hf.closure_connectedComponentIn_compl_range hEG hEF hy
  refine ⟨Subtype.val ∘ h.symm,
    isClosed_closure.isClosedEmbedding_subtypeVal.comp h.symm.isClosedEmbedding, ?_, fun x ↦ ?_⟩
  · rw [range_comp, h.symm.surjective.range_eq, image_univ, Subtype.range_coe_subtype,
      ofPred_mem_eq]
  · have hx : σ x ∈ closure (connectedComponentIn (range σ)ᶜ y) :=
      hcl ▸ Or.inr (mem_range_self x)
    have hhx : h ⟨σ x, hx⟩ = ⟨x, sphere_subset_closedBall x.2⟩ :=
      Subtype.ext (hh ⟨σ x, hx⟩ x rfl)
    exact congrArg Subtype.val (h.symm_apply_eq.2 hhx.symm)

end Normed

section InnerProduct

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  {σ : sphere (0 : E) 1 → sphere (0 : F) 1}

/-- **Simultaneous locally flat Schoenflies theorem on spheres.** Let `σ : S(E) → S(F)` be a locally
flat codimension-one sphere in the unit sphere of a real inner product space `F`, and let `u` and
`v` lie in distinct connected components of `(range σ)ᶜ`. For any pole `p` of `F` and homeomorphism
`e` of unit spheres, there is an ambient self-homeomorphism `h` of `S(F)` with `h u = p`,
`h (σ x) = equatorInclusion (p : F) (e x)`, and carrying the closures of the complementary
components of `u` and `v` onto the closed hemispheres around `p` and `-p`. -/
theorem exists_homeomorph_eq_equatorInclusion_of_connectedComponentIn_ne
    (hf : IsLocallyFlat G ℝ σ) (hEG : finrank ℝ E = finrank ℝ G + 1)
    (hEF : finrank ℝ F = finrank ℝ E + 1) (p : sphere (0 : F) 1)
    (e : sphere (0 : E) 1 ≃ₜ sphere (0 : (ℝ ∙ (p : F))ᗮ) 1)
    {u v : sphere (0 : F) 1} (hu : u ∉ range σ) (hv : v ∉ range σ)
    (huv : connectedComponentIn (range σ)ᶜ u ≠ connectedComponentIn (range σ)ᶜ v) :
    ∃ h : sphere (0 : F) 1 ≃ₜ sphere (0 : F) 1,
      h u = p ∧
      (∀ x, h (σ x) = equatorInclusion (p : F) (e x)) ∧
      (∀ y, 0 ≤ ⟪(h y : F), (p : F)⟫ ↔ y ∈ closure (connectedComponentIn (range σ)ᶜ u)) ∧
      (∀ y, ⟪(h y : F), (p : F)⟫ ≤ 0 ↔ y ∈ closure (connectedComponentIn (range σ)ᶜ v)) := by
  obtain ⟨b, hb⟩ := isBicollared_iff.1 (hf.isBicollared_sphere hEG hEF)
  exact hb.exists_homeomorph_eq_equatorInclusion_of_connectedComponentIn_ne hEF p e hu hv huv

end InnerProduct

end TauCeti.IsLocallyFlat
