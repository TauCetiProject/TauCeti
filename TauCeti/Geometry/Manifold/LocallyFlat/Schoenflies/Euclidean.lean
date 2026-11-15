/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.LocallyFlat.Schoenflies.Sphere
public import TauCeti.Topology.Compactification.OnePoint.FilledHull
import TauCeti.Analysis.InnerProductSpace.Sphere.Stereographic
import TauCeti.Analysis.Normed.Module.Ball.Homeomorph
import TauCeti.Topology.Compactification.OnePoint.Map
import TauCeti.Topology.ConnectedComponents

/-!
# The generalized Schoenflies theorem in Euclidean and normed spaces

Every locally flat codimension-one embedding `f : S(E) → E` of the unit sphere of a real normed
space `E` into `E` (`dim E = dim G + 1` for a finite-dimensional tangential model `G`) straightens
under an ambient self-homeomorphism `Φ : E ≃ₜ E` such that `Φ (f x) = x` on `S(E)` and
`Φ '' filledHull (range f) = closedBall (0 : E) 1`
(`TauCeti.IsLocallyFlat.exists_homeomorph_apply_eq_coe_and_image_filledHull`).

Here `TauCeti.filledHull (range f)` is the union of `range f` with the bounded connected components
of `(range f)ᶜ`. Under inverse stereographic compactification `OnePoint E ≃ₜ S(F)`
(`onePointHyperplaneHomeoUnitSphere`) sending `∞` to a pole `p`, `filledHull (range f)` corresponds
via `TauCeti.mem_filledHull_iff_coe_notMem_connectedComponentIn_infty` to the complementary disc on
`S(F)` opposite `p`, while self-homeomorphisms of `S(F)` fixing `p` correspond via
`Homeomorph.ofOnePoint` to ambient self-homeomorphisms of `E`.

## Main results

* `TauCeti.IsLocallyFlat.exists_homeomorph_apply_eq_coe_and_image_filledHull`: **ambient Euclidean
  Schoenflies theorem**: there is `Φ : E ≃ₜ E` with `Φ (f x) = x` on `S(E)` carrying
  `filledHull (range f)` onto `closedBall (0 : E) 1`, `filledHull (range f) \ range f` onto
  `ball (0 : E) 1`, and `range f` onto `sphere (0 : E) 1`.
* `TauCeti.IsLocallyFlat.exists_homeomorph_filledHull`: `filledHull (range f) ≃ₜ closedBall 0 1`
  inverting `f` on `range f`.
* `TauCeti.IsLocallyFlat.exists_isClosedEmbedding_closedBall`: `filledHull (range f)` is the range
  of a closed embedding `closedBall (0 : E) 1 → E` extending `f`.
* `TauCeti.IsLocallyFlat.interior_filledHull`, `TauCeti.IsLocallyFlat.frontier_filledHull`,
  `TauCeti.IsLocallyFlat.closure_filledHull_sdiff`: topological interior, frontier, and closure
  identities for `filledHull (range f)`.

## References

* M. Brown, *A proof of the generalized Schoenflies theorem*, Bull. Amer. Math. Soc. 66 (1960),
  74–76.
* M. Brown, *Locally flat imbeddings of topological manifolds*, Annals of Mathematics 75 (1962),
  331–341.
-/

public section

namespace TauCeti.IsLocallyFlat

open Function Metric Module OnePoint Set Topology
open scoped RealInnerProductSpace

/-- Scaled inverse stereographic projection from `OnePoint E` onto the unit sphere of an inner
product space `F` of dimension `dim E + 1` around a pole `p`, sending `∞` to `p`, `S(E)` to the
equator, and `closedBall (0 : E) 1` to the closed southern hemisphere `{y | ⟪y, p⟫ ≤ 0}`. -/
private theorem exists_onePoint_homeomorph_sphere {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (hEF : finrank ℝ F = finrank ℝ E + 1) (p : sphere (0 : F) 1) :
    ∃ (e : sphere (0 : E) 1 ≃ₜ sphere (0 : (ℝ ∙ (p : F))ᗮ) 1)
      (K : OnePoint E ≃ₜ sphere (0 : F) 1),
      K ∞ = p ∧
      (∀ x : sphere (0 : E) 1, K (x : E) = equatorInclusion (p : F) (e x)) ∧
      (∀ z : E, ⟪(K (z : OnePoint E) : F), (p : F)⟫ ≤ 0 ↔ z ∈ closedBall (0 : E) 1) := by
  have : FiniteDimensional ℝ F := .of_finrank_pos (by omega)
  have : Fact (finrank ℝ F = finrank ℝ E + 1) := ⟨hEF⟩
  have hp1 : ‖(p : F)‖ = 1 := norm_eq_of_mem_sphere p
  have hfin : finrank ℝ E = finrank ℝ (ℝ ∙ (p : F))ᗮ :=
    (Submodule.finrank_orthogonal_span_singleton (ne_zero_of_mem_unit_sphere p)).symm
  let L : E ≃L[ℝ] (ℝ ∙ (p : F))ᗮ := ContinuousLinearEquiv.ofFinrankEq hfin
  let uH := L.unitBallHomeomorph
  let e : sphere (0 : E) 1 ≃ₜ sphere (0 : (ℝ ∙ (p : F))ᗮ) 1 :=
    uH.subtype fun x ↦ by
      simp only [mem_sphere_zero_iff_norm, uH]
      exact L.norm_unitBallHomeomorph_eq_one_iff.symm
  let D : E ≃ₜ (ℝ ∙ (p : F))ᗮ := uH.trans (Homeomorph.smulOfNeZero (2 : ℝ) two_ne_zero)
  let K : OnePoint E ≃ₜ sphere (0 : F) 1 :=
    D.onePointCongr.trans (onePointHyperplaneHomeoUnitSphere hp1)
  have hDz (z : E) : ‖D z‖ = 2 * ‖uH z‖ := by
    simp [D, norm_smul]
  have hinner (z : E) :
      ⟪(K (z : OnePoint E) : F), (p : F)⟫ = (‖D z‖ ^ 2 - 4) / (‖D z‖ ^ 2 + 4) := by
    have hDp : ⟪(D z : F), (p : F)⟫ = 0 :=
      Submodule.mem_orthogonal_singleton_iff_inner_left.1 (D z).2
    simp only [K, Homeomorph.trans_apply, Homeomorph.onePointCongr_apply, map_some]
    rw [coe_onePointHyperplaneHomeoUnitSphere_coe]
    simp [inner_add_left, real_inner_smul_left, hDp, hp1]
    field_simp
  refine ⟨e, K, Subtype.ext (by simp [K]), fun x ↦ Subtype.ext ?_, fun z ↦ ?_⟩
  · have hx1 : ‖uH x‖ = 1 :=
      L.norm_unitBallHomeomorph_eq_one_iff.2 (norm_eq_of_mem_sphere x)
    have hDx : ‖D x‖ = 2 := by rw [hDz, hx1, mul_one]
    simp only [K, Homeomorph.trans_apply, Homeomorph.onePointCongr_apply, map_some]
    rw [coe_onePointHyperplaneHomeoUnitSphere_coe, hDx, coe_equatorInclusion_apply]
    have hDeq : (D x : F) = (2 : ℝ) • ((e x : (ℝ ∙ (p : F))ᗮ) : F) := rfl
    rw [hDeq]
    norm_num
    rw [smul_smul, smul_smul]
    norm_num
  · have hpos : 0 < ‖D z‖ ^ 2 + 4 := by positivity
    rw [hinner, div_le_iff₀ hpos, zero_mul, sub_nonpos, hDz, mem_closedBall_zero_iff,
      ← L.norm_unitBallHomeomorph_le_one_iff]
    constructor <;> intro h <;> nlinarith [norm_nonneg (uH z)]

private theorem mem_filledHull_iff_mem_closure_sphere {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace F]
    {s : Set E} (hs : IsClosed s) (K : OnePoint E ≃ₜ F) {p v : F} (hKinf : K ∞ = p)
    (hcard : Nat.card (ConnectedComponents ↥(K '' ((↑) '' s))ᶜ) = 2)
    (hp : p ∉ K '' ((↑) '' s)) (hv : v ∉ K '' ((↑) '' s))
    (hpv : connectedComponentIn (K '' ((↑) '' s))ᶜ p ≠ connectedComponentIn (K '' ((↑) '' s))ᶜ v)
    (hcl : closure (connectedComponentIn (K '' ((↑) '' s))ᶜ v) =
      connectedComponentIn (K '' ((↑) '' s))ᶜ v ∪ K '' ((↑) '' s))
    (z : E) :
    z ∈ filledHull s ↔
      K (z : OnePoint E) ∈ closure (connectedComponentIn (K '' ((↑) '' s))ᶜ v) := by
  have himgK : K '' (((↑) : E → OnePoint E) '' s)ᶜ = (K '' ((↑) '' s))ᶜ := by
    ext w
    obtain ⟨u, rfl⟩ := K.surjective w
    simp [K.injective.mem_set_image]
  rw [mem_filledHull_iff_coe_notMem_connectedComponentIn_infty hs,
    closure_connectedComponentIn_compl_eq_compl hcard hp hv hpv hcl, mem_compl_iff,
    ← himgK, ← hKinf,
    ← K.image_connectedComponentIn (OnePoint.infty_notMem_image_coe (s := s)),
    K.injective.mem_set_image]

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  {f : sphere (0 : E) 1 → E}

/-- **Ambient Euclidean Schoenflies theorem.** Let `f : S(E) → E` be a locally flat codimension-one
embedding of the unit sphere of a real normed space `E` into `E` (`dim E = dim G + 1` for a
finite-dimensional tangential model `G`). Then there is an ambient homeomorphism `Φ : E ≃ₜ E`
satisfying `Φ (f x) = x` on `S(E)` and carrying `filledHull (range f)` onto `closedBall (0 : E) 1`,
`filledHull (range f) \ range f` onto `ball (0 : E) 1`, and `range f` onto `sphere (0 : E) 1`. -/
theorem exists_homeomorph_apply_eq_coe_and_image_filledHull
    (hf : IsLocallyFlat G ℝ f) (hEG : finrank ℝ E = finrank ℝ G + 1) :
    ∃ Φ : E ≃ₜ E,
      (∀ x : sphere (0 : E) 1, Φ (f x) = x) ∧
      Φ '' filledHull (range f) = closedBall (0 : E) 1 ∧
      Φ '' (filledHull (range f) \ range f) = ball (0 : E) 1 ∧
      Φ '' range f = sphere (0 : E) 1 := by
  have : FiniteDimensional ℝ E := .of_finrank_pos (by omega)
  let F := EuclideanSpace ℝ (Fin (finrank ℝ E + 1))
  have hEF : finrank ℝ F = finrank ℝ E + 1 := by simp [F]
  have : Nontrivial F := Module.nontrivial_of_finrank_pos (R := ℝ) (by omega)
  obtain ⟨p⟩ : Nonempty (sphere (0 : F) 1) :=
    (NormedSpace.sphere_nonempty.2 zero_le_one).to_subtype
  obtain ⟨e, K, hKinf, hKeq, hKball⟩ := exists_onePoint_homeomorph_sphere hEF p
  let σ : sphere (0 : E) 1 → sphere (0 : F) 1 := (K ∘ ((↑) : E → OnePoint E)) ∘ f
  have hσ : IsLocallyFlat G ℝ σ :=
    hf.isOpenEmbedding_comp (K.isOpenEmbedding.comp OnePoint.isOpenEmbedding_coe)
  have hpσ : p ∉ range σ := fun ⟨x, hx⟩ ↦
    OnePoint.infty_ne_coe (f x) (K.injective (hKinf.trans hx.symm))
  have hcard := natCard_connectedComponents_sphere_compl_range_eq_two hEF hσ.continuous hσ.injective
  obtain ⟨c, hcne, -⟩ :=
    (Nat.card_eq_two_iff' ((⟨p, hpσ⟩ : ↥(range σ)ᶜ) : ConnectedComponents ↥(range σ)ᶜ)).1 hcard
  obtain ⟨⟨v, hvσ⟩, rfl⟩ := Quotient.exists_rep c
  have hpv : connectedComponentIn (range σ)ᶜ p ≠ connectedComponentIn (range σ)ᶜ v := fun heq ↦
    hcne ((ConnectedComponents.coe_eq_coe_iff_connectedComponentIn_eq hvσ hpσ).2 heq.symm)
  obtain ⟨h, hhp, hhσ, -, hhneg⟩ :=
    hσ.exists_homeomorph_eq_equatorInclusion_of_connectedComponentIn_ne hEG hEF p e hpσ hvσ hpv
  let Ψ : OnePoint E ≃ₜ OnePoint E := K.trans (h.trans K.symm)
  have hΨ : Ψ ∞ = ∞ := by simp [Ψ, hKinf, hhp, K.symm_apply_eq.2 hKinf.symm]
  let Φ : E ≃ₜ E := Ψ.ofOnePoint hΨ
  have hΦf (x : sphere (0 : E) 1) : Φ (f x) = x := by
    have hσx : K (f x : OnePoint E) = σ x := rfl
    apply OnePoint.coe_injective
    rw [Ψ.coe_ofOnePoint_apply hΨ]
    simp only [Ψ, Homeomorph.trans_apply]
    rw [hσx, hhσ x, ← hKeq x, K.symm_apply_apply]
  have hrng : Φ '' range f = sphere (0 : E) 1 := by
    rw [← range_comp]
    convert Subtype.range_coe_subtype using 1
    ext z
    simp [hΦf]
  have hrngσ : K '' (((↑) : E → OnePoint E) '' range f) = range σ := by
    simp [σ, range_comp, image_image]
  have hfill : Φ '' filledHull (range f) = closedBall (0 : E) 1 := by
    ext w
    obtain ⟨z, rfl⟩ := Φ.surjective w
    have hKΦ : K (Φ z : OnePoint E) = h (K (z : OnePoint E)) := by
      rw [Ψ.coe_ofOnePoint_apply hΨ]
      simp [Ψ]
    rw [Φ.injective.mem_set_image,
      mem_filledHull_iff_mem_closure_sphere (isCompact_range hf.continuous).isClosed K hKinf
        (hrngσ.symm ▸ hcard) (hrngσ.symm ▸ hpσ) (hrngσ.symm ▸ hvσ) (hrngσ.symm ▸ hpv)
        (hrngσ.symm ▸ hσ.closure_connectedComponentIn_compl_range hEG hEF hvσ),
      hrngσ, ← hhneg, ← hKΦ, hKball]
  exact ⟨Φ, hΦf, hfill, by rw [image_sdiff Φ.injective, hfill, hrng, closedBall_sdiff_sphere], hrng⟩

/-- **The Euclidean Schoenflies disc theorem.** For a locally flat codimension-one sphere
`f : S(E) → E`, `filledHull (range f)` is homeomorphic to `closedBall (0 : E) 1` by a homeomorphism
inverting `f` on `range f` and sending `range f` onto `sphere (0 : E) 1`. -/
theorem exists_homeomorph_filledHull
    (hf : IsLocallyFlat G ℝ f) (hEG : finrank ℝ E = finrank ℝ G + 1) :
    ∃ h : filledHull (range f) ≃ₜ closedBall (0 : E) 1,
      (∀ (z : filledHull (range f)) x, (z : E) = f x → (h z : E) = x) ∧
      ∀ z, (h z : E) ∈ sphere (0 : E) 1 ↔ (z : E) ∈ range f := by
  obtain ⟨Φ, hΦf, hfill, -, hrng⟩ := hf.exists_homeomorph_apply_eq_coe_and_image_filledHull hEG
  let h : filledHull (range f) ≃ₜ closedBall (0 : E) 1 :=
    Φ.subtype fun z ↦ by rw [← hfill, Φ.injective.mem_set_image]
  refine ⟨h, fun z x hzx ↦ ?_, fun z ↦ ?_⟩
  · rw [Homeomorph.subtype_apply_coe, hzx, hΦf x]
  · exact (Set.ext_iff.1 hrng.symm (Φ z)).trans Φ.injective.mem_set_image

/-- For a locally flat codimension-one sphere `f : S(E) → E`, `filledHull (range f)` is the range of
a closed embedding `g : closedBall (0 : E) 1 → E` extending `f`. -/
theorem exists_isClosedEmbedding_closedBall
    (hf : IsLocallyFlat G ℝ f) (hEG : finrank ℝ E = finrank ℝ G + 1) :
    ∃ g : closedBall (0 : E) 1 → E, IsClosedEmbedding g ∧
      range g = filledHull (range f) ∧
      ∀ x : sphere (0 : E) 1, g ⟨x, sphere_subset_closedBall x.2⟩ = f x := by
  obtain ⟨Φ, hΦf, hfill, -, -⟩ := hf.exists_homeomorph_apply_eq_coe_and_image_filledHull hEG
  refine ⟨Φ.symm ∘ Subtype.val,
    Φ.symm.isClosedEmbedding.comp isClosed_closedBall.isClosedEmbedding_subtypeVal, ?_, fun x ↦ ?_⟩
  · rw [range_comp, Subtype.range_coe_subtype, ofPred_mem_eq, ← hfill, ← image_comp]
    simp
  · exact Φ.symm_apply_eq.2 (hΦf x).symm

/-- The interior of `filledHull (range f)` is `filledHull (range f) \ range f`. -/
theorem interior_filledHull (hf : IsLocallyFlat G ℝ f) (hEG : finrank ℝ E = finrank ℝ G + 1) :
    interior (filledHull (range f)) = filledHull (range f) \ range f := by
  obtain ⟨Φ, -, hfill, hball, -⟩ := hf.exists_homeomorph_apply_eq_coe_and_image_filledHull hEG
  apply Φ.injective.image_injective
  rw [Φ.image_interior (filledHull (range f)), hfill, interior_closedBall _ one_ne_zero, hball]

/-- The frontier of `filledHull (range f)` is `range f`. -/
theorem frontier_filledHull (hf : IsLocallyFlat G ℝ f) (hEG : finrank ℝ E = finrank ℝ G + 1) :
    frontier (filledHull (range f)) = range f := by
  obtain ⟨Φ, -, hfill, -, hrng⟩ := hf.exists_homeomorph_apply_eq_coe_and_image_filledHull hEG
  apply Φ.injective.image_injective
  rw [Φ.image_frontier (filledHull (range f)), hfill, frontier_closedBall _ one_ne_zero, hrng]

/-- `filledHull (range f)` is the closure of its open interior `filledHull (range f) \ range f`. -/
theorem closure_filledHull_sdiff (hf : IsLocallyFlat G ℝ f) (hEG : finrank ℝ E = finrank ℝ G + 1) :
    closure (filledHull (range f) \ range f) = filledHull (range f) := by
  obtain ⟨Φ, -, hfill, hball, -⟩ := hf.exists_homeomorph_apply_eq_coe_and_image_filledHull hEG
  apply Φ.injective.image_injective
  rw [Φ.image_closure (filledHull (range f) \ range f), hball, closure_ball _ one_ne_zero, hfill]

end TauCeti.IsLocallyFlat
