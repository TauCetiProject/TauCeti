/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Homotopy.Contractible
public import TauCeti.Geometry.Manifold.Irreducible.Defs
import TauCeti.AlgebraicTopology.Disk
import TauCeti.AlgebraicTopology.Sphere.Contractible
import TauCeti.Analysis.Normed.Module.Ball.Homeomorph

/-!
# Basic API for `IsSphereBoundsBall`

This file develops the basic structural API and homotopy obstructions for
`TauCeti.IsSphereBoundsBall`:

* metric characterizations replacing `TopCat.sphere 2` and `TopCat.disk 3` with the unit sphere and
  closed unit ball of `EuclideanSpace ℝ (Fin 3)`
  (`TauCeti.isSphereBoundsBall_iff_sphere_closedBall`) or of any 3-dimensional real normed space
  (`TauCeti.isSphereBoundsBall_iff_of_finrank_eq_three`), and simplifying the closed-embedding
  requirements in Hausdorff targets (`TauCeti.isSphereBoundsBall_iff_of_t2Space`);
* topological invariance across arbitrary universes (`Homeomorph.isSphereBoundsBall_iff`);
* nullhomotopy of every closed locally flat embedded 2-sphere in an `IsSphereBoundsBall` space
  (`TauCeti.IsSphereBoundsBall.nullhomotopic`), together with the resulting homotopy/retraction
  obstructions (`TauCeti.not_isSphereBoundsBall_of_homotopic_id`,
  `TauCeti.not_isSphereBoundsBall_of_leftInverse`).

## References

* A. Hatcher, *Notes on Basic 3-Manifold Topology*, Chapter 1.
-/

public section

open CategoryTheory Function Metric Module Set Topology

universe u v

namespace TauCeti

/-- `IsSphereBoundsBall M` expressed directly on the metric unit sphere and closed unit ball of
`EuclideanSpace ℝ (Fin 3)`, without `TopCat` or `ULift` wrappers: every closed locally flat
embedding of `S²` into `M` extends to a closed embedding of `D³` into `M`. -/
theorem isSphereBoundsBall_iff_sphere_closedBall (M : Type u) [TopologicalSpace M] :
    IsSphereBoundsBall M ↔
      ∀ f : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 → M, IsClosedEmbedding f →
        IsLocallyFlat (EuclideanSpace ℝ (Fin 2)) ℝ f →
        ∃ g : closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1 → M, IsClosedEmbedding g ∧
          ∀ x : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1,
            g ⟨x, sphere_subset_closedBall x.2⟩ = f x := by
  let eS : (TopCat.diskBoundary 3 : TopCat.{u}) ≃ₜ sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 :=
    Homeomorph.ulift
  let eB : (TopCat.disk 3 : TopCat.{u}) ≃ₜ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1 :=
    Homeomorph.ulift
  have hinc (s : (TopCat.diskBoundary 3 : TopCat.{u})) :
      (TopCat.diskBoundaryInclusion.{u} 3).hom s =
        eB.symm ⟨eS s, sphere_subset_closedBall (eS s).2⟩ :=
    ULift.ext (Subtype.ext (TauCeti.TopCat.coe_diskBoundaryInclusion_apply_down 3 s))
  rw [isSphereBoundsBall_iff]
  constructor
  · intro hM f hf_cl hf_lf
    let f' : C((TopCat.diskBoundary 3 : TopCat.{u}), M) :=
      ⟨f ∘ eS, hf_cl.continuous.comp eS.continuous⟩
    obtain ⟨g', hg'_cl, hg'f⟩ :=
      hM f' (hf_cl.comp eS.isClosedEmbedding) (hf_lf.comp_homeomorph eS)
    refine ⟨g' ∘ eB.symm, hg'_cl.comp eB.symm.isClosedEmbedding, fun x ↦ ?_⟩
    have hx := DFunLike.congr_fun hg'f (eS.symm x)
    simp only [ContinuousMap.comp_apply, hinc, f', ContinuousMap.coe_mk, Function.comp_apply,
      eS.apply_symm_apply] at hx
    exact hx
  · intro hM f' hf'_cl hf'_lf
    let f'' : C((TopCat.diskBoundary 3 : TopCat.{u}), M) := f'
    obtain ⟨g, hg_cl, hgf⟩ := hM (f'' ∘ eS.symm)
      (hf'_cl.comp eS.symm.isClosedEmbedding) (hf'_lf.comp_homeomorph eS.symm)
    refine ⟨⟨g ∘ eB, hg_cl.continuous.comp eB.continuous⟩,
      hg_cl.comp eB.isClosedEmbedding, ?_⟩
    ext s
    simp only [ContinuousMap.comp_apply, ContinuousMap.coe_mk, Function.comp_apply]
    rw [hinc s, eB.apply_symm_apply, hgf (eS s), Function.comp_apply]
    exact congrArg f'' (eS.symm_apply_apply s)

/-- `IsSphereBoundsBall M` expressed using the unit sphere and closed unit ball of any
3-dimensional real normed space `E`. -/
theorem isSphereBoundsBall_iff_of_finrank_eq_three (M : Type u) [TopologicalSpace M]
    {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E] (hE : finrank ℝ E = 3) :
    IsSphereBoundsBall M ↔
      ∀ f : sphere (0 : E) 1 → M, IsClosedEmbedding f →
        IsLocallyFlat (EuclideanSpace ℝ (Fin 2)) ℝ f →
        ∃ g : closedBall (0 : E) 1 → M, IsClosedEmbedding g ∧
          ∀ x : sphere (0 : E) 1, g ⟨x, sphere_subset_closedBall x.2⟩ = f x := by
  have : FiniteDimensional ℝ E := .of_finrank_pos (by omega)
  let eS : sphere (0 : E) 1 ≃ₜ sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 :=
    sphereHomeomorphOfFinrankEq (by simp [hE])
  let eB : closedBall (0 : E) 1 ≃ₜ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1 :=
    closedBallHomeomorphOfFinrankEq (by simp [hE])
  have heBS (x : sphere (0 : E) 1) :
      eB ⟨x, sphere_subset_closedBall x.2⟩ = ⟨eS x, sphere_subset_closedBall (eS x).2⟩ :=
    Subtype.ext (by simp [eB, eS])
  have heBS' (y : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
      eB.symm ⟨y, sphere_subset_closedBall y.2⟩ =
        ⟨eS.symm y, sphere_subset_closedBall (eS.symm y).2⟩ := by
    apply eB.injective
    rw [eB.apply_symm_apply, heBS, eS.apply_symm_apply]
  rw [isSphereBoundsBall_iff_sphere_closedBall]
  constructor
  · intro hM f hf_cl hf_lf
    obtain ⟨g, hg_cl, hgf⟩ := hM (f ∘ eS.symm)
      (hf_cl.comp eS.symm.isClosedEmbedding) (hf_lf.comp_homeomorph eS.symm)
    refine ⟨g ∘ eB, hg_cl.comp eB.isClosedEmbedding, fun x ↦ ?_⟩
    simp only [Function.comp_apply, heBS, hgf, eS.symm_apply_apply]
  · intro hM f hf_cl hf_lf
    obtain ⟨g, hg_cl, hgf⟩ := hM (f ∘ eS)
      (hf_cl.comp eS.isClosedEmbedding) (hf_lf.comp_homeomorph eS)
    refine ⟨g ∘ eB.symm, hg_cl.comp eB.symm.isClosedEmbedding, fun y ↦ ?_⟩
    simp only [Function.comp_apply, heBS', hgf, eS.apply_symm_apply]

/-- In a Hausdorff space, compactness of the sphere and closed ball makes the closed-embedding
hypotheses in `IsSphereBoundsBall` automatic from local flatness of `f` and injective continuity of
`g`. -/
theorem isSphereBoundsBall_iff_of_t2Space (M : Type u) [TopologicalSpace M] [T2Space M] :
    IsSphereBoundsBall M ↔
      ∀ f : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 → M,
        IsLocallyFlat (EuclideanSpace ℝ (Fin 2)) ℝ f →
        ∃ g : closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1 → M,
          Continuous g ∧ Injective g ∧
          ∀ x : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1,
            g ⟨x, sphere_subset_closedBall x.2⟩ = f x := by
  rw [isSphereBoundsBall_iff_sphere_closedBall]
  constructor
  · intro hM f hf_lf
    obtain ⟨g, hg_cl, hgf⟩ := hM f (hf_lf.continuous.isClosedEmbedding hf_lf.injective) hf_lf
    exact ⟨g, hg_cl.continuous, hg_cl.injective, hgf⟩
  · intro hM f _ hf_lf
    obtain ⟨g, hg_cont, hg_inj, hgf⟩ := hM f hf_lf
    exact ⟨g, hg_cont.isClosedEmbedding hg_inj, hgf⟩

private theorem isSphereBoundsBall_of_homeomorph {M : Type u} {N : Type v}
    [TopologicalSpace M] [TopologicalSpace N] (e : M ≃ₜ N) (hM : IsSphereBoundsBall M) :
    IsSphereBoundsBall N := by
  rw [isSphereBoundsBall_iff_sphere_closedBall] at hM ⊢
  intro f hf_cl hf_lf
  obtain ⟨g, hg_cl, hgf⟩ := hM (e.symm ∘ f)
    (e.symm.isClosedEmbedding.comp hf_cl) (hf_lf.homeomorph_comp e.symm)
  refine ⟨e ∘ g, e.isClosedEmbedding.comp hg_cl, fun x ↦ ?_⟩
  simp only [Function.comp_apply, hgf, e.apply_symm_apply]

/-- `IsSphereBoundsBall` is a topological invariant across arbitrary universes. -/
protected theorem _root_.Homeomorph.isSphereBoundsBall_iff {M : Type u} {N : Type v}
    [TopologicalSpace M] [TopologicalSpace N] (e : M ≃ₜ N) :
    IsSphereBoundsBall M ↔ IsSphereBoundsBall N :=
  ⟨isSphereBoundsBall_of_homeomorph e, isSphereBoundsBall_of_homeomorph e.symm⟩

/-- In an `IsSphereBoundsBall` space, every closed locally flat embedded 2-sphere is
nullhomotopic. -/
theorem IsSphereBoundsBall.nullhomotopic {M : Type u} [TopologicalSpace M]
    (hM : IsSphereBoundsBall M) {f : C((TopCat.sphere 2 : TopCat.{u}), M)}
    (hf_cl : IsClosedEmbedding f) (hf_lf : IsLocallyFlat (EuclideanSpace ℝ (Fin 2)) ℝ f) :
    f.Nullhomotopic := by
  obtain ⟨g, -, hgf⟩ := (isSphereBoundsBall_iff M).1 hM f hf_cl hf_lf
  exact (TopCat.Hom.nullhomotopic_iff_exists_diskBoundaryInclusion_comp_eq (TopCat.ofHom f)).2
    ⟨TopCat.ofHom g, TopCat.Hom.ext hgf⟩

/-- Metric-sphere form of `TauCeti.IsSphereBoundsBall.nullhomotopic` over any 3-dimensional real
normed space. -/
theorem IsSphereBoundsBall.nullhomotopic_of_finrank_eq_three {M : Type u} [TopologicalSpace M]
    {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E] (hM : IsSphereBoundsBall M)
    (hE : finrank ℝ E = 3) {f : C(sphere (0 : E) 1, M)}
    (hf_cl : IsClosedEmbedding f) (hf_lf : IsLocallyFlat (EuclideanSpace ℝ (Fin 2)) ℝ f) :
    f.Nullhomotopic := by
  obtain ⟨g, hg_cl, hgf⟩ := (isSphereBoundsBall_iff_of_finrank_eq_three M hE).1 hM f hf_cl hf_lf
  exact (ContinuousMap.nullhomotopic_iff_exists_extension_closedBall f).2
    ⟨⟨g, hg_cl.continuous⟩, hgf⟩

/-- **Homotopy retraction obstruction to `IsSphereBoundsBall`.** If a closed locally flat embedded
2-sphere `f : S(E) → M` (`dim E = 3`) admits a continuous map `r : M → S(E)` with `r ∘ f`
homotopic to the identity of `S(E)`, then `M` does not satisfy `IsSphereBoundsBall`. -/
theorem not_isSphereBoundsBall_of_homotopic_id {M : Type u} [TopologicalSpace M]
    {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E] (hE : finrank ℝ E = 3)
    {f : C(sphere (0 : E) 1, M)} (hf_cl : IsClosedEmbedding f)
    (hf_lf : IsLocallyFlat (EuclideanSpace ℝ (Fin 2)) ℝ f) {r : C(M, sphere (0 : E) 1)}
    (hrf : (r.comp f).Homotopic (ContinuousMap.id _)) :
    ¬ IsSphereBoundsBall M := by
  intro hM
  have : FiniteDimensional ℝ E := .of_finrank_pos (by omega)
  have : Nontrivial E := Module.nontrivial_of_finrank_pos (R := ℝ) (by omega)
  obtain ⟨c, hc⟩ := (hM.nullhomotopic_of_finrank_eq_three hE hf_cl hf_lf).comp_right r
  have hid : (ContinuousMap.id (sphere (0 : E) 1)).Nullhomotopic := ⟨c, hrf.symm.trans hc⟩
  exact not_contractibleSpace_sphere ((contractible_iff_id_nullhomotopic _).2 hid)

/-- **Retraction obstruction to `IsSphereBoundsBall`.** If a closed locally flat embedded 2-sphere
`f : S(E) → M` (`dim E = 3`) has a continuous left inverse `r : M → S(E)`, then `M` does not
satisfy `IsSphereBoundsBall`. -/
theorem not_isSphereBoundsBall_of_leftInverse {M : Type u} [TopologicalSpace M]
    {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E] (hE : finrank ℝ E = 3)
    {f : sphere (0 : E) 1 → M} (hf_cl : IsClosedEmbedding f)
    (hf_lf : IsLocallyFlat (EuclideanSpace ℝ (Fin 2)) ℝ f) {r : M → sphere (0 : E) 1}
    (hr : Continuous r) (hrf : LeftInverse r f) :
    ¬ IsSphereBoundsBall M := by
  refine not_isSphereBoundsBall_of_homotopic_id hE (f := ⟨f, hf_cl.continuous⟩) hf_cl hf_lf
    (r := ⟨r, hr⟩) ?_
  convert ContinuousMap.Homotopic.refl (ContinuousMap.id (sphere (0 : E) 1)) using 1
  exact ContinuousMap.ext fun x ↦ hrf x

end TauCeti
