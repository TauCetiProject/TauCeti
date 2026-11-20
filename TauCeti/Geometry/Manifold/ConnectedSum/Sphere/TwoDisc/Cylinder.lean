/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import TauCeti.Geometry.Manifold.ConnectedSum.Sphere.TwoDisc.Complement
import TauCeti.Geometry.Diffeomorphism.Diffeotopy.DiscConfiguration
import TauCeti.Geometry.Diffeomorphism.Sphere
import TauCeti.Geometry.Manifold.Orientation.Sphere
import TauCeti.Geometry.Sphere.Connected
import TauCeti.Geometry.Manifold.Orientation.CoordinateBall
import TauCeti.Geometry.Manifold.Diffeomorph.NormedSpace

/-!
# The complement of two supplied smooth discs in the three-sphere

For two smooth embeddings of the open unit three-ball with disjoint images, the complement of
their radius-`1/2` closed discs is diffeomorphic to the native unit two-sphere times `(0,1)`.
The construction retains both original radial collar coordinates, with independently chosen
orthogonal angular frames and one common positive linear speed. No orientation condition on the
supplied embeddings is required.

The simultaneous ambient disc theorem moves a compact neighborhood of the original discs to
small complementary stereographic discs. The standard cylinder coordinates then supply both
collar formulas. Globalizing the original open-ball charts preserves their exact radial
coordinates, because the unit-ball diffeomorphism commutes with orthogonal maps.

The simultaneous normalization of the supplied discs and transport of their original collars
are adapted from
[frenzymath/PoincareConjecture](https://github.com/frenzymath/PoincareConjecture), with
[frenzymath/lean-eval-submissions](https://github.com/frenzymath/lean-eval-submissions) as a
supporting formalization reference.
-/

public section

noncomputable section

open Set Function Filter Metric Topology TopologicalSpace
open scoped Manifold ContDiff

namespace TauCeti

local instance : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 4)) = 3 + 1) := ⟨by simp⟩
local instance : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩

private theorem exists_sphere_disc_normalization
    (f g : Fin 2 → SmoothEmbedding (𝓡 3) (𝓡 3) ∞
      (EuclideanSpace ℝ (Fin 3)) (sphere (0 : EuclideanSpace ℝ (Fin 4)) 1))
    (hfd : Pairwise (Disjoint on fun i ↦ range (f i)))
    (hgd : Pairwise (Disjoint on fun i ↦ range (g i))) (r : ℝ) :
    ∃ R : Fin 2 → EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3),
      ∃ Φ : sphere (0 : EuclideanSpace ℝ (Fin 4)) 1 ≃ₘ^∞⟮𝓡 3, 𝓡 3⟯
        sphere (0 : EuclideanSpace ℝ (Fin 4)) 1,
        ∀ i, EqOn (Φ ∘ f i) (g i ∘ R i) (closedBall 0 r) := by
  have : ConnectedSpace (sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) :=
    TauCeti.connectedSpace_sphere (E := EuclideanSpace ℝ (Fin 4)) 3
  let oE : TauCeti.Manifold.Orientation (𝓡 3) (EuclideanSpace ℝ (Fin 3)) (Fin 3) :=
    TauCeti.Manifold.Orientation.model
      (Module.finBasisOfFinrankEq ℝ (EuclideanSpace ℝ (Fin 3)) (by simp)).orientation (by simp)
  let oM : TauCeti.Manifold.Orientation (𝓡 3) (sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) (Fin 3) :=
    (Module.finBasisOfFinrankEq ℝ (EuclideanSpace ℝ (Fin 4))
      (by simp)).orientation.sphereOrientation
  choose Rf hRf using fun i ↦
    SmoothEmbedding.exists_linearIsometryEquiv_isOrientationPreservingAt_zero (f i) (by simp) oE oM
  choose Rg hRg using fun i ↦
    SmoothEmbedding.exists_linearIsometryEquiv_isOrientationPreservingAt_zero (g i) (by simp) oE oM
  let F i := (f i).compDiffeomorph ((Rf i).toContinuousLinearEquiv.toContDiffDiffeomorph ∞)
  let G i := (g i).compDiffeomorph ((Rg i).toContinuousLinearEquiv.toContDiffDiffeomorph ∞)
  have hF (i) : ⇑(F i) = f i ∘ Rf i := by simp [F]
  have hG (i) : ⇑(G i) = g i ∘ Rg i := by simp [G]
  have hrF (i) : range (F i) = range (f i) := by
    rw [hF, range_comp, (Rf i).surjective.range_eq, image_univ]
  have hrG (i) : range (G i) = range (g i) := by
    rw [hG, range_comp, (Rg i).surjective.range_eq, image_univ]
  obtain ⟨Ψ, -, -, -, -, hΨ⟩ :=
    TauCeti.SmoothEmbedding.exists_diffeotopy_eqOn_of_pairwise_disjoint
      (by rw [← Module.finrank_eq_rank]; norm_num) isOpen_univ isPreconnected_univ F G
      (by simpa only [hrF] using hfd) (by simpa only [hrG] using hgd)
      (fun _ ↦ subset_univ _) (fun _ ↦ subset_univ _)
      oE oM (fun i ↦ by rw [hF]; exact hRf i) (fun i ↦ by rw [hG]; exact hRg i)
      (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin 3)) r)
  refine ⟨fun i ↦ (Rf i).symm.trans (Rg i), Ψ.final, fun i x hx ↦ ?_⟩
  have hx' : (Rf i).symm x ∈ closedBall 0 r := by
    simpa only [mem_closedBall_zero_iff, LinearIsometryEquiv.norm_map] using hx
  have h := hΨ i hx'
  simpa only [hF, hG, comp_apply, LinearIsometryEquiv.apply_symm_apply,
    LinearIsometryEquiv.trans_apply] using h


private theorem exists_original_normalization
    (v : sphere (0 : EuclideanSpace ℝ (Fin 4)) 1)
    (f : Fin 2 → SmoothEmbedding (𝓡 3) (𝓡 3) ∞
      (unitBallOpens (EuclideanSpace ℝ (Fin 3))) (sphere (0 : EuclideanSpace ℝ (Fin 4)) 1))
    (hfd : Pairwise (Disjoint on fun i ↦ range (f i))) :
    ∃ R : Fin 2 → EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3),
      ∃ Φ : sphere (0 : EuclideanSpace ℝ (Fin 4)) 1 ≃ₘ^∞⟮𝓡 3, 𝓡 3⟯
        sphere (0 : EuclideanSpace ℝ (Fin 4)) 1,
        ∀ i (p : unitBallOpens (EuclideanSpace ℝ (Fin 3))),
          ‖(p : EuclideanSpace ℝ (Fin 3))‖ ≤ 3 / 4 →
          Φ (f i p) = sphereStandardDisc v i ⟨R i p, by
            simpa only [mem_unitBallOpens, LinearIsometryEquiv.norm_map] using p.property⟩ := by
  let g := sphereStandardDisc v
  have hgd := sphereStandardDisc_disjoint v
  let D := TauCeti.unitBallDiffeomorph (EuclideanSpace ℝ (Fin 3))
  let f' i := (f i).compDiffeomorph D.symm
  let g' i := (g i).compDiffeomorph D.symm
  have hr (a : Fin 2 → TauCeti.SmoothEmbedding (𝓡 3) (𝓡 3) ∞
      (TauCeti.unitBallOpens (EuclideanSpace ℝ (Fin 3)))
        (sphere (0 : EuclideanSpace ℝ (Fin 4)) 1)) (i) :
      range ((a i).compDiffeomorph D.symm) = range (a i) := by
    rw [SmoothEmbedding.coe_compDiffeomorph]
    have hD : range (D.symm : EuclideanSpace ℝ (Fin 3) →
        TauCeti.unitBallOpens (EuclideanSpace ℝ (Fin 3))) = univ :=
      Set.range_eq_univ.2 fun p ↦ ⟨D p, D.symm_apply_apply p⟩
    rw [range_comp, hD, image_univ]
  obtain ⟨R, Φ, hΦ⟩ :=
    exists_sphere_disc_normalization f' g'
    (by simpa only [f', hr] using hfd) (by simpa only [g', hr] using hgd) 2
  refine ⟨R, Φ, fun i p hp ↦ ?_⟩
  have h := hΦ i (mem_closedBall_zero_iff.2 (norm_unitBallDiffeomorph_le_two p hp))
  simp only [f', g', SmoothEmbedding.coe_compDiffeomorph, comp_apply] at h
  rw [Diffeomorph.symm_apply_apply] at h
  convert h using 1
  apply congrArg (g i)
  apply Subtype.ext
  exact (unitBallDiffeomorph_symm_rotation (R i) p).symm

private theorem image_originalDisc (f g : Fin 2 → (TauCeti.SmoothEmbedding (𝓡 3) (𝓡 3) ∞
  (TauCeti.unitBallOpens (EuclideanSpace ℝ (Fin 3))) (sphere (0 : EuclideanSpace ℝ (Fin 4)) 1)))
  (R : Fin 2 → (EuclideanSpace ℝ (Fin 3)) ≃ₗᵢ[ℝ] (EuclideanSpace ℝ (Fin 3)))
    (Φ : (sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) ≃ₘ^∞⟮𝓡 3, 𝓡 3⟯ (sphere (0 : EuclideanSpace ℝ
      (Fin 4)) 1))
    (hΦ : ∀ i (p : TauCeti.unitBallOpens (EuclideanSpace ℝ (Fin 3))), ‖(p : (EuclideanSpace ℝ (Fin
      3)))‖ ≤ 3 / 4 →
      Φ (f i p) = g i ⟨R i p, by
        simpa only [TauCeti.mem_unitBallOpens, LinearIsometryEquiv.norm_map] using p.property⟩)
    (i : Fin 2) :
    Φ '' range (f i ∘ sphereHalfDiscInclusion) = range (g i ∘ sphereHalfDiscInclusion) := by
  ext x
  constructor
  · rintro ⟨_, ⟨p, rfl⟩, rfl⟩
    have hp : R i (p : (EuclideanSpace ℝ (Fin 3))) ∈ closedBall 0 (1 / 2) := by
      simpa only [mem_closedBall_zero_iff, LinearIsometryEquiv.norm_map] using p.property
    refine ⟨⟨R i p, hp⟩, ?_⟩
    simp only [Function.comp_apply]
    rw [hΦ i (sphereHalfDiscInclusion p)
      (by simpa only [coe_sphereHalfDiscInclusion] using
        (mem_closedBall_zero_iff.1 p.property).trans (by norm_num : (1 / 2 : ℝ) ≤ 3 / 4))]
    apply congrArg (g i)
    apply Subtype.ext
    simp only [coe_sphereHalfDiscInclusion]
  · rintro ⟨p, rfl⟩
    have hp : (R i).symm (p : (EuclideanSpace ℝ (Fin 3))) ∈ closedBall 0 (1 / 2) := by
      simpa only [mem_closedBall_zero_iff, LinearIsometryEquiv.norm_map] using p.property
    let q : closedBall (0 : (EuclideanSpace ℝ (Fin 3))) (1 / 2) := ⟨(R i).symm p, hp⟩
    refine ⟨f i (sphereHalfDiscInclusion q), mem_range_self q, ?_⟩
    rw [hΦ i (sphereHalfDiscInclusion q)
      (by simpa only [coe_sphereHalfDiscInclusion] using
        (mem_closedBall_zero_iff.1 q.property).trans (by norm_num : (1 / 2 : ℝ) ≤ 3 / 4))]
    apply congrArg (g i)
    apply Subtype.ext
    simpa only [coe_sphereHalfDiscInclusion, q] using (R i).apply_symm_apply p

private def normalizationComplement (f g : Fin 2 → (TauCeti.SmoothEmbedding (𝓡 3) (𝓡 3) ∞
  (TauCeti.unitBallOpens (EuclideanSpace ℝ (Fin 3))) (sphere (0 : EuclideanSpace ℝ (Fin 4)) 1)))
  (R : Fin 2 → (EuclideanSpace ℝ (Fin 3)) ≃ₗᵢ[ℝ] (EuclideanSpace ℝ (Fin 3)))
    (Φ : (sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) ≃ₘ^∞⟮𝓡 3, 𝓡 3⟯ (sphere (0 : EuclideanSpace ℝ
      (Fin 4)) 1))
    (hΦ : ∀ i (p : TauCeti.unitBallOpens (EuclideanSpace ℝ (Fin 3))), ‖(p : (EuclideanSpace ℝ (Fin
      3)))‖ ≤ 3 / 4 →
      Φ (f i p) = g i ⟨R i p, by
        simpa only [TauCeti.mem_unitBallOpens, LinearIsometryEquiv.norm_map] using p.property⟩) :
    sphereTwoDiscComplementOpens f ≃ₘ^∞⟮𝓡 3, 𝓡 3⟯ sphereTwoDiscComplementOpens g := by
  refine Φ.subtype fun x ↦ ?_
  have himage : Φ '' (range (f 0 ∘ sphereHalfDiscInclusion) ∪
      range (f 1 ∘ sphereHalfDiscInclusion)) =
      range (g 0 ∘ sphereHalfDiscInclusion) ∪ range (g 1 ∘ sphereHalfDiscInclusion) := by
    rw [image_union, image_originalDisc f g R Φ hΦ 0, image_originalDisc f g R Φ hΦ 1]
  rw [mem_sphereTwoDiscComplementOpens, mem_sphereTwoDiscComplementOpens]
  rw [← not_or, ← not_or, ← mem_union, ← mem_union, ← himage]
  constructor
  · rintro hx ⟨y, hy, he⟩
    exact hx ((Φ.injective he) ▸ hy)
  · intro hx hy
    exact hx ⟨x, hy, rfl⟩

variable (v : (sphere (0 : EuclideanSpace ℝ (Fin 4)) 1)) (f : Fin 2 → (TauCeti.SmoothEmbedding (𝓡
  3) (𝓡 3) ∞ (TauCeti.unitBallOpens (EuclideanSpace ℝ (Fin 3))) (sphere (0 : EuclideanSpace ℝ (Fin
  4)) 1))) (R : Fin 2 → (EuclideanSpace ℝ (Fin 3)) ≃ₗᵢ[ℝ] (EuclideanSpace ℝ (Fin 3)))
  (Φ : (sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) ≃ₘ^∞⟮𝓡 3, 𝓡 3⟯ (sphere (0 : EuclideanSpace ℝ (Fin
    4)) 1))
  (hΦ : ∀ i (p : TauCeti.unitBallOpens (EuclideanSpace ℝ (Fin 3))), ‖(p : (EuclideanSpace ℝ (Fin
    3)))‖ ≤ 3 / 4 →
    Φ (f i p) = sphereStandardDisc v i ⟨R i p, by
      simpa only [TauCeti.mem_unitBallOpens, LinearIsometryEquiv.norm_map] using p.property⟩)

include hΦ in
private theorem normalization_collar (i : Fin 2) (z : (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1))
  (s : Ioo (0 : ℝ) (1 / 8)) :
    Φ (f i (sphereDiscCollarPoint z s)) = sphereStandardDiscCollar v i ((R i).unitSphereEquiv z) s
      := by
  rw [hΦ i (sphereDiscCollarPoint z s)
    (by rw [sphereDiscCollarPoint_norm]; linarith [s.property.2])]
  rw [← sphereStandardDisc_collarPoint v i ((R i).unitSphereEquiv z) s]
  apply congrArg (sphereStandardDisc v i)
  apply Subtype.ext
  simp only [sphereDiscCollarPoint_coe, map_smul,
    LinearIsometryEquiv.coe_unitSphereEquiv_apply]

include hΦ in
private theorem normalization_collar_mem
    (i : Fin 2) (z : (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)) (s : Ioo (0 : ℝ) (1 / 8)) :
    f i (sphereDiscCollarPoint z s) ∈ sphereTwoDiscComplementOpens f := by
  let N := normalizationComplement f (sphereStandardDisc v) R Φ hΦ
  let y : sphereTwoDiscComplementOpens (sphereStandardDisc v) := ⟨sphereStandardDiscCollar v i ((R
    i).unitSphereEquiv z) s,
    sphereStandardDiscCollar_mem v i _ s s.property.1 s.property.2⟩
  let x := N.symm y
  have he : (N x : (sphere (0 : EuclideanSpace ℝ (Fin 4)) 1)) = y := congrArg Subtype.val
    (N.apply_symm_apply y)
  simp only [N, normalizationComplement, Diffeomorph.subtype_apply_coe] at he
  have hx : (x : (sphere (0 : EuclideanSpace ℝ (Fin 4)) 1)) = f i (sphereDiscCollarPoint z s) :=
    Φ.injective (he.trans (normalization_collar v f R Φ hΦ i z s).symm)
  exact hx ▸ x.property

omit v R Φ hΦ in
/-- The complement of two disjoint supplied smooth discs in the unit three-sphere is a cylinder.
Both original radial collars have exact linear time coordinates with the same positive speed;
the two angular frames are constructed without imposing an orientation condition on the discs. -/
theorem exists_sphereTwoDiscCylinder
    (hfd : Pairwise (Disjoint on fun i ↦ range (f i))) :
    ∃ θ : Fin 2 → (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) ≃ₘ^∞⟮𝓡 2, 𝓡 2⟯ (sphere (0 :
      EuclideanSpace ℝ (Fin 3)) 1), ∃ k η : ℝ,
      0 < k ∧ k ≤ 1 / 2 ∧ 0 < η ∧ η ≤ 1 / 8 ∧
      ∃ C : sphereTwoDiscComplementOpens f ≃ₘ^∞⟮𝓡 3, ((𝓡 2).prod 𝓘(ℝ))⟯ sphereUnitCylinderOpens,
        (∀ i z s, f i (sphereDiscCollarPoint z s) ∈ sphereTwoDiscComplementOpens f) ∧
        (∀ z (s : Ioo (0 : ℝ) (1 / 8)), (s : ℝ) < η →
          ∀ hx : f 0 (sphereDiscCollarPoint z s) ∈ sphereTwoDiscComplementOpens f,
            (C ⟨f 0 (sphereDiscCollarPoint z s), hx⟩ : (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) ×
              ℝ) = (θ 0 z, k * (s : ℝ))) ∧
        (∀ z (s : Ioo (0 : ℝ) (1 / 8)), (s : ℝ) < η →
          ∀ hx : f 1 (sphereDiscCollarPoint z s) ∈ sphereTwoDiscComplementOpens f,
            (C ⟨f 1 (sphereDiscCollarPoint z s), hx⟩ : (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) ×
              ℝ) = (θ 1 z, 1 - k * (s : ℝ))) := by
  have : ConnectedSpace (sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) :=
    TauCeti.connectedSpace_sphere (E := EuclideanSpace ℝ (Fin 4)) 3
  obtain ⟨v⟩ := (inferInstance : Nonempty (sphere (0 : EuclideanSpace ℝ (Fin 4)) 1))
  obtain ⟨R, Φ, hΦ⟩ := exists_original_normalization v f hfd
  obtain ⟨k, η, hk, hk2, hη, hη8, C, hstd, hlow, hupp⟩ := exists_sphereStandardDiscCylinder v
  let θ (i : Fin 2) : (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) ≃ₘ^∞⟮𝓡 2, 𝓡 2⟯ (sphere (0 :
    EuclideanSpace ℝ (Fin 3)) 1) :=
    (R i).unitSphereDiffeomorph ∞
  have hθ (i : Fin 2) (z : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
      θ i z = (R i).unitSphereEquiv z := by
    apply Subtype.ext
    simp only [θ, LinearIsometryEquiv.coe_unitSphereDiffeomorph_apply,
      LinearIsometryEquiv.coe_unitSphereEquiv_apply]
  let N := normalizationComplement f (sphereStandardDisc v) R Φ hΦ
  refine ⟨θ, k, η, hk, hk2, hη, hη8, N.trans C,
    normalization_collar_mem v f R Φ hΦ, ?_, ?_⟩
  · intro z s hs hx
    have he : N ⟨f 0 (sphereDiscCollarPoint z s), hx⟩ =
        ⟨sphereStandardDiscCollar v 0 ((R 0).unitSphereEquiv z) s,
          hstd 0 _ s s.property.1 s.property.2⟩ := by
      apply Subtype.ext
      simpa only [N, normalizationComplement, Diffeomorph.subtype_apply_coe] using
        normalization_collar v f R Φ hΦ 0 z s
    simp only [Diffeomorph.coe_trans, Function.comp_apply]
    rw [he]
    simpa only [hθ] using hlow _ s s.property.1 hs _
  · intro z s hs hx
    have he : N ⟨f 1 (sphereDiscCollarPoint z s), hx⟩ =
        ⟨sphereStandardDiscCollar v 1 ((R 1).unitSphereEquiv z) s,
          hstd 1 _ s s.property.1 s.property.2⟩ := by
      apply Subtype.ext
      simpa only [N, normalizationComplement, Diffeomorph.subtype_apply_coe] using
        normalization_collar v f R Φ hΦ 1 z s
    simp only [Diffeomorph.coe_trans, Function.comp_apply]
    rw [he]
    simpa only [hθ] using hupp _ s s.property.1 hs _

end TauCeti
