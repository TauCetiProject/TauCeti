/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import TauCeti.Geometry.Manifold.ConnectedSum.Sphere.TwoDisc.Complement
import TauCeti.Geometry.Manifold.Diffeomorph.OpenSubset
import TauCeti.Geometry.Diffeomorphism.Diffeotopy.DiscConfiguration
import TauCeti.Geometry.Diffeomorphism.Sphere
import TauCeti.Geometry.Manifold.Orientation.Sphere
import TauCeti.Geometry.Sphere.Connected

/-!
# The complement of two supplied smooth discs in a sphere

For `2 ≤ n`, the complement of the radius-`1/2` closed discs supplied by two smooth embeddings
of the open unit `n`-ball with disjoint images is diffeomorphic to the native unit `(n - 1)`-sphere
times `(0,1)`.
Near the removed discs, for collar times below some `η ≤ 1/8`, the construction retains both
original radial collar coordinates with independently chosen angular diffeomorphisms and one
common positive linear speed. No orientation condition on the supplied embeddings is required.

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

variable {n : ℕ}
open scoped SphereTwoDisc

private theorem norm_unitBallDiffeomorph_le_two (p : unitBallOpens (EuclideanSpace ℝ (Fin n)))
    (hp : ‖(p : EuclideanSpace ℝ (Fin n))‖ ≤ 3 / 4) :
    ‖unitBallDiffeomorph (EuclideanSpace ℝ (Fin n)) p‖ ≤ 2 := by
  let d := Real.sqrt (1 - ‖(p : EuclideanSpace ℝ (Fin n))‖ ^ 2)
  have hpos : 0 < 1 - ‖(p : EuclideanSpace ℝ (Fin n))‖ ^ 2 := by
    nlinarith [norm_nonneg (p : EuclideanSpace ℝ (Fin n))]
  have hd : 0 < d := Real.sqrt_pos.2 hpos
  have hd2 : d ^ 2 = 1 - ‖(p : EuclideanSpace ℝ (Fin n))‖ ^ 2 := Real.sq_sqrt hpos.le
  have hle : ‖(p : EuclideanSpace ℝ (Fin n))‖ ≤ 2 * d := by
    by_contra h
    have hsq := (sq_lt_sq₀ (by positivity)
      (norm_nonneg (p : EuclideanSpace ℝ (Fin n)))).2 (lt_of_not_ge h)
    nlinarith [norm_nonneg (p : EuclideanSpace ℝ (Fin n))]
  rw [norm_unitBallDiffeomorph]
  exact (div_le_iff₀ hd).2 hle

private def discNormalization
    (f g : Fin 2 → SmoothEmbedding (𝓡 n) (𝓡 n) ∞
      (unitBallOpens (EuclideanSpace ℝ (Fin n)))
      (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1))
    (R : Fin 2 → EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n))
    (Φ : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 ≃ₘ^∞⟮𝓡 n, 𝓡 n⟯
      sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) : Prop :=
  ∀ i (p : unitBallOpens (EuclideanSpace ℝ (Fin n))),
    ‖(p : EuclideanSpace ℝ (Fin n))‖ ≤ 3 / 4 →
    Φ (f i p) = g i ⟨R i p, by
      simpa only [mem_unitBallOpens, LinearIsometryEquiv.norm_map] using p.property⟩

private theorem norm_sphereHalfDiscInclusion_le_three_quarters
    (p : closedBall (0 : EuclideanSpace ℝ (Fin n)) (1 / 2)) :
    ‖(sphereHalfDiscInclusion p : EuclideanSpace ℝ (Fin n))‖ ≤ 3 / 4 := by
  simpa only [coe_sphereHalfDiscInclusion] using
    (mem_closedBall_zero_iff.1 p.property).trans (by norm_num : (1 / 2 : ℝ) ≤ 3 / 4)

private theorem exists_original_normalization [Fact (2 ≤ n)]
    (v : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)
    (f : Fin 2 → SmoothEmbedding (𝓡 n) (𝓡 n) ∞
      (unitBallOpens (EuclideanSpace ℝ (Fin n))) (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1))
    (hfd : Pairwise (Disjoint on fun i ↦ range (f i))) :
    ∃ R : Fin 2 → EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n),
      ∃ Φ : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 ≃ₘ^∞⟮𝓡 n, 𝓡 n⟯
        sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1,
        discNormalization f (sphereStandardDisc v) R Φ := by
  have : ConnectedSpace (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :=
    TauCeti.connectedSpace_sphere (E := EuclideanSpace ℝ (Fin (n + 1))) n
  let oM : Manifold.Orientation (𝓡 n)
      (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) (Fin n) :=
    (Module.finBasisOfFinrankEq ℝ (EuclideanSpace ℝ (Fin (n + 1)))
      (by simp)).orientation.sphereOrientation
  let g := sphereStandardDisc v
  have hgd := sphereStandardDisc_disjoint v
  let D := TauCeti.unitBallDiffeomorph (EuclideanSpace ℝ (Fin n))
  let f' i := (f i).compDiffeomorph D.symm
  let g' i := (g i).compDiffeomorph D.symm
  obtain ⟨R, Φ, hΦ⟩ :=
    SmoothEmbedding.exists_diffeomorph_eqOn_comp_linearIsometryEquiv_of_pairwise_disjoint
      (by
        rw [← Module.finrank_eq_rank]
        simpa using (show 1 < n from by have h := Fact.out (p := 2 ≤ n); omega))
      f' g' (by simpa only [f', SmoothEmbedding.range_compDiffeomorph] using hfd)
      (by simpa only [g', SmoothEmbedding.range_compDiffeomorph] using hgd) oM 2
  refine ⟨R, Φ, fun i p hp ↦ ?_⟩
  have h := hΦ i (mem_closedBall_zero_iff.2 (norm_unitBallDiffeomorph_le_two p hp))
  simp only [f', g', SmoothEmbedding.coe_compDiffeomorph, comp_apply] at h
  rw [Diffeomorph.symm_apply_apply] at h
  convert h using 1
  apply congrArg (g i)
  apply Subtype.ext
  exact (coe_unitBallDiffeomorph_symm_linearIsometryEquiv_unitBallDiffeomorph (R i) p).symm

private theorem image_originalDisc
    (f g : Fin 2 → SmoothEmbedding (𝓡 n) (𝓡 n) ∞ (unitBallOpens (EuclideanSpace ℝ (Fin n)))
      (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1))
    (R : Fin 2 → EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n))
    (Φ : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 ≃ₘ^∞⟮𝓡 n, 𝓡 n⟯
      sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)
    (hΦ : discNormalization f g R Φ)
    (i : Fin 2) :
    Φ '' range (f i ∘ sphereHalfDiscInclusion) = range (g i ∘ sphereHalfDiscInclusion) := by
  ext x
  constructor
  · rintro ⟨_, ⟨p, rfl⟩, rfl⟩
    have hp : R i (p : (EuclideanSpace ℝ (Fin n))) ∈ closedBall 0 (1 / 2) := by
      simpa only [mem_closedBall_zero_iff, LinearIsometryEquiv.norm_map] using p.property
    refine ⟨⟨R i p, hp⟩, ?_⟩
    simp only [Function.comp_apply]
    rw [hΦ i (sphereHalfDiscInclusion p)
      (norm_sphereHalfDiscInclusion_le_three_quarters p)]
    apply congrArg (g i)
    apply Subtype.ext
    simp only [coe_sphereHalfDiscInclusion]
  · rintro ⟨p, rfl⟩
    have hp : (R i).symm (p : (EuclideanSpace ℝ (Fin n))) ∈ closedBall 0 (1 / 2) := by
      simpa only [mem_closedBall_zero_iff, LinearIsometryEquiv.norm_map] using p.property
    let q : closedBall (0 : (EuclideanSpace ℝ (Fin n))) (1 / 2) := ⟨(R i).symm p, hp⟩
    refine ⟨f i (sphereHalfDiscInclusion q), mem_range_self q, ?_⟩
    rw [hΦ i (sphereHalfDiscInclusion q)
      (norm_sphereHalfDiscInclusion_le_three_quarters q)]
    apply congrArg (g i)
    apply Subtype.ext
    simpa only [coe_sphereHalfDiscInclusion, q] using (R i).apply_symm_apply p

private def normalizationComplement
    (f g : Fin 2 → SmoothEmbedding (𝓡 n) (𝓡 n) ∞ (unitBallOpens (EuclideanSpace ℝ (Fin n)))
      (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1))
    (R : Fin 2 → EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n))
    (Φ : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 ≃ₘ^∞⟮𝓡 n, 𝓡 n⟯
      sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)
    (hΦ : discNormalization f g R Φ) :
    sphereTwoDiscComplementOpens f ≃ₘ^∞⟮𝓡 n, 𝓡 n⟯ sphereTwoDiscComplementOpens g := by
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

variable (v : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)
  (f : Fin 2 → SmoothEmbedding (𝓡 n) (𝓡 n) ∞ (unitBallOpens (EuclideanSpace ℝ (Fin n)))
    (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1))
  (R : Fin 2 → EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n))
  (Φ : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 ≃ₘ^∞⟮𝓡 n, 𝓡 n⟯
    sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)

private theorem normalization_collar (hnorm : discNormalization f (sphereStandardDisc v) R Φ)
    (i : Fin 2) (z : sphere (0 : EuclideanSpace ℝ (Fin n)) 1)
    (s : Ioo (0 : ℝ) 1) (hs : (s : ℝ) ≤ 1 / 2) :
    Φ (f i (sphereDiscCollarPoint z s)) =
      sphereStandardDiscCollar v i ((R i).unitSphereEquiv z) s := by
  rw [hnorm i (sphereDiscCollarPoint z s)
    (by rw [norm_sphereDiscCollarPoint]; linarith)]
  rw [← sphereStandardDisc_sphereDiscCollarPoint v i ((R i).unitSphereEquiv z)
    s]
  apply congrArg (sphereStandardDisc v i)
  apply Subtype.ext
  simp only [coe_sphereDiscCollarPoint, map_smul,
    LinearIsometryEquiv.coe_unitSphereEquiv_apply]


omit v R Φ in
/-- The complement of two disjoint supplied smooth discs in the unit `n`-sphere is a cylinder.
Both original radial collars have linear time coordinates with the same positive speed near
the removed discs, for collar times below some `η ≤ 1/8`. The two angular frames are constructed
without imposing an orientation condition on the discs. -/
theorem exists_diffeomorph_sphereTwoDiscComplementOpens_prodIooOpens [Fact (2 ≤ n)]
    (hfd : Pairwise (Disjoint on fun i ↦ range (f i))) :
    ∃ θ : Fin 2 → (sphere (0 : EuclideanSpace ℝ (Fin n)) 1) ≃ₘ^∞⟮𝓡 (n - 1), 𝓡 (n - 1)⟯ (sphere (0 :
      EuclideanSpace ℝ (Fin n)) 1), ∃ k η : ℝ,
      0 < k ∧ k ≤ 1 / 2 ∧ 0 < η ∧ η ≤ 1 / 8 ∧
      ∃ C : sphereTwoDiscComplementOpens f ≃ₘ^∞⟮𝓡 n, ((𝓡 (n - 1)).prod 𝓘(ℝ))⟯
          prodIooOpens (sphere (0 : EuclideanSpace ℝ (Fin n)) 1) 0 1,
        (∀ i z s, f i (sphereDiscCollarPoint z s) ∈ sphereTwoDiscComplementOpens f) ∧
        (∀ z (s : Ioo (0 : ℝ) 1), (s : ℝ) < η →
          ∀ hx : f 0 (sphereDiscCollarPoint z s) ∈ sphereTwoDiscComplementOpens f,
            (C ⟨f 0 (sphereDiscCollarPoint z s), hx⟩ : (sphere (0 : EuclideanSpace ℝ (Fin n)) 1) ×
              ℝ) = (θ 0 z, k * (s : ℝ))) ∧
        (∀ z (s : Ioo (0 : ℝ) 1), (s : ℝ) < η →
          ∀ hx : f 1 (sphereDiscCollarPoint z s) ∈ sphereTwoDiscComplementOpens f,
            (C ⟨f 1 (sphereDiscCollarPoint z s), hx⟩ : (sphere (0 : EuclideanSpace ℝ (Fin n)) 1) ×
              ℝ) = (θ 1 z, 1 - k * (s : ℝ))) := by
  have : ConnectedSpace (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :=
    TauCeti.connectedSpace_sphere (E := EuclideanSpace ℝ (Fin (n + 1))) n
  obtain ⟨v⟩ := (inferInstance : Nonempty (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1))
  obtain ⟨R, Φ, hΦ⟩ := exists_original_normalization v f hfd
  obtain ⟨k, η, hk, hk2, hη, hη8, C, hstd, hlow, hupp⟩ :=
    exists_diffeomorph_sphereTwoDiscComplementOpens_sphereStandardDisc_prodIooOpens v
  let θ (i : Fin 2) : sphere (0 : EuclideanSpace ℝ (Fin n)) 1
      ≃ₘ^∞⟮𝓡 (n - 1), 𝓡 (n - 1)⟯ sphere (0 : EuclideanSpace ℝ (Fin n)) 1 :=
    (R i).unitSphereDiffeomorph ∞
  have hθ (i : Fin 2) (z : sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :
      θ i z = (R i).unitSphereEquiv z := by
    apply Subtype.ext
    simp only [θ, LinearIsometryEquiv.coe_unitSphereDiffeomorph_apply,
      LinearIsometryEquiv.coe_unitSphereEquiv_apply]
  let N := normalizationComplement f (sphereStandardDisc v) R Φ hΦ
  have he (i : Fin 2) (z : sphere (0 : EuclideanSpace ℝ (Fin n)) 1)
      (s : Ioo (0 : ℝ) 1)
      (hs8 : (s : ℝ) < 1 / 8)
      (hx : f i (sphereDiscCollarPoint z s) ∈ sphereTwoDiscComplementOpens f) :
      N ⟨f i (sphereDiscCollarPoint z s), hx⟩ =
        ⟨sphereStandardDiscCollar v i ((R i).unitSphereEquiv z) s,
          hstd i _ s s.property.1 s.property.2⟩ := by
    apply Subtype.ext
    simpa only [N, normalizationComplement, Diffeomorph.subtype_apply_coe] using
      normalization_collar v f R Φ hΦ i z s (by linarith)
  have hcollar (i : Fin 2) (z : sphere (0 : EuclideanSpace ℝ (Fin n)) 1)
      (s : Ioo (0 : ℝ) 1) (hs : (s : ℝ) < η)
      (hx : f i (sphereDiscCollarPoint z s) ∈ sphereTwoDiscComplementOpens f) (t : ℝ)
      (hC : (C ⟨sphereStandardDiscCollar v i ((R i).unitSphereEquiv z) s,
          hstd i _ s s.property.1 s.property.2⟩ :
          (sphere (0 : EuclideanSpace ℝ (Fin n)) 1) × ℝ) = ((R i).unitSphereEquiv z, t)) :
      ((N.trans C) ⟨f i (sphereDiscCollarPoint z s), hx⟩ :
        (sphere (0 : EuclideanSpace ℝ (Fin n)) 1) × ℝ) = (θ i z, t) := by
    simp only [Diffeomorph.coe_trans, Function.comp_apply]
    rw [he i z s (hs.trans_le hη8) hx]
    simpa only [hθ] using hC
  refine ⟨θ, k, η, hk, hk2, hη, hη8, N.trans C,
    sphereDiscCollarPoint_mem_sphereTwoDiscComplementOpens f hfd, ?_, ?_⟩
  · intro z s hs hx
    exact hcollar 0 z s hs hx _ (hlow _ s s.property.1 hs _)
  · intro z s hs hx
    exact hcollar 1 z s hs hx _ (hupp _ s s.property.1 hs _)

end TauCeti
