/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import TauCeti.Geometry.Manifold.ConnectedSum.Sphere.TwoDisc.Cylinder
public import TauCeti.Geometry.Manifold.Instances.MappingTorus.IntervalChart
public import TauCeti.Geometry.Manifold.Instances.MappingTorus.Attaching

/-!
# Comparing the two-disc sphere complement with a mapping-torus interval cut

The complement of two supplied smooth discs in an `n`-sphere (`2 ≤ n`) maps diffeomorphically to the
native smooth mapping-torus region over `(0,1)`. Both original collars keep their exact linear
time coordinates, at times `k * s` and `1 - k * s` inside the cut. For an arbitrary angular
attaching diffeomorphism `g`, the constructed monodromy satisfies the quotient identity
`[1 + t, θ₁ z] = [t, θ₀ (g z)]`. The quotient and its smooth interval chart are the native
mapping-torus APIs.

The collar comparison and angular attaching-monodromy construction are adapted from
[frenzymath/PoincareConjecture](https://github.com/frenzymath/PoincareConjecture), with
[frenzymath/lean-eval-submissions](https://github.com/frenzymath/lean-eval-submissions) as a
supporting formalization reference.
-/

public section

noncomputable section

open Set Function Metric Topology TopologicalSpace
open scoped Manifold ContDiff

namespace TauCeti

variable {n : ℕ}
open scoped SphereTwoDisc

/-- Two supplied disjoint sphere discs and an arbitrary angular attachment construct the native
mapping-torus comparison with both exact original collar formulas and the attaching seam law. -/
theorem exists_diffeomorph_sphereTwoDiscComplementOpens_intervalCutOpens [Fact (2 ≤ n)]
    (f : Fin 2 → SmoothEmbedding (𝓡 n) (𝓡 n) ∞ (unitBallOpens (EuclideanSpace ℝ (Fin n)))
      (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1))
    (hfd : Pairwise (Disjoint on fun i ↦ range (f i)))
    (g : sphere (0 : EuclideanSpace ℝ (Fin n)) 1 ≃ₘ^∞⟮𝓡 (n - 1), 𝓡 (n - 1)⟯
      sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :
    ∃ θ : Fin 2 → (sphere (0 : EuclideanSpace ℝ (Fin n)) 1) ≃ₘ^∞⟮𝓡 (n - 1), 𝓡 (n - 1)⟯ (sphere (0 :
      EuclideanSpace ℝ (Fin n)) 1), ∃ k η : ℝ,
      0 < k ∧ k ≤ 1 / 2 ∧ 0 < η ∧ η ≤ 1 / 8 ∧
      ∃ C : sphereTwoDiscComplementOpens f ≃ₘ^∞⟮𝓡 n, (𝓘(ℝ).prod (𝓡 (n - 1)))⟯
          SmoothMappingTorus.intervalCutOpens (SmoothMappingTorus.attachingMonodromy (θ 0) (θ 1) g)
            0 1,
        (∀ i z s, f i (sphereDiscCollarPoint z s) ∈ sphereTwoDiscComplementOpens f) ∧
        (∀ z (s : Ioo (0 : ℝ) 1), (s : ℝ) < η →
          ∀ hx : f 0 (sphereDiscCollarPoint z s) ∈ sphereTwoDiscComplementOpens f,
            (C ⟨f 0 (sphereDiscCollarPoint z s), hx⟩ :
              TauCeti.SmoothMappingTorus (SmoothMappingTorus.attachingMonodromy (θ 0) (θ 1) g)) =
              TauCeti.SmoothMappingTorus.mk (SmoothMappingTorus.attachingMonodromy (θ 0) (θ 1) g)
                (k * (s : ℝ)) (θ 0 z)) ∧
        (∀ z (s : Ioo (0 : ℝ) 1), (s : ℝ) < η →
          ∀ hx : f 1 (sphereDiscCollarPoint z s) ∈ sphereTwoDiscComplementOpens f,
            (C ⟨f 1 (sphereDiscCollarPoint z s), hx⟩ :
              TauCeti.SmoothMappingTorus (SmoothMappingTorus.attachingMonodromy (θ 0) (θ 1) g)) =
              TauCeti.SmoothMappingTorus.mk (SmoothMappingTorus.attachingMonodromy (θ 0) (θ 1) g)
                (1 - k * (s : ℝ)) (θ 1 z)) ∧
        (∀ (z : (sphere (0 : EuclideanSpace ℝ (Fin n)) 1)) (t : ℝ),
          TauCeti.SmoothMappingTorus.mk (SmoothMappingTorus.attachingMonodromy (θ 0) (θ 1) g)
            (1 + t) (θ 1 z) =
            TauCeti.SmoothMappingTorus.mk (SmoothMappingTorus.attachingMonodromy (θ 0) (θ 1) g)
              t (θ 0 (g z))) := by
  obtain ⟨θ, k, η, hk, hk2, hη, hη8, C, hmem, hlow, hupp⟩ :=
    exists_diffeomorph_sphereTwoDiscComplementOpens_prodIooOpens f hfd
  let φ := SmoothMappingTorus.attachingMonodromy (θ 0) (θ 1) g
  let A := SmoothMappingTorus.intervalCutDiffeomorph φ (a := 0) (b := 1) (by norm_num)
  have hcollar (i : Fin 2) (z : sphere (0 : EuclideanSpace ℝ (Fin n)) 1)
      (s : Ioo (0 : ℝ) 1)
      (hx : f i (sphereDiscCollarPoint z s) ∈ sphereTwoDiscComplementOpens f) (t : ℝ)
      (hC : (C ⟨f i (sphereDiscCollarPoint z s), hx⟩ :
          (sphere (0 : EuclideanSpace ℝ (Fin n)) 1) × ℝ) = (θ i z, t)) :
      ((C.trans A) ⟨f i (sphereDiscCollarPoint z s), hx⟩ : SmoothMappingTorus φ) =
        SmoothMappingTorus.mk φ t (θ i z) := by
    simp only [Diffeomorph.coe_trans, Function.comp_apply]
    rw [SmoothMappingTorus.intervalCutDiffeomorph_apply_coe]
    exact congrArg (fun p : (sphere (0 : EuclideanSpace ℝ (Fin n)) 1) × ℝ ↦
      SmoothMappingTorus.mk φ p.2 p.1) hC
  refine ⟨θ, k, η, hk, hk2, hη, hη8, C.trans A, hmem, ?_, ?_,
    SmoothMappingTorus.mk_one_add_attachingMonodromy _ _ _⟩
  · intro z s hs hx
    exact hcollar 0 z s hx _ (hlow z s hs hx)
  · intro z s hs hx
    exact hcollar 1 z s hx _ (hupp z s hs hx)

end TauCeti
