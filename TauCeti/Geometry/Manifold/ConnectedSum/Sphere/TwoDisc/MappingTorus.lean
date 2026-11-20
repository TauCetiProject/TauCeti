/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import TauCeti.Geometry.Manifold.ConnectedSum.Sphere.TwoDisc.Cylinder
public import TauCeti.Geometry.Manifold.Instances.MappingTorus.IntervalChart
import TauCeti.Geometry.Sphere.Connected

/-!
# Gluing the two original sphere-disc collars into a native mapping torus

The complement of two supplied smooth discs in the three-sphere maps diffeomorphically to the
native smooth mapping-torus region over `(0,1)`. Both original collars keep their exact linear
time coordinates. For an arbitrary angular attaching diffeomorphism, the constructed monodromy
makes the upper collar at time `1 + t` equal to the lower collar at time `t` with precisely that
angular attachment. The quotient and its smooth interval chart are the native mapping-torus APIs.

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

local instance : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩
local instance : Nonempty (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :=
  (TauCeti.connectedSpace_sphere (E := EuclideanSpace ℝ (Fin 3)) 2).toNonempty

/-- The native interval-chart region of the smooth mapping torus over `(0,1)`. -/
def sphereMappingTorusCutOpens (φ : (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) ≃ₘ^∞⟮𝓡 2, 𝓡 2⟯
  (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)) :
    Opens (TauCeti.SmoothMappingTorus φ) :=
  ⟨(TauCeti.SmoothMappingTorus.intervalChart φ 0 1 (by norm_num)).source,
    (TauCeti.SmoothMappingTorus.intervalChart φ 0 1 (by norm_num)).open_source⟩

/-- A point belongs to the cut region exactly when its circle coordinate lies over `(0,1)`. -/
@[simp]
theorem mem_sphereMappingTorusCutOpens
    (φ : (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) ≃ₘ^∞⟮𝓡 2, 𝓡 2⟯
      (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)) (x : SmoothMappingTorus φ) :
    x ∈ sphereMappingTorusCutOpens φ ↔
      SmoothMappingTorus.proj φ x ∈ (((↑) : ℝ → UnitAddCircle) '' Ioo (0 : ℝ) 1) := by
  simp only [sphereMappingTorusCutOpens, SmoothMappingTorus.intervalChart_source]
  -- Opens membership reads the carrier preimage supplied by the interval-chart source law.
  rfl

private def sphereMappingTorusCylinder (φ : (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) ≃ₘ^∞⟮𝓡 2, 𝓡
  2⟯ (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)) :
    sphereUnitCylinderOpens ≃ₘ^∞⟮((𝓡 2).prod 𝓘(ℝ)), (𝓘(ℝ).prod (𝓡 2))⟯ sphereMappingTorusCutOpens
      φ := by
  let e := TauCeti.SmoothMappingTorus.intervalChart φ 0 1 (by norm_num)
  let V : Opens (ℝ × (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)) := ⟨e.target, e.open_target⟩
  let a : sphereUnitCylinderOpens ≃ₘ^∞⟮((𝓡 2).prod 𝓘(ℝ)), (𝓘(ℝ).prod (𝓡 2))⟯ V :=
    (Diffeomorph.prodComm (𝓡 2) 𝓘(ℝ) (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) ℝ ∞).subtype fun p
      ↦ by
      simp only [Diffeomorph.coe_prodComm]
      rw [mem_sphereUnitCylinderOpens]
      -- V is the target Opens of the local chart e; its carrier is given by intervalChart_target.
      change 0 < p.2 ∧ p.2 < 1 ↔ (p.2, p.1) ∈ e.target
      dsimp only [e]
      rw [TauCeti.SmoothMappingTorus.intervalChart_target]
      simp only [mem_prod, mem_univ, and_true, mem_Ioo]
  exact a.trans e.toDiffeomorphSourceTarget.symm

private theorem sphereMappingTorusCylinder_apply (φ : (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)
  ≃ₘ^∞⟮𝓡 2, 𝓡 2⟯ (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)) (p : sphereUnitCylinderOpens) :
    (sphereMappingTorusCylinder φ p : TauCeti.SmoothMappingTorus φ) =
      TauCeti.SmoothMappingTorus.mk φ p.val.2 p.val.1 := by
  -- Unfold the private construction before its named cut Opens carrier; these are the
  -- same native interval-chart source, with the def wrapper now opaque to default simp.
  unfold sphereMappingTorusCylinder sphereMappingTorusCutOpens
  erw [Diffeomorph.coe_trans]
  simp only [Function.comp_apply,
    PartialDiffeomorph.toDiffeomorphSourceTarget_symm_apply_coe, Diffeomorph.subtype_apply_coe,
    Diffeomorph.coe_prodComm]
  exact congrFun (TauCeti.SmoothMappingTorus.coe_intervalChart_symm φ
    (a := 0) (b := 1) (by norm_num)) (p.val.2, p.val.1)

/-- The monodromy realizing an angular attachment between the two chosen collar frames. -/
def sphereAttachingMonodromy (θ₀ θ₁ g : (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) ≃ₘ^∞⟮𝓡 2, 𝓡 2⟯
  (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)) : (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) ≃ₘ^∞⟮𝓡 2,
  𝓡 2⟯ (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :=
  θ₁.symm.trans (g.trans θ₀)

/-- The attaching monodromy changes from the upper frame to the prescribed lower frame. -/
@[simp]
theorem sphereAttachingMonodromy_apply
    (θ₀ θ₁ g : (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) ≃ₘ^∞⟮𝓡 2, 𝓡 2⟯
      (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1))
    (z : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
    sphereAttachingMonodromy θ₀ θ₁ g z = θ₀ (g (θ₁.symm z)) := by
  simp only [sphereAttachingMonodromy, Diffeomorph.coe_trans, Function.comp_apply]

/-- The quotient seam follows the prescribed angular attachment in the original frames. -/
theorem sphereAttachingMonodromy_seam (θ₀ θ₁ g : (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) ≃ₘ^∞⟮𝓡
  2, 𝓡 2⟯ (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)) (z : (sphere (0 : EuclideanSpace ℝ (Fin 3))
  1)) (t : ℝ) :
    TauCeti.SmoothMappingTorus.mk (sphereAttachingMonodromy θ₀ θ₁ g) (1 + t) (θ₁ z) =
      TauCeti.SmoothMappingTorus.mk (sphereAttachingMonodromy θ₀ θ₁ g) t (θ₀ (g z)) := by
  rw [add_comm 1 t, TauCeti.SmoothMappingTorus.mk_add_one]
  simp only [sphereAttachingMonodromy_apply, Diffeomorph.symm_apply_apply]

/-- Two supplied disjoint sphere discs and an arbitrary angular attachment construct the native
mapping-torus comparison with both exact original collar formulas and the attaching seam law. -/
theorem exists_sphereTwoDiscMappingTorusComparison (f : Fin 2 → (TauCeti.SmoothEmbedding (𝓡 3) (𝓡
  3) ∞ (TauCeti.unitBallOpens (EuclideanSpace ℝ (Fin 3))) (sphere (0 : EuclideanSpace ℝ (Fin 4))
  1)))
    (hfd : Pairwise (Disjoint on fun i ↦ range (f i)))
    (g : (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) ≃ₘ^∞⟮𝓡 2, 𝓡 2⟯ (sphere (0 : EuclideanSpace ℝ
      (Fin 3)) 1)) :
    ∃ θ : Fin 2 → (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) ≃ₘ^∞⟮𝓡 2, 𝓡 2⟯ (sphere (0 :
      EuclideanSpace ℝ (Fin 3)) 1), ∃ k η : ℝ,
      0 < k ∧ k ≤ 1 / 2 ∧ 0 < η ∧ η ≤ 1 / 8 ∧
      ∃ C : sphereTwoDiscComplementOpens f ≃ₘ^∞⟮𝓡 3, (𝓘(ℝ).prod (𝓡 2))⟯
          sphereMappingTorusCutOpens (sphereAttachingMonodromy (θ 0) (θ 1) g),
        (∀ i z s, f i (sphereDiscCollarPoint z s) ∈ sphereTwoDiscComplementOpens f) ∧
        (∀ z (s : Ioo (0 : ℝ) (1 / 8)), (s : ℝ) < η →
          ∀ hx : f 0 (sphereDiscCollarPoint z s) ∈ sphereTwoDiscComplementOpens f,
            (C ⟨f 0 (sphereDiscCollarPoint z s), hx⟩ :
              TauCeti.SmoothMappingTorus (sphereAttachingMonodromy (θ 0) (θ 1) g)) =
              TauCeti.SmoothMappingTorus.mk (sphereAttachingMonodromy (θ 0) (θ 1) g)
                (k * (s : ℝ)) (θ 0 z)) ∧
        (∀ z (s : Ioo (0 : ℝ) (1 / 8)), (s : ℝ) < η →
          ∀ hx : f 1 (sphereDiscCollarPoint z s) ∈ sphereTwoDiscComplementOpens f,
            (C ⟨f 1 (sphereDiscCollarPoint z s), hx⟩ :
              TauCeti.SmoothMappingTorus (sphereAttachingMonodromy (θ 0) (θ 1) g)) =
              TauCeti.SmoothMappingTorus.mk (sphereAttachingMonodromy (θ 0) (θ 1) g)
                (1 - k * (s : ℝ)) (θ 1 z)) ∧
        (∀ (z : (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)) (t : ℝ),
          TauCeti.SmoothMappingTorus.mk (sphereAttachingMonodromy (θ 0) (θ 1) g) (1 + t) (θ 1 z) =
            TauCeti.SmoothMappingTorus.mk (sphereAttachingMonodromy (θ 0) (θ 1) g) t (θ 0 (g z)))
              := by
  obtain ⟨θ, k, η, hk, hk2, hη, hη8, C, hmem, hlow, hupp⟩ := exists_sphereTwoDiscCylinder f hfd
  let φ := sphereAttachingMonodromy (θ 0) (θ 1) g
  let A := sphereMappingTorusCylinder φ
  refine ⟨θ, k, η, hk, hk2, hη, hη8, C.trans A, hmem, ?_, ?_, sphereAttachingMonodromy_seam _ _ _⟩
  · intro z s hs hx
    simp only [Diffeomorph.coe_trans, Function.comp_apply]
    rw [sphereMappingTorusCylinder_apply]
    exact congrArg (fun p : (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) × ℝ ↦
      TauCeti.SmoothMappingTorus.mk φ p.2 p.1)
      (hlow z s hs hx)
  · intro z s hs hx
    simp only [Diffeomorph.coe_trans, Function.comp_apply]
    rw [sphereMappingTorusCylinder_apply]
    exact congrArg (fun p : (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) × ℝ ↦
      TauCeti.SmoothMappingTorus.mk φ p.2 p.1)
      (hupp z s hs hx)

end TauCeti
