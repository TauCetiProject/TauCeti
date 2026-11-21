/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace
public import TauCeti.Geometry.Manifold.Riemannian.Sphere.Basic
import TauCeti.Geometry.Manifold.VectorField.Immersion
import TauCeti.Geometry.Manifold.VectorField.Regularity

/-!
# Ambient characterization and lifting of tangent vector fields on the round sphere

Through the isometric tangent-space identification `TauCeti.sphereTangentEquiv`, a tangent vector
field on the unit sphere `Sⁿ = sphere (0 : E) 1` of an `(n + 1)`-dimensional real inner product
space `E` corresponds to a map `V : Sⁿ → E` taking values orthogonal to the radius vector at each
point (`TauCeti.sphereTangentField`). Because the inclusion `Sⁿ ↪ E` is an analytic immersion whose
differential admits a continuous linear left inverse at every point
(`TauCeti.hasLeftInverse_mfderiv_coe_sphere`), a tangent vector field on `Sⁿ` is `C^m` (for any
`m : ℕ∞ω`, including `∞` and `ω`) if and only if its ambient pushforward
`x ↦ mvfderiv (𝓡 n) (↑) x (v x)` is `C^m` (`TauCeti.contMDiff_tangentBundle_sphere_iff`).

## Main definitions and results

* `TauCeti.hasLeftInverse_mfderiv_coe_sphere`: at every point `x ∈ Sⁿ`, the differential
  `mfderiv (𝓡 n) 𝓘(ℝ, E) (↑) x` has a continuous linear left inverse.
* `TauCeti.contMDiff_tangentBundle_sphere_iff`: a tangent vector field on `Sⁿ` is `C^m` if and only
  if `x ↦ mvfderiv (𝓡 n) (↑) x (v x)` is `C^m`.
* `TauCeti.sphereTangentField`: tangent vector field on `Sⁿ` lifted from an ambient map
  `V : Sⁿ → E` pointwise orthogonal to the radius vector, together with its round-metric inner
  product, norm, smoothness (`TauCeti.contMDiff_sphereTangentField_iff`), orthonormality
  (`TauCeti.orthonormal_sphereTangentField_iff`), and linear-independence
  (`TauCeti.linearIndependent_sphereTangentField_iff`) characterizations.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Chapter 8.
* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Graduate Texts in Mathematics 176,
  Springer, 2018, Chapter 2.
-/

public section

noncomputable section

open Bundle Metric Module
open scoped Bundle ContDiff InnerProductSpace Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
  [Fact (finrank ℝ E = n + 1)]

/-- At every point `x` of the unit sphere, the differential of the inclusion `Sⁿ ↪ E` admits a
continuous linear left inverse. -/
theorem hasLeftInverse_mfderiv_coe_sphere (x : sphere (0 : E) 1) :
    (mfderiv (𝓡 n) 𝓘(ℝ, E) ((↑) : sphere (0 : E) 1 → E) x).HasLeftInverse := by
  have : FiniteDimensional ℝ E := .of_fact_finrank_eq_succ n
  exact ContinuousLinearMap.HasLeftInverse.of_injective_of_finiteDimensional
    (injective_mvfderiv_iff.mp (injective_mvfderiv_subtypeVal_sphere x))

/-- A tangent vector field `v` on `sphere (0 : E) 1` is `C^m` as a section of the tangent bundle
if and only if its ambient image `x ↦ mvfderiv (𝓡 n) (↑) x (v x)` under the differential of the
inclusion is `C^m`. Because the inclusion is analytic, this holds for every `m : ℕ∞ω` (including
`∞` and `ω`). -/
theorem contMDiff_tangentBundle_sphere_iff {m : ℕ∞ω}
    {v : (x : sphere (0 : E) 1) → TangentSpace (𝓡 n) x} :
    ContMDiff (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) m
        (fun x ↦ (⟨x, v x⟩ : TangentBundle (𝓡 n) (sphere (0 : E) 1))) ↔
      ContMDiff (𝓡 n) 𝓘(ℝ, E) m
        (fun x ↦ mvfderiv (𝓡 n) ((↑) : sphere (0 : E) 1 → E) x (v x)) := by
  constructor
  · intro hv
    exact ((contMDiff_coe_sphere (E := E) (n := n) (m := ω)).contMDiff_mvfderiv_apply
      (m := m) le_top).comp hv
  · intro hpush x₀
    refine (contMDiff_coe_sphere (E := E) (n := n) (m := ω) x₀).vectorField_of_mfderiv
      (m := m) le_top (hasLeftInverse_mfderiv_coe_sphere x₀) ?_
    refine Bundle.contMDiffAt_totalSpace_iff.mpr ⟨contMDiff_coe_sphere x₀, ?_⟩
    simpa only [trivializationAt_model_space_apply, ← mvfderiv_apply_eq_mfderiv_apply] using
      hpush x₀

/-- Lift an ambient map `V : sphere (0 : E) 1 → E` pointwise orthogonal to the radius vector to a
tangent vector field on `sphere (0 : E) 1`. -/
def sphereTangentField (V : sphere (0 : E) 1 → E)
    (hV : ∀ x : sphere (0 : E) 1, V x ∈ (ℝ ∙ (x : E))ᗮ)
    (x : sphere (0 : E) 1) : TangentSpace (𝓡 n) x :=
  (sphereTangentEquiv x).symm ⟨V x, hV x⟩

/-- `TauCeti.sphereTangentField` unfolds to `(sphereTangentEquiv x).symm ⟨V x, hV x⟩`. -/
theorem sphereTangentField_def (V : sphere (0 : E) 1 → E)
    (hV : ∀ x : sphere (0 : E) 1, V x ∈ (ℝ ∙ (x : E))ᗮ) (x : sphere (0 : E) 1) :
    sphereTangentField (n := n) V hV x = (sphereTangentEquiv x).symm ⟨V x, hV x⟩ :=
  (rfl)

/-- `TauCeti.sphereTangentEquiv` recovers the ambient vector `V x` from
`TauCeti.sphereTangentField V hV x`. -/
@[simp]
theorem sphereTangentEquiv_sphereTangentField (V : sphere (0 : E) 1 → E)
    (hV : ∀ x : sphere (0 : E) 1, V x ∈ (ℝ ∙ (x : E))ᗮ) (x : sphere (0 : E) 1) :
    sphereTangentEquiv (n := n) x (sphereTangentField (n := n) V hV x) = ⟨V x, hV x⟩ := by
  simp [sphereTangentField]

/-- Lifting the ambient pushforward `x ↦ mfderiv (𝓡 n) 𝓘(ℝ, E) (↑) x (v x)` of a tangent vector
field `v` via `TauCeti.sphereTangentField` recovers `v`. -/
@[simp]
theorem sphereTangentField_mfderiv_coe
    (v : (x : sphere (0 : E) 1) → TangentSpace (𝓡 n) x)
    (hv : ∀ x : sphere (0 : E) 1,
      mfderiv (𝓡 n) 𝓘(ℝ, E) ((↑) : sphere (0 : E) 1 → E) x (v x) ∈ (ℝ ∙ (x : E))ᗮ)
    (x : sphere (0 : E) 1) :
    sphereTangentField (n := n)
      (fun x ↦ mfderiv (𝓡 n) 𝓘(ℝ, E) ((↑) : sphere (0 : E) 1 → E) x (v x)) hv x = v x :=
  (sphereTangentEquiv x).injective <|
    (sphereTangentEquiv_sphereTangentField _ hv x).trans <|
      Subtype.ext (coe_sphereTangentEquiv_apply x (v x)).symm

/-- Lifting the ambient projection of a tangent vector field `v` via `TauCeti.sphereTangentField`
recovers `v`. -/
theorem sphereTangentField_coe_sphereTangentEquiv
    (v : (x : sphere (0 : E) 1) → TangentSpace (𝓡 n) x)
    (hv : ∀ x : sphere (0 : E) 1, (sphereTangentEquiv x (v x) : E) ∈ (ℝ ∙ (x : E))ᗮ)
    (x : sphere (0 : E) 1) :
    sphereTangentField (n := n) (fun x ↦ (sphereTangentEquiv x (v x) : E)) hv x = v x := by
  simp

@[simp]
theorem sphereTangentField_zero (h0 : ∀ x : sphere (0 : E) 1, (0 : E) ∈ (ℝ ∙ (x : E))ᗮ)
    (x : sphere (0 : E) 1) :
    sphereTangentField (n := n) (fun _ ↦ 0) h0 x = 0 := by
  simp [sphereTangentField]

@[simp]
theorem sphereTangentField_add (V W : sphere (0 : E) 1 → E)
    (hV : ∀ x : sphere (0 : E) 1, V x ∈ (ℝ ∙ (x : E))ᗮ)
    (hW : ∀ x : sphere (0 : E) 1, W x ∈ (ℝ ∙ (x : E))ᗮ)
    (hVW : ∀ x : sphere (0 : E) 1, V x + W x ∈ (ℝ ∙ (x : E))ᗮ) (x : sphere (0 : E) 1) :
    sphereTangentField (n := n) (fun x ↦ V x + W x) hVW x =
      sphereTangentField (n := n) V hV x + sphereTangentField (n := n) W hW x := by
  have hsub : (⟨V x + W x, hVW x⟩ : (ℝ ∙ (x : E))ᗮ) = ⟨V x, hV x⟩ + ⟨W x, hW x⟩ := rfl
  rw [sphereTangentField, hsub, map_add, ← sphereTangentField_def, ← sphereTangentField_def]

@[simp]
theorem sphereTangentField_smul (c : sphere (0 : E) 1 → ℝ) (V : sphere (0 : E) 1 → E)
    (hV : ∀ x : sphere (0 : E) 1, V x ∈ (ℝ ∙ (x : E))ᗮ)
    (hcV : ∀ x : sphere (0 : E) 1, c x • V x ∈ (ℝ ∙ (x : E))ᗮ) (x : sphere (0 : E) 1) :
    sphereTangentField (n := n) (fun x ↦ c x • V x) hcV x =
      c x • sphereTangentField (n := n) V hV x := by
  have hsub : (⟨c x • V x, hcV x⟩ : (ℝ ∙ (x : E))ᗮ) = c x • ⟨V x, hV x⟩ := rfl
  rw [sphereTangentField, hsub, map_smul, ← sphereTangentField_def]

@[simp]
theorem mfderiv_coe_sphereTangentField (V : sphere (0 : E) 1 → E)
    (hV : ∀ x : sphere (0 : E) 1, V x ∈ (ℝ ∙ (x : E))ᗮ) (x : sphere (0 : E) 1) :
    mfderiv (𝓡 n) 𝓘(ℝ, E) ((↑) : sphere (0 : E) 1 → E) x (sphereTangentField (n := n) V hV x) =
      V x := by
  rw [← coe_sphereTangentEquiv_apply, sphereTangentEquiv_sphereTangentField]

/-- Pushing `TauCeti.sphereTangentField V hV x` forward by `mvfderiv` along `(↑)` yields `V x`. -/
theorem mvfderiv_coe_sphereTangentField (V : sphere (0 : E) 1 → E)
    (hV : ∀ x : sphere (0 : E) 1, V x ∈ (ℝ ∙ (x : E))ᗮ) (x : sphere (0 : E) 1) :
    mvfderiv (𝓡 n) ((↑) : sphere (0 : E) 1 → E) x (sphereTangentField (n := n) V hV x) = V x := by
  rw [mvfderiv_apply_eq_mfderiv_apply, mfderiv_coe_sphereTangentField]

/-- The round inner product of two lifted ambient tangent fields equals their ambient inner
product. -/
theorem inner_sphereTangentField (V W : sphere (0 : E) 1 → E)
    (hV : ∀ x : sphere (0 : E) 1, V x ∈ (ℝ ∙ (x : E))ᗮ)
    (hW : ∀ x : sphere (0 : E) 1, W x ∈ (ℝ ∙ (x : E))ᗮ)
    (x : sphere (0 : E) 1) :
    ⟪sphereTangentField (n := n) V hV x, sphereTangentField (n := n) W hW x⟫_ℝ = ⟪V x, W x⟫_ℝ := by
  rw [inner_tangentSpace_sphere, mvfderiv_coe_sphereTangentField, mvfderiv_coe_sphereTangentField]

/-- Pairing `TauCeti.sphereTangentField V hV x` with a tangent vector `w` in the round metric
equals pairing `V x` with `mvfderiv (𝓡 n) (↑) x w` in `E`. -/
theorem inner_sphereTangentField_left (V : sphere (0 : E) 1 → E)
    (hV : ∀ x : sphere (0 : E) 1, V x ∈ (ℝ ∙ (x : E))ᗮ)
    (x : sphere (0 : E) 1) (w : TangentSpace (𝓡 n) x) :
    ⟪sphereTangentField (n := n) V hV x, w⟫_ℝ =
      ⟪V x, mvfderiv (𝓡 n) ((↑) : sphere (0 : E) 1 → E) x w⟫_ℝ := by
  rw [inner_tangentSpace_sphere, mvfderiv_coe_sphereTangentField]

/-- `TauCeti.sphereTangentField` preserves pointwise norms. -/
theorem norm_sphereTangentField (V : sphere (0 : E) 1 → E)
    (hV : ∀ x : sphere (0 : E) 1, V x ∈ (ℝ ∙ (x : E))ᗮ) (x : sphere (0 : E) 1) :
    ‖sphereTangentField (n := n) V hV x‖ = ‖V x‖ := by
  rw [norm_tangentSpace_sphere, mvfderiv_coe_sphereTangentField]

/-- A lifted ambient tangent field `sphereTangentField V hV` is `C^m` on the tangent bundle if and
only if `V : sphere (0 : E) 1 → E` is `C^m`. -/
@[simp]
theorem contMDiff_sphereTangentField_iff {m : ℕ∞ω} {V : sphere (0 : E) 1 → E}
    (hV : ∀ x : sphere (0 : E) 1, V x ∈ (ℝ ∙ (x : E))ᗮ) :
    ContMDiff (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) m
        (fun x ↦ (⟨x, sphereTangentField V hV x⟩ : TangentBundle (𝓡 n) (sphere (0 : E) 1))) ↔
      ContMDiff (𝓡 n) 𝓘(ℝ, E) m V := by
  simp only [contMDiff_tangentBundle_sphere_iff, mvfderiv_coe_sphereTangentField]

/-- Pointwise orthonormality of lifted ambient tangent fields in the round metric is equivalent to
pointwise orthonormality of their ambient values in `E`. -/
theorem orthonormal_sphereTangentField_iff {ι : Type*} {V : ι → sphere (0 : E) 1 → E}
    (hV : ∀ i (x : sphere (0 : E) 1), V i x ∈ (ℝ ∙ (x : E))ᗮ) (x : sphere (0 : E) 1) :
    Orthonormal ℝ (fun i ↦ sphereTangentField (n := n) (V i) (hV i) x) ↔
      Orthonormal ℝ (fun i ↦ V i x) := by
  simp only [Orthonormal, norm_sphereTangentField, inner_sphereTangentField]

/-- Pointwise linear independence of lifted ambient tangent fields is equivalent to pointwise
linear independence of their ambient values in `E`. -/
theorem linearIndependent_sphereTangentField_iff {ι : Type*} {V : ι → sphere (0 : E) 1 → E}
    (hV : ∀ i (x : sphere (0 : E) 1), V i x ∈ (ℝ ∙ (x : E))ᗮ) (x : sphere (0 : E) 1) :
    LinearIndependent ℝ (fun i ↦ sphereTangentField (n := n) (V i) (hV i) x) ↔
      LinearIndependent ℝ (fun i ↦ V i x) := by
  have hcomp : (fun i ↦ V i x) =
      (Submodule.subtype (ℝ ∙ (x : E))ᗮ).comp (sphereTangentEquiv x).toLinearEquiv.toLinearMap ∘
        fun i ↦ sphereTangentField (n := n) (V i) (hV i) x := by
    funext i
    exact congrArg Subtype.val (sphereTangentEquiv_sphereTangentField (n := n) (V i) (hV i) x).symm
  rw [hcomp]
  exact (LinearMap.linearIndependent_iff _
    (LinearMap.ker_eq_bot.mpr (Subtype.val_injective.comp (sphereTangentEquiv x).injective))).symm

end TauCeti

end
