/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Sphere.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.OrthonormalTrivialization
public import TauCeti.LinearAlgebra.CliffordAlgebra.Module.Euclidean
import TauCeti.Geometry.Manifold.VectorField.Immersion
import TauCeti.Geometry.Manifold.VectorField.Regularity

/-!
# Clifford tangent frames and parallelizability of `S⁰`, `S¹`, `S³`, and `S⁷`

Through the isometric tangent-space identification `TauCeti.sphereTangentEquiv`, a tangent vector
field on the unit sphere `Sⁿ = sphere (0 : E) 1` of an `(n + 1)`-dimensional real inner product
space `E` corresponds to a map `V : Sⁿ → E` taking values orthogonal to the radius vector at each
point. Because the inclusion `Sⁿ ↪ E` is an analytic immersion with split-injective differential,
a tangent vector field on `Sⁿ` is `C^m` (for any `m : ℕ∞ω`, including `∞` and `ω`) if and only if
its ambient directional-derivative map `x ↦ mvfderiv (𝓡 n) (↑) x (v x)` is `C^m`
(`TauCeti.contMDiff_tangentBundle_sphere_iff`).

Any skew-symmetric continuous linear operator `L : E →L[ℝ] E` sends each `x ∈ Sⁿ` into `(ℝ ∙ x)ᗮ`,
giving an analytic tangent vector field `TauCeti.sphereSkewField L hL`. When
`A : Fin n → (E →L[ℝ] E)` consists of pairwise anticommuting skew-symmetric operators squaring to
`-1`, these fields form an analytic global orthonormal frame of `TSⁿ` in the round metric
(`TauCeti.orthonormal_sphereSkewField`), hence an explicit `C^m` diffeomorphism
`TangentBundle (𝓡 n) Sⁿ ≃ₘ^m Sⁿ × EuclideanSpace ℝ (Fin n)`
(`TauCeti.sphereSkewTangentDiffeomorph`) that acts as a linear isometry on every fibre.

Combining this construction with the Hurwitz–Radon Clifford algebra representations on `ℝ²`, `ℝ⁴`,
and `ℝ⁸` (`TauCeti.exists_skewAdjoint_anticommuting_clm`) and the empty frame in dimension zero
yields global analytic orthonormal tangent frames and isometric tangent-bundle trivializations on
`S⁰`, `S¹`, `S³`, and `S⁷` (`TauCeti.exists_orthonormal_contMDiff_sphere_tangentFrame`,
`TauCeti.nonempty_sphere_tangentBundle_diffeomorph`, and
`TauCeti.exists_linearIndependent_contMDiff_sphere_tangentFrame`).

## Main definitions

* `TauCeti.sphereTangentField`: tangent vector field on `sphere (0 : E) 1` lifted from an ambient
  map `V : sphere (0 : E) 1 → E` pointwise orthogonal to the radius vector.
* `TauCeti.sphereSkewField`: analytic tangent vector field on `sphere (0 : E) 1` induced by a
  skew-symmetric continuous linear operator `L : E →L[ℝ] E`.
* `TauCeti.sphereSkewOrthonormalBasis`: global orthonormal tangent basis of `sphere (0 : E) 1`
  induced by `n` anticommuting skew-symmetric operators squaring to `-1`.
* `TauCeti.sphereSkewTangentDiffeomorph`: explicit `C^m` isometric diffeomorphism
  `TangentBundle (𝓡 n) (sphere (0 : E) 1) ≃ₘ^m sphere (0 : E) 1 × EuclideanSpace ℝ (Fin n)`.
* `TauCeti.sphereZeroTangentDiffeomorph`: canonical `C^m` diffeomorphism trivializing `TS⁰`.

## Main results

* `TauCeti.contMDiff_tangentBundle_sphere_iff`: a tangent vector field on `sphere (0 : E) 1` is
  `C^m` if and only if its ambient pushforward `x ↦ mvfderiv (𝓡 n) (↑) x (v x)` is `C^m`.
* `TauCeti.exists_orthonormal_contMDiff_sphere_tangentFrame`: for `n ∈ {0, 1, 3, 7}`, the unit
  sphere `sphere (0 : E) 1` admits a `C^m` global orthonormal tangent frame.
* `TauCeti.nonempty_sphere_tangentBundle_diffeomorph`: for `n ∈ {0, 1, 3, 7}`, `TSⁿ` is `C^m`
  diffeomorphic to `Sⁿ × ℝⁿ`.
* `TauCeti.exists_sphere_tangentBundle_trivialization_mem_maximalAtlas`: for `n ∈ {0, 1, 3, 7}`,
  `TSⁿ` admits a global linear norm-preserving trivialization in its `C^m` maximal atlas.
* `TauCeti.exists_linearIndependent_contMDiff_sphere_tangentFrame`: for `n ∈ {0, 1, 3, 7}`, the
  standard sphere `sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1` admits `n` `C^m` linearly
  independent tangent vector fields.

## References

* A. Hatcher, *Vector Bundles and K-Theory*, §1.1, p. 5.
* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry*, Princeton Mathematical Series 38,
  Princeton University Press, 1989, Chapter I, §4–§5.
-/

public section

noncomputable section

open Bundle Metric Module Set
open scoped Bundle ContDiff InnerProductSpace Manifold

namespace TauCeti

section AmbientLift

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
  [Fact (finrank ℝ E = n + 1)]

/-- At every point `x` of the unit sphere, the differential of the inclusion `Sⁿ ↪ E` admits a
continuous linear left inverse given by orthogonal projection onto `(ℝ ∙ x)ᗮ` followed by
`(sphereTangentEquiv x).symm`. -/
theorem hasLeftInverse_mfderiv_coe_sphere (x : sphere (0 : E) 1) :
    (mfderiv (𝓡 n) 𝓘(ℝ, E) ((↑) : sphere (0 : E) 1 → E) x).HasLeftInverse := by
  have : FiniteDimensional ℝ E := FiniteDimensional.of_finrank_pos
    (by rw [Fact.out (p := finrank ℝ E = n + 1)]; exact Nat.succ_pos n)
  let Q : TangentSpace 𝓘(ℝ, E) (x : E) →L[ℝ] E :=
    { toLinearMap := { toFun := id, map_add' := fun _ _ ↦ rfl, map_smul' := fun _ _ ↦ rfl }
      cont := continuous_id }
  refine ⟨(sphereTangentEquiv x).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((ℝ ∙ (x : E))ᗮ.orthogonalProjectionOnto.comp Q), fun u ↦ ?_⟩
  have hQ : Q (mfderiv (𝓡 n) 𝓘(ℝ, E) ((↑) : sphere (0 : E) 1 → E) x u) =
      (sphereTangentEquiv x u : E) :=
    (coe_sphereTangentEquiv_apply x u).symm
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, hQ,
    Submodule.orthogonalProjectionOnto_mem_subspace_eq_self]
  exact (sphereTangentEquiv x).symm_apply_apply u

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
    have : FiniteDimensional ℝ E := FiniteDimensional.of_finrank_pos
      (by rw [Fact.out (p := finrank ℝ E = n + 1)]; exact Nat.succ_pos n)
    have : CompleteSpace E := FiniteDimensional.completeSpace ℝ E
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

/-- `TauCeti.sphereTangentEquiv` recovers the ambient vector `V x` from
`TauCeti.sphereTangentField V hV x`. -/
theorem sphereTangentEquiv_sphereTangentField (V : sphere (0 : E) 1 → E)
    (hV : ∀ x : sphere (0 : E) 1, V x ∈ (ℝ ∙ (x : E))ᗮ) (x : sphere (0 : E) 1) :
    sphereTangentEquiv (n := n) x (sphereTangentField (n := n) V hV x) = ⟨V x, hV x⟩ := by
  simp [sphereTangentField]

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

end AmbientLift

section SkewFrames

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
  [Fact (finrank ℝ E = n + 1)]

/-- A skew-symmetric continuous linear operator `L : E →L[ℝ] E` restricts to an analytic tangent
vector field `x ↦ L x` on the unit sphere `sphere (0 : E) 1`. -/
def sphereSkewField (L : E →L[ℝ] E) (hL : ∀ x y, ⟪L x, y⟫_ℝ = -⟪x, L y⟫_ℝ)
    (x : sphere (0 : E) 1) : TangentSpace (𝓡 n) x :=
  sphereTangentField (fun x ↦ L (x : E))
    (fun x ↦ mem_orthogonal_span_singleton_of_skew hL (x : E)) x

@[simp]
theorem mfderiv_coe_sphereSkewField (L : E →L[ℝ] E) (hL : ∀ x y, ⟪L x, y⟫_ℝ = -⟪x, L y⟫_ℝ)
    (x : sphere (0 : E) 1) :
    mfderiv (𝓡 n) 𝓘(ℝ, E) ((↑) : sphere (0 : E) 1 → E) x (sphereSkewField (n := n) L hL x) =
      L (x : E) :=
  mfderiv_coe_sphereTangentField _ _ x

/-- Pushing `TauCeti.sphereSkewField L hL x` forward by `mvfderiv` along `(↑)` yields `L x`. -/
theorem mvfderiv_coe_sphereSkewField (L : E →L[ℝ] E) (hL : ∀ x y, ⟪L x, y⟫_ℝ = -⟪x, L y⟫_ℝ)
    (x : sphere (0 : E) 1) :
    mvfderiv (𝓡 n) ((↑) : sphere (0 : E) 1 → E) x (sphereSkewField (n := n) L hL x) = L (x : E) :=
  mvfderiv_coe_sphereTangentField _ _ x

/-- The round inner product of two skew-symmetric tangent fields at `x` equals `⟪L₁ x, L₂ x⟫_ℝ`. -/
theorem inner_sphereSkewField (L₁ L₂ : E →L[ℝ] E)
    (hL₁ : ∀ x y, ⟪L₁ x, y⟫_ℝ = -⟪x, L₁ y⟫_ℝ)
    (hL₂ : ∀ x y, ⟪L₂ x, y⟫_ℝ = -⟪x, L₂ y⟫_ℝ) (x : sphere (0 : E) 1) :
    ⟪sphereSkewField (n := n) L₁ hL₁ x, sphereSkewField (n := n) L₂ hL₂ x⟫_ℝ =
      ⟪L₁ (x : E), L₂ (x : E)⟫_ℝ :=
  inner_sphereTangentField _ _ _ _ x

/-- Pairing `TauCeti.sphereSkewField L hL x` with a tangent vector `w` in the round metric equals
pairing `L x` with `mvfderiv (𝓡 n) (↑) x w` in `E`. -/
theorem inner_sphereSkewField_left (L : E →L[ℝ] E) (hL : ∀ x y, ⟪L x, y⟫_ℝ = -⟪x, L y⟫_ℝ)
    (x : sphere (0 : E) 1) (w : TangentSpace (𝓡 n) x) :
    ⟪sphereSkewField (n := n) L hL x, w⟫_ℝ =
      ⟪L (x : E), mvfderiv (𝓡 n) ((↑) : sphere (0 : E) 1 → E) x w⟫_ℝ :=
  inner_sphereTangentField_left _ _ x w

/-- The round norm of `TauCeti.sphereSkewField L hL x` equals `‖L x‖`. -/
theorem norm_sphereSkewField (L : E →L[ℝ] E) (hL : ∀ x y, ⟪L x, y⟫_ℝ = -⟪x, L y⟫_ℝ)
    (x : sphere (0 : E) 1) :
    ‖sphereSkewField (n := n) L hL x‖ = ‖L (x : E)‖ :=
  norm_sphereTangentField _ _ x

/-- The tangent vector field induced by a skew-symmetric continuous linear operator `L : E →L[ℝ] E`
is `C^m` on `sphere (0 : E) 1` for every regularity `m : ℕ∞ω` (in particular smooth and real
analytic). -/
theorem contMDiff_sphereSkewField {m : ℕ∞ω} (L : E →L[ℝ] E)
    (hL : ∀ x y, ⟪L x, y⟫_ℝ = -⟪x, L y⟫_ℝ) :
    ContMDiff (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) m
      (fun x ↦ (⟨x, sphereSkewField L hL x⟩ : TangentBundle (𝓡 n) (sphere (0 : E) 1))) :=
  (contMDiff_sphereTangentField_iff _).mpr (L.contDiff.comp_contMDiff contMDiff_coe_sphere)

/-- A family of pairwise anticommuting skew-symmetric continuous linear operators squaring to `-1`
induces a pointwise orthonormal family of tangent vectors in the round metric at every point of
`sphere (0 : E) 1`. -/
theorem orthonormal_sphereSkewField {ι : Type*} {A : ι → E →L[ℝ] E}
    (hskew : ∀ i x y, ⟪A i x, y⟫_ℝ = -⟪x, A i y⟫_ℝ)
    (hsq : ∀ i x, A i (A i x) = -x)
    (hanti : ∀ i j, i ≠ j → ∀ x, A i (A j x) + A j (A i x) = 0)
    (x : sphere (0 : E) 1) :
    Orthonormal ℝ (fun i ↦ sphereSkewField (n := n) (A i) (hskew i) x) := by
  have horth := orthonormal_apply_of_skew_anticommute hskew hsq hanti (norm_eq_of_mem_sphere x)
  exact ⟨fun i ↦ (norm_sphereSkewField (A i) (hskew i) x).trans (horth.1 i),
    fun {i j} hij ↦ (inner_sphereSkewField (A i) (A j) (hskew i) (hskew j) x).trans (horth.2 hij)⟩

/-- Given `n` pairwise anticommuting skew-symmetric continuous linear operators on `E` squaring to
`-1`, their induced tangent fields form an `OrthonormalBasis` of `TangentSpace (𝓡 n) x` at every
`x : sphere (0 : E) 1`. -/
def sphereSkewOrthonormalBasis {A : Fin n → E →L[ℝ] E}
    (hskew : ∀ i x y, ⟪A i x, y⟫_ℝ = -⟪x, A i y⟫_ℝ)
    (hsq : ∀ i x, A i (A i x) = -x)
    (hanti : ∀ i j, i ≠ j → ∀ x, A i (A j x) + A j (A i x) = 0)
    (x : sphere (0 : E) 1) :
    OrthonormalBasis (Fin n) ℝ (TangentSpace (𝓡 n) x) :=
  orthonormalBasisOfOrthonormalSections (F := EuclideanSpace ℝ (Fin n))
    (orthonormal_sphereSkewField hskew hsq hanti) (by simp) x

@[simp]
theorem sphereSkewOrthonormalBasis_apply {A : Fin n → E →L[ℝ] E}
    (hskew : ∀ i x y, ⟪A i x, y⟫_ℝ = -⟪x, A i y⟫_ℝ)
    (hsq : ∀ i x, A i (A i x) = -x)
    (hanti : ∀ i j, i ≠ j → ∀ x, A i (A j x) + A j (A i x) = 0)
    (x : sphere (0 : E) 1) (i : Fin n) :
    sphereSkewOrthonormalBasis hskew hsq hanti x i = sphereSkewField (A i) (hskew i) x := by
  simp [sphereSkewOrthonormalBasis]

/-- A family of `n` pairwise anticommuting skew-symmetric continuous linear operators on `E`
squaring to `-1` induces an explicit `C^m` diffeomorphism
`TangentBundle (𝓡 n) (sphere (0 : E) 1) ≃ₘ^m sphere (0 : E) 1 × EuclideanSpace ℝ (Fin n)` that is a
linear isometry on every tangent space. -/
def sphereSkewTangentDiffeomorph {m : ℕ∞ω} {A : Fin n → E →L[ℝ] E}
    (hskew : ∀ i x y, ⟪A i x, y⟫_ℝ = -⟪x, A i y⟫_ℝ)
    (hsq : ∀ i x, A i (A i x) = -x)
    (hanti : ∀ i j, i ≠ j → ∀ x, A i (A j x) + A j (A i x) = 0) :
    TangentBundle (𝓡 n) (sphere (0 : E) 1)
      ≃ₘ^m⟮(𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)),
        (𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))⟯
      sphere (0 : E) 1 × EuclideanSpace ℝ (Fin n) :=
  OrthonormalBasis.totalSpaceEuclideanDiffeomorph
    (F := EuclideanSpace ℝ (Fin n)) (E := TangentSpace (𝓡 n))
    (sphereSkewOrthonormalBasis hskew hsq hanti) fun i ↦ by
      simpa only [sphereSkewOrthonormalBasis_apply] using
        contMDiff_sphereSkewField (m := m) (A i) (hskew i)

@[simp]
theorem sphereSkewTangentDiffeomorph_fst {m : ℕ∞ω} {A : Fin n → E →L[ℝ] E}
    (hskew : ∀ i x y, ⟪A i x, y⟫_ℝ = -⟪x, A i y⟫_ℝ)
    (hsq : ∀ i x, A i (A i x) = -x)
    (hanti : ∀ i j, i ≠ j → ∀ x, A i (A j x) + A j (A i x) = 0)
    (p : TangentBundle (𝓡 n) (sphere (0 : E) 1)) :
    (sphereSkewTangentDiffeomorph (m := m) hskew hsq hanti p).1 = p.proj :=
  OrthonormalBasis.totalSpaceEuclideanDiffeomorph_fst _ _ p

@[simp]
theorem sphereSkewTangentDiffeomorph_snd_apply {m : ℕ∞ω} {A : Fin n → E →L[ℝ] E}
    (hskew : ∀ i x y, ⟪A i x, y⟫_ℝ = -⟪x, A i y⟫_ℝ)
    (hsq : ∀ i x, A i (A i x) = -x)
    (hanti : ∀ i j, i ≠ j → ∀ x, A i (A j x) + A j (A i x) = 0)
    (x : sphere (0 : E) 1) (w : TangentSpace (𝓡 n) x) (i : Fin n) :
    (sphereSkewTangentDiffeomorph (m := m) hskew hsq hanti ⟨x, w⟩).2 i =
      ⟪A i (x : E), mvfderiv (𝓡 n) ((↑) : sphere (0 : E) 1 → E) x w⟫_ℝ := by
  rw [sphereSkewTangentDiffeomorph, OrthonormalBasis.totalSpaceEuclideanDiffeomorph_snd_apply,
    sphereSkewOrthonormalBasis_apply, inner_sphereSkewField_left]

/-- The inverse of `TauCeti.sphereSkewTangentDiffeomorph` expands coordinates in `ℝⁿ` along the
skew-symmetric tangent frame `sphereSkewField (A i)`. -/
theorem sphereSkewTangentDiffeomorph_symm_eq_sum {m : ℕ∞ω} {A : Fin n → E →L[ℝ] E}
    (hskew : ∀ i x y, ⟪A i x, y⟫_ℝ = -⟪x, A i y⟫_ℝ)
    (hsq : ∀ i x, A i (A i x) = -x)
    (hanti : ∀ i j, i ≠ j → ∀ x, A i (A j x) + A j (A i x) = 0)
    (x : sphere (0 : E) 1) (y : EuclideanSpace ℝ (Fin n)) :
    (sphereSkewTangentDiffeomorph (m := m) hskew hsq hanti).symm (x, y) =
      ⟨x, ∑ i, y i • sphereSkewField (A i) (hskew i) x⟩ := by
  rw [sphereSkewTangentDiffeomorph, OrthonormalBasis.totalSpaceEuclideanDiffeomorph_symm_eq_sum]
  simp only [sphereSkewOrthonormalBasis_apply]

@[simp]
theorem norm_sphereSkewTangentDiffeomorph_snd {m : ℕ∞ω} {A : Fin n → E →L[ℝ] E}
    (hskew : ∀ i x y, ⟪A i x, y⟫_ℝ = -⟪x, A i y⟫_ℝ)
    (hsq : ∀ i x, A i (A i x) = -x)
    (hanti : ∀ i j, i ≠ j → ∀ x, A i (A j x) + A j (A i x) = 0)
    (p : TangentBundle (𝓡 n) (sphere (0 : E) 1)) :
    ‖(sphereSkewTangentDiffeomorph (m := m) hskew hsq hanti p).2‖ = ‖p.2‖ :=
  OrthonormalBasis.norm_totalSpaceEuclideanDiffeomorph_snd _ _ p

end SkewFrames

section Parallelizable

/-- The canonical `C^m` diffeomorphism trivializing the rank-zero tangent bundle `TS⁰` of the unit
sphere in a `1`-dimensional real inner product space `E`. -/
def sphereZeroTangentDiffeomorph {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [Fact (finrank ℝ E = 0 + 1)] (m : ℕ∞ω) :
    TangentBundle (𝓡 0) (sphere (0 : E) 1)
      ≃ₘ^m⟮(𝓡 0).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin 0)),
        (𝓡 0).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin 0))⟯
      sphere (0 : E) 1 × EuclideanSpace ℝ (Fin 0) :=
  sphereSkewTangentDiffeomorph (A := Fin.elim0)
    (fun i ↦ i.elim0) (fun i ↦ i.elim0) (fun i ↦ i.elim0)

/-- When `n ∈ {0, 1, 3, 7}`, any `(n + 1)`-dimensional real inner product space `E` carries `n`
pairwise anticommuting skew-symmetric continuous linear operators squaring to `-1`. -/
theorem exists_skewAdjoint_anticommuting_clm_of_zero_or_hurwitz {n : ℕ}
    (hn : n = 0 ∨ n = 1 ∨ n = 3 ∨ n = 7)
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (hE : finrank ℝ E = n + 1) :
    ∃ A : Fin n → (E →L[ℝ] E),
      (∀ i x y, ⟪A i x, y⟫_ℝ = -⟪x, A i y⟫_ℝ) ∧
      (∀ i x, A i (A i x) = -x) ∧
      (∀ i j, i ≠ j → ∀ x, A i (A j x) + A j (A i x) = 0) := by
  rcases hn with rfl | hn'
  · exact ⟨Fin.elim0, fun i ↦ i.elim0, fun i ↦ i.elim0, fun i ↦ i.elim0⟩
  · exact exists_skewAdjoint_anticommuting_clm hn' hE

/-- **Clifford–Hurwitz tangent frames on `S⁰`, `S¹`, `S³`, and `S⁷`.** For `n ∈ {0, 1, 3, 7}` and
any regularity `m : ℕ∞ω` (in particular `∞` and `ω`), the unit sphere `sphere (0 : E) 1` of any
`(n + 1)`-dimensional real inner product space `E` admits `n` global `C^m` tangent vector fields
that are orthonormal in the round metric at every point. -/
theorem exists_orthonormal_contMDiff_sphere_tangentFrame
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
    [Fact (finrank ℝ E = n + 1)] (m : ℕ∞ω) (hn : n = 0 ∨ n = 1 ∨ n = 3 ∨ n = 7) :
    ∃ v : Fin n → (x : sphere (0 : E) 1) → TangentSpace (𝓡 n) x,
      (∀ i, ContMDiff (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) m
        (fun x ↦ (⟨x, v i x⟩ : TangentBundle (𝓡 n) (sphere (0 : E) 1)))) ∧
      ∀ x, Orthonormal ℝ (fun i ↦ v i x) := by
  obtain ⟨A, hskew, hsq, hanti⟩ := exists_skewAdjoint_anticommuting_clm_of_zero_or_hurwitz
    hn (Fact.out (p := finrank ℝ E = n + 1))
  exact ⟨fun i ↦ sphereSkewField (A i) (hskew i),
    fun i ↦ contMDiff_sphereSkewField (A i) (hskew i),
    orthonormal_sphereSkewField hskew hsq hanti⟩

/-- For `n ∈ {0, 1, 3, 7}` and any regularity `m : ℕ∞ω`, the tangent bundle of `sphere (0 : E) 1`
is `C^m` diffeomorphic to `sphere (0 : E) 1 × EuclideanSpace ℝ (Fin n)`. -/
theorem nonempty_sphere_tangentBundle_diffeomorph
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
    [Fact (finrank ℝ E = n + 1)] (m : ℕ∞ω) (hn : n = 0 ∨ n = 1 ∨ n = 3 ∨ n = 7) :
    Nonempty (TangentBundle (𝓡 n) (sphere (0 : E) 1)
      ≃ₘ^m⟮(𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)),
        (𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))⟯
      sphere (0 : E) 1 × EuclideanSpace ℝ (Fin n)) := by
  obtain ⟨A, hskew, hsq, hanti⟩ := exists_skewAdjoint_anticommuting_clm_of_zero_or_hurwitz
    hn (Fact.out (p := finrank ℝ E = n + 1))
  exact ⟨sphereSkewTangentDiffeomorph hskew hsq hanti⟩

/-- For `n ∈ {0, 1, 3, 7}` and any regularity `m : ℕ∞ω`, the tangent bundle of `sphere (0 : E) 1`
admits a global linear norm-preserving `Bundle.Trivialization` in its `C^m` maximal atlas. -/
theorem exists_sphere_tangentBundle_trivialization_mem_maximalAtlas
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
    [Fact (finrank ℝ E = n + 1)] (m : ℕ∞ω) (hn : n = 0 ∨ n = 1 ∨ n = 3 ∨ n = 7) :
    ∃ (e : Trivialization (EuclideanSpace ℝ (Fin n))
        (π (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n) : sphere (0 : E) 1 → Type _))),
      e.IsLinear ℝ ∧ e.baseSet = univ ∧
      (∀ (x : sphere (0 : E) 1) (v : TangentSpace (𝓡 n) x), ‖(e ⟨x, v⟩).2‖ = ‖v‖) ∧
      e.toOpenPartialHomeomorph ∈
        (contMDiffFiberwiseLinear (sphere (0 : E) 1) (EuclideanSpace ℝ (Fin n))
          (𝓡 n) m).maximalAtlas (TangentBundle (𝓡 n) (sphere (0 : E) 1)) := by
  obtain ⟨A, hskew, hsq, hanti⟩ := exists_skewAdjoint_anticommuting_clm_of_zero_or_hurwitz
    hn (Fact.out (p := finrank ℝ E = n + 1))
  let c := EuclideanSpace.basisFun (Fin n) ℝ
  let d : ∀ b : (univ : Set (sphere (0 : E) 1)),
      OrthonormalBasis (Fin n) ℝ (TangentSpace (𝓡 n) (b : sphere (0 : E) 1)) :=
    fun b ↦ sphereSkewOrthonormalBasis hskew hsq hanti b.1
  have hd : ∀ i : Fin n, ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) m
      (fun b : sphere (0 : E) 1 ↦ TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) b
        (@dite _ (b ∈ (univ : Set (sphere (0 : E) 1))) (Classical.propDecidable _)
          (fun hb ↦ d ⟨b, hb⟩ i) (fun _ ↦ 0))) univ := by
    intro i
    refine (contMDiff_sphereSkewField (m := m) (A i) (hskew i)).contMDiffOn.congr fun b hb ↦ ?_
    rw [dite_eq_left_of_eq_true (eq_true hb)]
    simp [d]
  have hcont := OrthonormalBasis.continuous_of_contMDiffOn_orthonormalBasis
    (F := EuclideanSpace ℝ (Fin n)) (E := TangentSpace (𝓡 n)) d hd
  refine ⟨c.bundleTrivialization (E := TangentSpace (𝓡 n)) isOpen_univ d hcont,
    inferInstance, c.bundleTrivialization_baseSet (E := TangentSpace (𝓡 n)) isOpen_univ d hcont,
    fun x v ↦ ?_,
    c.bundleTrivialization_mem_maximalAtlas (E := TangentSpace (𝓡 n)) isOpen_univ d hd⟩
  rw [OrthonormalBasis.bundleTrivialization_apply (E := TangentSpace (𝓡 n))
    c isOpen_univ d hcont (mem_univ x) v,
    c.repr.symm.norm_map, (d ⟨x, mem_univ x⟩).repr.norm_map]

/-- For `n ∈ {0, 1, 3, 7}` and any regularity `m : ℕ∞ω`, the tangent bundle of the standard sphere
`sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1` is `C^m` diffeomorphic to
`sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 × EuclideanSpace ℝ (Fin n)`. -/
theorem nonempty_euclideanSphere_tangentBundle_diffeomorph {n : ℕ} (m : ℕ∞ω)
    (hn : n = 0 ∨ n = 1 ∨ n = 3 ∨ n = 7) :
    Nonempty (TangentBundle (𝓡 n) (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)
      ≃ₘ^m⟮(𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)),
        (𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))⟯
      sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 × EuclideanSpace ℝ (Fin n)) := by
  let : Fact (finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = n + 1) := ⟨finrank_euclideanSpace_fin⟩
  exact nonempty_sphere_tangentBundle_diffeomorph m hn

/-- **Parallelizability of `S⁰`, `S¹`, `S³`, and `S⁷`.** For `n ∈ {0, 1, 3, 7}` and any regularity
`m : ℕ∞ω` (in particular `∞` and `ω`), the standard sphere
`sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1` admits `n` global `C^m` tangent vector fields that
are linearly independent at every point. -/
theorem exists_linearIndependent_contMDiff_sphere_tangentFrame {n : ℕ} (m : ℕ∞ω)
    (hn : n = 0 ∨ n = 1 ∨ n = 3 ∨ n = 7) :
    ∃ v : Fin n → (x : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) → TangentSpace (𝓡 n) x,
      (∀ i, ContMDiff (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) m
        (fun x ↦ (⟨x, v i x⟩ :
          TangentBundle (𝓡 n) (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)))) ∧
      ∀ x, LinearIndependent ℝ (fun i ↦ v i x) := by
  let : Fact (finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = n + 1) := ⟨finrank_euclideanSpace_fin⟩
  obtain ⟨v, hv, horth⟩ := exists_orthonormal_contMDiff_sphere_tangentFrame
    (E := EuclideanSpace ℝ (Fin (n + 1))) m hn
  exact ⟨v, hv, fun x ↦ (horth x).linearIndependent⟩

end Parallelizable

end TauCeti

end
