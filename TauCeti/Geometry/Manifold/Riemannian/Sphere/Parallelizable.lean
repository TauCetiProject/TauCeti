/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.SkewSymmetric.Basic
public import TauCeti.Geometry.Manifold.Riemannian.Sphere.VectorField
public import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.OrthonormalTrivialization
import TauCeti.Geometry.Manifold.Instances.Sphere
import TauCeti.LinearAlgebra.CliffordAlgebra.Module.Euclidean

/-!
# Clifford tangent frames and parallelizability of `S⁰`, `S¹`, `S³`, and `S⁷`

Any skew-symmetric continuous linear operator `L : E →L[ℝ] E` on an `(n + 1)`-dimensional real
inner product space `E` sends each `x ∈ Sⁿ = sphere (0 : E) 1` into `(ℝ ∙ x)ᗮ`, giving an analytic
tangent vector field `ContinuousLinearMap.sphereSkewField L hL` via `TauCeti.sphereTangentField`.
When `A : Fin n → (E →L[ℝ] E)` consists of pairwise anticommuting skew-symmetric operators squaring
to `-1`, these fields form an analytic global orthonormal frame of `TSⁿ` in the round metric
(`TauCeti.orthonormal_sphereSkewField`), hence an explicit `C^m` fiberwise-isometric diffeomorphism
`TangentBundle (𝓡 n) Sⁿ ≃ₘ^m Sⁿ × EuclideanSpace ℝ (Fin n)`
(`TauCeti.sphereSkewTangentDiffeomorph`).

Combining this construction with the Clifford-algebra operator families on `(n + 1)`-dimensional
real inner product spaces for `n ∈ {0, 1, 3, 7}` (`TauCeti.exists_skew_sq_neg_id_anticommute_clm`)
yields global analytic orthonormal and linearly independent tangent frames on `S⁰`, `S¹`, `S³`, and
`S⁷` (`TauCeti.exists_orthonormal_contMDiff_sphere_tangentFrame`,
`TauCeti.exists_linearIndependent_contMDiff_sphere_tangentFrame`), global isometric tangent-bundle
trivializations in the `C^m` maximal atlas
(`TauCeti.exists_sphere_tangentBundle_trivialization_mem_maximalAtlas`), and `C^m` total-space
diffeomorphisms (`TauCeti.nonempty_sphere_tangentBundle_diffeomorph`).

## Main definitions

* `ContinuousLinearMap.sphereSkewField`: analytic tangent vector field on `sphere (0 : E) 1`
  induced by a skew-symmetric continuous linear operator `L : E →L[ℝ] E`.
* `TauCeti.sphereSkewOrthonormalBasis`: global orthonormal tangent basis of `sphere (0 : E) 1`
  induced by `n` anticommuting skew-symmetric operators squaring to `-1`.
* `TauCeti.sphereSkewTangentDiffeomorph`: explicit `C^m` fiberwise-isometric diffeomorphism
  `TangentBundle (𝓡 n) (sphere (0 : E) 1) ≃ₘ^m sphere (0 : E) 1 × EuclideanSpace ℝ (Fin n)`.
* `TauCeti.sphereZeroTangentDiffeomorph`: canonical `C^m` diffeomorphism trivializing `TS⁰`.

## Main results

* `TauCeti.exists_orthonormal_contMDiff_sphere_tangentFrame`: for `n ∈ {0, 1, 3, 7}`, the unit
  sphere `sphere (0 : E) 1` admits a `C^m` global orthonormal tangent frame.
* `TauCeti.nonempty_sphere_tangentBundle_diffeomorph`,
  `TauCeti.nonempty_euclideanSphere_tangentBundle_diffeomorph`: for `n ∈ {0, 1, 3, 7}`, `TSⁿ` is
  `C^m` diffeomorphic to `Sⁿ × ℝⁿ`.
* `TauCeti.exists_sphere_tangentBundle_trivialization_mem_maximalAtlas`: for `n ∈ {0, 1, 3, 7}`,
  `TSⁿ` admits a global linear norm-preserving trivialization in its `C^m` maximal atlas.
* `TauCeti.exists_linearIndependent_contMDiff_sphere_tangentFrame`,
  `TauCeti.exists_linearIndependent_contMDiff_euclideanSphere_tangentFrame`: for `n ∈ {0, 1, 3, 7}`,
  the unit sphere admits `n` `C^m` linearly independent tangent vector fields.

## References

* A. Hatcher, *Vector Bundles and K-Theory*, §1.1, p. 5.
* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry*, Princeton Mathematical Series 38,
  Princeton University Press, 1989, Chapter I, §4–§5.
-/

public section

noncomputable section

open Bundle Metric Module Set TauCeti
open scoped Bundle ContDiff InnerProductSpace Manifold

namespace ContinuousLinearMap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
  [Fact (finrank ℝ E = n + 1)]

/-- A skew-symmetric continuous linear operator `L : E →L[ℝ] E` restricts to an analytic tangent
vector field `x ↦ L x` on the unit sphere `sphere (0 : E) 1`. -/
def sphereSkewField (L : E →L[ℝ] E) (hL : ∀ x y, ⟪L x, y⟫_ℝ = -⟪x, L y⟫_ℝ)
    (x : sphere (0 : E) 1) : TangentSpace (𝓡 n) x :=
  sphereTangentField (fun x ↦ L (x : E))
    (fun x ↦ mem_orthogonal_span_singleton_of_skew hL (x : E)) x

/-- `ContinuousLinearMap.sphereSkewField` unfolds to `TauCeti.sphereTangentField` applied to
`x ↦ L x`. -/
theorem sphereSkewField_def (L : E →L[ℝ] E) (hL : ∀ x y, ⟪L x, y⟫_ℝ = -⟪x, L y⟫_ℝ)
    (x : sphere (0 : E) 1) :
    L.sphereSkewField (n := n) hL x =
      sphereTangentField (fun x ↦ L (x : E))
        (fun x ↦ mem_orthogonal_span_singleton_of_skew hL (x : E)) x :=
  (rfl)

@[simp]
theorem sphereTangentEquiv_sphereSkewField (L : E →L[ℝ] E)
    (hL : ∀ x y, ⟪L x, y⟫_ℝ = -⟪x, L y⟫_ℝ) (x : sphere (0 : E) 1) :
    sphereTangentEquiv (n := n) x (L.sphereSkewField (n := n) hL x) =
      ⟨L (x : E), mem_orthogonal_span_singleton_of_skew hL (x : E)⟩ :=
  sphereTangentEquiv_sphereTangentField _ _ x

@[simp]
theorem mfderiv_coe_sphereSkewField (L : E →L[ℝ] E) (hL : ∀ x y, ⟪L x, y⟫_ℝ = -⟪x, L y⟫_ℝ)
    (x : sphere (0 : E) 1) :
    mfderiv (𝓡 n) 𝓘(ℝ, E) ((↑) : sphere (0 : E) 1 → E) x (L.sphereSkewField (n := n) hL x) =
      L (x : E) :=
  mfderiv_coe_sphereTangentField _ _ x

/-- Pushing `ContinuousLinearMap.sphereSkewField L hL x` forward by `mvfderiv` along `(↑)` yields
`L x`. -/
theorem mvfderiv_coe_sphereSkewField (L : E →L[ℝ] E) (hL : ∀ x y, ⟪L x, y⟫_ℝ = -⟪x, L y⟫_ℝ)
    (x : sphere (0 : E) 1) :
    mvfderiv (𝓡 n) ((↑) : sphere (0 : E) 1 → E) x (L.sphereSkewField (n := n) hL x) = L (x : E) :=
  mvfderiv_coe_sphereTangentField _ _ x

/-- The round inner product of two skew-symmetric tangent fields at `x` equals `⟪L₁ x, L₂ x⟫_ℝ`. -/
theorem inner_sphereSkewField (L₁ L₂ : E →L[ℝ] E)
    (hL₁ : ∀ x y, ⟪L₁ x, y⟫_ℝ = -⟪x, L₁ y⟫_ℝ)
    (hL₂ : ∀ x y, ⟪L₂ x, y⟫_ℝ = -⟪x, L₂ y⟫_ℝ) (x : sphere (0 : E) 1) :
    ⟪L₁.sphereSkewField (n := n) hL₁ x, L₂.sphereSkewField (n := n) hL₂ x⟫_ℝ =
      ⟪L₁ (x : E), L₂ (x : E)⟫_ℝ :=
  inner_sphereTangentField _ _ _ _ x

/-- Pairing `ContinuousLinearMap.sphereSkewField L hL x` with a tangent vector `w` in the round
metric equals pairing `L x` with `mvfderiv (𝓡 n) (↑) x w` in `E`. -/
theorem inner_sphereSkewField_left (L : E →L[ℝ] E) (hL : ∀ x y, ⟪L x, y⟫_ℝ = -⟪x, L y⟫_ℝ)
    (x : sphere (0 : E) 1) (w : TangentSpace (𝓡 n) x) :
    ⟪L.sphereSkewField (n := n) hL x, w⟫_ℝ =
      ⟪L (x : E), mvfderiv (𝓡 n) ((↑) : sphere (0 : E) 1 → E) x w⟫_ℝ :=
  inner_sphereTangentField_left _ _ x w

/-- The round norm of `ContinuousLinearMap.sphereSkewField L hL x` equals `‖L x‖`. -/
theorem norm_sphereSkewField (L : E →L[ℝ] E) (hL : ∀ x y, ⟪L x, y⟫_ℝ = -⟪x, L y⟫_ℝ)
    (x : sphere (0 : E) 1) :
    ‖L.sphereSkewField (n := n) hL x‖ = ‖L (x : E)‖ :=
  norm_sphereTangentField _ _ x

/-- The tangent vector field induced by a skew-symmetric continuous linear operator `L : E →L[ℝ] E`
is `C^m` on `sphere (0 : E) 1` for every regularity `m : ℕ∞ω` (in particular smooth and real
analytic). -/
theorem contMDiff_sphereSkewField {m : ℕ∞ω} (L : E →L[ℝ] E)
    (hL : ∀ x y, ⟪L x, y⟫_ℝ = -⟪x, L y⟫_ℝ) :
    ContMDiff (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) m
      (fun x ↦ (⟨x, L.sphereSkewField hL x⟩ : TangentBundle (𝓡 n) (sphere (0 : E) 1))) :=
  (contMDiff_sphereTangentField_iff _).mpr (L.contDiff.comp_contMDiff contMDiff_coe_sphere)

end ContinuousLinearMap

namespace TauCeti

section SkewFrames

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
  [Fact (finrank ℝ E = n + 1)]

/-- A family of pairwise anticommuting skew-symmetric continuous linear operators squaring to `-1`
induces a pointwise orthonormal family of tangent vectors in the round metric at every point of
`sphere (0 : E) 1`. -/
theorem orthonormal_sphereSkewField {ι : Type*} {A : ι → E →L[ℝ] E}
    (hskew : ∀ i x y, ⟪A i x, y⟫_ℝ = -⟪x, A i y⟫_ℝ)
    (hsq : ∀ i x, A i (A i x) = -x)
    (hanti : ∀ i j, i ≠ j → ∀ x, A i (A j x) + A j (A i x) = 0)
    (x : sphere (0 : E) 1) :
    Orthonormal ℝ (fun i ↦ (A i).sphereSkewField (n := n) (hskew i) x) :=
  (orthonormal_sphereTangentField_iff _ x).mpr
    (orthonormal_apply_of_skew_anticommute hskew hsq hanti (norm_eq_of_mem_sphere x))

/-- Given `n` pairwise anticommuting skew-symmetric continuous linear operators on `E` squaring to
`-1`, their induced tangent fields form an `OrthonormalBasis` of `TangentSpace (𝓡 n) x` at every
`x : sphere (0 : E) 1`. -/
def sphereSkewOrthonormalBasis {A : Fin n → E →L[ℝ] E}
    (hskew : ∀ i x y, ⟪A i x, y⟫_ℝ = -⟪x, A i y⟫_ℝ)
    (hsq : ∀ i x, A i (A i x) = -x)
    (hanti : ∀ i j, i ≠ j → ∀ x, A i (A j x) + A j (A i x) = 0)
    (x : sphere (0 : E) 1) :
    OrthonormalBasis (Fin n) ℝ (TangentSpace (𝓡 n) x) :=
  orthonormalBasisOfOrthonormalSections (F₀ := EuclideanSpace ℝ (Fin n))
    (orthonormal_sphereSkewField hskew hsq hanti) (by simp) x

@[simp]
theorem sphereSkewOrthonormalBasis_apply {A : Fin n → E →L[ℝ] E}
    (hskew : ∀ i x y, ⟪A i x, y⟫_ℝ = -⟪x, A i y⟫_ℝ)
    (hsq : ∀ i x, A i (A i x) = -x)
    (hanti : ∀ i j, i ≠ j → ∀ x, A i (A j x) + A j (A i x) = 0)
    (x : sphere (0 : E) 1) (i : Fin n) :
    sphereSkewOrthonormalBasis hskew hsq hanti x i = (A i).sphereSkewField (hskew i) x := by
  simp [sphereSkewOrthonormalBasis]

/-- A family of `n` pairwise anticommuting skew-symmetric continuous linear operators on `E`
squaring to `-1` induces an explicit `C^m` fiberwise-isometric diffeomorphism
`TangentBundle (𝓡 n) (sphere (0 : E) 1) ≃ₘ^m sphere (0 : E) 1 × EuclideanSpace ℝ (Fin n)`. -/
def sphereSkewTangentDiffeomorph {m : ℕ∞ω} {A : Fin n → E →L[ℝ] E}
    (hskew : ∀ i x y, ⟪A i x, y⟫_ℝ = -⟪x, A i y⟫_ℝ)
    (hsq : ∀ i x, A i (A i x) = -x)
    (hanti : ∀ i j, i ≠ j → ∀ x, A i (A j x) + A j (A i x) = 0) :
    TangentBundle (𝓡 n) (sphere (0 : E) 1)
      ≃ₘ^m⟮(𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)),
        (𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))⟯
      sphere (0 : E) 1 × EuclideanSpace ℝ (Fin n) :=
  orthonormalFrameDiffeomorph (F := EuclideanSpace ℝ (Fin n)) (E := TangentSpace (𝓡 n))
    (orthonormal_sphereSkewField hskew hsq hanti) (by simp)
    fun i ↦ (A i).contMDiff_sphereSkewField (hskew i)

/-- `TauCeti.sphereSkewTangentDiffeomorph` unfolds to `TauCeti.orthonormalFrameDiffeomorph` on the
skew-symmetric tangent frame `fun i ↦ (A i).sphereSkewField (hskew i)`. -/
theorem sphereSkewTangentDiffeomorph_def {m : ℕ∞ω} {A : Fin n → E →L[ℝ] E}
    (hskew : ∀ i x y, ⟪A i x, y⟫_ℝ = -⟪x, A i y⟫_ℝ)
    (hsq : ∀ i x, A i (A i x) = -x)
    (hanti : ∀ i j, i ≠ j → ∀ x, A i (A j x) + A j (A i x) = 0) :
    sphereSkewTangentDiffeomorph (m := m) hskew hsq hanti =
      orthonormalFrameDiffeomorph (F := EuclideanSpace ℝ (Fin n)) (E := TangentSpace (𝓡 n))
        (orthonormal_sphereSkewField hskew hsq hanti) (by simp)
        (fun i ↦ (A i).contMDiff_sphereSkewField (hskew i)) :=
  (rfl)

@[simp]
theorem sphereSkewTangentDiffeomorph_fst {m : ℕ∞ω} {A : Fin n → E →L[ℝ] E}
    (hskew : ∀ i x y, ⟪A i x, y⟫_ℝ = -⟪x, A i y⟫_ℝ)
    (hsq : ∀ i x, A i (A i x) = -x)
    (hanti : ∀ i j, i ≠ j → ∀ x, A i (A j x) + A j (A i x) = 0)
    (p : TangentBundle (𝓡 n) (sphere (0 : E) 1)) :
    (sphereSkewTangentDiffeomorph (m := m) hskew hsq hanti p).1 = p.proj :=
  orthonormalFrameDiffeomorph_fst _ _ _ p

@[simp]
theorem sphereSkewTangentDiffeomorph_snd_apply {m : ℕ∞ω} {A : Fin n → E →L[ℝ] E}
    (hskew : ∀ i x y, ⟪A i x, y⟫_ℝ = -⟪x, A i y⟫_ℝ)
    (hsq : ∀ i x, A i (A i x) = -x)
    (hanti : ∀ i j, i ≠ j → ∀ x, A i (A j x) + A j (A i x) = 0)
    (x : sphere (0 : E) 1) (w : TangentSpace (𝓡 n) x) (i : Fin n) :
    (sphereSkewTangentDiffeomorph (m := m) hskew hsq hanti ⟨x, w⟩).2 i =
      ⟪A i (x : E), mvfderiv (𝓡 n) ((↑) : sphere (0 : E) 1 → E) x w⟫_ℝ := by
  rw [sphereSkewTangentDiffeomorph_def, orthonormalFrameDiffeomorph_snd_apply,
    (A i).inner_sphereSkewField_left (hskew i)]

/-- The inverse of `TauCeti.sphereSkewTangentDiffeomorph` expands coordinates in `ℝⁿ` along the
skew-symmetric tangent frame `(A i).sphereSkewField`. -/
@[simp]
theorem sphereSkewTangentDiffeomorph_symm_eq_sum {m : ℕ∞ω} {A : Fin n → E →L[ℝ] E}
    (hskew : ∀ i x y, ⟪A i x, y⟫_ℝ = -⟪x, A i y⟫_ℝ)
    (hsq : ∀ i x, A i (A i x) = -x)
    (hanti : ∀ i j, i ≠ j → ∀ x, A i (A j x) + A j (A i x) = 0)
    (x : sphere (0 : E) 1) (y : EuclideanSpace ℝ (Fin n)) :
    (sphereSkewTangentDiffeomorph (m := m) hskew hsq hanti).symm (x, y) =
      ⟨x, ∑ i, y i • (A i).sphereSkewField (hskew i) x⟩ :=
  orthonormalFrameDiffeomorph_symm_eq_sum _ _ _ x y

@[simp]
theorem norm_sphereSkewTangentDiffeomorph_snd {m : ℕ∞ω} {A : Fin n → E →L[ℝ] E}
    (hskew : ∀ i x y, ⟪A i x, y⟫_ℝ = -⟪x, A i y⟫_ℝ)
    (hsq : ∀ i x, A i (A i x) = -x)
    (hanti : ∀ i j, i ≠ j → ∀ x, A i (A j x) + A j (A i x) = 0)
    (p : TangentBundle (𝓡 n) (sphere (0 : E) 1)) :
    ‖(sphereSkewTangentDiffeomorph (m := m) hskew hsq hanti p).2‖ = ‖p.snd‖ :=
  norm_orthonormalFrameDiffeomorph_snd _ _ _ p

/-- `TauCeti.sphereSkewTangentDiffeomorph` preserves the round inner product on every tangent
space. -/
theorem inner_sphereSkewTangentDiffeomorph_snd {m : ℕ∞ω} {A : Fin n → E →L[ℝ] E}
    (hskew : ∀ i x y, ⟪A i x, y⟫_ℝ = -⟪x, A i y⟫_ℝ)
    (hsq : ∀ i x, A i (A i x) = -x)
    (hanti : ∀ i j, i ≠ j → ∀ x, A i (A j x) + A j (A i x) = 0)
    (x : sphere (0 : E) 1) (w₁ w₂ : TangentSpace (𝓡 n) x) :
    ⟪(sphereSkewTangentDiffeomorph (m := m) hskew hsq hanti ⟨x, w₁⟩).2,
      (sphereSkewTangentDiffeomorph (m := m) hskew hsq hanti ⟨x, w₂⟩).2⟫_ℝ = ⟪w₁, w₂⟫_ℝ :=
  inner_orthonormalFrameDiffeomorph_snd _ _ _ x w₁ w₂

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

/-- `TauCeti.sphereZeroTangentDiffeomorph` unfolds to `TauCeti.sphereSkewTangentDiffeomorph` on the
empty operator family `Fin.elim0`. -/
theorem sphereZeroTangentDiffeomorph_def {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [Fact (finrank ℝ E = 0 + 1)] (m : ℕ∞ω) :
    sphereZeroTangentDiffeomorph (E := E) m =
      sphereSkewTangentDiffeomorph (A := Fin.elim0)
        (fun i ↦ i.elim0) (fun i ↦ i.elim0) (fun i ↦ i.elim0) :=
  (rfl)

@[simp]
theorem sphereZeroTangentDiffeomorph_apply {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [Fact (finrank ℝ E = 0 + 1)] (m : ℕ∞ω)
    (p : TangentBundle (𝓡 0) (sphere (0 : E) 1)) :
    sphereZeroTangentDiffeomorph m p = (p.proj, 0) :=
  Prod.ext (by simp [sphereZeroTangentDiffeomorph_def]) (Subsingleton.elim _ _)

@[simp]
theorem sphereZeroTangentDiffeomorph_symm_apply {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [Fact (finrank ℝ E = 0 + 1)] (m : ℕ∞ω)
    (x : sphere (0 : E) 1) (y : EuclideanSpace ℝ (Fin 0)) :
    (sphereZeroTangentDiffeomorph m).symm (x, y) = ⟨x, 0⟩ := by
  simp [sphereZeroTangentDiffeomorph_def]

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
  obtain ⟨A, hskew, hsq, hanti⟩ := exists_skew_sq_neg_id_anticommute_clm
    hn (Fact.out (p := finrank ℝ E = n + 1))
  exact ⟨fun i ↦ (A i).sphereSkewField (hskew i),
    fun i ↦ (A i).contMDiff_sphereSkewField (hskew i),
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
  obtain ⟨A, hskew, hsq, hanti⟩ := exists_skew_sq_neg_id_anticommute_clm
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
  obtain ⟨A, hskew, hsq, hanti⟩ := exists_skew_sq_neg_id_anticommute_clm
    hn (Fact.out (p := finrank ℝ E = n + 1))
  let c := EuclideanSpace.basisFun (Fin n) ℝ
  let d : ∀ x : sphere (0 : E) 1, OrthonormalBasis (Fin n) ℝ (TangentSpace (𝓡 n) x) :=
    sphereSkewOrthonormalBasis hskew hsq hanti
  have hd : ∀ i : Fin n, ContMDiff (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) m
      (fun x : sphere (0 : E) 1 ↦ TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) x (d x i)) :=
    fun i ↦ by simpa only [d, sphereSkewOrthonormalBasis_apply] using
      (A i).contMDiff_sphereSkewField (m := m) (hskew i)
  have hcont : ∀ i : Fin n, Continuous fun b : (univ : Set (sphere (0 : E) 1)) ↦
      TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) (b : sphere (0 : E) 1) (d b.val i) :=
    fun i ↦ (hd i).continuous.comp continuous_subtypeVal
  refine ⟨c.bundleTrivialization (E := TangentSpace (𝓡 n)) isOpen_univ (fun b ↦ d b.val) hcont,
    inferInstance, c.bundleTrivialization_baseSet (E := TangentSpace (𝓡 n)) isOpen_univ _ hcont,
    fun x v ↦ ?_,
    c.bundleTrivialization_univ_mem_maximalAtlas (E := TangentSpace (𝓡 n)) d hd⟩
  rw [c.bundleTrivialization_univ_apply (n := m) (E := TangentSpace (𝓡 n)) d hd ⟨x, v⟩,
    c.norm_totalSpaceDiffeomorph_snd (n := m) (E := TangentSpace (𝓡 n)) d hd ⟨x, v⟩]

/-- For `n ∈ {0, 1, 3, 7}` and any regularity `m : ℕ∞ω`, the tangent bundle of the standard sphere
`sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1` is `C^m` diffeomorphic to
`sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 × EuclideanSpace ℝ (Fin n)`. -/
theorem nonempty_euclideanSphere_tangentBundle_diffeomorph {n : ℕ} (m : ℕ∞ω)
    (hn : n = 0 ∨ n = 1 ∨ n = 3 ∨ n = 7) :
    Nonempty (TangentBundle (𝓡 n) (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)
      ≃ₘ^m⟮(𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)),
        (𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))⟯
      sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 × EuclideanSpace ℝ (Fin n)) := by
  have := finrank_euclideanSpace_fin_succ_fact n
  exact nonempty_sphere_tangentBundle_diffeomorph m hn

/-- **Parallelizability of `S⁰`, `S¹`, `S³`, and `S⁷`.** For `n ∈ {0, 1, 3, 7}` and any regularity
`m : ℕ∞ω` (in particular `∞` and `ω`), the unit sphere `sphere (0 : E) 1` of any
`(n + 1)`-dimensional real inner product space `E` admits `n` global `C^m` tangent vector fields
that are linearly independent at every point. -/
theorem exists_linearIndependent_contMDiff_sphere_tangentFrame
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
    [Fact (finrank ℝ E = n + 1)] (m : ℕ∞ω) (hn : n = 0 ∨ n = 1 ∨ n = 3 ∨ n = 7) :
    ∃ v : Fin n → (x : sphere (0 : E) 1) → TangentSpace (𝓡 n) x,
      (∀ i, ContMDiff (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) m
        (fun x ↦ (⟨x, v i x⟩ : TangentBundle (𝓡 n) (sphere (0 : E) 1)))) ∧
      ∀ x, LinearIndependent ℝ (fun i ↦ v i x) := by
  obtain ⟨v, hv, horth⟩ := exists_orthonormal_contMDiff_sphere_tangentFrame (E := E) m hn
  exact ⟨v, hv, fun x ↦ (horth x).linearIndependent⟩

/-- **Parallelizability of the standard spheres `S⁰`, `S¹`, `S³`, and `S⁷`.** For `n ∈ {0, 1, 3, 7}`
and any regularity `m : ℕ∞ω` (in particular `∞` and `ω`), the standard sphere
`sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1` admits `n` global `C^m` tangent vector fields that
are linearly independent at every point. -/
theorem exists_linearIndependent_contMDiff_euclideanSphere_tangentFrame {n : ℕ} (m : ℕ∞ω)
    (hn : n = 0 ∨ n = 1 ∨ n = 3 ∨ n = 7) :
    ∃ v : Fin n → (x : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) → TangentSpace (𝓡 n) x,
      (∀ i, ContMDiff (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) m
        (fun x ↦ (⟨x, v i x⟩ :
          TangentBundle (𝓡 n) (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)))) ∧
      ∀ x, LinearIndependent ℝ (fun i ↦ v i x) := by
  have := finrank_euclideanSpace_fin_succ_fact n
  exact exists_linearIndependent_contMDiff_sphere_tangentFrame m hn

end Parallelizable

end TauCeti

end
