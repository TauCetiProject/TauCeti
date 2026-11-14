/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Sphere.Gradient
public import TauCeti.Geometry.Manifold.VectorBundle.FrameTrivialization
public import TauCeti.Geometry.Manifold.VectorBundle.Hom
public import TauCeti.LinearAlgebra.CliffordAlgebra.Module.Euclidean
import Mathlib.Analysis.InnerProductSpace.Calculus
import TauCeti.Geometry.Manifold.VectorBundle.LocalFrame.Orthonormal
import TauCeti.Geometry.Manifold.VectorBundle.Scalar
import TauCeti.Geometry.Manifold.VectorBundle.Translate
import TauCeti.Geometry.Manifold.VectorBundle.Trivial

/-!
# Orthonormal Clifford tangent frames and parallelizability of `S⁰`, `S¹`, `S³`, and `S⁷`

Let `E` be a real inner product space of dimension `n + 1` and `sphere (0 : E) 1` its unit sphere
equipped with the analytic round Riemannian metric (`TauCeti.sphereRoundMetric`). At each point `x`
of the sphere, `TauCeti.sphereTangentEquiv x` identifies `TangentSpace (𝓡 n) x` isometrically with
the hyperplane `(ℝ ∙ (x : E))ᗮ` in `E`.

We first establish full `C^m` regularity (for every `m : ℕ∞ω`, including real-analyticity `m = ω`)
in both directions of this ambient-tangent identification:
* `TauCeti.contMDiff_coe_sphereTangentEquiv`: reading a tangent vector in `E` via
  `sphereTangentEquiv` is `C^m` on `TangentBundle (𝓡 n) (sphere (0 : E) 1)`.
* `TauCeti.sphereTangentEquiv_symm_eq_sum_mgradient`: expanding a vector `w ∈ (ℝ ∙ (x : E))ᗮ` in
  any finite orthonormal basis `b` of `E` expresses `(sphereTangentEquiv x).symm w` as the linear
  combination `∑ j, ⟪b j, w⟫_ℝ • ∇(q ↦ ⟪b j, q⟫_ℝ)(x)` of round height gradients.
* `TauCeti.contMDiff_sphereTangentEquiv_symm`: any `C^m` map `u : M → E` orthogonal to a `C^m` base
  map `f : M → sphere (0 : E) 1` lifts via `(sphereTangentEquiv (f ·)).symm` to a `C^m` map into
  `TangentBundle (𝓡 n) (sphere (0 : E) 1)`.

Given a `TauCeti.SkewAdjointCliffordSystem ι E` — an `ι`-indexed family of pairwise anticommuting
skew-adjoint complex structures `A_i` on `E` — evaluating `(sphereTangentEquiv x).symm` on `A_i x`
defines analytic unit vector fields `S.tangentField i` on `sphere (0 : E) 1` that are pointwise
orthonormal (`S.orthonormal_tangentField`). When `|ι| = n`, they form a global `C^m` orthonormal
frame (`S.isLocalFrameOn_tangentField`), inducing:
* a compatible global linear trivialization `S.tangentTrivialization m` in the `C^m` maximal atlas
  of the tangent bundle (`S.tangentTrivialization_mem_maximalAtlas`);
* an explicit `C^m` diffeomorphism `S.tangentBundleDiffeomorph m` from
  `TangentBundle (𝓡 n) (sphere (0 : E) 1)` onto `sphere (0 : E) 1 × EuclideanSpace ℝ (Fin n)` with
  inner-product forward coordinates `v ↦ (i ↦ ⟪S.tangentField i x, v⟫_ℝ)` and linear-combination
  inverse `c ↦ ∑ i, c_i • S.tangentField i x`;
* the corresponding `C^m` bundle diffeomorphism `S.tangentBundleTrivialDiffeomorph m` onto the
  total space of `Bundle.Trivial (sphere (0 : E) 1) (EuclideanSpace ℝ (Fin n))`.

Combining these constructions with `TauCeti.nonempty_skewAdjointCliffordSystem_of_eq` (from the
real Clifford algebra classification of `Cliff(0, 1)`, `Cliff(0, 3)`, and `Cliff(0, 7)`) yields
global analytic orthonormal tangent frames and tangent-bundle trivializations on the unit sphere in
dimensions `n ∈ {0, 1, 3, 7}`, establishing the constructive direction of the parallelizability
characterization of spheres
(`TauCeti.exists_linearIndependent_contMDiff_tangentSpace_sphere_of_eq`).

## Main definitions

* `TauCeti.SkewAdjointCliffordSystem.tangentField`: the `i`-th Clifford tangent vector field
  `x ↦ (sphereTangentEquiv x).symm (S.orthogonalVec i x)` on `sphere (0 : E) 1`.
* `TauCeti.SkewAdjointCliffordSystem.tangentOrthonormalBasis`: the pointwise `OrthonormalBasis` of
  `TangentSpace (𝓡 n) x` induced when `Fintype.card ι = n`.
* `TauCeti.SkewAdjointCliffordSystem.tangentTrivialization`: the global `Bundle.Trivialization` of
  `TangentSpace (𝓡 n)` associated with a `Fin n`-indexed `SkewAdjointCliffordSystem`.
* `TauCeti.SkewAdjointCliffordSystem.tangentBundleDiffeomorph`: the `C^m` diffeomorphism
  `TangentBundle (𝓡 n) (sphere (0 : E) 1) ≃ₘ^m sphere (0 : E) 1 × EuclideanSpace ℝ (Fin n)`.
* `TauCeti.SkewAdjointCliffordSystem.tangentBundleTrivialDiffeomorph`: the `C^m` bundle
  diffeomorphism onto `TotalSpace (EuclideanSpace ℝ (Fin n)) (Bundle.Trivial _ _)`.

## Main results

* `TauCeti.contMDiff_coe_sphereTangentEquiv` and `TauCeti.contMDiff_sphereTangentEquiv_symm`:
  `C^m` regularity (for all `m : ℕ∞ω`) of `sphereTangentEquiv` and its inverse.
* `TauCeti.SkewAdjointCliffordSystem.contMDiff_tangentField` and
  `TauCeti.SkewAdjointCliffordSystem.orthonormal_tangentField`: `S.tangentField` is a `C^m`
  pointwise orthonormal family of tangent vector fields.
* `TauCeti.SkewAdjointCliffordSystem.isLocalFrameOn_tangentField`: when `Fintype.card ι = n`,
  `S.tangentField` is a global `C^m` frame on `Set.univ`.
* `TauCeti.exists_orthonormal_contMDiff_tangentSpace_sphere_of_eq`,
  `TauCeti.exists_linearIndependent_contMDiff_tangentSpace_sphere_of_eq`, and
  `TauCeti.nonempty_tangentBundleDiffeomorph_sphere_of_eq`: global `C^m` orthonormal frames and
  tangent-bundle trivializations on `Sⁿ` for `n ∈ {0, 1, 3, 7}`.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §§4–5.
* A. Hatcher, *Vector Bundles and K-Theory*, §1.1.
* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed. (2018), Chapter 2.
-/

public section

noncomputable section

open Bundle Metric Module Set
open scoped ContDiff InnerProductSpace Manifold

namespace TauCeti

/-! ### Regularity of `sphereTangentEquiv` and its inverse -/

section AmbientTangent

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
  [Fact (finrank ℝ E = n + 1)]

/-- Reading a tangent vector to the unit sphere in the ambient inner product space `E` via
`sphereTangentEquiv` is `C^m` for every `m : ℕ∞ω` (including `m = ω`). -/
theorem contMDiff_coe_sphereTangentEquiv {m : ℕ∞ω} :
    ContMDiff (𝓡 n).tangent 𝓘(ℝ, E) m
      (fun p : TangentBundle (𝓡 n) (sphere (0 : E) 1) ↦
        (sphereTangentEquiv p.proj p.2 : E)) := by
  have htan : ContMDiff (𝓡 n).tangent 𝓘(ℝ, E).tangent m
      (tangentMap (𝓡 n) 𝓘(ℝ, E) ((↑) : sphere (0 : E) 1 → E)) :=
    (contMDiff_coe_sphere (E := E) (n := n) (m := ω)).contMDiff_tangentMap le_top
  exact ((contMDiff_snd_tangentBundle_modelSpace E 𝓘(ℝ, E)).comp htan).congr fun p ↦
    coe_sphereTangentEquiv_apply p.proj p.2

/-- Expanding `w ∈ (ℝ ∙ (x : E))ᗮ` in any finite orthonormal basis `b` of `E` expresses its
corresponding tangent vector `(sphereTangentEquiv x).symm w` as a linear combination of the round
gradients of the height functions `q ↦ ⟪b j, q⟫_ℝ`. -/
theorem sphereTangentEquiv_symm_eq_sum_mgradient {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ E) (x : sphere (0 : E) 1) (w : (ℝ ∙ (x : E))ᗮ) :
    (sphereTangentEquiv x).symm w =
      ∑ j : ι, ⟪b j, (w : E)⟫_ℝ •
        Manifold.mgradient (𝓡 n) (fun q : sphere (0 : E) 1 ↦ ⟪b j, (q : E)⟫_ℝ) x := by
  apply injective_mvfderiv_subtypeVal_sphere x
  rw [mvfderiv_subtypeVal_sphere_eq_sphereTangentEquiv, LinearIsometryEquiv.apply_symm_apply,
    map_sum]
  have hwx : ⟪(w : E), (x : E)⟫_ℝ = 0 := by
    rw [real_inner_comm]
    exact Submodule.mem_orthogonal_singleton_iff_inner_right.mp w.2
  calc
    (w : E) = (∑ j : ι, ⟪b j, (w : E)⟫_ℝ • b j) -
        (∑ j : ι, ⟪(w : E), b j⟫_ℝ * ⟪b j, (x : E)⟫_ℝ) • (x : E) := by
      rw [b.sum_repr', b.sum_inner_mul_inner, hwx, zero_smul, sub_zero]
    _ = ∑ j : ι, (⟪b j, (w : E)⟫_ℝ • b j -
        (⟪b j, (w : E)⟫_ℝ * ⟪b j, (x : E)⟫_ℝ) • (x : E)) := by
      rw [Finset.sum_smul, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      rw [real_inner_comm (w : E) (b j)]
    _ = ∑ j : ι, mvfderiv (𝓡 n) ((↑) : sphere (0 : E) 1 → E) x
        (⟪b j, (w : E)⟫_ℝ •
          Manifold.mgradient (𝓡 n) (fun q : sphere (0 : E) 1 ↦ ⟪b j, (q : E)⟫_ℝ) x) := by
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      rw [ContinuousLinearMap.map_smul, mvfderiv_coe_mgradient_inner_coe_sphere, smul_sub,
        smul_smul]

/-- Any `C^m` ambient map `u : M → E` orthogonal to a `C^m` base map `f : M → sphere (0 : E) 1`
lifts via `(sphereTangentEquiv (f ·)).symm` to a `C^m` map into the tangent bundle of the sphere,
for every `m : ℕ∞ω` (including `m = ω`). -/
theorem contMDiff_sphereTangentEquiv_symm {E' H' M : Type*}
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
    {J : ModelWithCorners ℝ E' H'} [TopologicalSpace M] [ChartedSpace H' M]
    {m : ℕ∞ω} {f : M → sphere (0 : E) 1} {u : M → E}
    (hf : ContMDiff J (𝓡 n) m f) (hu_diff : ContMDiff J 𝓘(ℝ, E) m u)
    (hu : ∀ z, u z ∈ (ℝ ∙ (f z : E))ᗮ) :
    ContMDiff J (𝓡 n).tangent m
      (fun z ↦ (⟨f z, (sphereTangentEquiv (f z)).symm ⟨u z, hu z⟩⟩ :
        TangentBundle (𝓡 n) (sphere (0 : E) 1))) := by
  have : FiniteDimensional ℝ E := .of_fact_finrank_eq_succ n
  have : IsManifold (𝓡 n) (ω + 1) (sphere (0 : E) 1) := by
    simpa only [show (ω : ℕ∞ω) + 1 = ω by simp] using
      (inferInstance : IsManifold (𝓡 n) ω (sphere (0 : E) 1))
  let b := stdOrthonormalBasis ℝ E
  have hgrad (j : Fin (finrank ℝ E)) :
      ContMDiff (𝓡 n) (𝓡 n).tangent m
        (fun q : sphere (0 : E) 1 ↦
          (⟨q, Manifold.mgradient (𝓡 n) (fun r : sphere (0 : E) 1 ↦ ⟪b j, (r : E)⟫_ℝ) q⟩ :
            TangentBundle (𝓡 n) (sphere (0 : E) 1))) := by
    have hh : ContMDiff (𝓡 n) 𝓘(ℝ) (ω + 1) (fun r : sphere (0 : E) 1 ↦ ⟪b j, (r : E)⟫_ℝ) :=
      ((innerSL ℝ (b j)).contDiff.contMDiff.comp
        (contMDiff_coe_sphere (E := E) (n := n) (m := ω))).of_le le_top
    exact (Manifold.contMDiff_mgradient (I := 𝓡 n) (n := ω) hh).of_le le_top
  have hsum := ContMDiff.sum_sectionAlong Finset.univ
    (fun j z ↦ ⟪b j, u z⟫_ℝ •
      Manifold.mgradient (𝓡 n) (fun r : sphere (0 : E) 1 ↦ ⟪b j, (r : E)⟫_ℝ) (f z)) hf
    fun j _ ↦ (((innerSL ℝ (b j)).contDiff.contMDiff.comp hu_diff).smul_totalSpace
      ((hgrad j).comp hf))
  exact hsum.congr fun z ↦
    congrArg (TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) (f z))
      (sphereTangentEquiv_symm_eq_sum_mgradient (n := n) b (f z) ⟨u z, hu z⟩)

/-- A `C^m` ambient map `u : sphere (0 : E) 1 → E` satisfying `u x ∈ (ℝ ∙ (x : E))ᗮ` at every
point `x` defines a `C^m` tangent vector field on `sphere (0 : E) 1`. -/
theorem contMDiff_section_sphereTangentEquiv_symm {m : ℕ∞ω} {u : sphere (0 : E) 1 → E}
    (hu_diff : ContMDiff (𝓡 n) 𝓘(ℝ, E) m u)
    (hu : ∀ x : sphere (0 : E) 1, u x ∈ (ℝ ∙ (x : E))ᗮ) :
    ContMDiff (𝓡 n) (𝓡 n).tangent m
      (fun x : sphere (0 : E) 1 ↦
        (⟨x, (sphereTangentEquiv x).symm ⟨u x, hu x⟩⟩ :
          TangentBundle (𝓡 n) (sphere (0 : E) 1))) :=
  contMDiff_sphereTangentEquiv_symm contMDiff_id hu_diff hu

end AmbientTangent

/-! ### Clifford tangent vector fields and global smooth trivializations -/

namespace SkewAdjointCliffordSystem

section GeneralIndex

variable {ι E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (S : SkewAdjointCliffordSystem ι E) {n : ℕ} [Fact (finrank ℝ E = n + 1)]

/-- The `i`-th Clifford tangent vector field on the unit sphere `sphere (0 : E) 1`, obtained by
transporting `S.op i x ∈ (ℝ ∙ (x : E))ᗮ` to `TangentSpace (𝓡 n) x` via
`(sphereTangentEquiv x).symm`. -/
def tangentField (i : ι) (x : sphere (0 : E) 1) : TangentSpace (𝓡 n) x :=
  (sphereTangentEquiv x).symm (S.orthogonalVec i (x : E))

/-- `sphereTangentEquiv x` maps `S.tangentField i x` back to `S.orthogonalVec i x`. -/
@[simp]
theorem sphereTangentEquiv_tangentField (i : ι) (x : sphere (0 : E) 1) :
    sphereTangentEquiv (n := n) x (S.tangentField i x) = S.orthogonalVec i (x : E) :=
  (sphereTangentEquiv x).apply_symm_apply _

/-- In the ambient space `E`, `sphereTangentEquiv x (S.tangentField i x)` equals `S.op i x`. -/
theorem coe_sphereTangentEquiv_tangentField (i : ι) (x : sphere (0 : E) 1) :
    (sphereTangentEquiv (n := n) x (S.tangentField i x) : E) = S.op i (x : E) := by
  rw [sphereTangentEquiv_tangentField, coe_orthogonalVec]

/-- Pushing `S.tangentField i x` forward along the inclusion of the sphere into `E` yields
`S.op i x`. -/
theorem mvfderiv_coe_tangentField (i : ι) (x : sphere (0 : E) 1) :
    mvfderiv (𝓡 n) ((↑) : sphere (0 : E) 1 → E) x (S.tangentField i x) = S.op i (x : E) := by
  rw [mvfderiv_subtypeVal_sphere_eq_sphereTangentEquiv, coe_sphereTangentEquiv_tangentField]

/-- Each Clifford tangent vector field `S.tangentField i` is `C^m` for every `m : ℕ∞ω`
(in particular smooth and real-analytic). -/
theorem contMDiff_tangentField {m : ℕ∞ω} (i : ι) :
    ContMDiff (𝓡 n) (𝓡 n).tangent m
      (fun x : sphere (0 : E) 1 ↦
        (⟨x, S.tangentField i x⟩ : TangentBundle (𝓡 n) (sphere (0 : E) 1))) := by
  have hop : ContMDiff (𝓡 n) 𝓘(ℝ, E) m (fun x : sphere (0 : E) 1 ↦ S.op i (x : E)) :=
    ((S.isometryEquiv i).contDiff.contMDiff.comp contMDiff_coe_sphere).congr fun x ↦
      (S.coe_isometryEquiv_apply i (x : E)).symm
  have ho (x : sphere (0 : E) 1) :
      S.orthogonalVec i (x : E) = ⟨S.op i (x : E), S.mem_orthogonal_span_singleton i (x : E)⟩ :=
    Subtype.ext (S.coe_orthogonalVec i (x : E))
  exact (contMDiff_section_sphereTangentEquiv_symm hop fun x ↦
    S.mem_orthogonal_span_singleton i (x : E)).congr fun x ↦ by
      rw [tangentField, ho]

/-- The round inner product of `S.tangentField i x` with any tangent vector `v` equals the ambient
inner product of `S.op i x` with `sphereTangentEquiv x v`. -/
theorem inner_tangentField_left (i : ι) (x : sphere (0 : E) 1) (v : TangentSpace (𝓡 n) x) :
    ⟪S.tangentField i x, v⟫_ℝ = ⟪S.op i (x : E), (sphereTangentEquiv x v : E)⟫_ℝ := by
  rw [inner_tangentSpace_sphere, mvfderiv_coe_tangentField,
    mvfderiv_subtypeVal_sphere_eq_sphereTangentEquiv]

/-- Symmetric form of `inner_tangentField_left`. -/
theorem inner_tangentField_right (i : ι) (x : sphere (0 : E) 1) (v : TangentSpace (𝓡 n) x) :
    ⟪v, S.tangentField i x⟫_ℝ = ⟪(sphereTangentEquiv x v : E), S.op i (x : E)⟫_ℝ := by
  rw [real_inner_comm, inner_tangentField_left, real_inner_comm]

/-- Every Clifford tangent vector field has unit round norm at every point of the sphere. -/
theorem norm_tangentField (i : ι) (x : sphere (0 : E) 1) :
    ‖S.tangentField (n := n) i x‖ = 1 := by
  rw [norm_tangentSpace_sphere, mvfderiv_coe_tangentField, S.norm_op, norm_eq_of_mem_sphere]

/-- Distinct Clifford tangent vector fields are pointwise orthogonal in the round metric. -/
theorem inner_tangentField_ne {i j : ι} (hij : i ≠ j) (x : sphere (0 : E) 1) :
    ⟪S.tangentField (n := n) i x, S.tangentField (n := n) j x⟫_ℝ = 0 := by
  rw [inner_tangentField_left, coe_sphereTangentEquiv_tangentField]
  exact S.inner_op_ne hij (x : E)

/-- At every point `x` of the unit sphere, the vectors `S.tangentField i x` form an orthonormal
family in `TangentSpace (𝓡 n) x` for the round metric. -/
theorem orthonormal_tangentField (x : sphere (0 : E) 1) :
    Orthonormal ℝ fun i ↦ S.tangentField (n := n) i x :=
  ⟨fun i ↦ S.norm_tangentField i x, fun {_ _} hij ↦ S.inner_tangentField_ne hij x⟩

/-- At every point `x` of the unit sphere, the vectors `S.tangentField i x` are linearly
independent in `TangentSpace (𝓡 n) x`. -/
theorem linearIndependent_tangentField (x : sphere (0 : E) 1) :
    LinearIndependent ℝ fun i ↦ S.tangentField (n := n) i x :=
  (S.orthonormal_tangentField x).linearIndependent

/-- When `Fintype.card ι = n`, the vectors `S.tangentField i x` form an orthonormal basis of
`TangentSpace (𝓡 n) x` at every point `x` of the unit sphere. -/
def tangentOrthonormalBasis [Fintype ι] (hcard : Fintype.card ι = n)
    (x : sphere (0 : E) 1) : OrthonormalBasis ι ℝ (TangentSpace (𝓡 n) x) :=
  (S.orthonormalBasisOrthogonal
    ((Fact.out : finrank ℝ E = n + 1).trans (congrArg (· + 1) hcard.symm)) x).map
    (sphereTangentEquiv x).symm

/-- The `i`-th vector of `S.tangentOrthonormalBasis` at `x` is `S.tangentField i x`. -/
@[simp]
theorem tangentOrthonormalBasis_apply [Fintype ι] (hcard : Fintype.card ι = n)
    (x : sphere (0 : E) 1) (i : ι) :
    S.tangentOrthonormalBasis hcard x i = S.tangentField i x := by
  simp [tangentOrthonormalBasis, tangentField]

/-- Coordinates in `S.tangentOrthonormalBasis` are round inner products with `S.tangentField`. -/
@[simp]
theorem tangentOrthonormalBasis_repr_apply [Fintype ι] (hcard : Fintype.card ι = n)
    (x : sphere (0 : E) 1) (v : TangentSpace (𝓡 n) x) (i : ι) :
    (S.tangentOrthonormalBasis hcard x).repr v i = ⟪S.tangentField i x, v⟫_ℝ := by
  rw [OrthonormalBasis.repr_apply_apply, tangentOrthonormalBasis_apply]

/-- Reconstructing a tangent vector from its coordinates in `S.tangentOrthonormalBasis` gives the
linear combination `∑ i, c.ofLp i • S.tangentField i x`. -/
theorem tangentOrthonormalBasis_repr_symm_apply [Fintype ι] (hcard : Fintype.card ι = n)
    (x : sphere (0 : E) 1) (c : EuclideanSpace ℝ ι) :
    (S.tangentOrthonormalBasis hcard x).repr.symm c =
      ∑ i : ι, c.ofLp i • S.tangentField i x := by
  rw [← OrthonormalBasis.sum_repr_symm]
  exact Finset.sum_congr rfl fun i _ ↦ by rw [tangentOrthonormalBasis_apply]

/-- When `Fintype.card ι = n`, `S.tangentField` is a global `C^m` frame on `sphere (0 : E) 1` for
every `m : ℕ∞ω` (in the sense of `IsLocalFrameOn` on `Set.univ`). -/
theorem isLocalFrameOn_tangentField [Fintype ι] (hcard : Fintype.card ι = n) (m : ℕ∞ω) :
    IsLocalFrameOn (𝓡 n) (EuclideanSpace ℝ (Fin n)) m (S.tangentField (n := n)) univ where
  linearIndependent {_} _ := S.linearIndependent_tangentField _
  generating {x} _ := by
    have hfun : ⇑(S.tangentOrthonormalBasis hcard x).toBasis =
        fun i ↦ S.tangentField (n := n) i x := by
      ext i
      rw [OrthonormalBasis.coe_toBasis, tangentOrthonormalBasis_apply]
    rw [← hfun]
    exact (S.tangentOrthonormalBasis hcard x).toBasis.span_eq.ge
  contMDiffOn i := (S.contMDiff_tangentField i).contMDiffOn

/-- The `i`-th frame coefficient of a tangent vector `v` in `S.isLocalFrameOn_tangentField` is its
round inner product with `S.tangentField i x`. -/
@[simp]
theorem coeff_isLocalFrameOn_tangentField [Fintype ι] (hcard : Fintype.card ι = n) (m : ℕ∞ω)
    (i : ι) (x : sphere (0 : E) 1) (v : TangentSpace (𝓡 n) x) :
    (S.isLocalFrameOn_tangentField hcard m).coeff i x v = ⟪S.tangentField i x, v⟫_ℝ :=
  (S.isLocalFrameOn_tangentField hcard m).coeff_eq_inner (mem_univ x)
    (S.orthonormal_tangentField x) i v

end GeneralIndex

section FinIndex

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
  [Fact (finrank ℝ E = n + 1)] (S : SkewAdjointCliffordSystem (Fin n) E)

/-- The global `Bundle.Trivialization` of `TangentSpace (𝓡 n)` over `sphere (0 : E) 1` defined by
a `Fin n`-indexed `SkewAdjointCliffordSystem` and the standard orthonormal basis of
`EuclideanSpace ℝ (Fin n)`. -/
def tangentTrivialization (m : ℕ∞ω) :
    Trivialization (EuclideanSpace ℝ (Fin n))
      (π (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n) : sphere (0 : E) 1 → Type _)) :=
  (S.isLocalFrameOn_tangentField (Fintype.card_fin n) m).trivialization isOpen_univ
    (EuclideanSpace.basisFun (Fin n) ℝ).toBasis

/-- `S.tangentTrivialization m` is defined over the entire unit sphere `Set.univ`. -/
@[simp]
theorem baseSet_tangentTrivialization (m : ℕ∞ω) : (S.tangentTrivialization m).baseSet = univ := by
  rw [tangentTrivialization, IsLocalFrameOn.baseSet_trivialization]

/-- `S.tangentTrivialization m` is fiberwise `ℝ`-linear. -/
instance isLinear_tangentTrivialization (m : ℕ∞ω) : (S.tangentTrivialization m).IsLinear ℝ := by
  delta tangentTrivialization
  infer_instance

/-- For every `m : ℕ∞ω`, `S.tangentTrivialization m` belongs to the `C^m` maximal atlas of
compatible fiberwise-linear trivializations of `TangentBundle (𝓡 n) (sphere (0 : E) 1)`. -/
theorem tangentTrivialization_mem_maximalAtlas (m : ℕ∞ω) :
    (S.tangentTrivialization m).toOpenPartialHomeomorph ∈
      (contMDiffFiberwiseLinear (sphere (0 : E) 1) (EuclideanSpace ℝ (Fin n)) (𝓡 n) m).maximalAtlas
        (TangentBundle (𝓡 n) (sphere (0 : E) 1)) :=
  have : IsManifold (𝓡 n) (m + 1) (sphere (0 : E) 1) :=
    IsManifold.of_le (le_top : m + 1 ≤ ω)
  (S.isLocalFrameOn_tangentField (Fintype.card_fin n) m).trivialization_mem_maximalAtlas
    isOpen_univ (EuclideanSpace.basisFun (Fin n) ℝ).toBasis

/-- Inverse formula for `S.tangentTrivialization m`: a coordinate vector `c` is mapped to
`∑ i, c_i • S.tangentField i x`. -/
@[simp]
theorem tangentTrivialization_symm_apply (m : ℕ∞ω) (x : sphere (0 : E) 1)
    (c : EuclideanSpace ℝ (Fin n)) :
    (S.tangentTrivialization m).symm x c = ∑ i : Fin n, c.ofLp i • S.tangentField i x := by
  rw [tangentTrivialization, IsLocalFrameOn.trivialization_symm_apply _ isOpen_univ _ (mem_univ x)]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [OrthonormalBasis.coe_toBasis_repr_apply, EuclideanSpace.basisFun_repr]

/-- On fibers, `S.tangentTrivialization m` sends a tangent vector `v` at `x` to its coordinate
vector `i ↦ ⟪S.tangentField i x, v⟫_ℝ` in `EuclideanSpace ℝ (Fin n)`. -/
@[simp]
theorem tangentTrivialization_apply (m : ℕ∞ω) (x : sphere (0 : E) 1) (v : TangentSpace (𝓡 n) x) :
    S.tangentTrivialization m ⟨x, v⟩ =
      (x, (S.tangentOrthonormalBasis (Fintype.card_fin n) x).repr v) := by
  have hv :
      (S.tangentTrivialization m).symm x
        ((S.tangentOrthonormalBasis (Fintype.card_fin n) x).repr v) = v := by
    rw [S.tangentTrivialization_symm_apply, ← S.tangentOrthonormalBasis_repr_symm_apply
      (Fintype.card_fin n), LinearIsometryEquiv.symm_apply_apply]
  have hx : x ∈ (S.tangentTrivialization m).baseSet := by simp
  conv_lhs => rw [← hv]
  exact Trivialization.apply_mk_symm _ hx _

/-- Reading the fiberwise coordinate vector `(S.tangentOrthonormalBasis _ p.proj).repr p.2` on
`TangentBundle (𝓡 n) (sphere (0 : E) 1)` is `C^m` for every `m : ℕ∞ω`. -/
theorem contMDiff_tangentOrthonormalBasis_repr (m : ℕ∞ω) :
    ContMDiff (𝓡 n).tangent 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) m
      (fun p : TangentBundle (𝓡 n) (sphere (0 : E) 1) ↦
        (S.tangentOrthonormalBasis (Fintype.card_fin n) p.proj).repr p.2) := by
  have hpi : ContMDiff (𝓡 n).tangent 𝓘(ℝ, Fin n → ℝ) m
      (fun p : TangentBundle (𝓡 n) (sphere (0 : E) 1) ↦ fun i : Fin n ↦
        ⟪S.op i (p.proj : E), (sphereTangentEquiv p.proj p.2 : E)⟫_ℝ) := by
    refine contMDiff_pi_module_iff.mpr fun i ↦ ?_
    have hop : ContMDiff (𝓡 n).tangent 𝓘(ℝ, E) m
        (fun p : TangentBundle (𝓡 n) (sphere (0 : E) 1) ↦ S.op i (p.proj : E)) :=
      ((S.isometryEquiv i).contDiff.contMDiff.comp
        ((contMDiff_coe_sphere (E := E) (n := n)).comp
          (Bundle.contMDiff_proj (TangentSpace (𝓡 n))))).congr
        fun p ↦ (S.coe_isometryEquiv_apply i (p.proj : E)).symm
    exact (isBoundedBilinearMap_inner (𝕜 := ℝ) (E := E)).contDiff.contMDiff.comp
      (hop.prodMk_space contMDiff_coe_sphereTangentEquiv)
  exact ((EuclideanSpace.equiv (Fin n) ℝ).symm.contDiff.contMDiff.comp hpi).congr fun p ↦ by
    ext i
    rw [tangentOrthonormalBasis_repr_apply, inner_tangentField_left]
    rfl

/-- The global `C^m` diffeomorphism `TangentBundle (𝓡 n) (sphere (0 : E) 1) ≃ₘ^m
sphere (0 : E) 1 × EuclideanSpace ℝ (Fin n)` induced by a `Fin n`-indexed
`SkewAdjointCliffordSystem`, sending `⟨x, v⟩` to `(x, i ↦ ⟪S.tangentField i x, v⟫_ℝ)` and
`(x, c)` to `⟨x, ∑ i, c_i • S.tangentField i x⟩`. -/
def tangentBundleDiffeomorph (m : ℕ∞ω) :
    TangentBundle (𝓡 n) (sphere (0 : E) 1) ≃ₘ^m⟮(𝓡 n).tangent,
      (𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))⟯
      sphere (0 : E) 1 × EuclideanSpace ℝ (Fin n) where
  toFun p := (p.proj, (S.tangentOrthonormalBasis (Fintype.card_fin n) p.proj).repr p.2)
  invFun q := ⟨q.1, (S.tangentOrthonormalBasis (Fintype.card_fin n) q.1).repr.symm q.2⟩
  left_inv p := by
    obtain ⟨x, v⟩ := p
    simp
  right_inv q := by
    obtain ⟨x, c⟩ := q
    simp
  contMDiff_toFun :=
    (Bundle.contMDiff_proj (TangentSpace (𝓡 n))).prodMk (S.contMDiff_tangentOrthonormalBasis_repr m)
  contMDiff_invFun := by
    have hfst : ContMDiff ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (𝓡 n) m
        (Prod.fst : sphere (0 : E) 1 × EuclideanSpace ℝ (Fin n) → sphere (0 : E) 1) :=
      contMDiff_fst
    have hsnd : ContMDiff ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
        𝓘(ℝ, EuclideanSpace ℝ (Fin n)) m
        (Prod.snd : sphere (0 : E) 1 × EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) :=
      contMDiff_snd
    have hsum := ContMDiff.sum_sectionAlong Finset.univ
      (fun i (q : sphere (0 : E) 1 × EuclideanSpace ℝ (Fin n)) ↦
        q.2.ofLp i • S.tangentField i q.1)
      hfst fun i _ ↦
        (((EuclideanSpace.proj i).contDiff.contMDiff.comp hsnd).smul_totalSpace
          ((S.contMDiff_tangentField i).comp hfst))
    exact hsum.congr fun q ↦
      congrArg (TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) q.1)
        (S.tangentOrthonormalBasis_repr_symm_apply (Fintype.card_fin n) q.1 q.2)

/-- Forward formula for `S.tangentBundleDiffeomorph m` in terms of `S.tangentOrthonormalBasis`. -/
@[simp]
theorem tangentBundleDiffeomorph_apply (m : ℕ∞ω)
    (p : TangentBundle (𝓡 n) (sphere (0 : E) 1)) :
    S.tangentBundleDiffeomorph m p =
      (p.proj, (S.tangentOrthonormalBasis (Fintype.card_fin n) p.proj).repr p.2) := by
  rfl

/-- Inverse formula for `S.tangentBundleDiffeomorph m` as a linear combination of
`S.tangentField i`. -/
@[simp]
theorem tangentBundleDiffeomorph_symm_apply (m : ℕ∞ω)
    (q : sphere (0 : E) 1 × EuclideanSpace ℝ (Fin n)) :
    (S.tangentBundleDiffeomorph m).symm q =
      ⟨q.1, ∑ i : Fin n, q.2.ofLp i • S.tangentField i q.1⟩ := by
  exact congrArg (TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) q.1)
    (S.tangentOrthonormalBasis_repr_symm_apply (Fintype.card_fin n) q.1 q.2)

/-- The global `C^m` bundle diffeomorphism from `TangentBundle (𝓡 n) (sphere (0 : E) 1)` onto the
total space of `Bundle.Trivial (sphere (0 : E) 1) (EuclideanSpace ℝ (Fin n))`, constructed via
`TauCeti.bundleDiffeomorph`. -/
def tangentBundleTrivialDiffeomorph (m : ℕ∞ω) :
    TangentBundle (𝓡 n) (sphere (0 : E) 1) ≃ₘ^m⟮(𝓡 n).tangent,
      (𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))⟯
      TotalSpace (EuclideanSpace ℝ (Fin n))
        (Bundle.Trivial (sphere (0 : E) 1) (EuclideanSpace ℝ (Fin n))) :=
  have : IsManifold (𝓡 n) (m + 1) (sphere (0 : E) 1) :=
    IsManifold.of_le (le_top : m + 1 ≤ ω)
  bundleDiffeomorph
    (fun x : sphere (0 : E) 1 ↦
      (S.tangentOrthonormalBasis (Fintype.card_fin n) x).repr.toContinuousLinearEquiv)
    (Bundle.Trivial.contMDiff_mk_iff.mpr
      ⟨Bundle.contMDiff_proj (TangentSpace (𝓡 n)), S.contMDiff_tangentOrthonormalBasis_repr m⟩)

/-- Forward formula for `S.tangentBundleTrivialDiffeomorph m`. -/
@[simp]
theorem tangentBundleTrivialDiffeomorph_apply (m : ℕ∞ω)
    (p : TangentBundle (𝓡 n) (sphere (0 : E) 1)) :
    S.tangentBundleTrivialDiffeomorph m p =
      ⟨p.proj, (S.tangentOrthonormalBasis (Fintype.card_fin n) p.proj).repr p.2⟩ := by
  rw [tangentBundleTrivialDiffeomorph, bundleDiffeomorph_apply]
  rfl

/-- Inverse formula for `S.tangentBundleTrivialDiffeomorph m` as a linear combination of
`S.tangentField i`. -/
@[simp]
theorem tangentBundleTrivialDiffeomorph_symm_apply (m : ℕ∞ω)
    (p : TotalSpace (EuclideanSpace ℝ (Fin n))
      (Bundle.Trivial (sphere (0 : E) 1) (EuclideanSpace ℝ (Fin n)))) :
    (S.tangentBundleTrivialDiffeomorph m).symm p =
      ⟨p.proj, ∑ i : Fin n, p.2.ofLp i • S.tangentField i p.proj⟩ := by
  rw [tangentBundleTrivialDiffeomorph, bundleDiffeomorph_symm_apply]
  exact congrArg (TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) p.proj)
    (S.tangentOrthonormalBasis_repr_symm_apply (Fintype.card_fin n) p.proj p.2)

end FinIndex

end SkewAdjointCliffordSystem

/-! ### Smooth and analytic parallelizability of `S⁰`, `S¹`, `S³`, and `S⁷` -/

section ParallelizableSpheres

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
  [Fact (finrank ℝ E = n + 1)]

/-- For `n ∈ {0, 1, 3, 7}`, the unit sphere `sphere (0 : E) 1` of any `(n + 1)`-dimensional real
inner product space `E` admits `n` `C^m` tangent vector fields (for every `m : ℕ∞ω`, including
`m = ω`) that are orthonormal in the round metric at every point. -/
theorem exists_orthonormal_contMDiff_tangentSpace_sphere_of_eq (m : ℕ∞ω)
    (hn : n = 0 ∨ n = 1 ∨ n = 3 ∨ n = 7) :
    ∃ v : Fin n → (x : sphere (0 : E) 1) → TangentSpace (𝓡 n) x,
      (∀ i, ContMDiff (𝓡 n) (𝓡 n).tangent m
        (fun x ↦ (⟨x, v i x⟩ : TangentBundle (𝓡 n) (sphere (0 : E) 1)))) ∧
      ∀ x, Orthonormal ℝ fun i ↦ v i x := by
  obtain ⟨S⟩ := nonempty_skewAdjointCliffordSystem_of_eq (Fact.out : finrank ℝ E = n + 1) hn
  exact ⟨S.tangentField, S.contMDiff_tangentField, S.orthonormal_tangentField⟩

/-- For `n ∈ {0, 1, 3, 7}`, the unit sphere `sphere (0 : E) 1` admits a global `C^m` orthonormal
tangent frame on `Set.univ` (for every `m : ℕ∞ω`). -/
theorem exists_isLocalFrameOn_univ_sphere_of_eq (m : ℕ∞ω)
    (hn : n = 0 ∨ n = 1 ∨ n = 3 ∨ n = 7) :
    ∃ v : Fin n → (x : sphere (0 : E) 1) → TangentSpace (𝓡 n) x,
      IsLocalFrameOn (𝓡 n) (EuclideanSpace ℝ (Fin n)) m v univ ∧
      ∀ x, Orthonormal ℝ fun i ↦ v i x := by
  obtain ⟨S⟩ := nonempty_skewAdjointCliffordSystem_of_eq (Fact.out : finrank ℝ E = n + 1) hn
  exact ⟨S.tangentField, S.isLocalFrameOn_tangentField (Fintype.card_fin n) m,
    S.orthonormal_tangentField⟩

/-- For `n ∈ {0, 1, 3, 7}`, the unit sphere `sphere (0 : E) 1` admits `n` `C^m` tangent vector
fields that are linearly independent at every point (for every `m : ℕ∞ω`, including `m = ∞` and
`m = ω`). -/
theorem exists_linearIndependent_contMDiff_tangentSpace_sphere_of_eq (m : ℕ∞ω)
    (hn : n = 0 ∨ n = 1 ∨ n = 3 ∨ n = 7) :
    ∃ v : Fin n → (x : sphere (0 : E) 1) → TangentSpace (𝓡 n) x,
      (∀ i, ContMDiff (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) m
        (fun x ↦ (⟨x, v i x⟩ : TangentBundle (𝓡 n) (sphere (0 : E) 1)))) ∧
      ∀ x, LinearIndependent ℝ fun i ↦ v i x := by
  obtain ⟨v, hv_diff, hv_ortho⟩ :=
    exists_orthonormal_contMDiff_tangentSpace_sphere_of_eq (E := E) m hn
  exact ⟨v, hv_diff, fun x ↦ (hv_ortho x).linearIndependent⟩

/-- For `n ∈ {0, 1, 3, 7}`, the tangent bundle of `sphere (0 : E) 1` is `C^m`-diffeomorphic to the
product `sphere (0 : E) 1 × EuclideanSpace ℝ (Fin n)` (for every `m : ℕ∞ω`). -/
theorem nonempty_tangentBundleDiffeomorph_sphere_of_eq (m : ℕ∞ω)
    (hn : n = 0 ∨ n = 1 ∨ n = 3 ∨ n = 7) :
    Nonempty (TangentBundle (𝓡 n) (sphere (0 : E) 1) ≃ₘ^m⟮(𝓡 n).tangent,
      (𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))⟯
      sphere (0 : E) 1 × EuclideanSpace ℝ (Fin n)) := by
  obtain ⟨S⟩ := nonempty_skewAdjointCliffordSystem_of_eq (Fact.out : finrank ℝ E = n + 1) hn
  exact ⟨S.tangentBundleDiffeomorph m⟩

/-- For `n ∈ {0, 1, 3, 7}`, the tangent bundle of `sphere (0 : E) 1` is `C^m`-diffeomorphic to the
total space of `Bundle.Trivial (sphere (0 : E) 1) (EuclideanSpace ℝ (Fin n))` (for every
`m : ℕ∞ω`). -/
theorem nonempty_tangentBundleTrivialDiffeomorph_sphere_of_eq (m : ℕ∞ω)
    (hn : n = 0 ∨ n = 1 ∨ n = 3 ∨ n = 7) :
    Nonempty (TangentBundle (𝓡 n) (sphere (0 : E) 1) ≃ₘ^m⟮(𝓡 n).tangent,
      (𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))⟯
      TotalSpace (EuclideanSpace ℝ (Fin n))
        (Bundle.Trivial (sphere (0 : E) 1) (EuclideanSpace ℝ (Fin n)))) := by
  obtain ⟨S⟩ := nonempty_skewAdjointCliffordSystem_of_eq (Fact.out : finrank ℝ E = n + 1) hn
  exact ⟨S.tangentBundleTrivialDiffeomorph m⟩

end ParallelizableSpheres

end TauCeti
