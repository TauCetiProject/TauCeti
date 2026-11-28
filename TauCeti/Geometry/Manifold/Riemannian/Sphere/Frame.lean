/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Sphere.Gradient
public import TauCeti.Geometry.Manifold.VectorBundle.FrameTrivialization
public import TauCeti.Geometry.Manifold.VectorBundle.Hom.Basic
public import TauCeti.LinearAlgebra.CliffordAlgebra.Module.Euclidean
import TauCeti.Geometry.Manifold.VectorBundle.LocalFrame.Orthonormal
import TauCeti.Geometry.Manifold.VectorBundle.Trivial

/-!
# Orthonormal Clifford tangent frames and parallelizability of `S⁰`, `S¹`, `S³`, and `S⁷`

Let `E` be a real inner product space of dimension `n + 1` and `sphere (0 : E) 1` its unit sphere
equipped with the analytic round Riemannian metric (`TauCeti.sphereRoundMetric`). At each point `x`
of the sphere, `TauCeti.sphereTangentEquiv x` identifies `TangentSpace (𝓡 n) x` isometrically with
the hyperplane `(ℝ ∙ (x : E))ᗮ` in `E`, with `C^m` regularity in both directions for every
`m : ℕ∞ω` (`TauCeti.contMDiff_coe_sphereTangentEquiv`,
`TauCeti.contMDiff_sphereTangentEquiv_symm`).

Given a `TauCeti.SkewAdjointCliffordSystem ι E` — an `ι`-indexed family of pairwise anticommuting
skew-adjoint complex structures `A_i` on `E` — evaluating `(sphereTangentEquiv x).symm` on `A_i x`
defines analytic unit vector fields `S.tangentField i` on `sphere (0 : E) 1` that are pointwise
orthonormal (`S.orthonormal_tangentField`). When `|ι| = n`, they form a global `C^m` orthonormal
frame (`S.isLocalFrameOn_tangentField`), inducing:
* for `ι = Fin n`, a global linear trivialization `S.tangentTrivialization` belonging to the `C^m`
  maximal atlas of the tangent bundle for every `m : ℕ∞ω`
  (`S.tangentTrivialization_mem_maximalAtlas`);
* a `C^m` diffeomorphism of total spaces `S.tangentBundleTrivialDiffeomorph` from
  `TangentBundle (𝓡 n) (sphere (0 : E) 1)` onto the total space of
  `Bundle.Trivial (sphere (0 : E) 1) (EuclideanSpace ℝ ι)` sending `⟨x, v⟩` to
  `⟨x, (S.tangentOrthonormalBasis hcard x).repr v⟩`;
* the composite `C^m` diffeomorphism `S.tangentBundleDiffeomorph` from
  `TangentBundle (𝓡 n) (sphere (0 : E) 1)` onto `sphere (0 : E) 1 × EuclideanSpace ℝ ι` with
  inner-product forward coordinates `v ↦ (i ↦ ⟪S.tangentField i x, v⟫_ℝ)` and linear-combination
  inverse `c ↦ ∑ i, c_i • S.tangentField i x`.

Combining these constructions with `TauCeti.nonempty_skewAdjointCliffordSystem_of_finrank_eq_succ`
(from the real Clifford algebra classification of `Cliff(0, 1)`, `Cliff(0, 3)`, and `Cliff(0, 7)`)
yields global `C^m` orthonormal tangent frames and `C^m` diffeomorphisms of the tangent bundle
total space on the unit sphere in dimensions `n ∈ {0, 1, 3, 7}`, establishing the constructive
direction of the parallelizability characterization of spheres
(`TauCeti.exists_linearIndependent_contMDiff_tangentSpace_sphere`).

## Main definitions

* `TauCeti.SkewAdjointCliffordSystem.tangentField`: the `i`-th Clifford tangent vector field
  `x ↦ (sphereTangentEquiv x).symm (S.orthogonalVec i x)` on `sphere (0 : E) 1`.
* `TauCeti.SkewAdjointCliffordSystem.tangentOrthonormalBasis`: the pointwise `OrthonormalBasis` of
  `TangentSpace (𝓡 n) x` induced when `Fintype.card ι = n`.
* `TauCeti.SkewAdjointCliffordSystem.tangentTrivialization`: the global `Bundle.Trivialization` of
  `TangentSpace (𝓡 n)` associated with a `Fin n`-indexed `SkewAdjointCliffordSystem`.
* `TauCeti.SkewAdjointCliffordSystem.tangentBundleTrivialDiffeomorph`: the `C^m` diffeomorphism of
  total spaces onto `TotalSpace (EuclideanSpace ℝ ι) (Bundle.Trivial _ _)`.
* `TauCeti.SkewAdjointCliffordSystem.tangentBundleDiffeomorph`: the `C^m` diffeomorphism
  `TangentBundle (𝓡 n) (sphere (0 : E) 1) ≃ₘ^m sphere (0 : E) 1 × EuclideanSpace ℝ ι`.

## Main results

* `TauCeti.SkewAdjointCliffordSystem.contMDiff_tangentField` and
  `TauCeti.SkewAdjointCliffordSystem.orthonormal_tangentField`: `S.tangentField` is a `C^m`
  pointwise orthonormal family of tangent vector fields.
* `TauCeti.SkewAdjointCliffordSystem.isLocalFrameOn_tangentField`: when `Fintype.card ι = n`,
  `S.tangentField` is a global `C^m` frame on `Set.univ`.
* `TauCeti.exists_orthonormal_contMDiff_tangentSpace_sphere`,
  `TauCeti.exists_orthonormal_isLocalFrameOn_univ_sphere`, and
  `TauCeti.exists_linearIndependent_contMDiff_tangentSpace_sphere`: global `C^m` orthonormal and
  linearly independent tangent frames on `Sⁿ` for `n ∈ {0, 1, 3, 7}`.
* `TauCeti.nonempty_tangentBundleDiffeomorph_sphere` and
  `TauCeti.nonempty_tangentBundleTrivialDiffeomorph_sphere`: `C^m` diffeomorphisms from the
  tangent-bundle total space of `Sⁿ` onto `Sⁿ × EuclideanSpace ℝ (Fin n)` and the total space of
  the trivial bundle for `n ∈ {0, 1, 3, 7}`.

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

namespace SkewAdjointCliffordSystem

section GeneralIndex

variable {ι E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (S : SkewAdjointCliffordSystem ι E) {n : ℕ} [Fact (finrank ℝ E = n + 1)]

/-- The `i`-th Clifford tangent vector field on the unit sphere `sphere (0 : E) 1`, obtained by
transporting `S.op i x ∈ (ℝ ∙ (x : E))ᗮ` to `TangentSpace (𝓡 n) x` via
`(sphereTangentEquiv x).symm`. -/
def tangentField (i : ι) (x : sphere (0 : E) 1) : TangentSpace (𝓡 n) x :=
  (sphereTangentEquiv x).symm (S.orthogonalVec i (x : E))

/-- Reindexing a `SkewAdjointCliffordSystem` reindexes `tangentField`. -/
@[simp]
theorem reindex_tangentField {ι' : Type*} (e : ι' ≃ ι) (i : ι') (x : sphere (0 : E) 1) :
    (S.reindex e).tangentField (n := n) i x = S.tangentField (e i) x := by
  rw [tangentField, tangentField, reindex_orthogonalVec]

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
@[simp 1100]
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
      (S.isometryEquiv_apply i (x : E)).symm
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

/-- The round inner product of a Clifford tangent vector field with itself is `1`. -/
@[simp 1100]
theorem inner_tangentField_self (i : ι) (x : sphere (0 : E) 1) :
    ⟪S.tangentField (n := n) i x, S.tangentField (n := n) i x⟫_ℝ = 1 := by
  rw [real_inner_self_eq_norm_sq, S.norm_tangentField, one_pow]

/-- Distinct Clifford tangent vector fields are pointwise orthogonal in the round metric. -/
theorem inner_tangentField_eq_zero_of_ne {i j : ι} (hij : i ≠ j) (x : sphere (0 : E) 1) :
    ⟪S.tangentField (n := n) i x, S.tangentField (n := n) j x⟫_ℝ = 0 := by
  rw [inner_tangentField_left, coe_sphereTangentEquiv_tangentField]
  exact S.inner_op_eq_zero_of_ne hij (x : E)

/-- At every point `x` of the unit sphere, the vectors `S.tangentField i x` form an orthonormal
family in `TangentSpace (𝓡 n) x` for the round metric. -/
theorem orthonormal_tangentField (x : sphere (0 : E) 1) :
    Orthonormal ℝ fun i ↦ S.tangentField (n := n) i x :=
  ⟨fun i ↦ S.norm_tangentField i x, fun {_ _} hij ↦ S.inner_tangentField_eq_zero_of_ne hij x⟩

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
    ((Fact.out : finrank ℝ E = n + 1).trans (congrArg (· + 1) hcard.symm))
    (norm_eq_of_mem_sphere x)).map (sphereTangentEquiv x).symm

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
def tangentTrivialization :
    Trivialization (EuclideanSpace ℝ (Fin n))
      (π (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n) : sphere (0 : E) 1 → Type _)) :=
  (S.isLocalFrameOn_tangentField (Fintype.card_fin n) ω).trivialization isOpen_univ
    (EuclideanSpace.basisFun (Fin n) ℝ).toBasis

/-- `S.tangentTrivialization` is defined over the entire unit sphere `Set.univ`. -/
@[simp]
theorem baseSet_tangentTrivialization : S.tangentTrivialization.baseSet = univ := by
  rw [tangentTrivialization, IsLocalFrameOn.baseSet_trivialization]

/-- `S.tangentTrivialization` is fiberwise `ℝ`-linear. -/
instance isLinear_tangentTrivialization : S.tangentTrivialization.IsLinear ℝ := by
  delta tangentTrivialization
  infer_instance

/-- For every `m : ℕ∞ω`, `S.tangentTrivialization` belongs to the `C^m` maximal atlas of
compatible fiberwise-linear trivializations of `TangentBundle (𝓡 n) (sphere (0 : E) 1)`. -/
theorem tangentTrivialization_mem_maximalAtlas (m : ℕ∞ω) :
    S.tangentTrivialization.toOpenPartialHomeomorph ∈
      (contMDiffFiberwiseLinear (sphere (0 : E) 1) (EuclideanSpace ℝ (Fin n)) (𝓡 n) m).maximalAtlas
        (TangentBundle (𝓡 n) (sphere (0 : E) 1)) := by
  have : IsManifold (𝓡 n) (m + 1) (sphere (0 : E) 1) :=
    IsManifold.of_le (le_top : m + 1 ≤ ω)
  rw [Trivialization.mem_maximalAtlas_contMDiffFiberwiseLinear_iff]
  have hω := (Trivialization.mem_maximalAtlas_contMDiffFiberwiseLinear_iff (𝓡 n) ω
    S.tangentTrivialization).mp
    ((S.isLocalFrameOn_tangentField (Fintype.card_fin n) ω).trivialization_mem_maximalAtlas
      isOpen_univ (EuclideanSpace.basisFun (Fin n) ℝ).toBasis)
  intro e' _
  exact ⟨(hω e').1.of_le le_top, (hω e').2.of_le le_top⟩

/-- Inverse formula for `S.tangentTrivialization` in terms of `S.tangentOrthonormalBasis`. -/
@[simp]
theorem tangentTrivialization_symm_apply (x : sphere (0 : E) 1)
    (c : EuclideanSpace ℝ (Fin n)) :
    S.tangentTrivialization.symm x c =
      (S.tangentOrthonormalBasis (Fintype.card_fin n) x).repr.symm c := by
  rw [tangentTrivialization, IsLocalFrameOn.trivialization_symm_apply _ isOpen_univ _ (mem_univ x),
    S.tangentOrthonormalBasis_repr_symm_apply]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [OrthonormalBasis.coe_toBasis_repr_apply, EuclideanSpace.basisFun_repr]

/-- Inverse formula for `S.tangentTrivialization` expanded as a linear combination of
`S.tangentField i x`. -/
theorem tangentTrivialization_symm_apply_eq_sum (x : sphere (0 : E) 1)
    (c : EuclideanSpace ℝ (Fin n)) :
    S.tangentTrivialization.symm x c = ∑ i : Fin n, c.ofLp i • S.tangentField i x := by
  rw [S.tangentTrivialization_symm_apply, S.tangentOrthonormalBasis_repr_symm_apply]

/-- On fibers, `S.tangentTrivialization` sends a tangent vector `v` at `x` to its coordinate
vector in `S.tangentOrthonormalBasis`. -/
@[simp]
theorem tangentTrivialization_apply (x : sphere (0 : E) 1) (v : TangentSpace (𝓡 n) x) :
    S.tangentTrivialization ⟨x, v⟩ =
      (x, (S.tangentOrthonormalBasis (Fintype.card_fin n) x).repr v) := by
  have hx : x ∈ S.tangentTrivialization.baseSet := by simp
  conv_lhs =>
    rw [← LinearIsometryEquiv.symm_apply_apply
      (S.tangentOrthonormalBasis (Fintype.card_fin n) x).repr v,
      ← S.tangentTrivialization_symm_apply]
  exact Trivialization.apply_mk_symm _ hx _

end FinIndex

section TotalSpaceDiffeomorph

variable {ι E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (S : SkewAdjointCliffordSystem ι E) {n : ℕ} [Fact (finrank ℝ E = n + 1)]

/-- Reading the fiberwise coordinate vector `(S.tangentOrthonormalBasis hcard p.proj).repr p.2` on
`TangentBundle (𝓡 n) (sphere (0 : E) 1)` is `C^m` for every `m : ℕ∞ω`. -/
theorem contMDiff_tangentOrthonormalBasis_repr [Fintype ι] (hcard : Fintype.card ι = n)
    (m : ℕ∞ω) :
    ContMDiff (𝓡 n).tangent 𝓘(ℝ, EuclideanSpace ℝ ι) m
      (fun p : TangentBundle (𝓡 n) (sphere (0 : E) 1) ↦
        (S.tangentOrthonormalBasis hcard p.proj).repr p.snd) := by
  have : IsManifold (𝓡 n) (m + 1) (sphere (0 : E) 1) :=
    IsManifold.of_le (le_top : m + 1 ≤ ω)
  let e : Fin n ≃ ι := (Fintype.equivFinOfCardEq hcard).symm
  let S' := S.reindex e
  have hfin : ContMDiff (𝓡 n).tangent 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) m
      (fun p : TangentBundle (𝓡 n) (sphere (0 : E) 1) ↦
        (S'.tangentOrthonormalBasis (Fintype.card_fin n) p.proj).repr p.snd) := by
    intro p
    exact (((Bundle.Trivialization.contMDiffAt_iff_of_mem_maximalAtlas
      (S'.tangentTrivialization_mem_maximalAtlas m) (f := id) (x₀ := p)
      (S'.tangentTrivialization.mem_source.mpr (by simp))).mp
      contMDiffAt_id).2).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun ⟨x, v⟩ ↦ by simp)
  exact ((LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ e).contDiff.contMDiff.comp hfin).congr
    fun ⟨x, v⟩ ↦ by
      ext i
      simp [S', Equiv.piCongrLeft'_apply]

/-- The global `C^m` diffeomorphism of total spaces from `TangentBundle (𝓡 n) (sphere (0 : E) 1)`
onto `TotalSpace (EuclideanSpace ℝ ι) (Bundle.Trivial (sphere (0 : E) 1) (EuclideanSpace ℝ ι))`
sending `⟨x, v⟩` to `⟨x, (S.tangentOrthonormalBasis hcard x).repr v⟩`. -/
def tangentBundleTrivialDiffeomorph [Fintype ι] (hcard : Fintype.card ι = n) (m : ℕ∞ω) :
    TangentBundle (𝓡 n) (sphere (0 : E) 1) ≃ₘ^m⟮(𝓡 n).tangent,
      (𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ ι)⟯
      TotalSpace (EuclideanSpace ℝ ι)
        (Bundle.Trivial (sphere (0 : E) 1) (EuclideanSpace ℝ ι)) :=
  have : IsManifold (𝓡 n) (m + 1) (sphere (0 : E) 1) :=
    IsManifold.of_le (le_top : m + 1 ≤ ω)
  bundleDiffeomorph
    (fun x : sphere (0 : E) 1 ↦
      (S.tangentOrthonormalBasis hcard x).repr.toContinuousLinearEquiv)
    (Bundle.Trivial.contMDiff_mk_iff.mpr ⟨Bundle.contMDiff_proj (TangentSpace (𝓡 n)),
      S.contMDiff_tangentOrthonormalBasis_repr hcard m⟩)

/-- Forward formula for `S.tangentBundleTrivialDiffeomorph hcard m`. -/
@[simp]
theorem tangentBundleTrivialDiffeomorph_apply [Fintype ι] (hcard : Fintype.card ι = n) (m : ℕ∞ω)
    (p : TangentBundle (𝓡 n) (sphere (0 : E) 1)) :
    S.tangentBundleTrivialDiffeomorph hcard m p =
      ⟨p.proj, (S.tangentOrthonormalBasis hcard p.proj).repr p.snd⟩ := by
  simp [tangentBundleTrivialDiffeomorph]

/-- Inverse formula for `S.tangentBundleTrivialDiffeomorph hcard m` in terms of
`S.tangentOrthonormalBasis`. -/
@[simp]
theorem tangentBundleTrivialDiffeomorph_symm_apply [Fintype ι] (hcard : Fintype.card ι = n)
    (m : ℕ∞ω)
    (p : TotalSpace (EuclideanSpace ℝ ι)
      (Bundle.Trivial (sphere (0 : E) 1) (EuclideanSpace ℝ ι))) :
    (S.tangentBundleTrivialDiffeomorph hcard m).symm p =
      ⟨p.proj, (S.tangentOrthonormalBasis hcard p.proj).repr.symm p.snd⟩ := by
  simp [tangentBundleTrivialDiffeomorph, LinearIsometryEquiv.coe_symm_toContinuousLinearEquiv]

/-- Inverse formula for `S.tangentBundleTrivialDiffeomorph hcard m` expanded as a linear
combination of `S.tangentField i`. -/
theorem tangentBundleTrivialDiffeomorph_symm_apply_eq_mk_sum [Fintype ι]
    (hcard : Fintype.card ι = n) (m : ℕ∞ω)
    (p : TotalSpace (EuclideanSpace ℝ ι)
      (Bundle.Trivial (sphere (0 : E) 1) (EuclideanSpace ℝ ι))) :
    (S.tangentBundleTrivialDiffeomorph hcard m).symm p =
      ⟨p.proj, ∑ i : ι, p.snd.ofLp i • S.tangentField i p.proj⟩ := by
  rw [S.tangentBundleTrivialDiffeomorph_symm_apply, S.tangentOrthonormalBasis_repr_symm_apply]

/-- The global `C^m` diffeomorphism `TangentBundle (𝓡 n) (sphere (0 : E) 1) ≃ₘ^m
sphere (0 : E) 1 × EuclideanSpace ℝ ι` induced by an `ι`-indexed `SkewAdjointCliffordSystem` with
`Fintype.card ι = n`, sending `⟨x, v⟩` to `(x, (S.tangentOrthonormalBasis hcard x).repr v)` and
`(x, c)` to `⟨x, ∑ i, c_i • S.tangentField i x⟩`. -/
def tangentBundleDiffeomorph [Fintype ι] (hcard : Fintype.card ι = n) (m : ℕ∞ω) :
    TangentBundle (𝓡 n) (sphere (0 : E) 1) ≃ₘ^m⟮(𝓡 n).tangent,
      (𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ ι)⟯
      sphere (0 : E) 1 × EuclideanSpace ℝ ι :=
  (S.tangentBundleTrivialDiffeomorph hcard m).trans
    (Bundle.Trivial.diffeomorphProd (𝓡 n) (sphere (0 : E) 1) (EuclideanSpace ℝ ι) m)

/-- Forward formula for `S.tangentBundleDiffeomorph hcard m` in terms of
`S.tangentOrthonormalBasis`. -/
@[simp]
theorem tangentBundleDiffeomorph_apply [Fintype ι] (hcard : Fintype.card ι = n) (m : ℕ∞ω)
    (p : TangentBundle (𝓡 n) (sphere (0 : E) 1)) :
    S.tangentBundleDiffeomorph hcard m p =
      (p.proj, (S.tangentOrthonormalBasis hcard p.proj).repr p.snd) := by
  simp [tangentBundleDiffeomorph]

/-- Inverse formula for `S.tangentBundleDiffeomorph hcard m` in terms of
`S.tangentOrthonormalBasis`. -/
@[simp]
theorem tangentBundleDiffeomorph_symm_apply [Fintype ι] (hcard : Fintype.card ι = n) (m : ℕ∞ω)
    (q : sphere (0 : E) 1 × EuclideanSpace ℝ ι) :
    (S.tangentBundleDiffeomorph hcard m).symm q =
      ⟨q.1, (S.tangentOrthonormalBasis hcard q.1).repr.symm q.2⟩ := by
  simp [tangentBundleDiffeomorph]

/-- Inverse formula for `S.tangentBundleDiffeomorph hcard m` expanded as a linear combination of
`S.tangentField i`. -/
theorem tangentBundleDiffeomorph_symm_apply_eq_mk_sum [Fintype ι] (hcard : Fintype.card ι = n)
    (m : ℕ∞ω) (q : sphere (0 : E) 1 × EuclideanSpace ℝ ι) :
    (S.tangentBundleDiffeomorph hcard m).symm q =
      ⟨q.1, ∑ i : ι, q.2.ofLp i • S.tangentField i q.1⟩ := by
  rw [S.tangentBundleDiffeomorph_symm_apply, S.tangentOrthonormalBasis_repr_symm_apply]

end TotalSpaceDiffeomorph

end SkewAdjointCliffordSystem

/-! ### Smooth and analytic parallelizability of `S⁰`, `S¹`, `S³`, and `S⁷` -/

section ParallelizableSpheres

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
  [Fact (finrank ℝ E = n + 1)]

/-- For `n ∈ {0, 1, 3, 7}`, the unit sphere `sphere (0 : E) 1` of any `(n + 1)`-dimensional real
inner product space `E` admits `n` `C^m` tangent vector fields (for every `m : ℕ∞ω`, including
`m = ω`) that are orthonormal in the round metric at every point. -/
theorem exists_orthonormal_contMDiff_tangentSpace_sphere (m : ℕ∞ω)
    (hn : n = 0 ∨ n = 1 ∨ n = 3 ∨ n = 7) :
    ∃ v : Fin n → (x : sphere (0 : E) 1) → TangentSpace (𝓡 n) x,
      (∀ i, ContMDiff (𝓡 n) (𝓡 n).tangent m
        (fun x ↦ (⟨x, v i x⟩ : TangentBundle (𝓡 n) (sphere (0 : E) 1)))) ∧
      ∀ x, Orthonormal ℝ fun i ↦ v i x := by
  obtain ⟨S⟩ :=
    nonempty_skewAdjointCliffordSystem_of_finrank_eq_succ (Fact.out : finrank ℝ E = n + 1) hn
  exact ⟨S.tangentField, S.contMDiff_tangentField, S.orthonormal_tangentField⟩

/-- For `n ∈ {0, 1, 3, 7}`, the unit sphere `sphere (0 : E) 1` admits a global `C^m` orthonormal
tangent frame on `Set.univ` (for every `m : ℕ∞ω`). -/
theorem exists_orthonormal_isLocalFrameOn_univ_sphere (m : ℕ∞ω)
    (hn : n = 0 ∨ n = 1 ∨ n = 3 ∨ n = 7) :
    ∃ v : Fin n → (x : sphere (0 : E) 1) → TangentSpace (𝓡 n) x,
      IsLocalFrameOn (𝓡 n) (EuclideanSpace ℝ (Fin n)) m v univ ∧
      ∀ x, Orthonormal ℝ fun i ↦ v i x := by
  obtain ⟨S⟩ :=
    nonempty_skewAdjointCliffordSystem_of_finrank_eq_succ (Fact.out : finrank ℝ E = n + 1) hn
  exact ⟨S.tangentField, S.isLocalFrameOn_tangentField (Fintype.card_fin n) m,
    S.orthonormal_tangentField⟩

/-- For `n ∈ {0, 1, 3, 7}`, the unit sphere `sphere (0 : E) 1` admits `n` `C^m` tangent vector
fields that are linearly independent at every point (for every `m : ℕ∞ω`, including `m = ∞` and
`m = ω`). -/
theorem exists_linearIndependent_contMDiff_tangentSpace_sphere (m : ℕ∞ω)
    (hn : n = 0 ∨ n = 1 ∨ n = 3 ∨ n = 7) :
    ∃ v : Fin n → (x : sphere (0 : E) 1) → TangentSpace (𝓡 n) x,
      (∀ i, ContMDiff (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) m
        (fun x ↦ (⟨x, v i x⟩ : TangentBundle (𝓡 n) (sphere (0 : E) 1)))) ∧
      ∀ x, LinearIndependent ℝ fun i ↦ v i x := by
  obtain ⟨v, hv_diff, hv_ortho⟩ :=
    exists_orthonormal_contMDiff_tangentSpace_sphere (E := E) m hn
  exact ⟨v, hv_diff, fun x ↦ (hv_ortho x).linearIndependent⟩

/-- For `n ∈ {0, 1, 3, 7}`, the tangent bundle of `sphere (0 : E) 1` is `C^m`-diffeomorphic to the
product `sphere (0 : E) 1 × EuclideanSpace ℝ (Fin n)` (for every `m : ℕ∞ω`). -/
theorem nonempty_tangentBundleDiffeomorph_sphere (m : ℕ∞ω)
    (hn : n = 0 ∨ n = 1 ∨ n = 3 ∨ n = 7) :
    Nonempty (TangentBundle (𝓡 n) (sphere (0 : E) 1) ≃ₘ^m⟮(𝓡 n).tangent,
      (𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))⟯
      sphere (0 : E) 1 × EuclideanSpace ℝ (Fin n)) := by
  obtain ⟨S⟩ :=
    nonempty_skewAdjointCliffordSystem_of_finrank_eq_succ (Fact.out : finrank ℝ E = n + 1) hn
  exact ⟨S.tangentBundleDiffeomorph (Fintype.card_fin n) m⟩

/-- For `n ∈ {0, 1, 3, 7}`, the tangent bundle of `sphere (0 : E) 1` is `C^m`-diffeomorphic to the
total space of `Bundle.Trivial (sphere (0 : E) 1) (EuclideanSpace ℝ (Fin n))` (for every
`m : ℕ∞ω`). -/
theorem nonempty_tangentBundleTrivialDiffeomorph_sphere (m : ℕ∞ω)
    (hn : n = 0 ∨ n = 1 ∨ n = 3 ∨ n = 7) :
    Nonempty (TangentBundle (𝓡 n) (sphere (0 : E) 1) ≃ₘ^m⟮(𝓡 n).tangent,
      (𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))⟯
      TotalSpace (EuclideanSpace ℝ (Fin n))
        (Bundle.Trivial (sphere (0 : E) 1) (EuclideanSpace ℝ (Fin n)))) := by
  obtain ⟨S⟩ :=
    nonempty_skewAdjointCliffordSystem_of_finrank_eq_succ (Fact.out : finrank ℝ E = n + 1) hn
  exact ⟨S.tangentBundleTrivialDiffeomorph (Fintype.card_fin n) m⟩

end ParallelizableSpheres

end TauCeti
