/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Boundary.SecondFundamentalForm.Basic
public import Mathlib.Analysis.InnerProductSpace.Trace
import TauCeti.Analysis.InnerProductSpace.Nondegenerate
import TauCeti.Geometry.Manifold.MFDeriv.Slice

/-!
# The Weingarten map, principal curvatures and mean curvature of the boundary

Let `M` be a Riemannian manifold with boundary modelled on the half-space `𝓡∂ (n + 1)`, let
`q ∈ ∂M`, and let `ι : ∂M → M` be the inclusion. The boundary carries the induced metric
`h_q(u, w) = ⟨dι u, dι w⟩` on its tangent space `T_q∂M` (`TauCeti.boundaryInducedForm`), and
the second fundamental form `II_q` (`TauCeti.boundarySecondFundamentalForm`). The **Weingarten
map** `S_q : T_q∂M → T_q∂M` is defined by `h(S_q u, w) = II_q(u, w)`. It is `h`-self-adjoint. Its
eigenvalues, the **principal curvatures** `κ₁ ≥ ⋯ ≥ κₙ`, are real, and `II_q` is diagonal in an
`h`-orthonormal basis of **principal directions**. The **mean curvature** is the average
`H(q) = tr S_q / n` (for `n ≥ 1`).

The Weingarten equation identifies `S_q` with the covariant derivative of the outward unit normal:
for every vector field `N` differentiable at `q` and equal to `ν_out` along `∂M` near `q`,
`∇_{dι u} N = dι (S_q u)`. In particular `∇_{dι u} N` is tangent to the boundary.

With these conventions the unit sphere bounding the closed unit ball has `S = id`, all principal
curvatures `1` and `H = 1`.

## Main declarations

* `TauCeti.boundaryWeingarten`: the Weingarten map `S_q`, with
  `TauCeti.boundaryInducedForm_boundaryWeingarten`: `h(S_q u, w) = II_q(u, w)`, and
  `TauCeti.boundaryInducedForm_boundaryWeingarten_comm`: `S_q` is `h`-self-adjoint.
* `TauCeti.leviCivitaConnection_eq_mfderiv_boundaryWeingarten`: the Weingarten equation
  `∇_{dι u} N = dι (S_q u)`.
* `TauCeti.boundaryPrincipalCurvatures`, `TauCeti.boundaryPrincipalDirection`: the principal
  curvatures, in decreasing order, and an `h`-orthonormal basis of principal directions,
  bundled as `TauCeti.boundaryPrincipalBasis`
  (`TauCeti.boundaryWeingarten_boundaryPrincipalDirection`,
  `TauCeti.boundaryInducedForm_boundaryPrincipalDirection`), in which `II_q` is diagonal
  (`TauCeti.boundarySecondFundamentalForm_boundaryPrincipalDirection`).
* `TauCeti.boundaryMeanCurvature`: the mean curvature `H(q) = tr S_q / n`, with
  `TauCeti.sum_boundarySecondFundamentalForm_eq_mul_boundaryMeanCurvature`: `tr_h II = n H`, the
  sum of `II_q(e_i, e_i)` over every `h`-orthonormal basis `(e_i)`, and
  `TauCeti.mul_boundaryMeanCurvature`, `TauCeti.boundaryMeanCurvature_eq_sum_div`: `n H` is the
  sum of the principal curvatures, `H` their average.
* `TauCeti.boundaryWeingarten_eq_smul_id_iff`: `S_q = c • id ↔ II_q = c • h`, in which case
  every principal curvature and, for `n ≥ 1`, the mean curvature is `c`
  (`TauCeti.boundaryPrincipalCurvatures_eq_of_boundaryWeingarten_eq_smul`,
  `TauCeti.boundaryMeanCurvature_eq_of_boundaryWeingarten_eq_smul`).

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018), Chapter 8.
-/

public section

noncomputable section

open Bundle Filter
open scoped Manifold ContDiff InnerProductSpace Topology

namespace TauCeti

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (n + 1)) M] [IsManifold (𝓡∂ (n + 1)) 2 M]
  [RiemannianBundle (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x)]
  [IsContMDiffRiemannianBundle (𝓡∂ (n + 1)) 1 (EuclideanSpace ℝ (Fin (n + 1)))
    (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x)]

/-! ### The Weingarten map -/

/-- The **Weingarten map** `S_q : T_q∂M → T_q∂M` of the boundary at `q ∈ ∂M`, defined by
`h(S_q u, w) = II_q(u, w)` for the induced metric `h` and the second fundamental form `II`. -/
def boundaryWeingarten (q : (𝓡∂ (n + 1)).boundary M) :
    Module.End ℝ (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) q) :=
  (boundarySecondFundamentalForm q).symmCompOfNondegenerate (boundaryInducedForm q)
    (boundaryInducedForm_nondegenerate q)

/-- **The defining property of the Weingarten map**: `h(S_q u, w) = II_q(u, w)`. -/
@[simp]
theorem boundaryInducedForm_boundaryWeingarten (q : (𝓡∂ (n + 1)).boundary M)
    (u w : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) q) :
    boundaryInducedForm q (boundaryWeingarten q u) w = boundarySecondFundamentalForm q u w :=
  LinearMap.BilinForm.symmCompOfNondegenerate_left_apply _ _ w u

/-- The Weingarten map is the unique endomorphism `S` of `T_q∂M` with `h(S u, w) = II_q(u, w)`. -/
theorem eq_boundaryWeingarten_iff (q : (𝓡∂ (n + 1)).boundary M)
    (S : Module.End ℝ (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) q)) :
    S = boundaryWeingarten q ↔
      ∀ u w, boundaryInducedForm q (S u) w = boundarySecondFundamentalForm q u w := by
  refine ⟨fun h ↦ h ▸ boundaryInducedForm_boundaryWeingarten q, fun h ↦ ?_⟩
  ext u
  refine eq_of_forall_inner_comp (injective_mfderiv_subtypeVal_boundary q) fun w ↦ ?_
  rw [ContinuousLinearMap.coe_coe, ← boundaryInducedForm_apply, h,
    ← boundaryInducedForm_boundaryWeingarten, boundaryInducedForm_apply]

/-- The Weingarten map is the scalar `c` exactly when the second fundamental form is `c` times the
induced metric: `S_q = c • id ↔ II_q = c • h`. -/
theorem boundaryWeingarten_eq_smul_id_iff (q : (𝓡∂ (n + 1)).boundary M) (c : ℝ) :
    boundaryWeingarten q = c • LinearMap.id ↔
      boundarySecondFundamentalForm q = c • boundaryInducedForm q := by
  rw [eq_comm, eq_boundaryWeingarten_iff, LinearMap.ext_iff₂]
  refine forall₂_congr fun u w ↦ ?_
  simp only [LinearMap.smul_apply, LinearMap.id_apply, map_smul, eq_comm]

/-- **The Weingarten map is self-adjoint** for the induced metric: `h(S_q u, w) = h(u, S_q w)`. -/
theorem boundaryInducedForm_boundaryWeingarten_comm (q : (𝓡∂ (n + 1)).boundary M)
    (u w : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) q) :
    boundaryInducedForm q (boundaryWeingarten q u) w =
      boundaryInducedForm q u (boundaryWeingarten q w) := by
  rw [boundaryInducedForm_boundaryWeingarten, (boundaryInducedForm_isSymm q).eq,
    boundaryInducedForm_boundaryWeingarten, (boundarySecondFundamentalForm_isSymm q).eq]

/-! ### The Weingarten equation -/

/-- **The Weingarten equation.** Let `N` be a vector field on `M`, differentiable at `q ∈ ∂M` and
equal to the outward unit normal at the boundary points near `q`. Then `∇_{dι u} N = dι (S_q u)`.
In particular `∇_{dι u} N` is tangent to the boundary, and `dι (S_q u)` is its tangential part. -/
theorem leviCivitaConnection_eq_mfderiv_boundaryWeingarten (q : (𝓡∂ (n + 1)).boundary M)
    (u : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) q)
    {N : (y : M) → TangentSpace (𝓡∂ (n + 1)) y} (hN : MDiffAt (T% N) (q : M))
    (hNν : ∀ᶠ p : (𝓡∂ (n + 1)).boundary M in 𝓝 q, N p = outwardUnitNormal p) :
    CovariantDerivative.leviCivitaConnection (𝓡∂ (n + 1)) M N q
        (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡∂ (n + 1))
          (Subtype.val : (𝓡∂ (n + 1)).boundary M → M) q u) =
      mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡∂ (n + 1))
        (Subtype.val : (𝓡∂ (n + 1)).boundary M → M) q (boundaryWeingarten q u) := by
  -- `⟨N, N⟩ = 1` along the boundary near `q`, so its derivative along `dι u` vanishes.
  have h1 : (fun y ↦ ⟪N y, N y⟫_ℝ) ∘ (Subtype.val : (𝓡∂ (n + 1)).boundary M → M) =ᶠ[𝓝 q]
      fun _ ↦ (1 : ℝ) := by
    filter_upwards [hNν] with p hp
    simp [hp, norm_outwardUnitNormal]
  have h0 : mvfderiv (𝓡∂ (n + 1)) (fun y ↦ ⟪N y, N y⟫_ℝ) q
      (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡∂ (n + 1))
        (Subtype.val : (𝓡∂ (n + 1)).boundary M → M) q u) = 0 :=
    mfderiv_mfderiv_apply_eq_zero_of_comp_eventuallyEq_const (K := 𝓘(ℝ, ℝ)) h1 u
  -- Metric compatibility: `d⟨N, N⟩(dι u) = 2 ⟨∇_{dι u} N, N(q)⟩`.
  have hc :=
    (CovariantDerivative.isMetricCompatible_leviCivitaConnection (𝓡∂ (n + 1)) (M := M)
      ).mvfderiv_inner_eq (x := (q : M))
      (FiberBundle.extend (EuclideanSpace ℝ (Fin (n + 1)))
        (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡∂ (n + 1))
          (Subtype.val : (𝓡∂ (n + 1)).boundary M → M) q u)) hN hN
  simp only [FiberBundle.extend_apply_self] at hc
  rw [h0, real_inner_comm (N q)] at hc
  -- Hence `∇_{dι u} N` is orthogonal to the normal, so it is `dι v` for some `v`.
  have hmem : CovariantDerivative.leviCivitaConnection (𝓡∂ (n + 1)) M N q
      (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡∂ (n + 1))
        (Subtype.val : (𝓡∂ (n + 1)).boundary M → M) q u) ∈ boundaryTangentSpace q := by
    rw [mem_boundaryTangentSpace_iff_inner_inwardUnitNormal_eq_zero, inwardUnitNormal_def,
      inner_neg_right, ← hNν.self_of_nhds, real_inner_comm]
    linarith
  rw [boundaryTangentSpace_def] at hmem
  obtain ⟨v, hv⟩ := hmem
  rw [ContinuousLinearMap.coe_coe] at hv
  rw [← hv]
  congr 1
  -- `h(v, w) = ⟨∇_{dι u} N, dι w⟩ = II_q(u, w) = h(S_q u, w)` for every `w`.
  refine eq_of_forall_inner_comp (injective_mfderiv_subtypeVal_boundary q) fun w ↦ ?_
  rw [ContinuousLinearMap.coe_coe, hv,
    ← boundarySecondFundamentalForm_apply_eq_inner_of_eq_outwardUnitNormal q u w hN hNν,
    ← boundaryInducedForm_boundaryWeingarten, boundaryInducedForm_apply]

/-! ### Principal curvatures and principal directions -/

/-- The Weingarten map transported to the tangent space `T_q∂M ⊆ T_qM` of the boundary along
`TauCeti.boundaryTangentEquiv`. It is symmetric for the inner product of `T_qM`
(`TauCeti.isSymmetric_boundaryWeingartenTangent`). -/
def boundaryWeingartenTangent (q : (𝓡∂ (n + 1)).boundary M) :
    Module.End ℝ (boundaryTangentSpace q) :=
  (boundaryTangentEquiv q).conj (boundaryWeingarten q)

/-- `TauCeti.boundaryWeingartenTangent` is conjugate to the Weingarten map. -/
@[simp]
theorem boundaryWeingartenTangent_boundaryTangentEquiv (q : (𝓡∂ (n + 1)).boundary M)
    (u : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) q) :
    boundaryWeingartenTangent q (boundaryTangentEquiv q u) =
      boundaryTangentEquiv q (boundaryWeingarten q u) := by
  simp [boundaryWeingartenTangent, LinearEquiv.conj_apply]

/-- The Weingarten map transported to `T_q∂M ⊆ T_qM` is symmetric. -/
theorem isSymmetric_boundaryWeingartenTangent (q : (𝓡∂ (n + 1)).boundary M) :
    (boundaryWeingartenTangent q).IsSymmetric := by
  intro a b
  obtain ⟨u, rfl⟩ := (boundaryTangentEquiv q).surjective a
  obtain ⟨w, rfl⟩ := (boundaryTangentEquiv q).surjective b
  rw [boundaryWeingartenTangent_boundaryTangentEquiv,
    boundaryWeingartenTangent_boundaryTangentEquiv,
    ← boundaryInducedForm_eq_inner_boundaryTangentEquiv,
    ← boundaryInducedForm_eq_inner_boundaryTangentEquiv,
    boundaryInducedForm_boundaryWeingarten_comm]

/-- The **principal curvatures** `κ₁ ≥ ⋯ ≥ κₙ` of the boundary at `q ∈ ∂M`: the eigenvalues of the
Weingarten map `S_q`, which is self-adjoint for the induced metric, in decreasing order. -/
def boundaryPrincipalCurvatures (q : (𝓡∂ (n + 1)).boundary M) : Fin n → ℝ :=
  (isSymmetric_boundaryWeingartenTangent q).eigenvalues (finrank_boundaryTangentSpace q)

/-- The **principal directions** of the boundary at `q ∈ ∂M`: a basis of the tangent space of the
boundary, orthonormal for the induced metric, of eigenvectors of the Weingarten map `S_q`, the
`i`-th with eigenvalue the `i`-th principal curvature. As a `Module.Basis`, it is
`TauCeti.boundaryPrincipalBasis`. -/
def boundaryPrincipalDirection (q : (𝓡∂ (n + 1)).boundary M) (i : Fin n) :
    TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) q :=
  (boundaryTangentEquiv q).symm
    ((isSymmetric_boundaryWeingartenTangent q).eigenvectorBasis (finrank_boundaryTangentSpace q) i)

/-- The principal directions at `q ∈ ∂M`, bundled as a basis of the tangent space of the
boundary. -/
def boundaryPrincipalBasis (q : (𝓡∂ (n + 1)).boundary M) :
    Module.Basis (Fin n) ℝ (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) q) :=
  ((isSymmetric_boundaryWeingartenTangent q).eigenvectorBasis
    (finrank_boundaryTangentSpace q)).toBasis.map (boundaryTangentEquiv q).symm

/-- The vectors of `TauCeti.boundaryPrincipalBasis` are the principal directions. -/
@[simp]
theorem coe_boundaryPrincipalBasis (q : (𝓡∂ (n + 1)).boundary M) :
    ⇑(boundaryPrincipalBasis q) = boundaryPrincipalDirection q := by
  ext1 i
  rw [boundaryPrincipalBasis, Module.Basis.map_apply, OrthonormalBasis.coe_toBasis,
    boundaryPrincipalDirection]

/-- The principal curvatures are listed in decreasing order. -/
theorem boundaryPrincipalCurvatures_antitone (q : (𝓡∂ (n + 1)).boundary M) :
    Antitone (boundaryPrincipalCurvatures q) :=
  LinearMap.IsSymmetric.eigenvalues_antitone _ _

/-- The `i`-th principal direction is an eigenvector of the Weingarten map for the `i`-th
principal curvature: `S_q eᵢ = κᵢ eᵢ`. -/
@[simp]
theorem boundaryWeingarten_boundaryPrincipalDirection (q : (𝓡∂ (n + 1)).boundary M) (i : Fin n) :
    boundaryWeingarten q (boundaryPrincipalDirection q i) =
      boundaryPrincipalCurvatures q i • boundaryPrincipalDirection q i := by
  apply (boundaryTangentEquiv q).injective
  rw [← boundaryWeingartenTangent_boundaryTangentEquiv, boundaryPrincipalDirection,
    LinearEquiv.apply_symm_apply, LinearMap.IsSymmetric.apply_eigenvectorBasis, map_smul,
    LinearEquiv.apply_symm_apply, boundaryPrincipalCurvatures, RCLike.ofReal_real_eq_id, id]

/-- The principal directions are orthonormal for the induced metric. -/
@[simp]
theorem boundaryInducedForm_boundaryPrincipalDirection (q : (𝓡∂ (n + 1)).boundary M)
    (i j : Fin n) :
    boundaryInducedForm q (boundaryPrincipalDirection q i) (boundaryPrincipalDirection q j) =
      if i = j then 1 else 0 := by
  rw [boundaryInducedForm_eq_inner_boundaryTangentEquiv, boundaryPrincipalDirection,
    boundaryPrincipalDirection, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply,
    OrthonormalBasis.inner_eq_ite]

/-- **The second fundamental form is diagonal in the principal directions**:
`II_q(eᵢ, eⱼ) = κᵢ δᵢⱼ`. -/
@[simp]
theorem boundarySecondFundamentalForm_boundaryPrincipalDirection (q : (𝓡∂ (n + 1)).boundary M)
    (i j : Fin n) :
    boundarySecondFundamentalForm q (boundaryPrincipalDirection q i)
        (boundaryPrincipalDirection q j) =
      if i = j then boundaryPrincipalCurvatures q i else 0 := by
  rw [← boundaryInducedForm_boundaryWeingarten, boundaryWeingarten_boundaryPrincipalDirection,
    map_smul, LinearMap.smul_apply, boundaryInducedForm_boundaryPrincipalDirection]
  split_ifs <;> simp

/-- The principal directions are nonzero. -/
theorem boundaryPrincipalDirection_ne_zero (q : (𝓡∂ (n + 1)).boundary M) (i : Fin n) :
    boundaryPrincipalDirection q i ≠ 0 := fun h ↦ by
  have := boundaryInducedForm_boundaryPrincipalDirection q i i
  simp [h] at this

/-- **The principal curvatures are the eigenvalues of the Weingarten map.** -/
theorem hasEigenvalue_boundaryWeingarten_iff (q : (𝓡∂ (n + 1)).boundary M) (μ : ℝ) :
    Module.End.HasEigenvalue (boundaryWeingarten q) μ ↔
      ∃ i, boundaryPrincipalCurvatures q i = μ := by
  constructor
  · intro hμ
    obtain ⟨x, hx⟩ := hμ.exists_hasEigenvector
    refine (isSymmetric_boundaryWeingartenTangent q).exists_eigenvalues_eq
      (finrank_boundaryTangentSpace q)
      (Module.End.hasEigenvalue_of_hasEigenvector (x := boundaryTangentEquiv q x) ⟨?_, ?_⟩)
    · rw [Module.End.mem_eigenspace_iff, boundaryWeingartenTangent_boundaryTangentEquiv,
        Module.End.mem_eigenspace_iff.mp hx.1, map_smul]
    · simpa using hx.2
  · rintro ⟨i, rfl⟩
    exact Module.End.hasEigenvalue_of_hasEigenvector
      ⟨Module.End.mem_eigenspace_iff.mpr (boundaryWeingarten_boundaryPrincipalDirection q i),
        boundaryPrincipalDirection_ne_zero q i⟩

/-- If the Weingarten map is the scalar `c`, then every principal curvature is `c`. -/
theorem boundaryPrincipalCurvatures_eq_of_boundaryWeingarten_eq_smul
    {q : (𝓡∂ (n + 1)).boundary M} {c : ℝ} (h : boundaryWeingarten q = c • LinearMap.id)
    (i : Fin n) : boundaryPrincipalCurvatures q i = c := by
  have h' := boundaryWeingarten_boundaryPrincipalDirection q i
  rw [h, LinearMap.smul_apply, LinearMap.id_apply] at h'
  exact smul_left_injective ℝ (boundaryPrincipalDirection_ne_zero q i) h'.symm

/-! ### Mean curvature -/

/-- The **mean curvature** `H(q) = tr S_q / n` of the boundary at `q ∈ ∂M`, the average of the
principal curvatures (`TauCeti.mul_boundaryMeanCurvature`). It is meaningful for `n ≥ 1`; for
`n = 0` it is `0`. -/
def boundaryMeanCurvature (q : (𝓡∂ (n + 1)).boundary M) : ℝ :=
  LinearMap.trace ℝ _ (boundaryWeingarten q) / n

/-- The defining formula of `TauCeti.boundaryMeanCurvature`: `H(q) = tr S_q / n`. -/
theorem boundaryMeanCurvature_def (q : (𝓡∂ (n + 1)).boundary M) :
    boundaryMeanCurvature q = LinearMap.trace ℝ _ (boundaryWeingarten q) / n :=
  (rfl)

/-- The trace of the Weingarten map is the sum of the principal curvatures. -/
theorem trace_boundaryWeingarten (q : (𝓡∂ (n + 1)).boundary M) :
    LinearMap.trace ℝ _ (boundaryWeingarten q) = ∑ i, boundaryPrincipalCurvatures q i := by
  rw [← LinearMap.trace_conj' (boundaryWeingarten q) (boundaryTangentEquiv q)]
  exact (isSymmetric_boundaryWeingartenTangent q).trace_eq_sum_eigenvalues
    (finrank_boundaryTangentSpace q)

/-- The mean curvature is the average of the principal curvatures, `H = (∑ᵢ κᵢ) / n`. -/
theorem boundaryMeanCurvature_eq_sum_div (q : (𝓡∂ (n + 1)).boundary M) :
    boundaryMeanCurvature q = (∑ i, boundaryPrincipalCurvatures q i) / n := by
  rw [boundaryMeanCurvature_def, trace_boundaryWeingarten]

/-- `n H` is the sum of the principal curvatures. -/
theorem mul_boundaryMeanCurvature (q : (𝓡∂ (n + 1)).boundary M) :
    (n : ℝ) * boundaryMeanCurvature q = ∑ i, boundaryPrincipalCurvatures q i := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · rw [boundaryMeanCurvature_eq_sum_div, mul_div_cancel₀ _ (Nat.cast_ne_zero.mpr hn)]

/-- If the Weingarten map is the scalar `c`, then the mean curvature is `c`, for `n ≥ 1`. -/
theorem boundaryMeanCurvature_eq_of_boundaryWeingarten_eq_smul [NeZero n]
    {q : (𝓡∂ (n + 1)).boundary M} {c : ℝ} (h : boundaryWeingarten q = c • LinearMap.id) :
    boundaryMeanCurvature q = c := by
  rw [boundaryMeanCurvature_eq_sum_div]
  simp [boundaryPrincipalCurvatures_eq_of_boundaryWeingarten_eq_smul h, NeZero.ne n]

/-- **`tr_h II = n H`**: for every basis `(eᵢ)` of the tangent space of the boundary at `q`,
orthonormal for the induced metric, `∑ᵢ II_q(eᵢ, eᵢ) = n H(q)`. -/
theorem sum_boundarySecondFundamentalForm_eq_mul_boundaryMeanCurvature
    (q : (𝓡∂ (n + 1)).boundary M) (e : Fin n → TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) q)
    (he : ∀ i j, boundaryInducedForm q (e i) (e j) = if i = j then 1 else 0) :
    ∑ i, boundarySecondFundamentalForm q (e i) (e i) = n * boundaryMeanCurvature q := by
  have hon : Orthonormal ℝ fun i ↦ boundaryTangentEquiv q (e i) := by
    rw [orthonormal_iff_ite]
    intro i j
    rw [← boundaryInducedForm_eq_inner_boundaryTangentEquiv, he]
  have hsp : ⊤ ≤ Submodule.span ℝ (Set.range fun i ↦ boundaryTangentEquiv q (e i)) :=
    (hon.linearIndependent.span_eq_top_of_card_eq_finrank' (by simp)).ge
  rw [mul_boundaryMeanCurvature, ← trace_boundaryWeingarten,
    ← LinearMap.trace_conj' (boundaryWeingarten q) (boundaryTangentEquiv q),
    LinearMap.trace_eq_sum_inner _ (OrthonormalBasis.mk hon hsp)]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [OrthonormalBasis.coe_mk, ← boundaryWeingartenTangent,
    boundaryWeingartenTangent_boundaryTangentEquiv,
    ← boundaryInducedForm_eq_inner_boundaryTangentEquiv,
    ← boundaryInducedForm_boundaryWeingarten_comm, boundaryInducedForm_boundaryWeingarten]
end TauCeti
