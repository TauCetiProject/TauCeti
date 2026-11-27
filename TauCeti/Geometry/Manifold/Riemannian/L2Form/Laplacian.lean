/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.L2Form.HodgeDecomposition

import TauCeti.LinearAlgebra.LinearPMap.Basic

/-!
# The Hodge Laplacian on `L²` forms

On an oriented Riemannian manifold `M` of dimension `m = k + 2 + l`, this file realizes the Hodge
Laplacian `Δ = d d* + d* d` of `(k + 1)`-forms as a partial linear map
`TauCeti.L2Form.hodgeLaplacian o hkl` on the space `L²Ωᵏ⁺¹(M)` of square-integrable forms. It is the
Laplacian `LinearPMap.hodgeLaplacian` of the Hilbert complex formed by the exterior derivative of
compactly supported smooth `k`-forms and the weak exterior derivative of `(k + 1)`-forms, whose
harmonic space is `TauCeti.L2Form.harmonicSpace o hkl`. Explicitly
(`TauCeti.L2Form.hodgeLaplacian_def`),

`Δ = (d*_w)† d*_w + (d_w)† d_w`

with `d_w` the weak exterior derivative and `d*_w` the weak codifferential; their adjoints are the
closures of `d` and of `d*` on compactly supported smooth forms. Its domain consists of the
`L²` forms `ω` with `d*_w ω` in the domain of the closure of `d` and `d_w ω` in the domain of the
closure of `d*`.

On an oriented boundaryless manifold:

* `Δ` is self-adjoint (`TauCeti.L2Form.isSelfAdjoint_hodgeLaplacian`) and nonnegative
  (`TauCeti.L2Form.inner_hodgeLaplacian_self_nonneg`);
* its kernel is the `L²` harmonic space of weakly closed and weakly coclosed forms
  (`TauCeti.L2Form.ker_hodgeLaplacian`);
* it extends the Hodge Laplacian `d*d + dd*` of compactly supported smooth forms
  (`TauCeti.L2Form.toL2Form_mem_graph_hodgeLaplacian`, `TauCeti.L2Form.hodgeLaplacian_toL2Form`).

On a compact manifold every smooth form is compactly supported, so `Δ` extends the Hodge Laplacian
of all smooth `(k + 1)`-forms. That its domain consists of the forms of Sobolev class `H²`, and
that its resolvent is compact, are statements of elliptic regularity which are not proved here.
As for the harmonic space, degrees `0` and `m` are not covered.

## Main definitions

* `TauCeti.L2Form.hodgeLaplacian`: the Hodge Laplacian on `L²Ωᵏ⁺¹(M)`.

## References

* M. P. Gaffney, *Hilbert space methods in the theory of harmonic integrals*, Trans. Amer. Math.
  Soc. 78 (1955), 426–444.
* J. Brüning, M. Lesch, *Hilbert complexes*, J. Funct. Anal. 108 (1992), §2.
-/

public section

noncomputable section

open Bundle MeasureTheory
open scoped Manifold ContDiff InnerProductSpace LinearPMap

namespace TauCeti

namespace L2Form

open compactlySupportedForms

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M] [IsManifold I ∞ M]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)] {m k l : ℕ}

/-- The Riemannian volume and the `L²` metric need only a continuous metric. -/
local instance instIsContinuousRiemannianBundleTangentSpaceLaplacian :
    IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
  IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle
    (IB := I) (n := 1) (F := E) (V := fun x : M ↦ TangentSpace I x)

/-- The **Hodge Laplacian on `L²` forms** of an oriented Riemannian manifold of dimension
`m = k + 2 + l`: the Laplacian `d d* + d* d` on `L²Ωᵏ⁺¹(M)` of the Hilbert complex formed by the
exterior derivative of compactly supported smooth `k`-forms and the weak exterior derivative of
`(k + 1)`-forms. Its first term is the closure of `d` composed with the weak codifferential, and
its second term the closure of `d*` composed with the weak exterior derivative. -/
def hodgeLaplacian (o : Manifold.Orientation I M (Fin m)) (hkl : k + 1 + 1 + l = m) :
    L2Form I M (k + 1) →ₗ.[ℝ] L2Form I M (k + 1) :=
  LinearPMap.hodgeLaplacian (toL2Operator (compactlySupportedForms.mextDerivₗ I M k))
    (weakExtDeriv o hkl)

/-- The Hodge Laplacian on `L²` forms is `(d*_w)† d*_w + (d_w)† d_w`, for the weak codifferential
`d*_w` and the weak exterior derivative `d_w`. -/
theorem hodgeLaplacian_def (o : Manifold.Orientation I M (Fin m)) (hkl : k + 1 + 1 + l = m) :
    hodgeLaplacian o hkl =
      (weakCodifferential I M k).adjointComp + (weakExtDeriv o hkl).adjointComp := by
  rw [hodgeLaplacian, LinearPMap.hodgeLaplacian_def, weakCodifferential_def]

variable [T2Space M] [BoundarylessManifold I M]

/-- The adjoint of the exterior derivative of compactly supported smooth forms, the weak
codifferential, is densely defined. -/
private theorem dense_domain_adjoint_toL2Operator_mextDerivₗ (o : Manifold.Orientation I M (Fin m))
    (hkl : k + 1 + 1 + l = m) :
    Dense ((toL2Operator (compactlySupportedForms.mextDerivₗ I M k))†.domain :
      Set (L2Form I M (k + 1))) := by
  rw [← weakCodifferential_def]
  exact dense_domain_weakCodifferential o (l := l + 1) (by omega)

/-- **The Hodge Laplacian on `L²` forms is self-adjoint** on an oriented boundaryless Riemannian
manifold. -/
theorem isSelfAdjoint_hodgeLaplacian (o : Manifold.Orientation I M (Fin m))
    (hkl : k + 1 + 1 + l = m) : IsSelfAdjoint (hodgeLaplacian o hkl) :=
  LinearPMap.isSelfAdjoint_hodgeLaplacian (dense_domain_toL2Operator _)
    (dense_domain_adjoint_toL2Operator_mextDerivₗ o hkl) (isClosed_weakExtDeriv o hkl)
    (dense_domain_weakExtDeriv o hkl) (range_toL2Operator_mextDerivₗ_le_ker_weakExtDeriv o hkl)

/-- **The Hodge Laplacian on `L²` forms is nonnegative** on an oriented boundaryless Riemannian
manifold: `0 ≤ ⟪Δu, u⟫`. -/
theorem inner_hodgeLaplacian_self_nonneg (o : Manifold.Orientation I M (Fin m))
    (hkl : k + 1 + 1 + l = m) (u : (hodgeLaplacian o hkl).domain) :
    0 ≤ ⟪hodgeLaplacian o hkl u, (u : L2Form I M (k + 1))⟫_ℝ := by
  have h := LinearPMap.inner_hodgeLaplacian_self
    (dense_domain_adjoint_toL2Operator_mextDerivₗ o hkl) (dense_domain_weakExtDeriv o hkl) u
  rw [RCLike.ofReal_real_eq_id, id] at h
  exact (add_nonneg (sq_nonneg _) (sq_nonneg _)).trans_eq h.symm

/-- **The kernel of the Hodge Laplacian on `L²` forms is the `L²` harmonic space** of weakly
closed and weakly coclosed forms, on an oriented boundaryless Riemannian manifold. -/
theorem ker_hodgeLaplacian (o : Manifold.Orientation I M (Fin m)) (hkl : k + 1 + 1 + l = m) :
    (hodgeLaplacian o hkl).ker = harmonicSpace o hkl := by
  rw [harmonicSpace_def, weakCodifferential_def, ← LinearPMap.harmonicSpace_def]
  exact LinearPMap.ker_hodgeLaplacian (dense_domain_adjoint_toL2Operator_mextDerivₗ o hkl)
    (dense_domain_weakExtDeriv o hkl)

/-- On an oriented boundaryless Riemannian manifold, the Hodge Laplacian on `L²` forms extends the
Hodge Laplacian of compactly supported smooth forms: `(α, Δα)` lies on its graph. -/
theorem toL2Form_mem_graph_hodgeLaplacian (o : Manifold.Orientation I M (Fin m))
    (hkl : k + 1 + 1 + l = m) {l' : ℕ} (hkl' : k + 1 + l' = m)
    (α : compactlySupportedForms I M (k + 1)) :
    (toL2Form I M (k + 1) α, toL2Form I M (k + 1) (compactlySupportedForms.hodgeLaplacian o hkl' α))
      ∈ (hodgeLaplacian o hkl).graph := by
  obtain rfl : l' = l + 1 := by omega
  rw [hodgeLaplacian, LinearPMap.mem_graph_hodgeLaplacian_iff]
  -- The witnesses are `d*α`, `dd*α`, `dα` and `d*dα`, as `L²` forms.
  refine ⟨toL2Form I M k (codifferential o hkl' α),
    toL2Form I M (k + 1) (compactlySupportedForms.mextDerivₗ I M k (codifferential o hkl' α)),
    toL2Form I M (k + 1 + 1) (compactlySupportedForms.mextDerivₗ I M (k + 1) α),
    toL2Form I M (k + 1) (codifferential o hkl (compactlySupportedForms.mextDerivₗ I M (k + 1) α)),
    ?_, ?_, ?_, ?_, ?_⟩
  · rw [← weakCodifferential_def, ← LinearPMap.exists_apply_eq_iff_mem_graph]
    exact ⟨_, weakCodifferential_toL2Form o hkl' α
      (toL2Form_mem_domain_weakCodifferential o hkl' α)⟩
  · -- The adjoint of the weak codifferential extends `d` on compactly supported smooth forms.
    have hle : toL2Operator (compactlySupportedForms.mextDerivₗ I M k) ≤
        (toL2Operator (compactlySupportedForms.mextDerivₗ I M k))†† :=
      (LinearPMap.adjoint_isFormalAdjoint
        (dense_domain_toL2Operator (compactlySupportedForms.mextDerivₗ I M k))).le_adjoint
        (dense_domain_adjoint_toL2Operator_mextDerivₗ o hkl)
    exact LinearPMap.le_graph_iff.2 hle ((mem_graph_toL2Operator_iff _).2 ⟨_, rfl, rfl⟩)
  · rw [← LinearPMap.exists_apply_eq_iff_mem_graph]
    exact ⟨_, weakExtDeriv_toL2Form o hkl α (toL2Form_mem_domain_weakExtDeriv o hkl α)⟩
  · -- The adjoint of the weak exterior derivative extends `d*` on compactly supported smooth forms.
    have hle : toL2Operator (codifferential o hkl) ≤ (weakExtDeriv o hkl)† := by
      rw [weakExtDeriv_def]
      exact (LinearPMap.adjoint_isFormalAdjoint
        (dense_domain_toL2Operator (codifferential o hkl))).le_adjoint
        (by rw [← weakExtDeriv_def]; exact dense_domain_weakExtDeriv o hkl)
    exact LinearPMap.le_graph_iff.2 hle ((mem_graph_toL2Operator_iff _).2 ⟨_, rfl, rfl⟩)
  · rw [← map_add]
    congr 1
    ext1
    rw [compactlySupportedForms.coe_hodgeLaplacian,
      SmoothForm.hodgeLaplacian_add_one_add_one o hkl' hkl, Submodule.coe_add, coe_mextDerivₗ,
      coe_codifferential, coe_codifferential, coe_mextDerivₗ]
    exact add_comm _ _

/-- On an oriented boundaryless Riemannian manifold, the class of a compactly supported smooth
`(k + 1)`-form lies in the domain of the Hodge Laplacian on `L²` forms. -/
theorem toL2Form_mem_domain_hodgeLaplacian (o : Manifold.Orientation I M (Fin m))
    (hkl : k + 1 + 1 + l = m) (α : compactlySupportedForms I M (k + 1)) :
    toL2Form I M (k + 1) α ∈ (hodgeLaplacian o hkl).domain :=
  LinearPMap.mem_domain_of_mem_graph
    (toL2Form_mem_graph_hodgeLaplacian o hkl (l' := l + 1) (by omega) α)

/-- On an oriented boundaryless Riemannian manifold, the Hodge Laplacian on `L²` forms of the class
of a compactly supported smooth `(k + 1)`-form `α` is the class of `Δα = d*dα + dd*α`. -/
theorem hodgeLaplacian_toL2Form (o : Manifold.Orientation I M (Fin m)) (hkl : k + 1 + 1 + l = m)
    {l' : ℕ} (hkl' : k + 1 + l' = m) (α : compactlySupportedForms I M (k + 1))
    (h : toL2Form I M (k + 1) α ∈ (hodgeLaplacian o hkl).domain) :
    hodgeLaplacian o hkl ⟨toL2Form I M (k + 1) α, h⟩ =
      toL2Form I M (k + 1) (compactlySupportedForms.hodgeLaplacian o hkl' α) :=
  ((LinearPMap.image_iff h).2 (toL2Form_mem_graph_hodgeLaplacian o hkl hkl' α)).symm

end L2Form

end TauCeti
