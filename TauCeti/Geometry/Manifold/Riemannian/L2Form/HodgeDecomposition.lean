/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.LinearPMap.HilbertComplex.Basic
public import TauCeti.Geometry.Manifold.DeRham.Harmonic
public import TauCeti.Geometry.Manifold.Riemannian.L2Form.Weak

/-!
# The Hodge–Kodaira decomposition of `L²` forms

On an oriented boundaryless Riemannian manifold `M` of dimension `m`, the space `L²Ωᵏ⁺¹(M)` of
square-integrable `(k + 1)`-forms, `k + 2 ≤ m`, splits as the orthogonal sum

`L²Ωᵏ⁺¹(M) = closure (d Ω_cᵏ) ⊕ ℋᵏ⁺¹ ⊕ closure (d* Ω_cᵏ⁺²)`

of the closures of the exterior derivatives and of the codifferentials of compactly supported
smooth forms, and of the space `ℋᵏ⁺¹ = TauCeti.L2Form.harmonicSpace o hkl` of `L²` forms which
are weakly closed and weakly coclosed. This is Kodaira's decomposition. The harmonic space is
the orthogonal complement of the other two summands (`TauCeti.L2Form.harmonicSpace_eq_orthogonal`):
a form lies in it when it is orthogonal to `dα` and `d*β` for all compactly supported smooth
forms `α` and `β`.

The decomposition is that of the Hilbert complex formed by the exterior derivative of compactly
supported smooth `k`-forms and the weak exterior derivative on `(k + 1)`-forms,
`LinearPMap.topologicalClosure_range_sup_harmonicSpace_sup_topologicalClosure_range_adjoint`.
A compactly supported smooth form lies in the harmonic space exactly when it is closed and
coclosed (`TauCeti.L2Form.toL2Form_mem_harmonicSpace_iff`), that is when it is harmonic in the
sense of `TauCeti.harmonicForms`; on a compact manifold every smooth form is compactly supported.
That every form of `ℋᵏ⁺¹` is smooth, and that the two other summands are already closed on a
compact manifold, are statements of elliptic regularity which this decomposition does not
supply.

## Main definitions

* `TauCeti.L2Form.harmonicSpace`: the weakly closed and weakly coclosed `L²` forms.

## Main results

All in the namespace `TauCeti.L2Form`:

* `topologicalClosure_range_sup_harmonicSpace_sup_topologicalClosure_range`: the Hodge–Kodaira
  decomposition; the pairwise orthogonality of its summands is
  `isOrtho_topologicalClosure_range_mextDerivₗ_harmonicSpace`,
  `isOrtho_harmonicSpace_topologicalClosure_range_codifferential` and
  `isOrtho_topologicalClosure_range_mextDerivₗ_topologicalClosure_range_codifferential`.
* `topologicalClosure_range_mextDerivₗ_sup_harmonicSpace`: a weakly closed `L²` form is the sum
  of a limit of smooth exact forms and of a form of the harmonic space.
* `toL2Form_mem_harmonicSpace_iff_mem_harmonicForms`: the compactly supported smooth forms in the
  harmonic space are the harmonic forms.

## References

* K. Kodaira, *Harmonic fields in Riemannian manifolds (generalized potential theory)*, Ann. of
  Math. 50 (1949), 587–665.
* G. de Rham, *Variétés différentiables*, Hermann (1955), §32.
* J. Brüning, M. Lesch, *Hilbert complexes*, J. Funct. Anal. 108 (1992), Lemma 2.1.
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
local instance instIsContinuousRiemannianBundleTangentSpaceHodgeDecomposition :
    IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
  IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle
    (IB := I) (n := 1) (F := E) (V := fun x : M ↦ TangentSpace I x)

/-- The **`L²` harmonic space** `ℋᵏ⁺¹` of an oriented Riemannian manifold of dimension
`m = k + 2 + l`: the square-integrable `(k + 1)`-forms which are weakly closed and weakly
coclosed. It is the harmonic space of the Hilbert complex formed by the exterior derivative of
compactly supported smooth `k`-forms and the weak exterior derivative of `(k + 1)`-forms. -/
def harmonicSpace (o : Manifold.Orientation I M (Fin m)) (hkl : k + 1 + 1 + l = m) :
    Submodule ℝ (L2Form I M (k + 1)) :=
  LinearPMap.harmonicSpace (toL2Operator (compactlySupportedForms.mextDerivₗ I M k))
    (weakExtDeriv o hkl)

/-- The harmonic space is the intersection of the kernels of the weak exterior derivative and of
the weak codifferential. -/
theorem harmonicSpace_def (o : Manifold.Orientation I M (Fin m)) (hkl : k + 1 + 1 + l = m) :
    harmonicSpace o hkl = (weakExtDeriv o hkl).ker ⊓ (weakCodifferential I M k).ker := by
  rw [harmonicSpace, LinearPMap.harmonicSpace_def, weakCodifferential_def]

/-- An `L²` form lies in the harmonic space exactly when it is weakly closed and weakly
coclosed. -/
@[simp]
theorem mem_harmonicSpace_iff (o : Manifold.Orientation I M (Fin m)) (hkl : k + 1 + 1 + l = m)
    {u : L2Form I M (k + 1)} :
    u ∈ harmonicSpace o hkl ↔
      u ∈ (weakExtDeriv o hkl).ker ∧ u ∈ (weakCodifferential I M k).ker := by
  rw [harmonicSpace_def, Submodule.mem_inf]

variable [T2Space M]

/-- **Harmonic forms are orthogonal to exact and coexact forms.** The harmonic space consists of
the `L²` forms orthogonal to the exterior derivatives and to the codifferentials of all compactly
supported smooth forms. -/
theorem harmonicSpace_eq_orthogonal (o : Manifold.Orientation I M (Fin m))
    (hkl : k + 1 + 1 + l = m) :
    harmonicSpace o hkl =
      (LinearMap.range (toL2Form I M (k + 1) ∘ₗ compactlySupportedForms.mextDerivₗ I M k) ⊔
        LinearMap.range (toL2Form I M (k + 1) ∘ₗ codifferential o hkl))ᗮ := by
  rw [← Submodule.inf_orthogonal, ← ker_weakCodifferential, ← ker_weakExtDeriv, inf_comm,
    harmonicSpace_def]

/-- The harmonic space is closed. -/
theorem isClosed_harmonicSpace (o : Manifold.Orientation I M (Fin m))
    (hkl : k + 1 + 1 + l = m) :
    IsClosed (harmonicSpace o hkl : Set (L2Form I M (k + 1))) :=
  LinearPMap.isClosed_harmonicSpace (dense_domain_toL2Operator _) (isClosed_weakExtDeriv o hkl)

/-- The closure of the exterior derivatives of compactly supported smooth forms is orthogonal to
the harmonic space. -/
theorem isOrtho_topologicalClosure_range_mextDerivₗ_harmonicSpace
    (o : Manifold.Orientation I M (Fin m)) (hkl : k + 1 + 1 + l = m) :
    (LinearMap.range (toL2Form I M (k + 1) ∘ₗ
      compactlySupportedForms.mextDerivₗ I M k)).topologicalClosure ⟂ harmonicSpace o hkl := by
  rw [← range_toL2Operator]
  exact LinearPMap.isOrtho_topologicalClosure_range_harmonicSpace (dense_domain_toL2Operator _)

/-- The harmonic space is orthogonal to the closure of the codifferentials of compactly
supported smooth forms. -/
theorem isOrtho_harmonicSpace_topologicalClosure_range_codifferential
    (o : Manifold.Orientation I M (Fin m)) (hkl : k + 1 + 1 + l = m) :
    harmonicSpace o hkl ⟂
      (LinearMap.range (toL2Form I M (k + 1) ∘ₗ codifferential o hkl)).topologicalClosure := by
  rw [Submodule.isOrtho_iff_le, Submodule.orthogonal_closure, harmonicSpace_eq_orthogonal]
  exact Submodule.orthogonal_le le_sup_right

variable [BoundarylessManifold I M]

/-- The closure of the range of the codifferential of compactly supported smooth forms is the
closure of the range of the adjoint of the weak exterior derivative. -/
private theorem topologicalClosure_range_adjoint_weakExtDeriv
    (o : Manifold.Orientation I M (Fin m)) (hkl : k + 1 + 1 + l = m) :
    (LinearMap.range (weakExtDeriv o hkl)†.toFun).topologicalClosure =
      (LinearMap.range (toL2Form I M (k + 1) ∘ₗ codifferential o hkl)).topologicalClosure := by
  rw [LinearPMap.topologicalClosure_range_adjoint_eq_orthogonal_ker (isClosed_weakExtDeriv o hkl)
    (dense_domain_weakExtDeriv o hkl), ker_weakExtDeriv, Submodule.orthogonal_orthogonal_eq_closure]

/-- **Exact and coexact forms are orthogonal**: on an oriented boundaryless manifold, the closures
of the exterior derivatives and of the codifferentials of compactly supported smooth forms are
orthogonal. -/
theorem isOrtho_topologicalClosure_range_mextDerivₗ_topologicalClosure_range_codifferential
    (o : Manifold.Orientation I M (Fin m)) (hkl : k + 1 + 1 + l = m) :
    (LinearMap.range (toL2Form I M (k + 1) ∘ₗ
        compactlySupportedForms.mextDerivₗ I M k)).topologicalClosure ⟂
      (LinearMap.range (toL2Form I M (k + 1) ∘ₗ codifferential o hkl)).topologicalClosure := by
  rw [← range_toL2Operator, ← topologicalClosure_range_adjoint_weakExtDeriv]
  exact LinearPMap.isOrtho_topologicalClosure_range_topologicalClosure_range_adjoint
    (dense_domain_weakExtDeriv o hkl) (range_toL2Operator_mextDerivₗ_le_ker_weakExtDeriv o hkl)

/-- **The Hodge–Kodaira decomposition of weakly closed forms**: on an oriented boundaryless
manifold, the weakly closed `L²` forms are the sums of a limit of exterior derivatives of
compactly supported smooth forms and of a form of the harmonic space. -/
theorem topologicalClosure_range_mextDerivₗ_sup_harmonicSpace (o : Manifold.Orientation I M (Fin m))
    (hkl : k + 1 + 1 + l = m) :
    (LinearMap.range (toL2Form I M (k + 1) ∘ₗ
        compactlySupportedForms.mextDerivₗ I M k)).topologicalClosure ⊔ harmonicSpace o hkl =
      (weakExtDeriv o hkl).ker := by
  rw [← range_toL2Operator]
  exact LinearPMap.topologicalClosure_range_sup_harmonicSpace (dense_domain_toL2Operator _)
    (isClosed_weakExtDeriv o hkl) (range_toL2Operator_mextDerivₗ_le_ker_weakExtDeriv o hkl)

/-- **The Hodge–Kodaira decomposition**: on an oriented boundaryless Riemannian manifold of
dimension `m = k + 2 + l`, every square-integrable `(k + 1)`-form is the sum of a limit of
exterior derivatives of compactly supported smooth forms, of a weakly closed and weakly coclosed
form, and of a limit of codifferentials of compactly supported smooth forms. The three summands
are pairwise orthogonal. -/
theorem topologicalClosure_range_sup_harmonicSpace_sup_topologicalClosure_range
    (o : Manifold.Orientation I M (Fin m)) (hkl : k + 1 + 1 + l = m) :
    (LinearMap.range (toL2Form I M (k + 1) ∘ₗ
        compactlySupportedForms.mextDerivₗ I M k)).topologicalClosure ⊔ harmonicSpace o hkl ⊔
      (LinearMap.range (toL2Form I M (k + 1) ∘ₗ codifferential o hkl)).topologicalClosure =
      ⊤ := by
  rw [← range_toL2Operator, ← topologicalClosure_range_adjoint_weakExtDeriv]
  exact LinearPMap.topologicalClosure_range_sup_harmonicSpace_sup_topologicalClosure_range_adjoint
    (dense_domain_toL2Operator _) (isClosed_weakExtDeriv o hkl) (dense_domain_weakExtDeriv o hkl)
    (range_toL2Operator_mextDerivₗ_le_ker_weakExtDeriv o hkl)

/-- On an oriented boundaryless manifold, a compactly supported smooth `(k + 1)`-form lies in the
harmonic space exactly when it is closed and coclosed. -/
theorem toL2Form_mem_harmonicSpace_iff (o : Manifold.Orientation I M (Fin m))
    (hkl : k + 1 + 1 + l = m) {l' : ℕ} (hkl' : k + 1 + l' = m)
    (α : compactlySupportedForms I M (k + 1)) :
    toL2Form I M (k + 1) α ∈ harmonicSpace o hkl ↔
      mextDerivₗ I (k + 1) (α : SmoothForm I M ℝ (k + 1)) = 0 ∧
        SmoothForm.codifferential o hkl' (α : SmoothForm I M ℝ (k + 1)) = 0 := by
  rw [mem_harmonicSpace_iff, toL2Form_mem_ker_weakExtDeriv_iff,
    toL2Form_mem_ker_weakCodifferential_iff o hkl', ← coe_mextDerivₗ, ← coe_codifferential,
    Submodule.coe_eq_zero, Submodule.coe_eq_zero]

/-- On an oriented boundaryless Riemannian manifold, a compactly supported smooth `(k + 1)`-form
lies in the `L²` harmonic space exactly when it is harmonic. -/
theorem toL2Form_mem_harmonicSpace_iff_mem_harmonicForms (o : Manifold.Orientation I M (Fin m))
    (hkl : k + 1 + 1 + l = m) {l' : ℕ} (hkl' : k + 1 + l' = m)
    (α : compactlySupportedForms I M (k + 1)) :
    toL2Form I M (k + 1) α ∈ harmonicSpace o hkl ↔
      (α : SmoothForm I M ℝ (k + 1)) ∈ harmonicForms o hkl' := by
  have : LocallyCompactSpace H := I.locallyCompactSpace
  have : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace H M
  rw [toL2Form_mem_harmonicSpace_iff o hkl hkl', mem_harmonicForms]
  exact (SmoothForm.hodgeLaplacian_eq_zero_iff o hkl' α.property).symm

end L2Form

end TauCeti
