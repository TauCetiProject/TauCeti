/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.LinearPMap.SelfAdjoint
public import TauCeti.Topology.Algebra.Module.LinearPMap.Basic

/-!
# The Hodge decomposition of a Hilbert complex

Let `d₀ : E →ₗ.[𝕜] F` and `d₁ : F →ₗ.[𝕜] G` be densely defined partial linear maps between
Hilbert spaces, with `d₁` closed and `range d₀ ≤ ker d₁`. This is one segment of a Hilbert complex,
in the sense of Brüning and Lesch; the model is the `L²` de Rham complex, where `d₀` and `d₁` are
the weak exterior derivative in two consecutive degrees. The **harmonic space**
`LinearPMap.harmonicSpace d₀ d₁ = ker d₁ ⊓ ker d₀†` consists of the vectors that are closed for the
complex and coclosed for its adjoint. This file proves the **Hodge decomposition**

`F = closure (range d₀) ⊕ harmonicSpace d₀ d₁ ⊕ closure (range d₁†)`,

an orthogonal decomposition. The characterization of closed ranges by a **Poincaré inequality**,
`LinearPMap.isClosed_range_iff_exists_norm_le_mul_norm`, holds for any closed operator and is in
`TauCeti.Analysis.InnerProductSpace.LinearPMap.ClosedRange`.

For bounded operators with closed range, the decomposition of the kernel is
`ContinuousLinearMap.range_sup_ker_inf_ker_adjoint`. Here the operators are unbounded, as the
exterior derivative is on `L²` forms, so the decomposition uses the closures of the ranges, and
needs no closed range assumption. It rests on the descriptions of closures of ranges as
orthogonal complements of kernels, `LinearPMap.topologicalClosure_range_eq_orthogonal_ker_adjoint`
and `LinearPMap.topologicalClosure_range_adjoint_eq_orthogonal_ker`, in
`TauCeti.Analysis.InnerProductSpace.LinearPMap.SelfAdjoint`.

## Main results

* `LinearPMap.harmonicSpace_eq_orthogonal_sup`: the harmonic space is the orthogonal complement of
  `closure (range d₀) ⊔ closure (range d₁†)`.
* `LinearPMap.topologicalClosure_range_sup_harmonicSpace`: for a complex, the kernel of `d₁` is
  `closure (range d₀) ⊔ harmonicSpace d₀ d₁`, the weak Hodge decomposition of the closed vectors.
* `LinearPMap.topologicalClosure_range_sup_harmonicSpace_sup_topologicalClosure_range_adjoint`:
  the three summands of the Hodge decomposition span `F`; the three orthogonality relations are
  `LinearPMap.isOrtho_topologicalClosure_range_harmonicSpace`,
  `LinearPMap.isOrtho_harmonicSpace_topologicalClosure_range_adjoint` and
  `LinearPMap.isOrtho_topologicalClosure_range_topologicalClosure_range_adjoint`.

## References

* D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to
  numerical stability*, Bull. Amer. Math. Soc. 47 (2010), §3.1.
* D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus, homological techniques,
  and applications*, Acta Numerica 15 (2006), §3.
* J. Brüning, M. Lesch, *Hilbert complexes*, J. Funct. Anal. 108 (1992).
-/

public section

noncomputable section

namespace LinearPMap

variable {𝕜 E F G : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]

/-! ### The harmonic space and the Hodge decomposition -/

section Hodge

variable [CompleteSpace E] {d₀ : E →ₗ.[𝕜] F} {d₁ : F →ₗ.[𝕜] G}

variable (d₀ d₁) in
/-- The **harmonic space** `ker d₁ ⊓ ker d₀†` of a pair of composable partial linear maps
`d₀ : E →ₗ.[𝕜] F` and `d₁ : F →ₗ.[𝕜] G`: the vectors of `F` that are closed for `d₁` and coclosed
for the adjoint of `d₀`. -/
def harmonicSpace : Submodule 𝕜 F :=
  d₁.ker ⊓ d₀†.ker

@[simp]
theorem mem_harmonicSpace_iff {x : F} : x ∈ harmonicSpace d₀ d₁ ↔ x ∈ d₁.ker ∧ x ∈ d₀†.ker :=
  Submodule.mem_inf

/-- Harmonic vectors are closed: they lie in the kernel of `d₁`. -/
theorem harmonicSpace_le_ker : harmonicSpace d₀ d₁ ≤ d₁.ker :=
  inf_le_left

/-- Harmonic vectors are coclosed: they lie in the kernel of `d₀†`. -/
theorem harmonicSpace_le_ker_adjoint : harmonicSpace d₀ d₁ ≤ d₀†.ker :=
  inf_le_right

/-- The harmonic space is closed when `d₁` is closed and `d₀` is densely defined. -/
theorem isClosed_harmonicSpace (hd₀ : Dense (d₀.domain : Set E)) (hc₁ : d₁.IsClosed) :
    _root_.IsClosed (harmonicSpace d₀ d₁ : Set F) :=
  hc₁.isClosed_ker.inter (adjoint_isClosed hd₀).isClosed_ker

/-- The harmonic space consists of the vectors of `ker d₁` orthogonal to the range of `d₀`. -/
theorem harmonicSpace_eq_ker_inf_orthogonal_range (hd₀ : Dense (d₀.domain : Set E)) :
    harmonicSpace d₀ d₁ = d₁.ker ⊓ (LinearMap.range d₀.toFun)ᗮ := by
  rw [harmonicSpace, orthogonal_range_eq_ker_adjoint hd₀]

/-- **Harmonic vectors are orthogonal to exact and coexact ones.** For `d₀` densely defined and
`d₁` closed and densely defined, the harmonic space is the orthogonal complement of
`closure (range d₀) ⊔ closure (range d₁†)`. -/
theorem harmonicSpace_eq_orthogonal_sup [CompleteSpace F] [CompleteSpace G]
    (hd₀ : Dense (d₀.domain : Set E)) (hc₁ : d₁.IsClosed) (hd₁ : Dense (d₁.domain : Set F)) :
    harmonicSpace d₀ d₁ = ((LinearMap.range d₀.toFun).topologicalClosure ⊔
      (LinearMap.range d₁†.toFun).topologicalClosure)ᗮ := by
  rw [← Submodule.inf_orthogonal, topologicalClosure_range_eq_orthogonal_ker_adjoint hd₀,
    topologicalClosure_range_adjoint_eq_orthogonal_ker hc₁ hd₁,
    Submodule.orthogonal_orthogonal_eq_closure, Submodule.orthogonal_orthogonal_eq_closure,
    (adjoint_isClosed hd₀).isClosed_ker.submodule_topologicalClosure_eq,
    hc₁.isClosed_ker.submodule_topologicalClosure_eq, harmonicSpace, inf_comm]

omit [CompleteSpace E] in
/-- In a complex `range d₀ ≤ ker d₁` with `d₁` closed, the closure of the range of `d₀` is still
contained in the kernel of `d₁`. -/
theorem topologicalClosure_range_le_ker (hc₁ : d₁.IsClosed)
    (hcomplex : LinearMap.range d₀.toFun ≤ d₁.ker) :
    (LinearMap.range d₀.toFun).topologicalClosure ≤ d₁.ker :=
  Submodule.topologicalClosure_minimal _ hcomplex hc₁.isClosed_ker

/-- The closure of the range of `d₀` is orthogonal to the harmonic space. -/
theorem isOrtho_topologicalClosure_range_harmonicSpace (hd₀ : Dense (d₀.domain : Set E)) :
    (LinearMap.range d₀.toFun).topologicalClosure ⟂ harmonicSpace d₀ d₁ := by
  rw [Submodule.isOrtho_comm, Submodule.isOrtho_iff_le, Submodule.orthogonal_closure,
    orthogonal_range_eq_ker_adjoint hd₀]
  exact harmonicSpace_le_ker_adjoint

/-- The harmonic space is orthogonal to the closure of the range of `d₁†`. -/
theorem isOrtho_harmonicSpace_topologicalClosure_range_adjoint [CompleteSpace F]
    (hd₁ : Dense (d₁.domain : Set F)) :
    harmonicSpace d₀ d₁ ⟂ (LinearMap.range d₁†.toFun).topologicalClosure := by
  rw [Submodule.isOrtho_comm, Submodule.isOrtho_iff_le]
  exact (Submodule.topologicalClosure_minimal _ (range_adjoint_le_orthogonal_ker hd₁)
    (Submodule.isClosed_orthogonal _)).trans (Submodule.orthogonal_le harmonicSpace_le_ker)

omit [CompleteSpace E] in
/-- In a complex, the closures of the ranges of `d₀` and of `d₁†` are orthogonal. -/
theorem isOrtho_topologicalClosure_range_topologicalClosure_range_adjoint [CompleteSpace F]
    (hd₁ : Dense (d₁.domain : Set F)) (hcomplex : LinearMap.range d₀.toFun ≤ d₁.ker) :
    (LinearMap.range d₀.toFun).topologicalClosure ⟂
      (LinearMap.range d₁†.toFun).topologicalClosure := by
  rw [Submodule.isOrtho_comm, Submodule.isOrtho_iff_le, Submodule.orthogonal_closure]
  exact (Submodule.topologicalClosure_minimal _ (range_adjoint_le_orthogonal_ker hd₁)
    (Submodule.isClosed_orthogonal _)).trans (Submodule.orthogonal_le hcomplex)

/-- **The Hodge decomposition of the closed vectors.** In a complex `range d₀ ≤ ker d₁`, with `d₀`
densely defined and `d₁` closed, the kernel of `d₁` is the sum of the closure of the range of
`d₀` and the harmonic space. -/
theorem topologicalClosure_range_sup_harmonicSpace [CompleteSpace F]
    (hd₀ : Dense (d₀.domain : Set E)) (hc₁ : d₁.IsClosed)
    (hcomplex : LinearMap.range d₀.toFun ≤ d₁.ker) :
    (LinearMap.range d₀.toFun).topologicalClosure ⊔ harmonicSpace d₀ d₁ = d₁.ker := by
  have : (LinearMap.range d₀.toFun).topologicalClosure.HasOrthogonalProjection :=
    have := (Submodule.isClosed_topologicalClosure (LinearMap.range d₀.toFun)).completeSpace_coe
    inferInstance
  rw [harmonicSpace_eq_ker_inf_orthogonal_range hd₀, ← Submodule.orthogonal_closure, inf_comm]
  exact Submodule.sup_orthogonal_inf_of_hasOrthogonalProjection
    (topologicalClosure_range_le_ker hc₁ hcomplex)

/-- **The Hodge decomposition.** In a complex `range d₀ ≤ ker d₁`, with `d₀` densely defined and
`d₁` closed and densely defined, `F` is the sum of the closure of the range of `d₀`, the harmonic
space and the closure of the range of `d₁†`. The three summands are pairwise orthogonal
(`isOrtho_topologicalClosure_range_harmonicSpace`,
`isOrtho_harmonicSpace_topologicalClosure_range_adjoint` and
`isOrtho_topologicalClosure_range_topologicalClosure_range_adjoint`). -/
theorem topologicalClosure_range_sup_harmonicSpace_sup_topologicalClosure_range_adjoint
    [CompleteSpace F] [CompleteSpace G] (hd₀ : Dense (d₀.domain : Set E)) (hc₁ : d₁.IsClosed)
    (hd₁ : Dense (d₁.domain : Set F)) (hcomplex : LinearMap.range d₀.toFun ≤ d₁.ker) :
    (LinearMap.range d₀.toFun).topologicalClosure ⊔ harmonicSpace d₀ d₁ ⊔
      (LinearMap.range d₁†.toFun).topologicalClosure = ⊤ := by
  have : d₁.ker.HasOrthogonalProjection :=
    have := hc₁.isClosed_ker.completeSpace_coe
    inferInstance
  rw [topologicalClosure_range_sup_harmonicSpace hd₀ hc₁ hcomplex,
    topologicalClosure_range_adjoint_eq_orthogonal_ker hc₁ hd₁]
  exact Submodule.sup_orthogonal_of_hasOrthogonalProjection

end Hodge

end LinearPMap
