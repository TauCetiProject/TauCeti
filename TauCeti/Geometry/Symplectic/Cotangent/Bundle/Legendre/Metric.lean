/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.NondegenerateMetric.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.Riesz
public import TauCeti.Geometry.Symplectic.Cotangent.Bundle.Cogeodesic
public import TauCeti.Geometry.Symplectic.Cotangent.Bundle.Hyperregular
import TauCeti.Geometry.Manifold.VectorBundle.NondegenerateMetric.Musical

/-!
# The Legendre transform of the mechanical Lagrangian of a metric

Let `g` be a smooth symmetric nondegenerate metric on a finite-dimensional manifold `M`, of any
signature (`TauCeti.Manifold.ContMDiffNondegenerateMetric`), and let
`L(v) = ½ g(v, v) - V(x)` be its mechanical Lagrangian (`TauCeti.mechanicalLagrangian g V`).
This file records the basic mechanics of `L` that need neither a connection nor geodesics: `L` is
as smooth as the potential, and it is hyperregular, since its Legendre map `v ↦ g(v, ·)` is
fibrewise the invertible flat map of `g`.

For a Riemannian metric, given by the ambient Riemannian bundle instance, the Legendre map is the
inverse of the Riesz isomorphism and is isometric on fibres, so the Hamiltonian `E_L ∘ FL⁻¹` is the
covector kinetic energy `‖p‖² / 2` of `Cogeodesic.lean` plus the potential.

## Main results

* `TauCeti.Manifold.ContMDiffNondegenerateMetric.contMDiff_mechanicalLagrangian` and
  `TauCeti.Manifold.ContMDiffNondegenerateMetric.contMDiff_mechanicalLagrangian_zero`: smoothness
  of mechanical and kinetic Lagrangians.
* `TauCeti.Manifold.ContMDiffNondegenerateMetric.isHyperregularLagrangian_mechanicalLagrangian`:
  the mechanical Lagrangian of a nondegenerate metric is hyperregular.
* `TauCeti.legendreMap_mechanicalLagrangian_ofRiemannianBundle_rieszDual` and
  `TauCeti.norm_legendreMap_mechanicalLagrangian_ofRiemannianBundle_snd`: the Riemannian Legendre
  map inverts the Riesz isomorphism and is isometric on fibres.
* `TauCeti.IsHyperregularLagrangian.hamiltonian_mechanicalLagrangian_ofRiemannianBundle` and
  `TauCeti.IsHyperregularLagrangian.hamiltonian_eq_kineticEnergy`: the Hamiltonian of a Riemannian
  mechanical Lagrangian is the covector kinetic energy plus the potential.

## References

* R. Abraham, J. E. Marsden, *Foundations of Mechanics*, 2nd ed., Benjamin/Cummings, 1978,
  Section 3.7.
-/

public section

noncomputable section

open Bundle
open scoped Manifold ContDiff

namespace TauCeti

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]

namespace Manifold.ContMDiffNondegenerateMetric

variable (g : ContMDiffNondegenerateMetric (I := I) (M := M))

/-- A mechanical Lagrangian has the regularity of its potential, since the metric is smooth. -/
theorem contMDiff_mechanicalLagrangian {n : WithTop ℕ∞} {V : M → ℝ} (hn : n ≤ ∞)
    (hV : ContMDiff I 𝓘(ℝ) n V) :
    ContMDiff I.tangent 𝓘(ℝ) n (mechanicalLagrangian g V) :=
  TauCeti.contMDiff_mechanicalLagrangian (g.contMDiff.of_le hn) hV

/-- The kinetic Lagrangian is smooth because the metric is smooth and the potential is zero. -/
theorem contMDiff_mechanicalLagrangian_zero :
    ContMDiff I.tangent 𝓘(ℝ) ∞ (mechanicalLagrangian g 0) :=
  g.contMDiff_mechanicalLagrangian le_rfl contMDiff_const

/-- **The mechanical Lagrangian of a nondegenerate metric is hyperregular**: its Legendre map
`v ↦ g(v, ·)` is a bijection `TM → T*M`, for every potential `V`. -/
theorem isHyperregularLagrangian_mechanicalLagrangian [FiniteDimensional ℝ E] (V : M → ℝ) :
    IsHyperregularLagrangian (mechanicalLagrangian g V) :=
  (isHyperregularLagrangian_mechanicalLagrangian_iff g.apply_comm V).2 g.isInvertible

end Manifold.ContMDiffNondegenerateMetric

/-! ### Riemannian mechanical Lagrangians -/

section Riemannian

open _root_.TauCeti.Manifold

variable [FiniteDimensional ℝ E] [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]

/-- **The Legendre map of a Riemannian mechanical Lagrangian inverts the Riesz isomorphism:** it
sends the Riesz dual of a covector `p` back to `p`. -/
@[simp]
theorem legendreMap_mechanicalLagrangian_ofRiemannianBundle_rieszDual (V : M → ℝ)
    (p : CotangentBundle I M) :
    legendreMap (mechanicalLagrangian (ContMDiffNondegenerateMetric.ofRiemannianBundle I M) V)
        (TotalSpace.mk' E p.proj (Riemannian.Tensor.rieszDual (I := I) p.proj p.2)) = p := by
  let g := ContMDiffNondegenerateMetric.ofRiemannianBundle I M
  -- The metric lowers the index of the Riesz dual of `p` back to `p`.
  have hR : g p.proj (Riemannian.Tensor.rieszDual (I := I) p.proj p.2) = p.2 := by
    ext w
    rw [ContMDiffNondegenerateMetric.ofRiemannianBundle_apply, Riemannian.Tensor.inner_rieszDual]
  rw [legendreMap_mechanicalLagrangian g.apply_comm]
  exact TotalSpace.ext rfl (heq_of_eq hR)

/-- **The Legendre map of a Riemannian mechanical Lagrangian is isometric on fibres:** the
covector `⟪v, ·⟫` has the norm of `v`. -/
@[simp]
theorem norm_legendreMap_mechanicalLagrangian_ofRiemannianBundle_snd (V : M → ℝ)
    (v : TangentBundle I M) :
    ‖(legendreMap
      (mechanicalLagrangian (ContMDiffNondegenerateMetric.ofRiemannianBundle I M) V) v).2‖ =
      ‖v.2‖ := by
  let g := ContMDiffNondegenerateMetric.ofRiemannianBundle I M
  -- `v` is the Riesz dual of `⟪v, ·⟫`, and the Riesz isomorphism is isometric.
  have hv : v.2 = Riemannian.Tensor.rieszDual (I := I) v.proj (g v.proj v.2) :=
    Riemannian.Tensor.eq_rieszDual_iff_inner_eq.2 fun w ↦
      (ContMDiffNondegenerateMetric.ofRiemannianBundle_apply I M v.proj _ w).symm
  rw [legendreMap_mechanicalLagrangian g.apply_comm]
  conv_rhs => rw [hv]
  exact ((Riemannian.Tensor.rieszDual (I := I) v.proj).norm_map _).symm

/-- The Hamiltonian of a Riemannian mechanical Lagrangian is covector kinetic energy plus
its potential. -/
theorem IsHyperregularLagrangian.hamiltonian_mechanicalLagrangian_ofRiemannianBundle
    {V : M → ℝ} (h : IsHyperregularLagrangian
      (mechanicalLagrangian (ContMDiffNondegenerateMetric.ofRiemannianBundle I M) V))
    (p : CotangentBundle I M) :
    h.hamiltonian p = CotangentBundle.kineticEnergy I M p + V p.proj := by
  have hp := legendreMap_mechanicalLagrangian_ofRiemannianBundle_rieszDual V p
  conv_lhs => rw [← hp]
  rw [h.hamiltonian_legendreMap, lagrangianEnergy_mechanicalLagrangian,
    ContMDiffNondegenerateMetric.ofRiemannianBundle_apply, CotangentBundle.kineticEnergy_apply,
    Riemannian.Tensor.norm_sq_eq_apply_rieszDual, Riemannian.Tensor.inner_rieszDual]
  ring

/-- **The Hamiltonian of the kinetic Lagrangian is the kinetic energy of covectors.** For the
Lagrangian `½ ‖v‖²` of a Riemannian metric, the Hamiltonian `E_L ∘ FL⁻¹` is `‖p‖² / 2`, for the
norm of covectors induced by the metric. -/
@[simp]
theorem IsHyperregularLagrangian.hamiltonian_eq_kineticEnergy
    (h : IsHyperregularLagrangian
      (mechanicalLagrangian (ContMDiffNondegenerateMetric.ofRiemannianBundle I M) 0)) :
    h.hamiltonian = CotangentBundle.kineticEnergy I M := by
  funext p
  simpa using h.hamiltonian_mechanicalLagrangian_ofRiemannianBundle p

end Riemannian

end TauCeti
