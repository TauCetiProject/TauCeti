/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Boundary.BoundaryFlow.Basic
public import TauCeti.Geometry.Manifold.IntegralCurve.Extension
public import TauCeti.Geometry.Manifold.IntegralCurve.Forward

/-!
# The inward flow of a compact manifold with boundary for all positive times

Let `M` be a compact smooth Hausdorff manifold modeled on the Euclidean half-space `𝓡∂ (n + 1)`
and `v` a smooth vector field on `M` pointing inward at every boundary point, in the sense that
`-v a` points outward (`TauCeti.IsOutwardPointing`). Then the integral curve of `v` through every
point of `M` exists for all positive time and stays in the interior of `M` at every positive time
(`TauCeti.exists_isMIntegralCurveOn_Ici_of_isOutwardPointing_neg`). So the forward integral curve
`TauCeti.forwardIntegralCurve v x` is an integral curve on `[0, ∞)`
(`TauCeti.isMIntegralCurveOn_forwardIntegralCurve_of_isOutwardPointing_neg`), in the interior at
positive times (`TauCeti.forwardIntegralCurve_mem_interior_of_isOutwardPointing_neg`), satisfies
the flow law (`TauCeti.forwardIntegralCurve_add_of_isOutwardPointing_neg`), and the
flow-out `(x, t) ↦ forwardIntegralCurve v x t` of the boundary is injective on `∂M × [0, ∞)`
(`TauCeti.injOn_forwardIntegralCurve_of_isOutwardPointing_neg`).

The proof is the uniform time argument. Near a boundary point, the integral curves of `v` exist
forward for a uniform time and enter the interior at once
(`TauCeti.exists_contMDiffOn_localFlow_of_isOutwardPointing_neg`); near an interior point they
exist for a uniform time in both directions and stay in the interior
(`exists_mem_nhds_forall_exists_isMIntegralCurveOn_Ioo_of_isInteriorPoint`). By compactness one
time `ε > 0` serves every point
(`TauCeti.exists_pos_forall_exists_isMIntegralCurveOn_Ico_of_isOutwardPointing_neg`), and the
short curves glue by uniqueness to curves on `[0, ∞)`
(`TauCeti.exists_isMIntegralCurveOn_Ici_of_forall_exists_isMIntegralCurveOn_Ico`).

For a field `V` pointing outward along the whole boundary (`TauCeti.IsOutwardPointingField`) this
is a statement about its backward flow, applied to `v = -V`: the curve
`t ↦ forwardIntegralCurve (-V) x (-t)` is an integral curve of `V` on `(-∞, 0]` ending at `x`
(`TauCeti.IsOutwardPointingField.isMIntegralCurveOn_Iic_forwardIntegralCurve_neg`), and the
backward flow-out of the boundary is injective on `∂M × (-∞, 0]`
(`TauCeti.IsOutwardPointingField.injOn_forwardIntegralCurve_neg`). For the Liouville field of a
compact Liouville domain `W`, which points outward along `∂W`, the backward flow-out
`(s, t) ↦ φₜ(s)`, `t < 0`, is the collar of the boundary along which the cylindrical end
`[0, ∞) × ∂W` is attached in the completion `W ∪ [0, ∞) × ∂W`. This file shows that this
collar is defined on all of `∂W × (-∞, 0)`, lies in the interior of `W` and is injective.

## Main results

* `TauCeti.exists_pos_forall_exists_isMIntegralCurveOn_Ico_of_isOutwardPointing_neg`: a uniform
  time of forward existence for an inward field on a compact manifold with boundary.
* `TauCeti.exists_isMIntegralCurveOn_Ici_of_isOutwardPointing_neg`: forward completeness of an
  inward field on a compact manifold with boundary, with the curves in the interior at positive
  times.
* `TauCeti.isMIntegralCurveOn_forwardIntegralCurve_of_isOutwardPointing_neg`,
  `TauCeti.forwardIntegralCurve_mem_interior_of_isOutwardPointing_neg`,
  `TauCeti.forwardIntegralCurve_add_of_isOutwardPointing_neg` and
  `TauCeti.injOn_forwardIntegralCurve_of_isOutwardPointing_neg`: the forward integral curves of an
  inward field, their flow law, and the injectivity of the flow-out of the boundary.
* `TauCeti.IsOutwardPointingField.isMIntegralCurveOn_Iic_forwardIntegralCurve_neg`,
  `TauCeti.IsOutwardPointingField.forwardIntegralCurve_neg_mem_interior` and
  `TauCeti.IsOutwardPointingField.injOn_forwardIntegralCurve_neg`: the backward flow of an outward
  field.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Lemma 9.15 and Theorem 9.16 (uniform time and completeness on compact
  manifolds) and Theorem 9.25 (flowing the boundary inward).
* P. Seidel, *A biased view of symplectic cohomology*, Current Developments in Mathematics 2006,
  Section 2(a) (the collar of a Liouville domain and its completion).
-/

public section

open Bundle Filter Function Manifold Set Topology
open scoped ContDiff Manifold

namespace TauCeti

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace (n + 1)) M]
  [IsManifold (𝓡∂ (n + 1)) ∞ M]

section Inward

variable {v : (x : M) → TangentSpace (𝓡∂ (n + 1)) x}

/-- Near every point of a manifold with boundary, the integral curves of an inward-pointing smooth
field exist forward for a uniform time and lie in the interior at positive times. -/
private theorem exists_mem_nhds_forall_exists_isMIntegralCurveOn_Ico
    (hv : ContMDiff (𝓡∂ (n + 1)) (𝓡∂ (n + 1)).tangent ∞
      (fun x ↦ (⟨x, v x⟩ : TangentBundle (𝓡∂ (n + 1)) M)))
    (hin : ∀ a ∈ (𝓡∂ (n + 1)).boundary M, IsOutwardPointing a (-v a)) (x₀ : M) :
    ∃ U ∈ 𝓝 x₀, ∃ ε > (0 : ℝ), ∀ x ∈ U, ∃ γ : ℝ → M, γ 0 = x ∧
      IsMIntegralCurveOn γ v (Ico 0 ε) ∧ MapsTo γ (Ioo 0 ε) ((𝓡∂ (n + 1)).interior M) := by
  rcases (𝓡∂ (n + 1)).isInteriorPoint_or_isBoundaryPoint x₀ with hx₀ | hx₀
  · -- Near an interior point, curves in both directions that stay in the interior.
    obtain ⟨w, hw, ε, hε, h⟩ :=
      exists_mem_nhds_forall_exists_isMIntegralCurveOn_Ioo_of_isInteriorPoint hx₀
        ((hv x₀).of_le (by simp))
    refine ⟨w, hw, ε, hε, fun x hx ↦ ?_⟩
    obtain ⟨γ, hγ0, hγ, hγS⟩ := h 0 x hx
    have hsub : Ico 0 ε ⊆ Ioo (0 - ε) (0 + ε) := fun t ht ↦ ⟨by linarith [ht.1], by linarith [ht.2]⟩
    exact ⟨γ, hγ0, hγ.mono hsub, hγS.mono_left (Ioo_subset_Ico_self.trans hsub)⟩
  · -- Near a boundary point, the local inward flow.
    obtain ⟨U, hU, ε, hε, Φ, -, hΦ⟩ := exists_contMDiffOn_localFlow_of_isOutwardPointing_neg v
      (V := univ) hv.contMDiffOn univ_mem (hin x₀ hx₀)
    exact ⟨U, hU, ε, hε, fun x hx ↦ ⟨Φ x, (hΦ x hx).1, (hΦ x hx).2.1, (hΦ x hx).2.2⟩⟩

/-- **A uniform time of forward existence.** On a compact manifold with boundary, the
integral curves of a smooth vector field pointing inward along the boundary exist forward for a
uniform time `ε > 0` from every point, and lie in the interior at positive times. -/
theorem exists_pos_forall_exists_isMIntegralCurveOn_Ico_of_isOutwardPointing_neg [CompactSpace M]
    (hv : ContMDiff (𝓡∂ (n + 1)) (𝓡∂ (n + 1)).tangent ∞
      (fun x ↦ (⟨x, v x⟩ : TangentBundle (𝓡∂ (n + 1)) M)))
    (hin : ∀ a ∈ (𝓡∂ (n + 1)).boundary M, IsOutwardPointing a (-v a)) :
    ∃ ε > (0 : ℝ), ∀ x : M, ∃ γ : ℝ → M, γ 0 = x ∧ IsMIntegralCurveOn γ v (Ico 0 ε) ∧
      MapsTo γ (Ioo 0 ε) ((𝓡∂ (n + 1)).interior M) := by
  rcases isEmpty_or_nonempty M with hM | hM
  · exact ⟨1, one_pos, fun x ↦ isEmptyElim x⟩
  choose U hU ε hε hγ using exists_mem_nhds_forall_exists_isMIntegralCurveOn_Ico hv hin
  -- Finitely many of the neighbourhoods cover `M`; take the least of their times.
  obtain ⟨s, -, hs⟩ := isCompact_univ.elim_nhds_subcover U fun x _ ↦ hU x
  have hne : s.Nonempty := by
    obtain ⟨x⟩ := hM
    obtain ⟨y, hy, -⟩ := mem_iUnion₂.1 (hs (mem_univ x))
    exact ⟨y, hy⟩
  refine ⟨s.inf' hne ε, (Finset.lt_inf'_iff hne).2 fun y _ ↦ hε y, fun x ↦ ?_⟩
  obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.1 (hs (mem_univ x))
  obtain ⟨γ, hγ0, hγ, hγS⟩ := hγ y x hxy
  have hle : s.inf' hne ε ≤ ε y := Finset.inf'_le ε hy
  exact ⟨γ, hγ0, hγ.mono (Ico_subset_Ico_right hle), hγS.mono_left (Ioo_subset_Ioo_right hle)⟩

variable [T2Space M] [CompactSpace M]

/-- **Forward completeness of an inward field.** On a compact Hausdorff manifold with boundary, the
integral curve of a smooth vector field pointing inward along the boundary through any point exists
for all positive time, and lies in the interior at every positive time. -/
theorem exists_isMIntegralCurveOn_Ici_of_isOutwardPointing_neg
    (hv : ContMDiff (𝓡∂ (n + 1)) (𝓡∂ (n + 1)).tangent ∞
      (fun x ↦ (⟨x, v x⟩ : TangentBundle (𝓡∂ (n + 1)) M)))
    (hin : ∀ a ∈ (𝓡∂ (n + 1)).boundary M, IsOutwardPointing a (-v a)) (x : M) :
    ∃ γ : ℝ → M, γ 0 = x ∧ IsMIntegralCurveOn γ v (Ici 0) ∧
      MapsTo γ (Ioi 0) ((𝓡∂ (n + 1)).interior M) := by
  obtain ⟨ε, hε, h⟩ :=
    exists_pos_forall_exists_isMIntegralCurveOn_Ico_of_isOutwardPointing_neg hv hin
  exact exists_isMIntegralCurveOn_Ici_of_forall_exists_isMIntegralCurveOn_Ico
    (hv.of_le (by simp)) hε h x

/-- On a compact Hausdorff manifold with boundary, the forward integral curve of a smooth vector
field pointing inward along the boundary is an integral curve on `[0, ∞)`. -/
theorem isMIntegralCurveOn_forwardIntegralCurve_of_isOutwardPointing_neg
    (hv : ContMDiff (𝓡∂ (n + 1)) (𝓡∂ (n + 1)).tangent ∞
      (fun x ↦ (⟨x, v x⟩ : TangentBundle (𝓡∂ (n + 1)) M)))
    (hin : ∀ a ∈ (𝓡∂ (n + 1)).boundary M, IsOutwardPointing a (-v a)) (x : M) :
    IsMIntegralCurveOn (forwardIntegralCurve v x) v (Ici 0) :=
  isMIntegralCurveOn_forwardIntegralCurve
    ((exists_isMIntegralCurveOn_Ici_of_isOutwardPointing_neg hv hin x).imp fun _ h ↦ ⟨h.1, h.2.1⟩)

/-- **The flow law of an inward field.** On a compact Hausdorff manifold with boundary, for a
smooth vector field pointing inward along the boundary, following its forward integral curve for
time `s ≥ 0` and then for time `t ≥ 0` is following it for time `s + t`. -/
theorem forwardIntegralCurve_add_of_isOutwardPointing_neg
    (hv : ContMDiff (𝓡∂ (n + 1)) (𝓡∂ (n + 1)).tangent ∞
      (fun x ↦ (⟨x, v x⟩ : TangentBundle (𝓡∂ (n + 1)) M)))
    (hin : ∀ a ∈ (𝓡∂ (n + 1)).boundary M, IsOutwardPointing a (-v a)) (x : M) {s t : ℝ}
    (hs : 0 ≤ s) (ht : 0 ≤ t) :
    forwardIntegralCurve v (forwardIntegralCurve v x s) t = forwardIntegralCurve v x (s + t) :=
  forwardIntegralCurve_add (hv.of_le (by simp))
    ((exists_isMIntegralCurveOn_Ici_of_isOutwardPointing_neg hv hin x).imp fun _ h ↦ ⟨h.1, h.2.1⟩)
    hs ht

/-- On a compact Hausdorff manifold with boundary, the forward integral curve of a smooth vector
field pointing inward along the boundary lies in the interior at every positive time. -/
theorem forwardIntegralCurve_mem_interior_of_isOutwardPointing_neg
    (hv : ContMDiff (𝓡∂ (n + 1)) (𝓡∂ (n + 1)).tangent ∞
      (fun x ↦ (⟨x, v x⟩ : TangentBundle (𝓡∂ (n + 1)) M)))
    (hin : ∀ a ∈ (𝓡∂ (n + 1)).boundary M, IsOutwardPointing a (-v a)) (x : M) {t : ℝ}
    (ht : 0 < t) : forwardIntegralCurve v x t ∈ (𝓡∂ (n + 1)).interior M := by
  obtain ⟨γ, rfl, hγ, hγS⟩ := exists_isMIntegralCurveOn_Ici_of_isOutwardPointing_neg hv hin x
  rw [← hγ.eqOn_forwardIntegralCurve (hv.of_le (by simp)) (mem_Ici.2 ht.le)]
  exact hγS ht

/-- **The flow-out of the boundary is injective for all positive times.** On a compact Hausdorff
manifold with boundary, for a smooth vector field pointing inward along the boundary, the map
`(x, t) ↦ forwardIntegralCurve v x t` is injective on `∂M × [0, ∞)`. -/
theorem injOn_forwardIntegralCurve_of_isOutwardPointing_neg
    (hv : ContMDiff (𝓡∂ (n + 1)) (𝓡∂ (n + 1)).tangent ∞
      (fun x ↦ (⟨x, v x⟩ : TangentBundle (𝓡∂ (n + 1)) M)))
    (hin : ∀ a ∈ (𝓡∂ (n + 1)).boundary M, IsOutwardPointing a (-v a)) :
    InjOn (fun p : M × ℝ ↦ forwardIntegralCurve v p.1 p.2)
      ((𝓡∂ (n + 1)).boundary M ×ˢ Ici 0) := by
  have h := injOn_flowOut_boundary (W := univ) (Φ := forwardIntegralCurve v) (hv.of_le (by simp))
    fun x _ t _ _ ↦ ⟨fun _ _ ↦ mem_univ _, forwardIntegralCurve_zero v x,
      (isMIntegralCurveOn_forwardIntegralCurve_of_isOutwardPointing_neg hv hin x).mono
        Icc_subset_Ici_self,
      forwardIntegralCurve_mem_interior_of_isOutwardPointing_neg hv hin x⟩
  rwa [univ_inter] at h

end Inward

namespace IsOutwardPointingField

variable [T2Space M] [CompactSpace M]
  {V : (x : M) → TangentSpace (𝓡∂ (n + 1)) x} (hV : IsOutwardPointingField V)
include hV

/-- **The backward flow of an outward field.** On a compact Hausdorff manifold with boundary, for
a smooth vector field `V` pointing outward along the boundary, the forward integral curve of `-V`
from `x`, run backwards, is an integral curve of `V` on `(-∞, 0]` ending at `x`. -/
theorem isMIntegralCurveOn_Iic_forwardIntegralCurve_neg (x : M) :
    IsMIntegralCurveOn (fun t ↦ forwardIntegralCurve (-V) x (-t)) V (Iic 0) := by
  have h := (isMIntegralCurveOn_forwardIntegralCurve_of_isOutwardPointing_neg hV.contMDiff_neg
    hV.isOutwardPointing_neg_neg x).comp_neg
  rw [neg_neg] at h
  convert h using 1
  ext t
  simp

/-- On a compact Hausdorff manifold with boundary, the backward flow of a smooth vector field
pointing outward along the boundary lies in the interior at every negative time. -/
theorem forwardIntegralCurve_neg_mem_interior (x : M) {t : ℝ} (ht : t < 0) :
    forwardIntegralCurve (-V) x (-t) ∈ (𝓡∂ (n + 1)).interior M :=
  forwardIntegralCurve_mem_interior_of_isOutwardPointing_neg hV.contMDiff_neg
    hV.isOutwardPointing_neg_neg x (neg_pos.2 ht)

/-- **The backward flow-out of the boundary is injective.** On a compact Hausdorff manifold with
boundary, for a smooth vector field `V` pointing outward along the boundary, the map
`(x, t) ↦ forwardIntegralCurve (-V) x (-t)`, the backward flow of `V`, is injective on
`∂M × (-∞, 0]`. -/
theorem injOn_forwardIntegralCurve_neg :
    InjOn (fun p : M × ℝ ↦ forwardIntegralCurve (-V) p.1 (-p.2))
      ((𝓡∂ (n + 1)).boundary M ×ˢ Iic 0) := by
  intro p hp q hq h
  have hinj := injOn_forwardIntegralCurve_of_isOutwardPointing_neg hV.contMDiff_neg
    hV.isOutwardPointing_neg_neg (x₁ := (p.1, -p.2)) ⟨hp.1, neg_nonneg.2 hp.2⟩
    (x₂ := (q.1, -q.2)) ⟨hq.1, neg_nonneg.2 hq.2⟩ h
  simp only [Prod.mk.injEq, neg_inj] at hinj
  exact Prod.ext hinj.1 hinj.2

end IsOutwardPointingField

end TauCeti
