/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.CauchyRiemann.Weak
public import TauCeti.Analysis.Sobolev.WeakDeriv.WithLp
public import TauCeti.Geometry.Symplectic.Floer.Graph.Basic
import TauCeti.LinearAlgebra.Complex.LinearPart

/-!
# Weak solutions and their graphs

Let `J : ℂ × V → V →L[ℝ] V` be a field of real-linear endomorphisms and
`X : ℂ × V → ℂ →L[ℝ] V` a one-form, both depending on a domain point `z` and a target point `x`.
Gromov's structure `TauCeti.Floer.graphStructure J X` on the Euclidean product
`WithLp 2 (ℂ × V)` sends `(ξ, v)` at `(z, x)` to `(i ξ, J(z, x)(v - X(z, x) ξ) + X(z, x)(i ξ))`.
This file proves the weak form of Gromov's graph construction: a map `u : ℂ → V` is a weak
solution of the inhomogeneous equation

`∂ₛu + J(z, u) ∂ₜu = X(z, u) 1 + J(z, u) (X(z, u) i)`

on a set `U` exactly when its graph `z ↦ (z, u z)` is a weak solution of the homogeneous equation
for Gromov's structure on `U`. No hypothesis on `J` or `X` is needed, and the exponent is
arbitrary.

The equivalence holds for any identification `e` of `ℂ × V` with a Banach space and any field of
structures on it which, at graph points, turns the homogeneous equation for the graph derivative
`e ∘ (id, D)` into the inhomogeneous equation for `D`. The Euclidean product is one such
identification; the plain product `ℂ × V`, the model space of product charts on a product of
manifolds, is another.

## Main results

* `TauCeti.isWeakCauchyRiemannOn_graph_iff`: the graph equivalence for an arbitrary identification
  of the product and an arbitrary field satisfying the pointwise condition.
* `TauCeti.isWeakCauchyRiemannOn_toLp_prodMk_graphStructure_iff`: the graph equivalence for the
  weak Cauchy–Riemann equation on an arbitrary set `U ⊆ ℂ`, so on open sets and on half-discs.
* `TauCeti.isWeakCauchyRiemannOn_toLp_prodMk_graphStructure_iff_of_contDiffOn`: for `u` of class
  `C¹` on an open set, with `J(z, u)` and `X(z, u)` continuous and `J(z, u)² = -1`, the weak
  graph equation is the pointwise graph equation `∂ₜU = J'(U) ∂ₛU` of
  `TauCeti.Floer.fderiv_toLp_prodMk_I_eq_graphStructure_iff`.

## References

* M. Gromov, *Pseudo holomorphic curves in symplectic manifolds*, Invent. Math. 82 (1985),
  307–347.
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Section 8.1 and Appendix B.4.
-/

public noncomputable section

open Complex MeasureTheory TopologicalSpace

namespace TauCeti

/-! ### The graph equivalence for the weak Cauchy–Riemann equation -/

section Graph

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  {p : ENNReal} {U : Set ℂ} {Ω : Opens ℂ}
  {J : ℂ × V → V →L[ℝ] V} {X : ℂ × V → ℂ →L[ℝ] V} {u : ℂ → V}

/-- **Graphs of weak solutions, for any identification of the product.** Let `e` identify
`ℂ × V` with a Banach space `W`, and let `K` be a field of endomorphisms of `W` such that, at
every point `z` of `U` and for every candidate derivative `D` of `u` at `z`, the homogeneous
equation `e (1, D 1) + K(z, e (z, u z)) e (i, D i) = 0` for the graph derivative `e ∘ (id, D)`
is the inhomogeneous equation `D 1 + J(z, u z) (D i) = η(z, u z)`. Then, on `U` and for any
exponent, `u` is a weak solution of the inhomogeneous equation exactly when its graph
`z ↦ e (z, u z)` is a weak solution of the homogeneous equation for `K`. The graph has weak
derivative `e ∘ (id, D)` for each weak derivative `D` of `u`
(`TauCeti.hasWeakFDerivOn_graph_iff`), and conversely `u` is the second component of `e⁻¹` applied
to the graph. -/
theorem isWeakCauchyRiemannOn_graph_iff [CompleteSpace V] {W : Type*} [NormedAddCommGroup W]
    [NormedSpace ℝ W] [CompleteSpace W] (e : (ℂ × V) ≃L[ℝ] W) {K : ℂ → W → W →L[ℝ] W}
    {J : ℂ → V → V →L[ℝ] V} {η : ℂ → V → V}
    (hK : ∀ z ∈ U, ∀ D : ℂ →L[ℝ] V, e (1, D 1) + K z (e (z, u z)) (e (I, D I)) = 0 ↔
      D 1 + J z (u z) (D I) = η z (u z)) :
    IsWeakCauchyRiemannOn p U K (fun _ _ ↦ 0) (fun z ↦ e (z, u z)) ↔
      IsWeakCauchyRiemannOn p U J η u := by
  set L := ContinuousLinearMap.snd ℝ ℂ V ∘L e.symm.toContinuousLinearMap
  have hsnd : ∀ z, L (e (z, u z)) = u z := fun z ↦ by simp [L]
  have hgraph : ∀ {D : ℂ → ℂ →L[ℝ] V}, HasWeakFDerivOn volume (Opens.interior U) u D →
      HasWeakFDerivOn volume (Opens.interior U) (fun z ↦ e (z, u z))
        (fun z ↦ e.toContinuousLinearMap ∘L (ContinuousLinearMap.id ℝ ℂ).prod (D z)) :=
    fun hD ↦ (hasWeakFDerivOn_graph_iff e).2 hD
  have hmem : ∀ᵐ z ∂volume.restrict (interior U), z ∈ U :=
    (ae_restrict_mem measurableSet_interior).mono fun _ hz ↦ interior_subset hz
  rw [isWeakCauchyRiemannOn_iff, isWeakCauchyRiemannOn_iff]
  constructor
  · rintro ⟨hc, hp, E, hE, hEp, hae⟩
    have hD : HasWeakFDerivOn volume (Opens.interior U) u (fun z ↦ L ∘L E z) := by
      simpa only [hsnd] using hE.clm_comp L
    refine ⟨?_, ?_, fun z ↦ L ∘L E z, hD,
      by simpa using hEp.clm_comp (ContinuousLinearMap.compL ℝ ℂ _ V L), ?_⟩
    · exact (L.continuous.comp_continuousOn hc).congr fun z _ ↦ (hsnd z).symm
    · simpa only [hsnd] using hp.clm_comp L
    · filter_upwards [hae, hE.ae_eq (hgraph hD), hmem] with z hz hEz hzU
      rw [hEz] at hz
      exact (hK z hzU _).1 hz
  · rintro ⟨hc, hp, D, hD, hDp, hae⟩
    refine ⟨?_, ?_, fun z ↦ e.toContinuousLinearMap ∘L (ContinuousLinearMap.id ℝ ℂ).prod (D z),
      hgraph hD, ((memLpLoc_const _).clm_prod hDp).clm_comp
        (ContinuousLinearMap.compL ℝ ℂ _ _ e.toContinuousLinearMap), ?_⟩
    · exact e.continuous.comp_continuousOn (continuousOn_id.prodMk hc)
    · have hsplit : (fun z ↦ e (z, u z)) =
          fun z ↦ (e.toContinuousLinearMap ∘L ContinuousLinearMap.inl ℝ ℂ V) z +
            (e.toContinuousLinearMap ∘L ContinuousLinearMap.inr ℝ ℂ V) (u z) :=
        funext fun z ↦ by simp [← map_add]
      rw [hsplit]
      exact (e.toContinuousLinearMap ∘L ContinuousLinearMap.inl ℝ ℂ V).continuous
        |>.continuousOn.memLpLoc.add (hp.clm_comp
          (e.toContinuousLinearMap ∘L ContinuousLinearMap.inr ℝ ℂ V))
    · filter_upwards [hae, hmem] with z hz hzU
      exact (hK z hzU (D z)).2 hz

/-- The pointwise algebra: the homogeneous equation for Gromov's structure at a graph point, with
the graph derivative `(id, D)`, is the inhomogeneous equation for `D`. -/
private theorem toLp_add_graphStructure_eq_zero_iff (D : ℂ →L[ℝ] V) (z : ℂ) (x : V) :
    WithLp.toLp 2 (1, D 1) + Floer.graphStructure J X (WithLp.toLp 2 (z, x))
        (WithLp.toLp 2 (I, D I)) = 0 ↔
      D 1 + J (z, x) (D I) = X (z, x) 1 + J (z, x) (X (z, x) I) := by
  simp only [Floer.graphStructure_apply]
  simp only [WithLp.ext_iff, Prod.ext_iff, WithLp.ofLp_add, WithLp.toLp_fst, WithLp.toLp_snd,
    Prod.fst_add, Prod.snd_add, WithLp.ofLp_zero, Prod.fst_zero, Prod.snd_zero, I_mul_I,
    add_neg_cancel, true_and, map_sub, map_neg]
  refine Iff.trans ?_ sub_eq_zero
  abel_nf

/-- **Gromov's graph construction for weak solutions.** On any set `U ⊆ ℂ` and for any exponent,
`u` is a weak solution of `∂ₛu + J(z, u) ∂ₜu = X(z, u) 1 + J(z, u) (X(z, u) i)` exactly when its
graph `z ↦ (z, u z)` is a weak solution of the homogeneous equation for Gromov's structure
`TauCeti.Floer.graphStructure J X`. No hypothesis on `J` or `X` is needed: the graph has weak
derivative `(id, D)` for each weak derivative `D` of `u`, and the equation for `(id, D)` is the
inhomogeneous equation for `D` pointwise. -/
theorem isWeakCauchyRiemannOn_toLp_prodMk_graphStructure_iff [CompleteSpace V] :
    IsWeakCauchyRiemannOn p U (fun _ q ↦ Floer.graphStructure J X q) (fun _ _ ↦ 0)
        (fun z ↦ WithLp.toLp 2 (z, u z)) ↔
      IsWeakCauchyRiemannOn p U (fun z x ↦ J (z, x))
        (fun z x ↦ X (z, x) 1 + J (z, x) (X (z, x) I)) u :=
  isWeakCauchyRiemannOn_graph_iff (WithLp.prodContinuousLinearEquiv 2 ℝ ℂ V).symm
    fun z _ D ↦ by
      simpa only [WithLp.prodContinuousLinearEquiv_symm_apply] using
        toLp_add_graphStructure_eq_zero_iff D z (u z)

/-- **The `C¹` comparison for graphs.** For `u` of class `C¹` on an open set `Ω`, with `J(z, u)`
and `X(z, u)` continuous on `Ω` and `J(z, u)² = -1` there, the graph is a weak solution of the
homogeneous equation for Gromov's structure, for any exponent, exactly when it solves
`∂ₜU = J'(U) ∂ₛU` at every point of `Ω`, the pointwise graph equation of
`TauCeti.Floer.fderiv_toLp_prodMk_I_eq_graphStructure_iff`. -/
theorem isWeakCauchyRiemannOn_toLp_prodMk_graphStructure_iff_of_contDiffOn [CompleteSpace V]
    (hu : ContDiffOn ℝ 1 u Ω) (hJ : ContinuousOn (fun z ↦ J (z, u z)) Ω)
    (hX : ContinuousOn (fun z ↦ X (z, u z)) Ω)
    (hJJ : ∀ z ∈ (Ω : Set ℂ), ∀ v, J (z, u z) (J (z, u z) v) = -v) :
    IsWeakCauchyRiemannOn p Ω (fun _ q ↦ Floer.graphStructure J X q) (fun _ _ ↦ 0)
        (fun z ↦ WithLp.toLp 2 (z, u z)) ↔
      ∀ z ∈ (Ω : Set ℂ), fderiv ℝ (fun w ↦ WithLp.toLp 2 (w, u w)) z I =
        Floer.graphStructure J X (WithLp.toLp 2 (z, u z))
          (fderiv ℝ (fun w ↦ WithLp.toLp 2 (w, u w)) z 1) := by
  have hη : ContinuousOn (fun z ↦ X (z, u z) 1 + J (z, u z) (X (z, u z) I)) Ω :=
    (hX.clm_apply continuousOn_const).add (hJ.clm_apply (hX.clm_apply continuousOn_const))
  rw [isWeakCauchyRiemannOn_toLp_prodMk_graphStructure_iff,
    isWeakCauchyRiemannOn_iff_of_contDiffOn hu hJ hη]
  refine forall₂_congr fun z hz ↦ ?_
  rw [Floer.fderiv_toLp_prodMk_I_eq_graphStructure_iff
      ((hu.differentiableOn one_ne_zero).differentiableAt (Ω.isOpen.mem_nhds hz)),
    ← add_apply_eq_zero_iff_eq_apply (hJJ z hz), map_sub, ← sub_eq_zero]
  constructor <;> intro h <;> rw [← h] <;> abel

end Graph

end TauCeti
