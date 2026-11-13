/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.CauchyRiemann.Weak
public import TauCeti.Analysis.Sobolev.WeakDeriv.WithLp
public import TauCeti.Geometry.Symplectic.Floer.Graph
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

The weak derivative of the graph is computed by `TauCeti.hasWeakFDerivOn_toLp_prodMk_iff`.

## Main results

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

/-- The derivative `(id, D)` of the graph, read through the Euclidean product. -/
private abbrev graphDeriv (D : ℂ →L[ℝ] V) : ℂ →L[ℝ] WithLp 2 (ℂ × V) :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ ℂ V).symm.toContinuousLinearMap ∘L
    (ContinuousLinearMap.id ℝ ℂ).prod D

/-- The pointwise algebra: the homogeneous equation for Gromov's structure at a graph point, with
the graph derivative `(id, D)`, is the inhomogeneous equation for `D`. -/
private theorem graphDeriv_add_graphStructure_eq_zero_iff (D : ℂ →L[ℝ] V) (z : ℂ) (x : V) :
    graphDeriv D 1 + Floer.graphStructure J X (WithLp.toLp 2 (z, x)) (graphDeriv D I) = 0 ↔
      D 1 + J (z, x) (D I) = X (z, x) 1 + J (z, x) (X (z, x) I) := by
  simp only [graphDeriv, ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.id_apply, ContinuousLinearEquiv.coe_coe,
    WithLp.prodContinuousLinearEquiv_symm_apply, Floer.graphStructure_apply]
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
        (fun z x ↦ X (z, x) 1 + J (z, x) (X (z, x) I)) u := by
  set e := WithLp.prodContinuousLinearEquiv 2 ℝ ℂ V
  have hsnd : ∀ z, (ContinuousLinearMap.snd ℝ ℂ V ∘L e.toContinuousLinearMap)
      (WithLp.toLp 2 (z, u z)) = u z := fun z ↦ by simp [e]
  have hgraph : ∀ {D : ℂ → ℂ →L[ℝ] V}, HasWeakFDerivOn volume (Opens.interior U) u D →
      HasWeakFDerivOn volume (Opens.interior U) (fun z ↦ WithLp.toLp 2 (z, u z))
        (fun z ↦ graphDeriv (D z)) := fun hD ↦ hasWeakFDerivOn_toLp_prodMk_iff.2 hD
  rw [isWeakCauchyRiemannOn_iff, isWeakCauchyRiemannOn_iff]
  constructor
  · rintro ⟨hc, hp, E, hE, hEp, hae⟩
    set L := ContinuousLinearMap.snd ℝ ℂ V ∘L e.toContinuousLinearMap
    have hD : HasWeakFDerivOn volume (Opens.interior U) u (fun z ↦ L ∘L E z) := by
      simpa only [hsnd] using hE.clm_comp L
    refine ⟨?_, ?_, fun z ↦ L ∘L E z, hD,
      by simpa using hEp.clm_comp (ContinuousLinearMap.compL ℝ ℂ _ V L), ?_⟩
    · exact (L.continuous.comp_continuousOn hc).congr fun z _ ↦ (hsnd z).symm
    · simpa only [hsnd] using hp.clm_comp L
    · filter_upwards [hae, hE.ae_eq (hgraph hD)] with z hz hEz
      rw [hEz] at hz
      exact (graphDeriv_add_graphStructure_eq_zero_iff _ z (u z)).1 hz
  · rintro ⟨hc, hp, D, hD, hDp, hae⟩
    refine ⟨?_, ?_, fun z ↦ graphDeriv (D z), hgraph hD, ((memLpLoc_const _).clm_prod hDp).clm_comp
      (ContinuousLinearMap.compL ℝ ℂ _ _ e.symm.toContinuousLinearMap), ?_⟩
    · exact e.symm.continuous.comp_continuousOn (continuousOn_id.prodMk hc)
    · rw [toLp_prodMk_eq_add (𝕜 := ℝ)]
      exact (e.symm.toContinuousLinearMap ∘L ContinuousLinearMap.inl ℝ ℂ V).continuous
        |>.continuousOn.memLpLoc.add (hp.clm_comp
          (e.symm.toContinuousLinearMap ∘L ContinuousLinearMap.inr ℝ ℂ V))
    · filter_upwards [hae] with z hz
      exact (graphDeriv_add_graphStructure_eq_zero_iff _ z (u z)).2 hz

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
