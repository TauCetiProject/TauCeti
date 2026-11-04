/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Jacobi.Conjugate.Basic
public import TauCeti.Geometry.Manifold.Riemannian.Jacobi.Exponential

/-!
# Conjugate multiplicity and the exponential differential

Along the radial geodesic `γ(t) = exp_p(t v)`, initial covariant differentiation identifies
the Jacobi fields vanishing at `0` and `b ≠ 0` with the kernel of `d(exp_p)_(b v)`.
The inverse sends `w` to `t ↦ d(exp_p)_(t v)(t w)`, restricted to the parameter set
using the canonical zero extension of `jacobiFieldSpace`.

`mfderiv_riemannianExp_mem_endpointJacobiFieldSpace` shows that the radial Jacobi field of
a kernel vector vanishes at both endpoints. `endpointJacobiFieldEquivExpKer` gives the linear
equivalence, with computation rules in both directions. Consequently
`conjugateMultiplicity_eq_finrank_ker_mfderiv_riemannianExp`
identifies conjugate multiplicity with the kernel dimension, and
`isConjugateOn_iff_not_injective_mfderiv_riemannianExp` characterizes conjugacy by the singularity
of the exponential differential.

The parameter set may be any preconnected set with unique derivatives contained in the
maximal geodesic interval and containing both endpoints. In particular closed intervals are
allowed. The time factor `b` is retained explicitly in the inverse formula; no unit-speed,
nonzero-velocity or completeness assumption is needed.

The construction uses the radial Jacobi field and its initial derivative from
`Jacobi.Exponential`, and initial-data uniqueness from `Jacobi.Conjugate`.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, second edition, Chapter 10
  (the differential of the exponential map and conjugate multiplicity).
-/

public section

open Bundle CovariantDerivative Set
open scoped ContDiff Manifold

noncomputable section

namespace TauCeti.Manifold

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
  [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  {p : M} {v : TangentSpace I p} {s : Set ℝ} {b : ℝ}
  (hγ : IsGeodesicCurveOn I (fun t : ℝ ↦ riemannianExp I M p (t • v)) s)
  (hs : IsPreconnected s) (hsub : s ⊆ geodesicInterval I M p v)
  (h0 : (0 : ℝ) ∈ s) (hb : b ∈ s) (hb0 : b ≠ 0)

include hγ hs hsub h0 hb hb0

omit hs hb0 in
/-- For `w` in the kernel of `d(exp_p)_(b v)`, the radial Jacobi field `t ↦ d(exp_p)_(t v)(t w)`,
restricted to the parameter set, vanishes at `0` and `b`. -/
theorem mfderiv_riemannianExp_mem_endpointJacobiFieldSpace {w : TangentSpace I p}
    (hw : mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) (b • v) w = 0) :
    ((isJacobiFieldOn_mfderiv_riemannianExp p v w).mono hγ.uniqueDiffOn hsub).toJacobiFieldSpace ∈
      endpointJacobiFieldSpace hγ 0 b := by
  -- Pull the time factor out of the differential. The field value `t • w` is formed in `T_p M`,
  -- while the differential's domain is `T_(t v)(T_p M)`; these agree only after unfolding, so
  -- `map_smul` is stated at the explicit differential and applied with `trans`, not `rw`.
  have hscale (t : ℝ) :=
    (mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) (t • v)).map_smul t w
  refine (mem_endpointJacobiFieldSpace hγ _).2 ⟨?_, ?_⟩
  · rw [IsJacobiFieldOn.toJacobiFieldSpace_apply _ h0]
    exact (hscale 0).trans (zero_smul ℝ _)
  · rw [IsJacobiFieldOn.toJacobiFieldSpace_apply _ hb]
    exact (hscale b).trans (by rw [hw, smul_zero])

/-- Initial covariant differentiation identifies endpoint-zero radial Jacobi fields with the
kernel of the exponential differential at `b • v`. The source tangent space at time zero is
read as `TangentSpace I p`; both are the model space `E`. -/
def endpointJacobiFieldEquivExpKer :
    endpointJacobiFieldSpace hγ 0 b ≃ₗ[ℝ]
      LinearMap.ker (mfderiv 𝓘(ℝ, TangentSpace I p) I
        (riemannianExp I M p) (b • v)).toLinearMap := by
  -- Identify the initial fibre with T_p M using exp_p(0) = p, and then identify
  -- T_(b v)(T_p M) with its underlying vector space by the native normed-space equivalence.
  let D := (NormedSpace.fromTangentSpace (𝕜 := ℝ) (b • v)).symm.toLinearMap ∘ₗ
    (tangentSpaceCast I (riemannianExp I M p ((0 : ℝ) • v)) p).toLinearMap ∘ₗ
      endpointJacobiInitialDerivative hγ h0 b
  have hD (V : endpointJacobiFieldSpace hγ 0 b) :
      D V ∈ LinearMap.ker (mfderiv 𝓘(ℝ, TangentSpace I p) I
        (riemannianExp I M p) (b • v)).toLinearMap := by
    have hV := (mem_endpointJacobiFieldSpace hγ V.val).1 V.property
    have hinit : alongCurveWithin (leviCivitaConnection I M)
        (fun t : ℝ ↦ riemannianExp I M p (t • v)) V.val.val s 0 =
        (D V : TangentSpace I p) :=
      (endpointJacobiInitialDerivative_apply hγ h0 V).symm
    have h := (isJacobiFieldOn_of_mem_jacobiFieldSpace V.val).eq_mfderiv_riemannianExp
      hs hsub h0 hV.1 hinit hb
    have hm := (mfderiv 𝓘(ℝ, TangentSpace I p) I
      (riemannianExp I M p) (b • v)).map_smul b (D V)
    exact (smul_eq_zero.mp (hm.symm.trans (h.symm.trans hV.2))).resolve_left hb0
  refine LinearEquiv.ofBijective (D.codRestrict _ hD) ⟨?_, ?_⟩
  · intro V W h
    exact endpointJacobiInitialDerivative_injective hγ hs h0 (congrArg Subtype.val h)
  · intro w
    have hJ := (isJacobiFieldOn_mfderiv_riemannianExp p v w.val).mono hγ.uniqueDiffOn hsub
    have hw := w.property
    rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe] at hw
    let V : endpointJacobiFieldSpace hγ 0 b :=
      ⟨hJ.toJacobiFieldSpace, mfderiv_riemannianExp_mem_endpointJacobiFieldSpace hγ hsub h0 hb hw⟩
    refine ⟨V, Subtype.ext ?_⟩
    -- The two native tangent identifications in D are the identity on vectors.
    have hvalue : (D V : TangentSpace I p) = endpointJacobiInitialDerivative hγ h0 b V := rfl
    have hinit := (endpointJacobiInitialDerivative_apply hγ h0 V).trans
      (hJ.alongCurveWithin_toJacobiFieldSpace h0)
    have hJinit := (isJacobiFieldOn_mfderiv_riemannianExp p v w.val).alongCurveWithin_subset
      (hγ.uniqueDiffOn 0 h0) hsub h0
    exact hvalue.trans (hinit.trans (hJinit.trans
      (alongCurveWithin_mfderiv_riemannianExp_zero p v w.val)))

/-- The equivalence sends a Jacobi field to its initial covariant derivative. -/
@[simp]
theorem endpointJacobiFieldEquivExpKer_apply (V : endpointJacobiFieldSpace hγ 0 b) :
    (endpointJacobiFieldEquivExpKer hγ hs hsub h0 hb hb0 V).val =
      (NormedSpace.fromTangentSpace (𝕜 := ℝ) (b • v)).symm
        (tangentSpaceCast I (riemannianExp I M p ((0 : ℝ) • v)) p
          (alongCurveWithin (leviCivitaConnection I M)
            (fun t : ℝ ↦ riemannianExp I M p (t • v)) V.val.val s 0)) := by
  rw [← endpointJacobiInitialDerivative_apply hγ h0 V]
  -- The equivalence is `LinearEquiv.ofBijective` of the codomain restriction of this composite.
  rfl

/-- The inverse equivalence is the radial Jacobi field `d(exp_p)_(t v)(t w)` on the
parameter set. This formula records the affine-parameter scaling. -/
@[simp]
theorem endpointJacobiFieldEquivExpKer_symm_apply
    (w : LinearMap.ker (mfderiv 𝓘(ℝ, TangentSpace I p) I
      (riemannianExp I M p) (b • v)).toLinearMap) {t : ℝ} (ht : t ∈ s) :
    ((endpointJacobiFieldEquivExpKer hγ hs hsub h0 hb hb0).symm w).val.val t =
      mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) (t • v) (t • w.val) := by
  let e := endpointJacobiFieldEquivExpKer hγ hs hsub h0 hb hb0
  have hD : alongCurveWithin (leviCivitaConnection I M)
      (fun t : ℝ ↦ riemannianExp I M p (t • v)) (e.symm w).val.val s 0 = w.val := by
    have h := congrArg Subtype.val (e.apply_symm_apply w)
    rw [endpointJacobiFieldEquivExpKer_apply] at h
    -- `fromTangentSpace` and `tangentSpaceCast` are both the identity on vectors.
    exact h
  exact (isJacobiFieldOn_of_mem_jacobiFieldSpace (e.symm w).val).eq_mfderiv_riemannianExp
    hs hsub h0 ((mem_endpointJacobiFieldSpace hγ _).1 (e.symm w).property).1 hD ht

/-- Conjugate multiplicity is the nullity of the exponential differential, with the endpoint
`b` corresponding to the tangent vector `b • v`. -/
theorem conjugateMultiplicity_eq_finrank_ker_mfderiv_riemannianExp :
    conjugateMultiplicity hγ hs h0 b =
      Module.finrank ℝ (LinearMap.ker (mfderiv 𝓘(ℝ, TangentSpace I p) I
        (riemannianExp I M p) (b • v)).toLinearMap) := by
  rw [conjugateMultiplicity_eq_finrank]
  exact (endpointJacobiFieldEquivExpKer hγ hs hsub h0 hb hb0).finrank_eq

/-- Distinct radial parameters are conjugate exactly when the exponential differential
has a nonzero kernel, equivalently when it is not injective. -/
theorem isConjugateOn_iff_not_injective_mfderiv_riemannianExp :
    IsConjugateOn I (fun t : ℝ ↦ riemannianExp I M p (t • v)) s 0 b ↔
      ¬ Function.Injective (mfderiv 𝓘(ℝ, TangentSpace I p) I
        (riemannianExp I M p) (b • v)) := by
  rw [← conjugateMultiplicity_pos_iff hγ hs h0 hb hb0.symm,
    conjugateMultiplicity_eq_finrank_ker_mfderiv_riemannianExp hγ hs hsub h0 hb hb0,
    Nat.pos_iff_ne_zero, ne_eq, Submodule.finrank_eq_zero, LinearMap.ker_eq_bot,
    ContinuousLinearMap.coe_coe]

end TauCeti.Manifold
