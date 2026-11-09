/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Exponential
public import TauCeti.Geometry.Manifold.VectorBundle.Scalar

/-!
# Exponential variations of a curve

Let `γ : ℝ → M` be a curve in a Riemannian manifold and `V` a tangent field along `γ`. The
**exponential variation** `TauCeti.Manifold.exponentialVariation I γ V` is the two-parameter
family `(s, t) ↦ exp_(γ t) (s • V t)`. Its central curve is `γ` and its variation field is `V`.
It is jointly `C^n` at every point `(s, t)` with `s • V t` in the domain of the exponential map
at `γ t`, as soon as the lift of `V` to the tangent bundle is `C^n` at `t`. In particular it is
`C^n` along the central curve. Neither completeness nor a normal neighbourhood containing the
curve is needed.

## Main definitions and results

* `TauCeti.Manifold.exponentialVariation`: the exponential variation of a curve along a field.
* `TauCeti.Manifold.exponentialVariation_zero`: its central curve is the original curve.
* `TauCeti.Manifold.variationField_exponentialVariation`: its variation field is the given field.
* `TauCeti.Manifold.contMDiffAt_exponentialVariation`: its joint regularity on the domain of the
  exponential map.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018),
  Chapter 6 (variations of curves).
-/

public section

open Bundle Set
open scoped ContDiff Manifold

noncomputable section

namespace TauCeti.Manifold

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  (γ : ℝ → M) (V : ∀ t, TangentSpace I (γ t))

variable (I) in
/-- The exponential variation `(s, t) ↦ exp_(γ t) (s • V t)` of the curve `γ` along the tangent
field `V`. -/
def exponentialVariation (s t : ℝ) : M :=
  riemannianExp I M (γ t) (s • V t)

omit [I.Boundaryless] [T2Space M] in
/-- The defining formula of the exponential variation. -/
@[simp]
theorem exponentialVariation_apply (s t : ℝ) :
    exponentialVariation I γ V s t = riemannianExp I M (γ t) (s • V t) :=
  (rfl)

/-- The central curve of the exponential variation is the original curve. -/
@[simp]
theorem exponentialVariation_zero : exponentialVariation I γ V 0 = γ := by
  funext t
  simp only [exponentialVariation_apply, zero_smul, riemannianExp_zero]

/-- The variation field of the exponential variation is the given field. -/
@[simp]
theorem variationField_exponentialVariation (t : ℝ) :
    variationField I (exponentialVariation I γ V) t = V t := by
  rw [variationField_apply]
  exact curveVelocity_riemannianExp_smul_zero (γ t) (V t)

/-- The exponential variation is jointly `C^n` at every `(s, t)` with `s • V t` in the domain of
the exponential map at `γ t`, when the lift of `V` to the tangent bundle is `C^n` at `t`. -/
theorem contMDiffAt_exponentialVariation {n : ℕ∞} {s t : ℝ}
    (hV : ContMDiffAt 𝓘(ℝ, ℝ) I.tangent n (fun t ↦ TotalSpace.mk' E (γ t) (V t)) t)
    (hv : s • V t ∈ expDomain I M (γ t)) :
    ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I n
      (fun z : ℝ × ℝ ↦ exponentialVariation I γ V z.1 z.2) (s, t) := by
  have hinput : ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I.tangent n
      (fun z : ℝ × ℝ ↦ TotalSpace.mk' E (γ z.2) (z.1 • V z.2)) (s, t) :=
    contDiff_fst.contMDiff.contMDiffAt.smul_totalSpace
      (hV.comp (s, t) contDiff_snd.contMDiff.contMDiffAt)
  have hexp : ContMDiffAt I.tangent I n
      (fun z : TangentBundle I M ↦ riemannianExp I M z.proj z.2)
      (TotalSpace.mk' E (γ t) (s • V t)) :=
    (contMDiffOn_riemannianExp_tangentBundle.contMDiffAt
      (isOpen_setOfPred_mem_expDomain.mem_nhds hv)).of_le (by exact_mod_cast le_top)
  exact hexp.comp (s, t) hinput

end TauCeti.Manifold
