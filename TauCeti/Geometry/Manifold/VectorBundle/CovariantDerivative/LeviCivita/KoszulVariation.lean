/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita.Basic
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace
import TauCeti.Geometry.Manifold.VectorBundle.Bilinear.Family

/-!
# The parameter derivative of the Koszul expression

Let `b_s` be a one-parameter family of fields of bilinear forms on `TM`, jointly `C²` in `(s, x)`
as a map into the bundle of bilinear forms on `TM`, with parameter derivative `h = ∂ₛ b`. This file
proves that the Koszul expression `TauCeti.Manifold.koszulBilinear` of `b_s` on vector fields that
are `C²` at `x` is differentiable in `s`, with derivative the Koszul expression of `h`. Symmetry,
nondegeneracy and finite dimensionality are not needed. The proof commutes the parameter derivative
with the differentials of the pairings, `TauCeti.Manifold.hasDerivAt_mvfderiv_apply_apply`.

## Main results

* `TauCeti.Manifold.differentiableAt_koszulBilinear`: the Koszul expression of a jointly `C²`
  family of fields of bilinear forms is differentiable in the parameter.
* `TauCeti.Manifold.hasDerivAt_koszulBilinear`: its parameter derivative is the Koszul expression
  of the parameter derivative of the family.

## References

* A. L. Besse, *Einstein Manifolds*, Springer (1987), Section 1.K, Theorem 1.174.
-/

public section

noncomputable section

open Bundle Filter VectorField
open scoped ContDiff Manifold Topology

namespace TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {b : ℝ → (x : M) → TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ}
  {h : (x : M) → TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ} {t : ℝ} {x : M}

variable [IsManifold I ∞ M]

/-- The Koszul expression `K_{b_s}(X, Y, Z)` at `x` of a family of fields of bilinear forms,
jointly `C²` at `(t, x)`, is differentiable in the parameter at `t`, for vector fields `X`, `Y`, `Z`
that are `C²` at `x`. -/
theorem differentiableAt_koszulBilinear
    (hb : ContMDiffAt (𝓘(ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) 2
      (fun q : ℝ × M ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun y : M ↦ TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ) q.2 (b q.1 q.2))
      (t, x))
    {X Y Z : Π x : M, TangentSpace I x} (hX : CMDiffAt 2 (T% X) x) (hY : CMDiffAt 2 (T% Y) x)
    (hZ : CMDiffAt 2 (T% Z) x) :
    DifferentiableAt ℝ (fun s ↦ koszulBilinear I (b s) X Y Z x) t := by
  have hd {V W : Π x : M, TangentSpace I x} (U : Π x : M, TangentSpace I x)
      (hV : CMDiffAt 2 (T% V) x) (hW : CMDiffAt 2 (T% W) x) :
      DifferentiableAt ℝ (fun s ↦ mvfderiv I (fun y ↦ b s y (V y) (W y)) x (U x)) t :=
    (hasDerivAt_mvfderiv_apply_apply hb hV hW (U x)).differentiableAt
  have hp (u w : TangentSpace I x) :=
    differentiableAt_apply_apply_of_contMDiffAt (by norm_num) hb u w
  simp only [koszulBilinear_apply]
  exact ((((hd X hY hZ).add (hd Y hZ hX)).sub (hd Z hX hY)).add (hp _ _)).sub (hp _ _) |>.sub
    (hp _ _)

/-- **Variation of the Koszul expression.** Let `b_s` be a family of fields of bilinear forms on
`TM`, jointly `C²` in `(s, y)` at `(t, x)`, with parameter derivative `h = ∂ₛ b` at `s = t` near
`x`. Then for vector fields `X`, `Y`, `Z` that are `C²` at `x`, the parameter derivative of the
Koszul expression `K_{b_s}(X, Y, Z)` at `x` is the Koszul expression `K_h(X, Y, Z)` of `h`. -/
theorem hasDerivAt_koszulBilinear
    (hb : ContMDiffAt (𝓘(ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) 2
      (fun q : ℝ × M ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun y : M ↦ TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ) q.2 (b q.1 q.2)) (t, x))
    (hh : ∀ᶠ y in 𝓝 x, ∀ v w, HasDerivAt (fun s ↦ b s y v w) (h y v w) t)
    {X Y Z : Π x : M, TangentSpace I x} (hX : CMDiffAt 2 (T% X) x) (hY : CMDiffAt 2 (T% Y) x)
    (hZ : CMDiffAt 2 (T% Z) x) :
    HasDerivAt (fun s ↦ koszulBilinear I (b s) X Y Z x) (koszulBilinear I h X Y Z x) t := by
  -- The derivative terms: commute the parameter derivative with the differential.
  have hd {V W : Π x : M, TangentSpace I x} (U : Π x : M, TangentSpace I x)
      (hV : CMDiffAt 2 (T% V) x) (hW : CMDiffAt 2 (T% W) x) :
      HasDerivAt (fun s ↦ mvfderiv I (fun y ↦ b s y (V y) (W y)) x (U x))
        (mvfderiv I (fun y ↦ h y (V y) (W y)) x (U x)) t := by
    have hderiv := hasDerivAt_mvfderiv_apply_apply hb hV hW (U x)
    have heq : (fun y ↦ deriv (fun s ↦ b s y (V y) (W y)) t) =ᶠ[𝓝 x]
        fun y ↦ h y (V y) (W y) :=
      hh.mono fun y hy ↦ (hy (V y) (W y)).deriv
    rwa [heq.mvfderiv_eq] at hderiv
  -- The bracket terms: the parameter derivative of the pairing at `x`.
  have hp (u w : TangentSpace I x) : HasDerivAt (fun s ↦ b s x u w) (h x u w) t :=
    hh.self_of_nhds u w
  simp only [koszulBilinear_apply]
  exact ((((hd X hY hZ).add (hd Y hZ hX)).sub (hd Z hX hY)).add (hp _ _)).sub (hp _ _) |>.sub
    (hp _ _)

end TauCeti.Manifold
