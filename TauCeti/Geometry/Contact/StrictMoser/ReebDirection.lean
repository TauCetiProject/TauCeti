/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Contact.Family
public import TauCeti.Geometry.Manifold.DifferentialForm.Flow.Family
public import TauCeti.Geometry.Manifold.Flow.Integral
public import TauCeti.Geometry.Manifold.Flow.Parametric
import TauCeti.Geometry.Manifold.MFDeriv.Prod

/-!
# The Reeb-direction equation with zero values on a transverse slice

Let `α_t = ι_t^* α` be a smooth family of contact forms on a manifold `M`, represented by a
one-form `α` on `ℝ × M`, with Reeb vector fields `R_t` and velocities `∂_t α_t`. The strict Moser
method (`TauCeti.Geometry.Contact.StrictMoser`) produces an isotopy pulling `α_t` back to `α_s`
exactly, once it is given a smooth function `h` on `ℝ × M` solving the **Reeb-direction
equation**

`R_t h_t = -(∂_t α_t)(R_t)`, where `h_t = h (t, ·)`,

on an open set `U ⊆ ℝ × M`; this is the hypothesis `hR` of
`TauCeti.SmoothForm.exists_partialDiffeomorph_mpullback_eq`. This file solves the equation near a
hypersurface transverse to the Reeb fields, with zero values on the hypersurface. The solution is
smooth only on that neighbourhood, the target of a flow-out chart, so it gives `hR` there but not
the global smoothness of `h` that the strict Moser theorem also requires. Before it is fed to that
theorem it still has to be cut off or extended to a smooth function on all of `ℝ × M` which agrees
with it on a smaller open set, and that set is then used as `U`.

The equation is an ordinary differential equation along the trajectories of the Reeb fields, so it
is solved by integration along them. On `ℝ × M` the Reeb fields form the vertical field
`(t, x) ↦ (0, R_t x)` (`TauCeti.verticalField`), whose flow is `(t, x) ↦ (t, φ^{R_t}_σ x)`. Let
`ι : S → M` be a map, typically the inclusion of a hypersurface, and let `e` be a partial
diffeomorphism from `ℝ × (ℝ × S)` to `ℝ × M` that agrees on its source with the flow-out
`(σ, (t, s)) ↦ (t, φ^{R_t}_σ(ι s))`. Then the function

`h(t, φ^{R_t}_σ(ι s)) = -∫₀^σ (∂_t α_t)(R_t)(φ^{R_t}_u(ι s)) du`

is smooth on the target of `e`, vanishes at the points `(t, ι s)` with `(0, (t, s))` in the source
of `e`, and solves the Reeb-direction equation there
(`TauCeti.SmoothForm.exists_mvfderiv_apply_reebVectorField_eq_of_flowOut`). It is the trajectory
integral solving the transport equation along the flow-out
(`TauCeti.exists_mvfderiv_apply_eq_of_flowOut`), applied to the vertical Reeb field.

In the strict neighbourhood theorem for a Legendrian submanifold `Λ` (Kriegl–Michor,
`TauCeti.Geometry.Contact.Legendrian.Neighborhood`), `α_t` is the linear interpolation between the
model form `dz - λ` on `J¹Λ = T^* Λ × ℝ` and a pulled-back contact form, which agree along the zero
section and all of whose interpolations are contact there. The hypersurface `ι` is the slice
`T^* Λ × {0}`, which contains the zero section; the one-form `β = dz` vanishes on the slice and
equals every `α_t` along the zero section, so `β(R_t) = 1` there and the Reeb fields are transverse
to the slice near the zero section. Near the zero section, a globally smooth extension of the
solution `h` of this file serves as the function `h_t = α_t(X_t)` of the strict Moser vector field
`X_t` there.

## Main results

* `TauCeti.SmoothForm.exists_mvfderiv_apply_reebVectorField_eq_of_flowOut`: a smooth solution of
  the Reeb-direction equation on the target of a flow-out chart, vanishing on the slice, given by
  the integral of `-(∂_t α_t)(R_t)` along the Reeb trajectories.

## References

* Andreas Kriegl and Peter W. Michor, *The Convenient Setting of Global Analysis*, Mathematical
  Surveys and Monographs 53, American Mathematical Society, 1997, Proposition 43.18 (the
  Reeb-direction equation in the strict Moser argument for Legendrian neighbourhoods).
* John M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Chapter 9 (first-order partial differential equations solved along a flow-out).
-/

public section

noncomputable section

open scoped ContDiff Manifold

namespace TauCeti.SmoothForm

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless] [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {E' H' S : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {J : ModelWithCorners ℝ E' H'} [TopologicalSpace S] [ChartedSpace H' S]

/-- **The Reeb-direction equation along a flow-out.** Let `α_t` be a smooth family of contact
forms on `M`, with Reeb fields `R_t`, and let `e` be a smooth partial diffeomorphism from
`ℝ × (ℝ × S)` to `ℝ × M` which on its source is the flow-out
`(σ, (t, s)) ↦ (t, φ^{R_t}_σ(ι s))` of a smooth map `ι : S → M`. Then there is a function `h`
on `ℝ × M`, smooth on the target of `e`, given on it by
`h(t, φ^{R_t}_σ(ι s)) = ∫₀^σ -(∂_t α_t)(R_t)(φ^{R_t}_u(ι s)) du`, which vanishes at `(t, ι s)`
whenever `(0, (t, s))` lies in the source of `e`, and which solves the Reeb-direction equation
`R_t h_t = -(∂_t α_t)(R_t)` at every point of the target of `e`. -/
theorem exists_mvfderiv_apply_reebVectorField_eq_of_flowOut
    (α : SmoothForm (𝓘(ℝ, ℝ).prod I) (ℝ × M) ℝ 1)
    (hc : ∀ t, (mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) α).IsContactForm)
    {ι : S → M} (hι : ContMDiff J I ∞ ι)
    (e : PartialDiffeomorph (𝓘(ℝ, ℝ).prod (𝓘(ℝ, ℝ).prod J)) (𝓘(ℝ, ℝ).prod I) (ℝ × (ℝ × S))
      (ℝ × M) ∞)
    (he : ∀ p ∈ e.source,
      (p.1, ι p.2.2) ∈ flowDomain
          (mpullback (Prod.mk p.2.1) (contMDiff_const.prodMk contMDiff_id) α).reebVectorField ∧
        e p = (p.2.1, flowOf
          (mpullback (Prod.mk p.2.1) (contMDiff_const.prodMk contMDiff_id) α).reebVectorField
          p.1 (ι p.2.2))) :
    ∃ h : ℝ × M → ℝ, ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) ∞ h e.target ∧
      (∀ p ∈ e.source, h (e p) = flowIntegral
        (mpullback (Prod.mk p.2.1) (contMDiff_const.prodMk contMDiff_id) α).reebVectorField
        (fun y ↦ -(mpullback (Prod.mk p.2.1) (contMDiff_const.prodMk contMDiff_id)
          α.timeDeriv).val y
            ![(mpullback (Prod.mk p.2.1) (contMDiff_const.prodMk contMDiff_id)
              α).reebVectorField y]) p.1 (ι p.2.2)) ∧
      (∀ t s, ((0 : ℝ), (t, s)) ∈ e.source → h (t, ι s) = 0) ∧
      ∀ p ∈ e.target, mvfderiv I (fun y ↦ h (p.1, y)) p.2
          ((mpullback (Prod.mk p.1) (contMDiff_const.prodMk contMDiff_id) α).reebVectorField
            p.2) =
        -(mpullback (Prod.mk p.1) (contMDiff_const.prodMk contMDiff_id) α.timeDeriv).val p.2
          ![(mpullback (Prod.mk p.1) (contMDiff_const.prodMk contMDiff_id) α).reebVectorField
            p.2] := by
  -- The Reeb fields of the slices, and the right-hand side of the Reeb-direction equation.
  set R : ℝ → (x : M) → TangentSpace I x := fun t ↦
    (mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) α).reebVectorField
  set f : ℝ × M → ℝ := fun p ↦
    -(mpullback (Prod.mk p.1) (contMDiff_const.prodMk contMDiff_id) α.timeDeriv).val p.2
      ![R p.1 p.2]
  have hRsmooth : ContMDiff (𝓘(ℝ, ℝ).prod I) I.tangent ∞
      (fun p : ℝ × M ↦ (⟨p.2, R p.1 p.2⟩ : TangentBundle I M)) :=
    contMDiff_reebVectorField_mpullback_prodMk α hc
  have hRt (t : ℝ) : CMDiff 1 (fun y ↦ (⟨y, R t y⟩ : TangentBundle I M)) :=
    (hRsmooth.apply_param t).of_le (by simp)
  have hV := contMDiff_verticalField (J := 𝓘(ℝ, ℝ)) hRsmooth
  have hfsmooth : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) ∞ f :=
    (contMDiff_apply_reebVectorField_mpullback_prodMk α α.timeDeriv hc).neg
  -- On `ℝ × M`, the flow-out of `(t, s) ↦ (t, ι s)` along the vertical Reeb field is `e`.
  have he' : ∀ p ∈ e.source,
      (p.1, (p.2.1, ι p.2.2)) ∈ flowDomain (verticalField 𝓘(ℝ, ℝ) R) ∧
        e p = flowOf (verticalField 𝓘(ℝ, ℝ) R) p.1 (p.2.1, ι p.2.2) := fun p hp ↦
    ⟨mem_flowDomain_verticalField_iff.2 (he p hp).1,
      (he p hp).2.trans (flowOf_verticalField (hRt p.2.1) _ _).symm⟩
  obtain ⟨h, hsmooth, hval, hzero, hderiv⟩ := exists_mvfderiv_apply_eq_of_flowOut (n := (⊤ : ℕ∞))
    le_top hV hfsmooth ((contMDiff_fst.prodMk (hι.comp contMDiff_snd) :
      ContMDiff (𝓘(ℝ, ℝ).prod J) (𝓘(ℝ, ℝ).prod I) ∞ fun q : ℝ × S ↦ (q.1, ι q.2))) e he'
  refine ⟨h, hsmooth, fun p hp ↦ ?_, fun t s hs ↦ hzero (t, s) hs, fun p hp ↦ ?_⟩
  · -- Along the vertical field the parameter stays fixed, so the trajectory integral of `f` is
    -- the trajectory integral of the slice of `f` along the Reeb field `R_t`.
    rw [hval p hp, flowIntegral_def, flowIntegral_def]
    refine intervalIntegral.integral_congr fun u _ ↦ ?_
    rw [flowOf_verticalField (hRt p.2.1)]
  · -- The derivative of the slice `h_t` along `R_t` is the derivative of `h` along `(0, R_t)`.
    have hmd : MDifferentiableAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) h p :=
      (hsmooth.contMDiffAt (e.open_target.mem_nhds hp)).mdifferentiableAt (by simp)
    have hp' := hderiv p hp
    rw [verticalField_apply] at hp'
    exact (congrArg (· (R p.1 p.2)) (mvfderiv_curry_right p.1 p.2 hmd)).trans hp'

end TauCeti.SmoothForm
