/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.CauchyRiemann.Weak.Bootstrap

/-!
# Regularity of the nonlinear Cauchy–Riemann equation across a point

Let `J : ℂ → V → (V →L[ℝ] V)` and `η : ℂ → V → V` be of class `C^ℓ` jointly in `(z, x)` on an open
set containing the graph of `u` over a disc `B(z₀, R)`, with `J(z, u z)² = -1`. Suppose that `u` is
a `C¹` solution of

`∂ₛu + J(z, u) ∂ₜu = η(z, u)`

on the punctured disc `B(z₀, R) \ {z₀}`, and a weak solution in the sense of
`TauCeti.IsWeakCauchyRiemannOn` with an exponent `p > 2` on a smaller disc `B(z₀, ε)`. Then `u` is
of class `C^ℓ` on the whole disc (`TauCeti.contDiffOn_ball_of_isWeakCauchyRiemannOn`): near `z₀`
by interior bootstrapping (`TauCeti.contDiffOn_of_isWeakCauchyRiemannOn`) and off `z₀` because
classical solutions are regular (`TauCeti.contDiffOn_of_cauchyRiemann`). For `ℓ ≥ 1` the classical
equation then holds at `z₀` as well, since both of its sides are continuous and agree off `z₀`
(`TauCeti.fderiv_apply_one_add_eq_of_forall_ne`).

This is the analytic step of removal of singularities: the filling of a finite-energy puncture of
a pseudoholomorphic curve, or of a Floer solution, is a continuous weak solution across the
puncture with weak derivative in `Lᵖ` for some `p > 2`, and these results make it a classical
solution of the same regularity as the data.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed.,
  Section 4.5 (removal of singularities) and Appendix B.4 (elliptic bootstrapping).
-/

public section

open Complex Metric Set TopologicalSpace

namespace TauCeti

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {W : Set (ℂ × V)}
  {J : ℂ → V → V →L[ℝ] V} {η : ℂ → V → V} {u : ℂ → V} {z₀ : ℂ} {R ε : ℝ}

/-- **Regularity across a point.** Let `J` and `η` be of class `C^ℓ`, `ℓ ≤ ∞`, jointly in `(z, x)`
on an open set `W` containing the graph of `u` over `B(z₀, R)`, with `J(z, u z)² = -1` there. If
`u` is a `C¹` solution of `∂ₛu + J(z, u) ∂ₜu = η(z, u)` on `B(z₀, R) \ {z₀}` and a weak solution
with an exponent `p > 2` on a disc `B(z₀, ε)`, `0 < ε ≤ R`, then `u` is of class `C^ℓ` on
`B(z₀, R)`. -/
theorem contDiffOn_ball_of_isWeakCauchyRiemannOn [FiniteDimensional ℝ V] {ℓ : ℕ∞} {p : ENNReal}
    (hp : 2 < p) (hε : 0 < ε) (hεR : ε ≤ R) (hW : IsOpen W)
    (hJ : ContDiffOn ℝ ℓ (fun x : ℂ × V => J x.1 x.2) W)
    (hη : ContDiffOn ℝ ℓ (fun x : ℂ × V => η x.1 x.2) W) (huW : ∀ z ∈ ball z₀ R, (z, u z) ∈ W)
    (hJ2 : ∀ z ∈ ball z₀ R, J z (u z) * J z (u z) = -1)
    (hu : ContDiffOn ℝ 1 u (ball z₀ R \ {z₀}))
    (h : ∀ z ∈ ball z₀ R \ {z₀}, fderiv ℝ u z 1 + J z (u z) (fderiv ℝ u z I) = η z (u z))
    (hweak : IsWeakCauchyRiemannOn p (ball z₀ ε) J η u) :
    ContDiffOn ℝ ℓ u (ball z₀ R) := by
  have hεR' : ball z₀ ε ⊆ ball z₀ R := ball_subset_ball hεR
  -- Near `z₀`, bootstrapping of the weak solution.
  have hnear : ContDiffOn ℝ ℓ u (ball z₀ ε) :=
    contDiffOn_of_isWeakCauchyRiemannOn (Ω := ⟨ball z₀ ε, isOpen_ball⟩) hp hW hJ hη
      (fun z hz ↦ huW z (hεR' hz))
      ((MeasureTheory.ae_restrict_iff' measurableSet_ball).2
        (.of_forall fun z hz ↦ hJ2 z (hεR' hz))) hweak
  -- Off `z₀`, regularity of the classical solution.
  have hoff : ContDiffOn ℝ ℓ u (ball z₀ R \ {z₀}) :=
    contDiffOn_of_cauchyRiemann (Ω := ⟨ball z₀ R \ {z₀}, isOpen_ball.sdiff isClosed_singleton⟩)
      hW hJ hη (fun z hz ↦ huW z hz.1) (fun z hz ↦ hJ2 z hz.1) hu h
  refine contDiffOn_of_locally_contDiffOn fun z _ ↦ ?_
  by_cases hzz : z = z₀
  · exact ⟨ball z₀ ε, isOpen_ball, hzz ▸ mem_ball_self hε, hnear.mono inter_subset_right⟩
  · exact ⟨{z₀}ᶜ, isOpen_compl_singleton, hzz, hoff.mono fun w hw ↦ ⟨hw.1, hw.2⟩⟩

/-- **The classical equation across a point.** If `u` is `C¹` on an open set `Ω`, the fields
`z ↦ J(z, u z)` and `z ↦ η(z, u z)` are continuous on `Ω`, and `u` solves
`∂ₛu + J(z, u) ∂ₜu = η(z, u)` at every point of `Ω` other than `z₀`, then it solves it at `z₀` as
well. -/
theorem fderiv_apply_one_add_eq_of_forall_ne {Ω : Set ℂ} (hΩ : IsOpen Ω)
    (hu : ContDiffOn ℝ 1 u Ω) (hJ : ContinuousOn (fun z ↦ J z (u z)) Ω)
    (hη : ContinuousOn (fun z ↦ η z (u z)) Ω)
    (h : ∀ z ∈ Ω \ {z₀}, fderiv ℝ u z 1 + J z (u z) (fderiv ℝ u z I) = η z (u z)) :
    ∀ z ∈ Ω, fderiv ℝ u z 1 + J z (u z) (fderiv ℝ u z I) = η z (u z) := by
  have hdu : ContinuousOn (fderiv ℝ u) Ω := hu.continuousOn_fderiv_of_isOpen hΩ le_rfl
  refine EqOn.of_subset_closure h
    ((hdu.clm_apply continuousOn_const).add (hJ.clm_apply (hdu.clm_apply continuousOn_const))) hη
    sdiff_subset ?_
  rw [Set.sdiff_eq]
  exact (dense_compl_singleton z₀).open_subset_closure_inter hΩ

end TauCeti
