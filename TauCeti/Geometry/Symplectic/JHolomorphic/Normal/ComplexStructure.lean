/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.JHolomorphic.Normal.Linearization
public import TauCeti.Geometry.Symplectic.Manifold.Nijenhuis
import TauCeti.Analysis.Calculus.FDeriv.ContinuousLinearMap

/-!
# The complex structure of the normal fibre and the normal Cauchy–Riemann operator

Let `u` be a parametrized curve and `x` a point where its Cauchy–Riemann defect
`du ∘ j - J(u) ∘ du` vanishes. Then `J (u x) (du v) = du (j v)`, so the tangent image
`range (du x)` is `J (u x)`-invariant and `J (u x)` descends to the normal fibre
`V ⧸ range (du x)`. This is the normal structure `J_N` (`TauCeti.normalStructure`), a complex
structure when `J (u x)² = -1` (`TauCeti.normalStructure_normalStructure`). For an embedded curve
the normal fibre is the fibre of its normal bundle.

The normal Cauchy–Riemann linearization `D_N`
(`TauCeti.normalCauchyRiemannLinearization`) has the two properties of a real Cauchy–Riemann
operator on this complex normal fibre:

* it is anti-linear in the source direction, `D_N ξ (j v) = -J_N (D_N ξ v)`, when `j² = -1` and
  `J² = -1` near `u x` (`TauCeti.normalCauchyRiemannLinearization_comp_eq_neg_comp`);
* it is complex linear in the section up to a term of order zero:
  `D_N (J ξ) v = J_N (D_N ξ v) + [N_J (du v, ξ x)]`, where `N_J` is the Nijenhuis tensor of `J`
  (`TauCeti.normalCauchyRiemannLinearization_clm_apply_eq_add_nijenhuis`; the coordinate form
  `TauCeti.normalCauchyRiemannLinearization_clm_apply` only needs `J` differentiable at `u x`).

Together with the Leibniz rule `TauCeti.normalCauchyRiemannLinearization_fun_smul`, whose symbol
`ξ ↦ df(j v) ξ - df(v) J ξ` is anti-linear in `v`, these are the pointwise laws of a real
Cauchy–Riemann operator on the complex normal fibre. Its failure to commute with `J_N` is the
Nijenhuis term: when `N_J` vanishes at `u x`, for instance for an integrable `J`, the normal
operator commutes with `J_N`
(`TauCeti.normalCauchyRiemannLinearization_clm_eq_comp_of_nijenhuis_eq_zero`). The target `J`
need not be integrable. These are pointwise statements in local coordinates; global bundles, Sobolev
realizations and Fredholm theory are separate.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Section 3.1 (the linearized operator) and Appendix C (real linear Cauchy–Riemann operators).
* C. H. Taubes, *Counting pseudo-holomorphic submanifolds in dimension 4*,
  J. Differential Geom. 44 (1996), 818–893 (the normal operator of an embedded curve).
-/

public section

noncomputable section

open scoped Manifold

namespace TauCeti

open ContinuousLinearMap Filter
open scoped Topology

variable {U V : Type*}
variable [NormedAddCommGroup U] [NormedSpace ℝ U]
variable [NormedAddCommGroup V] [NormedSpace ℝ V]
variable {j : U →L[ℝ] U} {J : V → V →L[ℝ] V} {u : U → V} {x : U}

/-- Where the Cauchy–Riemann defect vanishes, the tangent image `range (du x)` is invariant under
`J (u x)`, since `J (u x) (du v) = du (j v)`. -/
theorem range_fderiv_le_comap_range_fderiv (hhol : cauchyRiemannOperator j J u x = 0) :
    (fderiv ℝ u x).toLinearMap.range ≤
      (fderiv ℝ u x).toLinearMap.range.comap (J (u x)).toLinearMap := by
  rintro _ ⟨v, rfl⟩
  exact ⟨j v, fderiv_apply_eq_of_cauchyRiemannOperator_eq_zero hhol v⟩

/-- The **normal structure** `J_N`: where the Cauchy–Riemann defect of `u` vanishes, `J (u x)`
descends to the normal fibre `V ⧸ range (du x)`. -/
def normalStructure (hhol : cauchyRiemannOperator j J u x = 0) :
    Module.End ℝ (V ⧸ (fderiv ℝ u x).toLinearMap.range) :=
  Submodule.mapQ _ _ (J (u x)).toLinearMap (range_fderiv_le_comap_range_fderiv hhol)

/-- The normal structure is the quotient map `Submodule.mapQ` of `J (u x)`. -/
theorem normalStructure_def (hhol : cauchyRiemannOperator j J u x = 0) :
    normalStructure hhol =
      Submodule.mapQ _ _ (J (u x)).toLinearMap (range_fderiv_le_comap_range_fderiv hhol) :=
  (rfl)

/-- The normal structure is characterized by its composition with the quotient map. -/
@[simp]
theorem normalStructure_comp_mkQ (hhol : cauchyRiemannOperator j J u x = 0) :
    (normalStructure hhol).comp (fderiv ℝ u x).toLinearMap.range.mkQ =
      (fderiv ℝ u x).toLinearMap.range.mkQ.comp (J (u x)).toLinearMap :=
  Submodule.mapQ_mkQ _ _ _

/-- The normal structure sends the class of `w` to the class of `J (u x) w`. -/
@[simp]
theorem normalStructure_mk (hhol : cauchyRiemannOperator j J u x = 0) (w : V) :
    normalStructure hhol (Submodule.Quotient.mk w) = Submodule.Quotient.mk (J (u x) w) :=
  (rfl)

/-- The normal structure squares to `-1` when `J (u x)` does, so it is a complex structure on the
normal fibre. -/
theorem normalStructure_normalStructure (hhol : cauchyRiemannOperator j J u x = 0)
    (hJ : ∀ w, J (u x) (J (u x) w) = -w) (w : V ⧸ (fderiv ℝ u x).toLinearMap.range) :
    normalStructure hhol (normalStructure hhol w) = -w := by
  induction w using Submodule.Quotient.induction_on with
  | H w => simp [hJ]

/-- **Anti-linearity of the normal operator.** At a point where the Cauchy–Riemann defect
vanishes, for `j² = -1` and `J² = -1` near `u x`, the normal linearization satisfies
`D_N ξ (j v) = -J_N (D_N ξ v)`. -/
theorem normalCauchyRiemannLinearization_comp_eq_neg_comp (ξ : U → V)
    (hj : ∀ v, j (j v) = -v) (hJsq : ∀ᶠ y in 𝓝 (u x), ∀ w, J y (J y w) = -w)
    (hhol : cauchyRiemannOperator j J u x = 0) :
    (normalCauchyRiemannLinearization j J u ξ x).comp j.toLinearMap =
      -(normalStructure hhol).comp (normalCauchyRiemannLinearization j J u ξ x) := by
  ext v
  have h := congrArg (fun L : U →L[ℝ] V ↦ L v)
    (cauchyRiemannLinearization_comp_eq_neg_comp ξ hj hJsq hhol)
  simp only [comp_apply, neg_apply] at h
  simp [h]

/-- **The normal operator on `J ξ`.** At a point where the Cauchy–Riemann defect vanishes, with
`w = du v` and `J'` the derivative of `J` at `u x`, the normal linearization on the lift
`y ↦ J (u y) (ξ y)` is `J_N (D_N ξ v)` plus the class of the coordinate Nijenhuis expression
`J' (J w) ξ - J' (J ξ) w + J (J' ξ w) - J (J' w ξ)`. -/
theorem normalCauchyRiemannLinearization_clm_apply {ξ : U → V}
    (hu : DifferentiableAt ℝ u x) (hξ : DifferentiableAt ℝ ξ x)
    (hJ : DifferentiableAt ℝ J (u x)) (hhol : cauchyRiemannOperator j J u x = 0) (v : U) :
    normalCauchyRiemannLinearization j J u (fun y ↦ J (u y) (ξ y)) x v =
      normalStructure hhol (normalCauchyRiemannLinearization j J u ξ x v) +
        Submodule.Quotient.mk
          (fderiv ℝ J (u x) (J (u x) (fderiv ℝ u x v)) (ξ x) -
            fderiv ℝ J (u x) (J (u x) (ξ x)) (fderiv ℝ u x v) +
            J (u x) (fderiv ℝ J (u x) (ξ x) (fderiv ℝ u x v)) -
            J (u x) (fderiv ℝ J (u x) (fderiv ℝ u x v) (ξ x))) := by
  simp [cauchyRiemannLinearization_clm_apply hu hξ hJ hhol]

section Nijenhuis

variable [FiniteDimensional ℝ V] (K : SmoothAlmostComplexStructure 𝓘(ℝ, V) V)

/-- **The normal operator on `J ξ` and the Nijenhuis tensor.** Let `J` agree near `u x` with a
smooth almost complex structure `K` on `V`. At a point where the Cauchy–Riemann defect vanishes,
`D_N (J ξ) v = J_N (D_N ξ v) + [N_K (du v, ξ x)]`, where `N_K` is the Nijenhuis tensor of `K`. -/
theorem normalCauchyRiemannLinearization_clm_apply_eq_add_nijenhuis {ξ : U → V}
    (hK : (fun y ↦ (K.toEndomorphism y : V →L[ℝ] V)) =ᶠ[𝓝 (u x)] J)
    (hu : DifferentiableAt ℝ u x) (hξ : DifferentiableAt ℝ ξ x)
    (hhol : cauchyRiemannOperator j J u x = 0) (v : U) :
    normalCauchyRiemannLinearization j J u (fun y ↦ J (u y) (ξ y)) x v =
      normalStructure hhol (normalCauchyRiemannLinearization j J u ξ x v) +
        Submodule.Quotient.mk
          ((K.nijenhuis (u x) : V →L[ℝ] V →L[ℝ] V) (fderiv ℝ u x v) (ξ x)) := by
  have hJ : DifferentiableAt ℝ J (u x) :=
    ((K.contDiff_toEndomorphism.differentiable (by simp)) (u x)).congr_of_eventuallyEq hK.symm
  -- `TangentSpace 𝓘(ℝ, V) (u x)` is `V` by definition. Make this identification once at the
  -- tensor level, so that the rest of the proof uses the ordinary model-space instances.
  let NK : V →L[ℝ] V →L[ℝ] V := K.nijenhuis (u x)
  have hN : NK (fderiv ℝ u x v) (ξ x) =
      fderiv ℝ J (u x) (J (u x) (fderiv ℝ u x v)) (ξ x) -
        fderiv ℝ J (u x) (J (u x) (ξ x)) (fderiv ℝ u x v) +
        J (u x) (fderiv ℝ J (u x) (ξ x) (fderiv ℝ u x v)) -
        J (u x) (fderiv ℝ J (u x) (fderiv ℝ u x v) (ξ x)) := by
    have h := K.nijenhuis_eq_fderiv J (u x) hK (fderiv ℝ u x v) (ξ x)
    simp only [fderiv_clm_apply_const_apply hJ] at h
    exact h
  change _ = _ + Submodule.Quotient.mk (NK (fderiv ℝ u x v) (ξ x))
  rw [normalCauchyRiemannLinearization_clm_apply hu hξ hJ hhol, hN]

/-- **Complex linearity of the normal operator where `N_K = 0`.** Let `J` agree near `u x` with a
smooth almost complex structure `K` on `V` whose Nijenhuis tensor vanishes at `u x`, for instance
an integrable one. At a point where the Cauchy–Riemann defect vanishes, the normal linearization
commutes with the normal structure: `D_N (J ξ) = J_N ∘ D_N ξ`. -/
theorem normalCauchyRiemannLinearization_clm_eq_comp_of_nijenhuis_eq_zero {ξ : U → V}
    (hK : (fun y ↦ (K.toEndomorphism y : V →L[ℝ] V)) =ᶠ[𝓝 (u x)] J)
    (hN : K.nijenhuis (u x) = 0) (hu : DifferentiableAt ℝ u x) (hξ : DifferentiableAt ℝ ξ x)
    (hhol : cauchyRiemannOperator j J u x = 0) :
    normalCauchyRiemannLinearization j J u (fun y ↦ J (u y) (ξ y)) x =
      (normalStructure hhol).comp (normalCauchyRiemannLinearization j J u ξ x) := by
  ext v
  rw [normalCauchyRiemannLinearization_clm_apply_eq_add_nijenhuis K hK hu hξ hhol,
    (K.nijenhuis_model_eq_zero_iff (u x)).1 hN]
  -- The remaining class is that of the zero vector, read in `TangentSpace 𝓘(ℝ, V) (u x) = V`.
  exact add_zero _

end Nijenhuis

end TauCeti
