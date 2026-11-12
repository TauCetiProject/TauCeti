/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.HomotopyOperator
public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Smooth

/-!
# The iterated homotopy operator on the double cylinder

Let `h` be the homotopy operator of the cylinder `M × [0, 1]` (`TauCeti.homotopyOperator`),
`(h φ)(x) = ∫₀¹ φ(x, t)(∂ₜ, (·, 0)) dt`. On the double cylinder `(M × [0, 1]) × [0, 1]`, with
coordinates `((x, t), s)`, write `h_s` for the homotopy operator in `s` and `h_t` for the one in
`t`. For a closed `C¹` form `φ` there, with values in a Banach space, combining the
cochain-homotopy identities of both operators gives

`d (h_t (h_s φ)) = (ι₁^* (h_s φ) - ι₀^* (h_s φ)) - (h_t (j₁^* φ) - h_t (j₀^* φ))`

(`TauCeti.mextDeriv_homotopyOperator_homotopyOperator`), where `ι_c x = (x, c)` are the slices in
`t` and `j_c p = (p, c)` the slices in `s`. No condition on `φ` at the ends of the cylinder is
needed. When `φ` vanishes on `∂ₛ` over both ends `t = 0` and `t = 1`, the first difference
vanishes; that special case is `TauCeti.homotopyOperator_mpullback_one_sub_mpullback_zero`, which
gives the homotopy invariance of flux (`TauCeti.Diffeotopy.fluxForm_sub_fluxForm_mem_exactForms`).
The general identity, whose `t`-ends need not vanish, gives the flux of a pointwise composite of
diffeotopies (`TauCeti.Diffeotopy.fluxForm_trans_sub_sub_mem_exactForms`).

## Main results

* `TauCeti.mextDeriv_homotopyOperator_homotopyOperator`: for a closed `C¹` form `φ` on the double
  cylinder, `d (h_t (h_s φ))` in terms of the slices of `h_s φ` and of `φ`.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Chapter 17, section Homotopy
  Invariance, whose homotopy operator on `M × I` this is.
* R. Bott and L. W. Tu, *Differential Forms in Algebraic Topology*, GTM 82, §4.
-/

public section

noncomputable section

open Set
open scoped ContDiff Manifold

namespace TauCeti

variable {E H M F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {k : ℕ}

variable [IsManifold I 2 M] [CompleteSpace F]

/-- **The iterated homotopy operator on the double cylinder.** For a closed `C¹` `(k + 2)`-form
`φ` on `(M × [0, 1]) × [0, 1]` with values in a Banach space, on a `C²` manifold `M` possibly with
boundary or corners, the exterior derivative of `h_t (h_s φ)` is
`(ι₁^* (h_s φ) - ι₀^* (h_s φ)) - (h_t (j₁^* φ) - h_t (j₀^* φ))`, where the inner homotopy operator
`h_s` integrates over the last coordinate `s` and the outer one `h_t` over `t`, `ι_c x = (x, c)`,
and `j_c p = (p, c)`. -/
theorem mextDeriv_homotopyOperator_homotopyOperator
    {φ : RoughForm ((I.prod (𝓡∂ 1)).prod (𝓡∂ 1)) ((M × Icc (0 : ℝ) 1) × Icc (0 : ℝ) 1) F (k + 2)}
    (hφ : IsSmoothForm ((I.prod (𝓡∂ 1)).prod (𝓡∂ 1)) 1 φ) (hclosed : mextDeriv φ = 0) :
    mextDeriv (homotopyOperator (homotopyOperator φ)) =
      (mpullback I (I.prod (𝓡∂ 1)) (fun x ↦ (x, 1)) (homotopyOperator φ) -
          mpullback I (I.prod (𝓡∂ 1)) (fun x ↦ (x, 0)) (homotopyOperator φ)) -
        (homotopyOperator
            (mpullback (I.prod (𝓡∂ 1)) ((I.prod (𝓡∂ 1)).prod (𝓡∂ 1)) (fun p ↦ (p, 1)) φ) -
          homotopyOperator
            (mpullback (I.prod (𝓡∂ 1)) ((I.prod (𝓡∂ 1)).prod (𝓡∂ 1)) (fun p ↦ (p, 0)) φ)) := by
  have : IsManifold (I.prod (𝓡∂ 1)) ((1 : ℕ∞) + 1 : WithTop ℕ∞) (M × Icc (0 : ℝ) 1) :=
    IsManifold.of_le (n := 2) (by norm_num)
  have hres (c : Icc (0 : ℝ) 1) : ContMDiff (I.prod (𝓡∂ 1)) ((I.prod (𝓡∂ 1)).prod (𝓡∂ 1))
      ((0 : ℕ∞) + 1) fun p : M × Icc (0 : ℝ) 1 ↦ (p, c) :=
    contMDiff_id.prodMk contMDiff_const
  -- The slices `j₁^* φ` and `j₀^* φ` in `s` are continuous.
  set φ₁ := mpullback (I.prod (𝓡∂ 1)) ((I.prod (𝓡∂ 1)).prod (𝓡∂ 1)) (fun p ↦ (p, 1)) φ
  set φ₀ := mpullback (I.prod (𝓡∂ 1)) ((I.prod (𝓡∂ 1)).prod (𝓡∂ 1)) (fun p ↦ (p, 0)) φ
  have hφ₁ : IsSmoothForm (I.prod (𝓡∂ 1)) 0 φ₁ := (hφ.of_le (by simp)).mpullback (hres 1)
  have hφ₀ : IsSmoothForm (I.prod (𝓡∂ 1)) 0 φ₀ := (hφ.of_le (by simp)).mpullback (hres 0)
  -- `L = h_s φ` is `C¹` and, by the cochain-homotopy identity in `s`, `d L = j₁^* φ - j₀^* φ`.
  have hL : IsSmoothForm (I.prod (𝓡∂ 1)) 1 (homotopyOperator φ) := hφ.homotopyOperator
  have hdL : mextDeriv (homotopyOperator φ) = φ₁ - φ₀ :=
    funext (mextDeriv_homotopyOperator hφ hclosed)
  -- The homotopy operator in `t` commutes with the difference of the continuous forms `j₁^* φ`
  -- and `j₀^* φ`; the cochain-homotopy identity in `t` for `L` concludes.
  funext x
  have key := mextDeriv_homotopyOperator_add_homotopyOperator_mextDeriv hL x
  rw [hdL, homotopyOperator_sub hφ₁ hφ₀] at key
  rw [Pi.sub_apply, Pi.sub_apply, Pi.sub_apply, ← key, Pi.sub_apply]
  abel

end TauCeti
