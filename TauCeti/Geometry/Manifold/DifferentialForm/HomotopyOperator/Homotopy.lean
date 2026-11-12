/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.HomotopyOperator
public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Smooth
import TauCeti.Geometry.Manifold.DifferentialForm.Naturality

/-!
# The homotopy operator along homotopies of cylinder maps

Let `h` be the homotopy operator of the cylinder `M × [0, 1]` (`TauCeti.homotopyOperator`),
`(h φ)(x) = ∫₀¹ φ(x, t)(∂ₜ, (·, 0)) dt`. For a map `f : M × [0, 1] → N` and a `(k + 1)`-form `σ`
on `N`, `h (f^* σ)` integrates `σ` over the paths `t ↦ f (x, t)`: it is the `k`-form
`x ↦ ∫₀¹ σ_{f (x, t)} (∂ₜ f (x, t), d f_t ·) dt` on `M`, where `f_t = f (·, t)`. This file shows
that, for a closed `σ`, this form changes only by an exact form when `f` moves through a homotopy
that keeps both time ends stationary.

The identity behind this lives on the double cylinder `(M × [0, 1]) × [0, 1]`, with coordinates
`((x, t), s)`. For a closed `C¹` form `φ` there, with values in a Banach space, write `h_s` for
the homotopy operator in `s` and `h_t` for the one in `t`. Combining the cochain-homotopy
identities of both operators gives

`d (h_t (h_s φ)) = (ι₁^* (h_s φ) - ι₀^* (h_s φ)) - (h_t (j₁^* φ) - h_t (j₀^* φ))`

(`TauCeti.mextDeriv_homotopyOperator_homotopyOperator`), where `ι_c x = (x, c)` are the slices in
`t` and `j_c p = (p, c)` the slices in `s`.

Now let `G : (M × [0, 1]) × [0, 1] → N` be a `C²` homotopy from `f = G (·, 0)` to `g = G (·, 1)`
such that `G ((x, 0), s)` and `G ((x, 1), s)` do not depend on `s`. Then for every closed `C¹`
`(k + 2)`-form `σ` on `N` with values in a Banach space

`d (h (h (G^* σ))) = h (f^* σ) - h (g^* σ)`

(`TauCeti.mextDeriv_homotopyOperator_homotopyOperator_mpullback`): the `t`-ends of `h_s (G^* σ)`
vanish, since the homotopy is stationary in `s` over `t = 0` and `t = 1`
(`TauCeti.homotopyOperator_mpullback_apply_eq_zero`).

For a diffeotopy `φ_t` of a manifold with a closed two-form `σ`, `h (φ^* σ)` is the flux form, so
this is the homotopy invariance of flux (`TauCeti.Diffeotopy.fluxForm_sub_fluxForm_mem_exactForms`).
The general identity on the double cylinder also gives the flux of a pointwise composite of
diffeotopies (`TauCeti.Diffeotopy.fluxForm_trans_sub_sub_mem_exactForms`).

## Main results

* `TauCeti.mextDeriv_homotopyOperator_homotopyOperator`: for a closed `C¹` form `φ` on the double
  cylinder, `d (h_t (h_s φ))` in terms of the slices of `h_s φ` and of `φ`.
* `TauCeti.mextDeriv_homotopyOperator_homotopyOperator_mpullback`: for a closed `C¹`
  `(k + 2)`-form `σ` with values in a Banach space and a `C²` homotopy `G` from `f` to `g`
  stationary at both time ends, `d (h (h (G^* σ))) = h (f^* σ) - h (g^* σ)`.

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

variable {E' H' N : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {I' : ModelWithCorners ℝ E' H'} [TopologicalSpace N] [ChartedSpace H' N]

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
  -- The homotopy operator in `t` is additive on the continuous forms `j₁^* φ - j₀^* φ` and
  -- `j₀^* φ`.
  have hadd := homotopyOperator_add (sub_eq_add_neg φ₁ φ₀ ▸ hφ₁.add hφ₀.neg) hφ₀
  rw [sub_add_cancel] at hadd
  -- The cochain-homotopy identity in `t` for `L` concludes.
  funext x
  have key := mextDeriv_homotopyOperator_add_homotopyOperator_mextDeriv hL x
  rw [hdL] at key
  rw [Pi.sub_apply, Pi.sub_apply, Pi.sub_apply, ← key, hadd, Pi.add_apply]
  abel

/-- **Homotopy invariance of the homotopy operator.** Let `G` be a `C²` homotopy from
`f = G (·, 0)` to `g = G (·, 1)`, maps from the cylinder `M × [0, 1]` to `N`, such that
`G ((x, 0), s)` and `G ((x, 1), s)` do not depend on `s`. For a closed `C¹` `(k + 2)`-form `σ` on
`N` with values in a Banach space, the forms `h (f^* σ)` and `h (g^* σ)` on `M` differ by the
exterior derivative of `h (h (G^* σ))`, where the inner homotopy operator integrates over `s` and
the outer one over `t`. -/
theorem mextDeriv_homotopyOperator_homotopyOperator_mpullback [IsManifold I' 2 N]
    {σ : RoughForm I' N F (k + 2)} (hσ : IsSmoothForm I' 1 σ) (hclosed : mextDeriv σ = 0)
    {G : (M × Icc (0 : ℝ) 1) × Icc (0 : ℝ) 1 → N}
    (hG : ContMDiff ((I.prod (𝓡∂ 1)).prod (𝓡∂ 1)) I' 2 G)
    (hG₀ : ∀ x s, G ((x, 0), s) = G ((x, 0), 0)) (hG₁ : ∀ x s, G ((x, 1), s) = G ((x, 1), 0)) :
    mextDeriv (homotopyOperator (homotopyOperator
        (mpullback ((I.prod (𝓡∂ 1)).prod (𝓡∂ 1)) I' G σ))) =
      homotopyOperator (mpullback (I.prod (𝓡∂ 1)) I' (fun p ↦ G (p, 0)) σ) -
        homotopyOperator (mpullback (I.prod (𝓡∂ 1)) I' (fun p ↦ G (p, 1)) σ) := by
  have hres (c : Icc (0 : ℝ) 1) : MDifferentiable (I.prod (𝓡∂ 1)) ((I.prod (𝓡∂ 1)).prod (𝓡∂ 1))
      fun p : M × Icc (0 : ℝ) 1 ↦ (p, c) :=
    (contMDiff_id.prodMk contMDiff_const).mdifferentiable (n := 1) one_ne_zero
  have hGd : MDifferentiable ((I.prod (𝓡∂ 1)).prod (𝓡∂ 1)) I' G := hG.mdifferentiable two_ne_zero
  -- The ends in `t` of `h_s (G^* σ)` vanish, since `G` is stationary in `s` over `t = 0` and
  -- `t = 1`.
  have hend (c : Icc (0 : ℝ) 1) (hc : ∀ x s, G ((x, c), s) = G ((x, c), 0)) :
      mpullback I (I.prod (𝓡∂ 1)) (fun x ↦ (x, c))
        (homotopyOperator (mpullback ((I.prod (𝓡∂ 1)).prod (𝓡∂ 1)) I' G σ)) = 0 :=
    funext fun x ↦ mpullback_apply_eq_zero (homotopyOperator_mpullback_apply_eq_zero (hc x) σ)
  rw [mextDeriv_homotopyOperator_homotopyOperator (hσ.mpullback hG)
      (hσ.mextDeriv_mpullback_eq_zero hclosed hG), hend 0 hG₀, hend 1 hG₁,
    ← mpullback_comp (hres 1) hGd, ← mpullback_comp (hres 0) hGd, sub_self, zero_sub, neg_sub]
  rfl

end TauCeti
