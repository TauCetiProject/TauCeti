/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Closed
public import TauCeti.Geometry.Manifold.DifferentialForm.HomotopyOperator
public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Smooth

/-!
# The homotopy operator along homotopies of cylinder maps

Let `h` be the homotopy operator of the cylinder `M × [0, 1]` (`TauCeti.homotopyOperator`),
`(h φ)(x) = ∫₀¹ φ(x, t)(∂ₜ, (·, 0)) dt`. For a map `f : M × [0, 1] → N` and a form `σ` on `N`,
`h (f^* σ)` integrates `σ` over the paths `t ↦ f (x, t)`: it is the form `∫₀¹ f_t^* (ι_{∂ₜ f} σ) dt`
on `M`. This file shows that, for a closed `σ`, this form changes only by an exact form when `f`
moves through a homotopy that keeps both time ends stationary.

Precisely, let `G : (M × [0, 1]) × [0, 1] → N`, `((x, t), s) ↦ G ((x, t), s)`, be a smooth homotopy
from `f = G (·, 0)` to `g = G (·, 1)` such that `G ((x, 0), s)` and `G ((x, 1), s)` do not depend
on `s`. Then for every closed smooth form `σ` on `N`

`d (h (h (G^* σ))) = h (f^* σ) - h (g^* σ)`

(`TauCeti.mextDeriv_homotopyOperator_homotopyOperator_mpullback`), where the inner homotopy
operator integrates over `s` and the outer one over `t`. The proof combines the cochain-homotopy
identities of both operators. In `s`, the closed form `G^* σ` gives `d (h (G^* σ)) = g^* σ - f^* σ`.
In `t`, the ends of `h (G^* σ)` vanish: over `t = 0` and `t = 1` the homotopy factors through the
projection to `M`, which kills the unit time vector `∂ₛ`
(`TauCeti.homotopyOperator_mpullback_fst`).

For a diffeotopy `φ_t` of a manifold with a closed two-form `σ`, `h (φ^* σ)` is the flux form, so
this is the homotopy invariance of flux (`TauCeti.Diffeotopy.fluxForm_sub_fluxForm_mem_exactForms`).

## Main results

* `TauCeti.homotopyOperator_mpullback_fst`: the homotopy operator vanishes on forms pulled back
  from `M` along the projection `M × [0, 1] → M`.
* `TauCeti.mextDeriv_homotopyOperator_homotopyOperator_mpullback`: for a closed form `σ` and a
  homotopy `G` from `f` to `g` stationary at both time ends, `d (h (h (G^* σ))) = h (f^* σ) -
  h (g^* σ)`.

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

/-- The homotopy operator vanishes on every form pulled back from `M` along the projection
`M × [0, 1] → M`: the derivative of the projection kills the unit time vector `∂ₜ`. -/
@[simp]
theorem homotopyOperator_mpullback_fst (α : RoughForm I M F (k + 1)) :
    homotopyOperator (mpullback (I.prod (𝓡∂ 1)) I (Prod.fst : M × Icc (0 : ℝ) 1 → M) α) = 0 := by
  funext x
  refine homotopyOperator_apply_eq_zero fun t v ↦ ?_
  rw [mpullback_apply, mfderiv_fst]
  exact (α x).map_coord_zero 0 rfl

variable {E' H' N : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {I' : ModelWithCorners ℝ E' H'} [TopologicalSpace N] [ChartedSpace H' N]

variable [IsManifold I ∞ M] [IsManifold I' ∞ N] [CompleteSpace F]

/-- Over a time end `t = c` at which the homotopy `G` is stationary in `s`, the slice at `c` of
the homotopy operator in `s` of `G^* σ` vanishes. -/
private theorem mpullback_slice_homotopyOperator_mpullback_eq_zero (σ : SmoothForm I' N F (k + 2))
    {G : (M × Icc (0 : ℝ) 1) × Icc (0 : ℝ) 1 → N}
    (hG : ContMDiff ((I.prod (𝓡∂ 1)).prod (𝓡∂ 1)) I' ∞ G) (c : Icc (0 : ℝ) 1)
    (hc : ∀ x s, G ((x, c), s) = G ((x, c), 0)) :
    mpullback I (I.prod (𝓡∂ 1)) (fun x ↦ (x, c))
        (homotopyOperator (SmoothForm.mpullback G hG σ).1) = 0 := by
  have hslice : ContMDiff I (I.prod (𝓡∂ 1)) ∞ fun x : M ↦ (x, c) :=
    contMDiff_id.prodMk contMDiff_const
  have hend : ContMDiff I I' ∞ fun x ↦ G ((x, c), 0) :=
    hG.comp (hslice.prodMk contMDiff_const)
  -- Over `t = c`, the homotopy is the stationary map `((x, c), s) ↦ G ((x, c), 0)`.
  have hfac : G ∘ Prod.map (fun x ↦ (x, c)) id = (fun x ↦ G ((x, c), 0)) ∘ Prod.fst :=
    funext fun p ↦ hc p.1 p.2
  rw [← homotopyOperator_mpullback_prodMap_id_of_isSmoothForm
      (hslice.mdifferentiable (by simp))
      ((SmoothForm.mpullback G hG σ).isSmoothForm.of_le (by simp)),
    SmoothForm.coe_mpullback,
    ← mpullback_comp ((hslice.prodMap contMDiff_id).mdifferentiable (by simp))
      (hG.mdifferentiable (by simp)), hfac,
    mpullback_comp mdifferentiable_fst (hend.mdifferentiable (by simp)),
    homotopyOperator_mpullback_fst]

/-- **Homotopy invariance of the homotopy operator.** Let `G` be a smooth homotopy from
`f = G (·, 0)` to `g = G (·, 1)`, maps from the cylinder `M × [0, 1]` to `N`, such that
`G ((x, 0), s)` and `G ((x, 1), s)` do not depend on `s`. For a closed smooth form `σ` on `N`, the
forms `h (f^* σ)` and `h (g^* σ)` on `M` differ by the exterior derivative of `h (h (G^* σ))`,
where the inner homotopy operator integrates over `s` and the outer one over `t`. -/
theorem mextDeriv_homotopyOperator_homotopyOperator_mpullback {σ : SmoothForm I' N F (k + 2)}
    (hσ : σ.IsClosed) {G : (M × Icc (0 : ℝ) 1) × Icc (0 : ℝ) 1 → N}
    (hG : ContMDiff ((I.prod (𝓡∂ 1)).prod (𝓡∂ 1)) I' ∞ G)
    (hG₀ : ∀ x s, G ((x, 0), s) = G ((x, 0), 0)) (hG₁ : ∀ x s, G ((x, 1), s) = G ((x, 1), 0)) :
    mextDeriv (homotopyOperator (homotopyOperator
        (mpullback ((I.prod (𝓡∂ 1)).prod (𝓡∂ 1)) I' G σ.1))) =
      homotopyOperator (mpullback (I.prod (𝓡∂ 1)) I' (fun p ↦ G (p, 0)) σ.1) -
        homotopyOperator (mpullback (I.prod (𝓡∂ 1)) I' (fun p ↦ G (p, 1)) σ.1) := by
  have : IsManifold I ((⊤ : ℕ∞) + 1 : WithTop ℕ∞) M := IsManifold.of_le (n := ∞) (by simp)
  have : IsManifold (I.prod (𝓡∂ 1)) ((⊤ : ℕ∞) + 1 : WithTop ℕ∞) (M × Icc (0 : ℝ) 1) :=
    IsManifold.of_le (n := ∞) (by simp)
  have hres (c : Icc (0 : ℝ) 1) : ContMDiff (I.prod (𝓡∂ 1)) ((I.prod (𝓡∂ 1)).prod (𝓡∂ 1)) ∞
      fun p : M × Icc (0 : ℝ) 1 ↦ (p, c) :=
    contMDiff_id.prodMk contMDiff_const
  -- The two ends `f = G (·, 0)` and `g = G (·, 1)` of the homotopy, and `τ = G^* σ`.
  set f : M × Icc (0 : ℝ) 1 → N := fun p ↦ G (p, 0)
  set g : M × Icc (0 : ℝ) 1 → N := fun p ↦ G (p, 1)
  have hf : ContMDiff (I.prod (𝓡∂ 1)) I' ∞ f := hG.comp (hres 0)
  have hg : ContMDiff (I.prod (𝓡∂ 1)) I' ∞ g := hG.comp (hres 1)
  set τ := SmoothForm.mpullback G hG σ
  -- `L = h_s τ` satisfies `d L = g^* σ - f^* σ`, by the cochain-homotopy identity in `s`.
  set L := homotopyOperator τ.1
  have hLs : IsSmoothForm (I.prod (𝓡∂ 1)) ∞ L := IsSmoothForm.homotopyOperator τ.isSmoothForm
  have hdL : mextDeriv L =
      (SmoothForm.mpullback g hg σ - SmoothForm.mpullback f hf σ : SmoothForm _ _ F _).1 := by
    funext p
    rw [mextDeriv_homotopyOperator (τ.isSmoothForm.of_le (by simp))
      ((SmoothForm.isClosed_def _).mp (hσ.mpullback G hG)) p, SmoothForm.coe_mpullback,
      ← mpullback_comp ((hres 1).mdifferentiable (by simp)) (hG.mdifferentiable (by simp)),
      ← mpullback_comp ((hres 0).mdifferentiable (by simp)) (hG.mdifferentiable (by simp)),
      Submodule.coe_sub, Pi.sub_apply, SmoothForm.coe_mpullback, SmoothForm.coe_mpullback]
    rfl
  -- The ends of `L` vanish, since `G` is stationary in `s` over `t = 0` and `t = 1`.
  have hL₀ := mpullback_slice_homotopyOperator_mpullback_eq_zero σ hG 0 hG₀
  have hL₁ := mpullback_slice_homotopyOperator_mpullback_eq_zero σ hG 1 hG₁
  -- The cochain-homotopy identity in `t` for `L` concludes.
  rw [← SmoothForm.coe_mpullback G hG, ← SmoothForm.coe_mpullback f hf,
    ← SmoothForm.coe_mpullback g hg]
  funext x
  have key := mextDeriv_homotopyOperator_add_homotopyOperator_mextDeriv (hLs.of_le (by simp)) x
  rw [hdL, hL₀, hL₁, Pi.zero_apply, sub_zero] at key
  -- The homotopy operator in `t` is additive on the continuous forms `g^* σ - f^* σ` and `f^* σ`.
  have hadd := homotopyOperator_add
    ((SmoothForm.mpullback g hg σ - SmoothForm.mpullback f hf σ).isSmoothForm.of_le (by simp))
    ((SmoothForm.mpullback f hf σ).isSmoothForm.of_le (by simp))
  rw [Submodule.coe_sub, sub_add_cancel] at hadd
  rw [eq_neg_of_add_eq_zero_left key, Pi.sub_apply, hadd, Pi.add_apply]
  abel

end TauCeti
