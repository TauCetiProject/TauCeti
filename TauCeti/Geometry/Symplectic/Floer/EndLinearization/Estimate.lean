/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.AsymptoticOperator.Estimate
public import TauCeti.Geometry.Symplectic.Floer.EndLinearization

/-!
# The `L²` estimate of the linearized Floer operator on a cylindrical end

Let `u` be a map on a cylindrical end of a punctured Floer domain, with perturbation
`K = H_t dt`, whose loops converge to a nondegenerate one-periodic orbit `x` of `H` while the
slice defect `∂t u - X_{H_t}(u)` tends to zero. This file proves that the linearized Floer operator
`D_u` along `u` satisfies, on a far enough part of the end, the same `L²` estimate as the
stationary cylinder operator `D_x = ∂s + J_t(x) (∂t - S_t)` at the orbit, with
`S_t = dX_{H_t}(x(t))`: there are `C` and a far part `I` of the end such that

`∫ (g(∂s ξ, ∂s ξ) + g(∂t ξ - S ξ, ∂t ξ - S ξ) + g(ξ, ξ)) ≤ C ∫ g(D_u ξ, D_u ξ)`

over `[a, b] × [0, 1]`, for every `[a, b] ⊆ I` and every `C²` map `ξ` of period one in `t`
vanishing on the slices `s = a` and `s = b`, where `g_t = ω(·, J_t(x(t)) ·)`
(`TauCeti.SymplecticForm.exists_forall_setIntegral_le_mul_setIntegral_floerLinearization`). This
is the injectivity estimate of the linearized operator on the ends, the half of its Fredholm
property that is local to the ends.

The argument combines three results. The stationary operator `D_x` satisfies the cylinder
estimate at the nondegenerate orbit `x`
(`SymplecticForm.exists_forall_setIntegral_le_mul_setIntegral_stationaryCylinderOperator`). That
estimate is stable under perturbations `f` of `D_x ξ` with `‖f - D_x ξ‖ ≤ ε (‖∂t ξ‖ + ‖ξ‖)` for a
small enough `ε > 0`
(`TauCeti.Floer.exists_pos_forall_setIntegral_le_mul_setIntegral_of_norm_sub_le`). On a far
enough part of the end, `D_u` is such a perturbation of `D_x`
(`TauCeti.SymplecticForm.eventually_norm_floerLinearization_sub_stationaryCylinderOperator_le`).

The Sobolev completion, the surjectivity half and the patching with the compact core are not
treated here.

## References

* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), Lecture 2, on the operator `∂s + J ∂t + S(s, t)` with limits `S^±(t)`.
* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, 2nd ed., Section 3.1
  on the linearized operator.
-/

public section

open Function Filter Set MeasureTheory Topology
open scoped Manifold NNReal

namespace TauCeti

namespace SymplecticForm

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- **The `L²` estimate of the linearized Floer operator on a cylindrical end.** Let `x` be a
one-periodic orbit of a one-periodic, jointly `C²` time-dependent Hamiltonian `H` whose suspended
vector field is globally Lipschitz, with `x(0)` a nondegenerate fixed point of the time-one map.
Let `J_t(y)` be a `C¹` family of almost complex structures, `ω`-compatible along `x`. Let `u` be
`C¹` on the far part of an end, along a filter `l` such as `atTop` for a positive end or `atBot`
for a negative one, with loops `u(s, ·)` converging uniformly on `[0, 1]` to `x` and slice defect
`∂t u - X_{H_t}(u)` converging uniformly to zero there.

Then there are a constant `C ≥ 0` and a set `I ∈ l` such that the linearized Floer operator `D_u`
along `u` for the datum `K = H_t dt` satisfies, for every `[a, b] ⊆ I` and every `C²` map `ξ` of
period one in `t` vanishing on the slices `s = a` and `s = b`,

`∫ (g(∂s ξ, ∂s ξ) + g(∂t ξ - S ξ, ∂t ξ - S ξ) + g(ξ, ξ)) ≤ C ∫ g(D_u ξ, D_u ξ)`

over `[a, b] × [0, 1]`, for `g_t = ω(·, J_t(x(t)) ·)` and `S_t = dX_{H_t}(x(t))`. -/
theorem exists_forall_setIntegral_le_mul_setIntegral_floerLinearization
    (ω : SymplecticForm V) {H : ℝ → V → ℝ} {K : ℝ≥0}
    (hX : LipschitzWith K (ω.timeDependentHamiltonianSuspension H))
    (hH : ContDiff ℝ 2 (uncurry H)) (hHp : Periodic H 1) {x : ℝ → V}
    (hx : ∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) (hxp : Periodic x 1)
    (hnd : IsNondegenerateFixedPt 𝓘(ℝ, V) (ω.timeDependentHamiltonianFlow H hX 0 1) (x 0))
    {J : ℝ → V → AlmostComplexStructure V}
    (hJ : ContDiff ℝ 1 fun p : ℝ × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap)
    (hJx : ∀ t, ω.Compatible (J t (x t))) {l : Filter ℝ} {u : ℝ × ℝ → V}
    (hu : ∀ᶠ s in l, ∀ t, ContDiffAt ℝ 1 u (s, t))
    (hux : TendstoUniformlyOn (fun s t ↦ u (s, t)) x l (Icc 0 1))
    (hδ : TendstoUniformlyOn
      (fun s t ↦ sliceDefect (fun t ↦ ω.hamiltonianVectorField (H t)) u (s, t)) 0 l (Icc 0 1)) :
    ∃ C, 0 ≤ C ∧ ∃ I ∈ l, ∀ ⦃ξ : ℝ × ℝ → V⦄, ContDiff ℝ 2 ξ →
      (∀ s t, ξ (s, t + 1) = ξ (s, t)) → ∀ ⦃a b : ℝ⦄, a ≤ b → Icc a b ⊆ I →
        (∀ t, ξ (a, t) = 0) → (∀ t, ξ (b, t) = 0) →
        ∫ z in Icc a b ×ˢ Icc 0 1,
            ((ω.associatedBilinForm (J z.2 (x z.2)) (fderiv ℝ ξ z stdComplexLineReal)
                (fderiv ℝ ξ z stdComplexLineReal) +
              ω.associatedBilinForm (J z.2 (x z.2)) (fderiv ℝ ξ z stdComplexLineImag -
                  fderiv ℝ (ω.hamiltonianVectorField (H z.2)) (x z.2) (ξ z))
                (fderiv ℝ ξ z stdComplexLineImag -
                  fderiv ℝ (ω.hamiltonianVectorField (H z.2)) (x z.2) (ξ z))) +
              ω.associatedBilinForm (J z.2 (x z.2)) (ξ z) (ξ z)) ≤
          C * ∫ z in Icc a b ×ˢ Icc 0 1, ω.associatedBilinForm (J z.2 (x z.2))
            (ω.floerLinearization (fun w y ↦ (J w.2 y).toLinearMap.toContinuousLinearMap)
              (fun _ _ ↦ 0) (fun w ↦ H w.2) u ξ z)
            (ω.floerLinearization (fun w y ↦ (J w.2 y).toLinearMap.toContinuousLinearMap)
              (fun _ _ ↦ 0) (fun w ↦ H w.2) u ξ z) := by
  have hxc : Continuous x := continuous_iff_continuousAt.2 fun t ↦ (hx t).continuousAt
  have hJxc : Continuous fun p : ℝ × V ↦ J p.1 (x p.1) p.2 := by
    simpa [Function.comp_def] using
      ((hJ.continuous.comp (continuous_id.prodMk hxc)).comp continuous_fst).clm_apply
        continuous_snd
  -- The stationary cylinder estimate at `x`, and its stability under small perturbations.
  obtain ⟨C₀, hC₀, hst⟩ := ω.exists_forall_setIntegral_le_mul_setIntegral_stationaryCylinderOperator
    hX hH hHp hx hxp hnd hJx hJxc
  obtain ⟨ε, hε, C, hC, hpert⟩ :=
    Floer.exists_pos_forall_setIntegral_le_mul_setIntegral_of_norm_sub_le
      (fun t ↦ (hJx t).tames) hJxc (ω.continuous_fderiv_hamiltonianVectorField_comp hH hxc) hC₀
  -- On the far part of the end, `D_u` is within `ε` of the stationary cylinder operator.
  have hev := eventually_norm_floerLinearization_sub_stationaryCylinderOperator_le ω hJ hH
    isCompact_Icc hxc.continuousOn hux hδ hε
  refine ⟨C, hC, _, hev.and hu, fun ξ hξ hper a b hab hI ha hb ↦ ?_⟩
  have hJ' : ContDiff ℝ 1 (uncurry fun (w : ℝ × ℝ) (y : V) ↦
      (J w.2 y).toLinearMap.toContinuousLinearMap) :=
    hJ.comp (contDiff_fst.snd.prodMk contDiff_snd)
  have hKt : ContDiff ℝ 2 (uncurry fun (w : ℝ × ℝ) ↦ H w.2) :=
    hH.comp (contDiff_fst.snd.prodMk contDiff_snd)
  refine hpert (hξ.of_le one_le_two) (hst hξ hper hab ha hb) ?_ ?_
  · rintro ⟨s, t⟩ ⟨hs, -⟩
    exact (ω.continuousAt_floerLinearization hJ' contDiff_const hKt ((hI hs).2 t)
      (hξ.of_le one_le_two).contDiffAt).continuousWithinAt
  · rintro ⟨s, t⟩ ⟨hs, ht⟩
    exact (hI hs).1 t ht ξ

end SymplecticForm

end TauCeti
