/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Continuation
public import TauCeti.Geometry.Symplectic.Floer.Manifold
public import TauCeti.Geometry.Symplectic.Hamiltonian.Action
public import TauCeti.Geometry.Symplectic.Hamiltonian.ContractibleAction.Basic
public import TauCeti.Geometry.Symplectic.Hamiltonian.ContractibleAction.Capped
import TauCeti.Analysis.Calculus.FDeriv.Prod
import TauCeti.MeasureTheory.Integral.Rectangle

/-!
# The energy of Floer cylinders in a manifold and the action of their loops

Let `ω` be a nondegenerate two-form on a finite-dimensional manifold `M` and `H : ℝ → M → ℝ` a
`C¹` time-dependent Hamiltonian. A Floer cylinder for `H` is a map `u : ℝ × ℝ → M`, `1`-periodic
in `t`, solving `∂_s u + J (∂_t u - X_{H_t}(u)) = 0`, with the convention `ι_{X_H} ω = dH`. It is
the inhomogeneous Floer equation for the **cylindrical perturbation** `K = H_t dt`, whose `ds`
component vanishes and whose `dt` component does not depend on `s`; the curvature of such a
perturbation vanishes (`TauCeti.SmoothTwoForm.hamiltonianCurvature_cylindrical`).

The energy identity for manifold targets
(`TauCeti.SmoothTwoForm.IsNondegenerate.integral_floerEnergyDensity`) then says that the Floer
energy of a `C¹` map over `[a, b] × [0, 1]` is its symplectic area plus the Hamiltonian terms of
its two boundary loops `γ_a = u(a, ·)` and `γ_b = u(b, ·)`:

`E(u) = ∫ u^* ω + ∫₀¹ H(t, γ_b(t)) dt - ∫₀¹ H(t, γ_a(t)) dt`

(`TauCeti.SmoothTwoForm.IsNondegenerate.integral_floerEnergyDensity_cylindrical`). This file
rewrites the right-hand side as a difference of actions of the two loops, in five settings.

* For an arbitrary nondegenerate form, such as the symplectic form of a closed monotone
  manifold, and a `C¹` map `v` with `v (0, ·) = γ_b`, the energy is
  `A_H(γ_a, w # v) - A_H(γ_b, v)` for the action `A_H(γ, u) = ∫ u^* ω - ∫₀¹ H(t, γ(t)) dt` of
  `γ` measured against `u` (`TauCeti.cylinderAction`), where `w` is `u` on `[a, b] × ℝ` rescaled
  to `[0, 1] × ℝ`
  (`SmoothTwoForm.IsNondegenerate.integral_floerEnergyDensity_eq_cylinderAction_sub`). When `v`
  is a cap of `γ_b`, `w # v` is a cap of `γ_a`, and the energy is the drop of the capped action.
* For an arbitrary form, such as the symplectic form of a closed symplectic manifold, the actions
  depend on caps. For a disc `D` bounding `γ_a`, the map `u` glued to `D` is a disc `D ⋆ u` bounding
  `γ_b`, and the energy is `A_H(γ_b, D ⋆ u) - A_H(γ_a, D)` for the capped action
  `A_H(γ, D) = ∫ D^* ω + ∫₀¹ H(t, γ(t)) dt` (`TauCeti.cappedLoopAction`)
  (`SmoothTwoForm.IsNondegenerate.integral_floerEnergyDensity_eq_cappedLoopAction_sub`). With
  reference discs `D_a` of `γ_a` and `D_b` of `γ_b` chosen independently, the energy is
  `A_H(γ_b, D_b) - A_H(γ_a, D_a) + ω(A)` for the sphere `A = D_a ⋆ u ⋆ D_b⁻¹`, the class of the
  cylinder relative to its reference discs
  (`SmoothTwoForm.IsNondegenerate.integral_floerEnergyDensity_eq_cappedLoopAction_sub_add`).
* For a weakly exact form (`TauCeti.IsWeaklyExact`, the area half of symplectic asphericity) and
  a `C²` cylinder whose loop `γ_b` bounds a cap, the energy is `A_H(γ_a) - A_H(γ_b)` for the
  action `A_H(γ) = ∫ v^* ω - ∫₀¹ H(t, γ(t)) dt` of contractible loops
  (`TauCeti.contractibleLoopAction`), the cap `v` running from `γ` to its centre
  (`SmoothTwoForm.IsNondegenerate.integral_floerEnergyDensity_eq_contractibleLoopAction_sub`).
* For an exact form `ω = dα`, such as the form of a Liouville domain, no cap is needed: for every
  `C²` cylinder the energy is `A_H(γ_a) - A_H(γ_b)` for the action
  `A_H(γ) = -∫_γ α - ∫₀¹ H(t, γ(t)) dt` of arbitrary loops
  (`TauCeti.SmoothTwoForm.IsNondegenerate.integral_floerEnergyDensity_eq_sub_of_mextDeriv_eq`).
* For a form vanishing on tori (`TauCeti.VanishesOnTori`, the area half of symplectic
  atoroidality) and a smooth map `u` whose loop `γ_b` is joined to a reference loop `γ₀` by a
  smooth cylinder, the energy is `𝒜_H(γ_a) - 𝒜_H(γ_b)` for the action
  `𝒜_H(γ) = ∫ Γ^* ω - ∫₀¹ H(t, γ(t)) dt` relative to `γ₀`
  (`TauCeti.SmoothTwoForm.referenceAction`), the cylinder `Γ` running from `γ` to `γ₀`
  (`TauCeti.SmoothTwoForm.IsNondegenerate.integral_floerEnergyDensity_eq_referenceAction_sub`).
  Choosing one reference loop in each free homotopy class, this is the energy identity on the
  whole free loop space, not only on contractible loops.

For a solution of the Floer equation and almost complex structures tamed by `ω`, the energy
density is nonnegative
(`TauCeti.SmoothTwoForm.IsNondegenerate.floerEnergyDensity_zero_left_nonneg`), so the capped
action decreases along a Floer cylinder when the caps are glued along it
(`TauCeti.SmoothTwoForm.IsNondegenerate.cylinderAction_le_cylinderAction`), for a weakly exact
form the contractible action of the loops decreases
(`TauCeti.SmoothTwoForm.IsNondegenerate.contractibleLoopAction_le_contractibleLoopAction`), and
for a form vanishing on tori so does the action relative to a reference loop
(`TauCeti.SmoothTwoForm.IsNondegenerate.referenceAction_le_referenceAction`). In the opposite
convention of `TauCeti.cappedLoopAction`, the capped action increases along a Floer cylinder when
the disc is transported along it
(`TauCeti.SmoothTwoForm.IsNondegenerate.cappedLoopAction_le_cappedLoopAction`).
This monotonicity underlies the action filtration of the Floer complex.

**Continuation cylinders.** For an `s`-dependent family of Hamiltonians `G_z`, `z = (s, t)`, the
perturbation `K = G_z dt` has curvature `∂_s G`, and the energy picks up the integral of
`-∂_s G` along `u`
(`TauCeti.SmoothTwoForm.IsNondegenerate.integral_floerEnergyDensity_zero_left`). For a weakly
exact form,

`E(u) = A_{G(a, ·)}(γ_a) - A_{G(b, ·)}(γ_b) - ∫∫ (∂_s G)(s, t, u(s, t))`

(`IsNondegenerate.integral_floerEnergyDensity_eq_contractibleLoopAction_sub_sub_integral`), so
along a solution the action at `s = b` is at most the action at `s = a` minus the integral of
`∂_s G`. Hence:

* **monotone homotopies preserve the action filtration**: if every `s ↦ G_{(s, t)}(x)` is
  monotone, the action decreases along the cylinder
  (`SmoothTwoForm.IsNondegenerate.contractibleLoopAction_le_contractibleLoopAction_of_monotone`);
* **general homotopies shift it by at most a Hofer-type bound**: for the continuation homotopy
  `G = H₀ + β(s) (H₁ - H₀)` (`TauCeti.Floer.continuationHomotopy`) and a cylinder over
  `[a, b] × [0, 1]` with `a ≤ 0` and `1 ≤ b`, if `H₀ - H₁ ≤ h` for an integrable `h` on `[0, 1]`,
  then `A_{H₁}(γ_b) ≤ A_{H₀}(γ_a) + ∫₀¹ h`, whatever the length of the cylinder
  (`IsNondegenerate.contractibleLoopAction_le_contractibleLoopAction_add_of_continuationHomotopy`).
  When `h(t) = sup_x (H₀ - H₁)(t, x)` is finite and integrable on `[0, 1]`, for instance on a
  compact manifold, this is the shift `∫₀¹ sup_x (H₀ - H₁) dt` of the filtration by continuation
  maps.

These are the manifold-target, capped-action versions of the estimates of
`TauCeti.Geometry.Symplectic.Floer.Continuation` for a symplectic vector space. The curvature
`∂_s G(z, u z)` along a `C¹` map is continuous, as a partial derivative of the `C¹` map
`(z, y) ↦ G z (u y)` on `ℝ² × ℝ²`, so no integrability hypothesis is needed. The existence,
compactness and counting of continuation cylinders are not treated here.

## Main results

* `TauCeti.SmoothTwoForm.IsNondegenerate.integral_floerEnergyDensity_zero_left`: the energy of a
  map over `[a, b] × [0, 1]` for a perturbation `K = G_z dt`.
* `TauCeti.SmoothTwoForm.IsNondegenerate.integral_floerEnergyDensity_cylindrical`: the energy of a
  map over `[a, b] × [0, 1]` for a cylindrical perturbation.
* `SmoothTwoForm.IsNondegenerate.integral_floerEnergyDensity_eq_cylinderAction_sub`: the energy
  of a cylinder is the drop of the capped action, for any nondegenerate form.
* `TauCeti.SmoothTwoForm.IsNondegenerate.cylinderAction_le_cylinderAction`: the capped action
  decreases along Floer cylinders.
* `IsNondegenerate.integral_floerEnergyDensity_eq_contractibleLoopAction_sub_sub_integral`,
  `SmoothTwoForm.IsNondegenerate.integral_floerEnergyDensity_eq_contractibleLoopAction_sub`: for a
  weakly exact form, the energy of a cylinder is the drop of the contractible action, corrected by
  the curvature for an `s`-dependent perturbation.
* `SmoothTwoForm.IsNondegenerate.integral_floerEnergyDensity_eq_cappedLoopAction_sub`: the energy
  of a cylinder is the increase of the capped action, with the disc transported along it.
* `SmoothTwoForm.IsNondegenerate.integral_floerEnergyDensity_eq_cappedLoopAction_sub_add`: the
  energy of a cylinder with reference discs at both ends.
* `TauCeti.SmoothTwoForm.IsNondegenerate.integral_floerEnergyDensity_eq_sub_of_mextDeriv_eq`: for
  an exact form, the energy of a cylinder is the drop of the action of its loops.
* `TauCeti.SmoothTwoForm.IsNondegenerate.contractibleLoopAction_le_contractibleLoopAction`: the
  contractible action decreases along Floer cylinders.
* `TauCeti.SmoothTwoForm.IsNondegenerate.cappedLoopAction_le_cappedLoopAction`: the capped action
  increases along Floer cylinders.
* `TauCeti.SmoothTwoForm.IsNondegenerate.integral_floerEnergyDensity_eq_referenceAction_sub`: for a
  form vanishing on tori, the energy of a cylinder is the drop of the action relative to a
  reference loop.
* `TauCeti.SmoothTwoForm.IsNondegenerate.referenceAction_le_referenceAction`: the action relative
  to a reference loop decreases along Floer cylinders.
* `SmoothTwoForm.IsNondegenerate.contractibleLoopAction_le_contractibleLoopAction_sub_integral`,
  `SmoothTwoForm.IsNondegenerate.contractibleLoopAction_le_contractibleLoopAction_of_monotone`: the
  action estimate along a Floer cylinder for an `s`-dependent perturbation, and its monotone case.
* `IsNondegenerate.contractibleLoopAction_le_contractibleLoopAction_add_of_linearHomotopy`,
  `IsNondegenerate.contractibleLoopAction_le_contractibleLoopAction_add_of_continuationHomotopy`:
  the action shift along cylinders of a linear homotopy and of the continuation homotopy.

## References

* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), Lecture 1 (the energy identity for Floer cylinders, with the sign
  conventions used here).
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS, 2012,
  Section 8.1 and the chapter on Floer homology.
* H. Hofer and D. A. Salamon, *Floer homology and Novikov rings*, in *The Floer memorial
  volume*, Progr. Math. 133 (1995), 483–524, on the energy of Floer cylinders between capped
  orbits.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §3.2 and Corollaries 3.24 and 3.25.
-/

public noncomputable section

open Set MeasureTheory Function Real
open scoped Manifold Interval

namespace TauCeti.Floer

variable {E HM M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace HM]
  {I : ModelWithCorners ℝ E HM} [TopologicalSpace M] [ChartedSpace HM M]

/-- The cylindrical family `(s, t) ↦ H_t` of a `Cⁿ` time-dependent Hamiltonian on a manifold,
independent of `s`, is a `Cⁿ` family of Hamiltonians. -/
theorem contMDiff_uncurry_comp_snd {n : ℕ∞} {H : ℝ → M → ℝ}
    (hH : ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) n (uncurry H)) :
    ContMDiff (𝓘(ℝ, ℝ × ℝ).prod I) 𝓘(ℝ) n (uncurry fun w : ℝ × ℝ ↦ H w.2) :=
  hH.comp ((contDiff_snd.contMDiff.comp contMDiff_fst).prodMk contMDiff_snd)

/-- The linear homotopy `H₀ + β(s) (H₁ - H₀)` of two `Cⁿ` time-dependent Hamiltonians on a manifold
with a `Cⁿ` profile `β` is a `Cⁿ` family of Hamiltonians. -/
theorem contMDiff_uncurry_linearHomotopy {n : ℕ∞} {H₀ H₁ : ℝ → M → ℝ} {β : ℝ → ℝ}
    (hβ : ContDiff ℝ n β) (hH₀ : ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) n (uncurry H₀))
    (hH₁ : ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) n (uncurry H₁)) :
    ContMDiff (𝓘(ℝ, ℝ × ℝ).prod I) 𝓘(ℝ) n (uncurry (linearHomotopy β H₀ H₁)) := by
  have hs : ContMDiff (𝓘(ℝ, ℝ × ℝ).prod I) 𝓘(ℝ) n fun p : (ℝ × ℝ) × M ↦ β p.1.1 :=
    (hβ.comp contDiff_fst).contMDiff.comp contMDiff_fst
  exact ((contMDiff_uncurry_comp_snd hH₀).add (hs.smul ((contMDiff_uncurry_comp_snd hH₁).sub
    (contMDiff_uncurry_comp_snd hH₀)))).congr fun p ↦ linearHomotopy_def β p.1 p.2

end TauCeti.Floer

namespace TauCeti.SmoothTwoForm

variable {E HM M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace HM]
  {I : ModelWithCorners ℝ E HM} [TopologicalSpace M] [ChartedSpace HM M]
  [IsManifold I (⊤ : ℕ∞) M]

variable {ω : SmoothTwoForm I M} {H : ℝ → M → ℝ} {G : ℝ × ℝ → M → ℝ} {u : ℝ × ℝ → M}

/-! ### The energy identity for perturbations without `ds` component -/

section Energy

variable [FiniteDimensional ℝ E]

/-- **The energy identity for a perturbation without `ds` component.** Let `G_z`, `z = (s, t)`, be
a `C¹` family of Hamiltonians and `u` a `C¹` map, for a nondegenerate two-form on a
finite-dimensional manifold. For the perturbation `K = G_z dt`, the Floer energy of `u` over
`[a, b] × [0, 1]` is its symplectic area over the rectangle, plus the Hamiltonian term of the loop
at `s = b` for `G(b, ·)`, minus that of the loop at `s = a` for `G(a, ·)`, minus the integral of the
curvature `∂_s G` along `u`. Neither periodicity of `u` in `t` nor closedness of the form is
needed. -/
theorem IsNondegenerate.integral_floerEnergyDensity_zero_left (hω : ω.IsNondegenerate)
    (hG : ContMDiff (𝓘(ℝ, ℝ × ℝ).prod I) 𝓘(ℝ) 1 (uncurry G)) (hu : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 1 u)
    {a b : ℝ} (hab : a ≤ b) :
    ∫ z in Icc a b ×ˢ Icc 0 1, ω.floerEnergyDensity (fun _ _ ↦ 0) G u z =
      rectangleIntegral ω.1 u (a, 0) (b, 1) + (∫ t in 0..1, G (b, t) (u (b, t))) -
        (∫ t in 0..1, G (a, t) (u (a, t))) -
        ∫ z in Icc a b ×ˢ Icc 0 1, fderiv ℝ (fun w ↦ G w (u z)) z stdComplexLineReal := by
  have hR : Icc a b ×ˢ Icc (0 : ℝ) 1 = Icc (a, 0) (b, 1) := Icc_prod_Icc _ _ _ _
  have hab' : ((a, 0) : ℝ × ℝ) ≤ (b, 1) := Prod.mk_le_mk.2 ⟨hab, zero_le_one⟩
  have hω₀ : IsSmoothForm I 0 ω.1 := ω.isSmoothForm.of_le (by simp)
  -- The symplectic area density is the integrand of the rectangle integral.
  let area : ℝ × ℝ → ℝ := fun z ↦ SmoothBundleForm.eval₂ ω (u z)
    (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag)
  have harea_cont : Continuous area :=
    (hω₀.continuous_apply_mfderiv hu (1, 0) (0, 1)).congr fun z ↦ by
      simp [area, SmoothBundleForm.eval₂_apply, stdComplexLineReal_eq, stdComplexLineImag_eq]
  -- The derivative term `d(K(u))` is continuous, since `K_t(u)` is `C¹`.
  have hf : ContDiff ℝ 1 fun w ↦ G w (u w) :=
    contMDiff_iff_contDiff.mp (hG.comp (contMDiff_id.prodMk hu))
  have hdK : Continuous fun z ↦ fderiv ℝ (fun w ↦ G w (u w)) z stdComplexLineReal :=
    (hf.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hcurv : Continuous fun z ↦ fderiv ℝ (fun w ↦ G w (u z)) z stdComplexLineReal :=
    (continuous_fderiv_of_contMDiff hu hG).clm_apply continuous_const
  -- Pointwise, the energy density is the area density plus `d(K(u))` minus the curvature.
  have hpt (z : ℝ × ℝ) : ω.floerEnergyDensity (fun _ _ ↦ 0) G u z =
      area z + fderiv ℝ (fun w ↦ G w (u w)) z stdComplexLineReal -
        fderiv ℝ (fun w ↦ G w (u z)) z stdComplexLineReal := by
    rw [hω.floerEnergyDensity_eq ((hu z).mdifferentiableAt one_ne_zero)
      (contMDiffAt_const.mdifferentiableAt one_ne_zero)
      ((hG _).mdifferentiableAt one_ne_zero), hamiltonianCurvature_zero_left]
    simp [area]
  have hE : Continuous (ω.floerEnergyDensity (fun _ _ ↦ 0) G u) :=
    ((harea_cont.add hdK).sub hcurv).congr fun z ↦ (hpt z).symm
  have h := hω.integral_floerEnergyDensity (Ks := fun _ _ ↦ 0) (Kt := G) isOpen_univ
    hu.contMDiffOn contMDiffOn_const hG.contMDiffOn hab' (subset_univ _)
    (hE.continuousOn.integrableOn_compact isCompact_Icc)
    (by simpa only [hamiltonianCurvature_zero_left] using
      hcurv.continuousOn.integrableOn_compact isCompact_Icc)
  simp only [hamiltonianCurvature_zero_left, intervalIntegral.integral_zero] at h
  rw [hR, h, ← hω₀.setIntegral_eq_rectangleIntegral hu hab']
  simp only [SmoothBundleForm.eval₂_apply, stdComplexLineReal_eq, stdComplexLineImag_eq]
  ring

/-- **The energy identity for a cylindrical perturbation.** Let `H` be a `C¹` time-dependent
Hamiltonian and `u` a `C¹` map, for a nondegenerate two-form on a finite-dimensional manifold.
For the cylindrical perturbation `K = H_t dt`, the Floer energy of `u` over `[a, b] × [0, 1]` is
its symplectic area over the rectangle, plus the Hamiltonian term of the loop at `s = b`, minus
that of the loop at `s = a`. Neither periodicity of `u` in `t` nor closedness of the form is
needed. -/
theorem IsNondegenerate.integral_floerEnergyDensity_cylindrical (hω : ω.IsNondegenerate)
    (hH : ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) 1 (uncurry H)) (hu : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 1 u)
    {a b : ℝ} (hab : a ≤ b) :
    ∫ z in Icc a b ×ˢ Icc 0 1, ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) u z =
      rectangleIntegral ω.1 u (a, 0) (b, 1) + (∫ t in 0..1, H t (u (b, t))) -
        ∫ t in 0..1, H t (u (a, t)) := by
  rw [hω.integral_floerEnergyDensity_zero_left (Floer.contMDiff_uncurry_comp_snd hH) hu hab]
  simp [fderiv_cylindrical_apply_stdComplexLineReal]

/-- **The energy of a Floer cylinder is the drop of the capped action.** Let `ω` be a
nondegenerate two-form on a finite-dimensional manifold, `H` a `C¹` time-dependent Hamiltonian
and `u` a `C¹` map. Let `v` be an arbitrary `C¹` map with `v (0, ·) = γ_b`, where
`γ_b = u(b, ·)`. Rescaling `[a, b]` to `[0, 1]` makes `u` a map `w` from `γ_a = u(a, ·)` to
`γ_b`, which is glued to `v` as `w # v` (`TauCeti.rectangleTrans`). The Floer energy of `u` over
`[a, b] × [0, 1]` for the cylindrical perturbation `K = H_t dt` is
`A_H(γ_a, w # v) - A_H(γ_b, v)`, for the action `TauCeti.cylinderAction` of a loop measured
against a map. When `v` is a cap of `γ_b`, `w # v` is a cap of `γ_a`, and this is the energy
identity for capped loops: the energy is the drop of the capped action. Neither weak exactness nor
closedness of `ω` is needed, and neither `u` nor `v` needs to be periodic. -/
theorem IsNondegenerate.integral_floerEnergyDensity_eq_cylinderAction_sub
    (hω : ω.IsNondegenerate) (hH : ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) 1 (uncurry H))
    (hu : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 1 u) {a b : ℝ} (hab : a ≤ b) {v : ℝ × ℝ → M}
    (hv : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 1 v) (hv₀ : ∀ t, v (0, t) = u (b, t)) :
    ∫ z in Icc a b ×ˢ Icc 0 1, ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) u z =
      cylinderAction ω.1 H (rectangleTrans (u ∘ Prod.map (fun s ↦ a + (b - a) * s) id) v) -
        cylinderAction ω.1 H v := by
  have hω₀ : IsSmoothForm I 0 ω.1 := ω.isSmoothForm.of_le (by simp)
  -- Rescale `[a, b]` to `[0, 1]` to view `u` as a cylinder from `γ_a` to `γ_b`.
  let σ : ℝ → ℝ := fun s ↦ a + (b - a) * s
  have hσ (s : ℝ) : HasDerivAt σ (b - a) s := by
    have h := ((hasDerivAt_id s).const_mul (b - a)).const_add a
    rwa [mul_one] at h
  have hw : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 1 (u ∘ Prod.map σ id) :=
    hu.comp (((contDiff_const.add (contDiff_const.mul contDiff_id)).prodMap contDiff_id).contMDiff)
  have hrect : rectangleIntegral ω.1 (u ∘ Prod.map σ id) (0, 0) (1, 1) =
      rectangleIntegral ω.1 u (a, 0) (b, 1) := by
    rw [rectangleIntegral_comp_prodMap hω₀ hu (fun s _ ↦ hσ s) continuousOn_const]
    simp [σ]
  have h := cylinderAction_rectangleTrans_sub hω₀ H hw hv fun t ↦ by simp [σ, hv₀]
  simp only [Function.comp_apply, Prod.map_apply, id_eq, σ, hrect] at h
  rw [hω.integral_floerEnergyDensity_cylindrical hH hu hab, h]
  simp only [mul_zero, add_zero, mul_one, add_sub_cancel]
  ring

/-- **The energy of a Floer cylinder for an `s`-dependent perturbation.** Let `ω` be a
nondegenerate weakly exact two-form on a finite-dimensional manifold, `G_z`, `z = (s, t)`, a `C¹`
family of Hamiltonians, and `u` a `C²` map, `1`-periodic in its second coordinate. If the loop
`γ_b = u(b, ·)` bounds a cap, the Floer energy of `u` over `[a, b] × [0, 1]` for the perturbation
`K = G_z dt` is `A_{G(a, ·)}(γ_a) - A_{G(b, ·)}(γ_b)` minus the integral of `∂_s G` along `u`,
where `γ_a = u(a, ·)` and `A` is the action `TauCeti.contractibleLoopAction` of contractible
loops. The loop `γ_a` is capped by gluing `u` to the cap of `γ_b`. -/
theorem IsNondegenerate.integral_floerEnergyDensity_eq_contractibleLoopAction_sub_sub_integral
    (hω : ω.IsNondegenerate) (hωe : IsWeaklyExact ω.1)
    (hG : ContMDiff (𝓘(ℝ, ℝ × ℝ).prod I) 𝓘(ℝ) 1 (uncurry G)) (hu : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 2 u)
    (hper : ∀ z : ℝ × ℝ, u (z.1, z.2 + 1) = u z) {a b : ℝ} (hab : a ≤ b) {v : ℝ × ℝ → M}
    (hv : IsCap I v fun t ↦ u (b, t)) :
    ∫ z in Icc a b ×ˢ Icc 0 1, ω.floerEnergyDensity (fun _ _ ↦ 0) G u z =
      contractibleLoopAction ω.1 (fun t ↦ G (a, t)) (fun t ↦ u (a, t)) -
        contractibleLoopAction ω.1 (fun t ↦ G (b, t)) (fun t ↦ u (b, t)) -
        ∫ z in Icc a b ×ˢ Icc 0 1, fderiv ℝ (fun w ↦ G w (u z)) z stdComplexLineReal := by
  have hω₀ : IsSmoothForm I 0 ω.1 := ω.isSmoothForm.of_le (by simp)
  -- Rescale `[a, b]` to `[0, 1]` to view `u` as a cylinder from `γ_a` to `γ_b`.
  let σ : ℝ → ℝ := fun s ↦ a + (b - a) * s
  have hσ (s : ℝ) : HasDerivAt σ (b - a) s := by
    have h := ((hasDerivAt_id s).const_mul (b - a)).const_add a
    rwa [mul_one] at h
  have hw : IsLoopCylinder I (u ∘ Prod.map σ id) (fun t ↦ u (a, t)) fun t ↦ u (b, t) :=
    { contMDiff := hu.comp
        (((contDiff_const.add (contDiff_const.mul contDiff_id)).prodMap contDiff_id).contMDiff)
      apply_add_one := fun z ↦ hper (σ z.1, z.2)
      apply_zero := fun t ↦ by simp [σ]
      apply_one := fun t ↦ by simp [σ] }
  have hrect : rectangleIntegral ω.1 (u ∘ Prod.map σ id) (0, 0) (1, 1) =
      rectangleIntegral ω.1 u (a, 0) (b, 1) := by
    rw [rectangleIntegral_comp_prodMap hω₀ (hu.of_le one_le_two) (fun s _ ↦ hσ s)
      continuousOn_const]
    simp [σ]
  rw [hω.integral_floerEnergyDensity_zero_left hG (hu.of_le one_le_two) hab,
    contractibleLoopAction_def, contractibleLoopAction_def,
    hωe.capArea_eq_rectangleIntegral_add hω₀ hw hv, hrect]
  ring

/-- **The energy of a Floer cylinder is the increase of the capped action.** Let `ω` be a
nondegenerate two-form on a finite-dimensional manifold, `H` a `C¹` time-dependent Hamiltonian,
and `u` a `C²` map, `1`-periodic in its second coordinate. Let `D` be a disc bounding the loop
`γ_a = u(a, ·)`. Gluing to `D` the cylinder swept by `u` from `γ_a` to `γ_b = u(b, ·)` gives a disc
`D ⋆ u` bounding `γ_b`, and the Floer energy of `u` over `[a, b] × [0, 1]` for the cylindrical
perturbation `K = H_t dt` is `A_H(γ_b, D ⋆ u) - A_H(γ_a, D)`, for the capped action
`TauCeti.cappedLoopAction`. No exactness of `ω` is assumed. -/
theorem IsNondegenerate.integral_floerEnergyDensity_eq_cappedLoopAction_sub
    (hω : ω.IsNondegenerate) (hH : ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) 1 (uncurry H))
    (hu : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 2 u) (hper : ∀ z : ℝ × ℝ, u (z.1, z.2 + 1) = u z) {a b : ℝ}
    (hab : a ≤ b) {D : ℝ × ℝ → M} {x : M}
    (hD : IsLoopCylinder I D (fun _ ↦ x) fun t ↦ u (a, t)) :
    ∫ z in Icc a b ×ˢ Icc 0 1, ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) u z =
      cappedLoopAction ω.1 H (fun t ↦ u (b, t))
          (rectangleTrans D (u ∘ Prod.map (fun σ ↦ a + (b - a) * σ) id)) -
        cappedLoopAction ω.1 H (fun t ↦ u (a, t)) D := by
  rw [hω.integral_floerEnergyDensity_cylindrical hH (hu.of_le one_le_two) hab,
    cappedLoopAction_rectangleTrans_sub_cappedLoopAction (ω.isSmoothForm.of_le (by simp)) H hD
      (isLoopCylinder_comp_prodMap hu hper a b),
    rectangleIntegral_comp_prodMap_affine (ω.isSmoothForm.of_le (by simp)) (hu.of_le one_le_two) a b
      0 1]

/-- **The energy of a Floer cylinder between reference discs.** Under the hypotheses of
`TauCeti.SmoothTwoForm.IsNondegenerate.integral_floerEnergyDensity_eq_cappedLoopAction_sub`, let
`D_a` and `D_b` be discs bounding the loops `γ_a = u(a, ·)` and `γ_b = u(b, ·)`, chosen
independently. Gluing `D_a`, the cylinder swept by `u`, and `D_b` run backwards gives a sphere
`A = D_a ⋆ u ⋆ D_b⁻¹` (`TauCeti.IsLoopCylinder.trans`, `TauCeti.IsLoopCylinder.symm`), the class
of the cylinder relative to the reference discs, and the Floer energy of `u` over
`[a, b] × [0, 1]` is `A_H(γ_b, D_b) - A_H(γ_a, D_a) + ω(A)`. -/
theorem IsNondegenerate.integral_floerEnergyDensity_eq_cappedLoopAction_sub_add
    (hω : ω.IsNondegenerate) (hH : ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) 1 (uncurry H))
    (hu : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 2 u) (hper : ∀ z : ℝ × ℝ, u (z.1, z.2 + 1) = u z) {a b : ℝ}
    (hab : a ≤ b) {Da Db : ℝ × ℝ → M} {xa xb : M}
    (hDa : IsLoopCylinder I Da (fun _ ↦ xa) fun t ↦ u (a, t))
    (hDb : IsLoopCylinder I Db (fun _ ↦ xb) fun t ↦ u (b, t)) :
    ∫ z in Icc a b ×ˢ Icc 0 1, ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) u z =
      cappedLoopAction ω.1 H (fun t ↦ u (b, t)) Db -
          cappedLoopAction ω.1 H (fun t ↦ u (a, t)) Da +
        rectangleIntegral ω.1
          (rectangleTrans (rectangleTrans Da (u ∘ Prod.map (fun σ ↦ a + (b - a) * σ) id))
            (Db ∘ Prod.map (fun s ↦ 1 - s) id)) (0, 0) (1, 1) := by
  rw [hω.integral_floerEnergyDensity_eq_cappedLoopAction_sub hH hu hper hab hDa,
    ← cappedLoopAction_sub_cappedLoopAction (ω.isSmoothForm.of_le (by simp)) H hDb
      (hDa.trans (isLoopCylinder_comp_prodMap hu hper a b))]
  ring

/-- **The capped action increases along Floer cylinders.** Under the hypotheses of
`TauCeti.SmoothTwoForm.IsNondegenerate.integral_floerEnergyDensity_eq_cappedLoopAction_sub`, if
`u` solves the Floer equation `∂_s u + J (∂_t u - X_{H_t}(u)) = 0` on `[a, b] × [0, 1]` for almost
complex structures `J z` on `T_{u z} M` tamed by `ω`, then the capped action of `(γ_a, D)` is at
most that of `γ_b` capped by the transported disc `D ⋆ u`. -/
theorem IsNondegenerate.cappedLoopAction_le_cappedLoopAction (hω : ω.IsNondegenerate)
    (hH : ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) 1 (uncurry H)) (hu : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 2 u)
    (hper : ∀ z : ℝ × ℝ, u (z.1, z.2 + 1) = u z) {a b : ℝ} (hab : a ≤ b) {D : ℝ × ℝ → M} {x : M}
    (hD : IsLoopCylinder I D (fun _ ↦ x) fun t ↦ u (a, t))
    (J : ∀ z, AlmostComplexStructure (TangentSpace I (u z)))
    (hJ : ∀ z ∈ Icc a b ×ˢ Icc 0 1, (hω.symplecticFormAt (u z)).Tames (J z))
    (hfloer : ∀ z ∈ Icc a b ×ˢ Icc 0 1, mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal +
      J z (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag -
        ω.hamiltonianVectorField (H z.2) (u z)) = 0) :
    cappedLoopAction ω.1 H (fun t ↦ u (a, t)) D ≤
      cappedLoopAction ω.1 H (fun t ↦ u (b, t))
        (rectangleTrans D (u ∘ Prod.map (fun σ ↦ a + (b - a) * σ) id)) := by
  have h := hω.integral_floerEnergyDensity_eq_cappedLoopAction_sub hH hu hper hab hD
  have hnonneg := setIntegral_nonneg (μ := volume) (measurableSet_Icc.prod measurableSet_Icc)
    fun z hz ↦ hω.floerEnergyDensity_zero_left_nonneg (Kt := fun w ↦ H w.2) (hJ z hz)
      (hfloer z hz)
  linarith

/-- **The energy of a Floer cylinder is the drop of the contractible action.** Let `ω` be a
nondegenerate weakly exact two-form on a finite-dimensional manifold, `H` a `C¹` time-dependent
Hamiltonian, and `u` a `C²` map, `1`-periodic in its second coordinate. If the loop
`γ_b = u(b, ·)` bounds a cap, the Floer energy of `u` over `[a, b] × [0, 1]` for the cylindrical
perturbation `K = H_t dt` is `A_H(γ_a) - A_H(γ_b)`, where `γ_a = u(a, ·)` and `A_H` is the action
`TauCeti.contractibleLoopAction` of contractible loops. The loop `γ_a` is capped by gluing `u` to
the cap of `γ_b`, so both actions are computed with genuine caps. -/
theorem IsNondegenerate.integral_floerEnergyDensity_eq_contractibleLoopAction_sub
    (hω : ω.IsNondegenerate) (hωe : IsWeaklyExact ω.1)
    (hH : ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) 1 (uncurry H)) (hu : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 2 u)
    (hper : ∀ z : ℝ × ℝ, u (z.1, z.2 + 1) = u z) {a b : ℝ} (hab : a ≤ b) {v : ℝ × ℝ → M}
    (hv : IsCap I v fun t ↦ u (b, t)) :
    ∫ z in Icc a b ×ˢ Icc 0 1, ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) u z =
      contractibleLoopAction ω.1 H (fun t ↦ u (a, t)) -
        contractibleLoopAction ω.1 H (fun t ↦ u (b, t)) := by
  have hω₀ : IsSmoothForm I 0 ω.1 := ω.isSmoothForm.of_le (by simp)
  obtain ⟨x, hv'⟩ := isCap_iff.1 hv
  rw [hω.integral_floerEnergyDensity_eq_cylinderAction_sub hH (hu.of_le one_le_two) hab
      (hv'.contMDiff.of_le one_le_two) hv'.apply_zero,
    hωe.contractibleLoopAction_eq hω₀ H ((isLoopCylinder_comp_prodMap hu hper a b).trans hv').isCap,
    hωe.contractibleLoopAction_eq hω₀ H hv'.isCap]

/-- **The capped action decreases along Floer cylinders.** Under the hypotheses of
`TauCeti.SmoothTwoForm.IsNondegenerate.integral_floerEnergyDensity_eq_cylinderAction_sub`, if
`u` solves the Floer equation `∂_s u + J (∂_t u - X_{H_t}(u)) = 0` on `[a, b] × [0, 1]` for
almost complex structures `J z` on `T_{u z} M` tamed by `ω`, then the action of the loop at
`s = b` measured against the arbitrary `C¹` map `v` is at most the action of the loop at `s = a`
measured against the glued map. When `v` is a cap of the loop at `s = b`, the glued map is a cap
of the loop at `s = a`, and this says that the capped action decreases. -/
theorem IsNondegenerate.cylinderAction_le_cylinderAction
    (hω : ω.IsNondegenerate) (hH : ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) 1 (uncurry H))
    (hu : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 1 u) {a b : ℝ} (hab : a ≤ b) {v : ℝ × ℝ → M}
    (hv : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 1 v) (hv₀ : ∀ t, v (0, t) = u (b, t))
    (J : ∀ z, AlmostComplexStructure (TangentSpace I (u z)))
    (hJ : ∀ z ∈ Icc a b ×ˢ Icc 0 1, (hω.symplecticFormAt (u z)).Tames (J z))
    (hfloer : ∀ z ∈ Icc a b ×ˢ Icc 0 1, mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal +
      J z (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag -
        ω.hamiltonianVectorField (H z.2) (u z)) = 0) :
    cylinderAction ω.1 H v ≤
      cylinderAction ω.1 H (rectangleTrans (u ∘ Prod.map (fun s ↦ a + (b - a) * s) id) v) := by
  have h := hω.integral_floerEnergyDensity_eq_cylinderAction_sub hH hu hab hv hv₀
  have hnonneg := setIntegral_nonneg (μ := volume) (measurableSet_Icc.prod measurableSet_Icc)
    fun z hz ↦ hω.floerEnergyDensity_zero_left_nonneg (Kt := fun w ↦ H w.2) (hJ z hz)
      (hfloer z hz)
  linarith

/-- **The energy of a Floer cylinder for an exact form.** Let `ω = dα` be a nondegenerate exact
two-form on a finite-dimensional manifold, `H` a `C¹` time-dependent Hamiltonian, and `u` a `C²`
map, `1`-periodic in its second coordinate. With the action `A_H(γ) = -∫_γ α - ∫₀¹ H(t, γ(t)) dt`
of an arbitrary loop, the Floer energy of `u` over `[a, b] × [0, 1]` for the cylindrical
perturbation `K = H_t dt` is `A_H(γ_a) - A_H(γ_b)`, for the loops `γ_a = u(a, ·)` and
`γ_b = u(b, ·)`. No cap of the loops is needed. -/
theorem IsNondegenerate.integral_floerEnergyDensity_eq_sub_of_mextDeriv_eq
    (hω : ω.IsNondegenerate) {α : SmoothForm I M ℝ 1} (hα : mextDeriv α.1 = ω.1)
    (hH : ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) 1 (uncurry H)) (hu : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 2 u)
    (hper : ∀ z : ℝ × ℝ, u (z.1, z.2 + 1) = u z) {a b : ℝ} (hab : a ≤ b) :
    ∫ z in Icc a b ×ˢ Icc 0 1, ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) u z =
      (-pathIntegral α.1 (fun t ↦ u (a, t)) 0 1 - ∫ t in 0..1, H t (u (a, t))) -
        (-pathIntegral α.1 (fun t ↦ u (b, t)) 0 1 - ∫ t in 0..1, H t (u (b, t))) := by
  -- The two horizontal sides of the rectangle are the same curve, by periodicity.
  have hside : (fun s ↦ u (s, 1)) = fun s ↦ u (s, 0) :=
    funext fun s ↦ by simpa using hper (s, 0)
  rw [hω.integral_floerEnergyDensity_cylindrical hH (hu.of_le one_le_two) hab, ← hα,
    rectangleIntegral_mextDeriv (α.isSmoothForm.of_le (by simp)) hu, hside, sub_self, sub_zero]
  ring

/-- **The contractible action decreases along Floer cylinders.** Under the hypotheses of
`TauCeti.SmoothTwoForm.IsNondegenerate.integral_floerEnergyDensity_eq_contractibleLoopAction_sub`,
if `u` solves the Floer equation `∂_s u + J (∂_t u - X_{H_t}(u)) = 0` on `[a, b] × [0, 1]` for
almost complex structures `J z` on `T_{u z} M` tamed by `ω`, then the action of the loop at
`s = b` is at most that of the loop at `s = a`. -/
theorem IsNondegenerate.contractibleLoopAction_le_contractibleLoopAction
    (hω : ω.IsNondegenerate) (hωe : IsWeaklyExact ω.1)
    (hH : ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) 1 (uncurry H)) (hu : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 2 u)
    (hper : ∀ z : ℝ × ℝ, u (z.1, z.2 + 1) = u z) {a b : ℝ} (hab : a ≤ b) {v : ℝ × ℝ → M}
    (hv : IsCap I v fun t ↦ u (b, t)) (J : ∀ z, AlmostComplexStructure (TangentSpace I (u z)))
    (hJ : ∀ z ∈ Icc a b ×ˢ Icc 0 1, (hω.symplecticFormAt (u z)).Tames (J z))
    (hfloer : ∀ z ∈ Icc a b ×ˢ Icc 0 1, mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal +
      J z (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag -
        ω.hamiltonianVectorField (H z.2) (u z)) = 0) :
    contractibleLoopAction ω.1 H (fun t ↦ u (b, t)) ≤
      contractibleLoopAction ω.1 H (fun t ↦ u (a, t)) := by
  have h := hω.integral_floerEnergyDensity_eq_contractibleLoopAction_sub hωe hH hu hper hab hv
  have hnonneg := setIntegral_nonneg (μ := volume) (measurableSet_Icc.prod measurableSet_Icc)
    fun z hz ↦ hω.floerEnergyDensity_zero_left_nonneg (Kt := fun w ↦ H w.2) (hJ z hz)
      (hfloer z hz)
  linarith

/-! ### The action relative to a reference loop -/

/-- **The energy of a Floer cylinder is the drop of the action relative to a reference loop.**
Let `ω` be a nondegenerate two-form vanishing on tori on a finite-dimensional manifold, `H` a
`C¹` time-dependent Hamiltonian, and `u` a smooth map, `1`-periodic in its second coordinate.
If the loop `γ_b = u(b, ·)` is joined to the reference loop `γ₀` by a smooth cylinder, the Floer
energy of `u` over `[a, b] × [0, 1]` for the cylindrical perturbation `K = H_t dt` is
`𝒜_H(γ_a) - 𝒜_H(γ_b)`, where `γ_a = u(a, ·)` and `𝒜_H` is the action
`TauCeti.SmoothTwoForm.referenceAction` relative to `γ₀`. The loop `γ_a` is joined to `γ₀` by
gluing `u` to the cylinder from `γ_b`, so both actions are computed with genuine cylinders. -/
theorem IsNondegenerate.integral_floerEnergyDensity_eq_referenceAction_sub
    (hω : ω.IsNondegenerate) (hωt : VanishesOnTori ω.1)
    (hH : ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) 1 (uncurry H))
    (hu : ContMDiff 𝓘(ℝ, ℝ × ℝ) I (⊤ : ℕ∞) u) (hper : ∀ z : ℝ × ℝ, u (z.1, z.2 + 1) = u z)
    {a b : ℝ} (hab : a ≤ b) {γ₀ : ℝ → M} {v : ℝ × ℝ → M}
    (hv : IsSmoothCylinder I (fun t ↦ u (b, t)) γ₀ v) :
    ∫ z in Icc a b ×ˢ Icc 0 1, ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) u z =
      ω.referenceAction H γ₀ (fun t ↦ u (a, t)) - ω.referenceAction H γ₀ (fun t ↦ u (b, t)) := by
  have hω₀ : IsSmoothForm I 0 ω.1 := ω.isSmoothForm.of_le (by simp)
  -- Rescale `[a, b]` to `[0, 1]` and glue the result to `v`: a cylinder from `γ_a` to `γ₀`.
  have hc := isSmoothCylinder_comp_prodMap_affine hu hper a b
  have hw := hc.trans hv fun t ↦ by simp [hv.apply_zero]
  rw [hω.integral_floerEnergyDensity_cylindrical hH (hu.of_le (by simp)) hab,
    referenceAction_eq hωt hw, referenceAction_eq hωt hv, cylinderAction_eq_of_isSmoothCylinder hw,
    cylinderAction_eq_of_isSmoothCylinder hv,
    rectangleIntegral_rectangleTrans hω₀ (hc.contMDiff.of_le (by simp))
      (hv.contMDiff.of_le (by simp)) (fun t ↦ by simp [hv.apply_zero]),
    rectangleIntegral_comp_prodMap_affine hω₀ (hu.of_le (by simp)) a b 0 1]
  ring

/-- **The action relative to a reference loop decreases along Floer cylinders.** Under the
hypotheses of
`TauCeti.SmoothTwoForm.IsNondegenerate.integral_floerEnergyDensity_eq_referenceAction_sub`, if
`u` solves the Floer equation `∂_s u + J (∂_t u - X_{H_t}(u)) = 0` on `[a, b] × [0, 1]` for
almost complex structures `J z` on `T_{u z} M` tamed by `ω`, then the action of the loop at
`s = b` relative to `γ₀` is at most that of the loop at `s = a`. -/
theorem IsNondegenerate.referenceAction_le_referenceAction
    (hω : ω.IsNondegenerate) (hωt : VanishesOnTori ω.1)
    (hH : ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) 1 (uncurry H))
    (hu : ContMDiff 𝓘(ℝ, ℝ × ℝ) I (⊤ : ℕ∞) u) (hper : ∀ z : ℝ × ℝ, u (z.1, z.2 + 1) = u z)
    {a b : ℝ} (hab : a ≤ b) {γ₀ : ℝ → M} {v : ℝ × ℝ → M}
    (hv : IsSmoothCylinder I (fun t ↦ u (b, t)) γ₀ v)
    (J : ∀ z, AlmostComplexStructure (TangentSpace I (u z)))
    (hJ : ∀ z ∈ Icc a b ×ˢ Icc 0 1, (hω.symplecticFormAt (u z)).Tames (J z))
    (hfloer : ∀ z ∈ Icc a b ×ˢ Icc 0 1, mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal +
      J z (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag -
        ω.hamiltonianVectorField (H z.2) (u z)) = 0) :
    ω.referenceAction H γ₀ (fun t ↦ u (b, t)) ≤ ω.referenceAction H γ₀ (fun t ↦ u (a, t)) := by
  have h := hω.integral_floerEnergyDensity_eq_referenceAction_sub hωt hH hu hper hab hv
  have hnonneg := setIntegral_nonneg (μ := volume) (measurableSet_Icc.prod measurableSet_Icc)
    fun z hz ↦ hω.floerEnergyDensity_zero_left_nonneg (Kt := fun w ↦ H w.2) (hJ z hz)
      (hfloer z hz)
  linarith

/-! ### Continuation cylinders and the action filtration -/

/-- **The action estimate along a Floer cylinder for an `s`-dependent perturbation.** Under the
hypotheses of
`IsNondegenerate.integral_floerEnergyDensity_eq_contractibleLoopAction_sub_sub_integral`, if `u`
solves the Floer equation `∂_s u + J (∂_t u - X_{G_z}(u)) = 0` on `[a, b] × [0, 1]` for almost
complex structures `J z` on `T_{u z} M` tamed by `ω`, then the action of the loop at `s = b`
for `G(b, ·)` is at most that of the loop at `s = a` for `G(a, ·)` minus the integral of `∂_s G`
along `u`. -/
theorem IsNondegenerate.contractibleLoopAction_le_contractibleLoopAction_sub_integral
    (hω : ω.IsNondegenerate) (hωe : IsWeaklyExact ω.1)
    (hG : ContMDiff (𝓘(ℝ, ℝ × ℝ).prod I) 𝓘(ℝ) 1 (uncurry G)) (hu : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 2 u)
    (hper : ∀ z : ℝ × ℝ, u (z.1, z.2 + 1) = u z) {a b : ℝ} (hab : a ≤ b) {v : ℝ × ℝ → M}
    (hv : IsCap I v fun t ↦ u (b, t)) (J : ∀ z, AlmostComplexStructure (TangentSpace I (u z)))
    (hJ : ∀ z ∈ Icc a b ×ˢ Icc 0 1, (hω.symplecticFormAt (u z)).Tames (J z))
    (hfloer : ∀ z ∈ Icc a b ×ˢ Icc 0 1, mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal +
      J z (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag -
        ω.hamiltonianVectorField (G z) (u z)) = 0) :
    contractibleLoopAction ω.1 (fun t ↦ G (b, t)) (fun t ↦ u (b, t)) ≤
      contractibleLoopAction ω.1 (fun t ↦ G (a, t)) (fun t ↦ u (a, t)) -
        ∫ z in Icc a b ×ˢ Icc 0 1, fderiv ℝ (fun w ↦ G w (u z)) z stdComplexLineReal := by
  have h := hω.integral_floerEnergyDensity_eq_contractibleLoopAction_sub_sub_integral hωe hG hu
    hper hab hv
  have hnonneg := setIntegral_nonneg (μ := volume) (measurableSet_Icc.prod measurableSet_Icc)
    fun z hz ↦ hω.floerEnergyDensity_zero_left_nonneg (hJ z hz) (hfloer z hz)
  linarith

/-- **Monotone homotopies preserve the action filtration.** Under the hypotheses of
`SmoothTwoForm.IsNondegenerate.contractibleLoopAction_le_contractibleLoopAction_sub_integral`, if
every `s ↦ G_{(s, t)}(x)` is monotone, then the action of the loop at `s = b` for `G(b, ·)` is at
most that of the loop at `s = a` for `G(a, ·)`. -/
theorem IsNondegenerate.contractibleLoopAction_le_contractibleLoopAction_of_monotone
    (hω : ω.IsNondegenerate) (hωe : IsWeaklyExact ω.1)
    (hG : ContMDiff (𝓘(ℝ, ℝ × ℝ).prod I) 𝓘(ℝ) 1 (uncurry G))
    (hmono : ∀ t x, Monotone fun s ↦ G (s, t) x) (hu : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 2 u)
    (hper : ∀ z : ℝ × ℝ, u (z.1, z.2 + 1) = u z) {a b : ℝ} (hab : a ≤ b) {v : ℝ × ℝ → M}
    (hv : IsCap I v fun t ↦ u (b, t)) (J : ∀ z, AlmostComplexStructure (TangentSpace I (u z)))
    (hJ : ∀ z ∈ Icc a b ×ˢ Icc 0 1, (hω.symplecticFormAt (u z)).Tames (J z))
    (hfloer : ∀ z ∈ Icc a b ×ˢ Icc 0 1, mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal +
      J z (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag -
        ω.hamiltonianVectorField (G z) (u z)) = 0) :
    contractibleLoopAction ω.1 (fun t ↦ G (b, t)) (fun t ↦ u (b, t)) ≤
      contractibleLoopAction ω.1 (fun t ↦ G (a, t)) (fun t ↦ u (a, t)) := by
  have h := hω.contractibleLoopAction_le_contractibleLoopAction_sub_integral hωe hG hu hper hab hv
    J hJ hfloer
  -- `∂_s G` is the derivative of the monotone functions `s ↦ G_{(s, t)}(x)`.
  have hnonneg : 0 ≤ ∫ z in Icc a b ×ˢ Icc 0 1, fderiv ℝ (fun w ↦ G w (u z)) z stdComplexLineReal :=
    setIntegral_nonneg (measurableSet_Icc.prod measurableSet_Icc) fun z _ ↦ by
      have hd : ContDiff ℝ 1 fun w ↦ G w (u z) :=
        contMDiff_iff_contDiff.mp (hG.comp (contMDiff_id.prodMk contMDiff_const))
      rw [stdComplexLineReal_eq, fderiv_apply_mk_one_zero (u := fun w ↦ G w (u z))
        (hd.differentiable one_ne_zero z)]
      exact (hmono z.2 (u z)).deriv_nonneg
  linarith

/-- **The action shift of a linear homotopy.** Let `ω` be a nondegenerate weakly exact two-form on
a finite-dimensional manifold, `H₀` and `H₁` `C¹` time-dependent Hamiltonians, `β` a monotone `C¹`
profile and `G = H₀ + β(s) (H₁ - H₀)` the linear homotopy. Let `u` be a `C²` map, `1`-periodic in
its second coordinate, whose loop at `s = b` bounds a cap, solving the Floer equation
`∂_s u + J (∂_t u - X_{G_z}(u)) = 0` on `[a, b] × [0, 1]` for almost complex structures tamed by
`ω`. If `H₀ - H₁ ≤ B` along `u` for a function `B` integrable on `[0, 1]`, then the action of the
loop at `s = b` for `G(b, ·)` is at most that of the loop at `s = a` for `G(a, ·)` plus
`(β(b) - β(a)) ∫₀¹ B`. -/
theorem IsNondegenerate.contractibleLoopAction_le_contractibleLoopAction_add_of_linearHomotopy
    (hω : ω.IsNondegenerate) (hωe : IsWeaklyExact ω.1) {H₀ H₁ : ℝ → M → ℝ}
    (hH₀ : ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) 1 (uncurry H₀))
    (hH₁ : ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) 1 (uncurry H₁)) {β : ℝ → ℝ} (hβ : ContDiff ℝ 1 β)
    (hβm : Monotone β) (hu : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 2 u)
    (hper : ∀ z : ℝ × ℝ, u (z.1, z.2 + 1) = u z) {a b : ℝ} (hab : a ≤ b) {v : ℝ × ℝ → M}
    (hv : IsCap I v fun t ↦ u (b, t)) (J : ∀ z, AlmostComplexStructure (TangentSpace I (u z)))
    (hJ : ∀ z ∈ Icc a b ×ˢ Icc 0 1, (hω.symplecticFormAt (u z)).Tames (J z))
    (hfloer : ∀ z ∈ Icc a b ×ˢ Icc 0 1, mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal +
      J z (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag -
        ω.hamiltonianVectorField (Floer.linearHomotopy β H₀ H₁ z) (u z)) = 0)
    {B : ℝ → ℝ} (hB : IntegrableOn B (Icc 0 1))
    (hHB : ∀ z ∈ Icc a b ×ˢ Icc 0 1, H₀ z.2 (u z) - H₁ z.2 (u z) ≤ B z.2) :
    contractibleLoopAction ω.1 (fun t ↦ Floer.linearHomotopy β H₀ H₁ (b, t)) (fun t ↦ u (b, t)) ≤
      contractibleLoopAction ω.1 (fun t ↦ Floer.linearHomotopy β H₀ H₁ (a, t))
          (fun t ↦ u (a, t)) +
        (β b - β a) * ∫ t in Icc 0 1, B t := by
  have h := hω.contractibleLoopAction_le_contractibleLoopAction_sub_integral hωe
    (Floer.contMDiff_uncurry_linearHomotopy hβ hH₀ hH₁) hu hper hab hv J hJ hfloer
  -- It remains to bound `-∫ ∂_s G(u) = ∫ β'(s) (H₀ - H₁)(t, u)` by `(∫ β') (∫ B)`.
  have hd {K : ℝ → M → ℝ} (hK : ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) 1 (uncurry K)) (t : ℝ) (x : M) :
      DifferentiableAt ℝ (fun t ↦ K t x) t :=
    (contMDiff_iff_contDiff.mp (hK.comp (contMDiff_id.prodMk contMDiff_const))).differentiable
      one_ne_zero t
  have hcurv (z : ℝ × ℝ) :
      fderiv ℝ (fun w ↦ Floer.linearHomotopy β H₀ H₁ w (u z)) z stdComplexLineReal =
        deriv β z.1 * (H₁ z.2 (u z) - H₀ z.2 (u z)) :=
    Floer.fderiv_linearHomotopy_stdComplexLineReal (hβ.differentiable one_ne_zero z.1)
      (hd hH₀ _ _) (hd hH₁ _ _)
  simp only [hcurv] at h
  have hp : Continuous fun z : ℝ × ℝ ↦ (z.2, u z) := continuous_snd.prodMk hu.continuous
  have hle := neg_mul_setIntegral_le_setIntegral_deriv_mul
    (f := fun z ↦ H₁ z.2 (u z) - H₀ z.2 (u z)) hβ hβm hab
    ((hH₁.continuous.comp hp).sub (hH₀.continuous.comp hp)).continuousOn hB
    fun z hz ↦ by linarith [hHB z hz]
  linarith

/-- **The action shift of a continuation cylinder.** Let `ω` be a nondegenerate weakly exact
two-form on a finite-dimensional manifold, and `H₀` and `H₁` `C¹` time-dependent Hamiltonians with
`H₀ - H₁ ≤ h` on `[0, 1]`, uniformly on the manifold, for a function `h` integrable on `[0, 1]`.
Let `u` be a `C²` map, `1`-periodic in its second coordinate, whose loop at `s = b` bounds a cap,
solving the Floer equation
`∂_s u + J (∂_t u - X_{G_z}(u)) = 0` on `[a, b] × [0, 1]`, with `a ≤ 0` and `1 ≤ b`, for the
continuation homotopy `G` from `H₀` to `H₁` and almost complex structures tamed by `ω`. Then
`A_{H₁}(u(b, ·)) ≤ A_{H₀}(u(a, ·)) + ∫₀¹ h`. When `h(t) = sup_x (H₀ - H₁)(t, x)` is finite and
integrable on `[0, 1]` (for instance when `M` is compact), continuation cylinders shift the action
filtration by at most `∫₀¹ sup_x (H₀ - H₁) dt`; when `H₀ ≤ H₁`, taking `h = 0` shows that they
preserve it. -/
theorem
    IsNondegenerate.contractibleLoopAction_le_contractibleLoopAction_add_of_continuationHomotopy
    (hω : ω.IsNondegenerate) (hωe : IsWeaklyExact ω.1) {H₀ H₁ : ℝ → M → ℝ}
    (hH₀ : ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) 1 (uncurry H₀))
    (hH₁ : ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) 1 (uncurry H₁)) (hu : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 2 u)
    (hper : ∀ z : ℝ × ℝ, u (z.1, z.2 + 1) = u z) {a b : ℝ} (ha : a ≤ 0) (hb : 1 ≤ b)
    {v : ℝ × ℝ → M} (hv : IsCap I v fun t ↦ u (b, t))
    (J : ∀ z, AlmostComplexStructure (TangentSpace I (u z)))
    (hJ : ∀ z ∈ Icc a b ×ˢ Icc 0 1, (hω.symplecticFormAt (u z)).Tames (J z))
    (hfloer : ∀ z ∈ Icc a b ×ˢ Icc 0 1, mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal +
      J z (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag -
        ω.hamiltonianVectorField (Floer.continuationHomotopy H₀ H₁ z) (u z)) = 0)
    {h : ℝ → ℝ} (hh : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x, H₀ t x - H₁ t x ≤ h t)
    (hhi : IntegrableOn h (Icc 0 1)) :
    contractibleLoopAction ω.1 H₁ (fun t ↦ u (b, t)) ≤
      contractibleLoopAction ω.1 H₀ (fun t ↦ u (a, t)) + ∫ t in Icc 0 1, h t := by
  rw [Floer.continuationHomotopy_eq_linearHomotopy] at hfloer
  have h := hω.contractibleLoopAction_le_contractibleLoopAction_add_of_linearHomotopy hωe hH₀ hH₁
    (smoothTransition.contDiff (n := 1)) smoothTransition.monotone hu hper
    (ha.trans (zero_le_one.trans hb)) hv J hJ hfloer hhi fun z hz ↦ hh z.2 hz.2 (u z)
  -- At the two ends the homotopy is `H₀` and `H₁`.
  have hA : (fun t ↦ Floer.continuationHomotopy H₀ H₁ (a, t)) = H₀ :=
    funext fun t ↦ funext (Floer.continuationHomotopy_of_nonpos (z := (a, t)) ha)
  have hB : (fun t ↦ Floer.continuationHomotopy H₀ H₁ (b, t)) = H₁ :=
    funext fun t ↦ funext (Floer.continuationHomotopy_of_one_le (z := (b, t)) hb)
  simpa [← Floer.continuationHomotopy_eq_linearHomotopy, hA, hB,
    smoothTransition.zero_of_nonpos ha, smoothTransition.one_of_one_le hb] using h

end Energy

end TauCeti.SmoothTwoForm
