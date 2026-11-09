/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Manifold
public import TauCeti.Geometry.Symplectic.Hamiltonian.Action
public import TauCeti.Geometry.Symplectic.Hamiltonian.ContractibleAction.Basic

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
rewrites the right-hand side as a difference of actions of the two loops, in four settings.

* For an arbitrary nondegenerate form, such as the symplectic form of a closed monotone
  manifold, and a `C¹` map `v` with `v (0, ·) = γ_b`, the energy is
  `A_H(γ_a, w # v) - A_H(γ_b, v)` for the action `A_H(γ, u) = ∫ u^* ω - ∫₀¹ H(t, γ(t)) dt` of
  `γ` measured against `u` (`TauCeti.cylinderAction`), where `w` is `u` on `[a, b] × ℝ` rescaled
  to `[0, 1] × ℝ`
  (`SmoothTwoForm.IsNondegenerate.integral_floerEnergyDensity_eq_cylinderAction_sub`). When `v`
  is a cap of `γ_b`, `w # v` is a cap of `γ_a`, and the energy is the drop of the capped action.
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
(`TauCeti.SmoothTwoForm.IsNondegenerate.referenceAction_le_referenceAction`).
This monotonicity underlies the action filtration of the Floer complex.

## Main results

* `TauCeti.SmoothTwoForm.IsNondegenerate.integral_floerEnergyDensity_cylindrical`: the energy of a
  map over `[a, b] × [0, 1]` for a cylindrical perturbation.
* `SmoothTwoForm.IsNondegenerate.integral_floerEnergyDensity_eq_cylinderAction_sub`: the energy
  of a cylinder is the drop of the capped action, for any nondegenerate form.
* `TauCeti.SmoothTwoForm.IsNondegenerate.cylinderAction_le_cylinderAction`: the capped action
  decreases along Floer cylinders.
* `SmoothTwoForm.IsNondegenerate.integral_floerEnergyDensity_eq_contractibleLoopAction_sub`: for a
  weakly exact form, the energy of a cylinder is the drop of the contractible action.
* `TauCeti.SmoothTwoForm.IsNondegenerate.integral_floerEnergyDensity_eq_sub_of_mextDeriv_eq`: for
  an exact form, the energy of a cylinder is the drop of the action of its loops.
* `TauCeti.SmoothTwoForm.IsNondegenerate.contractibleLoopAction_le_contractibleLoopAction`: the
  contractible action decreases along Floer cylinders.
* `TauCeti.SmoothTwoForm.IsNondegenerate.integral_floerEnergyDensity_eq_referenceAction_sub`: for a
  form vanishing on tori, the energy of a cylinder is the drop of the action relative to a
  reference loop.
* `TauCeti.SmoothTwoForm.IsNondegenerate.referenceAction_le_referenceAction`: the action relative
  to a reference loop decreases along Floer cylinders.

## References

* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), Lecture 1 (the energy identity for Floer cylinders, with the sign
  conventions used here).
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS, 2012,
  Section 8.1 and the chapter on Floer homology.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §3.2.
-/

public noncomputable section

open Set MeasureTheory Function
open scoped Manifold Interval

namespace TauCeti.SmoothTwoForm

variable {E HM M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace HM]
  {I : ModelWithCorners ℝ E HM} [TopologicalSpace M] [ChartedSpace HM M]
  [IsManifold I (⊤ : ℕ∞) M]

variable {ω : SmoothTwoForm I M} {H : ℝ → M → ℝ} {u : ℝ × ℝ → M}

/-! ### The energy identity for cylindrical perturbations -/

section Energy

variable [FiniteDimensional ℝ E]

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
  have hR : Icc a b ×ˢ Icc (0 : ℝ) 1 = Icc (a, 0) (b, 1) := Icc_prod_Icc _ _ _ _
  have hab' : ((a, 0) : ℝ × ℝ) ≤ (b, 1) := Prod.mk_le_mk.2 ⟨hab, zero_le_one⟩
  have hKt : ContMDiff (𝓘(ℝ, ℝ × ℝ).prod I) 𝓘(ℝ) 1 (uncurry fun (w : ℝ × ℝ) ↦ H w.2) :=
    hH.comp ((contDiff_snd.contMDiff.comp contMDiff_fst).prodMk contMDiff_snd)
  have hω₀ : IsSmoothForm I 0 ω.1 := ω.isSmoothForm.of_le (by simp)
  have hE := hω.continuous_floerEnergyDensity_zero_left hKt hu
  have h := hω.integral_floerEnergyDensity (Ks := fun _ _ ↦ 0) (Kt := fun w ↦ H w.2) isOpen_univ
    hu.contMDiffOn contMDiffOn_const hKt.contMDiffOn hab' (subset_univ _)
    (hE.continuousOn.integrableOn_compact isCompact_Icc)
    (by simp [hamiltonianCurvature_cylindrical])
  simp only [hamiltonianCurvature_cylindrical, intervalIntegral.integral_zero, integral_zero] at h
  rw [hR, h, ← hω₀.setIntegral_eq_rectangleIntegral hu hab']
  simp only [SmoothBundleForm.eval₂_apply, stdComplexLineReal_eq, stdComplexLineImag_eq]
  ring

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
  -- Rescaling `[a, b]` to `[0, 1]` makes `u` a cylinder from `γ_a` to `γ_b`.
  have hw : IsLoopCylinder I (u ∘ Prod.map (fun s ↦ a + (b - a) * s) id) (fun t ↦ u (a, t))
      fun t ↦ u (b, t) :=
    { contMDiff := hu.comp (contMDiff_prodMap_affine a b)
      apply_add_one := fun z ↦ hper (a + (b - a) * z.1, z.2)
      apply_zero := fun t ↦ by simp
      apply_one := fun t ↦ by simp }
  rw [hω.integral_floerEnergyDensity_eq_cylinderAction_sub hH (hu.of_le one_le_two) hab
      (hv'.contMDiff.of_le one_le_two) hv'.apply_zero,
    hωe.contractibleLoopAction_eq hω₀ H (hw.trans hv').isCap,
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

end Energy

end TauCeti.SmoothTwoForm
