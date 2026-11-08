/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Flow.Periodic
public import TauCeti.Geometry.Symplectic.Floer.CylinderAction
import TauCeti.Geometry.Manifold.MFDeriv.Constancy
import TauCeti.Geometry.Manifold.MFDeriv.Curve
import TauCeti.MeasureTheory.Integral.Lebesgue.Strip

/-!
# Stationary Floer cylinders in a manifold

Let `ω` be a nondegenerate two-form on a finite-dimensional manifold `M`, such as a closed
symplectic manifold, and `H : ℝ → M → ℝ` a time-dependent Hamiltonian. The Floer differential, and
the cylinders inserted at the ends of a pair of pants, count maps `u : ℝ × ℝ → M` solving

`∂_s u + J (∂_t u - X_{H_t}(u)) = 0`

for the cylindrical perturbation `K = H_t dt`, up to the translations `(s, t) ↦ (s + c, t)`, with
the convention `ι_{X_H} ω = dH`. This file is the manifold-target counterpart of
`TauCeti.Geometry.Symplectic.Floer.Translation`: it identifies the fixed points of the translation
action and shows that the action is free elsewhere.

The *stationary* maps `u(s, t) = x(t)` are fixed by every translation. Such a map has
`∂_s u = 0` and `∂_t u = x'`, so it solves the Floer equation exactly when
`x' = X_{H_t}(x)`, whatever the almost complex structure
(`SmoothTwoForm.isComplexLinearMap_perturbedMFDeriv_comp_snd_iff`). In particular the stationary
cylinder over a `1`-periodic orbit (`TauCeti.periodicSolutions`) is a Floer cylinder
(`SmoothTwoForm.isComplexLinearMap_perturbedMFDeriv_comp_snd_of_mem_periodicSolutions`), and its
energy density vanishes.

Conversely, for almost complex structures tamed by `ω`, the energy density of a solution vanishes
exactly where `∂_s u` does
(`SmoothTwoForm.IsNondegenerate.floerEnergyDensity_cylindrical_eq_zero_iff`). The energy density
of a `C¹` map is continuous
(`SmoothTwoForm.IsNondegenerate.continuous_floerEnergyDensity_cylindrical`), so a `C¹` solution
on the strip `ℝ × [0, 1]` has zero energy exactly when it is stationary there
(`SmoothTwoForm.IsNondegenerate.lintegral_floerEnergyDensity_eq_zero_iff`).

A solution of finite energy that is invariant under a translation by `c ≠ 0` has the same energy
over each of the infinitely many disjoint period rectangles of the strip, so its energy is zero
(`SmoothTwoForm.lintegral_floerEnergyDensity_eq_zero_of_periodic`, from
`TauCeti.setLIntegral_univ_prod_eq_zero_of_periodic`), and it is stationary. Hence a
nonstationary finite-energy solution is fixed by no nontrivial translation
(`SmoothTwoForm.IsNondegenerate.eq_zero_of_lintegral_floerEnergyDensity_ne_top_of_periodic`).

These are statements about classical solutions; no Sobolev completion, compactness or
transversality is asserted.

## Main results

* `SmoothTwoForm.isComplexLinearMap_perturbedMFDeriv_comp_snd_iff`: stationary solutions are the
  Hamiltonian orbits.
* `SmoothTwoForm.IsNondegenerate.lintegral_floerEnergyDensity_eq_zero_iff`: a solution has zero
  energy exactly when it is stationary.
* `SmoothTwoForm.lintegral_floerEnergyDensity_eq_zero_of_periodic`: a finite-energy map invariant
  under a nontrivial translation has zero energy.
* `SmoothTwoForm.IsNondegenerate.eq_zero_of_lintegral_floerEnergyDensity_ne_top_of_periodic`:
  translations act freely on nonstationary finite-energy solutions.

## References

* A. Floer, *Symplectic fixed points and holomorphic spheres*, Comm. Math. Phys. **120** (1989),
  575–611, on the translation action on connecting trajectories.
* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), Lecture 1, on the energy of Floer cylinders and the stationary solutions.
-/

public section

open Filter Function MeasureTheory Set Topology
open scoped Manifold

namespace TauCeti.SmoothTwoForm

variable {E HM M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace HM]
  {I : ModelWithCorners ℝ E HM} [TopologicalSpace M] [ChartedSpace HM M]
  [IsManifold I (⊤ : ℕ∞) M]

/-! ### Stationary maps -/

section Stationary

variable {ω : SmoothTwoForm I M} {H : ℝ → M → ℝ} {x : ℝ → M} {z : ℝ × ℝ}

/-- **Stationary Floer cylinders are Hamiltonian orbits.** For the cylindrical perturbation
`K = H_t dt` and any almost complex structure `J` on the tangent space, the stationary map
`(s, t) ↦ x(t)` solves the Floer equation at `z` exactly when `x'(t) = X_{H_t}(x(t))`, where
`t = z.2`. -/
theorem isComplexLinearMap_perturbedMFDeriv_comp_snd_iff
    {J : AlmostComplexStructure (TangentSpace I (x z.2))} (hx : MDifferentiableAt 𝓘(ℝ) I x z.2) :
    IsComplexLinearMap (AlmostComplexStructure.product ℝ) J
        (ω.perturbedMFDeriv (fun _ _ ↦ 0) (fun w ↦ H w.2) (fun w ↦ x w.2) z).toLinearMap ↔
      Manifold.curveVelocity I x z.2 = ω.hamiltonianVectorField (H z.2) (x z.2) := by
  rw [ω.isComplexLinearMap_perturbedMFDeriv_iff _ _ (fun w ↦ x w.2) z J,
    stdComplexLineReal_eq, stdComplexLineImag_eq, Manifold.mfderiv_comp_snd_apply_one_zero hx,
    Manifold.mfderiv_comp_snd_apply_zero_one hx, hamiltonianVectorField_const, Pi.zero_apply,
    sub_zero, zero_add]
  -- An almost complex structure is injective, since `J (J v) = -v`.
  refine ⟨fun h ↦ ?_, fun h ↦ by rw [h, sub_self, map_zero]⟩
  have h' := congrArg J h
  rw [AlmostComplexStructure.apply_apply, map_zero, neg_eq_zero] at h'
  exact sub_eq_zero.1 h'

/-- **The stationary cylinder over a periodic orbit is a Floer cylinder.** If `x` is a periodic
solution of the Hamiltonian vector field of `H`, then the stationary map `(s, t) ↦ x(t)` solves the
Floer equation for the cylindrical perturbation `K = H_t dt` at every point, for every almost
complex structure. -/
theorem isComplexLinearMap_perturbedMFDeriv_comp_snd_of_mem_periodicSolutions {T : ℝ}
    (hx : x ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H t)) T) (z : ℝ × ℝ)
    (J : AlmostComplexStructure (TangentSpace I (x z.2))) :
    IsComplexLinearMap (AlmostComplexStructure.product ℝ) J
      (ω.perturbedMFDeriv (fun _ _ ↦ 0) (fun w ↦ H w.2) (fun w ↦ x w.2) z).toLinearMap := by
  have h := (mem_periodicSolutions.1 hx).1 z.2
  rw [isComplexLinearMap_perturbedMFDeriv_comp_snd_iff h.mdifferentiableAt]
  simpa only [Manifold.curveVelocityWithin_univ] using
    Manifold.curveVelocityWithin_eq_of_hasMFDerivWithinAt h.hasMFDerivWithinAt
      uniqueDiffWithinAt_univ

/-- **The energy density of a stationary map.** For the cylindrical perturbation `K = H_t dt`,
the Floer energy density of `(s, t) ↦ x(t)` vanishes. -/
theorem floerEnergyDensity_comp_snd (hx : MDifferentiableAt 𝓘(ℝ) I x z.2) :
    ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) (fun w ↦ x w.2) z = 0 := by
  rw [floerEnergyDensity_def, perturbedMFDeriv_apply_stdComplexLineReal,
    stdComplexLineReal_eq, Manifold.mfderiv_comp_snd_apply_one_zero hx,
    hamiltonianVectorField_const, Pi.zero_apply, sub_zero, SmoothBundleForm.eval₂_apply]
  exact ContinuousAlternatingMap.map_coord_zero _ 0 rfl

end Stationary

/-! ### Zero energy and translations -/

section Energy

variable {ω : SmoothTwoForm I M} {H : ℝ → M → ℝ} {u : ℝ × ℝ → M}

/-- For a solution of the Floer equation for the cylindrical perturbation `K = H_t dt` with `J`
tamed by `ω` at `u z`, the Floer energy density at `z` vanishes exactly when `∂_s u` does. -/
theorem IsNondegenerate.floerEnergyDensity_cylindrical_eq_zero_iff (hω : ω.IsNondegenerate)
    {z : ℝ × ℝ} {J : AlmostComplexStructure (TangentSpace I (u z))}
    (hJ : (hω.symplecticFormAt (u z)).Tames J)
    (hfloer : mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal +
      J (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag -
        ω.hamiltonianVectorField (H z.2) (u z)) = 0) :
    ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) u z = 0 ↔
      mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal = 0 := by
  set a := mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal
  -- The Floer equation `a + J b = 0` says `b = J a`, so the density is `ω(a, J a)`.
  have hb : mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag -
      ω.hamiltonianVectorField (H z.2) (u z) = J a := by
    have h := congrArg J hfloer
    rw [map_add, AlmostComplexStructure.apply_apply, map_zero] at h
    exact (add_neg_eq_zero.1 h).symm
  have hρ : ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) u z =
      hω.symplecticFormAt (u z) a (J a) := by
    rw [floerEnergyDensity_def, perturbedMFDeriv_apply_stdComplexLineImag,
      perturbedMFDeriv_apply_stdComplexLineReal, hb, hamiltonianVectorField_const, Pi.zero_apply,
      sub_zero, IsNondegenerate.symplecticFormAt_apply]
  rw [hρ]
  refine ⟨fun h ↦ by_contra fun ha ↦ (hJ a ha).ne' h, fun h ↦ ?_⟩
  rw [h]
  simp

variable {J : (z : ℝ × ℝ) → AlmostComplexStructure (TangentSpace I (u z))}

/-- The open strip `ℝ × (0, 1)` lies in the closed strip `ℝ × [0, 1]`. -/
private theorem strip_Ioo_subset_Icc :
    (univ : Set ℝ) ×ˢ Ioo (0 : ℝ) 1 ⊆ (univ : Set ℝ) ×ˢ Icc 0 1 :=
  prod_mono subset_rfl Ioo_subset_Icc_self

/-- The closed strip `ℝ × [0, 1]` is the closure of the open strip `ℝ × (0, 1)`. -/
private theorem closure_univ_prod_Ioo :
    closure ((univ : Set ℝ) ×ˢ Ioo (0 : ℝ) 1) = (univ : Set ℝ) ×ˢ Icc 0 1 := by
  rw [closure_prod_eq, closure_univ, closure_Ioo zero_ne_one]

variable [FiniteDimensional ℝ E]

/-- For a `C¹` solution with tamed almost complex structures, zero energy over the open strip
`ℝ × (0, 1)` forces the energy density to vanish on the closed strip `ℝ × [0, 1]`. -/
private theorem IsNondegenerate.eqOn_floerEnergyDensity_zero (hω : ω.IsNondegenerate)
    (hH : ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) 1 (uncurry H)) (hu : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 1 u)
    (hJ : ∀ z ∈ (univ : Set ℝ) ×ˢ Icc 0 1, (hω.symplecticFormAt (u z)).Tames (J z))
    (hfloer : ∀ z ∈ (univ : Set ℝ) ×ˢ Icc 0 1, mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal +
      J z (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag -
        ω.hamiltonianVectorField (H z.2) (u z)) = 0)
    (hE : ∫⁻ z in (univ : Set ℝ) ×ˢ Ioo 0 1,
      ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) u z) = 0) :
    EqOn (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) u) 0 ((univ : Set ℝ) ×ˢ Icc 0 1) := by
  have hρ := hω.continuous_floerEnergyDensity_cylindrical hH hu
  -- A continuous function with zero integral over the open strip vanishes there.
  have hc := ENNReal.continuous_ofReal.comp hρ
  have hae := (lintegral_eq_zero_iff' hc.measurable.aemeasurable).1 hE
  have h0 : EqOn (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) u) 0
      ((univ : Set ℝ) ×ˢ Ioo 0 1) := fun z hz ↦ by
    have h := Measure.eqOn_open_of_ae_eq hae (isOpen_univ.prod isOpen_Ioo) hc.continuousOn
      continuous_zero.continuousOn hz
    exact le_antisymm (ENNReal.ofReal_eq_zero.1 h)
      (hω.floerEnergyDensity_cylindrical_nonneg (hJ z (strip_Ioo_subset_Icc hz))
        (hfloer z (strip_Ioo_subset_Icc hz)))
  -- By continuity it vanishes on the closed strip.
  exact h0.of_subset_closure hρ.continuousOn continuous_zero.continuousOn strip_Ioo_subset_Icc
    closure_univ_prod_Ioo.ge

/-- **Zero energy characterizes stationary Floer cylinders.** Let `H` be a jointly `C¹`
time-dependent Hamiltonian and let `u` be a `C¹` map solving the Floer equation for the
cylindrical perturbation `K = H_t dt` on the strip `ℝ × [0, 1]`, for almost complex structures
`J z` tamed by `ω`. Then the energy of `u` over the strip vanishes exactly when `u` is stationary
there, `u(s, t) = u(0, t)`. -/
theorem IsNondegenerate.lintegral_floerEnergyDensity_eq_zero_iff (hω : ω.IsNondegenerate)
    (hH : ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) 1 (uncurry H)) (hu : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 1 u)
    (hJ : ∀ z ∈ (univ : Set ℝ) ×ˢ Icc 0 1, (hω.symplecticFormAt (u z)).Tames (J z))
    (hfloer : ∀ z ∈ (univ : Set ℝ) ×ˢ Icc 0 1, mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal +
      J z (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag -
        ω.hamiltonianVectorField (H z.2) (u z)) = 0) :
    ∫⁻ z in (univ : Set ℝ) ×ˢ Icc 0 1,
        ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) u z) = 0 ↔
      ∀ s, ∀ t ∈ Icc (0 : ℝ) 1, u (s, t) = u (0, t) := by
  -- On the closed strip, the energy density vanishes exactly where `∂_s u` does.
  have hiff (z : ℝ × ℝ) (hz : z ∈ (univ : Set ℝ) ×ˢ Icc 0 1) :
      ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) u z = 0 ↔
        mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal = 0 :=
    hω.floerEnergyDensity_cylindrical_eq_zero_iff (hJ z hz) (hfloer z hz)
  constructor
  · intro hE
    have h0 := hω.eqOn_floerEnergyDensity_zero hH hu hJ hfloer
      (le_antisymm (hE ▸ lintegral_mono_set strip_Ioo_subset_Icc) zero_le)
    intro s t ht
    refine Manifold.apply_eq_of_mfderiv_apply_one_zero_eq_zero
      (fun r ↦ (hu (r, t)).mdifferentiableAt one_ne_zero) (fun r ↦ ?_) s 0
    rw [← stdComplexLineReal_eq]
    exact (hiff _ ⟨mem_univ r, ht⟩).1 (h0 ⟨mem_univ r, ht⟩)
  · intro hst
    have hs (z : ℝ × ℝ) (hz : z ∈ (univ : Set ℝ) ×ˢ Icc 0 1) :
        mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal = 0 := by
      rw [stdComplexLineReal_eq]
      exact Manifold.mfderiv_apply_one_zero_eq_zero_of_apply_eq
        ((hu z).mdifferentiableAt one_ne_zero) fun s ↦ hst s z.2 hz.2
    rw [setLIntegral_congr_fun (MeasurableSet.univ.prod measurableSet_Icc) fun z hz ↦ by
      rw [(hiff z hz).2 (hs z hz), ENNReal.ofReal_zero]]
    exact lintegral_zero

omit [FiniteDimensional ℝ E] in
/-- **Translation-invariant maps have zero energy.** Suppose that a differentiable map `u` has
finite energy over the strip `ℝ × [0, 1]` for the cylindrical perturbation `K = H_t dt`, and is
invariant there under the translation `(s, t) ↦ (s + c, t)` for some `c ≠ 0`. Then the energy of
`u` vanishes. No Floer equation, regularity of `H` or nondegeneracy of `ω` is needed; for a Floer
cylinder, `TauCeti.SmoothTwoForm.IsNondegenerate.lintegral_floerEnergyDensity_eq_zero_iff` then
shows that `u` is stationary. -/
theorem lintegral_floerEnergyDensity_eq_zero_of_periodic (hu : MDifferentiable 𝓘(ℝ, ℝ × ℝ) I u)
    (hfin : ∫⁻ z in (univ : Set ℝ) ×ˢ Icc 0 1,
      ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) u z) ≠ ⊤)
    {c : ℝ} (hc : c ≠ 0) (hper : ∀ s, ∀ t ∈ Icc (0 : ℝ) 1, u (s + c, t) = u (s, t)) :
    ∫⁻ z in (univ : Set ℝ) ×ˢ Icc 0 1,
      ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) u z) = 0 := by
  set f : ℝ × ℝ → ENNReal := fun z ↦
    ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) u z)
  -- `u` is also invariant under the translation by the positive period `|c|`.
  have hper' : ∀ s, ∀ t ∈ Icc (0 : ℝ) 1, u (s + |c|, t) = u (s, t) := by
    intro s t ht
    rcases abs_cases c with ⟨hc', -⟩ | ⟨hc', -⟩
    · rw [hc', hper s t ht]
    · rw [hc', ← hper (s + -c) t ht, neg_add_cancel_right]
  -- So is its energy density on the open strip, where the translate agrees with `u` nearby.
  have hf : ∀ s, ∀ t ∈ Ioo (0 : ℝ) 1, f (s + |c|, t) = f (s, t) := by
    intro s t ht
    have hev : (fun w : ℝ × ℝ ↦ u (w.1 + |c|, w.2)) =ᶠ[𝓝 (s, t)] u :=
      Filter.mem_of_superset ((isOpen_univ.prod isOpen_Ioo).mem_nhds ⟨mem_univ s, ht⟩)
        fun w hw ↦ hper' w.1 w.2 (Ioo_subset_Icc_self hw.2)
    -- By the chain rule for the translation, `u` has the same derivative at `(s, t)` and at
    -- `(s + |c|, t)`, up to the identification of the tangent spaces at equal points.
    have hτ : HasMFDerivAt 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ) (fun w : ℝ × ℝ ↦ (w.1 + |c|, w.2)) (s, t)
        (ContinuousLinearMap.id ℝ (ℝ × ℝ)) := by
      have hfun : (fun w : ℝ × ℝ ↦ id w + ((|c|, (0 : ℝ)) : ℝ × ℝ)) =
          fun w ↦ (w.1 + |c|, w.2) :=
        funext fun w ↦ Prod.ext (by simp) (by simp)
      have h := ((hasFDerivAt_id (𝕜 := ℝ) (s, t)).add_const ((|c|, 0) : ℝ × ℝ)).hasMFDerivAt
      rwa [hfun] at h
    have hd : mfderiv 𝓘(ℝ, ℝ × ℝ) I u (s + |c|, t) =
        (tangentSpaceCast I (u (s, t)) (u (s + |c|, t)) :
          TangentSpace I (u (s, t)) →L[ℝ] TangentSpace I (u (s + |c|, t))) ∘L
          mfderiv 𝓘(ℝ, ℝ × ℝ) I u (s, t) := by
      have h1 := ((hu (s + |c|, t)).hasMFDerivAt.comp (s, t) hτ).mfderiv
      -- `h1` reads `mfderiv u (s + |c|, t) ∘L id`, with the point written as `τ (s, t)`; both
      -- agree with the stated form by unfolding `ContinuousLinearMap.comp` and the projections.
      exact h1.symm.trans (hev.mfderiv_eq (I := 𝓘(ℝ, ℝ × ℝ)) (I' := I))
    simp only [f, floerEnergyDensity_def, perturbedMFDeriv_apply]
    rw [hd, hper' s t (Ioo_subset_Icc_self ht)]
    -- `tangentSpaceCast` between the tangent spaces at two equal points is the identity.
    rfl
  have hμ : MeasurePreserving (fun z : ℝ × ℝ ↦ (z.1 + |c|, z.2)) volume volume :=
    (measurePreserving_add_right volume |c|).prod (MeasurePreserving.id volume)
  -- The energy over the open strip vanishes, and the open and closed strips differ by the null
  -- set `ℝ × {0, 1}`.
  have hE := setLIntegral_univ_prod_eq_zero_of_periodic measurableSet_Ioo (abs_pos.2 hc) hμ hf
    (ne_top_of_le_ne_top hfin (lintegral_mono_set strip_Ioo_subset_Icc))
  have hae : (univ : Set ℝ) ×ˢ Ioo (0 : ℝ) 1 =ᵐ[volume] (univ : Set ℝ) ×ˢ Icc 0 1 := by
    rw [Measure.volume_eq_prod]
    exact Measure.set_prod_ae_eq (ae_eq_refl _) Ioo_ae_eq_Icc
  rwa [← setLIntegral_congr hae]

/-- **Translations act freely on nonstationary finite-energy Floer cylinders.** Under the
hypotheses of `TauCeti.SmoothTwoForm.IsNondegenerate.lintegral_floerEnergyDensity_eq_zero_iff`, if
`u` has finite energy over the strip `ℝ × [0, 1]` and is not stationary there, then the only
translation `(s, t) ↦ (s + c, t)` leaving `u` invariant on the strip is the identity, `c = 0`. -/
theorem IsNondegenerate.eq_zero_of_lintegral_floerEnergyDensity_ne_top_of_periodic
    (hω : ω.IsNondegenerate) (hH : ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) 1 (uncurry H))
    (hu : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 1 u)
    (hJ : ∀ z ∈ (univ : Set ℝ) ×ˢ Icc 0 1, (hω.symplecticFormAt (u z)).Tames (J z))
    (hfloer : ∀ z ∈ (univ : Set ℝ) ×ˢ Icc 0 1, mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal +
      J z (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag -
        ω.hamiltonianVectorField (H z.2) (u z)) = 0)
    (hfin : ∫⁻ z in (univ : Set ℝ) ×ˢ Icc 0 1,
      ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) u z) ≠ ⊤)
    (hns : ∃ s, ∃ t ∈ Icc (0 : ℝ) 1, u (s, t) ≠ u (0, t))
    {c : ℝ} (hper : ∀ s, ∀ t ∈ Icc (0 : ℝ) 1, u (s + c, t) = u (s, t)) :
    c = 0 := by
  by_contra hc
  obtain ⟨s, t, ht, hne⟩ := hns
  exact hne ((hω.lintegral_floerEnergyDensity_eq_zero_iff hH hu hJ hfloer).1
    (lintegral_floerEnergyDensity_eq_zero_of_periodic (hu.mdifferentiable one_ne_zero) hfin hc
      hper) s t ht)

end Energy

end TauCeti.SmoothTwoForm
