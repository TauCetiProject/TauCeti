/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Translation.Basic
public import TauCeti.MeasureTheory.Measure.ArctanCenter
public import TauCeti.MeasureTheory.Measure.FiniteMeasure.WithDensity

/-!
# A slice for the translation action on Floer cylinders

Floer cylinders `u : ℝ × [0, 1] → V`, solutions of `∂_s u + J (∂_t u - X_{H_t}(u)) = 0` for the
cylindrical perturbation `K = H_t dt`, are counted up to the translations
`(s, t) ↦ (s + c, t)`. Away from the stationary cylinders this action of `ℝ` is free
(`TauCeti.SymplecticForm.eq_zero_of_lintegral_floerEnergyDensity_ne_top_of_periodic`). This file
constructs a global slice for it: a translation-equivariant real-valued *center* of a cylinder,
whose zero set meets every orbit of nonstationary finite-energy cylinders exactly once.

The center is read off from the energy. The *strip energy measure*
`TauCeti.SymplecticForm.stripEnergyMeasure ω Ks Kt u` is the measure on `ℝ` giving each set `A`
of `s`-values the Floer energy of `u` over `A × [0, 1]`. Its total mass is the energy of `u` over
the strip, so it is finite and nonzero exactly for a finite-energy cylinder of nonzero energy; for
a solution of the Floer equation, nonzero energy means not stationary
(`TauCeti.SymplecticForm.lintegral_floerEnergyDensity_eq_zero_iff`). Translating `u` and its
perturbation data by `(c, 0)` translates this measure by `-c`
(`TauCeti.SymplecticForm.stripEnergyMeasure_comp_add_right`). The center of `u` is the arctan
center of its strip energy measure (`MeasureTheory.Measure.arctanCenter`), the unique `m` with
`∫ arctan (s - m) dE(s) = 0`. It is therefore equivariant: the center of the translate of `u` by
`(c, 0)` is the center of `u` minus `c`
(`TauCeti.SymplecticForm.arctanCenter_stripEnergyMeasure_cylindrical_comp_add_right`). Hence:

* each orbit contains exactly one cylinder of center zero, the translate of `u` by its center
  (`TauCeti.SymplecticForm.existsUnique_arctanCenter_stripEnergyMeasure_comp_add_right_eq_zero`,
  and its Floer form `..._eq_zero_of_floer` for nonstationary solutions);
* recentering a translate of `u` gives the recentered `u` itself
  (`TauCeti.SymplecticForm.comp_add_arctanCenter_stripEnergyMeasure_comp_add_right`), so
  recentering is a well-defined section of the quotient by translations.

The center is continuous for the weak topology on energy measures
(`MeasureTheory.FiniteMeasure.tendsto_arctanCenter`), so cylinders whose finite energy measures
converge weakly to a nonzero limit have converging centers. Weak convergence holds along cylinders
`u i → u₀` whose energy densities converge almost everywhere on the strip, as they do under `C¹`
convergence on compact sets, provided no energy is lost in the limit: the energies of `u i`
converge to the energy of `u₀`. By Scheffé's lemma the densities then converge in `L¹`, so the
strip energy measures converge weakly
(`MeasureTheory.FiniteMeasure.tendsto_of_ae_tendsto_of_tendsto_integral`), and if the energy of
`u₀` is nonzero the centers of `u i` converge to that of `u₀`
(`TauCeti.SymplecticForm.tendsto_arctanCenter_stripEnergyMeasure`). This is the continuity of the
slice where convergence loses no energy; along a sequence which breaks, part of the energy escapes
along the ends and the hypothesis fails. Unlike the usual action level slice
`A_H(u(0, ·)) = a`, which needs a level strictly between the actions of the two ends and the strict
monotonicity of the action along the cylinder, this slice needs neither unique continuation nor a
choice of level.

The target is a symplectic vector space and no Sobolev completion of the space of cylinders is
considered: the statements are about the action of `ℝ` on classical solutions.

## Main results

* `TauCeti.SymplecticForm.stripEnergyMeasure_comp_add_right`: translating the cylinder translates
  its strip energy measure.
* `TauCeti.SymplecticForm.arctanCenter_stripEnergyMeasure_cylindrical_comp_add_right`: the center
  is translation equivariant.
* `SymplecticForm.existsUnique_arctanCenter_stripEnergyMeasure_comp_add_right_eq_zero_of_floer`:
  each translation orbit of a nonstationary finite-energy Floer cylinder meets the slice of center
  zero exactly once.
* `TauCeti.SymplecticForm.tendsto_arctanCenter_stripEnergyMeasure`: the center is continuous along
  cylinders whose energy densities converge without loss of energy.

## References

* A. Floer, *Symplectic fixed points and holomorphic spheres*, Comm. Math. Phys. **120** (1989),
  575–611, on the translation action on connecting trajectories.
* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), Lecture 1, on moduli spaces of Floer cylinders modulo translation.
* H. Scheffé, *A useful convergence theorem for probability distributions*, Ann. Math. Statist.
  **18** (1947), 434–438.
-/

public section

noncomputable section

open Filter MeasureTheory Set Topology

namespace TauCeti.SymplecticForm

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

section Slice

variable {ω : SymplecticForm V} {H : ℝ → V → ℝ} {u : ℝ × ℝ → V}

/-- **Translation equivariance of the energy center.** For the cylindrical perturbation
`K = H_t dt` and a map `u` of finite nonzero energy over the strip, the arctan center of the strip
energy measure of the translate `(s, t) ↦ u(s + c, t)` is that of `u` minus `c`. -/
theorem arctanCenter_stripEnergyMeasure_cylindrical_comp_add_right
    (hfin : ∫⁻ z in (univ : Set ℝ) ×ˢ Icc 0 1,
      ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) u z) ≠ ⊤)
    (hE : ∫⁻ z in (univ : Set ℝ) ×ˢ Icc 0 1,
      ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) u z) ≠ 0) (c : ℝ) :
    (ω.stripEnergyMeasure (fun _ _ ↦ 0) (fun w ↦ H w.2) fun w ↦ u (w + (c, 0))).arctanCenter =
      (ω.stripEnergyMeasure (fun _ _ ↦ 0) (fun w ↦ H w.2) u).arctanCenter - c := by
  have := isFiniteMeasure_stripEnergyMeasure hfin
  have : NeZero (ω.stripEnergyMeasure (fun _ _ ↦ 0) (fun w ↦ H w.2) u) :=
    ⟨fun h ↦ hE (stripEnergyMeasure_eq_zero_iff.1 h)⟩
  simp_rw [stripEnergyMeasure_cylindrical_comp_add_right, sub_eq_add_neg,
    Measure.arctanCenter_map_add]

/-- **Each translation orbit meets the slice once.** For the cylindrical perturbation `K = H_t dt`
and a map `u` of finite nonzero energy over the strip, there is exactly one translation
`(s, t) ↦ (s + c, t)` after which the arctan center of the strip energy measure is `0`; it is
translation by the center of `u`. -/
theorem existsUnique_arctanCenter_stripEnergyMeasure_comp_add_right_eq_zero
    (hfin : ∫⁻ z in (univ : Set ℝ) ×ˢ Icc 0 1,
      ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) u z) ≠ ⊤)
    (hE : ∫⁻ z in (univ : Set ℝ) ×ˢ Icc 0 1,
      ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) u z) ≠ 0) :
    ∃! c : ℝ,
      (ω.stripEnergyMeasure (fun _ _ ↦ 0) (fun w ↦ H w.2) fun w ↦ u (w + (c, 0))).arctanCenter =
        0 := by
  simp_rw [arctanCenter_stripEnergyMeasure_cylindrical_comp_add_right hfin hE, sub_eq_zero]
  exact ⟨_, rfl, fun _ h ↦ h.symm⟩

/-- **The slice for nonstationary Floer cylinders.** Let `u` be `C¹` on a neighbourhood of the
strip `ℝ × [0, 1]`, solve the Floer equation for the cylindrical perturbation `K = H_t dt` and
almost complex structures tamed by `ω`, have finite energy, and not be stationary. Then exactly
one translate `(s, t) ↦ u(s + c, t)` of `u` has strip energy measure of arctan center `0`. -/
theorem existsUnique_arctanCenter_stripEnergyMeasure_comp_add_right_eq_zero_of_floer
    {J : ℝ × ℝ → AlmostComplexStructure V} {U : Set (ℝ × ℝ)}
    (hH : ContDiff ℝ 1 (Function.uncurry H)) (hU : IsOpen U)
    (hu : ContDiffOn ℝ 1 u U) (hRU : (univ : Set ℝ) ×ˢ Icc 0 1 ⊆ U)
    (hJ : ∀ z ∈ (univ : Set ℝ) ×ˢ Icc 0 1, ω.Tames (J z))
    (hfloer : ∀ z ∈ (univ : Set ℝ) ×ˢ Icc 0 1,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedFDeriv (fun _ _ ↦ 0) (fun w ↦ H w.2) u z : ℝ × ℝ →ₗ[ℝ] V))
    (hfin : ∫⁻ z in (univ : Set ℝ) ×ˢ Icc 0 1,
      ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) u z) ≠ ⊤)
    (hns : ∃ s, ∃ t ∈ Icc (0 : ℝ) 1, u (s, t) ≠ u (0, t)) :
    ∃! c : ℝ,
      (ω.stripEnergyMeasure (fun _ _ ↦ 0) (fun w ↦ H w.2) fun w ↦ u (w + (c, 0))).arctanCenter =
        0 := by
  refine existsUnique_arctanCenter_stripEnergyMeasure_comp_add_right_eq_zero hfin fun hE ↦ ?_
  obtain ⟨s, t, ht, hne⟩ := hns
  exact hne ((ω.lintegral_floerEnergyDensity_eq_zero_iff hH hU hu hRU hJ hfloer).1 hE s t ht)

/-- **Recentering is constant on translation orbits.** For the cylindrical perturbation `K = H_t dt`
and a map `u` of finite nonzero energy over the strip, translate any translate
`v = u(· + (c, 0))` of `u` by the arctan center of its strip energy measure: the result is the
translate of `u` by its own center. So recentering is a section of the quotient by translations,
with values in the slice of center zero. -/
theorem comp_add_arctanCenter_stripEnergyMeasure_comp_add_right
    (hfin : ∫⁻ z in (univ : Set ℝ) ×ˢ Icc 0 1,
      ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) u z) ≠ ⊤)
    (hE : ∫⁻ z in (univ : Set ℝ) ×ˢ Icc 0 1,
      ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) u z) ≠ 0) (c : ℝ) :
    (fun w ↦ u (w + ((ω.stripEnergyMeasure (fun _ _ ↦ 0) (fun w ↦ H w.2)
        fun w ↦ u (w + (c, 0))).arctanCenter, 0) + (c, 0))) =
      fun w ↦ u (w + ((ω.stripEnergyMeasure (fun _ _ ↦ 0) (fun w ↦ H w.2) u).arctanCenter, 0)) := by
  rw [arctanCenter_stripEnergyMeasure_cylindrical_comp_add_right hfin hE]
  set m := (ω.stripEnergyMeasure (fun _ _ ↦ 0) (fun w ↦ H w.2) u).arctanCenter
  have hm : ((m - c, 0) + (c, 0) : ℝ × ℝ) = (m, 0) := by ext <;> simp
  simp_rw [add_assoc, hm]

end Slice

section Continuity

variable {ω : SymplecticForm V} {Ks Kt : ℝ × ℝ → V → ℝ} {ι : Type*} {l : Filter ι}
  [l.IsCountablyGenerated] {u : ι → ℝ × ℝ → V} {u₀ : ℝ × ℝ → V}

/-- **Continuity of the energy center.** Let maps `u i` of the strip `ℝ × [0, 1]` have integrable
energy densities, nonnegative almost everywhere, which converge almost everywhere on the strip to
the integrable energy density of a map `u₀`. If moreover no energy is lost in the limit, that is,
the energies of `u i` over the strip converge to the energy of `u₀`, and the energy of `u₀` is
nonzero, then the arctan centers of the strip energy measures of `u i` converge to that of `u₀`.
-/
theorem tendsto_arctanCenter_stripEnergyMeasure
    (hint : ∀ i, IntegrableOn (ω.floerEnergyDensity Ks Kt (u i)) ((univ : Set ℝ) ×ˢ Icc 0 1))
    (hint₀ : IntegrableOn (ω.floerEnergyDensity Ks Kt u₀) ((univ : Set ℝ) ×ˢ Icc 0 1))
    (hnonneg : ∀ i, 0 ≤ᵐ[volume.restrict ((univ : Set ℝ) ×ˢ Icc 0 1)]
      ω.floerEnergyDensity Ks Kt (u i))
    (hlim : ∀ᵐ z ∂volume.restrict ((univ : Set ℝ) ×ˢ Icc 0 1),
      Tendsto (fun i ↦ ω.floerEnergyDensity Ks Kt (u i) z) l
        (𝓝 (ω.floerEnergyDensity Ks Kt u₀ z)))
    (henergy : Tendsto
      (fun i ↦ ∫ z in (univ : Set ℝ) ×ˢ Icc 0 1, ω.floerEnergyDensity Ks Kt (u i) z) l
      (𝓝 (∫ z in (univ : Set ℝ) ×ˢ Icc 0 1, ω.floerEnergyDensity Ks Kt u₀ z)))
    (hE : ∫ z in (univ : Set ℝ) ×ˢ Icc 0 1, ω.floerEnergyDensity Ks Kt u₀ z ≠ 0) :
    Tendsto (fun i ↦ (ω.stripEnergyMeasure Ks Kt (u i)).arctanCenter) l
      (𝓝 (ω.stripEnergyMeasure Ks Kt u₀).arctanCenter) := by
  rcases l.eq_or_neBot with rfl | _
  · exact tendsto_bot
  set S := (univ : Set ℝ) ×ˢ Icc (0 : ℝ) 1
  -- The energy measures on the strip, as finite measures.
  let μ (v : ℝ × ℝ → V) (hv : IntegrableOn (ω.floerEnergyDensity Ks Kt v) S) :
      FiniteMeasure (ℝ × ℝ) :=
    ⟨(volume.restrict S).withDensity fun z ↦ ENNReal.ofReal (ω.floerEnergyDensity Ks Kt v z),
      isFiniteMeasure_withDensity_ofReal hv.hasFiniteIntegral⟩
  -- Their pushforwards to the `s`-axis are the strip energy measures.
  have hμ (v : ℝ × ℝ → V) (hv : IntegrableOn (ω.floerEnergyDensity Ks Kt v) S) :
      ((μ v hv).map Prod.fst).toMeasure = ω.stripEnergyMeasure Ks Kt v := by
    rw [FiniteMeasure.toMeasure_map, stripEnergyMeasure_def]
    simp only [μ, S, FiniteMeasure.toMeasure_mk]
  -- By Scheffé's lemma the finite measures converge weakly, and so do their pushforwards.
  have h := FiniteMeasure.tendsto_map_of_tendsto_of_continuous _ _
    (FiniteMeasure.tendsto_of_ae_tendsto_of_tendsto_integral (μs := fun i ↦ μ (u i) (hint i))
      (ν := μ u₀ hint₀) hint hint₀ hnonneg (fun _ ↦ rfl) rfl hlim henergy) continuous_fst
  -- The limit is nonzero: otherwise the energy density of `u₀` would be nonpositive almost
  -- everywhere, while its energy is a limit of nonnegative energies.
  have hne : (μ u₀ hint₀).map Prod.fst ≠ 0 := by
    intro h0
    have h0' : ω.stripEnergyMeasure Ks Kt u₀ = 0 := by
      rw [← hμ u₀ hint₀, h0, FiniteMeasure.toMeasure_zero]
    have hle : ω.floerEnergyDensity Ks Kt u₀ ≤ᵐ[volume.restrict S] 0 := by
      filter_upwards [(lintegral_eq_zero_iff' hint₀.aemeasurable.ennreal_ofReal).1
        (stripEnergyMeasure_eq_zero_iff.1 h0')] with z hz
      exact ENNReal.ofReal_eq_zero.1 hz
    exact hE (le_antisymm (integral_nonpos_of_ae hle)
      (ge_of_tendsto' henergy fun i ↦ integral_nonneg_of_ae (hnonneg i)))
  simpa only [hμ] using FiniteMeasure.tendsto_arctanCenter hne h

end Continuity

end TauCeti.SymplecticForm
