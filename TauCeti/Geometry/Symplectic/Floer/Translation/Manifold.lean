/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Stationary
public import TauCeti.Geometry.Symplectic.Floer.Translation.Slice
public import TauCeti.MeasureTheory.Measure.FiniteMeasure.WithDensity

/-!
# The translation slice for Floer cylinders in a manifold

Let `ω` be a nondegenerate two-form on a finite-dimensional manifold `M`, such as a closed
symplectic manifold. Floer cylinders `u : ℝ × [0, 1] → M`, solutions of
`∂_s u + J (∂_t u - X_{H_t}(u)) = 0` for the cylindrical perturbation `K = H_t dt`, are counted up
to the translations `(s, t) ↦ (s + c, t)`, which act freely away from the stationary cylinders
(`SmoothTwoForm.IsNondegenerate.eq_zero_of_lintegral_floerEnergyDensity_ne_top_of_periodic`).
This file constructs a slice for this action, and shows that it depends continuously on the
cylinder. It is the manifold-target counterpart of
`TauCeti.Geometry.Symplectic.Floer.Translation.Slice`.

The *strip energy measure* `TauCeti.SmoothTwoForm.stripEnergyMeasure ω Ks Kt u` is the measure on
`ℝ` giving each set `A` of `s`-values the Floer energy of `u` over `A × [0, 1]`. Translating `u`
and its perturbation data by `(c, 0)` translates it by `-c`
(`TauCeti.SmoothTwoForm.stripEnergyMeasure_comp_add_right`); this needs no differentiability, by
the chain rule for translations of arbitrary maps
(`TauCeti.SmoothTwoForm.perturbedMFDeriv_comp_add_right`). The *center* of a cylinder of finite
nonzero energy is the arctan center of its strip energy measure
(`MeasureTheory.Measure.arctanCenter`), so it is translation equivariant
(`TauCeti.SmoothTwoForm.arctanCenter_stripEnergyMeasure_cylindrical_comp_add_right`). Hence every
translation orbit of a nonstationary finite-energy Floer cylinder contains exactly one cylinder of
center zero
(`IsNondegenerate.existsUnique_arctanCenter_stripEnergyMeasure_comp_add_right_eq_zero_of_floer`),
and recentering is constant on orbits
(`TauCeti.SmoothTwoForm.comp_add_arctanCenter_stripEnergyMeasure_comp_add_right`). For a constant
form on a vector space the strip energy measure is that of the vector-space theory
(`TauCeti.SymplecticForm.stripEnergyMeasure_constSmooth`).

**Continuity.** Let cylinders `u i` converge to `u₀` in the sense that their energy densities
converge almost everywhere on the strip, as they do under `C¹` convergence on compact sets, and
suppose that no energy is lost in the limit: the energies of `u i` converge to the energy of `u₀`,
which is nonzero. Then the centers of `u i` converge to the center of `u₀`
(`TauCeti.SmoothTwoForm.tendsto_arctanCenter_stripEnergyMeasure`). By Scheffé's lemma the energy
densities converge in `L¹`, so the strip energy measures converge weakly
(`MeasureTheory.FiniteMeasure.tendsto_of_ae_tendsto_of_tendsto_integral`), and the arctan center
is continuous for weak convergence (`MeasureTheory.FiniteMeasure.tendsto_arctanCenter`). This is
the continuity of the slice on the part of the space of cylinders where convergence loses no
energy; along a sequence which breaks, part of the energy escapes along the ends and the
hypothesis fails. The vector-space case is
`TauCeti.SymplecticForm.tendsto_arctanCenter_stripEnergyMeasure`.

The statements concern classical solutions; no Sobolev completion of the space of cylinders is
considered.

## Main definitions

* `TauCeti.SmoothTwoForm.stripEnergyMeasure`: the strip energy measure of a map into a manifold.

## Main results

* `TauCeti.SmoothTwoForm.stripEnergyMeasure_comp_add_right`: translating the cylinder translates
  its strip energy measure.
* `TauCeti.SmoothTwoForm.arctanCenter_stripEnergyMeasure_cylindrical_comp_add_right`: the center
  is translation equivariant.
* `IsNondegenerate.existsUnique_arctanCenter_stripEnergyMeasure_comp_add_right_eq_zero_of_floer`:
  each translation orbit of a nonstationary finite-energy Floer cylinder meets the slice of center
  zero exactly once.
* `TauCeti.SmoothTwoForm.tendsto_arctanCenter_stripEnergyMeasure`: the center is continuous along
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

open Filter Function MeasureTheory Set Topology
open scoped Manifold

namespace TauCeti.SmoothTwoForm

variable {E HM M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace HM]
  {I : ModelWithCorners ℝ E HM} [TopologicalSpace M] [ChartedSpace HM M]
  [IsManifold I (⊤ : ℕ∞) M]

/-! ### The strip energy measure -/

section Measure

variable (ω : SmoothTwoForm I M) (Ks Kt : ℝ × ℝ → M → ℝ) (u : ℝ × ℝ → M)

/-- The *strip energy measure* of a map `u` of the strip `ℝ × [0, 1]` into a manifold: the measure
on `ℝ` giving each set `A` of `s`-values the Floer energy of `u` over `A × [0, 1]` for the
perturbation data `Ks`, `Kt` (`TauCeti.SmoothTwoForm.stripEnergyMeasure_apply`). It is the
pushforward to the `s`-axis of the energy density on the strip. -/
def stripEnergyMeasure : Measure ℝ :=
  ((volume.restrict ((univ : Set ℝ) ×ˢ Icc (0 : ℝ) 1)).withDensity fun z ↦
    ENNReal.ofReal (ω.floerEnergyDensity Ks Kt u z)).map Prod.fst

/-- The strip energy measure is the pushforward to the `s`-axis of the measure with density the
positive part of the energy density on the strip. -/
theorem stripEnergyMeasure_def :
    ω.stripEnergyMeasure Ks Kt u =
      ((volume.restrict ((univ : Set ℝ) ×ˢ Icc (0 : ℝ) 1)).withDensity fun z ↦
        ENNReal.ofReal (ω.floerEnergyDensity Ks Kt u z)).map Prod.fst :=
  (rfl)

/-- The strip energy measure of a measurable set `A` is the energy over `A × [0, 1]`. -/
theorem stripEnergyMeasure_apply {A : Set ℝ} (hA : MeasurableSet A) :
    ω.stripEnergyMeasure Ks Kt u A =
      ∫⁻ z in A ×ˢ Icc 0 1, ENNReal.ofReal (ω.floerEnergyDensity Ks Kt u z) := by
  rw [stripEnergyMeasure_def, Measure.map_apply measurable_fst hA,
    withDensity_apply _ (measurable_fst hA), Measure.restrict_restrict (measurable_fst hA),
    ← prod_univ, prod_inter_prod, inter_univ, univ_inter]

/-- The total mass of the strip energy measure is the energy over the strip. -/
theorem stripEnergyMeasure_univ :
    ω.stripEnergyMeasure Ks Kt u univ =
      ∫⁻ z in (univ : Set ℝ) ×ˢ Icc 0 1, ENNReal.ofReal (ω.floerEnergyDensity Ks Kt u z) :=
  ω.stripEnergyMeasure_apply Ks Kt u MeasurableSet.univ

variable {ω Ks Kt u}

/-- The strip energy measure of a map of finite energy is finite. -/
theorem isFiniteMeasure_stripEnergyMeasure
    (hfin : ∫⁻ z in (univ : Set ℝ) ×ˢ Icc 0 1,
      ENNReal.ofReal (ω.floerEnergyDensity Ks Kt u z) ≠ ⊤) :
    IsFiniteMeasure (ω.stripEnergyMeasure Ks Kt u) :=
  ⟨by rw [stripEnergyMeasure_univ]; exact hfin.lt_top⟩

/-- The strip energy measure vanishes exactly when the energy over the strip does. -/
theorem stripEnergyMeasure_eq_zero_iff :
    ω.stripEnergyMeasure Ks Kt u = 0 ↔
      ∫⁻ z in (univ : Set ℝ) ×ˢ Icc 0 1, ENNReal.ofReal (ω.floerEnergyDensity Ks Kt u z) = 0 := by
  rw [← Measure.measure_univ_eq_zero, stripEnergyMeasure_univ]

variable (ω Ks Kt u)

/-- **Translations translate the strip energy measure.** Translating a map and its perturbation
data by `(c, 0)` translates its strip energy measure by `-c`. -/
theorem stripEnergyMeasure_comp_add_right (c : ℝ) :
    ω.stripEnergyMeasure (fun w ↦ Ks (w + (c, 0))) (fun w ↦ Kt (w + (c, 0)))
        (fun w ↦ u (w + (c, 0))) =
      (ω.stripEnergyMeasure Ks Kt u).map (· - c) := by
  ext A hA
  have hpre : A ×ˢ Icc (0 : ℝ) 1 = (· + (c, 0)) ⁻¹' (((· - c) ⁻¹' A) ×ˢ Icc 0 1) := by
    ext z
    simp
  rw [Measure.map_apply (measurable_sub_const c) hA, stripEnergyMeasure_apply _ _ _ _ hA,
    stripEnergyMeasure_apply _ _ _ _ (measurable_sub_const c hA), hpre,
    lintegral_floerEnergyDensity_comp_add_right]

/-- For the cylindrical perturbation `K = H_t dt`, translating the map by `(c, 0)` translates its
strip energy measure by `-c`. -/
theorem stripEnergyMeasure_cylindrical_comp_add_right (H : ℝ → M → ℝ) (c : ℝ) :
    ω.stripEnergyMeasure (fun _ _ ↦ 0) (fun w ↦ H w.2) (fun w ↦ u (w + (c, 0))) =
      (ω.stripEnergyMeasure (fun _ _ ↦ 0) (fun w ↦ H w.2) u).map (· - c) := by
  simpa using ω.stripEnergyMeasure_comp_add_right (fun _ _ ↦ 0) (fun w ↦ H w.2) u c

end Measure

/-! ### The slice -/

section Slice

variable {ω : SmoothTwoForm I M} {H : ℝ → M → ℝ} {u : ℝ × ℝ → M}

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

/-- **The slice for nonstationary Floer cylinders in a manifold.** Let `H` be a jointly `C¹`
time-dependent Hamiltonian and `u` a `C¹` map solving the Floer equation for the cylindrical
perturbation `K = H_t dt` on the strip `ℝ × [0, 1]`, for almost complex structures `J z` tamed by
`ω`. If `u` has finite energy and is not stationary, exactly one translate
`(s, t) ↦ u(s + c, t)` of `u` has strip energy measure of arctan center `0`. -/
theorem IsNondegenerate.existsUnique_arctanCenter_stripEnergyMeasure_comp_add_right_eq_zero_of_floer
    [FiniteDimensional ℝ E] (hω : ω.IsNondegenerate)
    {J : (z : ℝ × ℝ) → AlmostComplexStructure (TangentSpace I (u z))}
    (hH : ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) 1 (uncurry H)) (hu : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 1 u)
    (hJ : ∀ z ∈ (univ : Set ℝ) ×ˢ Icc 0 1, (hω.symplecticFormAt (u z)).Tames (J z))
    (hfloer : ∀ z ∈ (univ : Set ℝ) ×ˢ Icc 0 1, mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal +
      J z (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag -
        ω.hamiltonianVectorField (H z.2) (u z)) = 0)
    (hfin : ∫⁻ z in (univ : Set ℝ) ×ˢ Icc 0 1,
      ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) u z) ≠ ⊤)
    (hns : ∃ s, ∃ t ∈ Icc (0 : ℝ) 1, u (s, t) ≠ u (0, t)) :
    ∃! c : ℝ,
      (ω.stripEnergyMeasure (fun _ _ ↦ 0) (fun w ↦ H w.2) fun w ↦ u (w + (c, 0))).arctanCenter =
        0 := by
  refine existsUnique_arctanCenter_stripEnergyMeasure_comp_add_right_eq_zero hfin fun hE ↦ ?_
  obtain ⟨s, t, ht, hne⟩ := hns
  exact hne ((hω.lintegral_floerEnergyDensity_eq_zero_iff hH hu hJ hfloer).1 hE s t ht)

/-- **Recentering is constant on translation orbits.** For the cylindrical perturbation
`K = H_t dt` and a map `u` of finite nonzero energy over the strip, translate any translate
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

/-! ### Continuity of the center -/

section Continuity

variable {ω : SmoothTwoForm I M} {Ks Kt : ℝ × ℝ → M → ℝ} {ι : Type*} {l : Filter ι}
  [l.IsCountablyGenerated] {u : ι → ℝ × ℝ → M} {u₀ : ℝ × ℝ → M}

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
  let μ (v : ℝ × ℝ → M) (hv : IntegrableOn (ω.floerEnergyDensity Ks Kt v) S) :
      FiniteMeasure (ℝ × ℝ) :=
    ⟨(volume.restrict S).withDensity fun z ↦ ENNReal.ofReal (ω.floerEnergyDensity Ks Kt v z),
      isFiniteMeasure_withDensity_ofReal hv.hasFiniteIntegral⟩
  -- Their pushforwards to the `s`-axis are the strip energy measures.
  have hμ (v : ℝ × ℝ → M) (hv : IntegrableOn (ω.floerEnergyDensity Ks Kt v) S) :
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

end TauCeti.SmoothTwoForm

namespace TauCeti.SymplecticForm

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- For a constant form on a vector space, the strip energy measure of the manifold theory is the
strip energy measure of the vector-space theory. -/
@[simp]
theorem stripEnergyMeasure_constSmooth (ω : SymplecticForm V) (Ks Kt : ℝ × ℝ → V → ℝ)
    (u : ℝ × ℝ → V) :
    ω.constSmooth.stripEnergyMeasure Ks Kt u = ω.stripEnergyMeasure Ks Kt u := by
  ext A hA
  rw [SmoothTwoForm.stripEnergyMeasure_apply _ _ _ _ hA, stripEnergyMeasure_apply _ _ _ _ hA]
  simp only [floerEnergyDensity_constSmooth]

/-- **Continuity of the energy center, for a vector-space target.** If the energy densities of maps
`u i` of the strip `ℝ × [0, 1]` into a symplectic vector space are integrable, nonnegative almost
everywhere and converge almost everywhere on the strip to the integrable energy density of `u₀`,
and the energies of `u i` converge to the nonzero energy of `u₀`, then the arctan centers of the
strip energy measures of `u i` converge to that of `u₀`. This is the constant-form case of
`TauCeti.SmoothTwoForm.tendsto_arctanCenter_stripEnergyMeasure`. -/
theorem tendsto_arctanCenter_stripEnergyMeasure {ω : SymplecticForm V} {Ks Kt : ℝ × ℝ → V → ℝ}
    {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated] {u : ι → ℝ × ℝ → V} {u₀ : ℝ × ℝ → V}
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
  have he (v : ℝ × ℝ → V) :
      ω.constSmooth.floerEnergyDensity Ks Kt v = ω.floerEnergyDensity Ks Kt v :=
    funext (floerEnergyDensity_constSmooth ω Ks Kt v)
  simp_rw [← stripEnergyMeasure_constSmooth]
  exact SmoothTwoForm.tendsto_arctanCenter_stripEnergyMeasure (by simpa only [he] using hint)
    (by simpa only [he] using hint₀) (by simpa only [he] using hnonneg)
    (by simpa only [he] using hlim) (by simpa only [he] using henergy)
    (by simpa only [he] using hE)

end TauCeti.SymplecticForm
