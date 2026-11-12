/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Rotation
public import TauCeti.Geometry.Symplectic.Floer.Stationary
public import TauCeti.MeasureTheory.Measure.ArctanCenter

/-!
# A slice for the translation action on Floer cylinders in a manifold

Let `ω` be a two-form on a manifold `M`, such as the symplectic form of a closed symplectic
manifold. Floer cylinders `u : ℝ × [0, 1] → M`, solutions of `∂_s u + J (∂_t u - X_{H_t}(u)) = 0`
for the cylindrical perturbation `K = H_t dt`, are counted up to the translations
`(s, t) ↦ (s + c, t)`. Away from the stationary cylinders this action of `ℝ` is free
(`SmoothTwoForm.IsNondegenerate.eq_zero_of_lintegral_floerEnergyDensity_ne_top_of_periodic`).
This file constructs a global slice for it: a translation-equivariant real-valued *center* of a
cylinder, whose zero set meets every orbit of nonstationary finite-energy cylinders exactly once.
It is the manifold-target counterpart of `TauCeti.Geometry.Symplectic.Floer.Translation.Slice`.

The center is read off from the energy. The *strip energy measure*
`TauCeti.SmoothTwoForm.stripEnergyMeasure ω Ks Kt u` is the measure on `ℝ` giving each set `A`
of `s`-values the Floer energy of `u` over `A × [0, 1]` (`SmoothTwoForm.stripEnergyMeasure_apply`).
Its total mass is the energy of `u` over the strip, so it is finite and nonzero exactly for a
finite-energy cylinder of nonzero energy; for a solution of the Floer equation with tamed almost
complex structures, nonzero energy means not stationary
(`TauCeti.SmoothTwoForm.IsNondegenerate.lintegral_floerEnergyDensity_eq_zero_iff`). For a
differentiable map, translating `u` and its perturbation data by `(c, 0)` translates this measure
by `-c` (`TauCeti.SmoothTwoForm.stripEnergyMeasure_comp_add_right`), because the energy density of
the translate is the translate of the energy density
(`TauCeti.SmoothTwoForm.floerEnergyDensity_comp_add_right`). The center of `u` is the arctan
center of its strip energy measure (`MeasureTheory.Measure.arctanCenter`), the unique `m` with
`∫ arctan (s - m) dE(s) = 0`. It is therefore equivariant: the center of the translate of `u` by
`(c, 0)` is the center of `u` minus `c`
(`TauCeti.SmoothTwoForm.arctanCenter_stripEnergyMeasure_cylindrical_comp_add_right`). Hence:

* each orbit contains exactly one cylinder of center zero, the translate of `u` by its center
  (`TauCeti.SmoothTwoForm.existsUnique_arctanCenter_stripEnergyMeasure_comp_add_right_eq_zero`,
  and its Floer form `IsNondegenerate.existsUnique_..._eq_zero_of_floer` for nonstationary
  solutions);
* recentering a translate of `u` gives the recentered `u` itself
  (`TauCeti.SmoothTwoForm.comp_add_arctanCenter_stripEnergyMeasure_comp_add_right`), so
  recentering is a well-defined section of the quotient by translations.

The center is continuous along cylinders `u i → u₀` whose energy densities converge almost
everywhere on the strip, provided no energy is lost in the limit and the energy of `u₀` is nonzero
(`TauCeti.SmoothTwoForm.tendsto_arctanCenter_stripEnergyMeasure`, from
`MeasureTheory.Measure.tendsto_arctanCenter_map_withDensity`). The energy densities converge at
every point where the derivatives of `u i` converge in the tangent bundle to those of `u₀`
(`TauCeti.SmoothTwoForm.tendsto_floerEnergyDensity`), so the centers converge along cylinders
converging in `C¹` almost everywhere without loss of energy
(`TauCeti.SmoothTwoForm.tendsto_arctanCenter_stripEnergyMeasure_of_tendsto_mfderiv`). Along a
sequence which breaks, part of the energy escapes along the ends and this hypothesis fails.

No Sobolev completion of the space of cylinders is considered: the statements are about the
action of `ℝ` on classical solutions.

## Main definitions

* `TauCeti.SmoothTwoForm.stripEnergyMeasure`: the strip energy measure of a map of the strip into
  a manifold.

## Main results

* `TauCeti.SmoothTwoForm.stripEnergyMeasure_comp_add_right`: translating a differentiable map
  translates its strip energy measure.
* `TauCeti.SmoothTwoForm.arctanCenter_stripEnergyMeasure_cylindrical_comp_add_right`: the center
  is translation equivariant.
* `IsNondegenerate.existsUnique_arctanCenter_stripEnergyMeasure_comp_add_right_eq_zero_of_floer`:
  each translation orbit of a nonstationary finite-energy Floer cylinder meets the slice of center
  zero exactly once.
* `TauCeti.SmoothTwoForm.tendsto_arctanCenter_stripEnergyMeasure`,
  `TauCeti.SmoothTwoForm.tendsto_arctanCenter_stripEnergyMeasure_of_tendsto_mfderiv`: the center
  is continuous along cylinders whose energy densities, or derivatives, converge without loss of
  energy.

## References

* A. Floer, *Symplectic fixed points and holomorphic spheres*, Comm. Math. Phys. **120** (1989),
  575–611, on the translation action on connecting trajectories.
* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), Lecture 1, on moduli spaces of Floer cylinders modulo translation.
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
  rw [stripEnergyMeasure, Measure.map_apply measurable_fst hA,
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

/-- **Translations preserve the energy.** For a differentiable map `u`, the energy of the translate
`w ↦ u (w + v)` for the translated data over the preimage of `S` under `· + v` is the energy of `u`
over `S`. -/
theorem lintegral_floerEnergyDensity_comp_add_right (hu : MDifferentiable 𝓘(ℝ, ℝ × ℝ) I u)
    (v : ℝ × ℝ) (S : Set (ℝ × ℝ)) :
    ∫⁻ z in (· + v) ⁻¹' S, ENNReal.ofReal
        (ω.floerEnergyDensity (fun w ↦ Ks (w + v)) (fun w ↦ Kt (w + v)) (fun w ↦ u (w + v)) z) =
      ∫⁻ z in S, ENNReal.ofReal (ω.floerEnergyDensity Ks Kt u z) := by
  have hv : MeasurePreserving (· + v) volume volume :=
    (measurePreserving_add_right volume v.1).prod (measurePreserving_add_right volume v.2)
  simp only [fun z ↦ ω.floerEnergyDensity_comp_add_right Ks Kt (hu (z + v))]
  exact hv.setLIntegral_comp_preimage_emb (measurableEmbedding_addRight v)
    (fun z ↦ ENNReal.ofReal (ω.floerEnergyDensity Ks Kt u z)) S

/-- **Translations translate the strip energy measure.** Translating a differentiable map and its
perturbation data by `(c, 0)` translates its strip energy measure by `-c`. -/
theorem stripEnergyMeasure_comp_add_right (hu : MDifferentiable 𝓘(ℝ, ℝ × ℝ) I u) (c : ℝ) :
    ω.stripEnergyMeasure (fun w ↦ Ks (w + (c, 0))) (fun w ↦ Kt (w + (c, 0)))
        (fun w ↦ u (w + (c, 0))) =
      (ω.stripEnergyMeasure Ks Kt u).map (· - c) := by
  ext A hA
  have hpre : A ×ˢ Icc (0 : ℝ) 1 = (· + (c, 0)) ⁻¹' (((· - c) ⁻¹' A) ×ˢ Icc 0 1) := by
    ext z
    simp
  rw [Measure.map_apply (measurable_sub_const c) hA, stripEnergyMeasure_apply _ _ _ _ hA,
    stripEnergyMeasure_apply _ _ _ _ (measurable_sub_const c hA), hpre,
    lintegral_floerEnergyDensity_comp_add_right hu]

/-- For the cylindrical perturbation `K = H_t dt`, translating a differentiable map by `(c, 0)`
translates its strip energy measure by `-c`. -/
theorem stripEnergyMeasure_cylindrical_comp_add_right {H : ℝ → M → ℝ}
    (hu : MDifferentiable 𝓘(ℝ, ℝ × ℝ) I u) (c : ℝ) :
    ω.stripEnergyMeasure (fun _ _ ↦ 0) (fun w ↦ H w.2) (fun w ↦ u (w + (c, 0))) =
      (ω.stripEnergyMeasure (fun _ _ ↦ 0) (fun w ↦ H w.2) u).map (· - c) := by
  simpa using stripEnergyMeasure_comp_add_right (Ks := fun _ _ ↦ 0) (Kt := fun w ↦ H w.2) hu c

end Measure

/-! ### The slice -/

section Slice

variable {ω : SmoothTwoForm I M} {H : ℝ → M → ℝ} {u : ℝ × ℝ → M}

/-- **Translation equivariance of the energy center.** For the cylindrical perturbation
`K = H_t dt` and a differentiable map `u` of finite nonzero energy over the strip, the arctan
center of the strip energy measure of the translate `(s, t) ↦ u(s + c, t)` is that of `u` minus
`c`. -/
theorem arctanCenter_stripEnergyMeasure_cylindrical_comp_add_right
    (hu : MDifferentiable 𝓘(ℝ, ℝ × ℝ) I u)
    (hfin : ∫⁻ z in (univ : Set ℝ) ×ˢ Icc 0 1,
      ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) u z) ≠ ⊤)
    (hE : ∫⁻ z in (univ : Set ℝ) ×ˢ Icc 0 1,
      ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) u z) ≠ 0) (c : ℝ) :
    (ω.stripEnergyMeasure (fun _ _ ↦ 0) (fun w ↦ H w.2) fun w ↦ u (w + (c, 0))).arctanCenter =
      (ω.stripEnergyMeasure (fun _ _ ↦ 0) (fun w ↦ H w.2) u).arctanCenter - c := by
  have := isFiniteMeasure_stripEnergyMeasure hfin
  have : NeZero (ω.stripEnergyMeasure (fun _ _ ↦ 0) (fun w ↦ H w.2) u) :=
    ⟨fun h ↦ hE (stripEnergyMeasure_eq_zero_iff.1 h)⟩
  simp_rw [stripEnergyMeasure_cylindrical_comp_add_right hu, sub_eq_add_neg,
    Measure.arctanCenter_map_add]

/-- **Each translation orbit meets the slice once.** For the cylindrical perturbation `K = H_t dt`
and a differentiable map `u` of finite nonzero energy over the strip, there is exactly one
translation `(s, t) ↦ (s + c, t)` after which the arctan center of the strip energy measure is
`0`; it is translation by the center of `u`. -/
theorem existsUnique_arctanCenter_stripEnergyMeasure_comp_add_right_eq_zero
    (hu : MDifferentiable 𝓘(ℝ, ℝ × ℝ) I u)
    (hfin : ∫⁻ z in (univ : Set ℝ) ×ˢ Icc 0 1,
      ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) u z) ≠ ⊤)
    (hE : ∫⁻ z in (univ : Set ℝ) ×ˢ Icc 0 1,
      ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) u z) ≠ 0) :
    ∃! c : ℝ,
      (ω.stripEnergyMeasure (fun _ _ ↦ 0) (fun w ↦ H w.2) fun w ↦ u (w + (c, 0))).arctanCenter =
        0 := by
  simp_rw [arctanCenter_stripEnergyMeasure_cylindrical_comp_add_right hu hfin hE, sub_eq_zero]
  exact ⟨_, rfl, fun _ h ↦ h.symm⟩

/-- **The slice for nonstationary Floer cylinders.** Let `ω` be nondegenerate on a
finite-dimensional manifold, let `H` be a jointly `C¹` time-dependent Hamiltonian, and let `u` be a
`C¹` map solving the Floer equation for the cylindrical perturbation `K = H_t dt` on the strip
`ℝ × [0, 1]`, for almost complex structures `J z` tamed by `ω`. If `u` has finite energy and is not
stationary, then exactly one translate `(s, t) ↦ u(s + c, t)` of `u` has strip energy measure of
arctan center `0`. -/
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
  refine existsUnique_arctanCenter_stripEnergyMeasure_comp_add_right_eq_zero
    (hu.mdifferentiable one_ne_zero) hfin fun hE ↦ ?_
  obtain ⟨s, t, ht, hne⟩ := hns
  exact hne ((hω.lintegral_floerEnergyDensity_eq_zero_iff hH hu hJ hfloer).1 hE s t ht)

/-- **Recentering is constant on translation orbits.** For the cylindrical perturbation
`K = H_t dt` and a differentiable map `u` of finite nonzero energy over the strip, translate any
translate `v = u(· + (c, 0))` of `u` by the arctan center of its strip energy measure: the result
is the translate of `u` by its own center. So recentering is a section of the quotient by
translations, with values in the slice of center zero. -/
theorem comp_add_arctanCenter_stripEnergyMeasure_comp_add_right
    (hu : MDifferentiable 𝓘(ℝ, ℝ × ℝ) I u)
    (hfin : ∫⁻ z in (univ : Set ℝ) ×ˢ Icc 0 1,
      ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) u z) ≠ ⊤)
    (hE : ∫⁻ z in (univ : Set ℝ) ×ˢ Icc 0 1,
      ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) u z) ≠ 0) (c : ℝ) :
    (fun w ↦ u (w + ((ω.stripEnergyMeasure (fun _ _ ↦ 0) (fun w ↦ H w.2)
        fun w ↦ u (w + (c, 0))).arctanCenter, 0) + (c, 0))) =
      fun w ↦ u (w + ((ω.stripEnergyMeasure (fun _ _ ↦ 0) (fun w ↦ H w.2) u).arctanCenter, 0)) := by
  rw [arctanCenter_stripEnergyMeasure_cylindrical_comp_add_right hu hfin hE]
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
  simp only [stripEnergyMeasure_def]
  exact Measure.tendsto_arctanCenter_map_withDensity continuous_fst hint hint₀ hnonneg hlim henergy
    hE

/-- **Continuity of the energy center under `C¹` convergence.** Let the Hamiltonian vector fields
of the perturbation `K = K_s ds + K_t dt` be continuous into the tangent bundle, and let maps `u i`
of the strip `ℝ × [0, 1]` with integrable energy densities, nonnegative almost everywhere,
converge to a map `u₀` with integrable energy density, in the sense that at almost every point `z`
of the strip the derivatives of `u i` at `z` converge in the tangent bundle to the derivative of
`u₀` at `z`. If no energy is lost in the limit and the energy of `u₀` is nonzero, then the arctan
centers of the strip energy measures of `u i` converge to that of `u₀`. -/
theorem tendsto_arctanCenter_stripEnergyMeasure_of_tendsto_mfderiv
    (hXs : Continuous (fun p : (ℝ × ℝ) × M ↦
      (⟨p.2, ω.hamiltonianVectorField (Ks p.1) p.2⟩ : TangentBundle I M)))
    (hXt : Continuous (fun p : (ℝ × ℝ) × M ↦
      (⟨p.2, ω.hamiltonianVectorField (Kt p.1) p.2⟩ : TangentBundle I M)))
    (hint : ∀ i, IntegrableOn (ω.floerEnergyDensity Ks Kt (u i)) ((univ : Set ℝ) ×ˢ Icc 0 1))
    (hint₀ : IntegrableOn (ω.floerEnergyDensity Ks Kt u₀) ((univ : Set ℝ) ×ˢ Icc 0 1))
    (hnonneg : ∀ i, 0 ≤ᵐ[volume.restrict ((univ : Set ℝ) ×ˢ Icc 0 1)]
      ω.floerEnergyDensity Ks Kt (u i))
    (hD : ∀ᵐ z ∂volume.restrict ((univ : Set ℝ) ×ˢ Icc 0 1), ∀ e,
      Tendsto (fun i ↦ (⟨u i z, mfderiv 𝓘(ℝ, ℝ × ℝ) I (u i) z e⟩ : TangentBundle I M)) l
        (𝓝 ⟨u₀ z, mfderiv 𝓘(ℝ, ℝ × ℝ) I u₀ z e⟩))
    (henergy : Tendsto
      (fun i ↦ ∫ z in (univ : Set ℝ) ×ˢ Icc 0 1, ω.floerEnergyDensity Ks Kt (u i) z) l
      (𝓝 (∫ z in (univ : Set ℝ) ×ˢ Icc 0 1, ω.floerEnergyDensity Ks Kt u₀ z)))
    (hE : ∫ z in (univ : Set ℝ) ×ˢ Icc 0 1, ω.floerEnergyDensity Ks Kt u₀ z ≠ 0) :
    Tendsto (fun i ↦ (ω.stripEnergyMeasure Ks Kt (u i)).arctanCenter) l
      (𝓝 (ω.stripEnergyMeasure Ks Kt u₀).arctanCenter) :=
  tendsto_arctanCenter_stripEnergyMeasure hint hint₀ hnonneg
    (hD.mono fun _ hz ↦ ω.tendsto_floerEnergyDensity tendsto_const_nhds hz hXs.continuousAt
      hXt.continuousAt) henergy hE

end Continuity

end TauCeti.SmoothTwoForm
