/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Alternating.Basic
public import Mathlib.Topology.Semicontinuity.Basic
public import TauCeti.Analysis.Distribution.TestFunction.NormDuality
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-!
# Mass of functionals on vector-valued test functions

For a map `f : 𝓓^{n}(Ω, F) → V` from `F`-valued test functions on an open set `Ω` of a real
normed space `E` to a real normed space `V`, the *mass* is the extended supremum

`mass f = ⨆ { ‖f φ‖ₑ | φ ∈ 𝓓^{n}(Ω, F), ‖φ x‖ ≤ 1 for all x }`,

and the *local mass* `localMass f U` takes the same supremum over the tests supported in `U`.
With `F = E [⋀^Fin k]→L[ℝ] ℝ` and `V = ℝ`, a continuous linear `f` is a Euclidean `k`-current on
`Ω`, the pointwise norm of a test form is the operator norm of the alternating map, and `mass f`
is the extended mass of the current; it is often infinite. A current has *locally finite mass*
when it satisfies an order-zero bound on the tests supported in each compact subset of `Ω`.

## Main declarations

* `Distribution.mass`, `Distribution.localMass`: the extended mass and local mass.
* `Distribution.enorm_apply_le_localMass_mul`: for linear `T`,
  `‖T φ‖ₑ ≤ localMass T U * ‖φ‖_∞` when `φ` is supported in `U`.
* `Distribution.mass_eq_zero_iff`: a linear map has mass zero exactly when it vanishes.
* `Distribution.mass_add_le`, `Distribution.mass_smul`: the triangle inequality and homogeneity.
* `Distribution.lowerSemicontinuous_mass`: mass is lower semicontinuous for pointwise
  (weak) convergence; `Distribution.mass_le_liminf` is the corresponding `liminf` bound.
* `Distribution.mass_comp_monoCLM`: the mass of the restriction to an open `Ω' ⊆ Ω` is the local
  mass on `Ω'`.
* `Distribution.HasLocallyFiniteMass` and
  `Distribution.hasLocallyFiniteMass_iff_localMass_ne_top`: local finiteness of mass by order-zero
  bounds and its variational characterization.
* `Distribution.mass_apply_apply`: the point evaluation `φ ↦ ℓ (φ x)` has mass `‖ℓ‖`; in particular
  the degree-zero point current has mass one (`Distribution.mass_apply_finZero`).
* `Distribution.mass_integral_apply`: integration against a locally integrable field `G` has mass
  `∫_Ω ‖G‖`.

## References

* H. Federer, *Geometric Measure Theory*, §4.1.7 (the mass of a current).
* L. Simon, *Introduction to Geometric Measure Theory*, Chapter 6, §2 (currents and their mass).
-/

public section

noncomputable section

open MeasureTheory TopologicalSpace Filter Set
open scoped BoundedContinuousFunction ENNReal Distributions Topology

namespace Distribution

variable {E F V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup V]
  {Ω : Opens E} {n : ℕ∞}

section Defs

/-- The local mass of `f` on a set `U`: the supremum of `‖f φ‖ₑ` over the tests `φ` supported in
`U` with `‖φ x‖ ≤ 1` everywhere. -/
def localMass (f : 𝓓^{n}(Ω, F) → V) (U : Set E) : ℝ≥0∞ :=
  ⨆ (φ : 𝓓^{n}(Ω, F)) (_ : tsupport φ ⊆ U) (_ : ∀ x, ‖φ x‖ ≤ 1), ‖f φ‖ₑ

/-- The (extended) mass of `f`: the supremum of `‖f φ‖ₑ` over the tests `φ` with `‖φ x‖ ≤ 1`
everywhere. For a Euclidean current this is its mass; it may be infinite. -/
def mass (f : 𝓓^{n}(Ω, F) → V) : ℝ≥0∞ :=
  ⨆ (φ : 𝓓^{n}(Ω, F)) (_ : ∀ x, ‖φ x‖ ≤ 1), ‖f φ‖ₑ

end Defs

variable {f g : 𝓓^{n}(Ω, F) → V} {U U' : Set E} {φ : 𝓓^{n}(Ω, F)} {c : ℝ≥0∞}

section Basic

theorem enorm_le_localMass (hφU : tsupport φ ⊆ U) (hφ : ∀ x, ‖φ x‖ ≤ 1) :
    ‖f φ‖ₑ ≤ localMass f U :=
  le_iSup₂_of_le φ hφU <| le_iSup_of_le hφ le_rfl

theorem enorm_le_mass (hφ : ∀ x, ‖φ x‖ ≤ 1) : ‖f φ‖ₑ ≤ mass f :=
  le_iSup₂_of_le φ hφ le_rfl

theorem localMass_le_iff :
    localMass f U ≤ c ↔ ∀ φ : 𝓓^{n}(Ω, F), tsupport φ ⊆ U → (∀ x, ‖φ x‖ ≤ 1) → ‖f φ‖ₑ ≤ c := by
  simp only [localMass, iSup_le_iff]

theorem mass_le_iff : mass f ≤ c ↔ ∀ φ : 𝓓^{n}(Ω, F), (∀ x, ‖φ x‖ ≤ 1) → ‖f φ‖ₑ ≤ c := by
  simp only [mass, iSup_le_iff]

/-- The local mass on any set containing `Ω` is the mass. -/
theorem localMass_eq_mass_of_subset (h : (Ω : Set E) ⊆ U) : localMass f U = mass f :=
  le_antisymm (localMass_le_iff.2 fun _ _ hφ => enorm_le_mass hφ)
    (mass_le_iff.2 fun φ hφ => enorm_le_localMass (φ.tsupport_subset.trans h) hφ)

@[simp]
theorem localMass_univ : localMass f univ = mass f :=
  localMass_eq_mass_of_subset (subset_univ _)

@[gcongr]
theorem localMass_mono (h : U ⊆ U') : localMass f U ≤ localMass f U' :=
  localMass_le_iff.2 fun _ hφU hφ => enorm_le_localMass (hφU.trans h) hφ

theorem localMass_le_mass : localMass f U ≤ mass f :=
  localMass_univ (f := f) ▸ localMass_mono (subset_univ U)

@[simp]
theorem localMass_zero : localMass (0 : 𝓓^{n}(Ω, F) → V) U = 0 := by
  simp [localMass]

@[simp]
theorem mass_zero : mass (0 : 𝓓^{n}(Ω, F) → V) = 0 := by
  simp [mass]

theorem localMass_add_le : localMass (f + g) U ≤ localMass f U + localMass g U :=
  localMass_le_iff.2 fun _ hφU hφ => (enorm_add_le _ _).trans <|
    add_le_add (enorm_le_localMass hφU hφ) (enorm_le_localMass hφU hφ)

theorem mass_add_le : mass (f + g) ≤ mass f + mass g := by
  simpa using localMass_add_le (f := f) (g := g) (U := univ)

theorem localMass_smul [NormedSpace ℝ V] (a : ℝ) : localMass (a • f) U = ‖a‖ₑ * localMass f U := by
  simp only [localMass, ENNReal.mul_iSup, Pi.smul_apply, enorm_smul]

theorem mass_smul [NormedSpace ℝ V] (a : ℝ) : mass (a • f) = ‖a‖ₑ * mass f := by
  simpa using localMass_smul (f := f) (U := univ) a

@[simp]
theorem localMass_neg : localMass (-f) U = localMass f U := by
  simp only [localMass, Pi.neg_apply, enorm_neg]

@[simp]
theorem mass_neg : mass (-f) = mass f := by
  simpa using localMass_neg (f := f) (U := univ)

theorem mass_sub_le : mass (f - g) ≤ mass f + mass g := by
  simpa [sub_eq_add_neg] using mass_add_le (f := f) (g := -g)

end Basic

section Linear

variable [NormedSpace ℝ V] {𝓕 : Type*} [FunLike 𝓕 𝓓^{n}(Ω, F) V] [LinearMapClass 𝓕 ℝ 𝓓^{n}(Ω, F) V]

/-- The mass bound: a linear map evaluated on a test supported in `U` is bounded by the local mass
on `U` times the supremum norm of the test. -/
theorem enorm_apply_le_localMass_mul (T : 𝓕) (hφU : tsupport φ ⊆ U) :
    ‖T φ‖ₑ ≤ localMass T U * ‖(φ : E →ᵇ F)‖ₑ := by
  set b := ‖(φ : E →ᵇ F)‖
  rcases (norm_nonneg (φ : E →ᵇ F)).eq_or_lt with hb | hb
  · have hφ0 : φ = 0 := TestFunction.ext fun x => by
      simpa using (BoundedContinuousFunction.norm_le le_rfl).1 hb.ge x
    simp [hφ0]
  -- The rescaled test `b⁻¹ • φ` has norm at most one and the same support.
  have hψU : tsupport (b⁻¹ • φ) ⊆ U := (tsupport_smul_subset_right _ _).trans hφU
  have hψ (x : E) : ‖(b⁻¹ • φ) x‖ ≤ 1 := by
    rw [smul_apply, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hb.le),
      inv_mul_le_one₀ hb]
    exact BoundedContinuousFunction.norm_coe_le_norm (φ : E →ᵇ F) x
  have hφ : φ = b • (b⁻¹ • φ) := by rw [smul_smul, mul_inv_cancel₀ hb.ne', one_smul]
  calc ‖T φ‖ₑ = ‖b‖ₑ * ‖T (b⁻¹ • φ)‖ₑ := by
        conv_lhs => rw [hφ]
        rw [map_smul, enorm_smul]
    _ ≤ ‖b‖ₑ * localMass T U := by gcongr; exact enorm_le_localMass hψU hψ
    _ = localMass T U * ‖(φ : E →ᵇ F)‖ₑ := by
        rw [mul_comm, Real.enorm_of_nonneg hb.le, ← ofReal_norm]

theorem enorm_apply_le_mass_mul (T : 𝓕) (φ : 𝓓^{n}(Ω, F)) :
    ‖T φ‖ₑ ≤ mass T * ‖(φ : E →ᵇ F)‖ₑ := by
  simpa using enorm_apply_le_localMass_mul T (subset_univ (tsupport φ))

/-- **Mass zero iff current zero.** -/
theorem mass_eq_zero_iff (T : 𝓕) : mass T = 0 ↔ ⇑T = 0 := by
  refine ⟨fun h => funext fun φ => ?_, fun h => h ▸ mass_zero⟩
  simpa [h] using enorm_apply_le_mass_mul T φ

end Linear

section Semicontinuity

/-- **Weak lower semicontinuity of local mass.** On the space of maps `𝓓^{n}(Ω, F) → V` with the
topology of pointwise convergence, the local mass on any set is lower semicontinuous. -/
theorem lowerSemicontinuous_localMass (U : Set E) :
    LowerSemicontinuous fun f : 𝓓^{n}(Ω, F) → V => localMass f U :=
  lowerSemicontinuous_biSup fun φ _ => lowerSemicontinuous_iSup fun _ =>
    (continuous_enorm.comp (continuous_apply φ)).lowerSemicontinuous

/-- **Weak lower semicontinuity of mass.** -/
theorem lowerSemicontinuous_mass :
    LowerSemicontinuous fun f : 𝓓^{n}(Ω, F) → V => mass f := by
  simpa using lowerSemicontinuous_localMass (Ω := Ω) (n := n) (F := F) (V := V) univ

/-- If `fᵢ φ → f φ` along `l` for every test `φ`, then `mass f ≤ liminf mass fᵢ`. -/
theorem mass_le_liminf {ι : Type*} {l : Filter ι} {fs : ι → 𝓓^{n}(Ω, F) → V}
    (h : ∀ φ, Tendsto (fun i => fs i φ) l (𝓝 (f φ))) :
    mass f ≤ liminf (fun i => mass (fs i)) l :=
  calc mass f ≤ liminf mass (𝓝 f) := LowerSemicontinuousAt.le_liminf (lowerSemicontinuous_mass f)
    _ ≤ liminf mass (map fs l) := liminf_le_liminf_of_le (tendsto_pi_nhds.2 h)
    _ = liminf (fun i => mass (fs i)) l := liminf_comp mass fs l |>.symm

end Semicontinuity

section Restriction

/-- **Restriction.** The mass of the restriction of `f` to tests on an open `Ω' ⊆ Ω` is the local
mass of `f` on `Ω'`. -/
theorem mass_comp_monoCLM {Ω' : Opens E} (h : Ω' ≤ Ω) :
    mass (f ∘ (TestFunction.monoCLM ℝ : 𝓓^{n}(Ω', F) →L[ℝ] 𝓓^{n}(Ω, F))) = localMass f Ω' := by
  set ι : 𝓓^{n}(Ω', F) →L[ℝ] 𝓓^{n}(Ω, F) := TestFunction.monoCLM ℝ
  have hι (ψ : 𝓓^{n}(Ω', F)) : ⇑(ι ψ) = ψ := by simp [ι, h]
  refine le_antisymm (mass_le_iff.2 fun ψ hψ => ?_) (localMass_le_iff.2 fun φ hφU hφ => ?_)
  · exact enorm_le_localMass (f := f) (φ := ι ψ) (by rw [hι]; exact ψ.tsupport_subset)
      (by simpa [hι] using hψ)
  · -- A test on `Ω` supported in `Ω'` is the image of a test on `Ω'`.
    let ψ : 𝓓^{n}(Ω', F) := ⟨φ, φ.contDiff, φ.hasCompactSupport, hφU⟩
    have hψ : ι ψ = φ := TestFunction.ext fun x => by simp [hι, ψ]
    simpa [hψ] using enorm_le_mass (f := f ∘ ι) (φ := ψ) hφ

end Restriction

section LocallyFinite

/-- A map on test functions has *locally finite mass* if it satisfies an order-zero bound on the
tests supported in each compact subset of `Ω`. -/
def HasLocallyFiniteMass (f : 𝓓^{n}(Ω, F) → V) : Prop :=
  ∀ K : Set E, IsCompact K → K ⊆ Ω → ∃ C : ℝ, 0 ≤ C ∧
    ∀ φ : 𝓓^{n}(Ω, F), tsupport φ ⊆ K → ‖f φ‖ ≤ C * ‖(φ : E →ᵇ F)‖

/-- Unfolding `HasLocallyFiniteMass` into its order-zero bounds on compact subsets of `Ω`. -/
theorem hasLocallyFiniteMass_def :
    HasLocallyFiniteMass f ↔ ∀ K : Set E, IsCompact K → K ⊆ Ω → ∃ C : ℝ, 0 ≤ C ∧
      ∀ φ : 𝓓^{n}(Ω, F), tsupport φ ⊆ K → ‖f φ‖ ≤ C * ‖(φ : E →ᵇ F)‖ :=
  Iff.rfl

theorem hasLocallyFiniteMass_zero : HasLocallyFiniteMass (0 : 𝓓^{n}(Ω, F) → V) :=
  fun _ _ _ => ⟨0, le_rfl, fun φ _ => by simp⟩

theorem HasLocallyFiniteMass.add (hf : HasLocallyFiniteMass f) (hg : HasLocallyFiniteMass g) :
    HasLocallyFiniteMass (f + g) := fun K hK hKΩ => by
  obtain ⟨C, hC, hfC⟩ := hf K hK hKΩ
  obtain ⟨D, hD, hgD⟩ := hg K hK hKΩ
  exact ⟨C + D, add_nonneg hC hD, fun φ hφ => (norm_add_le _ _).trans <| by
    rw [add_mul]; exact add_le_add (hfC φ hφ) (hgD φ hφ)⟩

theorem HasLocallyFiniteMass.smul [NormedSpace ℝ V] (hf : HasLocallyFiniteMass f) (a : ℝ) :
    HasLocallyFiniteMass (a • f) := fun K hK hKΩ => by
  obtain ⟨C, hC, hfC⟩ := hf K hK hKΩ
  refine ⟨‖a‖ * C, mul_nonneg (norm_nonneg a) hC, fun φ hφ => ?_⟩
  rw [Pi.smul_apply, norm_smul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (hfC φ hφ) (norm_nonneg a)

variable [NormedSpace ℝ V] {𝓕 : Type*} [FunLike 𝓕 𝓓^{n}(Ω, F) V]
  [LinearMapClass 𝓕 ℝ 𝓓^{n}(Ω, F) V]

/-- **Variational characterization of local finiteness of mass.** A linear map on test functions
has locally finite mass if and only if its local mass on every compact subset of `Ω` is finite. -/
theorem hasLocallyFiniteMass_iff_localMass_ne_top (T : 𝓕) :
    HasLocallyFiniteMass T ↔ ∀ K : Set E, IsCompact K → K ⊆ Ω → localMass T K ≠ ⊤ := by
  refine ⟨fun hT K hK hKΩ => ?_, fun hT K hK hKΩ => ?_⟩
  · obtain ⟨C, hC, hTC⟩ := hT K hK hKΩ
    refine ne_top_of_le_ne_top (ENNReal.ofReal_ne_top (r := C)) <|
      localMass_le_iff.2 fun φ hφU hφ => ?_
    rw [← ofReal_norm]
    refine ENNReal.ofReal_le_ofReal <| (hTC φ hφU).trans ?_
    exact mul_le_of_le_one_right hC <| (BoundedContinuousFunction.norm_le zero_le_one).2 hφ
  · refine ⟨(localMass T K).toReal, ENNReal.toReal_nonneg, fun φ hφU => ?_⟩
    have h := enorm_apply_le_localMass_mul T hφU
    rw [← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_toReal (hT K hK hKΩ),
      ← ENNReal.ofReal_mul ENNReal.toReal_nonneg] at h
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h

/-- A linear map of finite mass has locally finite mass. -/
theorem hasLocallyFiniteMass_of_mass_ne_top (T : 𝓕) (hT : mass T ≠ ⊤) :
    HasLocallyFiniteMass T :=
  (hasLocallyFiniteMass_iff_localMass_ne_top T).2 fun _ _ _ =>
    ne_top_of_le_ne_top hT localMass_le_mass

end LocallyFinite

section Evaluation

variable [FiniteDimensional ℝ E] [NormedSpace ℝ V]

/-- **Point currents.** For `x ∈ Ω`, the evaluation `φ ↦ ℓ (φ x)` of a continuous linear map at
the value of the test at `x` has mass `‖ℓ‖`. -/
theorem mass_apply_apply {x : E} (hx : x ∈ Ω) (ℓ : F →L[ℝ] V) :
    mass (fun φ : 𝓓^{n}(Ω, F) => ℓ (φ x)) = ‖ℓ‖ₑ := by
  refine le_antisymm (mass_le_iff.2 fun φ hφ => ?_) ?_
  · rw [← ofReal_norm, ← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal <|
      (ℓ.le_opNorm _).trans (mul_le_of_le_one_right (norm_nonneg ℓ) (hφ x))
  -- Test `ℓ` on `u • v` for a bump `u` at `x` with values in `[0, 1]` and a unit vector `v`.
  obtain ⟨u, huΩ, hu, hud, hu01, hux⟩ :=
    exists_contDiff_tsupport_subset (n := n) (Ω.isOpen.mem_nhds hx)
  rcases eq_top_or_lt_top (mass fun φ : 𝓓^{n}(Ω, F) => ℓ (φ x)) with hM | hM
  · simp [hM]
  rw [← ofReal_norm, ← ENNReal.ofReal_toReal hM.ne]
  refine ENNReal.ofReal_le_ofReal <| ℓ.opNorm_le_of_unit_norm ENNReal.toReal_nonneg fun v hv => ?_
  let φ : 𝓓^{n}(Ω, F) := ⟨fun y => u y • v, hud.smul contDiff_const, hu.smul_right,
    (tsupport_smul_subset_left _ _).trans huΩ⟩
  have hφ (y : E) : ‖φ y‖ ≤ 1 := by
    have := hu01 (mem_range_self y)
    simpa [φ, norm_smul, hv, abs_of_nonneg this.1] using this.2
  have h := enorm_le_mass (f := fun φ : 𝓓^{n}(Ω, F) => ℓ (φ x)) hφ
  rw [← ofReal_norm, ← ENNReal.ofReal_toReal hM.ne] at h
  simpa [φ, hux] using (ENNReal.ofReal_le_ofReal_iff ENNReal.toReal_nonneg).1 h

/-- The degree-zero point current `ω ↦ ω x ![]` at a point of `Ω` has mass one. -/
theorem mass_apply_finZero {x : E} (hx : x ∈ Ω) :
    mass (fun ω : 𝓓^{n}(Ω, E [⋀^Fin 0]→L[ℝ] ℝ) => ω x ![]) = 1 := by
  -- Evaluation at `![]` has norm one on degree-zero forms.
  let ℓ := ContinuousAlternatingMap.apply ℝ E ℝ (![] : Fin 0 → E)
  have hℓ : ‖ℓ‖ = 1 := by
    refine le_antisymm (ℓ.opNorm_le_bound zero_le_one fun c => ?_) ?_
    · simpa [ℓ] using c.le_opNorm ![]
    · let c := ContinuousAlternatingMap.constOfIsEmpty ℝ E (Fin 0) (1 : ℝ)
      simpa [ℓ, c] using ℓ.le_opNorm c
  simpa [ℓ, ← ofReal_norm, hℓ] using mass_apply_apply (n := n) hx ℓ

end Evaluation

section Integral

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {μ : Measure E}
  [μ.IsAddHaarMeasure] {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  {G : E → H →L[ℝ] ℝ}

/-- **Mass of an absolutely continuous current.** Against an additive Haar measure, integration
against a field `G` of continuous linear functionals on a real Hilbert space, locally integrable
on `Ω`, has mass `∫_Ω ‖G‖`; both sides may be infinite. -/
theorem mass_integral_apply (hG : LocallyIntegrableOn G Ω μ) :
    mass (fun φ : 𝓓(Ω, H) => ∫ x, G x (φ x) ∂μ) = ∫⁻ x in Ω, ‖G x‖ₑ ∂μ := by
  refine le_antisymm (mass_le_iff.2 fun φ hφ => φ.enorm_integral_apply_le_setLIntegral_enorm hφ G)
    ?_
  rw [← hG.iSup_ofReal_integral_apply_eq_setLIntegral_enorm]
  exact iSup₂_mono fun φ _ => ENNReal.ofReal_le_of_le_toReal <| by
    simpa using le_abs_self _

end Integral

end Distribution
