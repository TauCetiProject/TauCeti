/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.GraphStep
public import TauCeti.Analysis.Sobolev.WeakDeriv.GelfandTriple
public import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.Topology.Order.ProjIcc

/-!
# The energy space of a Gelfand triple

For a continuous linear map `ι : V →L[ℝ] H` into a real inner-product space, `EvolutionSpace ι a b`
is the space of `u ∈ L²(a,b;V)` whose image under `ι.gelfandDual ∘ ι` has weak time derivative
in `L²(a,b;V*)`. It carries the Euclidean graph norm and is Banach when `V` is Banach.
The derivative is uniquely determined by the value field; extensionality needs no injectivity
or dense-range hypothesis on `ι`.

When `a < b` and `H` is complete, `EvolutionSpace.toContinuousMap` is the bounded linear map
assigning the unique continuous representative in `C([a,b];H)`. Its evaluations give bounded
time traces, including both endpoints, and it is injective when `ι` is injective. This is the
space in which energy solutions of parabolic equations have a meaningful initial value.
The energy identity is stated for the canonical representative.

The construction reuses `WeakDerivStep` for the closed graph and
`HasWeakLineDerivOn.exists_continuousOn_ae_eq_of_gelfandDual` for the continuous representative.
Time derivatives are identified with linear maps from `ℝ` using Mathlib's
`ContinuousLinearMap.toSpanSingletonLIE`.

## References

* L. C. Evans, *Partial Differential Equations*, second edition, §5.9.2, Theorem 3.
* E. Zeidler, *Nonlinear Functional Analysis and its Applications II/A*, Chapter 23.
-/

public section

noncomputable section

namespace TauCeti

open MeasureTheory Filter Set TopologicalSpace Topology
open scoped InnerProductSpace

universe u v

variable {V : Type u} {H : Type v} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The map from `L²(a,b;V)` to dual-valued fields through the pivot space. -/
def _root_.ContinuousLinearMap.evolutionBaseL (ι : V →L[ℝ] H) (a b : ℝ) :
    Lp V 2 (volume.restrict (Ioo a b)) →L[ℝ]
      Lp (StrongDual ℝ V) 2 (volume.restrict (Ioo a b)) :=
  (ι.gelfandDual.comp ι).compLpL 2 (volume.restrict (Ioo a b))

open ContinuousLinearMap (evolutionBaseL)

/-- The pivot map acts pointwise almost everywhere. -/
theorem _root_.ContinuousLinearMap.evolutionBaseL_apply_ae (ι : V →L[ℝ] H) (a b : ℝ)
    (u : Lp V 2 (volume.restrict (Ioo a b))) :
    evolutionBaseL ι a b u =ᵐ[volume.restrict (Ioo a b)] fun t ↦ ι.gelfandDual (ι (u t)) :=
  (ι.gelfandDual.comp ι).coeFn_compLp u

open ContinuousLinearMap (evolutionBaseL_apply_ae)

/-- The energy space `L²(a,b;V) ∩ H¹(a,b;V*)`, with the Euclidean graph norm. The derivative
is recorded as an `ℝ →L[ℝ] V*` field, canonically equivalent to a `V*` field. -/
abbrev EvolutionSpace (ι : V →L[ℝ] H) (a b : ℝ) :=
  WeakDerivStep volume ⟨Ioo a b, isOpen_Ioo⟩ 2 (evolutionBaseL ι a b)

namespace EvolutionSpace

variable {ι : V →L[ℝ] H} {a b : ℝ}

/-- The continuous projection to the `L²(a,b;V)` value field. -/
def valueL : EvolutionSpace ι a b →L[ℝ] Lp V 2 (volume.restrict (Ioo a b)) :=
  WeakDerivStep.prevL (mu := volume) (Omega := ⟨Ioo a b, isOpen_Ioo⟩)
    (evolutionBaseL ι a b)

/-- The continuous projection to the dual-valued weak time derivative. -/
def timeDerivL : EvolutionSpace ι a b →L[ℝ]
    Lp (StrongDual ℝ V) 2 (volume.restrict (Ioo a b)) :=
  ((ContinuousLinearMap.apply ℝ (StrongDual ℝ V) 1).compLpL
    2 (volume.restrict (Ioo a b))).comp
    (WeakDerivStep.weakFDerivL (mu := volume) (Omega := ⟨Ioo a b, isOpen_Ioo⟩)
      (evolutionBaseL ι a b))

/-- The `L²(a,b;V)` value field. -/
def value (u : EvolutionSpace ι a b) : Lp V 2 (volume.restrict (Ioo a b)) := valueL u

/-- The `L²(a,b;V*)` weak time derivative. -/
def timeDeriv (u : EvolutionSpace ι a b) :
    Lp (StrongDual ℝ V) 2 (volume.restrict (Ioo a b)) := timeDerivL u

@[simp]
theorem valueL_apply (u : EvolutionSpace ι a b) : valueL u = value u := (rfl)

@[simp]
theorem timeDerivL_apply (u : EvolutionSpace ι a b) : timeDerivL u = timeDeriv u := (rfl)

private theorem value_eq_prev (u : EvolutionSpace ι a b) :
    value u = WeakDerivStep.prev (mu := volume) (Omega := ⟨Ioo a b, isOpen_Ioo⟩)
      (evolutionBaseL ι a b) u :=
  WeakDerivStep.prevL_apply (mu := volume) (Omega := ⟨Ioo a b, isOpen_Ioo⟩)
    (evolutionBaseL ι a b) u

@[simp]
theorem value_add (u v : EvolutionSpace ι a b) : value (u + v) = value u + value v :=
  (valueL (ι := ι) (a := a) (b := b)).map_add u v

@[simp]
theorem value_smul (c : ℝ) (u : EvolutionSpace ι a b) : value (c • u) = c • value u :=
  (valueL (ι := ι) (a := a) (b := b)).map_smul c u

@[simp]
theorem value_zero : value (0 : EvolutionSpace ι a b) = 0 :=
  (valueL (ι := ι) (a := a) (b := b)).map_zero

@[simp]
theorem timeDeriv_add (u v : EvolutionSpace ι a b) :
    timeDeriv (u + v) = timeDeriv u + timeDeriv v :=
  (timeDerivL (ι := ι) (a := a) (b := b)).map_add u v

@[simp]
theorem timeDeriv_smul (c : ℝ) (u : EvolutionSpace ι a b) : timeDeriv (c • u) = c • timeDeriv u :=
  (timeDerivL (ι := ι) (a := a) (b := b)).map_smul c u

@[simp]
theorem timeDeriv_zero : timeDeriv (0 : EvolutionSpace ι a b) = 0 :=
  (timeDerivL (ι := ι) (a := a) (b := b)).map_zero

@[simp]
theorem value_neg (u : EvolutionSpace ι a b) : value (-u) = -value u :=
  (valueL (ι := ι) (a := a) (b := b)).map_neg u

@[simp]
theorem value_sub (u v : EvolutionSpace ι a b) : value (u - v) = value u - value v :=
  (valueL (ι := ι) (a := a) (b := b)).map_sub u v

@[simp]
theorem timeDeriv_neg (u : EvolutionSpace ι a b) : timeDeriv (-u) = -timeDeriv u :=
  (timeDerivL (ι := ι) (a := a) (b := b)).map_neg u

@[simp]
theorem timeDeriv_sub (u v : EvolutionSpace ι a b) :
    timeDeriv (u - v) = timeDeriv u - timeDeriv v :=
  (timeDerivL (ι := ι) (a := a) (b := b)).map_sub u v

/-- The value determines the entire element, since the weak time derivative is unique. -/
@[ext]
theorem ext {u v : EvolutionSpace ι a b} (h : value u = value v) : u = v :=
  WeakDerivStep.ext (mu := volume) (Omega := ⟨Ioo a b, isOpen_Ioo⟩)
    (by simpa only [value_eq_prev] using h)

private theorem timeDeriv_apply_ae (u : EvolutionSpace ι a b) :
    timeDeriv u =ᵐ[volume.restrict (Ioo a b)] fun t ↦
      WeakDerivStep.weakFDeriv (mu := volume) (Omega := ⟨Ioo a b, isOpen_Ioo⟩)
        (evolutionBaseL ι a b) u t 1 := by
  rw [timeDeriv, timeDerivL, ContinuousLinearMap.comp_apply,
    WeakDerivStep.weakFDerivL_apply]
  simpa only [ContinuousLinearMap.apply_apply, Opens.coe_mk] using
    (ContinuousLinearMap.apply ℝ (StrongDual ℝ V) 1).coeFn_compLpL
      (WeakDerivStep.weakFDeriv (mu := volume) (Omega := ⟨Ioo a b, isOpen_Ioo⟩)
        (evolutionBaseL ι a b) u)

/-- The recorded derivative is the weak derivative of the value viewed in `V*`. -/
theorem hasWeakLineDerivOn (u : EvolutionSpace ι a b) :
    HasWeakLineDerivOn volume ⟨Ioo a b, isOpen_Ioo⟩
      (fun t ↦ ι.gelfandDual (ι (value u t))) (timeDeriv u) 1 := by
  have h := (WeakDerivStep.hasWeakFDerivOn_base_prev (mu := volume)
    (Omega := ⟨Ioo a b, isOpen_Ioo⟩) (evolutionBaseL ι a b) u).hasWeakLineDerivOn 1
  rw [← value_eq_prev] at h
  refine (h.congr_ae (evolutionBaseL_apply_ae ι a b (value u))).congr_ae_deriv ?_
  filter_upwards [timeDeriv_apply_ae u] with t ht
  exact ht.symm

/-- Construct an energy-space element from a value and its dual-valued weak time derivative. -/
def mk (u : Lp V 2 (volume.restrict (Ioo a b)))
    (d : Lp (StrongDual ℝ V) 2 (volume.restrict (Ioo a b)))
    (h : HasWeakLineDerivOn volume ⟨Ioo a b, isOpen_Ioo⟩
      (fun t ↦ ι.gelfandDual (ι (u t))) d 1) : EvolutionSpace ι a b := by
  -- Abstract the field while constructing the map so its normed instances are fixed before
  -- specializing to the nested continuous-linear-map type `V*`.
  let lift {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F]
      (d : Lp F 2 (volume.restrict (Ioo a b))) :=
    (ContinuousLinearMap.toSpanSingletonLIE ℝ F).toLinearIsometry.toContinuousLinearMap.compLp d
  let D := lift (F := StrongDual ℝ V) d
  refine WeakDerivStep.mk (mu := volume) (Omega := ⟨Ioo a b, isOpen_Ioo⟩)
    (evolutionBaseL ι a b) u D ?_
  rw [hasWeakFDerivOn_iff]
  intro v
  have hv := (h.smul_direction v).congr_ae (evolutionBaseL_apply_ae ι a b u).symm
  simp only [smul_eq_mul, mul_one] at hv
  refine hv.congr_ae_deriv ?_
  have lift_ae {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F]
      (d : Lp F 2 (volume.restrict (Ioo a b))) :
      lift d =ᵐ[volume.restrict (Ioo a b)] fun t ↦ ContinuousLinearMap.toSpanSingleton ℝ (d t) :=
    (ContinuousLinearMap.toSpanSingletonLIE ℝ F).toLinearIsometry.toContinuousLinearMap
      |>.coeFn_compLp d
  filter_upwards [lift_ae d] with t ht
  simp only [D, ht, ContinuousLinearMap.toSpanSingleton_apply, Pi.smul_apply]

@[simp]
theorem value_mk (u : Lp V 2 (volume.restrict (Ioo a b)))
    (d : Lp (StrongDual ℝ V) 2 (volume.restrict (Ioo a b))) (h) :
    value (mk (ι := ι) u d h) = u := by
  rw [value_eq_prev]
  exact WeakDerivStep.prev_mk _ _ _ _

@[simp]
theorem timeDeriv_mk (u : Lp V 2 (volume.restrict (Ioo a b)))
    (d : Lp (StrongDual ℝ V) 2 (volume.restrict (Ioo a b))) (h) :
    timeDeriv (mk (ι := ι) u d h) = d := by
  apply Lp.ext
  exact (hasWeakLineDerivOn (mk u d h)).ae_eq (by simpa using h)

/-- Reconstructing from the value and the time derivative recovers the energy-space element. -/
@[simp]
theorem mk_value_timeDeriv (u : EvolutionSpace ι a b) :
    mk (value u) (timeDeriv u) (hasWeakLineDerivOn u) = u := by
  apply ext
  simp

private theorem norm_timeDeriv_eq (u : EvolutionSpace ι a b) :
    ‖timeDeriv u‖ = ‖WeakDerivStep.weakFDeriv (mu := volume)
      (Omega := ⟨Ioo a b, isOpen_Ioo⟩) (evolutionBaseL ι a b) u‖ := by
  rw [Lp.norm_def, Lp.norm_def]
  congr 1
  apply eLpNorm_congr_norm_ae (Lp.aestronglyMeasurable _) (Lp.aestronglyMeasurable _)
  filter_upwards [timeDeriv_apply_ae u] with t ht
  rw [ht, ← ContinuousLinearMap.toSpanSingletonLIE_symm_apply]
  exact LinearIsometryEquiv.norm_map _ _

/-- Convergence in the energy space is equivalent to convergence of the value and the
dual-valued weak time derivative in their respective `L²` spaces. -/
theorem tendsto_iff_value_timeDeriv {I : Type*} {l : Filter I}
    {v : I → EvolutionSpace ι a b} {u : EvolutionSpace ι a b} :
    Tendsto v l (𝓝 u) ↔
      Tendsto (fun i ↦ value (v i)) l (𝓝 (value u)) ∧
      Tendsto (fun i ↦ timeDeriv (v i)) l (𝓝 (timeDeriv u)) := by
  rw [WeakDerivStep.tendsto_iff_prev_weakFDeriv]
  simp only [← value_eq_prev]
  refine and_congr Iff.rfl ?_
  conv_lhs => rw [tendsto_iff_norm_sub_tendsto_zero]
  conv_rhs => rw [tendsto_iff_norm_sub_tendsto_zero]
  simp only [← timeDeriv_sub, norm_timeDeriv_eq, ← WeakDerivStep.weakFDerivL_apply, map_sub]

/-- The squared energy norm is the sum of the squared value and time-derivative `L²` norms. -/
theorem norm_sq_eq_norm_value_sq_add_norm_timeDeriv_sq (u : EvolutionSpace ι a b) :
    ‖u‖ ^ 2 = ‖value u‖ ^ 2 + ‖timeDeriv u‖ ^ 2 := by
  rw [value_eq_prev, norm_timeDeriv_eq]
  exact WeakDerivStep.norm_sq_eq_norm_prev_sq_add_norm_weakFDeriv_sq _ u

/-- The graph norm controls the `L²(a,b;V)` norm. -/
theorem norm_value_le (u : EvolutionSpace ι a b) : ‖value u‖ ≤ ‖u‖ := by
  rw [value_eq_prev]
  exact WeakDerivStep.norm_prev_le _ u

/-- The graph norm controls the `L²(a,b;V*)` time-derivative norm. -/
theorem norm_timeDeriv_le (u : EvolutionSpace ι a b) : ‖timeDeriv u‖ ≤ ‖u‖ := by
  rw [norm_timeDeriv_eq]
  exact WeakDerivStep.norm_weakFDeriv_le _ u

/-- The energy space is complete in its graph norm. -/
instance [CompleteSpace V] : CompleteSpace (EvolutionSpace ι a b) := inferInstance

variable [CompleteSpace V] [CompleteSpace H]

private theorem exists_continuousMap (hab : a < b) (u : EvolutionSpace ι a b) :
    ∃ w : C(Icc a b, H), (fun t ↦ ι (value u t)) =ᵐ[volume.restrict (Ioo a b)]
      fun t ↦ w (projIcc a b hab.le t) := by
  obtain ⟨w, hw, hae⟩ := (hasWeakLineDerivOn u).exists_continuousOn_ae_eq_of_gelfandDual
    (Lp.memLp (value u)) (Lp.memLp (timeDeriv u))
  let wMap : C(Icc a b, H) := ⟨fun t ↦ w t, hw.domRestrict⟩
  have hwMap (t : Icc a b) : wMap t = w t := rfl
  refine ⟨wMap, ?_⟩
  filter_upwards [hae, ae_restrict_mem measurableSet_Ioo] with t ht hmem
  rw [projIcc_of_mem hab.le (Ioo_subset_Icc_self hmem), hwMap]
  exact ht

omit [CompleteSpace V] [CompleteSpace H] in
private theorem eq_of_value_ae_eq (hab : a < b) {u : EvolutionSpace ι a b}
    {w z : C(Icc a b, H)}
    (hw : (fun t ↦ ι (value u t)) =ᵐ[volume.restrict (Ioo a b)]
      fun t ↦ w (projIcc a b hab.le t))
    (hz : (fun t ↦ ι (value u t)) =ᵐ[volume.restrict (Ioo a b)]
      fun t ↦ z (projIcc a b hab.le t)) : w = z := by
  have h := hw.symm.trans hz
  rw [restrict_Ioo_eq_restrict_Icc] at h
  have heq := Measure.eqOn_Icc_of_ae_eq volume hab.ne h
    (w.continuous.comp continuous_projIcc).continuousOn
    (z.continuous.comp continuous_projIcc).continuousOn
  ext t
  simpa only [projIcc_of_mem hab.le t.property] using heq t.property

private def representativeₗ (hab : a < b) : EvolutionSpace ι a b →ₗ[ℝ] C(Icc a b, H) where
  toFun u := (exists_continuousMap hab u).choose
  map_add' u v := by
    apply eq_of_value_ae_eq hab (exists_continuousMap hab (u + v)).choose_spec
    filter_upwards [(exists_continuousMap hab u).choose_spec,
      (exists_continuousMap hab v).choose_spec,
      Lp.coeFn_add (value u) (value v)] with t hu hv hadd
    calc
      ι (value (u + v) t) = ι (value u t) + ι (value v t) := by
        rw [value_add, hadd, Pi.add_apply, map_add]
      _ = _ := by rw [ContinuousMap.add_apply]; exact congrArg₂ (· + ·) hu hv
  map_smul' c u := by
    apply eq_of_value_ae_eq hab (exists_continuousMap hab (c • u)).choose_spec
    filter_upwards [(exists_continuousMap hab u).choose_spec,
      Lp.coeFn_smul c (value u)] with t hu hsmul
    simp only [RingHom.id_apply]
    calc
      ι (value (c • u) t) = c • ι (value u t) := by rw [value_smul, hsmul, Pi.smul_apply, map_smul]
      _ = _ := by rw [ContinuousMap.smul_apply]; exact congrArg (c • ·) hu

private theorem representativeₗ_ae (hab : a < b) (u : EvolutionSpace ι a b) :
    (fun t ↦ ι (value u t)) =ᵐ[volume.restrict (Ioo a b)]
      fun t ↦ representativeₗ hab u (projIcc a b hab.le t) :=
  (exists_continuousMap hab u).choose_spec

private theorem representativeₗ_closedGraph (hab : a < b)
    (u : ℕ → EvolutionSpace ι a b) (v : EvolutionSpace ι a b) (w : C(Icc a b, H))
    (hu : Tendsto u atTop (𝓝 v)) (hw : Tendsto (representativeₗ hab ∘ u) atTop (𝓝 w)) :
    w = representativeₗ hab v := by
  have hval : Tendsto (fun n ↦ value (u n)) atTop (𝓝 (value v)) :=
    ((valueL (ι := ι) (a := a) (b := b)).continuous.tendsto v).comp hu
  obtain ⟨ns, hmono, hns⟩ := (tendstoInMeasure_of_tendsto_Lp hval).exists_seq_tendsto_ae
  have hrep := ae_all_iff.mpr fun n ↦ representativeₗ_ae hab (u (ns n))
  apply eq_of_value_ae_eq hab (u := v) ?_ (representativeₗ_ae hab v)
  filter_upwards [hns, hrep] with t ht hrt
  have heval : Tendsto (fun n ↦ representativeₗ hab (u (ns n)) (projIcc a b hab.le t))
      atTop (𝓝 (w (projIcc a b hab.le t))) :=
    ((ContinuousMap.evalCLM ℝ (projIcc a b hab.le t)).continuous.tendsto w).comp
      (hw.comp hmono.tendsto_atTop)
  exact tendsto_nhds_unique ((ι.continuous.tendsto _).comp ht |>.congr hrt) heval

/-- The bounded linear time-trace map into `C([a,b];H)`, assigning the unique continuous pivot
representative. Both endpoint evaluations are therefore bounded linear maps. -/
def toContinuousMap (hab : a < b) : EvolutionSpace ι a b →L[ℝ] C(Icc a b, H) :=
  .ofSeqClosedGraph (g := representativeₗ hab) (representativeₗ_closedGraph hab)

private theorem toContinuousMap_apply (hab : a < b) (u : EvolutionSpace ι a b) :
    toContinuousMap hab u = representativeₗ hab u := by
  simp only [toContinuousMap, ContinuousLinearMap.coeFn_ofSeqClosedGraph]

/-- The canonical time trace represents the pivot-valued function almost everywhere. -/
theorem value_ae_eq_toContinuousMap (hab : a < b) (u : EvolutionSpace ι a b) :
    (fun t ↦ ι (value u t)) =ᵐ[volume.restrict (Ioo a b)]
      fun t ↦ toContinuousMap hab u (projIcc a b hab.le t) := by
  rw [toContinuousMap_apply]
  exact representativeₗ_ae hab u

/-- A continuous function is the time trace exactly when it represents the pivot value field. -/
theorem toContinuousMap_eq_iff (hab : a < b) (u : EvolutionSpace ι a b)
    (w : C(Icc a b, H)) : toContinuousMap hab u = w ↔
      (fun t ↦ ι (value u t)) =ᵐ[volume.restrict (Ioo a b)]
        fun t ↦ w (projIcc a b hab.le t) := by
  refine ⟨fun h ↦ h ▸ value_ae_eq_toContinuousMap hab u, fun h ↦ ?_⟩
  exact eq_of_value_ae_eq hab (value_ae_eq_toContinuousMap hab u) h

/-- The time-trace map is injective when the inclusion into the pivot space is injective. -/
theorem toContinuousMap_injective (hab : a < b) (hι : Function.Injective ι) :
    Function.Injective (toContinuousMap (ι := ι) hab) := by
  intro u v h
  apply ext
  apply Lp.ext
  have hae := (value_ae_eq_toContinuousMap hab u).trans
    (h ▸ value_ae_eq_toContinuousMap hab v).symm
  exact hae.mono fun t ht ↦ hι ht

/-- The energy identity for the canonical continuous representative, including endpoint times. -/
theorem norm_sq_sub_norm_sq_eq_integral (hab : a < b) (u : EvolutionSpace ι a b)
    (s t : Icc a b) :
    ‖toContinuousMap hab u t‖ ^ 2 - ‖toContinuousMap hab u s‖ ^ 2 =
      2 * ∫ r in (s : ℝ)..(t : ℝ), timeDeriv u r (value u r) := by
  simpa only [Function.comp_apply, projIcc_of_mem hab.le t.property,
    projIcc_of_mem hab.le s.property] using
    (hasWeakLineDerivOn u).norm_sq_sub_norm_sq_eq_of_gelfandDual
      (Lp.memLp (value u)) (Lp.memLp (timeDeriv u))
      ((toContinuousMap hab u).continuous.comp continuous_projIcc).continuousOn
      (value_ae_eq_toContinuousMap hab u) s.property t.property

end EvolutionSpace

end TauCeti
