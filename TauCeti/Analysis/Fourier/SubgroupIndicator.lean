/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Fourier.FourierTransform
public import TauCeti.Analysis.Fourier.CharacterAnnihilator

/-!
# Fourier transforms of subgroup and coset indicators

Using Mathlib's negative-kernel `VectorFourier.fourierIntegral` and its translation law, we
compute the transform of the indicator of a measurable additive subgroup and of a translate.
The transform is supported on the character annihilator, and the factor there is the subgroup
volume times the phase of the translate. For two measures whose volumes on a subgroup and its
annihilator multiply to one, the subgroup-indicator formula gives Fourier inversion with the
transposed pairing, provided the double annihilator recovers the original subgroup.

More generally, periods of a function restrict the support of its transform, and subgroup
support gives periods of the transform. These are the compact-support and local-constancy
arguments used for Fourier analysis on locally constant test functions over local fields.
All the identities use Mathlib's totalized Bochner integral.
-/

public section

open Function MeasureTheory

namespace VectorFourier

variable {R V W E : Type*} [CommRing R]
  [AddCommGroup V] [Module R V] [MeasurableSpace V] [AddCommGroup W] [Module R W]
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  {ψ : AddChar R Circle} {B : V →ₗ[R] W →ₗ[R] R} {μ : Measure V} {f : V → E}
  {U : AddSubgroup V}

section Periods

variable [MeasurableAdd V] [μ.IsAddRightInvariant]

/-- A period with nontrivial phase at `w` forces the Fourier transform to vanish at `w`. -/
theorem fourierIntegral_eq_zero_of_periodic {u : V} {w : W} (h : Periodic f u)
    (hw : ψ (B u w) ≠ 1) : fourierIntegral ψ μ B f w = 0 := by
  have htrans := congrFun (fourierIntegral_comp_add_right ψ μ B f u) w
  have hcomp : (f ∘ fun v ↦ v + u) = f := funext h
  rw [hcomp, Circle.smul_def] at htrans
  have heq : ((ψ (B u w) : ℂ) - 1) • fourierIntegral ψ μ B f w = 0 := by
    rw [sub_smul, one_smul, ← htrans, sub_self]
  exact (smul_eq_zero.mp heq).resolve_left (sub_ne_zero.mpr (hw ∘ Circle.coe_eq_one.mp))

/-- If every element of `U` is a period of `f`, its Fourier transform vanishes off the
annihilator of `U`. -/
theorem support_fourierIntegral_subset_characterAnnihilator (h : ∀ u ∈ U, Periodic f u) :
    support (fourierIntegral ψ μ B f) ⊆ U.characterAnnihilator ψ B := by
  intro w hw
  refine AddSubgroup.mem_characterAnnihilator.mpr fun u hu ↦ ?_
  by_contra hn
  exact hw (fourierIntegral_eq_zero_of_periodic (h u hu) hn)

/-- A compact period annihilator contains the support of the transform, which is therefore
compactly supported. -/
theorem hasCompactSupport_fourierIntegral_of_periodic [TopologicalSpace W] [T2Space W]
    (h : ∀ u ∈ U, Periodic f u) (hU : IsCompact (U.characterAnnihilator ψ B : Set W)) :
    HasCompactSupport (fourierIntegral ψ μ B f) :=
  HasCompactSupport.of_support_subset_isCompact hU
    (support_fourierIntegral_subset_characterAnnihilator h)

end Periods

/-- Modulation by the positive phase at `a` shifts the negative-kernel transform by `a`. -/
theorem fourierIntegral_char_smul (ψ : AddChar R Circle) (μ : Measure V)
    (B : V →ₗ[R] W →ₗ[R] R) (f : V → E) (a : W) :
    fourierIntegral ψ μ B (fun x ↦ ψ (B x a) • f x) =
      fun w ↦ fourierIntegral ψ μ B f (w - a) := by
  funext w
  simp only [fourierIntegral]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x ↦ by
    have hphase : -(B x (w - a)) = -B x w + B x a := by
      rw [map_sub, neg_sub, sub_eq_add_neg, add_comm]
    simp only [smul_smul, ← ψ.map_add_eq_mul, hphase]

/-- If the support of `f` is contained in `U`, each element of its character annihilator
is a period of the Fourier transform of `f`. -/
theorem periodic_fourierIntegral_of_support_subset (hf : support f ⊆ U) {a : W}
    (ha : a ∈ U.characterAnnihilator ψ B) : Periodic (fourierIntegral ψ μ B f) a := by
  have hmod : (fun x ↦ ψ (B x a) • f x) = f := by
    funext x
    by_cases hx : x ∈ support f
    · rw [AddSubgroup.mem_characterAnnihilator.mp ha x (hf hx), one_smul]
    · simp [notMem_support.mp hx]
  intro w
  simpa [hmod] using congrFun (fourierIntegral_char_smul ψ μ B f a) (w + a)

/-- A function supported in a compact subgroup has locally constant Fourier transform when
the character pairing is jointly continuous on `U × W`. -/
theorem isLocallyConstant_fourierIntegral_of_support_subset
    [TopologicalSpace V] [TopologicalSpace W]
    (hf : support f ⊆ U) (hU : IsCompact (U : Set V))
    (h : Continuous (fun p : U × W ↦ ψ (B p.1 p.2))) :
    IsLocallyConstant (fourierIntegral ψ μ B f) := by
  refine (IsLocallyConstant.iff_exists_open _).mpr fun w ↦ ?_
  obtain ⟨S, hS, hw, hphase⟩ := (U.isLocallyConstant_characterPairing hU h).exists_open w
  refine ⟨S, hS, hw, fun y hy ↦ ?_⟩
  have hmem : y - w ∈ U.characterAnnihilator ψ B := by
    refine AddSubgroup.mem_characterAnnihilator.mpr fun u hu ↦ ?_
    have hval := congrFun (hphase y hy) ⟨u, hu⟩
    rw [map_sub, ψ.map_sub_eq_div, hval, div_self']
  simpa using periodic_fourierIntegral_of_support_subset (μ := μ) hf hmem w

section Indicators

variable [MeasurableAdd V] [μ.IsAddRightInvariant]

/-- The Fourier transform of `1_U` is the indicator of the character annihilator multiplied
by `μ.real U`. The statement uses the totalized integral even if the volume is infinite. -/
theorem fourierIntegral_indicator_addSubgroup (hU : MeasurableSet (U : Set V)) :
    fourierIntegral ψ μ B ((U : Set V).indicator (fun _ ↦ (1 : ℂ))) =
      (μ.real (U : Set V)) • (U.characterAnnihilator ψ B : Set W).indicator (fun _ ↦ (1 : ℂ)) := by
  classical
  funext w
  by_cases hw : w ∈ U.characterAnnihilator ψ B
  · simp only [Pi.smul_apply, Set.indicator_of_mem hw, fourierIntegral]
    rw [← integral_indicator_const (μ := μ) 1 hU]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun v ↦ by
      by_cases hv : v ∈ U
      · simp [Set.indicator_of_mem hv, ψ.map_neg_eq_inv,
          AddSubgroup.mem_characterAnnihilator.mp hw v hv]
      · simp [Set.indicator_of_notMem hv]
  · have hper : ∀ u ∈ U, Periodic ((U : Set V).indicator (fun _ ↦ (1 : ℂ))) u := by
      intro u hu v
      simp only [Set.indicator_apply, SetLike.mem_coe, U.add_mem_cancel_right hu]
    have hzero : w ∉ support (fourierIntegral ψ μ B
        ((U : Set V).indicator (fun _ ↦ (1 : ℂ)))) :=
      fun hm ↦ hw (support_fourierIntegral_subset_characterAnnihilator hper hm)
    simpa [Set.indicator_of_notMem hw] using notMem_support.mp hzero

/-- Translating the indicator to `a + U` introduces the negative Fourier phase of `a`. -/
theorem fourierIntegral_indicator_addSubgroup_sub (hU : MeasurableSet (U : Set V)) (a : V) :
    fourierIntegral ψ μ B (fun v ↦ (U : Set V).indicator (fun _ ↦ (1 : ℂ)) (v - a)) =
      fun w ↦ ψ (-B a w) • ((μ.real (U : Set V)) •
        (U.characterAnnihilator ψ B : Set W).indicator (fun _ ↦ (1 : ℂ)) w) := by
  simpa only [Function.comp_def, ← sub_eq_add_neg, map_neg, LinearMap.neg_apply,
    fourierIntegral_indicator_addSubgroup hU, Pi.smul_apply] using
    fourierIntegral_comp_add_right ψ μ B ((U : Set V).indicator (fun _ ↦ (1 : ℂ))) (-a)

/-- Fourier inversion for a subgroup indicator, with the transposed pairing for the second
transform. The double-annihilator and reciprocal-volume identities are explicit inputs. -/
theorem fourierIntegral_fourierIntegral_indicator_addSubgroup
    [MeasurableSpace W] [MeasurableAdd W] (ν : Measure W) [ν.IsAddRightInvariant]
    (hU : MeasurableSet (U : Set V)) (hA : MeasurableSet (U.characterAnnihilator ψ B : Set W))
    (hdual : (U.characterAnnihilator ψ B).characterAnnihilator ψ B.flip = U)
    (hvol : μ.real (U : Set V) * ν.real (U.characterAnnihilator ψ B : Set W) = 1) :
    fourierIntegral ψ ν B.flip
        (fourierIntegral ψ μ B ((U : Set V).indicator (fun _ ↦ (1 : ℂ)))) =
      fun v ↦ (U : Set V).indicator (fun _ ↦ (1 : ℂ)) (-v) := by
  rw [fourierIntegral_indicator_addSubgroup hU, ← Complex.coe_smul,
    fourierIntegral_const_smul, fourierIntegral_indicator_addSubgroup hA, hdual,
    Complex.coe_smul, smul_smul, hvol, one_smul]
  classical
  funext v
  simp [Set.indicator_apply]

end Indicators

end VectorFourier
