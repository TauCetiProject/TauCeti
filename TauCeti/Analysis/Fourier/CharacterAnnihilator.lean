/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Fourier.FourierTransform
public import Mathlib.Topology.LocallyConstant.Basic
public import TauCeti.Algebra.Ring.Periodic
public import TauCeti.Topology.Algebra.Group.CharacterAnnihilator

/-!
# Fourier identities for subgroups and character annihilators

Let `ψ : AddChar R Circle`, `L : V →ₗ[R] W →ₗ[R] R` and `μ` a measure on `V`, and write
`𝓕 f = VectorFourier.fourierIntegral ψ μ L f`, so that `𝓕 f w = ∫ ψ (-L v w) • f v ∂μ`. This file
relates periods of `f` and the support of `𝓕 f` through the character annihilator
`U.characterAnnihilator ψ L` of an additive subgroup `U` of `V`, and computes the transform of the
indicator of `U` and of its cosets. These are the identities behind Fourier analysis on a
nonarchimedean local field, where a Schwartz–Bruhat function is a finite combination of indicators
of cosets of a compact open lattice, and the self-dual measure is normalized by the volumes of a
lattice and of its annihilator. Here `R` is any commutative ring and `V`, `W` any modules: no
topology, nondegeneracy or Haar normalization is assumed beyond what each statement uses.

All transforms are Mathlib's totalized Bochner integrals, so none of the identities carries an
integrability hypothesis. Translation invariance of `μ` is needed only where a period of `f` is
used.

## Main results

* `VectorFourier.fourierIntegral_eq_zero_of_periodic`: a period `u` of `f` kills `𝓕 f` at every
  frequency `w` with `ψ (L u w) ≠ 1`.
* `VectorFourier.support_fourierIntegral_subset`: if every element of `U` is a period of `f`, then
  `𝓕 f` is supported in the annihilator of `U`.
* `VectorFourier.fourierIntegral_indicator_addSubgroup`: `𝓕 (1_U · c) = 1_(U⊥) · μ.real U • c`.
* `VectorFourier.fourierIntegral_indicator_addSubgroup_comp_sub_right`: the transform of the
  indicator of the coset `a + U`.
* `VectorFourier.fourierIntegral_char_smul`: modulation by `ψ (L · w₀)` translates the transform
  by `w₀`.
* `VectorFourier.periodic_fourierIntegral`: if `f` is supported in `U`, every element of the
  annihilator of `U` is a period of `𝓕 f`.
* `VectorFourier.isLocallyConstant_fourierIntegral`: the transform of a function supported in a
  compact subgroup is locally constant when the pairing is continuous on `U × W`.
* `VectorFourier.hasCompactSupport_fourierIntegral`: if `f` is `U`-periodic and the annihilator of
  `U` is compact, `𝓕 f` has compact support.
* `VectorFourier.fourierIntegral_fourierIntegral_indicator_addSubgroup`: Fourier inversion for the
  indicator of `U`, when `U` is the annihilator of its annihilator and the two volumes are
  reciprocal.

## References

* J. Tate, *Fourier analysis in number fields and Hecke's zeta-functions*, Thesis (1950), in
  Cassels–Fröhlich, *Algebraic Number Theory*, §2.2.
-/

public section

open MeasureTheory Function Set

namespace VectorFourier

variable {R V W E : Type*} [CommRing R] [AddCommGroup V] [Module R V] [MeasurableSpace V]
  [AddCommGroup W] [Module R W] [NormedAddCommGroup E] [NormedSpace ℂ E]
  (ψ : AddChar R Circle) (μ : Measure V) (L : V →ₗ[R] W →ₗ[R] R)

section Period

variable [MeasurableAdd V] [μ.IsAddRightInvariant]

/-- **Fourier vanishing from a period.** If `u` is a period of `f` and the phase `ψ (L u w)` is
nontrivial, the Fourier transform of `f` vanishes at `w`. -/
theorem fourierIntegral_eq_zero_of_periodic {f : V → E} {u : V} (hf : Periodic f u) {w : W}
    (hw : ψ (L u w) ≠ 1) : fourierIntegral ψ μ L f w = 0 := by
  have hfu : (f ∘ fun v ↦ v + u) = f := funext hf
  have h := congrFun (fourierIntegral_comp_add_right ψ μ L f u) w
  rw [hfu, Circle.smul_def] at h
  -- `h` says that `𝓕 f w` is fixed by the scalar `ψ (L u w) ≠ 1`.
  have hsub : ((ψ (L u w) : ℂ) - 1) • fourierIntegral ψ μ L f w = 0 := by
    rw [sub_smul, one_smul, ← h, sub_self]
  refine (smul_eq_zero.mp hsub).resolve_left (sub_ne_zero.mpr fun h1 ↦ hw ?_)
  exact Circle.ext (by simpa using h1)

/-- **Fourier support lies in the period annihilator.** If every element of `U` is a period of
`f`, the Fourier transform of `f` is supported in `U.characterAnnihilator ψ L`. -/
theorem support_fourierIntegral_subset {f : V → E} {U : AddSubgroup V}
    (hf : ∀ u ∈ U, Periodic f u) :
    support (fourierIntegral ψ μ L f) ⊆ U.characterAnnihilator ψ L := by
  intro w hw
  rw [SetLike.mem_coe, AddSubgroup.mem_characterAnnihilator]
  intro u hu
  by_contra h
  exact hw (fourierIntegral_eq_zero_of_periodic ψ μ L (hf u hu) h)

variable [CompleteSpace E]

/-- **Fourier transform of a subgroup indicator.** For a measurable additive subgroup `U` and a
right-invariant measure `μ`, the transform of `1_U · c` is `μ.real U • c` times the indicator of
the annihilator of `U`. No normalization of `μ` is assumed. -/
theorem fourierIntegral_indicator_addSubgroup {U : AddSubgroup V}
    (hU : MeasurableSet (U : Set V)) (c : E) :
    fourierIntegral ψ μ L ((U : Set V).indicator fun _ ↦ c) =
      (U.characterAnnihilator ψ L : Set W).indicator fun _ ↦ μ.real U • c := by
  ext w
  by_cases hw : w ∈ U.characterAnnihilator ψ L
  · rw [indicator_of_mem hw, ← integral_indicator_const c hU, fourierIntegral]
    -- On `U` the phase `ψ (-L v w)` is trivial, so the integrand is the indicator itself.
    congr 1 with v
    by_cases hv : v ∈ U
    · rw [indicator_of_mem hv, ← LinearMap.neg_apply, ← map_neg,
        AddSubgroup.mem_characterAnnihilator.mp hw _ (neg_mem hv), one_smul]
    · rw [indicator_of_notMem hv, smul_zero]
  · rw [indicator_of_notMem hw]
    exact notMem_support.mp fun h ↦ hw <| support_fourierIntegral_subset ψ μ L
      (fun _ ↦ Periodic.indicator_addSubgroup fun _ ↦ rfl) h

/-- **Fourier transform of a coset indicator.** The transform of `v ↦ 1_U (v - a) · c`, the
indicator of the coset `a + U`, is the subgroup formula multiplied by the phase `ψ (-L a w)`. -/
theorem fourierIntegral_indicator_addSubgroup_comp_sub_right {U : AddSubgroup V}
    (hU : MeasurableSet (U : Set V)) (c : E) (a : V) :
    fourierIntegral ψ μ L (fun v ↦ (U : Set V).indicator (fun _ ↦ c) (v - a)) =
      fun w ↦ ψ (-L a w) •
        (U.characterAnnihilator ψ L : Set W).indicator (fun _ ↦ μ.real U • c) w := by
  have h := fourierIntegral_comp_add_right ψ μ L ((U : Set V).indicator fun _ ↦ c) (-a)
  simp only [fourierIntegral_indicator_addSubgroup ψ μ L hU, map_neg, LinearMap.neg_apply] at h
  simpa [comp_def, sub_eq_add_neg] using h

end Period

/-- **Fourier transform of a character modulation.** Multiplying `f` by the character
`ψ (L · w₀)` translates its Fourier transform by `w₀`. No invariance of `μ` is needed. -/
theorem fourierIntegral_char_smul (f : V → E) (w₀ : W) :
    fourierIntegral ψ μ L (fun v ↦ ψ (L v w₀) • f v) =
      fun w ↦ fourierIntegral ψ μ L f (w - w₀) := by
  ext w
  simp only [fourierIntegral, smul_smul, ← AddChar.map_add_eq_mul, map_sub, neg_sub,
    neg_add_eq_sub]

/-- **Frequency periods from support containment.** If `f` is supported in `U`, every element of
the annihilator of `U` is a period of the Fourier transform of `f`. No invariance of `μ` is
needed. -/
theorem periodic_fourierIntegral {f : V → E} {U : AddSubgroup V} (hf : support f ⊆ U) {a : W}
    (ha : a ∈ U.characterAnnihilator ψ L) : Periodic (fourierIntegral ψ μ L f) a := fun w ↦ by
  -- Modulation by `ψ (L · a)` fixes `f`: the phase is trivial on `U` and `f` vanishes off `U`.
  have hmod : (fun v ↦ ψ (L v a) • f v) = f := funext fun v ↦ by
    by_cases hv : v ∈ U
    · rw [AddSubgroup.mem_characterAnnihilator.mp ha v hv, one_smul]
    · rw [notMem_support.mp fun h ↦ hv (hf h), smul_zero]
  simpa [hmod] using congrFun (fourierIntegral_char_smul ψ μ L f a) (w + a)

/-- **Local constancy of the Fourier transform.** The Fourier transform of a function supported
in a compact additive subgroup `U` is locally constant if the pairing is continuous on `U × W`.
No compatibility between the topology and the addition of `W` is needed. -/
theorem isLocallyConstant_fourierIntegral [TopologicalSpace V] [TopologicalSpace W]
    {f : V → E} {U : AddSubgroup V}
    (hU : IsCompact (U : Set V)) (hψL : Continuous fun p : U × W ↦ ψ (L p.1 p.2))
    (hf : support f ⊆ U) : IsLocallyConstant (fourierIntegral ψ μ L f) := by
  refine (IsLocallyConstant.iff_exists_open _).mpr fun w ↦
    ⟨_, U.isOpen_setOf_sub_mem_characterAnnihilator hU hψL w, by simp, fun w' hw' ↦ ?_⟩
  simpa using periodic_fourierIntegral ψ μ L hf hw' w

/-- **Compact support from a compact period annihilator.** If every element of `U` is a period of
`f` and the annihilator of `U` is compact in the `R₁` space `W`, the Fourier transform of `f` has
compact support. -/
theorem hasCompactSupport_fourierIntegral [MeasurableAdd V] [μ.IsAddRightInvariant]
    [TopologicalSpace W] [R1Space W] {f : V → E} {U : AddSubgroup V}
    (hf : ∀ u ∈ U, Periodic f u) (hU : IsCompact (U.characterAnnihilator ψ L : Set W)) :
    HasCompactSupport (fourierIntegral ψ μ L f) :=
  HasCompactSupport.of_support_subset_isCompact hU (support_fourierIntegral_subset ψ μ L hf)

/-- **Fourier inversion for a subgroup indicator.** Let `μ` on `V` and `ν` on `W` be
right-invariant, and let `A = U.characterAnnihilator ψ L`. If the annihilator of `A` for the
transposed pairing `L.flip` is contained in `U` (it always contains `U`), and the volumes satisfy
`μ.real U * ν.real A = 1`, then transforming `1_U · c` first for `(μ, L)` and then for
`(ν, L.flip)` returns `1_U · c`. Since `U = -U`, this is the inversion formula `𝓕 (𝓕 f) v = f (-v)`
for `f = 1_U · c`. -/
theorem fourierIntegral_fourierIntegral_indicator_addSubgroup [MeasurableAdd V]
    [μ.IsAddRightInvariant] [CompleteSpace E] [MeasurableSpace W] [MeasurableAdd W]
    (ν : Measure W) [ν.IsAddRightInvariant] {U : AddSubgroup V} (hU : MeasurableSet (U : Set V))
    (hA : MeasurableSet (U.characterAnnihilator ψ L : Set W))
    (hdual : (U.characterAnnihilator ψ L).characterAnnihilator ψ L.flip ≤ U)
    (hvol : μ.real U * ν.real (U.characterAnnihilator ψ L) = 1) (c : E) :
    fourierIntegral ψ ν L.flip (fourierIntegral ψ μ L ((U : Set V).indicator fun _ ↦ c)) =
      (U : Set V).indicator fun _ ↦ c := by
  rw [fourierIntegral_indicator_addSubgroup ψ μ L hU, fourierIntegral_indicator_addSubgroup ψ ν
    L.flip hA, le_antisymm hdual (U.le_characterAnnihilator_characterAnnihilator_flip ψ L),
    smul_smul, mul_comm, hvol, one_smul]

end VectorFourier
