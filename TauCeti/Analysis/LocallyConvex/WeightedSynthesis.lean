/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Group.Quotient
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient
public import TauCeti.Analysis.LocallyConvex.WithSeminorms
public import TauCeti.Analysis.Normed.Lp.Basic
public import TauCeti.Topology.Semicontinuity.Basic

/-!
# Separable Banach spaces of smooth directions from weighted series

Transversality arguments in Floer theory perturb the data (Hamiltonian terms, almost complex
structures) along a separable Banach space of *smooth* directions, so that the Sard–Smale theorem
applies to the universal moduli space while every perturbation stays smooth. Floer's `C_ε` space is
the classical example. This file constructs such a space from a countable family of smooth
directions by weighted series, in the following abstract form.

Let `E` be a complete Hausdorff space whose topology is given by a sequence of seminorms `p m` (for
instance smooth fields with the topology of `C^∞`-convergence on compact sets), and let `e ν` be a
sequence of elements of `E`, the *testing elements*. Fix numbers `a m ν ≥ p m (e ν)`; in
applications `a m ν = A m (e ν)` for a sequence of possibly infinite, lower semicontinuous
*controls* `A m ≥ p m` on `E`, such as weighted global `C^k` or `L^q` norms, all of which are finite
on the testing elements. The weight of `e ν` is

`w ν = 2 ^ ν * max 1 (a 0 ν, …, a ν ν)` (`TauCeti.synthesisWeight`),

so that `a m ν / w ν ≤ 2⁻ᵛ` as soon as `m ≤ ν`, and `a m ν / w ν` is bounded in `ν` by
`TauCeti.synthesisBound a m` for each fixed `m`.

The *weighted synthesis* (`TauCeti.weightedSynthesis`) sends a summable sequence `c ∈ ℓ¹` to

`∑' ν, (c ν / w ν) • e ν`.

Equivalently it sends `(c ν / w ν) ∈ ℓ¹(w)` to `∑ (c ν / w ν) • e ν`: the coefficient space is
`ℓ¹(w)`, identified isometrically with `ℓ¹`. The series converges in `E`
(`TauCeti.hasSum_weightedSynthesis`), so the synthesis is a continuous linear map with
`p m (S c) ≤ synthesisBound a m * ‖c‖` (`TauCeti.seminorm_weightedSynthesis_le`). Moreover, for
every lower semicontinuous subadditive and absolutely homogeneous `A : E → ℝ≥0∞` with
`A (e ν) ≤ a m ν`, the sum satisfies `A (S c) ≤ synthesisBound a m * ‖c‖ₑ`
(`TauCeti.apply_weightedSynthesis_le`) and the partial sums converge to it in `A`
(`TauCeti.tendsto_apply_weightedSynthesis_sub_sum`). Lower semicontinuity is what passes the bounds
on the partial sums to the limit, which converges only in the topology of `E`.

The synthesis is in general not injective. Its kernel is closed, and the quotient of `ℓ¹` by it is
the *synthesis carrier* `TauCeti.SynthesisCarrier`: a separable Banach space with a continuous
injective linear map `TauCeti.synthesisCarrierMap` into `E`, whose range contains every testing
element (`TauCeti.exists_synthesisCarrierMap_eq`) and is therefore dense when the testing elements
span a dense subspace (`TauCeti.denseRange_synthesisCarrierMap`). Every control `A` as above is
bounded on it by `synthesisBound a m` times the norm (`TauCeti.apply_synthesisCarrierMap_le`).

## Main definitions

* `TauCeti.synthesisWeight a ν`: the weight `2 ^ ν * max 1 (a 0 ν, …, a ν ν)`.
* `TauCeti.synthesisBound a m`: the bound `max 1 (a m 0, …, a m (m - 1))` for `a m ν / w ν`.
* `TauCeti.weightedSynthesis hp hpa`: the continuous linear map `c ↦ ∑' ν, (c ν / w ν) • e ν`
  from `ℓ¹` to `E`.
* `TauCeti.SynthesisCarrier hp hpa`: the quotient of `ℓ¹` by the kernel of the synthesis, a
  separable Banach space.
* `TauCeti.synthesisCarrierMap hp hpa`: the induced injective continuous linear map into `E`.
* `TauCeti.liftSynthesisCarrier hp hpa f hf`: the descent to the carrier of a continuous linear
  map `f` on `ℓ¹` vanishing on the kernel of the synthesis.

## References

* A. Floer, *The unregularized gradient flow of the symplectic action*, Comm. Pure Appl. Math. 41
  (1988), 775–813, Section 5 (the space `C_ε` of smooth perturbations).
* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, 2nd ed., AMS Colloquium
  Publications 52, 2012, Section 3.2 (Floer's `C_ε` space in transversality arguments).
-/

public section

open Filter Topology
open scoped NNReal ENNReal

namespace TauCeti

/-- The weight `2 ^ ν * max 1 (a 0 ν, …, a ν ν)` of the `ν`-th testing element, where `a m ν`
bounds the `m`-th control of the `ν`-th testing element. -/
noncomputable def synthesisWeight (a : ℕ → ℕ → ℝ≥0) (ν : ℕ) : ℝ≥0 :=
  2 ^ ν * max 1 ((Finset.range (ν + 1)).sup fun m ↦ a m ν)

/-- The bound `max 1 (a m 0, …, a m (m - 1))` for the weighted control values `a m ν / w ν`
(`TauCeti.div_synthesisWeight_le_synthesisBound`). -/
noncomputable def synthesisBound (a : ℕ → ℕ → ℝ≥0) (m : ℕ) : ℝ≥0 :=
  max 1 ((Finset.range m).sup fun ν ↦ a m ν)

section Weight

variable (a : ℕ → ℕ → ℝ≥0)

theorem synthesisWeight_def (ν : ℕ) :
    synthesisWeight a ν = 2 ^ ν * max 1 ((Finset.range (ν + 1)).sup fun m ↦ a m ν) := (rfl)

theorem synthesisBound_def (m : ℕ) :
    synthesisBound a m = max 1 ((Finset.range m).sup fun ν ↦ a m ν) := (rfl)

theorem one_le_synthesisWeight (ν : ℕ) : 1 ≤ synthesisWeight a ν :=
  one_le_mul_of_one_le_of_one_le (one_le_pow₀ one_le_two) (le_max_left _ _)

theorem synthesisWeight_pos (ν : ℕ) : 0 < synthesisWeight a ν :=
  zero_lt_one.trans_le (one_le_synthesisWeight a ν)

/-- The weight of the `ν`-th testing element dominates `2 ^ ν` times its first `ν + 1` control
values. -/
theorem two_pow_mul_le_synthesisWeight {m ν : ℕ} (h : m ≤ ν) :
    2 ^ ν * a m ν ≤ synthesisWeight a ν :=
  mul_le_mul_right (le_max_of_le_right (Finset.le_sup (f := fun m ↦ a m ν)
    (Finset.mem_range.2 (Nat.lt_succ_of_le h)))) _

/-- The weighted `m`-th control values decay geometrically from `ν = m` on. -/
theorem div_synthesisWeight_le_inv_two_pow {m ν : ℕ} (h : m ≤ ν) :
    a m ν / synthesisWeight a ν ≤ (2 ^ ν)⁻¹ := by
  rw [div_le_iff₀ (synthesisWeight_pos a ν), ← div_eq_inv_mul,
    le_div_iff₀ (pow_pos two_pos ν), mul_comm]
  exact two_pow_mul_le_synthesisWeight a h

theorem one_le_synthesisBound (m : ℕ) : 1 ≤ synthesisBound a m := le_max_left _ _

theorem synthesisBound_pos (m : ℕ) : 0 < synthesisBound a m :=
  zero_lt_one.trans_le (one_le_synthesisBound a m)

/-- The weighted `m`-th control values are bounded by `synthesisBound a m`. -/
theorem div_synthesisWeight_le_synthesisBound (m ν : ℕ) :
    a m ν / synthesisWeight a ν ≤ synthesisBound a m := by
  rcases lt_or_ge ν m with h | h
  · exact (div_le_self zero_le (one_le_synthesisWeight a ν)).trans
      (le_max_of_le_right (Finset.le_sup (f := fun ν ↦ a m ν) (Finset.mem_range.2 h)))
  · exact (div_synthesisWeight_le_inv_two_pow a h).trans
      ((inv_le_one_of_one_le₀ (one_le_pow₀ one_le_two)).trans (one_le_synthesisBound a m))

private theorem summable_norm_mul_div_synthesisWeight (c : lp (fun _ : ℕ ↦ ℝ) 1) (m : ℕ) :
    Summable fun ν ↦ ‖c ν‖ * (a m ν / synthesisWeight a ν : ℝ≥0) := by
  refine ((lp.hasSum_norm_one c).summable.mul_right (synthesisBound a m : ℝ)).of_nonneg_of_le
    (fun ν ↦ by positivity) fun ν ↦ mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  exact_mod_cast div_synthesisWeight_le_synthesisBound a m ν

private theorem tsum_enorm_div_mul_le {m : ℕ} {b : ℕ → ℝ≥0∞} (hb : ∀ ν, b ν ≤ a m ν)
    (c : lp (fun _ : ℕ ↦ ℝ) 1) :
    ∑' ν, ‖c ν‖ₑ / synthesisWeight a ν * b ν ≤ synthesisBound a m * ‖c‖ₑ := by
  calc ∑' ν, ‖c ν‖ₑ / synthesisWeight a ν * b ν ≤ ∑' ν, ‖c ν‖ₑ * synthesisBound a m := by
        refine tsum_le_tsum fun ν ↦ ?_
        calc ‖c ν‖ₑ / synthesisWeight a ν * b ν
            ≤ ‖c ν‖ₑ / synthesisWeight a ν * a m ν := by gcongr; exact hb ν
          _ = ‖c ν‖ₑ * ((a m ν / synthesisWeight a ν : ℝ≥0) : ℝ≥0∞) := by
            rw [ENNReal.coe_div (synthesisWeight_pos a ν).ne', div_eq_mul_inv, div_eq_mul_inv]
            ring
          _ ≤ ‖c ν‖ₑ * synthesisBound a m := by
            gcongr; exact_mod_cast div_synthesisWeight_le_synthesisBound a m ν
    _ = synthesisBound a m * ‖c‖ₑ := by
        rw [ENNReal.tsum_mul_right, (lp.hasSum_enorm_one c).tsum_eq, mul_comm]

end Weight

section Synthesis

section Term

variable {E : Type*} [AddCommGroup E] [Module ℝ E] {p : SeminormFamily ℝ E ℕ} {e : ℕ → E}
  {a : ℕ → ℕ → ℝ≥0}

private theorem seminorm_smul_le (hpa : ∀ m ν, p m (e ν) ≤ a m ν)
    (c : lp (fun _ : ℕ ↦ ℝ) 1) (m ν : ℕ) :
    p m ((c ν / synthesisWeight a ν) • e ν) ≤ ‖c ν‖ * (a m ν / synthesisWeight a ν : ℝ≥0) := by
  rw [map_smul_eq_mul, norm_div, Real.norm_of_nonneg (synthesisWeight a ν).coe_nonneg,
    NNReal.coe_div, mul_div_assoc', div_mul_eq_mul_div]
  gcongr
  exact hpa m ν

private theorem apply_smul_le {A : E → ℝ≥0∞} (hsmul : ∀ (r : ℝ) x, A (r • x) ≤ ‖r‖ₑ * A x)
    (c : lp (fun _ : ℕ ↦ ℝ) 1) (ν : ℕ) :
    A ((c ν / synthesisWeight a ν) • e ν) ≤ ‖c ν‖ₑ / synthesisWeight a ν * A (e ν) := by
  refine (hsmul _ _).trans_eq ?_
  simp [enorm_eq_nnnorm, nnnorm_div, ENNReal.coe_div, (synthesisWeight_pos a ν).ne']

end Term

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [UniformSpace E] [IsUniformAddGroup E]
  [CompleteSpace E] {p : SeminormFamily ℝ E ℕ} (hp : WithSeminorms p) {e : ℕ → E}
  {a : ℕ → ℕ → ℝ≥0} (hpa : ∀ m ν, p m (e ν) ≤ a m ν)

include hp hpa in
private theorem summable_synthesis (c : lp (fun _ : ℕ ↦ ℝ) 1) :
    Summable fun ν ↦ (c ν / synthesisWeight a ν) • e ν :=
  hp.summable_of_summable_seminorm fun m ↦
    (summable_norm_mul_div_synthesisWeight a c m).of_nonneg_of_le (fun _ ↦ apply_nonneg _ _)
      (seminorm_smul_le hpa c m)

include hp hpa in
private theorem seminorm_tsum_smul_le (c : lp (fun _ : ℕ ↦ ℝ) 1) (m : ℕ) :
    p m (∑' ν, (c ν / synthesisWeight a ν) • e ν) ≤ synthesisBound a m * ‖c‖ := by
  have hb := summable_norm_mul_div_synthesisWeight a c m
  have hc := lp.hasSum_norm_one c
  calc p m (∑' ν, (c ν / synthesisWeight a ν) • e ν)
      ≤ ∑' ν, p m ((c ν / synthesisWeight a ν) • e ν) :=
        Seminorm.map_tsum_le (hp.continuous_seminorm m) (summable_synthesis hp hpa c)
          (hb.of_nonneg_of_le (fun _ ↦ apply_nonneg _ _) (seminorm_smul_le hpa c m))
    _ ≤ ∑' ν, ‖c ν‖ * synthesisBound a m := by
        refine Summable.tsum_le_tsum (fun ν ↦ (seminorm_smul_le hpa c m ν).trans ?_)
          (hb.of_nonneg_of_le (fun _ ↦ apply_nonneg _ _) (seminorm_smul_le hpa c m))
          (hc.summable.mul_right _)
        exact mul_le_mul_of_nonneg_left (by exact_mod_cast
          div_synthesisWeight_le_synthesisBound a m ν) (norm_nonneg _)
    _ = synthesisBound a m * ‖c‖ := by rw [tsum_mul_right, hc.tsum_eq, mul_comm]

variable [T2Space E]

/-- The weighted synthesis `c ↦ ∑' ν, (c ν / w ν) • e ν` of the testing elements `e ν`, as a
continuous linear map from `ℓ¹` into `E`, for the weights `w = TauCeti.synthesisWeight a` built from
bounds `a m ν` on the seminorms `p m (e ν)`. -/
noncomputable def weightedSynthesis : lp (fun _ : ℕ ↦ ℝ) 1 →L[ℝ] E :=
  haveI := hp.continuousSMul
  let L : lp (fun _ : ℕ ↦ ℝ) 1 →ₗ[ℝ] E :=
    { toFun c := ∑' ν, (c ν / synthesisWeight a ν) • e ν
      map_add' c d := by
        rw [← (summable_synthesis hp hpa c).tsum_add (summable_synthesis hp hpa d)]
        simp [add_div, add_smul]
      map_smul' r c := by
        rw [RingHom.id_apply, ← (summable_synthesis hp hpa c).tsum_const_smul r]
        simp [mul_div_assoc, mul_smul] }
  ⟨L, hp.continuous_normedSpace_dom _ L fun m ↦ ⟨synthesisBound a m, fun c ↦ by
    simpa [L, NNReal.smul_def] using seminorm_tsum_smul_le hp hpa c m⟩⟩

theorem weightedSynthesis_apply (c : lp (fun _ : ℕ ↦ ℝ) 1) :
    weightedSynthesis hp hpa c = ∑' ν, (c ν / synthesisWeight a ν) • e ν := (rfl)

/-- The weighted series of the testing elements converges in `E` to the weighted synthesis. -/
theorem hasSum_weightedSynthesis (c : lp (fun _ : ℕ ↦ ℝ) 1) :
    HasSum (fun ν ↦ (c ν / synthesisWeight a ν) • e ν) (weightedSynthesis hp hpa c) :=
  (summable_synthesis hp hpa c).hasSum

@[simp]
theorem weightedSynthesis_single (ν : ℕ) (r : ℝ) :
    weightedSynthesis hp hpa (lp.single 1 ν r) = (r / synthesisWeight a ν) • e ν := by
  classical
  rw [weightedSynthesis_apply, tsum_eq_single ν fun μ hμ ↦ by simp [Pi.single_eq_of_ne hμ]]
  simp

/-- The `m`-th seminorm of the weighted synthesis is bounded by `synthesisBound a m` times the
`ℓ¹` norm. -/
theorem seminorm_weightedSynthesis_le (m : ℕ) (c : lp (fun _ : ℕ ↦ ℝ) 1) :
    p m (weightedSynthesis hp hpa c) ≤ synthesisBound a m * ‖c‖ :=
  seminorm_tsum_smul_le hp hpa c m

section Control

variable {A : E → ℝ≥0∞}

/-- A lower semicontinuous subadditive and absolutely homogeneous control `A` of the weighted
synthesis is at most the weighted sum of its values on the testing elements. -/
theorem apply_weightedSynthesis_le_tsum (hA : LowerSemicontinuous A)
    (hadd : ∀ x y, A (x + y) ≤ A x + A y) (hsmul : ∀ (r : ℝ) x, A (r • x) ≤ ‖r‖ₑ * A x)
    (c : lp (fun _ : ℕ ↦ ℝ) 1) :
    A (weightedSynthesis hp hpa c) ≤ ∑' ν, ‖c ν‖ₑ / synthesisWeight a ν * A (e ν) := by
  have h0 : A 0 = 0 := le_antisymm (by simpa using hsmul 0 0) zero_le
  exact (hA.le_tsum_of_hasSum h0 hadd (hasSum_weightedSynthesis hp hpa c)).trans
    (tsum_le_tsum (apply_smul_le hsmul c))

/-- A lower semicontinuous subadditive and absolutely homogeneous control `A` bounded on the
testing elements by the `m`-th bounds `a m ν` is bounded on the weighted synthesis by
`synthesisBound a m` times the `ℓ¹` norm. -/
theorem apply_weightedSynthesis_le (hA : LowerSemicontinuous A)
    (hadd : ∀ x y, A (x + y) ≤ A x + A y) (hsmul : ∀ (r : ℝ) x, A (r • x) ≤ ‖r‖ₑ * A x)
    {m : ℕ} (hAa : ∀ ν, A (e ν) ≤ a m ν) (c : lp (fun _ : ℕ ↦ ℝ) 1) :
    A (weightedSynthesis hp hpa c) ≤ synthesisBound a m * ‖c‖ₑ :=
  (apply_weightedSynthesis_le_tsum hp hpa hA hadd hsmul c).trans (tsum_enorm_div_mul_le a hAa c)

/-- The partial sums of the weighted series converge to the weighted synthesis in every lower
semicontinuous subadditive and absolutely homogeneous control `A` bounded on the testing elements
by the `m`-th bounds `a m ν`. -/
theorem tendsto_apply_weightedSynthesis_sub_sum (hA : LowerSemicontinuous A)
    (hadd : ∀ x y, A (x + y) ≤ A x + A y) (hsmul : ∀ (r : ℝ) x, A (r • x) ≤ ‖r‖ₑ * A x)
    {m : ℕ} (hAa : ∀ ν, A (e ν) ≤ a m ν) (c : lp (fun _ : ℕ ↦ ℝ) 1) :
    Tendsto (fun N ↦ A (weightedSynthesis hp hpa c -
      ∑ ν ∈ Finset.range N, (c ν / synthesisWeight a ν) • e ν)) atTop (𝓝 0) := by
  have h0 : A 0 = 0 := le_antisymm (by simpa using hsmul 0 0) zero_le
  set g : ℕ → ℝ≥0∞ := fun ν ↦ ‖c ν‖ₑ / synthesisWeight a ν * A (e ν)
  have hg : ∑' ν, g ν ≠ ∞ :=
    ((tsum_enorm_div_mul_le a hAa c).trans_lt (by simp [ENNReal.mul_lt_top])).ne
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (ENNReal.tendsto_sum_nat_add g hg) (fun _ ↦ zero_le) fun N ↦ ?_
  -- The difference is the tail of the series, bounded by the tail of `∑ g`.
  have hs := summable_synthesis hp hpa c
  have htail : HasSum (fun k ↦ (c (k + N) / synthesisWeight a (k + N)) • e (k + N))
      (weightedSynthesis hp hpa c - ∑ ν ∈ Finset.range N, (c ν / synthesisWeight a ν) • e ν) := by
    rw [weightedSynthesis_apply, ← hs.sum_add_tsum_nat_add N, add_sub_cancel_left]
    exact ((summable_nat_add_iff N).2 hs).hasSum
  exact (hA.le_tsum_of_hasSum h0 hadd htail).trans
    (tsum_le_tsum fun k ↦ apply_smul_le hsmul c (k + N))

end Control

section Carrier

/-- The synthesis carrier: the quotient of `ℓ¹` by the closed kernel of the weighted synthesis. It
is a separable Banach space, mapped injectively into `E` by `TauCeti.synthesisCarrierMap`. -/
def SynthesisCarrier : Type :=
  lp (fun _ : ℕ ↦ ℝ) 1 ⧸ (weightedSynthesis hp hpa).ker

noncomputable instance : NormedAddCommGroup (SynthesisCarrier hp hpa) :=
  haveI : IsClosed ((weightedSynthesis hp hpa).ker : Set (lp (fun _ : ℕ ↦ ℝ) 1)) :=
    (weightedSynthesis hp hpa).isClosed_ker
  inferInstanceAs (NormedAddCommGroup (_ ⧸ (weightedSynthesis hp hpa).ker))

noncomputable instance : NormedSpace ℝ (SynthesisCarrier hp hpa) :=
  inferInstanceAs (NormedSpace ℝ (_ ⧸ (weightedSynthesis hp hpa).ker))

instance : CompleteSpace (SynthesisCarrier hp hpa) :=
  inferInstanceAs (CompleteSpace (_ ⧸ (weightedSynthesis hp hpa).ker))

/-- The quotient map from `ℓ¹` onto the synthesis carrier. -/
noncomputable def toSynthesisCarrier : lp (fun _ : ℕ ↦ ℝ) 1 →L[ℝ] SynthesisCarrier hp hpa :=
  (weightedSynthesis hp hpa).ker.mkQL

/-- The injective continuous linear map from the synthesis carrier into `E` induced by the weighted
synthesis. -/
noncomputable def synthesisCarrierMap : SynthesisCarrier hp hpa →L[ℝ] E :=
  (weightedSynthesis hp hpa).ker.liftQL (weightedSynthesis hp hpa) le_rfl

instance : TopologicalSpace.SeparableSpace (SynthesisCarrier hp hpa) :=
  haveI := lp.separableSpace (E := fun _ : ℕ ↦ ℝ) (p := 1) ENNReal.one_ne_top
  (Submodule.isQuotientMap_mkQL (weightedSynthesis hp hpa).ker).separableSpace

@[simp]
theorem synthesisCarrierMap_toSynthesisCarrier (c : lp (fun _ : ℕ ↦ ℝ) 1) :
    synthesisCarrierMap hp hpa (toSynthesisCarrier hp hpa c) = weightedSynthesis hp hpa c := (rfl)

theorem toSynthesisCarrier_surjective : Function.Surjective (toSynthesisCarrier hp hpa) :=
  Submodule.mkQ_surjective _

theorem synthesisCarrierMap_injective : Function.Injective (synthesisCarrierMap hp hpa) :=
  LinearMap.ker_eq_bot.1 (Submodule.ker_liftQ_eq_bot _ _ _ le_rfl)

/-- Two sequences have the same image in the synthesis carrier exactly when they have the same
weighted synthesis. -/
theorem toSynthesisCarrier_eq_toSynthesisCarrier_iff {c d : lp (fun _ : ℕ ↦ ℝ) 1} :
    toSynthesisCarrier hp hpa c = toSynthesisCarrier hp hpa d ↔
      weightedSynthesis hp hpa c = weightedSynthesis hp hpa d := by
  rw [← synthesisCarrierMap_toSynthesisCarrier, ← synthesisCarrierMap_toSynthesisCarrier]
  exact (synthesisCarrierMap_injective hp hpa).eq_iff.symm

theorem norm_toSynthesisCarrier_le (c : lp (fun _ : ℕ ↦ ℝ) 1) :
    ‖toSynthesisCarrier hp hpa c‖ ≤ ‖c‖ :=
  Submodule.Quotient.norm_mk_le _ c

section Lift

variable {F : Type*} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]

/-- A continuous linear map on `ℓ¹` vanishing on the kernel of the weighted synthesis descends to
the synthesis carrier. -/
noncomputable def liftSynthesisCarrier (f : lp (fun _ : ℕ ↦ ℝ) 1 →L[ℝ] F)
    (hf : (weightedSynthesis hp hpa).ker ≤ f.ker) : SynthesisCarrier hp hpa →L[ℝ] F :=
  (weightedSynthesis hp hpa).ker.liftQL f hf

@[simp]
theorem liftSynthesisCarrier_toSynthesisCarrier (f : lp (fun _ : ℕ ↦ ℝ) 1 →L[ℝ] F)
    (hf : (weightedSynthesis hp hpa).ker ≤ f.ker) (c : lp (fun _ : ℕ ↦ ℝ) 1) :
    liftSynthesisCarrier hp hpa f hf (toSynthesisCarrier hp hpa c) = f c := (rfl)

/-- Two continuous linear maps on the synthesis carrier agreeing after composition with
`TauCeti.toSynthesisCarrier` are equal. -/
theorem synthesisCarrier_continuousLinearMap_ext {g₁ g₂ : SynthesisCarrier hp hpa →L[ℝ] F}
    (h : g₁ ∘L toSynthesisCarrier hp hpa = g₂ ∘L toSynthesisCarrier hp hpa) : g₁ = g₂ :=
  ContinuousLinearMap.ext fun x ↦ by
    obtain ⟨c, rfl⟩ := toSynthesisCarrier_surjective hp hpa x
    exact congr($h c)

/-- `TauCeti.liftSynthesisCarrier f hf` is the unique continuous linear map on the synthesis
carrier whose composition with `TauCeti.toSynthesisCarrier` is `f`. -/
theorem liftSynthesisCarrier_unique (f : lp (fun _ : ℕ ↦ ℝ) 1 →L[ℝ] F)
    (hf : (weightedSynthesis hp hpa).ker ≤ f.ker) {g : SynthesisCarrier hp hpa →L[ℝ] F}
    (hg : g ∘L toSynthesisCarrier hp hpa = f) : g = liftSynthesisCarrier hp hpa f hf :=
  synthesisCarrier_continuousLinearMap_ext hp hpa (by rw [hg]; rfl)

end Lift

/-- Every testing element lies in the range of the synthesis carrier. -/
theorem exists_synthesisCarrierMap_eq (ν : ℕ) : ∃ x, synthesisCarrierMap hp hpa x = e ν := by
  refine ⟨toSynthesisCarrier hp hpa (lp.single 1 ν (synthesisWeight a ν)), ?_⟩
  rw [synthesisCarrierMap_toSynthesisCarrier, weightedSynthesis_single,
    div_self (NNReal.coe_ne_zero.2 (synthesisWeight_pos a ν).ne'), one_smul]

/-- If the testing elements span a dense subspace of `E`, then the synthesis carrier has dense
range in `E`. -/
theorem denseRange_synthesisCarrierMap (h : Dense (Submodule.span ℝ (Set.range e) : Set E)) :
    DenseRange (synthesisCarrierMap hp hpa) := by
  have hle : Submodule.span ℝ (Set.range e) ≤
      LinearMap.range (synthesisCarrierMap hp hpa : SynthesisCarrier hp hpa →ₗ[ℝ] E) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨ν, rfl⟩
    exact exists_synthesisCarrierMap_eq hp hpa ν
  exact h.mono fun y hy ↦ LinearMap.mem_range.1 (hle hy)

/-- A lower semicontinuous subadditive and absolutely homogeneous control `A` bounded on the
testing elements by the `m`-th bounds `a m ν` is bounded on the synthesis carrier by
`synthesisBound a m` times its norm. -/
theorem apply_synthesisCarrierMap_le {A : E → ℝ≥0∞} (hA : LowerSemicontinuous A)
    (hadd : ∀ x y, A (x + y) ≤ A x + A y) (hsmul : ∀ (r : ℝ) x, A (r • x) ≤ ‖r‖ₑ * A x)
    {m : ℕ} (hAa : ∀ ν, A (e ν) ≤ a m ν) (x : SynthesisCarrier hp hpa) :
    A (synthesisCarrierMap hp hpa x) ≤ synthesisBound a m * ‖x‖ₑ := by
  have hB := synthesisBound_pos a m
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ ↦ ?_
  -- Represent `x` by a sequence `c` whose norm exceeds that of `x` by less than `ε / B`.
  obtain ⟨c, rfl, hc⟩ := Submodule.Quotient.norm_mk_lt (S := (weightedSynthesis hp hpa).ker) x
    (div_pos (NNReal.coe_pos.2 hε) (NNReal.coe_pos.2 hB))
  calc A (synthesisCarrierMap hp hpa (toSynthesisCarrier hp hpa c))
      ≤ synthesisBound a m * ‖c‖ₑ := apply_weightedSynthesis_le hp hpa hA hadd hsmul hAa c
    _ ≤ synthesisBound a m *
          ENNReal.ofReal (‖toSynthesisCarrier hp hpa c‖ + ε / synthesisBound a m) := by
        rw [← ofReal_norm]
        gcongr
        exact hc.le
    _ = synthesisBound a m * ‖toSynthesisCarrier hp hpa c‖ₑ + ε := by
        rw [ENNReal.ofReal_add (norm_nonneg _) (by positivity), mul_add, ofReal_norm,
          ← NNReal.coe_div, ENNReal.ofReal_coe_nnreal, ← ENNReal.coe_mul,
          mul_div_cancel₀ _ hB.ne']

end Carrier

end Synthesis

end TauCeti
