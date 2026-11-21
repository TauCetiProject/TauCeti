/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.FunctionalSpaces.BesselPotentialSpace
public import TauCeti.Analysis.Distribution.Sobolev
public import TauCeti.Analysis.Distribution.TemperedDistribution.MulLeft
import TauCeti.Analysis.Calculus.ContDiff.Bounds
import TauCeti.Analysis.Calculus.IteratedFDeriv.FDerivApply
import TauCeti.Analysis.Distribution.TemperateGrowth
import TauCeti.Analysis.Distribution.TemperedDistribution.Lp
import TauCeti.Analysis.Distribution.TemperedDistribution.SmulLeft
import TauCeti.Analysis.Sobolev.BesselPotential.Inclusion
import TauCeti.Analysis.Sobolev.BesselPotential.Postcomp

/-!
# Multiplication by functions with bounded derivatives on `H^{k,p}(ℝⁿ)`

Let `g` be a scalar function of temperate growth whose iterated derivatives of order at most `|k|`
are bounded. For `1 < p < ∞`, multiplication by `g` maps the Bessel-potential space `H^{k,p}` of
integer order `k`, positive or negative, into itself: if a tempered distribution `f` lies in
`H^{k,p}`, then so does `g f`. For `k ≥ 0` this is
`TemperedDistribution.MemSobolev.smulLeftCLM_of_norm_iteratedFDeriv_le`, and for negative orders
`TemperedDistribution.MemSobolev.smulLeftCLM_of_norm_iteratedFDeriv_le_neg`. Here `g f` is
Mathlib's `TemperedDistribution.smulLeftCLM`.

Unlike multiplication by Schwartz functions, the multiplier need not decay. Typical examples are
smooth functions which outside a ball agree with a winding phase `(z / |z|) ^ m` or with a
coefficient of the angular form `dθ`, such as the reference fields of framed vortices on the plane.
These multipliers appear in the linear terms of nonlinear field equations on affine Sobolev spaces
centred at such a reference field. The same applies to scalar coefficients with bounded
derivatives, such as the coefficients of a differential operator.

Matrix-valued multipliers `A : E → (F →L[ℂ] G)` between finite-dimensional spaces, such as the
changes of frame of a vector bundle read in a chart, act on tempered distributions by
`TemperedDistribution.mulLeftCLM A`, which is `∑ᵢ bᵢ (gᵢ f)` for the coordinates `gᵢ` of `A` in a
basis `(bᵢ)` of `F →L[ℂ] G`. The coordinates inherit the derivative bounds of `A`, so the scalar
results give `A f ∈ H^{k,p}(E, G)` for `f ∈ H^{k,p}(E, F)`. The closed graph theorem turns this
into a bounded operator `H^{k,p}(E, F) → H^{k,p}(E, G)`, and pointwise inverse frame changes give
mutually inverse operators, hence an isomorphism `H^{k,p}(E, F) ≃L[ℂ] H^{k,p}(E, G)`.

Both scalar results are proved by induction on `k`, starting from `H^{0,p} = Lᵖ`, which a
bounded `g` multiplies into itself (`TemperedDistribution.MemSobolev.smulLeftCLM_of_norm_le`). Going
up, a distribution lies in `H^{k+1,p}` exactly when it lies in `Lᵖ` and its directional derivatives
lie in `H^{k,p}` (`TemperedDistribution.memSobolev_natCast_add_one_iff`, which uses `1 < p < ∞`).
By the Leibniz rule (`TemperedDistribution.lineDerivOp_smulLeftCLM`)
`∂_v (g f) = (∂_v g) f + g ∂_v f`, and both terms are of order `k`: `∂_v g` has bounded derivatives
up to order `k` and `f ∈ H^{k,p}`, while `∂_v f ∈ H^{k,p}`. Going down, a distribution lies in
`H^{-k-1,p}` exactly when it is `u + ∑ᵢ ∂ᵢ wᵢ` with `u` and `wᵢ` in `H^{-k,p}`
(`TemperedDistribution.memSobolev_sub_one_iff`). The Leibniz rule turns `g f` into
`g u - ∑ᵢ (∂ᵢ g) wᵢ + ∑ᵢ ∂ᵢ (g wᵢ)`, again of this form.

## Main results

* `TemperedDistribution.MemSobolev.smulLeftCLM_of_norm_le`: a bounded function of temperate
  growth multiplies `H^{0,p}` into itself, for every `1 ≤ p ≤ ∞`.
* `TemperedDistribution.MemSobolev.smulLeftCLM_of_norm_iteratedFDeriv_le`: a function of temperate
  growth with bounded derivatives up to order `k` multiplies `H^{k,p}` into itself, for
  `1 < p < ∞`.
* `TemperedDistribution.MemSobolev.smulLeftCLM_of_norm_iteratedFDeriv_le_neg`: the same for the
  negative order `H^{-k,p}`.
* `TemperedDistribution.MemSobolev.smulLeftCLM_of_norm_iteratedFDeriv_le_intCast`: the two
  combined, for `H^{k,p}` with `k ∈ ℤ` and bounded derivatives up to order `|k|`.
* `TemperedDistribution.MemSobolev.mulLeftCLM_of_forall_smulLeftCLM`: a matrix-valued multiplier
  `A` preserves `H^{s,p}` if each scalar multiplier `ℓ ∘ A` does.
* `TemperedDistribution.MemSobolev.mulLeftCLM_of_norm_iteratedFDeriv_le_intCast`: a
  matrix-valued `A` of temperate growth with bounded derivatives up to order `|k|` maps
  `H^{k,p}(E, F)` into `H^{k,p}(E, G)`, for `k ∈ ℤ` and `1 < p < ∞`.
* `BesselPotentialSpace.mulLeftCLM`: multiplication by `A` as a bounded operator
  `H^{k,p}(E, F) →L[ℂ] H^{k,p}(E, G)`.
* `BesselPotentialSpace.mulLeftEquiv`: for pointwise inverse `A` and `B` with bounded
  derivatives, the isomorphism `H^{k,p}(E, F) ≃L[ℂ] H^{k,p}(E, G)`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  AMS, 2010, §5.2.3, Theorem 1 (the Leibniz formula for weak derivatives).
* J. Bergh and J. Löfström, *Interpolation Spaces*, Springer, 1976, §6.2 (the Bessel-potential
  spaces `H^{s,p}` and the isomorphisms `J^r : H^{s,p} → H^{s-r,p}`).
-/

public section

namespace TemperedDistribution

open MeasureTheory
open scoped SchwartzMap LineDeriv ENNReal

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- **A bounded multiplier acts on `H^{0,p} = Lᵖ`.** If `g` has temperate growth and is bounded,
then `g f ∈ H^{0,p}` for every `f ∈ H^{0,p}`. -/
theorem MemSobolev.smulLeftCLM_of_norm_le [NormedSpace ℂ F] [CompleteSpace F] {g : E → ℂ}
    (hg : g.HasTemperateGrowth) {C : ℝ} (hC : ∀ x, ‖g x‖ ≤ C) {f : 𝓢'(E, F)}
    (hf : MemSobolev 0 p f) : MemSobolev 0 p (smulLeftCLM F g f) := by
  obtain ⟨f', rfl⟩ := memSobolev_zero_iff.1 hf
  obtain ⟨v, hv, -⟩ := Lp.exists_smulLeftCLM_toTemperedDistribution_eq_and_norm_le hg hC f'
  rw [hv]
  exact memSobolev_zero_iff.2 ⟨_, rfl⟩

section Reduction

variable [NormedSpace ℂ F] [CompleteSpace F] [FiniteDimensional ℂ F] {G : Type*}
  [NormedAddCommGroup G] [NormedSpace ℂ G] [CompleteSpace G] [FiniteDimensional ℂ G]

/-- **Reduction of matrix multipliers to scalar ones.** If multiplication by each scalar function
`x ↦ ℓ (A x)`, for `ℓ` a linear functional on `F →L[ℂ] G`, sends `f` into `H^{s,p}(E, F)`, then
`A f ∈ H^{s,p}(E, G)`: `A f = ∑ᵢ bᵢ (gᵢ f)` for a basis `(bᵢ)` of `F →L[ℂ] G`, with coordinates
`gᵢ = bᵢ* ∘ A`. -/
theorem MemSobolev.mulLeftCLM_of_forall_smulLeftCLM {s : ℝ} {A : E → F →L[ℂ] G} {f : 𝓢'(E, F)}
    (h : ∀ ℓ : (F →L[ℂ] G) →L[ℂ] ℂ, MemSobolev s p (smulLeftCLM F (fun x ↦ ℓ (A x)) f)) :
    MemSobolev s p (mulLeftCLM A f) := by
  rw [mulLeftCLM_def]
  simp only [sum_apply, ContinuousLinearMap.comp_apply]
  exact MemSobolev.sum fun i _ ↦
    (h (LinearMap.toContinuousLinearMap ((Module.finBasis ℂ (F →L[ℂ] G)).coord i))).postcomp _

end Reduction

variable [InnerProductSpace ℂ F] [CompleteSpace F]

/-- **Multipliers with bounded derivatives act on `H^{k,p}`.** Let `1 < p < ∞` and let `g` be a
function of temperate growth whose iterated derivatives of order at most `k` are bounded. Then
`g f ∈ H^{k,p}` for every `f ∈ H^{k,p}`. -/
theorem MemSobolev.smulLeftCLM_of_norm_iteratedFDeriv_le (hp : 1 < p) (hp_top : p ≠ ∞) {k : ℕ}
    {g : E → ℂ} (hg : g.HasTemperateGrowth)
    (hbd : ∀ n ≤ k, ∃ C, ∀ x, ‖iteratedFDeriv ℝ n g x‖ ≤ C) {f : 𝓢'(E, F)}
    (hf : MemSobolev k p f) : MemSobolev k p (smulLeftCLM F g f) := by
  induction k generalizing g f with
  | zero =>
    obtain ⟨C, hC⟩ := hbd 0 le_rfl
    rw [Nat.cast_zero] at hf ⊢
    exact hf.smulLeftCLM_of_norm_le hg (C := C) (fun x ↦ by simpa using hC x)
  | succ k ih =>
    rw [Nat.cast_succ] at hf ⊢
    have hf' := (memSobolev_natCast_add_one_iff hp hp_top).1 hf
    refine (memSobolev_natCast_add_one_iff hp hp_top).2 ⟨?_, fun v ↦ ?_⟩
    · obtain ⟨C, hC⟩ := hbd 0 (by omega)
      exact hf'.1.smulLeftCLM_of_norm_le hg (C := C) (fun x ↦ by simpa using hC x)
    -- `∂_v (g f) = (∂_v g) f + g ∂_v f`, and `∂_v g` has bounded derivatives up to order `k`.
    rw [lineDerivOp_smulLeftCLM hg]
    exact (ih (hg.fderiv_apply v) (hg.1.exists_bound_iteratedFDeriv_fderiv_apply (by simp) hbd v)
      (hf.mono_of_one_lt hp hp_top (by linarith))).add
      (ih hg (fun n hn ↦ hbd n (by omega)) (hf'.2 v))

/-- **Multipliers with bounded derivatives act on `H^{-k,p}`.** Let `1 < p < ∞` and let `g` be a
function of temperate growth whose iterated derivatives of order at most `k` are bounded. Then
`g f ∈ H^{-k,p}` for every `f ∈ H^{-k,p}`. -/
theorem MemSobolev.smulLeftCLM_of_norm_iteratedFDeriv_le_neg (hp : 1 < p) (hp_top : p ≠ ∞)
    {k : ℕ} {g : E → ℂ} (hg : g.HasTemperateGrowth)
    (hbd : ∀ n ≤ k, ∃ C, ∀ x, ‖iteratedFDeriv ℝ n g x‖ ≤ C) {f : 𝓢'(E, F)}
    (hf : MemSobolev (-k) p f) : MemSobolev (-k) p (smulLeftCLM F g f) := by
  induction k generalizing g f with
  | zero =>
    obtain ⟨C, hC⟩ := hbd 0 le_rfl
    rw [Nat.cast_zero, neg_zero] at hf ⊢
    exact hf.smulLeftCLM_of_norm_le hg (C := C) (fun x ↦ by simpa using hC x)
  | succ k ih =>
    have hk : -((k + 1 : ℕ) : ℝ) = -k - 1 := by push_cast; ring
    rw [hk] at hf ⊢
    -- Write `f = u + ∑ᵢ ∂ᵢ wᵢ` with `u` and `wᵢ` in `H^{-k,p}`. Then
    -- `g f = g u + ∑ᵢ (∂ᵢ (g wᵢ) - (∂ᵢ g) wᵢ)`, each of whose terms lies in `H^{-k-1,p}`.
    have hbd' : ∀ n ≤ k, ∃ C, ∀ x, ‖iteratedFDeriv ℝ n g x‖ ≤ C := fun n hn ↦ hbd n (by omega)
    obtain ⟨u, w, hu, hw, rfl⟩ :=
      (memSobolev_sub_one_iff hp hp_top (stdOrthonormalBasis ℝ E)).1 hf
    refine (memSobolev_sub_one_iff hp hp_top (stdOrthonormalBasis ℝ E)).2
      ⟨smulLeftCLM F g u - ∑ i, smulLeftCLM F (fun x ↦ fderiv ℝ g x (stdOrthonormalBasis ℝ E i))
        (w i), fun i ↦ smulLeftCLM F g (w i), ?_, fun i ↦ ih hg hbd' (hw i), ?_⟩
    · exact (ih hg hbd' hu).sub (MemSobolev.sum fun i _ ↦ ih (hg.fderiv_apply _)
        (hg.1.exists_bound_iteratedFDeriv_fderiv_apply (by simp) hbd _) (hw i))
    · simp only [map_add, map_sum, lineDerivOp_smulLeftCLM hg]
      rw [Finset.sum_add_distrib]
      abel

/-- **Multipliers with bounded derivatives act on `H^{k,p}` for every integer `k`.** Let
`1 < p < ∞` and let `g` be a function of temperate growth whose iterated derivatives of order at
most `|k|` are bounded. Then `g f ∈ H^{k,p}` for every `f ∈ H^{k,p}`. -/
theorem MemSobolev.smulLeftCLM_of_norm_iteratedFDeriv_le_intCast (hp : 1 < p) (hp_top : p ≠ ∞)
    {k : ℤ} {g : E → ℂ} (hg : g.HasTemperateGrowth)
    (hbd : ∀ n ≤ k.natAbs, ∃ C, ∀ x, ‖iteratedFDeriv ℝ n g x‖ ≤ C) {f : 𝓢'(E, F)}
    (hf : MemSobolev k p f) : MemSobolev k p (smulLeftCLM F g f) := by
  obtain ⟨k, rfl | rfl⟩ := k.eq_nat_or_neg
  · exact_mod_cast hf.smulLeftCLM_of_norm_iteratedFDeriv_le hp hp_top hg (by simpa using hbd)
  · push_cast at hf ⊢
    exact hf.smulLeftCLM_of_norm_iteratedFDeriv_le_neg hp hp_top hg (by simpa using hbd)

section Matrix

variable [FiniteDimensional ℂ F] {G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G]
  [CompleteSpace G] [FiniteDimensional ℂ G]

/-- **Matrix multipliers with bounded derivatives act on `H^{k,p}` for every integer `k`.** Let
`1 < p < ∞`, let `F` and `G` be finite-dimensional, and let `A : E → (F →L[ℂ] G)` be a function of
temperate growth whose iterated derivatives of order at most `|k|` are bounded. Then
`A f ∈ H^{k,p}(E, G)` for every `f ∈ H^{k,p}(E, F)`. -/
theorem MemSobolev.mulLeftCLM_of_norm_iteratedFDeriv_le_intCast (hp : 1 < p) (hp_top : p ≠ ∞)
    {k : ℤ} {A : E → F →L[ℂ] G} (hA : A.HasTemperateGrowth)
    (hbd : ∀ n ≤ k.natAbs, ∃ C, ∀ x, ‖iteratedFDeriv ℝ n A x‖ ≤ C) {f : 𝓢'(E, F)}
    (hf : MemSobolev k p f) : MemSobolev k p (mulLeftCLM A f) :=
  -- Each scalar function `ℓ ∘ A` inherits the derivative bounds of `A`.
  MemSobolev.mulLeftCLM_of_forall_smulLeftCLM fun ℓ ↦
    hf.smulLeftCLM_of_norm_iteratedFDeriv_le_intCast hp hp_top
      (hA.continuousLinearMap_comp ℓ)
      (ℓ.exists_bound_iteratedFDeriv_comp_left (hA.1.of_le (mod_cast le_top)) hbd)

end Matrix

end TemperedDistribution

namespace BesselPotentialSpace

open TemperedDistribution

open scoped SchwartzMap ENNReal

variable {E F G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [CompleteSpace F] [FiniteDimensional ℂ F] {p : ℝ≥0∞} [Fact (1 ≤ p)] {k : ℤ}

/-- **Multiplication by a matrix-valued function with bounded derivatives**, as a bounded operator
`H^{k,p}(E, F) → H^{k,p}(E, G)` for an integer `k` and `1 < p < ∞`. On the underlying tempered
distributions it is `TemperedDistribution.mulLeftCLM A`
(`BesselPotentialSpace.toDistr_mulLeftCLM`). -/
noncomputable def mulLeftCLM [NormedAddCommGroup G] [NormedSpace ℂ G] [CompleteSpace G]
    [FiniteDimensional ℂ G] (hp : 1 < p) (hp_top : p ≠ ∞) {A : E → F →L[ℂ] G}
    (hA : A.HasTemperateGrowth) (hbd : ∀ n ≤ k.natAbs, ∃ C, ∀ x, ‖iteratedFDeriv ℝ n A x‖ ≤ C) :
    H^{k, p}(E, F) →L[ℂ] H^{k, p}(E, G) :=
  mapCLM (TemperedDistribution.mulLeftCLM A) fun u ↦
    u.memSobolev_toDistr.mulLeftCLM_of_norm_iteratedFDeriv_le_intCast hp hp_top hA hbd

@[simp]
theorem toDistr_mulLeftCLM [NormedAddCommGroup G] [NormedSpace ℂ G] [CompleteSpace G]
    [FiniteDimensional ℂ G] (hp : 1 < p) (hp_top : p ≠ ∞) {A : E → F →L[ℂ] G}
    (hA : A.HasTemperateGrowth) (hbd : ∀ n ≤ k.natAbs, ∃ C, ∀ x, ‖iteratedFDeriv ℝ n A x‖ ≤ C)
    (u : H^{k, p}(E, F)) :
    (mulLeftCLM hp hp_top hA hbd u).toDistr = TemperedDistribution.mulLeftCLM A u.toDistr :=
  toDistr_mapCLM _ _ u

variable [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G] [FiniteDimensional ℂ G]

/-- **Changes of frame are isomorphisms of `H^{k,p}`.** If `A : E → (F →L[ℂ] G)` and
`B : E → (G →L[ℂ] F)` are pointwise inverse functions of temperate growth whose iterated derivatives
of order at most `|k|` are bounded, multiplication by `A` is an isomorphism
`H^{k,p}(E, F) ≃L[ℂ] H^{k,p}(E, G)`, with inverse multiplication by `B`. -/
noncomputable def mulLeftEquiv (hp : 1 < p) (hp_top : p ≠ ∞) {A : E → F →L[ℂ] G}
    {B : E → G →L[ℂ] F} (hA : A.HasTemperateGrowth) (hB : B.HasTemperateGrowth)
    (hAbd : ∀ n ≤ k.natAbs, ∃ C, ∀ x, ‖iteratedFDeriv ℝ n A x‖ ≤ C)
    (hBbd : ∀ n ≤ k.natAbs, ∃ C, ∀ x, ‖iteratedFDeriv ℝ n B x‖ ≤ C)
    (hBA : ∀ x, B x ∘L A x = ContinuousLinearMap.id ℂ F)
    (hAB : ∀ x, A x ∘L B x = ContinuousLinearMap.id ℂ G) :
    H^{k, p}(E, F) ≃L[ℂ] H^{k, p}(E, G) :=
  ContinuousLinearEquiv.ofContinuousLinearMap (mulLeftCLM hp hp_top hA hAbd)
    (mulLeftCLM hp hp_top hB hBbd)
    (ContinuousLinearMap.ext fun u ↦ ext <| by
      rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply, toDistr_mulLeftCLM,
        toDistr_mulLeftCLM, mulLeftCLM_mulLeftCLM_apply hB hA, funext hAB,
        mulLeftCLM_id_apply])
    (ContinuousLinearMap.ext fun u ↦ ext <| by
      rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply, toDistr_mulLeftCLM,
        toDistr_mulLeftCLM, mulLeftCLM_mulLeftCLM_apply hA hB, funext hBA,
        mulLeftCLM_id_apply])

@[simp]
theorem mulLeftEquiv_apply (hp : 1 < p) (hp_top : p ≠ ∞) {A : E → F →L[ℂ] G}
    {B : E → G →L[ℂ] F} (hA : A.HasTemperateGrowth) (hB : B.HasTemperateGrowth)
    (hAbd : ∀ n ≤ k.natAbs, ∃ C, ∀ x, ‖iteratedFDeriv ℝ n A x‖ ≤ C)
    (hBbd : ∀ n ≤ k.natAbs, ∃ C, ∀ x, ‖iteratedFDeriv ℝ n B x‖ ≤ C)
    (hBA : ∀ x, B x ∘L A x = ContinuousLinearMap.id ℂ F)
    (hAB : ∀ x, A x ∘L B x = ContinuousLinearMap.id ℂ G) (u : H^{k, p}(E, F)) :
    mulLeftEquiv hp hp_top hA hB hAbd hBbd hBA hAB u = mulLeftCLM hp hp_top hA hAbd u :=
  (rfl)

@[simp]
theorem mulLeftEquiv_symm_apply (hp : 1 < p) (hp_top : p ≠ ∞) {A : E → F →L[ℂ] G}
    {B : E → G →L[ℂ] F} (hA : A.HasTemperateGrowth) (hB : B.HasTemperateGrowth)
    (hAbd : ∀ n ≤ k.natAbs, ∃ C, ∀ x, ‖iteratedFDeriv ℝ n A x‖ ≤ C)
    (hBbd : ∀ n ≤ k.natAbs, ∃ C, ∀ x, ‖iteratedFDeriv ℝ n B x‖ ≤ C)
    (hBA : ∀ x, B x ∘L A x = ContinuousLinearMap.id ℂ F)
    (hAB : ∀ x, A x ∘L B x = ContinuousLinearMap.id ℂ G) (u : H^{k, p}(E, G)) :
    (mulLeftEquiv hp hp_top hA hB hAbd hBbd hBA hAB).symm u = mulLeftCLM hp hp_top hB hBbd u :=
  (rfl)

end BesselPotentialSpace
