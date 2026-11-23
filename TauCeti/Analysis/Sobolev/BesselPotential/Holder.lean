/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Holder.CompLinear
public import TauCeti.Analysis.Holder.Inclusion
public import TauCeti.Analysis.Holder.LowOrder
public import TauCeti.Analysis.Holder.Zygmund
public import TauCeti.Analysis.Sobolev.BesselPotential.Besov
public import TauCeti.Analysis.Sobolev.BesselPotential.NormEquivalence.Basic
import TauCeti.Analysis.Distribution.TemperedDistribution.Lp

/-!
# Hölder embeddings of Bessel-potential spaces

Let `E` be a finite-dimensional real inner product space of dimension `n` and `1 ≤ p ≤ ∞`. If
`k : ℕ` and `0 < α < 1` satisfy `k + α ≤ s - n / p`, then every element of Mathlib's
Bessel-potential space `H^{s,p}(E, F)` is a bounded `C^k` function whose derivatives through
order `k` are bounded and whose `k`-th derivative is globally `α`-Hölder:

`H^{s,p}(E, F) ⊆ C_b^{k,α}(E, F)`, with `‖u‖_{C^{k,α}} ≤ C ‖u‖_{H^{s,p}}`

(`BesselPotentialSpace.toCkHolderSpace`). This is the Sobolev–Morrey embedding into Hölder
spaces. The hypothesis is an inequality, so it contains both classical cases:

* if `s - n / p = k + α` with `0 < α < 1`, the embedding into `C^{k,α}`;
* if `s - n / p = k + 1` is an integer, the embedding into `C^{k,β}` for every `0 < β < 1`.
  At an integer margin the Lipschitz endpoint `β = 1` is not claimed, and it fails in general.

For `1 < p < ∞` and a natural order `m`, the weak-derivative Sobolev space `W^{m,p}(E)` has the
same elements as `H^{m,p}(E)` (Calderón's theorem, `TauCeti.Wkp.toBesselPotentialSpace`), so the
continuous representative of a real `W^{m,p}` function lies in `C_b^{k,α}(E, ℝ)` whenever
`k + α ≤ m - n / p` (`TauCeti.Wkp.toCkHolderSpace`). For instance `W^{2,2}(ℝ³) ⊆ C^{0,1/2}` and
`W^{2,2}(ℝ²) ⊆ C^{0,β}` for every `β < 1`. For `m = 1` and `k = 0` this is the exponent
`α = 1 - n / p` of Morrey's embedding `TauCeti.W1p.morreyEmbedding`, which is proved from Morrey's
inequality; on bounded Lipschitz domains the higher-order statements are
`TauCeti.Wkp.exists_morreyEmbeddingL_of_isLipschitzDomainWith` and
`TauCeti.Wkp.exists_contDiffOn_holderOnWith_iteratedFDeriv_of_isLipschitzDomainWith_image`.

At order zero the embedding is compact on compact sets, at a strict Hölder margin: for a compact
`K ⊆ E`, a finite-dimensional `F` and `0 < α < 1` with `α < s - n / p`, restricting the continuous
representative to `K` is a compact operator `H^{s,p}(E, F) → C^{0,α}(K, F)`
(`BesselPotentialSpace.isCompactOperator_restrictHolderSpace`).

## The argument

The embedding is a composition of three continuous inclusions, each of which keeps the
underlying tempered distribution:

* `H^{s,p} ⊆ B^s_{p,∞}`, comparing Bessel-potential and Besov spaces
  (`BesselPotentialSpace.toBesovSpace`);
* the Bernstein embedding `B^s_{p,∞} ⊆ B^{s - n/p}_{∞,∞}`
  (`TauCeti.BesovSpace.inclusionOfExponentLE`), followed by the monotonicity
  `B^{s - n/p}_{∞,∞} ⊆ B^{k+α}_{∞,∞}` of the Besov scale in the smoothness;
* the identification `B^{k+α}_{∞,∞} ⊆ C_b^{k,α}` of the Hölder–Zygmund space of non-integer order
  with the classical Hölder space (`TauCeti.BesovSpace.toCkHolderSpace`).

All three use one fixed Littlewood–Paley partition; the resulting map does not depend on it,
since it sends `u` to the unique bounded continuous function representing `u`
(`BesselPotentialSpace.toCkHolderSpace_eq_iff`). Compactness then follows from the compactness of
the inclusion `C^{0,α'}(K) → C^{0,α}(K)` for `α < α'` on a compact set
(`TauCeti.HolderSpace.isCompactOperator_inclusionL`), with `α'` chosen in the strict margin.

## Main declarations

* `BesselPotentialSpace.toCkHolderSpace`: the embedding `H^{s,p}(E, F) → C_b^{k,α}(E, F)` for
  `k + α ≤ s - n / p`, characterised by `BesselPotentialSpace.toLpTop_toCkHolderSpace` and
  `BesselPotentialSpace.toCkHolderSpace_eq_iff`.
* `BesselPotentialSpace.toCkHolderSpace_apply_congr`: the representative does not depend on
  `k` and `α`.
* `TemperedDistribution.MemSobolev.exists_toLpTop_eq`: a tempered distribution in `H^{s,p}` is
  given by a bounded `C^{k,α}` function.
* `BesselPotentialSpace.restrictHolderSpace`,
  `BesselPotentialSpace.isCompactOperator_restrictHolderSpace`: the restriction of the
  representative to a compact set, compact into `C^{0,α}` at a strict margin.
* `TauCeti.Wkp.toCkHolderSpace`: the embedding `W^{m,p}(E) → C_b^{k,α}(E, ℝ)` for `1 < p < ∞` and
  `k + α ≤ m - n / p`, characterised by `TauCeti.Wkp.value_ae_eq_toCkHolderSpace` and
  `TauCeti.Wkp.toCkHolderSpace_eq_iff`.

## References

* J. Bergh and J. Löfström, *Interpolation Spaces: An Introduction*, Theorem 6.5.1 (Sobolev and
  Besov embeddings by the Bernstein inequality).
* H. Triebel, *Theory of Function Spaces*, Sections 2.7.1 and 2.5.7.
* R. A. Adams and J. J. F. Fournier, *Sobolev Spaces*, 2nd ed., Theorem 4.12, Part II.
-/

public section

noncomputable section

open MeasureTheory TemperedDistribution Module BoundedContinuousFunction
open scoped ENNReal NNReal SchwartzMap BesselPotentialSpace BoundedContinuousFunction

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
  {s : ℝ} {p : ℝ≥0∞} [Fact (1 ≤ p)] {k : ℕ} {α : ℝ≥0}

namespace BesselPotentialSpace

open TauCeti

/-- The embedding `H^{s,p} ⊆ B^t_{∞,∞}` for `t ≤ s - n / p`, for the default Littlewood–Paley
partition. -/
private def toZygmund {t : ℝ} (h : t ≤ s - finrank ℝ E / p.toReal) :
    H^{s, p}(E, F) →L[ℂ] BesovSpace F (default : ContDiffBump (0 : E)) t ∞ ∞ :=
  (BesovSpace.inclusion F default ∞ (h.trans_eq (by simp [div_eq_mul_inv])) le_rfl).comp
    ((BesovSpace.inclusionOfExponentLE F default ∞ le_top).comp (toBesovSpace default))

private theorem toDistr_toZygmund {t : ℝ} (h : t ≤ s - finrank ℝ E / p.toReal)
    (u : H^{s, p}(E, F)) : (toZygmund h u).toDistr = u.toDistr := by
  simp only [toZygmund, ContinuousLinearMap.comp_apply, BesovSpace.toDistr_inclusion,
    BesovSpace.toDistr_inclusionOfExponentLE, toDistr_toBesovSpace]

variable (F) in
/-- **The Hölder embedding `H^{s,p} ⊆ C_b^{k,α}`.** For `0 < α < 1` and `k + α ≤ s - n / p`,
where `n` is the dimension of `E`, an element of the Bessel-potential space `H^{s,p}(E, F)`, as
the bounded `C^k` map with bounded derivatives through order `k` and `α`-Hölder `k`-th
derivative representing it. -/
def toCkHolderSpace (k : ℕ) (hα0 : 0 < α) (hα1 : α < 1)
    (h : k + α ≤ s - finrank ℝ E / p.toReal) : H^{s, p}(E, F) →L[ℝ] CkHolderSpace k α E F :=
  (BesovSpace.toCkHolderSpace F default k hα0 hα1).comp ((toZygmund h).restrictScalars ℝ)

variable {hα0 : 0 < α} {hα1 : α < 1} {h : k + α ≤ s - finrank ℝ E / p.toReal}

/-- The `C^{k,α}` map `toCkHolderSpace F k hα0 hα1 h u` represents `u`: its tempered
distribution is that of `u`. -/
@[simp]
theorem toLpTop_toCkHolderSpace (u : H^{s, p}(E, F)) :
    (toLpTop volume ℂ (toCkHolderSpace F k hα0 hα1 h u).toBoundedContinuousFunction :
      𝓢'(E, F)) = u.toDistr := by
  simp [toCkHolderSpace, toDistr_toZygmund]

/-- `toCkHolderSpace F k hα0 hα1 h u` is the only `C^{k,α}` map representing `u`. -/
theorem toCkHolderSpace_eq_iff {u : H^{s, p}(E, F)} {f : CkHolderSpace k α E F} :
    toCkHolderSpace F k hα0 hα1 h u = f ↔
      (toLpTop volume ℂ f.toBoundedContinuousFunction : 𝓢'(E, F)) = u.toDistr := by
  rw [← toDistr_toZygmund h u]
  exact BesovSpace.toCkHolderSpace_eq_iff default k hα0 hα1

/-- The Hölder embedding is injective: an element of `H^{s,p}` is determined by its continuous
representative. -/
theorem toCkHolderSpace_injective : Function.Injective (toCkHolderSpace F k hα0 hα1 h) :=
  fun u v huv ↦ ext <| by
    rw [← toLpTop_toCkHolderSpace (hα0 := hα0) (hα1 := hα1) (h := h) u, huv,
      toLpTop_toCkHolderSpace]

/-- The continuous representative of `u ∈ H^{s,p}` does not depend on the order `k` and the
exponent `α` of the Hölder space it is viewed in. -/
theorem toCkHolderSpace_apply_congr {k' : ℕ} {α' : ℝ≥0} {hα0' : 0 < α'} {hα1' : α' < 1}
    {h' : k' + α' ≤ s - finrank ℝ E / p.toReal} (u : H^{s, p}(E, F)) (x : E) :
    toCkHolderSpace F k hα0 hα1 h u x = toCkHolderSpace F k' hα0' hα1' h' u x := by
  have := toTemperedDistribution_toLpTop_injective (μ := volume)
    (a₁ := (toCkHolderSpace F k hα0 hα1 h u).toBoundedContinuousFunction)
    (a₂ := (toCkHolderSpace F k' hα0' hα1' h' u).toBoundedContinuousFunction) (by simp)
  simpa using DFunLike.congr_fun this x

end BesselPotentialSpace

/-- **Elements of `H^{s,p}` are bounded `C^{k,α}` functions.** For `0 < α < 1` and
`k + α ≤ s - n / p`, a tempered distribution in the Bessel-potential space `H^{s,p}` is the
tempered distribution of a bounded `C^k` map with bounded derivatives through order `k` and
`α`-Hölder `k`-th derivative. -/
theorem TemperedDistribution.MemSobolev.exists_toLpTop_eq {u : 𝓢'(E, F)} (hu : u.MemSobolev s p)
    (k : ℕ) (hα0 : 0 < α) (hα1 : α < 1) (h : k + α ≤ s - finrank ℝ E / p.toReal) :
    ∃ f : TauCeti.CkHolderSpace k α E F,
      (toLpTop volume ℂ f.toBoundedContinuousFunction : 𝓢'(E, F)) = u :=
  ⟨BesselPotentialSpace.toCkHolderSpace F k hα0 hα1 h hu.toBesselPotentialSpace, by simp⟩

namespace BesselPotentialSpace

open TauCeti

/-! ### Compactness on compact sets -/

section Compact

variable (K : Set E) {hα0 : 0 < α} {hα1 : α < 1}

variable (F) in
/-- For `0 < α < 1` and `α ≤ s - n / p`, the restriction to a set `K ⊆ E` of the continuous
representative of an element of `H^{s,p}(E, F)`, as an `α`-Hölder function on `K`. -/
def restrictHolderSpace (hα0 : 0 < α) (hα1 : α < 1) (h : α ≤ s - finrank ℝ E / p.toReal) :
    H^{s, p}(E, F) →L[ℝ] HolderSpace α K F :=
  (HolderSpace.compLipschitzL ((↑) : K → E) (LipschitzWith.subtypeVal K)).comp
    (CkHolderSpace.equivHolderSpace.toLinearIsometry.toContinuousLinearMap.comp
      (toCkHolderSpace F 0 hα0 hα1 (by simpa using h)))

@[simp]
theorem restrictHolderSpace_apply {h : α ≤ s - finrank ℝ E / p.toReal} (u : H^{s, p}(E, F))
    (x : K) :
    restrictHolderSpace F K hα0 hα1 h u x =
      toCkHolderSpace F 0 hα0 hα1 (by simpa using h) u x := by
  simp [restrictHolderSpace, CkHolderSpace.equivHolderSpace_apply]

/-- **Compactness of the Hölder embedding on compact sets.** For a compact set `K`, a
finite-dimensional `F` and `0 < α < 1` with `α < s - n / p`, restricting the continuous
representative of an element of `H^{s,p}(E, F)` to `K` is a compact operator into `C^{0,α}(K, F)`.
-/
theorem isCompactOperator_restrictHolderSpace [FiniteDimensional ℂ F] [CompactSpace K]
    (h : α < s - finrank ℝ E / p.toReal) :
    IsCompactOperator (restrictHolderSpace F K hα0 hα1 h.le) := by
  -- Factor through `C^{0,α'}(K)` for an exponent `α < α' < min 1 (s - n / p)`.
  set m := min 1 (s - finrank ℝ E / p.toReal)
  have hαm : (α : ℝ) < m := lt_min (by exact_mod_cast hα1) h
  set α' : ℝ≥0 := ⟨(α + m) / 2, div_nonneg (by linarith [α.coe_nonneg]) zero_le_two⟩
  have hα' : (α' : ℝ) = (α + m) / 2 := NNReal.coe_mk _ _
  have hαα' : α < α' := by rw [← NNReal.coe_lt_coe, hα']; linarith
  have hα'1 : α' < 1 := by
    rw [← NNReal.coe_lt_coe, hα', NNReal.coe_one]
    linarith [min_le_left 1 (s - finrank ℝ E / p.toReal)]
  have hα'h : (α' : ℝ) ≤ s - finrank ℝ E / p.toReal := by
    rw [hα']; linarith [min_le_right 1 (s - finrank ℝ E / p.toReal)]
  have heq : restrictHolderSpace F K hα0 hα1 h.le =
      (HolderSpace.inclusionL hαα'.le).comp
        (restrictHolderSpace F K (hα0.trans hαα') hα'1 hα'h) := by
    ext u x
    simp only [ContinuousLinearMap.comp_apply, HolderSpace.inclusionL_apply,
      restrictHolderSpace_apply]
    exact toCkHolderSpace_apply_congr u x
  have : FiniteDimensional ℝ F := Module.Finite.trans ℂ F
  have : ProperSpace F := FiniteDimensional.proper_real F
  rw [heq]
  exact (HolderSpace.isCompactOperator_inclusionL hαα').comp_clm _

end Compact

end BesselPotentialSpace

/-! ### Weak-derivative Sobolev spaces -/

namespace TauCeti.Wkp

variable (hp : 1 < p) (hp_top : p ≠ ∞)

/-- **The Hölder embedding `W^{m,p} ⊆ C_b^{k,α}`.** For `1 < p < ∞`, `0 < α < 1` and
`k + α ≤ m - n / p`, where `n` is the dimension of `E`, a real `W^{m,p}` function on the whole
space, as its bounded continuous representative, a `C^k` function with bounded derivatives
through order `k` and `α`-Hölder `k`-th derivative. -/
def toCkHolderSpace (m k : ℕ) (hα0 : 0 < α) (hα1 : α < 1)
    (h : k + α ≤ m - finrank ℝ E / p.toReal) :
    Wkp (volume : Measure E) ⊤ p m →L[ℝ] CkHolderSpace k α E ℝ :=
  (CkHolderSpace.compLeftL Complex.reCLM).comp
    ((BesselPotentialSpace.toCkHolderSpace ℂ k hα0 hα1 h).comp (toBesselPotentialSpace hp hp_top m))

variable {m : ℕ} {hα0 : 0 < α} {hα1 : α < 1} {h : k + α ≤ m - finrank ℝ E / p.toReal}

/-- `toCkHolderSpace hp hp_top m k hα0 hα1 h u` is almost everywhere equal to the value of `u`. -/
theorem value_ae_eq_toCkHolderSpace (u : Wkp (volume : Measure E) ⊤ p m) :
    (value m u : E → ℝ) =ᵐ[volume] toCkHolderSpace hp hp_top m k hα0 hα1 h u := by
  set v := toBesselPotentialSpace hp hp_top m u
  set f := BesselPotentialSpace.toCkHolderSpace ℂ k hα0 hα1 h v
  -- The `Lᵖ` function of `v` and the continuous function `f` have the same tempered distribution.
  have hf : BesselPotentialSpace.inclusionLp (Nat.cast_nonneg m) v =ᵐ[volume] f := by
    refine Lp.ae_eq_of_toTemperedDistribution_apply_eq _ f.contDiff.continuous.locallyIntegrable
      fun φ ↦ ?_
    rw [BesselPotentialSpace.toTemperedDistribution_inclusionLp,
      ← BesselPotentialSpace.toLpTop_toCkHolderSpace (hα0 := hα0) (hα1 := hα1) (h := h) v,
      Lp.toTemperedDistribution_apply]
    exact integral_congr_ae ((coeFn_toLpTop volume (𝕜 := ℂ) f.toBoundedContinuousFunction).mono
      fun x hx ↦ by simp [hx, f])
  filter_upwards [hf, coeFn_inclusionLp_toBesselPotentialSpace hp hp_top m u] with x hx hu
  rw [toCkHolderSpace, ContinuousLinearMap.comp_apply, CkHolderSpace.compLeftL_apply,
    ContinuousLinearMap.comp_apply, ← hx, hu, Complex.reCLM_apply, Complex.ofReal_re]

/-- `toCkHolderSpace hp hp_top m k hα0 hα1 h u` is the only bounded `C^{k,α}` function almost
everywhere equal to the value of `u`. -/
theorem toCkHolderSpace_eq_iff {u : Wkp (volume : Measure E) ⊤ p m}
    {f : CkHolderSpace k α E ℝ} :
    toCkHolderSpace hp hp_top m k hα0 hα1 h u = f ↔ (value m u : E → ℝ) =ᵐ[volume] f := by
  refine ⟨fun hf ↦ hf ▸ value_ae_eq_toCkHolderSpace hp hp_top u, fun hf ↦ ?_⟩
  refine DFunLike.coe_injective ?_
  exact ((CkHolderSpace.contDiff _).continuous.ae_eq_iff_eq volume f.contDiff.continuous).1
    ((value_ae_eq_toCkHolderSpace hp hp_top u).symm.trans hf)

end TauCeti.Wkp
