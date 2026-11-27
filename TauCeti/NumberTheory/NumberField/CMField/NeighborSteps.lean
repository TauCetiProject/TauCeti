/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.LinearAlgebra.Projectivization.Basic
public import Mathlib.SetTheory.Cardinal.Order
public import TauCeti.NumberTheory.NumberField.CMField.AdelicLattice
public import TauCeti.RingTheory.DedekindDomain.FiniteAdeleRing.Place
import Mathlib.LinearAlgebra.Projectivization.Cardinality
import TauCeti.NumberTheory.ArithmeticDirichletSeries.ResidueDegree
import TauCeti.NumberTheory.NumberField.CMField.Basic
import TauCeti.NumberTheory.NumberField.RingOfIntegers.Transport
import TauCeti.RingTheory.DedekindDomain.AdicValuation.Completion
import TauCeti.RingTheory.DedekindDomain.AdicValuation.Transport
import TauCeti.RingTheory.LocalRing.ResidueField.Quotient

/-!
# Neighbour residues, step weights and place signs of a CM field

Let `E` be a CM field with complex conjugation `x ↦ conj x`, `𝔸_f` its finite adeles and `Ô`
the integral ones. Conjugation permutes the finite places, `w ↦ conj w`; a finite place `w` is
*split* if `conj w ≠ w`. At a finite place `w` write `E_w`, `O_w`, `𝔪_w`, `k_w` for the
completion, its integers, their maximal ideal and the residue field, and `q_w = #k_w`, the
absolute norm of `w`.

Kneser's neighbour method for the standard hermitian lattice `Ô^n` moves a lattice one step
towards the standard lattice by a quasi-reflection at one place `w`. The quasi-reflections needed
at `w` are indexed by the *steps* at `w` (`IsDedekindDomain.HeightOneSpectrum.neighborSteps`): a
line of `k_w^n` together with a *residue*, an element of

`R_w = {ϖ s_w mod 𝔪_w : s ∈ 𝔸_f supported at w, ϖ s_w ∈ O_w, s + conj s ∈ Ô} ⊆ k_w`

(`IsDedekindDomain.HeightOneSpectrum.neighborResidues`), where `ϖ ∈ E_w` is a uniformiser; the
choice of `ϖ` is an explicit argument. The *step weight* `s_{n,M}(w) = #{steps at w} · q_w^{−M/2}`
(`IsDedekindDomain.HeightOneSpectrum.stepWeight`) is the weight of one step in a walk through
neighbours whose coefficients have size `[L : L ∩ γ⁻¹L]^{−M/2}`.

The residues are few. At a split place `w`, a finite adele `s` supported at `w` and its conjugate
live at different places, so `s` is integral and `R_w = {0}`. At a place `w = conj w`, an integer
`y` of `E` with `y − conj y ∉ w` makes
`(r, r′) ↦ r + y r′` injective on `R_w × R_w`, so `(#R_w)² ≤ q_w`. With at most `q_w^n/(q_w − 1)`
lines in `k_w^n`, this gives, for `2n < M`, `s_{n,M}(w) ≤ 1/(q_w − 1)`, and
`s_{n,M}(w) ≤ 1/((q_w − 1)√q_w)` at a split place. If `E` contains roots of `X² + X + 1` and
`X² + 1`, then `q_w ≥ 4` (`IsDedekindDomain.HeightOneSpectrum.four_le_absNorm`), and the weights
of a place and of its conjugate add up to at most `1/3`. A place `w = conj w` has residue degree
at least two over `ℚ`, because conjugation acts nontrivially on its residue field; so the step
weights are summable over all finite places.

A fixed well-ordering of the finite places (`WellOrderingRel`) defines the *place sign*
`ε_w = −1` if `w` precedes `conj w` and `ε_w = 1` otherwise
(`IsDedekindDomain.HeightOneSpectrum.placeSign`). Then `ε_w = 1` if `w = conj w`,
`ε_{conj w} = −ε_w` at a split place, and so
`(1 − ε_w q_w^{−s})(1 − ε_{conj w} q_{conj w}^{−s}) = 1 − q_w^{−2s}` at a split place.

The conjugate place `conj w` is the image of `w` under the isomorphism of rings of integers
induced by complex conjugation,
`HeightOneSpectrum.equivOfRingEquiv (RingOfIntegers.mapRingEquiv (complexConj E).toRingEquiv) w`;
declaration names refer to it as `conjPlace`.

## Main definitions

* `IsDedekindDomain.HeightOneSpectrum.neighborResidues`: the residues `R_w ⊆ k_w`.
* `IsDedekindDomain.HeightOneSpectrum.neighborSteps`: the steps `(ℓ, r)`, `ℓ` a line in `k_w^ι`
  and `r ∈ R_w`.
* `IsDedekindDomain.HeightOneSpectrum.stepWeight`: the step weight `#{steps} · q_w^{−M/2}`.
* `IsDedekindDomain.HeightOneSpectrum.placeSign`: the place sign `ε_w`.

## Main results

* `IsDedekindDomain.HeightOneSpectrum.neighborResidues_eq_singleton_zero`: `R_w = {0}` at a
  split place.
* `IsDedekindDomain.HeightOneSpectrum.ncard_neighborResidues_sq_le`: `(#R_w)² ≤ q_w`.
* `IsDedekindDomain.HeightOneSpectrum.stepWeight_le`,
  `IsDedekindDomain.HeightOneSpectrum.stepWeight_le_of_conjPlace_ne`: the bounds `1/(q_w − 1)`
  and, at a split place, `1/((q_w − 1)√q_w)`, for `2n < M`.
* `IsDedekindDomain.HeightOneSpectrum.sum_stepWeight_pair_le`: `s(w) + s(conj w) ≤ 1/3` (one term if
  `w = conj w`).
* `IsDedekindDomain.HeightOneSpectrum.summable_stepWeight`: the step weights are summable over
  the finite places.
* `IsDedekindDomain.HeightOneSpectrum.placeSign_of_conjPlace_eq`,
  `IsDedekindDomain.HeightOneSpectrum.placeSign_conjPlace_of_ne`: the two laws of the place signs,
  and `IsDedekindDomain.HeightOneSpectrum.prod_one_sub_placeSign_mul_rpow`: the Euler factor of a
  split pair.

## References

* M. Kneser, *Klassenzahlen definiter quadratischer Formen*, Arch. Math. 8 (1957), 241–250.
* M. Greenberg, J. Voight, *Lattice methods for algebraic modular forms on classical groups*, in
  *Computations with Modular Forms*, Contrib. Math. Comput. Sci. 6, Springer (2014), 147–179, §5.
* `grh-lean`, https://github.com/lsernau/grh-lean, files `src/Lib/SiegelWeil/NeighbourLattices.lean`
  (`New.SiegelWeil.neighbourResidues`, `New.SiegelWeil.card_neighbourResidues_sq_le`),
  `src/Lib/SiegelWeil/UnramifiedSeries/VacuumCoefficients.lean` (`New.SiegelWeil.stepWeight`,
  `New.SiegelWeil.summable_stepWeight`) and `src/Lib/SiegelWeil/RallisInner/SharpData.lean`
  (`New.placeSign`); Apache 2.0, Copyright 2026 Anthropic, PBC. The definitions and the route of
  the bounds (the injection `(r, r′) ↦ r + y r′`, the count of lines, `q_w ≥ 4` from roots of
  `X² + X + 1` and `X² + 1`) follow the method of those declarations; the summability is reduced
  here to the convergence of `∑ q_w^{−1}` over the primes of residue degree at least two.
-/

public section
noncomputable section

open IsDedekindDomain IsDedekindDomain.FiniteAdeleRing NumberField NumberField.IsCMField
open WithZero
open scoped NumberField.AdeleRing LinearAlgebra.Projectivization

namespace IsDedekindDomain.HeightOneSpectrum

variable {E : Type*} [Field E] [NumberField E] [IsCMField E]

/-- The conjugate `conj w` of a finite place `w` of a CM field: its image under the isomorphism of
rings of integers induced by complex conjugation. -/
local notation "conjPlace" =>
  HeightOneSpectrum.equivOfRingEquiv
    (RingOfIntegers.mapRingEquiv (AlgEquiv.toRingEquiv (complexConj E)))

/-! ### Complex conjugation on the places and on the finite adeles -/

section Conjugation

/-- `|conj x|_{conj w} = |x|_w`. -/
private theorem valuation_conjPlace (w : HeightOneSpectrum (𝓞 E)) (x : E) :
    (conjPlace w).valuation E (complexConj E x) = w.valuation E x := by
  have := valuation_ringEquivOfRingEquiv (K := E) (K' := E)
    (RingOfIntegers.mapRingEquiv (complexConj E).toRingEquiv)
    (asIdeal_equivOfRingEquiv _ w) x
  rwa [RingOfIntegers.ringEquivOfRingEquiv_mapRingEquiv, AlgEquiv.coe_toRingEquiv] at this

/-- `|conj x|_w = |x|_{conj w}`. -/
private theorem valuation_complexConj (w : HeightOneSpectrum (𝓞 E)) (x : E) :
    w.valuation E ((complexConj E).toRingEquiv x) = (conjPlace w).valuation E x := by
  rw [AlgEquiv.coe_toRingEquiv, ← valuation_conjPlace w (complexConj E x),
    complexConj_apply_apply]

/-- Conjugation of finite places is an involution. -/
private theorem conjPlace_conjPlace (w : HeightOneSpectrum (𝓞 E)) :
    conjPlace (conjPlace w) = w := by
  ext x
  rw [asIdeal_equivOfRingEquiv, asIdeal_equivOfRingEquiv, ← Ideal.symm_apply_mem_of_equiv_iff,
    ← Ideal.symm_apply_mem_of_equiv_iff]
  convert Iff.rfl using 2
  ext
  simp [AlgEquiv.eq_symm_apply]

/-- The conjugate place has the same absolute norm. -/
private theorem absNorm_conjPlace (w : HeightOneSpectrum (𝓞 E)) :
    Ideal.absNorm (conjPlace w).asIdeal = Ideal.absNorm w.asIdeal := by
  rw [asIdeal_equivOfRingEquiv, Ideal.absNorm_map_of_ringEquiv]

/-- The component of `conj a` at a place `w'` with `|conj x|_{w'} = |x|_w` is the image of `a_w`
under the isomorphism `E_w ≃ E_{w'}` extending complex conjugation. -/
private theorem finiteAdeleConj_apply {w w' : HeightOneSpectrum (𝓞 E)}
    (hw : ∀ x, w'.valuation E ((complexConj E).toRingEquiv x) = w.valuation E x) (a : 𝔸ᶠ[E]) :
    finiteAdeleConj E a w' = adicCompletionCongr w w' (complexConj E).toRingEquiv hw (a w) := by
  -- Both sides are continuous in `a` and agree on the dense image of `E`.
  have hconj : Continuous (finiteAdeleConj E) := by
    rw [finiteAdeleConj_def]
    exact TauCeti.GlobalNumberFields.continuous_finiteAdeleEquiv E E _
  have hl : Continuous fun a ↦ proj E w' (finiteAdeleConj E a) :=
    (proj E w').continuous.comp hconj
  have hr : Continuous fun a ↦ adicCompletionCongr w w' _ hw (proj E w a) :=
    (continuous_adicCompletionCongr hw).comp (proj E w).continuous
  have h := congr_fun ((FiniteAdeleRing.denseRange_algebraMap (𝓞 E) E).equalizer hl hr
    (funext fun x ↦ ?_)) a
  · simpa only [proj_apply] using h
  simp only [Function.comp_apply, finiteAdeleConj_algebraMap, AlgHomClass.commutes,
    adicCompletionCongr_algebraMap, AlgEquiv.coe_toRingEquiv]

/-- The conjugate of a finite adele supported at `w` vanishes at every place `u` with
`conj u ≠ w`. -/
private theorem finiteAdeleConj_single_apply_of_ne {u w : HeightOneSpectrum (𝓞 E)}
    (hu : conjPlace u ≠ w) (t : w.adicCompletion E) :
    finiteAdeleConj E (single E w t) u = 0 := by
  rw [finiteAdeleConj_apply (valuation_complexConj u), single_apply_of_ne hu, map_zero]

/-- At a place with `conj w = w`, complex conjugation preserves the `w`-adic valuation. -/
private theorem valuation_complexConj_of_conjPlace_eq {w : HeightOneSpectrum (𝓞 E)}
    (h : conjPlace w = w) (x : E) :
    w.valuation E ((complexConj E).toRingEquiv x) = w.valuation E x := by
  rw [valuation_complexConj, h]

/-- At a place with `conj w = w`, the conjugate of a finite adele supported at `w` has component
`conj t` at `w`, for the continuous extension `t ↦ conj t` of complex conjugation to `E_w`. -/
private theorem finiteAdeleConj_single_apply_self_of_conjPlace_eq {w : HeightOneSpectrum (𝓞 E)}
    (h : conjPlace w = w) (t : w.adicCompletion E) :
    finiteAdeleConj E (single E w t) w =
      adicCompletionCongr w w _ (valuation_complexConj_of_conjPlace_eq h) t := by
  rw [finiteAdeleConj_apply (valuation_complexConj_of_conjPlace_eq h), single_apply_self]

/-- At a split place, a finite adele `s` supported at `w` with `s + conj s ∈ Ô` is integral. -/
private theorem mem_adicCompletionIntegers_of_conjPlace_ne {w : HeightOneSpectrum (𝓞 E)}
    (h : conjPlace w ≠ w) {t : w.adicCompletion E}
    (ht : single E w t + finiteAdeleConj E (single E w t) ∈ integralAdeles (𝓞 E) E) :
    t ∈ w.adicCompletionIntegers E := by
  have := mem_integralAdeles.1 ht w
  rwa [FiniteAdeleRing.add_apply, single_apply_self, finiteAdeleConj_single_apply_of_ne h,
    add_zero] at this

/-- At a place with `conj w = w`, a finite adele `s` supported at `w` with `s + conj s ∈ Ô` has
component `t = s_w` with `t + conj t ∈ O_w`. -/
private theorem add_mem_adicCompletionIntegers_of_conjPlace_eq {w : HeightOneSpectrum (𝓞 E)}
    (h : conjPlace w = w) {t : w.adicCompletion E}
    (ht : single E w t + finiteAdeleConj E (single E w t) ∈ integralAdeles (𝓞 E) E) :
    t + adicCompletionCongr w w _ (valuation_complexConj_of_conjPlace_eq h) t ∈
      w.adicCompletionIntegers E := by
  have := mem_integralAdeles.1 ht w
  rwa [FiniteAdeleRing.add_apply, single_apply_self,
    finiteAdeleConj_single_apply_self_of_conjPlace_eq h] at this

end Conjugation

/-! ### Residues, steps and step weights -/

variable (w : HeightOneSpectrum (𝓞 E))

/-- The **neighbour residues** `R_w ⊆ k_w` at a finite place `w` of a CM field, for a chosen
`ϖ ∈ E_w` (a uniformiser in the results below): the reductions modulo the maximal ideal of
`ϖ s_w ∈ O_w` for the finite adeles `s` supported at `w`, written `s = single w t` (every finite
adele supported at `w` is of this form, `IsDedekindDomain.FiniteAdeleRing.eq_single_iff`), with
`ϖ s_w ∈ O_w` and `s + conj s ∈ Ô`, where `conj s` is the complex conjugate of `s`. -/
def neighborResidues (ϖ : w.adicCompletion E) :
    Set (IsLocalRing.ResidueField (w.adicCompletionIntegers E)) :=
  {r | ∃ (t : w.adicCompletion E) (h : ϖ * t ∈ w.adicCompletionIntegers E),
    single E w t + finiteAdeleConj E (single E w t) ∈ integralAdeles (𝓞 E) E ∧
      IsLocalRing.residue _ ⟨ϖ * t, h⟩ = r}

variable {w} in
/-- Membership in `R_w`: `r` is the residue of `ϖ t ∈ O_w` for some `t ∈ E_w` such that the finite
adele `s = single w t` satisfies `s + conj s ∈ Ô`. -/
theorem mem_neighborResidues {ϖ : w.adicCompletion E}
    {r : IsLocalRing.ResidueField (w.adicCompletionIntegers E)} :
    r ∈ w.neighborResidues ϖ ↔
      ∃ (t : w.adicCompletion E) (h : ϖ * t ∈ w.adicCompletionIntegers E),
      single E w t + finiteAdeleConj E (single E w t) ∈ integralAdeles (𝓞 E) E ∧
        IsLocalRing.residue _ ⟨ϖ * t, h⟩ = r :=
  Iff.rfl

/-- `0` is a neighbour residue, the reduction for `s = 0`. -/
@[simp]
theorem zero_mem_neighborResidues (ϖ : w.adicCompletion E) : 0 ∈ w.neighborResidues ϖ :=
  ⟨0, by simp, by simp,
    (IsLocalRing.residue_eq_zero_iff _).2 ((Valuation.mem_maximalIdeal_iff _ _).2 (by simp))⟩

/-- The **steps** at a finite place `w` of a CM field: the pairs `(ℓ, r)` of a line `ℓ` of
`k_w^ι` and a neighbour residue `r ∈ R_w`. -/
def neighborSteps (ι : Type*) (ϖ : w.adicCompletion E) :
    Set (ℙ (IsLocalRing.ResidueField (w.adicCompletionIntegers E))
      (ι → IsLocalRing.ResidueField (w.adicCompletionIntegers E)) ×
      IsLocalRing.ResidueField (w.adicCompletionIntegers E)) :=
  Set.univ ×ˢ w.neighborResidues ϖ

variable {w} in
/-- A pair `(ℓ, r)` is a step exactly when `r` is a neighbour residue. -/
@[simp]
theorem mem_neighborSteps {ι : Type*} {ϖ : w.adicCompletion E}
    {x : ℙ (IsLocalRing.ResidueField (w.adicCompletionIntegers E))
      (ι → IsLocalRing.ResidueField (w.adicCompletionIntegers E)) ×
      IsLocalRing.ResidueField (w.adicCompletionIntegers E)} :
    x ∈ w.neighborSteps ι ϖ ↔ x.2 ∈ w.neighborResidues ϖ := by
  simp [neighborSteps]

/-- The **step weight** `s(w) = #{steps at w} · q_w^{−M/2}` at a finite place `w` of a CM field,
for lines in `k_w^ι`, where `q_w` is the absolute norm of `w`. -/
def stepWeight (ι : Type*) (M : ℕ) (ϖ : w.adicCompletion E) : ℝ :=
  (w.neighborSteps ι ϖ).ncard * (Ideal.absNorm w.asIdeal : ℝ) ^ (-(M : ℝ) / 2)

/-- The defining formula of the step weight. -/
theorem stepWeight_def (ι : Type*) (M : ℕ) (ϖ : w.adicCompletion E) :
    w.stepWeight ι M ϖ =
      (w.neighborSteps ι ϖ).ncard * (Ideal.absNorm w.asIdeal : ℝ) ^ (-(M : ℝ) / 2) :=
  (rfl)

/-- Step weights are nonnegative. -/
theorem stepWeight_nonneg (ι : Type*) (M : ℕ) (ϖ : w.adicCompletion E) :
    0 ≤ w.stepWeight ι M ϖ := by
  rw [stepWeight_def]
  positivity

/-! ### The number of residues -/

section Residues

variable {w}

omit [IsCMField E] in
/-- Two elements of `O_w` have the same residue exactly when their difference has valuation
`< 1`. -/
private theorem residue_eq_residue_iff_valued_sub_lt_one {x x' : w.adicCompletionIntegers E} :
    IsLocalRing.residue _ x = IsLocalRing.residue _ x' ↔
      Valued.v ((x : w.adicCompletion E) - x') < 1 :=
  TauCeti.residue_eq_residue_iff.trans (Valuation.mem_maximalIdeal_iff _ _)

omit [IsCMField E] in
/-- If `|ϖ| = exp (-1)` and `|ϖ z| < 1`, then `|z| ≤ 1`. -/
private theorem valued_le_one_of_valued_mul_lt_one {ϖ z : w.adicCompletion E}
    (hϖ : Valued.v ϖ = exp (-1)) (h : Valued.v (ϖ * z) < 1) : Valued.v z ≤ 1 := by
  rw [map_mul, hϖ] at h
  rcases eq_or_ne (Valued.v z) 0 with h0 | h0
  · simp [h0]
  · rw [← exp_log h0, ← exp_add, ← exp_zero, exp_lt_exp] at h
    rw [← exp_log h0, ← exp_zero, exp_le_exp]
    omega

omit [IsCMField E] in
/-- If `|ϖ| < 1` and `|z| ≤ 1`, then `|ϖ z| < 1`. -/
private theorem valued_mul_lt_one {ϖ z : w.adicCompletion E} (hϖ : Valued.v ϖ < 1)
    (hz : Valued.v z ≤ 1) : Valued.v (ϖ * z) < 1 := by
  rw [map_mul]
  exact mul_lt_one_of_lt_of_le hϖ hz

/-- **At a split place, the only residue is `0`.** If `conj w ≠ w` and `ϖ` lies in the maximal
ideal, then `R_w = {0}`: a finite adele `s` supported at `w` with `s + conj s ∈ Ô` is integral,
because `conj s` is supported at `conj w`. -/
theorem neighborResidues_eq_singleton_zero (h : conjPlace w ≠ w) {ϖ : w.adicCompletion E}
    (hϖ : Valued.v ϖ < 1) : w.neighborResidues ϖ = {0} := by
  refine Set.eq_singleton_iff_unique_mem.2 ⟨zero_mem_neighborResidues w ϖ, ?_⟩
  rintro r ⟨t, ht, hs, rfl⟩
  rw [IsLocalRing.residue_eq_zero_iff]
  exact (Valuation.mem_maximalIdeal_iff _ _).2 <| valued_mul_lt_one hϖ <|
    (mem_adicCompletionIntegers _ _ _).1 (mem_adicCompletionIntegers_of_conjPlace_ne h hs)

omit [IsCMField E] in
/-- The algebraic core of the residue count. Let `τ` be an automorphism of `E_w` preserving the
valuation and `y ∈ O_w` with `y − τ y` a unit of `O_w`. If `a + τ a`, `a′ + τ a′` and `a + y a′`
lie in `O_w`, then so does `a′`: applying `τ` to `a + y a′` shows that `a + (τ y) a′ ∈ O_w`. -/
private theorem mem_adicCompletionIntegers_of_add_mul_mem
    {τ : w.adicCompletion E ≃+* w.adicCompletion E} (hτ : ∀ x, Valued.v (τ x) = Valued.v x)
    {y a a' : w.adicCompletion E} (hy : y ∈ w.adicCompletionIntegers E)
    (hyτ : Valued.v (y - τ y) = 1) (ha : a + τ a ∈ w.adicCompletionIntegers E)
    (ha' : a' + τ a' ∈ w.adicCompletionIntegers E)
    (hsum : a + y * a' ∈ w.adicCompletionIntegers E) : a' ∈ w.adicCompletionIntegers E := by
  have hτO {x : w.adicCompletion E} (hx : x ∈ w.adicCompletionIntegers E) :
      τ x ∈ w.adicCompletionIntegers E := by
    rw [mem_adicCompletionIntegers, hτ]
    exact (mem_adicCompletionIntegers _ _ _).1 hx
  have h₁ : a + τ y * a' ∈ w.adicCompletionIntegers E := by
    have e : a + τ y * a' = (a + τ a) + τ y * (a' + τ a') - τ (a + y * a') := by
      rw [map_add, map_mul]
      ring
    rw [e]
    exact sub_mem (add_mem ha (mul_mem (hτO hy) ha')) (hτO hsum)
  have h₂ : (y - τ y) * a' ∈ w.adicCompletionIntegers E := by
    have e : (y - τ y) * a' = (a + y * a') - (a + τ y * a') := by ring
    rw [e]
    exact sub_mem hsum h₁
  rw [mem_adicCompletionIntegers, map_mul, hyτ, one_mul] at h₂
  exact (mem_adicCompletionIntegers _ _ _).2 h₂

/-- At a place with `conj w = w`, `y − conj y` has valuation `1` in `E_w` when it lies outside
`w`. -/
private theorem valued_sub_adicCompletionCongr_eq_one (h : conjPlace w = w) {y : 𝓞 E}
    (hy : y - ringOfIntegersComplexConj E y ∉ w.asIdeal) :
    Valued.v (algebraMap (𝓞 E) (w.adicCompletion E) y -
      adicCompletionCongr w w _ (valuation_complexConj_of_conjPlace_eq h)
        (algebraMap (𝓞 E) (w.adicCompletion E) y)) = 1 := by
  have hτ : adicCompletionCongr w w _ (valuation_complexConj_of_conjPlace_eq h)
      (algebraMap (𝓞 E) (w.adicCompletion E) y) =
        algebraMap (𝓞 E) (w.adicCompletion E) (ringOfIntegersComplexConj E y) := by
    rw [IsScalarTower.algebraMap_apply (𝓞 E) E (w.adicCompletion E),
      IsScalarTower.algebraMap_apply (𝓞 E) E (w.adicCompletion E) (ringOfIntegersComplexConj E y),
      adicCompletionCongr_algebraMap]
    simp [← RingOfIntegers.coe_eq_algebraMap]
  rw [hτ, ← map_sub]
  exact (notMem_asIdeal_iff_valued_algebraMap_eq_one (K := E) w).1 hy

/-- At a place with `conj w = w`, an integer `y` with `y − conj y ∉ w` makes `(r, r′) ↦ r + y r′`
injective on `R_w × R_w`, for a uniformiser `ϖ`. -/
private theorem injOn_neighborResidues_prod (h : conjPlace w = w) {ϖ : w.adicCompletion E}
    (hϖ : Valued.v ϖ = exp (-1)) {y : 𝓞 E} (hy : y - ringOfIntegersComplexConj E y ∉ w.asIdeal)
    {Y : w.adicCompletionIntegers E}
    (hY : (Y : w.adicCompletion E) = algebraMap (𝓞 E) (w.adicCompletion E) y) :
    Set.InjOn (fun r ↦ r.1 + IsLocalRing.residue _ Y * r.2)
      (w.neighborResidues ϖ ×ˢ w.neighborResidues ϖ) := by
  set τ := adicCompletionCongr w w _ (valuation_complexConj_of_conjPlace_eq h)
  have hτ : ∀ x, Valued.v (τ x) = Valued.v x := valued_adicCompletionCongr _
  rintro ⟨-, -⟩ ⟨⟨t₁, h₁, hs₁, rfl⟩, ⟨t₁', h₁', hs₁', rfl⟩⟩ ⟨-, -⟩
    ⟨⟨t₂, h₂, hs₂, rfl⟩, ⟨t₂', h₂', hs₂', rfl⟩⟩ heq
  simp only [← map_mul, ← map_add] at heq
  rw [residue_eq_residue_iff_valued_sub_lt_one] at heq
  -- `ϖ ((t₁ - t₂) + y (t₁' - t₂'))` lies in the maximal ideal, so its cofactor is integral.
  have hsum : (t₁ - t₂) + (Y : w.adicCompletion E) * (t₁' - t₂') ∈ w.adicCompletionIntegers E := by
    refine (mem_adicCompletionIntegers _ _ _).2 (valued_le_one_of_valued_mul_lt_one hϖ ?_)
    convert heq using 2
    push_cast
    ring
  have hconj {t₁ t₂ : w.adicCompletion E}
      (hs₁ : single E w t₁ + finiteAdeleConj E (single E w t₁) ∈ integralAdeles (𝓞 E) E)
      (hs₂ : single E w t₂ + finiteAdeleConj E (single E w t₂) ∈ integralAdeles (𝓞 E) E) :
      (t₁ - t₂) + τ (t₁ - t₂) ∈ w.adicCompletionIntegers E := by
    have := sub_mem (add_mem_adicCompletionIntegers_of_conjPlace_eq h hs₁)
      (add_mem_adicCompletionIntegers_of_conjPlace_eq h hs₂)
    rw [map_sub]
    convert this using 1
    ring
  have hYτ : Valued.v ((Y : w.adicCompletion E) - τ Y) = 1 := by
    rw [hY]
    exact valued_sub_adicCompletionCongr_eq_one h hy
  have ha' := mem_adicCompletionIntegers_of_add_mul_mem hτ Y.property hYτ (hconj hs₁ hs₂)
    (hconj hs₁' hs₂') hsum
  have ha : t₁ - t₂ ∈ w.adicCompletionIntegers E := by
    simpa using sub_mem hsum (mul_mem Y.property ha')
  have hϖ' : Valued.v ϖ < 1 := by
    rw [hϖ]
    decide
  refine Prod.ext (residue_eq_residue_iff_valued_sub_lt_one.2 ?_)
    (residue_eq_residue_iff_valued_sub_lt_one.2 ?_)
  · rw [← mul_sub]
    exact valued_mul_lt_one hϖ' ((mem_adicCompletionIntegers _ _ _).1 ha)
  · rw [← mul_sub]
    exact valued_mul_lt_one hϖ' ((mem_adicCompletionIntegers _ _ _).1 ha')

omit [IsCMField E] in
/-- The residue field `k_w` has `q_w` elements. -/
private theorem natCard_residueField (w : HeightOneSpectrum (𝓞 E)) :
    Nat.card (IsLocalRing.ResidueField (w.adicCompletionIntegers E)) =
      Ideal.absNorm w.asIdeal := by
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  exact (Nat.card_congr (w.residueFieldEquivAdicCompletionIntegers (K := E)).toEquiv).symm

/-- **The number of residues.** For a uniformiser `ϖ` of `E_w` and an integer `y` of `E` with
`y − conj y ∉ w` (for instance `y − conj y` a unit), `(#R_w)² ≤ q_w`. At a split place
`R_w = {0}`; at a place with `conj w = w`, `(r, r′) ↦ r + y r′` embeds `R_w × R_w` into `k_w`. -/
theorem ncard_neighborResidues_sq_le {ϖ : w.adicCompletion E} (hϖ : Valued.v ϖ = exp (-1))
    {y : 𝓞 E} (hy : y - ringOfIntegersComplexConj E y ∉ w.asIdeal) :
    (w.neighborResidues ϖ).ncard ^ 2 ≤ Ideal.absNorm w.asIdeal := by
  by_cases h : conjPlace w = w
  · rw [sq, ← Set.ncard_prod, ← natCard_residueField, ← Set.ncard_univ]
    exact Set.ncard_le_ncard_of_injOn _ (fun _ _ ↦ Set.mem_univ _)
      (injOn_neighborResidues_prod h hϖ hy
        (Y := ⟨_, coe_mem_adicCompletionIntegers (K := E) w y⟩) rfl)
  · rw [neighborResidues_eq_singleton_zero h (by rw [hϖ]; decide), Set.ncard_singleton, one_pow]
    exact Nat.one_le_iff_ne_zero.2 (Ideal.absNorm_ne_zero_iff_mem_nonZeroDivisors.2
      (mem_nonZeroDivisors_of_ne_zero w.ne_bot))

/-- A place with `conj w = w` has residue degree at least two over `ℚ` if `y − conj y ∉ w` for some
integer `y`: on a residue field with a prime number of elements every element is the class of
an integer, so conjugation would act trivially on it. -/
private theorem mem_higherDegreePrimes_of_conjPlace_eq (h : conjPlace w = w) {y : 𝓞 E}
    (hy : y - ringOfIntegersComplexConj E y ∉ w.asIdeal) : w ∈ TauCeti.higherDegreePrimes E := by
  rw [TauCeti.mem_higherDegreePrimes_iff_not_prime_absNorm]
  intro hp
  have : NeZero (Ideal.absNorm w.asIdeal) := ⟨hp.ne_zero⟩
  have hconj {x : 𝓞 E} (hx : x ∈ w.asIdeal) : ringOfIntegersComplexConj E x ∈ w.asIdeal := by
    have e : RingOfIntegers.mapRingEquiv (complexConj E).toRingEquiv x =
        ringOfIntegersComplexConj E x := RingOfIntegers.ext (by simp)
    have := Ideal.mem_map_of_mem (RingOfIntegers.mapRingEquiv (complexConj E).toRingEquiv) hx
    rwa [← asIdeal_equivOfRingEquiv, h, e] at this
  let := Fintype.ofFinite (𝓞 E ⧸ w.asIdeal)
  have hcard : Fintype.card (𝓞 E ⧸ w.asIdeal) = Ideal.absNorm w.asIdeal := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
  obtain ⟨z, hz⟩ := (ZMod.ringEquivOfPrime _ hp hcard).surjective (Ideal.Quotient.mk _ y)
  obtain ⟨n, rfl⟩ := ZMod.natCast_zmod_surjective z
  rw [map_natCast, ← map_natCast (Ideal.Quotient.mk w.asIdeal), Ideal.Quotient.eq] at hz
  have hn := hconj (neg_mem hz)
  rw [neg_sub, map_sub, map_natCast] at hn
  have := neg_mem (add_mem hn hz)
  rw [show -(ringOfIntegersComplexConj E y - n + (n - y)) = y - ringOfIntegersComplexConj E y by
    ring] at this
  exact hy this

end Residues

/-! ### Bounds for the step weights -/

section Weights

omit [IsCMField E] in
/-- There are `P` lines in `k_w^ι` with `P (q_w − 1) ≤ q_w^{#ι}`; both sides are read with
`Nat.card`, so for an infinite `ι` there are `0` lines. -/
private theorem natCard_projectivization_mul_le (w : HeightOneSpectrum (𝓞 E)) (ι : Type*) :
    (Nat.card (ℙ (IsLocalRing.ResidueField (w.adicCompletionIntegers E))
      (ι → IsLocalRing.ResidueField (w.adicCompletionIntegers E))) : ℝ) *
        ((Ideal.absNorm w.asIdeal : ℝ) - 1) ≤ (Ideal.absNorm w.asIdeal : ℝ) ^ Nat.card ι := by
  set k := IsLocalRing.ResidueField (w.adicCompletionIntegers E)
  rw [← natCard_residueField w]
  have h1 : 1 ≤ Nat.card k := Nat.one_le_iff_ne_zero.2 Nat.card_pos.ne'
  have hV : Nat.card (ι → k) ≤ Nat.card k ^ Nat.card ι := by
    rcases finite_or_infinite ι with hι | hι
    · rw [Nat.card_fun]
    · rw [Nat.card_eq_zero_of_infinite]
      exact Nat.zero_le _
  have h2 : Nat.card (ℙ k (ι → k)) * (Nat.card k - 1) ≤ Nat.card k ^ Nat.card ι :=
    Projectivization.card k (ι → k) ▸ (Nat.sub_le _ _).trans hV
  calc (Nat.card (ℙ k (ι → k)) : ℝ) * ((Nat.card k : ℝ) - 1)
      = ((Nat.card (ℙ k (ι → k)) * (Nat.card k - 1) : ℕ) : ℝ) := by
        push_cast [Nat.cast_sub h1]
        ring
    _ ≤ (Nat.card k : ℝ) ^ Nat.card ι := by exact_mod_cast h2

/-- The arithmetic of the step-weight bound: `P (q − 1) ≤ q^n`, `R ≤ √q` and `2n < M` give
`P R q^{−M/2} ≤ 1/(q − 1)`. -/
private theorem mul_mul_rpow_le_one_div {q P R : ℝ} {n M : ℕ} (hq : 1 < q)
    (hP : P * (q - 1) ≤ q ^ n) (hR₀ : 0 ≤ R) (hR : R ≤ √q) (hM : 2 * n < M) :
    P * R * q ^ (-(M : ℝ) / 2) ≤ 1 / (q - 1) := by
  rw [le_div_iff₀ (by linarith)]
  have hM' : (2 * n + 1 : ℝ) ≤ M := by exact_mod_cast hM
  have h1 : q ^ n * √q * q ^ (-(M : ℝ) / 2) ≤ 1 := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_add (by linarith),
      ← Real.rpow_add (by linarith)]
    exact Real.rpow_le_one_of_one_le_of_nonpos hq.le (by linarith)
  calc P * R * q ^ (-(M : ℝ) / 2) * (q - 1) = P * (q - 1) * R * q ^ (-(M : ℝ) / 2) := by ring
    _ ≤ q ^ n * √q * q ^ (-(M : ℝ) / 2) := by gcongr
    _ ≤ 1 := h1

/-- The arithmetic of the split bound: `P (q − 1) ≤ q^n`, `R ≤ 1` and `2n < M` give
`P R q^{−M/2} ≤ 1/((q − 1)√q)`. -/
private theorem mul_mul_rpow_le_one_div_mul_sqrt {q P R : ℝ} {n M : ℕ} (hq : 1 < q)
    (hP : P * (q - 1) ≤ q ^ n) (hR₀ : 0 ≤ R) (hR : R ≤ 1) (hM : 2 * n < M) :
    P * R * q ^ (-(M : ℝ) / 2) ≤ 1 / ((q - 1) * √q) := by
  have : 0 < q - 1 := by linarith
  rw [le_div_iff₀ (by positivity)]
  have hM' : (2 * n + 1 : ℝ) ≤ M := by exact_mod_cast hM
  have h1 : q ^ n * q ^ (-(M : ℝ) / 2) * √q ≤ 1 := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_add (by linarith),
      ← Real.rpow_add (by linarith)]
    exact Real.rpow_le_one_of_one_le_of_nonpos hq.le (by linarith)
  calc P * R * q ^ (-(M : ℝ) / 2) * ((q - 1) * √q)
      = P * (q - 1) * R * q ^ (-(M : ℝ) / 2) * √q := by ring
    _ ≤ q ^ n * 1 * q ^ (-(M : ℝ) / 2) * √q := by gcongr
    _ ≤ 1 := by rwa [mul_one]

variable (ι : Type*)

/-- The number of steps is the number of lines in `k_w^ι` times the number of residues. -/
theorem ncard_neighborSteps (ϖ : w.adicCompletion E) :
    (w.neighborSteps ι ϖ).ncard =
      Nat.card (ℙ (IsLocalRing.ResidueField (w.adicCompletionIntegers E))
        (ι → IsLocalRing.ResidueField (w.adicCompletionIntegers E))) *
        (w.neighborResidues ϖ).ncard := by
  rw [neighborSteps, Set.ncard_prod, Set.ncard_univ]

variable {w}

/-- **The step weight bound.** If `2n < M` (`n = #ι`), `ϖ` is a uniformiser and `y − conj y ∉ w`,
then `s(w) ≤ 1/(q_w − 1)`. -/
theorem stepWeight_le {M : ℕ} (hM : 2 * Nat.card ι < M) {ϖ : w.adicCompletion E}
    (hϖ : Valued.v ϖ = exp (-1)) {y : 𝓞 E} (hy : y - ringOfIntegersComplexConj E y ∉ w.asIdeal) :
    w.stepWeight ι M ϖ ≤ 1 / ((Ideal.absNorm w.asIdeal : ℝ) - 1) := by
  rw [stepWeight_def, ncard_neighborSteps, Nat.cast_mul]
  refine mul_mul_rpow_le_one_div (by exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm w)
    (natCard_projectivization_mul_le w ι) (Nat.cast_nonneg _) ?_ hM
  rw [Real.le_sqrt (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
  exact_mod_cast ncard_neighborResidues_sq_le hϖ hy

/-- **The step weight bound at a split place.** If `conj w ≠ w`, `2n < M` (`n = #ι`) and `ϖ` lies in
the maximal ideal, then `s(w) ≤ 1/((q_w − 1)√q_w)`. -/
theorem stepWeight_le_of_conjPlace_ne (h : conjPlace w ≠ w) {M : ℕ} (hM : 2 * Nat.card ι < M)
    {ϖ : w.adicCompletion E} (hϖ : Valued.v ϖ < 1) :
    w.stepWeight ι M ϖ ≤
      1 / (((Ideal.absNorm w.asIdeal : ℝ) - 1) * √(Ideal.absNorm w.asIdeal : ℝ)) := by
  rw [stepWeight_def, ncard_neighborSteps, Nat.cast_mul]
  refine mul_mul_rpow_le_one_div_mul_sqrt
    (by exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm w)
    (natCard_projectivization_mul_le w ι) (Nat.cast_nonneg _) ?_ hM
  rw [neighborResidues_eq_singleton_zero h hϖ, Set.ncard_singleton, Nat.cast_one]

/-- If `E` contains a root `ω` of `X² + X + 1` and a root `i` of `X² + 1`, then at every finite
place `w` one of `i − conj i`, `ω − conj ω` lies outside `w`: as `i · conj i = ω · conj ω = 1`,
otherwise `w` would contain `−i (i − conj i) = 2` and `−ω (ω − conj ω) = ω + 2`, hence the unit
`ω`. -/
private theorem exists_sub_ringOfIntegersComplexConj_notMem (w : HeightOneSpectrum (𝓞 E))
    {ω i : 𝓞 E} (hω : ω ^ 2 + ω + 1 = 0) (hi : i ^ 2 + 1 = 0) :
    ∃ y : 𝓞 E, y - ringOfIntegersComplexConj E y ∉ w.asIdeal := by
  -- A root of unity times its conjugate is `1`.
  have hconj {z : 𝓞 E} {n : ℕ} (hn : n ≠ 0) (hz : z ^ n = 1) :
      z * ringOfIntegersComplexConj E z = 1 := by
    refine RingOfIntegers.ext ?_
    simpa using mul_complexConj_eq_one_of_pow_eq (K := E) (x := 1) hn
      (by exact_mod_cast congrArg ((↑) : 𝓞 E → E) hz) (by simp)
  have hi' := hconj four_ne_zero (by linear_combination (i ^ 2 - 1) * hi)
  have hω' := hconj three_ne_zero (by linear_combination (ω - 1) * hω)
  by_contra! h
  have h2 : (2 : 𝓞 E) ∈ w.asIdeal := by
    convert w.asIdeal.mul_mem_left (-i) (h i) using 1
    linear_combination hi - hi'
  have hω2 : ω + 2 ∈ w.asIdeal := by
    convert w.asIdeal.mul_mem_left (-ω) (h ω) using 1
    linear_combination hω - hω'
  have h1 : (1 : 𝓞 E) ∈ w.asIdeal := by
    convert w.asIdeal.mul_mem_left (-ω - 1) (sub_mem hω2 h2) using 1
    linear_combination hω
  exact w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h1)

/-- **The step weights of a place and its conjugate.** If `2n < M` (`n = #ι`), `E` contains roots
of `X² + X + 1` and `X² + 1`, and `ϖ w` and `ϖ (conj w)` are uniformisers, then
`s(w) + s(conj w) ≤ 1/3`, with one term if `conj w = w`. -/
theorem sum_stepWeight_pair_le [DecidableEq (HeightOneSpectrum (𝓞 E))] {M : ℕ}
    (hM : 2 * Nat.card ι < M) {ω i : 𝓞 E} (hω : ω ^ 2 + ω + 1 = 0) (hi : i ^ 2 + 1 = 0)
    {ϖ : (u : HeightOneSpectrum (𝓞 E)) → u.adicCompletion E}
    (hϖ : ∀ u ∈ ({w, conjPlace w} : Finset _), Valued.v (ϖ u) = exp (-1)) :
    ∑ u ∈ {w, conjPlace w}, u.stepWeight ι M (ϖ u) ≤ 1 / 3 := by
  have hq (u : HeightOneSpectrum (𝓞 E)) : (4 : ℝ) ≤ Ideal.absNorm u.asIdeal := by
    exact_mod_cast u.four_le_absNorm hω hi
  by_cases h : conjPlace w = w
  · have hϖw := hϖ w (by simp)
    obtain ⟨y, hy⟩ := exists_sub_ringOfIntegersComplexConj_notMem w hω hi
    rw [h, Finset.insert_eq_of_mem (Finset.mem_singleton_self w), Finset.sum_singleton]
    refine (stepWeight_le ι hM hϖw hy).trans ?_
    gcongr
    linarith [hq w]
  · have hsplit (u : HeightOneSpectrum (𝓞 E)) (hu : conjPlace u ≠ u)
        (hϖu : Valued.v (ϖ u) = exp (-1)) : u.stepWeight ι M (ϖ u) ≤ 1 / 6 := by
      refine (stepWeight_le_of_conjPlace_ne ι hu hM (by rw [hϖu]; decide)).trans ?_
      have h2 : (2 : ℝ) ≤ √(Ideal.absNorm u.asIdeal : ℝ) := by
        rw [Real.le_sqrt (by norm_num) (Nat.cast_nonneg _)]
        linarith [hq u]
      gcongr
      nlinarith [hq u]
    have hw : conjPlace (conjPlace w) ≠ conjPlace w := by
      rw [conjPlace_conjPlace]
      exact Ne.symm h
    rw [Finset.sum_pair (Ne.symm h)]
    linarith [hsplit w h (hϖ w (by simp)), hsplit _ hw (hϖ _ (by simp))]

/-- **The step weights are summable.** If `2n < M` (`n = #ι`), the `ϖ u` are uniformisers and
`E` has an integer `y` with `y − conj y` a unit, then `∑_w s(w) < ∞` over the finite places of `E`:
`s(w) ≤ 2 q_w^{−3/2}` at a split place, and a place with `conj w = w` has residue degree at least
two, where `s(w) ≤ 2 q_w^{−1}`. -/
theorem summable_stepWeight {M : ℕ} (hM : 2 * Nat.card ι < M)
    {ϖ : (u : HeightOneSpectrum (𝓞 E)) → u.adicCompletion E}
    (hϖ : ∀ u, Valued.v (ϖ u) = exp (-1)) {y : 𝓞 E}
    (hy : IsUnit (y - ringOfIntegersComplexConj E y)) :
    Summable fun u : HeightOneSpectrum (𝓞 E) ↦ u.stepWeight ι M (ϖ u) := by
  have hy' (u : HeightOneSpectrum (𝓞 E)) : y - ringOfIntegersComplexConj E y ∉ u.asIdeal :=
    fun hmem ↦ u.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hmem hy)
  have h₁ : Summable fun u : HeightOneSpectrum (𝓞 E) ↦
      (Ideal.absNorm u.asIdeal : ℝ) ^ (-(3 / 2 : ℝ)) :=
    summable_of_sum_le (fun _ ↦ by positivity)
      (TauCeti.sum_absNorm_rpow_le_finrank_mul_tsum (by norm_num))
  have h₂ : Summable ((TauCeti.higherDegreePrimes E).indicator
      fun u : HeightOneSpectrum (𝓞 E) ↦ (Ideal.absNorm u.asIdeal : ℝ) ^ (-(1 : ℝ))) :=
    summable_subtype_iff_indicator.1
      (TauCeti.summable_absNorm_rpow_higherDegreePrimes (by norm_num))
  refine Summable.of_nonneg_of_le (fun u ↦ stepWeight_nonneg u ι M (ϖ u)) (fun u ↦ ?_)
    ((h₁.add h₂).mul_left 2)
  set q : ℝ := (Ideal.absNorm u.asIdeal : ℝ) with hq_def
  have hq : 2 ≤ q := by
    rw [hq_def]
    exact_mod_cast Nat.succ_le_of_lt (NumberField.HeightOneSpectrum.one_lt_absNorm u)
  have hind : 0 ≤ (TauCeti.higherDegreePrimes E).indicator
      (fun u : HeightOneSpectrum (𝓞 E) ↦ (Ideal.absNorm u.asIdeal : ℝ) ^ (-(1 : ℝ))) u :=
    Set.indicator_nonneg (fun _ _ ↦ by positivity) u
  have hsqrt : 0 < √q := Real.sqrt_pos.2 (by linarith)
  have hq32 : q ^ (-(3 / 2 : ℝ)) = 1 / (q * √q) := by
    rw [Real.rpow_neg (by linarith), Real.sqrt_eq_rpow, ← Real.rpow_one_add' (by linarith)
      (by norm_num), one_div]
    norm_num
  by_cases hu : conjPlace u = u
  · rw [Set.indicator_of_mem (mem_higherDegreePrimes_of_conjPlace_eq hu (hy' u)),
      Real.rpow_neg_one]
    refine (stepWeight_le ι hM (hϖ u) (hy' u)).trans ?_
    have : 1 / (q - 1) ≤ 2 * q⁻¹ := by
      rw [div_le_iff₀ (by linarith)]
      field_simp
      linarith
    have : 0 ≤ q ^ (-(3 / 2 : ℝ)) := by positivity
    linarith
  · refine (stepWeight_le_of_conjPlace_ne ι hu hM (by rw [hϖ u]; decide)).trans ?_
    have : 1 / ((q - 1) * √q) ≤ 2 * q ^ (-(3 / 2 : ℝ)) := by
      rw [hq32, mul_one_div, div_le_div_iff₀ (mul_pos (by linarith) hsqrt) (by positivity)]
      nlinarith
    linarith

end Weights

/-! ### The place signs -/

open scoped Classical in
/-- The **place sign** `ε_w` of a finite place `w` of a CM field, for the well-ordering
`WellOrderingRel` of the finite places: `ε_w = −1` if `w` precedes its conjugate `conj w`, and
`ε_w = 1` otherwise. -/
def placeSign : ℤ :=
  if WellOrderingRel w (conjPlace w) then -1 else 1

open scoped Classical in
/-- The defining formula of the place sign. -/
theorem placeSign_def : w.placeSign = if WellOrderingRel w (conjPlace w) then -1 else 1 :=
  (rfl)

variable {w}

/-- `ε_w = 1` at a place with `conj w = w`. -/
theorem placeSign_of_conjPlace_eq (h : conjPlace w = w) : w.placeSign = 1 := by
  rw [placeSign, h, ite_eq_right (irrefl w)]

/-- `ε_{conj w} = −ε_w` at a split place: of `w` and `conj w`, exactly one precedes the other. -/
theorem placeSign_conjPlace_of_ne (h : conjPlace w ≠ w) :
    (conjPlace w).placeSign = -w.placeSign := by
  rw [placeSign, placeSign, conjPlace_conjPlace]
  rcases trichotomous_of WellOrderingRel w (conjPlace w) with hlt | heq | hgt
  · rw [ite_eq_right (asymm hlt), ite_eq_left hlt, neg_neg]
  · exact absurd heq.symm h
  · rw [ite_eq_left hgt, ite_eq_right (asymm hgt)]

/-- `ε_w² = 1`. -/
@[simp]
theorem placeSign_mul_self : w.placeSign * w.placeSign = 1 := by
  unfold placeSign
  split_ifs <;> rfl

/-- **The Euler factor of a split pair.** At a split place, with `q_{conj w} = q_w`,
`(1 − ε_w q_w^{−s}) (1 − ε_{conj w} q_{conj w}^{−s}) = 1 − q_w^{−2s}`. -/
theorem prod_one_sub_placeSign_mul_rpow [DecidableEq (HeightOneSpectrum (𝓞 E))]
    (h : conjPlace w ≠ w) (s : ℝ) :
    ∏ u ∈ {w, conjPlace w}, (1 - u.placeSign * (Ideal.absNorm u.asIdeal : ℝ) ^ (-s)) =
      1 - (Ideal.absNorm w.asIdeal : ℝ) ^ (-(2 * s)) := by
  have e : -(2 * s) = -s * 2 := by ring
  rw [Finset.prod_pair (Ne.symm h), placeSign_conjPlace_of_ne h, absNorm_conjPlace, e,
    Real.rpow_mul (Nat.cast_nonneg _), Real.rpow_two]
  have := congrArg (Int.cast : ℤ → ℝ) (placeSign_mul_self (w := w))
  push_cast at this ⊢
  linear_combination -((Ideal.absNorm w.asIdeal : ℝ) ^ (-s)) ^ 2 * this

end IsDedekindDomain.HeightOneSpectrum
