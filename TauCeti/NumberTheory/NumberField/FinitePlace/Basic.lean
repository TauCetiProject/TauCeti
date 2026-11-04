/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace

public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.Analysis.AbsoluteValue.Equivalence
import Mathlib.Algebra.Order.Hom.Lattice
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Finite places of number fields

This file records general facts about the finite places of a number field.

The nonzero values of a finite place are exactly the integer powers of its prime norm
(`apply_eq_absNorm_zpow`, `exists_ne_zero_apply_eq_absNorm_zpow`), using Mathlib's
`HeightOneSpectrum.valuation_surjective` for attainment.

The valuation dictionary `FinitePlace.mk_apply_le_one_iff` and
`FinitePlace.mk_apply_eq_one_iff` compares the finite-place absolute value with the adic valuation.
These comparisons follow Ralf Stephan's `ArithmeticHeights/SUnit.lean` in
`rwst/Subspace-Theorems` at `e443c2479e19f7665b31d8e94e2317c8ced1ca06` (Apache 2.0).
`FinitePlace.mk_apply_le_one_iff_algebraMap_mem` reads integrality in the adic completion instead.

The file also records that a number field always *has* a finite place: the finite places are the
height one primes of its ring of integers, and that ring is a Dedekind domain which is not a
field, so it has a maximal ideal. Recording this as a `Nonempty` instance lets local-global
arguments pick a finite place with `Classical.arbitrary` whenever a hypothesis quantified over
all finite places has to be used at some place — for instance to read off an invariant, such as
the dimension of the underlying space, that is the same at every place. Without the instance
each such argument has to rebuild the existence proof inline.

Two finite places are equal exactly when their absolute values are equivalent,
`NumberField.FinitePlace.eq_iff_isEquiv`, as Mathlib has for infinite places. For a prime `w` of a
finite extension over a prime `v`, `NumberField.FinitePlace.mk_apply_algebraMap` restates Mathlib's
`equivHeightOneSpectrum_symm_apply_algebraMap` with `FinitePlace.mk`: on the base, the finite place
of `w` is the `e * f`-th power of that of `v`.

`NumberField.HeightOneSpectrum.log_adicAbv` reads the logarithm of the `v`-adic absolute value
as minus the `v`-adic order times `log N(v)`, the form in which valuations enter height estimates.

`NumberField.FinitePlace.finprod_comp_mk` reindexes a product over the finite places by the
height one primes of the ring of integers.

Finally, `NumberField.FinitePlace.hasFiniteMulSupport_iSup` records that the maximum of the
finite-place absolute values of the coordinates of a nonzero finite tuple is `1` at all but
finitely many finite places, and `NumberField.FinitePlace.hasFiniteMulSupport_max_one` and
`NumberField.FinitePlace.hasFiniteMulSupport_min_one` record the same for the absolute value of an
element truncated from below or above at `1`.

An algebraic integer is at most `1` at every finite place, `NumberField.FinitePlace.apply_le_one`,
and `NumberField.FinitePlace.exists_ne_zero_forall_apply_le` produces a nonzero algebraic integer
which is as small as prescribed at finitely many finite places. Its form
`NumberField.FinitePlace.exists_ne_zero_forall_mul_apply_le` clears prescribed bounds `R v` at
those places: `v d * R v ≤ 1`. When a finite place `u` lies outside that finite set,
`NumberField.FinitePlace.exists_apply_eq_one_forall_apply_le` and
`NumberField.FinitePlace.exists_apply_eq_one_forall_mul_apply_le` choose `d` to have `u d = 1` as
well. These follow Ralf Stephan's `DiophantineApproximation/FinitePlaceValues.lean` in
`rwst/Subspace-Theorems`, snapshot `c26d909dc48cf7fe` (Apache 2.0).
-/

public section
noncomputable section

open IsDedekindDomain NumberField

namespace TauCeti

variable {K : Type*} [Field K]

/-- A number field has a finite place: its ring of integers is not a field. -/
instance [NumberField K] : Nonempty (HeightOneSpectrum (𝓞 K)) :=
  ⟨(HeightOneSpectrum.equivMaximalSpectrum (RingOfIntegers.not_isField K)).symm
    (Classical.choice (inferInstance : Nonempty (MaximalSpectrum (𝓞 K))))⟩

end TauCeti

namespace NumberField.FinitePlace

variable {K : Type*} [Field K] [NumberField K]

/-- Every nonzero finite-place value is an integer power of the norm of its prime. -/
theorem apply_eq_absNorm_zpow (v : FinitePlace K) {x : K} (hx : x ≠ 0) :
    v x = (v.maximalIdeal.asIdeal.absNorm : ℝ) ^
      WithZero.log (v.maximalIdeal.valuation K x) := by
  rw [← norm_embedding_eq, norm_embedding, HeightOneSpectrum.adicAbv_def,
    WithZeroMulInt.toNNReal_neg_apply _ ((v.maximalIdeal.valuation K).ne_zero_iff.mpr hx),
    NNReal.coe_zpow, NNReal.coe_natCast]

/-- Every integer power of the prime norm occurs as a nonzero finite-place value. -/
theorem exists_ne_zero_apply_eq_absNorm_zpow (v : FinitePlace K) (n : ℤ) :
    ∃ x : K, x ≠ 0 ∧ v x = (v.maximalIdeal.asIdeal.absNorm : ℝ) ^ n := by
  obtain ⟨x, hx⟩ := v.maximalIdeal.valuation_surjective K (WithZero.exp n)
  have hx0 : x ≠ 0 := (v.maximalIdeal.valuation K).ne_zero_iff.mp (by
    rw [hx]
    exact WithZero.exp_ne_zero)
  refine ⟨x, hx0, ?_⟩
  rw [v.apply_eq_absNorm_zpow hx0, hx, WithZero.log_exp]

/-- An element is integral at a prime iff its finite-place absolute value is at most one. -/
theorem mk_apply_le_one_iff (v : HeightOneSpectrum (𝓞 K)) (x : K) :
    mk v x ≤ 1 ↔ v.valuation K x ≤ 1 := by
  rw [mk_apply, norm_embedding, HeightOneSpectrum.adicAbv_def]
  norm_cast
  exact WithZeroMulInt.toNNReal_le_one_iff (HeightOneSpectrum.one_lt_absNorm_nnreal v)

/-- An element is integral at a prime iff its finite-place absolute value is at most one, read in
the completion: its image lies in the ring of integers of the adic completion. -/
theorem mk_apply_le_one_iff_algebraMap_mem (v : HeightOneSpectrum (𝓞 K)) (x : K) :
    mk v x ≤ 1 ↔ algebraMap K (v.adicCompletion K) x ∈ v.adicCompletionIntegers K := by
  rw [mk_apply_le_one_iff, HeightOneSpectrum.mem_adicCompletionIntegers]
  simp [HeightOneSpectrum.algebraMap_adicCompletion]

/-- An element has valuation one at a prime iff its finite-place absolute value is one. -/
theorem mk_apply_eq_one_iff (v : HeightOneSpectrum (𝓞 K)) (x : K) :
    mk v x = 1 ↔ v.valuation K x = 1 := by
  rw [mk_apply, norm_embedding, HeightOneSpectrum.adicAbv_def]
  norm_cast
  exact WithZeroMulInt.toNNReal_eq_one_iff _ (HeightOneSpectrum.absNorm_ne_zero v)
    (HeightOneSpectrum.one_lt_absNorm_nnreal v).ne'

/-- Two finite places of a number field are equal if and only if their absolute values are
equivalent. This is the finite counterpart of Mathlib's `InfinitePlace.eq_iff_isEquiv`. -/
theorem eq_iff_isEquiv {w v : FinitePlace K} : w = v ↔ w.1.IsEquiv v.1 := by
  refine ⟨fun h ↦ h ▸ .rfl, fun h ↦ ?_⟩
  rw [← maximalIdeal_inj]
  refine HeightOneSpectrum.ext (Ideal.ext fun y ↦ ?_)
  rw [← norm_lt_one_iff_mem K, ← norm_lt_one_iff_mem K, ← mk_apply, ← mk_apply,
    mk_maximalIdeal, mk_maximalIdeal]
  exact h.lt_one_iff

/-- For a prime `w` of `𝓞 L` over the prime `v` of `𝓞 K`, the finite place of `w` restricts on
`K` to the `e * f`-th power of the finite place of `v`, where `e` and `f` are the ramification
index and the inertia degree of `w` over `v`. This is Mathlib's
`equivHeightOneSpectrum_symm_apply_algebraMap` stated with `FinitePlace.mk`. -/
theorem mk_apply_algebraMap {L : Type*} [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal]
    (x : K) :
    mk w (algebraMap K L x) =
      mk v x ^ (w.asIdeal.ramificationIdx (𝓞 K) * w.asIdeal.inertiaDeg (𝓞 K)) := by
  simpa only [equivHeightOneSpectrum_symm_apply, ← mk_apply] using
    equivHeightOneSpectrum_symm_apply_algebraMap v w x

/-- A product over the finite places of a number field, reindexed by the height one primes of its
ring of integers. -/
theorem finprod_comp_mk {M : Type*} [CommMonoid M] (f : FinitePlace K → M) :
    ∏ᶠ v : HeightOneSpectrum (𝓞 K), f (mk v) = ∏ᶠ w, f w :=
  finprod_comp_equiv equivHeightOneSpectrum.symm

/-- For a nonzero tuple over a number field, the maximum of the finite-place absolute values of
its coordinates is `1` at all but finitely many finite places. -/
-- This proof adapts the private `Height.hasFiniteMulSupport_iSup_nonarchAbsVal` from Mathlib.
theorem hasFiniteMulSupport_iSup {ι : Type*} [Finite ι] {y : ι → K} (hy : y ≠ 0) :
    (fun v : FinitePlace K ↦ ⨆ i, v (y i)).HasFiniteMulSupport := by
  have : Nonempty {i // y i ≠ 0} := nonempty_subtype.mpr (Function.ne_iff.mp hy)
  simp_rw [Finite.iSup_eq_iSup_subtype hy]
  exact .iSup fun i ↦ FinitePlace.hasFiniteMulSupport i.property

/-- Truncating the finite places of `x` from below keeps finite multiplicative support. For
`x = 0` the family is constantly `1`. -/
theorem hasFiniteMulSupport_max_one (x : K) :
    Function.HasFiniteMulSupport fun v : FinitePlace K ↦ max (v x) 1 := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp [Function.HasFiniteMulSupport]
  · exact Function.HasFiniteMulSupport.fun_comp (FinitePlace.hasFiniteMulSupport hx)
      (g := fun t ↦ max t 1) (max_self 1)

/-- Truncating the finite places of a nonzero `x` from above keeps finite multiplicative
support. -/
theorem hasFiniteMulSupport_min_one {x : K} (hx : x ≠ 0) :
    Function.HasFiniteMulSupport fun v : FinitePlace K ↦ min 1 (v x) :=
  Function.HasFiniteMulSupport.fun_comp (FinitePlace.hasFiniteMulSupport hx) (min_self 1)

/-- An algebraic integer has absolute value at most `1` at every finite place. -/
theorem apply_le_one (v : FinitePlace K) (x : 𝓞 K) : v (x : K) ≤ 1 :=
  norm_embedding_eq v x ▸ norm_le_one K v.maximalIdeal x

/-- Given `p w ∈ 𝔭_w` for each `w ∈ T`, some power of `∏ w ∈ T.attach, p w` has absolute value at
most `ε v` at every `v ∈ T`. -/
private theorem exists_pow_prod_forall_apply_le {T : Finset (FinitePlace K)}
    (p : {w // w ∈ T} → 𝓞 K) (hp : ∀ w, p w ∈ w.1.maximalIdeal.asIdeal)
    {ε : FinitePlace K → ℝ} (hε : ∀ v ∈ T, 0 < ε v) :
    ∃ m : ℕ, ∀ v ∈ T, v (((∏ w ∈ T.attach, p w) ^ m : 𝓞 K) : K) ≤ ε v := by
  set t : 𝓞 K := ∏ w ∈ T.attach, p w
  have ht (v : FinitePlace K) (hv : v ∈ T) : v (t : K) < 1 := by
    rw [← norm_embedding_eq, norm_lt_one_iff_mem]
    obtain ⟨c, hc⟩ : p ⟨v, hv⟩ ∣ t := Finset.dvd_prod_of_mem p (Finset.mem_attach T ⟨v, hv⟩)
    rw [hc]
    exact Ideal.mul_mem_right _ _ (hp ⟨v, hv⟩)
  have hpow (v : FinitePlace K) (hv : v ∈ T) :
      ∀ᶠ m : ℕ in Filter.atTop, v ((t ^ m : 𝓞 K) : K) ≤ ε v := by
    simp_rw [map_pow]
    exact (tendsto_pow_atTop_nhds_zero_of_lt_one (apply_nonneg v _) (ht v hv)).eventually
      (ge_mem_nhds (hε v hv))
  exact ((Filter.eventually_all_finset T).2 hpow).exists

private theorem mul_le_one_of_le_inv_one_add {x R : ℝ} (hR : 0 ≤ R) (hx : x ≤ (1 + R)⁻¹) :
    x * R ≤ 1 :=
  (mul_le_mul_of_nonneg_right hx hR).trans ((inv_mul_le_iff₀ (by positivity)).mpr (by linarith))

/-- Some nonzero algebraic integer is as small as prescribed at every place of a finite set of
finite places. -/
theorem exists_ne_zero_forall_apply_le (T : Finset (FinitePlace K)) {ε : FinitePlace K → ℝ}
    (hε : ∀ v ∈ T, 0 < ε v) : ∃ d : 𝓞 K, d ≠ 0 ∧ ∀ v ∈ T, v (d : K) ≤ ε v := by
  choose p hp hp0 using fun w : {w : FinitePlace K // w ∈ T} ↦
    Submodule.exists_mem_ne_zero_of_ne_bot w.1.maximalIdeal.ne_bot
  obtain ⟨m, hm⟩ := exists_pow_prod_forall_apply_le p hp hε
  exact ⟨(∏ w ∈ T.attach, p w) ^ m,
    pow_ne_zero m (Finset.prod_ne_zero_iff.2 fun w _ ↦ hp0 w), hm⟩

/-- Some nonzero algebraic integer clears prescribed nonnegative bounds at every place of a finite
set of finite places: `v d * R v ≤ 1` there. -/
theorem exists_ne_zero_forall_mul_apply_le (T : Finset (FinitePlace K)) {R : FinitePlace K → ℝ}
    (hR : ∀ v ∈ T, 0 ≤ R v) : ∃ d : 𝓞 K, d ≠ 0 ∧ ∀ v ∈ T, v (d : K) * R v ≤ 1 := by
  obtain ⟨d, hd0, hd⟩ := exists_ne_zero_forall_apply_le T (ε := fun v ↦ (1 + R v)⁻¹)
    fun v hv ↦ by have := hR v hv; positivity
  exact ⟨d, hd0, fun v hv ↦ mul_le_one_of_le_inv_one_add (hR v hv) (hd v hv)⟩

/-- Given a finite place `u` outside a finite set `T` of finite places, some algebraic integer has
absolute value `1` at `u` and is as small as prescribed at every place of `T`. -/
theorem exists_apply_eq_one_forall_apply_le (u : FinitePlace K) {T : Finset (FinitePlace K)}
    (hu : u ∉ T) {ε : FinitePlace K → ℝ} (hε : ∀ v ∈ T, 0 < ε v) :
    ∃ d : 𝓞 K, u (d : K) = 1 ∧ ∀ v ∈ T, v (d : K) ≤ ε v := by
  -- For each `w ∈ T`, its prime is maximal and distinct from that of `u`, so it contains an
  -- element outside the prime of `u`.
  have hp (w : {w // w ∈ T}) :
      ∃ x : 𝓞 K, x ∈ w.1.maximalIdeal.asIdeal ∧ x ∉ u.maximalIdeal.asIdeal := by
    have hne : w.1.maximalIdeal ≠ u.maximalIdeal :=
      (maximalIdeal_inj w.1 u).not.mpr (ne_of_mem_of_not_mem w.2 hu)
    by_contra! H
    exact hne <| HeightOneSpectrum.ext_iff.mpr <|
      Ideal.IsMaximal.eq_of_le w.1.maximalIdeal.isMaximal Ideal.IsPrime.ne_top' H
  choose p hp_mem hp_notMem using hp
  obtain ⟨m, hm⟩ := exists_pow_prod_forall_apply_le p hp_mem hε
  have hut : u (((∏ w ∈ T.attach, p w) ^ m : 𝓞 K) : K) = 1 := by
    rw [RingOfIntegers.coe_eq_algebraMap, map_pow, map_pow, map_prod, map_prod,
      Finset.prod_eq_one, one_pow]
    intro w _
    rw [← RingOfIntegers.coe_eq_algebraMap, ← norm_embedding_eq, norm_eq_one_iff_notMem]
    exact hp_notMem w
  exact ⟨(∏ w ∈ T.attach, p w) ^ m, hut, hm⟩

/-- Given a finite place `u` outside a finite set `T` of finite places, some algebraic integer has
absolute value `1` at `u` and clears prescribed nonnegative bounds `R v` at every place of `T`:
`v d * R v ≤ 1` there. -/
theorem exists_apply_eq_one_forall_mul_apply_le (u : FinitePlace K) {T : Finset (FinitePlace K)}
    (hu : u ∉ T) {R : FinitePlace K → ℝ} (hR : ∀ v ∈ T, 0 ≤ R v) :
    ∃ d : 𝓞 K, u (d : K) = 1 ∧ ∀ v ∈ T, v (d : K) * R v ≤ 1 := by
  obtain ⟨d, hdu, hd⟩ := u.exists_apply_eq_one_forall_apply_le hu (ε := fun v ↦ (1 + R v)⁻¹)
    fun v hv ↦ by have := hR v hv; positivity
  exact ⟨d, hdu, fun v hv ↦ mul_le_one_of_le_inv_one_add (hR v hv) (hd v hv)⟩

end NumberField.FinitePlace

namespace NumberField.HeightOneSpectrum

variable {K : Type*} [Field K] [NumberField K]

/-- The logarithm of the `v`-adic absolute value of `x` is `-ord_v(x)` times the logarithm of the
norm of `v`, where `ord_v(x) = -WithZero.log (v.valuation K x)` is the `v`-adic order of `x`.
Both sides vanish at `x = 0`. -/
theorem log_adicAbv (v : HeightOneSpectrum (𝓞 K)) (x : K) :
    Real.log (adicAbv K v x) =
      WithZero.log (v.valuation K x) * Real.log (Ideal.absNorm v.asIdeal) := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  rw [adicAbv_def, WithZeroMulInt.toNNReal_neg_apply _ ((v.valuation K).ne_zero_iff.mpr hx),
    NNReal.coe_zpow, NNReal.coe_natCast, Real.log_zpow]

end NumberField.HeightOneSpectrum
