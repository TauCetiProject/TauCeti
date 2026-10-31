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

/-!
# Finite places of number fields

This file records general facts about the finite places of a number field.

The valuation dictionary `FinitePlace.mk_apply_le_one_iff` and
`FinitePlace.mk_apply_eq_one_iff` compares the finite-place absolute value with the adic valuation.
These comparisons follow Ralf Stephan's `ArithmeticHeights/SUnit.lean` in
`rwst/Subspace-Theorems` at `e443c2479e19f7665b31d8e94e2317c8ced1ca06` (Apache 2.0).

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

Finally, `NumberField.FinitePlace.hasFiniteMulSupport_iSup` records that the maximum of the
finite-place absolute values of the coordinates of a nonzero finite tuple is `1` at all but
finitely many finite places, and `NumberField.FinitePlace.hasFiniteMulSupport_max_one` and
`NumberField.FinitePlace.hasFiniteMulSupport_min_one` record the same for the absolute value of an
element truncated from below or above at `1`.
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

/-- An element is integral at a prime iff its finite-place absolute value is at most one. -/
theorem mk_apply_le_one_iff (v : HeightOneSpectrum (𝓞 K)) (x : K) :
    mk v x ≤ 1 ↔ v.valuation K x ≤ 1 := by
  rw [mk_apply, norm_embedding, HeightOneSpectrum.adicAbv_def]
  norm_cast
  exact WithZeroMulInt.toNNReal_le_one_iff (HeightOneSpectrum.one_lt_absNorm_nnreal v)

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
