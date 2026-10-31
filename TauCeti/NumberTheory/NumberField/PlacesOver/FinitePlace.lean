/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Ring.WithAbs
public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace

import TauCeti.Analysis.AbsoluteValue.Equivalence
import TauCeti.Analysis.AbsoluteValue.Nonarchimedean
import TauCeti.NumberTheory.NumberField.FinitePlace
import TauCeti.RingTheory.DedekindDomain.PrimesAbove

/-!
# Absolute values of a finite extension lying over a finite place

Let `F / K` be a finite extension of number fields and `𝔭` a nonzero prime of `𝓞 K`. This file
classifies the absolute values `w : AbsoluteValue F ℝ` lying over the finite place
`FinitePlace.mk 𝔭` of `K`, in the sense of Mathlib's `AbsoluteValue.LiesOver`, that is, whose
restriction to `K` is that place on the nose. They are exactly the functions
`y ↦ FinitePlace.mk 𝔓 y ^ (e * f)⁻¹` for the primes `𝔓` of `𝓞 F` over `𝔭`, where `e` and `f` are
the ramification index and the inertia degree of `𝔓` over `𝔭`, and the prime `𝔓` is determined
by `w`.

Such a `w` is in general **not** the absolute value of a finite place of `F`: restricted to `K`,
the finite place `FinitePlace.mk 𝔓` is the `e * f`-th power of `FinitePlace.mk 𝔭`
(Mathlib's `FinitePlace.equivHeightOneSpectrum_symm_apply_algebraMap`), so its root is what lies
over `𝔭`. This is what lets statements about a finite extension take an absolute value lying over
a place of the base without passing to a completion.

## Main results

* `NumberField.existsUnique_finitePlace_rpow_inv_eq_of_liesOver`: an absolute value of `F` lying
  over `FinitePlace.mk 𝔭` is `FinitePlace.mk 𝔓 ^ (e * f)⁻¹` for a unique prime `𝔓` of `𝓞 F` over
  `𝔭`.
* `NumberField.exists_finitePlace_rpow_inv_eq_of_liesOver`: the same for an arbitrary finite place
  `v` of `K`, with the exponent recorded as some `0 < t ≤ 1`.
* `NumberField.liesOver_finitePlace_mk_iff`: conversely, every such root lies over
  `FinitePlace.mk 𝔭`, so the classification is an equivalence.
* `NumberField.exists_liesOver_forall_mem_iff_apply_lt_one` and
  `NumberField.eq_of_liesOver_of_forall_apply_lt_one_iff`: the integers at which an absolute value
  `w` lying over `FinitePlace.mk 𝔭` is less than `1` form a prime over `𝔭`, and this prime
  determines `w`.
* `NumberField.finite_setOf_liesOver_finitePlace_mk` and
  `NumberField.nonempty_setOf_liesOver_finitePlace_mk`: the absolute values of `F` over a finite
  place of `K` form a finite nonempty set.

## Implementation notes

The prime attached to `w` is `{y ∈ 𝓞 F | w y < 1}`. That it is an ideal uses that `w` is
nonarchimedean, `AbsoluteValue.isNonarchimedean_of_liesOver`, and hence bounded by `1` on `𝓞 F`,
which is integral over `ℤ`. The absolute value `w` is then equivalent to the finite place of this
prime by `AbsoluteValue.isEquiv_of_lt_one_imp`, after writing an element of `F` as a quotient of
integers with denominator outside the prime, and the exponent is read off on a nonzero element of
`𝔭` through `AbsoluteValue.IsEquiv.eq_of_apply_eq`. The prime is unique because equivalent finite
places are equal, `NumberField.FinitePlace.eq_iff_isEquiv`.

The same classification, along the same route through the prime `{y ∈ 𝓞 F | w y < 1}` and
`AbsoluteValue.isEquiv_of_lt_one_imp`, is formalized in Ralf Stephan's `rwst/Subspace-Theorems`
at `09835cb23557ae5ae0cf55a9c4ab9055f5d60338`, file `DiophantineApproximation/PlacesOverFinite.lean`
(Apache 2.0).

## References

* E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press, 2006,
  §1.3.
-/

public section

open IsDedekindDomain AbsoluteValue

namespace NumberField

variable {K F : Type*} [Field K] [Field F] [NumberField K] [NumberField F] [Algebra K F]
  {𝔭 : HeightOneSpectrum (𝓞 K)} {w : AbsoluteValue F ℝ}

/-- An absolute value of a finite extension lying over a finite place is at most `1` on the ring
of integers. -/
private theorem apply_le_one_of_liesOver (v : FinitePlace K) [w.LiesOver v.1] (y : 𝓞 F) :
    w (y : F) ≤ 1 :=
  (isNonarchimedean_of_liesOver (u := v.1) v.add_le).apply_le_one_of_isIntegral_int
    (RingOfIntegers.isIntegral_coe y)

/-- An element of the ring of integers of `K` lies in `𝔭` if and only if an absolute value lying
over `FinitePlace.mk 𝔭` is less than `1` on it. -/
private theorem apply_algebraMap_lt_one_iff [w.LiesOver (FinitePlace.mk 𝔭).1] (a : 𝓞 K) :
    w (algebraMap (𝓞 K) (𝓞 F) a : F) < 1 ↔ a ∈ 𝔭.asIdeal := by
  rw [RingOfIntegers.coe_eq_algebraMap, ← IsScalarTower.algebraMap_apply,
    IsScalarTower.algebraMap_apply (𝓞 K) K F, LiesOver.apply_algebraMap (FinitePlace.mk 𝔭).1,
    ← FinitePlace.coe_apply, FinitePlace.mk_apply, FinitePlace.norm_lt_one_iff_mem]

variable (𝔭 w) in
/-- The prime of `𝓞 F` attached to an absolute value `w` lying over `FinitePlace.mk 𝔭`: the
integers at which `w` is less than `1`. -/
private noncomputable def primeOfLiesOver [w.LiesOver (FinitePlace.mk 𝔭).1] :
    HeightOneSpectrum (𝓞 F) where
  asIdeal :=
    { carrier := {y | w (y : F) < 1}
      add_mem' {a b} ha hb := by
        simp only [Set.mem_ofPred_eq, map_add] at ha hb ⊢
        exact (isNonarchimedean_of_liesOver (FinitePlace.mk 𝔭).add_le _ _).trans_lt
          (max_lt ha hb)
      zero_mem' := by simp
      smul_mem' c y hy := by
        simp only [Set.mem_ofPred_eq, smul_eq_mul, map_mul] at hy ⊢
        exact (mul_le_of_le_one_left (w.nonneg _)
          (apply_le_one_of_liesOver (FinitePlace.mk 𝔭) c)).trans_lt hy }
  isPrime :=
    { ne_top' h := by simpa using (Ideal.eq_top_iff_one _).mp h
      mem_or_mem' {a b} hab := by
        simp only [Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk,
          Set.mem_ofPred_eq, map_mul] at hab ⊢
        by_contra! h
        have ha := le_antisymm (apply_le_one_of_liesOver (FinitePlace.mk 𝔭) a) h.1
        have hb := le_antisymm (apply_le_one_of_liesOver (FinitePlace.mk 𝔭) b) h.2
        simp [ha, hb] at hab }
  ne_bot h := by
    obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot 𝔭.ne_bot
    have : algebraMap (𝓞 K) (𝓞 F) a ∈ (⊥ : Ideal (𝓞 F)) := by
      rw [← h]
      exact (apply_algebraMap_lt_one_iff a).mpr ha
    simp_all

private theorem mem_primeOfLiesOver [w.LiesOver (FinitePlace.mk 𝔭).1] {y : 𝓞 F} :
    y ∈ (primeOfLiesOver 𝔭 w).asIdeal ↔ w (y : F) < 1 :=
  Iff.rfl

/-- The prime attached to an absolute value lying over `FinitePlace.mk 𝔭` lies over `𝔭`. -/
private theorem liesOver_primeOfLiesOver [w.LiesOver (FinitePlace.mk 𝔭).1] :
    (primeOfLiesOver 𝔭 w).asIdeal.LiesOver 𝔭.asIdeal :=
  ⟨Ideal.ext fun a ↦ by
    rw [Ideal.under_def, Ideal.mem_comap, mem_primeOfLiesOver,
      apply_algebraMap_lt_one_iff (𝔭 := 𝔭)]⟩

/-- An absolute value lying over `FinitePlace.mk 𝔭` is equivalent to the finite place of its
prime. -/
private theorem isEquiv_primeOfLiesOver [w.LiesOver (FinitePlace.mk 𝔭).1] :
    (FinitePlace.mk (primeOfLiesOver 𝔭 w)).1.IsEquiv w := by
  set 𝔓 := primeOfLiesOver 𝔭 w
  have hle := apply_le_one_of_liesOver (w := w) (FinitePlace.mk 𝔭)
  refine isEquiv_of_lt_one_imp ?_ fun x hx ↦ ?_
  · obtain ⟨y, hy, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot 𝔓.ne_bot
    refine ⟨y, RingOfIntegers.coe_ne_zero_iff.mpr hy0, (FinitePlace.norm_lt_one_iff_mem F 𝔓 y).mpr
      hy |>.ne⟩
  -- Write `x = n / d` with `n, d` integers and `d` outside `𝔓`.
  obtain ⟨n, d, hnd⟩ := HeightOneSpectrum.exists_primeCompl_mul_eq_of_integer 𝔓 x
    ((FinitePlace.mk_apply_le_one_iff 𝔓 x).mp hx.le)
  have hd := (FinitePlace.norm_eq_one_iff_notMem F 𝔓 d).mpr d.prop
  have hn : n ∈ 𝔓.asIdeal := by
    rwa [← FinitePlace.norm_lt_one_iff_mem F, ← hnd, map_mul, norm_mul, hd, mul_one,
      ← FinitePlace.mk_apply, FinitePlace.coe_apply]
  have hwd : w (d : 𝓞 F) = 1 :=
    le_antisymm (hle d) (not_lt.mp fun h ↦ d.prop (mem_primeOfLiesOver.mpr h))
  calc w x = w (x * algebraMap (𝓞 F) F d) := by
        rw [map_mul, ← RingOfIntegers.coe_eq_algebraMap, hwd, mul_one]
    _ < 1 := by rw [hnd]; exact mem_primeOfLiesOver.mp hn

section RootOfFinitePlace

variable (K) (𝔓 : HeightOneSpectrum (𝓞 F))

/-- The product `e * f` of the ramification index and the inertia degree of `𝔓` over its
contraction to `𝓞 K` is positive. -/
private theorem ramificationIdx_mul_inertiaDeg_pos :
    0 < 𝔓.asIdeal.ramificationIdx (𝓞 K) * 𝔓.asIdeal.inertiaDeg (𝓞 K) :=
  mul_pos (𝔓.asIdeal.ramificationIdx_pos (𝓞 K)) (𝔓.asIdeal.inertiaDeg_pos (𝓞 K))

/-- The absolute value `y ↦ FinitePlace.mk 𝔓 y ^ (e * f)⁻¹` of `F`. -/
private noncomputable def rootOfFinitePlace : AbsoluteValue F ℝ :=
  (FinitePlace.mk 𝔓).1.nonarchRpow (FinitePlace.mk 𝔓).add_le
    (inv_pos.mpr (Nat.cast_pos.mpr (ramificationIdx_mul_inertiaDeg_pos K 𝔓)))

private theorem rootOfFinitePlace_apply (y : F) :
    rootOfFinitePlace K 𝔓 y = FinitePlace.mk 𝔓 y ^
      ((𝔓.asIdeal.ramificationIdx (𝓞 K) : ℝ) * 𝔓.asIdeal.inertiaDeg (𝓞 K))⁻¹ := by
  rw [← Nat.cast_mul]
  -- `FinitePlace.mk 𝔓 y` is `(FinitePlace.mk 𝔓).1 y` by definition, `FinitePlace.coe_apply`; a
  -- rewrite with it is not type correct here because `FinitePlace` is not reducible to a subtype.
  exact nonarchRpow_apply _ _ _ y

variable {K} in
/-- On `K`, the root of the finite place of a prime `𝔓` over `𝔭` agrees with the finite place of
`𝔭`. -/
private theorem rootOfFinitePlace_algebraMap [𝔓.asIdeal.LiesOver 𝔭.asIdeal] (x : K) :
    rootOfFinitePlace K 𝔓 (algebraMap K F x) = FinitePlace.mk 𝔭 x := by
  rw [rootOfFinitePlace_apply, ← Nat.cast_mul, FinitePlace.mk_apply_algebraMap 𝔭 𝔓,
    Real.pow_rpow_inv_natCast (by positivity) (ramificationIdx_mul_inertiaDeg_pos K 𝔓).ne']

variable {K} in
private theorem liesOver_rootOfFinitePlace [𝔓.asIdeal.LiesOver 𝔭.asIdeal] :
    (rootOfFinitePlace K 𝔓).LiesOver (FinitePlace.mk 𝔭).1 :=
  ⟨AbsoluteValue.ext fun x ↦ by
    rw [under_def, comp_apply, rootOfFinitePlace_algebraMap (𝔭 := 𝔭), FinitePlace.coe_apply]⟩

private theorem isEquiv_rootOfFinitePlace :
    (FinitePlace.mk 𝔓).1.IsEquiv (rootOfFinitePlace K 𝔓) :=
  isEquiv_nonarchRpow _ _ _

end RootOfFinitePlace

/-- An absolute value lying over `FinitePlace.mk 𝔭` is the root `FinitePlace.mk 𝔓 ^ (e * f)⁻¹` of
the finite place of its prime `𝔓`. -/
private theorem rootOfFinitePlace_primeOfLiesOver [w.LiesOver (FinitePlace.mk 𝔭).1] :
    rootOfFinitePlace K (primeOfLiesOver 𝔭 w) = w := by
  have := liesOver_primeOfLiesOver (𝔭 := 𝔭) (w := w)
  obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot 𝔭.ne_bot
  -- Both sides are equivalent, and they agree at the image of a nonzero element of `𝔭`.
  refine ((isEquiv_rootOfFinitePlace K _).symm.trans isEquiv_primeOfLiesOver).eq_of_apply_eq
    (x := algebraMap K F a) (by simpa using ha0) ?_ ?_
  · rw [rootOfFinitePlace_algebraMap (𝔭 := 𝔭), FinitePlace.mk_apply]
    exact ((FinitePlace.norm_lt_one_iff_mem K 𝔭 a).mpr ha).ne
  · rw [rootOfFinitePlace_algebraMap (𝔭 := 𝔭), LiesOver.apply_algebraMap (FinitePlace.mk 𝔭).1,
      FinitePlace.coe_apply]

/-- **Absolute values over a finite place.** Let `F / K` be a finite extension of number fields.
An absolute value `w` of `F` lying over the finite place `FinitePlace.mk 𝔭` of `K` is
`y ↦ FinitePlace.mk 𝔓 y ^ (e * f)⁻¹` for a unique prime `𝔓` of `𝓞 F` over `𝔭`, where `e` and `f`
are the ramification index and the inertia degree of `𝔓` over `𝔭`. -/
theorem existsUnique_finitePlace_rpow_inv_eq_of_liesOver [w.LiesOver (FinitePlace.mk 𝔭).1] :
    ∃! 𝔓 : HeightOneSpectrum (𝓞 F), 𝔓.asIdeal.LiesOver 𝔭.asIdeal ∧ ∀ y, w y =
      FinitePlace.mk 𝔓 y ^
        ((𝔓.asIdeal.ramificationIdx (𝓞 K) : ℝ) * 𝔓.asIdeal.inertiaDeg (𝓞 K))⁻¹ := by
  refine ⟨primeOfLiesOver 𝔭 w, ⟨liesOver_primeOfLiesOver, fun y ↦ ?_⟩, ?_⟩
  · rw [← rootOfFinitePlace_apply, rootOfFinitePlace_primeOfLiesOver]
  rintro 𝔔 ⟨-, h𝔔⟩
  have hw : rootOfFinitePlace K 𝔔 = rootOfFinitePlace K (primeOfLiesOver 𝔭 w) := by
    rw [rootOfFinitePlace_primeOfLiesOver]
    ext y
    rw [rootOfFinitePlace_apply, h𝔔]
  rw [← FinitePlace.mk_eq_iff, FinitePlace.eq_iff_isEquiv]
  exact (isEquiv_rootOfFinitePlace K 𝔔).trans (hw ▸ (isEquiv_rootOfFinitePlace K _).symm)

/-- **Absolute values over a finite place.** Let `F / K` be a finite extension of number fields.
An absolute value `w` of `F` lies over the finite place `FinitePlace.mk 𝔭` of `K` if and only if it
is `y ↦ FinitePlace.mk 𝔓 y ^ (e * f)⁻¹` for a prime `𝔓` of `𝓞 F` over `𝔭`, where `e` and `f` are
the ramification index and the inertia degree of `𝔓` over `𝔭`. -/
theorem liesOver_finitePlace_mk_iff :
    w.LiesOver (FinitePlace.mk 𝔭).1 ↔ ∃ 𝔓 : HeightOneSpectrum (𝓞 F),
      𝔓.asIdeal.LiesOver 𝔭.asIdeal ∧ ∀ y, w y = FinitePlace.mk 𝔓 y ^
        ((𝔓.asIdeal.ramificationIdx (𝓞 K) : ℝ) * 𝔓.asIdeal.inertiaDeg (𝓞 K))⁻¹ := by
  refine ⟨fun _ ↦ existsUnique_finitePlace_rpow_inv_eq_of_liesOver.exists, ?_⟩
  rintro ⟨𝔓, h𝔓, hw⟩
  obtain rfl : rootOfFinitePlace K 𝔓 = w := ext fun y ↦ by rw [rootOfFinitePlace_apply, hw]
  exact liesOver_rootOfFinitePlace 𝔓

/-- The integers at which an absolute value lying over `FinitePlace.mk 𝔭` is less than `1` form a
prime of `𝓞 F` lying over `𝔭`. -/
theorem exists_liesOver_forall_mem_iff_apply_lt_one [w.LiesOver (FinitePlace.mk 𝔭).1] :
    ∃ 𝔓 : HeightOneSpectrum (𝓞 F), 𝔓.asIdeal.LiesOver 𝔭.asIdeal ∧
      ∀ y : 𝓞 F, y ∈ 𝔓.asIdeal ↔ w y < 1 :=
  ⟨primeOfLiesOver 𝔭 w, liesOver_primeOfLiesOver, fun _ ↦ mem_primeOfLiesOver⟩

/-- An absolute value lying over `FinitePlace.mk 𝔭` is determined by the integers at which it is
less than `1`. -/
theorem eq_of_liesOver_of_forall_apply_lt_one_iff {w' : AbsoluteValue F ℝ}
    [w.LiesOver (FinitePlace.mk 𝔭).1] [w'.LiesOver (FinitePlace.mk 𝔭).1]
    (h : ∀ y : 𝓞 F, w y < 1 ↔ w' y < 1) : w = w' := by
  have : primeOfLiesOver 𝔭 w = primeOfLiesOver 𝔭 w' :=
    HeightOneSpectrum.ext (Ideal.ext fun y ↦ by rw [mem_primeOfLiesOver, mem_primeOfLiesOver, h])
  rw [← rootOfFinitePlace_primeOfLiesOver (𝔭 := 𝔭) (w := w),
    ← rootOfFinitePlace_primeOfLiesOver (𝔭 := 𝔭) (w := w'), this]

variable (w) in
/-- **Absolute values over a finite place.** Let `F / K` be a finite extension of number fields.
An absolute value `w` of `F` lying over a finite place `v` of `K` is `y ↦ FinitePlace.mk 𝔓 y ^ t`
for a prime `𝔓` of `𝓞 F` and an exponent `0 < t ≤ 1`, namely `t = (e * f)⁻¹` as in
`NumberField.existsUnique_finitePlace_rpow_inv_eq_of_liesOver`. -/
theorem exists_finitePlace_rpow_inv_eq_of_liesOver (v : FinitePlace K) [w.LiesOver v.1] :
    ∃ (𝔓 : HeightOneSpectrum (𝓞 F)) (t : ℝ), 0 < t ∧ t ≤ 1 ∧
      ∀ y, w y = FinitePlace.mk 𝔓 y ^ t := by
  obtain ⟨𝔭, rfl⟩ : ∃ 𝔭, FinitePlace.mk 𝔭 = v := ⟨_, v.mk_maximalIdeal⟩
  obtain ⟨𝔓, -, hw⟩ := (existsUnique_finitePlace_rpow_inv_eq_of_liesOver (𝔭 := 𝔭) (w := w)).exists
  have h : (1 : ℝ) ≤ 𝔓.asIdeal.ramificationIdx (𝓞 K) * 𝔓.asIdeal.inertiaDeg (𝓞 K) := by
    exact_mod_cast ramificationIdx_mul_inertiaDeg_pos K 𝔓
  exact ⟨𝔓, _, inv_pos.mpr (one_pos.trans_le h), inv_le_one_of_one_le₀ h, hw⟩

variable (F 𝔭)

/-- A finite extension of number fields has only finitely many absolute values lying over a given
finite place of the base. -/
theorem finite_setOf_liesOver_finitePlace_mk :
    {w : AbsoluteValue F ℝ | w.LiesOver (FinitePlace.mk 𝔭).1}.Finite := by
  refine (Set.finite_range fun 𝔓 : {𝔓 : HeightOneSpectrum (𝓞 F) // 𝔓.asIdeal.LiesOver 𝔭.asIdeal} ↦
    rootOfFinitePlace K 𝔓.1).subset fun w (hw : w.LiesOver _) ↦ ?_
  obtain ⟨𝔓, h𝔓, hw⟩ := liesOver_finitePlace_mk_iff.mp hw
  exact ⟨⟨𝔓, h𝔓⟩, ext fun y ↦ by rw [rootOfFinitePlace_apply, hw]⟩

/-- Every finite place of the base has an absolute value of a finite extension of number fields
lying over it. -/
theorem nonempty_setOf_liesOver_finitePlace_mk :
    {w : AbsoluteValue F ℝ | w.LiesOver (FinitePlace.mk 𝔭).1}.Nonempty := by
  obtain ⟨𝔓, rfl⟩ := HeightOneSpectrum.under_surjective (𝓞 K) (𝓞 F) 𝔭
  exact ⟨rootOfFinitePlace K 𝔓, liesOver_rootOfFinitePlace 𝔓⟩

end NumberField
