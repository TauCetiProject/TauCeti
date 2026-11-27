/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.OrderOfElement
public import TauCeti.Dynamics.ForwardOrbit

/-!
# Preperiodic points of a self-map

A point `x` is *preperiodic* for a self-map `f : α → α` when some iterate `f^[m] x` is a periodic
point of `f`, that is, `f^[m + n] x = f^[m] x` for some `m` and some `n ≥ 1`. Equivalently, its
forward orbit is finite. Points that are not preperiodic are called *wandering*. In arithmetic
dynamics, for a rational map of degree `d ≥ 2` defined over a number field `K`, the preperiodic
points are the points of canonical height zero, and Northcott's theorem shows that only finitely
many of them are `K`-rational.

## Main definitions

* `Function.IsPreperiodicPt f x`: some iterate of `x` under `f` is a periodic point of `f`.
* `Function.preperiodicPts f`: the set of preperiodic points of `f`.

## Main results

* `Function.isPreperiodicPt_iff_exists_iterate_add_eq`: `x` is preperiodic iff
  `f^[m + n] x = f^[m] x` for some `m` and some `n > 0`.
* `Function.isPreperiodicPt_iff_finite_forwardOrbit`: `x` is preperiodic iff its forward orbit is
  finite; `Function.isPreperiodicPt_iff_not_injective`: iff the iterates of `x` are not pairwise
  distinct.
* `Function.isPreperiodicPt_apply_iff`: preperiodicity is invariant along forward orbits.
* `Function.isPreperiodicPt_iterate_iff`: for `k > 0`, `x` is preperiodic for `f^[k]` iff it is
  preperiodic for `f`.
* `Function.Semiconj.isPreperiodicPt`: a semiconjugacy maps preperiodic points to preperiodic
  points; `Function.Semiconj.isPreperiodicPt_iff`: an injective one also reflects them.
* `Function.isPreperiodicPt_pow_iff_isOfFinOrder`: for `d ≥ 2`, the preperiodic points of
  `g ↦ g ^ d` on a left-cancellative monoid are its elements of finite order.

## References

* J. H. Silverman, *Lecture notes on arithmetic dynamics*, Arizona Winter School 2010, §§1–2
  (the finite-orbit characterisation, Exercise A on `g ↦ g ^ d` and Exercise D on conjugation).
* G. S. Call and J. H. Silverman, *Canonical heights on varieties with morphisms*,
  Compositio Math. 89 (1993), §1.
-/

public section

open Set

namespace Function

variable {α β : Type*} {f : α → α} {x : α} {k : ℕ}

/-- A point `x` is preperiodic for `f` when some iterate `f^[m] x` is a periodic point of `f`
(of positive period). -/
def IsPreperiodicPt (f : α → α) (x : α) : Prop :=
  ∃ m : ℕ, f^[m] x ∈ periodicPts f

/-- The set of preperiodic points of `f`. -/
def preperiodicPts (f : α → α) : Set α :=
  {x | IsPreperiodicPt f x}

theorem isPreperiodicPt_def : IsPreperiodicPt f x ↔ ∃ m : ℕ, f^[m] x ∈ periodicPts f :=
  Iff.rfl

@[simp]
theorem mem_preperiodicPts : x ∈ preperiodicPts f ↔ IsPreperiodicPt f x :=
  Iff.rfl

/-- `x` is preperiodic for `f` iff `f^[m + n] x = f^[m] x` for some `m` and some `n > 0`. -/
theorem isPreperiodicPt_iff_exists_iterate_add_eq :
    IsPreperiodicPt f x ↔ ∃ m n : ℕ, 0 < n ∧ f^[m + n] x = f^[m] x := by
  simp only [isPreperiodicPt_def, mem_periodicPts, IsPeriodicPt, IsFixedPt, ← iterate_add_apply,
    add_comm]

theorem IsPreperiodicPt.exists_iterate_add_eq (hx : IsPreperiodicPt f x) :
    ∃ m n : ℕ, 0 < n ∧ f^[m + n] x = f^[m] x :=
  isPreperiodicPt_iff_exists_iterate_add_eq.1 hx

theorem isPreperiodicPt_of_iterate_add_eq {m n : ℕ} (hn : 0 < n) (h : f^[m + n] x = f^[m] x) :
    IsPreperiodicPt f x :=
  isPreperiodicPt_iff_exists_iterate_add_eq.2 ⟨m, n, hn, h⟩

theorem isPreperiodicPt_of_mem_periodicPts (hx : x ∈ periodicPts f) : IsPreperiodicPt f x :=
  ⟨0, hx⟩

/-- A periodic point of positive period is preperiodic. -/
theorem IsPeriodicPt.isPreperiodicPt {n : ℕ} (hx : IsPeriodicPt f n x) (hn : 0 < n) :
    IsPreperiodicPt f x :=
  isPreperiodicPt_of_mem_periodicPts (mk_mem_periodicPts hn hx)

theorem IsFixedPt.isPreperiodicPt (hx : IsFixedPt f x) : IsPreperiodicPt f x :=
  (hx.isPeriodicPt 1).isPreperiodicPt one_pos

theorem periodicPts_subset_preperiodicPts (f : α → α) : periodicPts f ⊆ preperiodicPts f :=
  fun _ ↦ isPreperiodicPt_of_mem_periodicPts

/-- `f^[k] x` is preperiodic for `f` iff `x` is. -/
@[simp]
theorem isPreperiodicPt_apply_iterate_iff (k : ℕ) :
    IsPreperiodicPt f (f^[k] x) ↔ IsPreperiodicPt f x := by
  refine ⟨fun ⟨m, hm⟩ ↦ ⟨m + k, by rwa [iterate_add_apply]⟩, fun ⟨m, hm⟩ ↦ ⟨m, ?_⟩⟩
  obtain ⟨n, hn, hp⟩ := mem_periodicPts.1 hm
  rw [← iterate_add_apply, add_comm, iterate_add_apply]
  exact mk_mem_periodicPts hn (hp.apply_iterate k)

/-- `f x` is preperiodic for `f` iff `x` is. -/
@[simp]
theorem isPreperiodicPt_apply_iff : IsPreperiodicPt f (f x) ↔ IsPreperiodicPt f x :=
  isPreperiodicPt_apply_iterate_iff 1

theorem IsPreperiodicPt.apply_iterate (hx : IsPreperiodicPt f x) (k : ℕ) :
    IsPreperiodicPt f (f^[k] x) :=
  (isPreperiodicPt_apply_iterate_iff k).2 hx

theorem IsPreperiodicPt.apply (hx : IsPreperiodicPt f x) : IsPreperiodicPt f (f x) :=
  isPreperiodicPt_apply_iff.2 hx

@[simp]
theorem preimage_preperiodicPts (f : α → α) : f ⁻¹' preperiodicPts f = preperiodicPts f :=
  ext fun _ ↦ isPreperiodicPt_apply_iff

theorem mapsTo_preperiodicPts (f : α → α) : MapsTo f (preperiodicPts f) (preperiodicPts f) :=
  fun _ ↦ IsPreperiodicPt.apply

/-- `x` is preperiodic for `f` iff the iterates `f^[n] x` are not pairwise distinct. -/
theorem isPreperiodicPt_iff_not_injective :
    IsPreperiodicPt f x ↔ ¬Injective fun n : ℕ ↦ f^[n] x := by
  refine ⟨fun hx hinj ↦ ?_, fun hx ↦ ?_⟩
  · obtain ⟨m, n, hn, h⟩ := hx.exists_iterate_add_eq
    have := hinj h
    omega
  · obtain ⟨i, j, h, hij⟩ := not_injective_iff.1 hx
    rcases Nat.lt_or_gt_of_ne hij with hlt | hlt
    · exact isPreperiodicPt_of_iterate_add_eq (Nat.sub_pos_of_lt hlt)
        (by rw [Nat.add_sub_cancel' hlt.le]; exact h.symm)
    · exact isPreperiodicPt_of_iterate_add_eq (Nat.sub_pos_of_lt hlt)
        (by rw [Nat.add_sub_cancel' hlt.le]; exact h)

/-- **Preperiodic iff the forward orbit is finite.** -/
theorem isPreperiodicPt_iff_finite_forwardOrbit :
    IsPreperiodicPt f x ↔ (forwardOrbit f x).Finite := by
  refine ⟨fun hx ↦ ?_, fun hx ↦ ?_⟩
  · -- Past the preperiod `m`, the iterates repeat with period `n`.
    obtain ⟨m, hm⟩ := hx
    obtain ⟨n, hn, hp⟩ := mem_periodicPts.1 hm
    refine ((finite_Iio (m + n)).image fun k ↦ f^[k] x).subset fun y hy ↦ ?_
    obtain ⟨k, rfl⟩ := mem_forwardOrbit.1 hy
    rcases lt_or_ge k m with hk | hk
    · exact ⟨k, mem_Iio.2 (by omega), rfl⟩
    · refine ⟨(k - m) % n + m, mem_Iio.2 (by have := Nat.mod_lt (k - m) hn; omega), ?_⟩
      dsimp only
      rw [iterate_add_apply, hp.iterate_mod_apply, ← iterate_add_apply, Nat.sub_add_cancel hk]
  · obtain ⟨i, j, hij, h⟩ :=
      Finite.exists_lt_map_eq_of_forall_mem (iterate_mem_forwardOrbit f x) hx
    exact isPreperiodicPt_iff_not_injective.2 fun hinj ↦ hij.ne (hinj h)

theorem IsPreperiodicPt.finite_forwardOrbit (hx : IsPreperiodicPt f x) :
    (forwardOrbit f x).Finite :=
  isPreperiodicPt_iff_finite_forwardOrbit.1 hx

/-- On a finite type every point is preperiodic. -/
theorem isPreperiodicPt_of_finite [Finite α] (f : α → α) (x : α) : IsPreperiodicPt f x :=
  isPreperiodicPt_iff_finite_forwardOrbit.2 (toFinite _)

@[simp]
theorem preperiodicPts_eq_univ [Finite α] (f : α → α) : preperiodicPts f = univ :=
  eq_univ_of_forall (isPreperiodicPt_of_finite f)

@[simp]
theorem preperiodicPts_id : preperiodicPts (id : α → α) = univ :=
  eq_univ_of_forall fun x ↦ (isFixedPt_id x).isPreperiodicPt

/-- A preperiodic point of `f` is preperiodic for every iterate `f^[k]`. -/
theorem IsPreperiodicPt.iterate (hx : IsPreperiodicPt f x) (k : ℕ) : IsPreperiodicPt f^[k] x :=
  isPreperiodicPt_iff_finite_forwardOrbit.2
    (hx.finite_forwardOrbit.subset (forwardOrbit_iterate_subset f x k))

/-- For `k > 0`, `x` is preperiodic for `f^[k]` iff it is preperiodic for `f`. -/
theorem isPreperiodicPt_iterate_iff (hk : 0 < k) :
    IsPreperiodicPt f^[k] x ↔ IsPreperiodicPt f x := by
  refine ⟨fun hx ↦ ?_, fun hx ↦ hx.iterate k⟩
  rw [isPreperiodicPt_iff_not_injective] at hx ⊢
  refine fun hinj ↦ hx fun i j hij ↦ Nat.eq_of_mul_eq_mul_left hk (hinj ?_)
  simpa only [← iterate_mul] using hij

/-! ### Semiconjugacies -/

section Semiconj

variable {fa : α → α} {fb : β → β} {g : α → β}

/-- A semiconjugacy from `fa` to `fb` maps preperiodic points of `fa` to preperiodic points of
`fb`. -/
theorem Semiconj.isPreperiodicPt (h : Semiconj g fa fb) (hx : IsPreperiodicPt fa x) :
    IsPreperiodicPt fb (g x) := by
  rw [isPreperiodicPt_iff_finite_forwardOrbit, ← h.image_forwardOrbit]
  exact hx.finite_forwardOrbit.image g

/-- An injective semiconjugacy from `fa` to `fb` reflects preperiodic points: `g x` is
preperiodic for `fb` iff `x` is preperiodic for `fa`. -/
theorem Semiconj.isPreperiodicPt_iff (h : Semiconj g fa fb) (hg : Injective g) :
    IsPreperiodicPt fb (g x) ↔ IsPreperiodicPt fa x := by
  rw [isPreperiodicPt_iff_finite_forwardOrbit, isPreperiodicPt_iff_finite_forwardOrbit,
    ← h.image_forwardOrbit, finite_image_iff hg.injOn]

theorem Semiconj.mapsTo_preperiodicPts (h : Semiconj g fa fb) :
    MapsTo g (preperiodicPts fa) (preperiodicPts fb) :=
  fun _ ↦ h.isPreperiodicPt

theorem Semiconj.preimage_preperiodicPts (h : Semiconj g fa fb) (hg : Injective g) :
    g ⁻¹' preperiodicPts fb = preperiodicPts fa :=
  ext fun _ ↦ h.isPreperiodicPt_iff hg

/-- A bijective semiconjugacy (a conjugacy) from `fa` to `fb` maps the preperiodic points of `fa`
onto those of `fb`. -/
theorem Semiconj.image_preperiodicPts (h : Semiconj g fa fb) (hg : Bijective g) :
    g '' preperiodicPts fa = preperiodicPts fb := by
  rw [← h.preimage_preperiodicPts hg.1, image_preimage_eq _ hg.2]

end Semiconj

/-! ### The power map `g ↦ g ^ d` -/

/-- An element of finite order of a monoid is preperiodic for every power map `g ↦ g ^ d`: its
forward orbit lies in its finite set of powers. -/
theorem _root_.IsOfFinOrder.isPreperiodicPt_pow {G : Type*} [Monoid G] {g : G}
    (hg : IsOfFinOrder g) (d : ℕ) : IsPreperiodicPt (· ^ d) g := by
  refine isPreperiodicPt_iff_finite_forwardOrbit.2 (hg.finite_powers.subset fun y hy ↦ ?_)
  obtain ⟨n, rfl⟩ := mem_forwardOrbit.1 hy
  exact ⟨d ^ n, by simp⟩

/-- For `d ≥ 2`, the preperiodic points of the power map `g ↦ g ^ d` on a left-cancellative monoid
are exactly its elements of finite order. -/
theorem isPreperiodicPt_pow_iff_isOfFinOrder {G : Type*} [LeftCancelMonoid G] {d : ℕ}
    (hd : 1 < d) {g : G} : IsPreperiodicPt (· ^ d) g ↔ IsOfFinOrder g := by
  refine ⟨fun hg ↦ ?_, fun hg ↦ hg.isPreperiodicPt_pow d⟩
  obtain ⟨m, n, hn, h⟩ := hg.exists_iterate_add_eq
  -- `g ^ d ^ (m + n) = g ^ d ^ m` forces `d ^ (m + n) = d ^ m` unless `g` has finite order.
  simp only [pow_iterate] at h
  by_contra hfin
  have := Nat.pow_right_injective hd ((injective_pow_iff_not_isOfFinOrder.2 hfin) h)
  omega

end Function
