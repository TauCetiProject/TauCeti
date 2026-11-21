/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.RingTheory.FractionalIdeal.Operations
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.AlmostIntegral

/-!
# The `p`-root closure and the complete integral closure away from an element

Let `S` be an `R`-algebra and `p` a natural number. A subalgebra `A` of `S` is *`p`-root closed*
if `s ^ p ∈ A` forces `s ∈ A`, and the *`p`-root closure* `R^†_S` of `R` in `S` is the smallest
`p`-root closed subalgebra. For an element `g ∈ R`, the *complete integral closure away from `g`*
`R^*_S` consists of the `s ∈ S` with `g ^ m • s ^ n ∈ R` for one `m` and all `n`. For
`S = R[1/g]` these sit in the chain

```text
R ⊆ R^†_S ⊆ R^+_S ⊆ R^*_S ⊆ completeIntegralClosure R S,
```

where `R^+_S` is the integral closure, the second inclusion needs `p > 0` and the last needs `g`
to be a nonzerodivisor.
`R^*_S` is the set of elements whose powers lie in one finitely generated `R`-submodule of `S`,
which is André's complete integral closure; Mathlib's `completeIntegralClosure` allows any
nonzerodivisor of `R` as multiplier.

For `p > 1`, if `t = t 0 ∈ R` carries compatible `p`-power roots `t (k + 1) ^ p = t k`, the *root
saturation* of a subalgebra `A` is `t^{-1/p^∞}A = {s | t k • s ∈ A for every k}`. For a `p`-root
closed `A` the root saturation is the complete integral closure of `A` away from `t`; in general
`R^*_S ⊆ t^{-1/p^∞}R^†_S`, with equality as soon as `t ^ N` maps `R^†_S` into `R`. Neither
statement needs `t` to be a nonzerodivisor or `S` to be a localisation.

These closures are the ring-theoretic input of André's dictionary between uniform Banach algebras
and their unit balls, where `p`-root closedness, integral closedness and complete integral
closedness of the unit ball are compared, and of the root saturation `g^{-1/p^∞}B°` of the unit ball
of such an algebra.

## Main definitions

* `Subalgebra.IsPRootClosed`: a subalgebra is `p`-root closed.
* `TauCeti.pRootClosure p R S`: the `p`-root closure of `R` in `S`.
* `TauCeti.awayCompleteIntegralClosure g S`: the complete integral closure of `R` in `S` away
  from `g`.
* `Subalgebra.rootSaturation`: the root saturation of a subalgebra along compatible roots.

## Main results

* `TauCeti.pRootClosure_eq_perfectClosure`: in characteristic `p` the `p`-root closure consists of
  the `s` with `s ^ p ^ n ∈ R` for some `n`.
* `TauCeti.pRootClosure_le_integralClosure`,
  `TauCeti.integralClosure_le_awayCompleteIntegralClosure` and
  `TauCeti.awayCompleteIntegralClosure_le_completeIntegralClosure`: the chain of inclusions.
* `TauCeti.mem_awayCompleteIntegralClosure_iff_exists_fg`: over `S = R[1/g]`, membership in the
  complete integral closure away from `g` means that all powers lie in one finitely generated
  submodule.
* `TauCeti.map_pRootClosure_le` and `TauCeti.map_awayCompleteIntegralClosure_le`: functoriality
  along commutative squares.
* `Subalgebra.IsPRootClosed.restrictScalars_awayCompleteIntegralClosure_eq_rootSaturation`: a
  `p`-root closed subalgebra has the root saturation as its complete integral closure away from `t`.
* `TauCeti.awayCompleteIntegralClosure_le_rootSaturation_pRootClosure` and
  `TauCeti.awayCompleteIntegralClosure_eq_rootSaturation_pRootClosure`: `R^*_S ⊆ t^{-1/p^∞}R^†_S`,
  with equality when `R^†_S ⊆ t^{-N}R`.

## References

* Y. André, *Le lemme d'Abhyankar perfectoïde*, Publ. Math. IHÉS 127 (2018), §2.3.1 (p. 15),
  §2.5.5 and Remarque 2.5.6 (pp. 26–27).
* The proof of `TauCeti.awayCompleteIntegralClosure` being a subalgebra follows Mathlib's
  `completeIntegralClosure`.
-/

public section

open scoped nonZeroDivisors

/-! ### `p`-root closed subalgebras -/

namespace Subalgebra

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] {p : ℕ}

/-- A subalgebra `A` of `S` is `p`-root closed in `S` if `s ^ p ∈ A` implies `s ∈ A`
(André, *Le lemme d'Abhyankar perfectoïde*, §2.3.1). -/
def IsPRootClosed (A : Subalgebra R S) (p : ℕ) : Prop :=
  ∀ ⦃s : S⦄, s ^ p ∈ A → s ∈ A

/-- Unfolding `IsPRootClosed`. -/
theorem isPRootClosed_iff {A : Subalgebra R S} :
    A.IsPRootClosed p ↔ ∀ s : S, s ^ p ∈ A → s ∈ A :=
  Iff.rfl

/-- A `p`-root closed subalgebra contains every `p`-th root of its elements. -/
theorem IsPRootClosed.mem_of_pow_mem {A : Subalgebra R S} (hA : A.IsPRootClosed p) {s : S}
    (hs : s ^ p ∈ A) : s ∈ A :=
  hA hs

/-- A `p`-root closed subalgebra contains every `p ^ n`-th root of its elements. -/
theorem IsPRootClosed.mem_of_pow_pow_mem {A : Subalgebra R S} (hA : A.IsPRootClosed p) {s : S}
    {n : ℕ} (hs : s ^ p ^ n ∈ A) : s ∈ A := by
  induction n generalizing s with
  | zero => simpa using hs
  | succ n ih => exact hA (ih (by rwa [← pow_mul, ← pow_succ']))

/-- The whole algebra is `p`-root closed. -/
theorem isPRootClosed_top : (⊤ : Subalgebra R S).IsPRootClosed p :=
  fun _ _ ↦ Algebra.mem_top

/-- An intersection of `p`-root closed subalgebras is `p`-root closed. -/
theorem isPRootClosed_sInf {𝒜 : Set (Subalgebra R S)} (h𝒜 : ∀ A ∈ 𝒜, A.IsPRootClosed p) :
    (sInf 𝒜).IsPRootClosed p := fun _ hs ↦
  Algebra.mem_sInf.mpr fun A hA ↦ h𝒜 A hA (Algebra.mem_sInf.mp hs A hA)

/-- An indexed intersection of `p`-root closed subalgebras is `p`-root closed. -/
theorem isPRootClosed_iInf {ι : Sort*} {A : ι → Subalgebra R S}
    (hA : ∀ i, (A i).IsPRootClosed p) : (⨅ i, A i).IsPRootClosed p := fun _ hs ↦
  Algebra.mem_iInf.mpr fun i ↦ hA i (Algebra.mem_iInf.mp hs i)

/-- The intersection of two `p`-root closed subalgebras is `p`-root closed. -/
theorem IsPRootClosed.inf {A B : Subalgebra R S} (hA : A.IsPRootClosed p)
    (hB : B.IsPRootClosed p) : (A ⊓ B).IsPRootClosed p := fun _ hs ↦
  ⟨hA hs.1, hB hs.2⟩

/-- The preimage of a `p`-root closed subalgebra is `p`-root closed. -/
theorem IsPRootClosed.comap {T : Type*} [CommRing T] [Algebra R T] {A : Subalgebra R S}
    (hA : A.IsPRootClosed p) (f : T →ₐ[R] S) : (A.comap f).IsPRootClosed p := fun s hs ↦ by
  rw [mem_comap, map_pow] at hs
  exact hA hs

/-- Restricting scalars does not change `p`-root closedness. -/
@[simp]
theorem isPRootClosed_restrictScalars {R' : Type*} [CommRing R'] [Algebra R R'] [Algebra R' S]
    [IsScalarTower R R' S] {A : Subalgebra R' S} :
    (A.restrictScalars R).IsPRootClosed p ↔ A.IsPRootClosed p :=
  Iff.rfl

/-- For `p > 0` the integral closure is `p`-root closed. -/
theorem isPRootClosed_integralClosure (hp : 0 < p) : (integralClosure R S).IsPRootClosed p :=
  fun _ hs ↦ IsIntegral.of_pow hp hs

end Subalgebra

/-! ### The `p`-root closure -/

namespace TauCeti

open Subalgebra

section PRootClosure

variable (p : ℕ) (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]

/-- The `p`-root closure `R^†_S` of `R` in `S`: the smallest `p`-root closed subalgebra of `S`
(André, *Le lemme d'Abhyankar perfectoïde*, §2.3.1). -/
def pRootClosure : Subalgebra R S :=
  sInf {A | A.IsPRootClosed p}

variable {p R S}

/-- The `p`-root closure is `p`-root closed. -/
theorem isPRootClosed_pRootClosure : (pRootClosure p R S).IsPRootClosed p :=
  isPRootClosed_sInf fun _ hA ↦ hA

/-- The `p`-root closure lies in every `p`-root closed subalgebra. -/
theorem pRootClosure_le {A : Subalgebra R S} (hA : A.IsPRootClosed p) : pRootClosure p R S ≤ A :=
  sInf_le hA

/-- `R` is `p`-root closed in `S` iff it equals its `p`-root closure. -/
theorem pRootClosure_eq_bot_iff :
    pRootClosure p R S = ⊥ ↔ (⊥ : Subalgebra R S).IsPRootClosed p :=
  ⟨fun h ↦ h ▸ isPRootClosed_pRootClosure, fun h ↦ le_bot_iff.mp (pRootClosure_le h)⟩

/-- A `p`-radicial element, one with `s ^ p ^ n ∈ R` for some `n`, lies in the `p`-root
closure. -/
theorem mem_pRootClosure_of_pow_pow_mem {s : S} {n : ℕ}
    (hs : s ^ p ^ n ∈ (algebraMap R S).range) : s ∈ pRootClosure p R S := by
  obtain ⟨r, hr⟩ := hs
  exact isPRootClosed_pRootClosure.mem_of_pow_pow_mem (hr ▸ algebraMap_mem _ r)

/-- In characteristic `p`, the `p`-radicial elements form a `p`-root closed subalgebra, so they
are the `p`-root closure. -/
theorem pRootClosure_eq_perfectClosure [ExpChar S p] :
    pRootClosure p R S = Subalgebra.perfectClosure R S p := by
  refine le_antisymm (pRootClosure_le fun s hs ↦ ?_) fun s hs ↦ ?_
  · obtain ⟨n, hn⟩ := (Subalgebra.mem_perfectClosure_iff).mp hs
    exact (Subalgebra.mem_perfectClosure_iff).mpr ⟨n + 1, by rwa [pow_succ', pow_mul]⟩
  · obtain ⟨n, r, hr⟩ := (Subalgebra.mem_perfectClosure_iff).mp hs
    exact mem_pRootClosure_of_pow_pow_mem ⟨r, hr⟩

/-- In characteristic `p`, `s` lies in the `p`-root closure iff `s ^ p ^ n ∈ R` for some `n`. -/
theorem mem_pRootClosure_iff_of_expChar [ExpChar S p] {s : S} :
    s ∈ pRootClosure p R S ↔ ∃ n : ℕ, s ^ p ^ n ∈ (algebraMap R S).range := by
  rw [pRootClosure_eq_perfectClosure]
  exact Subalgebra.mem_perfectClosure_iff

/-- For `p > 0` the `p`-root closure lies in the integral closure. -/
theorem pRootClosure_le_integralClosure (hp : 0 < p) : pRootClosure p R S ≤ integralClosure R S :=
  pRootClosure_le (isPRootClosed_integralClosure hp)

/-- A commutative square of rings `R → R'`, `S → S'` maps the `p`-root closure of `R` in `S` into
that of `R'` in `S'`. -/
theorem map_pRootClosure_le {R' S' : Type*} [CommRing R'] [CommRing S'] [Algebra R R']
    [Algebra R' S'] [Algebra R S'] [IsScalarTower R R' S'] (f : S →ₐ[R] S') :
    (pRootClosure p R S).map f ≤ (pRootClosure p R' S').restrictScalars R :=
  Subalgebra.map_le.mpr <| pRootClosure_le <|
    (isPRootClosed_restrictScalars.mpr isPRootClosed_pRootClosure).comap f

end PRootClosure

/-! ### The complete integral closure away from an element -/

section AwayCompleteIntegralClosure

variable {R : Type*} [CommRing R] (g : R) (S : Type*) [CommRing S] [Algebra R S]

/-- The complete integral closure `R^*_S` of `R` in `S` away from `g`: the elements `s` with
`g ^ m • s ^ n ∈ R` for one `m` and every `n`. For `S = R[1/g]` these are the elements whose powers
lie in one finitely generated `R`-submodule (`mem_awayCompleteIntegralClosure_iff_exists_fg`),
the complete integral closure of André, *Le lemme d'Abhyankar perfectoïde*, §2.5.5. -/
def awayCompleteIntegralClosure : Subalgebra R S where
  carrier := {s | ∃ m : ℕ, ∀ n : ℕ, g ^ m • s ^ n ∈ (algebraMap R S).range}
  mul_mem' := by
    rintro a b ⟨m, hm⟩ ⟨m', hm'⟩
    refine ⟨m + m', fun n ↦ ?_⟩
    rw [mul_pow, pow_add, mul_smul_mul_comm]
    exact mul_mem (hm n) (hm' n)
  add_mem' := by
    rintro a b ⟨m, hm⟩ ⟨m', hm'⟩
    refine ⟨m + m', fun n ↦ ?_⟩
    simp only [add_pow, Finset.smul_sum, pow_add, ← smul_mul_assoc _ (_ * _),
      ← smul_mul_smul_comm _ (a ^ _)]
    exact sum_mem fun i _ ↦ mul_mem (mul_mem (hm _) (hm' _)) (by simp)
  algebraMap_mem' r := ⟨0, fun n ↦ by simp [← map_pow]⟩

variable {g S}

/-- Unfolding `awayCompleteIntegralClosure`. -/
theorem mem_awayCompleteIntegralClosure {s : S} :
    s ∈ awayCompleteIntegralClosure g S ↔
      ∃ m : ℕ, ∀ n : ℕ, g ^ m • s ^ n ∈ (algebraMap R S).range :=
  Iff.rfl

/-- For a nonzerodivisor `g`, the complete integral closure away from `g` lies in Mathlib's
complete integral closure, whose multipliers are all nonzerodivisors. -/
theorem awayCompleteIntegralClosure_le_completeIntegralClosure (hg : g ∈ R⁰) :
    awayCompleteIntegralClosure g S ≤ completeIntegralClosure R S :=
  fun _ ⟨m, hm⟩ ↦ ⟨g ^ m, pow_mem hg m, hm⟩

/-- Over `S = R[1/g]`, an element lies in the complete integral closure away from `g` iff its
powers lie in one finitely generated `R`-submodule of `S`. -/
theorem mem_awayCompleteIntegralClosure_iff_exists_fg [IsLocalization.Away g S] {s : S} :
    s ∈ awayCompleteIntegralClosure g S ↔ ∃ M : Submodule R S, M.FG ∧ ∀ n : ℕ, s ^ n ∈ M := by
  refine ⟨fun ⟨m, hm⟩ ↦ ?_, fun ⟨M, hM, hsM⟩ ↦ ?_⟩
  · refine ⟨Submodule.span R {IsLocalization.Away.invSelf g ^ m},
      Submodule.fg_span_singleton _, fun n ↦ ?_⟩
    obtain ⟨r, hr⟩ := hm n
    refine Submodule.mem_span_singleton.mpr ⟨r, ?_⟩
    simp [Algebra.smul_def, hr, mul_right_comm _ (s ^ n), ← mul_pow,
      IsLocalization.Away.mul_invSelf]
  · obtain ⟨a, ⟨m, rfl⟩, ha⟩ := FractionalIdeal.isFractional_of_fg (S := Submonoid.powers g) hM
    exact ⟨m, fun n ↦ ha _ (hsM n)⟩

/-- Over `S = R[1/g]`, the integral closure lies in the complete integral closure away from `g`:
the powers of an integral element lie in the finitely generated module it generates. -/
theorem integralClosure_le_awayCompleteIntegralClosure [IsLocalization.Away g S] :
    integralClosure R S ≤ awayCompleteIntegralClosure g S := fun s hs ↦
  mem_awayCompleteIntegralClosure_iff_exists_fg.mpr ⟨_, hs.fg_adjoin_singleton,
    fun n ↦ pow_mem (Algebra.self_mem_adjoin_singleton R s) n⟩

/-- Over `S = R[1/g]` and for `p > 0`, the `p`-root closure lies in the complete integral closure
away from `g`. -/
theorem pRootClosure_le_awayCompleteIntegralClosure [IsLocalization.Away g S] {p : ℕ}
    (hp : 0 < p) : pRootClosure p R S ≤ awayCompleteIntegralClosure g S :=
  (pRootClosure_le_integralClosure hp).trans integralClosure_le_awayCompleteIntegralClosure

/-- A commutative square of rings `R → R'`, `S → S'` maps the complete integral closure of `R` in
`S` away from `g` into that of `R'` in `S'` away from the image of `g`. -/
theorem map_awayCompleteIntegralClosure_le {R' S' : Type*} [CommRing R'] [CommRing S']
    [Algebra R R'] [Algebra R' S'] [Algebra R S'] [IsScalarTower R R' S'] (f : S →ₐ[R] S') :
    (awayCompleteIntegralClosure g S).map f ≤
      (awayCompleteIntegralClosure (algebraMap R R' g) S').restrictScalars R := by
  intro x hx
  obtain ⟨s, ⟨m, hm⟩, rfl⟩ := Subalgebra.mem_map.mp hx
  refine ⟨m, fun n ↦ ?_⟩
  obtain ⟨r, hr⟩ := hm n
  refine ⟨algebraMap R R' r, ?_⟩
  rw [← IsScalarTower.algebraMap_apply, ← map_pow, algebraMap_smul, ← f.commutes, hr]
  simp

end AwayCompleteIntegralClosure

end TauCeti

/-! ### Root saturation -/

namespace TauCeti

/-- For compatible `p`-power roots `t (k + 1) ^ p = t k`, the root `t (j + k)` is a `p ^ k`-th
root of `t j`. -/
theorem pow_pow_of_succ_pow_eq {M : Type*} [Monoid M] {p : ℕ} {t : ℕ → M}
    (ht : ∀ k, t (k + 1) ^ p = t k) (j k : ℕ) : t (j + k) ^ p ^ k = t j := by
  induction k with
  | zero => simp
  | succ k ih => rw [← ih, ← add_assoc, ← ht (j + k), ← pow_mul, pow_succ']

end TauCeti

namespace Subalgebra

open TauCeti

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] {p : ℕ} {t : ℕ → R}

/-- If `t k * s ∈ A` for every root `t k` of `t 0`, then `t 0 * s ^ n ∈ A` for every `n`. -/
theorem algebraMap_mul_pow_mem_of_forall_algebraMap_mul_mem (hp : 1 < p)
    (ht : ∀ k, t (k + 1) ^ p = t k) {A : Subalgebra R S} {s : S}
    (hs : ∀ k, algebraMap R S (t k) * s ∈ A) (n : ℕ) : algebraMap R S (t 0) * s ^ n ∈ A := by
  have hle : n ≤ p ^ n := (Nat.lt_pow_self hp).le
  rw [← pow_pow_of_succ_pow_eq ht 0 n, zero_add, map_pow, ← Nat.sub_add_cancel hle, pow_add,
    mul_assoc, ← mul_pow]
  exact mul_mem (pow_mem (algebraMap_mem A _) _) (pow_mem (hs n) n)

/-- If `A` is `p`-root closed and `t 0 ^ m * s ^ n ∈ A` for every `n`, then `t k * s ∈ A` for
every root `t k` of `t 0`. -/
theorem IsPRootClosed.algebraMap_mul_mem_of_forall_pow_mul_pow_mem (hp : 1 < p)
    (ht : ∀ k, t (k + 1) ^ p = t k) {A : Subalgebra R S} (hA : A.IsPRootClosed p) {s : S}
    {m : ℕ} (hs : ∀ n, algebraMap R S (t 0) ^ m * s ^ n ∈ A) (k : ℕ) :
    algebraMap R S (t k) * s ∈ A := by
  -- `t (k + m) ^ m • s` has `p ^ (k + m)`-th power `t 0 ^ m • s ^ p ^ (k + m)`
  have hroot : algebraMap R S (t (k + m)) ^ m * s ∈ A := by
    refine hA.mem_of_pow_pow_mem (n := k + m) ?_
    have h0 := congrArg (algebraMap R S) (pow_pow_of_succ_pow_eq ht 0 (k + m))
    rw [zero_add, map_pow] at h0
    rw [mul_pow, ← pow_mul, mul_comm m, pow_mul, h0]
    exact hs _
  -- and `t k = t (k + m) ^ p ^ m` with `m ≤ p ^ m`
  have hle : m ≤ p ^ m := (Nat.lt_pow_self hp).le
  rw [← pow_pow_of_succ_pow_eq ht k m, map_pow, ← Nat.sub_add_cancel hle, pow_add, mul_assoc]
  exact mul_mem (pow_mem (algebraMap_mem A _) _) hroot

/-- The root saturation `t^{-1/p^∞}A = {s | t k • s ∈ A for every k}` of a subalgebra `A` along
compatible `p`-power roots `t (k + 1) ^ p = t k`, where `t k • s` is `algebraMap R S (t k) * s`
(André, *Le lemme d'Abhyankar perfectoïde*, §2.5.2). It is closed under products because
`p ≥ 2`. -/
def rootSaturation (A : Subalgebra R S) (hp : 1 < p) (ht : ∀ k, t (k + 1) ^ p = t k) :
    Subalgebra R S where
  carrier := {s | ∀ k, algebraMap R S (t k) * s ∈ A}
  mul_mem' {a b} ha hb k := by
    -- `t k = t (k + 1) ^ q * t (k + 1) * t (k + 1)` where `p = q + 2`
    obtain ⟨q, rfl⟩ : ∃ q, p = q + 2 := ⟨p - 2, by omega⟩
    have h : algebraMap R S (t k) * (a * b) = algebraMap R S (t (k + 1)) ^ q *
        (algebraMap R S (t (k + 1)) * a) * (algebraMap R S (t (k + 1)) * b) := by
      rw [← ht k, map_pow]
      ring
    rw [h]
    exact mul_mem (mul_mem (pow_mem (algebraMap_mem A _) _) (ha _)) (hb _)
  add_mem' ha hb k := by
    rw [mul_add]
    exact add_mem (ha k) (hb k)
  algebraMap_mem' r k := by
    rw [← map_mul]
    exact algebraMap_mem A _

@[simp]
theorem mem_rootSaturation {A : Subalgebra R S} {hp : 1 < p} {ht : ∀ k, t (k + 1) ^ p = t k}
    {s : S} : s ∈ A.rootSaturation hp ht ↔ ∀ k, algebraMap R S (t k) * s ∈ A :=
  Iff.rfl

/-- A subalgebra lies in its root saturation. -/
theorem le_rootSaturation (A : Subalgebra R S) (hp : 1 < p) (ht : ∀ k, t (k + 1) ^ p = t k) :
    A ≤ A.rootSaturation hp ht :=
  fun _ hs _ ↦ mul_mem (algebraMap_mem A _) hs

/-- Root saturation is monotone. -/
theorem rootSaturation_mono {A B : Subalgebra R S} (hAB : A ≤ B) (hp : 1 < p)
    (ht : ∀ k, t (k + 1) ^ p = t k) : A.rootSaturation hp ht ≤ B.rootSaturation hp ht :=
  fun _ hs k ↦ hAB (hs k)

/-- The root saturation of a `p`-root closed subalgebra `A` is the complete integral closure of
`A` away from `t 0`. -/
theorem IsPRootClosed.restrictScalars_awayCompleteIntegralClosure_eq_rootSaturation (hp : 1 < p)
    (ht : ∀ k, t (k + 1) ^ p = t k) {A : Subalgebra R S} (hA : A.IsPRootClosed p) :
    (TauCeti.awayCompleteIntegralClosure (algebraMap R A (t 0)) S).restrictScalars R =
      A.rootSaturation hp ht := by
  ext s
  simp only [mem_restrictScalars, TauCeti.mem_awayCompleteIntegralClosure,
    range_algebraMap, mem_toSubring, smul_def, SubmonoidClass.coe_pow,
    SubalgebraClass.coe_algebraMap, smul_eq_mul, mem_rootSaturation]
  refine ⟨fun ⟨_, hm⟩ ↦ hA.algebraMap_mul_mem_of_forall_pow_mul_pow_mem hp ht hm,
    fun h ↦ ⟨1, fun n ↦ ?_⟩⟩
  rw [pow_one]
  exact algebraMap_mul_pow_mem_of_forall_algebraMap_mul_mem hp ht h n

end Subalgebra

namespace TauCeti

open Subalgebra

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] {p : ℕ} {t : ℕ → R}

/-- The complete integral closure of `R` in `S` away from `t 0` lies in the root saturation of the
`p`-root closure: `R^*_S ⊆ t^{-1/p^∞}R^†_S` (André, *Le lemme d'Abhyankar perfectoïde*,
Remarque 2.5.6). -/
theorem awayCompleteIntegralClosure_le_rootSaturation_pRootClosure (hp : 1 < p)
    (ht : ∀ k, t (k + 1) ^ p = t k) :
    awayCompleteIntegralClosure (t 0) S ≤ (pRootClosure p R S).rootSaturation hp ht := by
  rintro s ⟨m, hm⟩
  refine mem_rootSaturation.mpr <|
    isPRootClosed_pRootClosure.algebraMap_mul_mem_of_forall_pow_mul_pow_mem hp ht (m := m)
      fun n ↦ ?_
  obtain ⟨r, hr⟩ := hm n
  rw [← map_pow, ← Algebra.smul_def, ← hr]
  exact algebraMap_mem _ r

/-- If `t 0 ^ N` maps the `p`-root closure into `R`, the complete integral closure of `R` in `S`
away from `t 0` is the root saturation of the `p`-root closure: `R^*_S = t^{-1/p^∞}R^†_S`. -/
theorem awayCompleteIntegralClosure_eq_rootSaturation_pRootClosure (hp : 1 < p)
    (ht : ∀ k, t (k + 1) ^ p = t k) {N : ℕ}
    (hN : ∀ a ∈ pRootClosure p R S, t 0 ^ N • a ∈ (algebraMap R S).range) :
    awayCompleteIntegralClosure (t 0) S = (pRootClosure p R S).rootSaturation hp ht := by
  refine le_antisymm (awayCompleteIntegralClosure_le_rootSaturation_pRootClosure hp ht) fun s hs ↦
    ⟨N + 1, fun n ↦ ?_⟩
  rw [pow_succ, mul_smul, Algebra.smul_def (t 0)]
  exact hN _ (algebraMap_mul_pow_mem_of_forall_algebraMap_mul_mem hp ht hs n)

/-- If `R` is `p`-root closed in `S`, the complete integral closure of `R` in `S` away from `t 0`
is the root saturation of `R`. -/
theorem awayCompleteIntegralClosure_eq_rootSaturation_bot (hp : 1 < p)
    (ht : ∀ k, t (k + 1) ^ p = t k) (hR : (⊥ : Subalgebra R S).IsPRootClosed p) :
    awayCompleteIntegralClosure (t 0) S = (⊥ : Subalgebra R S).rootSaturation hp ht := by
  have h := pRootClosure_eq_bot_iff.mpr hR
  rw [← h]
  refine awayCompleteIntegralClosure_eq_rootSaturation_pRootClosure hp ht (N := 0) fun a ha ↦ ?_
  rw [h] at ha
  obtain ⟨r, rfl⟩ := Algebra.mem_bot.mp ha
  rw [pow_zero, one_smul]
  exact ⟨r, rfl⟩

end TauCeti
