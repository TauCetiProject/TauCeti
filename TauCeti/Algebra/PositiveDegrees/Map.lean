/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.PositiveDegrees.Basic
public import Mathlib.Algebra.Group.Submonoid.Operations
public import Mathlib.Order.PartialSups

/-!
# Maps of positive degree data

A `PositiveDegreeMap` is an additive map preserving allowed and nonzero degrees,
with a monotone cutoff modulus. The modulus bounds source degrees of elements
whose images survive a target cutoff; this is the direction needed to induce
maps on graded truncations and their inverse limits.

Identity maps have identity modulus, and successive moduli compose in reverse
order to the underlying maps. We construct maps from arbitrary cutoff bounds,
linear degree bounds and injectivity on the allowed monoid.
In the last case, the modulus is the maximum source degree over the inverse
image of a target cutoff. In particular, changing the positive degree function
on a fixed monoid admits cutoff bounds in both directions.

Adapted from `Mei/Algebra/PositiveDegrees/Map.lean` in
[yuma-mizuno-lean/Mei](https://github.com/yuma-mizuno-lean/Mei), commit
`7f1e4c7714fb020473694755ad8748c8f15d0e7f`, released under Apache 2.0.
-/

public section

namespace TauCeti

variable {N M L K : Type*} [AddCommMonoid N] [AddCommMonoid M]
  [AddCommMonoid L] [AddCommMonoid K]

/-- An additive map of positive degree data, together with a monotone cutoff modulus.
The modulus is part of the data, so two maps with different moduli need not be equal. -/
structure PositiveDegreeMap (d : PositiveDegrees N) (e : PositiveDegrees M) where
  /-- The underlying additive map. -/
  toAddMonoidHom : N →+ M
  /-- Allowed degrees map to allowed degrees. -/
  map_mem : ∀ {n}, n ∈ d.monoid → toAddMonoidHom n ∈ e.monoid
  /-- Nonzero allowed degrees have nonzero images. -/
  map_ne_zero : ∀ {n}, n ∈ d.monoid → n ≠ 0 → toAddMonoidHom n ≠ 0
  /-- Source cutoff needed to compute a target cutoff. -/
  modulus : ℕ → ℕ
  /-- Increasing the target cutoff cannot decrease the required source cutoff. -/
  monotone_modulus : Monotone modulus
  /-- Degrees beyond the source cutoff map beyond the target cutoff. -/
  degree_gt : ∀ {n} (k : ℕ), n ∈ d.monoid →
    (modulus k : ℤ) < d.degree n → (k : ℤ) < e.degree (toAddMonoidHom n)

namespace PositiveDegreeMap

variable {d : PositiveDegrees N} {e : PositiveDegrees M}
  {f : PositiveDegrees L} {g : PositiveDegrees K}

instance : CoeFun (PositiveDegreeMap d e) (fun _ => N → M) where
  coe T := T.toAddMonoidHom

@[simp]
theorem map_zero (T : PositiveDegreeMap d e) : T 0 = 0 := T.toAddMonoidHom.map_zero

@[simp]
theorem map_add (T : PositiveDegreeMap d e) (a b : N) :
    T (a + b) = T a + T b := T.toAddMonoidHom.map_add a b

/-- The image of the source positive monoid lies in the target positive monoid. -/
theorem map_monoid_le (T : PositiveDegreeMap d e) : d.monoid.map T.toAddMonoidHom ≤ e.monoid :=
  AddSubmonoid.map_le_iff_le_comap.mpr fun _ => T.map_mem

/-- A positive degree map is determined by its additive map and its cutoff modulus. -/
@[ext]
theorem ext {T U : PositiveDegreeMap d e} (h : ∀ n, T n = U n)
    (hmod : ∀ k, T.modulus k = U.modulus k) : T = U := by
  have hh : T.toAddMonoidHom = U.toAddMonoidHom := AddMonoidHom.ext h
  have hm : T.modulus = U.modulus := funext hmod
  cases T
  cases U
  cases hh
  cases hm
  rfl

/-- An image surviving order `k` comes from the source cutoff given by the modulus. -/
theorem degree_le (T : PositiveDegreeMap d e) {n : N} (k : ℕ)
    (hn : n ∈ d.monoid) (h : e.degree (T n) ≤ k) :
    d.degree n ≤ T.modulus k := by
  have := T.degree_gt k hn
  by_contra hle
  exact (not_lt_of_ge h) (this (lt_of_not_ge hle))

/-- The inverse image of a target cutoff lies in the prescribed source cutoff. -/
theorem preimage_cutoff_subset (T : PositiveDegreeMap d e) (k : ℕ) :
    (d.monoid : Set N) ∩ T ⁻¹' e.cutoff k ⊆ d.cutoff (T.modulus k) := by
  rintro n ⟨hn, h⟩
  exact (d.mem_cutoff).mpr
    ⟨hn, T.degree_le k hn ((e.mem_cutoff).mp h).2⟩

/-- Identity map, with the identity cutoff modulus. -/
def id (d : PositiveDegrees N) : PositiveDegreeMap d d where
  toAddMonoidHom := AddMonoidHom.id N
  map_mem h := h
  map_ne_zero _ h := h
  modulus := _root_.id
  monotone_modulus := monotone_id
  degree_gt _ _ h := h

@[simp]
theorem id_apply (n : N) : id d n = n := (rfl)

@[simp]
theorem id_modulus (k : ℕ) : (id d).modulus k = k := (rfl)

/-- Composition of positive degree maps. The modulus is `T.modulus ∘ U.modulus`. -/
def comp (U : PositiveDegreeMap e f) (T : PositiveDegreeMap d e) :
    PositiveDegreeMap d f where
  toAddMonoidHom := U.toAddMonoidHom.comp T.toAddMonoidHom
  map_mem h := U.map_mem (T.map_mem h)
  map_ne_zero h hn := U.map_ne_zero (T.map_mem h) (T.map_ne_zero h hn)
  modulus := T.modulus ∘ U.modulus
  monotone_modulus := T.monotone_modulus.comp U.monotone_modulus
  degree_gt k hn h := U.degree_gt k (T.map_mem hn) (T.degree_gt _ hn h)

@[simp]
theorem comp_apply (U : PositiveDegreeMap e f) (T : PositiveDegreeMap d e) (n : N) :
    U.comp T n = U (T n) := (rfl)

@[simp]
theorem comp_modulus (U : PositiveDegreeMap e f) (T : PositiveDegreeMap d e) (k : ℕ) :
    (U.comp T).modulus k = T.modulus (U.modulus k) := (rfl)

@[simp]
theorem id_comp (T : PositiveDegreeMap d e) : (id e).comp T = T := by
  ext <;> rfl

@[simp]
theorem comp_id (T : PositiveDegreeMap d e) : T.comp (id d) = T := by
  ext <;> rfl

/-- Composition is associative, including the cutoff moduli. -/
theorem comp_assoc (V : PositiveDegreeMap f g) (U : PositiveDegreeMap e f)
    (T : PositiveDegreeMap d e) : (V.comp U).comp T = V.comp (U.comp T) := by
  ext <;> rfl

/-- Replace the cutoff modulus by any larger monotone modulus. -/
def enlarge (T : PositiveDegreeMap d e) (μ : ℕ → ℕ) (hμ : Monotone μ)
    (hle : ∀ k, T.modulus k ≤ μ k) : PositiveDegreeMap d e where
  toAddMonoidHom := T.toAddMonoidHom
  map_mem := T.map_mem
  map_ne_zero := T.map_ne_zero
  modulus := μ
  monotone_modulus := hμ
  degree_gt k hn h := T.degree_gt k hn (lt_of_le_of_lt (by exact_mod_cast hle k) h)

@[simp]
theorem enlarge_apply (T : PositiveDegreeMap d e) (μ : ℕ → ℕ) (hμ : Monotone μ)
    (hle : ∀ k, T.modulus k ≤ μ k) (n : N) : T.enlarge μ hμ hle n = T n := (rfl)

@[simp]
theorem enlarge_modulus (T : PositiveDegreeMap d e) (μ : ℕ → ℕ) (hμ : Monotone μ)
    (hle : ∀ k, T.modulus k ≤ μ k) : (T.enlarge μ hμ hle).modulus = μ := (rfl)

/-- Make an arbitrary cutoff bound monotone using its finite partial suprema. -/
def ofModulus (T : N →+ M) (hmem : ∀ n ∈ d.monoid, T n ∈ e.monoid)
    (μ : ℕ → ℕ)
    (hμ : ∀ n ∈ d.monoid, ∀ k : ℕ, (μ k : ℤ) < d.degree n →
      (k : ℤ) < e.degree (T n)) : PositiveDegreeMap d e where
  toAddMonoidHom := T
  map_mem := hmem _
  map_ne_zero {n} hn hn0 h := by
    have hp : (1 : ℤ) ≤ d.degree n := d.degree_pos hn hn0
    have hdeg : (μ 0 : ℤ) < d.degree ((μ 0 + 1) • n) := by
      rw [map_nsmul, nsmul_eq_mul]
      have := le_mul_of_one_le_right (Int.natCast_nonneg (μ 0 + 1)) hp
      omega
    simpa [map_nsmul, h] using hμ _ (d.monoid.nsmul_mem hn _) 0 hdeg
  modulus := partialSups μ
  monotone_modulus := (partialSups μ).monotone
  degree_gt k hn h := hμ _ hn k
    (lt_of_le_of_lt (by exact_mod_cast le_partialSups μ k) h)

@[simp]
theorem ofModulus_apply (T : N →+ M) (hmem) (μ) (hμ) (n : N) :
    ofModulus (d := d) (e := e) T hmem μ hμ n = T n := (rfl)

@[simp]
theorem ofModulus_modulus (T : N →+ M) (hmem) (μ) (hμ) :
    (ofModulus (d := d) (e := e) T hmem μ hμ).modulus = partialSups μ := (rfl)

/-- A linear source-degree bound gives modulus `k ↦ c * k`.
The bound must control the source degree by the image degree. -/
def ofBound (T : N →+ M) (hmem : ∀ n ∈ d.monoid, T n ∈ e.monoid)
    (c : ℕ)
    (hbound : ∀ n ∈ d.monoid, d.degree n ≤ c * e.degree (T n)) :
    PositiveDegreeMap d e where
  toAddMonoidHom := T
  map_mem := hmem _
  map_ne_zero {n} hn hn0 h := by
    have hb := hbound n hn
    have hp := d.degree_pos hn hn0
    simp only [h, _root_.map_zero, mul_zero] at hb
    omega
  modulus k := c * k
  monotone_modulus _ _ h := Nat.mul_le_mul_left c h
  degree_gt {n} k hn h := by
    have hb := hbound _ hn
    by_contra hle
    have hh := mul_le_mul_of_nonneg_left (le_of_not_gt hle) (Int.natCast_nonneg c)
    simp only [Nat.cast_mul] at h
    omega

@[simp]
theorem ofBound_apply (T : N →+ M) (hmem) (c) (hbound) (n : N) :
    ofBound (d := d) (e := e) T hmem c hbound n = T n := (rfl)

@[simp]
theorem ofBound_modulus (T : N →+ M) (hmem) (c) (hbound) (k : ℕ) :
    (ofBound (d := d) (e := e) T hmem c hbound).modulus k = c * k := (rfl)

/-- Finite inverse images of target cutoffs give a canonical modulus: the maximum
source degree of an allowed element surviving the target cutoff. -/
noncomputable def ofFinitePreimage (T : N →+ M)
    (hmem : ∀ n ∈ d.monoid, T n ∈ e.monoid)
    (hfin : ∀ k : ℕ, Set.Finite {n | n ∈ d.monoid ∧ e.degree (T n) ≤ k}) :
    PositiveDegreeMap d e where
  toAddMonoidHom := T
  map_mem := hmem _
  map_ne_zero {n} hn hn0 h := by
    have hi := (nsmul_left_strictMono (d.degree_pos hn hn0)).injective
    apply Set.infinite_of_injective_forall_mem hi ?_ ((hfin 0).image d.degree)
    intro m
    exact ⟨m • n, ⟨d.monoid.nsmul_mem hn m, by simp [map_nsmul, h]⟩,
      map_nsmul d.degree m n⟩
  modulus k := (hfin k).toFinset.sup (fun n => (d.degree n).toNat)
  monotone_modulus := by
    intro k l hkl
    apply Finset.sup_mono
    apply Set.Finite.toFinset_mono
    intro n hn
    exact ⟨hn.1, hn.2.trans (by exact_mod_cast hkl)⟩
  degree_gt {n} k hn h := by
    by_contra hle
    have hmem' : n ∈ (hfin k).toFinset := by
      simpa using And.intro hn (le_of_not_gt hle)
    have hb := Finset.le_sup (f := fun n => (d.degree n).toNat) hmem'
    have := Int.self_le_toNat (d.degree n)
    omega

@[simp]
theorem ofFinitePreimage_apply (T : N →+ M) (hmem) (hfin) (n : N) :
    ofFinitePreimage (d := d) (e := e) T hmem hfin n = T n := (rfl)

/-- The modulus is the finite supremum of the source degrees in the inverse cutoff.
Source degrees are nonnegative on the allowed monoid, so `toNat` loses no information. -/
@[simp]
theorem ofFinitePreimage_modulus (T : N →+ M) (hmem) (hfin) (k : ℕ) :
    (ofFinitePreimage (d := d) (e := e) T hmem hfin).modulus k =
      (hfin k).toFinset.sup (fun n => (d.degree n).toNat) := (rfl)

/-- The finite-maximum modulus is the least cutoff bound at each target order. -/
theorem ofFinitePreimage_modulus_le_iff (T : N →+ M) (hmem) (hfin) (k l : ℕ) :
    (ofFinitePreimage (d := d) (e := e) T hmem hfin).modulus k ≤ l ↔
      ∀ n ∈ d.monoid, e.degree (T n) ≤ k → d.degree n ≤ l := by
  simp [Finset.sup_le_iff, Int.toNat_le]

/-- Injectivity on the allowed monoid suffices for finite inverse cutoff sets.
The ambient additive map need not be injective. -/
noncomputable def ofInjectiveOn (T : N →+ M)
    (hmem : ∀ n ∈ d.monoid, T n ∈ e.monoid) (hinj : Set.InjOn T d.monoid) :
    PositiveDegreeMap d e :=
  ofFinitePreimage T hmem
    (fun k => (e.finite_cutoff k).of_injOn
      (fun n hn => (e.mem_cutoff).mpr ⟨hmem n hn.1, hn.2⟩)
      (hinj.mono (fun _ hn => hn.1)))

@[simp]
theorem ofInjectiveOn_apply (T : N →+ M) (hmem) (hinj) (n : N) :
    ofInjectiveOn (d := d) (e := e) T hmem hinj n = T n := (rfl)

/-- The injective-map modulus is exactly the maximum source degree over each
inverse target cutoff, characterized without unfolding the finite-set construction. -/
theorem ofInjectiveOn_modulus_le_iff (T : N →+ M) (hmem) (hinj) (k l : ℕ) :
    (ofInjectiveOn (d := d) (e := e) T hmem hinj).modulus k ≤ l ↔
      ∀ n ∈ d.monoid, e.degree (T n) ≤ k → d.degree n ≤ l :=
  ofFinitePreimage_modulus_le_iff _ _ _ _ _

/-- Changing the degree function on the same allowed monoid gives a positive degree
map. Applying this construction in reverse gives the reverse cutoff comparison. -/
noncomputable def changeDegree (d e : PositiveDegrees N) (hP : d.monoid = e.monoid) :
    PositiveDegreeMap d e :=
  ofInjectiveOn (AddMonoidHom.id N) (fun _ hn => hP ▸ hn)
    (Function.injective_id.injOn)

@[simp]
theorem changeDegree_apply (d e : PositiveDegrees N) (hP) (n : N) :
    changeDegree d e hP n = n := (rfl)

/-- The change-of-degree cutoff is the maximum old degree at bounded new degree. -/
theorem changeDegree_modulus_le_iff (d e : PositiveDegrees N) (hP) (k l : ℕ) :
    (changeDegree d e hP).modulus k ≤ l ↔
      ∀ n ∈ d.monoid, e.degree n ≤ k → d.degree n ≤ l :=
  ofInjectiveOn_modulus_le_iff _ _ _ _ _

end PositiveDegreeMap
end TauCeti
