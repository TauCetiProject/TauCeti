/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Ray
import Mathlib.Order.Preorder.Finite

/-!
# Vectors in the same ray: partitions, sums, finite orbits, and durations of segments

Mathlib's `SameRay.trans` chains two ray relations `SameRay R x y` and `SameRay R y z` into
`SameRay R x z`, provided the middle vector `y` vanishes only when `x` or `z` does.
`TauCeti.sameRay_of_partition` iterates this step along a finite ordered partition of an interval
in a linear order: if a map `w` into an ordered scalar module lies, on each piece of the
partition, on the ray of its value at the end of that piece, and `w` vanishes at a point of the
interval only if it vanishes at every earlier point, then every value of `w` lies on the ray of
the final value. The explicit-partition induction follows the pattern of the Apache-2.0
[`frenzymath/Poincare-Conjecture`](https://github.com/frenzymath/Poincare-Conjecture)
formalization, revision `24f32e4d600878bfaac6bc2f2f9324175571c321`, as used in
`TauCeti/Geometry/Manifold/Riemannian/EDistComparison.lean`.

Scaling a ray by a unit commutes with negating it (`Module.Ray.units_smul_neg`), complementing
Mathlib's `Module.Ray.neg_units_smul`, and with transporting it along a linear equivalence
(`Module.Ray.map_units_smul`). Over a linearly ordered ring, any map of rays commuting with negation
also commutes with scaling by units (`Module.Ray.units_smul_of_map_neg`).

Two nonzero vectors in the same ray cannot cancel: their sum is again nonzero. This is the
non-degeneracy needed to merge adjacent segments of a piecewise-linear path that point in the same
direction. A vector lies in the same ray as such a sum exactly when it lies in the same ray as the
summands, since `SameRay` is transitive through a nonzero vector.

Two distinct points of a finite orbit of a linear group action never lie in the same ray. This is
what makes the velocity of each segment of a path with velocities in a Weyl orbit recoverable from
the segment alone: if no two distinct points of a set `S ∌ 0` lie in the same ray, a segment `v`
traversed in a positive time `d` at a velocity `d⁻¹ • v ∈ S` determines `d`
(`Set.Pairwise.eq_of_snd_eq_of_inv_smul_mem`), and a list of such segments determines its list
of durations (`Set.Pairwise.eq_of_map_snd_eq_of_inv_smul_mem`). Two pairs `(d, v)` and `(e, w)`
of positive durations lie in the same ray exactly when they have the same velocity
(`Prod.sameRay_iff_inv_fst_smul_snd_eq`).
-/

public section

open Module

section Semiring

variable {R M : Type*} [CommSemiring R] [PartialOrder R] [IsStrictOrderedRing R]
  [AddCommMonoid M] [Module R M] {x y z : M}

/-- `SameRay` is transitive through a nonzero vector. -/
theorem SameRay.trans_of_ne_zero (hxy : SameRay R x y) (hyz : SameRay R y z) (hy : y ≠ 0) :
    SameRay R x z :=
  hxy.trans hyz fun h ↦ absurd h hy

/-- Transporting a ray along a linear equivalence commutes with scaling it by a unit. -/
@[simp]
theorem Module.Ray.map_units_smul {N : Type*} [AddCommMonoid N] [Module R N] (f : M ≃ₗ[R] N)
    (u : Rˣ) (v : Module.Ray R M) : Module.Ray.map f (u • v) = u • Module.Ray.map f v := by
  induction v using Module.Ray.ind with | h v hv =>
    simp only [smul_rayOfNeZero, Module.Ray.map_apply, Units.smul_def, map_smul]

end Semiring

section Partition

open Set

namespace TauCeti

variable {R α M : Type*} [CommSemiring R] [PartialOrder R] [IsStrictOrderedRing R]
  [LinearOrder α] [AddCommMonoid M] [Module R M] {w : α → M}

/-- **Rays chain through a partition.** If a map `w` into an ordered scalar module lies, on each
piece of an ordered partition, on the ray of its value at the end of that piece, and `w` vanishes
at a point of the interval only if it vanishes at every earlier point of the interval, then every
value lies on the ray of the final value. -/
theorem sameRay_of_partition {k : ℕ} (τ : Fin (k + 2) → α)
    (hτ : ∀ i : Fin (k + 1), τ i.castSucc ≤ τ i.succ)
    (hpiece : ∀ i : Fin (k + 1), ∀ t ∈ Icc (τ i.castSucc) (τ i.succ),
      SameRay R (w t) (w (τ i.succ)))
    (hzero : ∀ ⦃s⦄, s ∈ Icc (τ 0) (τ (Fin.last (k + 1))) →
      ∀ ⦃u⦄, u ∈ Icc (τ 0) (τ (Fin.last (k + 1))) → s ≤ u → w u = 0 → w s = 0)
    {t : α} (ht : t ∈ Icc (τ 0) (τ (Fin.last (k + 1)))) :
    SameRay R (w t) (w (τ (Fin.last (k + 1)))) := by
  induction k generalizing t with
  | zero => simpa using hpiece 0 t (by simpa using ht)
  | succ k ih =>
      have hτmono : Monotone τ := Fin.monotone_iff_le_succ.mpr hτ
      have hlast : τ (Fin.last (k + 1)).succ = τ (Fin.last (k + 2)) := by rw [Fin.succ_last]
      rcases le_or_gt (τ (Fin.last (k + 1)).castSucc) t with hmt | htm
      · simpa only [hlast] using hpiece (Fin.last (k + 1)) t ⟨hmt, hlast ▸ ht.2⟩
      · have hml : τ (Fin.last (k + 1)).castSucc ≤ τ (Fin.last (k + 2)) :=
          hτmono (Fin.le_last _)
        have hm : τ (Fin.last (k + 1)).castSucc ∈ Icc (τ 0) (τ (Fin.last (k + 2))) :=
          ⟨hτmono (Fin.zero_le _), hml⟩
        have h₁ : SameRay R (w t) (w (τ (Fin.last (k + 1)).castSucc)) :=
          ih (fun i ↦ τ i.castSucc)
            (fun i ↦ by simpa only [Fin.succ_castSucc] using hτ i.castSucc)
            (fun i u hu ↦ by simpa only [Fin.succ_castSucc] using hpiece i.castSucc u hu)
            (fun _ hs _ hu ↦ hzero ⟨hs.1, hs.2.trans hml⟩ ⟨hu.1, hu.2.trans hml⟩)
            ⟨ht.1, htm.le⟩
        have h₂ : SameRay R (w (τ (Fin.last (k + 1)).castSucc)) (w (τ (Fin.last (k + 2)))) := by
          simpa only [hlast] using hpiece (Fin.last (k + 1)) _ ⟨le_rfl, hτ _⟩
        exact h₁.trans h₂ fun hm0 ↦ Or.inl (hzero ht hm htm.le hm0)

end TauCeti

end Partition

section Neg

variable {R M : Type*} [CommRing R] [PartialOrder R] [IsStrictOrderedRing R]
  [AddCommGroup M] [Module R M]

/-- Scaling a ray by a unit commutes with negating it. -/
theorem Module.Ray.units_smul_neg (u : Rˣ) (v : Module.Ray R M) : u • -v = -(u • v) := by
  induction v using Module.Ray.ind with | h v hv =>
    simp only [neg_rayOfNeZero, smul_rayOfNeZero, Units.smul_def, smul_neg]

end Neg

section LinearOrder

variable {R M N : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- A map of rays commuting with negation commutes with scaling by units, since a unit acts on rays
as the identity or as negation according to its sign. -/
theorem Module.Ray.units_smul_of_map_neg {F : Module.Ray R M → Module.Ray R N}
    (hF : ∀ v, F (-v) = -F v) (u : Rˣ) (v : Module.Ray R M) : F (u • v) = u • F v := by
  rcases lt_or_gt_of_ne u.ne_zero with hu | hu
  · rw [units_smul_of_neg u hu, units_smul_of_neg u hu, hF]
  · rw [units_smul_of_pos u hu, units_smul_of_pos u hu]

end LinearOrder

variable {R M : Type*} [CommRing R] [PartialOrder R] [IsStrictOrderedRing R] [IsDomain R]
  [AddCommGroup M] [Module R M] [IsTorsionFree R M] {x y z : M}

/-- The sum of two vectors in the same ray, the first of them nonzero, is nonzero. -/
theorem SameRay.add_ne_zero (h : SameRay R x y) (hx : x ≠ 0) : x + y ≠ 0 := by
  intro hxy
  rw [add_eq_zero_iff_eq_neg'] at hxy
  exact hx (eq_zero_of_sameRay_self_neg (hxy ▸ h))

/-- If `x` and `y` lie in the same ray and `y` is nonzero, then a vector lies in the same ray as
`x + y` exactly when it lies in the same ray as `y`. -/
theorem SameRay.sameRay_add_left_iff (h : SameRay R x y) (hy : y ≠ 0) :
    SameRay R (x + y) z ↔ SameRay R y z := by
  have hxy : SameRay R (x + y) y := h.add_left SameRay.rfl
  exact ⟨fun h' ↦ hxy.symm.trans_of_ne_zero h' (add_comm x y ▸ h.symm.add_ne_zero hy),
    fun h' ↦ hxy.trans_of_ne_zero h' hy⟩

section Orbit

variable {R M G : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [AddCommGroup M]
  [Module R M] [Group G] [MulAction G M] [SMulCommClass G R M] {x y z : M}

/-- Two points of a finite orbit of a group acting by maps commuting with scalar multiplication
are equal as soon as they lie in the same ray. If `g` moved a nonzero point `y` of the orbit to
`r • y` with `0 < r`, the powers of `g` would move `y` to the points `r ^ n • y` of the orbit, which
are pairwise distinct unless `r = 1`. -/
theorem SameRay.eq_of_mem_orbit (h : SameRay R y z) (hy : y ∈ MulAction.orbit G x)
    (hz : z ∈ MulAction.orbit G x) (hfin : (MulAction.orbit G x).Finite) : y = z := by
  obtain ⟨g, rfl⟩ := hy
  obtain ⟨g', rfl⟩ := hz
  dsimp only at h ⊢
  -- The point `0` is fixed, since the action commutes with multiplication by `0 : R`.
  have hzero (k : G) : k • (0 : M) = 0 := by simpa using smul_comm k (0 : R) (0 : M)
  have hx (k : G) (hk : k • x = 0) : x = 0 := by
    rw [← inv_smul_smul k x, hk, hzero]
  by_cases hy0 : g • x = 0
  · rw [hy0, hx g hy0, hzero]
  by_cases hz0 : g' • x = 0
  · rw [hz0, hx g' hz0, hzero]
  obtain ⟨r, hr, hrz⟩ := h.exists_pos_left hy0 hz0
  -- The element `g' * g⁻¹` moves `g • x` to `r • g • x`, so its powers move it to `r ^ n • g • x`.
  have hpow (n : ℕ) : (g' * g⁻¹) ^ n • g • x = r ^ n • g • x := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, mul_smul, mul_smul, inv_smul_smul, ← hrz, smul_comm, ih, pow_succ', mul_smul]
  obtain ⟨m, n, hmn, hrmn⟩ := hfin.exists_lt_map_eq_of_forall_mem
    (f := fun n : ℕ ↦ r ^ n • g • x) fun n ↦
      MulAction.mem_orbit_iff.2 ⟨(g' * g⁻¹) ^ n * g, by rw [mul_smul, hpow]⟩
  have hr1 : r = 1 := by
    by_contra hr1
    exact hmn.ne (pow_right_injective₀ hr hr1 (smul_left_injective R hy0 hrmn))
  rw [← hrz, hr1, one_smul]

end Orbit

section Duration

variable {R M : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [AddCommGroup M]
  [Module R M] {S : Set M}

/-- If no two distinct points of a set `S ∌ 0` lie in the same ray, a pair `(d, v)` with `0 < d`
and `d⁻¹ • v ∈ S` is determined by `v`: a segment traversed at a velocity in `S` determines its
duration. -/
theorem Set.Pairwise.eq_of_snd_eq_of_inv_smul_mem (hS : S.Pairwise fun u v ↦ ¬ SameRay R u v)
    (h0 : (0 : M) ∉ S) {x y : R × M} (hx : 0 < x.1 ∧ x.1⁻¹ • x.2 ∈ S)
    (hy : 0 < y.1 ∧ y.1⁻¹ • y.2 ∈ S) (h : x.2 = y.2) : x = y := by
  obtain ⟨d, v⟩ := x
  obtain ⟨e, w⟩ := y
  dsimp only at hx hy h
  subst h
  have hv : v ≠ 0 := by
    rintro rfl
    exact h0 (by simpa using hx.2)
  -- Both velocities are positive multiples of `v`, hence equal.
  have hde : d⁻¹ • v = e⁻¹ • v := by
    by_contra hne
    exact hS hx.2 hy.2 hne
      ((SameRay.rfl.pos_smul_left (inv_pos.2 hx.1)).pos_smul_right (inv_pos.2 hy.1))
  rw [inv_inj.1 (smul_left_injective R hv hde)]

/-- If no two distinct points of a set `S ∌ 0` lie in the same ray, a list of pairs `(d, v)` with
`0 < d` and `d⁻¹ • v ∈ S` is determined by its second components: segments traversed at velocities
in `S` determine their durations. -/
theorem Set.Pairwise.eq_of_map_snd_eq_of_inv_smul_mem
    (hS : S.Pairwise fun u v ↦ ¬ SameRay R u v) (h0 : (0 : M) ∉ S) {p q : List (R × M)}
    (hp : ∀ x ∈ p, 0 < x.1 ∧ x.1⁻¹ • x.2 ∈ S) (hq : ∀ x ∈ q, 0 < x.1 ∧ x.1⁻¹ • x.2 ∈ S)
    (h : p.map Prod.snd = q.map Prod.snd) : p = q := by
  induction p generalizing q with
  | nil => exact (List.map_eq_nil_iff.1 h.symm).symm
  | cons x p ih =>
    cases q with
    | nil => simp at h
    | cons y q =>
      rw [List.map_cons, List.map_cons, List.cons.injEq] at h
      rw [List.forall_mem_cons] at hp hq
      rw [hS.eq_of_snd_eq_of_inv_smul_mem h0 hp.1 hq.1 h.1, ih hp.2 hq.2 h.2]

omit [LinearOrder R] [IsStrictOrderedRing R] in
/-- Rescaling a pair `(d, v)` by a nonzero factor does not change the velocity `d⁻¹ • v`. -/
theorem Prod.inv_fst_smul_snd_smul {a : R} (ha : a ≠ 0) (z : R × M) :
    (a • z).1⁻¹ • (a • z).2 = z.1⁻¹ • z.2 := by
  rw [Prod.smul_fst, Prod.smul_snd, smul_eq_mul, mul_inv_rev, mul_smul, inv_smul_smul₀ ha]

/-- Two pairs `(d, v)` and `(e, w)` with `0 < d` and `0 < e` lie in the same ray exactly when they
have the same velocity, `d⁻¹ • v = e⁻¹ • w`. -/
theorem Prod.sameRay_iff_inv_fst_smul_snd_eq {y z : R × M} (hy : 0 < y.1) (hz : 0 < z.1) :
    SameRay R y z ↔ y.1⁻¹ • y.2 = z.1⁻¹ • z.2 := by
  constructor
  · intro h
    obtain ⟨r, hr, rfl⟩ := h.exists_pos_left (fun h0 ↦ hy.ne' (by simp [h0]))
      (fun h0 ↦ hz.ne' (by simp [h0]))
    exact (inv_fst_smul_snd_smul hr.ne' y).symm
  · intro h
    -- Both pairs are positive multiples of `(1, u)`, where `u` is their common velocity.
    have hy' : y = y.1 • ((1 : R), z.1⁻¹ • z.2) := by
      ext <;> simp [← h, smul_inv_smul₀ hy.ne']
    have hz' : z = z.1 • ((1 : R), z.1⁻¹ • z.2) := by
      ext <;> simp [smul_inv_smul₀ hz.ne']
    have h := ((SameRay.refl (R := R) ((1 : R), z.1⁻¹ • z.2)).nonneg_smul_left
      hy.le).nonneg_smul_right hz.le
    rwa [← hy', ← hz'] at h

end Duration
