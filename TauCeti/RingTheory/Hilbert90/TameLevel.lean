/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.RingTheory.Artinian.Ring
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.GroupTheory.Index
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# Hilbert's Theorem 90 for `GL n` and units at a congruence level

Let `R` be a commutative ring, `σ : R →+* R` a ring endomorphism of finite period `p > 0`, and
`m : R` a `σ`-invariant element. We say `σ` is **tame at level `m`**
(`TauCeti.TameHilbert90.IsTameAtLevel σ p m`) if `σ m = m`, `σ ^ p = 1`, some element `e : R` has
trace `∑ i ∈ Finset.range p, (σ ^ i) e ≡ 1 [mod m]`, and for every `0 < i < p`, every prime ideal
modulo which `σ ^ i` acts trivially contains `m`.

Over any Artinian commutative ring `R`, we prove Hilbert's Theorem 90 with congruence level `m` for
both `GL n R` and `Rˣ`:

* `TauCeti.TameHilbert90.IsTameAtLevel.exists_smul_mem_span_fixedPoints`: Galois descent at any
  prime `P` with `m ∉ P` for a `σ`-semilinear map `τ : V →ₛₗ[σ] V` of period `p` (no Artinian
  assumption needed).
* `TauCeti.TameHilbert90.IsTameAtLevel.hilbert90_gl`: if `R` is Artinian and `c : GL n R` satisfies
  `c = 1 + m • Y` and `twistedNorm (GeneralLinearGroup.map σ) p c = 1`, then `c * k.map σ = k` for
  some `k : GL n R` with `k = 1 + m • W`.
* `TauCeti.TameHilbert90.IsTameAtLevel.hilbert90_units`: if `R` is Artinian and `x : Rˣ` satisfies
  `m ∣ (x : R) - 1` and `∏ i ∈ Finset.range p, (σ ^ i) x = 1`, then `x * σ g = g` for some `g : Rˣ`
  with `m ∣ (g : R) - 1`.
* `TauCeti.TameHilbert90.IsTameAtLevel.exists_norm_eq_of_finite`: if `R` is finite and `x : Rˣ` is
  `σ`-fixed with `m ∣ (x : R) - 1`, then `x` is the norm `∏ i ∈ Finset.range p, (σ ^ i) z` of a
  unit `z : Rˣ` with `m ∣ (z : R) - 1` and `m ∣ (z⁻¹ : R) - 1`.

## References

* J.-P. Serre, *Local Fields*, Chapter V, §2 and Chapter X, §1.
* S. Chase, D. Harrison, A. Rosenberg, *Galois theory and Galois cohomology of commutative rings*,
  Mem. AMS 52 (1965).
* P. Scholze, *The Langlands–Kottwitz approach for some simple Shimura varieties*, Invent. Math.
  192 (2013), Lemma 2.2.
-/

public section

open Finset Function Ideal Matrix

namespace TauCeti.TameHilbert90

section TwistedNorm

variable {M : Type*} [Monoid M]

/-- The **twisted norm** `δ * τ δ * τ² δ * ... * τ^(p-1) δ` of an element `δ` of a monoid `M`
under an endomorphism `τ : M →* M`. -/
@[expose] def twistedNorm (τ : M →* M) : ℕ → M → M
  | 0, _ => 1
  | p + 1, δ => δ * τ (twistedNorm τ p δ)

/-- The `0`-th twisted norm is `1`. -/
@[simp]
theorem twistedNorm_zero (τ : M →* M) (δ : M) : twistedNorm τ 0 δ = 1 :=
  rfl

/-- The `(p + 1)`-st twisted norm satisfies `N_{p+1}(δ) = δ * τ (N_p(δ))`. -/
@[simp]
theorem twistedNorm_succ (τ : M →* M) (p : ℕ) (δ : M) :
    twistedNorm τ (p + 1) δ = δ * τ (twistedNorm τ p δ) :=
  rfl

/-- In a commutative monoid, the twisted norm is the product `∏ i ∈ range p, τ^[i] δ`. -/
theorem twistedNorm_eq_prod {C : Type*} [CommMonoid C] (τ : C →* C) (p : ℕ) (δ : C) :
    twistedNorm τ p δ = ∏ i ∈ range p, τ^[i] δ := by
  induction p with
  | zero => simp
  | succ p ih =>
    rw [twistedNorm_succ, ih, map_prod, prod_range_succ', iterate_zero_apply, mul_comm]
    simp only [iterate_succ_apply']

end TwistedNorm

section TameAtLevel

variable {R : Type*} [CommRing R]

/-- A ring endomorphism `σ : R →+* R` is **tame at level `m` with exponent `p`** if `σ m = m`,
`σ ^ p = 1` with `0 < p`, some element has trace congruent to `1` modulo `m`, and for every
`0 < i < p` every prime ideal modulo which `σ ^ i` is the identity contains `m`. -/
structure IsTameAtLevel (σ : R →+* R) (p : ℕ) (m : R) : Prop where
  /-- The level `m` is fixed by `σ`. -/
  map_level : σ m = m
  /-- Some element has trace congruent to `1` modulo `m`. -/
  exists_trace_sub_one_dvd : ∃ e : R, m ∣ ∑ i ∈ range p, (σ ^ i) e - 1
  /-- The `p`-th power of `σ` is the identity. -/
  pow_eq_one : σ ^ p = 1
  /-- The exponent `p` is positive. -/
  pos : 0 < p
  /-- No nontrivial power `σ ^ i` (`0 < i < p`) is trivial modulo a prime not containing `m`. -/
  mem_of_forall_sub_mem : ∀ ⦃i : ℕ⦄, i ∈ Set.Ioo 0 p → ∀ (P : Ideal R) [P.IsPrime],
    (∀ y : R, (σ ^ i) y - y ∈ P) → m ∈ P

/-- The identity endomorphism is tame at every level `m` with exponent `1`. -/
theorem isTameAtLevel_one (m : R) : IsTameAtLevel (RingHom.id R) 1 m where
  map_level := rfl
  exists_trace_sub_one_dvd := ⟨1, by simp⟩
  pow_eq_one := one_pow 1
  pos := one_pos
  mem_of_forall_sub_mem i hi _ _ _ := by
    have := hi.1
    have := hi.2
    omega

/-- For a field extension `L / K` with finite automorphism group `Gal(L/K)`, every
`K`-automorphism `σ` of `L` is tame at level `1` with exponent `orderOf σ`. -/
theorem isTameAtLevel_gal {K L : Type*} [Field K] [Field L] [Algebra K L] (σ : L ≃ₐ[K] L)
    [Finite (L ≃ₐ[K] L)] :
    IsTameAtLevel (σ : L →+* L) (orderOf σ) 1 where
  map_level := map_one _
  exists_trace_sub_one_dvd := ⟨0, by simp⟩
  pow_eq_one := by
    ext y
    simp [← AlgEquiv.coe_pow]
  pos := orderOf_pos σ
  mem_of_forall_sub_mem i hi P hP h_triv := by
    have h_id : σ ^ i = 1 := by
      ext y
      have hy : ((σ : L →+* L) ^ i) y - y ∈ P := h_triv y
      rw [Ideal.eq_bot_of_prime P, Ideal.mem_bot, sub_eq_zero] at hy
      simpa [← AlgEquiv.coe_pow] using hy
    exact absurd h_id (pow_ne_one_of_lt_orderOf hi.1.ne' hi.2)

/-- An involution `σ` (`σ ^ 2 = 1`) fixing `m` such that `x - σ x` is a unit for some `x` is tame
at level `m` with exponent `2`. -/
theorem IsTameAtLevel.of_sq_eq_one_of_isUnit_sub {σ : R →+* R} {m x : R}
    (hσ : σ ^ 2 = 1) (hx : IsUnit (x - σ x)) (hm : σ m = m) :
    IsTameAtLevel σ 2 m := by
  obtain ⟨z, hz⟩ := hx.exists_right_inv
  have hσσ (y : R) : σ (σ y) = y := by simpa [sq] using RingHom.congr_fun hσ y
  have h_map : (σ x - x) * σ z = 1 := by simpa [hσσ] using congrArg σ hz
  have hσz : σ z = -z := by linear_combination (-σ z) * hz - z * h_map
  refine ⟨hm, ⟨x * z, ?_⟩, hσ, two_pos, ?_⟩
  · have h_trace : x * z + σ x * σ z = 1 := by linear_combination σ x * hσz + hz
    simp [sum_range_succ, h_trace]
  · intro i hi P _ h_triv
    obtain rfl : i = 1 := by
      have := hi.1
      have := hi.2
      omega
    have h_mem : x - σ x ∈ P := sub_mem_comm_iff.mp (by simpa using h_triv x)
    exact P.mem_of_dvd hx.dvd h_mem

private lemma map_prod_range_eq_self_of_periodic {M : Type*} [CommMonoid M] {p : ℕ}
    (τ : M →* M) (a : ℕ → M) (h_period : a p = a 0) (h_succ : ∀ i : ℕ, a (i + 1) = τ (a i)) :
    τ (∏ i ∈ range p, a i) = ∏ i ∈ range p, a i := by
  cases p with
  | zero => simp
  | succ p =>
    calc
      τ (∏ i ∈ range (p + 1), a i) = ∏ i ∈ range (p + 1), a (i + 1) := by
        simp only [map_prod, h_succ]
      _ = (∏ i ∈ range p, a (i + 1)) * a (p + 1) := prod_range_succ _ p
      _ = ∏ i ∈ range (p + 1), a i := by rw [h_period, prod_range_succ']

private lemma map_sum_range_eq_self_of_periodic {M : Type*} [AddCommMonoid M] {p : ℕ}
    (τ : M →+ M) (a : ℕ → M) (h_period : a p = a 0) (h_succ : ∀ i : ℕ, a (i + 1) = τ (a i)) :
    τ (∑ i ∈ range p, a i) = ∑ i ∈ range p, a i := by
  cases p with
  | zero => simp
  | succ p =>
    calc
      τ (∑ i ∈ range (p + 1), a i) = ∑ i ∈ range (p + 1), a (i + 1) := by
        simp only [map_sum, h_succ]
      _ = (∑ i ∈ range p, a (i + 1)) + a (p + 1) := sum_range_succ _ p
      _ = ∑ i ∈ range (p + 1), a i := by rw [h_period, sum_range_succ']

private lemma isFixedPt_prod_range_pow_apply {σ : R →+* R} {p : ℕ} (hσ : σ ^ p = 1) (x : R) :
    IsFixedPt σ (∏ i ∈ range p, (σ ^ i) x) :=
  map_prod_range_eq_self_of_periodic (σ : R →* R) (fun i ↦ (σ ^ i) x)
    (by rw [hσ, pow_zero]) fun i ↦ by simp [pow_succ']

/-- **Galois descent at a prime away from the level.** If `σ` is tame at level `m`, `τ` is a
`σ`-semilinear map on an `R`-module `V` of period `p`, and `P` is a prime ideal with `m ∉ P`, then
some `r ∉ P` multiplies all of `V` into the `R`-span of the fixed points of `τ`. -/
theorem IsTameAtLevel.exists_smul_mem_span_fixedPoints {σ : R →+* R} {p : ℕ} {m : R}
    {V : Type*} [AddCommGroup V] [Module R V] (h_tame : IsTameAtLevel σ p m)
    (τ : V →ₛₗ[σ] V) (hτ : ∀ v : V, τ^[p] v = v) (P : Ideal R) [hP : P.IsPrime] (hm : m ∉ P) :
    ∃ r ∉ P, ∀ v : V, r • v ∈ Submodule.span R (fixedPoints τ) := by
  have h_move (i : ℕ) (hi : i ∈ Set.Ioo 0 p) : ∃ a : R, (σ ^ i) a - a ∉ P := by
    by_contra! h_triv
    exact hm (h_tame.mem_of_forall_sub_mem hi P h_triv)
  choose! u hu using h_move
  let orbit : R →+* ℕ → R := RingHom.pi fun i : ℕ ↦ σ ^ i
  let w : ℕ → R := ∏ i ∈ Ioo 0 p, ((σ ^ i) (u i) • (1 : ℕ → R) - orbit (u i))
  have hw_mem : w ∈ Submodule.span R (orbit.range : Set (ℕ → R)) := by
    have h_adjoin : w ∈ Algebra.adjoin R (orbit.range : Set (ℕ → R)) := prod_mem fun i _ ↦
      sub_mem (Subalgebra.smul_mem _ (one_mem _) _) (Algebra.subset_adjoin ⟨u i, rfl⟩)
    simpa using (Algebra.adjoin_eq_span R (orbit.range : Set (ℕ → R))).le h_adjoin
  have hw_zero (z : ℕ) (hz : z ∈ Ioo 0 p) : w z = 0 := by simp [w, orbit, prod_eq_zero hz]
  have hw0 : w 0 ∉ P := by
    have h_eval : w 0 = ∏ i ∈ Ioo 0 p, ((σ ^ i) (u i) - u i) := by simp [w, orbit]
    rw [h_eval, hP.prod_mem_iff]
    rintro ⟨i, hi, h_mem⟩
    exact hu i (mem_Ioo.mp hi) h_mem
  refine ⟨w 0, hw0, fun v ↦ ?_⟩
  let L : (ℕ → R) →ₗ[R] V := ∑ z ∈ range p, (LinearMap.proj z).smulRight (τ^[z] v)
  have hL_orbit (a : R) : L (orbit a) ∈ fixedPoints τ := by
    have h_period : (σ ^ p) a • τ^[p] v = (σ ^ 0) a • τ^[0] v := by
      rw [h_tame.pow_eq_one, hτ, pow_zero, iterate_zero_apply]
    have h_succ (z : ℕ) : (σ ^ (z + 1)) a • τ^[z + 1] v = τ ((σ ^ z) a • τ^[z] v) := by
      simp only [map_smulₛₗ, RingHom.coe_pow, iterate_succ_apply']
    simp only [L, LinearMap.sum_apply, LinearMap.smulRight_apply, LinearMap.proj_apply, orbit,
      RingHom.pi_apply]
    exact map_sum_range_eq_self_of_periodic τ.toAddMonoidHom (fun z ↦ (σ ^ z) a • τ^[z] v)
      h_period h_succ
  have hL_w : L w = w 0 • v := by
    rw [LinearMap.sum_apply, sum_eq_single_of_mem 0 (mem_range.mpr h_tame.pos)]
    · simp
    · intro z hz hz_ne
      simp [hw_zero z (mem_Ioo.mpr ⟨Nat.pos_of_ne_zero hz_ne, mem_range.mp hz⟩)]
  have h_le : (Submodule.span R (orbit.range : Set (ℕ → R))).map L ≤
      Submodule.span R (fixedPoints τ) :=
    (L.map_span_le _ _).mpr <| by
      rintro _ ⟨a, rfl⟩
      exact Submodule.subset_span (hL_orbit a)
  exact h_le ⟨w, hw_mem, hL_w⟩

private lemma exists_fixed_separating {σ : R →+* R} {p : ℕ} {m : R}
    (h_tame : IsTameAtLevel σ p m) [IsArtinianRing R] {d : R} (hd : m ∣ 1 - d) {M : Ideal R}
    (hM : ∀ i : ℕ, (σ ^ i) d ∈ M) :
    ∃ N : R, σ N = N ∧ m ∣ N ∧ Ideal.Quotient.mk M N = 1 ∧
      ∀ P : Ideal R, P.IsPrime → d ∉ P → N ∈ P := by
  obtain ⟨l, y, hy⟩ := IsArtinian.exists_pow_succ_smul_dvd d (1 : R)
  have hy_mul : d ^ (l + 1) * y = d ^ l := by simpa [smul_eq_mul] using hy
  let a : R := (1 - d) * (1 - d * y)
  have ha_dvd : a ∣ ∏ i ∈ range p, (σ ^ i) a := dvd_prod_of_mem _ (mem_range.mpr h_tame.pos)
  have h_one : Ideal.Quotient.mk M (∏ i ∈ range p, (σ ^ i) a) = 1 := by
    rw [map_prod]
    exact prod_eq_one fun i _ ↦ by
      simp [a, -RingHom.coe_pow, Ideal.Quotient.eq_zero_iff_mem.mpr (hM i)]
  have h_zero : d ^ l * a = 0 := by
    calc d ^ l * a = (1 - d) * (d ^ l - d ^ (l + 1) * y) := by simp only [a]; ring
      _ = 0 := by rw [hy_mul, sub_self, mul_zero]
  refine ⟨∏ i ∈ range p, (σ ^ i) a, isFixedPt_prod_range_pow_apply h_tame.pow_eq_one a,
    (hd.mul_right _).trans ha_dvd, h_one, fun P hP hdP ↦ ?_⟩
  have ha_mem : a ∈ P :=
    (hP.mem_or_mem_of_mul_eq_zero h_zero).resolve_left (P.primeCompl.pow_mem hdP l)
  exact P.mem_of_dvd ha_dvd ha_mem

private lemma exists_fixed_det_notMem {n : Type*} [Fintype n] [DecidableEq n]
    {σ : R →+* R} {p : ℕ} {m : R} (h_tame : IsTameAtLevel σ p m) {c : Matrix n n R}
    {τ : Matrix n n R →ₛₗ[σ] Matrix n n R}
    (hτ : ∀ v : Matrix n n R, τ v = c * v.map σ) (hτ_period : ∀ v : Matrix n n R, τ^[p] v = v)
    (P : Ideal R) [P.IsPrime] (hm : m ∉ P) :
    ∃ v : Matrix n n R, τ v = v ∧ v.det ∉ P := by
  by_contra! h_all
  obtain ⟨r, hr, h_span⟩ := h_tame.exists_smul_mem_span_fixedPoints τ hτ_period P hm
  obtain ⟨k, s, G, hG⟩ : ∃ (k : ℕ) (s : Fin k → R) (G : Fin k → fixedPoints τ),
      ∑ i : Fin k, s i • (G i : Matrix n n R) = r • 1 :=
    Submodule.mem_span_set'.mp (h_span 1)
  have h_det : (∑ i, s i • (G i).val)ᵀ.det ∈ P := by
    have h_rows : (∑ i, s i • (G i).val)ᵀ = fun j : n ↦ ∑ i, s i • (G i).valᵀ j :=
      funext₂ fun j l ↦ by simp [Matrix.sum_apply, Finset.sum_apply]
    rw [h_rows]
    change detRowAlternating (fun j : n ↦ ∑ i, s i • (G i).valᵀ j) ∈ P
    rw [← AlternatingMap.coe_multilinearMap, MultilinearMap.map_sum]
    refine sum_mem fun f _ ↦ ?_
    rw [MultilinearMap.map_smul_univ]
    refine P.smul_mem _ ?_
    have h_fixed : τ (of fun i j : n ↦ (G (f j)).val i j) =
        of fun i j : n ↦ (G (f j)).val i j :=
      (hτ _).trans <| ext fun i j ↦ congrFun₂ ((hτ _).symm.trans (G (f j)).property) i j
    have h_mem : (of fun (i j) ↦ (G (f j) : Matrix n n R) i j).det ∈ P := h_all _ h_fixed
    rwa [← det_transpose] at h_mem
  have h_pow : r ^ Fintype.card n ∈ P := by simpa [hG] using h_det
  exact P.primeCompl.pow_mem hr (Fintype.card n) h_pow

private lemma exists_fixed_eq_one_add_smul {n : Type*} [Fintype n] [DecidableEq n]
    {σ : R →+* R} {p : ℕ} {m : R} (h_tame : IsTameAtLevel σ p m)
    {c Y : Matrix n n R} (hY : c = 1 + m • Y) {τ : Matrix n n R →ₛₗ[σ] Matrix n n R}
    (hτ : ∀ v : Matrix n n R, τ v = c * v.map σ) (hτ_period : ∀ v : Matrix n n R, τ^[p] v = v) :
    ∃ g : Matrix n n R, τ g = g ∧ ∃ W : Matrix n n R, g = 1 + m • W := by
  obtain ⟨e, w, he⟩ := h_tame.exists_trace_sub_one_dvd
  have h_step (v : Matrix n n R) : τ (1 + m • v) = 1 + m • (Y + τ v) := by
    simp [hτ, hY, Matrix.map_add, Matrix.map_smul, h_tame.map_level, mul_add, add_mul,
      smul_add, add_assoc]
  let Z (i : ℕ) : Matrix n n R := (fun v : Matrix n n R ↦ Y + τ v)^[i] 0
  have hZ (i : ℕ) : τ^[i] 1 = 1 + m • Z i := by
    induction i with
    | zero => simp [Z]
    | succ i ih => simp only [iterate_succ_apply', ih, h_step, Z]
  have h_smul (i : ℕ) (a : R) (v : Matrix n n R) : τ^[i] (a • v) = (σ ^ i) a • τ^[i] v := by
    induction i with
    | zero => simp
    | succ i ih => simp [iterate_succ_apply', ih, -iterate_succ]
  have h_fixed : τ (∑ i ∈ range p, τ^[i] (e • 1)) = ∑ i ∈ range p, τ^[i] (e • 1) :=
    map_sum_range_eq_self_of_periodic τ.toAddMonoidHom (fun i ↦ τ^[i] (e • 1))
      (hτ_period (e • 1)) fun i ↦ iterate_succ_apply' τ i (e • 1)
  refine ⟨_, h_fixed, w • 1 + ∑ i ∈ range p, (σ ^ i) e • Z i, ?_⟩
  calc
    ∑ i ∈ range p, τ^[i] (e • 1) = ∑ i ∈ range p, (σ ^ i) e • (1 + m • Z i) := by
      simp only [h_smul, hZ]
    _ = (∑ i ∈ range p, (σ ^ i) e) • 1 + m • ∑ i ∈ range p, (σ ^ i) e • Z i := by
      simp only [smul_add, sum_add_distrib, sum_smul, smul_sum, smul_comm m]
    _ = 1 + m • (w • 1 + ∑ i ∈ range p, (σ ^ i) e • Z i) := by
      rw [eq_add_of_sub_eq' he]
      simp [add_smul, mul_smul, add_assoc]

private lemma dvd_one_sub_det_one_add_smul {n : Type*} [Fintype n] [DecidableEq n]
    (m : R) (W : Matrix n n R) : m ∣ 1 - (1 + m • W).det := by
  rw [← Ideal.Quotient.eq_zero_iff_dvd, map_sub, map_one, RingHom.map_det]
  have hmap : (1 + m • W).map (Ideal.Quotient.mk (span {m})) = 1 := by
    ext i j
    have hm0 : Ideal.Quotient.mk (span {m}) m = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton m))
    simp [Matrix.one_apply, hm0]
  rw [RingHom.mapMatrix_apply, hmap, det_one, sub_self]

/-- **Hilbert's Theorem 90 for `GL n` at congruence level `m` over an Artinian ring.** If `R` is
Artinian, `σ` is tame at level `m` with exponent `p`, and `c : GL n R` satisfies `c = 1 + m • Y`
and `twistedNorm (GeneralLinearGroup.map σ) p c = 1`, then `c * k.map σ = k` for some `k : GL n R`
with `k = 1 + m • W`. -/
theorem IsTameAtLevel.hilbert90_gl {n : Type*} [Fintype n] [DecidableEq n]
    {σ : R →+* R} {p : ℕ} {m : R} (h_tame : IsTameAtLevel σ p m) [IsArtinianRing R]
    (c : GL n R) {Y : Matrix n n R} (hY : c.val = 1 + m • Y)
    (hc : twistedNorm (GeneralLinearGroup.map σ) p c = 1) :
    ∃ k : GL n R, ∃ W : Matrix n n R, c.val * k.val.map σ = k.val ∧ k.val = 1 + m • W := by
  let τ : Matrix n n R →ₛₗ[σ] Matrix n n R := .mulLeft R c.val ∘ₛₗ σ.toSemilinearMap.mapMatrix
  have hτ_apply (v : Matrix n n R) : τ v = c.val * v.map σ := rfl
  have hτ (i : ℕ) (v : Matrix n n R) :
      τ^[i] v = (twistedNorm (GeneralLinearGroup.map σ) i c).val * v.map (σ ^ i) := by
    induction i with
    | zero => simp
    | succ i ih =>
      rw [iterate_succ_apply', ih, hτ_apply, Matrix.map_mul, Matrix.map_map, ← mul_assoc]
      rw [twistedNorm_succ, Units.val_mul]
      congr 1
      ext a b
      simp [pow_succ']
  have hτ_period (v : Matrix n n R) : τ^[p] v = v := by simp [hτ, hc, h_tame.pow_eq_one]
  obtain ⟨g, ⟨hg, W, hW⟩, hmax⟩ := exists_maximalFor_of_wellFoundedGT
    (fun g ↦ τ g = g ∧ ∃ W : Matrix n n R, g = 1 + m • W) (fun g ↦ PrimeSpectrum.basicOpen g.det)
    (exists_fixed_eq_one_add_smul h_tame hY hτ_apply hτ_period)
  suffices h_unit : IsUnit g.det from ⟨Matrix.GeneralLinearGroup.mk'' g h_unit, W, hg, hW⟩
  by_contra h_nonunit
  obtain ⟨M, hM, hgM⟩ := exists_max_ideal_of_mem_nonunits h_nonunit
  have h_conj (i : ℕ) : (σ ^ i) g.det ∈ M := by
    have h_det : g.det = (twistedNorm (GeneralLinearGroup.map σ) i c).val.det * (σ ^ i) g.det := by
      conv_lhs => rw [← iterate_fixed hg i, hτ, det_mul]
      rw [RingHom.map_det, RingHom.mapMatrix_apply]
    have h_unit : IsUnit (twistedNorm (GeneralLinearGroup.map σ) i c).val.det := by simp
    rwa [h_det, M.unit_mul_mem_iff_mem h_unit] at hgM
  have hm_dvd : m ∣ 1 - g.det := hW ▸ dvd_one_sub_det_one_add_smul m W
  obtain ⟨N, hN_fixed, ⟨z, hz⟩, hN_one, hN_mem⟩ := exists_fixed_separating h_tame hm_dvd h_conj
  have hmM : m ∉ M := fun hm_mem ↦ by
    have hN_mem_M : N ∈ M := by simpa [hz] using M.mul_mem_right z hm_mem
    exact hM.ne_top <| (Ideal.eq_top_iff_one M).mpr <| by
      simp [← Ideal.Quotient.eq_zero_iff_mem, hN_one] at hN_mem_M
  obtain ⟨v, hv, hvM⟩ := exists_fixed_det_notMem h_tame hτ_apply hτ_period M hmM
  have h_fixed : τ (g - N • (g - v)) = g - N • (g - v) := by simp [hg, hv, hN_fixed]
  have h_cong : g - N • (g - v) = 1 + m • (W - z • (g - v)) := by
    rw [hz, mul_smul, smul_sub m, ← add_sub_assoc, ← hW]
  have h_le : PrimeSpectrum.basicOpen g.det ≤ PrimeSpectrum.basicOpen (g - N • (g - v)).det := by
    rintro ⟨P, hP⟩ hgP
    have hN_zero : Ideal.Quotient.mk P N = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (hN_mem P hP hgP)
    simpa [← Ideal.Quotient.eq_zero_iff_mem, RingHom.map_det, Matrix.map_sub, Matrix.map_smul',
      hN_zero] using hgP
  have h_mem : ⟨M, hM.isPrime⟩ ∈ PrimeSpectrum.basicOpen (g - N • (g - v)).det := by
    simpa [← Ideal.Quotient.eq_zero_iff_mem, RingHom.map_det, Matrix.map_sub, Matrix.map_smul',
      hN_one] using hvM
  exact hmax ⟨h_fixed, _, h_cong⟩ h_le h_mem hgM

/-- **Hilbert's Theorem 90 for units at congruence level `m` over an Artinian ring.** If `R` is
Artinian, `σ` is tame at level `m` with exponent `p`, and `x : Rˣ` satisfies `m ∣ (x : R) - 1` and
`∏ i ∈ range p, (σ ^ i) x = 1`, then `x * σ g = g` for some `g : Rˣ` with `m ∣ (g : R) - 1`. -/
theorem IsTameAtLevel.hilbert90_units {σ : R →+* R} {p : ℕ} {m : R}
    (h_tame : IsTameAtLevel σ p m) [IsArtinianRing R] {x : Rˣ} (hx_one : m ∣ (x : R) - 1)
    (hx_norm : ∏ i ∈ range p, (σ ^ i) (x : R) = 1) :
    ∃ g : Rˣ, m ∣ (g : R) - 1 ∧ (x : R) * σ g = g := by
  obtain ⟨y, hy⟩ := hx_one
  let c : GL Unit R := Units.mk (of fun _ _ ↦ (x : R)) (of fun _ _ ↦ ((x⁻¹ : Rˣ) : R))
    (by ext i j; simp [Matrix.mul_apply]) (by ext i j; simp [Matrix.mul_apply])
  have hc_val : c.val = 1 + m • of fun _ _ ↦ y := by
    ext i j
    simpa [c] using eq_add_of_sub_eq' hy
  have hc_norm : twistedNorm (GeneralLinearGroup.map σ) p c = 1 := by
    have h_entry (k : ℕ) : (twistedNorm (GeneralLinearGroup.map σ) k c).val () () =
        ∏ i ∈ range k, (σ ^ i) (x : R) := by
      induction k with
      | zero => simp
      | succ k ih =>
        rw [twistedNorm_succ, Units.val_mul, Matrix.mul_apply, Fintype.sum_unique]
        change (x : R) * σ ((twistedNorm (GeneralLinearGroup.map σ) k c).val () ()) = _
        rw [ih, map_prod, prod_range_succ']
        simp only [pow_zero, RingHom.coe_one, id_eq, pow_succ', RingHom.coe_mul,
          Function.comp_apply, mul_comm]
    ext i j
    have hi : i = () := rfl
    have hj : j = () := rfl
    subst hi; subst hj
    change (twistedNorm (GeneralLinearGroup.map σ) p c).val () () = 1
    rw [h_entry p, hx_norm]
  obtain ⟨k, W, hk, hW⟩ := h_tame.hilbert90_gl c hc_val hc_norm
  refine ⟨k.det, ?_, ?_⟩
  · have h_det : (k.det : R) = 1 + m * W () () := by simp [hW]
    rw [h_det, add_sub_cancel_left]
    exact dvd_mul_right m _
  · have h_entry : (c.val * k.val.map σ) () () = k.val () () := by rw [hk]
    simpa [c, Matrix.mul_apply] using h_entry

/-- **Surjectivity of the norm on `σ`-fixed units at congruence level `m` over a finite ring.** If
`R` is finite, `σ` is tame at level `m` with exponent `p`, and `x : Rˣ` is `σ`-fixed with
`m ∣ (x : R) - 1`, then `x` is the norm `∏ i ∈ range p, (σ ^ i) z` of a unit `z : Rˣ` with
`m ∣ (z : R) - 1` and `m ∣ (z⁻¹ : R) - 1`. -/
theorem IsTameAtLevel.exists_norm_eq_of_finite {σ : R →+* R} {p : ℕ} {m : R}
    (h_tame : IsTameAtLevel σ p m) [Finite R] {x : Rˣ} (hσx : σ x = x)
    (hx_one : m ∣ (x : R) - 1) :
    ∃ z : Rˣ, m ∣ (z : R) - 1 ∧ m ∣ ((z⁻¹ : Rˣ) : R) - 1 ∧ ∏ i ∈ range p, (σ ^ i) (z : R) = x := by
  have hσ : σ ^ p = 1 := h_tame.pow_eq_one
  let H : Subgroup Rˣ :=
    ((Ideal.Quotient.mk (span {m})).toMonoidHom.comp (Units.coeHom R)).ker.copy
      {u | m ∣ (u : R) - 1} (by simp [Set.ext_iff, ← Ideal.Quotient.eq_zero_iff_dvd, sub_eq_zero])
  have h_stable (i : ℕ) :
      Set.MapsTo (Units.map ((σ ^ i : R →+* R) : R →* R)) (H : Set Rˣ) (H : Set Rˣ) := by
    intro y hy
    have h_dvd : (σ ^ i) m ∣ (σ ^ i) ((y : R) - 1) := map_dvd (σ ^ i) hy
    change m ∣ ((Units.map ((σ ^ i : R →+* R) : R →* R) y : Rˣ) : R) - 1
    simpa [iterate_fixed h_tame.map_level] using h_dvd
  let s (i : ℕ) : H →* H := (Units.map ((σ ^ i : R →+* R) : R →* R)).restrict (h_stable i)
  let norm : H →* H := (range p).prod s
  let cob : H →* H := s 0 / s 1
  have h_s_coe (i : ℕ) (z : H) : ((s i z : Rˣ) : R) = (σ ^ i) ((z : Rˣ) : R) := rfl
  have h_norm_coe (z : H) : ((norm z : Rˣ) : R) = ∏ i ∈ range p, (σ ^ i) ((z : Rˣ) : R) := by
    simp [norm, h_s_coe]
  have h_range : norm.range ≤ cob.ker := by
    rintro _ ⟨z, rfl⟩
    apply div_eq_one_of_eq
    ext
    simpa [h_s_coe, h_norm_coe] using (isFixedPt_prod_range_pow_apply hσ
      (x := ((z : Rˣ) : R))).eq.symm
  have h_ker : norm.ker ≤ cob.range := by
    intro u hu
    have hu_norm : ∏ i ∈ range p, (σ ^ i) ((u : Rˣ) : R) = 1 := by
      rw [← h_norm_coe, MonoidHom.mem_ker.mp hu]
      rfl
    obtain ⟨g, hg, hgu⟩ := h_tame.hilbert90_units u.property hu_norm
    exact ⟨⟨g, hg⟩, div_eq_of_eq_mul'' (Subtype.ext (Units.ext hgu.symm))⟩
  have h_card : Nat.card cob.ker ≤ Nat.card norm.range :=
    calc
      Nat.card cob.ker = cob.range.index := Subgroup.index_range.symm
      _ ≤ norm.ker.index := Subgroup.index_antitone h_ker
      _ = Nat.card norm.range := Subgroup.index_ker norm
  have hx_fixed : (⟨x, hx_one⟩ : H) ∈ cob.ker :=
    div_eq_one_of_eq (Subtype.ext (Units.ext hσx.symm))
  obtain ⟨z, hz⟩ : ∃ z : H, norm z = ⟨x, hx_one⟩ :=
    (Subgroup.eq_of_le_of_card_ge h_range h_card).ge hx_fixed
  refine ⟨z.val, z.property, z⁻¹.property, ?_⟩
  rw [← h_norm_coe, hz]

end TameAtLevel

end TauCeti.TameHilbert90
