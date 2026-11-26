/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.RingTheory.Artinian.Ring
public import TauCeti.Algebra.Group.Hom.TwistedNorm
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.GroupTheory.Index
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Unique
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Spectrum.Prime.Topology
import TauCeti.Algebra.BigOperators.Finset.Periodic
import TauCeti.LinearAlgebra.Matrix.Determinant.IdealDivisibility

/-!
# Hilbert's Theorem 90 for `GL n` and units at a congruence level

Let `R` be a commutative ring, `σ : R →+* R` a ring endomorphism of finite period `p > 0`, and
`m : R` a `σ`-invariant element. We say `σ` is **tame at level `m`**
(`TauCeti.TameHilbert90.IsTameAtLevel σ p m`) if `σ m = m`, `σ ^ p = 1`, some element `e : R` has
`m ∣ ∑ i ∈ Finset.range p, (σ ^ i) e - 1`, and for every `0 < i < p`, every prime ideal modulo
which `σ ^ i` acts trivially contains `m`.

Over any Artinian commutative ring `R`, we prove Hilbert's Theorem 90 with congruence level `m` for
both `GL n R` and `Rˣ`:

* `TauCeti.TameHilbert90.IsTameAtLevel.exists_smul_mem_span_fixedPoints`: Galois descent at any
  prime `P` with `m ∉ P` for a `σ`-semilinear map `τ : V →ₛₗ[σ] V` of period `p` (no Artinian
  assumption needed).
* `TauCeti.TameHilbert90.IsTameAtLevel.exists_mul_map_eq_of_twistedNorm_eq_one`: if `R` is
  Artinian and `c : GL n R` satisfies `c = 1 + m • Y` and
  `MonoidHom.twistedNorm (GeneralLinearGroup.map σ) p c = 1`, then `c * k.map σ = k` for some
  `k : GL n R` with `k = 1 + m • W`.
* `TauCeti.TameHilbert90.IsTameAtLevel.exists_mul_map_eq_of_prod_eq_one`: if `R` is Artinian and
  `x : Rˣ` satisfies `m ∣ (x : R) - 1` and `∏ i ∈ Finset.range p, (σ ^ i) x = 1`, then
  `x * σ g = g` for some `g : Rˣ` with `m ∣ (g : R) - 1`.
* `TauCeti.TameHilbert90.IsTameAtLevel.exists_prod_range_pow_eq_of_finite`: if `R` is finite and
  `x : Rˣ` is `σ`-fixed with `m ∣ (x : R) - 1`, then `x = ∏ i ∈ Finset.range p, (σ ^ i) z` for a
  unit `z : Rˣ` with `m ∣ (z : R) - 1` and `m ∣ ((z⁻¹ : Rˣ) : R) - 1`.

## References

* J.-P. Serre, *Local Fields*, Chapter V, §2 and Chapter X, §1.
* S. Chase, D. Harrison, A. Rosenberg, *Galois theory and Galois cohomology of commutative rings*,
  Mem. AMS 52 (1965).
* P. Scholze, *The Langlands–Kottwitz approach for some simple Shimura varieties*, Invent. Math.
  192 (2013), Lemma 2.2.
* Adapted from L. Alpöge and L. Sernau, Lean formalization of the Riemann Hypothesis for Dirichlet
  L-functions (`https://github.com/leanprover-community/riemann-hypothesis`, commit `2d73830`),
  `src/Lib/GaloisRep/Hilbert90/TameActions.lean` (`New.IsTameAtLevel`).
-/

public section

open Finset Function Ideal Matrix

namespace TauCeti.TameHilbert90

variable {R : Type*} [CommRing R]

/-- A ring endomorphism `σ : R →+* R` is **tame at level `m` with exponent `p`** if `σ m = m`,
`σ ^ p = 1` with `0 < p`, some element has `m ∣ ∑ i ∈ range p, (σ ^ i) e - 1`, and for every
`0 < i < p` every prime ideal modulo which `σ ^ i` is the identity contains `m`. -/
structure IsTameAtLevel (σ : R →+* R) (p : ℕ) (m : R) : Prop where
  /-- The level `m` is fixed by `σ`. -/
  map_level : σ m = m
  /-- Some element has orbit sum congruent to `1` modulo `m`. -/
  exists_dvd_sum_range_pow_sub_one : ∃ e : R, m ∣ ∑ i ∈ range p, (σ ^ i) e - 1
  /-- The `p`-th power of `σ` is the identity. -/
  pow_eq_one : σ ^ p = 1
  /-- The exponent `p` is positive. -/
  pos : 0 < p
  /-- No nontrivial power `σ ^ i` (`0 < i < p`) is trivial modulo a prime not containing `m`. -/
  mem_of_forall_sub_mem : ∀ ⦃i : ℕ⦄, i ∈ Set.Ioo 0 p → ∀ (P : Ideal R) [P.IsPrime],
    (∀ y : R, (σ ^ i) y - y ∈ P) → m ∈ P

/-- The identity endomorphism is tame at every level `m` with exponent `1`. -/
theorem isTameAtLevel_id (m : R) : IsTameAtLevel (RingHom.id R) 1 m where
  map_level := rfl
  exists_dvd_sum_range_pow_sub_one := ⟨1, by simp⟩
  pow_eq_one := one_pow 1
  pos := one_pos
  mem_of_forall_sub_mem i hi _ _ _ := by
    have := hi.1
    have := hi.2
    omega

/-- An algebra automorphism `σ` of finite order of a field `L` over a commutative semiring `K` is
tame at level `1` with exponent `orderOf σ`. -/
theorem _root_.AlgEquiv.isTameAtLevel_orderOf {K L : Type*} [CommSemiring K] [Field L]
    [Algebra K L] (σ : L ≃ₐ[K] L) (hσ : IsOfFinOrder σ) :
    IsTameAtLevel (σ : L →+* L) (orderOf σ) 1 where
  map_level := map_one _
  exists_dvd_sum_range_pow_sub_one := ⟨0, by simp⟩
  pow_eq_one := by
    ext y
    simp [← AlgEquiv.coe_pow]
  pos := hσ.orderOf_pos
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

/-- **Galois descent at a prime away from the level.** If `σ` is tame at level `m`, `τ` is a
`σ`-semilinear map on an `R`-module `V` of period `p`, and `P` is a prime ideal with `m ∉ P`, then
some `r ∉ P` multiplies all of `V` into the `R`-span of the fixed points of `τ`. -/
theorem IsTameAtLevel.exists_smul_mem_span_fixedPoints {σ : R →+* R} {p : ℕ} {m : R}
    {V : Type*} [AddCommMonoid V] [Module R V] (h_tame : IsTameAtLevel σ p m)
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
    exact Finset.map_sum_range_eq_self_of_periodic τ.toAddMonoidHom (fun z ↦ (σ ^ z) a • τ^[z] v)
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
  refine ⟨∏ i ∈ range p, (σ ^ i) a, Finset.isFixedPt_prod_range_pow_apply h_tame.pow_eq_one a,
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
  have h_det : (∑ i : Fin k, s i • (G i).val).det ∈ P := by
    refine Matrix.det_sum_smul_mem_of_forall_det_mem fun f ↦ h_all _ ?_
    exact (hτ _).trans <| ext fun i j ↦ congrFun₂ ((hτ _).symm.trans (G (f j)).property) i j
  have h_pow : r ^ Fintype.card n ∈ P := by simpa [hG] using h_det
  exact P.primeCompl.pow_mem hr (Fintype.card n) h_pow

private lemma exists_fixed_eq_one_add_smul {n : Type*} [Fintype n] [DecidableEq n]
    {σ : R →+* R} {p : ℕ} {m : R} (h_tame : IsTameAtLevel σ p m)
    {c Y : Matrix n n R} (hY : c = 1 + m • Y) {τ : Matrix n n R →ₛₗ[σ] Matrix n n R}
    (hτ : ∀ v : Matrix n n R, τ v = c * v.map σ) (hτ_period : ∀ v : Matrix n n R, τ^[p] v = v) :
    ∃ g : Matrix n n R, τ g = g ∧ ∃ W : Matrix n n R, g = 1 + m • W := by
  obtain ⟨e, w, he⟩ := h_tame.exists_dvd_sum_range_pow_sub_one
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
    Finset.map_sum_range_eq_self_of_periodic τ.toAddMonoidHom (fun i ↦ τ^[i] (e • 1))
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

private lemma basicOpen_det_sub_smul_superset {n : Type*} [Fintype n] [DecidableEq n]
    {g v : Matrix n n R} {N : R} {M : Ideal R} [hM : M.IsPrime]
    (hN_mem : ∀ P : Ideal R, P.IsPrime → g.det ∉ P → N ∈ P)
    (hN_one : Ideal.Quotient.mk M N = 1) (hvM : v.det ∉ M) :
    PrimeSpectrum.basicOpen g.det ≤ PrimeSpectrum.basicOpen (g - N • (g - v)).det ∧
      ⟨M, hM⟩ ∈ PrimeSpectrum.basicOpen (g - N • (g - v)).det := by
  have hdet_mk (I : Ideal R) : Ideal.Quotient.mk I (g - N • (g - v)).det =
      ((1 - Ideal.Quotient.mk I N) • g.map (Ideal.Quotient.mk I) +
        Ideal.Quotient.mk I N • v.map (Ideal.Quotient.mk I)).det := by
    rw [RingHom.map_det, RingHom.mapMatrix_apply]
    congr 1
    ext i j
    simp only [Matrix.map_apply, Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply,
      smul_eq_mul, map_sub, map_mul]
    ring
  have hdet_of_zero {I : Ideal R} (h0 : Ideal.Quotient.mk I N = 0) :
      Ideal.Quotient.mk I (g - N • (g - v)).det = Ideal.Quotient.mk I g.det := by
    simpa [h0, RingHom.map_det, RingHom.mapMatrix_apply] using hdet_mk I
  have hdet_of_one {I : Ideal R} (h1 : Ideal.Quotient.mk I N = 1) :
      Ideal.Quotient.mk I (g - N • (g - v)).det = Ideal.Quotient.mk I v.det := by
    simpa [h1, RingHom.map_det, RingHom.mapMatrix_apply] using hdet_mk I
  refine ⟨?_, ?_⟩
  · rintro ⟨P, hP⟩ hgP
    have h0 := Ideal.Quotient.eq_zero_iff_mem.mpr (hN_mem P hP hgP)
    simpa [PrimeSpectrum.mem_basicOpen, ← Ideal.Quotient.eq_zero_iff_mem, hdet_of_zero h0] using hgP
  · simpa [PrimeSpectrum.mem_basicOpen, ← Ideal.Quotient.eq_zero_iff_mem, hdet_of_one hN_one]
      using hvM

/-- **Hilbert's Theorem 90 for `GL n` at congruence level `m` over an Artinian ring.** If `R` is
Artinian, `σ` is tame at level `m` with exponent `p`, and `c : GL n R` satisfies `c.val = 1 + m • Y`
and `MonoidHom.twistedNorm (GeneralLinearGroup.map σ) p c = 1`, then
`c * GeneralLinearGroup.map σ k = k` for some `k : GL n R` with `k.val = 1 + m • W`. -/
theorem IsTameAtLevel.exists_mul_map_eq_of_twistedNorm_eq_one {n : Type*} [Fintype n]
    [DecidableEq n] {σ : R →+* R} {p : ℕ} {m : R} (h_tame : IsTameAtLevel σ p m) [IsArtinianRing R]
    (c : GL n R) {Y : Matrix n n R} (hY : c.val = 1 + m • Y)
    (hc : MonoidHom.twistedNorm (GeneralLinearGroup.map σ) p c = 1) :
    ∃ k : GL n R, ∃ W : Matrix n n R,
      c * GeneralLinearGroup.map σ k = k ∧ k.val = 1 + m • W := by
  let τ : Matrix n n R →ₛₗ[σ] Matrix n n R := .mulLeft R c.val ∘ₛₗ σ.toSemilinearMap.mapMatrix
  have hτ_apply (v : Matrix n n R) : τ v = c.val * v.map σ := by simp [τ]
  have hτ (i : ℕ) (v : Matrix n n R) :
      τ^[i] v = (MonoidHom.twistedNorm (GeneralLinearGroup.map σ) i c).val * v.map (σ ^ i) := by
    induction i with
    | zero => simp
    | succ i ih =>
      rw [MonoidHom.twistedNorm_succ]
      simp [iterate_succ_apply', ih, hτ_apply, Matrix.map_mul, Matrix.map_map, mul_assoc, pow_succ']
  have hτ_period (v : Matrix n n R) : τ^[p] v = v := by simp [hτ, hc, h_tame.pow_eq_one]
  -- Pick a `τ`-fixed matrix `g ≡ 1 [mod m]` maximizing the basic open set `D(det g)`.
  obtain ⟨g, ⟨hg, W, hW⟩, hmax⟩ := exists_maximalFor_of_wellFoundedGT
    (fun g ↦ τ g = g ∧ ∃ W : Matrix n n R, g = 1 + m • W) (fun g ↦ PrimeSpectrum.basicOpen g.det)
    (exists_fixed_eq_one_add_smul h_tame hY hτ_apply hτ_period)
  suffices h_unit : IsUnit g.det from
    ⟨Matrix.GeneralLinearGroup.mk'' g h_unit, W, Units.ext hg, hW⟩
  by_contra h_nonunit
  obtain ⟨M, hM, hgM⟩ := exists_max_ideal_of_mem_nonunits h_nonunit
  have h_conj (i : ℕ) : (σ ^ i) g.det ∈ M := by
    have h_det : g.det =
        (MonoidHom.twistedNorm (GeneralLinearGroup.map σ) i c).val.det * (σ ^ i) g.det := by
      conv_lhs => rw [← iterate_fixed hg i, hτ, det_mul]
      rw [RingHom.map_det, RingHom.mapMatrix_apply]
    have h_unit : IsUnit (MonoidHom.twistedNorm (GeneralLinearGroup.map σ) i c).val.det := by simp
    rwa [h_det, M.unit_mul_mem_iff_mem h_unit] at hgM
  have hm_dvd : m ∣ 1 - g.det := by
    rw [hW, Matrix.det_one_add_smul, add_assoc, sub_add_cancel_left, dvd_neg]
    exact dvd_add (dvd_mul_left m _) ((dvd_pow_self m two_ne_zero).mul_left _)
  obtain ⟨N, hN_fixed, ⟨z, hz⟩, hN_one, hN_mem⟩ := exists_fixed_separating h_tame hm_dvd h_conj
  have hmM : m ∉ M := fun hm_mem ↦ by
    have hN_mem_M : N ∈ M := by simpa [hz] using M.mul_mem_right z hm_mem
    have hN_sub : N - 1 ∈ M := Ideal.Quotient.eq.mp (hN_one.trans (map_one _).symm)
    have h1 : (1 : R) ∈ M := by simpa using M.sub_mem hN_mem_M hN_sub
    exact hM.ne_top ((Ideal.eq_top_iff_one M).mpr h1)
  obtain ⟨v, hv, hvM⟩ := exists_fixed_det_notMem h_tame hτ_apply hτ_period M hmM
  have h_fixed : τ (g - N • (g - v)) = g - N • (g - v) := by simp [hg, hv, hN_fixed]
  have h_cong : g - N • (g - v) = 1 + m • (W - z • (g - v)) := by
    rw [hz, mul_smul, smul_sub m, ← add_sub_assoc, ← hW]
  have : M.IsPrime := hM.isPrime
  obtain ⟨h_le, h_mem⟩ := basicOpen_det_sub_smul_superset hN_mem hN_one hvM
  exact hmax ⟨h_fixed, _, h_cong⟩ h_le h_mem hgM

/-- **Hilbert's Theorem 90 for units at congruence level `m` over an Artinian ring.** If `R` is
Artinian, `σ` is tame at level `m` with exponent `p`, and `x : Rˣ` satisfies `m ∣ (x : R) - 1` and
`∏ i ∈ range p, (σ ^ i) x = 1`, then `x * Units.map (σ : R →* R) g = g` for some `g : Rˣ` with
`m ∣ (g : R) - 1`. -/
theorem IsTameAtLevel.exists_mul_map_eq_of_prod_eq_one {σ : R →+* R} {p : ℕ} {m : R}
    (h_tame : IsTameAtLevel σ p m) [IsArtinianRing R] {x : Rˣ} (hx_one : m ∣ (x : R) - 1)
    (hx_norm : ∏ i ∈ range p, (σ ^ i) (x : R) = 1) :
    ∃ g : Rˣ, m ∣ (g : R) - 1 ∧ x * Units.map (σ : R →* R) g = g := by
  obtain ⟨y, hy⟩ := hx_one
  let e : GL Unit R ≃* Rˣ := Units.mapEquiv (Matrix.uniqueRingEquiv (m := Unit) (A := R)).toMulEquiv
  let c : GL Unit R := e.symm x
  have he_map (u : GL Unit R) :
      e (GeneralLinearGroup.map σ u) = Units.map (σ : R →* R) (e u) := by
    ext
    simp [e]
  have hc_val : c.val = 1 + m • of fun _ _ ↦ y := by
    ext i j
    simpa [c, e] using eq_add_of_sub_eq' hy
  have hc_norm : MonoidHom.twistedNorm (GeneralLinearGroup.map σ) p c = 1 := by
    apply e.injective
    rw [map_one, ← MulEquiv.coe_toMonoidHom, MonoidHom.map_twistedNorm e.toMonoidHom he_map,
      MulEquiv.coe_toMonoidHom, e.apply_symm_apply]
    ext
    rw [Units.val_one, ← Units.coeHom_apply,
      MonoidHom.map_twistedNorm (Units.coeHom R) (τ' := (σ : R →* R)) (fun _ ↦ rfl),
      MonoidHom.twistedNorm_ringHom_eq_prod_pow]
    exact hx_norm
  obtain ⟨k, W, hk, hW⟩ := h_tame.exists_mul_map_eq_of_twistedNorm_eq_one c hc_val hc_norm
  refine ⟨e k, ?_, ?_⟩
  · have h_val : ((e k : Rˣ) : R) = 1 + m * W () () := by simp [e, hW]
    rw [h_val, add_sub_cancel_left]
    exact dvd_mul_right m _
  · simpa [c, he_map] using congrArg e hk

/-- **Surjectivity of the orbit product on `σ`-fixed units at congruence level `m` over a finite
ring.** If `R` is finite, `σ` is tame at level `m` with exponent `p`, and `x : Rˣ` is `σ`-fixed
with `m ∣ (x : R) - 1`, then `x = ∏ i ∈ range p, (σ ^ i) z` for a unit `z : Rˣ` with
`m ∣ (z : R) - 1` and `m ∣ ((z⁻¹ : Rˣ) : R) - 1`. -/
theorem IsTameAtLevel.exists_prod_range_pow_eq_of_finite {σ : R →+* R} {p : ℕ} {m : R}
    (h_tame : IsTameAtLevel σ p m) [Finite R] {x : Rˣ} (hσx : σ x = x)
    (hx_one : m ∣ (x : R) - 1) :
    ∃ z : Rˣ, m ∣ (z : R) - 1 ∧ m ∣ ((z⁻¹ : Rˣ) : R) - 1 ∧ ∏ i ∈ range p, (σ ^ i) (z : R) = x := by
  have hσ : σ ^ p = 1 := h_tame.pow_eq_one
  let H : Subgroup Rˣ :=
    ((Ideal.Quotient.mk (span {m})).toMonoidHom.comp (Units.coeHom R)).ker.copy
      {u | m ∣ (u : R) - 1} (by simp [Set.ext_iff, ← Ideal.Quotient.eq_zero_iff_dvd, sub_eq_zero])
  have mem_H {u : Rˣ} : u ∈ H ↔ m ∣ (u : R) - 1 := Iff.rfl
  have h_stable (i : ℕ) :
      Set.MapsTo (Units.map ((σ ^ i : R →+* R) : R →* R)) (H : Set Rˣ) (H : Set Rˣ) := by
    intro y hy
    rw [SetLike.mem_coe, mem_H, Units.coe_map]
    have h_dvd : (σ ^ i) m ∣ (σ ^ i) ((y : R) - 1) := map_dvd (σ ^ i) (mem_H.mp hy)
    simpa [iterate_fixed h_tame.map_level] using h_dvd
  let s (i : ℕ) : H →* H := (Units.map ((σ ^ i : R →+* R) : R →* R)).restrict (h_stable i)
  let norm : H →* H := (range p).prod s
  let cob : H →* H := s 0 / s 1
  -- `MonoidHom.restrict` applies `Units.map (σ ^ i)` to the underlying unit of `z : H`.
  have h_s_coe (i : ℕ) (z : H) : ((s i z : Rˣ) : R) = (σ ^ i) ((z : Rˣ) : R) := rfl
  have h_norm_coe (z : H) : ((norm z : Rˣ) : R) = ∏ i ∈ range p, (σ ^ i) ((z : Rˣ) : R) := by
    simp [norm, h_s_coe]
  have h_range : norm.range ≤ cob.ker := by
    rintro _ ⟨z, rfl⟩
    apply div_eq_one_of_eq
    ext
    simpa [h_s_coe, h_norm_coe] using
      (Finset.isFixedPt_prod_range_pow_apply hσ ((z : Rˣ) : R)).eq.symm
  have h_ker : norm.ker ≤ cob.range := by
    intro u hu
    have hu_norm : ∏ i ∈ range p, (σ ^ i) ((u : Rˣ) : R) = 1 := by
      rw [← h_norm_coe, MonoidHom.mem_ker.mp hu, OneMemClass.coe_one, Units.val_one]
    obtain ⟨g, hg, hgu⟩ := h_tame.exists_mul_map_eq_of_prod_eq_one (mem_H.mp u.property) hu_norm
    exact ⟨⟨g, mem_H.mpr hg⟩, div_eq_of_eq_mul'' (Subtype.ext hgu.symm)⟩
  have h_card : Nat.card cob.ker ≤ Nat.card norm.range :=
    calc
      Nat.card cob.ker = cob.range.index := Subgroup.index_range.symm
      _ ≤ norm.ker.index := Subgroup.index_antitone h_ker
      _ = Nat.card norm.range := Subgroup.index_ker norm
  have hx_fixed : (⟨x, mem_H.mpr hx_one⟩ : H) ∈ cob.ker :=
    div_eq_one_of_eq (Subtype.ext (Units.ext hσx.symm))
  obtain ⟨z, hz⟩ : ∃ z : H, norm z = ⟨x, mem_H.mpr hx_one⟩ :=
    (Subgroup.eq_of_le_of_card_ge h_range h_card).ge hx_fixed
  refine ⟨z.val, mem_H.mp z.property, mem_H.mp z⁻¹.property, ?_⟩
  rw [← h_norm_coe, hz]

end TauCeti.TameHilbert90
