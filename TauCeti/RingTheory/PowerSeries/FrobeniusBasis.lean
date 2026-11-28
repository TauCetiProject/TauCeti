/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.PowerSeries.Expand
public import Mathlib.RingTheory.PowerSeries.PiTopology
public import Mathlib.RingTheory.PowerSeries.Substitution
public import TauCeti.RingTheory.PowerSeries.Cartier

import Mathlib.Algebra.CharP.Lemmas
import TauCeti.LinearAlgebra.SModEq.Basic
import TauCeti.LinearAlgebra.Submodule.CompleteFiltration
import TauCeti.RingTheory.AdicCompletion.Pi
import TauCeti.RingTheory.PowerSeries.AdicComplete
import TauCeti.RingTheory.PowerSeries.Dvd
import TauCeti.RingTheory.PowerSeries.Ideal
import TauCeti.RingTheory.PowerSeries.OneAddXPow
import TauCeti.RingTheory.PowerSeries.Substitution

/-!
# The Frobenius power basis of a power series ring

For a prime `p` and a commutative ring `R`, the Frobenius substitution
`φ f = f ((1 + X) ^ p - 1)` is an `R`-algebra endomorphism of `R⟦X⟧`. Through `φ` the power
series ring becomes an algebra over itself, `a • f = φ a * f`; this is not the ordinary
self-module structure. When `R` is `p`-adically complete, for instance over `ℤ_[p]`, over the
integers of a finite unramified extension of `ℚ_[p]`, or over `ZMod p`, this algebra is free of
rank `p` with basis `1, 1 + X, …, (1 + X) ^ (p - 1)`: every series has a unique expansion

  `f = ∑ i < p, (1 + X) ^ i * φ (a i)`.

This is the finite free algebra whose determinant norm and trace are Coleman's norm and trace
operators on `R⟦X⟧`.

The proof combines the shifted-basis Cartier equivalence `PowerSeries.expandOneAddXEquiv`
(`Cartier.lean`) with `TauCeti.IsCompleteFiltration.isUnit_one_add` for the `p`-adically
contractive perturbation `φ - expand p` on the coefficientwise `p`-adic filtration. (Over any
commutative ring `R`, `PowerSeries.frobeniusAssembly_injective` also holds under `IsHausdorff`
alone when `p` is a nonzerodivisor.)

## Main definitions

* `PowerSeries.frobeniusSubst R p`: the substitution `f ↦ f ((1 + X) ^ p - 1)`.
* `PowerSeries.frobeniusAlgebra R p`: `R⟦X⟧` as an algebra over itself through `φ`.
* `PowerSeries.frobeniusAssembly R p`: the `R`-linear map `a ↦ ∑ i, (1 + X) ^ i * φ (a i)`.
* `PowerSeries.frobeniusBasis R p`: the basis `(1 + X) ^ i`, `i < p`, of `R⟦X⟧` over itself
  through `φ`.
* `PowerSeries.frobeniusCoord R p`: the `i`-th coordinate map `R⟦X⟧ →ₗ[R] R⟦X⟧` in
  `frobeniusBasis R p`.

## Main results

* `PowerSeries.frobeniusSubst_eq_expand`, `PowerSeries.frobeniusSubst_sub_expand_mem_span_p`:
  `φ` agrees with `PowerSeries.expand p` modulo `(p)`, and equals it when `(p : S) = 0`.
* `PowerSeries.continuous_frobeniusSubst`: continuity of `φ` in `PowerSeries.WithPiTopology`.
* `PowerSeries.map_frobeniusAssembly`, `PowerSeries.map_frobeniusCoord`: compatibility with
  change of coefficients.
* `PowerSeries.exists_frobeniusAssembly_add_pow_mul`: every series is a Frobenius assembly up to a
  multiple of `p ^ r`.
* `PowerSeries.natCast_pow_dvd_frobeniusAssembly_iff`: if `p` is a nonzerodivisor, `p ^ r` divides
  a Frobenius assembly exactly when it divides every coordinate.
* `PowerSeries.frobeniusAssembly_bijective`, `PowerSeries.frobeniusAssembly_injective`,
  `PowerSeries.frobeniusAssembly_surjective`: bijectivity for any `p`-adically complete `R`, and
  injectivity under `IsHausdorff` when `p` is a nonzerodivisor.
* `PowerSeries.frobeniusSubst_injective`, `PowerSeries.frobeniusSubst_mem_span_p_pow_iff`:
  injectivity and congruence reflection of `φ` for `p`-adically complete `R`.
* `PowerSeries.coeff_frobeniusCoord_mem_span_pow_of_coeff_mem_span_pow`: explicit `p`-adic
  modulus of continuity for Frobenius coordinates.
* `PowerSeries.module_free_frobeniusAlgebra`, `PowerSeries.module_finite_frobeniusAlgebra`,
  `PowerSeries.finrank_frobeniusAlgebra`: `R⟦X⟧` is finite free of rank `p` over itself through
  `φ`.

## References

* R. F. Coleman, *Division values in local fields*, Invent. Math. 53 (1979), 91–116, §2.
* J. Coates and R. Sujatha, *Cyclotomic Fields and Zeta Values*, Springer (2006), §2.2.
* R. Sharifi, *Iwasawa Theory*, §5.4.
* J. Rodrigues Jacinto and C. Williams, *An introduction to p-adic L-functions*, Essential Number
  Theory 4 (2025), Lemma 10.8.
-/

public section

namespace PowerSeries

/-! ### The Frobenius substitution -/

variable {R : Type*} [CommRing R] (p : ℕ)

private theorem constantCoeff_one_add_X_pow_sub_one :
    constantCoeff ((1 + X : R⟦X⟧) ^ p - 1) = 0 := by
  simp

/-- The series `(1 + X) ^ p - 1` has zero constant coefficient, so it can be substituted. -/
theorem hasSubst_one_add_X_pow_sub_one : HasSubst ((1 + X : R⟦X⟧) ^ p - 1) :=
  HasSubst.of_constantCoeff_zero' (constantCoeff_one_add_X_pow_sub_one p)

variable (R) in
/-- The Frobenius substitution `f ↦ f ((1 + X) ^ p - 1)` on `R⟦X⟧`. It is an `R`-algebra map,
so it fixes the constants `C c`. -/
noncomputable def frobeniusSubst : R⟦X⟧ →ₐ[R] R⟦X⟧ :=
  substAlgHom (hasSubst_one_add_X_pow_sub_one (R := R) p)

theorem frobeniusSubst_apply (f : R⟦X⟧) :
    frobeniusSubst R p f = f.subst ((1 + X : R⟦X⟧) ^ p - 1) :=
  congrFun (coe_substAlgHom (hasSubst_one_add_X_pow_sub_one p)) f

@[simp]
theorem frobeniusSubst_X : frobeniusSubst R p X = (1 + X) ^ p - 1 :=
  substAlgHom_X _

@[simp]
theorem frobeniusSubst_C (c : R) : frobeniusSubst R p (C c) = C c :=
  (frobeniusSubst R p).commutes c

@[simp]
theorem frobeniusSubst_one_add_X : frobeniusSubst R p (1 + X) = (1 + X) ^ p := by
  simp

@[simp]
theorem frobeniusSubst_one_add_X_pow (n : ℕ) :
    frobeniusSubst R p ((1 + X) ^ n) = (1 + X) ^ (p * n) := by
  rw [map_pow, frobeniusSubst_one_add_X, ← pow_mul]

@[simp]
theorem constantCoeff_frobeniusSubst (f : R⟦X⟧) :
    constantCoeff (frobeniusSubst R p f) = constantCoeff f := by
  rw [frobeniusSubst_apply]
  exact (constantCoeff_subst_of_constantCoeff_zero (S := R)
    (constantCoeff_one_add_X_pow_sub_one p) f).trans (Algebra.algebraMap_self_apply _)

/-- The Frobenius substitution commutes with change of coefficients. -/
@[simp]
theorem map_frobeniusSubst {S : Type*} [CommRing S] (h : R →+* S) (f : R⟦X⟧) :
    map h (frobeniusSubst R p f) = frobeniusSubst S p (map h f) := by
  rw [frobeniusSubst_apply, frobeniusSubst_apply]
  have : map h ((1 + X : R⟦X⟧) ^ p - 1) = (1 + X) ^ p - 1 := by simp
  exact (map_subst (hasSubst_one_add_X_pow_sub_one p) f).trans (congrArg (subst · (map h f)) this)

/-- For prime `p`, `frobeniusSubst R p f` agrees with `PowerSeries.expand p` modulo `(p)`. -/
theorem frobeniusSubst_sub_expand_mem_span_p [Fact p.Prime] (f : R⟦X⟧) :
    frobeniusSubst R p f - expand p (Fact.out : p.Prime).ne_zero f ∈ Ideal.span {(p : R⟦X⟧)} := by
  have hp : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  rw [← pow_one (Ideal.span {(p : R⟦X⟧)}), ← map_natCast (C : R →+* R⟦X⟧),
    PowerSeries.mem_span_C_pow_iff]
  intro n
  rw [pow_one, frobeniusSubst_apply, expand_apply]
  simpa using PowerSeries.coeff_subst_sub_subst_mem_span_mul (r := (p : R)) (by simp)
    (by rw [map_pow, constantCoeff_X, zero_pow hp])
    (C_dvd_one_add_X_pow_sub_one_sub_X_pow (Fact.out : p.Prime)) ⊤ (fun _ _ ↦ trivial)

/-- If `p = 0` in `S`, the Frobenius substitution is the expansion `f ↦ f (X ^ p)`. -/
theorem frobeniusSubst_eq_expand [hp : Fact p.Prime] {S : Type*} [CommRing S]
    (hpS : (p : S) = 0) (f : S⟦X⟧) :
    frobeniusSubst S p f = expand p hp.out.ne_zero f := by
  obtain ⟨r, hr⟩ := exists_add_pow_prime_eq hp.out (1 : S⟦X⟧) X
  have hp' : (p : S⟦X⟧) = 0 := by rw [← map_natCast (C (R := S)), hpS, map_zero]
  rw [frobeniusSubst_apply, expand_apply, hr, hp']
  simp

section Topology

open scoped PowerSeries.WithPiTopology

/-- Frobenius substitution is continuous for the coefficientwise topology on `R⟦X⟧`. -/
theorem continuous_frobeniusSubst [TopologicalSpace R] [IsTopologicalRing R] :
    Continuous (frobeniusSubst R p) :=
  (Continuous.powerSeries_subst continuous_id continuous_const (fun _ ↦ by simp)).congr
    fun f ↦ (frobeniusSubst_apply p f).symm

end Topology

/-! ### The Frobenius scalar algebra -/

variable (R) in
/-- The power series ring as an algebra over itself through the Frobenius substitution:
`a • f = φ a * f`. This is not an instance: it differs from the ordinary self-module
structure, and is passed explicitly. -/
@[instance_reducible]
noncomputable def frobeniusAlgebra : Algebra R⟦X⟧ R⟦X⟧ :=
  (frobeniusSubst R p).toRingHom.toAlgebra

theorem algebraMap_frobeniusAlgebra :
    @algebraMap R⟦X⟧ R⟦X⟧ _ _ (frobeniusAlgebra R p) = (frobeniusSubst R p).toRingHom :=
  (rfl)

@[simp]
theorem algebraMap_frobeniusAlgebra_apply (a : R⟦X⟧) :
    @algebraMap R⟦X⟧ R⟦X⟧ _ _ (frobeniusAlgebra R p) a = frobeniusSubst R p a :=
  (rfl)

@[simp]
theorem frobeniusAlgebra_smul (a f : R⟦X⟧) :
    @HSMul.hSMul _ _ _ (@instHSMul _ _ (frobeniusAlgebra R p).toSMul) a f =
      frobeniusSubst R p a * f :=
  (rfl)

/-! ### Frobenius coordinates -/

variable (R) in
/-- The Frobenius coordinate assembly `a ↦ ∑ i < p, (1 + X) ^ i * φ (a i)`. -/
noncomputable def frobeniusAssembly : (Fin p → R⟦X⟧) →ₗ[R] R⟦X⟧ where
  toFun a := ∑ i : Fin p, (1 + X) ^ (i : ℕ) * frobeniusSubst R p (a i)
  map_add' a b := by simp [mul_add, Finset.sum_add_distrib]
  map_smul' c a := by simp [Finset.smul_sum]

theorem frobeniusAssembly_apply (a : Fin p → R⟦X⟧) :
    frobeniusAssembly R p a = ∑ i : Fin p, (1 + X) ^ (i : ℕ) * frobeniusSubst R p (a i) :=
  (rfl)

@[simp]
theorem frobeniusAssembly_single (i : Fin p) (a : R⟦X⟧) :
    frobeniusAssembly R p (Pi.single i a) = (1 + X) ^ (i : ℕ) * frobeniusSubst R p a := by
  classical
  rw [frobeniusAssembly_apply, Finset.sum_eq_single i (fun j _ hj ↦ by simp [hj]) (by simp)]
  simp

/-- The assembly is the combination `∑ i < p, a i • (1 + X) ^ i` for the Frobenius scalar
action `a • f = φ a * f`. -/
theorem frobeniusAssembly_eq_sum_smul (a : Fin p → R⟦X⟧) :
    frobeniusAssembly R p a = ∑ i : Fin p, @HSMul.hSMul _ _ _
      (@instHSMul _ _ (frobeniusAlgebra R p).toSMul) (a i) ((1 + X) ^ (i : ℕ)) := by
  rw [frobeniusAssembly_apply]
  exact Finset.sum_congr rfl fun i _ ↦ by rw [frobeniusAlgebra_smul, mul_comm]

/-- The Frobenius assembly commutes with change of coefficients. -/
@[simp]
theorem map_frobeniusAssembly {S : Type*} [CommRing S] (h : R →+* S) (a : Fin p → R⟦X⟧) :
    map h (frobeniusAssembly R p a) = frobeniusAssembly S p (fun i ↦ map h (a i)) := by
  simp [frobeniusAssembly_apply]

/-- The assembly is linear over the Frobenius scalars: multiplying every coordinate by `a`
multiplies the assembled series by `φ a`. -/
theorem frobeniusAssembly_mul (a : R⟦X⟧) (v : Fin p → R⟦X⟧) :
    frobeniusAssembly R p (fun i ↦ a * v i) = frobeniusSubst R p a * frobeniusAssembly R p v := by
  simp only [frobeniusAssembly_apply, map_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ ↦ by ring

/-! ### Reduction modulo `p` -/

/-- Reduction modulo `p` of the Frobenius assembly is the expanded assembly. -/
private theorem map_mk_frobeniusAssembly [Fact p.Prime] (a : Fin p → R⟦X⟧) :
    map (Ideal.Quotient.mk (Ideal.span {(p : R)})) (frobeniusAssembly R p a) =
      ∑ i : Fin p, (1 + X) ^ (i : ℕ) *
        expand p (Fact.out : p.Prime).ne_zero (map (Ideal.Quotient.mk _) (a i)) := by
  have hp : (p : R ⧸ Ideal.span {(p : R)}) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk _), Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_span_singleton_self _
  rw [map_frobeniusAssembly, frobeniusAssembly_apply]
  simp [frobeniusSubst_eq_expand p hp]

/-- **Coordinates modulo `p`.** Every series is a Frobenius assembly up to a multiple of `p`. -/
theorem exists_frobeniusAssembly_add_natCast_mul [Fact p.Prime] (f : R⟦X⟧) :
    ∃ a h, f = frobeniusAssembly R p a + p * h := by
  obtain ⟨b, hb⟩ := exists_sum_one_add_X_pow_mul_expand p (Fact.out : p.Prime).ne_zero
    (map (Ideal.Quotient.mk (Ideal.span {(p : R)})) f)
  choose a ha using fun i ↦ map_surjective _ Ideal.Quotient.mk_surjective (b i)
  obtain ⟨h, hh⟩ : (p : R⟦X⟧) ∣ f - frobeniusAssembly R p a := by
    rw [← map_natCast C, C_dvd_iff_map_mk_eq_zero, map_sub, map_mk_frobeniusAssembly, ← hb]
    simp [ha]
  exact ⟨a, h, by rw [← hh]; ring⟩

/-- **Coordinates modulo `p ^ r`.** Every series is a Frobenius assembly up to a multiple of
`p ^ r`. -/
theorem exists_frobeniusAssembly_add_pow_mul [Fact p.Prime] (r : ℕ) (f : R⟦X⟧) :
    ∃ a h, f = frobeniusAssembly R p a + (p : R⟦X⟧) ^ r * h := by
  induction r generalizing f with
  | zero => exact ⟨0, f, by simp⟩
  | succ r ih =>
    obtain ⟨a, h, rfl⟩ := ih f
    obtain ⟨b, k, rfl⟩ := exists_frobeniusAssembly_add_natCast_mul p h
    refine ⟨a + fun i ↦ (p : R⟦X⟧) ^ r * b i, k, ?_⟩
    rw [map_add, frobeniusAssembly_mul, map_pow, map_natCast]
    ring

/-- **Reflection of divisibility by `p`.** If `p` divides a Frobenius assembly, it divides every
coordinate. -/
theorem natCast_dvd_of_natCast_dvd_frobeniusAssembly [Fact p.Prime] {a : Fin p → R⟦X⟧}
    (ha : (p : R⟦X⟧) ∣ frobeniusAssembly R p a) (i : Fin p) : (p : R⟦X⟧) ∣ a i := by
  rw [← map_natCast C, C_dvd_iff_map_mk_eq_zero, map_mk_frobeniusAssembly] at ha
  rw [← map_natCast C, C_dvd_iff_map_mk_eq_zero]
  exact congrFun (eq_zero_of_sum_one_add_X_pow_mul_expand_eq_zero _ ha) i

/-- **Divisibility by powers of `p`.** If `p` is a nonzerodivisor of `R`, then `p ^ r` divides a
Frobenius assembly if and only if it divides every coordinate. -/
theorem natCast_pow_dvd_frobeniusAssembly_iff [Fact p.Prime] (hp : IsSMulRegular R (p : R))
    {r : ℕ} {a : Fin p → R⟦X⟧} :
    (p : R⟦X⟧) ^ r ∣ frobeniusAssembly R p a ↔ ∀ i, (p : R⟦X⟧) ^ r ∣ a i := by
  have hp' : IsSMulRegular R⟦X⟧ (p : R⟦X⟧) := by
    rw [← map_natCast C]
    exact isSMulRegular_C_iff.mpr hp
  refine ⟨fun ha ↦ ?_, fun ha ↦ ?_⟩
  · induction r generalizing a with
    | zero => simp
    | succ r ih =>
      intro i
      choose b hb using natCast_dvd_of_natCast_dvd_frobeniusAssembly p
        ((dvd_pow_self _ r.succ_ne_zero).trans ha)
      rw [show a = fun i ↦ (p : R⟦X⟧) * b i from funext hb, frobeniusAssembly_mul,
        map_natCast, pow_succ'] at ha
      obtain ⟨c, hc⟩ := ha
      obtain ⟨d, hd⟩ := ih (a := b) ⟨c, hp' (hc.trans (mul_assoc _ _ _))⟩ i
      exact ⟨d, by rw [hb i, hd, pow_succ', mul_assoc]⟩
  · choose c hc using ha
    rw [show a = fun i ↦ (p : R⟦X⟧) ^ r * c i from funext hc, frobeniusAssembly_mul, map_pow,
      map_natCast]
    exact dvd_mul_right _ _

/-! ### Exact coordinates -/

/-- The ideal of series whose constant coefficient lies in `pR`. -/
local notation "𝔍" => Ideal.comap (constantCoeff (R := R)) (Ideal.span {(p : R)})

private theorem natCast_mem : (p : R⟦X⟧) ∈ 𝔍 := by
  simp

private theorem natCast_pow_mul_mem (n : ℕ) (x : R⟦X⟧) : (p : R⟦X⟧) ^ n * x ∈ 𝔍 ^ n :=
  Ideal.mul_mem_right x _ (Ideal.pow_mem_pow (natCast_mem p) n)

/-- **Uniqueness of Frobenius coordinates.** If `R` is `p`-adically Hausdorff and `p` is a
nonzerodivisor of `R`, the Frobenius assembly is injective. -/
theorem frobeniusAssembly_injective [Fact p.Prime] [IsHausdorff (Ideal.span {(p : R)}) R]
    (hp : IsSMulRegular R (p : R)) : Function.Injective (frobeniusAssembly R p) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro a ha
  funext i
  refine (isHausdorff_comap_constantCoeff (Ideal.span {(p : R)})).haus _ fun n ↦ ?_
  -- Every coordinate of a vanishing assembly is divisible by every power of `p`.
  obtain ⟨c, hc⟩ := (natCast_pow_dvd_frobeniusAssembly_iff p hp (r := n)).mp
    (ha ▸ dvd_zero _) i
  rw [SModEq.ideal_smul_top_iff_sub_mem, sub_zero, hc]
  exact natCast_pow_mul_mem p n c

section Neumann

variable (R) in
private noncomputable def neumannStep [Fact p.Prime] : Module.End R (Fin p → R⟦X⟧) :=
  let e := expandOneAddXEquiv p (Fact.out : p.Prime).ne_zero R
  e.symm.toLinearMap.comp (frobeniusAssembly R p - e.toLinearMap)

private theorem neumannStep_apply [Fact p.Prime] (a : Fin p → R⟦X⟧) :
    neumannStep R p a =
      (expandOneAddXEquiv p (Fact.out : p.Prime).ne_zero R).symm
        (frobeniusAssembly R p a - expandOneAddXEquiv p (Fact.out : p.Prime).ne_zero R a) :=
  rfl

private theorem frobeniusAssembly_eq_expandOneAddXEquiv_add_neumannStep [Fact p.Prime]
    (a : Fin p → R⟦X⟧) :
    frobeniusAssembly R p a =
      expandOneAddXEquiv p (Fact.out : p.Prime).ne_zero R (a + neumannStep R p a) := by
  rw [map_add, neumannStep_apply,
    (expandOneAddXEquiv p (Fact.out : p.Prime).ne_zero R).apply_symm_apply]
  exact (add_sub_cancel _ _).symm

private theorem coeff_frobeniusSubst_sub_expand_mem [Fact p.Prime] (J : Ideal R) {g : R⟦X⟧}
    {n : ℕ} (hg : ∀ m ≤ n, coeff m g ∈ J) :
    coeff n (frobeniusSubst R p g - expand p (Fact.out : p.Prime).ne_zero g) ∈
      Ideal.span {(p : R)} * J := by
  have hp : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  rw [frobeniusSubst_apply, expand_apply]
  exact coeff_subst_sub_subst_mem_span_mul (by simp)
    (by rw [map_pow, constantCoeff_X, zero_pow hp])
    (C_dvd_one_add_X_pow_sub_one_sub_X_pow (Fact.out : p.Prime)) J hg

private theorem coeff_neumannStep_mem [Fact p.Prime] (J : Ideal R) {a : Fin p → R⟦X⟧} {n : ℕ}
    (ha : ∀ i : Fin p, ∀ m < p * (n + 1), coeff m (a i) ∈ J) (j : Fin p) :
    coeff n (neumannStep R p a j) ∈ Ideal.span {(p : R)} * J := by
  rw [neumannStep_apply]
  refine coeff_expandOneAddXEquiv_symm_mem (Fact.out : p.Prime).ne_zero
    (Ideal.span {(p : R)} * J) (fun s hs ↦ ?_) j
  rw [frobeniusAssembly_apply, expandOneAddXEquiv_apply, ← Finset.sum_sub_distrib, map_sum]
  refine Ideal.sum_mem _ fun i _ ↦ ?_
  rw [mul_comm ((1 + X : R⟦X⟧) ^ (i : ℕ)), ← sub_mul, coeff_mul]
  refine Ideal.sum_mem _ fun xy hxy ↦ Ideal.mul_mem_right _ _ ?_
  exact coeff_frobeniusSubst_sub_expand_mem p J
    fun m hm ↦ ha i m (by rw [Finset.mem_antidiagonal] at hxy; omega)

variable (R) in
private def coeffIdealFiltration (m : ℕ) : Submodule R (Fin p → R⟦X⟧) where
  carrier := {a | ∀ (i : Fin p) (n : ℕ), coeff n (a i) ∈ Ideal.span {(p : R)} ^ m}
  zero_mem' _ _ := by simp
  add_mem' ha hb i n := by
    rw [Pi.add_apply, map_add]
    exact add_mem (ha i n) (hb i n)
  smul_mem' c a ha i n := by
    rw [Pi.smul_apply, map_smul, smul_eq_mul]
    exact Ideal.mul_mem_left _ c (ha i n)

private theorem coeffIdealFiltration_zero : coeffIdealFiltration R p 0 = ⊤ :=
  Submodule.eq_top_iff'.mpr fun _ _ _ ↦ by simp [pow_zero]

private theorem isCompleteFiltration_coeffIdealFiltration
    [IsAdicComplete (Ideal.span {(p : R)}) R] :
    TauCeti.IsCompleteFiltration (coeffIdealFiltration R p) where
  antitone _ _ hmn _ hx i n := Ideal.pow_le_pow_right hmn (hx i n)
  eq_zero_of_forall_mem a hx := by
    have hzero : (fun x : Fin p × ℕ ↦ coeff x.2 (a x.1)) = 0 :=
      TauCeti.eq_zero_of_forall_pow_dvd (p : R) fun m ⟨i, n⟩ ↦ by
        simpa only [Ideal.span_singleton_pow, Ideal.mem_span_singleton] using hx m i n
    exact funext fun i ↦ PowerSeries.ext fun n ↦ congrFun hzero (i, n)
  exists_limit seq hseq := by
    obtain ⟨c, hc⟩ := TauCeti.exists_forall_pow_dvd_sub (p : R)
      (fun m (x : Fin p × ℕ) ↦ coeff x.2 (seq m x.1)) fun m ⟨i, n⟩ ↦ by
        simpa only [← map_sub, ← Pi.sub_apply, Ideal.span_singleton_pow,
          Ideal.mem_span_singleton] using hseq m i n
    refine ⟨fun i ↦ mk fun n ↦ c (i, n), fun m i n ↦ ?_⟩
    simpa only [coeffIdealFiltration, Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk,
      Set.mem_ofPred_eq, Pi.sub_apply, map_sub, coeff_mk, Ideal.span_singleton_pow,
      Ideal.mem_span_singleton] using hc m (i, n)

private theorem map_coeffIdealFiltration_neumannStep_le [Fact p.Prime] (m : ℕ) :
    (coeffIdealFiltration R p m).map (neumannStep R p) ≤ coeffIdealFiltration R p (m + 1) := by
  rintro _ ⟨a, ha, rfl⟩ i n
  rw [pow_succ']
  exact coeff_neumannStep_mem p (Ideal.span {(p : R)} ^ m) (fun j s _ ↦ ha j s) i

end Neumann

/-- **Frobenius coordinates.** If `R` is `p`-adically complete, every series is uniquely
`∑ i < p, (1 + X) ^ i * φ (a i)`. -/
theorem frobeniusAssembly_bijective [Fact p.Prime] [IsAdicComplete (Ideal.span {(p : R)}) R] :
    Function.Bijective (frobeniusAssembly R p) := by
  have hunit : IsUnit ((LinearMap.id : Module.End R (Fin p → R⟦X⟧)) + neumannStep R p) :=
    (isCompleteFiltration_coeffIdealFiltration (R := R) p).isUnit_one_add
      (coeffIdealFiltration_zero (R := R) p)
      (map_coeffIdealFiltration_neumannStep_le (R := R) p)
  have hbij : Function.Bijective
      ((LinearMap.id : Module.End R (Fin p → R⟦X⟧)) + neumannStep R p) :=
    (Module.End.isUnit_iff _).mp hunit
  refine ⟨fun a b hab ↦ hbij.1
      ((expandOneAddXEquiv p (Fact.out : p.Prime).ne_zero R).injective ?_), fun y ↦ ?_⟩
  · simpa only [LinearMap.add_apply, LinearMap.id_apply,
      ← frobeniusAssembly_eq_expandOneAddXEquiv_add_neumannStep] using hab
  · obtain ⟨a, ha⟩ := hbij.2 ((expandOneAddXEquiv p (Fact.out : p.Prime).ne_zero R).symm y)
    refine ⟨a, ?_⟩
    rw [frobeniusAssembly_eq_expandOneAddXEquiv_add_neumannStep]
    simpa only [LinearMap.add_apply, LinearMap.id_apply, LinearEquiv.apply_symm_apply] using
      congrArg (expandOneAddXEquiv p (Fact.out : p.Prime).ne_zero R) ha

/-- **Existence of Frobenius coordinates.** If `R` is `p`-adically complete, the Frobenius
assembly is surjective. -/
theorem frobeniusAssembly_surjective [Fact p.Prime] [IsAdicComplete (Ideal.span {(p : R)}) R] :
    Function.Surjective (frobeniusAssembly R p) :=
  (frobeniusAssembly_bijective p).surjective

/-! ### The Frobenius power basis -/

section Basis

variable [Fact p.Prime] [IsAdicComplete (Ideal.span {(p : R)}) R]

variable (R) in
/-- **The Frobenius power basis.** If `R` is `p`-adically complete, the series `(1 + X) ^ i`,
`i < p`, form a basis of `R⟦X⟧` as an algebra over itself through the Frobenius substitution
`f ↦ f ((1 + X) ^ p - 1)`. The module structure is passed explicitly, since it differs from the
ordinary self-module structure. -/
noncomputable def frobeniusBasis :
    @Module.Basis (Fin p) R⟦X⟧ R⟦X⟧ _ _ (frobeniusAlgebra R p).toModule :=
  letI : Module R⟦X⟧ R⟦X⟧ := (frobeniusAlgebra R p).toModule
  Module.Basis.mk (v := fun i : Fin p ↦ (1 + X) ^ (i : ℕ))
    (Fintype.linearIndependent_iff.mpr fun g hg ↦ by
      have h0 : frobeniusAssembly R p g = 0 := (frobeniusAssembly_eq_sum_smul p g).trans hg
      exact congrFun ((frobeniusAssembly_bijective p).injective (h0.trans (map_zero _).symm)))
    fun f _ ↦ (Submodule.mem_span_range_iff_exists_fun _).mpr <| by
      obtain ⟨a, rfl⟩ := frobeniusAssembly_surjective p f
      exact ⟨a, (frobeniusAssembly_eq_sum_smul p a).symm⟩

@[simp]
theorem frobeniusBasis_apply (i : Fin p) : frobeniusBasis R p i = (1 + X) ^ (i : ℕ) :=
  letI : Module R⟦X⟧ R⟦X⟧ := (frobeniusAlgebra R p).toModule
  Module.Basis.mk_apply _ _ i

/-- Assembling coordinates is the inverse of the coordinate map of the Frobenius basis. -/
theorem frobeniusBasis_equivFun_symm_apply (a : Fin p → R⟦X⟧) :
    (@Module.Basis.equivFun _ _ _ _ _ (frobeniusAlgebra R p).toModule _
      (frobeniusBasis R p)).symm a = frobeniusAssembly R p a := by
  let : Module R⟦X⟧ R⟦X⟧ := (frobeniusAlgebra R p).toModule
  simp only [Module.Basis.equivFun_symm_apply, frobeniusBasis_apply]
  exact (frobeniusAssembly_eq_sum_smul p a).symm

variable (R) in
/-- The `i`-th Frobenius coordinate `R⟦X⟧ →ₗ[R] R⟦X⟧` with respect to `frobeniusBasis R p`,
satisfying `f = ∑ i < p, (1 + X) ^ i * frobeniusSubst R p (frobeniusCoord R p i f)`. -/
@[expose]
noncomputable def frobeniusCoord (i : Fin p) : R⟦X⟧ →ₗ[R] R⟦X⟧ where
  toFun f :=
    @Module.Basis.repr (Fin p) R⟦X⟧ R⟦X⟧ _ _ (frobeniusAlgebra R p).toModule
      (frobeniusBasis R p) f i
  map_add' f g := by simp only [map_add, Finsupp.coe_add, Pi.add_apply]
  map_smul' c f := by
    have hcf : c • f = frobeniusSubst R p (C c) * f := by
      rw [frobeniusSubst_C, PowerSeries.smul_eq_C_mul]
    rw [hcf, RingHom.id_apply, ← frobeniusAlgebra_smul, LinearEquiv.map_smul,
      Finsupp.smul_apply, smul_eq_mul, PowerSeries.smul_eq_C_mul]

/-- The `i`-th coordinate of `f` in `frobeniusBasis R p` is `frobeniusCoord R p i f`. -/
@[simp]
theorem frobeniusBasis_repr_apply (f : R⟦X⟧) (i : Fin p) :
    @Module.Basis.repr (Fin p) R⟦X⟧ R⟦X⟧ _ _ (frobeniusAlgebra R p).toModule
        (frobeniusBasis R p) f i = frobeniusCoord R p i f :=
  rfl

/-- Every series is the assembly of its Frobenius coordinates:
`frobeniusAssembly R p (fun i ↦ frobeniusCoord R p i f) = f`. -/
@[simp]
theorem frobeniusAssembly_frobeniusCoord (f : R⟦X⟧) :
    frobeniusAssembly R p (fun i ↦ frobeniusCoord R p i f) = f := by
  let : Module R⟦X⟧ R⟦X⟧ := (frobeniusAlgebra R p).toModule
  rw [← frobeniusBasis_equivFun_symm_apply p]
  exact (@Module.Basis.equivFun _ _ _ _ _ (frobeniusAlgebra R p).toModule _
    (frobeniusBasis R p)).symm_apply_apply f

/-- **Frobenius basis expansion:** `∑ i < p, (1 + X) ^ i * φ(cᵢ(f)) = f`. -/
theorem sum_one_add_X_pow_mul_frobeniusSubst_frobeniusCoord (f : R⟦X⟧) :
    ∑ i : Fin p, (1 + X) ^ (i : ℕ) * frobeniusSubst R p (frobeniusCoord R p i f) = f :=
  frobeniusAssembly_frobeniusCoord p f

/-- Uniqueness of coordinates in the Frobenius basis expansion. -/
theorem frobeniusCoord_unique {a : Fin p → R⟦X⟧} {f : R⟦X⟧}
    (ha : frobeniusAssembly R p a = f) (i : Fin p) :
    frobeniusCoord R p i f = a i := by
  have h : (fun j ↦ frobeniusCoord R p j f) = a :=
    (frobeniusAssembly_bijective p).injective ((frobeniusAssembly_frobeniusCoord p f).trans ha.symm)
  exact congrFun h i

/-- The Frobenius coordinates of an assembly are the assembled coordinates. -/
@[simp]
theorem frobeniusCoord_frobeniusAssembly (a : Fin p → R⟦X⟧) (i : Fin p) :
    frobeniusCoord R p i (frobeniusAssembly R p a) = a i :=
  frobeniusCoord_unique p rfl i

/-- Extracting the `i`-th Frobenius coordinate from an assembled sum
`∑ j, (1 + X) ^ j * φ(a j)` recovers `a i`. -/
theorem frobeniusCoord_sum_one_add_X_pow_mul_frobeniusSubst (a : Fin p → R⟦X⟧) (i : Fin p) :
    frobeniusCoord R p i (∑ j : Fin p, (1 + X) ^ (j : ℕ) * frobeniusSubst R p (a j)) = a i :=
  frobeniusCoord_frobeniusAssembly p a i

/-- The Frobenius coordinates are linear over the Frobenius scalars: the coordinates of
`φ a * f` are `a` times the coordinates of `f`. -/
@[simp]
theorem frobeniusCoord_frobeniusSubst_mul (a f : R⟦X⟧) (i : Fin p) :
    frobeniusCoord R p i (frobeniusSubst R p a * f) = a * frobeniusCoord R p i f := by
  rw [← frobeniusBasis_repr_apply, ← frobeniusAlgebra_smul, LinearEquiv.map_smul,
    Finsupp.smul_apply, smul_eq_mul, frobeniusBasis_repr_apply]

/-- Frobenius coordinates of `(1 + X) ^ n` pick out residue `n % p` with `(1 + X) ^ (n / p)`. -/
@[simp]
theorem frobeniusCoord_one_add_X_pow (n : ℕ) (j : Fin p) :
    frobeniusCoord R p j ((1 + X : R⟦X⟧) ^ n) =
      if (j : ℕ) = n % p then (1 + X) ^ (n / p) else 0 := by
  refine frobeniusCoord_unique p
    (a := fun k : Fin p ↦ if (k : ℕ) = n % p then (1 + X) ^ (n / p) else 0) ?_ j
  let r : Fin p := ⟨n % p, Nat.mod_lt n (Fact.out : p.Prime).pos⟩
  have hne (k : Fin p) (hkr : k ≠ r) : (k : ℕ) ≠ n % p := fun h ↦ hkr (Fin.ext h)
  rw [frobeniusAssembly_apply, Finset.sum_eq_single r (fun k _ hkr ↦ by simp [hne k hkr]) (by simp)]
  simp [r, frobeniusSubst_one_add_X_pow, ← pow_add, Nat.mod_add_div]

/-- The Frobenius coordinates of `1 + X` are `1` at `i = 1` and `0` elsewhere. -/
@[simp]
theorem frobeniusCoord_one_add_X (i : Fin p) :
    frobeniusCoord R p i (1 + X) = if (i : ℕ) = 1 then 1 else 0 := by
  simpa [Nat.mod_eq_of_lt (Fact.out : p.Prime).one_lt,
    Nat.div_eq_of_lt (Fact.out : p.Prime).one_lt] using frobeniusCoord_one_add_X_pow (R := R) p 1 i

/-- The Frobenius coordinates of `1` are `1` at `i = 0` and `0` elsewhere. -/
@[simp]
theorem frobeniusCoord_one (i : Fin p) :
    frobeniusCoord R p i 1 = if (i : ℕ) = 0 then 1 else 0 := by
  simpa using frobeniusCoord_one_add_X_pow (R := R) p 0 i

/-- The Frobenius coordinates of `φ(a)` are `a` at `i = 0` and `0` elsewhere. -/
@[simp]
theorem frobeniusCoord_frobeniusSubst (a : R⟦X⟧) (i : Fin p) :
    frobeniusCoord R p i (frobeniusSubst R p a) = if (i : ℕ) = 0 then a else 0 := by
  simpa using frobeniusCoord_frobeniusSubst_mul p a 1 i

/-- For prime `p` over a `p`-adically complete ring `R`, `frobeniusSubst R p` is injective. -/
theorem frobeniusSubst_injective : Function.Injective (frobeniusSubst R p) := fun _ _ h ↦ by
  simpa using congrArg (frobeniusCoord R p ⟨0, (Fact.out : p.Prime).pos⟩) h

/-- Multiplying by a constant `C c` scales every Frobenius coordinate by `C c`. -/
@[simp]
theorem frobeniusCoord_C_mul (c : R) (f : R⟦X⟧) (i : Fin p) :
    frobeniusCoord R p i (C c * f) = C c * frobeniusCoord R p i f := by
  simpa only [frobeniusSubst_C] using frobeniusCoord_frobeniusSubst_mul p (C c) f i

/-- The Frobenius coordinates of a constant series `C c` are `C c` at `i = 0` and `0` elsewhere. -/
@[simp]
theorem frobeniusCoord_C (c : R) (i : Fin p) :
    frobeniusCoord R p i (C c) = if (i : ℕ) = 0 then C c else 0 := by
  simpa only [frobeniusSubst_C] using frobeniusCoord_frobeniusSubst p (C c) i

/-- For prime `p` over a `p`-adically complete ring `R`, Frobenius substitution preserves and
reflects membership in `(p) ^ k`. -/
theorem frobeniusSubst_mem_span_p_pow_iff (k : ℕ) {f : R⟦X⟧} :
    frobeniusSubst R p f ∈ Ideal.span {(p : R⟦X⟧)} ^ k ↔ f ∈ Ideal.span {(p : R⟦X⟧)} ^ k := by
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton, Ideal.mem_span_singleton]
  refine ⟨fun ⟨g, hg⟩ ↦ ⟨frobeniusCoord R p ⟨0, (Fact.out : p.Prime).pos⟩ g, ?_⟩,
    fun ⟨g, hg⟩ ↦ ⟨frobeniusSubst R p g, by rw [hg, map_mul, map_pow, map_natCast]⟩⟩
  simpa only [frobeniusCoord_frobeniusSubst, ↓reduceIte, ← map_natCast C, ← map_pow,
    frobeniusCoord_C_mul] using
      congrArg (frobeniusCoord R p ⟨0, (Fact.out : p.Prime).pos⟩) hg

/-- Coefficientwise change of base ring commutes with Frobenius coordinates. -/
theorem map_frobeniusCoord {S : Type*} [CommRing S] [IsAdicComplete (Ideal.span {(p : S)}) S]
    (φ : R →+* S) (f : R⟦X⟧) (i : Fin p) :
    map φ (frobeniusCoord R p i f) = frobeniusCoord S p i (map φ f) :=
  (frobeniusCoord_unique p (a := fun j ↦ map φ (frobeniusCoord R p j f)) (by
    simpa only [map_frobeniusAssembly] using
      congrArg (map φ) (frobeniusAssembly_frobeniusCoord p f)) i).symm

/-- **Explicit `(p)`-adic modulus of continuity for Frobenius coordinates.** If the first
`p ^ k * (n + 1)` coefficients of `f` lie in `(p) ^ k`, then so does
`coeff n (frobeniusCoord R p i f)`. -/
theorem coeff_frobeniusCoord_mem_span_pow_of_coeff_mem_span_pow :
    ∀ k : ℕ, ∀ {f : R⟦X⟧} {n : ℕ},
      (∀ s < p ^ k * (n + 1), coeff s f ∈ Ideal.span {(p : R)} ^ k) →
      ∀ i : Fin p, coeff n (frobeniusCoord R p i f) ∈ Ideal.span {(p : R)} ^ k
  | 0, _, _, _, _ => by simp
  | k + 1, f, n, hf, i => by
    let a : Fin p → R⟦X⟧ := fun j ↦ frobeniusCoord R p j f
    have hp : p ≠ 0 := (Fact.out : p.Prime).ne_zero
    have ha_eq : a = (expandOneAddXEquiv p hp R).symm f - neumannStep R p a :=
      eq_sub_of_add_eq <| (expandOneAddXEquiv p hp R).injective <| by
        rw [LinearEquiv.apply_symm_apply, ← frobeniusAssembly_eq_expandOneAddXEquiv_add_neumannStep]
        exact frobeniusAssembly_frobeniusCoord p f
    have hcoeff : coeff n (frobeniusCoord R p i f) =
        coeff n ((expandOneAddXEquiv p hp R).symm f i) - coeff n (neumannStep R p a i) := by
      rw [← map_sub, ← Pi.sub_apply, ← ha_eq]
    have hstep : p * (n + 1) ≤ p ^ (k + 1) * (n + 1) := by
      have hpow : 1 ≤ p ^ k := Nat.one_le_pow k p (Fact.out : p.Prime).pos
      rw [pow_succ']
      exact Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_right p hpow)
    rw [hcoeff]
    refine sub_mem
      (coeff_expandOneAddXEquiv_symm_mem hp _ (fun s hs ↦ hf s (lt_of_lt_of_le hs hstep)) i) ?_
    rw [pow_succ']
    exact coeff_neumannStep_mem p (Ideal.span {(p : R)} ^ k) (fun j m hm ↦
      coeff_frobeniusCoord_mem_span_pow_of_coeff_mem_span_pow k (fun s hs ↦
        Ideal.pow_le_pow_right (Nat.le_succ k) (hf s (lt_of_lt_of_le hs
          (by rw [pow_succ, mul_assoc]; exact Nat.mul_le_mul_left _ hm)))) j) i

/-- Under `frobeniusAlgebra R p`, `R⟦X⟧` is a free `R⟦X⟧`-module. -/
theorem module_free_frobeniusAlgebra :
    @Module.Free R⟦X⟧ R⟦X⟧ _ _ (frobeniusAlgebra R p).toModule :=
  @Module.Free.of_basis _ _ _ _ (frobeniusAlgebra R p).toModule _ (frobeniusBasis R p)

/-- Under `frobeniusAlgebra R p`, `R⟦X⟧` is a finite `R⟦X⟧`-module. -/
theorem module_finite_frobeniusAlgebra :
    @Module.Finite R⟦X⟧ R⟦X⟧ _ _ (frobeniusAlgebra R p).toModule :=
  @Module.Finite.of_basis _ _ _ _ _ (frobeniusAlgebra R p).toModule _ (frobeniusBasis R p)

/-- If `R` is nontrivial and `p`-adically complete, the power series ring has rank `p` over
itself through the Frobenius substitution. -/
theorem finrank_frobeniusAlgebra [Nontrivial R] :
    @Module.finrank R⟦X⟧ R⟦X⟧ _ _ (frobeniusAlgebra R p).toModule = p := by
  let : Module R⟦X⟧ R⟦X⟧ := (frobeniusAlgebra R p).toModule
  rw [Module.finrank_eq_card_basis (frobeniusBasis R p), Fintype.card_fin]

end Basis

/-! At `p = 2` the scalar `X` acts on `1` by `2 X + X ^ 2`, not by `X`. -/

example : frobeniusSubst ℤ 2 X = 2 * X + X ^ 2 := by
  rw [frobeniusSubst_X]
  ring

end PowerSeries
