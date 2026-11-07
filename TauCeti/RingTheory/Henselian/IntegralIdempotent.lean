/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.IntegralClosure.Algebra.Defs
import Mathlib.RingTheory.IntegralClosure.Algebra.Ideal
import Mathlib.RingTheory.Polynomial.Eisenstein.Distinguished
import Mathlib.RingTheory.Polynomial.UniversalFactorizationRing
import TauCeti.RingTheory.Henselian.Idempotent
import TauCeti.RingTheory.Henselian.Section

/-!
# Lifting idempotents in integral algebras over a Henselian pair

Let `(R, I)` be a Henselian pair and let `T` be an integral `R`-algebra (in particular, any
module-finite `R`-algebra). Reduction modulo `IT` restricts to a bijection between the idempotents
of `T` and the idempotents of `T ⧸ IT`
(`TauCeti.HenselianRing.bijOn_quotient_mk_map_isIdempotentElem`), establishing conditions (3) and
(4) of [Stacks Project, Lemma 15.11.6](https://stacks.math.columbia.edu/tag/09XI).

Uniqueness of lifts and the bootstrap case of a cyclic summand are proved directly from Hensel's
lemma in `TauCeti.RingTheory.Henselian.Idempotent` and used to establish lifting of étale sections
(`TauCeti.HenselianRing.comp_bijective`). Conversely, once `comp_bijective` is available, existence
of lifts for arbitrary integral algebras follows via the universal coprime factorization ring:
given `a ∈ T` with `a ^ 2 - a ∈ IT`, integrality over `I`
(`Polynomial.exists_monic_aeval_eq_zero_forall_mem_of_mem_map`) yields a monic polynomial
`q ∈ R[X]` distinguished at `I` that kills `a ^ 2 - a`. Then `q(X ^ 2 - X)` reduces modulo `I` to
the coprime product `X ^ d (X - 1) ^ d`, which lifts to a coprime factorization `g * h` in `R[X]`
and produces an idempotent `e ∈ R[a] ⊆ T` congruent to `a` modulo `IT`.

## Main results

* `TauCeti.HenselianRing.exists_isIdempotentElem_of_mul_sub_one_mem`: over a Henselian pair `(R, I)`
  and an integral `R`-algebra `T`, every `a : T` with `a * (a - 1) ∈ IT` lifts to an idempotent
  `e ∈ T` congruent to `a` modulo `IT`.
* `TauCeti.HenselianRing.existsUnique_isIdempotentElem_mk_map_eq`: every idempotent of `T ⧸ IT`
  lifts to a unique idempotent of `T`.
* `TauCeti.HenselianRing.bijOn_quotient_mk_map_isIdempotentElem`: the quotient map `T → T ⧸ IT`
  restricts to a bijection on idempotents (Stacks, Lemma 15.11.6 (09XI), `(1) ⇒ (3), (4)`).

## References

* [Stacks Project, Lemma 15.11.6](https://stacks.math.columbia.edu/tag/09XI)
-/

public section

open Polynomial

namespace TauCeti.HenselianRing

variable {R : Type*} [CommRing R]

/-- Over a Henselian pair `(R, I)` with `R ⧸ I` nontrivial, if `q ∈ R[X]` is monic of degree `d`
and reduces to `X ^ d` modulo `I`, then `q.comp (X ^ 2 - X)` factors in `R[X]` as a product `g * h`
of coprime polynomials lifting `X ^ d` and `(X - 1) ^ d`. -/
private theorem exists_mul_eq_comp_and_isCoprime [Nontrivial R] (I : Ideal R) [HenselianRing R I]
    [Nontrivial (R ⧸ I)] {q : R[X]} {d : ℕ} (hq_monic : q.Monic) (hq_deg : q.natDegree = d)
    (hq_map : q.map (Ideal.Quotient.mk I) = X ^ d) :
    ∃ g h : R[X], g * h = q.comp (X ^ 2 - X) ∧ IsCoprime g h ∧
      g.map (algebraMap R (R ⧸ I)) = X ^ d ∧
      h.map (algebraMap R (R ⧸ I)) = (X - 1) ^ d := by
  have hX2_monic : (X ^ 2 - X : R[X]).Monic :=
    monic_X_pow_sub (degree_X_le.trans_lt (by exact_mod_cast one_lt_two))
  have hX2_deg : (X ^ 2 - X : R[X]).natDegree = 2 := by
    rw [natDegree_sub_eq_left_of_natDegree_lt] <;> simp
  let P : R[X] := q.comp (X ^ 2 - X)
  have hP_monic : P.Monic := hq_monic.comp hX2_monic (by rw [hX2_deg]; omega)
  have hP_deg : P.natDegree = d + d := by
    rw [natDegree_comp_eq_of_mul_ne_zero (by simp [hq_monic.leadingCoeff, hX2_monic.leadingCoeff]),
      hq_deg, hX2_deg]
    omega
  have hP_map : P.map (algebraMap R (R ⧸ I)) = X ^ d * (X - 1) ^ d := by
    have hX2_fac : (X ^ 2 - X : (R ⧸ I)[X]) = X * (X - 1) := by ring
    rw [Ideal.Quotient.algebraMap_eq, Polynomial.map_comp, hq_map]
    simp only [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, X_pow_comp, hX2_fac,
      mul_pow]
  let pMonic : MonicDegreeEq R (d + d) := .mk P hP_monic hP_deg
  let f₁Bar : MonicDegreeEq (R ⧸ I) d := .mk (X ^ d) (monic_X_pow d) (natDegree_X_pow d)
  let f₂Bar : MonicDegreeEq (R ⧸ I) d := .mk ((X - 1) ^ d) ((monic_X_sub_C 1).pow d)
    (by
      rw [← C_1, (monic_X_sub_C (1 : R ⧸ I)).natDegree_pow, natDegree_X_sub_C, mul_one])
  have hcopBar : IsCoprime f₁Bar.1 f₂Bar.1 :=
    IsCoprime.pow (⟨1, -1, by ring⟩ : IsCoprime (X : (R ⧸ I)[X]) (X - 1))
  let φ₀ := (Polynomial.UniversalCoprimeFactorizationRing.homEquiv (R ⧸ I) d d rfl
    pMonic).symm ⟨(f₁Bar, f₂Bar), hP_map.symm, hcopBar⟩
  obtain ⟨φ, hφ⟩ := (comp_bijective I).2 φ₀
  let qLift := Polynomial.UniversalCoprimeFactorizationRing.homEquiv R d d rfl pMonic φ
  refine ⟨qLift.1.1.1, qLift.1.2.1, ?_, qLift.2.2, ?_, ?_⟩
  · simpa [pMonic, P] using qLift.2.1
  · have hc := Polynomial.UniversalCoprimeFactorizationRing.homEquiv_comp_fst R d d rfl
      pMonic φ (Ideal.Quotient.mkₐ R I)
    rw [hφ, Equiv.apply_symm_apply] at hc
    exact (congrArg Subtype.val hc).symm
  · have hc := Polynomial.UniversalCoprimeFactorizationRing.homEquiv_comp_snd R d d rfl
      pMonic φ (Ideal.Quotient.mkₐ R I)
    rw [hφ, Equiv.apply_symm_apply] at hc
    exact (congrArg Subtype.val hc).symm

/-- **Lifting idempotents in integral algebras over a Henselian pair.** Let `(R, I)` be a Henselian
pair and `T` an integral `R`-algebra (for instance, a module-finite `R`-algebra). Every element
`a : T` with `a * (a - 1) ∈ IT` lifts to an idempotent `e ∈ T` congruent to `a` modulo `IT`. -/
@[stacks 09XI "(1) ⇒ (3) and (4), existence of lifts"]
theorem exists_isIdempotentElem_of_mul_sub_one_mem (I : Ideal R) [HenselianRing R I]
    {T : Type*} [CommRing T] [Algebra R T] [Algebra.IsIntegral R T] {a : T}
    (ha : a * (a - 1) ∈ I.map (algebraMap R T)) :
    ∃ e : T, IsIdempotentElem e ∧ e - a ∈ I.map (algebraMap R T) := by
  nontriviality T
  have : Nontrivial R := RingHom.domain_nontrivial (algebraMap R T)
  have hI_ne : I ≠ ⊤ := fun htop ↦ by
    have hjac : I ≤ Ideal.jacobson ⊥ := by
      simpa only [Ideal.jacobson_bot] using (HenselianRing.jac (R := R) (I := I))
    rw [htop, top_le_iff, Ideal.jacobson_eq_top_iff] at hjac
    exact bot_ne_top hjac
  have : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hI_ne
  obtain ⟨q, hq_monic, hq_eval, hq_coeff⟩ :=
    Polynomial.exists_monic_aeval_eq_zero_forall_mem_of_mem_map (R := R) (I := I)
      (x := a ^ 2 - a) (by convert ha using 1; ring)
  have hd_pos : 0 < q.natDegree := Nat.pos_of_ne_zero fun h0 ↦ by
    simp [Polynomial.eq_one_of_monic_natDegree_zero hq_monic h0] at hq_eval
  have hq_map : q.map (Ideal.Quotient.mk I) = X ^ q.natDegree :=
    Polynomial.IsDistinguishedAt.map_eq_X_pow ⟨⟨fun hi ↦ hq_coeff _ hi.ne⟩, hq_monic⟩
  obtain ⟨g, h, hgh, ⟨u, v, huv⟩, hg_map, hh_map⟩ :=
    exists_mul_eq_comp_and_isCoprime I hq_monic rfl hq_map
  let e : T := aeval a (u * g)
  refine ⟨e, ?_, ?_⟩
  · have hsum1 : e + aeval a (v * h) = 1 := by
      simpa [e, map_add] using congrArg (aeval a) huv
    have hprod0 : aeval a g * aeval a h = 0 := by
      rw [← map_mul, hgh, aeval_comp, map_sub, map_pow, aeval_X, hq_eval]
    have he1 : e * aeval a (v * h) = 0 := by
      simp only [e, map_mul]
      linear_combination aeval a u * aeval a v * hprod0
    rw [IsIdempotentElem]
    linear_combination e * hsum1 - he1
  · let π : T →+* T ⧸ I.map (algebraMap R T) := Ideal.Quotient.mk (I.map (algebraMap R T))
    let ψ : R ⧸ I →+* T ⧸ I.map (algebraMap R T) :=
      Ideal.quotientMap _ (algebraMap R T) Ideal.le_comap_map
    have hπψ (p : R[X]) : π (aeval a p) = eval₂ ψ (π a) (p.map (algebraMap R (R ⧸ I))) := by
      rw [aeval_def, hom_eval₂, eval₂_map]
      rfl
    have ha₀ : π a * (π a - 1) = 0 := by
      rw [← map_one π, ← map_sub, ← map_mul]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr ha
    have hg₀ : π (aeval a g) = π a ^ q.natDegree := by
      rw [hπψ, hg_map, eval₂_X_pow]
    have hh₀ : π (aeval a h) = (π a - 1) ^ q.natDegree := by
      rw [hπψ, hh_map, eval₂_pow, eval₂_sub, eval₂_X, eval₂_one]
    obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hd_pos.ne'
    rw [hm] at hg₀ hh₀
    have h1 : (π a - 1) * π e = 0 := by
      simp only [e, map_mul, hg₀, pow_succ]
      linear_combination π (aeval a u) * π a ^ m * ha₀
    have h2 : π a * (1 - π e) = 0 := by
      have huv1 : π (aeval a (u * g + v * h)) = 1 := by rw [huv, map_one, map_one]
      have hvh : 1 - π e = π (aeval a v) * (π a - 1) ^ m.succ := by
        simp only [e, map_add, map_mul, hh₀] at huv1 ⊢
        linear_combination -huv1
      rw [hvh, pow_succ]
      linear_combination π (aeval a v) * (π a - 1) ^ m * ha₀
    apply Ideal.Quotient.eq.mp
    linear_combination -(h1 + h2)

/-- **Unique lifting of idempotents in integral algebras.** Over a Henselian pair `(R, I)` and an
integral `R`-algebra `T`, every idempotent of `T ⧸ IT` is the image of a unique idempotent of
`T`. -/
theorem existsUnique_isIdempotentElem_mk_map_eq (I : Ideal R) [HenselianRing R I]
    {T : Type*} [CommRing T] [Algebra R T] [Algebra.IsIntegral R T]
    {t : T ⧸ I.map (algebraMap R T)} (ht : IsIdempotentElem t) :
    ∃! e : T, IsIdempotentElem e ∧ Ideal.Quotient.mk (I.map (algebraMap R T)) e = t := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective t
  obtain ⟨e, he, hea⟩ := exists_isIdempotentElem_of_mul_sub_one_mem I (a := a)
    (Ideal.Quotient.eq_zero_iff_mem.mp (by rw [map_mul, map_sub, map_one, mul_sub, mul_one,
      ht.eq, sub_self]))
  refine ⟨e, ⟨he, Ideal.Quotient.eq.mpr hea⟩, fun e' ⟨he', h⟩ ↦ ?_⟩
  exact injOn_quotient_mk_map_isIdempotentElem I he' he (h.trans (Ideal.Quotient.eq.mpr hea).symm)

/-- **Bijection on idempotents for integral algebras over a Henselian pair.** For a Henselian pair
`(R, I)` and an integral `R`-algebra `T`, the quotient map `T → T ⧸ IT` restricts to a bijection
between the idempotents of `T` and those of `T ⧸ IT`. -/
@[stacks 09XI "(1) ⇒ (3) and (4)"]
theorem bijOn_quotient_mk_map_isIdempotentElem {T : Type*} [CommRing T] [Algebra R T]
    [Algebra.IsIntegral R T] (I : Ideal R) [HenselianRing R I] :
    Set.BijOn (Ideal.Quotient.mk (I.map (algebraMap R T)))
      {e | IsIdempotentElem e} {t | IsIdempotentElem t} :=
  ⟨fun _ he ↦ he.map _, injOn_quotient_mk_map_isIdempotentElem I,
    fun _ ht ↦ (existsUnique_isIdempotentElem_mk_map_eq I ht).exists⟩

end TauCeti.HenselianRing
