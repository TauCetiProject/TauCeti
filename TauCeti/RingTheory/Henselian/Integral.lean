/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.AdjoinRoot
public import TauCeti.RingTheory.Henselian.Idempotent
import Mathlib.RingTheory.IntegralClosure.Algebra.Ideal
import Mathlib.RingTheory.Polynomial.Eisenstein.Distinguished
import TauCeti.RingTheory.AdjoinRoot.Idempotent
import TauCeti.RingTheory.Henselian.Basic
import TauCeti.RingTheory.Henselian.Factorization
import TauCeti.RingTheory.Henselian.Radical
import TauCeti.RingTheory.Idempotents.Polynomial

/-!
# Idempotents of integral algebras over a Henselian pair

Let `(R, I)` be a Henselian pair and let `S` be an integral `R`-algebra, for instance a finite
one. Then every idempotent of `S ⧸ IS` lifts to an idempotent of `S`
(`Ideal.exists_isIdempotentElem_sub_mem_map_of_isIntegral`), and the lift is unique. Conversely,
if `I` lies in the Jacobson radical and idempotents lift along `I` in every finite `R`-algebra,
then `(R, I)` is Henselian. This shows that `(S, IS)` is again a Henselian pair
for every integral `R`-algebra `S`, so reduction modulo `IS` is a bijection on idempotents
(`TauCeti.HenselianRing.bijOn_quotient_mk_isIdempotentElem`), and it characterises Henselian
pairs by their finite algebras, and by their integral algebras.

## Main results

* `Ideal.exists_isIdempotentElem_sub_mem_map_of_isIntegral`: over a Henselian pair `(R, I)`,
  idempotents of `S ⧸ IS` lift to `S` for every integral `R`-algebra `S`.
* `TauCeti.henselianRing_of_forall_exists_isIdempotentElem_adjoinRoot`: a pair `(R, I)` with `I`
  in the Jacobson radical is Henselian if idempotents lift along `I` in `R[X]/(f)` for every
  monic `f`.
* `Ideal.henselianRing_map_of_isIntegral`: if `(R, I)` is Henselian and `S` is an integral
  `R`-algebra, then `(S, IS)` is Henselian.
* `TauCeti.HenselianLocalRing.of_isIntegral`: an integral local algebra over a henselian local ring
  is henselian.
* `TauCeti.henselianRing_iff_forall_bijOn_isIdempotentElem` and
  `TauCeti.henselianRing_iff_forall_bijOn_isIdempotentElem_of_isIntegral`: `(R, I)` is Henselian
  if and only if reduction modulo `IS` is a bijection on idempotents for every finite, or every
  integral, `R`-algebra `S` in the universe of `R`.
* `TauCeti.henselianRing_iff_forall_henselianRing_map_of_isIntegral`: `(R, I)` is Henselian if and
  only if `(S, IS)` is Henselian for every integral `R`-algebra `S` in the universe of `R`.

## Implementation notes

To lift an idempotent `s` modulo `IS`: the element `s² - s` lies in `IS`, so it is a root of a
monic polynomial `q ≡ Xᵈ (mod I)`. Then `s` is a root of the monic polynomial
`P = q(X² - X) · (X² - X)`, which is `Xᵈ⁺¹ (X - 1)ᵈ⁺¹` modulo `I`. This factorization into coprime
monic polynomials lifts to `P = g h` with `a g + b h = 1`, and `a(s) g(s)` is the idempotent
lifting `s` (`Ideal.aeval_mul_sub_mem_map_of_add_eq_one`). The special case of an idempotent
cutting out a summand that is cyclic modulo `I`,
`TauCeti.HenselianRing.exists_isIdempotentElem_sub_mem_map`, has a direct proof by Hensel's
lemma; it is an input to the lifting of sections of étale algebras, on which the lifting of
factorizations used here rests.

For the converse, a simple root `a₀` modulo `I` of a monic `f` gives an idempotent of `R[X]/(f)`
modulo `I` cutting out the factor `R[X]/(X - a₀)`
(`TauCeti.exists_mul_self_sub_mem_of_isUnit_eval_derivative`), and its lift gives a root
`a ≡ a₀` of `f` (`Polynomial.Monic.exists_isRoot_of_isIdempotentElem`).

## References

* [Stacks Project, Lemma 15.11.6](https://stacks.math.columbia.edu/tag/09XI), conditions (1),
  (3) and (4).
* [Stacks Project, Lemma 15.11.8](https://stacks.math.columbia.edu/tag/09XK).
* [Stacks Project, Lemma 10.153.4](https://stacks.math.columbia.edu/tag/04GH).
-/

public section

universe u

open Polynomial

namespace TauCeti

variable {R : Type*} [CommRing R]

/-- **Henselian pairs from idempotents.** Let `I` be an ideal in the Jacobson radical of `R`. If for
every monic `f` over `R`, idempotents of `R[X]/(f)` modulo `I` lift to idempotents of `R[X]/(f)`,
then `(R, I)` is Henselian. -/
@[stacks 09XI "(3) ⇒ (1)"]
theorem henselianRing_of_forall_exists_isIdempotentElem_adjoinRoot {I : Ideal R}
    (hjac : I ≤ Ring.jacobson R)
    (H : ∀ f : R[X], f.Monic → ∀ s : AdjoinRoot f,
      s * s - s ∈ I.map (algebraMap R (AdjoinRoot f)) →
      ∃ e : AdjoinRoot f, IsIdempotentElem e ∧ e - s ∈ I.map (algebraMap R (AdjoinRoot f))) :
    HenselianRing R I where
  jac := hjac
  is_henselian f hf a₀ hfa₀ hunit := by
    set J := I.map (algebraMap R (AdjoinRoot f))
    obtain ⟨γ, hγ, hxγ, hrγ⟩ := exists_mul_self_sub_mem_of_isUnit_eval_derivative hfa₀ hunit
    -- The idempotent lift `e` of `γ` cuts out the factor `R[X]/(X - a₀)` of `R[X]/(f)`.
    obtain ⟨e, he, heγ⟩ := H f hf γ hγ
    refine hf.exists_isRoot_of_isIdempotentElem hjac he ?_ fun r hr ↦ hrγ r ?_
    · rw [← sub_add_cancel e γ, mul_add]
      exact add_mem (J.mul_mem_left _ heγ) hxγ
    · rw [← sub_sub_cancel e γ, smul_sub, Algebra.smul_def r (e - γ)]
      exact sub_mem hr (J.mul_mem_left _ heγ)

end TauCeti

namespace Ideal

variable {R : Type*} [CommRing R] (I : Ideal R)
  {S : Type*} [CommRing S] [Algebra R S] [HenselianRing R I] [Algebra.IsIntegral R S]

/-- **Idempotents lift along a Henselian pair in integral algebras.** If `(R, I)` is Henselian, `S`
is an integral `R`-algebra and `s : S` is idempotent modulo `IS`, then some idempotent of `S` is
congruent to `s` modulo `IS`. -/
@[stacks 09XI "(1) ⇒ (4), existence of lifts"]
theorem exists_isIdempotentElem_sub_mem_map_of_isIntegral {s : S}
    (hs : s * s - s ∈ I.map (algebraMap R S)) :
    ∃ e : S, IsIdempotentElem e ∧ e - s ∈ I.map (algebraMap R S) := by
  cases subsingleton_or_nontrivial R with
  | inl _ =>
    have := Module.subsingleton R S
    exact ⟨s, Subsingleton.elim _ _, Subsingleton.elim (s - s) 0 ▸ zero_mem _⟩
  | inr _ =>
  -- `s * s - s` is integral over `I`: it is a root of a monic `q ≡ Xᵈ` modulo `I`.
  obtain ⟨q, hq, hqs, hqI⟩ := Polynomial.exists_monic_aeval_eq_zero_forall_mem_of_mem_map hs
  set d := q.natDegree
  have hqmap : q.map (Ideal.Quotient.mk I) = X ^ d :=
    (IsDistinguishedAt.mk ⟨fun h ↦ hqI _ h.ne⟩ hq).map_eq_X_pow
  -- So `s` is a root of the monic `P = q(X² - X) (X² - X) ≡ Xᵈ⁺¹ (X - 1)ᵈ⁺¹` modulo `I`.
  set Q : R[X] := X * (X - C 1)
  have hQ : Q.Monic := monic_X.mul (monic_X_sub_C 1)
  have hQdeg : Q.natDegree ≠ 0 := by
    rw [monic_X.natDegree_mul (monic_X_sub_C 1), natDegree_X]
    omega
  set P := q.comp Q * Q
  have hP : P.Monic := (hq.comp hQ hQdeg).mul hQ
  have hPs : aeval s P = 0 := by
    have : aeval s Q = s * s - s := by simp [Q]; ring
    rw [aeval_mul, aeval_comp, this, hqs, zero_mul]
  have hPmap : P.map (Ideal.Quotient.mk I) = X ^ (d + 1) * (X - C 1) ^ (d + 1) := by
    have hQmap : Q.map (Ideal.Quotient.mk I) = X * (X - C 1) := by simp [Q]
    rw [Polynomial.map_mul, map_comp, hqmap, X_pow_comp, ← pow_succ, hQmap, mul_pow]
  have hcop : IsCoprime (X ^ (d + 1) : (R ⧸ I)[X]) ((X - C 1) ^ (d + 1)) :=
    IsCoprime.pow ⟨1, -1, by rw [map_one]; ring⟩
  obtain ⟨g, h, -, -, hgh, ⟨a, b, hab⟩, hgmap, hhmap⟩ :=
    I.exists_monic_mul_eq hP (monic_X_pow _) ((monic_X_sub_C _).pow _) hcop hPmap
  refine ⟨aeval s (a * g), ?_, aeval_mul_sub_mem_map_of_add_eq_one I hs hab hgmap hhmap⟩
  -- `a(s) g(s)` and `b(s) h(s)` are complementary idempotents, since `g h = P` kills `s`.
  have h1 : aeval s (a * g) + aeval s (b * h) = 1 := by rw [← map_add, hab, map_one]
  have hagbh : a * g * (b * h) = a * b * P := by rw [← hgh]; ring
  have h0 : aeval s (a * g) * aeval s (b * h) = 0 := by
    rw [← map_mul, hagbh, map_mul, hPs, mul_zero]
  exact (IsIdempotentElem.of_mul_add h0 h1).1

/-- **Henselian pairs are stable under integral extensions.** If `(R, I)` is Henselian and `S` is
an integral `R`-algebra, then `(S, IS)` is Henselian. -/
@[stacks 09XK]
instance henselianRing_map_of_isIntegral :
    HenselianRing S (I.map (algebraMap R S)) :=
  TauCeti.henselianRing_of_forall_exists_isIdempotentElem_adjoinRoot
    (by
      rw [← jacobson_bot]
      exact map_le_jacobson_bot_of_isIntegral (by rw [jacobson_bot]; exact HenselianRing.jac))
    fun f hf s hs ↦ by
      have : Module.Finite S (AdjoinRoot f) := hf.finite_adjoinRoot
      have : Algebra.IsIntegral R (AdjoinRoot f) := Algebra.IsIntegral.trans S
      rw [map_map, ← IsScalarTower.algebraMap_eq] at hs ⊢
      exact exists_isIdempotentElem_sub_mem_map_of_isIntegral I hs

end Ideal

namespace TauCeti

/-- An integral local algebra over a henselian local ring is henselian. -/
theorem HenselianLocalRing.of_isIntegral (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
    [HenselianLocalRing R] [IsLocalRing S] [Algebra.IsIntegral R S] : HenselianLocalRing S := by
  let I := (IsLocalRing.maximalIdeal R).map (algebraMap R S)
  have hrad : I.radical = IsLocalRing.maximalIdeal S := by
    apply le_antisymm
    · apply (Ideal.IsPrime.radical_le_iff inferInstance).mpr
      exact Ideal.map_le_iff_le_comap.mpr
        (Ideal.comap_eq_maximalIdeal_of_isIntegral (IsLocalRing.maximalIdeal S)).ge
    · rw [Ideal.radical_eq_sInf]
      refine le_sInf fun P ⟨hIP, hP⟩ ↦ ?_
      have : P.IsPrime := hP
      have hcomap : P.under R = IsLocalRing.maximalIdeal R :=
        ((inferInstance : (IsLocalRing.maximalIdeal R).IsMaximal).eq_of_le
          (Ideal.comap_ne_top (algebraMap R S) hP.ne_top)
          (Ideal.map_le_iff_le_comap.mp hIP)).symm
      have hmax : P.IsMaximal := Ideal.isMaximal_of_isIntegral_of_isMaximal_under P
        (by rw [hcomap]; infer_instance)
      exact (IsLocalRing.eq_maximalIdeal hmax).ge
  have : HenselianRing S I := inferInstance
  have : HenselianRing S I.radical := inferInstance
  rw [hrad] at this
  exact HenselianRing.henselianLocalRing S

/-- **Henselian pairs and idempotents of finite algebras.** A pair `(R, I)` is Henselian if and
only if, for every finite `R`-algebra `S` in the universe of `R`, the quotient map `S → S ⧸ IS`
restricts to a bijection between the idempotents of `S` and those of `S ⧸ IS`. -/
@[stacks 09XI "(1) ⇔ (3)"]
theorem henselianRing_iff_forall_bijOn_isIdempotentElem {R : Type u} [CommRing R] {I : Ideal R} :
    HenselianRing R I ↔ ∀ (S : Type u) [CommRing S] [Algebra R S] [Module.Finite R S],
      Set.BijOn (Ideal.Quotient.mk (I.map (algebraMap R S))) {e | IsIdempotentElem e}
        {t | IsIdempotentElem t} := by
  refine ⟨fun _ S _ _ _ ↦ HenselianRing.bijOn_quotient_mk_isIdempotentElem _,
    fun H ↦ henselianRing_of_forall_exists_isIdempotentElem_adjoinRoot ?_ fun f hf s hs ↦ ?_⟩
  · -- If `I ⊄ 𝔪` for a maximal ideal `𝔪`, then `0` and `1` in the field `R ⧸ 𝔪` both reduce to `0`.
    rw [← Ideal.jacobson_bot]
    refine le_sInf fun m ⟨_, hm⟩ ↦ ?_
    by_contra hIm
    obtain ⟨i, hi, him⟩ := Set.not_subset.mp hIm
    have : Nontrivial (R ⧸ m) := Ideal.Quotient.nontrivial_iff.mpr hm.ne_top
    obtain ⟨b, c, hc, hbc⟩ := hm.exists_inv him
    have htop : I.map (algebraMap R (R ⧸ m)) = ⊤ := by
      refine (Ideal.eq_top_iff_one _).mpr ?_
      have : algebraMap R (R ⧸ m) (b * i) = 1 := by
        rw [← map_one (algebraMap R (R ⧸ m)), ← hbc, map_add, Ideal.Quotient.algebraMap_eq,
          Ideal.Quotient.eq_zero_iff_mem.mpr hc, add_zero]
      exact this ▸ Ideal.mem_map_of_mem _ (I.mul_mem_left b hi)
    have := (H (R ⧸ m)).injOn (IsIdempotentElem.zero : IsIdempotentElem (0 : R ⧸ m))
      (IsIdempotentElem.one : IsIdempotentElem (1 : R ⧸ m))
      (Ideal.Quotient.eq.mpr (by rw [htop]; trivial))
    exact zero_ne_one this
  · have : Module.Finite R (AdjoinRoot f) := hf.finite_adjoinRoot
    obtain ⟨e, he, hes⟩ :=
      (H (AdjoinRoot f)).surjOn (Ideal.Quotient.isIdempotentElem_mk_iff.mpr hs)
    exact ⟨e, he, Ideal.Quotient.eq.mp hes⟩

/-- **Henselian pairs and idempotents of integral algebras.** A pair `(R, I)` is Henselian if and
only if, for every integral `R`-algebra `S` in the universe of `R`, the quotient map `S → S ⧸ IS`
restricts to a bijection between the idempotents of `S` and those of `S ⧸ IS`. -/
@[stacks 09XI "(1) ⇔ (4)"]
theorem henselianRing_iff_forall_bijOn_isIdempotentElem_of_isIntegral {R : Type u} [CommRing R]
    {I : Ideal R} :
    HenselianRing R I ↔ ∀ (S : Type u) [CommRing S] [Algebra R S] [Algebra.IsIntegral R S],
      Set.BijOn (Ideal.Quotient.mk (I.map (algebraMap R S))) {e | IsIdempotentElem e}
        {t | IsIdempotentElem t} :=
  ⟨fun _ _ _ _ _ ↦ HenselianRing.bijOn_quotient_mk_isIdempotentElem _,
    fun H ↦ henselianRing_iff_forall_bijOn_isIdempotentElem.mpr fun S _ _ _ ↦ H S⟩

/-- **Henselian pairs and integral extensions.** A pair `(R, I)` is Henselian if and only if
`(S, IS)` is Henselian for every integral `R`-algebra `S` in the universe of `R`; the converse
direction is the case `S = R`. -/
theorem henselianRing_iff_forall_henselianRing_map_of_isIntegral {R : Type u} [CommRing R]
    {I : Ideal R} :
    HenselianRing R I ↔ ∀ (S : Type u) [CommRing S] [Algebra R S] [Algebra.IsIntegral R S],
      HenselianRing S (I.map (algebraMap R S)) := by
  refine ⟨fun _ _ _ _ _ ↦ inferInstance, fun H ↦ ?_⟩
  have := H R
  rwa [Algebra.algebraMap_self, Ideal.map_id] at this

end TauCeti
