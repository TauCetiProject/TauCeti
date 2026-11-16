/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.AdjoinRoot
public import TauCeti.RingTheory.Henselian.Idempotent
public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.IntegralClosure.Algebra.Ideal
import Mathlib.RingTheory.Polynomial.Eisenstein.Distinguished
import TauCeti.RingTheory.AdjoinRoot.Idempotent
import TauCeti.RingTheory.Henselian.Basic
import TauCeti.RingTheory.Henselian.Factorization
import TauCeti.RingTheory.Henselian.Radical
import TauCeti.RingTheory.Idempotents.Polynomial
import TauCeti.RingTheory.LocalRing.Module
import TauCeti.RingTheory.LocalRing.Monogenic

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
* `TauCeti.exists_isIdempotentElem_eq_of_isIntegral`: over a Henselian local ring, an idempotent
  image of an integral element of a possibly noncommutative algebra, under an algebra map killing
  the maximal ideal, is the image of an idempotent.
* `Ideal.henselianRing_map_of_isIntegral`: if `(R, I)` is Henselian and `S` is an integral
  `R`-algebra, then `(S, IS)` is Henselian.
* `TauCeti.isLocalRing_of_isDomain_of_isIntegral_of_henselianRing`: a domain integral over a
  henselian local ring is local.
* `TauCeti.isLocalRing_of_isIntegral_of_forall_isIdempotentElem`: a possibly noncommutative
  integral algebra over a henselian local ring is local if it is nontrivial and has only trivial
  idempotents.
* `TauCeti.IsIntegralClosure.isLocalRing`: any model of the integral closure of a henselian local
  ring in a domain is local.
* `TauCeti.HenselianLocalRing.of_finite`: a finite local algebra over a henselian local ring
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
      exact map_le_jacobson_of_isIntegral bot_le (by rw [jacobson_bot]; exact HenselianRing.jac))
    fun f hf s hs ↦ by
      have : Module.Finite S (AdjoinRoot f) := hf.finite_adjoinRoot
      have : Algebra.IsIntegral R (AdjoinRoot f) := Algebra.IsIntegral.trans S
      rw [map_map, ← IsScalarTower.algebraMap_eq] at hs ⊢
      exact exists_isIdempotentElem_sub_mem_map_of_isIntegral I hs

end Ideal

namespace TauCeti

/-- A nontrivial finite algebra over a henselian local ring is local if its only idempotents
are zero and one. -/
private theorem isLocalRing_of_finite_of_forall_isIdempotentElem (R S : Type*) [CommRing R]
    [IsLocalRing R] [HenselianRing R (IsLocalRing.maximalIdeal R)] [CommRing S] [Nontrivial S]
    [Algebra R S] [Module.Finite R S]
    (h : ∀ e : S, IsIdempotentElem e → e = 0 ∨ e = 1) : IsLocalRing S := by
  let J := (IsLocalRing.maximalIdeal R).map (algebraMap R S)
  have : IsArtinianRing (S ⧸ J) := by
    let := Ideal.Quotient.field (IsLocalRing.maximalIdeal R)
    have : Module.Finite (R ⧸ IsLocalRing.maximalIdeal R) (S ⧸ J) :=
      .of_restrictScalars_finite R _ _
    exact IsArtinianRing.of_finite (R ⧸ IsLocalRing.maximalIdeal R) _
  exact HenselianRing.isLocalRing_of_forall_isIdempotentElem J h

open scoped IsMulCommutative in
/-- A nontrivial, possibly noncommutative integral algebra over a henselian local ring is local
if its only idempotents are zero and one. -/
theorem isLocalRing_of_isIntegral_of_forall_isIdempotentElem (R S : Type*) [CommRing R]
    [IsLocalRing R] [HenselianRing R (IsLocalRing.maximalIdeal R)] [Ring S] [Nontrivial S]
    [Algebra R S] [Algebra.IsIntegral R S]
    (h : ∀ e : S, IsIdempotentElem e → e = 0 ∨ e = 1) : IsLocalRing S := by
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun s ↦ ?_
  let T := Algebra.adjoin R {s}
  have : Module.Finite R T :=
    Algebra.finite_adjoin_simple_of_isIntegral (Algebra.IsIntegral.isIntegral s)
  have : IsLocalRing T := isLocalRing_of_finite_of_forall_isIdempotentElem R T fun e he ↦
    (h e (he.map T.val)).imp Subtype.ext Subtype.ext
  exact (IsLocalRing.isUnit_or_isUnit_one_sub_self
    (⟨s, Algebra.self_mem_adjoin_singleton R s⟩ : T)).imp (·.map T.val) (·.map T.val)

/-- A domain integral over a henselian local ring is local. -/
theorem isLocalRing_of_isDomain_of_isIntegral_of_henselianRing (R S : Type*) [CommRing R]
    [IsLocalRing R] [HenselianRing R (IsLocalRing.maximalIdeal R)] [Ring S] [IsDomain S]
    [Algebra R S] [Algebra.IsIntegral R S] : IsLocalRing S :=
  isLocalRing_of_isIntegral_of_forall_isIdempotentElem R S fun _ he ↦
    IsIdempotentElem.iff_eq_zero_or_one.mp he

/-- Any model of the integral closure of a henselian local ring in a domain is local. -/
theorem IsIntegralClosure.isLocalRing (R S B : Type*) [CommRing R] [IsLocalRing R]
    [HenselianRing R (IsLocalRing.maximalIdeal R)] [CommRing S] [IsDomain S] [Algebra R S]
    [CommRing B] [Algebra R B] [Algebra B S] [IsScalarTower R B S]
    [IsIntegralClosure B R S] : IsLocalRing B := by
  have : IsDomain B := (_root_.IsIntegralClosure.algebraMap_injective B R S).isDomain _
  have := _root_.IsIntegralClosure.isIntegral_algebra R S (A := B)
  exact isLocalRing_of_isDomain_of_isIntegral_of_henselianRing R B

/-- The integral closure of a henselian local ring in a domain is local. -/
instance integralClosure.isLocalRing (R S : Type*) [CommRing R] [IsLocalRing R]
    [HenselianRing R (IsLocalRing.maximalIdeal R)] [CommRing S] [IsDomain S] [Algebra R S] :
    IsLocalRing (integralClosure R S) :=
  IsIntegralClosure.isLocalRing R S _

/-- A finite local algebra over a henselian local ring is henselian. -/
theorem HenselianLocalRing.of_finite (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
    [HenselianLocalRing R] [IsLocalRing S] [Module.Finite R S] : HenselianLocalRing S := by
  let I := (IsLocalRing.maximalIdeal R).map (algebraMap R S)
  have hrad : I.radical = IsLocalRing.maximalIdeal S := by
    obtain ⟨n, hn⟩ := IsLocalRing.exists_maximalIdeal_pow_le_map (R := R) (S := S)
    apply le_antisymm
    · apply (Ideal.IsPrime.radical_le_iff inferInstance).mpr
      exact Ideal.map_le_iff_le_comap.mpr
        (Ideal.comap_eq_maximalIdeal_of_isIntegral (IsLocalRing.maximalIdeal S)).ge
    · intro b hb
      exact ⟨n, hn (Ideal.pow_mem_pow hb n)⟩
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


section Noncommutative

open _root_.IsLocalRing (maximalIdeal)

variable {R B : Type*} [CommRing R] [IsLocalRing R] [HenselianRing R (maximalIdeal R)]
  [Ring B] [Algebra R B] {A : Type*} [Ring A] [Algebra R A]

/-- **Idempotents lift along an algebra map killing the maximal ideal of a Henselian local ring**,
one integral element at a time. Let `R` be a Henselian local ring and `π : A → B` a map of
`R`-algebras, not necessarily commutative, such that the maximal ideal of `R` acts by zero on `B`.
If `x : A` is integral over `R` and `π x` is idempotent, then `π x = π e` for an idempotent `e`
of `A`.

Let `F` be monic with `F(x) = 0`. Unless `π x` is trivial, the reduction `F₀` vanishes at `0` and
`1`, since `Q(b) b = Q(1) b` and `Q(b) (1 - b) = Q(0) (1 - b)` for an idempotent `b`. Lifting the
coprime factorization `F₀ = Xʳ H₀` with `X ∤ H₀` to `F = G H` with `U G + V H = 1`, the element
`U(x) G(x)` is idempotent and maps to `U(1) b = b`. -/
theorem exists_isIdempotentElem_eq_of_isIntegral (hB : ∀ r ∈ maximalIdeal R, algebraMap R B r = 0)
    (π : A →ₐ[R] B) {x : A} (hx : IsIntegral R x) (hb : IsIdempotentElem (π x)) :
    ∃ e : A, IsIdempotentElem e ∧ π e = π x := by
  -- The trivial idempotents lift to themselves.
  by_cases h0 : π x = 0
  · exact ⟨0, .zero, by rw [map_zero, h0]⟩
  by_cases h1 : 1 - π x = 0
  · exact ⟨1, .one, by rw [map_one, ← sub_eq_zero.mp h1]⟩
  let := Ideal.Quotient.field (maximalIdeal R)
  obtain ⟨F, hF, hFx⟩ := hx
  replace hFx : aeval x F = 0 := hFx
  have hFb : aeval (π x) F = 0 := by rw [aeval_algHom_apply, hFx, map_zero]
  -- Reduction modulo the maximal ideal commutes with evaluation.
  have hev (P : R[X]) (a : R) : (P.map (Ideal.Quotient.mk (maximalIdeal R))).eval
      (Ideal.Quotient.mk (maximalIdeal R) a) = Ideal.Quotient.mk (maximalIdeal R) (P.eval a) := by
    rw [eval_map, eval₂_at_apply]
  -- The reduction `F₀` of `F` vanishes at `0` and at `1`.
  set F₀ := F.map (Ideal.Quotient.mk (maximalIdeal R))
  have hroot {a : R} {c : B} (hc : c ≠ 0) (h : algebraMap R B (F.eval a) * c = 0) :
      F₀.IsRoot (Ideal.Quotient.mk (maximalIdeal R) a) := by
    rw [IsRoot, hev, Ideal.Quotient.eq_zero_iff_mem]
    exact IsLocalRing.mem_maximalIdeal_of_smul_eq_zero hc (by rwa [Algebra.smul_def])
  have hF0 : F₀.IsRoot 0 := by
    simpa using hroot (a := 0) h1 (by rw [← hb.aeval_mul_one_sub, hFb, zero_mul])
  have hF1 : F₀.IsRoot 1 := by
    simpa using hroot (a := 1) h0 (by rw [← hb.aeval_mul_self, hFb, zero_mul])
  -- Split off the exact power of `X`: `F₀ = Xʳ H₀` with `r ≥ 1` and `X ∤ H₀`, so that `Xʳ` and `H₀`
  -- are coprime and `H₀(1) = 0`.
  have hF₀ : F₀.Monic := hF.map _
  obtain ⟨H₀, hFH, hX⟩ := exists_eq_pow_rootMultiplicity_mul_and_not_dvd F₀ hF₀.ne_zero 0
  set r := rootMultiplicity 0 F₀
  have hr : 0 < r := (rootMultiplicity_pos hF₀.ne_zero).mpr hF0
  have hH₀ : H₀.Monic := ((monic_X_sub_C 0).pow r).of_mul_monic_left (hFH ▸ hF₀)
  have hcop : IsCoprime ((X - C 0) ^ r) H₀ :=
    ((irreducible_X_sub_C 0).coprime_iff_not_dvd.mpr hX).pow_left
  have hH₀1 : H₀.eval 1 = 0 := by
    have := hF1
    rw [IsRoot, hFH] at this
    simpa using this
  -- Lift the factorization along the Henselian hypothesis, with a Bézout identity.
  obtain ⟨G, H, -, -, hGH, ⟨U, V, hUV⟩, hG, hH⟩ :=
    (maximalIdeal R).exists_monic_mul_eq hF ((monic_X_sub_C 0).pow r) hH₀ hcop hFH
  refine ⟨aeval x (U * G), (IsIdempotentElem.of_mul_add (b := aeval x (V * H)) ?_ ?_).1, ?_⟩
  · rw [← map_mul, show U * G * (V * H) = U * V * (G * H) by ring, hGH, map_mul, hFx, mul_zero]
  · rw [← map_add, hUV, map_one]
  -- The image of `e` is `U(b) G(b) = U(b) b = U(1) b = b`.
  have hGb : aeval (π x) G = π x := by
    rw [Ideal.aeval_eq_of_map_eq hB (π x) (Q := X ^ r) (by simp [hG]), aeval_X_pow,
      ← Nat.sub_add_cancel hr, hb.pow_succ_eq]
  have hU1 : Ideal.Quotient.mk (maximalIdeal R) (U.eval 1) = 1 := by
    have := congr(eval 1 (map (Ideal.Quotient.mk (maximalIdeal R)) $hUV))
    rw [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_mul, hG, hH] at this
    have hU : eval 1 (map (Ideal.Quotient.mk (maximalIdeal R)) U) =
        Ideal.Quotient.mk (maximalIdeal R) (U.eval 1) := by simp
    simpa [hH₀1, hU] using this
  rw [← aeval_algHom_apply, map_mul, hGb, hb.aeval_mul_self,
    Ideal.algebraMap_eq_one_of_mk_eq_one hB hU1, one_mul]

end Noncommutative

end TauCeti
