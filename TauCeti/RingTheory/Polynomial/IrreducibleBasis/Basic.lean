/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Polynomial.GaussLemma
public import Mathlib.RingTheory.Polynomial.Resultant.Basic
public import Mathlib.RingTheory.Polynomial.UniqueFactorization
public import Mathlib.RingTheory.UniqueFactorizationDomain.GCDMonoid

import Mathlib.Algebra.BigOperators.Associated
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.RingTheory.PrincipalIdealDomain
import TauCeti.RingTheory.Polynomial.Resultant.Discriminant

/-!
# Irreducible bases of finite families of polynomials

Let `D` be a unique factorization domain and `F` a finite family of polynomials in one
distinguished variable over `D`. An *irreducible basis* of `F` is a finite set `B` of pairwise
nonassociated irreducible polynomials of positive degree such that every member of `F` is a
constant times a product of powers of members of `B`, and every member of `B` divides some
nonzero member of `F`. The constant collects the unit and the irreducible factors that do not
involve the distinguished variable, that is, the content of the member up to a unit; the
product of powers is primitive. Zero members are reconstructed with the constant `0` and
contribute nothing to the basis.

The intended coefficient ring is `D = MvPolynomial (Fin n) R` over a field `R`, which is a
unique factorization domain by Mathlib's `MvPolynomial.uniqueFactorizationMonoid`. Projection
operators for cylindrical algebraic decomposition (McCallum's and Lazard's) are applied to an
irreducible basis of the input family together with the contents, and the signs and roots of
the original family are recovered from those of the basis and the contents. By Gauss's lemma
the basis stays irreducible over the fraction field of `D`, and its members stay pairwise
coprime there, so the product of the basis is squarefree over the fraction field. Pairwise
coprimality is the form in which resultants of distinct basis members are nonzero. Nonzero
discriminants additionally need separability, which follows from squarefreeness in
characteristic zero (as for `R = ℝ`) but can fail in positive characteristic, where an
irreducible member can be inseparable.

## Main definitions and results

* `Finset.IsIrreducibleBasis F B`: `B` is an irreducible basis of the finite family `F`.
* `Finset.exists_isIrreducibleBasis`: every finite family has an irreducible basis. It rests on
  `Polynomial.exists_eq_C_mul_prod_filter_factors`: a nonzero polynomial is a constant times the
  product of its irreducible factors of positive degree.
* `Finset.IsIrreducibleBasis.isPrimitive`, `Finset.IsIrreducibleBasis.isPrimitive_prod`: the
  members of the basis, and all products of their powers, are primitive.
* `Finset.IsIrreducibleBasis.exists_eq_C_content_mul_unit_mul_prod`: every member of the family
  is its content times a unit times a product of powers of the basis.
* `Finset.IsIrreducibleBasis.exists_associated_iff`: an irreducible polynomial of positive
  degree is associated to a member of the basis exactly when it divides a nonzero member of
  the family. Consequently any two irreducible bases agree up to associates
  (`Finset.IsIrreducibleBasis.exists_associated`, `Finset.IsIrreducibleBasis.exists_eq_C_mul`)
  and have the same cardinality (`Finset.IsIrreducibleBasis.card_eq`).
* `Finset.IsIrreducibleBasis.squarefree_prod`: the product of the basis is squarefree.
* `Finset.IsIrreducibleBasis.irreducible_map`, `Finset.IsIrreducibleBasis.isCoprime_map`,
  `Finset.IsIrreducibleBasis.squarefree_prod_map`: over the fraction field of `D`, the members
  of the basis are irreducible and pairwise coprime, and their product is squarefree.
* `Finset.IsIrreducibleBasis.resultant_ne_zero`, `Finset.IsIrreducibleBasis.discr_ne_zero`: the
  resultants of distinct members of the basis are nonzero, and in characteristic zero so are the
  discriminants of its members.
* `Finset.IsIrreducibleBasis.exists_associated_discr`,
  `Finset.IsIrreducibleBasis.exists_associated_resultant`: the discriminants and pairwise
  resultants of one irreducible basis are associated to those of any other.
* `Finset.IsIrreducibleBasis.isRoot_map_iff`: after a specialization `φ : D →+* A` into a
  domain under which a member `f` of the family does not vanish, the roots of the specialized
  `f` are exactly the roots of the specialized basis members dividing `f`.

## References

* S. McCallum, *An improved projection operation for cylindrical algebraic decomposition*, in
  *Quantifier Elimination and Cylindrical Algebraic Decomposition*, Springer (1998), 242–268.
* S. McCallum, A. Parusiński, L. Paunescu, *Validity proof of Lazard's method for CAD
  construction*, Journal of Symbolic Computation 92 (2019), 52–69.
-/

public section

open Polynomial

namespace Finset

section Defs

variable {D : Type*} [CommRing D]

/-- `B` is an irreducible basis of the finite family `F` of polynomials over `D`: its members
are pairwise nonassociated irreducible polynomials of positive degree, every member of `F` is a
constant times a product of powers of members of `B`, and every member of `B` divides a nonzero
member of `F`. -/
structure IsIrreducibleBasis (F B : Finset D[X]) : Prop where
  /-- Every member of the basis is irreducible. -/
  irreducible : ∀ b ∈ B, Irreducible b
  /-- Every member of the basis has positive degree. -/
  natDegree_pos : ∀ b ∈ B, 0 < b.natDegree
  /-- Distinct members of the basis are not associated. -/
  eq_of_associated : ∀ b ∈ B, ∀ b' ∈ B, Associated b b' → b = b'
  /-- Every member of the family is a constant times a product of powers of the basis. -/
  exists_eq_C_mul_prod : ∀ f ∈ F, ∃ (c : D) (e : D[X] → ℕ), f = C c * ∏ b ∈ B, b ^ e b
  /-- Every member of the basis divides a nonzero member of the family. -/
  exists_dvd : ∀ b ∈ B, ∃ f ∈ F, f ≠ 0 ∧ b ∣ f

end Defs

variable {D : Type*} [CommRing D] {F B B' : Finset D[X]} {b b' : D[X]}

namespace IsIrreducibleBasis

/-- Roots of a specialized member of the family are the roots of the specialized members of
the basis dividing it, provided the specialization of the member does not vanish. -/
theorem isRoot_map_iff (hB : F.IsIrreducibleBasis B) {f : D[X]} (hf : f ∈ F) {A : Type*}
    [CommRing A] [IsDomain A] (φ : D →+* A) (hφ : f.map φ ≠ 0) (t : A) :
    (f.map φ).IsRoot t ↔ ∃ b ∈ B, b ∣ f ∧ (b.map φ).IsRoot t := by
  refine ⟨fun ht ↦ ?_, fun ⟨b, _, hbf, hbt⟩ ↦ hbt.dvd (Polynomial.map_dvd φ hbf)⟩
  obtain ⟨c, e, rfl⟩ := hB.exists_eq_C_mul_prod f hf
  have hc : φ c ≠ 0 := by rintro hc; simp [Polynomial.map_mul, hc] at hφ
  simp only [Polynomial.map_mul, map_C, Polynomial.map_prod, Polynomial.map_pow, IsRoot,
    eval_mul, eval_C, eval_prod, eval_pow, mul_eq_zero, hc, false_or,
    Finset.prod_eq_zero_iff, pow_eq_zero_iff', ne_eq] at ht
  obtain ⟨b, hb, hbt, he⟩ := ht
  exact ⟨b, hb, ((dvd_pow_self b he).trans
    (dvd_prod_of_mem (fun b ↦ b ^ e b) hb)).mul_left _, hbt⟩

variable [IsDomain D]

/-- The members of an irreducible basis are primitive. -/
theorem isPrimitive (hB : F.IsIrreducibleBasis B) (hb : b ∈ B) : b.IsPrimitive :=
  (hB.irreducible b hb).isPrimitive (hB.natDegree_pos b hb).ne'

variable [UniqueFactorizationMonoid D]

/-- Every product of powers of the members of an irreducible basis is primitive, so the
constant in `exists_eq_C_mul_prod` is the content of the member up to a unit. -/
theorem isPrimitive_prod (hB : F.IsIrreducibleBasis B) (e : D[X] → ℕ) :
    (∏ b ∈ B, b ^ e b).IsPrimitive := by
  let := Classical.arbitrary (NormalizedGCDMonoid D)
  refine Finset.prod_induction _ IsPrimitive (fun _ _ ↦ IsPrimitive.mul) isPrimitive_one
    fun b hb ↦ ?_
  induction e b with
  | zero => simp
  | succ n ih => simpa [pow_succ] using ih.mul (hB.isPrimitive hb)

/-- Every member of the family is its content, times a unit, times a product of powers of the
members of an irreducible basis. -/
theorem exists_eq_C_content_mul_unit_mul_prod [NormalizedGCDMonoid D]
    (hB : F.IsIrreducibleBasis B) {f : D[X]} (hf : f ∈ F) :
    ∃ (u : Dˣ) (e : D[X] → ℕ), f = C (f.content * u) * ∏ b ∈ B, b ^ e b := by
  obtain ⟨c, e, rfl⟩ := hB.exists_eq_C_mul_prod f hf
  have hc := associated_content_C_mul c (∏ b ∈ B, b ^ e b)
  rw [(hB.isPrimitive_prod e).content_eq_one, mul_one] at hc
  obtain ⟨u, hu⟩ := hc.symm
  exact ⟨u⁻¹, e, by rw [← hu, Units.mul_inv_cancel_right]⟩

/-- The product of the members of an irreducible basis is squarefree. -/
theorem squarefree_prod (hB : F.IsIrreducibleBasis B) : Squarefree (∏ b ∈ B, b) :=
  Finset.squarefree_prod_of_pairwise_isCoprime
    (fun b hb b' hb' hne ↦ (hB.irreducible b hb).isRelPrime_iff_not_dvd.2 fun h ↦ hne <|
      hB.eq_of_associated b hb b' hb' <|
        (hB.irreducible b hb).associated_of_dvd (hB.irreducible b' hb') h)
    fun b hb ↦ (hB.irreducible b hb).squarefree

/-- An irreducible polynomial of positive degree is associated to a member of an irreducible
basis of `F` exactly when it divides a nonzero member of `F`. -/
theorem exists_associated_iff (hB : F.IsIrreducibleBasis B) {q : D[X]} (hq : Irreducible q)
    (hdeg : 0 < q.natDegree) : (∃ b ∈ B, Associated q b) ↔ ∃ f ∈ F, f ≠ 0 ∧ q ∣ f := by
  refine ⟨fun ⟨b, hb, hqb⟩ ↦ ?_, fun ⟨f, hf, hf0, hqf⟩ ↦ ?_⟩
  · obtain ⟨f, hf, hf0, hbf⟩ := hB.exists_dvd b hb
    exact ⟨f, hf, hf0, hqb.dvd.trans hbf⟩
  obtain ⟨c, e, rfl⟩ := hB.exists_eq_C_mul_prod f hf
  have hc : c ≠ 0 := by rintro rfl; simp at hf0
  have hq' := UniqueFactorizationMonoid.irreducible_iff_prime.1 hq
  rcases hq'.dvd_or_dvd hqf with h | h
  · have := natDegree_le_of_dvd h (C_ne_zero.2 hc)
    rw [natDegree_C] at this
    omega
  obtain ⟨b, hb, hqb⟩ := (hq'.dvd_finsetProd_iff _).1 h
  exact ⟨b, hb, hq.associated_of_dvd (hB.irreducible b hb) (hq'.dvd_of_dvd_pow hqb)⟩

/-- Irreducible bases of the same family agree up to associates. -/
theorem exists_associated (hB : F.IsIrreducibleBasis B) (hB' : F.IsIrreducibleBasis B')
    (hb : b ∈ B) : ∃ b' ∈ B', Associated b b' :=
  (hB'.exists_associated_iff (hB.irreducible b hb) (hB.natDegree_pos b hb)).2
    (hB.exists_dvd b hb)

/-- Each member of an irreducible basis is a unit multiple of a member of any other irreducible
basis of the same family. -/
theorem exists_eq_C_mul (hB : F.IsIrreducibleBasis B) (hB' : F.IsIrreducibleBasis B')
    (hb : b ∈ B) : ∃ b' ∈ B', ∃ r : D, IsUnit r ∧ b = C r * b' := by
  obtain ⟨b', hb', hbb'⟩ := hB.exists_associated hB' hb
  obtain ⟨u, hu⟩ := hbb'.symm
  obtain ⟨r, hr, hru⟩ := Polynomial.isUnit_iff.1 u.isUnit
  exact ⟨b', hb', r, hr, by rw [← hu, ← hru, mul_comm]⟩

/-- Irreducible bases of the same family have the same number of members. -/
theorem card_eq (hB : F.IsIrreducibleBasis B) (hB' : F.IsIrreducibleBasis B') :
    B.card = B'.card := by
  classical
  have hinj {B : Finset D[X]} (hB : F.IsIrreducibleBasis B) : Set.InjOn Associates.mk B :=
    fun b hb b' hb' h ↦ hB.eq_of_associated b hb b' hb' (Associates.mk_eq_mk_iff_associated.1 h)
  have himage : B.image Associates.mk = B'.image Associates.mk := by
    ext a
    simp only [mem_image]
    constructor
    · rintro ⟨b, hb, rfl⟩
      obtain ⟨b', hb', h⟩ := hB.exists_associated hB' hb
      exact ⟨b', hb', (Associates.mk_eq_mk_iff_associated.2 h).symm⟩
    · rintro ⟨b', hb', rfl⟩
      obtain ⟨b, hb, h⟩ := hB'.exists_associated hB hb'
      exact ⟨b, hb, (Associates.mk_eq_mk_iff_associated.2 h).symm⟩
  rw [← card_image_of_injOn (hinj hB), ← card_image_of_injOn (hinj hB'), himage]

/-- The discriminant of a member of an irreducible basis is associated to the discriminant of a
member of any other irreducible basis of the same family. -/
theorem exists_associated_discr (hB : F.IsIrreducibleBasis B) (hB' : F.IsIrreducibleBasis B')
    (hb : b ∈ B) : ∃ c ∈ B', Associated b.discr c.discr := by
  obtain ⟨c, hc, r, hr, rfl⟩ := hB.exists_eq_C_mul hB' hb
  refine ⟨c, hc, ?_⟩
  rw [TauCeti.discr_C_mul _ hr.ne_zero]
  exact associated_unit_mul_left _ _ (hr.pow _)

/-- The resultant of two distinct members of an irreducible basis is associated to the resultant
of two distinct members of any other irreducible basis of the same family. -/
theorem exists_associated_resultant (hB : F.IsIrreducibleBasis B)
    (hB' : F.IsIrreducibleBasis B') (hb : b ∈ B) (hb' : b' ∈ B) (hne : b ≠ b') :
    ∃ c ∈ B', ∃ c' ∈ B', c ≠ c' ∧ Associated (resultant b b') (resultant c c') := by
  obtain ⟨c, hc, r, hr, rfl⟩ := hB.exists_eq_C_mul hB' hb
  obtain ⟨c', hc', r', hr', rfl⟩ := hB.exists_eq_C_mul hB' hb'
  -- distinct members of `B` are not associated, so neither are the members of `B'` they are
  -- unit multiples of
  have hne' : c ≠ c' := by
    rintro rfl
    exact hne <| hB.eq_of_associated _ hb _ hb' <|
      (associated_unit_mul_left _ _ (isUnit_C.2 hr)).trans
        (associated_unit_mul_right _ _ (isUnit_C.2 hr'))
  refine ⟨c, hc, c', hc', hne', ?_⟩
  rw [natDegree_C_mul_of_isUnit hr, natDegree_C_mul_of_isUnit hr', resultant_C_mul_left,
    resultant_C_mul_right, ← mul_assoc]
  exact associated_unit_mul_left _ _ ((hr.pow _).mul (hr'.pow _))

section FractionField

variable (K : Type*) [Field K] [Algebra D K] [IsFractionRing D K]

/-- By Gauss's lemma, the members of an irreducible basis stay irreducible over the fraction
field. -/
theorem irreducible_map (hB : F.IsIrreducibleBasis B) (hb : b ∈ B) :
    Irreducible (b.map (algebraMap D K)) :=
  (hB.isPrimitive hb).irreducible_iff_irreducible_map_fraction_map.1 (hB.irreducible b hb)

/-- Distinct members of an irreducible basis are coprime over the fraction field. -/
theorem isCoprime_map (hB : F.IsIrreducibleBasis B) (hb : b ∈ B) (hb' : b' ∈ B) (hne : b ≠ b') :
    IsCoprime (b.map (algebraMap D K)) (b'.map (algebraMap D K)) :=
  (hB.irreducible_map K hb).coprime_iff_not_dvd.2 fun h ↦ hne <|
    hB.eq_of_associated b hb b' hb' <| (hB.irreducible b hb).associated_of_dvd
      (hB.irreducible b' hb') ((hB.isPrimitive hb).dvd_of_fraction_map_dvd_fraction_map h)

/-- The product of the members of an irreducible basis is squarefree over the fraction field. -/
theorem squarefree_prod_map (hB : F.IsIrreducibleBasis B) :
    Squarefree (∏ b ∈ B, b.map (algebraMap D K)) :=
  Finset.squarefree_prod_of_pairwise_isCoprime
    (fun _ hb _ hb' hne ↦ (hB.isCoprime_map K hb hb' hne).isRelPrime)
    fun _ hb ↦ (hB.irreducible_map K hb).squarefree

end FractionField

/-- The resultant of two distinct members of an irreducible basis is nonzero. -/
theorem resultant_ne_zero (hB : F.IsIrreducibleBasis B) (hb : b ∈ B) (hb' : b' ∈ B)
    (hne : b ≠ b') : resultant b b' ≠ 0 := by
  have hinj := IsFractionRing.injective D (FractionRing D)
  have h := Polynomial.resultant_ne_zero _ _ (hB.isCoprime_map (FractionRing D) hb hb' hne)
  rwa [natDegree_map_eq_of_injective hinj, natDegree_map_eq_of_injective hinj, resultant_map_map,
    map_ne_zero_iff _ hinj] at h

/-- In characteristic zero, the discriminant of a member of an irreducible basis is nonzero. In
positive characteristic an irreducible member can be inseparable, with zero discriminant. -/
theorem discr_ne_zero [CharZero D] (hB : F.IsIrreducibleBasis B) (hb : b ∈ B) : b.discr ≠ 0 := by
  have hinj := IsFractionRing.injective D (FractionRing D)
  have : CharZero (FractionRing D) := charZero_of_injective_algebraMap hinj
  have hb0 := (Polynomial.map_ne_zero_iff hinj).2 (hB.irreducible b hb).ne_zero
  have h := (discr_ne_zero_iff hb0).2 (hB.irreducible_map (FractionRing D) hb).separable
  rwa [discr_map_of_natDegree_eq _ (natDegree_map_eq_of_injective hinj _),
    map_ne_zero_iff _ hinj] at h

/-- In characteristic zero, the product of any subfamily of an irreducible basis has
nonzero discriminant. This includes the empty subfamily, whose product is `1`. -/
theorem discr_prod_ne_zero [CharZero D] (hB : F.IsIrreducibleBasis B)
    {A : Finset D[X]} (hA : A ⊆ B) : (∏ b ∈ A, b).discr ≠ 0 := by
  let K := FractionRing D
  have hinj := IsFractionRing.injective D K
  have : CharZero K := charZero_of_injective_algebraMap hinj
  have hsep : (∏ b ∈ A, b.map (algebraMap D K)).Separable :=
    PerfectField.separable_iff_squarefree.2 <|
      (hB.squarefree_prod_map K).squarefree_of_dvd
        (Finset.prod_dvd_prod_of_subset A B _ hA)
  have h := (Polynomial.discr_ne_zero_iff hsep.ne_zero).2 hsep
  rw [← Polynomial.map_prod, Polynomial.discr_map_of_natDegree_eq _
    (Polynomial.natDegree_map_eq_of_injective hinj _), map_ne_zero_iff _ hinj] at h
  exact h

end IsIrreducibleBasis

end Finset

namespace Polynomial

variable {D : Type*} [CommRing D] [IsDomain D] [UniqueFactorizationMonoid D]

/-- Over a unique factorization domain, a nonzero polynomial is a constant times the product of
its irreducible factors of positive degree. -/
theorem exists_eq_C_mul_prod_filter_factors {f : D[X]} (hf : f ≠ 0) :
    ∃ c, f = C c * ((UniqueFactorizationMonoid.factors f).filter (0 < ·.natDegree)).prod := by
  set m := UniqueFactorizationMonoid.factors f
  -- the factors of degree zero multiply to a constant
  obtain ⟨c, hc⟩ : ∃ c, (m.filter fun q ↦ ¬0 < q.natDegree).prod = C c := by
    refine ⟨_, eq_C_of_natDegree_eq_zero (Nat.eq_zero_of_le_zero
      ((natDegree_multiset_prod_le _).trans (Multiset.sum_eq_zero fun d hd ↦ ?_).le))⟩
    obtain ⟨q, hq, rfl⟩ := Multiset.mem_map.1 hd
    simpa using (Multiset.mem_filter.1 hq).2
  obtain ⟨u, hu⟩ := UniqueFactorizationMonoid.factors_prod hf
  obtain ⟨r, -, hr⟩ := isUnit_iff.1 u.isUnit
  refine ⟨c * r, ?_⟩
  rw [← hu, ← Multiset.prod_filter_mul_prod_filter_not (s := m) (0 < ·.natDegree), hc, ← hr,
    C_mul]
  ring

end Polynomial

namespace Finset

variable {D : Type*} [CommRing D] [IsDomain D] [UniqueFactorizationMonoid D]

/-- Every finite family of polynomials over a unique factorization domain has an irreducible
basis. -/
theorem exists_isIrreducibleBasis (F : Finset D[X]) : ∃ B, F.IsIrreducibleBasis B := by
  classical
  -- the irreducible factors of positive degree of the members of `F`
  let S := F.biUnion fun f ↦
    ((UniqueFactorizationMonoid.factors f).filter (0 < ·.natDegree)).toFinset
  have mem_S {q : D[X]} :
      q ∈ S ↔ ∃ f ∈ F, q ∈ UniqueFactorizationMonoid.factors f ∧ 0 < q.natDegree := by
    simp [S]
  -- one representative of each associate class
  let rep : D[X] → D[X] := fun q ↦ Quot.out (Associates.mk q)
  have hrep (q : D[X]) : Associated (rep q) q :=
    Associates.mk_eq_mk_iff_associated.1 (Associates.quot_out _)
  refine ⟨S.image rep, ⟨?_, ?_, ?_, fun f hf ↦ ?_, ?_⟩⟩
  · simp only [mem_image, mem_S]
    rintro _ ⟨q, ⟨f, -, hq, -⟩, rfl⟩
    exact (hrep q).symm.irreducible (UniqueFactorizationMonoid.irreducible_of_factor q hq)
  · simp only [mem_image, mem_S]
    rintro _ ⟨q, ⟨f, -, -, hq⟩, rfl⟩
    rwa [natDegree_eq_of_degree_eq (degree_eq_degree_of_associated (hrep q))]
  · simp only [mem_image]
    rintro _ ⟨q, -, rfl⟩ _ ⟨q', -, rfl⟩ h
    rw [← Associates.mk_eq_mk_iff_associated, Associates.quot_out, Associates.quot_out] at h
    simp only [rep, h]
  · by_cases hf0 : f = 0
    · exact ⟨0, 0, by simp [hf0]⟩
    obtain ⟨c, hc⟩ := exists_eq_C_mul_prod_filter_factors hf0
    set m := (UniqueFactorizationMonoid.factors f).filter (0 < ·.natDegree)
    -- replace each factor by its representative, and collect equal representatives
    have hprod : (m.map rep).prod = ∏ b ∈ S.image rep, b ^ (m.map rep).count b := by
      rw [Finset.prod_multiset_count]
      refine Finset.prod_subset (fun b hb ↦ ?_) fun b _ hb ↦ by
        rw [Multiset.count_eq_zero_of_notMem (by simpa using hb), pow_zero]
      obtain ⟨q, hq, rfl⟩ := Multiset.mem_map.1 (Multiset.mem_toFinset.1 hb)
      obtain ⟨hqm, hq⟩ := Multiset.mem_filter.1 hq
      exact mem_image_of_mem rep (mem_S.2 ⟨f, hf, hqm, hq⟩)
    obtain ⟨u, hu⟩ : Associated (m.map rep).prod m.prod := by
      rw [← Associates.mk_eq_mk_iff_associated, ← Associates.prod_mk, ← Associates.prod_mk,
        Multiset.map_map]
      exact congrArg _ (Multiset.map_congr rfl fun q _ ↦ Associates.quot_out _)
    obtain ⟨r, -, hr⟩ := Polynomial.isUnit_iff.1 u.isUnit
    refine ⟨c * r, fun b ↦ (m.map rep).count b, ?_⟩
    rw [hc, ← hu, ← hr, ← hprod, C_mul]
    ring
  · simp only [mem_image, mem_S]
    rintro _ ⟨q, ⟨f, hf, hq, -⟩, rfl⟩
    refine ⟨f, hf, ?_, (hrep q).dvd.trans (UniqueFactorizationMonoid.dvd_of_mem_factors hq)⟩
    rintro rfl
    simp at hq

end Finset
