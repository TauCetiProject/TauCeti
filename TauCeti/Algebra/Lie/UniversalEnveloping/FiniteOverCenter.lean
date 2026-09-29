/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.UniversalEnveloping.PBW.Ordered
public import TauCeti.Algebra.Lie.UniversalEnveloping.PCenter
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Finiteness.Subalgebra
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic

/-!
# Finite generation over central subalgebras

This file proves the finite-generation step in the positive-characteristic proof of Ado--Iwasawa.
If the canonical enveloping-algebra images of a finite spanning family of a Lie algebra are
integral over a central coefficient algebra, then the enveloping algebra is finite as a module over
that algebra.
The proof uses ordered PBW spanning: an ordered word is grouped into one power of each basis
generator, and each group lies in a finitely generated singleton algebra.

For a finite-dimensional Lie algebra over a field of prime characteristic, the central
`p`-polynomials constructed in
`TauCeti.Algebra.Lie.UniversalEnveloping.PCenter` supply these integral relations. Their finitely
generated algebra in the center is Noetherian, and the enveloping algebra is module-finite over it.
The chosen central generators also lie in the augmentation ideal; this is the input needed to form
the finite-dimensional augmentation quotient in the subsequent Krull-intersection argument.

## Main results

* `Subalgebra.centralSubalgebraAlgebra`: a subalgebra of the center acts on the ambient
  algebra.
* `TauCeti.UniversalEnvelopingAlgebra.moduleFinite_of_isIntegral_of_span_eq_top`: integral
  canonical images of a finite spanning family imply module-finiteness of the enveloping algebra.
* `TauCeti.UniversalEnvelopingAlgebra.exists_pCentralGenerators_moduleFinite`: in prime
  characteristic, finitely many central `p`-polynomials generate a Noetherian coefficient algebra
  over which the enveloping algebra is module-finite.

## References

* N. Jacobson, *Lie Algebras*, Chapter VI, section 2.
-/

public section

open scoped Pointwise

universe u v w

namespace Subalgebra

/-- A subalgebra of the center of an algebra acts on the ambient algebra by multiplication. -/
abbrev centralSubalgebraAlgebra {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]
    (S : Subalgebra R (Subalgebra.center R A)) : Algebra S A :=
  (((Subalgebra.center R A).val.comp S.val).toRingHom.toAlgebra' fun s a ↦
    (Subalgebra.mem_center_iff.mp s.1.property a).symm)

end Subalgebra

namespace TauCeti

namespace UniversalEnvelopingAlgebra

variable (R : Type u) (L : Type v)
variable [CommRing R] [LieRing L] [LieAlgebra R L]

attribute [local instance 100] LieRing.ofAssociativeRing

local notation "U" => _root_.UniversalEnvelopingAlgebra R L

section IntegralBasis

variable (S : Type w) [CommRing S] [Algebra R S]
variable [Algebra S (_root_.UniversalEnvelopingAlgebra R L)]
variable [IsScalarTower R S (_root_.UniversalEnvelopingAlgebra R L)]

/-- The nondecreasing list in which `i` occurs `c i` times. -/
private def repeatedIndices (n : ℕ) (c : Fin n → ℕ) : List (Fin n) :=
  (List.finRange n).flatMap fun i ↦ List.replicate (c i) i

private theorem repeatedIndices_pairwise (n : ℕ) (c : Fin n → ℕ) :
    (repeatedIndices n c).Pairwise (· ≤ ·) := by
  induction n with
  | zero => simp [repeatedIndices]
  | succ n ih =>
      rw [repeatedIndices, List.finRange_succ, List.flatMap_cons]
      simp only [List.flatMap_map]
      rw [List.pairwise_append]
      refine ⟨by simp, ?_, ?_⟩
      · have h := (ih (fun i ↦ c i.succ)).map Fin.succ
            (fun _ _ h ↦ Fin.succ_le_succ_iff.mpr h)
        simpa [repeatedIndices, List.map_flatMap] using h
      · simp

private theorem count_repeatedIndices (n : ℕ) (c : Fin n → ℕ) (i : Fin n) :
    (repeatedIndices n c).count i = c i := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
      have hexpand : repeatedIndices (n + 1) c = List.replicate (c 0) 0 ++
          (repeatedIndices n fun j ↦ c j.succ).map Fin.succ := by
        rw [repeatedIndices, List.finRange_succ, List.flatMap_cons, repeatedIndices,
          List.flatMap_map]
        rw [List.map_flatMap]
        simp
      rw [hexpand, List.count_append]
      by_cases hi : i = 0
      · subst i
        simp [List.count_eq_zero]
      · obtain ⟨j, rfl⟩ := Fin.eq_succ_of_ne_zero hi
        rw [List.count_map_of_injective _ Fin.succ (Fin.succ_injective n) j, ih]
        simp [List.count_replicate, Ne.symm hi]

private theorem eq_repeatedIndices {n : ℕ} {word : List (Fin n)}
    (hword : word.Pairwise (· ≤ ·)) :
    word = repeatedIndices n fun i ↦ word.count i := by
  apply List.Perm.eq_of_pairwise' hword (repeatedIndices_pairwise n _)
  rw [List.perm_iff_count]
  exact fun i ↦ (count_repeatedIndices n (fun i ↦ word.count i) i).symm

/-- The product of the singleton algebras associated to a list of generators. -/
private def integralProductSubmodule {n : ℕ} (x : Fin n → U) :
    List (Fin n) → Submodule S U
  | [] => 1
  | i :: l => (Algebra.adjoin S {x i}).toSubmodule * integralProductSubmodule x l

omit [Algebra R S] [IsScalarTower R S U] in
private theorem integralProductSubmodule_fg {n : ℕ} (x : Fin n → U)
    (hx : ∀ i, IsIntegral S (x i)) (l : List (Fin n)) :
    (integralProductSubmodule (R := R) (L := L) S x l).FG := by
  induction l with
  | nil =>
      rw [integralProductSubmodule]
      exact ⟨{1}, by simp [Submodule.one_eq_span]⟩
  | cons i l ih =>
      exact (hx i).fg_adjoin_singleton.mul ih

omit [Algebra R S] [IsScalarTower R S U] in
private theorem prod_pow_mem_integralProductSubmodule {n : ℕ} (x : Fin n → U)
    (c : Fin n → ℕ) (l : List (Fin n)) :
    (l.map fun i ↦ x i ^ c i).prod ∈
      integralProductSubmodule (R := R) (L := L) S x l := by
  induction l with
  | nil =>
      change 1 ∈ (1 : Submodule S U)
      rw [Submodule.one_eq_span]
      exact Submodule.subset_span (Set.mem_singleton 1)
  | cons i l ih =>
      rw [List.map_cons, List.prod_cons, integralProductSubmodule]
      exact Submodule.mul_mem_mul
        ((Algebra.adjoin S {x i}).pow_mem (Algebra.subset_adjoin rfl) _) ih

private theorem pbwMonomial_flatMap_replicate {n : ℕ} (e : Fin n → L)
    (c : Fin n → ℕ) (l : List (Fin n)) :
    pbwMonomial R L e (l.flatMap fun i ↦ List.replicate (c i) i) =
      (l.map fun i ↦ _root_.UniversalEnvelopingAlgebra.ι R (e i) ^ c i).prod := by
  induction l with
  | nil => simp
  | cons i l ih =>
      rw [List.flatMap_cons, pbwMonomial_append, List.map_cons, List.prod_cons, ih]
      simp [pbwMonomial_def]

private theorem pbwMonomial_repeatedIndices (n : ℕ) (e : Fin n → L) (c : Fin n → ℕ) :
    pbwMonomial R L e (repeatedIndices n c) =
      ((List.finRange n).map fun i ↦
        _root_.UniversalEnvelopingAlgebra.ι R (e i) ^ c i).prod := by
  exact pbwMonomial_flatMap_replicate R L e c _

/-- If the canonical images of a finite spanning family in `L` are integral over a central
coefficient algebra `S`, then `U(L)` is finite as an `S`-module.

The argument only needs ordered PBW spanning, not linear independence of PBW monomials. -/
theorem moduleFinite_of_isIntegral_of_span_eq_top {n : ℕ} (e : Fin n → L)
    (he : Submodule.span R (Set.range e) = ⊤)
    (h : ∀ i, IsIntegral S (_root_.UniversalEnvelopingAlgebra.ι R (e i))) :
    Module.Finite S U := by
  let M : Submodule S U := integralProductSubmodule (R := R) (L := L) S
    (fun i ↦ _root_.UniversalEnvelopingAlgebra.ι R (e i)) (List.finRange n)
  have hMfg : M.FG := integralProductSubmodule_fg (R := R) (L := L) S _ h _
  have hle : Submodule.span R (⋃ k, orderedPBWMonomials R L e k) ≤
      M.restrictScalars R := by
    rw [Submodule.span_le]
    intro a ha
    rw [Set.mem_iUnion] at ha
    obtain ⟨k, hak⟩ := ha
    rw [mem_orderedPBWMonomials_iff] at hak
    obtain ⟨word, hword, -, rfl⟩ := hak
    change pbwMonomial R L e word ∈ M
    rw [eq_repeatedIndices hword, pbwMonomial_repeatedIndices]
    exact prod_pow_mem_integralProductSubmodule (R := R) (L := L) S _ _ _
  have hMR : M.restrictScalars R = (⊤ : Submodule R U) := by
    rw [span_iUnion_orderedPBWMonomials_eq_top R L e he] at hle
    exact le_antisymm le_top hle
  have hMtop : M = (⊤ : Submodule S U) := by
    ext x
    constructor
    · exact fun _ ↦ trivial
    · intro _
      have hx : x ∈ M.restrictScalars R := by rw [hMR]; trivial
      exact hx
  let _ : Module.Finite S M := Module.Finite.of_fg hMfg
  exact Module.Finite.of_surjective M.subtype fun x ↦
    ⟨⟨x, by rw [hMtop]; trivial⟩, rfl⟩

end IntegralBasis

section Field

variable (K : Type u) (L : Type v) [Field K] [LieRing L] [LieAlgebra K L]

local notation "Uₖ" => _root_.UniversalEnvelopingAlgebra K L

private theorem isIntegral_of_pPolynomial_mem_subalgebra (p e : ℕ) [Fact p.Prime]
    (a : Fin e → K) (x : L)
    (hc : _root_.UniversalEnvelopingAlgebra.ι K x ^ p ^ e +
        ∑ i : Fin e, a i • _root_.UniversalEnvelopingAlgebra.ι K x ^ p ^ (i : ℕ) ∈
      Subalgebra.center K Uₖ)
    (S : Subalgebra K (Subalgebra.center K Uₖ))
    (hS : (⟨_, hc⟩ : Subalgebra.center K Uₖ) ∈ S) :
    let _ : Algebra S Uₖ := Subalgebra.centralSubalgebraAlgebra S
    IsIntegral S (_root_.UniversalEnvelopingAlgebra.ι K x) := by
  let _ : Algebra S Uₖ := Subalgebra.centralSubalgebraAlgebra S
  let c : S := ⟨⟨_, hc⟩, hS⟩
  let r : Polynomial S :=
    (∑ i : Fin e, Polynomial.C (algebraMap K S (a i)) * Polynomial.X ^ p ^ (i : ℕ)) -
      Polynomial.C c
  have hp : 1 < p := (Fact.out : p.Prime).one_lt
  have hsum : Polynomial.degree
      (∑ i : Fin e, Polynomial.C (algebraMap K S (a i)) *
        Polynomial.X ^ p ^ (i : ℕ)) < (p ^ e : WithBot ℕ) :=
    (Polynomial.degree_sum_le _ _).trans_lt <|
      (Finset.sup_lt_iff (WithBot.bot_lt_coe _)).2 fun i _ ↦
        (Polynomial.degree_C_mul_X_pow_le _ _).trans_lt <|
          WithBot.coe_lt_coe.mpr (Nat.pow_lt_pow_right hp i.isLt)
  have hr : Polynomial.degree r < (p ^ e : WithBot ℕ) :=
    (Polynomial.degree_sub_le _ _).trans_lt <| max_lt hsum <|
      Polynomial.degree_C_le.trans_lt <|
        WithBot.coe_lt_coe.mpr (pow_pos (Fact.out : p.Prime).pos e)
  let ev : Polynomial S →ₐ[S] Uₖ :=
    Polynomial.aeval (_root_.UniversalEnvelopingAlgebra.ι K x)
  refine ⟨Polynomial.X ^ p ^ e + r, Polynomial.monic_X_pow_add hr, ?_⟩
  dsimp only [r]
  change ev (Polynomial.X ^ p ^ e +
    ((∑ i : Fin e, Polynomial.C (algebraMap K S (a i)) *
      Polynomial.X ^ p ^ (i : ℕ)) - Polynomial.C c)) = 0
  rw [map_add ev, map_sub ev, map_sum ev]
  simp only [map_pow, map_mul, ev, Polynomial.aeval_X, Polynomial.aeval_C]
  have hc' : algebraMap S Uₖ c =
      _root_.UniversalEnvelopingAlgebra.ι K x ^ p ^ e +
        ∑ i : Fin e, a i • _root_.UniversalEnvelopingAlgebra.ι K x ^ p ^ (i : ℕ) := rfl
  rw [hc']
  let y : Uₖ := ∑ i : Fin e, algebraMap K Uₖ (a i) *
    _root_.UniversalEnvelopingAlgebra.ι K x ^ p ^ (i : ℕ)
  change _root_.UniversalEnvelopingAlgebra.ι K x ^ p ^ e +
    (y - (_root_.UniversalEnvelopingAlgebra.ι K x ^ p ^ e + y)) = 0
  abel

/-- **The enveloping algebra is module-finite over a Noetherian algebra generated by central
`p`-polynomials.** For a finite-dimensional Lie algebra `L` over a field of prime characteristic
`p`, there is one central `p`-polynomial for each member of a finite basis. These elements lie in
the augmentation ideal. Their algebra `S` in the center of `U(L)` is Noetherian, and `U(L)` is a
finite `S`-module.

The central generators are returned explicitly because their augmentation-ideal membership is
needed when passing to a finite-dimensional quotient. -/
theorem exists_pCentralGenerators_moduleFinite (p : ℕ) [Fact p.Prime] [CharP K p]
    [FiniteDimensional K L] :
    ∃ c : Fin (Module.finrank K L) → Subalgebra.center K Uₖ,
      (∀ i, (c i : Uₖ) ∈ (HopfIdeal.augmentation K Uₖ).toIdeal) ∧
      let S := Algebra.adjoin K (Set.range c)
      let _ : Algebra S Uₖ := Subalgebra.centralSubalgebraAlgebra S
      IsNoetherianRing S ∧ Module.Finite S Uₖ := by
  let b := Module.finBasis K L
  choose e a hc using fun i ↦ exists_pCentralPolynomial K L p (b i)
  let c : Fin (Module.finrank K L) → Subalgebra.center K Uₖ := fun i ↦
    ⟨_root_.UniversalEnvelopingAlgebra.ι K (b i) ^ p ^ e i +
      ∑ j : Fin (e i), a i j •
        _root_.UniversalEnvelopingAlgebra.ι K (b i) ^ p ^ (j : ℕ), hc i⟩
  refine ⟨c, ?_, ?_⟩
  · intro i
    exact pPolynomial_ι_mem_augmentation_toIdeal K L
      (Fact.out : p.Prime).ne_zero (e i) (a i) (b i)
  · let S := Algebra.adjoin K (Set.range c)
    let _ : Algebra.FiniteType K S :=
      Algebra.FiniteType.adjoin_of_finite (Set.finite_range c)
    let _ : Algebra S Uₖ := Subalgebra.centralSubalgebraAlgebra S
    let hTower : IsScalarTower K S Uₖ := by
      constructor
      intro k s x
      change (algebraMap K Uₖ k * (s : Uₖ)) * x =
        algebraMap K Uₖ k * ((s : Uₖ) * x)
      exact mul_assoc _ _ _
    refine ⟨Algebra.FiniteType.isNoetherianRing K S, ?_⟩
    apply @moduleFinite_of_isIntegral_of_span_eq_top K L _ _ _ S _ _ _ hTower _ b b.span_eq
    intro i
    apply isIntegral_of_pPolynomial_mem_subalgebra K L p (e i) (a i) (b i) (hc i) S
    exact Algebra.subset_adjoin (Set.mem_range_self i)

end Field

end UniversalEnvelopingAlgebra

end TauCeti
