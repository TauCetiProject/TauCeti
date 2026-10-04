/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Character
public import Mathlib.Data.Sum.Order
public import Mathlib.LinearAlgebra.Basis.Prod
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import TauCeti.Algebra.Lie.UniversalEnveloping.Functoriality
public import TauCeti.Algebra.Lie.UniversalEnveloping.PBW.Basis
public import TauCeti.Algebra.Lie.UniversalEnveloping.Subalgebra
public import TauCeti.Data.Multiset.Sort

/-!
# Modules induced from a character of a Lie subalgebra

Let `B` be a Lie subalgebra of a Lie algebra `L` over a commutative ring `R`, and let
`χ : B → R` be a character of `B`. The elements `ι x - χ x` of `U(L)`, for `x : B`, generate a
left ideal of `U(L)`, and the quotient of `U(L)` by it is the induced module
`U(L) ⊗_{U(B)} R_χ`, presented without a tensor product over the noncommutative ring `U(B)`. This
file proves that the left ideal is **proper** as soon as `B` has a complement in `L` and both `B`
and the complement are free; over a field this holds for every Lie subalgebra. In other words, the
induced module is nonzero.

When the complement is itself a Lie subalgebra `A`, the induced module is moreover a **free
`U(A)`-module of rank one** on the class of `1`: every element of `U(L)` is congruent to an element
of `U(A)` modulo the left ideal, and an element of `U(A)` lying in the left ideal is zero. For a
semisimple Lie algebra, its Borel subalgebra `𝔟` and the opposite nilradical `n⁻`, this is the
freeness of the Verma module over `U(n⁻)`.

The input is the freeness half of the Poincaré--Birkhoff--Witt theorem relative to a subalgebra:
`U(L)` is a free right `U(B)`-module on the ordered monomials in a basis of a complement of `B`.
For a semisimple Lie algebra and its Borel subalgebra this is what makes Verma modules nonzero.
The spanning half needs no basis: it only uses that `U(L) = U(A) · U(B)` when `A` and `B` span
`L`, and that every element `r` of `U(B)` is congruent to the scalar `χ r`.

## Main results

* `TauCeti.UniversalEnvelopingAlgebra.span_range_ι_sub_algebraMap_ne_top_of_isCompl`: over a
  nontrivial commutative ring, if `B` has a complement and both are free, the left ideal generated
  by `ι x - χ x` is proper.
* `TauCeti.UniversalEnvelopingAlgebra.span_range_ι_sub_algebraMap_ne_top`: over a field, the same
  holds for every Lie subalgebra.
* `TauCeti.UniversalEnvelopingAlgebra.map_sub_algebraMap_lift_mem_span_range_ι_sub_algebraMap`:
  every `r` in `U(B)` is congruent to `χ r` modulo the left ideal.
* `TauCeti.UniversalEnvelopingAlgebra.exists_sub_map_mem_span_range_ι_sub_algebraMap`: if the Lie
  subalgebras `A` and `B` span `L`, every element of `U(L)` is congruent to one of `U(A)`.
* `TauCeti.UniversalEnvelopingAlgebra.map_mem_span_range_ι_sub_algebraMap_iff_of_isCompl`: if the
  Lie subalgebra `A` is a complement of `B` and both are free, an element of `U(A)` lies in the left
  ideal only if it is zero.

## Implementation notes

Choose an ordered basis of `L` that lists a basis of the complement `A` before a basis of `B`. By
PBW its ordered monomials form a basis of `U(L)`, and each of them factors as an ordered monomial
in the basis of `A` times the image of an ordered monomial of `U(B)`. The linear form on `U(L)`
that reads off the coefficient of a fixed `A`-monomial and applies `χ` to it is then right
`U(B)`-semilinear along `χ`, so it kills the left ideal. The form attached to the empty monomial
sends `1` to `1`, which gives properness; when `A` is a Lie subalgebra, the forms attached to all
monomials restrict on `U(A)` to its PBW coordinates, which gives freeness. Rather than building
the right `U(B)`-module structure, the file defines these linear forms directly on the PBW basis.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, GTM 9, §17.4
  and §20.3.
-/

public section

namespace TauCeti.UniversalEnvelopingAlgebra

open LieAlgebra Module

attribute [local instance 100] LieRing.ofAssociativeRing

universe u v w₁ w₂

variable {R : Type u} {L : Type v} [CommRing R] [LieRing L] [LieAlgebra R L]

local notation "U" => _root_.UniversalEnvelopingAlgebra R L

section Adapted

variable (B : LieSubalgebra R L) {A : Submodule R L} (hA : IsCompl A (B : Submodule R L))
  {ιA : Type w₁} {ιB : Type w₂} (bA : Basis ιA R A) (bB : Basis ιB R B)

/-- The basis of `L` listing the basis `bA` of the complement before the basis `bB` of `B`. -/
private noncomputable def adaptedBasis : Basis (ιA ⊕ₗ ιB) R L :=
  ((bA.prod bB).map (Submodule.prodEquivOfIsCompl A (B : Submodule R L) hA)).reindex toLex

private theorem adaptedBasis_inl (i : ιA) :
    adaptedBasis B hA bA bB (Sum.inlₗ i) = (bA i : L) := by
  simp only [adaptedBasis, Basis.coe_reindex, toLex_symm_eq, Function.comp_apply, ofLex_toLex,
    Basis.map_apply, Basis.prod_apply, LinearMap.coe_inl, Sum.elim_inl]
  rw [Submodule.coe_prodEquivOfIsCompl', ZeroMemClass.coe_zero, add_zero]

private theorem adaptedBasis_inr (j : ιB) :
    adaptedBasis B hA bA bB (Sum.inrₗ j) = (bB j : L) := by
  simp only [adaptedBasis, Basis.coe_reindex, toLex_symm_eq, Function.comp_apply, ofLex_toLex,
    Basis.map_apply, Basis.prod_apply, LinearMap.coe_inr, Sum.elim_inr]
  rw [Submodule.coe_prodEquivOfIsCompl', ZeroMemClass.coe_zero, zero_add]

/-- Exponent vectors over the ordered sum, split into their two halves. -/
private noncomputable def sumExponentEquiv : ((ιA →₀ ℕ) × (ιB →₀ ℕ)) ≃ (ιA ⊕ₗ ιB →₀ ℕ) :=
  Finsupp.sumFinsuppEquivProdFinsupp.symm.trans (Finsupp.domCongr toLex).toEquiv

private theorem sumExponentEquiv_apply (α : ιA →₀ ℕ) (β : ιB →₀ ℕ) :
    sumExponentEquiv (α, β) = α.mapDomain Sum.inlₗ + β.mapDomain Sum.inrₗ := by
  ext x
  obtain ⟨i | j, rfl⟩ := toLex.surjective x
  · simp only [sumExponentEquiv, Equiv.trans_apply, Finsupp.coe_add, Pi.add_apply]
    simp [Finsupp.mapDomain_of_notMem_range,
      Finsupp.mapDomain_apply_of_injective (f := Sum.inlₗ (β := ιB))
        (toLex.injective.comp Sum.inl_injective) α i]
  · simp only [sumExponentEquiv, Equiv.trans_apply, Finsupp.coe_add, Pi.add_apply]
    simp [Finsupp.mapDomain_of_notMem_range,
      Finsupp.mapDomain_apply_of_injective (f := Sum.inrₗ (α := ιA))
        (toLex.injective.comp Sum.inr_injective) β j]

variable [LinearOrder ιA] [LinearOrder ιB]

/-- The ordered monomial in the basis of the complement with exponent vector `α`. -/
private noncomputable def complementMonomial (α : ιA →₀ ℕ) : U :=
  pbwMonomial R L (fun i ↦ (bA i : L)) (α.toMultiset.sort (· ≤ ·))

/-- **The adapted PBW basis factors**: the ordered monomial with exponents `α` on the complement
and `β` on `B` is the ordered `α`-monomial of the complement times the image of the ordered
`β`-monomial of `U(B)`. -/
private theorem pbwBasis_adaptedBasis_sumExponentEquiv (α : ιA →₀ ℕ) (β : ιB →₀ ℕ) :
    (adaptedBasis B hA bA bB).pbwBasis (sumExponentEquiv (α, β)) =
      complementMonomial bA α * map R B.incl (bB.pbwBasis β) := by
  -- The exponent vector of `(α, β)` is the sum of the two halves, pushed into `ιA ⊕ₗ ιB`.
  have hexp : (sumExponentEquiv (α, β)).toMultiset =
      α.toMultiset.map Sum.inlₗ + β.toMultiset.map Sum.inrₗ := by
    rw [sumExponentEquiv_apply, Finsupp.toMultiset_add, Finsupp.toMultiset_map,
      Finsupp.toMultiset_map]
  -- Every complement index precedes every index of `B`, so the sorted list splits in two.
  have hle : ∀ a ∈ α.toMultiset.map Sum.inlₗ, ∀ b ∈ β.toMultiset.map (Sum.inrₗ (α := ιA)),
      a ≤ b := by
    simp only [Multiset.mem_map]
    rintro _ ⟨i, -, rfl⟩ _ ⟨j, -, rfl⟩
    exact Sum.Lex.inl_le_inr i j
  have hsort : (sumExponentEquiv (α, β)).toMultiset.sort (· ≤ ·) =
      (α.toMultiset.sort (· ≤ ·)).map Sum.inlₗ ++ (β.toMultiset.sort (· ≤ ·)).map Sum.inrₗ := by
    rw [hexp, Multiset.sort_add _ hle,
      Multiset.map_sort Sum.inlₗ α.toMultiset (fun a b : ιA ↦ a ≤ b)
        (fun a b : ιA ⊕ₗ ιB ↦ a ≤ b) (fun _ _ _ _ ↦ Sum.Lex.inl_le_inl_iff.symm),
      Multiset.map_sort Sum.inrₗ β.toMultiset (fun a b : ιB ↦ a ≤ b)
        (fun a b : ιA ⊕ₗ ιB ↦ a ≤ b) (fun _ _ _ _ ↦ Sum.Lex.inr_le_inr_iff.symm)]
  -- The monomial of the concatenation is the product of the two monomials.
  rw [Basis.pbwBasis_apply, Basis.pbwBasis_apply, map_pbwMonomial, hsort, pbwMonomial_append,
    complementMonomial]
  simp only [pbwMonomial_def, List.map_map, Function.comp_def, adaptedBasis_inl, adaptedBasis_inr,
    LieSubalgebra.coe_incl]

variable (χ : LieCharacter R B)

/-- The linear form on `U(L)` reading off the coefficient of the complement monomial with
exponents `α` in the free right `U(B)`-module structure, and applying the character `χ` to it. -/
private noncomputable def characterForm (α : ιA →₀ ℕ) : U →ₗ[R] R :=
  (adaptedBasis B hA bA bB).pbwBasis.constr R fun n ↦
    if (sumExponentEquiv.symm n).1 = α then
      _root_.UniversalEnvelopingAlgebra.lift R χ (bB.pbwBasis (sumExponentEquiv.symm n).2)
    else 0

private theorem _root_.UniversalEnvelopingAlgebra.characterForm_complementMonomial_mul
    (α α' : ιA →₀ ℕ) (y : _root_.UniversalEnvelopingAlgebra R B) :
    characterForm B hA bA bB χ α (complementMonomial bA α' * map R B.incl y) =
      if α' = α then _root_.UniversalEnvelopingAlgebra.lift R χ y else 0 := by
  have hlin := bB.pbwBasis.ext (f₁ := characterForm B hA bA bB χ α ∘ₗ
      LinearMap.mulLeft R (complementMonomial bA α') ∘ₗ (map R B.incl).toLinearMap)
    (f₂ := if α' = α then (_root_.UniversalEnvelopingAlgebra.lift R χ).toLinearMap else 0)
    fun β ↦ by
      simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, LinearMap.mulLeft_apply]
      rw [← pbwBasis_adaptedBasis_sumExponentEquiv B hA, characterForm, Basis.constr_basis,
        Equiv.symm_apply_apply]
      split_ifs <;> simp
  have hy := LinearMap.congr_fun hlin y
  split_ifs at hy ⊢ <;> simpa using hy

/-- The character form is right `U(B)`-semilinear along the character `χ`. -/
private theorem _root_.UniversalEnvelopingAlgebra.characterForm_mul_map (α : ιA →₀ ℕ) (u : U)
    (r : _root_.UniversalEnvelopingAlgebra R B) :
    characterForm B hA bA bB χ α (u * map R B.incl r) =
      characterForm B hA bA bB χ α u * _root_.UniversalEnvelopingAlgebra.lift R χ r := by
  have hlin := (adaptedBasis B hA bA bB).pbwBasis.ext
    (f₁ := characterForm B hA bA bB χ α ∘ₗ LinearMap.mulRight R (map R B.incl r))
    (f₂ := _root_.UniversalEnvelopingAlgebra.lift R χ r • characterForm B hA bA bB χ α)
    fun n ↦ by
      obtain ⟨⟨α', β⟩, rfl⟩ := sumExponentEquiv.surjective n
      simp only [LinearMap.comp_apply, LinearMap.mulRight_apply, LinearMap.smul_apply,
        pbwBasis_adaptedBasis_sumExponentEquiv, mul_assoc, ← map_mul,
        _root_.UniversalEnvelopingAlgebra.characterForm_complementMonomial_mul, smul_eq_mul]
      split_ifs <;> simp [mul_comm]
  simpa [mul_comm] using LinearMap.congr_fun hlin u

private theorem characterForm_one : characterForm B hA bA bB χ 0 1 = 1 := by
  simpa [complementMonomial] using
    _root_.UniversalEnvelopingAlgebra.characterForm_complementMonomial_mul B hA bA bB χ 0 0 1

/-- Every character form vanishes on the left ideal generated by the elements `ι x - χ x`. -/
private theorem characterForm_eq_zero_of_mem_span (α : ιA →₀ ℕ) {s : U}
    (hs : s ∈ Submodule.span U (Set.range fun x : B ↦
      _root_.UniversalEnvelopingAlgebra.ι R (x : L) - algebraMap R U (χ x))) :
    characterForm B hA bA bB χ α s = 0 := by
  suffices key : ∀ v : U, characterForm B hA bA bB χ α (v * s) = 0 by simpa using key 1
  induction hs using Submodule.span_induction with
  | mem s hs =>
    obtain ⟨x, rfl⟩ := hs
    intro v
    dsimp only
    have hx : _root_.UniversalEnvelopingAlgebra.ι R (x : L) - algebraMap R U (χ x) =
        map R B.incl (_root_.UniversalEnvelopingAlgebra.ι R x -
          algebraMap R (_root_.UniversalEnvelopingAlgebra R B) (χ x)) := by
      rw [map_sub, map_ι, AlgHom.commutes, LieSubalgebra.coe_incl]
    rw [hx, _root_.UniversalEnvelopingAlgebra.characterForm_mul_map]
    simp
  | zero => simp
  | add s t _ _ hs ht => simp [mul_add, hs, ht]
  | smul a s _ hs =>
    intro v
    rw [smul_eq_mul, ← mul_assoc]
    exact hs _

include hA bA bB in
/-- The left ideal generated by `ι x - χ x` is proper, given ordered bases of `B` and of a
complement. -/
private theorem span_range_ι_sub_algebraMap_ne_top_of_basis [Nontrivial R] :
    Submodule.span U (Set.range fun x : B ↦
      _root_.UniversalEnvelopingAlgebra.ι R (x : L) - algebraMap R U (χ x)) ≠ ⊤ := by
  intro htop
  have h1 := characterForm_eq_zero_of_mem_span B hA bA bB χ 0 (htop ▸ Submodule.mem_top (x := 1))
  rw [characterForm_one] at h1
  exact one_ne_zero h1

/-- On the image of `U(A)` for a Lie subalgebra `A` complementing `B`, the character form of
index `α` is the coefficient of the ordered monomial of exponents `α`. -/
private theorem characterForm_map_incl {A : LieSubalgebra R L}
    (hA : IsCompl (A : Submodule R L) (B : Submodule R L)) (bA : Basis ιA R A) (α : ιA →₀ ℕ)
    (y : _root_.UniversalEnvelopingAlgebra R A) :
    characterForm B hA bA bB χ α (map R A.incl y) = bA.pbwBasis.repr y α := by
  have hlin := bA.pbwBasis.ext
    (f₁ := characterForm B hA bA bB χ α ∘ₗ (map R A.incl).toLinearMap)
    (f₂ := Finsupp.lapply α ∘ₗ bA.pbwBasis.repr.toLinearMap) fun α' ↦ by
      have hmon : map R A.incl (bA.pbwBasis α') =
          complementMonomial (A := (A : Submodule R L)) bA α' * map R B.incl 1 := by
        rw [map_one, mul_one, complementMonomial, Basis.pbwBasis_apply, map_pbwMonomial]
        simp only [pbwMonomial_def, List.map_map, Function.comp_def, LieSubalgebra.coe_incl]
      simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, LinearEquiv.coe_coe,
        Basis.repr_self, Finsupp.lapply_apply, Finsupp.single_apply]
      rw [hmon, _root_.UniversalEnvelopingAlgebra.characterForm_complementMonomial_mul, map_one]
  exact LinearMap.congr_fun hlin y

end Adapted

section Induced

variable (B : LieSubalgebra R L) (χ : LieCharacter R B)

/-- **`U(B)` acts on the induced module through the character.** For every `r` in `U(B)`, the
image of `r` in `U(L)` is congruent to the scalar `χ r` modulo the left ideal generated by the
elements `ι x - χ x`, for `x : B`. In the induced module `U(L) ⊗_{U(B)} R_χ` this says that `r`
acts on the canonical generator by `χ r`. -/
theorem map_sub_algebraMap_lift_mem_span_range_ι_sub_algebraMap
    (r : _root_.UniversalEnvelopingAlgebra R B) :
    map R B.incl r - algebraMap R U (_root_.UniversalEnvelopingAlgebra.lift R χ r) ∈
      Submodule.span U (Set.range fun x : B ↦
        _root_.UniversalEnvelopingAlgebra.ι R (x : L) - algebraMap R U (χ x)) := by
  induction r using induction_ι with
  | ι x =>
    rw [map_ι, _root_.UniversalEnvelopingAlgebra.lift_ι_apply]
    exact Submodule.subset_span ⟨x, rfl⟩
  | algebraMap r => simp
  | add a b ha hb =>
    convert add_mem ha hb using 1
    simp only [map_add]
    abel
  | mul a b ha hb =>
    -- `a b - χ(a) χ(b) = a (b - χ(b)) + χ(b) (a - χ(a))`
    convert add_mem (Submodule.smul_mem _ (map R B.incl a) hb)
      (Submodule.smul_of_tower_mem _ (_root_.UniversalEnvelopingAlgebra.lift R χ b) ha) using 1
    simp only [map_mul, smul_eq_mul, mul_sub, Algebra.smul_def,
      ← Algebra.commutes (_root_.UniversalEnvelopingAlgebra.lift R χ b) (map R B.incl a)]
    rw [← map_mul (algebraMap R U), ← map_mul (algebraMap R U),
      mul_comm (_root_.UniversalEnvelopingAlgebra.lift R χ a)]
    abel

variable {B} in
/-- **The induced module is spanned by the image of `U(A)`** when the Lie subalgebras `A` and `B`
together span `L`: every element of `U(L)` is congruent to an element of `U(A)` modulo the left
ideal generated by the elements `ι x - χ x`, for `x : B`. In the induced module
`U(L) ⊗_{U(B)} R_χ` this says that the canonical generator generates it over `U(A)`. -/
theorem exists_sub_map_mem_span_range_ι_sub_algebraMap {A : LieSubalgebra R L}
    (hAB : (A : Submodule R L) ⊔ (B : Submodule R L) = ⊤) (u : U) :
    ∃ y : _root_.UniversalEnvelopingAlgebra R A,
      u - map R A.incl y ∈ Submodule.span U (Set.range fun x : B ↦
        _root_.UniversalEnvelopingAlgebra.ι R (x : L) - algebraMap R U (χ x)) := by
  set I := Submodule.span U (Set.range fun x : B ↦
    _root_.UniversalEnvelopingAlgebra.ι R (x : L) - algebraMap R U (χ x))
  -- The elements congruent to an element of `U(A)` contain every product `U(A) · U(B)`.
  have htop : I.restrictScalars R ⊔ LinearMap.range (map R A.incl).toLinearMap = ⊤ := by
    rw [eq_top_iff, ← envelopingSubalgebra_mul_envelopingSubalgebra_eq_top hAB, Submodule.mul_le]
    intro m hm n hn
    obtain ⟨y, rfl⟩ := (mem_envelopingSubalgebra_iff R).mp ((Subalgebra.mem_toSubmodule _).mp hm)
    obtain ⟨r, rfl⟩ := (mem_envelopingSubalgebra_iff R).mp ((Subalgebra.mem_toSubmodule _).mp hn)
    have hsplit : map R A.incl y * map R B.incl r =
        map R A.incl y * (map R B.incl r -
          algebraMap R U (_root_.UniversalEnvelopingAlgebra.lift R χ r)) +
          map R A.incl (_root_.UniversalEnvelopingAlgebra.lift R χ r • y) := by
      rw [mul_sub, map_smul, Algebra.smul_def, Algebra.commutes, sub_add_cancel]
    rw [hsplit]
    exact Submodule.add_mem_sup (Submodule.smul_mem I _
      (map_sub_algebraMap_lift_mem_span_range_ι_sub_algebraMap B χ r))
      (LinearMap.mem_range_self _ _)
  obtain ⟨i, hi, w, ⟨y, rfl⟩, hu⟩ := Submodule.mem_sup.mp (htop ▸ Submodule.mem_top (x := u))
  exact ⟨y, by simpa [← hu] using hi⟩

variable {B} in
/-- **The image of `U(A)` meets the induced relations only in zero** when the Lie subalgebra `A`
is a complement of `B` and both are free: an element of `U(A)` whose image lies in the left
ideal generated by the elements `ι x - χ x`, for `x : B`, is zero. Together with
`TauCeti.UniversalEnvelopingAlgebra.exists_sub_map_mem_span_range_ι_sub_algebraMap` this says
that the induced module `U(L) ⊗_{U(B)} R_χ` is a free `U(A)`-module of rank one on its canonical
generator. -/
theorem map_mem_span_range_ι_sub_algebraMap_iff_of_isCompl {A : LieSubalgebra R L}
    (hAB : IsCompl (A : Submodule R L) (B : Submodule R L)) [Module.Free R A] [Module.Free R B]
    {y : _root_.UniversalEnvelopingAlgebra R A} :
    map R A.incl y ∈ Submodule.span U (Set.range fun x : B ↦
      _root_.UniversalEnvelopingAlgebra.ι R (x : L) - algebraMap R U (χ x)) ↔ y = 0 := by
  refine ⟨fun hy ↦ ?_, fun hy ↦ hy ▸ by simp⟩
  let _ : LinearOrder (Module.Free.ChooseBasisIndex R A) := IsWellOrder.linearOrder WellOrderingRel
  let _ : LinearOrder (Module.Free.ChooseBasisIndex R B) := IsWellOrder.linearOrder WellOrderingRel
  refine (Module.Free.chooseBasis R A).pbwBasis.repr.injective (Finsupp.ext fun α ↦ ?_)
  rw [← characterForm_map_incl B (Module.Free.chooseBasis R B) χ hAB,
    characterForm_eq_zero_of_mem_span B hAB _ _ χ α hy, map_zero, Finsupp.zero_apply]

end Induced

section Free

variable (B : LieSubalgebra R L) (χ : LieCharacter R B)

/-- **A character of a Lie subalgebra generates a proper left ideal.** If the Lie subalgebra `B`
of `L` has a complement `A` and both are free, then for every character `χ` of `B` the elements
`ι x - χ x` of `U(L)`, for `x : B`, generate a proper left ideal of `U(L)`. Equivalently, the
induced module `U(L) ⊗_{U(B)} R_χ` is nonzero. -/
theorem span_range_ι_sub_algebraMap_ne_top_of_isCompl [Nontrivial R] {A : Submodule R L}
    (hA : IsCompl A (B : Submodule R L)) [Module.Free R A] [Module.Free R B] :
    Submodule.span U (Set.range fun x : B ↦
      _root_.UniversalEnvelopingAlgebra.ι R (x : L) - algebraMap R U (χ x)) ≠ ⊤ := by
  let _ : LinearOrder (Module.Free.ChooseBasisIndex R A) := IsWellOrder.linearOrder WellOrderingRel
  let _ : LinearOrder (Module.Free.ChooseBasisIndex R B) := IsWellOrder.linearOrder WellOrderingRel
  exact span_range_ι_sub_algebraMap_ne_top_of_basis B hA (Module.Free.chooseBasis R A)
    (Module.Free.chooseBasis R B) χ

end Free

section Field

/-- **A character of a Lie subalgebra generates a proper left ideal, over a field.** For every
Lie subalgebra `B` of a Lie algebra `L` over a field and every character `χ` of `B`, the elements
`ι x - χ x` of `U(L)`, for `x : B`, generate a proper left ideal of `U(L)`. -/
theorem span_range_ι_sub_algebraMap_ne_top {K : Type u} {L : Type v} [Field K] [LieRing L]
    [LieAlgebra K L] (B : LieSubalgebra K L) (χ : LieCharacter K B) :
    Submodule.span (_root_.UniversalEnvelopingAlgebra K L) (Set.range fun x : B ↦
      _root_.UniversalEnvelopingAlgebra.ι K (x : L) -
        algebraMap K (_root_.UniversalEnvelopingAlgebra K L) (χ x)) ≠ ⊤ := by
  obtain ⟨A, hA⟩ := Submodule.exists_isCompl (B : Submodule K L)
  exact span_range_ι_sub_algebraMap_ne_top_of_isCompl B χ hA.symm

end Field

end TauCeti.UniversalEnvelopingAlgebra
