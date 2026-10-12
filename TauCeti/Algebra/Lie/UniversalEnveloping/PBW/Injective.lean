/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.UniversalEnveloping.PBW.Homogeneous
public import TauCeti.Algebra.Lie.UniversalEnveloping.PBW.Evaluation
public import TauCeti.LinearAlgebra.SymmetricAlgebra.BasisComparison

/-!
# The Poincaré--Birkhoff--Witt theorem

For a Lie algebra `L` over a commutative ring `R` that is free as an `R`-module, the canonical
algebra map

`Sym(L) → gr U(L)`

from the symmetric algebra to the associated graded of the PBW filtration is an isomorphism. It
is surjective for every `L`
(`TauCeti.UniversalEnvelopingAlgebra.pbwAssociatedGradedMap_surjective`); this file proves
injectivity, the linear-independence half of the theorem.

## The argument

Choose a basis `b` of `L` indexed by a linearly ordered type, and let `U(L)` act on the polynomial
algebra `S` through the PBW representation `Module.Basis.pbwPolynomialRep` of
`TauCeti/Algebra/Lie/UniversalEnveloping/PBW/PolynomialRep.lean`. Evaluating that action at `1`
sends the PBW filtration step `Uₙ` into the polynomials of total degree at most `n`, and sends a
word `ι(x₁) ⋯ ι(xₙ)` to the product of the linear forms `zₓ₁ ⋯ zₓₙ` up to terms of lower degree.
Taking the degree-`n` homogeneous component therefore kills `Uₙ₋₁` and descends to a linear map
on the `n`-th graded piece, which composed with the degree-`n` component of `Sym(L) → gr U(L)`
is the polynomial algebra isomorphism `Sym(L) ≃ S` attached to `b`. A map with an injective
composite is injective.

## Main results

* `TauCeti.UniversalEnvelopingAlgebra.pbwHomogeneousComponentMap_injective`: every degreewise
  component of the canonical map is injective.
* `TauCeti.UniversalEnvelopingAlgebra.pbwAssociatedGradedMap_injective`: the canonical map
  `Sym(L) → gr U(L)` is injective.
* `TauCeti.UniversalEnvelopingAlgebra.pbwAssociatedGradedEquiv`: **the Poincaré--Birkhoff--Witt
  theorem**, the algebra isomorphism `Sym(L) ≃ₐ[R] gr U(L)` for free `L`.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, Chapter V, §17.4.
* N. Bourbaki, *Lie Groups and Lie Algebras*, Chapter I, §2.7.
-/

public section

open MvPolynomial

namespace TauCeti.UniversalEnvelopingAlgebra

open TauCeti.Algebra
open TauCeti.Algebra.wordFiltration
open TauCeti.SymmetricAlgebra

universe u v w

variable (R : Type u) (L : Type v) [CommRing R] [LieRing L] [LieAlgebra R L]

attribute [local instance 100] LieRing.ofAssociativeRing

local notation "U" => _root_.UniversalEnvelopingAlgebra R L

section Basis

variable {R L} {ι : Type w} [LinearOrder ι] (b : Module.Basis ι R L)

/-- Multiplying by a linear form raises total degree by at most one. -/
private theorem constr_X_mul_mem {d : ℕ} (x : L) {p : MvPolynomial ι R}
    (hp : p ∈ restrictTotalDegree ι R d) :
    b.constr R X x * p ∈ restrictTotalDegree ι R (d + 1) := by
  have h := Submodule.sub_mem _ (b.pbwPolynomialRep_mem_restrictTotalDegree x hp)
    ((restrictTotalDegree_mono ι R (Nat.le_succ d))
      (b.pbwPolynomialRep_sub_mul_mem_restrictTotalDegree x hp))
  rwa [sub_sub_cancel] at h

private theorem pbwEval_prod_mem (l : List L) :
    b.pbwEval (l.map (_root_.UniversalEnvelopingAlgebra.ι R)).prod ∈
      restrictTotalDegree ι R l.length := by
  induction l with
  | nil =>
      rw [List.map_nil, List.prod_nil, Module.Basis.pbwEval_one, mem_restrictTotalDegree,
        totalDegree_one]
      exact Nat.zero_le _
  | cons x l ih =>
      rw [List.map_cons, List.prod_cons, Module.Basis.pbwEval_ι_mul, List.length_cons]
      exact b.pbwPolynomialRep_mem_restrictTotalDegree x ih

private theorem pbwEval_mem {n : ℕ} {a : U} (ha : a ∈ pbwFiltration R L n) :
    b.pbwEval a ∈ restrictTotalDegree ι R n := by
  have : pbwFiltration R L n ≤ (restrictTotalDegree ι R n).comap (b.pbwEval) :=
    (pbwFiltration_le_iff R L).2 fun l hl ↦
      restrictTotalDegree_mono ι R hl (pbwEval_prod_mem b l)
  exact this ha

/-- A word of length `n + 1` evaluates to the product of its linear forms, up to total degree at
most `n`. -/
private theorem pbwEval_prod_sub_mem (x : L) (l : List L) :
    b.pbwEval ((x :: l).map (_root_.UniversalEnvelopingAlgebra.ι R)).prod -
        ((x :: l).map (b.constr R X)).prod ∈ restrictTotalDegree ι R l.length := by
  induction l generalizing x with
  | nil =>
      simpa only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
        Module.Basis.pbwEval_ι_mul,
        Module.Basis.pbwEval_one, List.length_nil] using
        b.pbwPolynomialRep_sub_mul_mem_restrictTotalDegree x
          ((mem_restrictTotalDegree ι 0 (1 : MvPolynomial ι R)).2 totalDegree_one.le)
  | cons y l ih =>
      rw [List.map_cons, List.prod_cons, Module.Basis.pbwEval_ι_mul, List.map_cons, List.prod_cons,
        List.length_cons]
      have h := Submodule.add_mem _
        (b.pbwPolynomialRep_sub_mul_mem_restrictTotalDegree x (pbwEval_prod_mem b (y :: l)))
        (constr_X_mul_mem b x (ih y))
      rwa [mul_sub, sub_add_sub_cancel] at h

/-- The degree-`n` homogeneous component of the evaluation, as a linear map on the `n`-th PBW
graded piece. It kills the preceding filtration step because the evaluation sends it into total
degree less than `n`. -/
private noncomputable def pbwSymbol (n : ℕ) : PBWGradedPiece R L n →ₗ[R] MvPolynomial ι R :=
  (previousRestricted (_root_.UniversalEnvelopingAlgebra.ι R (L := L)).toLinearMap n).liftQ
    (homogeneousComponent n ∘ₗ b.pbwEval ∘ₗ
      (wordFiltration (_root_.UniversalEnvelopingAlgebra.ι R (L := L)).toLinearMap n).subtype)
    (by
      intro a ha
      rw [mem_previousRestricted_iff] at ha
      rw [LinearMap.mem_ker, LinearMap.comp_apply, LinearMap.comp_apply]
      cases n with
      | zero =>
          rw [wordFiltrationPrevious_zero, Submodule.mem_bot] at ha
          rw [Submodule.subtype_apply, ha, map_zero, map_zero]
      | succ k =>
          rw [wordFiltrationPrevious_succ, ← pbwFiltration_def] at ha
          exact homogeneousComponent_eq_zero _ _
            (Nat.lt_succ_of_le ((mem_restrictTotalDegree ι k _).1 (pbwEval_mem b ha))))

private theorem pbwSymbol_mk_prod (l : List L) :
    pbwSymbol b l.length (Submodule.Quotient.mk
      (⟨(l.map (_root_.UniversalEnvelopingAlgebra.ι R)).prod,
        prod_map_mem_wordFiltration
          (_root_.UniversalEnvelopingAlgebra.ι R (L := L)).toLinearMap le_rfl⟩ :
        wordFiltration (_root_.UniversalEnvelopingAlgebra.ι R (L := L)).toLinearMap l.length)) =
      SymmetricAlgebra.equivMvPolynomial b (l.map (SymmetricAlgebra.ι R L)).prod := by
  have hhom : (SymmetricAlgebra.equivMvPolynomial b
      (l.map (SymmetricAlgebra.ι R L)).prod).IsHomogeneous l.length :=
    (SymmetricAlgebra.equivMvPolynomial_isHomogeneous_iff R L b _ _).2
      (prod_map_ι_mem_homogeneousSubmodule R L l)
  have hprod : SymmetricAlgebra.equivMvPolynomial b (l.map (SymmetricAlgebra.ι R L)).prod =
      (l.map (b.constr R X)).prod := by
    rw [map_list_prod, List.map_map]
    exact congrArg List.prod
      (List.map_congr_left fun x _ ↦ SymmetricAlgebra.equivMvPolynomial_ι b x)
  rw [pbwSymbol, Submodule.liftQ_apply, LinearMap.comp_apply, LinearMap.comp_apply,
    Submodule.subtype_apply, Submodule.coe_mk]
  cases l with
  | nil => simp [Module.Basis.pbwEval_one]
  | cons x l =>
      rw [List.length_cons] at hhom ⊢
      rw [← sub_add_cancel (b.pbwEval _) ((x :: l).map (b.constr R X)).prod, map_add,
        homogeneousComponent_eq_zero _ _ (Nat.lt_succ_of_le ((mem_restrictTotalDegree ι _ _).1
          (pbwEval_prod_sub_mem b x l))), zero_add, ← hprod,
        homogeneousComponent_of_mem hhom, ite_eq_left rfl]

/-- The degree-`n` symbol is a left inverse of the degree-`n` component of the canonical map, up
to the polynomial algebra isomorphism attached to `b`. -/
private theorem pbwSymbol_pbwHomogeneousComponentMap (n : ℕ) (p : homogeneousSubmodule R L n) :
    pbwSymbol b n (pbwHomogeneousComponentMap R L n p) =
      SymmetricAlgebra.equivMvPolynomial b p := by
  obtain ⟨p, hp⟩ := p
  have hS := homogeneousSubmodule_eq_span R L n
  have hspan := hS ▸ hp
  induction hspan using Submodule.span_induction with
  | mem q hq =>
      obtain ⟨l, rfl, rfl⟩ := hq
      rw [pbwHomogeneousComponentMap_prod_map_ι, pbwSymbol_mk_prod]
  | zero =>
      have h0 : (⟨0, hp⟩ : homogeneousSubmodule R L n) = 0 := rfl
      rw [h0, map_zero, map_zero, Submodule.coe_zero, map_zero]
  | add q r hq hr ihq ihr =>
      have hadd : (⟨q + r, hp⟩ : homogeneousSubmodule R L n) = ⟨q, hS ▸ hq⟩ + ⟨r, hS ▸ hr⟩ := rfl
      rw [hadd, map_add, map_add, ihq, ihr, Submodule.coe_add, map_add]
  | smul c q hq ihq =>
      have hsmul : (⟨c • q, hp⟩ : homogeneousSubmodule R L n) = c • ⟨q, hS ▸ hq⟩ := rfl
      rw [hsmul, map_smul, map_smul, ihq, Submodule.coe_smul, map_smul]

include b in
private theorem pbwHomogeneousComponentMap_injective_of_basis (n : ℕ) :
    Function.Injective (pbwHomogeneousComponentMap R L n) := by
  intro p q h
  have := congrArg (pbwSymbol b n) h
  rw [pbwSymbol_pbwHomogeneousComponentMap, pbwSymbol_pbwHomogeneousComponentMap] at this
  exact Subtype.ext ((SymmetricAlgebra.equivMvPolynomial b).injective this)

end Basis

variable [Module.Free R L]

/-- Every degreewise component of the canonical map `Sym(L) → gr U(L)` is injective when `L` is a
free module. -/
theorem pbwHomogeneousComponentMap_injective (n : ℕ) :
    Function.Injective (pbwHomogeneousComponentMap R L n) :=
  letI : LinearOrder (Module.Free.ChooseBasisIndex R L) := IsWellOrder.linearOrder WellOrderingRel
  pbwHomogeneousComponentMap_injective_of_basis (Module.Free.chooseBasis R L) n

/-- **The linear-independence half of the Poincaré--Birkhoff--Witt theorem.** The canonical map
`Sym(L) → gr U(L)` is injective when `L` is a free module. -/
theorem pbwAssociatedGradedMap_injective : Function.Injective (pbwAssociatedGradedMap R L) :=
  (pbwAssociatedGradedMap_injective_iff R L).2 (pbwHomogeneousComponentMap_injective R L)

/-- The canonical map `Sym(L) → gr U(L)` is bijective when `L` is a free module. -/
theorem pbwAssociatedGradedMap_bijective : Function.Bijective (pbwAssociatedGradedMap R L) :=
  ⟨pbwAssociatedGradedMap_injective R L, pbwAssociatedGradedMap_surjective R L⟩

/-- **The Poincaré--Birkhoff--Witt theorem.** For a Lie algebra that is free as a module, the
symmetric algebra is isomorphic to the associated graded of the PBW filtration of the enveloping
algebra, by the algebra map sending `x ∈ L` to the degree-one class of `ι(x)`. -/
noncomputable def pbwAssociatedGradedEquiv : SymmetricAlgebra R L ≃ₐ[R] PBWAssociatedGraded R L :=
  AlgEquiv.ofBijective (pbwAssociatedGradedMap R L) (pbwAssociatedGradedMap_bijective R L)

@[simp]
theorem coe_pbwAssociatedGradedEquiv :
    ⇑(pbwAssociatedGradedEquiv R L) = pbwAssociatedGradedMap R L :=
  (rfl)

end TauCeti.UniversalEnvelopingAlgebra
