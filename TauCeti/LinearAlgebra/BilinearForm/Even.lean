/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.BilinearForm.Modular
public import Mathlib.Algebra.DirectSum.Module
import TauCeti.LinearAlgebra.BilinearForm.Orthogonal
import TauCeti.LinearAlgebra.Submodule.Compl
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Binary decomposition of even unimodular forms

Over a local ring, a symmetric perfect pairing on a finite free module whose diagonal values
are all nonunits is an orthogonal sum of binary perfect pairings. This includes even forms
when two is not a unit. Each summand comes with a two-element basis, so this is a decomposition
of the actual module, not just an equality of ranks. In
particular its rank is even. The empty decomposition covers the zero module.

These binary constituents are the inputs to the classification of even unimodular dyadic
lattices. No inverse of two, domain hypothesis, or completeness assumption is used here.

The splitting construction uses the unit-Gram criterion
`LinearMap.BilinForm.isModular_restrict_span_range` and the perfect-restriction splitting theorem
`LinearMap.BilinForm.isCompl_orthogonal_of_restrict_bijective`.

## References

* O. T. O'Meara, *Introduction to Quadratic Forms*, §93A.
* J. W. S. Cassels, *Rational Quadratic Forms*, Chapter 8, Lemma 4.1.
-/

public section

namespace LinearMap.BilinForm

open Module

variable {R M : Type*} [CommRing R] [IsLocalRing R] [AddCommGroup M] [Module R M]
  (B : LinearMap.BilinForm R M) [B.IsPerfPair]

/-- A symmetric perfect pairing with nonunit diagonal values splits off a binary perfect
pairing if some linear functional takes the value one. The summand is supplied with a basis
and is complementary to its orthogonal complement. -/
theorem IsSymm.exists_binary_isPerfPair_isCompl_orthogonal (hB : B.IsSymm)
    (hdiag : ∀ x, ¬ IsUnit (B x x)) (x : M) (f : Module.Dual R M) (hfx : f x = 1) :
    ∃ S : Submodule R M, Nonempty (Basis (Fin 2) R S) ∧
      (B.restrict S).IsPerfPair ∧ IsCompl S (B.orthogonal S) := by
  classical
  obtain ⟨w, hw⟩ := (LinearMap.IsPerfPair.bijective_left B).surjective f
  have hxw : B x w = 1 := by rw [hB.eq, hw, hfx]
  obtain ⟨hli, hmod⟩ := hB.linearIndependent_and_isModular_restrict_span_pair (one_mem _)
    hxw (one_mul (B x x)).symm (one_mul (B w w)).symm
    (fun h ↦ hdiag x (isUnit_of_mul_isUnit_left h))
  have hp := isModular_one_iff.mp hmod
  exact ⟨_, ⟨Basis.span hli⟩, hp,
    B.isCompl_orthogonal_of_restrict_bijective _ (hB.restrict _)
      (LinearMap.IsPerfPair.bijective_left _)⟩

/-- A symmetric perfect pairing with nonunit diagonal values over a local ring is an internal
orthogonal sum of binary perfect pairings. Each constituent has a two-element basis. -/
theorem IsSymm.exists_binary_orthogonal_decomposition [Free R M] [Module.Finite R M]
    (hB : B.IsSymm) (hdiag : ∀ x, ¬ IsUnit (B x x)) :
    ∃ k : ℕ, ∃ N : Fin k → Submodule R M,
      DirectSum.IsInternal N ∧
      (∀ i j, i ≠ j → ∀ x ∈ N i, ∀ y ∈ N j, B x y = 0) ∧
      ∀ i, Nonempty (Basis (Fin 2) R (N i)) ∧ (B.restrict (N i)).IsPerfPair := by
  classical
  induction hn : finrank R M using Nat.strong_induction_on generalizing M with
  | _ n ih =>
    by_cases hzero : n = 0
    · have : Subsingleton M := (Module.finrank_eq_zero_iff_of_free R M).mp (hn.trans hzero)
      refine ⟨0, Fin.elim0, ?_, fun i ↦ i.elim0, fun i ↦ i.elim0⟩
      apply (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top _).mpr
      exact ⟨by simp [iSupIndep], Subsingleton.elim _ _⟩
    have hpos : 0 < finrank R M := by omega
    let b := Module.finBasisOfFinrankEq R M (Nat.succ_pred_eq_of_pos hpos).symm
    obtain ⟨S, ⟨c⟩, hS, hc⟩ := hB.exists_binary_isPerfPair_isCompl_orthogonal B hdiag
      (b 0) (b.coord 0) (by simp)
    -- The complement is finite free because it is a retract over a local ring.
    let T := B.orthogonal S
    have : Module.Finite R S := .of_basis c
    have : Free R S := .of_basis c
    obtain ⟨hfinite, hfree⟩ := T.finite_free_of_isCompl hc.symm
    have hdouble := B.orthogonal_orthogonal_of_isCompl hB.isRefl
      (LinearMap.IsPerfPair.separatingRight (p := B) inferInstance) S hc
    have : (B.restrict T).IsPerfPair :=
      B.isPerfPair_restrict_of_isCompl_orthogonal hB T (by rw [hdouble]; exact hc.symm)
    have hsmall : finrank R T < n := by
      have hrank := (S.prodEquivOfIsCompl T hc).finrank_eq
      have hSrank : finrank R S = 2 := by simpa using Module.finrank_eq_card_basis c
      rw [Module.finrank_prod, hSrank, hn] at hrank
      omega
    -- Remove the binary summand and apply induction to the smaller perfect complement.
    obtain ⟨k, N, hN, horth, hperf⟩ := ih _ hsmall (B := B.restrict T)
      (hB.restrict T) (fun x ↦ hdiag x) rfl
    let P : Fin (k + 1) → Submodule R M := Fin.cons S (fun i ↦ (N i).map T.subtype)
    obtain ⟨hP, horthP⟩ := hB.isRefl.isInternal_orthogonal_finCons S hc N hN horth
    have hperfP : ∀ i, Nonempty (Basis (Fin 2) R (P i)) ∧
        (B.restrict (P i)).IsPerfPair := by
      refine Fin.cases ⟨⟨c⟩, hS⟩ fun i ↦ ?_
      let e := Submodule.equivMapOfInjective T.subtype T.injective_subtype (N i)
      obtain ⟨⟨d⟩, hd⟩ := hperf i
      refine ⟨⟨d.map e⟩, ?_⟩
      exact isModular_one_iff.mp (isModular_restrict_map_subtype_iff.mpr
        (isModular_one_iff.mpr hd))
    exact ⟨k + 1, P, hP, horthP, hperfP⟩

/-- A symmetric perfect pairing with nonunit diagonal values on a finite free module over a
local ring has even rank. In particular this holds for even forms when two is not a unit. -/
theorem IsSymm.even_finrank_of_isPerfPair [Free R M] [Module.Finite R M]
    (hB : B.IsSymm) (hdiag : ∀ x, ¬ IsUnit (B x x)) :
    Even (finrank R M) := by
  classical
  obtain ⟨k, N, hN, -, hc⟩ := hB.exists_binary_orthogonal_decomposition B hdiag
  let c : ∀ i, Basis (Fin 2) R (N i) := fun i ↦ Classical.choice (hc i).1
  have hrank := Module.finrank_eq_card_basis (hN.collectedBasis c)
  refine ⟨k, ?_⟩
  simpa [Fintype.card_sigma, mul_two] using hrank

end LinearMap.BilinForm
