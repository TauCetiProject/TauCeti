/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.BilinearForm.Modular
public import Mathlib.Algebra.DirectSum.Module
import TauCeti.LinearAlgebra.BilinearForm.LinearIndependent
import TauCeti.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Binary decomposition of even unimodular forms

Over a local ring where two is not a unit, an even symmetric perfect pairing on a finite free
module is an orthogonal sum of binary perfect pairings. Each summand comes with a two-element
basis, so this is a decomposition of the actual module, not just an equality of ranks. In
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

/-- A positive-rank even symmetric perfect pairing splits off a binary perfect pairing.
The summand is supplied with a basis and is complementary to its orthogonal complement. -/
theorem IsSymm.exists_binary_isPerfPair_isCompl_orthogonal (hB : B.IsSymm)
    (heven : ∀ x, (2 : R) ∣ B x x) (h2 : ¬ IsUnit (2 : R))
    {n : ℕ} (b : Basis (Fin (n + 1)) R M) :
    ∃ S : Submodule R M, Nonempty (Basis (Fin 2) R S) ∧
      (B.restrict S).IsPerfPair ∧ IsCompl S (B.orthogonal S) := by
  classical
  -- Represent the first coordinate functional, giving a pair with cross-pairing one.
  obtain ⟨w, hw⟩ := (LinearMap.IsPerfPair.bijective_left B).surjective (b.coord 0)
  have huw : B (b 0) w = 1 := by
    rw [hB.eq, hw]
    simp
  have hdiag : ∀ x, ¬ IsUnit (B x x) := fun x hx ↦ h2 (isUnit_of_dvd_unit (heven x) hx)
  have hunit : IsUnit (B (b 0) (b 0) * B w w - 1) := by
    rw [← neg_sub]
    exact (IsLocalRing.isUnit_one_sub_self_of_mem_nonunits _
      (mem_nonunits_iff.mpr fun h ↦ hdiag _ (isUnit_of_mul_isUnit_left h))).neg
  let v : Fin 2 → M := ![b 0, w]
  let G : Matrix (Fin 2) (Fin 2) R := !![B (b 0) (b 0), 1; 1, B w w]
  have hG : ∀ i j, B (v i) (v j) = 1 * G i j := by
    intro i j
    fin_cases i <;> fin_cases j <;> simp [v, G, huw, hB.eq w (b 0)]
  have hdet : IsUnit G.det := by simpa [G, Matrix.det_fin_two] using hunit
  let c := Basis.span (linearIndependent_of_isUnit_det (B := B)
    (a := 1) (one_mem _) hG hdet)
  have hp : (B.restrict (Submodule.span R (Set.range v))).IsPerfPair :=
    isModular_one_iff.mp (isModular_restrict_span_range (one_mem _) hG hdet)
  exact ⟨_, ⟨c⟩, hp,
    B.isCompl_orthogonal_of_restrict_bijective _ (hB.restrict _)
      (LinearMap.IsPerfPair.bijective_left _)⟩

/-- An even symmetric perfect pairing over a local ring with two noninvertible is an internal
orthogonal sum of binary perfect pairings. Each constituent has a two-element basis. -/
theorem IsSymm.exists_binary_orthogonal_decomposition [Free R M] [Module.Finite R M]
    (hB : B.IsSymm) (heven : ∀ x, (2 : R) ∣ B x x) (h2 : ¬ IsUnit (2 : R)) :
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
    obtain ⟨S, ⟨c⟩, hS, hc⟩ := hB.exists_binary_isPerfPair_isCompl_orthogonal B heven h2 b
    -- The complement is finite free because it is a retract over a local ring.
    let T := B.orthogonal S
    have : Module.Finite R S := .of_basis c
    have : Free R S := .of_basis c
    have : Module.Finite R T := .equiv (Submodule.quotientEquivOfIsCompl _ _ hc)
    have : Module.Flat R T := Module.Flat.of_retract T.subtype
      (T.projectionOnto S hc.symm) (by ext; simp)
    have : Free R T := free_of_flat_of_isLocalRing
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
      (hB.restrict T) (fun x ↦ heven x) rfl
    let P : Fin (k + 1) → Submodule R M := Fin.cons S (fun i ↦ (N i).map T.subtype)
    have hST : ∀ x ∈ S, ∀ y ∈ T, B x y = 0 := fun x hx y hy ↦ hy x hx
    have horthP : ∀ i j, i ≠ j → ∀ x ∈ P i, ∀ y ∈ P j, B x y = 0 := by
      intro i j
      refine Fin.cases ?_ (fun i ↦ ?_) i <;> refine Fin.cases ?_ (fun j ↦ ?_) j
      all_goals intro hij
      · exact (hij rfl).elim
      · rintro x hx _ ⟨y, hy, rfl⟩
        exact hST x hx y y.2
      · rintro _ ⟨x, hx, rfl⟩ y hy
        exact hB.isRefl.eq_zero (hST y hy x x.2)
      · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
        exact horth i j (fun h ↦ hij (congrArg Fin.succ h)) x hx y hy
    have hperfP : ∀ i, Nonempty (Basis (Fin 2) R (P i)) ∧
        (B.restrict (P i)).IsPerfPair := by
      refine Fin.cases ⟨⟨c⟩, hS⟩ fun i ↦ ?_
      let e := Submodule.equivMapOfInjective T.subtype T.injective_subtype (N i)
      obtain ⟨⟨d⟩, hd⟩ := hperf i
      refine ⟨⟨d.map e⟩, ?_⟩
      exact isModular_one_iff.mp (isModular_restrict_map_subtype_iff.mpr
        (isModular_one_iff.mpr hd))
    have htop : iSup P = ⊤ := by
      have hT : (⨆ i, (N i).map T.subtype) = T := by
        rw [← Submodule.map_iSup, hN.submodule_iSup_eq_top,
          Submodule.map_top, Submodule.range_subtype]
      apply eq_top_iff.mpr
      rw [← hc.sup_eq_top]
      refine sup_le (le_iSup P 0) ?_
      exact hT.symm.trans_le (iSup_le fun i ↦ le_iSup P i.succ)
    -- Orthogonality and separation make the spanning family an internal direct sum.
    refine ⟨k + 1, P, ?_, horthP, hperfP⟩
    exact (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top _).mpr
      ⟨B.iSupIndep_of_restrict_separatingRight horthP
        (fun i ↦ (LinearMap.IsPerfPair.nondegenerate (hperfP i).2).2), htop⟩

/-- An even symmetric perfect pairing on a finite free module over a local ring where two is
not a unit has even rank. -/
theorem IsSymm.even_finrank_of_isPerfPair [Free R M] [Module.Finite R M]
    (hB : B.IsSymm) (heven : ∀ x, (2 : R) ∣ B x x) (h2 : ¬ IsUnit (2 : R)) :
    Even (finrank R M) := by
  classical
  obtain ⟨k, N, hN, -, hc⟩ := hB.exists_binary_orthogonal_decomposition B heven h2
  let c : ∀ i, Basis (Fin 2) R (N i) := fun i ↦ Classical.choice (hc i).1
  have hrank := Module.finrank_eq_card_basis (hN.collectedBasis c)
  refine ⟨k, ?_⟩
  simpa [Fintype.card_sigma, mul_two] using hrank

end LinearMap.BilinForm
