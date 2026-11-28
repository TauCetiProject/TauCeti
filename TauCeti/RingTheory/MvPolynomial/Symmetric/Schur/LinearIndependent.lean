/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.MvPolynomial.Symmetric.Schur.Basic
import TauCeti.Algebra.BigOperators.Finset.SDiff
import TauCeti.RingTheory.MvPolynomial.Symmetric.Schur.Symmetric

/-!
# Linear independence of Schur polynomials

This file proves that the Schur polynomials of shapes with at most as many rows (or parts) as
alphabet letters are linearly independent over any additively cancellative commutative semiring `R`
(`[CommSemiring R] [IsCancelAdd R]`), and derives `ℕ`-coefficient uniqueness for those bounded-row
Schur polynomials over any characteristic-zero commutative semiring (`[CharZero R]`).

Unlike the basis construction in `TauCeti/RingTheory/MvPolynomial/Symmetric/Schur/Basis.lean`
(which inverts the unitriangular Kostka matrix and therefore requires a commutative ring), linear
independence needs only `K_{μν} = 0` for `μ < ν` in lexicographic order (in fact `K_{μν} = 0`
unless `μ` dominates `ν`) and `K_{μμ} = 1`, together with additive cancellation.

## Main results

* `TauCeti.linearIndependent_schurPoly_of_card_le`: in an alphabet `σ`, the Schur polynomials of
  the partitions of `n` with at most `Fintype.card σ` parts are linearly independent over any
  additively cancellative commutative semiring.
* `TauCeti.linearIndependent_schurPoly`: in an alphabet with at least `n` letters, the Schur
  polynomials of all partitions of `n` are linearly independent over any additively cancellative
  commutative semiring.
* `TauCeti.linearIndependent_diagramSchurPoly_of_colLen_le`: in `N` variables, the diagram Schur
  polynomials of the partitions of `n` with at most `N` rows are linearly independent over any
  additively cancellative commutative semiring.
* `TauCeti.eq_of_sum_nsmul_schurPoly_eq_of_card_le` and `TauCeti.eq_of_sum_nsmul_schurPoly_eq`:
  uniqueness of `ℕ`-coefficients in a bounded-part Schur expansion over any finite alphabet `σ` and
  any characteristic-zero commutative semiring.
* `TauCeti.eq_of_sum_nsmul_diagramSchurPoly_eq_of_colLen_le` and
  `TauCeti.eq_of_sum_nsmul_diagramSchurPoly_eq`: uniqueness of `ℕ`-coefficients in a bounded-row
  diagram Schur expansion over any characteristic-zero commutative semiring.
* `TauCeti.linearIndependent_diagramSchurPoly`: in `N` variables, the Schur polynomials of all
  Young diagrams with at most `N` rows, of every degree, are linearly independent over any
  additively cancellative commutative semiring.

## References

* [I. G. Macdonald, *Symmetric Functions and Hall Polynomials*][macdonald1995], Chapter I,
  Section 6.
* R. P. Stanley, *Enumerative Combinatorics*, Volume 2, §7.10.
-/

public section

namespace TauCeti

open Finset MvPolynomial

section LinearIndependent

variable {R : Type*} [CommSemiring R] {n : ℕ}

open scoped PartitionLex in
/-- The Schur polynomials of the partitions of `n` with at most `Fintype.card σ` parts are
linearly independent over any additively cancellative commutative semiring `R`. -/
theorem linearIndependent_schurPoly_of_card_le {σ : Type*} [Fintype σ] [IsCancelAdd R] :
    LinearIndependent R
      (fun ν : {ν : n.Partition // ν.parts.card ≤ Fintype.card σ} => schurPoly σ R ν.val) := by
  classical
  refine linearIndependent_iff'ₛ.mpr fun s g g' hsum μ hμ => ?_
  by_contra hne
  let t := s.filter fun ν => g ν ≠ g' ν
  have ht : t.Nonempty := ⟨μ, Finset.mem_filter.mpr ⟨hμ, hne⟩⟩
  let ξ := t.max' ht
  have hξt : ξ ∈ t := Finset.max'_mem t ht
  have hξne : g ξ ≠ g' ξ := (Finset.mem_filter.mp hξt).2
  have hcoeff := congrArg (fun p : MvPolynomial σ R => p.coeff (partWeight σ ξ.val)) hsum
  simp only [coeff_sum, AddMonoidAlgebra.coeff_smul_apply, smul_eq_mul] at hcoeff
  have hterm (ν : {ν : n.Partition // ν.parts.card ≤ Fintype.card σ}) :
      (schurPoly σ R ν.val).coeff (partWeight σ ξ.val) = (kostkaNumber ν.val ξ.val : R) :=
    coeff_schurPoly_partWeight ν.val ξ.val
      (by rw [YoungDiagram.colLen_zero_ofPartition]; exact ξ.property)
  simp_rw [hterm] at hcoeff
  rw [Finset.sum_eq_sum_iff_sdiff (Finset.filter_subset (fun ν => g ν = g' ν) s)
      (Finset.filter_subset (fun ν => g ν = g' ν) s)
      (Finset.sum_congr rfl fun ν hν => by rw [(Finset.mem_filter.mp hν).2]),
    ← Finset.filter_not] at hcoeff
  have htop (f : {ν : n.Partition // ν.parts.card ≤ Fintype.card σ} → R) :
      ∑ ν ∈ t, f ν * (kostkaNumber ν.val ξ.val : R) = f ξ := by
    refine (Finset.sum_eq_single ξ (fun ν hν hνξ => ?_) fun hξ' => absurd hξt hξ').trans ?_
    · have hlt : ν.val < ξ.val := lt_of_le_of_ne (Subtype.coe_le_coe.mpr (Finset.le_max' t ν hν))
        (fun h => hνξ (Subtype.ext h))
      rw [kostkaNumber_eq_zero_of_lt hlt, Nat.cast_zero, mul_zero]
    · rw [kostkaNumber_self, Nat.cast_one, mul_one]
  change ∑ ν ∈ t, g ν * (kostkaNumber ν.val ξ.val : R) =
      ∑ ν ∈ t, g' ν * (kostkaNumber ν.val ξ.val : R) at hcoeff
  rw [htop g, htop g'] at hcoeff
  exact hξne hcoeff

/-- Over an additively cancellative commutative semiring, in an alphabet with at least `n` letters,
the Schur polynomials of all partitions of `n` are linearly independent. -/
theorem linearIndependent_schurPoly {σ : Type*} [Fintype σ] [IsCancelAdd R]
    (h : n ≤ Fintype.card σ) :
    LinearIndependent R (schurPoly σ R : n.Partition → MvPolynomial σ R) :=
  linearIndependent_schurPoly_of_card_le.comp
    (fun μ : n.Partition => ⟨μ, μ.card_parts_le.trans h⟩)
    fun _ _ hμ => congrArg Subtype.val hμ

/-- Over an additively cancellative commutative semiring, in `N` variables, the diagram-indexed
Schur polynomials `s_ν` of the partitions `ν` of `n` with at most `N` rows are linearly
independent. -/
theorem linearIndependent_diagramSchurPoly_of_colLen_le [IsCancelAdd R] {N : ℕ} :
    LinearIndependent R
      (fun ν : {ν : n.Partition // (YoungDiagram.ofPartition ν).colLen 0 ≤ N} =>
        diagramSchurPoly N R (YoungDiagram.ofPartition ν.val)) := by
  let e : {ν : n.Partition // (YoungDiagram.ofPartition ν).colLen 0 ≤ N} ≃
      {ν : n.Partition // ν.parts.card ≤ Fintype.card (Fin N)} :=
    Equiv.subtypeEquivRight fun ν => by
      rw [YoungDiagram.colLen_zero_ofPartition, Fintype.card_fin]
  have heq :
      (fun ν : {ν : n.Partition // (YoungDiagram.ofPartition ν).colLen 0 ≤ N} =>
        diagramSchurPoly N R (YoungDiagram.ofPartition ν.val)) =
      (fun μ : {ν : n.Partition // ν.parts.card ≤ Fintype.card (Fin N)} =>
        schurPoly (Fin N) R μ.val) ∘ e := by
    funext ν
    simp only [Function.comp_apply, e, Equiv.subtypeEquivRight_apply,
      schurPoly_fin_eq_diagramSchurPoly]
  rw [heq]
  exact (linearIndependent_schurPoly_of_card_le (σ := Fin N) (R := R) (n := n)).comp e
    e.injective

/-- Over a characteristic-zero commutative semiring, a natural-number linear combination of the
Schur polynomials of the partitions of `n` with at most `Fintype.card σ` parts in the alphabet `σ`
determines its coefficients uniquely. -/
theorem eq_of_sum_nsmul_schurPoly_eq_of_card_le {σ : Type*} [Fintype σ] [CharZero R]
    {c c' : {ν : n.Partition // ν.parts.card ≤ Fintype.card σ} → ℕ}
    (heq :
      ∑ ν : {ν : n.Partition // ν.parts.card ≤ Fintype.card σ}, c ν • schurPoly σ R ν.val =
      ∑ ν : {ν : n.Partition // ν.parts.card ≤ Fintype.card σ}, c' ν • schurPoly σ R ν.val) :
    c = c' := by
  have hℕ :
      ∑ ν : {ν : n.Partition // ν.parts.card ≤ Fintype.card σ}, c ν • schurPoly σ ℕ ν.val =
      ∑ ν : {ν : n.Partition // ν.parts.card ≤ Fintype.card σ}, c' ν • schurPoly σ ℕ ν.val :=
    MvPolynomial.map_injective (Nat.castRingHom R) Nat.cast_injective <| by
      simpa only [map_sum, map_nsmul, map_schurPoly] using heq
  funext ν
  exact linearIndependent_iff'ₛ.mp
    (linearIndependent_schurPoly_of_card_le (R := ℕ))
    Finset.univ c c' hℕ ν (Finset.mem_univ ν)

/-- Over a characteristic-zero commutative semiring, a natural-number linear combination of the
Schur polynomials of the partitions of `n` in an alphabet `σ` with at least `n` letters determines
its coefficients uniquely. -/
theorem eq_of_sum_nsmul_schurPoly_eq {σ : Type*} [Fintype σ] [CharZero R]
    (h : n ≤ Fintype.card σ) {c c' : n.Partition → ℕ}
    (heq : ∑ ν : n.Partition, c ν • schurPoly σ R ν =
      ∑ ν : n.Partition, c' ν • schurPoly σ R ν) :
    c = c' := by
  rw [sum_smul_schurPoly_eq_sum_card_le le_rfl,
    sum_smul_schurPoly_eq_sum_card_le le_rfl] at heq
  funext ν
  exact congrFun (eq_of_sum_nsmul_schurPoly_eq_of_card_le heq) ⟨ν, ν.card_parts_le.trans h⟩

/-- Over a characteristic-zero commutative semiring, a natural-number linear combination of the
diagram Schur polynomials of the partitions of `n` with at most `N` rows in `N` variables determines
its coefficients uniquely. -/
theorem eq_of_sum_nsmul_diagramSchurPoly_eq_of_colLen_le [CharZero R] {N : ℕ}
    {c c' : {ν : n.Partition // (YoungDiagram.ofPartition ν).colLen 0 ≤ N} → ℕ}
    (heq :
      ∑ ν : {ν : n.Partition // (YoungDiagram.ofPartition ν).colLen 0 ≤ N},
        c ν • diagramSchurPoly N R (YoungDiagram.ofPartition ν.val) =
      ∑ ν : {ν : n.Partition // (YoungDiagram.ofPartition ν).colLen 0 ≤ N},
        c' ν • diagramSchurPoly N R (YoungDiagram.ofPartition ν.val)) :
    c = c' := by
  have hℕ :
      ∑ ν : {ν : n.Partition // (YoungDiagram.ofPartition ν).colLen 0 ≤ N},
        c ν • diagramSchurPoly N ℕ (YoungDiagram.ofPartition ν.val) =
      ∑ ν : {ν : n.Partition // (YoungDiagram.ofPartition ν).colLen 0 ≤ N},
        c' ν • diagramSchurPoly N ℕ (YoungDiagram.ofPartition ν.val) :=
    MvPolynomial.map_injective (Nat.castRingHom R) Nat.cast_injective <| by
      simpa only [map_sum, map_nsmul, map_diagramSchurPoly] using heq
  funext ν
  exact linearIndependent_iff'ₛ.mp
    (linearIndependent_diagramSchurPoly_of_colLen_le (R := ℕ))
    Finset.univ c c' hℕ ν (Finset.mem_univ ν)

/-- Over a characteristic-zero commutative semiring, a natural-number linear combination of the
diagram Schur polynomials of the partitions of `n` in `N ≥ n` variables determines its
coefficients uniquely. -/
theorem eq_of_sum_nsmul_diagramSchurPoly_eq [CharZero R] {N : ℕ} (h : n ≤ N)
    {c c' : n.Partition → ℕ}
    (heq : ∑ ν : n.Partition, c ν • diagramSchurPoly N R (YoungDiagram.ofPartition ν) =
      ∑ ν : n.Partition, c' ν • diagramSchurPoly N R (YoungDiagram.ofPartition ν)) :
    c = c' := by
  rw [sum_smul_diagramSchurPoly_eq_sum_colLen_le le_rfl,
    sum_smul_diagramSchurPoly_eq_sum_colLen_le le_rfl] at heq
  funext ν
  exact congrFun (eq_of_sum_nsmul_diagramSchurPoly_eq_of_colLen_le heq)
    ⟨ν, by rw [YoungDiagram.colLen_zero_ofPartition]; exact ν.card_parts_le.trans h⟩

/-- **The Schur polynomials are linearly independent**: in `N` variables, the Schur polynomials of
the Young diagrams with at most `N` rows are linearly independent over every additively
cancellative commutative semiring. The diagrams with more rows have Schur polynomial zero
(`TauCeti.diagramSchurPoly_eq_zero_of_lt_colLen`). -/
theorem linearIndependent_diagramSchurPoly [IsCancelAdd R] {N : ℕ} :
    LinearIndependent R fun μ : {μ : YoungDiagram // μ.colLen 0 ≤ N} => diagramSchurPoly N R μ := by
  classical
  let _ := MvPolynomial.gradedAlgebra (σ := Fin N) (R := R)
  let V := homogeneousSubmodule (Fin N) R
  let fiberEquiv (n : ℕ) :
      {μ : {μ : YoungDiagram // μ.colLen 0 ≤ N} // μ.val.card = n} ≃
        {ν : n.Partition // (YoungDiagram.ofPartition ν).colLen 0 ≤ N} :=
    ((Equiv.subtypeSubtypeEquivSubtypeInter (fun ν : YoungDiagram => ν.colLen 0 ≤ N)
        (fun ν : YoungDiagram => ν.card = n)).trans
      ((Equiv.subtypeEquivRight fun _ => and_comm).trans
        (Equiv.subtypeSubtypeEquivSubtypeInter (fun ν : YoungDiagram => ν.card = n)
          (fun ν : YoungDiagram => ν.colLen 0 ≤ N)).symm)).trans
      (Equiv.subtypeEquiv YoungDiagram.equivPartition fun ν => by
        simp [YoungDiagram.equivPartition])
  let f (n : ℕ) (μ : {μ : {μ : YoungDiagram // μ.colLen 0 ≤ N} // μ.val.card = n}) : V n :=
    ⟨diagramSchurPoly N R μ.val.val, (mem_homogeneousSubmodule _ _).mpr <| by
      have h := isHomogeneous_diagramSchurPoly (N := N) (R := R) (μ := μ.val.val)
      rwa [μ.property] at h⟩
  have hf (n : ℕ) : LinearIndependent R (f n) := by
    have hli : LinearIndependent R ((V n).subtype ∘ f n) := by
      rw [show (V n).subtype ∘ f n =
          (fun ν : {ν : n.Partition // (YoungDiagram.ofPartition ν).colLen 0 ≤ N} =>
            diagramSchurPoly N R (YoungDiagram.ofPartition ν.val)) ∘ fiberEquiv n by
        funext μ
        simp [f, fiberEquiv, YoungDiagram.equivPartition]]
      exact (linearIndependent_diagramSchurPoly_of_colLen_le
        (R := R) (n := n) (N := N)).comp (fiberEquiv n) (fiberEquiv n).injective
    exact hli.of_comp (V n).subtype
  have hsingle : LinearIndependent R fun ix :
      Σ n : ℕ, {μ : {μ : YoungDiagram // μ.colLen 0 ≤ N} // μ.val.card = n} =>
      DirectSum.lof R ℕ (fun n => V n) ix.1 (f ix.1 ix.2) :=
    DFinsupp.linearIndependent_single f hf
  have hdecomp : LinearIndependent R fun ix :
      Σ n : ℕ, {μ : {μ : YoungDiagram // μ.colLen 0 ≤ N} // μ.val.card = n} =>
      diagramSchurPoly N R ix.2.val.val := by
    have hcomp :=
      ((DirectSum.decomposeLinearEquiv V).symm.toLinearMap.linearIndependent_iff_of_injOn
        (v := fun ix : Σ n : ℕ, {μ : {μ : YoungDiagram // μ.colLen 0 ≤ N} // μ.val.card = n} =>
          DirectSum.lof R ℕ (fun n => V n) ix.1 (f ix.1 ix.2))
        (DirectSum.decomposeLinearEquiv V).symm.injective.injOn).mpr hsingle
    simpa [f, Function.comp_def] using hcomp
  exact hdecomp.comp
    (Equiv.sigmaFiberEquiv (fun μ : {μ : YoungDiagram // μ.colLen 0 ≤ N} => μ.val.card)).symm
    (Equiv.injective _)

end LinearIndependent

end TauCeti
