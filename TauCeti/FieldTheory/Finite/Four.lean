/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.FieldTheory.Finite.Trace
public import Mathlib.Algebra.CharP.CharAndCard
public import Mathlib.Algebra.CharP.Two
public import Mathlib.Data.Fin.VecNotation

import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.Data.List.Pi
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination

/-!
# The four elements of a field of order four

A root `ω` of `X² + X + 1` labels the four elements as `0, 1, ω, ω²`.
The explicit enumeration supports finite calculations over this alphabet without choosing
another model of the field. Squaring exchanges the two roots in characteristic two.

Additively, a field of four elements is the Klein four-group: `zmodTwoProdAddEquiv` sends
`(a, b) : ZMod 2 × ZMod 2` to `a + bω`, so that the three nonzero elements `1, ω, ω²` correspond
to `(1, 0)`, `(0, 1)` and `(1, 1)`. The absolute trace to the prime field is `z ↦ z + z²`.
-/

public section

namespace TauCeti

/-- The Galois field of order four has four elements, independently of its enumeration. -/
theorem card_galoisField_two_two [Fintype (GaloisField 2 2)] :
    Fintype.card (GaloisField 2 2) = 4 := by
  rw [← Nat.card_eq_fintype_card, GaloisField.card 2 2 (by decide)]
  decide

/-- A list of all vectors with entries in `coeffs` of length `dim`. -/
private def powerBasisCoeffVectors {K : Type*} (coeffs : List K) (dim : ℕ) : List (Fin dim → K) :=
  (List.pi (List.finRange dim) fun _ => coeffs).map (· · (by simp))

/-- A vector is in `powerBasisCoeffVectors` if and only if every coordinate is in `coeffs`. -/
private theorem mem_powerBasisCoeffVectors {K : Type*} (coeffs : List K)
    {dim : ℕ} (c : Fin dim → K) :
    c ∈ powerBasisCoeffVectors coeffs dim ↔ ∀ i, c i ∈ coeffs := by
  simp_rw [powerBasisCoeffVectors, List.mem_map, List.mem_pi]
  constructor
  · rintro ⟨f, hf, rfl⟩ i
    exact hf i (by simp)
  · intro hc
    use fun i _ => c i
    constructor
    · exact fun i _ => hc i
    · rfl

section PowerBasisExpansion

variable {K L : Type*} [CommRing K] [Ring L] [Algebra K L]

/-- A list of all evaluations at `gen` of polynomials with degree less than `dim` and coefficients
in `coeffs`. -/
private def powerBasisExpansions (coeffs : List K) (dim : ℕ) (gen : L) : List L :=
  (powerBasisCoeffVectors coeffs dim).map fun c => ∑ i : Fin dim, Algebra.cast (c i) * gen ^ (i : ℕ)

/-- If every element of `K` is in `coeffs`, then every element of `L` is in the list
returned by `powerBasisExpansions`. -/
private theorem powerBasisExpansions_toFinset_eq_univ [Fintype K] [DecidableEq K]
    [Fintype L] [DecidableEq L]
    (coeffs : List K) (pb : PowerBasis K L)
    (hcoeffs : coeffs.toFinset = Finset.univ) :
    (powerBasisExpansions coeffs pb.dim pb.gen).toFinset = Finset.univ := by
  ext x
  simp only [List.mem_toFinset, Finset.mem_univ, iff_true]
  rw [powerBasisExpansions, List.mem_map]
  use pb.basis.repr x
  constructor
  · rw [mem_powerBasisCoeffVectors coeffs _]
    simp [← List.mem_toFinset, hcoeffs]
  · simpa [powerBasisExpansions, pb.basis_eq_pow, Algebra.smul_def] using pb.basis.sum_repr x

end PowerBasisExpansion

variable {F : Type*} [Field F] [Finite F]

/-- Every element other than zero and one in a field of order four is a root of
`X² + X + 1`. -/
theorem sq_add_self_add_one_eq_zero (hF : Nat.card F = 4) {ω : F}
    (h0 : ω ≠ 0) (h1 : ω ≠ 1) : ω ^ 2 + ω + 1 = 0 := by
  let := Fintype.ofFinite F
  have hcard : Fintype.card F = 4 := by simpa only [Nat.card_eq_fintype_card] using hF
  have hpow : ω ^ 3 = 1 := by simpa [hcard] using FiniteField.pow_card_sub_one_eq_one ω h0
  have hmul : (ω - 1) * (ω ^ 2 + ω + 1) = 0 := by
    linear_combination hpow
  exact (mul_eq_zero.mp hmul).resolve_left (sub_ne_zero.mpr h1)

/-- Squaring preserves roots of `X² + X + 1` in characteristic two. -/
theorem sq_sq_add_sq_add_one_eq_zero {R : Type*} [CommSemiring R] [CharP R 2]
    {ω : R} (hω : ω ^ 2 + ω + 1 = 0) : (ω ^ 2) ^ 2 + ω ^ 2 + 1 = 0 := by
  simpa only [map_add, map_pow, map_one, map_zero, frobenius_def] using
    congrArg (frobenius R 2) hω

/-- Every field of order four contains a root of `X² + X + 1`. -/
theorem exists_sq_add_self_add_one_eq_zero_of_card_eq_four (hF : Nat.card F = 4) :
    ∃ ω : F, ω ^ 2 + ω + 1 = 0 := by
  classical
  have := Fintype.ofFinite F
  have hcard : Fintype.card F = 4 := by simpa only [Nat.card_eq_fintype_card] using hF
  obtain ⟨ω, _, hω⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := ({0, 1} : Finset F)) (t := Finset.univ) (by simp [hcard])
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hω
  exact ⟨ω, sq_add_self_add_one_eq_zero hF hω.1 hω.2⟩

omit [Finite F] in
/-- The four elements of a field of order four, labelled by a root of `X² + X + 1`. -/
theorem univ_eq_zero_one_root_sq [Fintype F] [DecidableEq F] (hF : Nat.card F = 4) {ω : F}
    (hω : ω ^ 2 + ω + 1 = 0) : Finset.univ = {0, 1, ω, ω ^ 2} := by
  have hcard : Fintype.card F = 4 := by simpa only [Nat.card_eq_fintype_card] using hF
  let := charP_of_card_eq_prime_pow (p := 2) (f := 2) hcard
  let := ZMod.algebra F 2
  let p : Polynomial (ZMod 2) := Polynomial.X ^ 2 + Polynomial.X + 1
  have hpdeg : p.natDegree = 2 := by
    unfold p
    compute_degree!
  have hpmonic : p.Monic := by
    unfold p
    monicity!
  have hpirr : Irreducible p := by
    apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
    · rw [hpdeg]
      decide
    · intro a
      rw [Polynomial.IsRoot.def]
      simp only [p, Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X,
        Polynomial.eval_one]
      fin_cases a <;> decide
  have hroot : Polynomial.aeval ω p = 0 := by
    simpa [p] using hω
  have hdim : Module.finrank (ZMod 2) F = p.natDegree := by
    apply Nat.pow_right_injective (by decide : 1 < 2)
    calc
      2 ^ Module.finrank (ZMod 2) F = Fintype.card F := FiniteField.pow_finrank_eq_card 2 F
      _ = 2 ^ p.natDegree := by rw [hcard, hpdeg]; norm_num
  have hint : IsIntegral (ZMod 2) ω := ⟨p, hpmonic, hroot⟩
  have hminpoly : p = minpoly (ZMod 2) ω :=
    minpoly.eq_of_irreducible_of_monic hpirr hroot hpmonic
  have hgen : IntermediateField.adjoin (ZMod 2) ({ω} : Set F) = ⊤ := by
    apply IntermediateField.eq_of_le_of_finrank_eq le_top
    rw [IntermediateField.adjoin.finrank hint, ← hminpoly, IntermediateField.finrank_top']
    exact hdim.symm
  let pb : PowerBasis (ZMod 2) F := PowerBasis.ofAdjoinSimpleEqTop hint hgen
  have hpb_dim : pb.dim = 2 := by
    rw [PowerBasis.ofAdjoinSimpleEqTop_dim hint hgen, ← hminpoly, hpdeg]
  have hsq : ω ^ 2 = ω + 1 := by
    linear_combination hω - (CharTwo.two_eq_zero (R := F)) * (ω + 1)
  let coeffs : List (ZMod 2) := [0, 1]
  let output := powerBasisExpansions coeffs pb.dim pb.gen
  have houtput_univ : output.toFinset = Finset.univ := powerBasisExpansions_toFinset_eq_univ _ _ rfl
  have houtput : output = [0, ω, 1, ω ^ 2] := by
    unfold output
    rw [hpb_dim]
    change [
      Algebra.cast (0 : ZMod 2) * ω ^ 0 + (Algebra.cast (0 : ZMod 2) * ω ^ 1 + 0),
      Algebra.cast (0 : ZMod 2) * ω ^ 0 + (Algebra.cast (1 : ZMod 2) * ω ^ 1 + 0),
      Algebra.cast (1 : ZMod 2) * ω ^ 0 + (Algebra.cast (0 : ZMod 2) * ω ^ 1 + 0),
      Algebra.cast (1 : ZMod 2) * ω ^ 0 + (Algebra.cast (1 : ZMod 2) * ω ^ 1 + 0)
    ] = _
    ring_nf
    simp [hsq]
  suffices Finset.univ = [0, 1, ω, ω ^ 2].toFinset by simpa [List.toFinset_cons]
  calc
    _ = output.toFinset := houtput_univ.symm
    _ = [0, ω, 1, ω ^ 2].toFinset := congr($(houtput).toFinset)
    _ = [0, 1, ω, ω ^ 2].toFinset := by
      simp only [List.toFinset_cons, List.toFinset_nil]
      exact congrArg (insert (0 : F)) (Finset.insert_comm ω 1 (insert (ω ^ 2) ∅))

/-- Label a field of four elements by `0, 1, ω, ω²`, in that order. -/
noncomputable def finFourEquiv (hF : Nat.card F = 4) {ω : F}
    (hω : ω ^ 2 + ω + 1 = 0) : Fin 4 ≃ F := by
  classical
  letI := Fintype.ofFinite F
  have hcard : Fintype.card F = 4 := by simpa only [Nat.card_eq_fintype_card] using hF
  refine Equiv.ofBijective ![0, 1, ω, ω ^ 2] ?_
  apply (Fintype.bijective_iff_surjective_and_card _).mpr
  refine ⟨?_, by simp [hcard]⟩
  intro x
  have hx : x ∈ ({0, 1, ω, ω ^ 2} : Finset F) := by
    rw [← univ_eq_zero_one_root_sq hF hω]
    exact Finset.mem_univ x
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact ⟨0, rfl⟩
  · exact ⟨1, rfl⟩
  · exact ⟨2, rfl⟩
  · exact ⟨3, rfl⟩

/-- The four-element labelling evaluates to the displayed tuple. -/
@[simp]
theorem finFourEquiv_apply (hF : Nat.card F = 4) {ω : F}
    (hω : ω ^ 2 + ω + 1 = 0) (i : Fin 4) :
    finFourEquiv hF hω i = ![0, 1, ω, ω ^ 2] i := (rfl)


/-! ### The additive group of a field of order four -/

/-- In a field of order four every element has additive order dividing two. -/
private theorem two_zsmul_eq_zero_of_natCard_eq_four (hF : Nat.card F = 4) (x : F) :
    (2 : ℤ) • x = 0 := by
  let := Fintype.ofFinite F
  have hcard : Fintype.card F = 2 ^ 2 := Nat.card_eq_fintype_card.symm.trans hF
  let := charP_of_card_eq_prime_pow hcard
  rw [two_zsmul, CharTwo.add_self_eq_zero]

/-- The additive homomorphism `ℤ/2 → F` sending `1` to `x`. -/
private noncomputable def zmodTwoHom (hF : Nat.card F = 4) (x : F) : ZMod 2 →+ F :=
  ZMod.lift 2 ⟨zmultiplesHom F x, by simpa using two_zsmul_eq_zero_of_natCard_eq_four hF x⟩

private theorem zmodTwoHom_apply (hF : Nat.card F = 4) (x : F) (a : ZMod 2) :
    zmodTwoHom hF x a = (a.val : F) * x := by
  have hcases : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
  rcases hcases a with rfl | rfl
  · rw [map_zero, ZMod.val_zero, Nat.cast_zero, zero_mul]
  · rw [zmodTwoHom, ← Int.cast_one, ZMod.lift_coe, Int.cast_one, ZMod.val_one, Nat.cast_one,
      one_mul]
    exact one_zsmul x

/-- **A field of order four is additively the Klein four-group**: given a root `ω` of
`X² + X + 1`, the pair `(a, b)` of residues modulo two corresponds to `a + bω`. -/
noncomputable def zmodTwoProdAddEquiv (hF : Nat.card F = 4) {ω : F}
    (hω : ω ^ 2 + ω + 1 = 0) : ZMod 2 × ZMod 2 ≃+ F := by
  refine AddEquiv.ofBijective ((zmodTwoHom hF 1).coprod (zmodTwoHom hF ω)) ?_
  rw [Nat.bijective_iff_injective_and_card]
  refine ⟨(injective_iff_map_eq_zero _).mpr fun x hx ↦ ?_, by simp [hF]⟩
  have h0 : ω ≠ 0 := by rintro rfl; simp at hω
  have hcases : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
  obtain ⟨a, b⟩ := x
  simp only [AddMonoidHom.coprod_apply, zmodTwoHom_apply] at hx
  rcases hcases a with rfl | rfl <;> rcases hcases b with rfl | rfl <;>
    simp only [ZMod.val_zero, ZMod.val_one, Nat.cast_zero, Nat.cast_one, zero_mul, one_mul,
      mul_one, add_zero, zero_add, one_ne_zero] at hx
  · rfl
  · exact absurd hx h0
  · have hω' : ω = -1 := eq_neg_of_add_eq_zero_right hx
    have : (1 : F) = 0 := by rw [← hω]; rw [hω']; ring
    exact absurd this one_ne_zero

/-- The additive identification sends `(a, b)` to `a + bω`, using the canonical
representatives of `a` and `b`. -/
theorem zmodTwoProdAddEquiv_apply (hF : Nat.card F = 4) {ω : F}
    (hω : ω ^ 2 + ω + 1 = 0) (a b : ZMod 2) :
    zmodTwoProdAddEquiv hF hω (a, b) = (a.val : F) + (b.val : F) * ω := by
  rw [zmodTwoProdAddEquiv, AddEquiv.ofBijective_apply, AddMonoidHom.coprod_apply,
    zmodTwoHom_apply, zmodTwoHom_apply, mul_one]

/-- The additive identification sends the first generator to `1`. -/
@[simp]
theorem zmodTwoProdAddEquiv_apply_one_zero (hF : Nat.card F = 4) {ω : F}
    (hω : ω ^ 2 + ω + 1 = 0) : zmodTwoProdAddEquiv hF hω (1, 0) = 1 := by
  rw [zmodTwoProdAddEquiv_apply, ZMod.val_one, ZMod.val_zero, Nat.cast_one, Nat.cast_zero,
    zero_mul, add_zero]

/-- The additive identification sends the second generator to `ω`. -/
@[simp]
theorem zmodTwoProdAddEquiv_apply_zero_one (hF : Nat.card F = 4) {ω : F}
    (hω : ω ^ 2 + ω + 1 = 0) : zmodTwoProdAddEquiv hF hω (0, 1) = ω := by
  rw [zmodTwoProdAddEquiv_apply, ZMod.val_one, ZMod.val_zero, Nat.cast_one, Nat.cast_zero,
    one_mul, zero_add]

/-- The additive identification sends the diagonal generator to `ω²`. -/
@[simp]
theorem zmodTwoProdAddEquiv_apply_one_one (hF : Nat.card F = 4) {ω : F}
    (hω : ω ^ 2 + ω + 1 = 0) : zmodTwoProdAddEquiv hF hω (1, 1) = ω ^ 2 := by
  let := Fintype.ofFinite F
  have hcard : Fintype.card F = 2 ^ 2 := Nat.card_eq_fintype_card.symm.trans hF
  let := charP_of_card_eq_prime_pow hcard
  rw [zmodTwoProdAddEquiv_apply, ZMod.val_one, Nat.cast_one, one_mul]
  linear_combination hω - ω ^ 2 * CharTwo.two_eq_zero (R := F)

/-- The inverse additive identification sends `1` to the first generator. -/
@[simp]
theorem zmodTwoProdAddEquiv_symm_one (hF : Nat.card F = 4) {ω : F}
    (hω : ω ^ 2 + ω + 1 = 0) : (zmodTwoProdAddEquiv hF hω).symm 1 = (1, 0) :=
  (AddEquiv.symm_apply_eq _).mpr (zmodTwoProdAddEquiv_apply_one_zero hF hω).symm

/-- The inverse additive identification sends `ω` to the second generator. -/
@[simp]
theorem zmodTwoProdAddEquiv_symm_root (hF : Nat.card F = 4) {ω : F}
    (hω : ω ^ 2 + ω + 1 = 0) : (zmodTwoProdAddEquiv hF hω).symm ω = (0, 1) :=
  (AddEquiv.symm_apply_eq _).mpr (zmodTwoProdAddEquiv_apply_zero_one hF hω).symm

/-- The inverse additive identification sends `ω²` to the diagonal generator. -/
@[simp]
theorem zmodTwoProdAddEquiv_symm_root_sq (hF : Nat.card F = 4) {ω : F}
    (hω : ω ^ 2 + ω + 1 = 0) : (zmodTwoProdAddEquiv hF hω).symm (ω ^ 2) = (1, 1) :=
  (AddEquiv.symm_apply_eq _).mpr (zmodTwoProdAddEquiv_apply_one_one hF hω).symm

/-- The absolute trace of a field of order four to its prime field is `z ↦ z + z²`. -/
theorem algebraMap_trace_eq_add_sq_of_natCard_eq_four [Algebra (ZMod 2) F] (hF : Nat.card F = 4)
    (z : F) :
    algebraMap (ZMod 2) F (Algebra.trace (ZMod 2) F z) = z + z ^ 2 := by
  let := Fintype.ofFinite F
  have hfinrank : Module.finrank (ZMod 2) F = 2 := by
    have hcard := Module.card_eq_pow_finrank (K := ZMod 2) (V := F)
    rw [ZMod.card, ← Nat.card_eq_fintype_card, hF] at hcard
    exact Nat.pow_right_injective le_rfl (hcard.symm.trans (by norm_num))
  rw [FiniteField.algebraMap_trace_eq_sum_pow, hfinrank, Nat.card_zmod]
  simp [Finset.sum_range_succ]

end TauCeti
