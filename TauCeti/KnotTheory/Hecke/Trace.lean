/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.TypeAHeckeAlgebra.MarkovTrace
public import TauCeti.KnotTheory.Markov.Basic
public import Mathlib.Tactic.LinearCombination

/-!
# The braid invariant of a Hecke Markov trace

Let `τ` be a normalized Markov trace with parameter `z` on the infinite type-A Hecke
algebra. The positive and negative stabilization constants are respectively `z` and
`z - (q - q⁻¹)`. Given `C : R` and `l : Rˣ` satisfying
`C * l * z = 1` and `C * l⁻¹ * (z - (q - q⁻¹)) = 1`, the expression

`C ^ (n - 1) * l ^ writhe(b) * τ(γ_n(b))`

is unchanged by both stabilizations and conjugation. Here `γ_n` is the canonical braid
representation in the universal Hecke algebra, not a tensor representation. The construction
works over a commutative ring once the normalization parameters have been chosen; it does not
assert that the required square roots exist in that ring.

`MarkovBraid.heckeTrace` is this normalized expression, and `heckeBraidInvariant` is its descent
to the quotient by ordinary unframed Markov equivalence. The unknot value is one, the
`n`-component unlink value is `C ^ (n - 1)`, and the skein coefficients are
`(l⁻¹, -l, -(q - q⁻¹))`. No geometric link carrier or geometric Markov theorem is used.

## References

* V. F. R. Jones, *Hecke algebra representations of braid groups and link polynomials*,
  Ann. of Math. 126 (1987), 335–388, Section 5.

The writhe calculation follows the native `MarkovBraid.jimboTrace` normalization in
`TauCeti.KnotTheory.Jimbo.Normalization`, with a separate strand-number factor to accommodate
the two arbitrary stabilization constants.
-/

public section

namespace TauCeti

open InfiniteTypeAHeckeAlgebra

variable {R : Type*} [CommRing R] {q : Rˣ} {z : R}
  {τ : InfiniteTypeAHeckeAlgebra R q →ₗ[R] R} {n : ℕ}

namespace InfiniteTypeAHeckeAlgebra.IsMarkovTrace

/-- Conjugation of a braid does not change its Hecke trace. -/
theorem braid_conj (hτ : IsMarkovTrace z τ) (b c : BraidGroup n) :
    τ (braidHom R q n (c * b * c⁻¹)) = τ (braidHom R q n b) := by
  simp only [map_mul, map_inv, Units.val_mul]
  rw [hτ.map_mul_comm, ← mul_assoc, Units.inv_mul, one_mul]

/-- Positive stabilization has constant `z`, independently of the strand count. -/
theorem braid_stabilize (hτ : IsMarkovTrace z τ) (b : BraidGroup (n + 1)) :
    τ (braidHom R q (n + 2) (BraidGroup.strandIncl b * BraidGroup.sigma (Fin.last n))) =
      z * τ (braidHom R q (n + 1) b) := by
  simp only [map_mul, braidHom_strandIncl, braidHom_sigma, Units.val_mul, val_unitT,
    Fin.val_last]
  exact hτ.map_mul_T (braidHom_mem_stage b)

/-- Negative stabilization has constant `z - (q - q⁻¹)`, dictated by the Hecke relation. -/
theorem braid_stabilizeInv (hτ : IsMarkovTrace z τ) (b : BraidGroup (n + 1)) :
    τ (braidHom R q (n + 2) (BraidGroup.strandIncl b * (BraidGroup.sigma (Fin.last n))⁻¹)) =
      (z - ((q : R) - ↑q⁻¹)) * τ (braidHom R q (n + 1) b) := by
  simp only [map_mul, map_inv, braidHom_strandIncl, braidHom_sigma, Units.val_mul,
    val_inv_unitT, Fin.val_last, Algebra.algebraMap_eq_smul_one, mul_sub, mul_smul_comm,
    mul_one, map_sub, map_smul, smul_eq_mul]
  rw [hτ.map_mul_T (braidHom_mem_stage b)]
  ring

end InfiniteTypeAHeckeAlgebra.IsMarkovTrace

/-- The unnormalized Hecke skein identity holds for every linear functional, without a trace
hypothesis, and in an arbitrary braid context. -/
theorem heckeBraidTrace_skein (τ : InfiniteTypeAHeckeAlgebra R q →ₗ[R] R)
    (b c : BraidGroup (n + 1)) (i : Fin n) :
    τ (braidHom R q (n + 1) (b * BraidGroup.sigma (n := n + 1) i * c)) -
        τ (braidHom R q (n + 1) (b * (BraidGroup.sigma (n := n + 1) i)⁻¹ * c)) =
      ((q : R) - ↑q⁻¹) * τ (braidHom R q (n + 1) (b * c)) := by
  simp only [map_mul, map_inv, braidHom_sigma, Units.val_mul, val_unitT, val_inv_unitT]
  rw [mul_sub, sub_mul, map_sub, sub_sub_cancel, Algebra.algebraMap_eq_smul_one,
    mul_smul_comm, mul_one, smul_mul_assoc, map_smul, smul_eq_mul]

namespace MarkovBraid

/-- The normalized braid trace of the universal Hecke representation. The strand count is
`β.predStrands + 1`; `l` supplies the writhe normalization and `C` the unlink factor. -/
def heckeTrace (β : MarkovBraid) (τ : InfiniteTypeAHeckeAlgebra R q →ₗ[R] R)
    (C : R) (l : Rˣ) : R :=
  C ^ β.predStrands * ↑(l ^ Multiplicative.toAdd (ArtinGroup.exponentSum _ β.braid)) *
    τ (braidHom R q (β.predStrands + 1) β.braid)

/-- The normalization formula for the Hecke braid trace. -/
theorem heckeTrace_def (β : MarkovBraid) (C : R) (l : Rˣ) :
    β.heckeTrace τ C l =
      C ^ β.predStrands * ↑(l ^ Multiplicative.toAdd (ArtinGroup.exponentSum _ β.braid)) *
        τ (braidHom R q (β.predStrands + 1) β.braid) := (rfl)

/-- The identity braid on `n + 1` strands has value `C ^ n`. In particular the one-strand
unknot has value one and the two-strand unlink has value `C`. -/
theorem heckeTrace_one (hτ : IsMarkovTrace z τ) (C : R) (l : Rˣ) :
    heckeTrace ⟨n, 1⟩ τ C l = C ^ n := by
  simp [heckeTrace_def, hτ.map_one]

/-- Conjugation preserves the normalized Hecke trace. -/
theorem heckeTrace_conj (hτ : IsMarkovTrace z τ) (C : R) (l : Rˣ)
    (b c : BraidGroup (n + 1)) :
    heckeTrace ⟨n, c * b * c⁻¹⟩ τ C l = heckeTrace ⟨n, b⟩ τ C l := by
  simp only [heckeTrace_def]
  rw [hτ.braid_conj]
  simp [map_mul, map_inv]

/-- Positive Markov stabilization preserves the normalized Hecke trace when
`C * l * z = 1`. -/
theorem heckeTrace_stabilize (hτ : IsMarkovTrace z τ) (C : R) (l : Rˣ)
    (hpos : C * (l : R) * z = 1) (b : BraidGroup (n + 1)) :
    heckeTrace ⟨n + 1, BraidGroup.strandIncl b * BraidGroup.sigma (Fin.last n)⟩ τ C l =
      heckeTrace ⟨n, b⟩ τ C l := by
  simp only [heckeTrace_def]
  rw [hτ.braid_stabilize]
  simp only [map_mul,
    BraidGroup.exponentSum_strandIncl, BraidGroup.exponentSum_sigma,
    toAdd_mul, toAdd_ofAdd, zpow_add, zpow_one, Units.val_mul, pow_succ]
  calc
    _ = (C * (l : R) * z) *
        (C ^ n * ↑(l ^ Multiplicative.toAdd (ArtinGroup.exponentSum _ b)) *
          τ (braidHom R q (n + 1) b)) := by ring
    _ = _ := by rw [hpos, one_mul]

/-- Negative Markov stabilization preserves the normalized Hecke trace when
`C * l⁻¹ * (z - (q - q⁻¹)) = 1`. -/
theorem heckeTrace_stabilizeInv (hτ : IsMarkovTrace z τ) (C : R) (l : Rˣ)
    (hneg : C * (↑l⁻¹ : R) * (z - ((q : R) - ↑q⁻¹)) = 1)
    (b : BraidGroup (n + 1)) :
    heckeTrace ⟨n + 1, BraidGroup.strandIncl b * (BraidGroup.sigma (Fin.last n))⁻¹⟩ τ C l =
      heckeTrace ⟨n, b⟩ τ C l := by
  simp only [heckeTrace_def]
  rw [hτ.braid_stabilizeInv]
  simp only [map_mul, map_inv,
    BraidGroup.exponentSum_strandIncl, BraidGroup.exponentSum_sigma,
    toAdd_mul, toAdd_inv, toAdd_ofAdd, zpow_add, zpow_neg_one, Units.val_mul, pow_succ]
  calc
    _ = (C * (↑l⁻¹ : R) * (z - ((q : R) - ↑q⁻¹))) *
        (C ^ n * ↑(l ^ Multiplicative.toAdd (ArtinGroup.exponentSum _ b)) *
          τ (braidHom R q (n + 1) b)) := by ring
    _ = _ := by rw [hneg, one_mul]

/-- The normalized skein identity in an arbitrary braid context. No Markov or normalization
hypotheses are needed for this identity; the inverse writhe factors determine its coefficients. -/
theorem heckeTrace_skein (C : R) (l : Rˣ) (b c : BraidGroup (n + 1)) (i : Fin n) :
    (↑l⁻¹ : R) * heckeTrace ⟨n, b * BraidGroup.sigma (n := n + 1) i * c⟩ τ C l -
        (l : R) * heckeTrace ⟨n, b * (BraidGroup.sigma (n := n + 1) i)⁻¹ * c⟩ τ C l =
      ((q : R) - ↑q⁻¹) * heckeTrace ⟨n, b * c⟩ τ C l := by
  have h := heckeBraidTrace_skein τ b c i
  simp only [map_mul, map_inv, Units.val_mul] at h
  simp only [heckeTrace_def, map_mul, map_inv, BraidGroup.exponentSum_sigma,
    toAdd_mul, toAdd_inv, toAdd_ofAdd, zpow_add, zpow_neg_one, zpow_one, Units.val_mul]
  have hu : (l : R) * ↑l⁻¹ = 1 := l.mul_inv
  linear_combination
    C ^ n * ↑(l ^ Multiplicative.toAdd (ArtinGroup.exponentSum _ b)) *
      ↑(l ^ Multiplicative.toAdd (ArtinGroup.exponentSum _ c)) * h +
    (C ^ n * ↑(l ^ Multiplicative.toAdd (ArtinGroup.exponentSum _ b)) *
      ↑(l ^ Multiplicative.toAdd (ArtinGroup.exponentSum _ c)) *
      (τ ((braidHom R q (n + 1) b : InfiniteTypeAHeckeAlgebra R q) *
          ↑(braidHom R q (n + 1) (BraidGroup.sigma i)) * ↑(braidHom R q (n + 1) c)) -
        τ ((braidHom R q (n + 1) b : InfiniteTypeAHeckeAlgebra R q) *
          ↑(braidHom R q (n + 1) (BraidGroup.sigma i))⁻¹ * ↑(braidHom R q (n + 1) c)))) * hu

end MarkovBraid

/-- Every generating Markov move preserves the normalized universal Hecke trace. -/
theorem IsMarkovMove.heckeTrace_eq {β γ : MarkovBraid} (h : IsMarkovMove β γ)
    (hτ : IsMarkovTrace z τ) (C : R) (l : Rˣ)
    (hpos : C * (l : R) * z = 1)
    (hneg : C * (↑l⁻¹ : R) * (z - ((q : R) - ↑q⁻¹)) = 1) :
    β.heckeTrace τ C l = γ.heckeTrace τ C l := by
  cases h with
  | conj b c => exact MarkovBraid.heckeTrace_conj hτ C l b c
  | stabilize b => exact MarkovBraid.heckeTrace_stabilize hτ C l hpos b
  | stabilizeInv b => exact MarkovBraid.heckeTrace_stabilizeInv hτ C l hneg b

/-- Markov-equivalent braids have equal normalized Hecke traces. -/
theorem MarkovEquiv.heckeTrace_eq {β γ : MarkovBraid} (h : MarkovEquiv β γ)
    (hτ : IsMarkovTrace z τ) (C : R) (l : Rˣ)
    (hpos : C * (l : R) * z = 1)
    (hneg : C * (↑l⁻¹ : R) * (z - ((q : R) - ↑q⁻¹)) = 1) :
    β.heckeTrace τ C l = γ.heckeTrace τ C l :=
  h.induction (fun hmove ↦ hmove.heckeTrace_eq hτ C l hpos hneg)
    (fun _ ↦ rfl) (fun _ ih ↦ ih.symm) (fun _ _ ih ih' ↦ ih.trans ih')

/-- The normalized Hecke invariant on algebraic braid closures, that is, the quotient by
ordinary unframed Markov equivalence. This does not identify that quotient with geometric links. -/
def heckeBraidInvariant (hτ : IsMarkovTrace z τ) (C : R) (l : Rˣ)
    (hpos : C * (l : R) * z = 1)
    (hneg : C * (↑l⁻¹ : R) * (z - ((q : R) - ↑q⁻¹)) = 1) : Quot MarkovEquiv → R :=
  Quot.lift (fun β ↦ β.heckeTrace τ C l) (fun _ _ h ↦ h.heckeTrace_eq hτ C l hpos hneg)

/-- Evaluation of the descended invariant on a braid representative. -/
@[simp]
theorem heckeBraidInvariant_mk (hτ : IsMarkovTrace z τ) (C : R) (l : Rˣ)
    (hpos : C * (l : R) * z = 1)
    (hneg : C * (↑l⁻¹ : R) * (z - ((q : R) - ↑q⁻¹)) = 1) (β : MarkovBraid) :
    heckeBraidInvariant hτ C l hpos hneg (Quot.mk MarkovEquiv β) = β.heckeTrace τ C l := (rfl)

end TauCeti
