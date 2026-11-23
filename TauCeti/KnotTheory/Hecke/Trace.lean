/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.TypeAHeckeAlgebra.MarkovTrace
public import TauCeti.KnotTheory.Markov.Basic
public import TauCeti.RingTheory.AdjoinRoot.Basic
import TauCeti.Algebra.Group.Units.Basic
import Mathlib.Tactic.LinearCombination

/-!
# The braid invariant of a Hecke Markov trace

Let `τ` be a normalized Markov trace with parameter `z` on the infinite type-A Hecke
algebra. The positive and negative stabilization constants are respectively `z` and
`z - (q - q⁻¹)`. Given `C : R` and `l : Rˣ` satisfying
`C * l * z = 1` and `C * l⁻¹ * (z - (q - q⁻¹)) = 1`, the expression

`C ^ (n - 1) * l ^ writhe(b) * τ(γ_n(b))`

is unchanged by both stabilizations and conjugation. Here `γ_n` is the canonical braid
representation in the universal Hecke algebra, not a tensor representation. The construction
works over a commutative ring once the normalization parameters have been chosen; when the two
stabilization constants `z` and `z - (q - q⁻¹)` are units of `R`, adjoining a square root of their
ratio via `AdjoinRoot (X ^ 2 - C (b * a⁻¹))` embeds `R` injectively into a commutative ring over
which `(C, l)` exist (`TauCeti.injective_algebraMap_and_exists_isHeckeNormalization`).

`MarkovBraid.heckeTrace` is this normalized expression, and `heckeBraidInvariant` is its descent
to the quotient by ordinary unframed Markov equivalence. The unknot value (both on one strand and
on either single-crossing two-strand closure) is one, the `n`-component unlink value is
`C ^ (n - 1)`, and the skein coefficients are `(l⁻¹, -l, -(q - q⁻¹))`. No geometric link carrier
or geometric Markov theorem is used.

## Main definitions

* `TauCeti.MarkovBraid.heckeTrace`: the normalized braid trace of the universal Hecke
  representation.
* `TauCeti.heckeBraidInvariant`: its descent to `Quot TauCeti.MarkovEquiv`.
* `TauCeti.IsHeckeNormalization`: the predicate bundling the positive and negative Markov
  normalization equations `C * l * z = 1` and `C * l⁻¹ * (z - (q - q⁻¹)) = 1`.

## Main results

* `LinearMap.heckeTrace_strandIncl` and
  `TauCeti.MarkovBraid.heckeTrace_one_strand`: the split-unknot factor and unknot value.
* `TauCeti.MarkovBraid.heckeTrace_two_strand_one`,
  `TauCeti.MarkovBraid.heckeTrace_sigma_two`, and
  `TauCeti.MarkovBraid.heckeTrace_sigma_two_inv`: explicit values on the two-strand unlink and
  both single-crossing closures.
* `LinearMap.heckeTrace_skein_of_eq_zero`: the skein relation attached to a linear
  relation between a generator and its inverse.
* `TauCeti.IsHeckeNormalization.mul_sub_inv_eq_inv_sub`,
  `TauCeti.IsHeckeNormalization.sq_mul_eq_sub`, `TauCeti.isHeckeNormalization_iff`, and
  `TauCeti.injective_algebraMap_and_exists_isHeckeNormalization`: consequences of the
  normalization equations and the quadratic coefficient extension supplying the root `l`.
* `TauCeti.MarkovBraid.heckeTrace_stabilize_eq_mul` and
  `TauCeti.MarkovBraid.heckeTrace_stabilizeInv_eq_mul`: general positive and negative stabilization
  formulas before imposing the normalization equations.
* `TauCeti.MarkovEquiv.heckeTrace_eq_of_sq_mul`: Markov invariance when `z` is a unit `a` and
  `l ^ 2 * z = z - (q - q⁻¹)`.

## References

* V. F. R. Jones, *Hecke algebra representations of braid groups and link polynomials*,
  Ann. of Math. 126 (1987), 335–388, Sections 5–6.
* C. Kassel and V. Turaev, *Braid Groups*, Springer GTM 247 (2008), Section 4.2.

The writhe calculation follows the native `MarkovBraid.jimboTrace` normalization in
`TauCeti.KnotTheory.Jimbo.Normalization`, with a separate strand-number factor to accommodate
the two arbitrary stabilization constants.
-/

public section

namespace TauCeti

open InfiniteTypeAHeckeAlgebra

variable {R : Type*} [CommRing R] {q : Rˣ} {z : R}
  {τ : InfiniteTypeAHeckeAlgebra R q →ₗ[R] R} {n : ℕ}

namespace MarkovBraid

open BraidGroup

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
theorem heckeTrace_one (h₁ : τ 1 = 1) (C : R) (l : Rˣ) :
    heckeTrace ⟨n, 1⟩ τ C l = C ^ n := by
  simp [heckeTrace_def, h₁]

/-- **Adding an uncrossed strand multiplies the normalized trace by `C`**: the closure gains a
split unknot. -/
theorem _root_.LinearMap.heckeTrace_strandIncl (τ : InfiniteTypeAHeckeAlgebra R q →ₗ[R] R)
    (C : R) (l : Rˣ) (b : BraidGroup (n + 1)) :
    heckeTrace ⟨n + 1, strandIncl b⟩ τ C l = C * heckeTrace ⟨n, b⟩ τ C l := by
  rw [heckeTrace_def, heckeTrace_def, braidHom_strandIncl, exponentSum_strandIncl]
  ring

/-- The only braid on one strand is trivial, and its closure, the unknot, has normalized
trace `1`. -/
theorem heckeTrace_one_strand (h₁ : τ 1 = 1) (C : R) (l : Rˣ)
    (b : BraidGroup 1) : heckeTrace ⟨0, b⟩ τ C l = 1 := by
  rw [eq_one_of_le_one le_rfl b, heckeTrace_one h₁, pow_zero]

/-- Conjugation preserves the normalized Hecke trace of a tracial linear functional. -/
theorem heckeTrace_conj (htr : ∀ x y, τ (x * y) = τ (y * x)) (C : R) (l : Rˣ)
    (b c : BraidGroup (n + 1)) :
    heckeTrace ⟨n, c * b * c⁻¹⟩ τ C l = heckeTrace ⟨n, b⟩ τ C l := by
  simp only [heckeTrace_def]
  rw [map_braidHom_conj htr]
  simp [map_mul, map_inv]

/-- Positive Markov stabilization multiplies the normalized Hecke trace by `C * l * z`. -/
theorem heckeTrace_stabilize_eq_mul (hτ : IsMarkovTrace z τ) (C : R) (l : Rˣ)
    (b : BraidGroup (n + 1)) :
    heckeTrace ⟨n + 1, BraidGroup.strandIncl b * BraidGroup.sigma (Fin.last n)⟩ τ C l =
      C * (l : R) * z * heckeTrace ⟨n, b⟩ τ C l := by
  simp only [heckeTrace_def]
  rw [hτ.map_braidHom_stabilize]
  simp only [map_mul,
    BraidGroup.exponentSum_strandIncl, BraidGroup.exponentSum_sigma,
    toAdd_mul, toAdd_ofAdd, zpow_add, zpow_one, Units.val_mul, pow_succ]
  ring

/-- Negative Markov stabilization multiplies the normalized Hecke trace by
`C * l⁻¹ * (z - (q - q⁻¹))`. -/
theorem heckeTrace_stabilizeInv_eq_mul (hτ : IsMarkovTrace z τ) (C : R) (l : Rˣ)
    (b : BraidGroup (n + 1)) :
    heckeTrace ⟨n + 1, BraidGroup.strandIncl b * (BraidGroup.sigma (Fin.last n))⁻¹⟩ τ C l =
      C * (↑l⁻¹ : R) * (z - ((q : R) - ↑q⁻¹)) * heckeTrace ⟨n, b⟩ τ C l := by
  simp only [heckeTrace_def]
  rw [hτ.map_braidHom_stabilizeInv]
  simp only [map_mul, map_inv,
    BraidGroup.exponentSum_strandIncl, BraidGroup.exponentSum_sigma,
    toAdd_mul, toAdd_inv, toAdd_ofAdd, zpow_add, zpow_neg_one, Units.val_mul, pow_succ]
  ring

/-- Positive Markov stabilization preserves the normalized Hecke trace when
`C * l * z = 1`. -/
theorem heckeTrace_stabilize (hτ : IsMarkovTrace z τ) (C : R) (l : Rˣ)
    (hpos : C * (l : R) * z = 1) (b : BraidGroup (n + 1)) :
    heckeTrace ⟨n + 1, BraidGroup.strandIncl b * BraidGroup.sigma (Fin.last n)⟩ τ C l =
      heckeTrace ⟨n, b⟩ τ C l := by
  rw [heckeTrace_stabilize_eq_mul hτ, hpos, one_mul]

/-- Negative Markov stabilization preserves the normalized Hecke trace when
`C * l⁻¹ * (z - (q - q⁻¹)) = 1`. -/
theorem heckeTrace_stabilizeInv (hτ : IsMarkovTrace z τ) (C : R) (l : Rˣ)
    (hneg : C * (↑l⁻¹ : R) * (z - ((q : R) - ↑q⁻¹)) = 1)
    (b : BraidGroup (n + 1)) :
    heckeTrace ⟨n + 1, BraidGroup.strandIncl b * (BraidGroup.sigma (Fin.last n))⁻¹⟩ τ C l =
      heckeTrace ⟨n, b⟩ τ C l := by
  rw [heckeTrace_stabilizeInv_eq_mul hτ, hneg, one_mul]

/-- The two-strand unlink closure `⟨1, 1⟩` has normalized Hecke trace `C`. -/
theorem heckeTrace_two_strand_one (h₁ : τ 1 = 1) (C : R) (l : Rˣ) :
    heckeTrace ⟨1, 1⟩ τ C l = C := by
  simpa using heckeTrace_one (n := 1) h₁ C l

/-- Before imposing `C * l * z = 1`, the single positive crossing on two strands has normalized
Hecke trace `C * l * z`. -/
theorem heckeTrace_sigma_two_eq (hτ : IsMarkovTrace z τ) (C : R) (l : Rˣ) :
    heckeTrace ⟨1, sigma (n := 2) 0⟩ τ C l = C * (l : R) * z := by
  have hT : τ (T q 0) = z := by
    simpa [hτ.map_one] using hτ.map_mul_T (one_mem (stage R q 1))
  have hexp : ArtinGroup.exponentSum (CoxeterMatrix.A 1) (sigma (n := 2) 0) =
      Multiplicative.ofAdd 1 := exponentSum_sigma (0 : Fin (2 - 1))
  simp [heckeTrace_def, hexp, val_unitT, hT]

/-- When `C * l * z = 1`, the single positive crossing on two strands closes to `1`. -/
theorem heckeTrace_sigma_two (hτ : IsMarkovTrace z τ) (C : R) (l : Rˣ)
    (hpos : C * (l : R) * z = 1) :
    heckeTrace ⟨1, sigma (n := 2) 0⟩ τ C l = 1 := by
  rw [heckeTrace_sigma_two_eq hτ, hpos]

/-- Before imposing `C * l⁻¹ * (z - (q - q⁻¹)) = 1`, the single negative crossing on two strands
has normalized Hecke trace `C * l⁻¹ * (z - (q - q⁻¹))`. -/
theorem heckeTrace_sigma_two_inv_eq (hτ : IsMarkovTrace z τ) (C : R) (l : Rˣ) :
    heckeTrace ⟨1, (sigma (n := 2) 0)⁻¹⟩ τ C l =
      C * (↑l⁻¹ : R) * (z - ((q : R) - ↑q⁻¹)) := by
  have hT : τ ↑(unitT q 0)⁻¹ = z - ((q : R) - ↑q⁻¹) := by
    simpa only [one_mul, hτ.map_one, mul_one] using
      hτ.map_mul_val_inv_unitT (one_mem (stage R q 1))
  have hexp : ArtinGroup.exponentSum (CoxeterMatrix.A 1) (sigma (n := 2) 0) =
      Multiplicative.ofAdd 1 := exponentSum_sigma (0 : Fin (2 - 1))
  simp only [heckeTrace_def, pow_one, map_inv, hexp, toAdd_inv, toAdd_ofAdd, zpow_neg_one,
    braidHom_sigma, Fin.val_zero, hT]

/-- When `C * l⁻¹ * (z - (q - q⁻¹)) = 1`, the single negative crossing on two strands closes to
`1`. -/
theorem heckeTrace_sigma_two_inv (hτ : IsMarkovTrace z τ) (C : R) (l : Rˣ)
    (hneg : C * (↑l⁻¹ : R) * (z - ((q : R) - ↑q⁻¹)) = 1) :
    heckeTrace ⟨1, (sigma (n := 2) 0)⁻¹⟩ τ C l = 1 := by
  rw [heckeTrace_sigma_two_inv_eq hτ, hneg]

/-- **The skein relation attached to a linear relation between a generator and its inverse.** If
`x • T i + y • (T i)⁻¹ + s • 1 = 0` in the Hecke algebra, then for a crossing `σ i` in any braid
context the normalized traces of the positive crossing `L₊`, the negative crossing `L₋` and the
smoothing `L₀` satisfy `x * l⁻¹ * F(L₊) + y * l * F(L₋) + s * F(L₀) = 0`. -/
theorem _root_.LinearMap.heckeTrace_skein_of_eq_zero (τ : InfiniteTypeAHeckeAlgebra R q →ₗ[R] R)
    (C : R) (l : Rˣ) {x y s : R} (i : Fin n)
    (h : x • T q i + y • (↑(unitT q i)⁻¹ : InfiniteTypeAHeckeAlgebra R q) + s • 1 = 0)
    (b c : BraidGroup (n + 1)) :
    x * ↑l⁻¹ * heckeTrace ⟨n, b * sigma (n := n + 1) i * c⟩ τ C l +
        y * l * heckeTrace ⟨n, b * (sigma (n := n + 1) i)⁻¹ * c⟩ τ C l +
          s * heckeTrace ⟨n, b * c⟩ τ C l = 0 := by
  -- The trace of the relation, inserted between the two halves of the braid context.
  have htr := congrArg
    (fun X ↦ τ (braidHom R q (n + 1) b * X * braidHom R q (n + 1) c)) h
  simp only [mul_add, add_mul, smul_mul_assoc, mul_smul_comm, mul_one, map_add, map_smul,
    smul_eq_mul, mul_zero, zero_mul, map_zero] at htr
  simp only [heckeTrace_def, map_mul, map_inv, braidHom_sigma, Units.val_mul, val_unitT,
    exponentSum_sigma, toAdd_mul, toAdd_inv, toAdd_ofAdd]
  generalize Multiplicative.toAdd (ArtinGroup.exponentSum _ b) = p
  generalize Multiplicative.toAdd (ArtinGroup.exponentSum _ c) = r
  rw [show p + 1 + r = (p + r) + 1 by ring, show p + -1 + r = (p + r) - 1 by ring, zpow_add_one,
    zpow_sub_one, Units.val_mul, Units.val_mul]
  -- After the writhe correction is split off, the inverse unit factors cancel.
  linear_combination C ^ n * ((l ^ (p + r) : Rˣ) : R) * htr +
    C ^ n * ((l ^ (p + r) : Rˣ) : R) * x * τ
      (braidHom R q (n + 1) b * T q i * braidHom R q (n + 1) c) * l.inv_mul +
    C ^ n * ((l ^ (p + r) : Rˣ) : R) * y * τ
      (braidHom R q (n + 1) b * ↑(unitT q i)⁻¹ * braidHom R q (n + 1) c) * l.mul_inv

/-- The normalized skein identity in an arbitrary braid context. No Markov or normalization
hypotheses are needed for this identity; the inverse writhe factors determine its coefficients. -/
theorem heckeTrace_skein (C : R) (l : Rˣ) (b c : BraidGroup (n + 1)) (i : Fin n) :
    (↑l⁻¹ : R) * heckeTrace ⟨n, b * BraidGroup.sigma (n := n + 1) i * c⟩ τ C l -
        (l : R) * heckeTrace ⟨n, b * (BraidGroup.sigma (n := n + 1) i)⁻¹ * c⟩ τ C l =
      ((q : R) - ↑q⁻¹) * heckeTrace ⟨n, b * c⟩ τ C l := by
  have hrel : (1 : R) • T q i + (-1 : R) •
      (↑(unitT q i)⁻¹ : InfiniteTypeAHeckeAlgebra R q) +
      (-((q : R) - ↑q⁻¹)) • (1 : InfiniteTypeAHeckeAlgebra R q) = 0 := by
    simpa only [Algebra.smul_def, map_one, map_neg, one_mul, neg_mul, mul_one,
      ← sub_eq_add_neg] using
      (sub_eq_zero.mpr (T_sub_val_inv_unitT (R := R) (q := q) i))
  have h := τ.heckeTrace_skein_of_eq_zero C l i hrel b c
  simpa only [one_mul, neg_one_mul, neg_mul, ← sub_eq_add_neg, sub_eq_zero] using h

end MarkovBraid

/-- Every generating Markov move preserves the normalized universal Hecke trace. -/
theorem IsMarkovMove.heckeTrace_eq {β γ : MarkovBraid} (h : IsMarkovMove β γ)
    (hτ : IsMarkovTrace z τ) (C : R) (l : Rˣ)
    (hpos : C * (l : R) * z = 1)
    (hneg : C * (↑l⁻¹ : R) * (z - ((q : R) - ↑q⁻¹)) = 1) :
    β.heckeTrace τ C l = γ.heckeTrace τ C l := by
  cases h with
  | conj b c => exact MarkovBraid.heckeTrace_conj hτ.map_mul_comm C l b c
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

/-! ### Normalization equations and quadratic root-choice extension -/

/-- A pair `(C, l)` satisfies the **Hecke Markov normalization equations** for Hecke parameter
`q : Rˣ` and Markov parameter `z : R` when `C * l * z = 1` and
`C * l⁻¹ * (z - (q - q⁻¹)) = 1`. These are the two stabilization equations making
`MarkovBraid.heckeTrace τ C l` invariant under positive and negative Markov stabilization. -/
structure IsHeckeNormalization (q : Rˣ) (z C : R) (l : Rˣ) : Prop where
  /-- Positive stabilization equation `C * l * z = 1`. -/
  stabilize : C * (l : R) * z = 1
  /-- Negative stabilization equation `C * l⁻¹ * (z - (q - q⁻¹)) = 1`. -/
  stabilizeInv : C * (↑l⁻¹ : R) * (z - ((q : R) - ↑q⁻¹)) = 1

/-- Under the two Markov normalization equations `C * l * z = 1` and
`C * l⁻¹ * (z - (q - q⁻¹)) = 1`, the unlink factor satisfies `C * (q - q⁻¹) = l⁻¹ - l`. -/
theorem IsHeckeNormalization.mul_sub_inv_eq_inv_sub {C : R} {l : Rˣ}
    (h : IsHeckeNormalization q z C l) :
    C * ((q : R) - ↑q⁻¹) = (↑l⁻¹ : R) - (l : R) := by
  linear_combination (↑l⁻¹ : R) * h.stabilize - (l : R) * h.stabilizeInv -
    C * ((q : R) - ↑q⁻¹) * l.inv_mul

/-- Under the two Markov normalization equations, `l ^ 2 * z = z - (q - q⁻¹)`. -/
theorem IsHeckeNormalization.sq_mul_eq_sub {C : R} {l : Rˣ}
    (h : IsHeckeNormalization q z C l) :
    (l : R) ^ 2 * z = z - ((q : R) - ↑q⁻¹) := by
  linear_combination -((l : R) ^ 2 * z) * h.stabilizeInv + (z - ((q : R) - ↑q⁻¹)) * h.stabilize +
    C * z * (z - ((q : R) - ↑q⁻¹)) * (l : R) * l.mul_inv

/-- The two Markov normalization equations are equivalent to the positive equation `C * l * z = 1`
together with the root equation `l ^ 2 * z = z - (q - q⁻¹)`. -/
theorem isHeckeNormalization_iff {C : R} {l : Rˣ} :
    IsHeckeNormalization q z C l ↔
      C * (l : R) * z = 1 ∧ (l : R) ^ 2 * z = z - ((q : R) - ↑q⁻¹) := by
  refine ⟨fun h ↦ ⟨h.stabilize, h.sq_mul_eq_sub⟩, fun ⟨hpos, hsq⟩ ↦ ⟨hpos, ?_⟩⟩
  rw [← hsq]
  linear_combination (C * z * (l : R)) * l.inv_mul + hpos

/-- **Quadratic coefficient extension for choosing the normalization root.** When the positive and
negative stabilization constants `a = z` and `b = z - (q - q⁻¹)` are units of `R`, the monic
quadratic extension `S = AdjoinRoot (X ^ 2 - C (b * a⁻¹))` embeds `R` injectively and supplies a
unit `l : Sˣ` (whose underlying element is the adjoined square root `AdjoinRoot.root _`) and scalar
`C : S` solving both Markov normalization equations over `S`. -/
theorem injective_algebraMap_and_exists_isHeckeNormalization (a b : Rˣ) (ha : (a : R) = z)
    (hb : (b : R) = z - ((q : R) - ↑q⁻¹)) :
    let g : Polynomial R := Polynomial.X ^ 2 - Polynomial.C (↑(b * a⁻¹) : R)
    let qS : (AdjoinRoot g)ˣ := Units.map (algebraMap R (AdjoinRoot g) : R →* AdjoinRoot g) q
    Function.Injective (algebraMap R (AdjoinRoot g)) ∧
      ∃ (C : AdjoinRoot g) (l : (AdjoinRoot g)ˣ),
        (l : AdjoinRoot g) = AdjoinRoot.root g ∧
        IsHeckeNormalization qS (algebraMap R (AdjoinRoot g) z) C l := by
  dsimp only
  set g : Polynomial R := Polynomial.X ^ 2 - Polynomial.C (↑(b * a⁻¹) : R)
  set qS : (AdjoinRoot g)ˣ := Units.map (algebraMap R (AdjoinRoot g) : R →* AdjoinRoot g) q
  refine ⟨?_, ?_⟩
  · rcases subsingleton_or_nontrivial R with _ | _
    · exact fun _ _ _ ↦ Subsingleton.elim _ _
    · rw [AdjoinRoot.algebraMap_eq]
      exact AdjoinRoot.of.injective_of_monic_of_degree_pos
        (Polynomial.monic_X_pow_sub_C _ two_ne_zero)
        (by rw [Polynomial.degree_X_pow_sub_C two_pos]; decide)
  · classical
    let hl : IsUnit (AdjoinRoot.root g) :=
      AdjoinRoot.isUnit_root_X_pow_sub_C (b * a⁻¹).isUnit two_ne_zero
    let l : (AdjoinRoot g)ˣ := hl.unit
    let aS : (AdjoinRoot g)ˣ := Units.map (algebraMap R (AdjoinRoot g) : R →* AdjoinRoot g) a
    refine ⟨↑(l * aS)⁻¹, l, hl.unit_spec, ?_⟩
    have hpos : (↑(l * aS)⁻¹ : AdjoinRoot g) * (l : AdjoinRoot g) *
        algebraMap R (AdjoinRoot g) z = 1 := by
      have haS : (aS : AdjoinRoot g) = algebraMap R (AdjoinRoot g) z := by simp [aS, ha]
      rw [← haS, mul_assoc, ← Units.val_mul, Units.inv_mul]
    have hsq : (l : AdjoinRoot g) ^ 2 * algebraMap R (AdjoinRoot g) z =
        algebraMap R (AdjoinRoot g) z - ((qS : AdjoinRoot g) - ↑qS⁻¹) := by
      have hroot : (l : AdjoinRoot g) ^ 2 = AdjoinRoot.of g (↑(b * a⁻¹) : R) := by
        rw [hl.unit_spec]
        exact AdjoinRoot.root_X_pow_sub_C_pow 2 (↑(b * a⁻¹) : R)
      have ha' : (↑a⁻¹ : R) * z = 1 := by rw [← ha, Units.inv_mul]
      rw [hroot, AdjoinRoot.algebraMap_eq, Units.val_mul, ← map_mul, mul_assoc, ha', mul_one, hb,
        map_sub, map_sub]
      simp [qS, AdjoinRoot.algebraMap_eq]
    exact (isHeckeNormalization_iff (q := qS)
      (z := algebraMap R (AdjoinRoot g) z)).mpr ⟨hpos, hsq⟩

/-- Markov invariance of `MarkovBraid.heckeTrace` for `C = (l * a)⁻¹` whenever `(a : R) = z` and
`l ^ 2 * z = z - (q - q⁻¹)`. -/
theorem MarkovEquiv.heckeTrace_eq_of_sq_mul {β γ : MarkovBraid} (h : MarkovEquiv β γ)
    (hτ : IsMarkovTrace z τ) (a l : Rˣ) (ha : (a : R) = z)
    (hl : (l : R) ^ 2 * z = z - ((q : R) - ↑q⁻¹)) :
    β.heckeTrace τ ↑(l * a)⁻¹ l = γ.heckeTrace τ ↑(l * a)⁻¹ l :=
  h.heckeTrace_eq hτ ↑(l * a)⁻¹ l (Units.val_inv_mul_mul_mul_eq_one a l ha)
    (Units.val_inv_mul_mul_inv_mul_eq_one a l ha hl)

end TauCeti
