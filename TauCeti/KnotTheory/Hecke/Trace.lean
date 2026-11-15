/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.AdjoinRoot
public import TauCeti.Algebra.TypeAHeckeAlgebra.BaseChange
public import TauCeti.Algebra.TypeAHeckeAlgebra.MarkovTrace
public import TauCeti.KnotTheory.Markov.Basic
import TauCeti.RingTheory.AdjoinRoot.Basic
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
works over any commutative ring once the normalization parameters have been chosen; when the two
stabilization constants `a = z` and `b = z - (q - q⁻¹)` are units of `R`, adjoining a square root
of `b * a⁻¹` via `AdjoinRoot (X ^ 2 - C (b * a⁻¹))` produces a faithful commutative `R`-algebra
extension in which `l ^ 2 = b * a⁻¹` and `C = (l * a)⁻¹` solve both normalization equations.

`MarkovBraid.heckeTrace` is this normalized expression, and `heckeBraidInvariant` is its descent
to the quotient by ordinary unframed Markov equivalence. The unknot value is one, the
`n`-component unlink value is `C ^ (n - 1)`, and the skein coefficients are
`(l⁻¹, -l, -(q - q⁻¹))`. No geometric link carrier or geometric Markov theorem is used.

## Main results

* `LinearMap.heckeTrace_strandIncl` and
  `TauCeti.MarkovBraid.heckeTrace_one_strand`: the split-unknot factor and unknot value.
* `LinearMap.heckeTrace_skein_of_eq_zero`: the skein relation attached to a linear
  relation between a generator and its inverse.
* `TauCeti.MarkovBraid.heckeTrace_map`: compatibility of `heckeTrace` with change of coefficients.
* `TauCeti.MarkovEquiv.heckeTrace_eq_of_sq_eq` and
  `TauCeti.adjoinRoot_sq_heckeTrace_normalization`: Markov invariance from a square root of
  `b * a⁻¹`, and the faithful quadratic `AdjoinRoot` extension supplying that root.

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

/-- Positive Markov stabilization preserves the normalized Hecke trace when
`C * l * z = 1`. -/
theorem heckeTrace_stabilize (hτ : IsMarkovTrace z τ) (C : R) (l : Rˣ)
    (hpos : C * (l : R) * z = 1) (b : BraidGroup (n + 1)) :
    heckeTrace ⟨n + 1, BraidGroup.strandIncl b * BraidGroup.sigma (Fin.last n)⟩ τ C l =
      heckeTrace ⟨n, b⟩ τ C l := by
  simp only [heckeTrace_def]
  rw [hτ.map_braidHom_stabilize]
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
  rw [hτ.map_braidHom_stabilizeInv]
  simp only [map_mul, map_inv,
    BraidGroup.exponentSum_strandIncl, BraidGroup.exponentSum_sigma,
    toAdd_mul, toAdd_inv, toAdd_ofAdd, zpow_add, zpow_neg_one, Units.val_mul, pow_succ]
  calc
    _ = (C * (↑l⁻¹ : R) * (z - ((q : R) - ↑q⁻¹))) *
        (C ^ n * ↑(l ^ Multiplicative.toAdd (ArtinGroup.exponentSum _ b)) *
          τ (braidHom R q (n + 1) b)) := by ring
    _ = _ := by rw [hneg, one_mul]

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

/-- **Change of coefficients for the normalized Hecke trace.** If a functional `τ'` on an
`R`-algebra extension `S` restricts along `InfiniteTypeAHeckeAlgebra.map` to `algebraMap R S ∘ τ`,
then `heckeTrace` commutes with `algebraMap R S`. In particular this applies to `ocneanuTrace` by
`InfiniteTypeAHeckeAlgebra.ocneanuTrace_map`. -/
theorem heckeTrace_map {S : Type*} [CommRing S] [Algebra R S] {q' : Sˣ}
    (hq : algebraMap R S q = q') {τ' : InfiniteTypeAHeckeAlgebra S q' →ₗ[S] S}
    (hτ : ∀ x, τ' (InfiniteTypeAHeckeAlgebra.map hq x) = algebraMap R S (τ x))
    (β : MarkovBraid) (C : R) (l : Rˣ) :
    β.heckeTrace τ' (algebraMap R S C) (Units.map (algebraMap R S).toMonoidHom l) =
      algebraMap R S (β.heckeTrace τ C l) := by
  rw [heckeTrace_def, heckeTrace_def, ← InfiniteTypeAHeckeAlgebra.map_braidHom hq, hτ,
    ← map_zpow (Units.map (algebraMap R S).toMonoidHom) l]
  simp only [map_mul, map_pow, Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_ofClass]

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

private theorem pos_eq_one_of_val_eq (ua l : Rˣ) (ha : (ua : R) = z) :
    (↑(l * ua)⁻¹ : R) * (l : R) * z = 1 := by
  rw [← ha, mul_assoc, ← Units.val_mul, Units.inv_mul]

private theorem neg_eq_one_of_sq_eq (ua ub l : Rˣ) (hb : (ub : R) = z - ((q : R) - ↑q⁻¹))
    (hl : l ^ 2 = ub * ua⁻¹) :
    (↑(l * ua)⁻¹ : R) * (↑l⁻¹ : R) * (z - ((q : R) - ↑q⁻¹)) = 1 := by
  have hub : ub = l ^ 2 * ua := by rw [hl, inv_mul_cancel_right]
  rw [← hb, hub]
  simp only [sq, mul_inv_rev, Units.val_mul]
  calc
    (↑ua⁻¹ : R) * ↑l⁻¹ * ↑l⁻¹ * ((l : R) * (l : R) * (ua : R)) =
      (↑ua⁻¹ : R) * ((↑l⁻¹ : R) * ((↑l⁻¹ : R) * (l : R)) * (l : R)) * (ua : R) := by ring
    _ = 1 := by simp

/-- When the positive and negative stabilization constants `a = z` and `b = z - (q - q⁻¹)` are
units `ua, ub : Rˣ` and `l ^ 2 = ub * ua⁻¹`, taking `C = (l * ua)⁻¹` makes `heckeTrace` Markov
invariant. -/
theorem MarkovEquiv.heckeTrace_eq_of_sq_eq {β γ : MarkovBraid} (h : MarkovEquiv β γ)
    (hτ : IsMarkovTrace z τ) (ua ub l : Rˣ) (ha : (ua : R) = z)
    (hb : (ub : R) = z - ((q : R) - ↑q⁻¹)) (hl : l ^ 2 = ub * ua⁻¹) :
    β.heckeTrace τ ↑(l * ua)⁻¹ l = γ.heckeTrace τ ↑(l * ua)⁻¹ l :=
  h.heckeTrace_eq hτ ↑(l * ua)⁻¹ l (pos_eq_one_of_val_eq ua l ha)
    (neg_eq_one_of_sq_eq ua ub l hb hl)

/-- **Quadratic coefficient extension for the normalization roots.** When the positive and negative
stabilization constants `a = z` and `b = z - (q - q⁻¹)` are units `ua, ub : Rˣ`, adjoining a root
of `X ^ 2 - C (ub * ua⁻¹)` yields a faithful commutative `R`-algebra extension containing a unit
`l` (namely `AdjoinRoot.root _`) with `l ^ 2 = ub * ua⁻¹`, so `C = (l * ua)⁻¹` satisfies both
Markov stabilization equations over the extension. -/
theorem adjoinRoot_sq_heckeTrace_normalization (ua ub : Rˣ) (ha : (ua : R) = z)
    (hb : (ub : R) = z - ((q : R) - ↑q⁻¹)) :
    let S := AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C (↑(ub * ua⁻¹) : R))
    let q' : Sˣ := Units.map (algebraMap R S).toMonoidHom q
    let ua' : Sˣ := Units.map (algebraMap R S).toMonoidHom ua
    let ub' : Sˣ := Units.map (algebraMap R S).toMonoidHom ub
    Function.Injective (algebraMap R S) ∧
      ∃ l : Sˣ,
        (l : S) = AdjoinRoot.root _ ∧
        l ^ 2 = ub' * ua'⁻¹ ∧
        (((l * ua')⁻¹ : Sˣ) : S) * (l : S) * algebraMap R S z = 1 ∧
        (((l * ua')⁻¹ : Sˣ) : S) * ((l⁻¹ : Sˣ) : S) *
          (algebraMap R S z - ((q' : S) - ((q'⁻¹ : Sˣ) : S))) = 1 := by
  dsimp only
  let S := AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C (↑(ub * ua⁻¹) : R))
  let φ : R →* S := (algebraMap R S).toMonoidHom
  refine ⟨?_, ?_⟩
  · rcases subsingleton_or_nontrivial R with _ | _
    · exact Function.injective_of_subsingleton _
    · exact AdjoinRoot.of.injective_of_monic_of_degree_pos
        (Polynomial.monic_X_pow_sub_C _ two_ne_zero)
        (by rw [Polynomial.degree_X_pow_sub_C (by positivity)]; exact zero_lt_two)
  · obtain ⟨l, hl⟩ := AdjoinRoot.isUnit_root_X_pow_sub_C (ub * ua⁻¹).isUnit two_ne_zero
    have hlsq : l ^ 2 = Units.map φ ub * (Units.map φ ua)⁻¹ := by
      rw [← map_inv, ← map_mul]
      ext
      dsimp only [S, φ]
      rw [Units.val_pow_eq_pow_val, hl, Units.coe_map, RingHom.toMonoidHom_eq_coe,
        MonoidHom.coe_ofClass, AdjoinRoot.algebraMap_eq]
      exact AdjoinRoot.root_X_pow_sub_C_pow 2 (↑(ub * ua⁻¹) : R)
    refine ⟨l, hl, hlsq, pos_eq_one_of_val_eq (Units.map φ ua) l ?_,
      neg_eq_one_of_sq_eq (Units.map φ ua) (Units.map φ ub) l ?_ hlsq⟩
    · simp only [Units.coe_map, φ, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_ofClass, ha]
      rfl
    · simp only [Units.coe_map, Units.coe_map_inv, φ, RingHom.toMonoidHom_eq_coe,
        MonoidHom.coe_ofClass, hb, map_sub]
      rfl

end TauCeti
