/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.TypeAHeckeAlgebra.OcneanuTrace
public import TauCeti.KnotTheory.Markov.Skein
import Mathlib.Tactic.LinearCombination

/-!
# The braid-closure invariant of the Ocneanu trace

Let `γₙ : BraidGroup n → H` be the braid homomorphism into the infinite type-A Hecke algebra
`TauCeti.InfiniteTypeAHeckeAlgebra R q`, sending `σ i` to `T i`
(`TauCeti.InfiniteTypeAHeckeAlgebra.braidHom`), and let `tr_z` be the Ocneanu trace with
parameter `z` (`TauCeti.InfiniteTypeAHeckeAlgebra.ocneanuTrace`). Adding a strand and crossing it
once with the previous one multiplies the trace by one of the two stabilization constants

* `a = tr_z (γ (σₙ)) = tr_z (T n) = z`, for a positive crossing, and
* `b = tr_z (γ (σₙ⁻¹)) = tr_z ((T n)⁻¹) = z - (q - q⁻¹)`, for a negative crossing,

independently of the braid it is added to, by the Markov rule
(`TauCeti.InfiniteTypeAHeckeAlgebra.IsMarkovTrace.map_mul_T` and
`TauCeti.InfiniteTypeAHeckeAlgebra.IsMarkovTrace.map_mul_val_inv_unitT`). For a unit `λ` (the
argument `l`) and a scalar `C` with `C * λ * a = 1` and `C * λ⁻¹ * b = 1`, the writhe- and
strand-normalized trace

`F(β) = C ^ (n - 1) * λ ^ w(β) * tr_z (γₙ β)`,

for `β` a braid on `n` strands with exponent sum `w(β)`, is unchanged by conjugation and by both
stabilizations (`TauCeti.MarkovBraid.heckeTrace_conj`, `TauCeti.MarkovBraid.heckeTrace_stabilize`
and `TauCeti.MarkovBraid.heckeTrace_stabilizeInv`). It is therefore constant on Markov
equivalence classes (`TauCeti.MarkovEquiv.heckeTrace_eq`), so by Markov's theorem an invariant of
the oriented link closing the braid. This is the link invariant Jones builds from the Ocneanu
trace; its comparison with the HOMFLY polynomial `TauCeti.MarkovBraid.homfly`, which is built from
the Jimbo representations, is not made here.

The invariant has value `1` on the unknot and is multiplied by `C` when an uncrossed strand is
added, that is, when a split unknot is added to the closure. A relation
`x • T i + y • (T i)⁻¹ + s • 1 = 0` in the Hecke algebra becomes the skein relation
`(x / λ) F(L₊) + (y λ) F(L₋) + s F(L₀) = 0` for any crossing in any braid context
(`TauCeti.MarkovBraid.heckeTrace_skein_of_eq_zero`); in particular `T i - (T i)⁻¹ = q - q⁻¹` gives
`λ⁻¹ F(L₊) - λ F(L₋) = (q - q⁻¹) F(L₀)` (`TauCeti.MarkovBraid.heckeTrace_skein`). Together with
the uniqueness of skein invariants (`TauCeti.MarkovBraid.eq_of_skein`), these properties
characterize the invariant (`TauCeti.MarkovBraid.eq_heckeTrace_of_skein`).

No root of `b / a` is chosen here: the unit `λ` and the scalar `C` are parameters, and the
invariance theorems assume the two normalization equations. They force `a` and `b` to be units;
conversely, if `a` and `b` are units and `λ ^ 2 = b / a`, then `C = (λ * a)⁻¹` satisfies both.

## Main definitions

* `TauCeti.MarkovBraid.heckeTrace`: the normalized Ocneanu trace `F(β)` of a braid.

## Main results

* `TauCeti.MarkovEquiv.heckeTrace_eq`: Markov-equivalent braids have the same normalized trace.
* `TauCeti.MarkovBraid.heckeTrace_skein_of_eq_zero` and `TauCeti.MarkovBraid.heckeTrace_skein`:
  the skein relations.
* `TauCeti.MarkovBraid.heckeTrace_strandIncl` and `TauCeti.MarkovBraid.heckeTrace_one`: the
  values on split unions with an unknot and on trivial braids.
* `TauCeti.MarkovBraid.eq_heckeTrace_of_skein`: the skein characterization.

## References

* V. F. R. Jones, *Hecke algebra representations of braid groups and link polynomials*,
  Ann. of Math. 126 (1987), 335–388, Section 6.
* C. Kassel and V. Turaev, *Braid Groups*, Springer GTM 247 (2008), Section 4.2.
-/

public section

namespace TauCeti.MarkovBraid

open BraidGroup InfiniteTypeAHeckeAlgebra

variable {R : Type*} [CommRing R] {n : ℕ}

/-- The normalized Ocneanu trace of a braid `β` on `n` strands with exponent sum `w`:
`C ^ (n - 1) * l ^ w * tr_z (γₙ β)`, where `tr_z` is the Ocneanu trace with parameter `z` on the
infinite type-A Hecke algebra and `γₙ` is the braid homomorphism `σ i ↦ T i`. When
`C * l * z = 1` and `C * l⁻¹ * (z - (q - q⁻¹)) = 1` it is a Markov invariant
(`TauCeti.MarkovEquiv.heckeTrace_eq`) with value `1` on the unknot. -/
noncomputable def heckeTrace (β : MarkovBraid) (q : Rˣ) (z : R) (l : Rˣ) (C : R) : R :=
  C ^ β.predStrands * ((l ^ Multiplicative.toAdd (ArtinGroup.exponentSum _ β.braid) : Rˣ) : R) *
    ocneanuTrace R q z (braidHom R q (β.predStrands + 1) β.braid)

/-- The normalized trace is the Ocneanu trace of the braid's image, corrected by the writhe and
the number of strands. -/
theorem heckeTrace_def (β : MarkovBraid) (q : Rˣ) (z : R) (l : Rˣ) (C : R) :
    heckeTrace β q z l C =
      C ^ β.predStrands *
        ((l ^ Multiplicative.toAdd (ArtinGroup.exponentSum _ β.braid) : Rˣ) : R) *
          ocneanuTrace R q z (braidHom R q (β.predStrands + 1) β.braid) := (rfl)

variable (q : Rˣ) (z : R) (l : Rˣ) (C : R)

/-- **Markov move I leaves the normalized trace unchanged**, by the trace property. -/
@[simp]
theorem heckeTrace_conj (b c : BraidGroup (n + 1)) :
    heckeTrace ⟨n, c * b * c⁻¹⟩ q z l C = heckeTrace ⟨n, b⟩ q z l C := by
  simp only [heckeTrace_def, map_mul, map_inv, Units.val_mul]
  rw [(isMarkovTrace_ocneanuTrace z).map_mul_comm, ← mul_assoc, ← Units.val_mul, inv_mul_cancel,
    Units.val_one, one_mul, mul_comm (ArtinGroup.exponentSum _ c), mul_inv_cancel_right]

/-- **Adding an uncrossed strand multiplies the normalized trace by `C`**: the closure gains a
split unknot. -/
theorem heckeTrace_strandIncl (b : BraidGroup (n + 1)) :
    heckeTrace ⟨n + 1, strandIncl b⟩ q z l C = C * heckeTrace ⟨n, b⟩ q z l C := by
  rw [heckeTrace_def, heckeTrace_def, braidHom_strandIncl, exponentSum_strandIncl]
  ring

/-- The trivial braid on `n + 1` strands, whose closure is the `(n + 1)`-component unlink, has
normalized trace `C ^ n`. -/
@[simp]
theorem heckeTrace_one : heckeTrace ⟨n, 1⟩ q z l C = C ^ n := by
  simp [heckeTrace_def]

/-- The only braid on one strand is trivial, and its closure, the unknot, has normalized
trace `1`. -/
@[simp]
theorem heckeTrace_one_strand (b : BraidGroup 1) : heckeTrace ⟨0, b⟩ q z l C = 1 := by
  rw [eq_one_of_le_one le_rfl b, heckeTrace_one, pow_zero]

variable {q z l C}

/-- **Positive stabilization leaves the normalized trace unchanged**: the new crossing multiplies
the trace by `z`, the writhe factor `l ^ w` by `l` and the strand factor by `C`. -/
theorem heckeTrace_stabilize (hpos : C * l * z = 1) (b : BraidGroup (n + 1)) :
    heckeTrace ⟨n + 1, strandIncl b * sigma (Fin.last n)⟩ q z l C = heckeTrace ⟨n, b⟩ q z l C := by
  simp only [heckeTrace_def, map_mul, braidHom_strandIncl, braidHom_sigma, Units.val_mul,
    val_unitT, Fin.val_last, (isMarkovTrace_ocneanuTrace z).map_mul_T (braidHom_mem_stage b),
    exponentSum_strandIncl, exponentSum_sigma, toAdd_mul, toAdd_ofAdd, zpow_add, zpow_one]
  linear_combination C ^ n * ((l ^ Multiplicative.toAdd (ArtinGroup.exponentSum _ b) : Rˣ) : R) *
    ocneanuTrace R q z (braidHom R q (n + 1) b) * hpos

/-- **Negative stabilization leaves the normalized trace unchanged**: the new crossing multiplies
the trace by `z - (q - q⁻¹)`, the writhe factor `l ^ w` by `l⁻¹` and the strand factor by `C`. -/
theorem heckeTrace_stabilizeInv (hneg : C * ↑l⁻¹ * (z - ((q : R) - ↑q⁻¹)) = 1)
    (b : BraidGroup (n + 1)) :
    heckeTrace ⟨n + 1, strandIncl b * (sigma (Fin.last n))⁻¹⟩ q z l C =
      heckeTrace ⟨n, b⟩ q z l C := by
  simp only [heckeTrace_def, map_mul, map_inv, braidHom_strandIncl, braidHom_sigma, Units.val_mul,
    Fin.val_last, (isMarkovTrace_ocneanuTrace z).map_mul_val_inv_unitT (braidHom_mem_stage b),
    exponentSum_strandIncl, exponentSum_sigma, toAdd_mul, toAdd_inv, toAdd_ofAdd, zpow_add,
    zpow_neg_one]
  linear_combination C ^ n * ((l ^ Multiplicative.toAdd (ArtinGroup.exponentSum _ b) : Rˣ) : R) *
    ocneanuTrace R q z (braidHom R q (n + 1) b) * hneg

/-- **The skein relation attached to a linear relation between a generator and its inverse.** If
`x • T i + y • (T i)⁻¹ + s • 1 = 0` in the Hecke algebra, then for a crossing `σ i` in any braid
context the normalized traces of the positive crossing `L₊`, the negative crossing `L₋` and the
smoothing `L₀` satisfy `x * l⁻¹ * F(L₊) + y * l * F(L₋) + s * F(L₀) = 0`. -/
theorem heckeTrace_skein_of_eq_zero {x y s : R} (i : Fin n)
    (h : x • T q i + y • (↑(unitT q i)⁻¹ : InfiniteTypeAHeckeAlgebra R q) + s • 1 = 0)
    (b c : BraidGroup (n + 1)) :
    x * ↑l⁻¹ * heckeTrace ⟨n, b * sigma (n := n + 1) i * c⟩ q z l C +
        y * l * heckeTrace ⟨n, b * (sigma (n := n + 1) i)⁻¹ * c⟩ q z l C +
          s * heckeTrace ⟨n, b * c⟩ q z l C = 0 := by
  -- The trace of the relation, inserted between the two halves of the braid context.
  have htr := congrArg
    (fun X ↦ ocneanuTrace R q z (braidHom R q (n + 1) b * X * braidHom R q (n + 1) c)) h
  simp only [mul_add, add_mul, smul_mul_assoc, mul_smul_comm, mul_one, map_add, map_smul,
    smul_eq_mul, mul_zero, zero_mul, map_zero] at htr
  simp only [heckeTrace_def, map_mul, map_inv, braidHom_sigma, Units.val_mul, val_unitT,
    exponentSum_sigma, toAdd_mul, toAdd_inv, toAdd_ofAdd]
  generalize Multiplicative.toAdd (ArtinGroup.exponentSum _ b) = p
  generalize Multiplicative.toAdd (ArtinGroup.exponentSum _ c) = r
  rw [show p + 1 + r = (p + r) + 1 by ring, show p + -1 + r = (p + r) - 1 by ring, zpow_add_one,
    zpow_sub_one, Units.val_mul, Units.val_mul]
  -- After the writhe correction `l ^ (p + r)` is split off, `l⁻¹ * l` and `l * l⁻¹` cancel.
  linear_combination C ^ n * ((l ^ (p + r) : Rˣ) : R) * htr +
    C ^ n * ((l ^ (p + r) : Rˣ) : R) * x * ocneanuTrace R q z
      (braidHom R q (n + 1) b * T q i * braidHom R q (n + 1) c) * l.inv_mul +
    C ^ n * ((l ^ (p + r) : Rˣ) : R) * y * ocneanuTrace R q z
      (braidHom R q (n + 1) b * ↑(unitT q i)⁻¹ * braidHom R q (n + 1) c) * l.mul_inv

/-- **The skein relation of the normalized trace**: since `T i - (T i)⁻¹ = q - q⁻¹`, for a
crossing `σ i` in any braid context, `l⁻¹ * F(L₊) - l * F(L₋) = (q - q⁻¹) * F(L₀)`. -/
theorem heckeTrace_skein (i : Fin n) (b c : BraidGroup (n + 1)) :
    ↑l⁻¹ * heckeTrace ⟨n, b * sigma (n := n + 1) i * c⟩ q z l C -
        l * heckeTrace ⟨n, b * (sigma (n := n + 1) i)⁻¹ * c⟩ q z l C =
      ((q : R) - ↑q⁻¹) * heckeTrace ⟨n, b * c⟩ q z l C := by
  have h : (1 : R) • T q i + (-1 : R) • (↑(unitT q i)⁻¹ : InfiniteTypeAHeckeAlgebra R q) +
      (-((q : R) - ↑q⁻¹)) • 1 = 0 := by
    rw [val_inv_unitT, Algebra.algebraMap_eq_smul_one]
    module
  linear_combination heckeTrace_skein_of_eq_zero (z := z) (l := l) (C := C) i h b c

end TauCeti.MarkovBraid

namespace TauCeti

open BraidGroup MarkovBraid

variable {R : Type*} [CommRing R] {q : Rˣ} {z : R} {l : Rˣ} {C : R}

/-- A single Markov move does not change the normalized trace. -/
theorem IsMarkovMove.heckeTrace_eq (hpos : C * l * z = 1)
    (hneg : C * ↑l⁻¹ * (z - ((q : R) - ↑q⁻¹)) = 1) {β γ : MarkovBraid} (h : IsMarkovMove β γ) :
    β.heckeTrace q z l C = γ.heckeTrace q z l C := by
  induction h with
  | conj b c => exact heckeTrace_conj q z l C b c
  | stabilize b => exact heckeTrace_stabilize hpos b
  | stabilizeInv b => exact heckeTrace_stabilizeInv hneg b

/-- **The normalized Ocneanu trace is a Markov invariant.** When `C * l * z = 1` and
`C * l⁻¹ * (z - (q - q⁻¹)) = 1`, Markov-equivalent braids have the same normalized trace; by
Markov's theorem it is an invariant of the oriented link obtained by closing the braid. -/
theorem MarkovEquiv.heckeTrace_eq (hpos : C * l * z = 1)
    (hneg : C * ↑l⁻¹ * (z - ((q : R) - ↑q⁻¹)) = 1) {β γ : MarkovBraid} (h : MarkovEquiv β γ) :
    β.heckeTrace q z l C = γ.heckeTrace q z l C :=
  h.induction (fun hmove ↦ hmove.heckeTrace_eq hpos hneg) (fun _ ↦ rfl) (fun _ ih ↦ ih.symm)
    (fun _ _ ih ih' ↦ ih.trans ih')

/-- **The skein characterization of the normalized Ocneanu trace.** A Markov invariant `F`
satisfying the skein relation `l⁻¹ * F(σᵢ c) - l * F(σᵢ⁻¹ c) = (q - q⁻¹) * F(c)`, multiplied by
`C` when an uncrossed strand is added, and with value `1` on the unknot, is the normalized Ocneanu
trace. -/
theorem MarkovBraid.eq_heckeTrace_of_skein (hpos : C * l * z = 1)
    (hneg : C * ↑l⁻¹ * (z - ((q : R) - ↑q⁻¹)) = 1) {F : MarkovBraid → R}
    (hF : ∀ β γ, MarkovEquiv β γ → F β = F γ)
    (hs : ∀ n (c : BraidGroup (n + 1)) (i : Fin n),
      ↑l⁻¹ * F ⟨n, sigma (n := n + 1) i * c⟩ - l * F ⟨n, (sigma (n := n + 1) i)⁻¹ * c⟩ =
        ((q : R) - ↑q⁻¹) * F ⟨n, c⟩)
    (hι : ∀ n (b : BraidGroup (n + 1)), F ⟨n + 1, strandIncl b⟩ = C * F ⟨n, b⟩)
    (h₁ : F ⟨0, 1⟩ = 1) :
    F = fun β ↦ β.heckeTrace q z l C :=
  eq_of_skein l⁻¹ ((q : R) - ↑q⁻¹) C hF (fun _ _ h ↦ h.heckeTrace_eq hpos hneg)
    (by simpa only [smul_eq_mul, inv_inv] using hs)
    (fun n c i ↦ by simpa only [smul_eq_mul, inv_inv, one_mul] using
      heckeTrace_skein (q := q) (z := z) (l := l) (C := C) i 1 c)
    (by simpa only [smul_eq_mul] using hι)
    (fun n b ↦ by rw [smul_eq_mul, heckeTrace_strandIncl]) (by rw [h₁, heckeTrace_one_strand])

end TauCeti
