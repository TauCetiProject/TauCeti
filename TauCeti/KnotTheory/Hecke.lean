/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.TypeAHeckeAlgebra.OcneanuTrace
public import TauCeti.KnotTheory.Hecke.Trace
public import TauCeti.KnotTheory.Markov.Skein
import Mathlib.Tactic.LinearCombination

/-!
# Skein characterization of normalized Hecke traces

The normalized braid trace `MarkovBraid.heckeTrace` and its Markov invariance are defined in
`TauCeti.KnotTheory.Hecke.Trace` for any Hecke Markov trace. This file proves its split-unknot
factor, its skein relation for an arbitrary linear relation between a generator and its inverse,
and its characterization by the skein relation and normalization.

The canonical specialization is obtained by taking `τ = ocneanuTrace R q z` and
`hτ = isMarkovTrace_ocneanuTrace z`. In this case the invariant is the braid-closure invariant
Jones constructs from the Ocneanu trace. Its comparison with the HOMFLY invariant built from
Jimbo representations is not made here. The skein relation itself needs only linearity of `τ`.

## Main results

* `TauCeti.MarkovBraid.heckeTrace_skein_of_eq_zero`: the skein relation attached to a linear
  relation between a generator and its inverse.
* `TauCeti.MarkovBraid.heckeTrace_strandIncl` and
  `TauCeti.MarkovBraid.heckeTrace_one_strand`: the split-unknot factor and unknot value.
* `TauCeti.MarkovBraid.eq_heckeTrace_of_skein`: the skein characterization.

## References

* V. F. R. Jones, *Hecke algebra representations of braid groups and link polynomials*,
  Ann. of Math. 126 (1987), 335–388, Section 6.
* C. Kassel and V. Turaev, *Braid Groups*, Springer GTM 247 (2008), Section 4.2.
-/

public section

namespace TauCeti.MarkovBraid

open BraidGroup InfiniteTypeAHeckeAlgebra

variable {R : Type*} [CommRing R] {q : Rˣ} {z : R}
  {τ : InfiniteTypeAHeckeAlgebra R q →ₗ[R] R} {n : ℕ}

/-- **Adding an uncrossed strand multiplies the normalized trace by `C`**: the closure gains a
split unknot. -/
theorem heckeTrace_strandIncl (τ : InfiniteTypeAHeckeAlgebra R q →ₗ[R] R) (C : R) (l : Rˣ)
    (b : BraidGroup (n + 1)) :
    heckeTrace ⟨n + 1, strandIncl b⟩ τ C l = C * heckeTrace ⟨n, b⟩ τ C l := by
  rw [heckeTrace_def, heckeTrace_def, braidHom_strandIncl, exponentSum_strandIncl]
  ring

/-- The only braid on one strand is trivial, and its closure, the unknot, has normalized
trace `1`. -/
theorem heckeTrace_one_strand (hτ : IsMarkovTrace z τ) (C : R) (l : Rˣ)
    (b : BraidGroup 1) : heckeTrace ⟨0, b⟩ τ C l = 1 := by
  rw [eq_one_of_le_one le_rfl b, heckeTrace_one hτ, pow_zero]

/-- **The skein relation attached to a linear relation between a generator and its inverse.** If
`x • T i + y • (T i)⁻¹ + s • 1 = 0` in the Hecke algebra, then for a crossing `σ i` in any braid
context the normalized traces of the positive crossing `L₊`, the negative crossing `L₋` and the
smoothing `L₀` satisfy `x * l⁻¹ * F(L₊) + y * l * F(L₋) + s * F(L₀) = 0`. -/
theorem heckeTrace_skein_of_eq_zero (τ : InfiniteTypeAHeckeAlgebra R q →ₗ[R] R)
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

end TauCeti.MarkovBraid

namespace TauCeti

open BraidGroup MarkovBraid InfiniteTypeAHeckeAlgebra

variable {R : Type*} [CommRing R] {q : Rˣ} {z : R}
  {τ : InfiniteTypeAHeckeAlgebra R q →ₗ[R] R} {l : Rˣ} {C : R}

/-- **The skein characterization of the normalized Hecke trace.** A Markov invariant `F`
satisfying the skein relation `l⁻¹ * F(σᵢ c) - l * F(σᵢ⁻¹ c) = (q - q⁻¹) * F(c)`, multiplied by
`C` when an uncrossed strand is added, and with value `1` on the unknot, is the normalized Hecke
trace. In particular this applies to the Ocneanu trace. -/
theorem MarkovBraid.eq_heckeTrace_of_skein (hτ : IsMarkovTrace z τ)
    (hpos : C * l * z = 1)
    (hneg : C * ↑l⁻¹ * (z - ((q : R) - ↑q⁻¹)) = 1) {F : MarkovBraid → R}
    (hF : ∀ β γ, MarkovEquiv β γ → F β = F γ)
    (hs : ∀ n (c : BraidGroup (n + 1)) (i : Fin n),
      ↑l⁻¹ * F ⟨n, sigma (n := n + 1) i * c⟩ - l * F ⟨n, (sigma (n := n + 1) i)⁻¹ * c⟩ =
        ((q : R) - ↑q⁻¹) * F ⟨n, c⟩)
    (hι : ∀ n (b : BraidGroup (n + 1)), F ⟨n + 1, strandIncl b⟩ = C * F ⟨n, b⟩)
    (h₁ : F ⟨0, 1⟩ = 1) :
    F = fun β ↦ β.heckeTrace τ C l :=
  eq_of_skein l⁻¹ ((q : R) - ↑q⁻¹) C hF
    (fun _ _ h ↦ h.heckeTrace_eq hτ C l hpos hneg)
    (by simpa only [smul_eq_mul, inv_inv] using hs)
    (fun n c i ↦ by simpa only [smul_eq_mul, inv_inv, one_mul] using
      heckeTrace_skein (τ := τ) C l 1 c i)
    (by simpa only [smul_eq_mul] using hι)
    (fun n b ↦ by rw [smul_eq_mul, heckeTrace_strandIncl])
    (by rw [h₁, heckeTrace_one_strand hτ])

end TauCeti
