/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.NumberTheory.HeckeRing.GL2.Gamma0.Basic

/-!
# The Hecke triple of `Γ₁(N)`

The submonoid `Δ₀(N) ⊆ GL₂(ℚ)` of integral matrices with positive determinant that are
upper-triangular modulo `N` with unit upper-left entry, and the Hecke triple it forms with
the image of the congruence subgroup `Γ₁(N)`. This is the level-`N` counterpart of the
arithmetic triple `(Δₙ, SL_n(ℤ))`, and the setting in which the Hecke operators on
`M_k(Γ₁(N))` live.

`Δ₀(N)` is the classical semigroup of Miyake, *Modular Forms*, §4.5: integral, of positive
determinant, with `c ≡ 0` and `a` coprime to `N`, the coprimality spelled here as
`IsUnit (a : ZMod N)`. Asking the upper-left entry to be a *unit* rather than `≡ 1` is what
makes `Γ₀(N) ≤ Δ₀(N)`, so that the resulting Hecke ring carries the diamond operators
alongside the `T_p`: an element of `Γ₀(N)` has `ad ≡ 1` modulo `N`, hence unit `a`, but
`a ≡ 1` only for the elements of `Γ₁(N)` itself. The smaller classical semigroup `Δ₁(N)`,
cut out by `a ≡ 1`, is the sub-semigroup carrying the `T_p` alone.

Determinants divisible by `N` are deliberately admitted: `diag(1, p)` lies in `Δ₀(N)` even
when `p ∣ N`, where it gives the bad-prime operator `U_p`. Because of this, the whole
determinant-`n` part of `Δ₀(N)` is the full diamond orbit of the classical `T_n`, not `T_n`
itself; an operator defined downstream must be cut out of the `a ≡ 1` part rather than taken
as that entire fibre.

Ported from the AINTLIB `LeanModularForms` project
([`LeanModularForms/HeckeRIngs/GL2/Gamma1Pair.lean`](https://github.com/CBirkbeck/AINTLIB),
Chris Birkbeck).

## Main results

* the `IsHeckeTriple (Delta0 N) ((Gamma1 N).map (mapGL ℚ)) ((Gamma1 N).map (mapGL ℚ))`
  instance.

## References

* [G. Shimura, *Introduction to the arithmetic theory of automorphic functions*][shimura1971],
  Chapter 3.
-/

public section

open Matrix Matrix.SpecialLinearGroup CongruenceSubgroup Subgroup
  Subgroup.Commensurable HeckeRing.GLn

open scoped Pointwise MatrixGroups

namespace HeckeRing.GL2

variable (N : ℕ) [NeZero N]

/-- **The Hecke triple of `Γ₁(N)`**: `Γ₁(N) ≤ Δ₀(N) ≤ commensurator(Γ₁(N))` inside
`GL₂(ℚ)` — the setting of the Hecke operators on modular forms of level `N`.

Stated at the unfolded `(Gamma1 N).map (mapGL ℚ)`, which is the spelling consumers meet: the
level of a modular form of level `N` is written `(Gamma1 N).map (mapGL ℝ)` and its rational
companion arrives in the same shape. Instance search does not unfold a `def`, so an abbreviation
for this subgroup would not be found here anyway. -/
instance : IsHeckeTriple (Delta0 N) ((Gamma1 N).map (mapGL ℚ)) ((Gamma1 N).map (mapGL ℚ)) :=
  IsHeckeTriple.of_diagonal
    (fun _ hg ↦ Gamma0Image_le_Delta0 N
      ((Gamma0Image_def N).symm ▸ Subgroup.map_mono (Gamma1_in_Gamma0 N) hg))
    (Delta0_le_commensurator_map N (Gamma1 N))

end HeckeRing.GL2
