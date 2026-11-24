/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Padics.AlgebraicClosure.ResidueField
public import TauCeti.RingTheory.RootsOfUnity.IntegrallyClosed
public import TauCeti.RingTheory.RootsOfUnity.LocalRing
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-!
# Roots of unity of prime-to-`p` order in the algebraic closure of `ℚ_p`

Let `O = 𝒪[PadicAlgCl p]` be the valuation ring of the algebraic closure `PadicAlgCl p` of `ℚ_p`
and `κ = 𝓀[PadicAlgCl p]` its residue field. For `m` prime to `p`, reduction modulo the maximal
ideal identifies the `m`-th roots of unity of `PadicAlgCl p` with those of `κ`:

`μ_m(PadicAlgCl p) ≃* μ_m(κ)`.

The roots of unity of `PadicAlgCl p` lie in `O`, which is integrally closed in `PadicAlgCl p`
(`TauCeti.rootsOfUnityMulEquiv`). Reduction is injective on them because `m` is a unit of `O`
(`TauCeti.rootsOfUnityResidue_injective`), and both groups have exactly `m` elements, since
`PadicAlgCl p` and `κ` are algebraically closed and `m` is nonzero in both.

## Main definitions

* `TauCeti.PadicAlgCl.rootsOfUnityResidueEquiv`: reduction `μ_m(PadicAlgCl p) ≃* μ_m(κ)` for `m`
  prime to `p`.
-/

public section

noncomputable section

open IsLocalRing Valued

namespace TauCeti.PadicAlgCl

variable {p : ℕ} [Fact p.Prime] {m : ℕ}

/-- For `m` prime to `p`, the natural number `m` is a unit of `𝒪[PadicAlgCl p]`: its residue is
nonzero, the residue field having characteristic `p`. -/
theorem isUnit_natCast_integer (hm : ¬ p ∣ m) : IsUnit (m : 𝒪[PadicAlgCl p]) := by
  rw [← residue_ne_zero_iff_isUnit, map_natCast]
  exact (CharP.cast_eq_zero_iff 𝓀[PadicAlgCl p] p m).not.mpr hm

/-- Reduction is a bijection from the `m`-th roots of unity of `𝒪[PadicAlgCl p]` to those of its
residue field, for `m` prime to `p`. -/
private theorem rootsOfUnityResidue_bijective (hm : ¬ p ∣ m) :
    Function.Bijective (rootsOfUnityResidue (R := 𝒪[PadicAlgCl p]) m) := by
  have : NeZero m := ⟨by rintro rfl; exact hm (dvd_zero p)⟩
  have : NeZero (m : 𝓀[PadicAlgCl p]) := ⟨(CharP.cast_eq_zero_iff _ p m).not.mpr hm⟩
  have : NeZero (m : PadicAlgCl p) := ⟨Nat.cast_ne_zero.mpr (NeZero.ne m)⟩
  refine (rootsOfUnityResidue_injective (isUnit_natCast_integer hm)).bijective_of_nat_card_le ?_
  rw [HasEnoughRootsOfUnity.natCard_rootsOfUnity 𝓀[PadicAlgCl p] m,
    Nat.card_congr (rootsOfUnityMulEquiv 𝒪[PadicAlgCl p] (PadicAlgCl p) m).toEquiv,
    HasEnoughRootsOfUnity.natCard_rootsOfUnity]

/-- **Roots of unity of prime-to-`p` order reduce isomorphically**: for `m` prime to `p`,
reduction modulo the maximal ideal of `𝒪[PadicAlgCl p]` is an isomorphism from the `m`-th roots of
unity of `PadicAlgCl p` onto those of its residue field. -/
def rootsOfUnityResidueEquiv (hm : ¬ p ∣ m) :
    rootsOfUnity m (PadicAlgCl p) ≃* rootsOfUnity m 𝓀[PadicAlgCl p] :=
  have : NeZero m := ⟨by rintro rfl; exact hm (dvd_zero p)⟩
  (rootsOfUnityMulEquiv 𝒪[PadicAlgCl p] (PadicAlgCl p) m).symm.trans
    (MulEquiv.ofBijective _ (rootsOfUnityResidue_bijective hm))

/-- `rootsOfUnityResidueEquiv` is reduction: the image of a root of unity `ζ`, which has norm `1`
and so lies in `𝒪[PadicAlgCl p]`, is its residue. -/
theorem coe_rootsOfUnityResidueEquiv_apply (hm : ¬ p ∣ m) (ζ : rootsOfUnity m (PadicAlgCl p))
    {x : 𝒪[PadicAlgCl p]} (hx : (x : PadicAlgCl p) = ((ζ : (PadicAlgCl p)ˣ) : PadicAlgCl p)) :
    ((rootsOfUnityResidueEquiv hm ζ : 𝓀[PadicAlgCl p]ˣ) : 𝓀[PadicAlgCl p]) = residue _ x := by
  have : NeZero m := ⟨by rintro rfl; exact hm (dvd_zero p)⟩
  simp only [rootsOfUnityResidueEquiv, MulEquiv.trans_apply, MulEquiv.ofBijective_apply,
    coe_rootsOfUnityResidue]
  congr 1
  apply Subtype.ext
  rw [hx, ← algebraMap_rootsOfUnityMulEquiv_symm_apply 𝒪[PadicAlgCl p] (PadicAlgCl p) m ζ]
  rfl

end TauCeti.PadicAlgCl
