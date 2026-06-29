/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.AlgebraicTopology.FundamentalGroupProduct
public import TauCeti.AlgebraicTopology.UniversalCover.CircleFundamentalGroup

/-!
# The fundamental group of a torus

Combining the product formula for fundamental groups
(`TauCeti.FundamentalGroup.prodMulEquiv`, `…piMulEquiv`) with the circle computation
`π₁(AddCircle p) ≃* Multiplicative ℤ` (`TauCeti.AddCircle.fundamentalGroupMulEquiv_zero`)
gives the fundamental group of a torus. For a finite product of circles this is the free
abelian group `(Multiplicative ℤ)ᵏ`; in particular the standard two-torus
`AddCircle p × AddCircle q` has fundamental group `Multiplicative ℤ × Multiplicative ℤ`.

This realises the universal-covers roadmap Stage 4 "applications" target `π_n(Tᵏ)` at
`n = 1`: `π₁(Tᵏ) ≅ ℤᵏ`.

## Main declarations

* `TauCeti.AddCircle.prodFundamentalGroupMulEquiv`:
  `π₁(AddCircle p × AddCircle q, (0, 0)) ≃* Multiplicative ℤ × Multiplicative ℤ`.
* `TauCeti.AddCircle.piFundamentalGroupMulEquiv`:
  `π₁(Π i, AddCircle (p i), 0) ≃* Π i, Multiplicative ℤ`, the fundamental group of a torus.
-/

public section

namespace TauCeti

noncomputable section

namespace AddCircle

/-- The fundamental group of the two-torus `AddCircle p × AddCircle q`, based at `(0, 0)`, is
`Multiplicative ℤ × Multiplicative ℤ`, for nonzero real periods `p` and `q`. -/
def prodFundamentalGroupMulEquiv {p q : ℝ} (hp : p ≠ 0) (hq : q ≠ 0) :
    FundamentalGroup (AddCircle p × AddCircle q) (0, 0) ≃*
      Multiplicative ℤ × Multiplicative ℤ :=
  (FundamentalGroup.prodMulEquiv (0 : AddCircle p) (0 : AddCircle q)).trans
    ((fundamentalGroupMulEquiv_zero p hp).prodCongr (fundamentalGroupMulEquiv_zero q hq))

/-- The fundamental group of a torus `Π i, AddCircle (p i)`, based at `0`, is the product
`Π i, Multiplicative ℤ`, for a family of nonzero real periods. For a finite index this is the
free abelian group `(Multiplicative ℤ)ᵏ`, i.e. `π₁(Tᵏ) ≅ ℤᵏ`. -/
def piFundamentalGroupMulEquiv {ι : Type*} {p : ι → ℝ} (hp : ∀ i, p i ≠ 0) :
    FundamentalGroup (∀ i, AddCircle (p i)) (fun _ => 0) ≃* ∀ _ : ι, Multiplicative ℤ :=
  (FundamentalGroup.piMulEquiv (fun i => (0 : AddCircle (p i)))).trans
    (MulEquiv.piCongrRight fun i => fundamentalGroupMulEquiv_zero (p i) (hp i))

end AddCircle

end

end TauCeti
