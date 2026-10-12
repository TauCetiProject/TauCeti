/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Homotopy.Lifting
public import TauCeti.AlgebraicTopology.FundamentalGroup.Homeomorph
public import TauCeti.AlgebraicTopology.NotSimplyConnected
public import TauCeti.AlgebraicTopology.Sphere.SimplyConnected
public import TauCeti.AlgebraicTopology.UniversalCover.LensSpace.Basic

/-!
# The fundamental group of a lens space

The lens space `L(m; ℓ₀, …, ℓₖ)` is the quotient of the unit sphere `S²ᵏ⁺¹ ⊆ ℂᵏ⁺¹` by a free
action of `ℤ/m`. For `1 ≤ k` the sphere is simply connected, so the quotient covering map
`TauCeti.LensSpace.mk` is a universal cover and the fundamental group of the lens space is the
acting group:

  `π₁(L(m; ℓ₀, …, ℓₖ)) ≃* ℤ/m`.

Mathlib's `IsQuotientCoveringMap.fundamentalGroupEquiv` identifies the fundamental group with the
opposite of the acting group `TauCeti.lensGroup m ℓ`; the lens group is commutative and isomorphic
to `ℤ/m` by `TauCeti.lensGroupEquiv`, which removes the opposite. A loop corresponds to the residue
`a` exactly when its monodromy carries the chosen lift of the basepoint to its rotation by `a`.

Consequently a lens space of order `m ≥ 2` is not simply connected, and the order `m` is a
topological invariant: lens spaces of different orders are not homeomorphic. For `k = 0` the lens
space is a circle and its fundamental group is `ℤ`, so the hypothesis `1 ≤ k` is needed.

## Main definitions

* `TauCeti.LensSpace.fundamentalGroupMulEquiv`: for `1 ≤ k`,
  `FundamentalGroup (LensSpace m ℓ) x ≃* Multiplicative (ZMod m)`, for any basepoint `x` with a
  chosen lift `e` to the sphere.

## Main results

* `TauCeti.LensSpace.fundamentalGroupMulEquiv_apply_eq_iff`: the residue assigned to a loop is
  read off from its monodromy.
* `TauCeti.LensSpace.card_fundamentalGroup`: the fundamental group has order `m`.
* `TauCeti.LensSpace.not_simplyConnectedSpace`: a lens space of order `m ≠ 1` is not simply
  connected.
* `TauCeti.LensSpace.eq_of_homeomorph`: homeomorphic lens spaces have the same order.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press (2002), Proposition 1.40 (the
  fundamental group of the quotient of a simply connected space by a covering space action) and
  Example 2.43 (lens spaces).
* The fundamental-group development (`fundamentalGroupMulEquiv`, its monodromy
  characterization, `card_fundamentalGroup`, and `not_simplyConnectedSpace`) is adapted from the
  computation of `π₁(RPⁿ)` in
  `TauCeti.AlgebraicTopology.UniversalCover.RealProjective.FundamentalGroup.Basic`.
-/

public section

open Metric Module

namespace TauCeti

namespace LensSpace

noncomputable section

variable (m : ℕ) [NeZero m] {k : ℕ} (ℓ : Fin (k + 1) → (ZMod m)ˣ)

/-- **The fundamental group of a lens space `L(m; ℓ₀, …, ℓₖ)` with `1 ≤ k` is `ℤ/m`**, at any
basepoint `x` with a chosen lift `e` to the sphere. -/
def fundamentalGroupMulEquiv (hk : 1 ≤ k) {x : LensSpace m ℓ} (e : mk m ℓ ⁻¹' {x}) :
    FundamentalGroup (LensSpace m ℓ) x ≃* Multiplicative (ZMod m) :=
  haveI := simplyConnectedSpace_sphere_euclideanSpace_complex hk
  ((isQuotientCoveringMap_mk m ℓ).fundamentalGroupEquiv e).trans
    ((MulEquiv.op (lensGroupEquiv m ℓ).symm).trans MulOpposite.opMulEquiv.symm)

/-- A loop class corresponds to the residue `a` exactly when its monodromy carries the chosen
lift `e` of the basepoint to the rotation of `e` by `a`. -/
theorem fundamentalGroupMulEquiv_apply_eq_iff (hk : 1 ≤ k) {x : LensSpace m ℓ}
    (e : mk m ℓ ⁻¹' {x}) (γ : FundamentalGroup (LensSpace m ℓ) x)
    (a : Multiplicative (ZMod m)) :
    fundamentalGroupMulEquiv m ℓ hk e γ = a ↔
      lensRotation m ℓ a (e : EuclideanSpace ℂ (Fin (k + 1))) =
        ((isCoveringMap_mk m ℓ).monodromy γ e : EuclideanSpace ℂ (Fin (k + 1))) := by
  have := simplyConnectedSpace_sphere_euclideanSpace_complex hk
  rw [fundamentalGroupMulEquiv, MulEquiv.trans_apply, MulEquiv.trans_apply,
    MulEquiv.symm_apply_eq]
  simp only [MulEquiv.op_apply_apply, MulOpposite.coe_opMulEquiv, Function.comp_apply,
    MulOpposite.op_inj, MulEquiv.symm_apply_eq]
  -- Mathlib has no apply lemma for `IsQuotientCoveringMap.fundamentalGroupEquiv`, which is
  -- `MulEquiv.ofBijective` of `fundamentalGroupToMulOpposite`; its value unfolds by `rfl`.
  have hF : (isQuotientCoveringMap_mk m ℓ).fundamentalGroupEquiv e γ =
      (isQuotientCoveringMap_mk m ℓ).fundamentalGroupToMulOpposite e γ :=
    rfl
  rw [← MulOpposite.op_inj, MulOpposite.op_unop, hF,
    IsQuotientCoveringMap.fundamentalGroupToMulOpposite_apply_eq_Iff, MulOpposite.unop_op,
    Subtype.ext_iff, Subgroup.smul_def, LinearIsometryEquiv.coe_smul_unitSphere,
    coe_lensGroupEquiv_apply]

/-- The fundamental group of a lens space `L(m; ℓ₀, …, ℓₖ)` with `1 ≤ k` has exactly `m`
elements. -/
theorem card_fundamentalGroup (hk : 1 ≤ k) (x : LensSpace m ℓ) :
    Nat.card (FundamentalGroup (LensSpace m ℓ) x) = m := by
  obtain ⟨y, rfl⟩ := mk_surjective m ℓ x
  rw [Nat.card_congr (fundamentalGroupMulEquiv m ℓ hk ⟨y, rfl⟩).toEquiv,
    Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]

/-- A lens space of order `m ≠ 1` with `1 ≤ k` has a nontrivial fundamental group. -/
theorem nontrivial_fundamentalGroup (hk : 1 ≤ k) (hm : m ≠ 1) (x : LensSpace m ℓ) :
    Nontrivial (FundamentalGroup (LensSpace m ℓ) x) := by
  obtain ⟨y, rfl⟩ := mk_surjective m ℓ x
  have : Fact (1 < m) := ⟨by have := NeZero.ne m; omega⟩
  exact (fundamentalGroupMulEquiv m ℓ hk ⟨y, rfl⟩).toEquiv.nontrivial

/-- A lens space of order `m ≠ 1` with `1 ≤ k` is not simply connected. -/
theorem not_simplyConnectedSpace (hk : 1 ≤ k) (hm : m ≠ 1) :
    ¬ SimplyConnectedSpace (LensSpace m ℓ) := by
  let x : LensSpace m ℓ := Classical.arbitrary _
  have := nontrivial_fundamentalGroup m ℓ hk hm x
  exact not_simplyConnectedSpace_of_nontrivial_fundamentalGroup x

/-- **The order of a lens space is a topological invariant**: lens spaces `L(m; ℓ)` and
`L(m'; ℓ')` of dimensions at least three are homeomorphic only if `m = m'`. -/
theorem eq_of_homeomorph {m' : ℕ} [NeZero m'] {k' : ℕ} (ℓ' : Fin (k' + 1) → (ZMod m')ˣ)
    (hk : 1 ≤ k) (hk' : 1 ≤ k') (φ : LensSpace m ℓ ≃ₜ LensSpace m' ℓ') : m = m' := by
  let x : LensSpace m ℓ := Classical.arbitrary _
  rw [← card_fundamentalGroup m ℓ hk x, ← card_fundamentalGroup m' ℓ' hk' (φ x)]
  exact Nat.card_congr (FundamentalGroup.homeomorphMulEquivOfEq φ rfl).toEquiv

end

end LensSpace

end TauCeti
