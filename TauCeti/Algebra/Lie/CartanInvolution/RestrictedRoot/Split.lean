/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.CartanInvolution.RestrictedRoot.WeightSpace
public import Mathlib.Algebra.Lie.Weights.Cartan

/-!
# When a maximal abelian subspace of `𝔭` is a Cartan subalgebra

Let `θ` be a Cartan involution of a real Lie algebra `L` over an ordered field, with fixed
subalgebra `𝔨` and `-1`-eigenspace `𝔭`, and let `𝔞` be a maximal abelian subspace of `𝔭`
(`LieEquiv.IsMaximalAbelianInP`), with centralizer `𝔤_0 = 𝔪 ⊕ 𝔞`, where `𝔪 = 𝔤_0 ∩ 𝔨`. This file
proves that `𝔞` is a Cartan subalgebra of `L` (Mathlib's `LieSubalgebra.IsCartanSubalgebra`)
exactly when `𝔤_0 = 𝔞`, exactly when `𝔪 = 0`. The first equivalence holds for every Lie
subalgebra `𝔞` contained in `𝔭`.

The proof identifies `𝔤_0` with the zero root space of `𝔞` acting on `L`: the operators `ad H`,
`H ∈ 𝔞`, are self-adjoint for `B_θ`, so generalized weight spaces are weight spaces
(`LieEquiv.IsCartanInvolution.toSubmodule_genWeightSpace_eq_restrictedRootSpace`), and a nilpotent
subalgebra is a Cartan subalgebra exactly when it is its own zero root space
(`LieAlgebra.zeroRootSubalgebra_eq_iff_is_cartan`). Then `𝔤_0 = 𝔞` is equivalent to `𝔪 = 0`
because `𝔤_0 = 𝔪 + 𝔞` (`LieEquiv.IsMaximalAbelianInP.restrictedRootSpace_zero_eq_sup`) and
`𝔞 ∩ 𝔨 ⊆ 𝔭 ∩ 𝔨 = 0`.

This is the characterization of split real forms, apart from the comparison of real and complex
ranks.

## Main results

* `LieEquiv.IsCartanInvolution.isCartanSubalgebra_iff_restrictedRootSpace_zero_eq`: a Lie
  subalgebra `𝔞` of `𝔭` is a Cartan subalgebra exactly when `𝔤_0 = 𝔞`.
* `LieEquiv.IsMaximalAbelianInP.restrictedRootSpace_zero_eq_iff`: `𝔤_0 = 𝔞` exactly when `𝔪 = 0`.
* `LieEquiv.IsMaximalAbelianInP.isCartanSubalgebra_iff`: `𝔞` is a Cartan subalgebra exactly when
  `𝔪 = 0`.

## References

* A. W. Knapp, *Lie Groups Beyond an Introduction*, 2nd ed., Chapter VI, §§5–6.
-/

public section

open LieAlgebra LieModule Module

namespace LieEquiv.IsMaximalAbelianInP

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L] {θ : L ≃ₗ⁅R⁆ L}

/-- **`𝔤_0 = 𝔞` exactly when `𝔪 = 0`**: the centralizer of a maximal abelian subspace `𝔞` of
`𝔭` is `𝔞` itself exactly when `𝔪 = 𝔤_0 ∩ 𝔨` vanishes. -/
theorem restrictedRootSpace_zero_eq_iff (h2 : IsUnit (2 : R)) (hθ : Function.Involutive θ)
    {𝔞 : Submodule R L} (h𝔞 : θ.IsMaximalAbelianInP 𝔞) :
    𝔞.restrictedRootSpace 0 = 𝔞 ↔
      𝔞.restrictedRootSpace 0 ⊓ θ.toLieHom.fixedSubalgebra.toSubmodule = ⊥ := by
  constructor
  · intro h
    rw [h, eq_bot_iff]
    refine le_trans (inf_le_inf_right _ h𝔞.le_cartanP) ?_
    rw [inf_comm]
    exact (θ.isCompl_fixedSubalgebra_cartanP h2 hθ).disjoint.le_bot
  · intro h
    rw [h𝔞.restrictedRootSpace_zero_eq_sup h2 hθ, h, bot_sup_eq]

end LieEquiv.IsMaximalAbelianInP

variable {K L : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [LieRing L]
  [LieAlgebra K L] {θ : L ≃ₗ⁅K⁆ L}

namespace LieEquiv.IsCartanInvolution

/-- **A Lie subalgebra `𝔥` of `𝔭` is a Cartan subalgebra exactly when it is its own centralizer
`𝔤_0`**, the zero restricted root space of `𝔥`. -/
theorem isCartanSubalgebra_iff_restrictedRootSpace_zero_eq (hθ : θ.IsCartanInvolution)
    {𝔥 : LieSubalgebra K L} (h𝔥 : 𝔥.toSubmodule ≤ θ.cartanP) :
    𝔥.IsCartanSubalgebra ↔ 𝔥.toSubmodule.restrictedRootSpace 0 = 𝔥.toSubmodule := by
  have : FiniteDimensional K L := hθ.finiteDimensional
  have : IsLieAbelian 𝔥 := isLieAbelian_of_le_cartanP (IsUnit.mk0 _ two_ne_zero) h𝔥
  have h0 := hθ.toSubmodule_genWeightSpace_eq_restrictedRootSpace h𝔥 0
  simp only [LinearMap.zero_apply, ← Pi.zero_def] at h0
  rw [← zeroRootSubalgebra_eq_iff_is_cartan, ← LieSubalgebra.toSubmodule_inj,
    coe_zeroRootSubalgebra, ← h0]

end LieEquiv.IsCartanInvolution

namespace LieEquiv.IsMaximalAbelianInP

/-- **A maximal abelian subspace `𝔞` of `𝔭` is a Cartan subalgebra exactly when `𝔪 = 0`**, where
`𝔪 = 𝔤_0 ∩ 𝔨` is the centralizer of `𝔞` in `𝔨`. -/
theorem isCartanSubalgebra_iff (hθ : θ.IsCartanInvolution) {𝔥 : LieSubalgebra K L}
    (h𝔥 : θ.IsMaximalAbelianInP 𝔥.toSubmodule) :
    𝔥.IsCartanSubalgebra ↔
      𝔥.toSubmodule.restrictedRootSpace 0 ⊓ θ.toLieHom.fixedSubalgebra.toSubmodule = ⊥ := by
  rw [hθ.isCartanSubalgebra_iff_restrictedRootSpace_zero_eq h𝔥.le_cartanP,
    restrictedRootSpace_zero_eq_iff (IsUnit.mk0 _ two_ne_zero) hθ.involutive h𝔥]

end LieEquiv.IsMaximalAbelianInP
