/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Pinning.Basic
public import TauCeti.Algebra.Lie.G2.ShortRoot.PrimeField.Positive.Borel.Basic
public import TauCeti.Algebra.Lie.G2.ShortRoot.PrimeField.Reductive
public import TauCeti.Algebra.Lie.G2.ShortRoot.PrimeField.Root.Trivialization

/-!
# A pinning of the short-root G₂ carrier over 𝔽₃

The short-root type-`G₂` carrier over `𝔽₃` is pinned by its rank-two split maximal weight torus,
its positive subgroup as Borel subgroup, and the differentials of its two numbered raising root
subgroups as simple root vectors. The carrier is reductive over `𝔽₃`, the positive subgroup is a
Borel subgroup containing the torus, and the intrinsic simple-root spaces of this torus and Borel
are trivialized by the numbered root vectors, so these data form a `TauCeti.Pinning`.

The intrinsic simple roots are numbered by the Bourbaki nodes through
`simpleRootCharacterEquiv`, and the stored root vector at node `i` is the tangent vector of the
numbered root subgroup `x_{αᵢ}` at parameter zero. The carrier is not identified here with an
independently constructed pinned group scheme of type `G₂`.

The structure of the construction and its characteristic lemmas follows the pinning
`TauCeti.SlStd.pinning` of the standard special linear carrier in
`TauCeti.Algebra.Lie.SpecialLinear.StandardCarrier.SpecialLinear.Pinning`.

## Main declarations

* `TauCeti.G2ShortRoot.PrimeField.pinning`: the pinning of the carrier.
* `TauCeti.G2ShortRoot.PrimeField.pinningSimpleRootEquiv`: Bourbaki numbering of its simple
  roots.
* `TauCeti.G2ShortRoot.PrimeField.pinning_rootVector`: its root vector at node `i` is the
  numbered root vector.

## References

* B. Conrad, *Reductive Group Schemes* (2014), §5.1.
* J. S. Milne, *Algebraic Groups* (2017), §§21.1 and 23.a.
-/

public section

namespace TauCeti.G2ShortRoot.PrimeField

noncomputable section

/-- The pinning of the short-root G₂ carrier over `𝔽₃`: the split maximal weight torus, the
positive subgroup as Borel subgroup, and the numbered raising root vectors. -/
def pinning : Pinning (ZMod 3) carrierAlgebra 2 where
  reductive := reductiveCommHopfAlgPropertyOver_finiteTypeCarrierAlgebra
  torus := splitMaximalTorus
  borel := positiveDefiningIdeal
  isBorel := isBorelOver_positiveDefiningIdeal
  borel_le_torus := positiveDefiningIdeal_le_splitMaximalTorus_definingIdeal
  rootSpaceEquiv := intrinsicSimpleRootSpaceEquiv

/-- The torus of the pinning is the carrier's split maximal weight torus. -/
@[simp]
theorem pinning_torus : pinning.torus = splitMaximalTorus := (rfl)

/-- The Borel subgroup of the pinning is the positive subgroup. -/
@[simp]
theorem pinning_borel : pinning.borel = positiveDefiningIdeal := (rfl)

/-- Bourbaki numbering of the simple roots of the pinning. -/
def pinningSimpleRootEquiv : Fin 2 ≃ {α // pinning.torus.IsSimpleRoot pinning.borel α} :=
  simpleRootCharacterEquiv

/-- The simple root of the pinning at node `i` is the numbered raising root. -/
@[simp]
theorem pinningSimpleRootEquiv_apply (i : Fin 2) :
    (pinningSimpleRootEquiv i).val = simpleRootCharacter i :=
  simpleRootCharacterEquiv_apply i

/-- The root vector of the pinning at node `i` is the tangent vector of the numbered raising root
subgroup. -/
@[simp↓ 1100]
theorem pinning_rootVector (i : Fin 2) :
    pinning.rootVector (pinningSimpleRootEquiv i) = rootVector (.inl i) := by
  rw [Pinning.rootVector_def]
  have h := intrinsicSimpleRootSpaceEquiv_apply_coe (simpleRootCharacterEquiv i) 1
  rw [Equiv.symm_apply_apply, one_smul] at h
  -- `pinning` stores `intrinsicSimpleRootSpaceEquiv` and `pinningSimpleRootEquiv` is
  -- `simpleRootCharacterEquiv`, so `h` is the goal after unfolding these two definitions.
  exact h

end

end TauCeti.G2ShortRoot.PrimeField
