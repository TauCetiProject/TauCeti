/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.G2.ShortRoot.PrimeField.Root.Simple

/-!
# Intrinsic simple-root trivializations of the short-root G₂ carrier

The intrinsic simple roots determined by the split maximal torus and the positive subgroup of the
short-root type-`G₂` carrier over `𝔽₃` are canonically trivialized by the differentials of the two
numbered raising root subgroups. The equivalence from Bourbaki nodes to intrinsic simple roots
transports the existing one-dimensional root-space calculations to every root in the intrinsic
indexing type.

This is the root-vector datum used by a pinning: each scalar parametrizes the corresponding simple
root space, and the scalar `1` is the normalized differential of the numbered root subgroup. The
construction depends only on the chosen torus and positive subgroup; maximality of the positive
subgroup is a separate property.

## Main declarations

* `TauCeti.G2ShortRoot.PrimeField.adjointWeightSpace_intrinsicSimpleRoot_eq_span`: every intrinsic
  simple-root space is the line spanned by its numbered root vector.
* `TauCeti.G2ShortRoot.PrimeField.intrinsicSimpleRootSpaceEquiv`: the trivialization of every
  intrinsic simple-root space.
* `TauCeti.G2ShortRoot.PrimeField.intrinsicSimpleRootSpaceEquiv_apply_coe`: its value in the
  ambient tangent space is the corresponding scalar multiple of the numbered root vector.

## References

* B. Conrad, *Reductive Group Schemes* (2014), §5.1.
* J. S. Milne, *Algebraic Groups* (2017), §21.1.
-/

public section

namespace TauCeti.G2ShortRoot.PrimeField

open DynkinType

noncomputable section

/-- **Every intrinsic simple-root space is the line spanned by its numbered root vector.** The
numbered vector is selected through the equivalence between Bourbaki nodes and intrinsic simple
roots. -/
theorem adjointWeightSpace_intrinsicSimpleRoot_eq_span
    (α : {α // splitMaximalTorus.IsSimpleRoot positiveDefiningIdeal α}) :
    Derivation.adjointWeightSpace splitMaximalTorus.coordinateMap.hom
        (Multiplicative.ofAdd α.val) =
      (ZMod 3) ∙ rootVector (.inl (simpleRootCharacterEquiv.symm α)) := by
  let i := simpleRootCharacterEquiv.symm α
  have hi : simpleRootCharacter i = α.val :=
    (simpleRootCharacterEquiv_apply i).symm.trans
      (congrArg Subtype.val (simpleRootCharacterEquiv.apply_symm_apply α))
  rw [← hi]
  exact adjointWeightSpace_simpleRootCharacter_eq_span i

/-- The normalized trivialization of an intrinsic simple-root space. Through
`simpleRootCharacterEquiv`, the scalar `1` is sent to the tangent vector of the corresponding
numbered raising root subgroup. -/
def intrinsicSimpleRootSpaceEquiv
    (α : {α // splitMaximalTorus.IsSimpleRoot positiveDefiningIdeal α}) :
    ZMod 3 ≃ₗ[ZMod 3]
      Derivation.adjointWeightSpace splitMaximalTorus.coordinateMap.hom
        (Multiplicative.ofAdd α.val) := by
  let i := simpleRootCharacterEquiv.symm α
  exact (rootSpaceEquiv (.inl i)).trans <| LinearEquiv.ofEq _ _ <|
    (adjointWeightSpace_rootGeneratorWeight_eq_span (.inl i)).trans
      (adjointWeightSpace_intrinsicSimpleRoot_eq_span α).symm

/-- The intrinsic simple-root trivialization sends a scalar to that multiple of the tangent vector
of the corresponding numbered raising root subgroup. -/
@[simp]
theorem intrinsicSimpleRootSpaceEquiv_apply_coe
    (α : {α // splitMaximalTorus.IsSimpleRoot positiveDefiningIdeal α}) (c : ZMod 3) :
    (intrinsicSimpleRootSpaceEquiv α c :
        Module.Dual (ZMod 3) (Bialgebra.CotangentSpace (ZMod 3) carrierAlgebra)) =
      c • rootVector (.inl (simpleRootCharacterEquiv.symm α)) := by
  rw [intrinsicSimpleRootSpaceEquiv, LinearEquiv.trans_apply, LinearEquiv.coe_ofEq_apply,
    rootSpaceEquiv_apply_coe]

end

end TauCeti.G2ShortRoot.PrimeField
