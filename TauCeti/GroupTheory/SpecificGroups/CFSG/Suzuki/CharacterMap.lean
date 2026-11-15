/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Symplectic.StandardCarrier.CharacterMap
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Suzuki.Basic

/-!
# The character map of the represented Suzuki Steinberg endomorphism

For every valid Suzuki parameter, the odd power of the matrix-of-minors special isogeny has
character pullback equal to the weight map of the independently defined root-datum Steinberg map.
The torus uses type-B₂ fundamental-weight coordinates; its embedding into the symplectic carrier
includes the node swap. This comparison concerns the represented carrier, without identifying it
with a canonical Chevalley–Demazure group.

## References

* R. W. Carter, *Simple Groups of Lie Type*, §13.4.
* A.-C. Radu, *On the cohomology of the Ree groups and kernels of exceptional isogenies*,
  arXiv:2108.06291v2, §2.2, for the odd-power construction.
-/

public section

namespace TauCeti.SuzukiLieIndex

/-- The represented Suzuki Steinberg map pulls characters back by the weight map of the native
root-datum Steinberg map. Both maps use the valid index's own field exponent. -/
theorem isCharacterMap_steinberg_suzuki (m : ℕ) (hv : (LieTypeIndex.suzuki m).Valid) :
    IsCharacterMap (SpStd.b2WeightTorusPoints (of m hv).1.Closure) (of m hv).steinberg
      (of m hv).toSuzukiReeIndex.datumSteinberg.weightMap := by
  let d := of m hv
  have : CharP d.1.Closure 2 := by
    rw [← d.characteristic_eq_two]
    infer_instance
  have h : IsCharacterMap (SpStd.b2WeightTorusPoints d.1.Closure) d.halfFrobenius
      DynkinType.b2SpecialIsogeny.weightMap := by
    rw [halfFrobenius_def]
    exact SpStd.isCharacterMap_specialIsogeny _
  have hpow := h.pow d.1.fieldExponent
  rw [← steinberg_def] at hpow
  rw [SuzukiReeIndex.datumSteinberg_def, RootPairingIsogeny.weightMap_pow,
    SuzukiReeIndex.datumSpecialIsogeny_weightMap_suzuki]
  exact hpow

end TauCeti.SuzukiLieIndex
