/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.FormalScheme.Spf.Discrete
public import Mathlib.Data.ZMod.Basic

/-!
# Examples of the discrete formal-spectrum comparison

The comparison with the ordinary spectrum fixes prime ideals and global coefficients.
These checks use the public API without unfolding the comparison. The nonzero square-zero
coefficient of `ℤ/4` survives, and the construction also applies to the zero ring.
-/

public section

noncomputable section

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry
open TauCeti TauCeti.FormalScheme TauCeti.FormalScheme.Spf

namespace TauCeti.Examples.FormalScheme.Spf

section Discrete

variable (R : Type*) [CommRing R] [TopologicalSpace R] [DiscreteTopology R]

-- No noetherianity or nontriviality assumption is needed.
example : Spf R ≅ Spec.locallyRingedSpaceObj (CommRingCat.of R) := discreteIsoSpec R

-- Both directions keep the prime ideal, not merely its residue characteristic.
example (p : carrier R) : (discreteIsoSpec R).hom.base p = (p : PrimeSpectrum R) :=
  discreteIsoSpec_hom_base_apply R p

example (q : PrimeSpectrum R) :
    Subtype.val ((discreteIsoSpec R).inv.base q : carrier R) = q :=
  discreteIsoSpec_inv_base_apply R q

-- The actual global-section map is the ordinary spectrum coefficient map.
example :
    have := (IsAdicRing.ideal_spec R).2.2
    (globalSectionsIso (IsAdicRing.ideal_spec R).2.1).inv ≫
      (discreteIsoSpec R).inv.c.app (op ⊤) = toSpecΓ (CommRingCat.of R) := by
  intro
  exact discreteIsoSpec_inv_globalSections R

end Discrete

section Nonreduced

/-- The discrete topology for the nonreduced comparison check. -/
local instance comparisonZModFourTopology : TopologicalSpace (ZMod 4) := ⊥
/-- Discreteness of the topology used in the nonreduced comparison check. -/
local instance comparisonZModFourDiscreteTopology : DiscreteTopology (ZMod 4) := ⟨rfl⟩

-- The comparison cannot lose the nonzero nilpotent coefficient `2`.
example :
    have := (IsAdicRing.ideal_spec (ZMod 4)).2.2
    let s := (globalSectionsIso (IsAdicRing.ideal_spec (ZMod 4)).2.1).inv 2
    let t := (discreteIsoSpec (ZMod 4)).inv.c.app (op ⊤) s
    t ≠ 0 ∧ t ^ 2 = 0 := by
  intro
  dsimp only
  have h := (CommRingCat.comp_apply
    (globalSectionsIso (IsAdicRing.ideal_spec (ZMod 4)).2.1).inv
    ((discreteIsoSpec (ZMod 4)).inv.c.app (op ⊤)) (2 : ZMod 4)).symm.trans
      (ConcreteCategory.congr_hom (discreteIsoSpec_inv_globalSections (ZMod 4)) 2)
  have hn : (toSpecΓ (CommRingCat.of (ZMod 4))) 2 ≠ 0 := by
    intro hz
    have hi := (ConcreteCategory.bijective_of_isIso (toSpecΓ (CommRingCat.of (ZMod 4)))).injective
    exact (by decide : (2 : ZMod 4) ≠ 0) (hi (hz.trans (map_zero _).symm))
  refine ⟨fun hz ↦ hn (h.symm.trans hz), ?_⟩
  refine (congrArg (· ^ 2) h).trans ?_
  rw [← map_pow]
  exact (congrArg (toSpecΓ (CommRingCat.of (ZMod 4))) (by decide : (2 : ZMod 4) ^ 2 = 0)).trans
    (map_zero _)

end Nonreduced

section Zero

/-- The discrete topology for the empty-spectrum comparison check. -/
local instance comparisonZModOneTopology : TopologicalSpace (ZMod 1) := ⊥
/-- Discreteness of the topology used in the empty-spectrum comparison check. -/
local instance comparisonZModOneDiscreteTopology : DiscreteTopology (ZMod 1) := ⟨rfl⟩

-- The zero-ideal inclusion is invertible even when the spectra are empty.
example : IsIso (fromSpecQuotient (is_bot_adic_iff.mpr inferInstance :
    IsAdic (⊥ : Ideal (ZMod 1)))) := inferInstance

example : Spf (ZMod 1) ≅ Spec.locallyRingedSpaceObj (CommRingCat.of (ZMod 1)) :=
  discreteIsoSpec (ZMod 1)

end Zero

end TauCeti.Examples.FormalScheme.Spf
