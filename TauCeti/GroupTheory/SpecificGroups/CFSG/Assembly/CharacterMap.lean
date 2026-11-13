/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.LieType
public import TauCeti.GroupTheory.SpecificGroups.CFSG.OrdinarySteinberg
public import TauCeti.GroupTheory.SpecificGroups.CFSG.TypeA.CharacterMap
public import TauCeti.GroupTheory.SpecificGroups.CFSG.TypeB.CharacterMap
public import TauCeti.GroupTheory.SpecificGroups.CFSG.TypeC.CharacterMap
public import TauCeti.GroupTheory.SpecificGroups.CFSG.TypeD.CharacterMap
public import TauCeti.GroupTheory.SpecificGroups.CFSG.TypeE6.CharacterMap
public import TauCeti.GroupTheory.SpecificGroups.CFSG.TypeE7.CharacterMap
public import TauCeti.GroupTheory.SpecificGroups.CFSG.TwistedE6.CharacterMap
public import TauCeti.GroupTheory.SpecificGroups.CFSG.TrialityD4.CharacterMap
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Suzuki.CharacterMap
public import TauCeti.GroupTheory.SpecificGroups.CFSG.ReeG2.CharacterMap
public import TauCeti.GroupTheory.SpecificGroups.CFSG.ReeF4.CharacterMap
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Tits.CharacterMap

/-!
# Character pullback of the represented Lie-type Steinberg maps

The ambient group of every valid Lie-type index has its represented weight torus, in
Bourbaki-numbered fundamental-weight coordinates. On this torus the represented Steinberg
endomorphism has character pullback equal to the weight map of the independently defined
root-datum Steinberg isogeny. This supplies a uniform model-side torus equation for comparisons
with other pinned realizations.

`ValidLieTypeIndex.weightTorus` selects the existing family torus, not a torus defined by
transport from a canonical carrier. In the Suzuki branch it uses `SpStd.b2WeightTorusPoints`,
including the B₂-to-C₂ node swap. The graph-twisted branches retain inverse diagram action on
characters, and the exceptional branches retain the native odd-power exponents. No assertion
about canonical-carrier comparisons, point generation, finiteness or simplicity is made here.

The dispatch follows `ValidLieTypeIndex.AmbientGroup` and `ValidLieTypeIndex.steinberg`.
The proofs consume the family character-map comparisons in the imported `CharacterMap`
modules; in the untwisted Geck branches they use `steinberg_geckWeightTorus`.

## References

* R. Steinberg, *Endomorphisms of linear algebraic groups*, Mem. Amer. Math. Soc. **80**
  (1968), §11.
* R. W. Carter, *Finite Groups of Lie Type: Conjugacy Classes and Complex Characters*, §1.17.
* A.-C. Radu, *On the cohomology of the Ree groups and kernels of exceptional isogenies*,
  arXiv:2108.06291v2, §2.2, for the exceptional odd-power construction.
-/

public section

namespace TauCeti.UnimodularExceptionalIndex

/-- The native datum Steinberg map is the character pullback of the represented Steinberg
map on the full-weight Geck torus of an untwisted unimodular exceptional index. -/
theorem isCharacterMap_steinberg (d : UnimodularExceptionalIndex) :
    IsCharacterMap d.1.1.geckWeightTorus d.steinberg d.1.1.datumSteinberg.weightMap := by
  rw [d.1.1.datumSteinberg_weightMap_of_diagramPerm_eq_one
    d.2 d.diagramPerm_toGraphTwistedIndex]
  exact IsCharacterMap.of_map_eq_pow d.steinberg_geckWeightTorus

end TauCeti.UnimodularExceptionalIndex

namespace TauCeti.ValidLieTypeIndex

noncomputable section

/-- The represented weight torus in the fundamental-weight coordinates of the valid index.
The Suzuki branch includes the B₂-to-C₂ adapter of the symplectic model. -/
def weightTorus : (d : ValidLieTypeIndex) → (Fin d.rank → d.Closureˣ) →* d.AmbientGroup
  | ⟨.A _ _, hv⟩ | ⟨.twistedA _ _, hv⟩ => TypeALieIndex.weightTorus ⟨⟨_, hv⟩, by simp⟩
  | ⟨.B _ _, hv⟩ => TypeBLieIndex.weightTorus ⟨⟨_, hv⟩, trivial⟩
  | ⟨.C _ _, hv⟩ => TypeCLieIndex.weightTorus ⟨⟨_, hv⟩, trivial⟩
  | ⟨.D _ _, hv⟩ | ⟨.twistedD _ _, hv⟩ =>
      TypeDDiagramLieIndex.weightTorus ⟨⟨_, hv⟩, by simp⟩
  | ⟨.E6 _, hv⟩ => TypeE6LieIndex.weightTorus ⟨⟨_, hv⟩, by simp⟩
  | ⟨.E7 _, hv⟩ => TypeE7LieIndex.weightTorus ⟨⟨_, hv⟩, by simp⟩
  | ⟨.E8 _, hv⟩ | ⟨.F4 _, hv⟩ | ⟨.G2 _, hv⟩ => geckWeightTorus ⟨_, hv⟩
  | ⟨.twistedE6 _, hv⟩ => TypeTwistedE6LieIndex.weightTorus ⟨⟨_, hv⟩, by simp⟩
  | ⟨.trialityD4 _, hv⟩ => TypeTrialityD4LieIndex.weightTorus ⟨⟨_, hv⟩, by simp⟩
  | ⟨.suzuki m, hv⟩ => SpStd.b2WeightTorusPoints (SuzukiLieIndex.of m hv).1.Closure
  | ⟨.reeG2 m, hv⟩ => (ReeG2LieIndex.of m hv).weightTorus
  | ⟨.reeF4 m, hv⟩ => (ReeF4LieIndex.of m hv).weightTorus
  | ⟨.tits, _⟩ => TitsLieIndex.of.weightTorus

section Branches

variable {n m : ℕ} {q : PrimePower}

/-- On type A the represented torus is the standard special-linear weight torus. -/
theorem weightTorus_A (hv : (LieTypeIndex.A n q).Valid) :
    weightTorus ⟨_, hv⟩ = TypeALieIndex.weightTorus ⟨⟨_, hv⟩, by simp⟩ :=
  (rfl)

/-- On twisted type A the represented torus is the standard special-linear weight torus. -/
theorem weightTorus_twistedA (hv : (LieTypeIndex.twistedA n q).Valid) :
    weightTorus ⟨_, hv⟩ = TypeALieIndex.weightTorus ⟨⟨_, hv⟩, by simp⟩ :=
  (rfl)

/-- On type B the represented torus is the full-weight spin torus. -/
theorem weightTorus_B (hv : (LieTypeIndex.B n q).Valid) :
    weightTorus ⟨_, hv⟩ = TypeBLieIndex.weightTorus ⟨⟨_, hv⟩, trivial⟩ :=
  (rfl)

/-- On type C the represented torus is the standard symplectic weight torus. -/
theorem weightTorus_C (hv : (LieTypeIndex.C n q).Valid) :
    weightTorus ⟨_, hv⟩ = TypeCLieIndex.weightTorus ⟨⟨_, hv⟩, trivial⟩ :=
  (rfl)

/-- On type D the represented torus is the full-weight spin torus. -/
theorem weightTorus_D (hv : (LieTypeIndex.D n q).Valid) :
    weightTorus ⟨_, hv⟩ = TypeDDiagramLieIndex.weightTorus ⟨⟨_, hv⟩, by simp⟩ :=
  (rfl)

/-- On twisted type D the represented torus is the full-weight spin torus. -/
theorem weightTorus_twistedD (hv : (LieTypeIndex.twistedD n q).Valid) :
    weightTorus ⟨_, hv⟩ = TypeDDiagramLieIndex.weightTorus ⟨⟨_, hv⟩, by simp⟩ :=
  (rfl)

/-- On type E₆ the represented torus is the minuscule weight torus. -/
theorem weightTorus_E6 (hv : (LieTypeIndex.E6 q).Valid) :
    weightTorus ⟨_, hv⟩ = TypeE6LieIndex.weightTorus ⟨⟨_, hv⟩, by simp⟩ :=
  (rfl)

/-- On type E₇ the represented torus is the minuscule weight torus. -/
theorem weightTorus_E7 (hv : (LieTypeIndex.E7 q).Valid) :
    weightTorus ⟨_, hv⟩ = TypeE7LieIndex.weightTorus ⟨⟨_, hv⟩, by simp⟩ :=
  (rfl)

/-- On type E₈ the represented torus is the Geck weight torus. -/
theorem weightTorus_E8 (hv : (LieTypeIndex.E8 q).Valid) :
    weightTorus ⟨_, hv⟩ = geckWeightTorus ⟨_, hv⟩ :=
  (rfl)

/-- On type F₄ the represented torus is the Geck weight torus. -/
theorem weightTorus_F4 (hv : (LieTypeIndex.F4 q).Valid) :
    weightTorus ⟨_, hv⟩ = geckWeightTorus ⟨_, hv⟩ :=
  (rfl)

/-- On type G₂ the represented torus is the Geck weight torus. -/
theorem weightTorus_G2 (hv : (LieTypeIndex.G2 q).Valid) :
    weightTorus ⟨_, hv⟩ = geckWeightTorus ⟨_, hv⟩ :=
  (rfl)

/-- On twisted type E₆ the represented torus is the doubled-minuscule weight torus. -/
theorem weightTorus_twistedE6 (hv : (LieTypeIndex.twistedE6 q).Valid) :
    weightTorus ⟨_, hv⟩ = TypeTwistedE6LieIndex.weightTorus ⟨⟨_, hv⟩, by simp⟩ :=
  (rfl)

/-- On triality-twisted D₄ the represented torus is the tripled-module weight torus. -/
theorem weightTorus_trialityD4 (hv : (LieTypeIndex.trialityD4 q).Valid) :
    weightTorus ⟨_, hv⟩ = TypeTrialityD4LieIndex.weightTorus ⟨⟨_, hv⟩, by simp⟩ :=
  (rfl)

/-- On the Suzuki family the symplectic torus is read in type-B₂ coordinates. -/
theorem weightTorus_suzuki (hv : (LieTypeIndex.suzuki m).Valid) :
    weightTorus ⟨_, hv⟩ = SpStd.b2WeightTorusPoints (SuzukiLieIndex.of m hv).1.Closure :=
  (rfl)

/-- On the Ree G₂ family the represented torus is the short-root model's weight torus. -/
theorem weightTorus_reeG2 (hv : (LieTypeIndex.reeG2 m).Valid) :
    weightTorus ⟨_, hv⟩ = (ReeG2LieIndex.of m hv).weightTorus :=
  (rfl)

/-- On the Ree F₄ family the represented torus is the short-root model's weight torus. -/
theorem weightTorus_reeF4 (hv : (LieTypeIndex.reeF4 m).Valid) :
    weightTorus ⟨_, hv⟩ = (ReeF4LieIndex.of m hv).weightTorus :=
  (rfl)

/-- On the Tits index the represented torus is the short-root F₄ model's weight torus. -/
theorem weightTorus_tits (hv : LieTypeIndex.tits.Valid) :
    weightTorus ⟨_, hv⟩ = TitsLieIndex.of.weightTorus :=
  (rfl)

end Branches

/-- On every represented ambient group, the Steinberg character pullback is the weight map
of the native datum Steinberg isogeny, using the same fundamental-weight coordinates. -/
theorem isCharacterMap_steinberg (d : ValidLieTypeIndex) :
    IsCharacterMap d.weightTorus d.steinberg d.datumSteinberg.weightMap := by
  -- Use the named torus and endomorphism branch equations, so the family comparisons need
  -- neither exposed definitions nor a second table of character maps.
  obtain ⟨_ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _, hv⟩ := d
  · rw [weightTorus_A, steinberg_A, GraphTwistedIndex.steinberg_A]
    exact TypeALieIndex.isCharacterMap_steinberg _
  · rw [weightTorus_twistedA, steinberg_twistedA, GraphTwistedIndex.steinberg_twistedA]
    exact TypeALieIndex.isCharacterMap_steinberg _
  · rw [weightTorus_B, steinberg_B, GraphTwistedIndex.steinberg_B]
    exact TypeBLieIndex.isCharacterMap_steinberg _
  · rw [weightTorus_C, steinberg_C, GraphTwistedIndex.steinberg_C]
    exact TypeCLieIndex.isCharacterMap_steinberg _
  · rw [weightTorus_D, steinberg_D, GraphTwistedIndex.steinberg_D]
    exact TypeDLieIndex.isCharacterMap_steinberg ⟨⟨_, hv⟩, by simp⟩
  · rw [weightTorus_twistedD, steinberg_twistedD, GraphTwistedIndex.steinberg_twistedD]
    exact TypeTwistedDLieIndex.isCharacterMap_steinberg ⟨⟨_, hv⟩, by simp⟩
  · rw [weightTorus_E6, steinberg_E6, GraphTwistedIndex.steinberg_E6]
    exact TypeE6LieIndex.isCharacterMap_steinberg _
  · rw [weightTorus_E7, steinberg_E7, GraphTwistedIndex.steinberg_E7]
    exact TypeE7LieIndex.isCharacterMap_steinberg _
  · rw [weightTorus_E8, steinberg_E8, GraphTwistedIndex.steinberg_E8]
    exact UnimodularExceptionalIndex.isCharacterMap_steinberg ⟨⟨⟨_, hv⟩, by simp⟩, by simp⟩
  · rw [weightTorus_F4, steinberg_F4, GraphTwistedIndex.steinberg_F4]
    exact UnimodularExceptionalIndex.isCharacterMap_steinberg ⟨⟨⟨_, hv⟩, by simp⟩, by simp⟩
  · rw [weightTorus_G2, steinberg_G2, GraphTwistedIndex.steinberg_G2]
    exact UnimodularExceptionalIndex.isCharacterMap_steinberg ⟨⟨⟨_, hv⟩, by simp⟩, by simp⟩
  · rw [weightTorus_twistedE6, steinberg_twistedE6, GraphTwistedIndex.steinberg_twistedE6]
    exact TypeTwistedE6LieIndex.isCharacterMap_steinberg _
  · rw [weightTorus_trialityD4, steinberg_trialityD4, GraphTwistedIndex.steinberg_trialityD4]
    exact TypeTrialityD4LieIndex.isCharacterMap_steinberg _
  · rw [weightTorus_suzuki, steinberg_suzuki,
      datumSteinberg_of_usesHalfFrobenius _ (by simp)]
    exact SuzukiLieIndex.isCharacterMap_steinberg_suzuki _ hv
  · rw [weightTorus_reeG2, steinberg_reeG2,
      datumSteinberg_of_usesHalfFrobenius _ (by simp)]
    exact ReeG2LieIndex.isCharacterMap_steinberg _
  · rw [weightTorus_reeF4, steinberg_reeF4,
      datumSteinberg_of_usesHalfFrobenius _ (by simp)]
    exact ReeF4LieIndex.isCharacterMap_steinberg _
  · rw [weightTorus_tits, steinberg_tits,
      datumSteinberg_of_usesHalfFrobenius _ (by simp)]
    exact TitsLieIndex.isCharacterMap_steinberg _

/-- The represented Steinberg map acts on torus parameters by the point map dual to the
native datum Steinberg weight map. -/
@[simp]
theorem steinberg_weightTorus (d : ValidLieTypeIndex) (s : Fin d.rank → d.Closureˣ) :
    d.steinberg (d.weightTorus s) =
      d.weightTorus (torusPointMap d.datumSteinberg.weightMap s) :=
  d.isCharacterMap_steinberg.map_apply s

end

end TauCeti.ValidLieTypeIndex
