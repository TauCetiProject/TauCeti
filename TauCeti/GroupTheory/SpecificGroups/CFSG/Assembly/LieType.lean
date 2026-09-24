/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.AmbientGroup
public import TauCeti.GroupTheory.SpecificGroups.CFSG.ReeG2.Basic
public import TauCeti.GroupTheory.SpecificGroups.CFSG.ReeF4.Basic
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Suzuki.Basic
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Tits.Basic

/-!
# The concrete carrier and Steinberg map of every valid Lie-type index

The thirteen ordinary and graph-twisted families use their existing assembly. The four
half-Frobenius families use their explicit Suzuki, Ree, or Tits endomorphism. Every branch
retains the validity proof of the input index; no carrier is assigned to an invalid index.

The candidate group is uniformly the derived subgroup of the fixed points modulo its centre.
Comparison with the pinned simply connected groups requires isomorphisms preserving the
root subgroups and Steinberg maps. No finiteness or simplicity of a candidate is asserted.
The construction follows the family modules it imports.
-/

public section

namespace TauCeti.ValidLieTypeIndex

noncomputable section

/-- The actual Steinberg endomorphism on the carrier of each valid Lie-type index. -/
def steinberg : (d : ValidLieTypeIndex) → d.AmbientGroup →* d.AmbientGroup
  | ⟨.suzuki _, hv⟩ => SuzukiLieIndex.steinberg ⟨⟨_, hv⟩, by simp⟩
  | ⟨.reeG2 _, hv⟩ => ReeG2LieIndex.steinberg ⟨⟨_, hv⟩, by simp⟩
  | ⟨.reeF4 _, hv⟩ => ReeF4LieIndex.steinberg ⟨⟨_, hv⟩, by simp⟩
  | ⟨.tits, hv⟩ => TitsLieIndex.steinberg ⟨⟨_, hv⟩, by simp⟩
  | ⟨.A _ _, hv⟩ | ⟨.twistedA _ _, hv⟩ | ⟨.B _ _, hv⟩
  | ⟨.C _ _, hv⟩ | ⟨.D _ _, hv⟩ | ⟨.twistedD _ _, hv⟩
  | ⟨.E6 _, hv⟩ | ⟨.E7 _, hv⟩ | ⟨.E8 _, hv⟩
  | ⟨.F4 _, hv⟩ | ⟨.G2 _, hv⟩ | ⟨.twistedE6 _, hv⟩
  | ⟨.trialityD4 _, hv⟩ =>
      GraphTwistedIndex.steinberg ⟨⟨_, hv⟩, by simp⟩

/-! The branch equations expose the actual family maps without unfolding the dispatcher. -/

section Branches

variable {n m : ℕ} {q : PrimePower}

/-- The `A` branch uses its family's Steinberg endomorphism. -/
theorem steinberg_A (hv : (LieTypeIndex.A n q).Valid) :
    steinberg ⟨.A n q, hv⟩ =
      GraphTwistedIndex.steinberg ⟨⟨_, hv⟩, by simp [LieTypeIndex.usesHalfFrobenius_iff]⟩ := by rfl

/-- The `twistedA` branch uses its family's Steinberg endomorphism. -/
theorem steinberg_twistedA (hv : (LieTypeIndex.twistedA n q).Valid) :
    steinberg ⟨.twistedA n q, hv⟩ =
      GraphTwistedIndex.steinberg ⟨⟨_, hv⟩, by simp [LieTypeIndex.usesHalfFrobenius_iff]⟩ := by rfl

/-- The `B` branch uses its family's Steinberg endomorphism. -/
theorem steinberg_B (hv : (LieTypeIndex.B n q).Valid) :
    steinberg ⟨.B n q, hv⟩ =
      GraphTwistedIndex.steinberg ⟨⟨_, hv⟩, by simp [LieTypeIndex.usesHalfFrobenius_iff]⟩ := by rfl

/-- The `C` branch uses its family's Steinberg endomorphism. -/
theorem steinberg_C (hv : (LieTypeIndex.C n q).Valid) :
    steinberg ⟨.C n q, hv⟩ =
      GraphTwistedIndex.steinberg ⟨⟨_, hv⟩, by simp [LieTypeIndex.usesHalfFrobenius_iff]⟩ := by rfl

/-- The `D` branch uses its family's Steinberg endomorphism. -/
theorem steinberg_D (hv : (LieTypeIndex.D n q).Valid) :
    steinberg ⟨.D n q, hv⟩ =
      GraphTwistedIndex.steinberg ⟨⟨_, hv⟩, by simp [LieTypeIndex.usesHalfFrobenius_iff]⟩ := by rfl

/-- The `twistedD` branch uses its family's Steinberg endomorphism. -/
theorem steinberg_twistedD (hv : (LieTypeIndex.twistedD n q).Valid) :
    steinberg ⟨.twistedD n q, hv⟩ =
      GraphTwistedIndex.steinberg ⟨⟨_, hv⟩, by simp [LieTypeIndex.usesHalfFrobenius_iff]⟩ := by rfl

/-- The `E6` branch uses its family's Steinberg endomorphism. -/
theorem steinberg_E6 (hv : (LieTypeIndex.E6 q).Valid) :
    steinberg ⟨.E6 q, hv⟩ =
      GraphTwistedIndex.steinberg ⟨⟨_, hv⟩, by simp [LieTypeIndex.usesHalfFrobenius_iff]⟩ := by rfl

/-- The `E7` branch uses its family's Steinberg endomorphism. -/
theorem steinberg_E7 (hv : (LieTypeIndex.E7 q).Valid) :
    steinberg ⟨.E7 q, hv⟩ =
      GraphTwistedIndex.steinberg ⟨⟨_, hv⟩, by simp [LieTypeIndex.usesHalfFrobenius_iff]⟩ := by rfl

/-- The `E8` branch uses its family's Steinberg endomorphism. -/
theorem steinberg_E8 (hv : (LieTypeIndex.E8 q).Valid) :
    steinberg ⟨.E8 q, hv⟩ =
      GraphTwistedIndex.steinberg ⟨⟨_, hv⟩, by simp [LieTypeIndex.usesHalfFrobenius_iff]⟩ := by rfl

/-- The `F4` branch uses its family's Steinberg endomorphism. -/
theorem steinberg_F4 (hv : (LieTypeIndex.F4 q).Valid) :
    steinberg ⟨.F4 q, hv⟩ =
      GraphTwistedIndex.steinberg ⟨⟨_, hv⟩, by simp [LieTypeIndex.usesHalfFrobenius_iff]⟩ := by rfl

/-- The `G2` branch uses its family's Steinberg endomorphism. -/
theorem steinberg_G2 (hv : (LieTypeIndex.G2 q).Valid) :
    steinberg ⟨.G2 q, hv⟩ =
      GraphTwistedIndex.steinberg ⟨⟨_, hv⟩, by simp [LieTypeIndex.usesHalfFrobenius_iff]⟩ := by rfl

/-- The `twistedE6` branch uses its family's Steinberg endomorphism. -/
theorem steinberg_twistedE6 (hv : (LieTypeIndex.twistedE6 q).Valid) :
    steinberg ⟨.twistedE6 q, hv⟩ =
      GraphTwistedIndex.steinberg ⟨⟨_, hv⟩, by simp [LieTypeIndex.usesHalfFrobenius_iff]⟩ := by rfl

/-- The `trialityD4` branch uses its family's Steinberg endomorphism. -/
theorem steinberg_trialityD4 (hv : (LieTypeIndex.trialityD4 q).Valid) :
    steinberg ⟨.trialityD4 q, hv⟩ =
      GraphTwistedIndex.steinberg ⟨⟨_, hv⟩, by simp [LieTypeIndex.usesHalfFrobenius_iff]⟩ := by rfl

/-- The `suzuki` branch uses its family's Steinberg endomorphism. -/
theorem steinberg_suzuki (hv : (LieTypeIndex.suzuki m).Valid) :
    steinberg ⟨.suzuki m, hv⟩ =
      SuzukiLieIndex.steinberg ⟨⟨_, hv⟩, by simp⟩ := by rfl

/-- The `reeG2` branch uses its family's Steinberg endomorphism. -/
theorem steinberg_reeG2 (hv : (LieTypeIndex.reeG2 m).Valid) :
    steinberg ⟨.reeG2 m, hv⟩ =
      ReeG2LieIndex.steinberg ⟨⟨_, hv⟩, by simp⟩ := by rfl

/-- The `reeF4` branch uses its family's Steinberg endomorphism. -/
theorem steinberg_reeF4 (hv : (LieTypeIndex.reeF4 m).Valid) :
    steinberg ⟨.reeF4 m, hv⟩ =
      ReeF4LieIndex.steinberg ⟨⟨_, hv⟩, by simp⟩ := by rfl

/-- The `tits` branch uses its family's Steinberg endomorphism. -/
theorem steinberg_tits (hv : (LieTypeIndex.tits).Valid) :
    steinberg ⟨.tits, hv⟩ =
      TitsLieIndex.steinberg ⟨⟨_, hv⟩, by simp⟩ := by rfl

end Branches

/-- On ordinary and graph-twisted indices the assembled map has the recorded diagram action
and field-order exponent. -/
theorem steinberg_simpleRootSubgroup_of_not_usesHalfFrobenius
    (d : ValidLieTypeIndex) (h : ¬ d.1.UsesHalfFrobenius) (i : Fin d.rank)
    (u : Multiplicative d.Closure) :
    d.steinberg (d.simpleRootSubgroup i u) =
      d.simpleRootSubgroup ((GraphTwistedIndex.diagramPerm ⟨d, h⟩) i)
        (Multiplicative.ofAdd (Multiplicative.toAdd u ^ d.fieldOrder)) := by
  obtain ⟨d, hv⟩ := d
  cases d
  all_goals simp only [simpleRootSubgroup_A, simpleRootSubgroup_twistedA,
    simpleRootSubgroup_B, simpleRootSubgroup_C, simpleRootSubgroup_D,
    simpleRootSubgroup_twistedD, simpleRootSubgroup_E6, simpleRootSubgroup_E7,
    simpleRootSubgroup_E8, simpleRootSubgroup_F4, simpleRootSubgroup_G2,
    simpleRootSubgroup_twistedE6, simpleRootSubgroup_trialityD4]
  all_goals first
  | exact GraphTwistedIndex.steinberg_simpleRootSubgroup ⟨⟨_, hv⟩, h⟩ i u
  | exact absurd (by simp [LieTypeIndex.usesHalfFrobenius_iff]) h

/-- On the Suzuki, Ree and Tits indices the assembled map exchanges root lengths and raises
the parameter to the odd half-Frobenius exponent. -/
theorem steinberg_simpleRootSubgroup_of_usesHalfFrobenius
    (d : ValidLieTypeIndex) (h : d.1.UsesHalfFrobenius) (i : Fin d.rank)
    (u : Multiplicative d.Closure) :
    d.steinberg (d.simpleRootSubgroup i u) =
      d.simpleRootSubgroup ((SuzukiReeIndex.lengthPerm ⟨d, h⟩) i)
        (Multiplicative.ofAdd (Multiplicative.toAdd u ^
          (d.characteristic ^ SuzukiReeIndex.halfExponent ⟨d, h⟩ *
            SuzukiReeIndex.exponent ⟨d, h⟩ i))) := by
  obtain ⟨d, hv⟩ := d
  cases d
  all_goals try { simp [LieTypeIndex.usesHalfFrobenius_iff] at h }
  all_goals simp only [simpleRootSubgroup_suzuki, simpleRootSubgroup_reeG2,
    simpleRootSubgroup_reeF4, simpleRootSubgroup_tits]
  · exact SuzukiLieIndex.steinberg_simpleRootSubgroup ⟨⟨_, hv⟩, by simp⟩ i u
  · exact ReeG2LieIndex.steinberg_simpleRootSubgroup ⟨⟨_, hv⟩, by simp⟩ i u
  · exact ReeF4LieIndex.steinberg_simpleRootSubgroup ⟨⟨_, hv⟩, by simp⟩ i u
  · rw [SuzukiReeIndex.halfExponent_tits, pow_zero, one_mul]
    exact TitsLieIndex.steinberg_simpleRootSubgroup ⟨⟨_, hv⟩, by simp⟩ i u

/-- On a half-Frobenius family, the assembled Steinberg map squares to the indexed
field-order Frobenius. -/
theorem steinberg_steinberg_of_usesHalfFrobenius (d : ValidLieTypeIndex)
    (h : d.1.UsesHalfFrobenius) (g : d.AmbientGroup) :
    d.steinberg (d.steinberg g) = d.frobenius g := by
  obtain ⟨d, hv⟩ := d
  cases d
  all_goals try { simp [LieTypeIndex.usesHalfFrobenius_iff] at h }
  all_goals simp only [frobenius_suzuki, frobenius_reeG2, frobenius_reeF4, frobenius_tits]
  · exact SuzukiLieIndex.steinberg_steinberg ⟨⟨_, hv⟩, by simp⟩ g
  · exact ReeG2LieIndex.steinberg_steinberg ⟨⟨_, hv⟩, by simp⟩ g
  · exact ReeF4LieIndex.steinberg_steinberg ⟨⟨_, hv⟩, by simp⟩ g
  · exact TitsLieIndex.steinberg_steinberg ⟨⟨_, hv⟩, by simp⟩ g

/-- The fixed subgroup of the family's Steinberg endomorphism. -/
abbrev FixedPoints (d : ValidLieTypeIndex) : Type := ↥(fixedSubgroup d.steinberg)

/-- The Lie-type candidate is the derived subgroup of the fixed points modulo its own centre.
No finiteness or simplicity instance is assumed or supplied. -/
abbrev Group (d : ValidLieTypeIndex) : Type := FixedPointCandidate d.steinberg

/-- On the thirteen ordinary or graph-twisted families, the assembled candidate is the
existing graph-twisted assembly's candidate. -/
theorem Group_eq_of_not_usesHalfFrobenius (d : ValidLieTypeIndex)
    (h : ¬ d.1.UsesHalfFrobenius) : d.Group = GraphTwistedIndex.Group ⟨d, h⟩ := by
  obtain ⟨d, hv⟩ := d
  cases d
  all_goals first
  | rfl
  | exact absurd (by simp [LieTypeIndex.usesHalfFrobenius_iff]) h

/-- The `suzuki` branch is the fixed-point candidate of its family. -/
theorem Group_suzuki (m : ℕ) (hv : (LieTypeIndex.suzuki m).Valid) :
    Group ⟨.suzuki m, hv⟩ = SuzukiLieIndex.Group ⟨⟨_, hv⟩, by simp⟩ := by
  rfl

/-- The `reeG2` branch is the fixed-point candidate of its family. -/
theorem Group_reeG2 (m : ℕ) (hv : (LieTypeIndex.reeG2 m).Valid) :
    Group ⟨.reeG2 m, hv⟩ = ReeG2LieIndex.Group ⟨⟨_, hv⟩, by simp⟩ := by
  rfl

/-- The `reeF4` branch is the fixed-point candidate of its family. -/
theorem Group_reeF4 (m : ℕ) (hv : (LieTypeIndex.reeF4 m).Valid) :
    Group ⟨.reeF4 m, hv⟩ = ReeF4LieIndex.Group ⟨⟨_, hv⟩, by simp⟩ := by
  rfl

/-- The separate Tits branch uses the first exceptional F4 iterate. -/
theorem Group_tits (hv : LieTypeIndex.tits.Valid) :
    Group ⟨.tits, hv⟩ = TitsLieIndex.Group ⟨⟨_, hv⟩, by simp⟩ := by
  rfl

example (d : ValidLieTypeIndex) : _root_.Group d.Group := inferInstance

end

end TauCeti.ValidLieTypeIndex
