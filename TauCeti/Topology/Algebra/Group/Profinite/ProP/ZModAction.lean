/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Topology.Algebra.MulAction
public import TauCeti.GroupTheory.PGroup
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.Basic

/-!
# A pro-`p` group acts trivially on `𝔽_p`

A continuous action of a pro-`p` group on `ZMod p` by additive automorphisms is trivial: the
kernel of the action `G → Aut(𝔽_p, +)` is open, so its image is a `p`-group inside a group of order
`p - 1`.

## Main statements

* `TauCeti.IsProP.smul_zmod_eq_self`: a pro-`p` group acting continuously on `ZMod p` acts
  trivially.
-/

public section

namespace TauCeti

variable {p : ℕ} [Fact p.Prime] {G : Type*} [Group G] [TopologicalSpace G]

omit [TopologicalSpace G] in
/-- A distributive action on `ZMod p` is multiplication by the image of `1`. -/
private theorem smul_zmod_eq_mul_smul_one [DistribMulAction G (ZMod p)] (g : G) (m : ZMod p) :
    g • m = m * (g • 1) := by
  simpa using map_nsmul (DistribSMul.toAddMonoidHom (ZMod p) g) m.val 1

/-- **A pro-`p` group acts trivially on `𝔽_p`.** A continuous action of a pro-`p` group `G` on
`ZMod p` by additive automorphisms is trivial, because the image of `G` in `Aut(𝔽_p, +) = 𝔽_pˣ`,
a group of order `p - 1`, is a `p`-group. -/
theorem IsProP.smul_zmod_eq_self (hG : IsProP p G) [DistribMulAction G (ZMod p)]
    [ContinuousSMul G (ZMod p)] (g : G) (m : ZMod p) : g • m = m := by
  let χ : G →* (ZMod p)ˣ := MonoidHom.mk'
    (fun g ↦ Units.mkOfMulEqOne (g • 1) (g⁻¹ • 1) (by
      rw [mul_comm, ← smul_zmod_eq_mul_smul_one, smul_inv_smul]))
    fun g h ↦ Units.ext (by
      change (g * h) • (1 : ZMod p) = (g • 1) * (h • 1)
      rw [mul_smul, smul_zmod_eq_mul_smul_one g (h • 1), mul_comm])
  have hker : IsOpen (χ.ker : Set G) := by
    have : (χ.ker : Set G) = (fun g : G ↦ g • (1 : ZMod p)) ⁻¹' {1} := by
      ext g
      simp [χ, Units.ext_iff]
    rw [this]
    exact (isOpen_discrete _).preimage (continuous_id.smul continuous_const)
  have h1 := (hG.isPGroup_range χ hker).smul_zmod_eq_self (⟨χ g, g, rfl⟩ : χ.range) 1
  have h2 : χ g = 1 := by simpa [Subgroup.smul_def, Units.smul_def] using h1
  rw [smul_zmod_eq_mul_smul_one, show g • (1 : ZMod p) = 1 from congrArg Units.val h2, mul_one]

end TauCeti
