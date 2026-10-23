/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Group.Profinite.Demushkin.Basic

/-!
# Demushkin groups under topological isomorphism

The cohomological definition of a Demushkin group is intrinsic to its topological group.
Continuous group isomorphisms transport its finite-dimensionality and cup-pairing conditions.
The maps on cohomology use the identity on trivial `ZMod p` coefficients.

## Main results

* `TauCeti.IsDemushkin.of_equiv`: transport the Demushkin property along a topological
  group isomorphism.
* `TauCeti.isDemushkin_congr`: the Demushkin property is invariant under a topological
  group isomorphism.
-/

public section

namespace TauCeti

universe u

variable (p : ℕ) {G H : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

variable [Fact p.Prime]

/-- The Demushkin property is invariant under topological group isomorphism. -/
theorem IsDemushkin.of_equiv (hG : IsDemushkin p G) (e : G ≃ₜ* H) :
    IsDemushkin p H := by
  let e₁ := cohomFpLinearEquiv p e 1
  let e₂ := cohomFpLinearEquiv p e 2
  have hcup (a b : cohomFp p G 1) :
      cupFp p H (e₁ a) (e₁ b) = e₂ (cupFp p G a b) := by
    simpa only [e₁, e₂, cohomFpLinearEquiv_apply] using
      (cupFp_map p G (ContinuousMonoidHom.toContinuousMonoidHom e.symm) a b).symm
  have hfin : Module.Finite (ZMod p) (cohomFp p H 1) := by
    exact @Module.Finite.equiv (ZMod p) (cohomFp p G 1) (cohomFp p H 1)
      _ _ _ _ _ hG.finite_cohomFp_one e₁
  refine ⟨hG.isProP.of_equiv e, hfin, ?_, ?_, ?_⟩
  · rw [← e₂.finrank_eq]
    exact hG.finrank_cohomFp_two
  · intro a ha
    let a₀ := e₁.symm a
    have ha₀ : a₀ ≠ 0 := by
      intro h
      apply ha
      have := congrArg e₁ h
      simpa [a₀] using this
    obtain ⟨b₀, hb₀⟩ := hG.cup_separatingLeft a₀ ha₀
    refine ⟨e₁ b₀, ?_⟩
    rw [← e₁.apply_symm_apply a, hcup]
    exact e₂.map_ne_zero_iff.mpr hb₀
  · intro b hb
    let b₀ := e₁.symm b
    have hb₀ : b₀ ≠ 0 := by
      intro h
      apply hb
      have := congrArg e₁ h
      simpa [b₀] using this
    obtain ⟨a₀, ha₀⟩ := hG.cup_separatingRight b₀ hb₀
    refine ⟨e₁ a₀, ?_⟩
    rw [← e₁.apply_symm_apply b, hcup]
    exact e₂.map_ne_zero_iff.mpr ha₀

/-- A topological group isomorphism preserves the Demushkin property in both directions. -/
theorem isDemushkin_congr (e : G ≃ₜ* H) : IsDemushkin p G ↔ IsDemushkin p H :=
  ⟨fun h => IsDemushkin.of_equiv p h e, fun h => IsDemushkin.of_equiv p h e.symm⟩

end TauCeti
