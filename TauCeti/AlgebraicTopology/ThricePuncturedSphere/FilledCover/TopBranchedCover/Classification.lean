/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.ThricePuncturedSphere.Classification
public import TauCeti.AlgebraicTopology.ThricePuncturedSphere.FilledCover.TopBranchedCover.Basic

/-!
# Classification of topological branched covers by permutation triples

Constructs `TauCeti.TopBranchedCover.IsoClass.equivConnectedIsoClass`, classifying degree-`n`
topological branched covers of the sphere with branch values in `{0, 1, ∞}` by connected
degree-`n` permutation triples, evaluates it on `.mk X` (`equivConnectedIsoClass_mk`), and deduces
`Unique (IsoClass.{0} 1)`, feeding the four-way equivalence and invariant comparisons.

## References

* E. Girondo and G. González-Diez, *Introduction to Compact Riemann Surfaces and Dessins
  d'Enfants*, LMSST 79, Cambridge University Press, 2012, §§1.2.7 and 4.2.
-/

public noncomputable section

namespace TauCeti.TopBranchedCover.IsoClass

open ThricePuncturedSphere

/-- **Topological branched covers are classified by connected permutation triples.** -/
def equivConnectedIsoClass (n : ℕ) : IsoClass.{0} n ≃ ConnectedIsoClass n :=
  (equivConnectedCoverClass n).trans ConnectedCoverClass.isoClassEquiv

/-- `equivConnectedIsoClass` classifies the unbranched cover `c.restrict` of `ℂ ∖ {0, 1}`. -/
theorem equivConnectedIsoClass_apply {n : ℕ} (c : IsoClass.{0} n) :
    equivConnectedIsoClass n c = c.restrict.isoClass := by
  rw [equivConnectedIsoClass, Equiv.trans_apply, equivConnectedCoverClass_apply,
    ConnectedCoverClass.isoClassEquiv_apply]

/-- On `.mk X`, `equivConnectedIsoClass` returns the connected class of its monodromy triple. -/
theorem equivConnectedIsoClass_mk {n : ℕ} (X : TopBranchedCover.{0} n)
    (ν : X.restrict ⁻¹' {basePt} ≃ Fin n) : equivConnectedIsoClass n (.mk X) =
      .mk ⟨X.isCoveringMap_restrict.monodromyTriple ν,
        X.isCoveringMap_restrict.isConnected_monodromyTriple ν⟩ := by
  obtain ⟨ν'⟩ := X.connectedCover.nonempty_equiv_fin
  rw [equivConnectedIsoClass_apply, restrict_mk, ConnectedCoverClass.isoClass_mk _ ν']
  exact ConnectedIsoClass.forget_injective <| by simpa using
    (X.connectedCover.cover.isCoveringMap_proj.isoClass_monodromyTriple_eq_of_homeomorph
      ν' X.isCoveringMap_restrict ν X.connectedCoverHomeomorph
      (funext X.restrict_connectedCoverHomeomorph)).symm

/-- Up to isomorphism there is a unique topological branched cover of degree one. -/
instance : Unique (IsoClass.{0} 1) := (equivConnectedIsoClass 1).unique

end TauCeti.TopBranchedCover.IsoClass
