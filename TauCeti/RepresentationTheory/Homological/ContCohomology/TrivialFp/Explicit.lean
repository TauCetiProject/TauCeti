/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.CohomologyComparison
public import TauCeti.RepresentationTheory.Homological.ContCohomology.ExplicitFunctoriality
public import TauCeti.RepresentationTheory.Homological.ContCohomology.H2ZMod
public import TauCeti.RepresentationTheory.Homological.ContCohomology.TrivialFp
public import TauCeti.Topology.Algebra.ContinuousZModDual

/-!
# The explicit models of `H¹(G, 𝔽_p)` and `H²(G, 𝔽_p)`

The cohomology `cohomFp p G n` with trivial `ZMod p` coefficients is Mathlib's continuous cohomology
of an object of `TopRep (ZMod p) G`, while the explicit low-degree cohomology `H1 G M` and `H2 G M`
of `TauCeti.ContCohomology` is computed from inhomogeneous cochains with values in a discrete
`G`-module, and every rank count of a pro-`p` group is stated for the explicit model. This file
identifies the two in degrees one and two.

The comparison for a discrete smooth representation over any scalars is
`TopRep.explicitH1AddEquivContinuousCohomologyOfDiscrete` and its degree-two counterpart. For
`X = trivialFp p G` the carrier is the universe lift of `ZMod p`, and a further change of
coefficients along `trivialFpEquiv p G` lands in `H1 G (ZMod p)` and `H2 G (ZMod p)`, for any
trivial action of `G` on `ZMod p`. In degree one, the class group of a trivial action is the group
of continuous characters, so `H¹(G, 𝔽_p)` is the continuous `𝔽_p`-dual of `G`, as an
`𝔽_p`-vector space.

## Main definitions

* `TauCeti.cohomFpAddEquivH1`, `TauCeti.cohomFpAddEquivH2`: `cohomFp p G 1` and `cohomFp p G 2` are
  the explicit `H1 G (ZMod p)` and `H2 G (ZMod p)` for a trivial action.
* `TauCeti.cohomFpLinearEquivH2`: the degree-two identification is `𝔽_p`-linear.
* `TauCeti.cohomFpLinearEquivContinuousZModDual`: `H¹(G, 𝔽_p)` is the continuous `𝔽_p`-dual of
  `G`, as an `𝔽_p`-vector space.

## References

* J.-P. Serre, *Galois Cohomology*, I §2.
-/
public section

namespace TauCeti

open CategoryTheory TauCeti.ContCohomology _root_.ContinuousCohomology

universe u

attribute [local instance] TopRep.distribMulAction

-- Preferring the ring path keeps a single additive structure on `ZMod p`.
attribute [local instance 2000] Ring.toAddCommGroup

section TrivialFp

variable (p : ℕ) (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

attribute [local instance] continuousSMul_trivialFp

variable [DistribMulAction G (ZMod p)] [ContinuousSMul G (ZMod p)]
  (htriv : ∀ (g : G) (m : ZMod p), g • m = m)
include htriv

omit [IsTopologicalGroup G] [ContinuousSMul G (ZMod p)] in
/-- The universe lift `trivialFpEquiv p G` is compatible with the trivial actions on both sides. -/
private theorem trivialFpEquiv_smul (g : G) (x : (trivialFp p G).V) :
    trivialFpEquiv p G ((ContinuousMulEquiv.refl G) g • x) = g • trivialFpEquiv p G x := by
  rw [TopRep.distribMulAction_smul, trivialFp_ρ_apply_apply, htriv]

/-- **`H¹(G, 𝔽_p)` is the explicit `H1 G (ZMod p)`**, for any trivial action of `G` on `ZMod p`. -/
noncomputable def cohomFpAddEquivH1 : cohomFp p G 1 ≃+ H1 G (ZMod p) :=
  (trivialFp p G).explicitH1AddEquivContinuousCohomologyOfDiscrete.symm.trans
    (explicitMap1Equiv G (trivialFp p G).V G (ZMod p) (ContinuousMulEquiv.refl G)
      (trivialFpEquiv p G).toAddEquiv continuous_of_discreteTopology continuous_of_discreteTopology
      (trivialFpEquiv_smul p G htriv))

/-- **`H²(G, 𝔽_p)` is the explicit `H2 G (ZMod p)`**, for any trivial action of `G` on `ZMod p`. -/
noncomputable def cohomFpAddEquivH2 [LocallyCompactSpace G] : cohomFp p G 2 ≃+ H2 G (ZMod p) :=
  (trivialFp p G).explicitH2AddEquivContinuousCohomologyOfDiscrete.symm.trans
    (explicitMap2Equiv G (trivialFp p G).V G (ZMod p) (ContinuousMulEquiv.refl G)
      (trivialFpEquiv p G).toAddEquiv continuous_of_discreteTopology continuous_of_discreteTopology
      (trivialFpEquiv_smul p G htriv))

/-- **`H²(G, 𝔽_p)` is the explicit `H2 G (ZMod p)` as an `𝔽_p`-vector space**, for any trivial
action of `G` on `ZMod p`. -/
noncomputable def cohomFpLinearEquivH2 [LocallyCompactSpace G] :
    cohomFp p G 2 ≃ₗ[ZMod p] H2 G (ZMod p) :=
  LinearEquiv.ofBijective ((cohomFpAddEquivH2 p G htriv).toAddMonoidHom.toZModLinearMap p)
    (cohomFpAddEquivH2 p G htriv).bijective

/-- The linear identification of `H²(G, 𝔽_p)` with its explicit model is the additive one. -/
@[simp]
theorem cohomFpLinearEquivH2_apply [LocallyCompactSpace G] (x : cohomFp p G 2) :
    cohomFpLinearEquivH2 p G htriv x = cohomFpAddEquivH2 p G htriv x :=
  (rfl)

omit htriv in
/-- **`H¹(G, 𝔽_p)` is the continuous `𝔽_p`-dual of `G`**, as an `𝔽_p`-vector space: the classes of
continuous `1`-cocycles for the trivial action are the continuous characters `G → 𝔽_p`. -/
noncomputable def cohomFpLinearEquivContinuousZModDual :
    cohomFp p G 1 ≃ₗ[ZMod p] continuousZModDual p G :=
  -- The explicit model `H1 G (ZMod p)` needs an action of `G` on `ZMod p`; the trivial one is
  -- installed for the duration of the construction and does not appear in the statement.
  let _ : DistribMulAction G (ZMod p) := DistribMulAction.compHom (ZMod p) (1 : G →* (ZMod p)ˣ)
  have htriv : ∀ (g : G) (m : ZMod p), g • m = m := fun _ m ↦ one_smul (ZMod p)ˣ m
  have : ContinuousSMul G (ZMod p) := ⟨continuous_snd.congr fun x ↦ (htriv x.1 x.2).symm⟩
  let e : cohomFp p G 1 ≃+ continuousZModDual p G :=
    (cohomFpAddEquivH1 p G htriv).trans (H1EquivOfSmulEqSelf htriv)
  LinearEquiv.ofBijective (e.toAddMonoidHom.toZModLinearMap p) e.bijective

end TrivialFp

end TauCeti
