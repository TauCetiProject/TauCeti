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
public import TauCeti.Data.ZMod.TrivialAction
public import TauCeti.Topology.Algebra.ContinuousZModDual
public import TauCeti.Topology.Algebra.GroupAction.TypeTags

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
`𝔽_p`-vector space. The extensions of a profinite group by `𝔽_p` are written multiplicatively, so
the degree-two identification is also read on the additive type tag of `Multiplicative (ZMod p)`
with a trivial action.

## Main definitions

* `TauCeti.cohomFpAddEquivH1`, `TauCeti.cohomFpAddEquivH2`: `cohomFp p G 1` and `cohomFp p G 2` are
  the explicit `H1 G (ZMod p)` and `H2 G (ZMod p)` for a trivial action.
* `TauCeti.cohomFpLinearEquivH2`: the degree-two identification is `𝔽_p`-linear; by
  `TauCeti.cohomFpAddEquivH2_cohomFpMap` it carries `cohomFpMap` to the explicit pullback.
* `TauCeti.cohomFpAddEquivH2Additive`: `cohomFp p G 2` is the explicit `H²(G, Additive 𝔽_p)` of
  the additive type tag of a multiplicatively written `𝔽_p` with trivial action.
* `TauCeti.cohomFpLinearEquivContinuousZModDual`: `H¹(G, 𝔽_p)` is the continuous `𝔽_p`-dual of
  `G`, as an `𝔽_p`-vector space; `TauCeti.cohomFpLinearEquivContinuousZModDual_π_apply` computes
  it on the class of a homogeneous one-cocycle.
* `TauCeti.cohomFpTwoLinearEquivOfContinuousMulEquiv`: a topological isomorphism `G ≃ₜ* H` induces
  `H²(G, 𝔽_p) ≃ₗ[𝔽_p] H²(H, 𝔽_p)`, with no action of either group in its statement; on the
  explicit models it is the pullback along `e.symm` for any trivial actions
  (`TauCeti.cohomFpTwoLinearEquivOfContinuousMulEquiv_apply`), so
  `TauCeti.finrank_cohomFp_two_congr`: the dimension of `H²(-, 𝔽_p)` is an isomorphism invariant.

## References

* J.-P. Serre, *Galois Cohomology*, I §2.
-/
public section

namespace TauCeti

open CategoryTheory TauCeti.ContCohomology _root_.ContinuousCohomology

universe u v

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
theorem trivialFpEquiv_smul (g : G) (x : (trivialFp p G).V) :
    trivialFpEquiv p G ((ContinuousMulEquiv.refl G) g • x) = g • trivialFpEquiv p G x := by
  rw [smul_trivialFp_V, htriv]

/-- **`H¹(G, 𝔽_p)` is the explicit `H1 G (ZMod p)`**, for any trivial action of `G` on `ZMod p`. -/
noncomputable def cohomFpAddEquivH1 : cohomFp p G 1 ≃+ H1 G (ZMod p) :=
  (trivialFp p G).explicitH1AddEquivContinuousCohomologyOfDiscrete.symm.trans
    (explicitMap1Equiv G (trivialFp p G).V G (ZMod p) (ContinuousMulEquiv.refl G)
      (trivialFpEquiv p G).toAddEquiv continuous_of_discreteTopology continuous_of_discreteTopology
      (trivialFpEquiv_smul p G htriv))

/-- On the comparison of the carrier of `trivialFp p G`, the identification `cohomFpAddEquivH1` is
the change of coefficients along the universe lift `trivialFpEquiv p G`. -/
theorem cohomFpAddEquivH1_explicitH1AddEquivContinuousCohomologyOfDiscrete
    (x : H1 G (trivialFp p G).V) :
    cohomFpAddEquivH1 p G htriv
        ((trivialFp p G).explicitH1AddEquivContinuousCohomologyOfDiscrete x) =
      explicitMap1Equiv G (trivialFp p G).V G (ZMod p) (ContinuousMulEquiv.refl G)
        (trivialFpEquiv p G).toAddEquiv continuous_of_discreteTopology
        continuous_of_discreteTopology (trivialFpEquiv_smul p G htriv) x := by
  rw [cohomFpAddEquivH1, AddEquiv.trans_apply, AddEquiv.symm_apply_apply]

/-- **`H²(G, 𝔽_p)` is the explicit `H2 G (ZMod p)`**, for any trivial action of `G` on `ZMod p`. -/
noncomputable def cohomFpAddEquivH2 [LocallyCompactSpace G] : cohomFp p G 2 ≃+ H2 G (ZMod p) :=
  (trivialFp p G).explicitH2AddEquivContinuousCohomologyOfDiscrete.symm.trans
    (explicitMap2Equiv G (trivialFp p G).V G (ZMod p) (ContinuousMulEquiv.refl G)
      (trivialFpEquiv p G).toAddEquiv continuous_of_discreteTopology continuous_of_discreteTopology
      (trivialFpEquiv_smul p G htriv))

/-- On the comparison of the carrier of `trivialFp p G`, the identification `cohomFpAddEquivH2` is
the change of coefficients along the universe lift `trivialFpEquiv p G`. -/
theorem cohomFpAddEquivH2_explicitH2AddEquivContinuousCohomologyOfDiscrete [LocallyCompactSpace G]
    (x : H2 G (trivialFp p G).V) :
    cohomFpAddEquivH2 p G htriv
        ((trivialFp p G).explicitH2AddEquivContinuousCohomologyOfDiscrete x) =
      explicitMap2Equiv G (trivialFp p G).V G (ZMod p) (ContinuousMulEquiv.refl G)
        (trivialFpEquiv p G).toAddEquiv continuous_of_discreteTopology
        continuous_of_discreteTopology (trivialFpEquiv_smul p G htriv) x := by
  rw [cohomFpAddEquivH2, AddEquiv.trans_apply, AddEquiv.symm_apply_apply]

/-- **The degree-two identification is natural.** Under `cohomFpAddEquivH2`, the cohomology map
`cohomFpMap p φ 2` along a continuous homomorphism `φ : H →ₜ* G` is the explicit pullback of
two-cocycles along `φ`, for any trivial actions of `G` and `H` on `ZMod p`. -/
theorem cohomFpAddEquivH2_cohomFpMap [LocallyCompactSpace G] {H : Type u} [Group H]
    [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H]
    [DistribMulAction H (ZMod p)] [ContinuousSMul H (ZMod p)]
    (htH : ∀ (h : H) (m : ZMod p), h • m = m) (φ : H →ₜ* G) (x : cohomFp p G 2) :
    cohomFpAddEquivH2 p H htH (cohomFpMap p φ 2 x) =
      explicitMap2 G (ZMod p) H (ZMod p) φ (AddMonoidHom.id (ZMod p)) continuous_id
        (fun h m ↦ (htriv (φ h) m).trans (htH h m).symm) (cohomFpAddEquivH2 p G htriv x) := by
  -- The coefficient transport of `cohomFpMap` is the identity of the universe lift `ZMod p`.
  let f : (trivialFp p G).V →+ (trivialFp p H).V :=
    ((trivialFpEquiv p H).symm.toLinearMap ∘ₗ (trivialFpEquiv p G).toLinearMap).toAddMonoidHom
  have hF (m : (TopRep.res (φ : H →* G) (trivialFp p G)).V) :
      (eqToHom (res_trivialFp_hom p φ)).hom m = f m :=
    (trivialFpEquiv p H).injective <| by
      simpa [f] using trivialFpEquiv_eqToHom_res_trivialFp_hom p φ m
  have hf (h : H) (m : (trivialFp p G).V) : f (φ h • m) = h • f m := by
    rw [smul_trivialFp_V, smul_trivialFp_V]
  obtain ⟨y, rfl⟩ := (trivialFp p G).explicitH2AddEquivContinuousCohomologyOfDiscrete.surjective x
  rw [cohomFpMap_def, TopRep.explicitH2AddEquivContinuousCohomologyOfDiscrete_map (trivialFp p G)
      (trivialFp p H) φ _ f hF hf,
    cohomFpAddEquivH2_explicitH2AddEquivContinuousCohomologyOfDiscrete,
    cohomFpAddEquivH2_explicitH2AddEquivContinuousCohomologyOfDiscrete]
  induction y using QuotientAddGroup.induction_on with
  | H c =>
    rw [explicitMap2Equiv_apply, explicitMap2Equiv_apply,
      explicitMap2_mk G (trivialFp p G).V H (trivialFp p H).V]
    -- `explicitMap2_mk` is applied as a term where `explicitMap2Equiv` states the continuity of
    -- the coefficient map at the equivalence, which `rw` does not identify with its coercion.
    refine (explicitMap2_mk H (trivialFp p H).V H (ZMod p) _ _ _ _ _).trans ?_
    refine Eq.trans ?_ (congrArg (explicitMap2 G (ZMod p) H (ZMod p) φ _ _ _)
      (explicitMap2_mk G (trivialFp p G).V G (ZMod p) _ _ _ _ c)).symm
    rw [explicitMap2_mk]
    -- Both cocycles read `c` at `(φ g, φ h)` through the universe lifts of `ZMod p`.
    refine congrArg _ (Subtype.ext (funext fun ⟨g, h⟩ ↦ ?_))
    simp [f, cocyclesMap2_apply]

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
  let _ := trivialZModAction p G
  have : ContinuousSMul G (ZMod p) := ⟨continuous_snd⟩
  let e : cohomFp p G 1 ≃+ continuousZModDual p G :=
    (cohomFpAddEquivH1 p G fun _ _ ↦ rfl).trans (H1EquivOfSmulEqSelf fun _ _ ↦ rfl)
  LinearEquiv.ofBijective (e.toAddMonoidHom.toZModLinearMap p) e.bijective

omit [DistribMulAction G (ZMod p)] [ContinuousSMul G (ZMod p)] htriv in
/-- **The defining equation of `cohomFpLinearEquivContinuousZModDual`**: for the trivial action
`trivialZModAction p G`, it is the identification `cohomFpAddEquivH1` of `H¹(G, 𝔽_p)` with the
explicit model followed by the identification `H1EquivOfSmulEqSelf` of the explicit classes with
the continuous characters. -/
-- Not a `simp` lemma: the canonical identification is the intended normal form of a character of
-- `H¹(G, 𝔽_p)`, and the `simp` lemmas `cohomFpLinearEquivContinuousZModDual_π_characterCocycle` and
-- `ContinuousMonoidHom.cohomFpLinearEquivContinuousZModDual_zmodFourReductionClass` own its
-- left-hand side; as a `simp` lemma this equation would rewrite theirs (simpNF).
theorem cohomFpLinearEquivContinuousZModDual_apply (x : cohomFp p G 1) :
    letI := trivialZModAction p G
    haveI : ContinuousSMul G (ZMod p) := ⟨continuous_snd⟩
    cohomFpLinearEquivContinuousZModDual p G x =
      H1EquivOfSmulEqSelf (fun _ _ ↦ rfl) (cohomFpAddEquivH1 p G (fun _ _ ↦ rfl) x) :=
  (rfl)

omit [DistribMulAction G (ZMod p)] [ContinuousSMul G (ZMod p)] htriv in
/-- The character attached by `cohomFpLinearEquivContinuousZModDual` to the class of a homogeneous
one-cocycle `z` reads `z` at `(1, g)`. -/
theorem cohomFpLinearEquivContinuousZModDual_π_apply (z : cocycles (trivialFp p G) 1) (g : G) :
    Multiplicative.toAdd
        (Additive.toMul (cohomFpLinearEquivContinuousZModDual p G (π (trivialFp p G) 1 z)) g) =
      trivialFpEquiv p G (((TopRep.homogeneousCochains (trivialFp p G)).iCycles 1 z).val 1 g) := by
  -- The trivial action installed by the construction.
  let _ := trivialZModAction p G
  have htriv : ∀ (g : G) (m : ZMod p), g • m = m := fun _ _ ↦ rfl
  have : ContinuousSMul G (ZMod p) := ⟨continuous_snd⟩
  have h1 : cohomFpLinearEquivContinuousZModDual p G (π (trivialFp p G) 1 z) =
      H1EquivOfSmulEqSelf htriv (cohomFpAddEquivH1 p G htriv (π (trivialFp p G) 1 z)) := rfl
  -- The cocycle of the carrier corresponding to `z`: it has the same values, and its class maps
  -- to the class of `z`.
  set w := (ofDiscreteModuleCocyclesRestrictScalarsIntIso (trivialFp p G) 1).inv z
  have hz : (ofDiscreteModuleCocyclesRestrictScalarsIntIso (trivialFp p G) 1).hom w = z :=
    Iso.inv_hom_id_apply _ _
  have hval : ((TopRep.homogeneousCochains (trivialFp p G)).iCycles 1 z).val 1 g =
      ((TopRep.homogeneousCochains (ofDiscreteModule ℤ G (trivialFp p G).V)).iCycles 1 w).val 1
        g := by
    rw [← hz]
    exact iCycles_ofDiscreteModuleCocyclesRestrictScalarsIntIso_hom_apply (trivialFp p G) w 1 g
  have hπ : ofDiscreteModuleRestrictScalarsIntEquiv (trivialFp p G) 1
      (π (ofDiscreteModule ℤ G (trivialFp p G).V) 1 w) = π (trivialFp p G) 1 z := by
    rw [ofDiscreteModuleRestrictScalarsIntEquiv_π, hz]
  have h2 : (trivialFp p G).explicitH1AddEquivContinuousCohomologyOfDiscrete.symm
      (π (trivialFp p G) 1 z) =
      (((cocycleEquiv1 G (trivialFp p G).V).symm w : Z1 G _) : H1 G (trivialFp p G).V) := by
    rw [AddEquiv.symm_apply_eq, TopRep.explicitH1AddEquivContinuousCohomologyOfDiscrete_apply,
      explicitH1AddEquivContinuousCohomology_apply, AddEquiv.apply_symm_apply]
    exact hπ.symm
  rw [h1, cohomFpAddEquivH1, AddEquiv.trans_apply, h2, explicitMap1Equiv_apply]
  -- `explicitMap1_mk` and `cocyclesMap1_apply` are applied as terms: `explicitMap1Equiv` states
  -- the continuity of the coefficient map at the equivalence and the lemmas at its coercion to a
  -- homomorphism, which `rw` does not identify.
  refine (congrArg (fun q ↦ Multiplicative.toAdd (Additive.toMul (H1EquivOfSmulEqSelf htriv q) g))
    (explicitMap1_mk _ _ _ _ _ _ _ _ ((cocycleEquiv1 G (trivialFp p G).V).symm w))).trans ?_
  rw [H1EquivOfSmulEqSelf_mk, Z1EquivOfSmulEqSelf_apply, toAdd_ofAdd]
  refine (cocyclesMap1_apply _ _ _ _ _ _ _ _ _ g).trans ?_
  rw [cocycleEquiv1_symm_apply, hval]
  rfl

end TrivialFp

section AdditiveTypeTag

variable (p : ℕ) (G : Type u) [Group G] [MulDistribMulAction G (Multiplicative (ZMod p))]
  (htriv : ∀ (g : G) (m : Multiplicative (ZMod p)), g • m = m)
include htriv

/-- The identification `Additive (Multiplicative (ZMod p)) ≃+ ZMod p` carries a trivial action of
`G` on the source to the trivial action `TauCeti.trivialZModAction` on the target. -/
theorem additiveMultiplicative_smul (g : G) (m : Additive (Multiplicative (ZMod p))) :
    letI := trivialZModAction p G
    AddEquiv.additiveMultiplicative (ZMod p) (g • m) =
      g • AddEquiv.additiveMultiplicative (ZMod p) m := by
  simp only [AddEquiv.additiveMultiplicative_apply, Additive.toMul_smul, htriv]
  -- The action on the right is `TauCeti.trivialZModAction`, whose scalar multiplication is
  -- `g • x = x` by definition.
  rfl

variable [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [hcont : ContinuousSMul G (Multiplicative (ZMod p))]

/-- **`H²(G, 𝔽_p)` is the explicit `H²(G, Additive 𝔽_p)`** of the multiplicatively written
`𝔽_p` with a trivial action of `G`, read additively: the identification `TauCeti.cohomFpAddEquivH2`
with the explicit `H²(G, ZMod p)` for the trivial action, followed by the change of coefficients
along `Additive (Multiplicative (ZMod p)) ≃+ ZMod p`. -/
noncomputable def cohomFpAddEquivH2Additive :
    cohomFp p G 2 ≃+ H2 G (Additive (Multiplicative (ZMod p))) :=
  letI := trivialZModAction p G
  haveI : ContinuousSMul G (ZMod p) := ⟨continuous_snd⟩
  (cohomFpAddEquivH2 p G fun _ _ => rfl).trans
    (explicitMap2Equiv G (Additive (Multiplicative (ZMod p))) G (ZMod p)
      (ContinuousMulEquiv.refl G) (AddEquiv.additiveMultiplicative (ZMod p))
      continuous_of_discreteTopology continuous_of_discreteTopology
      (additiveMultiplicative_smul p G htriv)).symm

/-- The identification `TauCeti.cohomFpAddEquivH2Additive` is `TauCeti.cohomFpAddEquivH2` for the
trivial action `TauCeti.trivialZModAction`, followed by the change of coefficients along
`Additive (Multiplicative (ZMod p)) ≃+ ZMod p`. -/
theorem cohomFpAddEquivH2Additive_apply (x : cohomFp p G 2) :
    letI := trivialZModAction p G
    haveI : ContinuousSMul G (ZMod p) := ⟨continuous_snd⟩
    cohomFpAddEquivH2Additive p G htriv x =
      (explicitMap2Equiv G (Additive (Multiplicative (ZMod p))) G (ZMod p)
        (ContinuousMulEquiv.refl G) (AddEquiv.additiveMultiplicative (ZMod p))
        continuous_of_discreteTopology continuous_of_discreteTopology
        (additiveMultiplicative_smul p G htriv)).symm (cohomFpAddEquivH2 p G (fun _ _ => rfl) x) :=
  (rfl)

end AdditiveTypeTag

section Transport

variable (p : ℕ) {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] {H : Type v} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

/-- **`H²(-, 𝔽_p)` is invariant under topological isomorphism**: a topological isomorphism
`G ≃ₜ* H` induces an `𝔽_p`-linear isomorphism `H²(G, 𝔽_p) ≃ₗ[𝔽_p] H²(H, 𝔽_p)`. On the explicit
models `H2 G (ZMod p)` and `H2 H (ZMod p)`, for any trivial actions of `G` and `H` on `ZMod p`, it
is the pullback along `e.symm` (`TauCeti.cohomFpTwoLinearEquivOfContinuousMulEquiv_apply`). -/
noncomputable def cohomFpTwoLinearEquivOfContinuousMulEquiv (e : G ≃ₜ* H) :
    cohomFp p G 2 ≃ₗ[ZMod p] cohomFp p H 2 :=
  -- The explicit models need actions of `G` and `H` on `ZMod p`; the trivial ones are installed
  -- for the duration of the construction and do not appear in the statement.
  haveI : LocallyCompactSpace H := e.toHomeomorph.locallyCompactSpace_iff.1 inferInstance
  letI := trivialZModAction p G
  letI := trivialZModAction p H
  haveI : ContinuousSMul G (ZMod p) := ⟨continuous_snd⟩
  haveI : ContinuousSMul H (ZMod p) := ⟨continuous_snd⟩
  let f : H2 G (ZMod p) ≃+ H2 H (ZMod p) :=
    explicitMap2Equiv G (ZMod p) H (ZMod p) e.symm (AddEquiv.refl (ZMod p)) continuous_id
      continuous_id fun _ _ ↦ rfl
  (cohomFpLinearEquivH2 p G fun _ _ ↦ rfl).trans
    ((LinearEquiv.ofBijective (f.toAddMonoidHom.toZModLinearMap p) f.bijective).trans
      (cohomFpLinearEquivH2 p H fun _ _ ↦ rfl).symm)

/-- On the explicit models, for any trivial actions of `G` and `H` on `ZMod p`, the transport of
`H²(-, 𝔽_p)` along `e : G ≃ₜ* H` is the pullback along `e.symm`. -/
@[simp]
theorem cohomFpTwoLinearEquivOfContinuousMulEquiv_apply [LocallyCompactSpace H]
    [DistribMulAction G (ZMod p)] [ContinuousSMul G (ZMod p)] [DistribMulAction H (ZMod p)]
    [ContinuousSMul H (ZMod p)] (e : G ≃ₜ* H) (htG : ∀ (g : G) (m : ZMod p), g • m = m)
    (htH : ∀ (h : H) (m : ZMod p), h • m = m) (x : cohomFp p G 2) :
    cohomFpTwoLinearEquivOfContinuousMulEquiv p e x =
      (cohomFpLinearEquivH2 p H htH).symm (explicitMap2 G (ZMod p) H (ZMod p) e.symm
        (AddMonoidHom.id (ZMod p)) continuous_id (fun h m ↦ (htG (e.symm h) m).trans (htH h m).symm)
        (cohomFpLinearEquivH2 p G htG x)) := by
  -- Both actions are the trivial one, so the explicit models are those of the construction.
  obtain rfl : ‹DistribMulAction G (ZMod p)› = trivialZModAction p G :=
    DistribMulAction.ext (funext fun g ↦ funext fun m ↦ htG g m)
  obtain rfl : ‹DistribMulAction H (ZMod p)› = trivialZModAction p H :=
    DistribMulAction.ext (funext fun h ↦ funext fun m ↦ htH h m)
  let := trivialZModAction p G
  let := trivialZModAction p H
  exact congrArg (cohomFpLinearEquivH2 p H htH).symm
    (explicitMap2Equiv_apply G (ZMod p) H (ZMod p) e.symm (AddEquiv.refl (ZMod p)) continuous_id
      continuous_id _ (cohomFpLinearEquivH2 p G htG x))

/-- **The dimension of `H²(-, 𝔽_p)` is invariant under topological isomorphism.** -/
theorem finrank_cohomFp_two_congr (e : G ≃ₜ* H) :
    Module.finrank (ZMod p) (cohomFp p G 2) = Module.finrank (ZMod p) (cohomFp p H 2) :=
  (cohomFpTwoLinearEquivOfContinuousMulEquiv p e).finrank_eq

end Transport

end TauCeti
