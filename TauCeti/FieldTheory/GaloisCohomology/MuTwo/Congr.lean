/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.GaloisCohomology.Congr
public import TauCeti.FieldTheory.GaloisCohomology.MuTwo.BrauerTorsion
public import TauCeti.RepresentationTheory.Homological.ContCohomology.TrivialF2.MapDegreeTwo

/-!
# Mod-two Galois cohomology of isomorphic fields

A field isomorphism `e : K ≃+* L` identifies the absolute Galois groups,
`RingEquiv.absoluteGaloisGroupCongr e : G_L ≃ₜ* G_K`, with the fields in independent universes.
Along it, `TauCeti.trivialF2Map2Equiv` transports `H²(G_K, 𝔽₂)` to `H²(G_L, 𝔽₂)`, and
`RingEquiv.unitsContinuousH2Congr e` transports `H²(G_K, (Kˢ)ˣ)` to `H²(G_L, (Lˢ)ˣ)`. This file
proves that the map `TauCeti.h2MuToUnits` induced by `μ₂ ⊆ (Kˢ)ˣ` intertwines the two:

```text
H²(G_K, 𝔽₂)  ── h2MuToUnits K ──→  H²(G_K, (Kˢ)ˣ)
    │                                     │
    │ trivialF2Map2Equiv                  │ unitsContinuousH2Congr e
    ↓                                     ↓
H²(G_L, 𝔽₂)  ── h2MuToUnits L ──→  H²(G_L, (Lˢ)ˣ)
```

Both composites are compatible-pair maps along `G_L ≃ G_K`
(`TauCeti.ContCohomology.continuousCohomologyMap2_comp`), and their coefficient maps agree because
the identification of separable closures sends `-1` to `-1`: both send the nontrivial element of
`𝔽₂` to `-1`.

## Main results

* `RingEquiv.h2MuToUnits_trivialF2Map2Equiv`: the square above commutes.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., (6.2.1) and
  Ch. I, §5.
-/

public noncomputable section

open CategoryTheory TauCeti TauCeti.ContCohomology

namespace RingEquiv

universe u v

attribute [local instance] TopRep.distribMulAction

/-- The trivial `𝔽₂` coefficients are a discrete module. -/
local instance continuousSMul_trivialF2_muTwoCongr (G : Type*) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] :
    ContinuousSMul G (trivialF2 G).V :=
  (isSmoothDiscrete_trivialF2 G).continuousSMul

/-- The absolute Galois group is locally compact, being compact and Hausdorff. Instance search
does not find this within its default budget, so it is assembled here from the Krull topology
being Hausdorff, as in `TauCeti.FieldTheory.GaloisCohomology.Congr`. -/
local instance locallyCompactSpace_absoluteGaloisGroup_muTwoCongr {F : Type*} [Field F] :
    LocallyCompactSpace (AbsoluteGaloisGroup F) :=
  have : R1Space (AbsoluteGaloisGroup F) := @T2Space.r1Space _ _ krullTopology_t2
  have : WeaklyLocallyCompactSpace (AbsoluteGaloisGroup F) :=
    ⟨fun _ ↦ ⟨Set.univ, isCompact_univ, Filter.univ_mem⟩⟩
  WeaklyLocallyCompactSpace.locallyCompactSpace

section Field

variable (K : Type u) [Field K] [Invertible (2 : K)]

/-- The coefficient map `𝔽₂ ≃ μ₂ ⊆ (Kˢ)ˣ` underlying `TauCeti.h2MuToUnits K`. -/
private def mu2ToUnits : (trivialF2 (AbsoluteGaloisGroup K)).V →+ UnitsCoeff K :=
  (kummerCoeffIncl K 2).comp (kummerCoeffEquiv K).symm.toAddMonoidHom

private theorem mu2ToUnits_apply (m : (trivialF2 (AbsoluteGaloisGroup K)).V) :
    mu2ToUnits K m = kummerCoeffIncl K 2 ((kummerCoeffEquiv K).symm m) :=
  (rfl)

private theorem mu2ToUnits_smul (g : AbsoluteGaloisGroup K)
    (m : (trivialF2 (AbsoluteGaloisGroup K)).V) :
    mu2ToUnits K (ContinuousMonoidHom.id _ g • m) = g • mu2ToUnits K m := by
  simp only [ContinuousMonoidHom.coe_id, id_eq, TopRep.distribMulAction_smul,
    trivialF2_ρ_apply_apply, mu2ToUnits_apply]
  rw [← kummerCoeffIncl_equivariant, mu2_smul_eq_self]

/-- The coefficient map sends `0` to `1` and the nontrivial element of `𝔽₂` to `-1`. -/
private theorem toMul_mu2ToUnits (m : (trivialF2 (AbsoluteGaloisGroup K)).V) :
    ((mu2ToUnits K m).toMul : SeparableClosure K) =
      if trivialF2Equiv (AbsoluteGaloisGroup K) m = 0 then 1 else -1 := by
  rw [mu2ToUnits_apply, kummerCoeffEquiv_symm_apply, toMul_kummerCoeffIncl]
  generalize trivialF2Equiv (AbsoluteGaloisGroup K) m = z
  rcases (by decide : ∀ z : ZMod 2, z = 0 ∨ z = 1) z with rfl | rfl
  · simp
  · rw [← mu2EquivZMod2_apply_mu2NegOne (K := K), AddEquiv.symm_apply_apply, toMul_mu2NegOne,
      mu2EquivZMod2_apply_mu2NegOne, ite_eq_right_of_eq_false _ _ (eq_false one_ne_zero),
      Units.val_neg, Units.val_one]

/-- On the discrete model of the trivial `𝔽₂` coefficients, `TauCeti.h2MuToUnits K` is the
compatible-pair map of the identity of `G_K` and the coefficient map `𝔽₂ ≃ μ₂ ⊆ (Kˢ)ˣ`. -/
private theorem h2MuToUnits_eqToHom
    (y : continuousCohomology 2
      (ofDiscreteModule ℤ (AbsoluteGaloisGroup K) (trivialF2 (AbsoluteGaloisGroup K)).V)) :
    (h2MuToUnits K).hom ((eqToHom (congrArg (continuousCohomology 2)
        (ofDiscreteModule_trivialF2 (AbsoluteGaloisGroup K)))).hom y) =
      continuousCohomologyMap2 _ _ _ _ (ContinuousMonoidHom.id _) (mu2ToUnits K)
        (mu2ToUnits_smul K) y := by
  have hpair : eqToHom (ofDiscreteModule_trivialF2 (AbsoluteGaloisGroup K)) ≫
      (kummerCoeffIsoTrivialF2 K).inv ≫ kummerCoeffToUnits K 2 =
      ofDiscreteModulePair (ContinuousMonoidHom.id (AbsoluteGaloisGroup K) :
          AbsoluteGaloisGroup K →* AbsoluteGaloisGroup K)
        (mu2ToUnits K).toIntLinearMap (mu2ToUnits_smul K) := by
    refine (ofDiscreteModulePair_eq_of_hom_apply _ (mu2ToUnits K).toIntLinearMap
      (mu2ToUnits_smul K) _ fun m ↦ ?_).symm
    -- `TopRep.res` along the identity unfolds to the source object, but not reducibly, so
    -- `TopRep.comp_apply` does not match the composite; `change` exposes it.
    change kummerCoeffToUnits K 2 ((kummerCoeffIsoTrivialF2 K).inv
      (eqToHom (ofDiscreteModule_trivialF2 (AbsoluteGaloisGroup K)) m)) = mu2ToUnits K m
    rw [eqToHom_ofDiscreteModule_trivialF2_apply, kummerCoeffIsoTrivialF2_inv_apply,
      kummerCoeffToUnits_hom_apply, mu2ToUnits_apply]
  rw [continuousCohomologyMap2_eq_map, ← ConcreteCategory.comp_apply, h2MuToUnits_def,
    h2KummerToUnits_def, ← TauCeti.ContinuousCohomology.coeffMap_eqToHom
      (ofDiscreteModule_trivialF2 (AbsoluteGaloisGroup K)),
    ← TauCeti.ContinuousCohomology.coeffMap_comp, ← TauCeti.ContinuousCohomology.coeffMap_comp,
    TauCeti.ContinuousCohomology.coeffMap_def, hpair]

end Field

variable {K : Type u} {L : Type v} [Field K] [Field L] [Invertible (2 : K)] [Invertible (2 : L)]

/-- **`TauCeti.h2MuToUnits` commutes with field transport.** For a field isomorphism
`e : K ≃+* L`, with the fields in independent universes, transporting a class of `H²(G_K, 𝔽₂)` to
`G_L` and then mapping it to `H²(G_L, (Lˢ)ˣ)` is mapping it to `H²(G_K, (Kˢ)ˣ)` and then
transporting along `e`. -/
theorem h2MuToUnits_trivialF2Map2Equiv (e : K ≃+* L)
    (x : continuousCohomology 2 (trivialF2 (AbsoluteGaloisGroup K))) :
    (h2MuToUnits L).hom (trivialF2Map2Equiv e.absoluteGaloisGroupCongr x) =
      e.unitsContinuousH2Congr ((h2MuToUnits K).hom x) := by
  set hK := congrArg (continuousCohomology 2) (ofDiscreteModule_trivialF2 (AbsoluteGaloisGroup K))
  obtain ⟨y, rfl⟩ : ∃ y, (eqToHom hK).hom y = x :=
    ⟨(eqToHom hK.symm).hom x, by rw [← ConcreteCategory.comp_apply, eqToHom_trans, eqToHom_refl,
      ConcreteCategory.id_apply]⟩
  -- Both composites are compatible-pair maps along `G_L ≃ G_K`.
  rw [trivialF2Map2Equiv_eqToHom, h2MuToUnits_eqToHom, h2MuToUnits_eqToHom,
    unitsContinuousH2Congr_apply, ← AddMonoidHom.comp_apply, ← continuousCohomologyMap2_comp]
  have hcomp := continuousCohomologyMap2_comp (AbsoluteGaloisGroup K) _ (AbsoluteGaloisGroup K)
    (UnitsCoeff K) (ContinuousMonoidHom.id _) (mu2ToUnits K) (mu2ToUnits_smul K)
    (AbsoluteGaloisGroup L) (UnitsCoeff L) e.absoluteGaloisGroupCongr
    e.unitsCoeffCongr.toAddMonoidHom e.unitsCoeffCongr_smul
  -- `rw [← hcomp]` fails: the equivariance argument of `unitsContinuousH2Congr` does not
  -- typecheck at reducible transparency, so the composite is matched by unification instead.
  refine Eq.trans ?_ ((DFunLike.congr_fun hcomp y).trans (AddMonoidHom.comp_apply _ _ y))
  -- The group homomorphisms agree by definition, and both coefficient maps send `0` to `1` and
  -- the nontrivial element of `𝔽₂` to `-1`.
  congr 2
  refine AddMonoidHom.ext fun m ↦ Additive.toMul.injective (Units.ext ?_)
  simp only [AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom, AddEquiv.trans_apply,
    unitsCoeffCongr_apply, toMul_mu2ToUnits, AddEquiv.apply_symm_apply]
  split_ifs <;> simp

end RingEquiv
