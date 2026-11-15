/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.Map.DegreeOne
public import TauCeti.RepresentationTheory.Homological.ContCohomology.TrivialF2

/-!
# First cohomology with trivial `𝔽₂` coefficients in independent universes

The trivial `𝔽₂` coefficient object `TauCeti.trivialF2 G` has as carrier the lift of `ZMod 2` to
the universe of `G`, and `TauCeti.trivialF2Map` pulls its cohomology back along continuous
homomorphisms of groups in one universe. This file transports `H¹(-, 𝔽₂)` along an isomorphism
`φ : H ≃ₜ* G` of topological groups in independent universes, such as the absolute Galois groups
of a field `K` and of its universe lift `ULift K`:

```text
trivialF2Map1Equiv φ : H¹(G, 𝔽₂) ≃+ H¹(H, 𝔽₂).
```

It is the canonical degree-one pullback `TauCeti.ContCohomology.continuousCohomologyMap1Equiv`
along `φ` and the identity of `𝔽₂`, read through the identification
`TauCeti.ofDiscreteModule_trivialF2` of the discrete model of the coefficients with
`TauCeti.trivialF2` itself. When the two groups share a universe it is the pullback
`TauCeti.trivialF2Map` along `φ`.

## Main definitions

* `TauCeti.trivialF2Map1Equiv`: transport of `H¹(-, 𝔽₂)` along a topological group isomorphism,
  with the two groups in independent universes.

## Main results

* `TauCeti.trivialF2Map1Equiv_eqToHom`: on the discrete model it is
  `TauCeti.ContCohomology.continuousCohomologyMap1` along `φ` and the identity of `𝔽₂`.
* `TauCeti.trivialF2Map1Equiv_symm`: its inverse is the transport along `φ.symm`.
* `TauCeti.trivialF2Map1Equiv_apply`: in a single universe it is `TauCeti.trivialF2Map`.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., Ch. I, §5:
  compatible pairs and the induced maps on cohomology.
-/

public noncomputable section

namespace TauCeti

open CategoryTheory ContCohomology

universe u v

attribute [local instance] TopRep.distribMulAction

/-- The trivial `𝔽₂` coefficients are a discrete module. -/
local instance continuousSMul_trivialF2_mapDegreeOne (G : Type*) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] :
    ContinuousSMul G (trivialF2 G).V :=
  (isSmoothDiscrete_trivialF2 G).continuousSMul

/-- The identification of the discrete model of the trivial `𝔽₂` coefficients with
`TauCeti.trivialF2 G`, read on first continuous cohomology. -/
private def modelEquiv (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] :
    continuousCohomology 1 (ofDiscreteModule ℤ G (trivialF2 G).V) ≃+
      continuousCohomology 1 (trivialF2 G) :=
  (eqToIso (congrArg (continuousCohomology 1)
    (ofDiscreteModule_trivialF2 G))).toContinuousLinearEquiv.toLinearEquiv.toAddEquiv

private theorem modelEquiv_apply {G : Type u} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (y : continuousCohomology 1 (ofDiscreteModule ℤ G (trivialF2 G).V)) :
    modelEquiv G y =
      (eqToHom (congrArg (continuousCohomology 1) (ofDiscreteModule_trivialF2 G))).hom y :=
  (rfl)

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {H : Type v} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

/-- **Transport of `H¹(-, 𝔽₂)` along a topological group isomorphism `φ : H ≃ₜ* G`**, with the
universes of `G` and `H` independent. It is the canonical degree-one pullback along `φ` and the
identity of `𝔽₂` (`TauCeti.trivialF2Map1Equiv_eqToHom`), and in a single universe it is
`TauCeti.trivialF2Map` along `φ` (`TauCeti.trivialF2Map1Equiv_apply`). -/
def trivialF2Map1Equiv (φ : H ≃ₜ* G) :
    continuousCohomology 1 (trivialF2 G) ≃+ continuousCohomology 1 (trivialF2 H) :=
  (modelEquiv G).symm.trans ((continuousCohomologyMap1Equiv G (trivialF2 G).V H (trivialF2 H).V φ
    ((trivialF2Equiv G).trans (trivialF2Equiv H).symm)
    (fun _ _ ↦ by simp only [TopRep.distribMulAction_smul, trivialF2_ρ_apply_apply])).trans
    (modelEquiv H))

/-- **The transport on the discrete model of the coefficients**: read on a class of the discrete
model `ofDiscreteModule ℤ G 𝔽₂`, `trivialF2Map1Equiv φ` is the canonical degree-one pullback along
`φ` and the identity of `𝔽₂`. -/
theorem trivialF2Map1Equiv_eqToHom (φ : H ≃ₜ* G)
    (y : continuousCohomology 1 (ofDiscreteModule ℤ G (trivialF2 G).V)) :
    trivialF2Map1Equiv φ
        ((eqToHom (congrArg (continuousCohomology 1) (ofDiscreteModule_trivialF2 G))).hom y) =
      (eqToHom (congrArg (continuousCohomology 1) (ofDiscreteModule_trivialF2 H))).hom
        (continuousCohomologyMap1 G (trivialF2 G).V H (trivialF2 H).V φ trivialF2CoeffHom
          (trivialF2CoeffHom_smul ((φ : H →ₜ* G) : H →* G)) y) := by
  rw [← modelEquiv_apply, trivialF2Map1Equiv, AddEquiv.trans_apply, AddEquiv.symm_apply_apply,
    AddEquiv.trans_apply, continuousCohomologyMap1Equiv_apply, modelEquiv_apply]
  simp only [trivialF2CoeffHom_def]

/-- **The inverse transport is the transport along the inverse isomorphism.** -/
@[simp]
theorem trivialF2Map1Equiv_symm (φ : H ≃ₜ* G) :
    (trivialF2Map1Equiv φ).symm = trivialF2Map1Equiv φ.symm := by
  have hcoeff : ((trivialF2Equiv G).trans (trivialF2Equiv H).symm).symm =
      (trivialF2Equiv H).trans (trivialF2Equiv G).symm := by
    ext m
    simp
  ext x
  simp only [trivialF2Map1Equiv, AddEquiv.symm_trans_apply, AddEquiv.trans_apply,
    AddEquiv.symm_symm, continuousCohomologyMap1Equiv_symm_apply,
    continuousCohomologyMap1Equiv_apply, hcoeff]

section SameUniverse

variable {G H : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

/-- **In a single universe the transport is pullback**: for groups in one universe,
`trivialF2Map1Equiv φ` is `TauCeti.trivialF2Map` along `φ`. -/
theorem trivialF2Map1Equiv_apply (φ : H ≃ₜ* G) (x : continuousCohomology 1 (trivialF2 G)) :
    trivialF2Map1Equiv φ x = (trivialF2Map (φ : H →ₜ* G) 1).hom x := by
  obtain ⟨y, rfl⟩ := (modelEquiv G).surjective x
  rw [modelEquiv_apply, trivialF2Map1Equiv_eqToHom, continuousCohomologyMap1_eq_map,
    ← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
    eqToHom_comp_trivialF2Map (φ : H →ₜ* G) (ofDiscreteModule_trivialF2 G)
      (ofDiscreteModule_trivialF2 H) trivialF2CoeffHom
      (trivialF2CoeffHom_smul ((φ : H →ₜ* G) : H →* G))
      (fun m ↦ by simp [eqToHom_ofDiscreteModule_trivialF2_apply])]

end SameUniverse

end TauCeti
