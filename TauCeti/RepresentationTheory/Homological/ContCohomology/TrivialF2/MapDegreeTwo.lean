/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.Map.DegreeTwo
public import TauCeti.RepresentationTheory.Homological.ContCohomology.TrivialF2

/-!
# Second cohomology with trivial `𝔽₂` coefficients in independent universes

The trivial `𝔽₂` coefficient object `TauCeti.trivialF2 G` has as carrier the lift of `ZMod 2` to
the universe of `G`, and `TauCeti.trivialF2Map` pulls its cohomology back along continuous
homomorphisms of groups in one universe. This file transports `H²(-, 𝔽₂)` along an isomorphism
`φ : H ≃ₜ* G` of locally compact groups in independent universes, such as the absolute Galois
groups of a field `K` and of its universe lift `ULift K`:

```text
trivialF2Map2Equiv φ : H²(G, 𝔽₂) ≃+ H²(H, 𝔽₂).
```

It is the canonical degree-two pullback `TauCeti.ContCohomology.continuousCohomologyMap2Equiv`
along `φ` and the identity of `𝔽₂`, read through the identification
`TauCeti.ofDiscreteModule_trivialF2` of the discrete model of the coefficients with
`TauCeti.trivialF2` itself. When the two groups share a universe it is the pullback
`TauCeti.trivialF2Map` along `φ`.

## Main definitions

* `TauCeti.trivialF2Map2Equiv`: transport of `H²(-, 𝔽₂)` along a topological group isomorphism,
  with the two groups in independent universes.

## Main results

* `TauCeti.trivialF2Map2Equiv_eqToHom`: on the discrete model it is
  `TauCeti.ContCohomology.continuousCohomologyMap2` along `φ` and the identity of `𝔽₂`.
* `TauCeti.trivialF2Map2Equiv_symm`: its inverse is the transport along `φ.symm`.
* `TauCeti.trivialF2Map2Equiv_trans`: transport along a composite is the composite of the
  transports, with the three groups in independent universes.
* `TauCeti.trivialF2Map2Equiv_apply`: in a single universe it is `TauCeti.trivialF2Map`.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., Ch. I, §5:
  compatible pairs and the induced maps on cohomology.
-/

public noncomputable section

namespace TauCeti

open CategoryTheory ContCohomology

universe u v w

attribute [local instance] TopRep.distribMulAction

/-- The trivial `𝔽₂` coefficients are a discrete module. -/
local instance continuousSMul_trivialF2_mapDegreeTwo (G : Type*) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] :
    ContinuousSMul G (trivialF2 G).V :=
  (isSmoothDiscrete_trivialF2 G).continuousSMul

/-- The identification of the discrete model of the trivial `𝔽₂` coefficients with
`TauCeti.trivialF2 G`, read on second continuous cohomology. -/
private def modelEquiv (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] :
    continuousCohomology 2 (ofDiscreteModule ℤ G (trivialF2 G).V) ≃+
      continuousCohomology 2 (trivialF2 G) :=
  (eqToIso (congrArg (continuousCohomology 2)
    (ofDiscreteModule_trivialF2 G))).toContinuousLinearEquiv.toLinearEquiv.toAddEquiv

private theorem modelEquiv_apply {G : Type u} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (y : continuousCohomology 2 (ofDiscreteModule ℤ G (trivialF2 G).V)) :
    modelEquiv G y =
      (eqToHom (congrArg (continuousCohomology 2) (ofDiscreteModule_trivialF2 G))).hom y :=
  (rfl)

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  {H : Type v} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H]

/-- **Transport of `H²(-, 𝔽₂)` along a topological group isomorphism `φ : H ≃ₜ* G`**, with the
universes of `G` and `H` independent. It is the canonical degree-two pullback along `φ` and the
identity of `𝔽₂` (`TauCeti.trivialF2Map2Equiv_eqToHom`), and in a single universe it is
`TauCeti.trivialF2Map` along `φ` (`TauCeti.trivialF2Map2Equiv_apply`). -/
def trivialF2Map2Equiv (φ : H ≃ₜ* G) :
    continuousCohomology 2 (trivialF2 G) ≃+ continuousCohomology 2 (trivialF2 H) :=
  (modelEquiv G).symm.trans ((continuousCohomologyMap2Equiv G (trivialF2 G).V H (trivialF2 H).V φ
    ((trivialF2Equiv G).trans (trivialF2Equiv H).symm) (trivialF2_map_smul _ _)).trans
    (modelEquiv H))

/-- **The transport on the discrete model of the coefficients**: read on a class of the discrete
model `ofDiscreteModule ℤ G 𝔽₂`, `trivialF2Map2Equiv φ` is the canonical degree-two pullback along
`φ` and the identity of `𝔽₂`. -/
theorem trivialF2Map2Equiv_eqToHom (φ : H ≃ₜ* G)
    (y : continuousCohomology 2 (ofDiscreteModule ℤ G (trivialF2 G).V)) :
    trivialF2Map2Equiv φ
        ((eqToHom (congrArg (continuousCohomology 2) (ofDiscreteModule_trivialF2 G))).hom y) =
      (eqToHom (congrArg (continuousCohomology 2) (ofDiscreteModule_trivialF2 H))).hom
        (continuousCohomologyMap2 G (trivialF2 G).V H (trivialF2 H).V φ
          ((trivialF2Equiv G).trans (trivialF2Equiv H).symm).toAddMonoidHom
          (trivialF2_map_smul _ _) y) := by
  rw [← modelEquiv_apply, trivialF2Map2Equiv, AddEquiv.trans_apply, AddEquiv.symm_apply_apply,
    AddEquiv.trans_apply, continuousCohomologyMap2Equiv_apply, modelEquiv_apply]

/-- **The inverse transport is the transport along the inverse isomorphism.** -/
@[simp]
theorem trivialF2Map2Equiv_symm (φ : H ≃ₜ* G) :
    (trivialF2Map2Equiv φ).symm = trivialF2Map2Equiv φ.symm := by
  -- The inverse of the coefficient identification is the identification in the other direction.
  have he : ((trivialF2Equiv G).trans (trivialF2Equiv H).symm).symm =
      (trivialF2Equiv H).trans (trivialF2Equiv G).symm :=
    AddEquiv.ext fun m ↦ by
      rw [AddEquiv.symm_trans_apply, AddEquiv.symm_symm, AddEquiv.trans_apply]
  ext x
  simp only [trivialF2Map2Equiv, AddEquiv.symm_trans_apply, AddEquiv.trans_apply,
    AddEquiv.symm_symm, continuousCohomologyMap2Equiv_symm_apply,
    continuousCohomologyMap2Equiv_apply, he]

/-- **Transport along a composite is the composite of the transports**, with the three groups in
independent universes. -/
theorem trivialF2Map2Equiv_trans {P : Type w} [Group P] [TopologicalSpace P]
    [IsTopologicalGroup P] [LocallyCompactSpace P] (ψ : P ≃ₜ* H) (φ : H ≃ₜ* G) :
    trivialF2Map2Equiv (ψ.trans φ) = (trivialF2Map2Equiv φ).trans (trivialF2Map2Equiv ψ) := by
  have hcomp := continuousCohomologyMap2_comp G (trivialF2 G).V H (trivialF2 H).V φ
    ((trivialF2Equiv G).trans (trivialF2Equiv H).symm).toAddMonoidHom
    (trivialF2_map_smul _ _) P (trivialF2 P).V ψ
    ((trivialF2Equiv H).trans (trivialF2Equiv P).symm).toAddMonoidHom
    (trivialF2_map_smul _ _)
  -- The composite coefficient map is the identification of the outer two carriers.
  have hcoeff : ((trivialF2Equiv H).trans (trivialF2Equiv P).symm).toAddMonoidHom.comp
      ((trivialF2Equiv G).trans (trivialF2Equiv H).symm).toAddMonoidHom =
        ((trivialF2Equiv G).trans (trivialF2Equiv P).symm).toAddMonoidHom :=
    AddMonoidHom.ext fun m ↦ by simp
  have hgrp : (φ : H →ₜ* G).comp (ψ : P →ₜ* H) = ((ψ.trans φ : P ≃ₜ* G) : P →ₜ* G) :=
    ContinuousMonoidHom.ext fun _ ↦ by simp
  simp only [hcoeff, hgrp] at hcomp
  ext x
  obtain ⟨y, rfl⟩ := (modelEquiv G).surjective x
  rw [modelEquiv_apply, AddEquiv.trans_apply, trivialF2Map2Equiv_eqToHom,
    trivialF2Map2Equiv_eqToHom, trivialF2Map2Equiv_eqToHom, ← AddMonoidHom.comp_apply, ← hcomp]

section SameUniverse

variable {G H : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  [LocallyCompactSpace H]

/-- **In a single universe the transport is pullback**: for groups in one universe,
`trivialF2Map2Equiv φ` is `TauCeti.trivialF2Map` along `φ`. -/
theorem trivialF2Map2Equiv_apply (φ : H ≃ₜ* G) (x : continuousCohomology 2 (trivialF2 G)) :
    trivialF2Map2Equiv φ x = (trivialF2Map (φ : H →ₜ* G) 2).hom x := by
  obtain ⟨y, rfl⟩ := (modelEquiv G).surjective x
  rw [modelEquiv_apply, trivialF2Map2Equiv_eqToHom, continuousCohomologyMap2_eq_map,
    ← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
    eqToHom_comp_trivialF2Map (φ : H →ₜ* G) (ofDiscreteModule_trivialF2 G)
      (ofDiscreteModule_trivialF2 H)
      ((trivialF2Equiv G).trans (trivialF2Equiv H).symm).toAddMonoidHom
      (trivialF2_map_smul _ _)
      (fun m ↦ by simp [eqToHom_ofDiscreteModule_trivialF2_apply])]

end SameUniverse

end TauCeti
