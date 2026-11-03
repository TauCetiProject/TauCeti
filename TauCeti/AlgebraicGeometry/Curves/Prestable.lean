/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.Family
public import TauCeti.AlgebraicGeometry.Curves.Node.Fiber
public import Mathlib.AlgebraicGeometry.Geometrically.Connected

/-!
# Prestable families of curves

A prestable family is a proper nodal relative curve with geometrically connected fibres.
Nodality is the scheme-theoretic criterion of syntomicity of relative dimension one and
unramifiedness of the relative singular subscheme. In particular, the fibres have pure
dimension one. No genus bound or projectivity hypothesis is part of this notion.

Prestable families are families of curves. They are invariant under isomorphisms, local on
the base, and stable under arbitrary base change; thus their restrictions and fibres are
again prestable. Smooth proper geometrically connected relative curves provide examples.

Over a local domain of Krull dimension at most one, for instance a discrete valuation ring, a
morphism is a prestable family exactly when it is proper, flat and locally of finite presentation
and its generic and special fibres are prestable curves
(`TauCeti.AlgebraicGeometry.prestableFamily_iff_genericFiber_and_specialFiber`).

## References

* [The Stacks Project, Section 109.20, Prestable curves](https://stacks.math.columbia.edu/tag/0E6S)
-/

public section

open CategoryTheory Limits AlgebraicGeometry

namespace TauCeti.AlgebraicGeometry

universe u

/-- A prestable family is a proper at-worst-nodal relative curve with geometrically connected
fibres. Its genus is separate data; in particular genus zero is allowed. -/
@[mk_iff]
class PrestableFamily {X S : Scheme.{u}} (f : X ⟶ S) : Prop
    extends IsProper f, GeometricallyConnected f where
  /-- The family is nodal, including at its smooth points. -/
  atWorstNodalOfRelativeDimensionOne : AtWorstNodalOfRelativeDimensionOne f

variable {X Y Z S : Scheme.{u}}

namespace PrestableFamily

/-- A prestable family is syntomic of relative dimension one. -/
instance syntomic (f : X ⟶ S) [PrestableFamily f] : SyntomicOfRelativeDimension 1 f :=
  (atWorstNodalOfRelativeDimensionOne (f := f)).syntomic

/-- A prestable family is a family of curves: it is proper, flat, finitely presented, and
has relative dimension at most one. -/
instance familyOfCurves (f : X ⟶ S) [PrestableFamily f] : FamilyOfCurves f :=
  ⟨⟩

/-- Prestable families are stable under arbitrary base change. -/
instance isStableUnderBaseChange :
    MorphismProperty.IsStableUnderBaseChange @PrestableFamily.{u} where
  of_isPullback h hf := by
    have := hf
    exact {
      toIsProper := MorphismProperty.of_isPullback (P := @IsProper) h inferInstance
      toGeometricallyConnected :=
        MorphismProperty.of_isPullback (P := @GeometricallyConnected) h inferInstance
      atWorstNodalOfRelativeDimensionOne :=
        MorphismProperty.of_isPullback (P := @AtWorstNodalOfRelativeDimensionOne) h
          hf.atWorstNodalOfRelativeDimensionOne }

/-- Prestable families are invariant under isomorphisms of arrows. -/
instance respectsIso : MorphismProperty.RespectsIso @PrestableFamily.{u} :=
  MorphismProperty.IsStableUnderBaseChange.respectsIso

/-- Being prestable is local on the base for the Zariski topology. -/
instance isZariskiLocalAtTarget : IsZariskiLocalAtTarget @PrestableFamily.{u} := by
  have : IsZariskiLocalAtTarget @GeometricallyConnected.{u} := by
    rw [GeometricallyConnected.eq_geometrically]
    infer_instance
  refine .mk' (fun f U hf ↦
    MorphismProperty.of_isPullback (P := @PrestableFamily)
      (isPullback_morphismRestrict f U).flip hf) ?_
  intro X S f ι U hU hf
  exact {
    toIsProper := IsZariskiLocalAtTarget.of_iSup_eq_top U hU fun i ↦ (hf i).toIsProper
    toGeometricallyConnected := IsZariskiLocalAtTarget.of_iSup_eq_top U hU fun i ↦
      (hf i).toGeometricallyConnected
    atWorstNodalOfRelativeDimensionOne :=
      IsZariskiLocalAtTarget.of_iSup_eq_top U hU fun i ↦
        (hf i).atWorstNodalOfRelativeDimensionOne }

/-- An arbitrary pullback of a prestable family is prestable. -/
theorem of_isPullback {P : Scheme.{u}} {fst : P ⟶ X} {snd : P ⟶ Y}
    {f : X ⟶ Z} {g : Y ⟶ Z} (h : IsPullback fst snd f g) [PrestableFamily f] :
    PrestableFamily snd :=
  MorphismProperty.of_isPullback (P := @PrestableFamily) h inferInstance

/-- The base change of a prestable family along any morphism is prestable. -/
instance pullback_snd (f : X ⟶ Z) (g : Y ⟶ Z) [PrestableFamily f] :
    PrestableFamily (pullback.snd f g) :=
  of_isPullback (.of_hasPullback f g)

/-- The base change of a prestable family along any morphism is prestable. -/
instance pullback_fst (f : X ⟶ Z) (g : Y ⟶ Z) [PrestableFamily g] :
    PrestableFamily (pullback.fst f g) :=
  of_isPullback (IsPullback.of_hasPullback f g).flip

/-- Restricting a prestable family to an open subscheme of the base preserves prestability. -/
instance morphismRestrict (f : X ⟶ S) (U : S.Opens) [PrestableFamily f] :
    PrestableFamily (f ∣_ U) :=
  of_isPullback (isPullback_morphismRestrict f U).flip

/-- Every residue-field fibre of a prestable family is a prestable curve. -/
instance fiberToSpecResidueField (f : X ⟶ S) (s : S) [PrestableFamily f] :
    PrestableFamily (f.fiberToSpecResidueField s) :=
  inferInstanceAs (PrestableFamily (pullback.snd _ _))

/-- A smooth proper relative curve of pure relative dimension one with geometrically
connected fibres is prestable. -/
theorem of_smooth (f : X ⟶ S) [IsProper f] [SmoothOfRelativeDimension 1 f]
    [GeometricallyConnected f] : PrestableFamily f where
  atWorstNodalOfRelativeDimensionOne := AtWorstNodalOfRelativeDimensionOne.of_smooth f

end PrestableFamily

section DimensionLEOne

variable {R : CommRingCat.{u}} [IsLocalRing R] [IsDomain R] [Ring.DimensionLEOne R]
variable (K : Type u) [CommRing K] [Algebra R K] [IsFractionRing R K]
variable (toBase : X ⟶ Spec R)

/-- **The two-fibre criterion for prestable families.** Over a local domain of dimension at most
one, for instance a discrete valuation ring, a morphism is a prestable family exactly when it is
proper, flat and locally of finite presentation and both its generic fibre over the fraction field
and its special fibre over the residue field are prestable curves. -/
theorem prestableFamily_iff_genericFiber_and_specialFiber :
    PrestableFamily toBase ↔
      IsProper toBase ∧ Flat toBase ∧ LocallyOfFinitePresentation toBase ∧
        PrestableFamily (genericFiber R K toBase).hom ∧
          PrestableFamily (specialFiber R toBase).hom := by
  refine ⟨fun _ ↦ ⟨inferInstance, inferInstance, inferInstance,
      .of_isPullback (isPullback_genericFiber R K toBase),
      .of_isPullback (isPullback_specialFiber R toBase)⟩, ?_⟩
  rintro ⟨hp, hf, hl, hg, hs⟩
  refine
    { toIsProper := hp
      toGeometricallyConnected := ?_
      atWorstNodalOfRelativeDimensionOne :=
        (atWorstNodalOfRelativeDimensionOne_iff_genericFiber_and_specialFiber K toBase).mpr
          ⟨hf, hl, hg.atWorstNodalOfRelativeDimensionOne, hs.atWorstNodalOfRelativeDimensionOne⟩ }
  -- Fixing the universe lets instance search find isomorphism invariance.
  have : MorphismProperty.RespectsIso @GeometricallyConnected.{u} :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  rw [GeometricallyConnected.iff_geometricallyConnected_fiber,
    forall_fiberToSpecResidueField_iff K toBase @GeometricallyConnected]
  exact ⟨hg.toGeometricallyConnected, hs.toGeometricallyConnected⟩

end DimensionLEOne

end TauCeti.AlgebraicGeometry
