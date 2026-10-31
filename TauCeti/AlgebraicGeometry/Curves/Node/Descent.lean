/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.Node.Fiber
public import TauCeti.AlgebraicGeometry.Morphisms.Flat.Descent
public import TauCeti.AlgebraicGeometry.Morphisms.Syntomic.Descent
import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent

/-!
# Nodal relative curves satisfy fpqc descent

A morphism whose base change along a surjective, flat and quasi-compact morphism is at worst
nodal of relative dimension one is itself at worst nodal of relative dimension one. Together
with stability under base change, this says that nodality is local on the base for the fpqc
topology, and hence for the étale and fppf topologies.

Over an affine base and along a faithfully flat ring map `R → R'`, both halves of the nodal
criterion descend: syntomicity of relative dimension one by
`SyntomicOfRelativeDimension.descendsAlong_surjective_inf_flat_inf_quasicompact`, and
unramifiedness of the singular subscheme because the singular subscheme of the base change is
the base change of the singular subscheme
(`AlgebraicGeometry.Scheme.isPullback_singularLocus_subschemeι`). For a general fpqc morphism,
the fibrewise criterion `atWorstNodalOfRelativeDimensionOne_iff_flat_and_fiberToSpecResidueField`
reduces the question to flatness and finite presentation, which descend, and to the fibres, which
are base changes of each other along extensions of residue fields.

## Main results

* `AffineAtWorstNodalOfRelativeDimensionOne.of_isPullback_of_faithfullyFlat`: over an affine
  base, nodality descends along faithfully flat extensions of the base ring.
* `AtWorstNodalOfRelativeDimensionOne.descendsAlong_surjective_inf_flat_inf_quasicompact`:
  nodality descends along surjective, flat, quasi-compact morphisms.

## References

* [Stacks Project, Section 53.20, Tag 0C58](https://stacks.math.columbia.edu/tag/0C58): families
  of nodal curves.
-/

public section

open CategoryTheory Limits MorphismProperty AlgebraicGeometry

namespace TauCeti.AlgebraicGeometry

universe u

variable {R R' : Type u} [CommRing R] [CommRing R'] [Algebra R R'] {X X' : Scheme.{u}}

/-- Over an affine base, nodality descends along a faithfully flat extension `R → R'` of the base
ring: if the base change of `X` to `R'` is a nodal relative curve, so is `X`. This is the converse
of `TauCeti.AlgebraicGeometry.AffineAtWorstNodalOfRelativeDimensionOne.of_isPullback`. -/
theorem AffineAtWorstNodalOfRelativeDimensionOne.of_isPullback_of_faithfullyFlat
    [Module.FaithfullyFlat R R'] [X.Over (Spec (.of R))] [X'.Over (Spec (.of R'))]
    {g : X' ⟶ X}
    (H : IsPullback g (X' ↘ Spec (.of R')) (X ↘ Spec (.of R))
      (Spec.map (CommRingCat.ofHom (algebraMap R R'))))
    (h : AffineAtWorstNodalOfRelativeDimensionOne (X' ↘ Spec (.of R'))) :
    AffineAtWorstNodalOfRelativeDimensionOne (X ↘ Spec (.of R)) := by
  have hR : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{u})
      (Spec.map (CommRingCat.ofHom (algebraMap R R'))) := by
    obtain ⟨hfl, hsurj⟩ := (flat_and_surjective_SpecMap_iff
      (CommRingCat.ofHom (algebraMap R R'))).mpr
      (RingHom.faithfullyFlat_algebraMap_iff.mpr inferInstance)
    exact ⟨⟨hsurj, hfl⟩, inferInstance⟩
  -- The syntomic instances on `X'` and `X` supply the flatness and finite presentation needed
  -- to compare singular subschemes below.
  have : SyntomicOfRelativeDimension 1 (X' ↘ Spec (.of R')) := h.syntomic
  have : SyntomicOfRelativeDimension 1 (X ↘ Spec (.of R)) :=
    of_isPullback_of_descendsAlong H.flip hR ‹_›
  refine AffineAtWorstNodalOfRelativeDimensionOne.mk ‹_› ?_
  have hs := (Scheme.isPullback_singularLocus_subschemeι (R := R) (R' := R') H).flip.paste_vert H
  exact of_isPullback_of_descendsAlong hs.flip hR h.unramified_singularLocus

/-- **Nodal curves satisfy fpqc descent.** Being at worst nodal of relative dimension one descends
along surjective, flat, quasi-compact morphisms. -/
instance AtWorstNodalOfRelativeDimensionOne.descendsAlong_surjective_inf_flat_inf_quasicompact :
    MorphismProperty.DescendsAlong @AtWorstNodalOfRelativeDimensionOne.{u}
      (@Surjective ⊓ @Flat ⊓ @QuasiCompact) := by
  refine DescendsAlong.mk' fun {X Y Z f g} _ hf h ↦ ?_
  rw [atWorstNodalOfRelativeDimensionOne_iff_flat_and_fiberToSpecResidueField] at h ⊢
  obtain ⟨hfl, hfp, hfib⟩ := h
  refine ⟨of_pullback_fst_of_descendsAlong hf hfl, of_pullback_fst_of_descendsAlong hf hfp,
    fun z ↦ ?_⟩
  obtain ⟨x, rfl⟩ := hf.1.1.surj z
  -- The fibre of `pullback.fst f g` over `x` is the base change of the fibre of `g` over `f x`
  -- along the field extension `κ(f x) → κ(x)`.
  have H := isPullback_fiberToSpecResidueField_of_isPullback (IsPullback.of_hasPullback f g).flip x
  algebraize [(f.residueFieldMap x).hom]
  let : (g.fiber (f x)).Over (Spec (.of (Z.residueField (f x)))) :=
    ⟨g.fiberToSpecResidueField (f x)⟩
  let : ((pullback.fst f g).fiber x).Over (Spec (.of (X.residueField x))) :=
    ⟨(pullback.fst f g).fiberToSpecResidueField x⟩
  have hx := hfib x
  rw [atWorstNodalOfRelativeDimensionOne_iff_of_isAffine _ (Iso.refl _)] at hx ⊢
  simp only [Iso.refl_hom, Category.comp_id] at hx ⊢
  exact AffineAtWorstNodalOfRelativeDimensionOne.of_isPullback_of_faithfullyFlat H hx

end TauCeti.AlgebraicGeometry
