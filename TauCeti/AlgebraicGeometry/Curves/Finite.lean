/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.Basic
public import TauCeti.AlgebraicGeometry.Morphisms.Dominant
public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem

/-!
# Nonconstant morphisms of curves are finite

On an irreducible scheme of dimension at most one every point other than the generic point is
closed. Consequently a morphism `f : X ⟶ Y` from an irreducible scheme to such a scheme is either
constant, with value a closed point, or dominant, sending the generic point of `X` to that of `Y`.

If moreover `X` is Noetherian of dimension at most one, `Y` has more than one point and `f` is
proper and dominant, then `f` is finite; `Y` is then irreducible of dimension at most one, as `f`
is surjective and lifts specializations. Its fibres are finite: the fibre over the generic point of
`Y` is the generic point of `X`, since `f` is a closed map and the generic point of `Y` is not
closed, and the fibre over a closed point is a closed subset of `X` missing its generic point.
So `f` is locally quasi-finite, and a proper locally quasi-finite morphism is finite (Mathlib's
`AlgebraicGeometry.IsFinite.of_isProper_of_locallyQuasiFinite`, a consequence of Zariski's main
theorem).

In particular a nonconstant morphism `f : X ⟶ Y` over `k` of curves over a field `k` is finite;
being proper and dominant, it is also surjective
(`AlgebraicGeometry.Surjective.of_universallyClosed_of_isDominant`). This is what makes the degree
`[K(X) : K(Y)]` of `f` the rank of the vector bundle `f_* 𝒪_X`, as in the degree formula for
pulled-back vector bundles.

## Main results

* `AlgebraicGeometry.Scheme.Hom.isDominant_of_nontrivial_range`: a morphism from an irreducible
  scheme to an irreducible scheme of dimension at most one whose image has more than one point is
  dominant;
* `AlgebraicGeometry.Scheme.Hom.isDominant_iff_nontrivial_range`: for a universally closed such
  morphism onto a scheme with more than one point, dominant means nonconstant;
* `AlgebraicGeometry.Scheme.Hom.isFinite_of_isDominant`: a proper dominant morphism from a
  Noetherian irreducible scheme of dimension at most one onto a scheme with more than one point is
  finite;
* `AlgebraicGeometry.Scheme.Hom.isFinite_of_isDominant_of_isCurveOver`: a dominant morphism of
  curves over `k` is finite.

## References

* R. Hartshorne, *Algebraic Geometry*, GTM 52, Springer, 1977, Proposition II.6.8.
-/

public section

open CategoryTheory TopologicalSpace TauCeti.AlgebraicGeometry.Scheme

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {X Y : Scheme.{u}}

section Irreducible

variable [IrreducibleSpace X] [IrreducibleSpace Y]

/-- A morphism from an irreducible scheme to an irreducible scheme of dimension at most one whose
image has more than one point is dominant. Otherwise it would be constant, with value a closed
point. -/
theorem isDominant_of_nontrivial_range (hY : topologicalKrullDim Y ≤ 1) (f : X ⟶ Y)
    (hf : (Set.range f).Nontrivial) : IsDominant f := by
  rw [isDominant_iff_genericPoint_eq]
  by_contra hne
  -- The preimage of the closed point `f (genericPoint X)` is a closed set containing the generic
  -- point of `X`, so `f` is constant.
  have hcl := (isClosed_singleton_of_ne_genericPoint hY hne).preimage f.continuous
  have hconst (x : X) : f x = f (genericPoint X) :=
    (genericPoint_specializes x).mem_closed hcl rfl
  obtain ⟨_, ⟨a, rfl⟩, _, ⟨b, rfl⟩, hab⟩ := hf
  exact hab ((hconst a).trans (hconst b).symm)

/-- A universally closed morphism from an irreducible scheme onto an irreducible scheme of
dimension at most one with more than one point is dominant exactly when it is nonconstant. -/
theorem isDominant_iff_nontrivial_range [Nontrivial Y] (hY : topologicalKrullDim Y ≤ 1)
    (f : X ⟶ Y) [UniversallyClosed f] : IsDominant f ↔ (Set.range f).Nontrivial :=
  ⟨fun _ ↦ f.surjective.range_eq ▸ Set.nontrivial_univ, f.isDominant_of_nontrivial_range hY⟩

omit [IrreducibleSpace Y] in
/-- A proper dominant morphism `f : X ⟶ Y` from a Noetherian irreducible scheme of dimension at
most one onto a scheme with more than one point is finite. -/
theorem isFinite_of_isDominant [NoetherianSpace X] (hX : topologicalKrullDim X ≤ 1)
    [Nontrivial Y] (f : X ⟶ Y) [IsProper f] [IsDominant f] : IsFinite f := by
  have := f.irreducibleSpace_of_isDominant
  -- `f` is surjective and lifts specializations, so `Y` too has dimension at most one.
  have hY : topologicalKrullDim Y ≤ 1 :=
    (f.isClosedMap.specializingMap.topologicalKrullDim_le_of_surjective
      f.surjective).trans hX
  have : LocallyQuasiFinite f := .of_finite_preimage_singleton f fun y ↦ by
    by_cases hy : y = genericPoint Y
    · -- A point `x ≠ genericPoint X` is closed, so its image is closed and is not the generic
      -- point of `Y`, which is not closed. Hence the fibre over the generic point is a singleton.
      subst hy
      refine (Set.finite_singleton (genericPoint X)).subset fun x (hx : f x = _) ↦ ?_
      by_contra hne
      have hcl := f.isClosedMap _ (isClosed_singleton_of_ne_genericPoint hX hne)
      rw [Set.image_singleton, hx] at hcl
      have hgen (z : Y) : z = genericPoint Y := (genericPoint_specializes z).mem_closed hcl rfl
      obtain ⟨a, b, hab⟩ := exists_pair_ne Y
      exact hab ((hgen a).trans (hgen b).symm)
    · -- The fibre over a closed point is closed and misses the generic point of `X`.
      refine finite_of_isClosed_of_genericPoint_notMem hX
        ((isClosed_singleton_of_ne_genericPoint hY hy).preimage f.continuous) fun h ↦ hy ?_
      rw [Set.mem_preimage, Set.mem_singleton_iff, f.genericPoint_eq_of_isDominant] at h
      exact h.symm
  exact IsFinite.of_isProper_of_locallyQuasiFinite f

end Irreducible

section Curve

variable (k : Type u) [Field k] [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]

/-- **Nonconstant morphisms of curves are finite.** A dominant, equivalently nonconstant
(`AlgebraicGeometry.Scheme.Hom.isDominant_iff_nontrivial_range`), morphism over `k` of curves over
a field `k` is finite. -/
theorem isFinite_of_isDominant_of_isCurveOver [X.IsCurveOver k] [Y.IsCurveOver k] (f : X ⟶ Y)
    [f.IsOver (Spec (.of k))] [IsDominant f] : IsFinite f := by
  -- `f` is proper, as `X` is proper and `Y` is separated over `k`.
  have : IsProper (f ≫ Y ↘ Spec (.of k)) := by
    rw [comp_over]
    infer_instance
  have := IsProper.of_comp f (Y ↘ Spec (.of k))
  have := IsCurveOver.nontrivial k Y
  have := IsCurveOver.isNoetherian k X
  exact f.isFinite_of_isDominant (IsCurveOver.topologicalKrullDim_eq_one k).le

end Curve

end AlgebraicGeometry.Scheme.Hom
