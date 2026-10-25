/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Cohomology.BaseChange
public import TauCeti.AlgebraicGeometry.Curves.AffineCover
public import TauCeti.AlgebraicGeometry.LineBundle.Degree
public import TauCeti.AlgebraicGeometry.LineBundle.Functoriality

/-!
# Line-bundle degree under extension of the base field

The Euler-characteristic degree of a line bundle is unchanged by extension of the ground field
when the source and its base change are locally Noetherian and the source has a two-affine cover
with affine intersection. The line bundle after base change is its actual pullback. In
particular, the result holds for smooth proper connected curves over arbitrary fields, without
a rational point or geometric connectedness hypothesis.

Both coefficient cohomology dimensions and both structure-sheaf dimensions are preserved by
field extension. This makes degree, and hence the subgroup of degree-zero line-bundle classes,
compatible with extension of the base field.

## References

* R. Hartshorne, *Algebraic Geometry*, Proposition III.9.3 (flat base change).
-/

public section

open CategoryTheory Limits AlgebraicGeometry

namespace TauCeti.AlgebraicGeometry

universe u

noncomputable section

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of K))] {g : Y ⟶ X}
  (H : IsPullback g (Y ↘ Spec (.of K)) (X ↘ Spec (.of k))
    (Spec.map (CommRingCat.ofHom (algebraMap k K))))

namespace InvertibleSheaf

include H in
/-- Pullback under a field extension preserves Euler-characteristic degree on a locally
Noetherian scheme with a two-affine cover having affine intersection, provided the base change
is also locally Noetherian. -/
theorem eulerDegree_pullback_of_two_affine_opens [IsLocallyNoetherian X]
    [IsLocallyNoetherian Y] (L : InvertibleSheaf X) {U V : X.Opens}
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hInter : IsAffineOpen (U ⊓ V))
    (hUV : U ⊔ V = ⊤) :
    ((pullback g).obj L).eulerDegree K = L.eulerDegree k := by
  have hOne (M : X.Modules) [M.IsQuasicoherent] :
      Module.finrank K (Scheme.Modules.Cohomology ((Scheme.Modules.pullback g).obj M) 1) =
        Module.finrank k (Scheme.Modules.Cohomology M 1) := by
    obtain ⟨e⟩ := nonempty_linearEquiv_tensor_cohomology_one_pullback H M hU hV hInter hUV
    have : Module.Free k (Scheme.Modules.Cohomology M 1) := Module.Free.of_divisionRing _ _
    rw [← e.finrank_eq, Module.finrank_baseChange]
  have : CompactSpace X := ⟨by
    rw [← TopologicalSpace.Opens.coe_top, ← hUV, TopologicalSpace.Opens.coe_sup]
    exact hU.isCompact.union hV.isCompact⟩
  let e : (Scheme.Modules.pullback g).obj (trivial X).obj ≅ (trivial Y).obj :=
    (Scheme.Modules.pullback g).mapIso (trivialObjIsoUnit X) ≪≫
      Scheme.Modules.pullbackObjUnitIso g ≪≫ (trivialObjIsoUnit Y).symm
  have hTrivial (i : ℕ) := Scheme.Modules.finrank_cohomology_congr K e i
  rw [eulerDegree_eq_finrank_sub, eulerDegree_eq_finrank_sub, pullback_obj_obj,
    ← hTrivial 0, ← hTrivial 1,
    finrank_cohomology_zero_pullback_eq_of_isPullback H L.obj, hOne L.obj,
    finrank_cohomology_zero_pullback_eq_of_isPullback H (trivial X).obj,
    hOne (trivial X).obj]

include H in
/-- The degree of a line bundle on a smooth proper connected curve is unchanged by any
extension of the ground field. The curve need not have a rational point or be geometrically
connected. -/
theorem eulerDegree_pullback [IsProper (X ↘ Spec (.of k))]
    [SmoothOfRelativeDimension 1 (X ↘ Spec (.of k))] [ConnectedSpace X]
    (L : InvertibleSheaf X) :
    ((pullback g).obj L).eulerDegree K = L.eulerDegree k := by
  have := SmoothOfRelativeDimension.smooth 1 (X ↘ Spec (.of k))
  have := Scheme.IsSeparated.of_isSeparated (X ↘ Spec (.of k))
  have : CompactSpace X := compactSpace_of_universallyClosed (X ↘ Spec (.of k))
  obtain ⟨U, V, hU, hV, hUV⟩ := X.exists_two_affine_opens_of_smooth (k := k)
  have : LocallyOfFiniteType (Y ↘ Spec (.of K)) := MorphismProperty.of_isPullback H inferInstance
  have := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  have := LocallyOfFiniteType.isLocallyNoetherian (Y ↘ Spec (.of K))
  exact eulerDegree_pullback_of_two_affine_opens H L hU hV (hU.inf hV) hUV

end InvertibleSheaf

namespace LineBundleClass

include H in
/-- Pullback under a field extension preserves the Euler-characteristic degree of a
line-bundle class on a locally Noetherian scheme with a two-affine cover having affine
intersection, provided the base change is also locally Noetherian. -/
theorem eulerDegree_pullback_of_two_affine_opens [IsLocallyNoetherian X]
    [IsLocallyNoetherian Y] (a : LineBundleClass X) {U V : X.Opens}
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hInter : IsAffineOpen (U ⊓ V))
    (hUV : U ⊔ V = ⊤) :
    eulerDegree K (pullback g a) = eulerDegree k a := by
  obtain ⟨L, rfl⟩ := mk_surjective a
  rw [pullback_mk, eulerDegree_mk, eulerDegree_mk,
    InvertibleSheaf.eulerDegree_pullback_of_two_affine_opens H L hU hV hInter hUV]

include H in
/-- Pullback under a field extension preserves the Euler-characteristic degree of a
line-bundle class on a smooth proper connected curve. -/
theorem eulerDegree_pullback [IsProper (X ↘ Spec (.of k))]
    [SmoothOfRelativeDimension 1 (X ↘ Spec (.of k))] [ConnectedSpace X]
    (a : LineBundleClass X) :
    eulerDegree K (pullback g a) = eulerDegree k a := by
  obtain ⟨L, rfl⟩ := mk_surjective a
  rw [pullback_mk, eulerDegree_mk, eulerDegree_mk, InvertibleSheaf.eulerDegree_pullback H]

end LineBundleClass

end

end TauCeti.AlgebraicGeometry
