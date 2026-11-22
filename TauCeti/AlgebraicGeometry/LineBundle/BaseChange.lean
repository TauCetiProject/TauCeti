/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Cohomology.ClosedImmersion.Linear
public import TauCeti.AlgebraicGeometry.Cohomology.FlatBaseChange
public import TauCeti.AlgebraicGeometry.LineBundle.Degree
public import TauCeti.AlgebraicGeometry.LineBundle.Functoriality

/-!
# Line-bundle degree under extension of the base field

The Euler-characteristic degree of a line bundle is unchanged by extension of the ground field
when the source is quasi-compact and quasi-separated, for instance separated of finite type over
the field, and in particular proper. The line bundle after base change is its actual pullback. No
smoothness, rational point or geometric connectedness is needed, so the result applies to nodal
and to reducible proper curves.

Both coefficient cohomology dimensions and both structure-sheaf dimensions are preserved by
field extension, by flat base change of cohomology
(`TauCeti.AlgebraicGeometry.finrank_cohomology_pullback_eq_of_isPullback`). This makes degree,
and hence the subgroup of degree-zero line-bundle classes, compatible with extension of the base
field. Pullback along an isomorphism of schemes over the field preserves degree on every scheme,
with no quasi-compactness or quasi-separation hypothesis
(`TauCeti.AlgebraicGeometry.LineBundleClass.eulerDegree_pullback_of_isIso`).

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
/-- **The degree of a line bundle is unchanged by any extension of the ground field**, on a
quasi-compact quasi-separated scheme, for instance a proper scheme over `k`. The scheme need
not be smooth, irreducible or geometrically connected, nor have a rational point. -/
theorem eulerDegree_pullback [CompactSpace X] [QuasiSeparatedSpace X]
    (L : InvertibleSheaf X) :
    ((pullback g).obj L).eulerDegree K = L.eulerDegree k := by
  let e := pullbackTrivialObjIso g
  rw [eulerDegree_eq_finrank_sub, eulerDegree_eq_finrank_sub, pullback_obj_obj,
    ← Scheme.Modules.finrank_cohomology_congr K e 0,
    ← Scheme.Modules.finrank_cohomology_congr K e 1]
  simp only [finrank_cohomology_pullback_eq_of_isPullback H]

end InvertibleSheaf

namespace LineBundleClass

include H in
/-- Pullback under a field extension preserves the Euler-characteristic degree of a
line-bundle class on a quasi-compact quasi-separated scheme, for instance a proper scheme
over `k`. -/
theorem eulerDegree_pullback [CompactSpace X] [QuasiSeparatedSpace X]
    (a : LineBundleClass X) :
    eulerDegree K (pullback g a) = eulerDegree k a := by
  obtain ⟨L, rfl⟩ := mk_surjective a
  rw [pullback_mk, eulerDegree_mk, eulerDegree_mk, InvertibleSheaf.eulerDegree_pullback H]

omit [Y.Over (Spec (.of K))] in
/-- Pullback along an isomorphism of schemes over `k` preserves the Euler-characteristic degree
of a line-bundle class. Unlike `eulerDegree_pullback`, this needs no quasi-compactness or
quasi-separation: along an isomorphism, cohomology is compared directly
(`AlgebraicGeometry.Scheme.Hom.eulerCharBelow_pullback_of_isIso`). -/
theorem eulerDegree_pullback_of_isIso [Y.Over (Spec (.of k))] (e : Y ⟶ X) [IsIso e]
    (he : e ≫ (X ↘ Spec (.of k)) = Y ↘ Spec (.of k)) (a : LineBundleClass X) :
    eulerDegree k (pullback e a) = eulerDegree k a := by
  have : e.IsOver (Spec (.of k)) := ⟨he⟩
  obtain ⟨L, rfl⟩ := mk_surjective a
  rw [pullback_mk, eulerDegree_mk, eulerDegree_mk, InvertibleSheaf.eulerDegree_def,
    InvertibleSheaf.eulerDegree_def, InvertibleSheaf.pullback_obj_obj,
    ← Scheme.Modules.eulerCharBelow_congr k (InvertibleSheaf.pullbackTrivialObjIso e),
    Scheme.Hom.eulerCharBelow_pullback_of_isIso, Scheme.Hom.eulerCharBelow_pullback_of_isIso]

end LineBundleClass

end

end TauCeti.AlgebraicGeometry
