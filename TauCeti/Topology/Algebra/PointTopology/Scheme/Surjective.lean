/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.RationalPoint.Image
public import TauCeti.Topology.Algebra.PointTopology.Scheme.Basic

/-!
# Surjective morphisms are surjective on rational points

Over an algebraically closed field `K`, a surjective morphism of `K`-schemes that is locally of
finite type induces a surjective map on `K`-points
(`TauCeti.SchemePointTopology.map_surjective_of_surjective`). This is the surjectivity
counterpart of `TauCeti.SchemePointTopology.map_injective`. It is purely algebraic: no topology
on the points and no properness is involved. It is kept out of the root point-topology module so
that module does not depend on the Jacobson-scheme theory behind
`AlgebraicGeometry.Scheme.Hom.exists_comp_eq_iff_mem_range`.
-/

public section

open CategoryTheory AlgebraicGeometry

universe u

namespace TauCeti.SchemePointTopology

/-- **Surjective morphisms are surjective on rational points over an algebraically closed field.**
A surjective morphism `g : X ⟶ Y` of `K`-schemes that is locally of finite type induces a
surjective map `X(K) → Y(K)`. -/
theorem map_surjective_of_surjective {K : Type u} [Field K] [IsAlgClosed K] {X Y : Scheme.{u}}
    {fX : X ⟶ Spec (.of K)}
    {fY : Y ⟶ Spec (.of K)} (g : X ⟶ Y) (hg : g ≫ fY = fX) [Surjective g]
    [LocallyOfFiniteType g] : Function.Surjective (map (R := K) g hg) := by
  intro y
  obtain ⟨x, hx⟩ := (Scheme.Hom.exists_comp_eq_iff_mem_range g y.val).2 (g.surjective _)
  exact ⟨⟨x, by rw [← hg, ← Category.assoc, hx, y.property]⟩,
    Subtype.ext ((map_val _ _ _).trans hx)⟩

end TauCeti.SchemePointTopology
