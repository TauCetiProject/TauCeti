/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.PlanarMatching.Rigid
public import TauCeti.CategoryTheory.Monoidal.Free.CircleCentral

/-!
# The Temperley–Lieb diagram category as a quotient of the presented self-duality

The Temperley–Lieb diagram category `TauCeti.TLDiagCat` records closed circles only by their
number, not by their position among the strands. Consequently a closed circle can be moved across
every strand: for every endomorphism `d` of the empty boundary and every object `X`, the left and
right actions of `d` on `X` agree (`TauCeti.TLDiagCat.circlesCommuteAt`). Two such actions are
diagrams with straight strands and the same number of circles.

In particular the generating self-duality of `TLDiagCat.of 1`, by the cup and the cap, has a
central closed circle. By the universal property of the monoidal category
`TauCeti.CircleCentralSelfDualityCat`, presented by a self-dual object, the two zigzag equations
and centrality of the circle at the generator, there is therefore a strong monoidal comparison
functor `TauCeti.CircleCentralSelfDualityCat.toTLDiagCat` sending the generator to `of 1`, the
generating cup and cap to `TLDiagCat.cup` and `TLDiagCat.cap`, and the generating closed circle to
`TLDiagCat.circle`. The presentation of the Temperley–Lieb diagram category is the statement that
this functor is an equivalence. This file constructs it and proves that it is surjective on
objects and that every endomorphism of the empty boundary, a power of the circle, is in its image.

Conversely, centrality of the circle is forced on every interpretation of `TLDiagCat`: a strong
monoidal functor `TLDiagCat ⥤ C` sending the generating self-duality to a self-duality of `V` makes
the closed circle of `V` central at `V` (`TauCeti.TLDiagCat.circlesCommuteAt_of_sendsSelfDuality`).
So the zigzag equations alone, which present `TauCeti.FreeSelfDualityCat`, do not describe the
functors out of `TLDiagCat`.

## Main definitions

* `TauCeti.CircleCentralSelfDualityCat.toTLDiagCat`: the strong monoidal comparison functor from
  the presented self-duality with central circle to the Temperley–Lieb diagram category.

## Main results

* `TauCeti.TLDiagCat.circlesCommuteAt`: in `TLDiagCat`, every endomorphism of the empty boundary
  acts in the same way on the left and on the right of every object.
* `TauCeti.TLDiagCat.circlesCommuteAt_of_sendsSelfDuality`: a strong monoidal functor out of
  `TLDiagCat` sends its generating self-duality only to self-dualities with central circle.
* `TauCeti.CircleCentralSelfDualityCat.toTLDiagCat_map_circle`: the comparison functor sends the
  generating closed circle to the closed circle.
* `TauCeti.CircleCentralSelfDualityCat.exists_toTLDiagCat_obj_eq`: every object of `TLDiagCat` is
  the image of an object, so the comparison functor is essentially surjective.
* `TauCeti.CircleCentralSelfDualityCat.toTLDiagCat_map_surjective_tensorUnit`: every endomorphism
  of the empty boundary is the image of an endomorphism of the unit.

## References

* A. Joyal and R. Street, *The geometry of tensor calculus I*, Adv. Math. 88 (1991), 55–112.
* J. Chen, *The Temperley–Lieb categories and skein modules*, arXiv:1502.06845, §2.
-/

public section

open CategoryTheory MonoidalCategory

namespace TauCeti

namespace TLDiagCat

/-- A closed circle can be moved across any number of straight strands: the closed circle acts in
the same way on the left and on the right of every object. -/
private theorem circlesCommuteAt_circle (X : TLDiagCat) : CirclesCommuteAt circle X := by
  rw [circlesCommuteAt_iff]
  ext : 1
  simp only [leftUnitor_hom, leftUnitor_inv, rightUnitor_hom, rightUnitor_inv, diagram_comp,
    diagram_eqToHom, diagram_whiskerLeft, diagram_whiskerRight, diagram_circle]
  -- Both sides are straight strands with one circle; compare the strands with the unit laws.
  have h₁ := congrArg TLDiagram.matching (TLDiagram.tensor_id_zero (TLDiagram.id X.as))
  have h₂ := congrArg TLDiagram.matching (TLDiagram.id_zero_tensor (TLDiagram.id X.as))
  simp only [TLDiagram.matching_tensor, TLDiagram.matching_cast, TLDiagram.matching_id] at h₁ h₂
  ext : 1
  · simpa [TLDiagram.matching_tensor, h₂] using h₁
  · simp

/-- **Closed circles are central in the Temperley–Lieb diagram category**: every endomorphism of
the empty boundary acts in the same way on the left and on the right of every object. -/
theorem circlesCommuteAt (d : 𝟙_ TLDiagCat ⟶ 𝟙_ TLDiagCat) (X : TLDiagCat) :
    CirclesCommuteAt d X := by
  have hd : d = (End.of circle ^ (End.of d).asHom.diagram.circles).asHom :=
    congrArg End.asHom (end_zero_eq_circle_pow (End.of d))
  rw [hd]
  induction (End.of d).asHom.diagram.circles with
  | zero => exact circlesCommuteAt_id X
  | succ k ih =>
    rw [pow_succ, End.mul_asHom]
    exact (circlesCommuteAt_circle X).comp ih

/-- **Necessity of circle centrality for interpretations of `TLDiagCat`**: if a strong monoidal
functor out of the Temperley–Lieb diagram category sends the generating self-duality of `of 1`,
by the cup and the cap, to the self-duality of `V`, then the closed circle of `V` is central at
`V`. -/
theorem circlesCommuteAt_of_sendsSelfDuality {C : Type*} [Category* C] [MonoidalCategory C]
    (G : TLDiagCat ⥤ C) [G.Monoidal] {V : C} [ExactPairing V V] {e : G.obj (of 1) ≅ V}
    (he : SendsSelfDuality G V e) : CirclesCommuteAt (η_ V V ≫ ε_ V V) V :=
  he.circlesCommuteAt (circlesCommuteAt _ _)

end TLDiagCat

namespace CircleCentralSelfDualityCat

/-- The **comparison functor** from the monoidal category presented by a self-dual object with
central closed circle to the Temperley–Lieb diagram category: the interpretation of the generator
as a single boundary point `TLDiagCat.of 1`, of the generating cup as `TLDiagCat.cup` and of the
generating cap as `TLDiagCat.cap`. It is strong monoidal, with identity comparison morphisms. -/
abbrev toTLDiagCat : CircleCentralSelfDualityCat ⥤ TLDiagCat :=
  lift (TLDiagCat.of 1) (TLDiagCat.circlesCommuteAt _ _)

/-- The comparison functor sends the unit to the empty boundary. -/
@[simp]
theorem toTLDiagCat_obj_tensorUnit :
    toTLDiagCat.obj (𝟙_ CircleCentralSelfDualityCat) = 𝟙_ TLDiagCat := (rfl)

/-- The comparison functor is strict on objects: the image of a tensor product is the tensor
product of the images. -/
@[simp]
theorem toTLDiagCat_obj_tensor (X Y : CircleCentralSelfDualityCat) :
    toTLDiagCat.obj (X ⊗ Y) = toTLDiagCat.obj X ⊗ toTLDiagCat.obj Y := (rfl)

/-- The comparison functor sends the generating closed circle to the closed circle. -/
theorem toTLDiagCat_map_circle :
    toTLDiagCat.map (η_ generator generator ≫ ε_ generator generator) = TLDiagCat.circle := by
  rw [Functor.map_comp, lift_map_coevaluation, lift_map_evaluation, TLDiagCat.coevaluation_one,
    TLDiagCat.evaluation_one]
  -- The objects of `cup` and `cap` are the images of the unit and of `generator ⊗ generator`.
  exact TLDiagCat.cup_comp_cap

/-- **Every object of `TLDiagCat` is in the image of the comparison functor**: the object with
`n` boundary points is the image of the `n`-fold tensor power of the generator. -/
theorem exists_toTLDiagCat_obj_eq (Y : TLDiagCat) : ∃ X, toTLDiagCat.obj X = Y := by
  obtain ⟨n⟩ := Y
  induction n with
  | zero => exact ⟨𝟙_ _, rfl⟩
  | succ n ih =>
    obtain ⟨X, hX⟩ := ih
    exact ⟨X ⊗ generator, by rw [toTLDiagCat_obj_tensor, hX]; rfl⟩

instance : toTLDiagCat.EssSurj where
  mem_essImage Y := ⟨_, ⟨eqToIso (exists_toTLDiagCat_obj_eq Y).choose_spec⟩⟩

/-- **The comparison functor is full at the unit**: every endomorphism of the empty boundary,
a number of closed circles, is the image of a power of the generating closed circle. -/
theorem toTLDiagCat_map_surjective_tensorUnit :
    Function.Surjective
      (toTLDiagCat.map : (𝟙_ CircleCentralSelfDualityCat ⟶ 𝟙_ _) → (𝟙_ TLDiagCat ⟶ 𝟙_ _)) := by
  intro f
  let F := Functor.mapEnd (𝟙_ CircleCentralSelfDualityCat) toTLDiagCat
  let c : End (𝟙_ CircleCentralSelfDualityCat) :=
    .of (η_ generator generator ≫ ε_ generator generator)
  have hc : F c = End.of TLDiagCat.circle := End.ext toTLDiagCat_map_circle
  have hpow := congrArg End.asHom (map_pow F c (End.of f).asHom.diagram.circles)
  rw [hc] at hpow
  exact ⟨_, hpow.trans (congrArg End.asHom (TLDiagCat.end_zero_eq_circle_pow (End.of f))).symm⟩

end CircleCentralSelfDualityCat

end TauCeti
