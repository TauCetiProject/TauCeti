/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Group.Smooth
public import TauCeti.AlgebraicGeometry.Geometrically.Reduced
public import TauCeti.AlgebraicGeometry.GroupScheme.ClosedSubgroup.Criterion
public import TauCeti.AlgebraicGeometry.IdealSheaf.VanishingIdeal
public import TauCeti.AlgebraicGeometry.Morphisms.Thickening

/-!
# The reduced subgroup scheme over a perfect field

Let `G` be a group scheme over a perfect field `k`. Its reduction `G_red`, the closed subscheme
of `G` cut out by the nilradical, is a closed subgroup scheme of `G` with the same underlying
space. Over a perfect field the product `G_red ×_k G_red` is again reduced, so the multiplication
of `G` restricted to it factors through `G_red`, as do the unit and the inversion, whose sources
are reduced. No finiteness hypothesis on `G` is needed for this. When `G` is locally of finite
type, `G_red` is reduced and locally of finite type over a perfect field, hence geometrically
reduced, hence smooth; in particular a reduced group scheme locally of finite type over a perfect
field is smooth.

`G_red` is the largest reduced subgroup scheme of `G`: every homomorphism from a group scheme
with reduced underlying scheme to `G` factors uniquely through it.

Perfectness is needed: over an imperfect field the reduction of a group scheme need not be a
subgroup scheme, and a reduced group scheme of finite type need not be smooth (SGA 3,
Exp. VI_A, 1.3.2; Milne, Example 1.27).

## Main declarations

* `TauCeti.GroupScheme.reduced`: the reduced subgroup scheme `G_red` of `G`.
* `TauCeti.GroupScheme.reducedι`: its inclusion into `G`, a closed immersion which is a
  homeomorphism onto `G` (a thickening).
* `TauCeti.GroupScheme.reducedLift`: the factorization through `G_red` of a homomorphism from a
  group scheme with reduced underlying scheme.
* `TauCeti.GroupScheme.exists_reduced_subgroup`: for `G` locally of finite type, `G_red` is a
  smooth closed subgroup scheme of `G` with the same underlying space.
* `TauCeti.GroupScheme.smooth_of_isReduced`: a reduced group scheme locally of finite type over a
  perfect field is smooth.

## References

* M. Demazure, A. Grothendieck et al., *Schémas en groupes* (SGA 3), Exp. VI_A, 0.2 and 1.3.1.
* J. S. Milne, *Algebraic groups* (2017), Proposition 1.26 and Corollary 1.39.
* The Stacks Project, Tag 047R.
-/

public section

open CategoryTheory MonoidalCategory AlgebraicGeometry
open scoped MonObj

namespace TauCeti.GroupScheme

open TauCeti.AlgebraicGeometry

universe u

variable {k : Type u} [Field k] (G : Grp (Over (Spec (.of k))))

/-- The reduction `G_red` of a group scheme `G` over `k`: the closed subscheme of `G` cut out by
its nilradical, as a scheme over `k`. -/
@[expose] noncomputable def reducedOver : Over (Spec (.of k)) :=
  Over.mk (G.X.left.nilradical.subschemeι ≫ G.X.hom)

/-- The inclusion of the reduction `G_red` into `G`, over `k`. -/
noncomputable def reducedOverι : reducedOver G ⟶ G.X :=
  Over.homMk G.X.left.nilradical.subschemeι

@[simp]
theorem reducedOver_left : (reducedOver G).left = G.X.left.nilradical.subscheme :=
  (rfl)

@[simp]
theorem reducedOver_hom :
    (reducedOver G).hom = G.X.left.nilradical.subschemeι ≫ G.X.hom :=
  (rfl)

@[simp]
theorem reducedOverι_left : (reducedOverι G).left = G.X.left.nilradical.subschemeι :=
  (rfl)

instance : IsReduced (reducedOver G).left :=
  Scheme.isReduced_subscheme_nilradical G.X.left

instance : IsThickening (reducedOverι G).left :=
  IsThickening.subschemeι_nilradical G.X.left

instance : Mono (reducedOverι G) :=
  Over.mono_of_mono_left _

variable [PerfectField k]

/-- The fibre product `G_red ×_k G_red` is reduced, since `k` is perfect. -/
instance : IsReduced (reducedOver G ⊗ reducedOver G).left := by
  rw [Over.tensorObj_left]; infer_instance

/-- The group structure on `G_red`: the unit, multiplication and inversion of `G` factor through
the thickening `G_red ⟶ G`, since their sources `Spec k`, `G_red ×_k G_red` and `G_red` are
reduced. -/
noncomputable instance : GrpObj (reducedOver G) :=
  grpObjOfClosedImmersion (reducedOverι G)
    (have : IsReduced (𝟙_ (Over (Spec (.of k)))).left := by
      rw [Over.tensorUnit_left]; infer_instance
    IsThickening.ker_le_ker _ _)
    (IsThickening.ker_le_ker _ _) (IsThickening.ker_le_ker _ _)

instance : IsMonHom (reducedOverι G) :=
  isMonHom_grpObjOfClosedImmersion _ _ _ _

/-- The **reduced subgroup scheme** `G_red` of a group scheme `G` over a perfect field `k`: the
reduction of `G`, with the group law restricted from `G`. -/
@[expose] noncomputable def reduced : Grp (Over (Spec (.of k))) :=
  Grp.mk (reducedOver G)

@[simp]
theorem reduced_X : (reduced G).X = reducedOver G :=
  (rfl)

/-- The inclusion `G_red ⟶ G` of the reduced subgroup scheme, a homomorphism of group
schemes. -/
noncomputable def reducedι : reduced G ⟶ G :=
  Grp.ofHom (reducedOverι G)

@[simp]
theorem reducedι_hom_hom : (reducedι G).hom.hom = reducedOverι G :=
  (rfl)

instance : Mono (reducedι G) :=
  (Grp.forget _).mono_of_mono_map (inferInstanceAs (Mono (reducedOverι G)))

/-- The underlying scheme of `G_red` is reduced. -/
instance isReduced_reduced : IsReduced (reduced G).X.left :=
  inferInstanceAs (IsReduced (reducedOver G).left)

/-- The inclusion `G_red ⟶ G` is a thickening: a closed immersion which is a homeomorphism. -/
instance isThickening_reducedι : IsThickening (reducedι G).hom.hom.left :=
  inferInstanceAs (IsThickening (reducedOverι G).left)

/-- If `G` is locally of finite type over `k`, so is `G_red`. -/
instance locallyOfFiniteType_reduced [LocallyOfFiniteType G.X.hom] :
    LocallyOfFiniteType (reduced G).X.hom := by
  rw [reduced_X, reducedOver_hom]
  -- The goal still names its source `(reducedOver G).left`, which instance search does not unfold.
  exact inferInstanceAs (LocallyOfFiniteType (G.X.left.nilradical.subschemeι ≫ G.X.hom))

/-- A reduced group scheme locally of finite type over a perfect field is smooth (SGA 3,
Exp. VI_A, 1.3.1): over a perfect field it is geometrically reduced. -/
theorem smooth_of_isReduced (H : Grp (Over (Spec (.of k)))) [LocallyOfFiniteType H.X.hom]
    [IsReduced H.X.left] : Smooth H.X.hom := by
  -- `smooth_of_grpObj` asks for the `Over.mk H.X.hom` spelling of `H.X`.
  have : GrpObj (Over.mk H.X.hom) := inferInstanceAs (GrpObj H.X)
  exact smooth_of_grpObj H.X.hom

/-- If `G` is locally of finite type over `k`, then `G_red` is smooth over `k`. -/
instance smooth_reduced [LocallyOfFiniteType G.X.hom] : Smooth (reduced G).X.hom :=
  smooth_of_isReduced (reduced G)

/-- Over a perfect field, the reduced subscheme `G_red` of a group scheme `G` locally of finite
type is a closed subgroup scheme with the same underlying space, and it is smooth (SGA 3,
Exp. VI_A, 0.2 and 1.3.1). -/
theorem exists_reduced_subgroup [LocallyOfFiniteType G.X.hom] :
    ∃ (H : Grp (Over (Spec (.of k)))) (i : H ⟶ G),
      IsClosedImmersion ((Grp.forget _).map i).left ∧ Surjective ((Grp.forget _).map i).left ∧
        IsReduced H.X.left ∧ Smooth H.X.hom :=
  ⟨reduced G, reducedι G, inferInstanceAs (IsClosedImmersion (reducedOverι G).left),
    inferInstanceAs (Surjective (reducedOverι G).left), inferInstance, inferInstance⟩

section Lift

variable {G} {H : Grp (Over (Spec (.of k)))} [IsReduced H.X.left]

/-- A homomorphism `f : H ⟶ G` from a group scheme with reduced underlying scheme factors
through the reduced subgroup scheme `G_red`. -/
noncomputable def reducedLift (f : H ⟶ G) : H ⟶ reduced G :=
  haveI : IsMonHom (closedImmersionOverLift (reducedOverι G) f.hom.hom
      (IsThickening.ker_le_ker (reducedOverι G).left f.hom.hom.left)) := by
    constructor <;> rw [← cancel_mono (reducedOverι G)] <;> simp
  Grp.ofHom (closedImmersionOverLift (reducedOverι G) f.hom.hom
    (IsThickening.ker_le_ker (reducedOverι G).left f.hom.hom.left))

@[reassoc (attr := simp)]
theorem reducedLift_reducedι (f : H ⟶ G) : reducedLift f ≫ reducedι G = f := by
  ext1
  rw [Grp.comp_hom_hom, reducedι_hom_hom]
  exact closedImmersionOverLift_comp (reducedOverι G) f.hom.hom _

/-- The factorization through `G_red` is unique. -/
theorem eq_reducedLift_iff (f : H ⟶ G) (g : H ⟶ reduced G) :
    g = reducedLift f ↔ g ≫ reducedι G = f :=
  ⟨fun h ↦ h ▸ reducedLift_reducedι f, fun h ↦ (cancel_mono (reducedι G)).mp (by simp [h])⟩

end Lift

/-- A group scheme with reduced underlying scheme is its own reduced subgroup scheme: the
inclusion `G_red ⟶ G` is an isomorphism, with inverse the factorization of the identity. -/
instance isIso_reducedι [IsReduced G.X.left] : IsIso (reducedι G) :=
  ⟨reducedLift (𝟙 G), (cancel_mono (reducedι G)).mp (by simp), reducedLift_reducedι _⟩

end TauCeti.GroupScheme
