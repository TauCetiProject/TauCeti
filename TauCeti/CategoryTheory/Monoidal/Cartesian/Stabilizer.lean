/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.GroupTheory.GroupAction.Defs
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import TauCeti.CategoryTheory.Monoidal.Cartesian.Action
import Mathlib.GroupTheory.GroupAction.Basic

/-!
# Fibers of orbit morphisms and stabilizers of global points

Let a monoid object `G` act on `X` in a cartesian monoidal category, and let `x` be a global
point of `X`. For a global point `y`, the fiber of the orbit morphism `G ⟶ X`, `g ↦ g • x`,
over `y` is the pullback of the orbit morphism along `y`. A morphism `g : T ⟶ G` factors
through it exactly when `g • x = y` as `T`-points, and the factorization is unique.

When `G` is a group object, the stabilizer of `x` is the fiber over `x` itself. Its `T`-points
are the stabilizer, in the group `T ⟶ G`, of the point `x` restricted to `T`. These subgroups
form a presheaf of groups
represented by the stabilizer, so Mathlib's `GrpObj.ofRepresentableBy` makes the stabilizer
a group object. Mathlib's `yonedaGrpObjIsoOfRepresentableBy` supplies its group equivalence
on each test object; its inclusion into `G` is a monoid morphism. The stabilizer is also the
equalizer of the orbit morphism and the constant morphism at `x`. The orbit morphism is
`TauCeti.orbitMap`.

The fibers over the points of the orbit are translates of the stabilizer: left translation by
`h⁻¹` identifies the fiber over `h • x` with the stabilizer of `x`. Conjugation by `h`
identifies the stabilizers of `h • x` and of `x`.

The stabilizer is characterized through all test objects `T`, not only through global points.
For group schemes over a base it is therefore the scheme-theoretic stabilizer, which can be
nonreduced, rather than a set of rational points.

## Main declarations

* `TauCeti.stabilizerPoints`: the stabilizer of `x` in the group of `T`-points of `G`.
* `TauCeti.orbitFiber`: the fiber of the orbit morphism of `x` over a global point `y`.
* `TauCeti.stabilizer`: the stabilizer of `x`, the fiber of its orbit morphism over `x`.
* `TauCeti.stabilizer.instGrpObj`: the group-object structure on the stabilizer.
* `TauCeti.stabilizer.homMulEquiv`: `T`-points of the stabilizer are the stabilizing
  `T`-points of `G`, as groups.
* `TauCeti.stabilizer.isoEqualizer`: the stabilizer is the equalizer of the orbit morphism and
  the constant morphism at `x`.
* `TauCeti.stabilizer.fiberSmulIso`: the fiber over `h • x` is isomorphic to the stabilizer of
  `x`, by left translation by `h⁻¹`.
* `TauCeti.stabilizer.smulIso`: the stabilizers of `x` and of `h • x` are isomorphic as group
  objects, by conjugation with `h`.

## References

* J. S. Milne, *Algebraic Groups* (2017), for group schemes and their subgroups described
  through functors of points, the setting in which this stabilizer is defined.
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj ModObj Opposite

namespace TauCeti

universe u v

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
variable (G : C) {X : C}

section GroupPoints

variable [GrpObj G] [ModObj G X] (x : 𝟙_ C ⟶ X)

/-- The stabilizer of the global point `x`, restricted to `T`, in the group of `T`-points
of `G`. -/
abbrev stabilizerPoints (T : C) : Subgroup (T ⟶ G) :=
  MulAction.stabilizer (T ⟶ G) (toUnit T ≫ x)

/-- A `T`-point of `G` stabilizes `x` exactly when its composite with the orbit morphism is
the constant `T`-point at `x`. -/
theorem mem_stabilizerPoints_iff {T : C} (g : T ⟶ G) :
    g ∈ stabilizerPoints G x T ↔ g ≫ orbitMap G x = toUnit T ≫ x := by
  rw [MulAction.mem_stabilizer_iff, comp_orbitMap]

/-- Restricting a stabilizing point along any morphism gives a stabilizing point. -/
theorem comp_mem_stabilizerPoints {T T' : C} (f : T' ⟶ T) {g : T ⟶ G}
    (hg : g ∈ stabilizerPoints G x T) : f ≫ g ∈ stabilizerPoints G x T' := by
  rw [mem_stabilizerPoints_iff] at hg ⊢
  rw [Category.assoc, hg, ← Category.assoc, toUnit_unique (f ≫ toUnit T) (toUnit T')]

/-- A `T`-point sending `x` to `h • x`, translated on the left by `h⁻¹`, stabilizes `x`. -/
theorem inv_mul_mem_stabilizerPoints (h : 𝟙_ C ⟶ G) {T : C} {g : T ⟶ G}
    (hg : g ≫ orbitMap G x = toUnit T ≫ (h • x)) :
    (toUnit T ≫ h)⁻¹ * g ∈ stabilizerPoints G x T := by
  rw [comp_orbitMap, comp_smul] at hg
  simp only [MulAction.mem_stabilizer_iff, SemigroupAction.mul_smul, hg, inv_smul_smul]

/-- A stabilizing `T`-point, translated on the left by `h`, sends `x` to `h • x`. -/
theorem mul_comp_orbitMap_of_mem (h : 𝟙_ C ⟶ G) {T : C} {g : T ⟶ G}
    (hg : g ∈ stabilizerPoints G x T) :
    ((toUnit T ≫ h) * g) ≫ orbitMap G x = toUnit T ≫ (h • x) := by
  rw [MulAction.mem_stabilizer_iff] at hg
  rw [comp_orbitMap, comp_smul, SemigroupAction.mul_smul, hg]

/-- Conjugating by a translate: a `T`-point stabilizing `h • x` conjugates to one
stabilizing `x`. -/
theorem inv_conj_mem_stabilizerPoints_of_mem_smul (h : 𝟙_ C ⟶ G) {T : C} {g : T ⟶ G}
    (hg : g ∈ stabilizerPoints G (h • x) T) :
    (toUnit T ≫ h)⁻¹ * g * (toUnit T ≫ h) ∈ stabilizerPoints G x T := by
  simpa only [MulAction.stabilizerEquivStabilizer_symm_apply, MulAut.conj_apply, inv_inv] using
    ((MulAction.stabilizerEquivStabilizer (comp_smul (toUnit T) h x)).symm ⟨g, hg⟩).property

/-- Conjugating the other way: a `T`-point stabilizing `x` conjugates to one stabilizing
`h • x`. -/
theorem conj_mem_stabilizerPoints_smul (h : 𝟙_ C ⟶ G) {T : C} {g : T ⟶ G}
    (hg : g ∈ stabilizerPoints G x T) :
    (toUnit T ≫ h) * g * (toUnit T ≫ h)⁻¹ ∈ stabilizerPoints G (h • x) T := by
  simpa only [MulAction.stabilizerEquivStabilizer_apply, MulAut.conj_apply] using
    ((MulAction.stabilizerEquivStabilizer (comp_smul (toUnit T) h x)) ⟨g, hg⟩).property

end GroupPoints

section Fibers

variable [MonObj G] [ModObj G X] (x y : 𝟙_ C ⟶ X) [HasPullback (orbitMap G x) y]

/-- The fiber of the orbit morphism of `x` over the global point `y`. -/
def orbitFiber : C :=
  pullback (orbitMap G x) y

namespace orbitFiber

/-- The inclusion of the fiber into the acting monoid. -/
def incl : orbitFiber G x y ⟶ G :=
  pullback.fst (orbitMap G x) y

/-- The fiber maps to `y` under the orbit morphism. -/
@[reassoc]
theorem incl_orbitMap : incl G x y ≫ orbitMap G x = toUnit (orbitFiber G x y) ≫ y :=
  (pullback.condition (f := orbitMap G x) (g := y)).trans <|
    congrArg (· ≫ y) (toUnit_unique _ _)

/-- The defining pullback square of an orbit fibre, with its canonical map to the unit. -/
theorem isPullback : IsPullback (incl G x y) (toUnit (orbitFiber G x y)) (orbitMap G x) y := by
  have he : pullback.snd (orbitMap G x) y = toUnit (orbitFiber G x y) := toUnit_unique _ _
  simpa only [orbitFiber, incl, he] using IsPullback.of_hasPullback (orbitMap G x) y

/-- The inclusion acts on the base point as the defining point of the fiber. -/
@[simp]
theorem incl_smul :
    incl G x y • (toUnit (orbitFiber G x y) ≫ x) = toUnit (orbitFiber G x y) ≫ y := by
  rw [← comp_orbitMap, incl_orbitMap]

/-- Morphisms into the fiber agree when their composites with the inclusion agree. -/
@[ext]
theorem hom_ext {T : C} {a b : T ⟶ orbitFiber G x y} (hab : a ≫ incl G x y = b ≫ incl G x y) :
    a = b :=
  pullback.hom_ext hab (toUnit_unique _ _)

instance : Mono (incl G x y) :=
  ⟨fun _ _ ↦ hom_ext G x y⟩

/-- Factorization through the fiber of a `T`-point of `G` sending `x` to `y`. -/
def lift {T : C} (g : T ⟶ G) (hg : g ≫ orbitMap G x = toUnit T ≫ y) :
    T ⟶ orbitFiber G x y :=
  pullback.lift g (toUnit T) hg

@[reassoc (attr := simp)]
theorem lift_incl {T : C} (g : T ⟶ G) (hg : g ≫ orbitMap G x = toUnit T ≫ y) :
    orbitFiber.lift G x y g hg ≫ incl G x y = g :=
  pullback.lift_fst _ _ _

/-- A `T`-point of `G` factors through the fiber over `y` exactly when it sends `x` to `y`. -/
theorem exists_lift_iff {T : C} (g : T ⟶ G) :
    (∃ s : T ⟶ orbitFiber G x y, s ≫ incl G x y = g) ↔
      g ≫ orbitMap G x = toUnit T ≫ y := by
  constructor
  · rintro ⟨s, rfl⟩
    rw [Category.assoc, incl_orbitMap, ← Category.assoc, toUnit_unique (s ≫ toUnit _)]
  · exact fun hg ↦ ⟨orbitFiber.lift G x y g hg, lift_incl G x y g hg⟩

end orbitFiber

end Fibers

variable [GrpObj G] [ModObj G X] (x : 𝟙_ C ⟶ X)

variable [HasPullback (orbitMap G x) x]

/-- The stabilizer of a global point: the fiber of its orbit morphism over the point itself. -/
abbrev stabilizer : C :=
  orbitFiber G x x

namespace stabilizer

/-- The inclusion of the stabilizer into the group. -/
abbrev incl : stabilizer G x ⟶ G :=
  orbitFiber.incl G x x

/-- The inclusion of the stabilizer is a stabilizing point of `G`. -/
theorem incl_mem : incl G x ∈ stabilizerPoints G x (stabilizer G x) :=
  (mem_stabilizerPoints_iff G x _).2 (orbitFiber.incl_orbitMap G x x)

/-- Factorization of a stabilizing `T`-point of `G` through the stabilizer. -/
def lift {T : C} (g : T ⟶ G) (hg : g ∈ stabilizerPoints G x T) : T ⟶ stabilizer G x :=
  orbitFiber.lift G x x g ((mem_stabilizerPoints_iff G x g).1 hg)

@[reassoc (attr := simp)]
theorem lift_incl {T : C} (g : T ⟶ G) (hg : g ∈ stabilizerPoints G x T) :
    stabilizer.lift G x g hg ≫ incl G x = g :=
  orbitFiber.lift_incl _ _ _ _ _

/-- A `T`-point of `G` factors through the stabilizer exactly when it stabilizes `x`. -/
theorem exists_lift_iff {T : C} (g : T ⟶ G) :
    (∃ s : T ⟶ stabilizer G x, s ≫ incl G x = g) ↔ g ∈ stabilizerPoints G x T :=
  (orbitFiber.exists_lift_iff G x x g).trans (mem_stabilizerPoints_iff G x g).symm

/-- The presheaf of groups of stabilizing points of `G`. -/
def pointsPresheaf : Cᵒᵖ ⥤ GrpCat.{v} where
  obj T := GrpCat.of (stabilizerPoints G x T.unop)
  map f := GrpCat.ofHom
    { toFun := fun g ↦ ⟨f.unop ≫ g.1, comp_mem_stabilizerPoints G x f.unop g.2⟩
      map_one' := Subtype.ext (MonObj.comp_one _)
      map_mul' := fun g h ↦ Subtype.ext (MonObj.comp_mul _ _ _) }

/-- The stabilizer represents the presheaf of stabilizing points. -/
def representableBy : (pointsPresheaf G x ⋙ forget _).RepresentableBy (stabilizer G x) where
  homEquiv {T} :=
    { toFun := fun s ↦ ⟨s ≫ incl G x, comp_mem_stabilizerPoints G x s (incl_mem G x)⟩
      invFun := fun g ↦ stabilizer.lift G x g.1 g.2
      left_inv := fun s ↦ by
        apply (cancel_mono (incl G x)).1
        simp
      right_inv := fun g ↦ Subtype.ext (lift_incl G x g.1 g.2) }
  homEquiv_comp f g := Subtype.ext (Category.assoc _ _ _)

/-- The stabilizer is a group object. -/
instance instGrpObj : GrpObj (stabilizer G x) :=
  GrpObj.ofRepresentableBy (stabilizer G x) (pointsPresheaf G x) (representableBy G x)

/-- The inclusion of the stabilizer is a monoid morphism. -/
instance : IsMonHom (incl G x) where
  one_hom := by
    -- The unit of `GrpObj.ofRepresentableBy` is, by construction, the morphism representing
    -- the unit of the presheaf; `change` exposes that construction.
    change (representableBy G x).homEquiv.symm 1 ≫ incl G x = _
    exact congrArg Subtype.val ((representableBy G x).homEquiv.apply_symm_apply 1) |>.trans
      (MonObj.one_eq_one G).symm
  mul_hom := by
    -- Likewise the multiplication represents the product of the two projections.
    change (representableBy G x).homEquiv.symm
        ((representableBy G x).homEquiv (fst _ _) * (representableBy G x).homEquiv (snd _ _)) ≫
      incl G x = _
    refine (congrArg Subtype.val ((representableBy G x).homEquiv.apply_symm_apply _)).trans ?_
    -- The product in the presheaf is computed in `T ⟶ G`, on the composites with `incl`.
    change fst _ _ ≫ incl G x * snd _ _ ≫ incl G x = _
    rw [Hom.mul_def]
    congr 1
    ext <;> simp

/-- The `T`-points of the stabilizer are the stabilizing `T`-points of `G`, as groups. -/
def homMulEquiv (T : C) : (T ⟶ stabilizer G x) ≃* stabilizerPoints G x T :=
  ((yonedaGrpObjIsoOfRepresentableBy (stabilizer G x) (pointsPresheaf G x)
    (representableBy G x)).app (op T)).groupIsoToMulEquiv

@[simp]
theorem homMulEquiv_apply_coe {T : C} (s : T ⟶ stabilizer G x) :
    (homMulEquiv G x T s : T ⟶ G) = s ≫ incl G x :=
  (rfl)

section Equalizer

variable [HasEqualizer (orbitMap G x) (toUnit G ≫ x)]

/-- The stabilizer is the equalizer of the orbit morphism and the constant morphism at the
point. -/
def isoEqualizer : stabilizer G x ≅ equalizer (orbitMap G x) (toUnit G ≫ x) where
  hom := equalizer.lift (incl G x) <| by
    rw [orbitFiber.incl_orbitMap, ← Category.assoc, toUnit_unique (incl G x ≫ toUnit G)]
  inv := stabilizer.lift G x (equalizer.ι _ _) <| by
    rw [mem_stabilizerPoints_iff, equalizer.condition, ← Category.assoc,
      toUnit_unique (equalizer.ι _ _ ≫ toUnit G)]
  hom_inv_id := by
    apply (cancel_mono (incl G x)).1
    simp
  inv_hom_id := by
    apply (cancel_mono (equalizer.ι (orbitMap G x) (toUnit G ≫ x))).1
    simp

@[reassoc (attr := simp)]
theorem isoEqualizer_hom_ι :
    (isoEqualizer G x).hom ≫ equalizer.ι (orbitMap G x) (toUnit G ≫ x) = incl G x := by
  simp [isoEqualizer]

end Equalizer

section Translation

variable (h : 𝟙_ C ⟶ G)

/-- The fiber of the orbit morphism over `h • x` is the translate of the stabilizer by `h`:
left translation by `h⁻¹` identifies it with the stabilizer of `x`. -/
def fiberSmulIso [HasPullback (orbitMap G x) (h • x)] :
    orbitFiber G x (h • x) ≅ stabilizer G x where
  hom := stabilizer.lift G x _
    (inv_mul_mem_stabilizerPoints G x h (orbitFiber.incl_orbitMap G x (h • x)))
  inv := orbitFiber.lift G x (h • x) _ (mul_comp_orbitMap_of_mem G x h (incl_mem G x))
  hom_inv_id := by
    apply (cancel_mono (orbitFiber.incl G x (h • x))).1
    simp [MonObj.comp_mul]
  inv_hom_id := by
    apply (cancel_mono (incl G x)).1
    simp [MonObj.comp_mul, GrpObj.comp_inv]

@[reassoc (attr := simp)]
theorem fiberSmulIso_hom_incl [HasPullback (orbitMap G x) (h • x)] :
    (fiberSmulIso G x h).hom ≫ incl G x =
      (toUnit _ ≫ h)⁻¹ * orbitFiber.incl G x (h • x) := by
  simp [fiberSmulIso]

@[reassoc (attr := simp)]
theorem fiberSmulIso_inv_incl [HasPullback (orbitMap G x) (h • x)] :
    (fiberSmulIso G x h).inv ≫ orbitFiber.incl G x (h • x) =
      (toUnit _ ≫ h) * incl G x := by
  simp [fiberSmulIso]

variable [HasPullback (orbitMap G (h • x)) (h • x)]

/-- The forward conjugation map, before proving its inverse laws. -/
private def conjugationHom : stabilizer G (h • x) ⟶ stabilizer G x :=
  stabilizer.lift G x _
    (inv_conj_mem_stabilizerPoints_of_mem_smul G x h (incl_mem G (h • x)))

/-- The inverse conjugation map, before proving its inverse laws. -/
private def conjugationInv : stabilizer G x ⟶ stabilizer G (h • x) :=
  stabilizer.lift G (h • x) _
    (conj_mem_stabilizerPoints_smul G x h (incl_mem G x))

/-- Restriction of the forward map is conjugation by the inverse restricted point. -/
private theorem comp_conjugationHom_incl {T : C} (s : T ⟶ stabilizer G (h • x)) :
    s ≫ conjugationHom G x h ≫ incl G x =
      (MulAut.conj (toUnit T ≫ h)).symm (s ≫ incl G (h • x)) := by
  simp [conjugationHom, MulAut.conj_symm_apply, MonObj.comp_mul, GrpObj.comp_inv]

/-- Restriction of the inverse map is conjugation by the restricted point. -/
private theorem comp_conjugationInv_incl {T : C} (s : T ⟶ stabilizer G x) :
    s ≫ conjugationInv G x h ≫ incl G (h • x) =
      (MulAut.conj (toUnit T ≫ h)) (s ≫ incl G x) := by
  simp [conjugationInv, MulAut.conj_apply, MonObj.comp_mul, GrpObj.comp_inv]

private theorem conjugationHom_incl :
    conjugationHom G x h ≫ incl G x =
      (MulAut.conj (toUnit (stabilizer G (h • x)) ≫ h)).symm (incl G (h • x)) := by
  simpa using comp_conjugationHom_incl G x h (𝟙 _)

private theorem conjugationInv_incl :
    conjugationInv G x h ≫ incl G (h • x) =
      (MulAut.conj (toUnit (stabilizer G x) ≫ h)) (incl G x) := by
  simpa using comp_conjugationInv_incl G x h (𝟙 _)

/-- The stabilizers of `x` and of its translate `h • x` are isomorphic, by conjugation with
`h`: a point `g` stabilizing `h • x` corresponds to `h⁻¹ * g * h`, which stabilizes `x`. -/
def smulIso : stabilizer G (h • x) ≅ stabilizer G x where
  hom := conjugationHom G x h
  inv := conjugationInv G x h
  hom_inv_id := by
    apply (cancel_mono (incl G (h • x))).1
    rw [Category.assoc, comp_conjugationInv_incl, conjugationHom_incl, Category.id_comp]
    exact (MulAut.conj (toUnit (stabilizer G (h • x)) ≫ h)).apply_symm_apply _
  inv_hom_id := by
    apply (cancel_mono (incl G x)).1
    rw [Category.assoc, comp_conjugationHom_incl, conjugationInv_incl, Category.id_comp]
    exact (MulAut.conj (toUnit (stabilizer G x) ≫ h)).symm_apply_apply _

@[reassoc (attr := simp)]
theorem smulIso_hom_incl :
    (smulIso G x h).hom ≫ incl G x =
      (toUnit _ ≫ h)⁻¹ * incl G (h • x) * (toUnit _ ≫ h) := by
  simpa only [smulIso, MulAut.conj_symm_apply] using conjugationHom_incl G x h

@[reassoc (attr := simp)]
theorem smulIso_inv_incl :
    (smulIso G x h).inv ≫ incl G (h • x) =
      (toUnit _ ≫ h) * incl G x * (toUnit _ ≫ h)⁻¹ := by
  simpa only [smulIso, MulAut.conj_apply] using conjugationInv_incl G x h

/-- On arbitrary test-object points, the forward map conjugates by the inverse of `h`. -/
theorem comp_smulIso_hom_incl {T : C} (s : T ⟶ stabilizer G (h • x)) :
    s ≫ (smulIso G x h).hom ≫ incl G x =
      (toUnit T ≫ h)⁻¹ * (s ≫ incl G (h • x)) * (toUnit T ≫ h) := by
  simpa only [smulIso, MulAut.conj_symm_apply] using comp_conjugationHom_incl G x h s

/-- On arbitrary test-object points, the inverse map conjugates by `h`. -/
theorem comp_smulIso_inv_incl {T : C} (s : T ⟶ stabilizer G x) :
    s ≫ (smulIso G x h).inv ≫ incl G (h • x) =
      (toUnit T ≫ h) * (s ≫ incl G x) * (toUnit T ≫ h)⁻¹ := by
  simpa only [smulIso, MulAut.conj_apply] using comp_conjugationInv_incl G x h s

/-- Composing with the conjugation isomorphism preserves products of `T`-points. -/
theorem mul_comp_smulIso_hom {T : C} (s t : T ⟶ stabilizer G (h • x)) :
    (s * t) ≫ (smulIso G x h).hom = s ≫ (smulIso G x h).hom * t ≫ (smulIso G x h).hom := by
  apply (cancel_mono (incl G x)).1
  -- Expose the isomorphism's forward morphism as `conjugationHom`, so its pointwise
  -- conjugation formula applies to the composites with the inclusion.
  change ((s * t) ≫ conjugationHom G x h) ≫ incl G x =
    (s ≫ conjugationHom G x h * t ≫ conjugationHom G x h) ≫ incl G x
  simp only [Category.assoc, comp_conjugationHom_incl, MonObj.mul_comp]
  exact (MulAut.conj (toUnit T ≫ h)).symm.map_mul _ _

/-- Conjugation is a morphism of group objects. Its inverse is one too, by Mathlib's instance
for inverses of monoid isomorphisms. -/
instance : IsMonHom (smulIso G x h).hom where
  one_hom := by
    rw [MonObj.one_eq_one, MonObj.one_eq_one]
    apply (cancel_mono (incl G x)).1
    -- Expose `smulIso`'s forward morphism as `conjugationHom`; after inclusion,
    -- its unit equation is the bundled conjugation automorphism's `map_one` law.
    change (1 ≫ conjugationHom G x h) ≫ incl G x = 1 ≫ incl G x
    simp only [Category.assoc, comp_conjugationHom_incl, MonObj.one_comp]
    exact (MulAut.conj (toUnit (𝟙_ C) ≫ h)).symm.map_one
  mul_hom := by
    rw [MonObj.mul_eq_mul, MonObj.mul_eq_mul, mul_comp_smulIso_hom, MonObj.comp_mul,
      tensorHom_fst, tensorHom_snd]

end Translation

end stabilizer

end TauCeti
