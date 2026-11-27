/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import TauCeti.AlgebraicGeometry.Geometrically.Reduced
public import TauCeti.AlgebraicGeometry.GroupAction.LocallyClosed
public import TauCeti.CategoryTheory.Monoidal.Mod.Algebra
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import TauCeti.AlgebraicGeometry.Morphisms.Flat.Descent
import TauCeti.AlgebraicGeometry.Morphisms.Flat.Equivariance
import TauCeti.AlgebraicGeometry.Pullback.Over
import TauCeti.CategoryTheory.Comma.Over
import TauCeti.CategoryTheory.Monoidal.Grp.Translation

/-!
# Surjective homomorphisms of algebraic groups are flat

Let `f : G ⟶ H` be a homomorphism of group schemes of finite type over a field `k`, with `H`
geometrically reduced. If `f` is surjective, then it is faithfully flat. No reducedness,
smoothness, connectedness or commutativity of `G` is needed, and `G` and `H` need not have the
same dimension.

Over an algebraically closed field the proof is the translation argument. Through `f`, the group
`G` acts on `H` by left multiplication (`CategoryTheory.Mod.comapRegular`), and the orbit
morphism of the unit point is `f` (`TauCeti.GroupScheme.orbitMap_one_eq`). Left translation by a
rational point `g` of `G` commutes with `f` and with translation by `f(g)` on `H`. Since `f` is
surjective, every point of `H` lies in the orbit of the unit, so the translations by rational
points of `G` act transitively on the closed points of `H`. Generic flatness gives a nonempty open
subset of `H` over which `f` is flat, and its translates cover `H`
(`AlgebraicGeometry.Scheme.Hom.flat_of_transitive_closedPoints_of_finiteType`). Over a general
field, the base change of `f` to an algebraic closure `k^alg` is again a surjective homomorphism
with geometrically reduced target, and flatness descends along the faithfully flat projection
from the base change.

## Main results

In the namespace `TauCeti.GroupScheme`:

* `orbitMap_one_eq`: for the action of `G` on `H` through `f`, the orbit morphism of the unit
  point is `f`.
* `flat_of_surjective_of_isAlgClosed`: the case of an algebraically closed field, where a reduced
  target suffices.
* `flat_of_surjective`: a surjective homomorphism of group schemes of finite type over a field,
  with geometrically reduced target, is flat.
* `faithfullyFlat_of_surjective`: such a homomorphism is flat and surjective, that is, faithfully
  flat.

## References

* J. S. Milne, *Algebraic Groups* (2017), Proposition 1.65(a), flatness of equivariant
  morphisms.
* The Stacks Project, Proposition 29.28.1 (Tag 052A), generic flatness, and Lemma 35.23.17
  (Tag 02L2), descent of flatness.
-/

public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj

namespace TauCeti.GroupScheme

universe u

variable {k : Type u} [Field k] {G H : Over (Spec (.of k))} [GrpObj G] [GrpObj H]

section Action

/-- For the action of `G` on `H` by left multiplication through `f` (`Mod.comapRegular f`), the
orbit morphism of the unit point is `f`. -/
theorem orbitMap_one_eq (f : G ⟶ H) [IsMonHom f] :
    letI : ModObj G H := (Mod.comapRegular f).mod
    orbitMap G (1 : 𝟙_ (Over (Spec (.of k))) ⟶ H) = f := by
  let : ModObj G H := (Mod.comapRegular f).mod
  rw [← Category.id_comp (orbitMap G _), comp_orbitMap, Hom.smul_def]
  change lift (𝟙 G) (toUnit G ≫ η[H]) ≫ f ▷ H ≫ μ[H] = f
  rw [lift_whiskerRight_assoc, Category.id_comp, ← Hom.mul_def, ← Hom.one_def, _root_.mul_one]

end Action

section AlgClosed

variable [IsAlgClosed k] (f : G ⟶ H) [IsMonHom f]

/-- **Surjective homomorphisms of algebraic groups are flat**, over an algebraically closed
field: a surjective homomorphism of group schemes of finite type with reduced target is flat. -/
theorem flat_of_surjective_of_isAlgClosed [LocallyOfFiniteType G.hom] [CompactSpace G.left]
    [LocallyOfFiniteType H.hom] [IsReduced H.left] [Surjective f.left] : Flat f.left := by
  let : ModObj G H := (Mod.comapRegular f).mod
  have : JacobsonSpace H.left := LocallyOfFiniteType.jacobsonSpace H.hom
  have : IsLocallyNoetherian H.left := LocallyOfFiniteType.isLocallyNoetherian H.hom
  have : LocallyOfFiniteType f.left := by
    have : LocallyOfFiniteType (f.left ≫ H.hom) := by rw [Over.w]; infer_instance
    exact locallyOfFiniteType_of_comp f.left H.hom
  have : QuasiCompact f.left := inferInstance
  have hcomm (g : 𝟙_ (Over (Spec (.of k))) ⟶ G) :
      (leftTranslation g).hom.left ≫ f.left = f.left ≫ (translation H g).hom.left := by
    have := congrArg Over.Hom.left (leftTranslation_hom_orbitMap g (1 : _ ⟶ H))
    simpa only [orbitMap_one_eq, Over.comp_left] using this
  have hrange : Set.range (𝟙 H.left) ⊆ SchemeAction.orbit G (1 : _ ⟶ H) := by
    rintro _ ⟨y, rfl⟩
    rw [SchemeAction.orbit_def, orbitMap_one_eq]
    exact Surjective.surj y
  exact f.left.flat_of_transitive_closedPoints_of_finiteType
    (fun g ↦ (Over.forget _).mapIso (leftTranslation g))
    (fun g ↦ (Over.forget _).mapIso (translation H g)) hcomm
    (fun _ _ hy hz ↦ SchemeAction.exists_eq_of_equivariant_of_range_subset_orbit G
      (1 : _ ⟶ H) (𝟙 H.left) hrange (fun g ↦ (Over.forget _).mapIso (translation H g))
      (fun g ↦ by simp) hy hz)

end AlgClosed

variable (f : G ⟶ H) [IsMonHom f]

/-- **Surjective homomorphisms of algebraic groups are flat.** Over any field, a surjective
homomorphism of group schemes of finite type with geometrically reduced target is flat. -/
theorem flat_of_surjective [LocallyOfFiniteType G.hom] [CompactSpace G.left]
    [LocallyOfFiniteType H.hom] [GeometricallyReduced H.hom] [Surjective f.left] :
    Flat f.left := by
  let φ := Spec.algebraMap k (AlgebraicClosure k)
  have h := Over.isPullback_pullback_map_left φ f
  have : Surjective ((Over.pullback φ).map f).left :=
    MorphismProperty.of_isPullback h.flip ‹_›
  exact MorphismProperty.of_isPullback_of_surjective_of_flat_of_quasiCompact h
    (flat_of_surjective_of_isAlgClosed ((Over.pullback φ).map f))

/-- **Surjective homomorphisms of algebraic groups are faithfully flat.** Over any field, a
surjective homomorphism of group schemes of finite type with geometrically reduced target is flat
and surjective. -/
theorem faithfullyFlat_of_surjective [LocallyOfFiniteType G.hom] [CompactSpace G.left]
    [LocallyOfFiniteType H.hom] [GeometricallyReduced H.hom] [Surjective f.left] :
    Flat f.left ∧ Surjective f.left :=
  ⟨flat_of_surjective f, ‹_›⟩

end TauCeti.GroupScheme
