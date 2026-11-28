/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import TauCeti.AlgebraicGeometry.Geometrically.Reduced
public import TauCeti.AlgebraicGeometry.GroupAction.LocallyClosed
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import TauCeti.AlgebraicGeometry.Morphisms.Flat.Descent
import TauCeti.AlgebraicGeometry.Morphisms.Flat.Equivariance
import TauCeti.AlgebraicGeometry.Morphisms.Flat.Fiber
import TauCeti.AlgebraicGeometry.Pullback.Over
import TauCeti.CategoryTheory.Comma.Over
import TauCeti.CategoryTheory.Monoidal.Cartesian.ComapRegular
import TauCeti.CategoryTheory.Monoidal.Grp.Translation

/-!
# Surjective homomorphisms of algebraic groups are flat

Let `f : G ⟶ H` be a finite-type homomorphism of group schemes over a field `k`, with `H`
geometrically reduced and locally of finite type over `k`. If `f` is surjective, then it is
faithfully flat. The result allows arbitrary dimensions and needs no reducedness, smoothness,
connectedness or commutativity of `G`.

Over an algebraically closed field the proof is the translation argument. Through `f`, the group
`G` acts on `H` by left multiplication (`CategoryTheory.Mod.comapRegular`), and the orbit
morphism of the unit point is `f` (`TauCeti.orbitMap_one_comapRegular`). Left translation by a
rational point `g` of `G` commutes with `f` and with translation by `f(g)` on `H`. Since `f` is
surjective, every point of `H` lies in the orbit of the unit, so the translations by rational
points of `G` act transitively on the closed points of `H`. Generic flatness gives a nonempty open
subset of `H` over which `f` is flat, and its translates cover `H`
(`AlgebraicGeometry.Scheme.Hom.flat_of_transitive_closedPoints_of_finiteType`). Over a general
field, the base change of `f` to an algebraic closure `k^alg` is again a surjective homomorphism
with geometrically reduced target, and flatness descends along the faithfully flat projection
from the base change.

Over an arbitrary base, a finite, locally finitely presented surjective homomorphism is flat
by the fibrewise criterion when the source is flat and the target is geometrically reduced
and locally of finite type over the base.

## Main results

In the namespace `TauCeti.GroupScheme`:

* `flat_of_surjective_of_isAlgClosed`: the case of an algebraically closed field, where a reduced
  target suffices.
* `flat_of_surjective`: a surjective finite-type homomorphism over a field, with geometrically
  reduced and locally finite-type target, is flat, hence faithfully flat.

`CategoryTheory.Over.Hom.flat_left_of_finite_of_surjective` is the arbitrary-base result.

## References

* J. S. Milne, *Algebraic Groups* (2017), Proposition 1.65(a), flatness of equivariant
  morphisms.
* The Stacks Project, Tag 0529, generic flatness over a reduced locally Noetherian base, and
  Lemma 35.23.17 (Tag 02L2), descent of flatness.
-/

public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj

namespace TauCeti.GroupScheme

universe u

variable {k : Type u} [Field k] {G H : Over (Spec (.of k))} [GrpObj G] [GrpObj H]

section AlgClosed

variable [IsAlgClosed k] (f : G ⟶ H) [IsMonHom f]

/-- **Surjective homomorphisms of algebraic groups are flat**, over an algebraically closed
field: a surjective finite-type homomorphism with reduced, locally finite-type target is flat. -/
theorem flat_of_surjective_of_isAlgClosed [QuasiCompact f.left] [LocallyOfFiniteType f.left]
    [LocallyOfFiniteType H.hom] [IsReduced H.left] [Surjective f.left] : Flat f.left := by
  let : ModObj G H := (Mod.comapRegular f).mod
  have : JacobsonSpace H.left := LocallyOfFiniteType.jacobsonSpace H.hom
  have : IsLocallyNoetherian H.left := LocallyOfFiniteType.isLocallyNoetherian H.hom
  have : LocallyOfFiniteType G.hom := by
    rw [← Over.w f]
    infer_instance
  have hcomm (g : 𝟙_ (Over (Spec (.of k))) ⟶ G) :
      (leftTranslation g).hom.left ≫ f.left = f.left ≫ (translation H g).hom.left := by
    simpa only [orbitMap_one_comapRegular] using
      (SchemeAction.orbitMap_left_translation G g (1 : _ ⟶ H)).symm
  have hrange : Set.range (𝟙 H.left) ⊆ SchemeAction.orbit G (1 : _ ⟶ H) := by
    rintro _ ⟨y, rfl⟩
    rw [SchemeAction.orbit_def, orbitMap_one_comapRegular]
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
finite-type homomorphism with geometrically reduced, locally finite-type target is flat. -/
theorem flat_of_surjective [QuasiCompact f.left] [LocallyOfFiniteType f.left]
    [LocallyOfFiniteType H.hom] [GeometricallyReduced H.hom] [Surjective f.left] :
    Flat f.left := by
  let φ := Spec.algebraMap k (AlgebraicClosure k)
  have h := Over.isPullback_pullback_map_left φ f
  have : QuasiCompact ((Over.pullback φ).map f).left :=
    MorphismProperty.of_isPullback h.flip ‹_›
  have : LocallyOfFiniteType ((Over.pullback φ).map f).left :=
    MorphismProperty.of_isPullback h.flip ‹_›
  have : Surjective ((Over.pullback φ).map f).left :=
    MorphismProperty.of_isPullback h.flip ‹_›
  exact MorphismProperty.of_isPullback_of_surjective_of_flat_of_quasiCompact h
    (flat_of_surjective_of_isAlgClosed ((Over.pullback φ).map f))

end TauCeti.GroupScheme

namespace CategoryTheory.Over.Hom

universe u

/-- A finite, locally finitely presented, surjective homomorphism over an arbitrary base is flat
if the source is flat and the target is geometrically reduced and locally of finite type over
the base. -/
theorem flat_left_of_finite_of_surjective {S : Scheme.{u}} {G H : Over S} [GrpObj G] [GrpObj H]
    (f : G ⟶ H) [IsMonHom f] [Flat G.hom] [GeometricallyReduced H.hom] [LocallyOfFiniteType H.hom]
    [IsFinite f.left] [LocallyOfFinitePresentation f.left] [Surjective f.left] : Flat f.left := by
  have : Flat (f.left ≫ H.hom) := by
    rw [Over.w f]
    infer_instance
  refine f.left.flat_of_flat_pullback_fiberι H.hom fun s ↦ ?_
  let p := S.fromSpecResidueField s
  let F := Over.pullback p
  let : IsFinite (F.map f).left := MorphismProperty.overPullbackMap p f ‹_›
  let : Surjective (F.map f).left := MorphismProperty.overPullbackMap p f ‹_›
  have : GeometricallyReduced (F.obj H).hom := by
    simp only [F, Over.pullback_obj_hom]
    infer_instance
  have hf : Flat (F.map f).left :=
    TauCeti.GroupScheme.flat_of_surjective (k := S.residueField s) (F.map f)
  have h := (Over.isPullback_pullback_map_left p f).flip
  -- The fibre inclusion is the first projection of the pullback along the residue field.
  have : Flat (pullback.snd f.left (pullback.fst H.hom p)) := by
    rw [← h.isoPullback_inv_snd]
    infer_instance
  exact this

end CategoryTheory.Over.Hom
