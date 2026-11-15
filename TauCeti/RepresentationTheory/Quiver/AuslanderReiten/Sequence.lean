/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.AuslanderReiten.Existence
public import TauCeti.CategoryTheory.AlmostSplit.Sequence
import TauCeti.RepresentationTheory.Quiver.Representation.Projective.Presentation
import TauCeti.CategoryTheory.AlmostSplit.Minimal

/-!
# Almost-split sequences for quivers of finite representation type

For a quiver with finitely many paths and finite representation type, every
finite-dimensional non-projective indecomposable ends an almost-split sequence
in the full subcategory of pointwise finite-dimensional representations.
Conversely, precisely these objects can end an almost-split sequence.

The lifting properties quantify over finite-dimensional representations. The
sequence is short exact in that abelian subcategory, whose inclusion preserves
finite limits and colimits, so it is also short exact as a sequence of ambient
representations. This does not identify its initial object with the `D Tr`
translate, nor assert the lifting properties for infinite-dimensional objects.

The construction uses the right minimal right almost-split morphism of
`TauCeti.QuiverRep.exists_right_minimal_isRightAlmostSplit` and finite projective
presentations. These give almost-split sequences without any assumption that
the coefficient field is algebraically closed.

## References

* M. Auslander, I. Reiten, S. O. Smalø, *Representation Theory of Artin Algebras*,
  Cambridge University Press (1995), Section V.1.
-/

public section

namespace TauCeti.QuiverRep

open CategoryTheory CategoryTheory.Limits

universe u v w t

variable {k : Type u} {Q : Type v} [Field k] [Quiver.{w} Q]
  [Finite (Quiver.TotalPath Q)] [Small.{t} (pathAlgebra k Q)]

/-- Every finite-dimensional non-projective indecomposable representation of a
quiver of finite representation type ends an almost-split sequence. Both lifting
properties are taken in the finite-dimensional full subcategory. -/
theorem exists_isAlmostSplit (h : IsFiniteRepType.{u, v, w, t} k Q)
    (Y : ObjectProperty.FullSubcategory (IsFinDim.{u, v, w, t} k Q))
    (hiY : Indecomposable Y.obj) (hpY : ¬ Projective Y.obj) :
    ∃ S : ShortComplex (ObjectProperty.FullSubcategory (IsFinDim.{u, v, w, t} k Q)),
      S.X₃ = Y ∧ S.IsAlmostSplit := by
  obtain ⟨E, f, hf, hmin⟩ := exists_right_minimal_isRightAlmostSplit h Y hiY
  have hp : ¬ Projective Y := fun hY ↦ hpY
    ((ObjectProperty.FullSubcategory.projective_iff_projective_obj_of_finite_paths Y).mp hY)
  -- A projective epimorphism onto a non-projective object cannot split.
  let P := Projective.over Y
  let π := Projective.π Y
  have hπ : ¬ IsSplitEpi π := by
    intro hs
    let r : Retract Y P :=
      { i := section_ π
        r := π
        retract := IsSplitEpi.id π }
    exact hp r.projective
  have : Epi f := hf.epi_of_epi π hπ
  -- Expose the sequence's endpoints as well as its map: the projection equation for
  -- `g` alone does not rewrite the implicit object indices of the lifting predicates.
  have hS : (ShortComplex.kernelSequence f).ShortExact :=
    { exact := ShortComplex.kernelSequence_exact f
      epi_g := by
        simpa only [ShortComplex.kernelSequence] using (inferInstance : Epi f) }
  exact ⟨ShortComplex.kernelSequence f, ShortComplex.kernelSequence_X₃ f,
    hS.isAlmostSplit_of_isRightAlmostSplit
      (by simpa only [ShortComplex.kernelSequence] using hf)
      (by simpa only [ShortComplex.kernelSequence] using hmin)⟩

/-- For a quiver of finite representation type, a finite-dimensional representation
ends an almost-split sequence exactly when it is indecomposable and non-projective.
The conditions on the right refer to the ambient representation category. -/
theorem exists_isAlmostSplit_iff (h : IsFiniteRepType.{u, v, w, t} k Q)
    (Y : ObjectProperty.FullSubcategory (IsFinDim.{u, v, w, t} k Q)) :
    (∃ S : ShortComplex (ObjectProperty.FullSubcategory (IsFinDim.{u, v, w, t} k Q)),
      S.X₃ = Y ∧ S.IsAlmostSplit) ↔ Indecomposable Y.obj ∧ ¬ Projective Y.obj := by
  refine ⟨?_, fun ⟨hiY, hpY⟩ ↦ exists_isAlmostSplit h Y hiY hpY⟩
  rintro ⟨S, rfl, hS⟩
  let F := ObjectProperty.ι (IsFinDim.{u, v, w, t} k Q)
  refine ⟨F.indecomposable_obj_of_map_bijective hS.isRightAlmostSplit_g.indecomposable
    ((Functor.FullyFaithful.ofFullyFaithful F).map_bijective _ _), ?_⟩
  intro hp
  exact hS.not_projective_X₃
    ((ObjectProperty.FullSubcategory.projective_iff_projective_obj_of_finite_paths S.X₃).mpr hp)

end TauCeti.QuiverRep
