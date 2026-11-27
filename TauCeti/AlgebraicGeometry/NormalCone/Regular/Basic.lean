/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Morphisms.RegularImmersion
public import TauCeti.AlgebraicGeometry.NormalCone.Basic
public import TauCeti.AlgebraicGeometry.VectorBundle.FixedRank
import TauCeti.AlgebraicGeometry.Morphisms.ClosedImmersion.Conormal
import TauCeti.AlgebraicGeometry.VectorBundle.OpenCover
import TauCeti.RingTheory.Regular.Cotangent

/-!
# The conormal sheaf of a regular immersion

The conormal sheaf `I/I²` of a regular immersion of codimension `d`
(`Scheme.Hom.IsRegularImmersion`) is finite locally free of rank `d` (`IsRegularImmersion.conormal`;
Stacks, Tags 063K and 063M; Fulton, Appendix B.7.1). Over an affine open `U` on which
`I(U) = (f₁, …, f_d)` for a regular sequence, the conormal sheaf restricted to
`Spec (Γ(U) ⧸ I(U))` is the sheaf associated with `I(U) ⧸ I(U)²`
(`Scheme.Hom.pullbackConormalAffineChartIsoTilde`), which is free on the classes of `f₁, …, f_d`
(`RingTheory.Sequence.IsWeaklyRegular.cotangentBasis`).

## Main declarations

* `AlgebraicGeometry.Scheme.Hom.IsRegularImmersion.isFiniteLocallyFree_conormal`: the conormal
  sheaf of a regular immersion is finite locally free.
* `AlgebraicGeometry.Scheme.Hom.IsRegularImmersion.conormal`: the conormal sheaf of a regular
  immersion of codimension `d`, as a finite locally free sheaf of rank `d`.

## References

* [The Stacks Project, Tag 063K](https://stacks.math.columbia.edu/tag/063K)
* [The Stacks Project, Tag 063M](https://stacks.math.columbia.edu/tag/063M)
* W. Fulton, *Intersection Theory*, 2nd ed., Appendix B.7.1.
-/

public section

open CategoryTheory Limits Opposite

universe u

namespace AlgebraicGeometry.Scheme

open TauCeti.AlgebraicGeometry

namespace Hom

variable {X Y : Scheme.{u}}

namespace IsRegularImmersion

variable {i : X ⟶ Y} [IsImmersion i] {d : ℕ}

/-- The conormal sheaf of a regular immersion of codimension `d` is free of rank `d` on an open
neighbourhood of every point. -/
theorem exists_pullback_conormal_iso_free (h : i.IsRegularImmersion d) (x : X) :
    ∃ (V : Scheme.{u}) (g : V ⟶ X), IsOpenImmersion g ∧ x ∈ Set.range g ∧
      Nonempty ((Scheme.Modules.pullback g).obj i.conormal.obj ≅
        SheafOfModules.free (ULift.{u} (Fin d))) := by
  obtain ⟨U, hxU, rs, rfl, hrs, hI⟩ := IdealSheafData.isLocallyRegular_iff.mp
    (isRegularImmersion_iff.mp h) (i.liftCoborder x)
    (i.liftCoborder.range_subset_ker_support ⟨x, rfl⟩)
  have b : Module.Basis (ULift.{u} (Fin rs.length)) (_ ⧸ i.liftCoborder.ker.ideal U)
      (Ideal.Cotangent (i.liftCoborder.ker.ideal U)) := by
    rw [hI]
    exact hrs.cotangentBasis.reindex Equiv.ulift.symm
  obtain ⟨e⟩ := i.liftCoborder.nonempty_pullback_conormal_affineChart_iso_free U b
  exact ⟨_, i.liftCoborder.affineChart U, inferInstance,
    (i.liftCoborder.mem_range_affineChart_iff U).mpr hxU,
    ⟨(Scheme.Modules.pullback _).mapIso (eqToIso i.conormal_obj) ≪≫ e⟩⟩

/-- **The conormal sheaf of a regular immersion is finite locally free** (Stacks, Tags 063K and
063M). -/
theorem isFiniteLocallyFree_conormal (h : i.IsRegularImmersion d) :
    Scheme.Modules.isFiniteLocallyFree X i.conormal.obj := by
  choose V g hg hx e using h.exists_pullback_conormal_iso_free
  choose y hy using hx
  refine (Scheme.Modules.isFiniteLocallyFree_iff_exists_openCover (M := i.conormal.obj)).mpr ?_
  exact ⟨Cover.mkOfCovers X V g (fun x ↦ ⟨x, y x, hy x⟩) hg,
    fun x ↦ ⟨ULift (Fin d), inferInstance, e x⟩⟩

/-- The conormal sheaf `I/I²` of a regular immersion of codimension `d`, as a finite locally free
sheaf of rank `d` (Stacks, Tags 063K and 063M). -/
noncomputable def conormal (h : i.IsRegularImmersion d) : FiniteLocallyFreeSheaf.FixedRank X d :=
  ⟨⟨i.conormal.obj, h.isFiniteLocallyFree_conormal⟩,
    (FiniteLocallyFreeSheaf.isConstantRank_iff _ _).mpr fun x ↦ by
    obtain ⟨V, g, -, ⟨y, rfl⟩, ⟨e⟩⟩ := h.exists_pullback_conormal_iso_free x
    rw [← FiniteLocallyFreeSheaf.rank_pullback_apply,
      FiniteLocallyFreeSheaf.rank_eq_of_iso (F := FiniteLocallyFreeSheaf.free V (ULift (Fin d)))
        (eqToIso (FiniteLocallyFreeSheaf.pullback_obj_obj g _) ≪≫ e ≪≫
          eqToIso (FiniteLocallyFreeSheaf.free_obj V _).symm),
      FiniteLocallyFreeSheaf.rank_free_apply]
    simp⟩

/-- The underlying sheaf of `IsRegularImmersion.conormal` is the conormal sheaf `I/I²`. -/
@[simp]
theorem conormal_obj_obj (h : i.IsRegularImmersion d) : h.conormal.obj.obj = i.conormal.obj :=
  (rfl)

end IsRegularImmersion

end Hom

end AlgebraicGeometry.Scheme
