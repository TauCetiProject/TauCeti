/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.Differentials.LocallyFree
public import TauCeti.AlgebraicGeometry.Morphisms.Smooth.StandardSmooth
public import TauCeti.AlgebraicGeometry.VectorBundle.Rank
public import Mathlib.RingTheory.Smooth.StandardSmoothCotangent

/-!
# The rank of the sheaf of relative differentials

For a scheme `X` smooth of relative dimension `n` over `Spec R`, the sheaf of relative
differentials `Ω_{X/R}` is finite locally free of rank `n` at every point. Around each point,
`X` has an affine open `W` whose ring of functions is a standard smooth `R`-algebra of relative
dimension `n`, so that its module of Kähler differentials is free of rank `n`; on `W` the sheaf
`Ω_{X/R}` is the sheaf associated with that module.

When `X` is smooth of relative dimension one over `Spec R`, as a smooth curve over a field is,
`Ω_{X/R}` is therefore an invertible sheaf.

## Main declarations

* `TauCeti.AlgebraicGeometry.FiniteLocallyFreeSheaf.rank_relativeDifferentials_apply`: the
  finite locally free sheaf `FiniteLocallyFreeSheaf.relativeDifferentials R X` has rank `n`
  everywhere when `X` is smooth of relative dimension `n`;
* `TauCeti.AlgebraicGeometry.isInvertible_relativeDifferentials` and
  `TauCeti.AlgebraicGeometry.InvertibleSheaf.relativeDifferentials`: in relative dimension one
  it is an invertible sheaf.

## References

* The Stacks Project, *Morphisms of Schemes*, Lemma 29.34.12 (Tag 02G1).
* R. Hartshorne, *Algebraic Geometry*, Theorem II.8.15.
-/

public section

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace RingHom

namespace TauCeti.AlgebraicGeometry

universe u

noncomputable section

variable (R : Type u) [CommRing R] (X : Scheme.{u}) [X.Over (Spec (.of R))]

variable {X} in
/-- Around every point of a scheme smooth of relative dimension `n` over `Spec R`, there is an
affine open whose ring of functions is standard smooth of relative dimension `n` over `R`. -/
private lemma exists_isStandardSmoothOfRelativeDimension (n : ℕ)
    [SmoothOfRelativeDimension n (X ↘ Spec (.of R))] (x : X) :
    ∃ W : X.affineOpens, x ∈ W.1 ∧
      ((X.baseRingToStructurePresheaf R).app (op W.1)).hom.IsStandardSmoothOfRelativeDimension n
        := by
  obtain ⟨W, hxW, h⟩ :=
    SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension_appLE_top
      (X ↘ Spec (.of R)) n x
  refine ⟨W, hxW, ?_⟩
  rw [Scheme.baseRingToStructurePresheaf_app_eq_appLE, CommRingCat.hom_comp]
  exact (isStandardSmoothOfRelativeDimension_respectsIso (n := n)).right _
    (Scheme.ΓSpecIso (.of R)).symm.commRingCatIsoToRingEquiv h

/-- On the spectrum of a standard smooth `R`-algebra `A` of relative dimension `n`, the sheaf of
relative differentials is free of rank `n`. -/
private lemma exists_relativeDifferentialsSpecIsoFree (n : ℕ) (A : CommRingCat.{u})
    [Nontrivial A] [Algebra R A] [Algebra.IsStandardSmoothOfRelativeDimension n R A] :
    ∃ (ι : Type u) (_ : Finite ι), Nat.card ι = n ∧
      Nonempty ((Spec A).relativeDifferentials R ≅
        (FiniteLocallyFreeSheaf.free (Spec A) ι).obj) := by
  have : Algebra.IsStandardSmooth R A :=
    Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth n
  let b := Module.Free.chooseBasis A Ω[A⁄R]
  have hcard : Cardinal.mk (Module.Free.ChooseBasisIndex A Ω[A⁄R]) = n :=
    b.mk_eq_rank''.trans (Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential n)
  refine ⟨_, Cardinal.lt_aleph0_iff_finite.mp (hcard ▸ Cardinal.natCast_lt_aleph0), ?_, ?_⟩
  · rw [Nat.card, hcard, Cardinal.toNat_natCast]
  · rw [FiniteLocallyFreeSheaf.free_obj]
    exact ⟨relativeDifferentialsSpecIso R A ≪≫
      (tilde.functor _).mapIso b.repr.toModuleIso ≪≫ tildeFinsupp _⟩

variable {X}

/-- On a scheme smooth of relative dimension `n` over `Spec R`, the sheaf of relative
differentials has rank `n` at every point. -/
theorem FiniteLocallyFreeSheaf.rank_relativeDifferentials_apply (n : ℕ)
    [SmoothOfRelativeDimension n (X ↘ Spec (.of R))] (x : X) :
    haveI := SmoothOfRelativeDimension.smooth n (X ↘ Spec (.of R))
    (FiniteLocallyFreeSheaf.relativeDifferentials R X).rank x = n := by
  have := SmoothOfRelativeDimension.smooth n (X ↘ Spec (.of R))
  obtain ⟨W, hxW, hW⟩ := exists_isStandardSmoothOfRelativeDimension R n x
  let : Algebra R Γ(X, W) := ((X.baseRingToStructurePresheaf R).app (op W.1)).hom.toAlgebra
  have : Algebra.IsStandardSmoothOfRelativeDimension n R Γ(X, W) := hW.toAlgebra
  have : Nonempty W.1 := ⟨⟨x, hxW⟩⟩
  have : W.property.fromSpec.IsOver (Spec (.of R)) := isOver_fromSpec R X W
  have : IsOpenImmersion W.property.fromSpec := IsAffineOpen.isOpenImmersion_fromSpec W.property
  obtain ⟨ι, _, hι, ⟨e⟩⟩ := exists_relativeDifferentialsSpecIsoFree R n Γ(X, W)
  -- `x` is the image of a point `y` of the canonical chart `Spec Γ(X, W) ⟶ X`, and the pullback
  -- of `Ω_{X/R}` along the chart is the free sheaf `Ω_{Spec Γ(X, W)/R}` of rank `n`.
  obtain ⟨y, rfl⟩ : x ∈ Set.range W.property.fromSpec := by
    rwa [IsAffineOpen.range_fromSpec W.property]
  rw [← FiniteLocallyFreeSheaf.rank_pullback_apply,
    FiniteLocallyFreeSheaf.rank_eq_of_iso (F := FiniteLocallyFreeSheaf.free _ ι)
      (eqToIso ((FiniteLocallyFreeSheaf.pullback_obj_obj _ _).trans
          (congrArg _ (FiniteLocallyFreeSheaf.relativeDifferentials_obj R X))) ≪≫
        ((Scheme.Modules.restrictFunctorIsoPullback W.property.fromSpec).app
        (X.relativeDifferentials R)).symm ≪≫
        relativeDifferentialsRestrictIso R W.property.fromSpec ≪≫ e),
    FiniteLocallyFreeSheaf.rank_free_apply, hι]

/-- On a scheme smooth of relative dimension one over `Spec R`, the sheaf of relative
differentials is invertible. -/
theorem isInvertible_relativeDifferentials [SmoothOfRelativeDimension 1 (X ↘ Spec (.of R))] :
    SheafOfModules.isInvertible X (X.relativeDifferentials R) := by
  have := SmoothOfRelativeDimension.smooth 1 (X ↘ Spec (.of R))
  rw [← FiniteLocallyFreeSheaf.relativeDifferentials_obj]
  exact (FiniteLocallyFreeSheaf.relativeDifferentials R X).isInvertible_iff_forall_rank_eq_one.mpr
    (FiniteLocallyFreeSheaf.rank_relativeDifferentials_apply R 1)

variable (X)

/-- The sheaf of relative differentials of a scheme smooth of relative dimension one over
`Spec R`, as an invertible sheaf. -/
def InvertibleSheaf.relativeDifferentials [SmoothOfRelativeDimension 1 (X ↘ Spec (.of R))] :
    InvertibleSheaf X :=
  ⟨X.relativeDifferentials R, isInvertible_relativeDifferentials R⟩

/-- The underlying sheaf of `InvertibleSheaf.relativeDifferentials R X` is `Ω_{X/R}`. -/
@[simp]
lemma InvertibleSheaf.relativeDifferentials_obj
    [SmoothOfRelativeDimension 1 (X ↘ Spec (.of R))] :
    (InvertibleSheaf.relativeDifferentials R X).obj = X.relativeDifferentials R :=
  (rfl)

end

end TauCeti.AlgebraicGeometry
