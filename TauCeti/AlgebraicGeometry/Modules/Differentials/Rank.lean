/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.Differentials.LocallyFree
public import TauCeti.AlgebraicGeometry.Modules.Differentials.Stalk
public import TauCeti.AlgebraicGeometry.Morphisms.Smooth.StandardSmooth
public import TauCeti.AlgebraicGeometry.VectorBundle.FixedRank
public import TauCeti.AlgebraicGeometry.VectorBundle.Rank
public import Mathlib.RingTheory.Smooth.StandardSmoothCotangent
import TauCeti.AlgebraicGeometry.Restrict
import TauCeti.AlgebraicGeometry.VectorBundle.Stalk

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
* `TauCeti.AlgebraicGeometry.FiniteLocallyFreeSheaf.FixedRank.relativeDifferentials`: the same
  sheaf as a finite locally free sheaf of constant rank `n`;
* `TauCeti.AlgebraicGeometry.FiniteLocallyFreeSheaf.rank_relativeDifferentials_of_isOpenImmersion`:
  the rank is unchanged by restriction along an open immersion over `Spec R`;
* `TauCeti.AlgebraicGeometry.smoothOfRelativeDimension_of_forall_rank_relativeDifferentials_eq`:
  conversely to the first item, a smooth scheme over `Spec R` on which `Ω_{X/R}` has constant
  rank `d` is smooth of relative dimension `d`;
* `TauCeti.AlgebraicGeometry.isInvertible_relativeDifferentials` and
  `TauCeti.AlgebraicGeometry.InvertibleSheaf.relativeDifferentials`: in relative dimension one
  it is an invertible sheaf;
* `TauCeti.AlgebraicGeometry.free_kaehlerDifferential_stalk`,
  `TauCeti.AlgebraicGeometry.finite_kaehlerDifferential_stalk` and
  `TauCeti.AlgebraicGeometry.finrank_kaehlerDifferential_stalk`: on a scheme smooth of relative
  dimension `n`, the Kähler differentials `Ω[𝒪_{X,x}⁄R]` of each local ring are free of rank `n`.

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
  let : Algebra R Γ(X, W) := ((X.baseRingToStructurePresheaf R).app (op W.val)).hom.toAlgebra
  have : Algebra.IsStandardSmoothOfRelativeDimension n R Γ(X, W) := hW.toAlgebra
  have : Nonempty W.val := ⟨⟨x, hxW⟩⟩
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

/-- The rank of the sheaf of relative differentials of a smooth scheme over `Spec R` is
unchanged by restriction along an open immersion over `Spec R`. -/
theorem FiniteLocallyFreeSheaf.rank_relativeDifferentials_of_isOpenImmersion
    {U X : Scheme.{u}} [U.Over (Spec (.of R))] [X.Over (Spec (.of R))] (f : U ⟶ X)
    [IsOpenImmersion f] [f.IsOver (Spec (.of R))] [Smooth (U ↘ Spec (.of R))]
    [Smooth (X ↘ Spec (.of R))] (u : U) :
    (FiniteLocallyFreeSheaf.relativeDifferentials R U).rank u =
      (FiniteLocallyFreeSheaf.relativeDifferentials R X).rank (f u) := by
  rw [← FiniteLocallyFreeSheaf.rank_pullback_apply,
    FiniteLocallyFreeSheaf.rank_eq_of_iso (F := FiniteLocallyFreeSheaf.relativeDifferentials R U)
      (eqToIso ((FiniteLocallyFreeSheaf.pullback_obj_obj _ _).trans
          (congrArg _ (FiniteLocallyFreeSheaf.relativeDifferentials_obj R X))) ≪≫
        ((Scheme.Modules.restrictFunctorIsoPullback f).app (X.relativeDifferentials R)).symm ≪≫
        relativeDifferentialsRestrictIso R f ≪≫
        eqToIso (FiniteLocallyFreeSheaf.relativeDifferentials_obj R U).symm)]

/-- A scheme smooth over `Spec R` whose sheaf of relative differentials has rank `d` at every
point is smooth of relative dimension `d` over `Spec R`. -/
theorem smoothOfRelativeDimension_of_forall_rank_relativeDifferentials_eq {X : Scheme.{u}}
    [X.Over (Spec (.of R))] [Smooth (X ↘ Spec (.of R))] {d : ℕ}
    (h : ∀ x, (FiniteLocallyFreeSheaf.relativeDifferentials R X).rank x = d) :
    SmoothOfRelativeDimension d (X ↘ Spec (.of R)) := by
  refine IsZariskiLocalAtSource.of_forall_exists_ι_comp fun x ↦ ?_
  -- Around `x`, the structure morphism is smooth of some relative dimension `m`.
  obtain ⟨V, m, hx, hm⟩ := (X ↘ Spec (.of R)).exists_smoothOfRelativeDimension_ι_comp_of_smooth x
  -- Regard `V` as a scheme over `Spec R`; it is smooth of relative dimension `m`, so `Ω` has rank
  -- `m` on it, and rank `d` because `V` is open in `X`.
  let : (V : Scheme).Over (Spec (.of R)) := ⟨V.ι ≫ X ↘ Spec (.of R)⟩
  have : V.ι.IsOver (Spec (.of R)) := ⟨rfl⟩
  have : SmoothOfRelativeDimension m ((V : Scheme) ↘ Spec (.of R)) := hm
  have := SmoothOfRelativeDimension.smooth m ((V : Scheme) ↘ Spec (.of R))
  have hy := (FiniteLocallyFreeSheaf.rank_relativeDifferentials_of_isOpenImmersion R V.ι
    ⟨x, hx⟩).symm.trans (FiniteLocallyFreeSheaf.rank_relativeDifferentials_apply R m _)
  rw [h] at hy
  exact ⟨V, hx, hy ▸ hm⟩

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

/-- On a scheme smooth over `Spec R`, the Kähler differentials `Ω[𝒪_{X,x}⁄R]` of each local ring
form a free `𝒪_{X,x}`-module. -/
instance free_kaehlerDifferential_stalk [Smooth (X ↘ Spec (.of R))] (x : X) :
    Module.Free (X.presheaf.stalk x) Ω[X.presheaf.stalk x⁄R] := by
  have := FiniteLocallyFreeSheaf.free_stalk (FiniteLocallyFreeSheaf.relativeDifferentials R X) x
  rw [FiniteLocallyFreeSheaf.relativeDifferentials_obj] at this
  exact Module.Free.of_equiv (X.relativeDifferentialsStalkEquiv R x)

/-- On a scheme smooth over `Spec R`, the Kähler differentials `Ω[𝒪_{X,x}⁄R]` of each local ring
form a finitely generated `𝒪_{X,x}`-module. -/
instance finite_kaehlerDifferential_stalk [Smooth (X ↘ Spec (.of R))] (x : X) :
    Module.Finite (X.presheaf.stalk x) Ω[X.presheaf.stalk x⁄R] := by
  have := FiniteLocallyFreeSheaf.finite_stalk (FiniteLocallyFreeSheaf.relativeDifferentials R X) x
  rw [FiniteLocallyFreeSheaf.relativeDifferentials_obj] at this
  exact Module.Finite.equiv (X.relativeDifferentialsStalkEquiv R x)

variable (n : ℕ) [SmoothOfRelativeDimension n (X ↘ Spec (.of R))]

/-- The sheaf of relative differentials `Ω_{X/R}` of a scheme smooth of relative dimension `n`
over `Spec R`, as a finite locally free sheaf of constant rank `n`. -/
def FiniteLocallyFreeSheaf.FixedRank.relativeDifferentials : FiniteLocallyFreeSheaf.FixedRank X n :=
  haveI := SmoothOfRelativeDimension.smooth n (X ↘ Spec (.of R))
  ⟨FiniteLocallyFreeSheaf.relativeDifferentials R X,
    (FiniteLocallyFreeSheaf.isConstantRank_iff _ n).mpr
      (FiniteLocallyFreeSheaf.rank_relativeDifferentials_apply R n)⟩

/-- The underlying sheaf of `FiniteLocallyFreeSheaf.FixedRank.relativeDifferentials R X n` is
`Ω_{X/R}`. -/
@[simp]
lemma FiniteLocallyFreeSheaf.FixedRank.relativeDifferentials_obj_obj :
    (FiniteLocallyFreeSheaf.FixedRank.relativeDifferentials R X n).obj.obj =
      X.relativeDifferentials R :=
  haveI := SmoothOfRelativeDimension.smooth n (X ↘ Spec (.of R))
  FiniteLocallyFreeSheaf.relativeDifferentials_obj R X

/-- On a scheme smooth of relative dimension `n` over `Spec R`, the Kähler differentials
`Ω[𝒪_{X,x}⁄R]` of each local ring have rank `n` over `𝒪_{X,x}`. -/
theorem finrank_kaehlerDifferential_stalk (x : X) :
    Module.finrank (X.presheaf.stalk x) Ω[X.presheaf.stalk x⁄R] = n := by
  rw [← (X.relativeDifferentialsStalkEquiv R x).finrank_eq,
    ← FiniteLocallyFreeSheaf.FixedRank.relativeDifferentials_obj_obj R X n,
    FiniteLocallyFreeSheaf.finrank_stalk, FiniteLocallyFreeSheaf.FixedRank.rank_apply]

end

end TauCeti.AlgebraicGeometry
