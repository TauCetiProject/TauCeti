/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Morphisms.PureRelativeDimension
public import TauCeti.AlgebraicGeometry.Morphisms.Smooth.StandardSmooth
public import TauCeti.RingTheory.Smooth.KrullDimension

/-!
# Smooth morphisms of relative dimension `n` have pure relative dimension `n`

A morphism `f : X ⟶ Y` that is smooth of relative dimension `n` has pure relative dimension `n`:
every irreducible component of every nonempty fibre has dimension exactly `n`. In particular a
smooth relative curve, a morphism smooth of relative dimension one, satisfies the pure
one-dimensionality required of the fibres of a family of nodal curves.

Both conditions are fibrewise, and the fibre `X_y ⟶ Spec κ(y)` is again smooth of relative
dimension `n`, so it suffices to treat a scheme `X` over a field `k`. Pure relative dimension is
local on the source for morphisms locally of finite type, and `X` is covered by affine opens whose
rings are standard smooth `k`-algebras of relative dimension `n`. The spectrum of such an algebra
is pure-dimensional of dimension `n` and has dimension at most `n`
(`TauCeti.isPureDimensional_primeSpectrum_of_isStandardSmoothOfRelativeDimension`).

## Main declarations

* `TauCeti.AlgebraicGeometry.PureRelativeDimension.of_smoothOfRelativeDimension`: a morphism
  smooth of relative dimension `n` has pure relative dimension `n`.

## References

* R. Hartshorne, *Algebraic Geometry*, Section III.10, where pure `n`-dimensionality of the fibres
  is part of the definition of a smooth morphism of relative dimension `n`.
-/

public section

open CategoryTheory Limits AlgebraicGeometry RingHom TopologicalSpace

namespace TauCeti.AlgebraicGeometry

universe u

variable {n : ℕ}

/-- If the ring of an affine open `W` of a scheme over a field `k` is standard smooth of relative
dimension `n` over the ring of global sections of `Spec k`, then `W` has pure relative dimension
`n` over `k`. -/
private lemma pureRelativeDimension_of_isStandardSmoothOfRelativeDimension {k : Type u} [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) {W : X.Opens} (hW : IsAffineOpen W)
    (h : (f.appLE ⊤ W le_top).hom.IsStandardSmoothOfRelativeDimension n) :
    PureRelativeDimension n (W.ι ≫ f) := by
  -- View `Γ(X, W)` as a standard smooth `k`-algebra through `k ≅ Γ(Spec k, ⊤)`.
  let φ := (Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ W le_top
  have hφ : φ.hom.IsStandardSmoothOfRelativeDimension n := by
    rw [CommRingCat.hom_comp]
    exact (isStandardSmoothOfRelativeDimension_respectsIso (n := n)).right _
      (Scheme.ΓSpecIso (.of k)).symm.commRingCatIsoToRingEquiv h
  let := φ.hom.toAlgebra
  have : Algebra.IsStandardSmoothOfRelativeDimension n k Γ(X, W) := hφ.toAlgebra
  -- `W` is homeomorphic to `Spec Γ(X, W)`.
  have e := hW.isoSpec.hom.homeomorph
  rw [pureRelativeDimension_iff_of_field, relativeDimensionLE_iff_of_field,
    e.isHomeomorph.topologicalKrullDim_eq, e.isPureDimensional_iff]
  refine ⟨?_, isPureDimensional_primeSpectrum_of_isStandardSmoothOfRelativeDimension k n⟩
  refine (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim Γ(X, W)).trans_le ?_
  cases subsingleton_or_nontrivial Γ(X, W)
  · rw [ringKrullDim_eq_bot_of_subsingleton]
    exact bot_le
  · rw [ringKrullDim_eq_of_isStandardSmoothOfRelativeDimension k n]

/-- A scheme smooth of relative dimension `n` over a field has pure relative dimension `n`. -/
private lemma pureRelativeDimension_of_field {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [SmoothOfRelativeDimension n f] : PureRelativeDimension n f := by
  have := SmoothOfRelativeDimension.smooth n f
  choose W hxW hW using
    SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension_appLE_top f n
  have hcov : IsOpenCover fun x ↦ (W x).1 :=
    eq_top_iff.mpr fun x _ ↦ Opens.mem_iSup.mpr ⟨x, hxW x⟩
  rw [pureRelativeDimension_iff_of_openCover f (X.openCoverOfIsOpenCover _ hcov)]
  exact fun x ↦ pureRelativeDimension_of_isStandardSmoothOfRelativeDimension f (W x).2 (hW x)

/-- A morphism smooth of relative dimension `n` has pure relative dimension `n`: every
irreducible component of every nonempty fibre has dimension `n`. -/
instance (priority := low) PureRelativeDimension.of_smoothOfRelativeDimension
    {X Y : Scheme.{u}} (f : X ⟶ Y) [SmoothOfRelativeDimension n f] : PureRelativeDimension n f := by
  -- The fibre `X_y ⟶ Spec κ(y)` is a base change of `f`, so it is smooth of relative
  -- dimension `n`.
  have (y : Y) : PureRelativeDimension n (f.fiberToSpecResidueField y) := by
    have : SmoothOfRelativeDimension n (f.fiberToSpecResidueField y) :=
      inferInstanceAs (SmoothOfRelativeDimension n (pullback.snd _ _))
    exact pureRelativeDimension_of_field (k := Y.residueField y) _
  rw [pureRelativeDimension_iff_relativeDimensionLE_and_isPureDimensional_fiber]
  refine ⟨⟨fun y ↦ ?_⟩, fun y ↦ ?_⟩
  · exact (relativeDimensionLE_iff_of_field (K := Y.residueField y) _).mp
      (this y).toRelativeDimensionLE
  · exact ((pureRelativeDimension_iff_of_field (K := Y.residueField y) _).mp (this y)).2

end TauCeti.AlgebraicGeometry
