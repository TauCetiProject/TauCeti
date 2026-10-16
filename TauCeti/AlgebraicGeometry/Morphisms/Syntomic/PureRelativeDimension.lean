/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Morphisms.PureRelativeDimension
public import TauCeti.AlgebraicGeometry.Morphisms.Syntomic.Basic

/-!
# Syntomic morphisms of relative dimension `n` have pure relative dimension `n`

A morphism `f : X ⟶ Y` that is syntomic of relative dimension `n` has pure relative dimension
`n`: every irreducible component of every nonempty fibre has dimension exactly `n`. In particular
a syntomic relative curve, such as a family of nodal curves or a smooth relative curve, has the
pure one-dimensional fibres on which the relative singular locus `Fitt₁(Ω_{X/S})` is defined.

Both conditions are fibrewise, and the fibre `X_y ⟶ Spec κ(y)` is again syntomic of relative
dimension `n`, so it suffices to treat a scheme `X` over a field `k`. Pure relative dimension is
local on the source for morphisms locally of finite type, and `X` is covered by affine opens whose
rings are standard syntomic `k`-algebras of relative dimension `n`. Such an algebra is a global
complete intersection `k[x₁, …, x_{n+c}] ⧸ (f₁, …, f_c)` of dimension at most `n`, so its spectrum
is pure-dimensional of dimension `n`
(`TauCeti.Algebra.IsStandardSyntomicOfRelativeDimension.isPureDimensional_primeSpectrum`).

Since smooth morphisms of relative dimension `n` are syntomic of relative dimension `n`
(`TauCeti.AlgebraicGeometry.SyntomicOfRelativeDimension.of_smoothOfRelativeDimension`), this also
gives pure relative dimension `n` for smooth morphisms.

## Main declarations

* `TauCeti.AlgebraicGeometry.PureRelativeDimension.of_syntomicOfRelativeDimension`: a morphism
  syntomic of relative dimension `n` has pure relative dimension `n`.

## References

* The Stacks Project, Commutative Algebra, Section *Syntomic morphisms*: global complete
  intersections over a field and their dimension.
-/

public section

open CategoryTheory Limits AlgebraicGeometry RingHom TopologicalSpace

namespace TauCeti.AlgebraicGeometry

universe u

variable {n : ℕ}

/-- Let `f : X ⟶ Spec k` be syntomic of relative dimension `n` over a field `k`. If the ring of an
affine open `W` of `X` is standard syntomic of relative dimension `n` over the ring of global
sections of `Spec k`, then `W` has pure relative dimension `n` over `k`. -/
private lemma pureRelativeDimension_of_isStandardSyntomicOfRelativeDimension {k : Type u}
    [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [SyntomicOfRelativeDimension n f]
    {W : X.Opens} (hW : IsAffineOpen W)
    (h : IsStandardSyntomicOfRelativeDimension n (f.appLE ⊤ W le_top).hom) :
    PureRelativeDimension n (W.ι ≫ f) := by
  -- View `Γ(X, W)` as a standard syntomic `k`-algebra through `k ≅ Γ(Spec k, ⊤)`.
  let φ := (Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ W le_top
  have hφ : IsStandardSyntomicOfRelativeDimension n φ.hom := by
    rw [CommRingCat.hom_comp]
    exact (isStandardSyntomicOfRelativeDimension_respectsIso n).right _
      (Scheme.ΓSpecIso (.of k)).symm.commRingCatIsoToRingEquiv h
  let := φ.hom.toAlgebra
  have : Algebra.IsStandardSyntomicOfRelativeDimension n k Γ(X, W) :=
    (isStandardSyntomicOfRelativeDimension_iff n φ.hom).mp hφ
  have : RelativeDimensionLE n (W.ι ≫ f) :=
    IsZariskiLocalAtSource.comp (P := @RelativeDimensionLE n) inferInstance W.ι
  -- `W` is homeomorphic to `Spec Γ(X, W)`.
  rw [pureRelativeDimension_iff_of_field, hW.isoSpec.hom.homeomorph.isPureDimensional_iff]
  exact ⟨inferInstance,
    Algebra.IsStandardSyntomicOfRelativeDimension.isPureDimensional_primeSpectrum n k Γ(X, W)⟩

/-- A scheme syntomic of relative dimension `n` over a field has pure relative dimension `n`. -/
private lemma pureRelativeDimension_of_field {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [SyntomicOfRelativeDimension n f] : PureRelativeDimension n f := by
  have := SyntomicOfRelativeDimension.locallyOfFinitePresentation n f
  choose W hxW _ hW using
    SyntomicOfRelativeDimension.exists_isStandardSyntomicOfRelativeDimension_appLE_top n f
  have hcov : IsOpenCover fun x ↦ (W x).1 :=
    eq_top_iff.mpr fun x _ ↦ Opens.mem_iSup.mpr ⟨x, hxW x⟩
  rw [pureRelativeDimension_iff_of_openCover f (X.openCoverOfIsOpenCover _ hcov)]
  exact fun x ↦ pureRelativeDimension_of_isStandardSyntomicOfRelativeDimension f (W x).2 (hW x)

/-- A morphism syntomic of relative dimension `n` has pure relative dimension `n`: every
irreducible component of every nonempty fibre has dimension `n`. -/
instance (priority := low) PureRelativeDimension.of_syntomicOfRelativeDimension
    {X Y : Scheme.{u}} (f : X ⟶ Y) [SyntomicOfRelativeDimension n f] :
    PureRelativeDimension n f := by
  -- The fibre `X_y ⟶ Spec κ(y)` is a base change of `f`, so it is syntomic of relative
  -- dimension `n`.
  have (y : Y) : PureRelativeDimension n (f.fiberToSpecResidueField y) := by
    have : SyntomicOfRelativeDimension n (f.fiberToSpecResidueField y) :=
      inferInstanceAs (SyntomicOfRelativeDimension n (pullback.snd _ _))
    exact pureRelativeDimension_of_field (k := Y.residueField y) _
  rw [pureRelativeDimension_iff_relativeDimensionLE_and_isPureDimensional_fiber]
  exact ⟨inferInstance, fun y ↦ ((pureRelativeDimension_iff_of_field
    (K := Y.residueField y) _).mp (this y)).2⟩

end TauCeti.AlgebraicGeometry
