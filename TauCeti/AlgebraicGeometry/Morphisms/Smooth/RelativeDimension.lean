/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Morphisms.Smooth.StandardSmooth
public import TauCeti.AlgebraicGeometry.Scheme.FunctionField
public import TauCeti.RingTheory.Smooth.KrullDimension

/-!
# The relative dimension of a smooth scheme over a field

A morphism `f : X ⟶ Spec k` to the spectrum of a field is smooth of relative dimension `n` exactly
when it is smooth and the local ring of `X` at every closed point has Krull dimension `n`. In
particular a smooth irreducible `k`-scheme of dimension `n` is smooth of relative dimension `n`,
and a smooth curve, an integral smooth `k`-scheme whose function field is an algebraic function
field of one variable over `k`, is smooth of relative dimension one. This turns the dimension
hypothesis on a smooth curve into the relative-dimension hypothesis under which its sheaf of
relative differentials `Ω_{X/k}` is invertible
(`TauCeti.AlgebraicGeometry.InvertibleSheaf.relativeDifferentials`).

Around every point a smooth morphism has affine charts whose rings are standard smooth over `k`
of some relative dimension. By `TauCeti.height_eq_of_isStandardSmoothOfRelativeDimension` that
relative dimension is the height of every maximal ideal of the chart, which is the dimension of
the local ring of `X` at every closed point of `X` lying in the chart. Charts are nonempty open
subsets of a Jacobson scheme, so they contain closed points.

## Main declarations

* `TauCeti.AlgebraicGeometry.smoothOfRelativeDimension_iff_ringKrullDim_stalk_eq`:
  `f : X ⟶ Spec k` is smooth of relative dimension `n` if and only if it is smooth and the local
  rings at closed points have dimension `n`;
* `TauCeti.AlgebraicGeometry.smoothOfRelativeDimension_of_topologicalKrullDim_eq`: a smooth
  irreducible `k`-scheme of dimension `n` is smooth of relative dimension `n`;
* `TauCeti.AlgebraicGeometry.smoothOfRelativeDimension_one_of_isFunctionField`: a smooth curve is
  smooth of relative dimension one.

## References

* R. Hartshorne, *Algebraic Geometry*, Chapter III, Section 10.
-/

public section

open CategoryTheory AlgebraicGeometry Order RingHom

namespace TauCeti.AlgebraicGeometry

universe u

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- If the ring of an affine open `W` is standard smooth of relative dimension `m` over the ring
of global sections of `Spec k`, then the local ring of `X` at every closed point of `X` in `W` has
dimension `m`. -/
private lemma ringKrullDim_stalk_eq_of_isStandardSmoothOfRelativeDimension {W : X.Opens}
    (hW : IsAffineOpen W) {m : ℕ}
    (h : (f.appLE ⊤ W le_top).hom.IsStandardSmoothOfRelativeDimension m)
    {x : X} (hxW : x ∈ W) (hx : IsClosed {x}) :
    ringKrullDim (X.presheaf.stalk x) = m := by
  -- View `Γ(X, W)` as a standard smooth `k`-algebra through `k ≅ Γ(Spec k, ⊤)`.
  let φ := (Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ W le_top
  have hφ : φ.hom.IsStandardSmoothOfRelativeDimension m := by
    rw [CommRingCat.hom_comp]
    exact (isStandardSmoothOfRelativeDimension_respectsIso (n := m)).right _
      (Scheme.ΓSpecIso (.of k)).symm.commRingCatIsoToRingEquiv h
  let := φ.hom.toAlgebra
  have : Algebra.IsStandardSmoothOfRelativeDimension m k Γ(X, W) := hφ.toAlgebra
  have : IsOpenImmersion hW.fromSpec := hW.isOpenImmersion_fromSpec
  -- `x` is the image of a closed point `y` of the chart `Spec Γ(X, W)`, a maximal ideal.
  obtain ⟨y, rfl⟩ : x ∈ Set.range hW.fromSpec := by rwa [hW.range_fromSpec]
  have hy : IsClosed ({y} : Set (Spec Γ(X, W))) :=
    preimage_closedPoints_subset hW.fromSpec.isOpenEmbedding.injective
      hW.fromSpec.continuous (Set.mem_preimage.mpr hx)
  have : y.asIdeal.IsMaximal := (PrimeSpectrum.isClosed_singleton_iff_isMaximal y).mp hy
  rw [ringKrullDim_stalk_eq_coheight, coheight_eq_of_isOpenImmersion, ← idealHeight_eq_coheight]
  exact_mod_cast height_eq_of_isStandardSmoothOfRelativeDimension k m y.asIdeal

/-- A morphism `f : X ⟶ Spec k` is smooth of relative dimension `n` if and only if it is smooth
and the local ring of `X` at every closed point has Krull dimension `n`. -/
theorem smoothOfRelativeDimension_iff_ringKrullDim_stalk_eq (n : ℕ) :
    SmoothOfRelativeDimension n f ↔
      Smooth f ∧ ∀ x : X, IsClosed {x} → ringKrullDim (X.presheaf.stalk x) = n := by
  refine ⟨fun _ ↦ ⟨SmoothOfRelativeDimension.smooth n f, fun x hx ↦ ?_⟩, fun ⟨_, hdim⟩ ↦ ⟨?_⟩⟩
  · obtain ⟨W, hxW, h⟩ :=
      SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension_appLE_top f n x
    exact ringKrullDim_stalk_eq_of_isStandardSmoothOfRelativeDimension f W.2 h hxW hx
  · intro x
    obtain ⟨U, hU, V, hV, hxV, e, hst⟩ := (Smooth.iff_forall_exists_isStandardSmooth f).mp ‹_› x
    -- The only nonempty open of `Spec k` is `⊤`.
    obtain rfl : U = ⊤ := eq_top_iff.mpr fun z _ ↦ Subsingleton.elim (f x) z ▸ e hxV
    -- The chart is standard smooth of some relative dimension `m`.
    let := (f.appLE ⊤ V e).hom.toAlgebra
    obtain ⟨ι, σ, _, _, ⟨P⟩⟩ := hst
    have hm : (f.appLE ⊤ V e).hom.IsStandardSmoothOfRelativeDimension P.dimension :=
      ⟨_, _, _, ‹_›, P, rfl⟩
    -- Comparing with a closed point of `X` in the chart shows `m = n`.
    have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace f
    obtain ⟨y, hyV, hy⟩ := nonempty_inter_closedPoints ⟨x, hxV⟩ V.isOpen.isLocallyClosed
    have hmn : P.dimension = n := by
      exact_mod_cast (ringKrullDim_stalk_eq_of_isStandardSmoothOfRelativeDimension f hV hm hyV
        hy).symm.trans (hdim y hy)
    exact ⟨⊤, hU, V, hV, hxV, e, hmn ▸ hm⟩

/-- A smooth irreducible scheme of dimension `n` over a field is smooth of relative
dimension `n`. -/
theorem smoothOfRelativeDimension_of_topologicalKrullDim_eq [Smooth f] [IrreducibleSpace X]
    {n : ℕ} (h : topologicalKrullDim X = n) : SmoothOfRelativeDimension n f :=
  (smoothOfRelativeDimension_iff_ringKrullDim_stalk_eq f n).mpr
    ⟨‹_›, fun _ hx ↦ (ringKrullDim_stalk_eq_topologicalKrullDim_of_isClosed f hx).trans h⟩

/-- A smooth curve over a field, an integral smooth scheme whose function field is an algebraic
function field of one variable, is smooth of relative dimension one. -/
theorem smoothOfRelativeDimension_one_of_isFunctionField [X.Over (Spec (.of k))] [IsIntegral X]
    [Smooth (X ↘ Spec (.of k))] (hF : IsFunctionField k X.functionField) :
    SmoothOfRelativeDimension 1 (X ↘ Spec (.of k)) :=
  smoothOfRelativeDimension_of_topologicalKrullDim_eq _ <| by
    exact_mod_cast (isFunctionField_functionField_iff k).mp hF

end TauCeti.AlgebraicGeometry
