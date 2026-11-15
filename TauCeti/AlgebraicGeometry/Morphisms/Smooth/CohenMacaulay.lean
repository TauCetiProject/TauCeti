/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import TauCeti.AlgebraicGeometry.Scheme.CohenMacaulay
public import TauCeti.RingTheory.CohenMacaulay.Smooth

/-!
# Smooth schemes over Cohen–Macaulay schemes are Cohen–Macaulay

If `f : X ⟶ Y` is a smooth morphism and `Y` is Cohen–Macaulay, then `X` is Cohen–Macaulay. On
affine opens `U ⊆ f⁻¹ V` this is `TauCeti.Ring.IsCohenMacaulay.of_smooth`, since the ring of
sections of a Cohen–Macaulay scheme over an affine open is a Cohen–Macaulay ring. The relative
dimension of `f` may vary from point to point.

## References

* H. Matsumura, *Commutative Ring Theory*, Corollary of Theorem 23.3.
-/

public section

open CategoryTheory

namespace AlgebraicGeometry.Scheme

universe u

variable {X Y : Scheme.{u}}

/-- A scheme smooth over a Cohen–Macaulay scheme is Cohen–Macaulay. -/
theorem IsCohenMacaulay.of_smooth (f : X ⟶ Y) [Smooth f] [Y.IsCohenMacaulay] :
    X.IsCohenMacaulay := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  refine ⟨fun x ↦ ?_⟩
  obtain ⟨V, hV, hxV, -⟩ := exists_isAffineOpen_mem_and_subset
    (TopologicalSpace.Opens.mem_top (f x))
  obtain ⟨U, hU, hxU, hUV⟩ := exists_isAffineOpen_mem_and_subset (f.mem_preimage.mpr hxV)
  have := hV.isCohenMacaulay
  let := (f.appLE V U hUV).hom.toAlgebra
  have : Algebra.Smooth Γ(Y, V) Γ(X, U) :=
    (HasRingHomProperty.appLE @Smooth f ‹_› ⟨V, hV⟩ ⟨U, hU⟩ hUV).toAlgebra
  have := TauCeti.Ring.IsCohenMacaulay.of_smooth (R := Γ(Y, V)) (S := Γ(X, U))
  exact (isCohenMacaulay_stalk_iff_of_isAffineOpen hU ⟨x, hxU⟩).mpr
    (TauCeti.Ring.IsCohenMacaulay.isCohenMacaulay_localization _)

end AlgebraicGeometry.Scheme
