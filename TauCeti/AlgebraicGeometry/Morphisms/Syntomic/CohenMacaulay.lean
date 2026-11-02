/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Morphisms.Syntomic.Basic
public import TauCeti.AlgebraicGeometry.Scheme.CohenMacaulay
public import TauCeti.RingTheory.Syntomic.CohenMacaulay

/-!
# Cohen–Macaulay fibres of syntomic morphisms

Every scheme syntomic of fixed relative dimension over a field is Cohen–Macaulay. Since
syntomicity is stable under arbitrary base change, all field-valued fibres are Cohen–Macaulay,
including geometric fibres over any algebraically closed extension of a residue field.

The proof uses the local complete-intersection presentations, not smoothness or reducedness.
For nodal families this gives the Cohen–Macaulay fibre hypothesis needed to construct a
relative dualizing sheaf.

## References

* The Stacks Project, Section 10.135, *Local complete intersections* (Tag 00S8).
* The Stacks Project, Section 29.30, *Syntomic morphisms* (Tag 01UB).
-/

public section

open CategoryTheory Limits
open TauCeti TauCeti.AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Hom

universe u

variable {n : ℕ} {X S : Scheme.{u}}

/-- A scheme syntomic of fixed relative dimension over a field is Cohen–Macaulay. -/
theorem isCohenMacaulay_of_syntomic_of_field {k : Type u} [Field k]
    (f : X ⟶ Spec (.of k)) [SyntomicOfRelativeDimension n f] : X.IsCohenMacaulay := by
  have := SyntomicOfRelativeDimension.locallyOfFinitePresentation n f
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  refine ⟨fun x ↦ ?_⟩
  obtain ⟨W, hxW, e, hW⟩ :=
    SyntomicOfRelativeDimension.exists_isStandardSyntomicOfRelativeDimension_appLE_top n f x
  -- Transport the chart's base ring along the canonical isomorphism k ≅ Γ(Spec k, ⊤).
  let φ := (Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ W e
  have hφ : IsStandardSyntomicOfRelativeDimension n φ.hom := by
    rw [CommRingCat.hom_comp]
    exact (isStandardSyntomicOfRelativeDimension_respectsIso n).right _
      (Scheme.ΓSpecIso (.of k)).symm.commRingCatIsoToRingEquiv hW
  let := φ.hom.toAlgebra
  have : TauCeti.Algebra.IsStandardSyntomicOfRelativeDimension n k Γ(X, W) :=
    (isStandardSyntomicOfRelativeDimension_iff n φ.hom).mp hφ
  have := TauCeti.Algebra.IsStandardSyntomicOfRelativeDimension.finitePresentation
    (n := n) (R := k) (S := Γ(X, W))
  have : IsNoetherianRing Γ(X, W) := Algebra.FiniteType.isNoetherianRing k Γ(X, W)
  exact (Scheme.isCohenMacaulay_stalk_iff_of_isAffineOpen W.2 ⟨x, hxW⟩).mpr
    (TauCeti.Algebra.IsStandardSyntomicOfRelativeDimension.isCohenMacaulay_localization
      (n := n) (k := k) _)

/-- Every field-valued fibre of a syntomic morphism of fixed relative dimension is
Cohen–Macaulay. This includes geometric fibres, with no hypothesis on the original base. -/
theorem isCohenMacaulay_pullback_of_syntomic {k : Type u} [Field k]
    (f : X ⟶ S) [SyntomicOfRelativeDimension n f] (g : Spec (.of k) ⟶ S) :
    (pullback f g).IsCohenMacaulay :=
  (pullback.snd f g).isCohenMacaulay_of_syntomic_of_field (n := n)

end AlgebraicGeometry.Scheme.Hom
