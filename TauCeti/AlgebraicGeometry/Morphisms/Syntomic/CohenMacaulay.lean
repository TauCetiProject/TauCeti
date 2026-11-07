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
# Syntomic morphisms and Cohen–Macaulay schemes

Every scheme syntomic of fixed relative dimension over a Cohen–Macaulay scheme is
Cohen–Macaulay; in particular so is every scheme syntomic over a field. Since syntomicity is
stable under arbitrary base change, all field-valued fibres of a syntomic morphism are
Cohen–Macaulay, including geometric fibres over any algebraically closed extension of a residue
field.

The proof uses the local complete-intersection presentations, not smoothness or reducedness.
For nodal families this gives the Cohen–Macaulay fibre hypothesis needed to construct a
relative dualizing sheaf.

## References

* The Stacks Project, Section 10.135, *Local complete intersections* (Tag 00S8).
* The Stacks Project, Section 29.30, *Syntomic morphisms* (Tag 01UB).
* H. Matsumura, *Commutative Ring Theory*, Corollary of Theorem 23.3.
-/

public section

open CategoryTheory Limits
open TauCeti TauCeti.AlgebraicGeometry

namespace AlgebraicGeometry.Scheme

universe u

variable {n : ℕ} {X Y : Scheme.{u}}

/-- A scheme syntomic of fixed relative dimension over a Cohen–Macaulay scheme is
Cohen–Macaulay. -/
theorem IsCohenMacaulay.of_syntomic (f : X ⟶ Y) [SyntomicOfRelativeDimension n f]
    [Y.IsCohenMacaulay] : X.IsCohenMacaulay := by
  have := SyntomicOfRelativeDimension.locallyOfFinitePresentation n f
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  refine ⟨fun x ↦ ?_⟩
  obtain ⟨U, V, hxV, e, hf⟩ :=
    SyntomicOfRelativeDimension.exists_isStandardSyntomicOfRelativeDimension (n := n) (f := f) x
  have := U.2.isCohenMacaulay
  let := (f.appLE U V e).hom.toAlgebra
  have : TauCeti.Algebra.IsStandardSyntomicOfRelativeDimension n Γ(Y, U) Γ(X, V) :=
    (isStandardSyntomicOfRelativeDimension_iff n _).mp hf
  have := TauCeti.Algebra.IsStandardSyntomicOfRelativeDimension.isCohenMacaulay
    (n := n) (R := Γ(Y, U)) (S := Γ(X, V))
  exact (isCohenMacaulay_stalk_iff_of_isAffineOpen V.2 ⟨x, hxV⟩).mpr
    (TauCeti.Ring.IsCohenMacaulay.isCohenMacaulay_localization _)

/-- Every field-valued fibre of a syntomic morphism of fixed relative dimension is
Cohen–Macaulay. This includes geometric fibres, with no hypothesis on the original base. -/
theorem Hom.isCohenMacaulay_pullback_of_syntomic {k : Type u} [Field k]
    (f : X ⟶ Y) [SyntomicOfRelativeDimension n f] (g : Spec (.of k) ⟶ Y) :
    (pullback f g).IsCohenMacaulay :=
  .of_syntomic (n := n) (pullback.snd f g)

end AlgebraicGeometry.Scheme
