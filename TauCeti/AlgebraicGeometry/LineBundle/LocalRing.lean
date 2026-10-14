/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.LineBundle.Functoriality

/-!
# Line bundles on local schemes are trivial

If every point of a scheme `X` specializes to a single point `x`, then the only open subset of
`X` containing `x` is `X` itself. A line bundle is trivial on some open neighbourhood of `x`, so it
is trivial on `X`, and the Picard group of `X` is trivial. This applies to the spectrum of a local
ring, and in particular to the spectrum of a field.

The triviality of `Pic(Spec K)` for a field `K` is what makes invariants of line bundles computed
on the fibres `Spec K ×_T X_T` of a base change insensitive to line bundles pulled back from the
base `T`.

## Main declarations

* `TauCeti.AlgebraicGeometry.LineBundleClass.eq_one_of_forall_specializes`: on a scheme in which
  every point specializes to a fixed point, every line-bundle class is trivial;
* `TauCeti.AlgebraicGeometry.LineBundleClass.subsingleton_spec_of_isLocalRing`: the Picard group
  of the spectrum of a local ring is trivial.

## References

* R. Hartshorne, *Algebraic Geometry*, Chapter II, Section 6.
-/

public section

open CategoryTheory

namespace TauCeti

namespace AlgebraicGeometry

open _root_.AlgebraicGeometry

universe u

noncomputable section

namespace LineBundleClass

variable {X : Scheme.{u}}

/-- **Line bundles on a local scheme are trivial.** If every point of `X` specializes to `x`, then
every line-bundle class on `X` is the identity. -/
theorem eq_one_of_forall_specializes {x : X} (hx : ∀ y : X, y ⤳ x) (a : LineBundleClass X) :
    a = 1 := by
  obtain ⟨L, rfl⟩ := mk_surjective a
  obtain ⟨V, e, hxV⟩ := Scheme.Modules.exists_mem_trivialization L.obj x
  -- An open subset containing `x` contains every point, since every point generalizes `x`.
  obtain rfl : V = ⊤ := eq_top_iff.mpr fun y _ ↦ (hx y).mem_open V.isOpen hxV
  have h : pullback (⊤ : X.Opens).ι (mk L) = 1 := by
    rw [pullback_mk, mk_eq_one_iff]
    exact ⟨((Scheme.Modules.restrictFunctorIsoPullback _).app L.obj).symm ≪≫
      (TauCeti.SheafOfModules.LocalTrivializations.unitIsoRestrict e).symm⟩
  calc mk L = pullback X.topIso.inv (pullback (⊤ : X.Opens).ι (mk L)) := by
        rw [pullback_comp, Scheme.toIso_inv_ι, pullback_id]
    _ = 1 := by rw [h, pullback_one]

/-- **The Picard group of the spectrum of a local ring is trivial.** In particular every line
bundle on the spectrum of a field is trivial. -/
instance subsingleton_spec_of_isLocalRing (R : Type u) [CommRing R] [IsLocalRing R] :
    Subsingleton (LineBundleClass (Spec (.of R))) :=
  ⟨fun a b ↦ (eq_one_of_forall_specializes IsLocalRing.specializes_closedPoint a).trans
    (eq_one_of_forall_specializes IsLocalRing.specializes_closedPoint b).symm⟩

end LineBundleClass

end

end AlgebraicGeometry

end TauCeti
