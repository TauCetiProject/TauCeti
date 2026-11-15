/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Geom.Torsion
public import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Geom.Torsion.Etale.Basic
import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Geom.MulBy.Finite
import TauCeti.AlgebraicGeometry.Morphisms.FormallyUnramified

/-!
# Unramified elliptic torsion over an arbitrary base

For an elliptic curve `E/S` and an integer `n` invertible in every residue field of `S`,
the torsion scheme `E[n]` is formally unramified over `S`. Together with local finite type,
this is unramifiedness; combined with flatness and local finite presentation, it gives étaleness.

The field-valued fibres are the torsion schemes of the base-changed elliptic curves, by
`EllipticCurveGeom.isPullback_torsionMap`. They are étale by the field-level theorem
`EllipticCurveGeom.etale_torsion_hom`. The relative conclusion uses
`Scheme.Hom.formallyUnramified_of_formallyUnramified_baseChange_field`.

## References

* N. M. Katz and B. Mazur, *Arithmetic Moduli of Elliptic Curves*, 2.3.1.
-/

public section

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace TauCeti.AlgebraicGeometry.EllipticCurveGeom

variable {S : Scheme.{u}} (E : EllipticCurveGeom S)

/-- The torsion scheme `E[n]` is formally unramified over any base on which the integer `n`
is invertible in every residue field. -/
theorem formallyUnramified_torsion_hom {n : ℤ}
    (hn : ∀ s : S, (n : S.residueField s) ≠ 0) : FormallyUnramified (E.torsion n).X.hom := by
  rcases isEmpty_or_nonempty S with hS | hS
  · have : IsEmpty (E.torsion n).X.left :=
      ⟨fun x ↦ isEmptyElim ((E.torsion n).X.hom x)⟩
    infer_instance
  have hn0 : n ≠ 0 := by
    obtain ⟨s⟩ := hS
    intro h
    exact hn s (by simp [h])
  have : IsFinite (E.torsion n).X.hom := E.isFinite_torsion_hom hn0
  refine ((E.torsion n).X.hom).formallyUnramified_of_formallyUnramified_baseChange_field
    fun K _ t ↦ ?_
  let E' := E.baseChange t
  have hg := E.isPullback_baseChange t
  have h0 : E'.zero ≫ (E.baseChangeIso t).hom ≫ pullback.fst _ _ = t ≫ E.zero := by
    simp [E']
  -- A field-valued point factors through the residue field of its image, so `n` remains nonzero.
  let φ := (S.descResidueField (Scheme.stalkClosedPointTo t)).hom
  have hnK : (n : K) ≠ 0 := by
    rw [← map_intCast φ, map_ne_zero]
    exact hn _
  have : Etale (E'.torsion n).X.hom := E'.etale_torsion_hom hnK
  have hT := isPullback_torsionMap n hg h0
  have : FormallyUnramified (hT.isoPullback.inv ≫ (E'.torsion n).X.hom) := inferInstance
  rw [hT.isoPullback_inv_snd] at this
  exact this

end TauCeti.AlgebraicGeometry.EllipticCurveGeom
