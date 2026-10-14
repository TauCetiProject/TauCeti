/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Geom.Torsion.Etale.Locus
public import TauCeti.AlgebraicGeometry.GroupScheme.Etale
import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Geom.MulBy.Rank

/-!
# Étale multiplication on an elliptic curve over an arbitrary base

Multiplication by an integer invertible in every residue field of the base is étale on the
whole elliptic curve. Its kernel is the torsion scheme `E[n]`, which is formally unramified
and flat over the base.
The kernel-pair identity identifies the self-pullback of `[n]` with `E[n] × E`, whose
projection to `E` is étale. Étaleness then descends along the finite faithfully flat
multiplication map.

This supplies the étaleness of multiplication needed to lift prime-to-characteristic
division points through infinitesimal thickenings.

## Main results

* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.etale_mulBy_left_of_forall_intCast_ne_zero`:
  multiplication by an integer invertible in every residue field is étale.

## References

* N. M. Katz and B. Mazur, *Arithmetic Moduli of Elliptic Curves*, 2.3.1.
-/

public section

open CategoryTheory AlgebraicGeometry

universe u

namespace TauCeti.AlgebraicGeometry.EllipticCurveGeom

/-- Multiplication by an integer invertible in every residue field of the base is étale
(Katz–Mazur 2.3.1). No reducedness or Noetherian hypothesis on the base is needed. -/
theorem etale_mulBy_left_of_forall_intCast_ne_zero {S : Scheme.{u}}
    (E : EllipticCurveGeom S) {n : ℤ} (hn : ∀ s : S, (n : S.residueField s) ≠ 0) :
    Etale (E.mulBy n).left := by
  rcases isEmpty_or_nonempty S with hS | hS
  · have : IsEmpty E.carrier := ⟨fun x ↦ isEmptyElim (E.structureMap x)⟩
    have : IsIso (E.mulBy n).left :=
      @_root_.AlgebraicGeometry.isIso_of_isEmpty E.carrier E.carrier (E.mulBy n).left inferInstance
    infer_instance
  have hn₀ : n ≠ 0 := by
    obtain ⟨s⟩ := hS
    rintro rfl
    exact hn s Int.cast_zero
  have := E.isFinite_mulBy_left hn₀
  have := E.flat_mulBy_left hn₀
  have := E.surjective_mulBy_left hn₀
  have hT := E.etale_torsion_hom_of_forall_intCast_ne_zero hn
  have : Surjective (Grp.ofHom (E.mulBy n)).hom.hom.left := by
    simpa only [Grp.ofHom_hom_hom] using E.surjective_mulBy_left hn₀
  have : Flat (Grp.ofHom (E.mulBy n)).hom.hom.left := by
    simpa only [Grp.ofHom_hom_hom] using E.flat_mulBy_left hn₀
  have : QuasiCompact (Grp.ofHom (E.mulBy n)).hom.hom.left := by
    simpa only [Grp.ofHom_hom_hom] using
      (inferInstance : QuasiCompact (E.mulBy n).left)
  rw [E.torsion_eq_kernel, E.forget₂Grp_map_intCast] at hT
  simpa only [Grp.ofHom_hom_hom] using
    (Grp.etale_iff_etale_kernel (Grp.ofHom (E.mulBy n))).mpr hT

end TauCeti.AlgebraicGeometry.EllipticCurveGeom
