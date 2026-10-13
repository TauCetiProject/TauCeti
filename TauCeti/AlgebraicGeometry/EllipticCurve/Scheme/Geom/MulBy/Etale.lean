/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Geom.Torsion.Etale.Basic
import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent
import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Geom.MulBy.Rank
import TauCeti.CategoryTheory.Monoidal.Grp.KernelPair

/-!
# Étale multiplication on an elliptic curve over a field

Multiplication by an integer invertible in the base field is étale on the whole elliptic
curve, not just over its zero section. Its kernel is the étale torsion scheme `E[n]`.
The kernel-pair identity identifies the self-pullback of `[n]` with `E[n] × E`, whose
projection to `E` is étale. Étaleness then descends along the finite faithfully flat
multiplication map.

This supplies the étaleness of multiplication needed to lift prime-to-characteristic
division points through infinitesimal thickenings.

## Main results

* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.etale_mulBy_left_of_field`: multiplication by
  an integer invertible in the base field is étale.

## References

* N. M. Katz and B. Mazur, *Arithmetic Moduli of Elliptic Curves*, 2.3.1.
-/

public section

open CategoryTheory Limits CartesianMonoidalCategory AlgebraicGeometry

universe u

namespace TauCeti.AlgebraicGeometry.EllipticCurveGeom

/-- Multiplication by an integer invertible in the base field is étale
(Katz–Mazur 2.3.1). -/
theorem etale_mulBy_left_of_field {K : Type u} [Field K]
    (E : EllipticCurveGeom (Spec (.of K))) {n : ℤ} (hn : (n : K) ≠ 0) :
    Etale (E.mulBy n).left := by
  have hn₀ : n ≠ 0 := by
    rintro rfl
    exact hn Int.cast_zero
  have := E.isFinite_mulBy_left hn₀
  have := E.flat_mulBy_left hn₀
  have := E.surjective_mulBy_left hn₀
  have := E.etale_torsion_hom hn
  have hk : IsPullback (E.torsionι n) (toUnit (E.torsion n).X)
      (E.mulBy n) MonObj.one := by
    apply IsPullback.of_map_of_faithful (Over.forget _)
    simpa only [Over.forget_map, Over.toUnit_left, E.one_left] using E.isPullback_torsion n
  -- In the self-pullback, `[n]` becomes the projection `E[n] × E ⟶ E`.
  have h := (isPullback_mul_of_isPullback_one (E.mulBy n) (E.torsionι n) hk).map (Over.forget _)
  have hs : Etale (snd (E.torsion n).X (Over.mk E.structureMap)).left := by
    rw [Over.snd_left]
    infer_instance
  have hf : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme)
      (E.mulBy n).left := ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩
  exact MorphismProperty.of_isPullback_of_descendsAlong h.flip hf hs

end TauCeti.AlgebraicGeometry.EllipticCurveGeom
