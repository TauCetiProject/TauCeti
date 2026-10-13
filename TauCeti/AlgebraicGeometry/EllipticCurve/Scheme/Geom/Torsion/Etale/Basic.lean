/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Geom.Torsion
import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.FieldPoints
import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Geom.BaseChange.Basic
import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Geom.MulBy.Rank
import TauCeti.AlgebraicGeometry.Morphisms.Etale

/-!
# The `n`-torsion of an elliptic curve over a field is étale when `n` is invertible

Let `E` be an elliptic curve over a field `K` and let `n` be an integer which is invertible in `K`.
This file proves that the `n`-torsion `E[n]` (`EllipticCurveGeom.torsion`) is étale over
`Spec K`, part of Katz–Mazur 2.3.1.

Over a separably closed field, `E[n]` is finite over `Spec K` of rank `n²`
(`EllipticCurveGeom.finrank_torsion_hom`) and has `n²` points with values in `Spec K`
(`EllipticCurveGeom.natCard_torsion`). A finite scheme over a field with as many rational points
as its rank is étale (`AlgebraicGeometry.Scheme.Hom.etale_of_finrank_le_natCard`). Over an arbitrary
field `K`, the `n`-torsion of the base change of `E` to an algebraic closure of `K` is the base
change of `E[n]` (`EllipticCurveGeom.isPullback_torsionMap`), and étaleness descends along the
faithfully flat morphism `Spec (AlgebraicClosure K) ⟶ Spec K`.

## Main results

* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.etale_torsion_hom`: over a field in which `n` is
  invertible, the `n`-torsion `E[n]` is étale.

## References

* N. M. Katz and B. Mazur, *Arithmetic Moduli of Elliptic Curves*, 2.3.1.
-/

public section

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace TauCeti.AlgebraicGeometry.EllipticCurveGeom

variable {K : Type u} [Field K] (E : EllipticCurveGeom (Spec (.of K)))

/-- **The `n`-torsion of an elliptic curve over a field is étale** when `n` is invertible
(Katz–Mazur 2.3.1). For an elliptic curve `E` over a field `K` and an integer `n` with
`(n : K) ≠ 0`, the `n`-torsion `E[n]` is étale over `Spec K`. -/
theorem etale_torsion_hom {n : ℤ} (hn : (n : K) ≠ 0) : Etale (E.torsion n).X.hom := by
  have hn₀ : n ≠ 0 := by
    rintro rfl
    exact hn Int.cast_zero
  -- the base change `E'` of `E` to an algebraic closure `L` of `K`
  let L := AlgebraicClosure K
  let t : Spec (.of L) ⟶ Spec (.of K) := Spec.map (CommRingCat.ofHom (algebraMap K L))
  let E' := E.baseChange t
  have hg := E.isPullback_baseChange t
  have h0 : E'.zero ≫ (E.baseChangeIso t).hom ≫ pullback.fst _ _ = t ≫ E.zero := by simp [E']
  -- over `L`, `E'[n]` has rank `n²` and `n²` points, so it is étale; the points of
  -- `Over.mk (E'.torsion n).X.hom` are those of `(E'.torsion n).X`, by eta for structures
  have hnL : (n : L) ≠ 0 := by
    rwa [← map_intCast (algebraMap K L), map_ne_zero]
  have : IsFinite (E'.torsion n).X.hom := E'.isFinite_torsion_hom hn₀
  obtain ⟨s⟩ : Nonempty (Spec (.of L)) := inferInstance
  have : Etale (E'.torsion n).X.hom :=
    (E'.torsion n).X.hom.etale_of_finrank_le_natCard s
      (by rw [E'.finrank_torsion_hom hn₀]; exact (E'.natCard_torsion hnL).ge)
  -- étaleness descends along the faithfully flat morphism `Spec L ⟶ Spec K`
  have ht : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme) t := by
    refine ⟨⟨?_, Flat.SpecMap_iff.mpr (RingHom.flat_algebraMap_iff.mpr inferInstance)⟩,
      inferInstance⟩
    exact ⟨fun x ↦ ⟨s, Subsingleton.elim _ _⟩⟩
  exact MorphismProperty.of_isPullback_of_descendsAlong (isPullback_torsionMap n hg h0).flip ht this

end TauCeti.AlgebraicGeometry.EllipticCurveGeom
