/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Geom.Torsion
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.RelativeFrobenius.Supersingular
import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.FieldPoints
import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Geom.BaseChange.Basic
import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Geom.MulBy.Rank
import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Geom.Torsion.Unramified
import TauCeti.AlgebraicGeometry.Morphisms.Etale
import TauCeti.AlgebraicGeometry.ResidueField

/-!
# The `n`-torsion of an elliptic curve is étale exactly where `n` is invertible

Let `E` be an elliptic curve over a scheme `S` and `n` a nonzero integer. The `n`-torsion `E[n]` is
finite locally free of rank `n²` over `S`. This file proves that it is étale over `S` exactly when
`n` is invertible in every residue field of `S` (Katz–Mazur 2.3.1).

Where `n` is invertible, `E[n]` is flat and locally of finite presentation over `S`, and formally
unramified (`EllipticCurveGeom.formallyUnramified_torsion_hom`), so it is étale. Over a residue
field of characteristic `p` dividing `n`, an elliptic curve has fewer than `n²` points of order
dividing `n`, even over an algebraically closed field: it has at most `p` points of order dividing
`p` (Silverman III.6.4). A finite étale scheme over a separably closed field has as many rational
points as its rank (`AlgebraicGeometry.Scheme.Hom.natCard_eq_finrank_of_etale`), so the base change
of `E[n]` to an algebraic closure of that residue field, of rank `n²`, is not étale, and neither is
`E[n]`.

## Main results

* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.natCard_torsion_lt`: over a field in which the
  nonzero integer `n` vanishes, `E[n]` has fewer than `n²` points with values in the field.
* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.etale_torsion_hom_of_forall_intCast_ne_zero`: if
  `n` is invertible in every residue field of `S`, then `E[n]` is étale over `S`; it is finite
  over `S`, so it is finite étale.
* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.etale_subscheme_of_ker_torsionι_le`: a flat,
  locally finitely presented closed subscheme of `E` contained in `E[n]` is étale over `S`
  where `n` is invertible.
* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.etale_torsion_hom_iff`: for `n ≠ 0`, `E[n]` is
  étale over `S` if and only if `n` is invertible in every residue field of `S`.

## References

* N. M. Katz and B. Mazur, *Arithmetic Moduli of Elliptic Curves*, 2.3.1.
* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.6.4.
-/

public section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory

universe u

namespace TauCeti.AlgebraicGeometry.EllipticCurveGeom

section Field

variable {K : Type u} [Field K] (E : EllipticCurveGeom (Spec (.of K)))

/-- **An elliptic curve has fewer than `n²` points of order dividing `n` when `n` vanishes in the
field.** For an elliptic curve `E` over a field `K` and a nonzero integer `n` with `(n : K) = 0`,
the `n`-torsion `E[n]` has fewer than `n.natAbs ^ 2` points with values in `Spec K`, although it
has rank `n.natAbs ^ 2` over `Spec K`. -/
theorem natCard_torsion_lt {n : ℤ} (hn : n ≠ 0) (hnK : (n : K) = 0) :
    Nat.card (𝟙_ (Over (Spec (.of K))) ⟶ (E.torsion n).X) < n.natAbs ^ 2 := by
  obtain ⟨W, _, hW⟩ := E.exists_natCard_torsion_eq
  -- the characteristic `p` of `K` is a prime dividing `n`
  have hpn : (ringChar K : ℤ) ∣ n := (CharP.intCast_eq_zero_iff K (ringChar K) n).1 hnK
  have hp : (ringChar K).Prime := by
    refine (CharP.char_is_prime_or_zero K (ringChar K)).resolve_right fun h ↦ hn ?_
    rwa [h, Nat.cast_zero, zero_dvd_iff] at hpn
  have : Fact (ringChar K).Prime := ⟨hp⟩
  rw [hW]
  exact WeierstrassCurve.natCard_torsionBy_lt (ringChar K) W hp hn hpn

end Field

variable {S : Scheme.{u}} (E : EllipticCurveGeom S)

/-- **The `n`-torsion of an elliptic curve is étale where `n` is invertible** (Katz–Mazur 2.3.1).
For an elliptic curve `E` over a scheme `S` and an integer `n` invertible in every residue field of
`S`, the `n`-torsion `E[n]` is étale over `S`. It is also finite over `S`
(`EllipticCurveGeom.isFinite_torsion_hom`), so `E[n]` is finite étale over `S`. -/
theorem etale_torsion_hom_of_forall_intCast_ne_zero {n : ℤ}
    (hn : ∀ s : S, (n : S.residueField s) ≠ 0) : Etale (E.torsion n).X.hom := by
  rcases isEmpty_or_nonempty S with hS | ⟨⟨s⟩⟩
  · have : IsEmpty (E.torsion n).X.left :=
      ⟨fun x ↦ isEmptyElim ((E.torsion n).X.hom x)⟩
    infer_instance
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact hn s Int.cast_zero
  have := E.flat_torsion_hom hn0
  have := E.formallyUnramified_torsion_hom hn
  exact Etale.of_formallyUnramified_of_flat _

/-- A flat, locally finitely presented closed subscheme of `E` contained in `E[n]` is étale
over the base when `n` is invertible in every residue field. Containment is expressed as the
reverse inclusion of ideal sheaves. -/
theorem etale_subscheme_of_ker_torsionι_le (I : E.carrier.IdealSheafData) {n : ℤ}
    [Flat (I.subschemeι ≫ E.structureMap)]
    [LocallyOfFinitePresentation (I.subschemeι ≫ E.structureMap)]
    (hn : ∀ s : S, (n : S.residueField s) ≠ 0) (hle : (E.torsionι n).left.ker ≤ I) :
    Etale (I.subschemeι ≫ E.structureMap) := by
  let j := IsClosedImmersion.lift (E.torsionι n).left I.subschemeι (by simpa using hle)
  have hj : j ≫ (E.torsionι n).left = I.subschemeι := IsClosedImmersion.lift_fac _ _ _
  have : Etale (E.torsion n).X.hom := E.etale_torsion_hom_of_forall_intCast_ne_zero hn
  have : FormallyUnramified (j ≫ (E.torsionι n).left) := by rw [hj]; infer_instance
  have : FormallyUnramified j := .of_comp j (E.torsionι n).left
  have : FormallyUnramified (I.subschemeι ≫ E.structureMap) := by
    rw [← hj, Category.assoc, torsionι_left_structureMap]
    exact MorphismProperty.comp_mem _ _ _ inferInstance inferInstance
  exact Etale.of_formallyUnramified_of_flat _

/-- **Criterion for `E[n]` to be étale** (Katz–Mazur 2.3.1). For an elliptic curve `E` over a
scheme `S` and a nonzero integer `n`, the `n`-torsion `E[n]` is étale over `S` if and only if `n` is
invertible in every residue field of `S`. -/
theorem etale_torsion_hom_iff {n : ℤ} (hn : n ≠ 0) :
    Etale (E.torsion n).X.hom ↔ ∀ s : S, (n : S.residueField s) ≠ 0 := by
  refine ⟨fun _ s hns ↦ ?_, E.etale_torsion_hom_of_forall_intCast_ne_zero⟩
  -- the base change `E'` of `E` to an algebraic closure `L` of the residue field at `s`
  let L := AlgebraicClosure (S.residueField s)
  let t := S.fromSpecAlgebraicClosure s
  let E' := E.baseChange t
  have h0 : E'.zero ≫ (E.baseChangeIso t).hom ≫ pullback.fst _ _ = t ≫ E.zero := by simp [E']
  -- `E'[n]` is the base change of `E[n]`, so it is finite étale over `Spec L`, of rank `n²`
  have : Etale (E'.torsion n).X.hom :=
    MorphismProperty.of_isPullback (isPullback_torsionMap n (E.isPullback_baseChange t) h0) ‹_›
  have : IsFinite (E'.torsion n).X.hom := E'.isFinite_torsion_hom hn
  obtain ⟨a⟩ : Nonempty (Spec (.of L)) := inferInstance
  have hcard := (E'.torsion n).X.hom.natCard_eq_finrank_of_etale a
  rw [E'.finrank_torsion_hom hn] at hcard
  -- but `n` vanishes in `L`, so `E'[n]` has fewer than `n²` points over `Spec L`
  have hnL : (n : L) = 0 := by
    rw [← map_intCast (algebraMap (S.residueField s) L), hns, map_zero]
  exact (E'.natCard_torsion_lt hn hnL).ne hcard

end TauCeti.AlgebraicGeometry.EllipticCurveGeom
