/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Degree.Basic
public import TauCeti.AlgebraicGeometry.IdealSheaf.Rank

/-!
# Incidence of relative effective Cartier divisors of equal degree

Proper relative effective Cartier divisors on a relative curve are finite and flat over
the base. Consequently, containment between two such divisors of equal degree is equality.
For every test scheme of the fixed-degree divisor functor, its incidence relation is therefore
the equality relation. This also applies after arbitrary base change, since each test scheme
is allowed and the degree condition is preserved by the divisor functor.

We state incidence using the underlying ideal sheaves, whose order reverses containment
of closed subschemes. Since the conclusion is equality, either orientation gives the same
criterion.
-/

public section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X S : Scheme.{u}} {I J : X.IdealSheafData} {f : X ⟶ S}

/-- If `I` is a proper relative effective Cartier divisor on a relative curve and `J` is a
relative effective Cartier divisor with the same rank function, containment of their ideal
sheaves is equivalent to equality. No properness assumption on `J` is needed: the containment
puts its closed subscheme inside that of `I`. -/
theorem IsRelativeEffectiveCartier.le_iff_eq_of_finrank_eq
    [LocallyOfFiniteType f] [TauCeti.AlgebraicGeometry.RelativeDimensionLE 1 f]
    [IsProper (I.subschemeι ≫ f)]
    (hI : I.IsRelativeEffectiveCartier f) (hJ : J.IsRelativeEffectiveCartier f)
    (hrank : (I.subschemeι ≫ f).finrank = (J.subschemeι ≫ f).finrank) :
    I ≤ J ↔ I = J := by
  have := hI.isFinite_iff_isProper.mpr inferInstance
  have := hI.flat
  have := hJ.flat
  exact ⟨fun h ↦ eq_of_le_of_finrank_eq h f hrank, fun h ↦ h.le⟩

end AlgebraicGeometry.Scheme.IdealSheafData

namespace TauCeti.AlgebraicGeometry

open _root_.AlgebraicGeometry

variable {X S : Scheme.{u}} (f : X ⟶ S) [IsProper f] [RelativeDimensionLE 1 f]

/-- On every test scheme, the incidence relation between relative effective Cartier divisors
of the same fixed degree is equality. -/
@[simp↓]
theorem relativeEffectiveCartierDegreeSubfunctor_le_iff_eq {d : ℕ} {T : (Over S)ᵒᵖ}
    (D E : (relativeEffectiveCartierDegreeSubfunctor f d).toFunctor.obj T) :
    D.1.1 ≤ E.1.1 ↔ D = E := by
  have hD : (D.1.1 : (pullback T.unop.hom f).IdealSheafData).IsRelativeEffectiveCartier
      (pullback.fst T.unop.hom f) :=
    (mem_relativeEffectiveCartierSubfunctor_obj_iff (f := f)).mp D.1.2
  have hE : (E.1.1 : (pullback T.unop.hom f).IdealSheafData).IsRelativeEffectiveCartier
      (pullback.fst T.unop.hom f) :=
    (mem_relativeEffectiveCartierSubfunctor_obj_iff (f := f)).mp E.1.2
  have hrank : (D.1.1.subschemeι ≫ pullback.fst T.unop.hom f).finrank =
      (E.1.1.subschemeι ≫ pullback.fst T.unop.hom f).finrank :=
    ((mem_relativeEffectiveCartierDegreeSubfunctor_obj_iff (f := f)).mp D.2).trans
      ((mem_relativeEffectiveCartierDegreeSubfunctor_obj_iff (f := f)).mp E.2).symm
  refine ⟨fun h ↦ Subtype.ext (Subtype.ext ?_), fun h ↦ h ▸ le_rfl⟩
  have := hD.isFinite
  exact (hD.le_iff_eq_of_finrank_eq hE hrank).mp h

end TauCeti.AlgebraicGeometry
