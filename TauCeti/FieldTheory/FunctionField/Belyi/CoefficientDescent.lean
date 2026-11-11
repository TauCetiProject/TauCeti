/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Belyi.PointedStabilizer
public import TauCeti.FieldTheory.FunctionField.Belyi.SinglePole
public import TauCeti.FieldTheory.FunctionField.Belyi.FieldOfModuli
public import TauCeti.FieldTheory.RatFunc.Galois
public import TauCeti.FieldTheory.Minpoly.Lifts
public import TauCeti.FieldTheory.Galois.FiniteIndex

/-!
# Descent of the equation of a pointed Belyi pair

At a rational unbranched place of degree one, the generator of a Belyi pair normalized by its
Laurent expansion is fixed by every semilinear automorphism fixing that place. Its minimal
polynomial therefore has coefficients in the rational function field over the fixed field of
the pointed stabilizer. This works even when the original constant field is transcendental over
that fixed field, notably for subgroups of the automorphism group of `ℂ`.

We identify this coefficient field, bound its degree over the field of moduli, and produce a
primitive element whose minimal polynomial descends to it. This is descent of an equation;
unramifiedness and exactness of constants for a descended Belyi pair are not asserted here.

## References

* B. Köck, *Belyi's theorem revisited*, Beiträge zur Algebra und Geometrie 45 (2004), 253–265,
  proof of (2.2) Theorem.
-/

public section

open Polynomial IntermediateField

namespace TauCeti.AlgebraicBelyiPair

universe u

variable {k : Type u} [Field k] [CharZero k] (X : AlgebraicBelyiPair k)

/-- The fixed field of the pointed stabilizer of `P`. It is a coefficient field for the equation
obtained from a normalized generator, not by definition a field of definition of the pair. -/
noncomputable def pointedFieldOfModuli (P : Place k X) : IntermediateField ℚ k :=
  IntermediateField.fixedField (X.pointedStabilizer P)

/-- The pointed coefficient field is the fixed field of the pointed stabilizer. -/
theorem pointedFieldOfModuli_def (P : Place k X) :
    X.pointedFieldOfModuli P = IntermediateField.fixedField (X.pointedStabilizer P) := (rfl)

/-- An element belongs to the pointed fixed field precisely when the pointed stabilizer fixes
it. -/
@[simp]
theorem mem_pointedFieldOfModuli_iff (P : Place k X) (c : k) :
    c ∈ X.pointedFieldOfModuli P ↔ ∀ g ∈ X.pointedStabilizer P, g c = c := by
  simp [pointedFieldOfModuli, IntermediateField.mem_fixedField_iff]

/-- The field of moduli of a pair is contained in its pointed fixed field. -/
theorem fieldOfModuli_le_pointedFieldOfModuli (P : Place k X) :
    (IsoClass.mk X).fieldOfModuli ≤ X.pointedFieldOfModuli P := by
  rw [IsoClass.fieldOfModuli_def, pointedFieldOfModuli]
  exact IntermediateField.fixedField_le (X.pointedStabilizer_le_stabilizer P)

/-- Over a rational point, the pointed fixed field has positive relative finrank over the
field of moduli, so it is a finite extension. The original constant field can be transcendental
over both fields. -/
theorem relfinrank_pointedFieldOfModuli_pos {P : Place k X} {q : ℚ}
    (hP : P.restrict k (RatFunc k) = Place.adicOfIrreducible (irreducible_X_sub_C (q : k))) :
    0 < (IsoClass.mk X).fieldOfModuli.relfinrank (X.pointedFieldOfModuli P) := by
  rw [IsoClass.fieldOfModuli_def, pointedFieldOfModuli_def,
    IntermediateField.relfinrank_eq_finrank_of_le
      (IntermediateField.fixedField_le (X.pointedStabilizer_le_stabilizer P))]
  have := IntermediateField.finiteDimensional_fixedField_of_relIndex_ne_zero
    (X.pointedStabilizer_le_stabilizer P) (X.relIndex_pointedStabilizer_ne_zero hP)
  exact Module.finrank_pos

/-- Over a rational point, the pointed fixed field has degree at most the degree of the cover
over the field of moduli. No algebraicity of the original constant field is required. -/
theorem relfinrank_pointedFieldOfModuli_le {P : Place k X} {q : ℚ}
    (hP : P.restrict k (RatFunc k) = Place.adicOfIrreducible (irreducible_X_sub_C (q : k))) :
    (IsoClass.mk X).fieldOfModuli.relfinrank (X.pointedFieldOfModuli P) ≤
      Module.finrank (RatFunc k) X := by
  rw [IsoClass.fieldOfModuli_def, pointedFieldOfModuli]
  exact (IntermediateField.relfinrank_fixedField_le_relIndex (X.pointedStabilizer_le_stabilizer P)
    (X.relIndex_pointedStabilizer_ne_zero hP)).trans (X.relIndex_pointedStabilizer_le_finrank hP)

variable {X} {P : Place k X} {q : ℚ}
  (hq₀ : (q : k) ≠ 0) (hq₁ : (q : k) ≠ 1)
  (hPa : P.restrict k (RatFunc k) = Place.adicOfIrreducible (irreducible_X_sub_C (q : k)))
  (hP : P.degree = 1)

section Normalized

variable {m : ℕ} (hm : 0 < m) (hpole : P.IsPoleNumber m)
  (hgap : ∀ n, 0 < n → n < m → P.IsGap n) {z : X}
  (hz : z ∈ riemannRochSpace ((m : ℤ) • AlgebraicGeometry.WeilDivisor.ofPoint P))
  (h₁ : P.laurentCoeff hP (X.isAlgebraicBelyiPair.ord_algebraMap_X_sub_C hq₀ hq₁ hPa) (-m) z = 1)
  (h₀ : P.laurentCoeff hP (X.isAlgebraicBelyiPair.ord_algebraMap_X_sub_C hq₀ hq₁ hPa) 0 z = 0)

include hq₀ hq₁ hPa hP hm hpole hgap hz h₁ h₀

/-- Every member of the pointed stabilizer fixes the equation of the normalized generator. -/
theorem map_minpoly_eq_of_mem_pointedStabilizer {g : k ≃ₐ[ℚ] k}
    (hg : g ∈ X.pointedStabilizer P) :
    (minpoly (RatFunc k) z).map (RatFunc.mapRingEquiv (g : k ≃+* k) : RatFunc k →+* RatFunc k) =
      minpoly (RatFunc k) z := by
  obtain ⟨τ, hτ, hτP⟩ := mem_pointedStabilizer_iff.mp hg
  have hplace : Place.equivOfRingEquiv (g : k ≃+* k) τ
      (apply_algebraMap_eq_of_mapRingEquiv (g : k ≃+* k) τ hτ) P = P :=
    (smul_eq_self_iff_valuation_apply_eq
      (p := ⟨(τ, g), mem_semilinearAut_iff.mpr hτ⟩)).mpr hτP
  exact X.isAlgebraicBelyiPair.map_minpoly_eq_of_laurentCoeff_eq_one_of_laurentCoeff_zero_eq_zero
    hq₀ hq₁ hPa hP hm hpole hgap (by simp) hτ hplace hz h₁ h₀

variable [Algebra (RatFunc (X.pointedFieldOfModuli P)) (RatFunc k)]

/-- The equation of a normalized generator descends to the pointed fixed field. The map between
rational function fields must preserve the constants and send `X` to `X`. -/
theorem minpoly_mem_lifts_of_normalized
    (hC : ∀ c : X.pointedFieldOfModuli P,
      algebraMap (RatFunc (X.pointedFieldOfModuli P)) (RatFunc k) (RatFunc.C c) = RatFunc.C (c : k))
    (hX : algebraMap (RatFunc (X.pointedFieldOfModuli P)) (RatFunc k) RatFunc.X = RatFunc.X) :
    minpoly (RatFunc k) z ∈
      Polynomial.lifts (algebraMap (RatFunc (X.pointedFieldOfModuli P)) (RatFunc k)) := by
  let S : Set (k ≃+* k) := AlgEquiv.toRingEquiv '' (X.pointedStabilizer P : Set (k ≃ₐ[ℚ] k))
  have := RatFunc.isScalarTower_of_algebraMap_C hC
  refine RatFunc.mem_lifts_of_forall_map_mapRingEquiv_eq
    (F := X.pointedFieldOfModuli P) (K := k) hX (S := S) ?_ ?_
  · intro c hc
    refine ⟨⟨c, (X.mem_pointedFieldOfModuli_iff P c).mpr fun g hg ↦ ?_⟩, rfl⟩
    exact hc _ ⟨g, hg, rfl⟩
  · rintro _ ⟨g, hg, rfl⟩
    exact map_minpoly_eq_of_mem_pointedStabilizer hq₀ hq₁ hPa hP hm hpole hgap hz h₁ h₀ hg

end Normalized

include hq₀ hq₁ hPa hP

variable [Algebra (RatFunc (X.pointedFieldOfModuli P)) (RatFunc k)]

/-- At a rational unbranched place of degree one there is a primitive element whose equation
descends to the pointed fixed field. In particular this produces a descended equation, rather
than requiring invariance of an equation as a hypothesis. -/
theorem exists_generator_minpoly_mem_lifts
    (hC : ∀ c : X.pointedFieldOfModuli P,
      algebraMap (RatFunc (X.pointedFieldOfModuli P)) (RatFunc k) (RatFunc.C c) = RatFunc.C (c : k))
    (hX : algebraMap (RatFunc (X.pointedFieldOfModuli P)) (RatFunc k) RatFunc.X = RatFunc.X) :
    ∃ z : X, (RatFunc k)⟮z⟯ = ⊤ ∧ minpoly (RatFunc k) z ∈
      Polynomial.lifts (algebraMap (RatFunc (X.pointedFieldOfModuli P)) (RatFunc k)) := by
  have hF : IsFunctionField k X := (IsFunctionField.ratFunc k).finite_extension
  obtain ⟨m, hm, hpole, hgap⟩ := P.exists_pos_isPoleNumber_and_isGap_of_lt hF
    X.isAlgebraicBelyiPair.isIntegrallyClosedIn
  obtain ⟨z, ⟨hz, h₁, h₀, hgen⟩, -⟩ :=
    X.isAlgebraicBelyiPair.existsUnique_laurentCoeff_eq_one_and_adjoin_simple_eq_top
      hq₀ hq₁ hPa hP hm hpole hgap
  exact ⟨z, hgen, minpoly_mem_lifts_of_normalized hq₀ hq₁ hPa hP hm hpole hgap hz h₁ h₀ hC hX⟩

variable [Algebra (RatFunc (X.pointedFieldOfModuli P)) X]
  [IsScalarTower (RatFunc (X.pointedFieldOfModuli P)) (RatFunc k) X]

/-- The descended equation defines an extension of the pointed rational function field with
exactly the original degree. Its primitive element still generates the original field after
extending the rational function field. -/
theorem exists_generator_finrank_adjoin_eq
    (hC : ∀ c : X.pointedFieldOfModuli P,
      algebraMap (RatFunc (X.pointedFieldOfModuli P)) (RatFunc k) (RatFunc.C c) = RatFunc.C (c : k))
    (hX : algebraMap (RatFunc (X.pointedFieldOfModuli P)) (RatFunc k) RatFunc.X = RatFunc.X) :
    ∃ z : X, (RatFunc k)⟮z⟯ = ⊤ ∧
      IsIntegral (RatFunc (X.pointedFieldOfModuli P)) z ∧
      (minpoly (RatFunc (X.pointedFieldOfModuli P)) z).map
        (algebraMap (RatFunc (X.pointedFieldOfModuli P)) (RatFunc k)) = minpoly (RatFunc k) z ∧
      Module.finrank (RatFunc (X.pointedFieldOfModuli P))
        (RatFunc (X.pointedFieldOfModuli P))⟮z⟯ = Module.finrank (RatFunc k) X := by
  obtain ⟨z, hgen, hlift⟩ := exists_generator_minpoly_mem_lifts hq₀ hq₁ hPa hP hC hX
  have hz : IsIntegral (RatFunc k) z := Algebra.IsIntegral.isIntegral z
  have hz' := hz.of_minpoly_mem_lifts hlift
  refine ⟨z, hgen, hz', minpoly.map_algebraMap hz' hlift, ?_⟩
  rw [IntermediateField.finrank_adjoin_simple_eq_of_minpoly_mem_lifts hz hlift, hgen,
    IntermediateField.finrank_top']

end TauCeti.AlgebraicBelyiPair
