/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Action.CrossedProduct.Representation
public import TauCeti.Analysis.CStarAlgebra.Action.CrossedProduct.Multiplier

/-!
# Nondegenerate representations of the full crossed product come from covariant pairs

Let `L` be a nondegenerate representation of the full crossed product `A ⋊_α G` on a Hilbert
space `H`. Extending `L` to the multiplier algebra by `NonUnitalStarAlgHom.multiplierExtension`
(written `L'`) and composing with the canonical multipliers `i_A` and `i_G` gives a covariant pair

`π(a) = L'(i_A(a))` and `U_s = L'(i_G(s))`,

`NonUnitalStarAlgHom.toCovariantRepresentation`. Its coefficient representation is nondegenerate
and its extended integrated form is `L` itself. Together with the uniqueness theorem
`CovariantRepresentation.ext_integratedFull`, this makes integration a bijection between covariant
pairs with nondegenerate coefficient representation and nondegenerate representations of the full
crossed product.

The key identity is the integral formula
`∫ i_A(f(s)) i_G(s) y dμ(s) = f * y` for `f` compactly supported and `y` in the full crossed
product, `FullCrossedProduct.integral_coefficientMultiplier_mul_groupMultiplier_fst`.

No unit, separability or σ-finiteness is assumed, and the Hilbert space may lie in any universe.

## Main declarations

* `NonUnitalStarAlgHom.toCovariantRepresentation`: the covariant pair of a nondegenerate
  representation of the full crossed product.
* `NonUnitalStarAlgHom.integratedFull_toCovariantRepresentation`: its integrated form is the
  given representation.
* `TauCeti.CStarAction.CovariantRepresentation.toCovariantRepresentation_integratedFull`: a
  covariant pair with nondegenerate coefficient representation is recovered from its integrated
  form.
* `NonUnitalStarAlgHom.IsNondegenerate.existsUnique_covariantRepresentation_integratedFull`: every
  nondegenerate representation is the integrated form of a unique covariant pair with
  nondegenerate coefficient representation.

## References

* Dana Williams, *Crossed Products of C*-Algebras*, Proposition 2.40, whose proof we follow
  through the canonical multipliers `FullCrossedProduct.coefficientMultiplier` and
  `FullCrossedProduct.groupMultiplier` and the multiplier extension of a nondegenerate
  representation.
-/

public section

noncomputable section

open MeasureTheory
open scoped CStarAlgebra CompactlySupported MultiplierAlgebra

namespace NonUnitalStarAlgHom

open TauCeti TauCeti.CStarAction TauCeti.CStarAction.FullCrossedProduct

universe u v

variable {G : Type u} {A : Type v} [Group G] [TopologicalSpace G] [MeasurableSpace G]
  [NonUnitalCStarAlgebra A] {α : CStarAction G A} {μ : Measure G}
  [IsTopologicalGroup G] [LocallyCompactSpace G] [BorelSpace G] [μ.IsHaarMeasure]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (L : FullCrossedProduct α μ →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (hL : L.IsNondegenerate)

/-- The covariant pair `(L' ∘ i_A, L' ∘ i_G)` of a nondegenerate representation `L` of the full
crossed product, where `L'` is the extension of `L` to the multiplier algebra. Its integrated form
is `L` (`integratedFull_toCovariantRepresentation`). -/
def toCovariantRepresentation : CovariantRepresentation α H where
  coefficient := (L.multiplierExtension hL).toNonUnitalStarAlgHom.comp (coefficientMultiplier α μ)
  group := .ofMonoidHom <| (L.multiplierExtension hL).toMonoidHom.comp
    ((unitary 𝓜(ℂ, FullCrossedProduct α μ)).subtype.comp (groupMultiplier α μ))
  isUnitary := (ContRepresentation.isUnitary_iff_mem_unitary _).2 fun r =>
    Unitary.map_mem (L.multiplierExtension hL) (groupMultiplier α μ r).2
  continuous_orbit ξ := continuous_multiplierExtension_apply hL
    (u := fun r => (groupMultiplier α μ r : 𝓜(ℂ, FullCrossedProduct α μ)))
    continuous_groupMultiplier_fst_apply (fun r => by
      simpa using (CStarRing.norm_coe_unitary_mul (groupMultiplier α μ r) 1).trans_le
        (IsStarProjection.one _).norm_le) ξ
  covariance r a ξ := by
    have h := congr(L.multiplierExtension hL $(groupMultiplier_mul_coefficientMultiplier r a) ξ)
    rw [map_mul, map_mul, mul_apply_eq_comp, mul_apply_eq_comp] at h
    exact h

/-- The coefficient representation of `L.toCovariantRepresentation hL` is the multiplier
extension of `L` composed with the canonical coefficient map. -/
@[simp]
theorem toCovariantRepresentation_coefficient_apply (a : A) :
    (L.toCovariantRepresentation hL).coefficient a =
      L.multiplierExtension hL (coefficientMultiplier α μ a) :=
  (rfl)

/-- The group representation of `L.toCovariantRepresentation hL` is the multiplier extension of
`L` composed with the canonical group map. -/
@[simp]
theorem toCovariantRepresentation_group_apply (r : G) :
    (L.toCovariantRepresentation hL).group r =
      L.multiplierExtension hL (groupMultiplier α μ r : 𝓜(ℂ, FullCrossedProduct α μ)) :=
  (rfl)

/-- The extended integrated form of the covariant pair of a nondegenerate representation `L` of
the full crossed product is `L`. -/
@[simp]
theorem integratedFull_toCovariantRepresentation :
    (L.toCovariantRepresentation hL).integratedFull μ = L := by
  refine starAlgHom_ext <| NonUnitalStarAlgHom.ext fun f => ?_
  refine hL.ext fun y => ContinuousLinearMap.ext fun ξ => ?_
  let Φ : FullCrossedProduct α μ →L[ℂ] H := (ContinuousLinearMap.apply ℂ H ξ).comp
    { toLinearMap := (L : _ →ₗ[ℂ] (H →L[ℂ] H)), cont := map_continuous _ }
  have hΦ (x) : Φ x = L x ξ := rfl
  rw [NonUnitalStarAlgHom.comp_apply, NonUnitalStarAlgHom.comp_apply, ← map_mul, ← hΦ,
    ← integral_coefficientMultiplier_mul_groupMultiplier_fst,
    ← Φ.integral_comp_comm (integrable_coefficientMultiplier_mul_groupMultiplier_fst f y),
    mul_apply_eq_comp, CovariantRepresentation.integratedFull_of_apply]
  simp [hΦ, DoubleCentralizer.mul_fst]

/-- The coefficient representation of the covariant pair of a nondegenerate representation of the
full crossed product is nondegenerate. -/
@[simp]
theorem isNondegenerate_toCovariantRepresentation_coefficient :
    (L.toCovariantRepresentation hL).coefficient.IsNondegenerate := by
  rw [← CovariantRepresentation.isNondegenerate_integratedFull_iff (μ := μ),
    integratedFull_toCovariantRepresentation]
  exact hL

/-- On compactly supported functions, the integrated form of the covariant pair of a nondegenerate
representation `L` of the full crossed product is `L`. -/
@[simp]
theorem integratedOperator_toCovariantRepresentation (f : C_c(G, A)) :
    (L.toCovariantRepresentation hL).integratedOperator μ f =
      L (of α μ (ConvolutionAlgebra.toConv f)) := by
  simpa only [CovariantRepresentation.integratedFull_of,
    CovariantRepresentation.integratedStarAlgHom_apply, ConvolutionAlgebra.ofConv_toConv] using
    congr($(integratedFull_toCovariantRepresentation L hL)
      (of α μ (ConvolutionAlgebra.toConv f)))

/-- The covariant pair of a nondegenerate representation `L` of the full crossed product is the
unique covariant pair with nondegenerate coefficient representation whose integrated form is
`L`. -/
theorem eq_toCovariantRepresentation_iff {P : CovariantRepresentation α H} :
    P = L.toCovariantRepresentation hL ↔
      P.coefficient.IsNondegenerate ∧ P.integratedFull μ = L :=
  ⟨fun h => h ▸ ⟨isNondegenerate_toCovariantRepresentation_coefficient L hL,
      integratedFull_toCovariantRepresentation L hL⟩,
    fun h => CovariantRepresentation.ext_integratedFull μ h.1
      (h.2.trans (integratedFull_toCovariantRepresentation L hL).symm)⟩

/-- Every nondegenerate representation of the full crossed product is the extended integrated
form of a unique covariant pair whose coefficient representation is nondegenerate (Williams,
Proposition 2.40). -/
theorem IsNondegenerate.existsUnique_covariantRepresentation_integratedFull
    {L : FullCrossedProduct α μ →⋆ₙₐ[ℂ] (H →L[ℂ] H)} (hL : L.IsNondegenerate) :
    ∃! P : CovariantRepresentation α H,
      P.coefficient.IsNondegenerate ∧ P.integratedFull μ = L :=
  ⟨L.toCovariantRepresentation hL, (eq_toCovariantRepresentation_iff L hL).1 rfl,
    fun _ => (eq_toCovariantRepresentation_iff L hL).2⟩

end NonUnitalStarAlgHom

namespace TauCeti.CStarAction.CovariantRepresentation

variable {G : Type*} {A : Type*} [Group G] [TopologicalSpace G] [MeasurableSpace G]
  [NonUnitalCStarAlgebra A] {α : CStarAction G A} {μ : Measure G}
  [IsTopologicalGroup G] [LocallyCompactSpace G] [BorelSpace G] [μ.IsHaarMeasure]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A covariant pair with nondegenerate coefficient representation is the covariant pair of its
integrated form. -/
@[simp]
theorem toCovariantRepresentation_integratedFull (P : CovariantRepresentation α H)
    (hP : (P.integratedFull μ).IsNondegenerate) :
    (P.integratedFull μ).toCovariantRepresentation hP = P :=
  ((NonUnitalStarAlgHom.eq_toCovariantRepresentation_iff _ hP).2
    ⟨(isNondegenerate_integratedFull_iff μ P).1 hP, rfl⟩).symm

end TauCeti.CStarAction.CovariantRepresentation
