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
and composing with the canonical multipliers `i_A` and `i_G` gives a covariant pair

`π(a) = L̃(i_A(a))` and `U_s = L̃(i_G(s))`,

`NonUnitalStarAlgHom.toCovariantRepresentation`. Its coefficient representation is nondegenerate
and its extended integrated form is `L` itself. Together with the uniqueness theorem
`CovariantRepresentation.ext_integratedFull`, this makes integration a bijection between covariant
pairs with nondegenerate coefficient representation and nondegenerate representations of the full
crossed product.

The key identity is the integral formula
`∫ i_A(f(s)) i_G(s) y dμ(s) = f * y` for `f` compactly supported and `y` in the full crossed
product, a Bochner integral in the full crossed product.

No unit, separability or σ-finiteness is assumed, and the Hilbert space may lie in any universe.

## Main declarations

* `TauCeti.CStarAction.FullCrossedProduct.integral_coefficientMultiplier_mul_groupMultiplier_fst`:
  the integral formula above.
* `NonUnitalStarAlgHom.toCovariantRepresentation`: the covariant pair of a nondegenerate
  representation of the full crossed product.
* `NonUnitalStarAlgHom.integratedFull_toCovariantRepresentation`: its integrated form is the
  given representation.
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
open scoped CStarAlgebra MultiplierAlgebra

namespace TauCeti.CStarAction.FullCrossedProduct

universe u v

variable {G : Type u} {A : Type v} [Group G] [TopologicalSpace G] [MeasurableSpace G]
  [NonUnitalCStarAlgebra A] {α : CStarAction G A} {μ : Measure G}
  [IsTopologicalGroup G] [LocallyCompactSpace G] [BorelSpace G] [μ.IsHaarMeasure]

/-- The integrand `s ↦ i_A(f(s)) i_G(s) y` of the integral formula is continuous. -/
private theorem continuous_coefficientMultiplier_mul_groupMultiplier_fst
    (f : ConvolutionAlgebra α μ) (y : FullCrossedProduct α μ) :
    Continuous fun s => (coefficientMultiplier α μ (f.ofConv s) *
      (groupMultiplier α μ s : 𝓜(ℂ, FullCrossedProduct α μ))).fst y := by
  simp only [DoubleCentralizer.mul_fst, mul_apply_eq_comp]
  have hfst : Continuous fun m : 𝓜(ℂ, FullCrossedProduct α μ) => m.fst :=
    DoubleCentralizer.isUniformEmbedding_toProdMulOpposite.uniformContinuous.continuous.fst
  exact (hfst.comp ((map_continuous (coefficientMultiplier α μ)).comp
    f.ofConv.continuous)).clm_apply (continuous_groupMultiplier_fst_apply y)

/-- The integrand `s ↦ i_A(f(s)) i_G(s) y` of the integral formula is integrable. -/
private theorem integrable_coefficientMultiplier_mul_groupMultiplier_fst
    (f : ConvolutionAlgebra α μ) (y : FullCrossedProduct α μ) :
    Integrable (fun s => (coefficientMultiplier α μ (f.ofConv s) *
      (groupMultiplier α μ s : 𝓜(ℂ, FullCrossedProduct α μ))).fst y) μ := by
  refine (continuous_coefficientMultiplier_mul_groupMultiplier_fst f y
    ).integrable_of_hasCompactSupport (f.ofConv.hasCompactSupport.mono fun s hs hzero => hs ?_)
  simp [hzero]

/-- An element of the twisted convolution algebra acts on the full crossed product as the
integral of its canonical multipliers: `∫ i_A(f(s)) i_G(s) y dμ(s) = f * y`. -/
theorem integral_coefficientMultiplier_mul_groupMultiplier_fst (f : ConvolutionAlgebra α μ)
    (y : FullCrossedProduct α μ) :
    ∫ s, (coefficientMultiplier α μ (f.ofConv s) *
      (groupMultiplier α μ s : 𝓜(ℂ, FullCrossedProduct α μ))).fst y ∂μ = of α μ f * y := by
  have hint := integrable_coefficientMultiplier_mul_groupMultiplier_fst f y
  set F : G → FullCrossedProduct α μ := fun s => (coefficientMultiplier α μ (f.ofConv s) *
    (groupMultiplier α μ s : 𝓜(ℂ, FullCrossedProduct α μ))).fst y
  rw [← sub_eq_zero, ← norm_le_zero_iff, norm_le_iff]
  intro H _ _ _ P
  -- Every integrated form takes the same value at both sides.
  suffices h : P.integratedFull μ (∫ s, F s ∂μ) = P.integratedFull μ (of α μ f * y) by
    rw [map_sub, h, sub_self, norm_zero]
  let Φ : FullCrossedProduct α μ →L[ℂ] (H →L[ℂ] H) := ⟨P.integratedFull μ, map_continuous _⟩
  have hΦ : ∫ s, P.integratedFull μ (F s) ∂μ = P.integratedFull μ (∫ s, F s ∂μ) :=
    Φ.integral_comp_comm hint
  have hΦint : Integrable (fun s => P.integratedFull μ (F s)) μ := Φ.integrable_comp hint
  rw [← hΦ]
  ext ξ
  rw [ContinuousLinearMap.integral_apply hΦint, map_mul, CovariantRepresentation.integratedFull_of,
    CovariantRepresentation.integratedStarAlgHom_apply, mul_apply_eq_comp,
    CovariantRepresentation.integratedOperator_apply]
  simp [F, DoubleCentralizer.mul_fst]

end TauCeti.CStarAction.FullCrossedProduct

namespace NonUnitalStarAlgHom

open TauCeti TauCeti.CStarAction TauCeti.CStarAction.FullCrossedProduct

universe u v

variable {G : Type u} {A : Type v} [Group G] [TopologicalSpace G] [MeasurableSpace G]
  [NonUnitalCStarAlgebra A] {α : CStarAction G A} {μ : Measure G}
  [IsTopologicalGroup G] [LocallyCompactSpace G] [BorelSpace G] [μ.IsHaarMeasure]

/-- The canonical unitary multipliers have norm at most one. -/
private theorem norm_groupMultiplier_le (r : G) :
    ‖(groupMultiplier α μ r : 𝓜(ℂ, FullCrossedProduct α μ))‖ ≤ 1 := by
  rcases subsingleton_or_nontrivial 𝓜(ℂ, FullCrossedProduct α μ) with h | h
  · simp [Subsingleton.elim (groupMultiplier α μ r : 𝓜(ℂ, FullCrossedProduct α μ)) 0]
  · exact (CStarRing.norm_coe_unitary _).le

section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (L : FullCrossedProduct α μ →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (hL : L.IsNondegenerate)

/-- The covariant pair `(L̃ ∘ i_A, L̃ ∘ i_G)` of a nondegenerate representation `L` of the full
crossed product, where `L̃` is the extension of `L` to the multiplier algebra. Its integrated form
is `L` (`integratedFull_toCovariantRepresentation`). -/
def toCovariantRepresentation : CovariantRepresentation α H where
  coefficient := (L.multiplierExtension hL).toNonUnitalStarAlgHom.comp (coefficientMultiplier α μ)
  group := .ofMonoidHom <| (L.multiplierExtension hL).toMonoidHom.comp
    ((unitary 𝓜(ℂ, FullCrossedProduct α μ)).subtype.comp (groupMultiplier α μ))
  isUnitary := (ContRepresentation.isUnitary_iff_mem_unitary _).2 fun r =>
    Unitary.map_mem (L.multiplierExtension hL) (groupMultiplier α μ r).2
  continuous_orbit ξ := continuous_multiplierExtension_apply hL
    (u := fun r => (groupMultiplier α μ r : 𝓜(ℂ, FullCrossedProduct α μ)))
    continuous_groupMultiplier_fst_apply norm_groupMultiplier_le ξ
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
  have hint := integrable_coefficientMultiplier_mul_groupMultiplier_fst f y
  set F : G → FullCrossedProduct α μ := fun s => (coefficientMultiplier α μ (f.ofConv s) *
    (groupMultiplier α μ s : 𝓜(ℂ, FullCrossedProduct α μ))).fst y
  let Φ : FullCrossedProduct α μ →L[ℂ] (H →L[ℂ] H) := ⟨L, map_continuous L⟩
  have hΦ : ∫ s, L (F s) ∂μ = L (∫ s, F s ∂μ) := Φ.integral_comp_comm hint
  have hΦint : Integrable (fun s => L (F s)) μ := Φ.integrable_comp hint
  rw [NonUnitalStarAlgHom.comp_apply, NonUnitalStarAlgHom.comp_apply, ← map_mul,
    ← integral_coefficientMultiplier_mul_groupMultiplier_fst, ← hΦ, mul_apply_eq_comp,
    ContinuousLinearMap.integral_apply hΦint, CovariantRepresentation.integratedFull_of,
    CovariantRepresentation.integratedStarAlgHom_apply,
    CovariantRepresentation.integratedOperator_apply]
  simp [F, DoubleCentralizer.mul_fst]

end

variable {H : Type (max u v)} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (L : FullCrossedProduct α μ →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (hL : L.IsNondegenerate)

/-- The coefficient representation of the covariant pair of a nondegenerate representation of the
full crossed product is nondegenerate. -/
theorem isNondegenerate_toCovariantRepresentation_coefficient :
    (L.toCovariantRepresentation hL).coefficient.IsNondegenerate := by
  rw [← CovariantRepresentation.isNondegenerate_integratedFull_iff (μ := μ),
    integratedFull_toCovariantRepresentation]
  exact hL

/-- Every nondegenerate representation of the full crossed product is the extended integrated
form of a unique covariant pair whose coefficient representation is nondegenerate (Williams,
Proposition 2.40). -/
theorem IsNondegenerate.existsUnique_covariantRepresentation_integratedFull
    {L : FullCrossedProduct α μ →⋆ₙₐ[ℂ] (H →L[ℂ] H)} (hL : L.IsNondegenerate) :
    ∃! P : CovariantRepresentation α H,
      P.coefficient.IsNondegenerate ∧ P.integratedFull μ = L :=
  ⟨L.toCovariantRepresentation hL,
    ⟨isNondegenerate_toCovariantRepresentation_coefficient L hL,
      integratedFull_toCovariantRepresentation L hL⟩,
    fun _ hP => CovariantRepresentation.ext_integratedFull μ hP.1
      (hP.2.trans (integratedFull_toCovariantRepresentation L hL).symm)⟩

end NonUnitalStarAlgHom
