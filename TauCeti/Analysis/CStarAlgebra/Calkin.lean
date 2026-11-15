/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.l2Space
public import TauCeti.Analysis.CStarAlgebra.Quotient
public import TauCeti.Analysis.InnerProductSpace.BorelCalculus.Basic
public import TauCeti.Analysis.Normed.Operator.Compact.Ideal
import TauCeti.Analysis.Normed.Lp.Basic

/-!
# Closed ideals of bounded operators and simplicity of the Calkin algebra

For a complex Hilbert space `H`, the compact operators form a norm-closed two-sided ideal
`ContinuousLinearMap.compactIdeal ℂ H` of `H →L[ℂ] H`, hence a nonunital C⋆-algebra on its subtype
carrier via `TwoSidedIdeal.nonUnitalCStarAlgebra`. The quotient C⋆-algebra
`TauCeti.CalkinAlgebra H := (H →L[ℂ] H) ⧸ ContinuousLinearMap.compactIdeal ℂ H` is the **Calkin
algebra** of `H`.

This file proves Calkin's classification of closed two-sided ideals of `H →L[ℂ] H` and characterizes
when the Calkin algebra is a simple ring:
1. In any C⋆-algebra `A`, a closed two-sided ideal `I` satisfies `star a * a ∈ I ↔ a ∈ I`
   (`TwoSidedIdeal.star_mul_self_mem_iff_of_isClosed`), so any ideal `J` not contained in `I`
   contains a self-adjoint (hence normal) element outside `I`.
2. For a normal operator `a : H →L[ℂ] H` and `ε > 0`, the spectral projection
   `a.spectralCutoff ε` onto `{z ∈ spectrum ℂ a | ε ≤ ‖z‖}` lies in every two-sided ideal containing
   `a` and satisfies `‖a - a * a.spectralCutoff ε‖ ≤ ε`. Consequently, if `a` avoids a closed
   two-sided ideal `I`, some spectral cutoff `a.spectralCutoff ε` (`ε > 0`) is a star projection
   avoiding `I`.
3. When `H` is separable, a noncompact star projection `p ∈ J` admits an isometry `v : H →ₗᵢ[ℂ] H`
   with `star v * p * v = 1`
   (`IsStarProjection.exists_linearIsometry_mul_eq_and_star_mul_mul_eq_one`), forcing `J = ⊤`.
   Hence the closed two-sided ideals of `H →L[ℂ] H` are precisely `⊥`, `compactIdeal ℂ H`, and `⊤`;
   conversely, this three-ideal property implies `SeparableSpace H` via `separableRangeIdeal ℂ H`.
4. Passing to the quotient and using the Neumann-series closure of maximal two-sided ideals in
   Banach rings (`IsSimpleRing.of_forall_isClosed_eq_bot_or_eq_top`), `CalkinAlgebra H` is
   algebraically simple (`IsSimpleRing (CalkinAlgebra H)`) if and only if `H` is separable and
   infinite-dimensional. In particular, `CalkinAlgebra ℓ²(ℕ, ℂ)` is unconditionally a simple
   C⋆-algebra, while `CalkinAlgebra (EuclideanSpace ℂ (Fin 2))` is a subsingleton.

## Main declarations

* `TwoSidedIdeal.star_mul_self_mem_iff_of_isClosed`: in a C⋆-algebra, `star a * a ∈ I ↔ a ∈ I` for
  any closed two-sided ideal `I`.
* `ContinuousLinearMap.spectralCutoff`: the spectral projection of a normal operator `a` onto
  `{z : spectrum ℂ a | ε ≤ ‖(z : ℂ)‖}`, with ideal membership `spectralCutoff_mem_twoSidedIdeal` and
  tail bound `norm_sub_mul_spectralCutoff_le`.
* `ContinuousLinearMap.eq_bot_or_eq_compactIdeal_or_eq_top_of_isClosed` and
  `ContinuousLinearMap.forall_isClosed_eq_bot_or_eq_compactIdeal_or_eq_top_iff`: Calkin's
  classification of closed two-sided ideals of `H →L[ℂ] H` and its equivalence with
  `SeparableSpace H`.
* `TauCeti.CalkinAlgebra`: the unital C⋆-algebra
  `(H →L[ℂ] H) ⧸ ContinuousLinearMap.compactIdeal ℂ H`, with quotient projection
  `TauCeti.CalkinAlgebra.mk` and essential-norm formula `TauCeti.CalkinAlgebra.norm_mk_eq`.
* `TauCeti.CalkinAlgebra.subsingleton_iff_finiteDimensional`,
  `TauCeti.CalkinAlgebra.isSimpleRing`, and `TauCeti.CalkinAlgebra.isSimpleRing_iff`: triviality and
  algebraic simplicity characterizations of the Calkin algebra, instantiated unconditionally on
  `ℓ²(ℕ, ℂ)` (`TauCeti.CalkinAlgebra.instIsSimpleRingL2`) and `EuclideanSpace ℂ n`
  (`TauCeti.CalkinAlgebra.instSubsingletonEuclideanSpace`).

## References

* J. W. Calkin, *Two-sided ideals and congruences in the ring of bounded operators in Hilbert
  space*, Annals of Mathematics 42 (1941), 839–873, Theorem 1.7.
* G. J. Murphy, *C*-Algebras and Operator Theory*, Academic Press (1990), Theorem 2.4.9 and §3.1.
* K. R. Davidson, *C*-Algebras by Example*, Fields Institute Monographs 6, AMS (1996), Theorem I.5.4
  and Example I.5.6.
-/

public noncomputable section

open Filter TauCeti TopologicalSpace Topology
open scoped ComplexConjugate ENNReal InnerProductSpace lp

namespace TwoSidedIdeal

variable {A : Type*} [NonUnitalCStarAlgebra A] (I : TwoSidedIdeal A) [IsClosed (I : Set A)]

/-- In a C⋆-algebra, `star a * a` belongs to a closed two-sided ideal `I` if and only if `a ∈ I`,
since the quotient `A ⧸ I` is a C⋆-algebra and therefore has a proper involution. -/
@[simp]
theorem star_mul_self_mem_iff_of_isClosed {a : A} : star a * a ∈ I ↔ a ∈ I := by
  refine ⟨fun h ↦ ?_, fun ha ↦ I.mul_mem_left (star a) a ha⟩
  rw [← Quotient.eq_zero_iff_mem] at h ⊢
  rwa [map_mul, Quotient.mk_star, star_mul_self_eq_zero] at h

/-- In a C⋆-algebra, `a * star a` belongs to a closed two-sided ideal `I` if and only if `a ∈ I`. -/
@[simp]
theorem mul_star_self_mem_iff_of_isClosed {a : A} : a * star a ∈ I ↔ a ∈ I := by
  simpa only [star_star, star_mem_iff_of_isClosed] using
    I.star_mul_self_mem_iff_of_isClosed (a := star a)

/-- If a two-sided ideal `J` of a C⋆-algebra is not contained in a closed two-sided ideal `I`, then
`J` contains a self-adjoint element outside `I`. -/
theorem exists_isSelfAdjoint_mem_notMem {J : TwoSidedIdeal A} (hJI : ¬ J ≤ I) :
    ∃ b ∈ J, b ∉ I ∧ IsSelfAdjoint b := by
  obtain ⟨a, haJ, haI⟩ := Set.not_subset.mp hJI
  exact ⟨star a * a, J.mul_mem_left (star a) a haJ,
    mt I.star_mul_self_mem_iff_of_isClosed.mp haI, IsSelfAdjoint.star_mul_self a⟩

end TwoSidedIdeal

namespace ContinuousLinearMap

section SpectralCutoff

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
/-- Measurability of the closed spectral tail `{z : spectrum ℂ a | ε ≤ ‖(z : ℂ)‖}`. -/
private theorem measurableSet_spectralCutoffSet (a : H →L[ℂ] H) (ε : ℝ) :
    MeasurableSet {z : spectrum ℂ a | ε ≤ ‖(z : ℂ)‖} :=
  (isClosed_le continuous_const (continuous_norm.comp continuous_subtype_val)).measurableSet

/-- For a normal operator `a : H →L[ℂ] H` and `ε : ℝ`, `a.spectralCutoff ε` is the spectral
projection of `a` onto `{z ∈ spectrum ℂ a | ε ≤ ‖z‖}`. -/
def spectralCutoff (a : H →L[ℂ] H) [IsStarNormal a] (ε : ℝ) : H →L[ℂ] H :=
  a.spectralPVM.proj {z : spectrum ℂ a | ε ≤ ‖(z : ℂ)‖} (measurableSet_spectralCutoffSet a ε)

/-- Every spectral cutoff of a normal operator is a star projection. -/
theorem isStarProjection_spectralCutoff (a : H →L[ℂ] H) [IsStarNormal a] (ε : ℝ) :
    IsStarProjection (a.spectralCutoff ε) :=
  a.spectralPVM.isStarProjection_proj _ _

/-- For `ε > 0`, `a.spectralCutoff ε` belongs to every two-sided ideal containing `a`: on
`{z ∈ spectrum ℂ a | ε ≤ ‖z‖}`, `1 = z * (conj z * (max (ε ^ 2) (‖z‖ ^ 2))⁻¹)`. -/
theorem spectralCutoff_mem_twoSidedIdeal (a : H →L[ℂ] H) [IsStarNormal a]
    {I : TwoSidedIdeal (H →L[ℂ] H)} (ha : a ∈ I) {ε : ℝ} (hε : 0 < ε) :
    a.spectralCutoff ε ∈ I := by
  let B : Set (spectrum ℂ a) := {z : spectrum ℂ a | ε ≤ ‖(z : ℂ)‖}
  have hB : MeasurableSet B := measurableSet_spectralCutoffSet a ε
  let invMap : C(spectrum ℂ a, ℂ) :=
    ⟨fun z ↦ conj (z : ℂ) * ((max (ε ^ 2) (‖(z : ℂ)‖ ^ 2) : ℝ) : ℂ)⁻¹, by
      refine (Complex.continuous_conj.comp continuous_subtype_val).mul ?_
      refine Continuous.inv₀ ?_ fun _ ↦ Complex.ofReal_ne_zero.mpr ?_
      · exact Complex.continuous_ofReal.comp
          (continuous_const.max ((continuous_norm.comp continuous_subtype_val).pow 2))
      · positivity⟩
  let g : BoundedBorelFunction (spectrum ℂ a) :=
    BoundedBorelFunction.indicator B hB (BoundedBorelFunction.ofContinuousMap invMap)
  let idSym : BoundedBorelFunction (spectrum ℂ a) :=
    BoundedBorelFunction.ofContinuousMap ((ContinuousMap.id ℂ).restrict (spectrum ℂ a))
  have hprod : idSym * g = BoundedBorelFunction.indicator B hB 1 := by
    ext z
    by_cases hz : z ∈ B
    · have hle : ε ^ 2 ≤ ‖(z : ℂ)‖ ^ 2 := pow_le_pow_left₀ hε.le hz 2
      have hne : ((‖(z : ℂ)‖ : ℂ) ^ 2) ≠ 0 :=
        pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr (hε.trans_le hz).ne')
      simp only [BoundedBorelFunction.mul_apply, BoundedBorelFunction.indicator_apply,
        Set.indicator_of_mem hz, BoundedBorelFunction.one_apply, idSym, g,
        BoundedBorelFunction.ofContinuousMap_apply, ContinuousMap.restrict_apply,
        ContinuousMap.id_apply, invMap, ContinuousMap.coe_mk, max_eq_right hle]
      rw [← mul_assoc, RCLike.mul_conj, RCLike.ofReal_eq_complex_ofReal, Complex.ofReal_pow,
        mul_inv_cancel₀ hne]
    · simp [idSym, g, hz]
  have heq : a.spectralCutoff ε = a * a.borelCalculus g := by
    rw [spectralCutoff, ← a.borelCalculus_indicator hB, ← hprod, map_mul,
      a.borelCalculus_restrict_id]
  rw [heq]
  exact I.mul_mem_right a _ ha

/-- Truncating the spectrum of a normal operator `a` below radius `ε ≥ 0` changes `a` by at most
`ε` in operator norm. -/
theorem norm_sub_mul_spectralCutoff_le (a : H →L[ℂ] H) [IsStarNormal a] {ε : ℝ} (hε : 0 ≤ ε) :
    ‖a - a * a.spectralCutoff ε‖ ≤ ε := by
  let B : Set (spectrum ℂ a) := {z : spectrum ℂ a | ε ≤ ‖(z : ℂ)‖}
  have hB : MeasurableSet B := measurableSet_spectralCutoffSet a ε
  let idSym : BoundedBorelFunction (spectrum ℂ a) :=
    BoundedBorelFunction.ofContinuousMap ((ContinuousMap.id ℂ).restrict (spectrum ℂ a))
  have heq : a - a * a.spectralCutoff ε =
      a.borelCalculus (idSym - idSym * BoundedBorelFunction.indicator B hB 1) := by
    rw [spectralCutoff, map_sub, map_mul, a.borelCalculus_restrict_id, a.borelCalculus_indicator hB]
  rw [heq]
  refine a.norm_borelCalculus_le hε fun z ↦ ?_
  by_cases hz : z ∈ B
  · simpa [hz] using hε
  · have hlt : ‖(z : ℂ)‖ < ε := not_le.mp hz
    simpa [idSym, hz] using hlt.le

/-- Along `ε = 1 / (n + 1)`, `a * a.spectralCutoff (1 / (n + 1))` converges to `a` in operator
norm. -/
theorem tendsto_mul_spectralCutoff (a : H →L[ℂ] H) [IsStarNormal a] :
    Tendsto (fun n : ℕ ↦ a * a.spectralCutoff (1 / (n + 1 : ℝ))) atTop (𝓝 a) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun _ ↦ norm_nonneg _) (fun n ↦ ?_) tendsto_one_div_add_atTop_nhds_zero_nat
  rw [norm_sub_rev]
  exact a.norm_sub_mul_spectralCutoff_le (by positivity)

/-- If a normal operator `a` avoids a closed two-sided ideal `I`, then some spectral cutoff
`a.spectralCutoff ε` (`ε > 0`) also avoids `I`. -/
theorem exists_spectralCutoff_notMem_of_isClosed (a : H →L[ℂ] H) [IsStarNormal a]
    {I : TwoSidedIdeal (H →L[ℂ] H)} (hI : IsClosed (I : Set (H →L[ℂ] H))) (ha : a ∉ I) :
    ∃ ε > 0, a.spectralCutoff ε ∉ I := by
  by_contra! h
  refine ha (hI.mem_of_tendsto a.tendsto_mul_spectralCutoff (Eventually.of_forall fun n ↦ ?_))
  exact I.mul_mem_left a _ (h (1 / (n + 1 : ℝ)) (by positivity))

end SpectralCutoff

section CalkinClassification

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

-- Verify that `↥(compactIdeal ℂ H)` automatically carries a `NonUnitalCStarAlgebra` structure.
example : NonUnitalCStarAlgebra ↥(compactIdeal ℂ H) := inferInstance

/-- **Calkin's theorem on closed ideals of `B(H)`.** On a separable complex Hilbert space `H`,
every closed two-sided ideal of `H →L[ℂ] H` is `⊥`, `compactIdeal ℂ H`, or `⊤`. -/
theorem eq_bot_or_eq_compactIdeal_or_eq_top_of_isClosed [SeparableSpace H]
    {I : TwoSidedIdeal (H →L[ℂ] H)} (hI : IsClosed (I : Set (H →L[ℂ] H))) :
    I = ⊥ ∨ I = compactIdeal ℂ H ∨ I = ⊤ := by
  rcases eq_bot_or_compactIdeal_le_of_isClosed hI with rfl | hle
  · exact Or.inl rfl
  · by_cases hsub : I ≤ compactIdeal ℂ H
    · exact Or.inr (Or.inl (le_antisymm hsub hle))
    · obtain ⟨a, haI, ha_not_cpt, ha_sa⟩ :=
        (compactIdeal ℂ H).exists_isSelfAdjoint_mem_notMem hsub
      have : IsStarNormal a := ha_sa.isStarNormal
      obtain ⟨ε, hε, hp_not_cpt⟩ :=
        a.exists_spectralCutoff_notMem_of_isClosed isClosed_compactIdeal ha_not_cpt
      have hpI : a.spectralCutoff ε ∈ I := a.spectralCutoff_mem_twoSidedIdeal haI hε
      obtain ⟨v, -, hv⟩ := (a.isStarProjection_spectralCutoff ε)
        |>.exists_linearIsometry_mul_eq_and_star_mul_mul_eq_one (mt mem_compactIdeal.mpr hp_not_cpt)
      refine Or.inr (Or.inr (I.eq_top ?_))
      rw [← hv]
      exact I.mul_mem_right _ _ (I.mul_mem_left _ _ hpI)

omit [CompleteSpace H] in
/-- On an infinite-dimensional complex inner product space, `⊥ < compactIdeal ℂ H < ⊤`, so the three
two-sided ideals `⊥`, `compactIdeal ℂ H`, and `⊤` are pairwise distinct. -/
theorem bot_lt_compactIdeal_and_compactIdeal_lt_top (hH : ¬ FiniteDimensional ℂ H) :
    ⊥ < compactIdeal ℂ H ∧ compactIdeal ℂ H < ⊤ := by
  have : Nontrivial H := by
    by_contra! hsub
    have : Subsingleton H := hsub
    exact hH inferInstance
  exact ⟨bot_lt_iff_ne_bot.mpr compactIdeal_ne_bot, compactIdeal_lt_top hH⟩

/-- The closed two-sided ideals of `H →L[ℂ] H` are exhausted by `{⊥, compactIdeal ℂ H, ⊤}` if and
only if `H` is separable. -/
theorem forall_isClosed_eq_bot_or_eq_compactIdeal_or_eq_top_iff :
    (∀ I : TwoSidedIdeal (H →L[ℂ] H),
      IsClosed (I : Set (H →L[ℂ] H)) → I = ⊥ ∨ I = compactIdeal ℂ H ∨ I = ⊤) ↔
      SeparableSpace H := by
  refine ⟨fun h ↦ ?_, fun _ _ hI ↦ eq_bot_or_eq_compactIdeal_or_eq_top_of_isClosed hI⟩
  by_contra hsep
  have hlt₁ : compactIdeal ℂ H < separableRangeIdeal ℂ H := compactIdeal_lt_separableRangeIdeal hsep
  have hlt₂ : separableRangeIdeal ℂ H < ⊤ := separableRangeIdeal_lt_top hsep
  rcases h (separableRangeIdeal ℂ H) isClosed_separableRangeIdeal with hbot | hcpt | htop
  · exact not_lt_bot (hbot ▸ hlt₁)
  · exact hlt₁.ne' hcpt
  · exact hlt₂.ne htop

end CalkinClassification

/-- On a finite-dimensional complex Euclidean space `EuclideanSpace ℂ (Fin d)`, every bounded
operator is compact (`compactIdeal = ⊤`). -/
@[simp]
theorem compactIdeal_euclideanSpace_fin_eq_top (d : ℕ) :
    compactIdeal ℂ (EuclideanSpace ℂ (Fin d)) = ⊤ :=
  compactIdeal_eq_top

/-- On `ℂ²` (`EuclideanSpace ℂ (Fin 2)`), the only two-sided ideals of bounded operators (closed or
not) are `⊥` and `⊤`. -/
theorem eq_bot_or_eq_top_euclideanSpace_fin_two
    (I : TwoSidedIdeal (EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2))) :
    I = ⊥ ∨ I = ⊤ :=
  IsSimpleOrder.eq_bot_or_eq_top I

end ContinuousLinearMap

/-- For an infinite index type `ι`, the Hilbert space `ℓ²(ι, 𝕜)` is infinite-dimensional. -/
theorem lp.not_finiteDimensional_l2 {𝕜 ι : Type*} [RCLike 𝕜] [Infinite ι] :
    ¬ FiniteDimensional 𝕜 ℓ²(ι, 𝕜) := fun _ ↦ by
  have : Finite ι :=
    (HilbertBasis.ofRepr (.refl 𝕜 ℓ²(ι, 𝕜))).orthonormal.linearIndependent.finite_of_isNoetherian
  exact not_finite ι

namespace TauCeti

/-- The **Calkin algebra** of a complex inner product space `H`: the quotient ring
`(H →L[ℂ] H) ⧸ ContinuousLinearMap.compactIdeal ℂ H` of bounded operators modulo compact operators,
which is a unital C⋆-algebra whenever `H` is complete (`CompleteSpace H`). -/
abbrev CalkinAlgebra (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] : Type _ :=
  (H →L[ℂ] H) ⧸ ContinuousLinearMap.compactIdeal ℂ H

namespace CalkinAlgebra

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

-- Verify that `CalkinAlgebra H` inherits a unital `CStarAlgebra` structure automatically.
example : CStarAlgebra (CalkinAlgebra H) := inferInstance

/-- The canonical surjective unital `⋆`-algebra homomorphism `(H →L[ℂ] H) →⋆ₐ[ℂ] CalkinAlgebra H`.
-/
def mk : (H →L[ℂ] H) →⋆ₐ[ℂ] CalkinAlgebra H :=
  TwoSidedIdeal.Quotient.mkUnitalStarAlgHom (ContinuousLinearMap.compactIdeal ℂ H)

/-- The Calkin projection `CalkinAlgebra.mk` is surjective. -/
theorem mk_surjective : Function.Surjective (mk (H := H)) :=
  TwoSidedIdeal.Quotient.mkUnitalStarAlgHom_surjective _

/-- Coercing `CalkinAlgebra.mk` to a function recovers `TwoSidedIdeal.Quotient.mk`. -/
theorem coe_mk :
    ⇑(mk (H := H)) = TwoSidedIdeal.Quotient.mk (ContinuousLinearMap.compactIdeal ℂ H) :=
  TwoSidedIdeal.Quotient.coe_mkUnitalStarAlgHom _

/-- Applying `CalkinAlgebra.mk` agrees with `TwoSidedIdeal.Quotient.mk`. -/
theorem mk_apply (T : H →L[ℂ] H) :
    mk T = TwoSidedIdeal.Quotient.mk (ContinuousLinearMap.compactIdeal ℂ H) T :=
  TwoSidedIdeal.Quotient.mkUnitalStarAlgHom_apply _ T

/-- An operator maps to `0` in `CalkinAlgebra H` if and only if it is compact. -/
@[simp]
theorem mk_eq_zero_iff {T : H →L[ℂ] H} : mk T = 0 ↔ IsCompactOperator T := by
  rw [mk_apply, TwoSidedIdeal.Quotient.eq_zero_iff_mem, ContinuousLinearMap.mem_compactIdeal]

/-- The kernel of `CalkinAlgebra.mk` is `ContinuousLinearMap.compactIdeal ℂ H`. -/
@[simp]
theorem ker_mk : TwoSidedIdeal.ker (mk (H := H)) = ContinuousLinearMap.compactIdeal ℂ H := by
  ext T
  rw [TwoSidedIdeal.mem_ker, mk_eq_zero_iff, ContinuousLinearMap.mem_compactIdeal]

/-- The Calkin projection `CalkinAlgebra.mk` is continuous. -/
@[fun_prop]
theorem continuous_mk : Continuous (mk (H := H)) := by
  rw [coe_mk]
  exact TwoSidedIdeal.Quotient.continuous_mk _

/-- The Calkin projection is contractive (`‖mk T‖ ≤ ‖T‖`). -/
theorem norm_mk_le (T : H →L[ℂ] H) : ‖mk T‖ ≤ ‖T‖ := by
  rw [mk_apply]
  exact TwoSidedIdeal.Quotient.norm_mk_le _ T

/-- **Essential norm formula.** The norm of `mk T` in `CalkinAlgebra H` is the infimum of
`‖T + K‖` over all compact operators `K : H →L[ℂ] H`. -/
theorem norm_mk_eq (T : H →L[ℂ] H) :
    ‖mk T‖ = sInf ((‖T + ·‖) '' {K : H →L[ℂ] H | IsCompactOperator K}) := by
  rw [mk_apply, TwoSidedIdeal.Quotient.norm_mk_eq, ContinuousLinearMap.coe_compactIdeal]

omit [CompleteSpace H] in
/-- The Calkin algebra of `H` is a subsingleton if and only if `H` is finite-dimensional. -/
@[simp]
theorem subsingleton_iff_finiteDimensional :
    Subsingleton (CalkinAlgebra H) ↔ FiniteDimensional ℂ H := by
  rw [← subsingleton_iff_zero_eq_one, eq_comm,
    ← TwoSidedIdeal.Quotient.mk_one (ContinuousLinearMap.compactIdeal ℂ H),
    TwoSidedIdeal.Quotient.eq_zero_iff_mem, ContinuousLinearMap.mem_compactIdeal,
    ContinuousLinearMap.one_def, ContinuousLinearMap.coe_id',
    isCompactOperator_id_iff_finiteDimensional (𝕜 := ℂ)]

omit [CompleteSpace H] in
/-- On a finite-dimensional complex inner product space, `CalkinAlgebra H` is a subsingleton. -/
instance instSubsingleton [FiniteDimensional ℂ H] : Subsingleton (CalkinAlgebra H) :=
  subsingleton_iff_finiteDimensional.mpr ‹_›

/-- On any finite-dimensional complex Euclidean space, the Calkin algebra is a subsingleton. -/
instance instSubsingletonEuclideanSpace (n : Type*) [Fintype n] :
    Subsingleton (CalkinAlgebra (EuclideanSpace ℂ n)) :=
  inferInstance

omit [CompleteSpace H] in
/-- The Calkin algebra of `H` is nontrivial if and only if `H` is infinite-dimensional. -/
@[simp]
theorem nontrivial_iff_not_finiteDimensional :
    Nontrivial (CalkinAlgebra H) ↔ ¬ FiniteDimensional ℂ H := by
  rw [← not_subsingleton_iff_nontrivial, subsingleton_iff_finiteDimensional]

/-- On a separable complex Hilbert space `H`, every closed two-sided ideal of `CalkinAlgebra H` is
`⊥` or `⊤`. -/
theorem eq_bot_or_eq_top_of_isClosed [SeparableSpace H] (J : TwoSidedIdeal (CalkinAlgebra H))
    (hJ : IsClosed (J : Set (CalkinAlgebra H))) : J = ⊥ ∨ J = ⊤ := by
  let π : (H →L[ℂ] H) →+* CalkinAlgebra H := (mk (H := H)).toRingHom
  let I : TwoSidedIdeal (H →L[ℂ] H) := J.comap π
  have hmemI : ∀ a : H →L[ℂ] H, a ∈ I ↔ mk a ∈ J := fun a ↦ TwoSidedIdeal.mem_comap π
  have hI_set : (I : Set (H →L[ℂ] H)) = mk ⁻¹' (J : Set (CalkinAlgebra H)) :=
    Set.ext hmemI
  have hI_closed : IsClosed (I : Set (H →L[ℂ] H)) := by
    rw [hI_set]
    exact hJ.preimage continuous_mk
  rcases ContinuousLinearMap.eq_bot_or_eq_compactIdeal_or_eq_top_of_isClosed hI_closed with
    hbot | hcpt | htop
  · refine Or.inl (le_bot_iff.mp fun x hx ↦ ?_)
    obtain ⟨a, rfl⟩ := mk_surjective x
    have ha : a ∈ (⊥ : TwoSidedIdeal (H →L[ℂ] H)) := hbot ▸ (hmemI a).mpr hx
    rw [TwoSidedIdeal.mem_bot] at ha ⊢
    rw [ha, map_zero]
  · refine Or.inl (le_bot_iff.mp fun x hx ↦ ?_)
    obtain ⟨a, rfl⟩ := mk_surjective x
    have ha : a ∈ ContinuousLinearMap.compactIdeal ℂ H := hcpt ▸ (hmemI a).mpr hx
    rw [TwoSidedIdeal.mem_bot, mk_eq_zero_iff]
    exact ContinuousLinearMap.mem_compactIdeal.mp ha
  · refine Or.inr (J.eq_top ?_)
    have h1 : (1 : H →L[ℂ] H) ∈ I := by rw [htop, TwoSidedIdeal.one_mem_iff]
    simpa only [hmemI, map_one] using h1

/-- **Simplicity of the Calkin algebra.** When `H` is a separable infinite-dimensional complex
Hilbert space, `CalkinAlgebra H` is algebraically simple: it is nontrivial and has no proper
nonzero two-sided ideals (closed or not). -/
theorem isSimpleRing [SeparableSpace H] (hH : ¬ FiniteDimensional ℂ H) :
    IsSimpleRing (CalkinAlgebra H) := by
  have : Nontrivial (CalkinAlgebra H) := nontrivial_iff_not_finiteDimensional.mpr hH
  exact IsSimpleRing.of_forall_isClosed_eq_bot_or_eq_top eq_bot_or_eq_top_of_isClosed

/-- The Calkin algebra `CalkinAlgebra H` is a simple ring if and only if `H` is separable and
infinite-dimensional. -/
theorem isSimpleRing_iff :
    IsSimpleRing (CalkinAlgebra H) ↔ SeparableSpace H ∧ ¬ FiniteDimensional ℂ H := by
  refine ⟨fun h ↦ ?_, fun ⟨_, hinf⟩ ↦ isSimpleRing hinf⟩
  have : IsSimpleRing (CalkinAlgebra H) := h
  have hinf : ¬ FiniteDimensional ℂ H := nontrivial_iff_not_finiteDimensional.mp inferInstance
  refine ⟨?_, hinf⟩
  by_contra hsep
  let f := TwoSidedIdeal.Quotient.factor
    (ContinuousLinearMap.compactIdeal_le_separableRangeIdeal (𝕜 := ℂ) (E := H))
  let J : TwoSidedIdeal (CalkinAlgebra H) := TwoSidedIdeal.ker f
  have hlt₁ := ContinuousLinearMap.compactIdeal_lt_separableRangeIdeal (𝕜 := ℂ) hsep
  have hlt₂ := ContinuousLinearMap.separableRangeIdeal_lt_top (R := ℂ) hsep
  rcases IsSimpleOrder.eq_bot_or_eq_top J with hbot | htop
  · obtain ⟨T, hT_sep, hT_not_cpt⟩ := Set.not_subset.mp hlt₁.not_ge
    have hmem : mk T ∈ J := by
      rw [TwoSidedIdeal.mem_ker, mk_apply, TwoSidedIdeal.Quotient.factor_mk,
        TwoSidedIdeal.Quotient.eq_zero_iff_mem]
      exact hT_sep
    rw [hbot, TwoSidedIdeal.mem_bot, mk_eq_zero_iff, ← ContinuousLinearMap.mem_compactIdeal] at hmem
    exact hT_not_cpt hmem
  · have h1 : (1 : CalkinAlgebra H) ∈ J := by rw [htop, TwoSidedIdeal.one_mem_iff]
    rw [← map_one mk, TwoSidedIdeal.mem_ker, mk_apply, TwoSidedIdeal.Quotient.factor_mk,
      TwoSidedIdeal.Quotient.eq_zero_iff_mem, TwoSidedIdeal.one_mem_iff] at h1
    exact hlt₂.ne h1

/-- For any infinite index type `ι`, `CalkinAlgebra ℓ²(ι, ℂ)` is nontrivial. -/
instance instNontrivialL2 {ι : Type*} [Infinite ι] : Nontrivial (CalkinAlgebra ℓ²(ι, ℂ)) :=
  nontrivial_iff_not_finiteDimensional.mpr lp.not_finiteDimensional_l2

/-- For any countably infinite index type `ι` (in particular `ι = ℕ`), `CalkinAlgebra ℓ²(ι, ℂ)` is
a simple C⋆-algebra. -/
instance instIsSimpleRingL2 {ι : Type*} [Countable ι] [Infinite ι] :
    IsSimpleRing (CalkinAlgebra ℓ²(ι, ℂ)) := by
  have : SeparableSpace ℓ²(ι, ℂ) := lp.separableSpace (by norm_num)
  exact isSimpleRing lp.not_finiteDimensional_l2

-- Non-vacuity check on `ℓ²(ℕ, ℂ)` with zero hypotheses.
example : IsSimpleRing (CalkinAlgebra ℓ²(ℕ, ℂ)) := inferInstance

end CalkinAlgebra

end TauCeti

end
