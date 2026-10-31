/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Hull
public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import Mathlib.Analysis.RCLike.Basic
public import TauCeti.Analysis.Normed.Module.ApproximationProperty.Basic
import Mathlib.Analysis.Normed.Lp.lpSpace
import TauCeti.Analysis.Convex.TotallyBounded
import TauCeti.Analysis.Normed.Module.Dual.NullSequence
import TauCeti.Analysis.Normed.Operator.Compact.Basic
import TauCeti.Analysis.Normed.Operator.Compact.NullSequence

/-!
# The approximation property and approximation of compact operators

Grothendieck's characterization of the approximation property: a Banach space `E` over `ℝ` or
`ℂ` has the approximation property exactly when every compact operator `T : F →L[𝕜] E` from a
Banach space `F` is an operator-norm limit of bounded finite-rank operators.

The forward implication holds for every source space: approximating the identity of `E` on the
compact closure of the image of the unit ball by a finite-rank operator `S` makes `S ∘ T`
uniformly close to `T`.

For the converse, let `K ⊆ E` be compact. By Grothendieck's compactness lemma
(`TotallyBounded.exists_tendsto_zero_subset_closure_convexHull`), `K` lies in the closed convex
hull of a null sequence `x`. Factoring `x n = r n • s n • v n` with three null factors, the
operator `T : a ↦ ∑ aₙ sₙ vₙ` on `ℓ¹` is compact and sends the null sequence `r n • eₙ` to `x`.
It induces an injective compact operator `J` on the Banach space `Y = ℓ¹ ⧸ ker T`, the
compact-disk space of the construction, and `x = J ∘ y` for a null sequence `y` in `Y`. If `J` is
a limit of finite-rank operators `G`, it remains to replace `G` by an operator of the form
`S ∘ J`, uniformly along `y`. This is a duality argument in `c₀`: a functional on `c₀`
annihilating the sequences `(ψ (J (y n)))ₙ` for all `ψ ∈ E*` is given by some `a ∈ ℓ¹`, and it
annihilates `(φ (y n))ₙ` for every `φ ∈ Y*`, because `J (∑ aₙ • yₙ) = 0` and `J` is injective.
Convexity then carries the estimates from `y` to its closed convex hull, hence to `K`. Indexing
`ℓ¹` by `ULift ℕ` places `Y` in the universe of the source spaces.

The compact operator on `ℓ¹` is `TauCeti.exists_isCompactOperator_apply_eq`, and the duality
step is `TauCeti.exists_forall_norm_sub_lt_of_finiteDimensional`; both live in general modules
below approximation-property theory.

## Main statements

* `TauCeti.HasApproximationProperty.mem_closure_setOf_hasFiniteRange`: on a space with the
  approximation property, every compact operator into it is a limit of finite-rank operators.
* `TauCeti.exists_hasFiniteRange_forall_norm_sub_lt_of_mem_closure`: if an injective operator
  `J` out of a Banach space is a limit of finite-rank operators, the identity is approximated by
  finite-rank operators uniformly on the closed convex hull of `J ∘ y` for each null sequence
  `y`.
* `TauCeti.hasApproximationProperty_iff_forall_isCompactOperator`: Grothendieck's
  characterization of the approximation property by compact operators.

## References

* A. Grothendieck, *Produits tensoriels topologiques et espaces nucléaires*, Mem. Amer. Math.
  Soc. **16** (1955).
* R. E. Megginson, *An Introduction to Banach Space Theory*, Theorem 3.4.32.
* J. Lindenstrauss and L. Tzafriri, *Classical Banach Spaces I*, Theorem 1.e.4.
-/

public section

open Filter Set
open scoped Topology lp

namespace TauCeti

section Forward

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- On a space with the approximation property, every compact operator into it is an
operator-norm limit of bounded finite-rank operators. The source space is arbitrary. -/
theorem HasApproximationProperty.mem_closure_setOf_hasFiniteRange
    (hE : HasApproximationProperty 𝕜 E) {T : F →L[𝕜] E} (hT : IsCompactOperator T) :
    T ∈ closure {R : F →L[𝕜] E | (R : F →ₗ[𝕜] E).HasFiniteRange} := by
  refine Metric.mem_closure_iff.mpr fun ε hε ↦ ?_
  obtain ⟨c, hc⟩ := NormedField.exists_one_lt_norm 𝕜
  have hc0 : 0 < ‖c‖ := zero_lt_one.trans hc
  -- Approximate the identity on the compact closure of `T '' ball 0 1`.
  obtain ⟨S, hS, hSK⟩ := hasApproximationProperty_iff.mp hE _ (hT.isCompact_closure_image_ball 1)
    (ε / (2 * ‖c‖)) (by positivity)
  refine ⟨S ∘L T, hS.comp_right _, ?_⟩
  rw [dist_eq_norm]
  refine (ContinuousLinearMap.opNorm_le_of_shell zero_lt_one (by positivity) hc
    fun x hx₁ hx₂ ↦ ?_).trans_lt (half_lt_self hε)
  have hx : ‖S (T x) - T x‖ < ε / (2 * ‖c‖) :=
    hSK _ (subset_closure ⟨x, mem_ball_zero_iff.mpr hx₂, rfl⟩)
  rw [sub_apply, norm_sub_rev]
  have hx₁' : 1 ≤ ‖c‖ * ‖x‖ := by rwa [div_le_iff₀' hc0] at hx₁
  calc ‖S (T x) - T x‖ ≤ ε / (2 * ‖c‖) := hx.le
    _ ≤ ε / (2 * ‖c‖) * (‖c‖ * ‖x‖) := le_mul_of_one_le_right (by positivity) hx₁'
    _ = ε / 2 * ‖x‖ := by field_simp

end Forward

section RCLike

variable {𝕜 E Y : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] [CompleteSpace Y]

/-- Let `J : Y →L[𝕜] E` be injective, with `Y` complete, and an operator-norm limit of bounded
finite-rank operators. For every null sequence `y` in `Y`, the identity of `E` is approximated
by bounded finite-rank operators uniformly on the closed convex hull of `J ∘ y`. -/
theorem exists_hasFiniteRange_forall_norm_sub_lt_of_mem_closure [NormedSpace ℝ E]
    [IsScalarTower ℝ 𝕜 E] {J : Y →L[𝕜] E} (hJ : Function.Injective J)
    (hJc : J ∈ closure {R : Y →L[𝕜] E | (R : Y →ₗ[𝕜] E).HasFiniteRange}) {y : ℕ → Y}
    (hy : Tendsto y atTop (𝓝 0)) {ε : ℝ} (hε : 0 < ε) :
    ∃ S : E →L[𝕜] E, (S : E →ₗ[𝕜] E).HasFiniteRange ∧
      ∀ x ∈ closure (convexHull ℝ (range (J ∘ y))), ‖S x - x‖ < ε := by
  let : NormedSpace ℝ Y := .restrictScalars ℝ 𝕜 Y
  have : IsScalarTower ℝ 𝕜 Y := .restrictScalars ℝ 𝕜 Y
  -- The closed convex hull `C` of the null sequence `y` is compact, hence bounded.
  set C := closure (convexHull ℝ (range y))
  have hC : IsCompact C :=
    (hy.isCompact_insert_range.totallyBounded.subset (subset_insert _ _)).convexHull.closure
      |>.isCompact_of_isClosed isClosed_closure
  obtain ⟨M, hM⟩ := hC.isBounded.exists_norm_le
  set M' := max M 0 + 1
  have hM' : 0 < M' := by positivity
  -- A finite-rank `G` close to `J`, and a finite-rank `S` with `S ∘ J` close to `G` along `y`.
  obtain ⟨G, hG, hGJ⟩ := Metric.mem_closure_iff.mp hJc (ε / 2 / M') (by positivity)
  have : FiniteDimensional 𝕜 (LinearMap.range (G : Y →ₗ[𝕜] E)) := .of_fg hG
  obtain ⟨S₀, hS₀⟩ := exists_forall_norm_sub_lt_of_finiteDimensional hJ hy
    (G.codRestrict _ fun v ↦ LinearMap.mem_range_self _ v) (half_pos hε)
  set S := (LinearMap.range (G : Y →ₗ[𝕜] E)).subtypeL ∘L S₀
  refine ⟨S, (LinearMap.HasFiniteRange.of_isNoetherian_rng
    (f := (S₀ : E →ₗ[𝕜] LinearMap.range (G : Y →ₗ[𝕜] E)))).comp_left _, ?_⟩
  -- The estimate `‖G v - S (J v)‖ ≤ ε / 2` passes from the `y n` to their closed convex hull.
  have hD : C ⊆ {v | ‖G v - S (J v)‖ ≤ ε / 2} := by
    refine closure_minimal (convexHull_min ?_ ?_) (isClosed_le (by fun_prop) continuous_const)
    · rintro _ ⟨n, rfl⟩
      exact (hS₀ n).le
    · have : {v | ‖G v - S (J v)‖ ≤ ε / 2} =
          ((G - S ∘L J).restrictScalars ℝ : Y →ₗ[ℝ] E) ⁻¹' Metric.closedBall 0 (ε / 2) := by
        ext v
        simp
      rw [this]
      exact (convex_closedBall _ _).linear_preimage _
  -- Every point of the closed convex hull of `J ∘ y` is `J v` for some `v ∈ C`.
  have hJC : closure (convexHull ℝ (range (J ∘ y))) ⊆ J '' C := by
    refine closure_minimal ?_ (hC.image J.continuous).isClosed
    rw [range_comp]
    exact (((J : Y →ₗ[𝕜] E).restrictScalars ℝ).image_convexHull (range y)).symm.trans_subset
      (image_mono subset_closure)
  intro x hx
  obtain ⟨v, hv, rfl⟩ := hJC hx
  have hGv : ‖G v - J v‖ < ε / 2 := by
    rw [dist_eq_norm, norm_sub_rev] at hGJ
    calc ‖G v - J v‖ = ‖(G - J) v‖ := by rw [sub_apply]
      _ ≤ ‖G - J‖ * M' := (G - J).le_opNorm_of_le ((hM v hv).trans (by grind))
      _ < ε / 2 / M' * M' := by gcongr
      _ = ε / 2 := div_mul_cancel₀ _ hM'.ne'
  calc ‖S (J v) - J v‖ ≤ ‖S (J v) - G v‖ + ‖G v - J v‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ < ε / 2 + ε / 2 := by
        rw [norm_sub_rev]
        exact add_lt_add_of_le_of_lt (hD hv) hGv
    _ = ε := add_halves ε

end RCLike

/-! ### Grothendieck's characterization -/

universe u v w

/-- **Grothendieck's characterization of the approximation property.** A Banach space `E` over
`ℝ` or `ℂ` has the approximation property exactly when every compact operator into `E` from a
Banach space is an operator-norm limit of bounded finite-rank operators.

The source spaces range over any universe containing that of the scalar field. For the forward
implication with an arbitrary source space, see
`HasApproximationProperty.mem_closure_setOf_hasFiniteRange`. -/
theorem hasApproximationProperty_iff_forall_isCompactOperator {𝕜 : Type u} {E : Type v}
    [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E] :
    HasApproximationProperty 𝕜 E ↔
      ∀ (F : Type max u w) [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]
        (T : F →L[𝕜] E), IsCompactOperator T →
          T ∈ closure {R : F →L[𝕜] E | (R : F →ₗ[𝕜] E).HasFiniteRange} := by
  refine ⟨fun h F _ _ _ T hT ↦ h.mem_closure_setOf_hasFiniteRange hT,
    fun h ↦ hasApproximationProperty_iff.mpr fun K hK ε hε ↦ ?_⟩
  let : NormedSpace ℝ E := .restrictScalars ℝ 𝕜 E
  have : IsScalarTower ℝ 𝕜 E := .restrictScalars ℝ 𝕜 E
  -- `K` lies in the closed convex hull of a null sequence `x`, which is `T ∘ y` for a compact
  -- operator `T` on `ℓ¹`. Indexing by `ULift ℕ` puts `ℓ¹` in the universe of the source spaces.
  obtain ⟨x, hx, hKx⟩ := hK.totallyBounded.exists_tendsto_zero_subset_closure_convexHull
  obtain ⟨T, hT, y, hy, hTy⟩ := exists_isCompactOperator_apply_eq (𝕜 := 𝕜)
    (x := x ∘ ULift.down.{max u w}) <| by
      rw [← Nat.cofinite_eq_atTop] at hx
      exact hx.comp ULift.down_injective.tendsto_cofinite
  -- On the compact-disk space `ℓ¹ ⧸ ker T`, `T` induces an injective compact operator.
  obtain ⟨N, hN⟩ : ∃ N, LinearMap.ker (T : ℓ^1(ULift ℕ, 𝕜) →ₗ[𝕜] E) = N := ⟨_, rfl⟩
  have : IsClosed (N : Set ℓ^1(ULift ℕ, 𝕜)) := hN ▸ T.isClosed_ker
  have hJ : Function.Injective (N.liftQL T hN.ge) := by
    intro a b hab
    induction a using Submodule.Quotient.induction_on
    induction b using Submodule.Quotient.induction_on
    exact (Submodule.Quotient.eq _).2 (by simpa [← hN, sub_eq_zero] using hab)
  obtain ⟨S, hS, hSK⟩ := exists_hasFiniteRange_forall_norm_sub_lt_of_mem_closure hJ
    (h _ _ (hT.liftQL hN.ge)) (y := N.mkQ ∘ y ∘ ULift.up) (by
      rw [← Nat.cofinite_eq_atTop]
      have := ((N.mkQL.continuous.tendsto 0).comp hy).comp ULift.up_injective.tendsto_cofinite
      rw [map_zero] at this
      exact this) hε
  refine ⟨S, hS, fun z hz ↦ hSK z ?_⟩
  convert hKx hz
  ext n
  simpa using hTy (ULift.up n)

end TauCeti
