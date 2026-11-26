/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Module.Spaces.PointwiseConvergenceCLM
public import TauCeti.Analysis.CStarAlgebra.Ideal
public import TauCeti.Analysis.CStarAlgebra.Module.Adjointable.Self
public import TauCeti.Analysis.CStarAlgebra.Multiplier.Strict.Topology
import TauCeti.Analysis.CStarAlgebra.Module.Factorization

/-!
# Adjointable operators as multipliers of the module-compact operators

For a complete Hilbert C⋆-module `E` over a possibly nonunital C⋆-algebra `A`, this file
identifies the adjointable endomorphisms `L_A(E) = TauCeti.AdjointableMap A E E` with the
multiplier algebra `𝓜(ℂ, K_A(E))` of the module-compact ideal
`K_A(E) = (compactOperatorIdeal A E).toNonUnitalStarSubalgebra`, and identifies the induced strict
topology on norm-bounded sets with strong-* convergence on `E`.

## Overview

1. **Nondegeneracy and approximate units of `K_A(E)`.** The module-compact operators separate
   vectors (`eq_of_forall_compactOperator_apply_eq`) and separate adjointable operators on both
   sides (`eq_of_forall_compactOperator_comp_eq`, `eq_of_forall_comp_compactOperator_eq`), without
   completeness. When `E` is complete, the special factorization `x = ⟪y, y⟫_A • y`
   (`CStarModule.existsUnique_inner_self_smul_eq`) exhibits every vector `x : E` as `θ_{y, y} y`
   (`exists_rankOne_self_apply_eq`), hence as `k y` for some `k : K_A(E)`
   (`exists_compactOperatorIdeal_apply_eq`). Consequently, along any approximate unit `e` of
   `K_A(E)` (with no norm bound assumed), `e x → x` for every `x : E`
   (`tendsto_compactOperatorIdeal_apply_of_isApproximateUnit`).
2. **The multiplier isomorphism `L_A(E) ≃⋆ₐ[ℂ] 𝓜(ℂ, K_A(E))`.** Left and right
   multiplication inside `L_A(E)` embed `L_A(E)` into `𝓜(ℂ, K_A(E))` via
   `NonUnitalStarSubalgebra.multiplierHom`. Conversely, for `m : 𝓜(ℂ, K_A(E))`, the map
   `x ↦ m.fst k_x y_x` (where `k_x y_x = x`) is well-defined independently of the factorization
   and has adjoint `x ↦ (star m).fst k_x y_x`, yielding an isometric unital `⋆`-isomorphism
   `TauCeti.AdjointableMap.multiplierStarAlgEquiv A E : L_A(E) ≃⋆ₐ[ℂ] 𝓜(ℂ, K_A(E))`.
   On the right self-module `A = Bᵐᵒᵖ` (`E = B`), this agrees with
   `multiplierMulOppositeStarAlgEquiv` transported along `compactOperatorMulOppositeStarAlgEquiv`
   (`multiplierMulOppositeStarAlgEquiv_trans_congr`).
3. **Strict and strong-* topologies.** Transporting the strict topology from `𝓜ₛ(ℂ, K_A(E))`
   via `multiplierStrictStarAlgEquiv A E`, strict convergence globally implies pointwise norm
   convergence of both `T` and `T.adjoint` on `E`
   (`continuous_toPointwiseConvergenceCLM_multiplierStrictStarAlgEquiv_symm`,
   `continuous_toPointwiseConvergenceCLM_adjoint_multiplierStrictStarAlgEquiv_symm`). On
   norm-bounded filters and bounded sets, the two notions coincide
   (`tendsto_multiplierStrictStarAlgEquiv_iff_of_eventually_norm_le`,
   `induced_multiplierStrictStarAlgEquiv_eq_induced_pointwiseConvergenceCLM_of_isBounded`).

## References

* Iain Raeburn and Dana P. Williams, *Morita Equivalence and Continuous-Trace C⋆-Algebras*,
  Proposition 2.31 and Corollary 2.54.
* E. Christopher Lance, *Hilbert C⋆-Modules: A Toolkit for Operator Algebraists*, Chapter 2,
  Proposition 2.2.
-/

public section

open CStarModule Filter Topology
open scoped MultiplierAlgebra

namespace TauCeti

namespace AdjointableMap

/-! ### Nondegeneracy and approximate-unit action of `K_A(E)` -/

section Nondegenerate

variable {A E F : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul A E] [CStarModule A E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul A F] [CStarModule A F]

/-- If `θ_{x, x} x = 0`, then `x = 0`. -/
theorem eq_zero_of_rankOne_self_apply_eq_zero {x : E} (h : rankOne A x x x = 0) : x = 0 := by
  refine (CStarModule.inner_self (A := A)).mp (mul_star_self_eq_zero.mp ?_)
  have hinner : inner A x (rankOne A x x x) = 0 := by rw [h, CStarModule.inner_zero_right]
  rw [rankOne_apply, CStarModule.inner_op_smul_right] at hinner
  nth_rw 2 [← CStarModule.isSelfAdjoint_inner_self.star_eq] at hinner
  exact hinner

/-- A vector annihilated by every module-compact operator vanishes. -/
theorem eq_zero_of_forall_compactOperator_apply_eq_zero {x : E}
    (h : ∀ k ∈ compactOperator A E E, k x = 0) : x = 0 :=
  eq_zero_of_rankOne_self_apply_eq_zero (h _ (rankOne_mem_compactOperator x x))

/-- Vectors on which all module-compact operators agree are equal. -/
theorem eq_of_forall_compactOperator_apply_eq {x y : E}
    (h : ∀ k ∈ compactOperator A E E, k x = k y) : x = y :=
  sub_eq_zero.mp <| eq_zero_of_forall_compactOperator_apply_eq_zero fun k hk ↦ by
    rw [map_sub, h k hk, sub_self]

/-- An adjointable operator `T : L_A(E, F)` whose composition with every module-compact
operator vanishes on the right is zero. -/
theorem eq_zero_of_forall_compactOperator_comp_eq_zero {T : AdjointableMap A E F}
    (h : ∀ k ∈ compactOperator A E E, T.comp k = 0) : T = 0 := by
  refine ext fun x ↦ (CStarModule.inner_self (A := A)).mp (mul_star_self_eq_zero.mp ?_)
  have happ : (T.comp (rankOne A x (T.adjoint (T x)))) x = 0 := by
    rw [h _ (rankOne_mem_compactOperator _ _), zero_apply]
  have hinner : inner A (T x) ((T.comp (rankOne A x (T.adjoint (T x)))) x) = 0 := by
    rw [happ, CStarModule.inner_zero_right]
  rw [comp_rankOne, rankOne_apply, T.adjoint_inner_left, CStarModule.inner_op_smul_right] at hinner
  nth_rw 2 [← CStarModule.isSelfAdjoint_inner_self.star_eq] at hinner
  exact hinner

/-- Two adjointable operators `S, T : L_A(E, F)` satisfying `S ∘ k = T ∘ k` for all
`k ∈ K_A(E)` are equal. -/
theorem eq_of_forall_compactOperator_comp_eq {S T : AdjointableMap A E F}
    (h : ∀ k ∈ compactOperator A E E, S.comp k = T.comp k) : S = T :=
  sub_eq_zero.mp <| eq_zero_of_forall_compactOperator_comp_eq_zero fun k hk ↦ by
    rw [sub_eq_add_neg, add_comp, show (-T).comp k = -(T.comp k) from ext fun _ ↦ by simp,
      h k hk, add_neg_cancel]

/-- An adjointable operator `T : L_A(E, F)` whose composition with every module-compact
operator vanishes on the left is zero. -/
theorem eq_zero_of_forall_comp_compactOperator_eq_zero {T : AdjointableMap A E F}
    (h : ∀ k ∈ compactOperator A F F, k.comp T = 0) : T = 0 := by
  rw [← adjoint_eq_zero_iff]
  refine eq_zero_of_forall_compactOperator_comp_eq_zero fun k hk ↦ ?_
  have hkT := congrArg adjoint (h k.adjoint (adjoint_mem_compactOperator hk))
  simpa [adjoint_comp] using hkT

/-- Two adjointable operators `S, T : L_A(E, F)` satisfying `k ∘ S = k ∘ T` for all
`k ∈ K_A(F)` are equal. -/
theorem eq_of_forall_comp_compactOperator_eq {S T : AdjointableMap A E F}
    (h : ∀ k ∈ compactOperator A F F, k.comp S = k.comp T) : S = T :=
  sub_eq_zero.mp <| eq_zero_of_forall_comp_compactOperator_eq_zero fun k hk ↦ by
    rw [sub_eq_add_neg, comp_add, show k.comp (-T) = -(k.comp T) from ext fun _ ↦ by simp,
      h k hk, add_neg_cancel]

/-- An adjointable endomorphism `T : L_A(E)` satisfying `T * k = 0` for all `k ∈ K_A(E)` is
zero (the ideal `K_A(E)` is essential in `L_A(E)`). -/
theorem eq_zero_of_forall_mul_compactOperator_eq_zero {T : AdjointableMap A E E}
    (h : ∀ k ∈ compactOperator A E E, T * k = 0) : T = 0 :=
  eq_zero_of_forall_compactOperator_comp_eq_zero h

/-- Two adjointable endomorphisms `S, T : L_A(E)` satisfying `S * k = T * k` for all `k ∈ K_A(E)`
are equal. -/
theorem eq_of_forall_mul_compactOperator_eq {S T : AdjointableMap A E E}
    (h : ∀ k ∈ compactOperator A E E, S * k = T * k) : S = T :=
  eq_of_forall_compactOperator_comp_eq h

/-- An adjointable endomorphism `T : L_A(E)` satisfying `k * T = 0` for all `k ∈ K_A(E)` is
zero. -/
theorem eq_zero_of_forall_compactOperator_mul_eq_zero {T : AdjointableMap A E E}
    (h : ∀ k ∈ compactOperator A E E, k * T = 0) : T = 0 :=
  eq_zero_of_forall_comp_compactOperator_eq_zero h

/-- Two adjointable endomorphisms `S, T : L_A(E)` satisfying `k * S = k * T` for all `k ∈ K_A(E)`
are equal. -/
theorem eq_of_forall_compactOperator_mul_eq {S T : AdjointableMap A E E}
    (h : ∀ k ∈ compactOperator A E E, k * S = k * T) : S = T :=
  eq_of_forall_comp_compactOperator_eq h

/-- Two adjointable endomorphisms `S, T : L_A(E)` multiplying identically on the left of every
`k : compactOperatorIdeal A E` are equal. -/
theorem eq_of_forall_compactOperatorIdeal_mul_eq {S T : AdjointableMap A E E}
    (h : ∀ k : compactOperatorIdeal A E,
      S * (k : AdjointableMap A E E) = T * (k : AdjointableMap A E E)) : S = T :=
  eq_of_forall_mul_compactOperator_eq fun k hk ↦ h ⟨k, mem_compactOperatorIdeal.mpr hk⟩

/-- Along any approximate unit `l` of `K_A(E)`, any `T ∈ K_A(E)` satisfies `T * e → T` in
operator norm. -/
theorem tendsto_mul_coe_compactOperatorIdeal_of_mem {l : Filter (compactOperatorIdeal A E)}
    (hl : l.IsApproximateUnit) {T : AdjointableMap A E E} (hT : T ∈ compactOperator A E E) :
    Tendsto (fun e : compactOperatorIdeal A E ↦ T * (e : AdjointableMap A E E)) l (𝓝 T) := by
  let k : compactOperatorIdeal A E := ⟨T, mem_compactOperatorIdeal.mpr hT⟩
  exact ((continuous_subtypeVal.tendsto k).comp (hl.tendsto_mul_left k)).congr fun _ ↦ rfl

/-- Along any approximate unit `l` of `K_A(E)`, any `T ∈ K_A(E)` satisfies `e * T → T` in
operator norm. -/
theorem tendsto_coe_compactOperatorIdeal_mul_of_mem {l : Filter (compactOperatorIdeal A E)}
    (hl : l.IsApproximateUnit) {T : AdjointableMap A E E} (hT : T ∈ compactOperator A E E) :
    Tendsto (fun e : compactOperatorIdeal A E ↦ (e : AdjointableMap A E E) * T) l (𝓝 T) := by
  let k : compactOperatorIdeal A E := ⟨T, mem_compactOperatorIdeal.mpr hT⟩
  exact ((continuous_subtypeVal.tendsto k).comp (hl.tendsto_mul_right k)).congr fun _ ↦ rfl

section Complete

variable [CompleteSpace E]

/-- In a complete Hilbert C⋆-module `E`, every vector `x` has the form `θ_{y, y} y` for some
`y : E`, by the special factorization `x = ⟪y, y⟫_A • y`. -/
theorem exists_rankOne_self_apply_eq (x : E) : ∃ y : E, rankOne A y y y = x := by
  obtain ⟨y, hy, -⟩ := CStarModule.existsUnique_inner_self_smul_eq (A := A) x
  exact ⟨y, by simpa [rankOne_apply] using hy⟩

/-- Every vector `x : E` in a complete Hilbert C⋆-module lies in the range of some element of
`K_A(E)`: `x = k y` with `k : compactOperatorIdeal A E` and `y : E`. -/
theorem exists_compactOperatorIdeal_apply_eq (x : E) :
    ∃ (k : compactOperatorIdeal A E) (y : E), (k : AdjointableMap A E E) y = x := by
  obtain ⟨y, hy⟩ := exists_rankOne_self_apply_eq (A := A) x
  exact ⟨⟨rankOne A y y,
    mem_compactOperatorIdeal.mpr (rankOne_mem_compactOperator y y)⟩, y, hy⟩

/-- Every vector `x : E` in a complete Hilbert C⋆-module lies in the range of some element of
`(compactOperatorIdeal A E).toNonUnitalStarSubalgebra`. -/
private theorem exists_compactOperatorSubalgebra_apply_eq (x : E) :
    ∃ (k : (compactOperatorIdeal A E).toNonUnitalStarSubalgebra) (y : E),
      (k : AdjointableMap A E E) y = x := by
  obtain ⟨k, y, hy⟩ := exists_compactOperatorIdeal_apply_eq (A := A) x
  exact ⟨⟨k, (TwoSidedIdeal.mem_toNonUnitalStarSubalgebra _).mpr k.property⟩, y, hy⟩

/-- The union of the ranges of all module-compact operators on a complete Hilbert C⋆-module `E` is
all of `E`. -/
@[simp]
theorem iUnion_range_compactOperatorIdeal_eq_univ :
    (⋃ k : compactOperatorIdeal A E, Set.range ((k : AdjointableMap A E E) : E → E)) =
      Set.univ :=
  Set.eq_univ_iff_forall.mpr fun x ↦
    let ⟨k, y, hy⟩ := exists_compactOperatorIdeal_apply_eq (A := A) x
    Set.mem_iUnion.mpr ⟨k, y, hy⟩

/-- The linear span of the ranges of the module-compact operators on a complete Hilbert C⋆-module
`E` is all of `E`. -/
theorem span_iUnion_range_compactOperatorIdeal_eq_top :
    Submodule.span ℂ
        (⋃ k : compactOperatorIdeal A E, Set.range ((k : AdjointableMap A E E) : E → E)) =
      ⊤ := by
  rw [iUnion_range_compactOperatorIdeal_eq_univ, Submodule.span_univ]

/-- The action of `K_A(E)` on a complete Hilbert C⋆-module `E` is nondegenerate (essential): the
linear span of `{k y | k ∈ K_A(E), y ∈ E}` is dense in `E`. -/
theorem dense_span_compactOperatorIdeal_apply :
    Dense (Submodule.span ℂ (⋃ k : compactOperatorIdeal A E,
      Set.range ((k : AdjointableMap A E E) : E → E)) : Set E) := by
  rw [span_iUnion_range_compactOperatorIdeal_eq_top]
  exact dense_univ

/-- Along any right-multiplication approximate identity filter `l` on `K_A(E)` (with no norm bound
assumed), `e x → x` in `E` for every `x : E`. -/
theorem tendsto_compactOperatorIdeal_apply_of_tendsto_mul_right
    {l : Filter (compactOperatorIdeal A E)}
    (hl : ∀ k : compactOperatorIdeal A E, Tendsto (· * k) l (𝓝 k)) (x : E) :
    Tendsto (fun e : compactOperatorIdeal A E ↦ (e : AdjointableMap A E E) x) l (𝓝 x) := by
  obtain ⟨k, y, rfl⟩ := exists_compactOperatorIdeal_apply_eq (A := A) x
  have heval : Continuous fun e : compactOperatorIdeal A E ↦ (e : AdjointableMap A E E) y :=
    ((ContinuousLinearMap.apply ℂ E y).continuous.comp
      isometry_toContinuousLinearMap.continuous).comp continuous_subtypeVal
  refine ((heval.tendsto k).comp (hl k)).congr fun e ↦ ?_
  change ((e * k : compactOperatorIdeal A E) : AdjointableMap A E E) y =
    (e : AdjointableMap A E E) ((k : AdjointableMap A E E) y)
  simp [mul_apply_eq_comp]

/-- Along any approximate unit `l` of `K_A(E)`, `e x → x` in `E` for every `x : E`
(Lance, Proposition 2.2). -/
theorem tendsto_compactOperatorIdeal_apply_of_isApproximateUnit
    {l : Filter (compactOperatorIdeal A E)} (hl : l.IsApproximateUnit) (x : E) :
    Tendsto (fun e : compactOperatorIdeal A E ↦ (e : AdjointableMap A E E) x) l (𝓝 x) :=
  tendsto_compactOperatorIdeal_apply_of_tendsto_mul_right hl.tendsto_mul_right x

/-- Along the canonical increasing approximate unit of `K_A(E)`, `e x → x` for every `x : E`. -/
theorem tendsto_approximateUnit_compactOperatorIdeal_apply (x : E) :
    Tendsto (fun e : compactOperatorIdeal A E ↦ (e : AdjointableMap A E E) x)
      (CStarAlgebra.approximateUnit (compactOperatorIdeal A E)) (𝓝 x) :=
  tendsto_compactOperatorIdeal_apply_of_isApproximateUnit
    (CStarAlgebra.increasingApproximateUnit (compactOperatorIdeal A E)).toIsApproximateUnit x

/-- Along any approximate unit `l` of `K_A(E)` and for any `T : L_A(E, F)`, `(T ∘ e) x → T x`
in `F` for every `x : E`. -/
theorem tendsto_comp_compactOperatorIdeal_apply_of_isApproximateUnit
    {l : Filter (compactOperatorIdeal A E)} (hl : l.IsApproximateUnit)
    (T : AdjointableMap A E F) (x : E) :
    Tendsto (fun e : compactOperatorIdeal A E ↦ (T.comp (e : AdjointableMap A E E)) x) l
      (𝓝 (T x)) := by
  refine ((T.continuous.tendsto x).comp
    (tendsto_compactOperatorIdeal_apply_of_isApproximateUnit hl x)).congr fun e ↦ ?_
  simp [comp_apply]

/-- Along any approximate unit `l` of `K_A(E)` and for any `T : L_A(E)`, `(e * T) x → T x`
in `E` for every `x : E`. -/
theorem tendsto_compactOperatorIdeal_mul_apply_of_isApproximateUnit
    {l : Filter (compactOperatorIdeal A E)} (hl : l.IsApproximateUnit)
    (T : AdjointableMap A E E) (x : E) :
    Tendsto (fun e : compactOperatorIdeal A E ↦ ((e : AdjointableMap A E E) * T) x) l
      (𝓝 (T x)) := by
  refine (tendsto_compactOperatorIdeal_apply_of_isApproximateUnit hl (T x)).congr fun e ↦ ?_
  simp [mul_apply_eq_comp]

end Complete

end Nondegenerate

/-! ### The multiplier algebra isomorphism `L_A(E) ≃⋆ₐ[ℂ] 𝓜(ℂ, K_A(E))` -/

section MultiplierIso

variable {A E : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul A E] [CStarModule A E] [CompleteSpace E]

/-- The canonical unital `⋆`-homomorphism `L_A(E) →⋆ₐ[ℂ] 𝓜(ℂ, K_A(E))` sending `T` to
left and right multiplication by `T` on
`K_A(E) = (compactOperatorIdeal A E).toNonUnitalStarSubalgebra`. -/
private noncomputable def toMultiplier :
    AdjointableMap A E E →⋆ₐ[ℂ]
      𝓜(ℂ, (compactOperatorIdeal A E).toNonUnitalStarSubalgebra) :=
  let I := (compactOperatorIdeal A E).toNonUnitalStarSubalgebra
  let ψ := I.multiplierHom (compactOperatorIdeal A E).mul_mem_toNonUnitalStarSubalgebra
  have h1 : ψ 1 = 1 := DoubleCentralizer.ext_fst_snd
    (fun k ↦ Subtype.ext <| by
      rw [I.coe_multiplierHom_fst_apply, one_mul]; rfl)
    (fun k ↦ Subtype.ext <| by
      rw [I.coe_multiplierHom_snd_apply, mul_one]; rfl)
  { __ := ψ
    map_one' := h1
    commutes' c := by
      rw [NonUnitalAlgHom.toFun_eq_coe, NonUnitalStarAlgHom.coe_toNonUnitalAlgHom,
        Algebra.algebraMap_eq_smul_one, map_smul, h1, Algebra.algebraMap_eq_smul_one] }

private theorem coe_toMultiplier_fst (T : AdjointableMap A E E)
    (k : (compactOperatorIdeal A E).toNonUnitalStarSubalgebra) :
    ((toMultiplier T).fst k : AdjointableMap A E E) = T * (k : AdjointableMap A E E) :=
  (compactOperatorIdeal A E).toNonUnitalStarSubalgebra.coe_multiplierHom_fst_apply _ T k

private theorem coe_toMultiplier_snd (T : AdjointableMap A E E)
    (k : (compactOperatorIdeal A E).toNonUnitalStarSubalgebra) :
    ((toMultiplier T).snd k : AdjointableMap A E E) = (k : AdjointableMap A E E) * T :=
  (compactOperatorIdeal A E).toNonUnitalStarSubalgebra.coe_multiplierHom_snd_apply _ T k

private theorem toMultiplier_coe (k : (compactOperatorIdeal A E).toNonUnitalStarSubalgebra) :
    toMultiplier (k : AdjointableMap A E E) =
      (k : 𝓜(ℂ, (compactOperatorIdeal A E).toNonUnitalStarSubalgebra)) :=
  DoubleCentralizer.ext_fst_snd
    (fun u ↦ Subtype.ext (coe_toMultiplier_fst _ u))
    (fun u ↦ Subtype.ext (coe_toMultiplier_snd _ u))

/-- Action of a multiplier `m : 𝓜(ℂ, K_A(E))` on `x : E`, defined by choosing a factorization
`x = k y` with `k : K_A(E)` and setting `m x := (m.fst k) y`. -/
private noncomputable def multiplierApply
    (m : 𝓜(ℂ, (compactOperatorIdeal A E).toNonUnitalStarSubalgebra)) (x : E) : E :=
  let h := exists_compactOperatorSubalgebra_apply_eq (A := A) x
  ((m.fst h.choose : AdjointableMap A E E) h.choose_spec.choose)

private theorem multiplierApply_eq_of_apply_eq
    (m : 𝓜(ℂ, (compactOperatorIdeal A E).toNonUnitalStarSubalgebra))
    {k₁ k₂ : (compactOperatorIdeal A E).toNonUnitalStarSubalgebra} {y₁ y₂ : E}
    (h : (k₁ : AdjointableMap A E E) y₁ = (k₂ : AdjointableMap A E E) y₂) :
    ((m.fst k₁ : AdjointableMap A E E) y₁) = ((m.fst k₂ : AdjointableMap A E E) y₂) := by
  refine eq_of_forall_compactOperator_apply_eq (A := A) fun u hu ↦ ?_
  let u' : (compactOperatorIdeal A E).toNonUnitalStarSubalgebra :=
    ⟨u, (TwoSidedIdeal.mem_toNonUnitalStarSubalgebra _).mpr (mem_compactOperatorIdeal.mpr hu)⟩
  have calc_eq (k : (compactOperatorIdeal A E).toNonUnitalStarSubalgebra) (y : E) :
      u ((m.fst k : AdjointableMap A E E) y) =
        ((m.snd u' : AdjointableMap A E E) ((k : AdjointableMap A E E) y)) := by
    calc u ((m.fst k : AdjointableMap A E E) y)
        = (((u' * m.fst k : (compactOperatorIdeal A E).toNonUnitalStarSubalgebra) :
            AdjointableMap A E E)) y := by simp [u', mul_apply_eq_comp]
      _ = (((m.snd u' * k : (compactOperatorIdeal A E).toNonUnitalStarSubalgebra) :
            AdjointableMap A E E)) y := by
          rw [m.central u' k]
      _ = (m.snd u' : AdjointableMap A E E) ((k : AdjointableMap A E E) y) := by
          simp [mul_apply_eq_comp]
  rw [calc_eq k₁ y₁, calc_eq k₂ y₂, h]

private theorem multiplierApply_apply_compactOperator
    (m : 𝓜(ℂ, (compactOperatorIdeal A E).toNonUnitalStarSubalgebra))
    (k : (compactOperatorIdeal A E).toNonUnitalStarSubalgebra) (y : E) :
    multiplierApply m ((k : AdjointableMap A E E) y) = (m.fst k : AdjointableMap A E E) y :=
  multiplierApply_eq_of_apply_eq m (Exists.choose_spec (exists_compactOperatorSubalgebra_apply_eq
    (A := A) ((k : AdjointableMap A E E) y)).choose_spec)

private theorem isAdjointPair_multiplierApply
    (m : 𝓜(ℂ, (compactOperatorIdeal A E).toNonUnitalStarSubalgebra)) (x₁ x₂ : E) :
    inner A (multiplierApply m x₁) x₂ = inner A x₁ (multiplierApply (star m) x₂) := by
  obtain ⟨k₁, y₁, rfl⟩ := exists_compactOperatorSubalgebra_apply_eq (A := A) x₁
  obtain ⟨k₂, y₂, rfl⟩ := exists_compactOperatorSubalgebra_apply_eq (A := A) x₂
  rw [multiplierApply_apply_compactOperator m k₁ y₁,
    multiplierApply_apply_compactOperator (star m) k₂ y₂]
  have hcent : star k₂ * m.fst k₁ = star ((star m).fst k₂) * k₁ := by
    simpa [DoubleCentralizer.star_fst] using (m.central (star k₂) k₁).symm
  have hcoe : (star (k₂ : AdjointableMap A E E) * (m.fst k₁ : AdjointableMap A E E)) =
      (star ((star m).fst k₂ : AdjointableMap A E E) * (k₁ : AdjointableMap A E E)) :=
    congrArg Subtype.val hcent
  calc inner A ((m.fst k₁ : AdjointableMap A E E) y₁) ((k₂ : AdjointableMap A E E) y₂)
      = inner A ((star (k₂ : AdjointableMap A E E) *
          (m.fst k₁ : AdjointableMap A E E)) y₁) y₂ := by
        rw [mul_apply_eq_comp, star_eq_adjoint, adjoint_inner_left]
    _ = inner A ((star ((star m).fst k₂ : AdjointableMap A E E) *
          (k₁ : AdjointableMap A E E)) y₁) y₂ := by
        rw [hcoe]
    _ = inner A ((k₁ : AdjointableMap A E E) y₁)
          (((star m).fst k₂ : AdjointableMap A E E) y₂) := by
        rw [mul_apply_eq_comp, star_eq_adjoint, adjoint_inner_left]

variable (A E) in
/-- **Multiplier representation of adjointable operators** (Raeburn–Williams, Corollary 2.54):
for any complete Hilbert C⋆-module `E` over `A`, `L_A(E) = AdjointableMap A E E` is unital
`⋆`-isomorphic to the multiplier algebra `𝓜(ℂ, K_A(E))` of the module-compact ideal
`K_A(E) = (compactOperatorIdeal A E).toNonUnitalStarSubalgebra`. Under this isomorphism,
`T : L_A(E)` corresponds to the double centralizer `(k ↦ T * k, k ↦ k * T)`, and the canonical
inclusion `K_A(E) → 𝓜(ℂ, K_A(E))` corresponds to `K_A(E) ↪ L_A(E)`.
It is isometric (`norm_multiplierStarAlgEquiv`). -/
noncomputable def multiplierStarAlgEquiv :
    AdjointableMap A E E ≃⋆ₐ[ℂ]
      𝓜(ℂ, (compactOperatorIdeal A E).toNonUnitalStarSubalgebra) where
  toFun := toMultiplier (A := A) (E := E)
  invFun m :=
    AdjointableMap.ofAdjointPair (multiplierApply m) (multiplierApply (star m))
      (isAdjointPair_multiplierApply m)
  left_inv T := ext fun x ↦ by
    obtain ⟨k, y, rfl⟩ := exists_compactOperatorSubalgebra_apply_eq (A := A) x
    rw [ofAdjointPair_apply, multiplierApply_apply_compactOperator]
    have h := congrArg (fun S : AdjointableMap A E E ↦ S y) (coe_toMultiplier_fst T k)
    simpa [mul_apply_eq_comp] using h
  right_inv m := DoubleCentralizer.ext_fst_snd
    (fun k ↦ Subtype.ext <| ext fun y ↦ by
      rw [coe_toMultiplier_fst, mul_apply_eq_comp]
      change AdjointableMap.ofAdjointPair (multiplierApply m) (multiplierApply (star m))
          (isAdjointPair_multiplierApply m) ((k : AdjointableMap A E E) y) =
        (m.fst k : AdjointableMap A E E) y
      rw [ofAdjointPair_apply, multiplierApply_apply_compactOperator])
    (fun k ↦ Subtype.ext <| ext fun y ↦ by
      obtain ⟨k_y, y', hy⟩ := exists_compactOperatorSubalgebra_apply_eq (A := A) y
      rw [coe_toMultiplier_snd, mul_apply_eq_comp]
      change (k : AdjointableMap A E E) (AdjointableMap.ofAdjointPair (multiplierApply m)
          (multiplierApply (star m)) (isAdjointPair_multiplierApply m) y) =
        (m.snd k : AdjointableMap A E E) y
      rw [ofAdjointPair_apply, ← hy, multiplierApply_apply_compactOperator]
      calc (k : AdjointableMap A E E) ((m.fst k_y : AdjointableMap A E E) y')
          = ((k * m.fst k_y : (compactOperatorIdeal A E).toNonUnitalStarSubalgebra) :
              AdjointableMap A E E) y' := by simp [mul_apply_eq_comp]
        _ = ((m.snd k * k_y : (compactOperatorIdeal A E).toNonUnitalStarSubalgebra) :
              AdjointableMap A E E) y' := by
            rw [m.central k k_y]
        _ = (m.snd k : AdjointableMap A E E) ((k_y : AdjointableMap A E E) y') := by
            simp [mul_apply_eq_comp])
  map_mul' := map_mul (toMultiplier (A := A) (E := E))
  map_add' := map_add (toMultiplier (A := A) (E := E))
  map_smul' := map_smul (toMultiplier (A := A) (E := E))
  map_star' := map_star (toMultiplier (A := A) (E := E))

/-- The left centralizer of `multiplierStarAlgEquiv A E T` acts on `K_A(E)` by left
multiplication by `T`. -/
@[simp]
theorem coe_multiplierStarAlgEquiv_fst (T : AdjointableMap A E E)
    (k : (compactOperatorIdeal A E).toNonUnitalStarSubalgebra) :
    ((multiplierStarAlgEquiv A E T).fst k : AdjointableMap A E E) =
      T * (k : AdjointableMap A E E) :=
  coe_toMultiplier_fst T k

/-- The right centralizer of `multiplierStarAlgEquiv A E T` acts on `K_A(E)` by right
multiplication by `T`. -/
@[simp]
theorem coe_multiplierStarAlgEquiv_snd (T : AdjointableMap A E E)
    (k : (compactOperatorIdeal A E).toNonUnitalStarSubalgebra) :
    ((multiplierStarAlgEquiv A E T).snd k : AdjointableMap A E E) =
      (k : AdjointableMap A E E) * T :=
  coe_toMultiplier_snd T k

/-- On `K_A(E)`, `multiplierStarAlgEquiv A E` agrees with the canonical inclusion
`K_A(E) → 𝓜(ℂ, K_A(E))`. -/
@[simp]
theorem multiplierStarAlgEquiv_coe (k : (compactOperatorIdeal A E).toNonUnitalStarSubalgebra) :
    multiplierStarAlgEquiv A E (k : AdjointableMap A E E) =
      (k : 𝓜(ℂ, (compactOperatorIdeal A E).toNonUnitalStarSubalgebra)) :=
  toMultiplier_coe k

/-- The inverse of `multiplierStarAlgEquiv A E` sends the canonical image of `k : K_A(E)` in
`𝓜(ℂ, K_A(E))` back to `(k : L_A(E))`. -/
@[simp]
theorem multiplierStarAlgEquiv_symm_coe
    (k : (compactOperatorIdeal A E).toNonUnitalStarSubalgebra) :
    (multiplierStarAlgEquiv A E).symm
        (k : 𝓜(ℂ, (compactOperatorIdeal A E).toNonUnitalStarSubalgebra)) =
      (k : AdjointableMap A E E) := by
  rw [← multiplierStarAlgEquiv_coe, StarAlgEquiv.symm_apply_apply]

/-- Multiplying `(multiplierStarAlgEquiv A E).symm m` on the right by `k : K_A(E)` yields
`(m.fst k : L_A(E))`. -/
@[simp]
theorem multiplierStarAlgEquiv_symm_mul_compactOperator
    (m : 𝓜(ℂ, (compactOperatorIdeal A E).toNonUnitalStarSubalgebra))
    (k : (compactOperatorIdeal A E).toNonUnitalStarSubalgebra) :
    (multiplierStarAlgEquiv A E).symm m * (k : AdjointableMap A E E) =
      (m.fst k : AdjointableMap A E E) := by
  rw [← coe_multiplierStarAlgEquiv_fst, StarAlgEquiv.apply_symm_apply]

/-- Multiplying `(multiplierStarAlgEquiv A E).symm m` on the left by `k : K_A(E)` yields
`(m.snd k : L_A(E))`. -/
@[simp]
theorem compactOperator_mul_multiplierStarAlgEquiv_symm
    (k : (compactOperatorIdeal A E).toNonUnitalStarSubalgebra)
    (m : 𝓜(ℂ, (compactOperatorIdeal A E).toNonUnitalStarSubalgebra)) :
    (k : AdjointableMap A E E) * (multiplierStarAlgEquiv A E).symm m =
      (m.snd k : AdjointableMap A E E) := by
  rw [← coe_multiplierStarAlgEquiv_snd, StarAlgEquiv.apply_symm_apply]

/-- Evaluating `(multiplierStarAlgEquiv A E).symm m` on a factored vector `k y` gives
`(m.fst k : L_A(E)) y`. -/
theorem multiplierStarAlgEquiv_symm_apply_compactOperator
    (m : 𝓜(ℂ, (compactOperatorIdeal A E).toNonUnitalStarSubalgebra))
    (k : (compactOperatorIdeal A E).toNonUnitalStarSubalgebra) (y : E) :
    (multiplierStarAlgEquiv A E).symm m ((k : AdjointableMap A E E) y) =
      (m.fst k : AdjointableMap A E E) y := by
  rw [← mul_apply_eq_comp, multiplierStarAlgEquiv_symm_mul_compactOperator]

/-- The adjoint of `(multiplierStarAlgEquiv A E).symm m` is
`(multiplierStarAlgEquiv A E).symm (star m)`. -/
@[simp]
theorem adjoint_multiplierStarAlgEquiv_symm
    (m : 𝓜(ℂ, (compactOperatorIdeal A E).toNonUnitalStarSubalgebra)) :
    ((multiplierStarAlgEquiv A E).symm m).adjoint = (multiplierStarAlgEquiv A E).symm (star m) := by
  rw [← star_eq_adjoint, ← map_star]

/-- Along any right-multiplication approximate unit `l` of `K_A(E)`, the compact operators
`m.fst e` converge pointwise on `E` to `(multiplierStarAlgEquiv A E).symm m`. -/
theorem tendsto_compactOperatorIdeal_fst_apply
    {l : Filter (compactOperatorIdeal A E).toNonUnitalStarSubalgebra}
    (hl : ∀ k : (compactOperatorIdeal A E).toNonUnitalStarSubalgebra, Tendsto (· * k) l (𝓝 k))
    (m : 𝓜(ℂ, (compactOperatorIdeal A E).toNonUnitalStarSubalgebra)) (x : E) :
    Tendsto (fun e : (compactOperatorIdeal A E).toNonUnitalStarSubalgebra ↦
        ((m.fst e : AdjointableMap A E E) x)) l
      (𝓝 ((multiplierStarAlgEquiv A E).symm m x)) := by
  obtain ⟨k, y, rfl⟩ := exists_compactOperatorSubalgebra_apply_eq (A := A) x
  have heval : Continuous fun e : (compactOperatorIdeal A E).toNonUnitalStarSubalgebra ↦
      ((m.fst e : AdjointableMap A E E) y) :=
    (((ContinuousLinearMap.apply ℂ E y).continuous.comp
      isometry_toContinuousLinearMap.continuous).comp continuous_subtypeVal).comp
      m.fst.continuous
  rw [multiplierStarAlgEquiv_symm_apply_compactOperator]
  refine ((heval.tendsto k).comp (hl k)).congr fun e ↦ ?_
  rw [Function.comp_apply, DoubleCentralizer.fst_mul]
  simp [mul_apply_eq_comp]

/-- `L_A(E) ≃⋆ₐ[ℂ] 𝓜(ℂ, K_A(E))` is isometric. -/
@[simp]
theorem norm_multiplierStarAlgEquiv (T : AdjointableMap A E E) :
    ‖multiplierStarAlgEquiv A E T‖ = ‖T‖ :=
  StarAlgEquiv.norm_map (multiplierStarAlgEquiv A E) T

/-- `L_A(E) ≃⋆ₐ[ℂ] 𝓜(ℂ, K_A(E))` is an isometry. -/
theorem isometry_multiplierStarAlgEquiv : Isometry (multiplierStarAlgEquiv A E) :=
  AddMonoidHomClass.isometry_of_norm _ norm_multiplierStarAlgEquiv

/-- Under `L_A(E) ≃⋆ₐ[ℂ] 𝓜(ℂ, K_A(E))`, the module-compact operators `K_A(E)`
correspond to the canonical image of `K_A(E)` in its multiplier algebra. -/
theorem mem_compactOperator_iff_exists_coe_eq_multiplierStarAlgEquiv
    {T : AdjointableMap A E E} :
    T ∈ compactOperator A E E ↔
      ∃ k : (compactOperatorIdeal A E).toNonUnitalStarSubalgebra,
        (k : 𝓜(ℂ, (compactOperatorIdeal A E).toNonUnitalStarSubalgebra)) =
          multiplierStarAlgEquiv A E T := by
  refine ⟨fun hT ↦ ⟨⟨T, (TwoSidedIdeal.mem_toNonUnitalStarSubalgebra _).mpr
      (mem_compactOperatorIdeal.mpr hT)⟩, ?_⟩, ?_⟩
  · exact (multiplierStarAlgEquiv_coe _).symm
  · rintro ⟨k, hk⟩
    have hT : T = (k : AdjointableMap A E E) :=
      (multiplierStarAlgEquiv A E).injective (hk.symm.trans (multiplierStarAlgEquiv_coe k).symm)
    rw [hT]
    exact mem_compactOperatorIdeal.mp
      ((TwoSidedIdeal.mem_toNonUnitalStarSubalgebra _).mp k.property)

/-- Compatibility with the right self-module (`Adjointable.Self`): on `E = A` as a right module
`Aᵐᵒᵖ`, `L_A(A) ≃⋆ₐ[ℂ] 𝓜(ℂ, A)` followed by `DoubleCentralizer.congr` along
`A ≃⋆ₐ[ℂ] K_A(A)` equals `multiplierStarAlgEquiv Aᵐᵒᵖ A`. -/
theorem multiplierMulOppositeStarAlgEquiv_trans_congr (A : Type*) [NonUnitalCStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A] :
    (multiplierMulOppositeStarAlgEquiv A).trans
        (DoubleCentralizer.congr
          ((compactOperatorMulOppositeStarAlgEquiv A).trans
            (compactOperatorIdeal Aᵐᵒᵖ A).toNonUnitalStarSubalgebraEquiv)) =
      multiplierStarAlgEquiv Aᵐᵒᵖ A := by
  let e : A ≃⋆ₐ[ℂ] (compactOperatorIdeal Aᵐᵒᵖ A).toNonUnitalStarSubalgebra :=
    (compactOperatorMulOppositeStarAlgEquiv A).trans
      (compactOperatorIdeal Aᵐᵒᵖ A).toNonUnitalStarSubalgebraEquiv
  have he_apply (a : A) : (e a : AdjointableMap Aᵐᵒᵖ A A) = mulLeft A a := by
    dsimp only [e]
    rw [StarAlgEquiv.trans_apply, TwoSidedIdeal.coe_toNonUnitalStarSubalgebraEquiv_apply,
      coe_compactOperatorMulOppositeStarAlgEquiv_apply]
  ext T : 1
  refine DoubleCentralizer.ext_fst_snd (fun k ↦ Subtype.ext ?_) (fun k ↦ Subtype.ext ?_)
  · have ha : mulLeft A (e.symm k) = (k : AdjointableMap Aᵐᵒᵖ A A) := by simp [← he_apply]
    calc (((multiplierMulOppositeStarAlgEquiv A).trans (DoubleCentralizer.congr e) T).fst k :
            AdjointableMap Aᵐᵒᵖ A A)
        = mulLeft A (T (e.symm k)) := by
          rw [StarAlgEquiv.trans_apply, DoubleCentralizer.congr_apply_fst, he_apply,
            multiplierMulOppositeStarAlgEquiv_fst]
          rfl
      _ = T * (k : AdjointableMap Aᵐᵒᵖ A A) := by
          rw [← ha]; ext x
          simpa [mul_apply_eq_comp, MulOpposite.smul_eq_mul_unop] using
            (T.map_smul_coeff (MulOpposite.op x) (e.symm k)).symm
      _ = ((multiplierStarAlgEquiv Aᵐᵒᵖ A T).fst k : AdjointableMap Aᵐᵒᵖ A A) := by
          rw [coe_multiplierStarAlgEquiv_fst]
  · have ha : mulLeft A (e.symm k) = (k : AdjointableMap Aᵐᵒᵖ A A) := by simp [← he_apply]
    calc (((multiplierMulOppositeStarAlgEquiv A).trans (DoubleCentralizer.congr e) T).snd k :
            AdjointableMap Aᵐᵒᵖ A A)
        = mulLeft A (star (T.adjoint (star (e.symm k)))) := by
          rw [StarAlgEquiv.trans_apply, DoubleCentralizer.congr_apply_snd, he_apply,
            multiplierMulOppositeStarAlgEquiv_snd_apply]
      _ = (k : AdjointableMap Aᵐᵒᵖ A A) * T := by
          rw [← ha]; ext x
          have h := T.star_adjoint_apply_mul (star (e.symm k)) x
          rw [star_star] at h
          simpa [mul_apply_eq_comp] using h
      _ = ((multiplierStarAlgEquiv Aᵐᵒᵖ A T).snd k : AdjointableMap Aᵐᵒᵖ A A) := by
          rw [coe_multiplierStarAlgEquiv_snd]

end MultiplierIso

/-! ### Strict topology on `L_A(E)` and strong-* convergence -/

section StrictTopology

section Unbounded

variable {A E F : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul A E] [CStarModule A E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul A F] [CStarModule A F]

private theorem tendsto_comp_sum_rankOne_of_tendsto
    {ι : Type*} {l : Filter ι} {G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G]
    [SMul A G] [CStarModule A G] {f : ι → AdjointableMap A E F} {T : AdjointableMap A E F}
    (hf : ∀ x : E, Tendsto (fun i ↦ f i x) l (𝓝 (T x)))
    {n : ℕ} (x : Fin n → E) (y : Fin n → G) :
    Tendsto (fun i ↦ (f i).comp (∑ j, rankOne A (x j) (y j))) l
      (𝓝 (T.comp (∑ j, rankOne A (x j) (y j)))) := by
  have hrank (u : E) (v : G) :
      Tendsto (fun i ↦ (f i).comp (rankOne A u v)) l (𝓝 (T.comp (rankOne A u v))) := by
    refine tendsto_iff_norm_sub_tendsto_zero.mpr <| squeeze_zero (fun _ ↦ norm_nonneg _)
      (fun i ↦ ?_) (by simpa only [zero_mul] using
        (tendsto_iff_norm_sub_tendsto_zero.mp (hf u)).mul_const ‖v‖)
    rw [comp_rankOne, comp_rankOne, ← rankOne_sub_left]
    exact norm_rankOne_le (f i u - T u) v
  have hcomp (S : AdjointableMap A E F) :
      S.comp (∑ j, rankOne A (x j) (y j)) = ∑ j, S.comp (rankOne A (x j) (y j)) := by
    ext z; simp
  simp_rw [hcomp]
  exact tendsto_finsetSum Finset.univ fun j _ ↦ hrank (x j) (y j)

/-- Along any norm-bounded filter of adjointable operators converging strongly on `E`,
composition on the right with any module-compact operator `k ∈ K_A(G, E)` converges in operator
norm. -/
theorem tendsto_comp_of_mem_compactOperator_of_eventually_norm_le
    {ι : Type*} {l : Filter ι} {G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G]
    [SMul A G] [CStarModule A G] {f : ι → AdjointableMap A E F} {T : AdjointableMap A E F}
    {C : ℝ} (hC : ∀ᶠ i in l, ‖f i‖ ≤ C)
    (hf : ∀ x : E, Tendsto (fun i ↦ f i x) l (𝓝 (T x)))
    {k : AdjointableMap A G E} (hk : k ∈ compactOperator A G E) :
    Tendsto (fun i ↦ (f i).comp k) l (𝓝 (T.comp k)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  set M : ℝ := max C 0 + ‖T‖ + 1
  have hM : 0 < M := by positivity
  obtain ⟨n, x, y, hkS⟩ :=
    mem_compactOperator_iff_forall_exists_sum.mp hk (ε / (2 * M)) (by positivity)
  set S : AdjointableMap A G E := ∑ j, rankOne A (x j) (y j)
  have hS_lim : ∀ᶠ i in l, dist ((f i).comp S) (T.comp S) < ε / 2 :=
    Metric.tendsto_nhds.mp (tendsto_comp_sum_rankOne_of_tendsto hf x y) (ε / 2) (by positivity)
  filter_upwards [hC, hS_lim] with i hiC hiS
  rw [dist_eq_norm] at hiS ⊢
  have hsplit : (f i).comp k - T.comp k =
      ((f i).comp (k - S) - T.comp (k - S)) + ((f i).comp S - T.comp S) := by
    ext z; simp [map_sub]; abel
  have hdiff_norm : ‖(f i).comp (k - S) - T.comp (k - S)‖ ≤ M * ‖k - S‖ := by
    calc ‖(f i).comp (k - S) - T.comp (k - S)‖
        ≤ ‖(f i).comp (k - S)‖ + ‖T.comp (k - S)‖ := norm_sub_le _ _
      _ ≤ ‖f i‖ * ‖k - S‖ + ‖T‖ * ‖k - S‖ :=
          add_le_add (opNorm_comp_le (f i) (k - S)) (opNorm_comp_le T (k - S))
      _ = (‖f i‖ + ‖T‖) * ‖k - S‖ := by ring
      _ ≤ M * ‖k - S‖ := by gcongr; linarith [le_max_left C 0]
  have hterm1 : ‖(f i).comp (k - S) - T.comp (k - S)‖ ≤ ε / 2 :=
    hdiff_norm.trans <| (mul_le_mul_of_nonneg_left hkS.le hM.le).trans_eq <| by
      field_simp
  calc ‖(f i).comp k - T.comp k‖
      ≤ ‖(f i).comp (k - S) - T.comp (k - S)‖ + ‖(f i).comp S - T.comp S‖ := by
        rw [hsplit]; exact norm_add_le _ _
    _ < ε / 2 + ε / 2 := add_lt_add_of_le_of_lt hterm1 hiS
    _ = ε := add_halves ε

/-- Along any norm-bounded filter `f i` converging strongly on `E`, `f i * k → T * k` in
operator norm for every `k ∈ K_A(E)`. -/
theorem tendsto_mul_of_mem_compactOperator_of_eventually_norm_le
    {ι : Type*} {l : Filter ι} {f : ι → AdjointableMap A E E} {T : AdjointableMap A E E}
    {C : ℝ} (hC : ∀ᶠ i in l, ‖f i‖ ≤ C)
    (hf : ∀ x : E, Tendsto (fun i ↦ f i x) l (𝓝 (T x)))
    {k : AdjointableMap A E E} (hk : k ∈ compactOperator A E E) :
    Tendsto (fun i ↦ f i * k) l (𝓝 (T * k)) :=
  tendsto_comp_of_mem_compactOperator_of_eventually_norm_le hC hf hk

/-- Along any norm-bounded filter `f i` whose adjoints `(f i).adjoint` converge strongly on `E`,
`k * f i → k * T` in operator norm for every `k ∈ K_A(E)`. -/
theorem tendsto_of_mem_compactOperator_mul_of_eventually_norm_le
    {ι : Type*} {l : Filter ι} {f : ι → AdjointableMap A E E} {T : AdjointableMap A E E}
    {C : ℝ} (hC : ∀ᶠ i in l, ‖f i‖ ≤ C)
    (hf_adj : ∀ x : E, Tendsto (fun i ↦ (f i).adjoint x) l (𝓝 (T.adjoint x)))
    {k : AdjointableMap A E E} (hk : k ∈ compactOperator A E E) :
    Tendsto (fun i ↦ k * f i) l (𝓝 (k * T)) := by
  have hC_adj : ∀ᶠ i in l, ‖(f i).adjoint‖ ≤ C := by
    filter_upwards [hC] with i hi
    simpa [norm_adjoint] using hi
  have hcomp := tendsto_mul_of_mem_compactOperator_of_eventually_norm_le hC_adj hf_adj
    (adjoint_mem_compactOperator hk)
  have hadj := continuous_adjoint.continuousAt.tendsto.comp hcomp
  simpa [Function.comp_def, adjoint_mul, adjoint_adjoint] using hadj

end Unbounded

section Complete

/-- The `⋆`-isomorphism `L_A(E) ≃⋆ₐ[ℂ] 𝓜ₛ(ℂ, K_A(E))` equipping `L_A(E)` with the
strict topology of `𝓜ₛ(ℂ, K_A(E))`. -/
noncomputable def multiplierStrictStarAlgEquiv (A E : Type*) [NonUnitalCStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A] [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul A E]
    [CStarModule A E] [CompleteSpace E] :
    AdjointableMap A E E ≃⋆ₐ[ℂ]
      𝓜ₛ(ℂ, (compactOperatorIdeal A E).toNonUnitalStarSubalgebra) :=
  (multiplierStarAlgEquiv A E).trans DoubleCentralizerStrict.starAlgEquiv.symm

variable {A E : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul A E] [CStarModule A E] [CompleteSpace E]

@[simp]
theorem toDoubleCentralizer_multiplierStrictStarAlgEquiv (T : AdjointableMap A E E) :
    (multiplierStrictStarAlgEquiv A E T).toDoubleCentralizer = multiplierStarAlgEquiv A E T :=
  (rfl)

@[simp]
theorem multiplierStrictStarAlgEquiv_symm_toDoubleCentralizer
    (m : 𝓜ₛ(ℂ, (compactOperatorIdeal A E).toNonUnitalStarSubalgebra)) :
    (multiplierStrictStarAlgEquiv A E).symm m =
      (multiplierStarAlgEquiv A E).symm m.toDoubleCentralizer :=
  (rfl)

@[simp]
theorem coe_multiplierStrictStarAlgEquiv
    (k : (compactOperatorIdeal A E).toNonUnitalStarSubalgebra) :
    multiplierStrictStarAlgEquiv A E (k : AdjointableMap A E E) =
      (k : 𝓜ₛ(ℂ, (compactOperatorIdeal A E).toNonUnitalStarSubalgebra)) :=
  DoubleCentralizerStrict.toDoubleCentralizer_injective (multiplierStarAlgEquiv_coe k)

theorem multiplierStrictStarAlgEquiv_symm_coe
    (k : (compactOperatorIdeal A E).toNonUnitalStarSubalgebra) :
    (multiplierStrictStarAlgEquiv A E).symm
        (k : 𝓜ₛ(ℂ, (compactOperatorIdeal A E).toNonUnitalStarSubalgebra)) =
      (k : AdjointableMap A E E) := by
  rw [← coe_multiplierStrictStarAlgEquiv, StarAlgEquiv.symm_apply_apply]

theorem norm_multiplierStrictStarAlgEquiv (T : AdjointableMap A E E) :
    ‖(multiplierStrictStarAlgEquiv A E T).toDoubleCentralizer‖ = ‖T‖ :=
  norm_multiplierStarAlgEquiv T

/-- **Global strict-to-strong continuity on `L_A(E)`:** for every `x : E`, evaluation at `x` is
globally strictly continuous on `𝓜ₛ(ℂ, K_A(E))` (without norm-boundedness). -/
@[fun_prop]
theorem continuous_apply_multiplierStrictStarAlgEquiv_symm (x : E) :
    Continuous fun m : 𝓜ₛ(ℂ, (compactOperatorIdeal A E).toNonUnitalStarSubalgebra) ↦
      (multiplierStrictStarAlgEquiv A E).symm m x := by
  obtain ⟨k, y, rfl⟩ := exists_compactOperatorSubalgebra_apply_eq (A := A) x
  have heval :
      Continuous fun m : 𝓜ₛ(ℂ, (compactOperatorIdeal A E).toNonUnitalStarSubalgebra) ↦
        ((m.toDoubleCentralizer.fst k : AdjointableMap A E E) y) :=
    (((ContinuousLinearMap.apply ℂ E y).continuous.comp
      isometry_toContinuousLinearMap.continuous).comp continuous_subtypeVal).comp
      (DoubleCentralizerStrict.continuous_fst_apply k)
  exact heval.congr fun m ↦ (multiplierStarAlgEquiv_symm_apply_compactOperator
    m.toDoubleCentralizer k y).symm

/-- **Global strict-to-strong-* continuity on `L_A(E)`:** for every `x : E`, evaluation of the
adjoint at `x` is globally strictly continuous on `𝓜ₛ(ℂ, K_A(E))`. -/
@[fun_prop]
theorem continuous_adjoint_apply_multiplierStrictStarAlgEquiv_symm (x : E) :
    Continuous fun m : 𝓜ₛ(ℂ, (compactOperatorIdeal A E).toNonUnitalStarSubalgebra) ↦
      ((multiplierStrictStarAlgEquiv A E).symm m).adjoint x :=
  ((continuous_apply_multiplierStrictStarAlgEquiv_symm (A := A) x).comp
    continuous_star).congr fun m ↦ by
      rw [Function.comp_apply, ← star_eq_adjoint, map_star]

/-- Global strict-to-strong continuity of `(multiplierStrictStarAlgEquiv A E).symm` into the
pointwise-convergence operator space `E →Lₚₜ[ℂ] E`. -/
theorem continuous_toPointwiseConvergenceCLM_multiplierStrictStarAlgEquiv_symm :
    Continuous fun m : 𝓜ₛ(ℂ, (compactOperatorIdeal A E).toNonUnitalStarSubalgebra) ↦
      ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) E E
        ((multiplierStrictStarAlgEquiv A E).symm m).toContinuousLinearMap :=
  PointwiseConvergenceCLM.continuous_of_continuous_eval
    continuous_apply_multiplierStrictStarAlgEquiv_symm

/-- Global strict-to-strong continuity of the adjoint of `(multiplierStrictStarAlgEquiv A E).symm`
into `E →Lₚₜ[ℂ] E`. -/
theorem continuous_toPointwiseConvergenceCLM_adjoint_multiplierStrictStarAlgEquiv_symm :
    Continuous fun m : 𝓜ₛ(ℂ, (compactOperatorIdeal A E).toNonUnitalStarSubalgebra) ↦
      ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) E E
        ((multiplierStrictStarAlgEquiv A E).symm m).adjoint.toContinuousLinearMap :=
  PointwiseConvergenceCLM.continuous_of_continuous_eval
    continuous_adjoint_apply_multiplierStrictStarAlgEquiv_symm

/-- Strict convergence in `𝓜ₛ(ℂ, K_A(E))` implies pointwise norm convergence on `E`. -/
theorem tendsto_apply_of_tendsto_multiplierStrictStarAlgEquiv {ι : Type*} {l : Filter ι}
    {f : ι → AdjointableMap A E E} {T : AdjointableMap A E E}
    (hf : Tendsto (fun i ↦ multiplierStrictStarAlgEquiv A E (f i)) l
      (𝓝 (multiplierStrictStarAlgEquiv A E T))) (x : E) :
    Tendsto (fun i ↦ f i x) l (𝓝 (T x)) := by
  have h := ((continuous_apply_multiplierStrictStarAlgEquiv_symm (A := A) x).tendsto
    (multiplierStrictStarAlgEquiv A E T)).comp hf
  rw [StarAlgEquiv.symm_apply_apply] at h
  exact h.congr fun i ↦ by rw [Function.comp_apply, StarAlgEquiv.symm_apply_apply]

/-- Strict convergence in `𝓜ₛ(ℂ, K_A(E))` implies pointwise norm convergence of adjoints on
`E`. -/
theorem tendsto_adjoint_apply_of_tendsto_multiplierStrictStarAlgEquiv {ι : Type*} {l : Filter ι}
    {f : ι → AdjointableMap A E E} {T : AdjointableMap A E E}
    (hf : Tendsto (fun i ↦ multiplierStrictStarAlgEquiv A E (f i)) l
      (𝓝 (multiplierStrictStarAlgEquiv A E T))) (x : E) :
    Tendsto (fun i ↦ (f i).adjoint x) l (𝓝 (T.adjoint x)) := by
  have h := ((continuous_adjoint_apply_multiplierStrictStarAlgEquiv_symm (A := A) x).tendsto
    (multiplierStrictStarAlgEquiv A E T)).comp hf
  rw [StarAlgEquiv.symm_apply_apply] at h
  exact h.congr fun i ↦ by rw [Function.comp_apply, StarAlgEquiv.symm_apply_apply]

/-- On norm-bounded filters, pointwise norm convergence of `f i` and `(f i).adjoint` on `E`
implies strict convergence in `𝓜ₛ(ℂ, K_A(E))`. -/
theorem tendsto_multiplierStrictStarAlgEquiv_of_eventually_norm_le {ι : Type*} {l : Filter ι}
    {f : ι → AdjointableMap A E E} {T : AdjointableMap A E E} {C : ℝ}
    (hC : ∀ᶠ i in l, ‖f i‖ ≤ C)
    (hf : ∀ x : E, Tendsto (fun i ↦ f i x) l (𝓝 (T x)))
    (hf_adj : ∀ x : E, Tendsto (fun i ↦ (f i).adjoint x) l (𝓝 (T.adjoint x))) :
    Tendsto (fun i ↦ multiplierStrictStarAlgEquiv A E (f i)) l
      (𝓝 (multiplierStrictStarAlgEquiv A E T)) := by
  rw [DoubleCentralizerStrict.tendsto_iff_forall_tendsto]
  refine ⟨fun k ↦ ?_, fun k ↦ ?_⟩
  · rw [isometry_subtypeVal.tendsto_nhds_iff]
    simpa [Function.comp_def] using
      tendsto_mul_of_mem_compactOperator_of_eventually_norm_le hC hf
        (mem_compactOperatorIdeal.mp
          ((TwoSidedIdeal.mem_toNonUnitalStarSubalgebra _).mp k.property))
  · rw [isometry_subtypeVal.tendsto_nhds_iff]
    simpa [Function.comp_def] using
      tendsto_of_mem_compactOperator_mul_of_eventually_norm_le hC hf_adj
        (mem_compactOperatorIdeal.mp
          ((TwoSidedIdeal.mem_toNonUnitalStarSubalgebra _).mp k.property))

/-- **Strict convergence on norm-bounded filters (Raeburn–Williams, Corollary 2.54).** Along any
norm-bounded filter `l` of adjointable operators `f i : L_A(E)`, `f i → T` strictly in
`𝓜ₛ(ℂ, K_A(E))` if and only if `f i x → T x` and `(f i).adjoint x → T.adjoint x` for all
`x : E`. -/
theorem tendsto_multiplierStrictStarAlgEquiv_iff_of_eventually_norm_le {ι : Type*} {l : Filter ι}
    {f : ι → AdjointableMap A E E} {T : AdjointableMap A E E} {C : ℝ}
    (hC : ∀ᶠ i in l, ‖f i‖ ≤ C) :
    Tendsto (fun i ↦ multiplierStrictStarAlgEquiv A E (f i)) l
        (𝓝 (multiplierStrictStarAlgEquiv A E T)) ↔
      (∀ x : E, Tendsto (fun i ↦ f i x) l (𝓝 (T x))) ∧
      (∀ x : E, Tendsto (fun i ↦ (f i).adjoint x) l (𝓝 (T.adjoint x))) :=
  ⟨fun h ↦ ⟨tendsto_apply_of_tendsto_multiplierStrictStarAlgEquiv h,
      tendsto_adjoint_apply_of_tendsto_multiplierStrictStarAlgEquiv h⟩,
    fun ⟨h₁, h₂⟩ ↦
      tendsto_multiplierStrictStarAlgEquiv_of_eventually_norm_le hC h₁ h₂⟩

/-- **Strict topology on norm-bounded sets.** On every bounded subset `s` of `L_A(E)`, the
topology induced from `𝓜ₛ(ℂ, K_A(E))` coincides with the strong-* topology induced by
`T ↦ (T, T.adjoint)` into `(E →Lₚₜ[ℂ] E) × (E →Lₚₜ[ℂ] E)`. -/
theorem induced_multiplierStrictStarAlgEquiv_eq_induced_pointwiseConvergenceCLM_of_isBounded
    {s : Set (AdjointableMap A E E)} (hs : Bornology.IsBounded s) :
    TopologicalSpace.induced (fun T : s ↦ multiplierStrictStarAlgEquiv A E T) inferInstance =
      TopologicalSpace.induced (fun T : s ↦
        (ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) E E
            (T : AdjointableMap A E E).toContinuousLinearMap,
          ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) E E
            (T : AdjointableMap A E E).adjoint.toContinuousLinearMap))
        inferInstance := by
  obtain ⟨C, hC⟩ := hs.subset_closedBall 0
  have hC' : ∀ T : s, ‖(T : AdjointableMap A E E)‖ ≤ C := fun T ↦ by
    simpa [Metric.mem_closedBall, dist_zero_right] using hC T.property
  let σ : s → 𝓜ₛ(ℂ, (compactOperatorIdeal A E).toNonUnitalStarSubalgebra) :=
    fun T ↦ multiplierStrictStarAlgEquiv A E T
  let τ : s → (E →Lₚₜ[ℂ] E) × (E →Lₚₜ[ℂ] E) := fun T ↦
    (ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) E E
        (T : AdjointableMap A E E).toContinuousLinearMap,
      ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) E E
        (T : AdjointableMap A E E).adjoint.toContinuousLinearMap)
  have hiff {l : Filter s} {T₀ : s} :
      Tendsto σ l (𝓝 (σ T₀)) ↔ Tendsto τ l (𝓝 (τ T₀)) := by
    rw [Prod.tendsto_iff, PointwiseConvergenceCLM.tendsto_iff_forall_tendsto,
      PointwiseConvergenceCLM.tendsto_iff_forall_tendsto]
    exact tendsto_multiplierStrictStarAlgEquiv_iff_of_eventually_norm_le
      (Eventually.of_forall fun T ↦ hC' T)
  have hcont_σ : @Continuous s _ (TopologicalSpace.induced τ inferInstance) _ σ :=
    @continuous_iff_continuousAt s _ (TopologicalSpace.induced τ inferInstance) _ σ |>.mpr
      fun T₁ ↦ hiff.mpr <|
        (@continuous_iff_continuousAt s _ (TopologicalSpace.induced τ inferInstance) _ τ).mp
          continuous_induced_dom T₁
  have hcont_τ : @Continuous s _ (TopologicalSpace.induced σ inferInstance) _ τ :=
    @continuous_iff_continuousAt s _ (TopologicalSpace.induced σ inferInstance) _ τ |>.mpr
      fun T₁ ↦ hiff.mp <|
        (@continuous_iff_continuousAt s _ (TopologicalSpace.induced σ inferInstance) _ σ).mp
          continuous_induced_dom T₁
  exact le_antisymm
    ((@continuous_iff_le_induced (t₁ := TopologicalSpace.induced σ inferInstance)
      (f := τ)).mp hcont_τ)
    ((@continuous_iff_le_induced (t₁ := TopologicalSpace.induced τ inferInstance)
      (f := σ)).mp hcont_σ)

/-- The module-compact operators `K_A(E)` are strictly dense in `L_A(E)` (via
`multiplierStrictStarAlgEquiv A E`). -/
theorem denseRange_multiplierStrictStarAlgEquiv_coe :
    DenseRange (fun k : (compactOperatorIdeal A E).toNonUnitalStarSubalgebra ↦
      multiplierStrictStarAlgEquiv A E (k : AdjointableMap A E E)) := by
  simpa only [coe_multiplierStrictStarAlgEquiv] using
    DoubleCentralizerStrict.denseRange_coe
      (A := (compactOperatorIdeal A E).toNonUnitalStarSubalgebra)

/-- Every closed operator-norm ball of radius `R` in `L_A(E)` is the strict closure of the closed
norm ball of radius `R` in `K_A(E)`. -/
theorem closure_multiplierStrictStarAlgEquiv_image_closedBall (R : ℝ) :
    closure ((fun k : (compactOperatorIdeal A E).toNonUnitalStarSubalgebra ↦
        multiplierStrictStarAlgEquiv A E (k : AdjointableMap A E E)) '' Metric.closedBall 0 R) =
      {m : 𝓜ₛ(ℂ, (compactOperatorIdeal A E).toNonUnitalStarSubalgebra) |
        ‖(multiplierStrictStarAlgEquiv A E).symm m‖ ≤ R} := by
  have himg : (fun k : (compactOperatorIdeal A E).toNonUnitalStarSubalgebra ↦
        multiplierStrictStarAlgEquiv A E (k : AdjointableMap A E E)) '' Metric.closedBall 0 R =
      (DoubleCentralizerStrict.coe ℂ :
          (compactOperatorIdeal A E).toNonUnitalStarSubalgebra →
            𝓜ₛ(ℂ, (compactOperatorIdeal A E).toNonUnitalStarSubalgebra)) ''
        Metric.closedBall 0 R := by
    ext m
    simp only [Set.mem_image, coe_multiplierStrictStarAlgEquiv]
  have hset :
      {m : 𝓜ₛ(ℂ, (compactOperatorIdeal A E).toNonUnitalStarSubalgebra) |
        ‖m.toDoubleCentralizer‖ ≤ R} =
      {m : 𝓜ₛ(ℂ, (compactOperatorIdeal A E).toNonUnitalStarSubalgebra) |
        ‖(multiplierStrictStarAlgEquiv A E).symm m‖ ≤ R} := by
    ext m
    simp only [Set.mem_ofPred_eq]
    rw [← norm_multiplierStarAlgEquiv, ← toDoubleCentralizer_multiplierStrictStarAlgEquiv,
      StarAlgEquiv.apply_symm_apply]
  rw [himg, ← hset]
  exact DoubleCentralizerStrict.closure_image_closedBall R

/-- Along any approximate unit `l` of `K_A(E)`, `T * e → T` strictly for every `T : L_A(E)`. -/
theorem tendsto_multiplierStrictStarAlgEquiv_mul_compactOperatorIdeal_of_isApproximateUnit
    {l : Filter (compactOperatorIdeal A E).toNonUnitalStarSubalgebra} (hl : l.IsApproximateUnit)
    (T : AdjointableMap A E E) :
    Tendsto (fun e : (compactOperatorIdeal A E).toNonUnitalStarSubalgebra ↦
        multiplierStrictStarAlgEquiv A E (T * (e : AdjointableMap A E E))) l
      (𝓝 (multiplierStrictStarAlgEquiv A E T)) := by
  have heq : (fun e : (compactOperatorIdeal A E).toNonUnitalStarSubalgebra ↦
        multiplierStrictStarAlgEquiv A E (T * (e : AdjointableMap A E E))) =
      fun e ↦ ((multiplierStrictStarAlgEquiv A E T).toDoubleCentralizer.fst e :
        𝓜ₛ(ℂ, (compactOperatorIdeal A E).toNonUnitalStarSubalgebra)) := by
    funext e
    rw [toDoubleCentralizer_multiplierStrictStarAlgEquiv, ← coe_multiplierStarAlgEquiv_fst T e,
      coe_multiplierStrictStarAlgEquiv]
  rw [heq]
  exact DoubleCentralizerStrict.tendsto_coe_fst_of_isApproximateUnit hl
    (multiplierStrictStarAlgEquiv A E T)

end Complete

end StrictTopology

end AdjointableMap

end TauCeti
