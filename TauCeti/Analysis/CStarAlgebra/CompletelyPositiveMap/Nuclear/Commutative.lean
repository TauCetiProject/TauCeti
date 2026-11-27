/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.CompletelyPositiveMap.Nuclear
public import TauCeti.Analysis.CStarAlgebra.CompletelyPositiveMap.Commutative
import Mathlib.Analysis.Convex.PartitionOfUnity
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.RCLike.ContinuousMap
import Mathlib.Topology.PartitionOfUnity
import Mathlib.Topology.ContinuousMap.StarOrdered
import TauCeti.Analysis.CStarAlgebra.Basic
import TauCeti.Analysis.CStarAlgebra.CStarMatrix

/-!
# Commutative C⋆-algebras are nuclear

For a compact Hausdorff space `X`, the identity of `C(X, ℂ)` is a nuclear completely positive
contraction (`TauCeti.CStarAlgebra.isNuclear_continuousMap`). Given finitely many functions `F`
and `ε > 0`, cover `X` by finitely many open sets `U_k`, `k ∈ t`, on each of which every `f ∈ F`
varies by less than `ε / 2` around its value at a point `x_k`, and take a partition of unity
`g_k` subordinate to the cover. The evaluation `α f = diag(f(x_k))` is a star homomorphism
`C(X, ℂ) → M_t(ℂ)`, and `β M = Σ_k M_kk g_k` (`TauCeti.CStarAlgebra.diagSumSMul`) is a positive
map into a commutative C⋆-algebra, hence completely positive, with `β 1 = Σ_k g_k = 1`. Then
`β (α f) = Σ_k f(x_k) g_k` is within `ε / 2` of `f` for `f ∈ F`, and `β ∘ α` factors through the
nuclear algebra `M_t(ℂ)`.

Through the Gelfand transform every commutative unital C⋆-algebra is nuclear
(`TauCeti.CStarAlgebra.isNuclear_of_commCStarAlgebra`). In particular the identity of `C[0,1]`
is a nuclear completely positive map.

## Main declarations

* `TauCeti.CStarAlgebra.diagSumSMul`: for positive `b_k` in a commutative C⋆-algebra, the
  completely positive map `M ↦ Σ_k M_kk • b_k` on `M_ι(ℂ)`, with
  `TauCeti.CStarAlgebra.norm_diagSumSMul_apply_le`: it is contractive when `Σ_k b_k = 1`.
* `TauCeti.CStarAlgebra.isNuclear_continuousMap`: `C(X, ℂ)` is nuclear for compact Hausdorff
  `X`.
* `TauCeti.CStarAlgebra.isNuclear_of_commCStarAlgebra`: commutative unital C⋆-algebras are
  nuclear.

## References

* B. Blackadar, *Operator Algebras: Theory of C⋆-Algebras and von Neumann Algebras*,
  Encyclopaedia of Mathematical Sciences 122, Springer (2006), IV.3.1.4 and II.9.4.4.
-/

public section

open scoped CStarAlgebra ComplexOrder

namespace TauCeti.CStarAlgebra

open CompletelyPositiveMap

section DiagSumSMul

variable {ι B : Type*} [Fintype ι]

/-- For positive `b : ι → B` in a commutative C⋆-algebra, the completely positive map
`M ↦ Σ_k M_kk • b_k` from `M_ι(ℂ)` to `B`. It is positive because the diagonal entries of a
positive matrix are positive, and so completely positive since `B` is commutative. -/
noncomputable def diagSumSMul [NonUnitalCommCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
    (b : ι → B) (hb : ∀ k, 0 ≤ b k) : CStarMatrix ι ι ℂ →CP B :=
  PositiveLinearMap.toCompletelyPositiveMapOfCommCodomain <| .mk₀
    { toFun := fun M ↦ ∑ k, M k k • b k
      map_add' := fun M N ↦ by simp [add_smul, Finset.sum_add_distrib]
      map_smul' := fun c M ↦ by simp [Finset.smul_sum, smul_smul] }
    fun M hM ↦ Finset.sum_nonneg fun k _ ↦
      smul_nonneg (CStarMatrix.diag_nonneg_of_nonneg hM k) (hb k)

@[simp]
theorem diagSumSMul_apply [NonUnitalCommCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
    (b : ι → B) (hb : ∀ k, 0 ≤ b k) (M : CStarMatrix ι ι ℂ) :
    diagSumSMul b hb M = ∑ k, M k k • b k :=
  congrFun (PositiveLinearMap.coe_toCompletelyPositiveMapOfCommCodomain _) M

/-- If the positive `b_k` sum to `1`, the map `M ↦ Σ_k M_kk • b_k` is unital, hence
contractive. -/
theorem norm_diagSumSMul_apply_le [CommCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
    (b : ι → B) (hb : ∀ k, 0 ≤ b k) (hsum : ∑ k, b k = 1) (M : CStarMatrix ι ι ℂ) :
    ‖diagSumSMul b hb M‖ ≤ ‖M‖ := by
  classical
  refine (CompletelyPositiveMapClass.norm_map_one_le_one_iff _).1 ?_ M
  have h1 : diagSumSMul b hb 1 = 1 := by
    simp [hsum]
  rw [h1]
  exact CStarRing.norm_one_le

end DiagSumSMul

variable (X : Type*) [TopologicalSpace X] [CompactSpace X] [T2Space X]

/-- **`C(X, ℂ)` is nuclear** for every compact Hausdorff space `X`. -/
instance isNuclear_continuousMap : IsNuclear C(X, ℂ) := by
  classical
  refine ⟨IsNuclearContraction.of_forall_exists fun F ε hε ↦ ?_⟩
  let U : X → Set X := fun x ↦ ⋂ f ∈ F, {y | ‖f y - f x‖ < ε / 2}
  have hUo (x : X) : IsOpen (U x) :=
    isOpen_biInter_finset fun f _ ↦ isOpen_lt (by fun_prop) continuous_const
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover U hUo fun x _ ↦
    Set.mem_iUnion.2 ⟨x, Set.mem_iInter₂.2 fun f _ ↦ by simpa using half_pos hε⟩
  obtain ⟨ρ, hρ⟩ := PartitionOfUnity.exists_isSubordinate isClosed_univ (fun k : t ↦ U k)
    (fun k ↦ hUo k) fun y _ ↦ by
      obtain ⟨x, hx, hyx⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ y))
      exact Set.mem_iUnion.mpr ⟨⟨x, hx⟩, hyx⟩
  let g : t → C(X, ℂ) := fun k ↦ (ρ k).realToRCLike ℂ
  have hg (k : t) (y : X) : g k y = (ρ k y : ℂ) := by
    simp [g, ContinuousMap.realToRCLike_apply]
  have hg0 (k : t) : 0 ≤ g k := fun y ↦ by
    simpa [hg] using ρ.nonneg k y
  have hsum : ∑ k, g k = 1 := by
    ext y
    have h := ρ.sum_eq_one (Set.mem_univ y)
    rw [finsum_eq_sum_of_fintype] at h
    simpa [hg] using congrArg ((↑) : ℝ → ℂ) h
  -- The evaluation `α` at the points of `t` and the partition-of-unity map `β`.
  let e : C(X, ℂ) →⋆ₐ[ℂ] CStarMatrix t t ℂ := (CStarMatrix.diagonalStarAlgHom ℂ t ℂ).comp
    ⟨AlgHom.pi fun k : t ↦ ContinuousMap.evalAlgHom ℂ ℂ (k : X), fun _ ↦ by ext; simp⟩
  let α : C(X, ℂ) →CP CStarMatrix t t ℂ :=
    CompletelyPositiveMapClass.toCompletelyPositiveLinearMap e
  have hα (f : C(X, ℂ)) : ‖α f‖ ≤ ‖f‖ := NonUnitalStarAlgHom.norm_apply_le e f
  have he (f : C(X, ℂ)) (k : t) : α f k k = f k := by
    simp [α, e]
  let β := diagSumSMul g hg0
  refine ⟨β.comp α, ?_, fun f hf ↦ ?_⟩
  · simpa using ((isNuclear_cstarMatrix t).isNuclearContraction_id.comp_right α hα).comp_left β
      (norm_diagSumSMul_apply_le g hg0 hsum)
  · refine lt_of_le_of_lt ((ContinuousMap.norm_le _ (half_pos hε).le).2 fun y ↦ ?_)
      (half_lt_self hε)
    -- `β (α f) y = Σ_k ρ_k(y) f(x_k)` is a convex combination of values within `ε / 2` of `f y`.
    have hy : ∑ᶠ k, ρ k y • f k ∈ Metric.closedBall (f y) (ε / 2) := by
      refine ρ.finsum_smul_mem_convex (g := fun k _ ↦ f k) (Set.mem_univ y) (fun k hk ↦ ?_)
        (convex_closedBall _ _)
      rw [Metric.mem_closedBall, dist_eq_norm, norm_sub_rev]
      exact (Set.mem_iInter₂.1 (hρ k (subset_tsupport _ hk)) f hf).le
    rw [Metric.mem_closedBall, dist_eq_norm, finsum_eq_sum_of_fintype] at hy
    simpa [β, he, hg, Complex.real_smul, mul_comm] using hy

/-- **Commutative unital C⋆-algebras are nuclear**, through the Gelfand transform
`A ≃⋆ₐ C(X, ℂ)` onto the continuous functions on the character space. -/
instance isNuclear_of_commCStarAlgebra (A : Type*) [CommCStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] : IsNuclear A :=
  .of_starAlgEquiv (gelfandStarTransform A)

end TauCeti.CStarAlgebra
