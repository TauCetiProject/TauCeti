/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.CompletelyPositiveMap.Nuclear
public import TauCeti.Analysis.CStarAlgebra.CompletelyPositiveMap.Commutative
public import Mathlib.Topology.UnitInterval
import Mathlib.Analysis.CStarAlgebra.Hom
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
`C(X, ℂ) → M_t(ℂ)`, and `β M = Σ_k M_kk g_k` is a positive map into a commutative C⋆-algebra,
hence completely positive, with `β 1 = Σ_k g_k = 1`. Then `β (α f) = Σ_k f(x_k) g_k` is within
`ε / 2` of `f` for `f ∈ F`, and `β ∘ α` factors through the nuclear algebra `M_t(ℂ)`.

Through the Gelfand transform every commutative unital C⋆-algebra is nuclear
(`TauCeti.CStarAlgebra.isNuclear_of_commCStarAlgebra`). In particular the identity of `C[0,1]`
is a nuclear completely positive map, the first `C[0,1]` Check of the roadmap
(`TauCeti.CStarAlgebra.isNuclear_unitInterval`).

## Main declarations

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

/-- The diagonal evaluation `f ↦ diag(f(x_k))` at finitely many points, as a star homomorphism
`C(X, ℂ) → M_t(ℂ)`. -/
private noncomputable def diagEval {Y : Type*} [TopologicalSpace Y] [DecidableEq Y]
    (t : Finset Y) : C(Y, ℂ) →⋆ₙₐ[ℂ] CStarMatrix t t ℂ where
  toFun f := CStarMatrix.ofMatrix (Matrix.diagonal fun k : t ↦ f k)
  map_smul' c f := by
    ext i j
    by_cases h : i = j <;> simp [h]
  map_zero' := by
    ext i j
    simp
  map_add' f f' := by
    ext i j
    by_cases h : i = j <;> simp [h]
  map_mul' f f' := by
    ext i j
    by_cases h : i = j <;> simp [CStarMatrix.mul_apply, Matrix.diagonal_apply, h]
  map_star' f := by
    ext i j
    by_cases h : i = j <;> simp [CStarMatrix.star_apply, h, eq_comm]

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
  have hsum (y : X) : ∑ k, (ρ k y : ℂ) = 1 := by
    have h := ρ.sum_eq_one (Set.mem_univ y)
    rw [finsum_eq_sum_of_fintype] at h
    exact_mod_cast h
  -- The evaluation `α` and the partition-of-unity map `β`.
  let α : C(X, ℂ) →CP CStarMatrix t t ℂ :=
    CompletelyPositiveMapClass.toCompletelyPositiveLinearMap (diagEval t)
  have hα (f : C(X, ℂ)) : ‖α f‖ ≤ ‖f‖ := NonUnitalStarAlgHom.norm_apply_le (diagEval t) f
  let βₗ : CStarMatrix t t ℂ →ₗ[ℂ] C(X, ℂ) :=
    { toFun := fun M ↦ ∑ k, M k k • g k
      map_add' := fun M N ↦ by simp [add_smul, Finset.sum_add_distrib]
      map_smul' := fun c M ↦ by simp [Finset.smul_sum, smul_smul] }
  have hβₗ (M : CStarMatrix t t ℂ) : βₗ M = ∑ k, M k k • g k := rfl
  let β : CStarMatrix t t ℂ →CP C(X, ℂ) :=
    (PositiveLinearMap.mk₀ βₗ fun M hM ↦ by
      rw [hβₗ]
      refine Finset.sum_nonneg fun k _ ↦ ?_
      rw [ContinuousMap.le_def]
      intro y
      simp only [ContinuousMap.zero_apply, ContinuousMap.smul_apply, hg, smul_eq_mul]
      exact mul_nonneg (CStarMatrix.diag_nonneg_of_nonneg hM k)
        (Complex.zero_le_real.2 (ρ.nonneg k y))).toCompletelyPositiveMapOfCommCodomain
  have hβ_apply (M : CStarMatrix t t ℂ) : β M = ∑ k, M k k • g k :=
    congrFun (PositiveLinearMap.coe_toCompletelyPositiveMapOfCommCodomain _) M
  have hβ : ∀ M, ‖β M‖ ≤ ‖M‖ := by
    refine (CompletelyPositiveMapClass.norm_map_one_le_one_iff β).1 ?_
    have h1 : β 1 = 1 := by
      ext y
      simpa [hβ_apply, hg] using hsum y
    rw [h1]
    exact CStarRing.norm_one_le
  refine ⟨β.comp α, ?_, fun f hf ↦ ?_⟩
  · simpa using
      ((isNuclear_cstarMatrix t).isNuclearContraction_id.comp_right α hα).comp_left β hβ
  · refine lt_of_le_of_lt ((ContinuousMap.norm_le _ (half_pos hε).le).2 fun y ↦ ?_)
      (half_lt_self hε)
    have hαf : β (α f) = ∑ k : t, f k • g k := by
      rw [hβ_apply]
      refine Finset.sum_congr rfl fun k _ ↦ ?_
      simp [α, diagEval]
    rw [CompletelyPositiveMap.comp_apply, hαf]
    simp only [ContinuousMap.sub_apply, ContinuousMap.coe_sum, Finset.sum_apply,
      ContinuousMap.smul_apply, hg, smul_eq_mul, CompletelyPositiveMap.id_apply]
    calc ‖∑ k : t, f k * (ρ k y : ℂ) - f y‖
        = ‖∑ k : t, (ρ k y : ℂ) * (f k - f y)‖ := by
          rw [Finset.sum_congr rfl fun k _ ↦ mul_sub (ρ k y : ℂ) _ _, Finset.sum_sub_distrib,
            ← Finset.sum_mul, hsum, one_mul]
          simp only [mul_comm]
      _ ≤ ∑ k : t, ρ k y * (ε / 2) := by
          refine (norm_sum_le _ _).trans <| Finset.sum_le_sum fun k _ ↦ ?_
          rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (ρ.nonneg k y)]
          by_cases h : ρ k y = 0
          · simp [h]
          refine mul_le_mul_of_nonneg_left ?_ (ρ.nonneg k y)
          have hy : y ∈ U k := hρ k (subset_tsupport _ h)
          rw [norm_sub_rev]
          exact (Set.mem_iInter₂.1 hy f hf).le
      _ = ε / 2 := by
          rw [← Finset.sum_mul, show ∑ k : t, ρ k y = 1 by exact_mod_cast hsum y, one_mul]

/-- **Commutative unital C⋆-algebras are nuclear**, through the Gelfand transform
`A ≃⋆ₐ C(X, ℂ)` onto the continuous functions on the character space. -/
theorem isNuclear_of_commCStarAlgebra (A : Type*) [CommCStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] : IsNuclear A :=
  .of_starAlgEquiv (gelfandStarTransform A)

/-- **Check**: the identity of `C[0,1]` is a nuclear completely positive map. -/
theorem isNuclear_unitInterval : IsNuclear C(unitInterval, ℂ) :=
  inferInstance

end TauCeti.CStarAlgebra
