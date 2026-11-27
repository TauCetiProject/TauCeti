/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Basis.Flag
public import Mathlib.LinearAlgebra.Charpoly.Basic
public import Mathlib.LinearAlgebra.Eigenspace.Basic

import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.LinearAlgebra.Eigenspace.Charpoly
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import TauCeti.LinearAlgebra.Basis.Triangular
import TauCeti.LinearAlgebra.Charpoly.Quotient

/-!
# Schur triangularization

Let `T` be an endomorphism of a finite-dimensional vector space `E` over a field `K`. A family
`v : Fin k → E` *triangularizes* `T` with diagonal `α : Fin k → K` when `T (v j) - α j • v j` lies
in the span of the earlier vectors `v i`, `i < j`, for every `j`. For a basis `b` this is the
hypothesis `T (b j) - α j • b j ∈ b.flag j.castSucc` of
`Module.Basis.linearMap_toMatrix_isUpperTriangular_of_sub_smul_mem_flag` and
`Module.Basis.linearMap_toMatrix_apply_self_of_sub_smul_mem_flag`: the matrix of `T` in `b` is
upper triangular with diagonal `α`.

Every tuple of roots of the characteristic polynomial of `T`, counted with multiplicity and taken
in any order, is the diagonal of a linearly independent family triangularizing `T`. Its span is an
invariant subspace on which `T` has exactly these eigenvalues. This is Schur's triangularization
theorem, in its invariant-subspace form. Nothing is assumed of `K`: the roots are given, and the
characteristic polynomial of `T` need not split.

## Main results

* `LinearMap.exists_linearIndependent_apply_sub_smul_mem_span`: every tuple `α : Fin k → K` with
  `Multiset.map α univ.val ≤ T.charpoly.roots` is the diagonal of a linearly independent family
  triangularizing `T`.
* `LinearMap.exists_basis_apply_sub_smul_mem_flag`: if moreover `k = finrank K E`, the family is
  a basis. Over `ℂ`, every enumeration of the eigenvalues of `T` is thus the diagonal of an upper
  triangular matrix of `T`.
* `LinearMap.exists_invariant_finrank_eq_roots_charpoly_restrict`: **Schur triangularization,
  invariant form.** Every sub-multiset `s` of the roots of `T.charpoly` is the multiset of roots
  of the characteristic polynomial of the restriction of `T` to an invariant subspace of dimension
  `card s`.

## Implementation notes

The family is built by induction on its length. An eigenvector `y` for the first entry of `α`
comes first, and the remaining vectors are lifts of a family triangularizing the endomorphism
induced on `E ⧸ K ∙ y`, whose characteristic polynomial is that of `T` divided by `X - C (α 0)`
(`LinearMap.charpoly_eq_X_sub_C_mul_charpoly_mapQ`).

## References

* R. A. Horn and C. R. Johnson, *Matrix Analysis*, Cambridge University Press (1985),
  Theorem 2.3.1, p. 79.
-/

public section

open Module Polynomial Submodule

namespace LinearMap

section Field

variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E] [FiniteDimensional K E]

/-- **Schur triangularization of a family.** If the entries of `α : Fin k → K` are roots of the
characteristic polynomial of `T`, with multiplicity, there is a linearly independent family
`v : Fin k → E` such that `T (v j) - α j • v j` lies in the span of the `v i` with `i < j` for
every `j`. -/
theorem exists_linearIndependent_apply_sub_smul_mem_span (T : E →ₗ[K] E) {k : ℕ} {α : Fin k → K}
    (hα : Multiset.map α Finset.univ.val ≤ T.charpoly.roots) :
    ∃ v : Fin k → E, LinearIndependent K v ∧
      ∀ j, T (v j) - α j • v j ∈ span K (v '' Set.Iio j) := by
  induction k generalizing E with
  | zero => exact ⟨Fin.elim0, linearIndependent_empty_type, fun j ↦ j.elim0⟩
  | succ k ih =>
    have hcons : Multiset.map α Finset.univ.val =
        α 0 ::ₘ Multiset.map (fun i : Fin k ↦ α i.succ) Finset.univ.val := by
      simp [Fin.univ_val_map, List.ofFn_succ]
    obtain ⟨y, hy⟩ := ((Module.End.hasEigenvalue_iff_isRoot_charpoly T (α 0)).2
      (isRoot_of_mem_roots (Multiset.mem_of_le hα (hcons ▸ Multiset.mem_cons_self _ _)))
      ).exists_hasEigenvector
    have hL : (K ∙ y) ≤ (K ∙ y).comap T := by
      rw [span_singleton_le_iff_mem, mem_comap, hy.apply_eq_smul]
      exact smul_mem _ _ (mem_span_singleton_self y)
    have hroots : T.charpoly.roots = α 0 ::ₘ ((K ∙ y).mapQ (K ∙ y) T hL).charpoly.roots := by
      rw [charpoly_eq_X_sub_C_mul_charpoly_mapQ hy hL, roots_mul, roots_X_sub_C,
        Multiset.singleton_add]
      exact mul_ne_zero (X_sub_C_ne_zero _) (charpoly_monic _).ne_zero
    obtain ⟨c, hc, hcT⟩ := ih ((K ∙ y).mapQ (K ∙ y) T hL) (α := fun i ↦ α i.succ)
      (by rwa [hcons, hroots, Multiset.cons_le_cons_iff] at hα)
    choose w hw using fun i ↦ (K ∙ y).mkQ_surjective (c i)
    have hwc : (K ∙ y).mkQ ∘ w = c := funext hw
    refine ⟨Fin.cons y w, linearIndependent_finCons.2 ⟨.of_comp (K ∙ y).mkQ (hwc ▸ hc), ?_⟩, ?_⟩
    · intro hmem
      obtain ⟨a, ha⟩ := (mem_span_range_iff_exists_fun K).1 hmem
      have h0 : ∑ i, a i • c i = 0 := by
        have := congrArg (K ∙ y).mkQ ha
        simpa [← hw, (Submodule.Quotient.mk_eq_zero _).2 (mem_span_singleton_self y)] using this
      have := Fintype.linearIndependent_iff.1 hc a h0
      exact hy.2 (by simp [← ha, this])
    · intro j
      cases j using Fin.cases with
      | zero => simp [hy.apply_eq_smul]
      | succ j =>
        simp only [Fin.cons_succ]
        have h1 : (K ∙ y).mkQ (T (w j) - α j.succ • w j) ∈
            (span K (w '' Set.Iio j)).map (K ∙ y).mkQ := by
          rw [map_span, ← Set.image_comp, hwc]
          simpa [← hw] using hcT j
        rw [← mem_comap, comap_map_mkQ] at h1
        have hle : (K ∙ y) ⊔ span K (w '' Set.Iio j) ≤
            span K (Fin.cons y w '' Set.Iio j.succ) := by
          refine sup_le ?_ (span_mono ?_)
          · rw [span_singleton_le_iff_mem]
            exact subset_span ⟨0, Fin.succ_pos j, rfl⟩
          · rintro _ ⟨i, hi, rfl⟩
            exact ⟨i.succ, Fin.succ_lt_succ_iff.2 hi, Fin.cons_succ _ _ _⟩
        exact hle h1

/-- **Schur triangularization.** If `finrank K E = n` and the entries of `α : Fin n → K` are
roots of the characteristic polynomial of `T`, with multiplicity, there is a basis `b` of `E`
such that `T (b j) - α j • b j` lies in the span `b.flag j.castSucc` of the `b i` with `i < j`
for every `j`. The matrix of `T` in `b` is then upper triangular with diagonal `α`
(`Module.Basis.linearMap_toMatrix_isUpperTriangular_of_sub_smul_mem_flag`,
`Module.Basis.linearMap_toMatrix_apply_self_of_sub_smul_mem_flag`). -/
theorem exists_basis_apply_sub_smul_mem_flag (T : E →ₗ[K] E) {n : ℕ} (hn : finrank K E = n)
    {α : Fin n → K} (hα : Multiset.map α Finset.univ.val ≤ T.charpoly.roots) :
    ∃ b : Basis (Fin n) K E, ∀ j, T (b j) - α j • b j ∈ b.flag j.castSucc := by
  obtain ⟨v, hv, hvT⟩ := T.exists_linearIndependent_apply_sub_smul_mem_span hα
  refine ⟨basisOfLinearIndependentOfCardEqFinrank' v hv (by simp [hn]), fun j ↦ ?_⟩
  simp only [coe_basisOfLinearIndependentOfCardEqFinrank', Basis.flag,
    Fin.castSucc_lt_castSucc_iff]
  exact hvT j

/-- **Schur triangularization, invariant form.** Every sub-multiset `s` of the roots of the
characteristic polynomial of `T` is the multiset of roots of the characteristic polynomial of the
restriction of `T` to some invariant subspace of dimension `card s`. -/
theorem exists_invariant_finrank_eq_roots_charpoly_restrict (T : E →ₗ[K] E) {s : Multiset K}
    (hs : s ≤ T.charpoly.roots) :
    ∃ (V : Submodule K E) (hV : ∀ x ∈ V, T x ∈ V),
      finrank K V = Multiset.card s ∧ (T.restrict hV).charpoly.roots = s := by
  set α : Fin s.toList.length → K := s.toList.get
  have hα : Multiset.map α Finset.univ.val = s := by
    rw [Fin.univ_val_map, List.ofFn_get, Multiset.coe_toList]
  obtain ⟨v, hv, hvT⟩ := T.exists_linearIndependent_apply_sub_smul_mem_span (hα ▸ hs)
  have hV : ∀ x ∈ span K (Set.range v), T x ∈ span K (Set.range v) := by
    refine fun x hx ↦ (span_le (p := (span K (Set.range v)).comap T).2 ?_ hx)
    rintro _ ⟨j, rfl⟩
    have := add_mem (span_mono (Set.image_subset_range _ _) (hvT j))
      (smul_mem _ (α j) (subset_span ⟨j, rfl⟩))
    simpa using this
  refine ⟨span K (Set.range v), hV, by simp [finrank_span_eq_card hv], ?_⟩
  have hb : ∀ j, T.restrict hV (Basis.span hv j) - α j • Basis.span hv j ∈
      (Basis.span hv).flag j.castSucc := by
    intro j
    rw [Basis.flag, ← Submodule.apply_mem_span_image_iff_mem_span
      (span K (Set.range v)).injective_subtype, ← Set.image_comp]
    simp only [Function.comp_def, Basis.span_apply, Fin.castSucc_lt_castSucc_iff,
      Submodule.subtype_apply, map_sub, map_smul, coe_restrict_apply]
    exact hvT j
  have hmap : Multiset.map (fun j ↦ X - C (α j)) Finset.univ.val =
      (Multiset.map α Finset.univ.val).map (fun a ↦ X - C a) :=
    (Multiset.map_map (fun a ↦ X - C a) α _).symm
  rw [(Basis.span hv).linearMap_charpoly_eq_prod_of_sub_smul_mem_flag hb,
    Finset.prod_eq_multiset_prod, hmap, roots_multiset_prod_X_sub_C, hα]

end Field

end LinearMap
