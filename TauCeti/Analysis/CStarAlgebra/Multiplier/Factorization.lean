/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Multiplier.Nondegenerate
import TauCeti.Analysis.CStarAlgebra.CohenFactorization

/-!
# Cohen–Hewitt factorization for multiplier homomorphisms

Applies `TauCeti.Analysis.CStarAlgebra.CohenFactorization` to `φ : A →⋆ₙₐ[ℂ] 𝓜(ℂ, B)`: the closed
linear spans of `(φ a).fst b` and `(φ a).snd b` already equal `⋃ a, Set.range (φ a).fst` and
`⋃ a, Set.range (φ a).snd` (`coe_topologicalClosure_span_range_fst_eq`,
`coe_topologicalClosure_span_range_snd_eq`). Hence `φ` is nondegenerate iff `B = φ(A)B`
(`isMultiplierNondegenerate_iff_iUnion_range_fst_eq_univ`) iff `B = B φ(A)`
(`isMultiplierNondegenerate_iff_iUnion_range_snd_eq_univ`), with norm-`≤ 1`, `ε`-close
factorizations on both sides (`IsMultiplierNondegenerate.exists_fst_apply_eq_of_pos`,
`exists_snd_apply_eq_of_pos`).

## References

* E. C. Lance, *Hilbert C\*-Modules*, LMS Lecture Note Series 210, Propositions 1.8 and 2.5.
* Iain Raeburn and Dana Williams, *Morita Equivalence and Continuous-Trace C\*-Algebras*,
  Propositions 2.31 and 2.50.
-/

public section
noncomputable section

open scoped MultiplierAlgebra

namespace NonUnitalStarAlgHom

variable {A B : Type*} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]

private def fstActionCLM (φ : A →⋆ₙₐ[ℂ] 𝓜(ℂ, B)) : A →L[ℂ] B →L[ℂ] B :=
  LinearMap.mkContinuous ⟨⟨fun a => (φ a).fst, fun a b => by simp⟩, fun c a => by simp⟩ 1
    fun a => by simpa using (φ a).norm_fst_le.trans (norm_apply_le φ a)

/-- By Cohen–Hewitt factorization, for any `φ : A →⋆ₙₐ[ℂ] 𝓜(ℂ, B)` the closed linear span of the
elements `(φ a).fst b` already equals the bare set of products `⋃ a, Set.range (φ a).fst`. -/
theorem coe_topologicalClosure_span_range_fst_eq (φ : A →⋆ₙₐ[ℂ] 𝓜(ℂ, B)) :
    ((Submodule.span ℂ (⋃ a, Set.range (φ a).fst)).topologicalClosure : Set B) =
      ⋃ a, Set.range (φ a).fst :=
  (fstActionCLM φ).coe_topologicalClosure_span_iUnion_range_eq fun a b z => by
    simp [fstActionCLM, mul_apply_eq_comp]

/-- By Cohen–Hewitt factorization, for any `φ : A →⋆ₙₐ[ℂ] 𝓜(ℂ, B)` the closed linear span of the
elements `(φ a).snd b` already equals the bare set of products `⋃ a, Set.range (φ a).snd`. -/
theorem coe_topologicalClosure_span_range_snd_eq (φ : A →⋆ₙₐ[ℂ] 𝓜(ℂ, B)) :
    ((Submodule.span ℂ (⋃ a, Set.range (φ a).snd)).topologicalClosure : Set B) =
      ⋃ a, Set.range (φ a).snd := by
  refine Set.Subset.antisymm (fun b hb => ?_) fun b hb =>
    Submodule.le_topologicalClosure _ (Submodule.subset_span hb)
  set S := (Submodule.span ℂ (⋃ a, Set.range (φ a).fst)).topologicalClosure
  have hstar : star b ∈ S := by
    rw [Submodule.topologicalClosure_coe] at hb
    rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe]
    refine (isClosed_closure.preimage continuous_star).closure_subset_iff.2
      (Submodule.span_le (p := S.comap (starₗᵢ ℂ : B ≃ₗᵢ⋆[ℂ] B).toLinearMap).2 fun z hz => ?_) hb
    obtain ⟨a, y, rfl⟩ := Set.mem_iUnion.1 hz
    exact Submodule.le_topologicalClosure _ <|
      Submodule.subset_span <| Set.mem_iUnion.2 ⟨star a, star y, by simp [map_star]⟩
  rw [← SetLike.mem_coe, φ.coe_topologicalClosure_span_range_fst_eq] at hstar
  obtain ⟨a, y, hay⟩ := Set.mem_iUnion.1 hstar
  exact Set.mem_iUnion.2 ⟨star a, star y, by simpa [map_star] using congrArg star hay⟩

/-- A multiplier homomorphism `φ : A →⋆ₙₐ[ℂ] 𝓜(ℂ, B)` is nondegenerate if and only if every element
of `B` is of the form `(φ a).fst y` (`B = φ(A)B`). -/
theorem isMultiplierNondegenerate_iff_iUnion_range_fst_eq_univ {φ : A →⋆ₙₐ[ℂ] 𝓜(ℂ, B)} :
    φ.IsMultiplierNondegenerate ↔ (⋃ a, Set.range (φ a).fst) = Set.univ := by
  rw [isMultiplierNondegenerate_iff_dense, Submodule.dense_iff_topologicalClosure_eq_top,
    ← SetLike.coe_set_eq, φ.coe_topologicalClosure_span_range_fst_eq, Submodule.top_coe]

/-- A multiplier homomorphism `φ : A →⋆ₙₐ[ℂ] 𝓜(ℂ, B)` is nondegenerate if and only if every element
of `B` is of the form `(φ a).snd y` (`B = B φ(A)`). -/
theorem isMultiplierNondegenerate_iff_iUnion_range_snd_eq_univ {φ : A →⋆ₙₐ[ℂ] 𝓜(ℂ, B)} :
    φ.IsMultiplierNondegenerate ↔ (⋃ a, Set.range (φ a).snd) = Set.univ := by
  rw [isMultiplierNondegenerate_iff_dense_snd, Submodule.dense_iff_topologicalClosure_eq_top,
    ← SetLike.coe_set_eq, φ.coe_topologicalClosure_span_range_snd_eq, Submodule.top_coe]

/-- **Cohen–Hewitt factorization for nondegenerate multiplier homomorphisms (left form).** Every
`b : B` factors as `b = (φ a).fst y` with `‖a‖ ≤ 1` and `y` arbitrarily close to `b`. -/
theorem IsMultiplierNondegenerate.exists_fst_apply_eq_of_pos {φ : A →⋆ₙₐ[ℂ] 𝓜(ℂ, B)}
    (hφ : φ.IsMultiplierNondegenerate) (b : B) {ε : ℝ} (hε : 0 < ε) :
    ∃ a y, ‖a‖ ≤ 1 ∧ ‖y - b‖ < ε ∧ (φ a).fst y = b := by
  have htop : (Submodule.span ℂ (⋃ a, Set.range (fstActionCLM φ a))).topologicalClosure = ⊤ := by
    simpa [fstActionCLM] using
      Submodule.dense_iff_topologicalClosure_eq_top.mp (isMultiplierNondegenerate_iff_dense.mp hφ)
  obtain ⟨a, y, ha, -, hy, hfac⟩ :=
    (fstActionCLM φ).exists_apply_eq_of_mem_topologicalClosure_span_iUnion
      (fun x y z => by simp [fstActionCLM, mul_apply_eq_comp]) (htop.symm ▸ Submodule.mem_top) hε
  exact ⟨a, y, ha, hy, hfac⟩

/-- Every `b : B` factors as `b = (φ a).fst y` when `φ : A →⋆ₙₐ[ℂ] 𝓜(ℂ, B)` is nondegenerate. -/
theorem IsMultiplierNondegenerate.exists_fst_apply_eq {φ : A →⋆ₙₐ[ℂ] 𝓜(ℂ, B)}
    (hφ : φ.IsMultiplierNondegenerate) (b : B) : ∃ a y, (φ a).fst y = b :=
  let ⟨a, y, _, _, h⟩ := hφ.exists_fst_apply_eq_of_pos b one_pos; ⟨a, y, h⟩

/-- **Cohen–Hewitt factorization for nondegenerate multiplier homomorphisms (right form).** Every
`b : B` factors as `b = (φ a).snd y` with `‖a‖ ≤ 1` and `y` arbitrarily close to `b`. -/
theorem IsMultiplierNondegenerate.exists_snd_apply_eq_of_pos {φ : A →⋆ₙₐ[ℂ] 𝓜(ℂ, B)}
    (hφ : φ.IsMultiplierNondegenerate) (b : B) {ε : ℝ} (hε : 0 < ε) :
    ∃ a y, ‖a‖ ≤ 1 ∧ ‖y - b‖ < ε ∧ (φ a).snd y = b := by
  obtain ⟨a, y, ha, hy, hfac⟩ := hφ.exists_fst_apply_eq_of_pos (star b) hε
  exact ⟨star a, star y, (norm_star a).trans_le ha,
    by rw [← norm_star (star y - b), star_sub, star_star]; exact hy,
    by simpa [map_star] using congrArg star hfac⟩

/-- Every `b : B` factors as `b = (φ a).snd y` when `φ : A →⋆ₙₐ[ℂ] 𝓜(ℂ, B)` is nondegenerate. -/
theorem IsMultiplierNondegenerate.exists_snd_apply_eq {φ : A →⋆ₙₐ[ℂ] 𝓜(ℂ, B)}
    (hφ : φ.IsMultiplierNondegenerate) (b : B) : ∃ a y, (φ a).snd y = b :=
  let ⟨a, y, _, _, h⟩ := hφ.exists_snd_apply_eq_of_pos b one_pos; ⟨a, y, h⟩

end NonUnitalStarAlgHom
