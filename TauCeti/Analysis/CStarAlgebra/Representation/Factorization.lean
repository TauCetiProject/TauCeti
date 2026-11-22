/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Representation.EssentialSubspace
import TauCeti.Analysis.CStarAlgebra.CohenFactorization

/-!
# Cohen–Hewitt factorization for Hilbert-space representations

Applies `TauCeti.Analysis.CStarAlgebra.CohenFactorization` to a Hilbert-space representation
`π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)`: `π.essentialSubspace` already equals `⋃ a, Set.range (π a)`
(`coe_essentialSubspace_eq_iUnion_range`), so `π` is nondegenerate iff `H = π(A)H`
(`isNondegenerate_iff_iUnion_range_eq_univ`), and every vector factors as `ξ = π a η` with `‖a‖ ≤ 1`
and `η` arbitrarily close to `ξ` (`IsNondegenerate.exists_apply_eq_of_pos`).

## References

* E. C. Lance, *Hilbert C\*-Modules*, London Math. Soc. Lecture Note Series 210, Proposition 1.8.
* Iain Raeburn and Dana Williams, *Morita Equivalence and Continuous-Trace C\*-Algebras*,
  Proposition 2.31.
-/

public section
noncomputable section

namespace NonUnitalStarAlgHom

variable {A H : Type*} [NonUnitalCStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

private def repActionCLM (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) : A →L[ℂ] H →L[ℂ] H :=
  LinearMap.mkContinuous ⟨⟨⇑π, map_add π⟩, map_smul π⟩ 1 fun a => by simpa using norm_apply_le π a

/-- **Cohen–Hewitt factorization for nondegenerate representations.** Every `ξ : H` factors as
`ξ = π a η` with `‖a‖ ≤ 1` and `η` arbitrarily close to `ξ`. -/
theorem IsNondegenerate.exists_apply_eq_of_pos {π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)}
    (hπ : π.IsNondegenerate) (ξ : H) {ε : ℝ} (hε : 0 < ε) :
    ∃ a η, ‖a‖ ≤ 1 ∧ ‖η - ξ‖ < ε ∧ π a η = ξ := by
  have htop : (Submodule.span ℂ (⋃ a, Set.range (repActionCLM π a))).topologicalClosure = ⊤ := by
    simpa [repActionCLM] using
      Submodule.dense_iff_topologicalClosure_eq_top.mp (isNondegenerate_iff_dense.mp hπ)
  obtain ⟨a, η, ha, -, hη, hfac⟩ :=
    (repActionCLM π).exists_apply_eq_of_mem_topologicalClosure_span_iUnion
      (fun a b v => by simp [repActionCLM, mul_apply_eq_comp]) (htop.symm ▸ Submodule.mem_top) hε
  exact ⟨a, η, ha, hη, hfac⟩

/-- Every `ξ : H` factors as `ξ = π a η` when `π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)` is nondegenerate. -/
theorem IsNondegenerate.exists_apply_eq {π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)}
    (hπ : π.IsNondegenerate) (ξ : H) : ∃ a η, π a η = ξ :=
  let ⟨a, η, _, _, h⟩ := hπ.exists_apply_eq_of_pos ξ one_pos; ⟨a, η, h⟩

/-- By Cohen–Hewitt factorization, `π.essentialSubspace` already equals `⋃ a, Set.range (π a)` as a
set, without taking linear spans or closures. -/
theorem coe_essentialSubspace_eq_iUnion_range (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) :
    (π.essentialSubspace : Set H) = ⋃ a, Set.range (π a) := by
  have hcl : π.essentialSubspace = (Submodule.span ℂ (⋃ a, Set.range (π a))).topologicalClosure :=
    le_antisymm
      ((π.essentialSubspace_le_iff (Submodule.isClosed_topologicalClosure _)).2 fun a ξ =>
        Submodule.le_topologicalClosure _ <| Submodule.subset_span <| Set.mem_iUnion.2 ⟨a, ξ, rfl⟩)
      (Submodule.topologicalClosure_minimal _ (Submodule.span_le.2 fun _ hx =>
        let ⟨a, ξ, h⟩ := Set.mem_iUnion.1 hx; h ▸ π.apply_mem_essentialSubspace a ξ)
        π.isClosed_essentialSubspace)
  rw [hcl]
  exact (repActionCLM π).coe_topologicalClosure_span_iUnion_range_eq fun a b v => by
    simp [repActionCLM, mul_apply_eq_comp]

/-- A Hilbert-space representation `π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)` is nondegenerate if and only if
every vector in `H` lies in the range of some `π a` (`H = π(A)H`). -/
theorem isNondegenerate_iff_iUnion_range_eq_univ {π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)} :
    π.IsNondegenerate ↔ (⋃ a, Set.range (π a)) = Set.univ := by
  rw [π.isNondegenerate_iff_essentialSubspace_eq_top, ← SetLike.coe_set_eq,
    π.coe_essentialSubspace_eq_iUnion_range, Submodule.top_coe]

end NonUnitalStarAlgHom
