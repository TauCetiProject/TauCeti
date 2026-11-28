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

private lemma essentialSubmodule_repActionCLM (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) :
    (repActionCLM π).essentialSubmodule = π.essentialSubspace := by
  rw [ContinuousLinearMap.essentialSubmodule_eq_topologicalClosure_span,
    π.essentialSubspace_eq_topologicalClosure_span]
  congr 2
  ext z
  simp [repActionCLM, Prod.exists]

/-- **Cohen–Hewitt factorization for nondegenerate representations.** Every `ξ : H` factors as
`ξ = π a η` with `‖a‖ ≤ 1` and `η` arbitrarily close to `ξ`. -/
theorem IsNondegenerate.exists_apply_eq_of_pos {π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)}
    (hπ : π.IsNondegenerate) (ξ : H) {ε : ℝ} (hε : 0 < ε) :
    ∃ a η, ‖a‖ ≤ 1 ∧ ‖η - ξ‖ < ε ∧ π a η = ξ := by
  have hx : ξ ∈ (repActionCLM π).essentialSubmodule := by
    rw [essentialSubmodule_repActionCLM, π.isNondegenerate_iff_essentialSubspace_eq_top.mp hπ]
    exact Submodule.mem_top
  obtain ⟨a, η, ha, -, hη, hfac⟩ :=
    (repActionCLM π).exists_norm_le_one_apply_eq_of_mem_essentialSubmodule
      (fun a b v => by simp [repActionCLM, mul_apply_eq_comp]) hx hε
  exact ⟨a, η, ha, hη, hfac⟩

/-- Every `ξ : H` factors as `ξ = π a η` when `π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)` is nondegenerate. -/
theorem IsNondegenerate.exists_apply_eq {π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)}
    (hπ : π.IsNondegenerate) (ξ : H) : ∃ a η, π a η = ξ :=
  let ⟨a, η, _, _, h⟩ := hπ.exists_apply_eq_of_pos ξ one_pos; ⟨a, η, h⟩

/-- By Cohen–Hewitt factorization, `π.essentialSubspace` already equals `⋃ a, Set.range (π a)` as a
set, without taking linear spans or closures. -/
theorem coe_essentialSubspace_eq_iUnion_range (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) :
    (π.essentialSubspace : Set H) = ⋃ a, Set.range (π a) := by
  rw [← essentialSubmodule_repActionCLM]
  exact (repActionCLM π).coe_essentialSubmodule_eq_iUnion_range fun a b v => by
    simp [repActionCLM, mul_apply_eq_comp]

/-- A Hilbert-space representation `π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)` is nondegenerate if and only if
every vector in `H` lies in the range of some `π a` (`H = π(A)H`). -/
theorem isNondegenerate_iff_iUnion_range_eq_univ {π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)} :
    π.IsNondegenerate ↔ (⋃ a, Set.range (π a)) = Set.univ := by
  rw [π.isNondegenerate_iff_essentialSubspace_eq_top, ← SetLike.coe_set_eq,
    π.coe_essentialSubspace_eq_iUnion_range, Submodule.top_coe]

end NonUnitalStarAlgHom
