/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.FiniteDimensional.Basic
import TauCeti.Analysis.CStarAlgebra.CStarMatrix
import TauCeti.Analysis.CStarAlgebra.FiniteDimensional.Embeddings

/-!
# Classification of complex C⋆-algebras of dimension at most `4`

Applying `TauCeti.CStarWedderburnPresentation` from
`TauCeti.Analysis.CStarAlgebra.FiniteDimensional.Basic` and the commutative matrix-embedding bound
`CStarAlgebra.finrank_le_card_of_injective_cstarMatrix` from
`TauCeti.Analysis.CStarAlgebra.FiniteDimensional.Embeddings`, this file classifies complex
C⋆-algebras (unital or presented only as `NonUnitalCStarAlgebra`) in complex dimensions at most
`4`:

* Every complex C⋆-algebra of dimension `< 4` is commutative and `⋆`-isomorphic to
  `Fin (Module.finrank ℂ A) → ℂ`; in particular dimensions `1`, `2`, and `3` each admit a unique
  `⋆`-isomorphism class (`ℂ`, `Fin 2 → ℂ`, and `Fin 3 → ℂ`).
* No `3`-dimensional complex C⋆-algebra admits an injective `NonUnitalStarAlgHom` into
  `CStarMatrix (Fin 2) (Fin 2) ℂ`, even without unitality, and no `⋆`-subalgebra of
  `CStarMatrix (Fin 2) (Fin 2) ℂ` has complex dimension `3`.
* Every `4`-dimensional complex C⋆-algebra is `⋆`-isomorphic either to `Fin 4 → ℂ` or to
  `CStarMatrix (Fin 2) (Fin 2) ℂ`; these two are not `⋆`-isomorphic
  (`CStarAlgebra.isEmpty_starAlgEquiv_fin_four_fun_cstarMatrix_fin_two`), making `4` the least
  complex dimension admitting two non-`⋆`-isomorphic complex C⋆-algebras in `Type`.

## Main results

* `CStarAlgebra.isMulCommutative_of_finrank_lt_four`,
  `CStarAlgebra.nonempty_starAlgEquiv_fun_of_finrank_lt_four`,
  `CStarAlgebra.nonempty_starAlgEquiv_of_finrank_eq_of_lt_four`: commutativity and uniqueness of
  `⋆`-isomorphism class below dimension `4`.
* `CStarAlgebra.nonempty_starAlgEquiv_complex_of_finrank_eq_one`,
  `CStarAlgebra.nonempty_starAlgEquiv_fin_two_fun_of_finrank_eq_two`,
  `CStarAlgebra.nonempty_starAlgEquiv_fin_three_fun_of_finrank_eq_three`: classification in
  dimensions `1`, `2`, and `3`.
* `CStarAlgebra.not_injective_nonUnitalStarAlgHom_cstarMatrix_fin_two_of_finrank_eq_three`,
  `NonUnitalStarSubalgebra.finrank_cstarMatrix_fin_two_ne_three`: non-embeddability of `ℂ³` into
  `M₂(ℂ)`.
* `CStarAlgebra.nonempty_starAlgEquiv_fin_four_fun_or_cstarMatrix_fin_two_of_finrank_eq_four`,
  `CStarAlgebra.isEmpty_starAlgEquiv_fin_four_fun_cstarMatrix_fin_two`,
  `CStarAlgebra.isLeast_finrank_exists_isEmpty_starAlgEquiv`: classification in dimension `4` and
  minimality of dimension `4` for non-`⋆`-isomorphic pairs.
-/

public section

open scoped BigOperators ComplexOrder

universe u v

namespace CStarAlgebra

/-! ### Classification in complex dimensions below `4` -/

section BelowFour

variable {A : Type u} [NonUnitalCStarAlgebra A] [FiniteDimensional ℂ A]

/-- Every complex C⋆-algebra of dimension strictly less than `4` is multiplicatively commutative. -/
theorem isMulCommutative_of_finrank_lt_four (h : Module.finrank ℂ A < 4) :
    IsMulCommutative A := by
  let P := cstarWedderburnPresentation A
  refine P.isMulCommutative_iff_forall_degree_eq_one.mpr fun i ↦ ?_
  have hsq : P.degree i ^ 2 < 4 := (P.sq_degree_le_finrank i).trans_lt h
  have hge : 1 ≤ P.degree i := P.one_le_degree i
  nlinarith

/-- Every complex C⋆-algebra of dimension `< 4` is `⋆`-isomorphic to
`Fin (Module.finrank ℂ A) → ℂ`. -/
theorem nonempty_starAlgEquiv_fun_of_finrank_lt_four (h : Module.finrank ℂ A < 4) :
    Nonempty (A ≃⋆ₐ[ℂ] (Fin (Module.finrank ℂ A) → ℂ)) :=
  (isMulCommutative_iff_nonempty_starAlgEquiv_fun A).mp (isMulCommutative_of_finrank_lt_four h)

/-- Any two complex C⋆-algebras of the same complex dimension `< 4` are `⋆`-algebra isomorphic. -/
theorem nonempty_starAlgEquiv_of_finrank_eq_of_lt_four {B : Type v} [NonUnitalCStarAlgebra B]
    [FiniteDimensional ℂ B] (hAB : Module.finrank ℂ A = Module.finrank ℂ B)
    (h : Module.finrank ℂ A < 4) : Nonempty (A ≃⋆ₐ[ℂ] B) := by
  obtain ⟨eA⟩ := nonempty_starAlgEquiv_fun_of_finrank_lt_four h
  obtain ⟨eB⟩ := nonempty_starAlgEquiv_fun_of_finrank_lt_four (hAB ▸ h)
  exact ⟨eA.trans ((StarAlgEquiv.piCongrLeft ℂ (fun _ ↦ ℂ) (finCongr hAB)).trans eB.symm)⟩

/-- Every `1`-dimensional complex C⋆-algebra is `⋆`-isomorphic to `ℂ`. -/
theorem nonempty_starAlgEquiv_complex_of_finrank_eq_one (h : Module.finrank ℂ A = 1) :
    Nonempty (A ≃⋆ₐ[ℂ] ℂ) := by
  obtain ⟨e⟩ := nonempty_starAlgEquiv_fun_of_finrank_lt_four (by omega : Module.finrank ℂ A < 4)
  exact ⟨e.trans ((StarAlgEquiv.piCongrLeft ℂ (fun _ ↦ ℂ) (finCongr h)).trans
    (StarAlgEquiv.funUnique ℂ (Fin 1) ℂ))⟩

/-- Every `2`-dimensional complex C⋆-algebra is `⋆`-isomorphic to `Fin 2 → ℂ`. -/
theorem nonempty_starAlgEquiv_fin_two_fun_of_finrank_eq_two (h : Module.finrank ℂ A = 2) :
    Nonempty (A ≃⋆ₐ[ℂ] (Fin 2 → ℂ)) := by
  obtain ⟨e⟩ := nonempty_starAlgEquiv_fun_of_finrank_lt_four (by omega : Module.finrank ℂ A < 4)
  exact ⟨e.trans (StarAlgEquiv.piCongrLeft ℂ (fun _ ↦ ℂ) (finCongr h))⟩

/-- Every `3`-dimensional complex C⋆-algebra is `⋆`-isomorphic to `Fin 3 → ℂ`. -/
theorem nonempty_starAlgEquiv_fin_three_fun_of_finrank_eq_three (h : Module.finrank ℂ A = 3) :
    Nonempty (A ≃⋆ₐ[ℂ] (Fin 3 → ℂ)) := by
  obtain ⟨e⟩ := nonempty_starAlgEquiv_fun_of_finrank_lt_four (by omega : Module.finrank ℂ A < 4)
  exact ⟨e.trans (StarAlgEquiv.piCongrLeft ℂ (fun _ ↦ ℂ) (finCongr h))⟩

/-- **No `3`-dimensional complex C⋆-algebra embeds into `M₂(ℂ)`, even nonunitally**: any
`NonUnitalStarAlgHom` from `A` into `CStarMatrix (Fin 2) (Fin 2) ℂ` fails to be injective. -/
theorem not_injective_nonUnitalStarAlgHom_cstarMatrix_fin_two_of_finrank_eq_three
    (h : Module.finrank ℂ A = 3) (φ : A →⋆ₙₐ[ℂ] CStarMatrix (Fin 2) (Fin 2) ℂ) :
    ¬Function.Injective φ := by
  have : IsMulCommutative A := isMulCommutative_of_finrank_lt_four (by omega)
  intro hφ
  have hle := finrank_le_card_of_injective_cstarMatrix φ hφ
  rw [h, Fintype.card_fin] at hle
  omega

end BelowFour

end CStarAlgebra

/-- No `⋆`-subalgebra (unital or not) of `CStarMatrix (Fin 2) (Fin 2) ℂ` has complex dimension
`3`. -/
theorem NonUnitalStarSubalgebra.finrank_cstarMatrix_fin_two_ne_three
    (S : NonUnitalStarSubalgebra ℂ (CStarMatrix (Fin 2) (Fin 2) ℂ)) :
    Module.finrank ℂ S ≠ 3 := by
  have : FiniteDimensional ℂ S := .of_injective S.toSubmodule.subtype Subtype.val_injective
  have : IsClosed (S : Set (CStarMatrix (Fin 2) (Fin 2) ℂ)) :=
    S.toSubmodule.isClosed_of_finiteDimensional
  let _ : NonUnitalCStarAlgebra S := NonUnitalStarSubalgebra.nonUnitalCStarAlgebra S
  intro hdim
  exact CStarAlgebra.not_injective_nonUnitalStarAlgHom_cstarMatrix_fin_two_of_finrank_eq_three hdim
    (NonUnitalStarSubalgebraClass.subtype S) Subtype.val_injective

/-! ### Classification in dimension `4` and least nonisomorphic dimension -/

namespace CStarAlgebra

/-- **Classification in dimension `4`**: every `4`-dimensional complex C⋆-algebra is `⋆`-isomorphic
either to `Fin 4 → ℂ` or to `CStarMatrix (Fin 2) (Fin 2) ℂ`. -/
theorem nonempty_starAlgEquiv_fin_four_fun_or_cstarMatrix_fin_two_of_finrank_eq_four
    {A : Type u} [NonUnitalCStarAlgebra A] [FiniteDimensional ℂ A] (h : Module.finrank ℂ A = 4) :
    Nonempty (A ≃⋆ₐ[ℂ] (Fin 4 → ℂ)) ∨ Nonempty (A ≃⋆ₐ[ℂ] CStarMatrix (Fin 2) (Fin 2) ℂ) := by
  let P := cstarWedderburnPresentation A
  by_cases hall : ∀ i, P.degree i = 1
  · have : IsMulCommutative A := P.isMulCommutative_iff_forall_degree_eq_one.mpr hall
    obtain ⟨e⟩ := (isMulCommutative_iff_nonempty_starAlgEquiv_fun A).mp inferInstance
    exact Or.inl ⟨e.trans (StarAlgEquiv.piCongrLeft ℂ (fun _ ↦ ℂ) (finCongr h))⟩
  · obtain ⟨i₀, hi₀⟩ := not_forall.mp hall
    have hge₂ : 2 ≤ P.degree i₀ := lt_of_le_of_ne (P.one_le_degree i₀) (Ne.symm hi₀)
    have hsq_le : P.degree i₀ ^ 2 ≤ 4 := h ▸ P.sq_degree_le_finrank i₀
    have hd₂ : P.degree i₀ = 2 := by nlinarith
    have hsum : ∑ j : Fin P.blockCount, P.degree j ^ 2 = 4 := P.finrank_eq_sum_sq.symm.trans h
    have herase : ∑ j ∈ Finset.univ.erase i₀, P.degree j ^ 2 = 0 := by
      have hsplit := Finset.add_sum_erase Finset.univ (fun j ↦ P.degree j ^ 2) (Finset.mem_univ i₀)
      rw [hsum, hd₂] at hsplit
      omega
    have hunique_idx : ∀ j : Fin P.blockCount, j = i₀ := by
      intro j
      by_contra hne
      have hmem : j ∈ Finset.univ.erase i₀ := Finset.mem_erase.mpr ⟨hne, Finset.mem_univ j⟩
      have hzero : P.degree j ^ 2 = 0 :=
        (Finset.sum_eq_zero_iff.mp herase) j hmem
      have hpos : 1 ≤ P.degree j := P.one_le_degree j
      nlinarith
    let _ : Unique (Fin P.blockCount) := ⟨⟨i₀⟩, hunique_idx⟩
    have e₁ : A ≃⋆ₐ[ℂ] CStarMatrix (Fin (P.degree i₀)) (Fin (P.degree i₀)) ℂ :=
      P.equiv.trans (StarAlgEquiv.piUnique ℂ
        (fun j : Fin P.blockCount ↦ CStarMatrix (Fin (P.degree j)) (Fin (P.degree j)) ℂ))
    exact Or.inr ⟨e₁.trans (CStarMatrix.reindexₐ ℂ ℂ (finCongr hd₂))⟩

/-- `Fin 4 → ℂ` and `CStarMatrix (Fin 2) (Fin 2) ℂ` are not `⋆`-algebra isomorphic. -/
theorem isEmpty_starAlgEquiv_fin_four_fun_cstarMatrix_fin_two :
    IsEmpty ((Fin 4 → ℂ) ≃⋆ₐ[ℂ] CStarMatrix (Fin 2) (Fin 2) ℂ) := by
  refine ⟨fun e ↦ CStarMatrix.not_isMulCommutative (m := Fin 2) (A := ℂ) ⟨⟨fun x y ↦ ?_⟩⟩⟩
  apply e.symm.injective
  rw [map_mul, map_mul, mul_comm]

/-- **`4` is the least complex dimension admitting two non-`⋆`-isomorphic complex C⋆-algebras**
(quantifying over `NonUnitalCStarAlgebra`s in `Type`; see
`isEmpty_starAlgEquiv_fin_four_fun_cstarMatrix_fin_two` for a witnessing pair). -/
theorem isLeast_finrank_exists_isEmpty_starAlgEquiv :
    IsLeast {d : ℕ | ∃ (A B : Type) (_ : NonUnitalCStarAlgebra A) (_ : NonUnitalCStarAlgebra B)
      (_ : FiniteDimensional ℂ A) (_ : FiniteDimensional ℂ B),
      Module.finrank ℂ A = d ∧ Module.finrank ℂ B = d ∧ IsEmpty (A ≃⋆ₐ[ℂ] B)} 4 := by
  refine ⟨?_, ?_⟩
  · exact ⟨Fin 4 → ℂ, CStarMatrix (Fin 2) (Fin 2) ℂ, inferInstance, inferInstance,
      inferInstance, inferInstance, by simp, by simp,
      isEmpty_starAlgEquiv_fin_four_fun_cstarMatrix_fin_two⟩
  · rintro d ⟨A, B, _, _, _, _, rfl, hB, hempty⟩
    by_contra! hlt
    obtain ⟨e⟩ := nonempty_starAlgEquiv_of_finrank_eq_of_lt_four hB.symm hlt
    exact hempty.false e

end CStarAlgebra
