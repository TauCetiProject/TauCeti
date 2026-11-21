/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.VonNeumannAlgebra.Lattice

/-!
# Factors of von Neumann algebras

Factors—von Neumann algebras with trivial center—are the indecomposable building blocks of von
Neumann algebra classification and the target of the Murray–von Neumann ICC factor theorem
(`TauCeti.isFactor_groupVonNeumannAlgebra_iff`). `VonNeumannAlgebra.IsFactor` holds when
`(1 : H →L[ℂ] H) ≠ 0` and every central element `x ∈ M ∩ M'` is a scalar multiple of `1`,
equivalently `Nontrivial H` and `M ⊓ M.commutant = ⊥`
(`VonNeumannAlgebra.isFactor_iff_inf_commutant_eq_bot`). Factorhood is preserved under commutants
(`VonNeumannAlgebra.isFactor_commutant_iff`) and holds for `⊤` and `⊥` on any nontrivial Hilbert
space.

## References

* J. Peterson, *Notes on von Neumann Algebras* (2013), Proposition 2.1.3.
* C. Anantharaman and S. Popa, *An Introduction to II₁ Factors*, §2.1.
-/

public section

namespace VonNeumannAlgebra

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A concrete von Neumann algebra `M` on `H` is a **factor** when `(1 : H →L[ℂ] H) ≠ 0` and every
element of the center `M ∩ M'` is a scalar multiple of the identity. -/
def IsFactor (M : VonNeumannAlgebra H) : Prop :=
  (1 : H →L[ℂ] H) ≠ 0 ∧
    ∀ x : H →L[ℂ] H, x ∈ M → x ∈ M.commutant → ∃ c : ℂ, x = c • (1 : H →L[ℂ] H)

theorem isFactor_def (M : VonNeumannAlgebra H) :
    M.IsFactor ↔
      (1 : H →L[ℂ] H) ≠ 0 ∧
        ∀ x : H →L[ℂ] H, x ∈ M → x ∈ M.commutant → ∃ c : ℂ, x = c • (1 : H →L[ℂ] H) :=
  Iff.rfl

/-- In a factor on `H`, the identity operator on `H` is nonzero. -/
theorem IsFactor.one_ne_zero {M : VonNeumannAlgebra H} (hM : M.IsFactor) :
    (1 : H →L[ℂ] H) ≠ 0 :=
  hM.1

/-- The underlying Hilbert space of a factor is nontrivial. -/
theorem IsFactor.nontrivial {M : VonNeumannAlgebra H} (hM : M.IsFactor) : Nontrivial H := by
  by_contra h
  rw [not_nontrivial_iff_subsingleton] at h
  exact hM.1 (Subsingleton.elim _ _)

/-- Every element in both a factor `M` and its commutant `M'` is a scalar multiple of `1`. -/
theorem IsFactor.exists_eq_smul_one {M : VonNeumannAlgebra H} (hM : M.IsFactor) {x : H →L[ℂ] H}
    (hx : x ∈ M) (hx' : x ∈ M.commutant) : ∃ c : ℂ, x = c • (1 : H →L[ℂ] H) :=
  hM.2 x hx hx'

/-- No von Neumann algebra on a subsingleton Hilbert space is a factor. -/
@[simp]
theorem not_isFactor_of_subsingleton [Subsingleton H] (M : VonNeumannAlgebra H) : ¬ M.IsFactor :=
  fun hM => hM.1 (Subsingleton.elim _ _)

/-- `M` is a factor if and only if `H` is nontrivial and the center `M ⊓ M'` is the scalar algebra
`⊥`. -/
theorem isFactor_iff_inf_commutant_eq_bot (M : VonNeumannAlgebra H) :
    M.IsFactor ↔ Nontrivial H ∧ M ⊓ M.commutant = ⊥ := by
  refine ⟨fun hM => ⟨hM.nontrivial, le_antisymm (fun x hx => ?_) bot_le⟩, fun ⟨_, hbot⟩ => ?_⟩
  · obtain ⟨c, rfl⟩ := hM.2 x (mem_inf.1 hx).1 (mem_inf.1 hx).2
    exact mem_bot.2 ⟨c, Algebra.algebraMap_eq_smul_one c⟩
  · refine ⟨one_ne_zero, fun x hx hx' => ?_⟩
    obtain ⟨c, rfl⟩ := mem_bot.1 (hbot ▸ mem_inf.2 ⟨hx, hx'⟩)
    exact ⟨c, (Algebra.algebraMap_eq_smul_one c).symm⟩

/-- The commutant of a factor is a factor. -/
theorem IsFactor.commutant {M : VonNeumannAlgebra H} (hM : M.IsFactor) : M.commutant.IsFactor :=
  ⟨hM.1, fun x hx hx' => hM.2 x (by simpa using hx') hx⟩

/-- A von Neumann algebra's commutant is a factor if and only if the algebra itself is a factor. -/
@[simp]
theorem isFactor_commutant_iff (M : VonNeumannAlgebra H) : M.commutant.IsFactor ↔ M.IsFactor :=
  ⟨fun h => by simpa using h.commutant, IsFactor.commutant⟩

/-- On a nontrivial Hilbert space, `⊤ = B(H)` is a factor. -/
@[simp]
theorem isFactor_top [Nontrivial H] : (⊤ : VonNeumannAlgebra H).IsFactor := by
  rw [isFactor_iff_inf_commutant_eq_bot, commutant_top, top_inf_eq]
  exact ⟨inferInstance, rfl⟩

/-- On a nontrivial Hilbert space, the scalar algebra `⊥ = ℂ • 1` is a factor. -/
@[simp]
theorem isFactor_bot [Nontrivial H] : (⊥ : VonNeumannAlgebra H).IsFactor := by
  rw [← commutant_top, isFactor_commutant_iff]; exact isFactor_top

end VonNeumannAlgebra
