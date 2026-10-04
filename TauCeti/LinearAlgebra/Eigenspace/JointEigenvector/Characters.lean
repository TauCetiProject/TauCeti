/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.Algebra.Pi
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

/-!
# Characters of a faithfully diagonalized algebra

If an algebra over a domain acts faithfully on a finite free module with a basis of joint
eigenvectors, every character of the algebra is one of the characters occurring on that basis.
Over a field, when those characters are distinct, their evaluation map is an isomorphism onto
the algebra of functions on the basis index set. The algebra and the eigenvectors must be over
the same coefficient ring: faithfulness before extending scalars alone does not imply this
conclusion.
-/

public section

section Domain

variable {K A V ι : Type*} [CommRing K] [IsDomain K] [Ring A] [Algebra K A]
  [AddCommGroup V] [Module K V] [_root_.Finite ι]

/-- Every character of a faithfully diagonalized algebra occurs on its eigenbasis.
No commutativity assumption on the algebra is needed. -/
theorem AlgHom.exists_eq_of_apply_basis_eq_smul (ρ : A →ₐ[K] Module.End K V)
    (hρ : Function.Injective ρ) (b : Module.Basis ι K V) (χ : ι → A →ₐ[K] K)
    (hb : ∀ a i, ρ a (b i) = χ i a • b i) (ψ : A →ₐ[K] K) :
    ∃ i, ψ = χ i := by
  classical
  let := Fintype.ofFinite ι
  by_contra h
  have hne : ∀ i, ψ ≠ χ i := by simpa using h
  have hdiff : ∀ i, ∃ a : A, ψ a ≠ χ i a := fun i ↦ by
    by_contra hn
    exact hne i (AlgHom.ext (by simpa using hn))
  choose a ha using hdiff
  let t := (Finset.univ.toList.map fun i ↦ a i - algebraMap K A (χ i (a i))).prod
  have hχ (i : ι) : χ i t = 0 := by
    rw [map_list_prod]
    apply List.prod_eq_zero_iff.mpr
    apply List.mem_map.mpr
    refine ⟨a i - algebraMap K A (χ i (a i)), ?_, ?_⟩
    · exact List.mem_map.mpr ⟨i, by simp, rfl⟩
    · simp
  have ht : t = 0 := hρ <| by
    apply b.ext
    intro i
    simp [hb, hχ]
  have hψ : ψ t ≠ 0 := by
    rw [map_list_prod]
    apply List.prod_ne_zero
    intro hx
    obtain ⟨y, hy, hy0⟩ := List.mem_map.mp hx
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hy
    exact sub_ne_zero.mpr (ha i) (by simpa using hy0)
  exact hψ (by simp [ht])

end Domain

section Field

variable {K A V ι : Type*} [Field K] [Ring A] [Algebra K A]
  [AddCommGroup V] [Module K V] [_root_.Finite ι]

/-- The eigenvalue map identifies a faithfully diagonalized algebra with the algebra of
functions on its eigenbasis, provided the basis characters are distinct. -/
theorem AlgHom.pi_bijective_of_apply_basis_eq_smul (ρ : A →ₐ[K] Module.End K V)
    (hρ : Function.Injective ρ) (b : Module.Basis ι K V) (χ : ι → A →ₐ[K] K)
    (hb : ∀ a i, ρ a (b i) = χ i a • b i) (hχ : Function.Injective χ) :
    Function.Bijective (AlgHom.pi χ) := by
  classical
  let := Fintype.ofFinite ι
  let := Module.Finite.of_basis b
  let := Module.Finite.of_injective ρ.toLinearMap hρ
  have hinj : Function.Injective (AlgHom.pi χ) := by
    intro a c hac
    apply hρ
    apply b.ext
    intro i
    rw [hb, hb]
    exact congrArg (· • b i) (congrFun hac i)
  have hle : Module.finrank K (ι → K) ≤ Module.finrank K A := by
    have h := ((linearIndependent_algHom_toLinearMap K A K).comp χ hχ).fintype_card_le_finrank
    simpa [Module.finrank_pi, Subspace.dual_finrank_eq] using h
  have hdim : Module.finrank K A = Module.finrank K (ι → K) :=
    le_antisymm (LinearMap.finrank_le_finrank_of_injective
      (f := (AlgHom.pi χ).toLinearMap) hinj) hle
  exact ⟨hinj,
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (f := (AlgHom.pi χ).toLinearMap) hdim).mp hinj⟩

end Field
