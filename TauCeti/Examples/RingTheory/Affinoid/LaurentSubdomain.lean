/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Affinoid.Subdomain.Laurent

/-!
# Boundary cases for Laurent subdomains

These examples use the algebraic subdomain universal property with an unnormed test algebra,
recover the ambient algebra when there are no inequalities, and check that inverting zero
produces an empty subdomain with zero coordinate ring. The whole-spectrum comparison also
checks that a nonzero nilpotent is retained, rather than lost by passing to classical points.
No nontriviality or reducedness assumption is imposed on the ambient affinoid algebra.
-/

public section

namespace TauCeti.Examples

universe u

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A : Type u} [NormedCommRing A] [NormedAlgebra K A] [IsUltrametricDist A] [CompleteSpace A]
  (hA : IsAffinoidAlgebra K A)

-- The test algebra has no chosen norm, including in the uniqueness clause.
example {r s : ℕ} (f : Fin r → A) (g : Fin s → A)
    {C : Type u} [CommRing C] [Algebra K C] (hC : IsAffinoidAlgebra K C)
    (ψ : A →ₐ[K] C) (hψ : Set.range (hC.maximalSpectrumComap ψ) ⊆ laurentDomain K f g) :
    ∃! χ : LaurentFraction f g →ₐ[K] C,
      χ.comp (IsScalarTower.toAlgHom K A _) = ψ :=
  (LaurentFraction.isAffinoidSubdomainMap hA).existsUnique_algHom hC ψ hψ

-- No inequalities give the whole spectrum, even when `A` is the zero algebra.
example : ∃ e : LaurentFraction (Fin.elim0 : Fin 0 → A) (Fin.elim0 : Fin 0 → A) ≃ₐ[K] A,
    ∀ a, e (algebraMap A _ a) = a := by
  have h := LaurentFraction.isAffinoidSubdomainMap hA
    (f := (Fin.elim0 : Fin 0 → A)) (g := (Fin.elim0 : Fin 0 → A))
  have hU : laurentDomain K (Fin.elim0 : Fin 0 → A) (Fin.elim0 : Fin 0 → A) = Set.univ := by
    ext x
    simp
  rw [hU] at h
  exact ⟨h.algEquiv (IsAffinoidSubdomainMap.id hA), fun a ↦ h.algEquiv_apply _ a⟩

-- A zero denominator is inverted, without a unit-ideal hypothesis on the input tuple.
example : Subsingleton (LaurentFraction (Fin.elim0 : Fin 0 → A) (fun _ : Fin 1 ↦ (0 : A))) := by
  have h := LaurentFraction.isAffinoidSubdomainMap hA
    (f := (Fin.elim0 : Fin 0 → A)) (g := fun _ : Fin 1 ↦ (0 : A))
  have hU : laurentDomain K (Fin.elim0 : Fin 0 → A) (fun _ : Fin 1 ↦ (0 : A)) = ∅ := by
    ext x
    simp
  rw [hU] at h
  exact (h.algEquiv (IsAffinoidSubdomainMap.empty hA)).injective.subsingleton

-- The whole-spectrum presentation preserves nonzero square-zero elements of any affinoid.
example {t : A} (ht : t ≠ 0) (ht2 : t ^ 2 = 0) :
    ∃ z : LaurentFraction (Fin.elim0 : Fin 0 → A) (Fin.elim0 : Fin 0 → A),
      z ≠ 0 ∧ z ^ 2 = 0 := by
  have h := LaurentFraction.isAffinoidSubdomainMap hA
    (f := (Fin.elim0 : Fin 0 → A)) (g := (Fin.elim0 : Fin 0 → A))
  have hU : laurentDomain K (Fin.elim0 : Fin 0 → A) (Fin.elim0 : Fin 0 → A) = Set.univ := by
    ext x
    simp
  rw [hU] at h
  let e := h.algEquiv (IsAffinoidSubdomainMap.id hA)
  exact ⟨e.symm t, by simpa using e.symm.injective.ne ht, by simp [← map_pow, ht2]⟩

end TauCeti.Examples
