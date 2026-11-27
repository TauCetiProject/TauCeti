/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.CompletelyPositiveMap.Nuclear
public import TauCeti.Analysis.CStarAlgebra.CompletelyPositiveMap.Unitization
import Mathlib.Tactic.FinCases
import TauCeti.Analysis.CStarAlgebra.Basic
import TauCeti.Algebra.Algebra.Unitization

/-!
# Unitization of nuclear completely positive contractions

The unital extension `λ + a ↦ λ + φ a` of a completely positive contraction `φ : A → B`
(`CompletelyPositiveMap.unitization`) is a unital completely positive map `A⁺¹ → B⁺¹`, hence a
contraction (`CompletelyPositiveMap.norm_unitization_apply_le`). If `φ` is a nuclear contraction,
so is its unital extension (`CompletelyPositiveMap.IsNuclearContraction.unitization`): for an
approximate factorization `φ ≈ β ∘ α` through `M_n`, the unital extensions give
`φ⁺ ≈ β⁺ ∘ α⁺` through `M_n⁺`, with the same error, and `M_n⁺ ≅ M_n × ℂ` is nuclear, being a finite
direct sum of matrix algebras. In particular the unitization of a nuclear C⋆-algebra is nuclear
(`TauCeti.CStarAlgebra.isNuclear_unitization`).

## Main declarations

* `CompletelyPositiveMap.norm_unitization_apply_le`: the unital extension of a completely positive
  contraction is a contraction.
* `CompletelyPositiveMap.unitization_comp`: unital extension commutes with composition.
* `CompletelyPositiveMap.IsNuclearContraction.unitization`: the unital extension of a nuclear
  contraction is a nuclear contraction.
* `TauCeti.CStarAlgebra.isNuclear_unitization`: `A⁺¹` is nuclear when `A` is.

## References

* B. Blackadar, *Operator Algebras: Theory of C⋆-Algebras and von Neumann Algebras*,
  Encyclopaedia of Mathematical Sciences 122, Springer (2006), IV.3.1.4.
-/

public section

open scoped CStarAlgebra ComplexOrder

namespace TauCeti.CStarAlgebra

/-- `M_n × ℂ` as the finite direct sum `Π i : Fin 2, M_{k i}` with `k = ![n, 1]`. -/
private noncomputable def prodComplexStarAlgEquiv (n : ℕ) :
    CStarMatrix (Fin n) (Fin n) ℂ × ℂ ≃⋆ₐ[ℂ]
      ∀ i : Fin 2, CStarMatrix (Fin (![n, 1] i)) (Fin (![n, 1] i)) ℂ where
  toFun p := Fin.cons p.1 (Fin.cons (CStarMatrix.toOneByOne (Fin 1) ℂ ℂ p.2) finZeroElim)
  invFun x := (x 0, (CStarMatrix.toOneByOne (Fin 1) ℂ ℂ).symm (x 1))
  left_inv p := Prod.ext rfl ((CStarMatrix.toOneByOne (Fin 1) ℂ ℂ).symm_apply_apply p.2)
  right_inv x := funext fun i ↦ by
    fin_cases i
    · rfl
    · exact (CStarMatrix.toOneByOne (Fin 1) ℂ ℂ).apply_symm_apply (x 1)
  map_mul' p q := funext fun i ↦ by
    fin_cases i
    · rfl
    · exact map_mul (CStarMatrix.toOneByOne (Fin 1) ℂ ℂ) p.2 q.2
  map_add' p q := funext fun i ↦ by
    fin_cases i
    · rfl
    · exact map_add (CStarMatrix.toOneByOne (Fin 1) ℂ ℂ) p.2 q.2
  map_star' p := funext fun i ↦ by
    fin_cases i
    · rfl
    · change CStarMatrix.toOneByOne (Fin 1) ℂ ℂ (star p.2) =
        star (CStarMatrix.toOneByOne (Fin 1) ℂ ℂ p.2)
      exact (CStarMatrix.toOneByOne (Fin 1) ℂ ℂ).map_star' p.2
  map_smul' c p := funext fun i ↦ by
    fin_cases i
    · rfl
    · exact map_smul (CStarMatrix.toOneByOne (Fin 1) ℂ ℂ) c p.2

/-- The unitization `M_n⁺¹ ≅ M_n × ℂ` of a full matrix algebra is nuclear. -/
private theorem isNuclear_unitization_cstarMatrix (n : ℕ) :
    IsNuclear (CStarMatrix (Fin n) (Fin n) ℂ)⁺¹ :=
  .of_starAlgEquiv ((Unitization.prodStarAlgEquiv ℂ _).trans (prodComplexStarAlgEquiv n))

end TauCeti.CStarAlgebra

namespace CompletelyPositiveMap

variable {A B C : Type*}
  [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NonUnitalCStarAlgebra C] [PartialOrder C] [StarOrderedRing C]

/-- The unital extension of a completely positive contraction is a contraction. -/
theorem norm_unitization_apply_le (φ : A →CP B) (hφ : ∀ a, ‖φ a‖ ≤ ‖a‖) (x : A⁺¹) :
    ‖φ.unitization hφ x‖ ≤ ‖x‖ :=
  (CompletelyPositiveMapClass.norm_map_one_le_one_iff _).1
    (by rw [unitization_apply_one]; exact CStarRing.norm_one_le) x

/-- The unital extension of a composite is the composite of the unital extensions. -/
theorem unitization_comp (φ : A →CP B) (ψ : B →CP C) (hφ : ∀ a, ‖φ a‖ ≤ ‖a‖)
    (hψ : ∀ b, ‖ψ b‖ ≤ ‖b‖) (h : ∀ a, ‖ψ.comp φ a‖ ≤ ‖a‖) :
    (ψ.comp φ).unitization h = (ψ.unitization hψ).comp (φ.unitization hφ) := by
  ext x <;> simp

/-- **Unitization of nuclear contractions.** The unital extension `λ + a ↦ λ + φ a` of a nuclear
contraction `φ` is a nuclear contraction. -/
theorem IsNuclearContraction.unitization {φ : A →CP B} (h : φ.IsNuclearContraction) :
    (φ.unitization h.norm_apply_le).IsNuclearContraction := by
  classical
  refine IsNuclearContraction.of_forall_exists fun F ε hε ↦ ?_
  obtain ⟨n, α, β, hα, hβ, hF⟩ :=
    isNuclearContraction_iff.1 h (F.image fun x : A⁺¹ ↦ x.snd) ε hε
  have hid := (TauCeti.CStarAlgebra.isNuclear_unitization_cstarMatrix n).isNuclearContraction_id
  refine ⟨(β.unitization hβ).comp (α.unitization hα), ?_, fun x hx ↦ ?_⟩
  · simpa using (hid.comp_right _ (norm_unitization_apply_le α hα)).comp_left _
      (norm_unitization_apply_le β hβ)
  · have hx' : ((β (α x.snd) - φ x.snd : B) : B⁺¹) =
        ((β.unitization hβ).comp (α.unitization hα)) x - φ.unitization h.norm_apply_le x := by
      ext <;> simp
    rw [← hx', Unitization.norm_inr]
    exact hF _ (Finset.mem_image_of_mem _ hx)

end CompletelyPositiveMap

namespace TauCeti.CStarAlgebra

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- **The unitization of a nuclear C⋆-algebra is nuclear.** The unital extension of the identity
of `A` is the identity of `A⁺¹`. -/
instance isNuclear_unitization [IsNuclear A] : IsNuclear A⁺¹ := by
  refine ⟨?_⟩
  convert (IsNuclear.isNuclearContraction_id (A := A)).unitization using 1
  ext x <;> simp

end TauCeti.CStarAlgebra
