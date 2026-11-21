/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Ideal
public import TauCeti.Analysis.CStarAlgebra.Representation.Multiplier

/-!
# Extensions of Hilbert-space representations from closed ideals

Composing `π.nonUnitalMultiplierExtension : 𝓜(ℂ, I) →⋆ₙₐ[ℂ] (H →L[ℂ] H)` with the canonical
multiplier homomorphism `I.multiplierHom hmul : A →⋆ₙₐ[ℂ] 𝓜(ℂ, I)` extends any (possibly
degenerate) Hilbert-space representation `π : I →⋆ₙₐ[ℂ] (H →L[ℂ] H)` of a closed two-sided star
ideal `I` of a C⋆-algebra `A` to a representation `π.idealExtension hmul : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)`
on the *same* Hilbert space `H`, with the same essential subspace. Keeping the ambient Hilbert
space unchanged allows covariant representations of C⋆-dynamical systems on closed invariant ideals
to extend with the same unitary group representation.

## Main definitions and results

* `NonUnitalStarAlgHom.idealExtension`: extension of a representation `π : I →⋆ₙₐ[ℂ] (H →L[ℂ] H)`
  of a closed two-sided star ideal `I` of `A` to `A →⋆ₙₐ[ℂ] (H →L[ℂ] H)` on the same `H`, with
  `idealExtension_coe` and `idealExtension_comp_subtype`.
* `NonUnitalStarAlgHom.eq_idealExtension_iff` and
  `NonUnitalStarAlgHom.eq_idealExtension_of_apply_coe`: uniqueness characterizations of the
  extended representation.
* `NonUnitalStarAlgHom.essentialSubspace_idealExtension` and
  `NonUnitalStarAlgHom.isNondegenerate_idealExtension_iff`: preservation of essential subspaces and
  nondegeneracy.
* `NonUnitalStarAlgHom.commute_nonUnitalMultiplierExtension_one`: the essential projection of a
  representation restricted to a closed two-sided star ideal commutes with every ambient operator.

## References

* Jacques Dixmier, *C*-Algebras*, Proposition 2.10.4.
* Iain Raeburn and Dana Williams, *Morita Equivalence and Continuous-Trace C*-Algebras*,
  Propositions 2.50 and 2.54.
* Dana Williams, *Crossed Products of C*-Algebras*, Proposition 3.19.
-/

public section

noncomputable section

open scoped InnerProductSpace

namespace NonUnitalStarAlgHom

section IdealExtension

variable {A H : Type*} [NonUnitalCStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {I : NonUnitalStarSubalgebra ℂ A} [IsClosed (I : Set A)]
  (π : I →⋆ₙₐ[ℂ] (H →L[ℂ] H))

/-- Canonical extension of a (possibly degenerate) Hilbert-space representation
`π : I →⋆ₙₐ[ℂ] (H →L[ℂ] H)` of a closed two-sided star ideal `I` of `A` to a representation of `A`
on the same Hilbert space `H`. -/
def idealExtension (hmul : ∀ a : A, ∀ x ∈ I, a * x ∈ I) : A →⋆ₙₐ[ℂ] (H →L[ℂ] H) :=
  π.nonUnitalMultiplierExtension.comp (I.multiplierHom hmul)

variable {π}

/-- `π.idealExtension hmul` extends `π` on elements of `I`. -/
@[simp]
theorem idealExtension_coe (hmul : ∀ a : A, ∀ x ∈ I, a * x ∈ I) (x : I) :
    π.idealExtension hmul (x : A) = π x := by
  simp [idealExtension]

/-- Composing `π.idealExtension hmul` with the subtype inclusion of `I` recovers `π`. -/
@[simp]
theorem idealExtension_comp_subtype (hmul : ∀ a : A, ∀ x ∈ I, a * x ∈ I) :
    (π.idealExtension hmul).comp (NonUnitalStarSubalgebraClass.subtype I) = π :=
  NonUnitalStarAlgHom.ext (π.idealExtension_coe hmul)

/-- Left-multiplication formula `(π.idealExtension hmul a) * π x = π ⟨a * x, _⟩`. -/
@[simp]
theorem idealExtension_mul_eq (hmul : ∀ a : A, ∀ x ∈ I, a * x ∈ I) (a : A) (x : I) :
    π.idealExtension hmul a * π x = π ⟨a * x, hmul a x x.property⟩ := by
  simp [idealExtension]

/-- Right-multiplication formula `π x * (π.idealExtension hmul a) = π ⟨x * a, _⟩`. -/
@[simp]
theorem mul_idealExtension_eq (hmul : ∀ a : A, ∀ x ∈ I, a * x ∈ I) (a : A) (x : I) :
    π x * π.idealExtension hmul a =
      π ⟨x * a, StarMemClass.mul_mem_right_of_mul_mem_left hmul a x.property⟩ := by
  simp [idealExtension]

/-- Action of `π.idealExtension hmul a` on vectors of the form `π x ξ`. -/
@[simp]
theorem idealExtension_apply_apply (hmul : ∀ a : A, ∀ x ∈ I, a * x ∈ I) (a : A) (x : I) (ξ : H) :
    π.idealExtension hmul a (π x ξ) = π ⟨a * x, hmul a x x.property⟩ ξ := by
  simp [idealExtension]

/-- `π.idealExtension hmul a` vanishes on `π.essentialSubspaceᗮ`. -/
theorem idealExtension_apply_eq_zero (hmul : ∀ a : A, ∀ x ∈ I, a * x ∈ I) (a : A) {ξ : H}
    (hξ : ξ ∈ π.essentialSubspaceᗮ) : π.idealExtension hmul a ξ = 0 :=
  π.nonUnitalMultiplierExtension_apply_eq_zero _ hξ

/-- Every operator `π.idealExtension hmul a` maps `H` into `π.essentialSubspace`. -/
theorem idealExtension_apply_mem_essentialSubspace (hmul : ∀ a : A, ∀ x ∈ I, a * x ∈ I)
    (a : A) (ξ : H) : π.idealExtension hmul a ξ ∈ π.essentialSubspace :=
  π.nonUnitalMultiplierExtension_apply_mem_essentialSubspace _ ξ

/-- Uniqueness characterization of `π.idealExtension hmul a` on `H`. -/
theorem eq_idealExtension_iff (hmul : ∀ a : A, ∀ x ∈ I, a * x ∈ I) {a : A} {T : H →L[ℂ] H} :
    T = π.idealExtension hmul a ↔
      (∀ x : I, T * π x = π ⟨a * x, hmul a x x.property⟩) ∧ (∀ ξ ∈ π.essentialSubspaceᗮ, T ξ = 0)
          := by
  rw [idealExtension, NonUnitalStarAlgHom.comp_apply, π.eq_nonUnitalMultiplierExtension_iff]
  simp only [I.multiplierHom_fst_apply]

/-- Extending a representation from a closed ideal preserves its essential subspace. -/
@[simp]
theorem essentialSubspace_idealExtension (hmul : ∀ a : A, ∀ x ∈ I, a * x ∈ I) :
    (π.idealExtension hmul).essentialSubspace = π.essentialSubspace := by
  apply le_antisymm
  · exact (π.idealExtension hmul).essentialSubspace_le_iff π.isClosed_essentialSubspace |>.2
      (π.idealExtension_apply_mem_essentialSubspace hmul)
  · exact π.essentialSubspace_le_iff (π.idealExtension hmul).isClosed_essentialSubspace |>.2
      fun x ξ => by
        rw [← π.idealExtension_coe hmul x]
        exact (π.idealExtension hmul).apply_mem_essentialSubspace (x : A) ξ

/-- The extended representation on `A` is nondegenerate if and only if `π` is nondegenerate on
`I`. -/
@[simp]
theorem isNondegenerate_idealExtension_iff (hmul : ∀ a : A, ∀ x ∈ I, a * x ∈ I) :
    (π.idealExtension hmul).IsNondegenerate ↔ π.IsNondegenerate := by
  rw [isNondegenerate_iff_essentialSubspace_eq_top, isNondegenerate_iff_essentialSubspace_eq_top,
    π.essentialSubspace_idealExtension hmul]

/-- When `π` is nondegenerate on `I`, `π.idealExtension hmul` is the unique multiplicative map
`A → (H →L[ℂ] H)` extending `π`. -/
theorem eq_idealExtension_of_apply_coe (hπ : π.IsNondegenerate)
    (hmul : ∀ a : A, ∀ x ∈ I, a * x ∈ I) {F : Type*} [FunLike F A (H →L[ℂ] H)]
    [MulHomClass F A (H →L[ℂ] H)] (ψ : F) (hψ : ∀ x : I, ψ x = π x) :
    ⇑ψ = π.idealExtension hmul := by
  funext a
  refine (π.eq_idealExtension_iff hmul).2 ⟨fun x => ?_, fun ξ hξ => ?_⟩
  · rw [← hψ, ← map_mul, ← hψ ⟨a * x, hmul a x x.property⟩]
  · rw [π.orthogonal_essentialSubspace_eq_bot_of_isNondegenerate hπ, Submodule.mem_bot] at hξ
    simp [hξ]

/-- For a Hilbert-space representation `π` of `A` restricted to a closed two-sided star ideal `I`,
the orthogonal projection `πS.nonUnitalMultiplierExtension 1` onto the essential subspace of
`πS := π.comp (NonUnitalStarSubalgebraClass.subtype I)` commutes with every `π a`. -/
theorem commute_nonUnitalMultiplierExtension_one
    (hmul : ∀ a : A, ∀ x ∈ I, a * x ∈ I) (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (a : A) :
    Commute
      ((π.comp (NonUnitalStarSubalgebraClass.subtype I)).nonUnitalMultiplierExtension 1)
      (π a) := by
  let πS : I →⋆ₙₐ[ℂ] (H →L[ℂ] H) := π.comp (NonUnitalStarSubalgebraClass.subtype I)
  let P : H →L[ℂ] H := πS.nonUnitalMultiplierExtension 1
  let T : H →L[ℂ] H := π a
  have hmul_left : ∀ x : I, T * πS x = πS ⟨a * (x : A), hmul a x x.property⟩ := fun x => by
    simp only [T, πS, NonUnitalStarAlgHom.comp_apply, NonUnitalStarSubalgebraClass.coe_subtype,
      ← map_mul]
  have hmul_right : ∀ x : I,
      πS x * T = πS ⟨(x : A) * a, StarMemClass.mul_mem_right_of_mul_mem_left hmul a x.property⟩ :=
    fun x => by
      simp only [T, πS, NonUnitalStarAlgHom.comp_apply, NonUnitalStarSubalgebraClass.coe_subtype,
        ← map_mul]
  refine πS.ext_of_orthogonal_essentialSubspace (fun x => ?_) (fun η hη => ?_)
  · rw [mul_assoc, hmul_left x, mul_assoc]
    have hPmul : ∀ y : I, P * πS y = πS y := fun y => by
      simpa [P, DoubleCentralizer.one_fst] using πS.nonUnitalMultiplierExtension_mul_eq_fst 1 y
    rw [hPmul, hPmul, hmul_left x]
  · have hTη : T η ∈ πS.essentialSubspaceᗮ := by
      rw [πS.mem_orthogonal_essentialSubspace_iff]
      intro x
      rw [← mul_apply_eq_comp, hmul_right x]
      exact πS.apply_eq_zero_of_mem_orthogonal_essentialSubspace hη _
    rw [mul_apply_eq_comp, mul_apply_eq_comp,
      πS.nonUnitalMultiplierExtension_apply_eq_zero 1 hTη,
      πS.nonUnitalMultiplierExtension_apply_eq_zero 1 hη, map_zero]

end IdealExtension

end NonUnitalStarAlgHom
