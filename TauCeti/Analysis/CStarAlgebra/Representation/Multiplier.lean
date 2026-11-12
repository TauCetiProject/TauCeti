/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Representation.EssentialSubspace

/-!
# Multiplier extensions of possibly degenerate representations

Extending the nondegenerate compression `π.restrictEssentialSubspace` of a Hilbert-space
representation `π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)` to `𝓜(ℂ, A)` via
`NonUnitalStarAlgHom.multiplierExtension` and composing with `π.essentialSubspace.extendByZero`
produces a canonical nonunital star-algebra homomorphism
`π.nonUnitalMultiplierExtension : 𝓜(ℂ, A) →⋆ₙₐ[ℂ] (H →L[ℂ] H)` on the *same* Hilbert space `H`.
It sends `1 : 𝓜(ℂ, A)` to `π.essentialSubspace.starProjection`, converges strongly along any
increasing approximate unit of `A`, and agrees with `π.multiplierExtension hπ` whenever `π` is
nondegenerate.

## Main definitions and results

* `NonUnitalStarAlgHom.nonUnitalMultiplierExtension`: the canonical extension
  `𝓜(ℂ, A) →⋆ₙₐ[ℂ] (H →L[ℂ] H)` of a possibly degenerate representation, uniquely characterized
  by `eq_nonUnitalMultiplierExtension_iff`, sending `1` to `π.essentialSubspace.starProjection`,
  converging strongly along increasing approximate units
  (`tendsto_nonUnitalMultiplierExtension_apply`), and agreeing with `π.multiplierExtension` when
  `π.IsNondegenerate`.

## References

* Iain Raeburn and Dana Williams, *Morita Equivalence and Continuous-Trace C*-Algebras*,
  Proposition 2.50.
* Dana Williams, *Crossed Products of C*-Algebras*, Section 1.1.
-/

public section

noncomputable section

open Filter Topology
open scoped MultiplierAlgebra InnerProductSpace

namespace NonUnitalStarAlgHom

variable {A H : Type*} [NonUnitalCStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)}

variable (π) in
/-- Canonical extension of a (possibly degenerate) representation `π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)` to
the multiplier algebra `𝓜(ℂ, A)` on the *same* Hilbert space `H`, obtained by extending the
nondegenerate compression `π.restrictEssentialSubspace` to `𝓜(ℂ, A)` and extending by zero on
`π.essentialSubspaceᗮ`. -/
def nonUnitalMultiplierExtension : 𝓜(ℂ, A) →⋆ₙₐ[ℂ] (H →L[ℂ] H) :=
  π.essentialSubspace.extendByZero.comp
    (π.restrictEssentialSubspace.multiplierExtension
      π.isNondegenerate_restrictEssentialSubspace).toNonUnitalStarAlgHom

/-- Explicit formula for `π.nonUnitalMultiplierExtension` as extension by zero of the multiplier
extension on `π.essentialSubspace`. -/
theorem nonUnitalMultiplierExtension_eq_extendByZero (m : 𝓜(ℂ, A)) :
    π.nonUnitalMultiplierExtension m =
      π.essentialSubspace.extendByZero
        (π.restrictEssentialSubspace.multiplierExtension
          π.isNondegenerate_restrictEssentialSubspace m) :=
  (rfl)

/-- Defining left-multiplication identity for `π.nonUnitalMultiplierExtension`. -/
@[simp]
theorem nonUnitalMultiplierExtension_mul_eq_fst (m : 𝓜(ℂ, A)) (a : A) :
    π.nonUnitalMultiplierExtension m * π a = π (m.fst a) := by
  rw [nonUnitalMultiplierExtension_eq_extendByZero, ← π.extendByZero_restrictEssentialSubspace a,
    ← map_mul, multiplierExtension_mul_eq_fst, π.extendByZero_restrictEssentialSubspace]

/-- Right-multiplication identity for `π.nonUnitalMultiplierExtension`. -/
@[simp]
theorem mul_nonUnitalMultiplierExtension_eq_snd (m : 𝓜(ℂ, A)) (a : A) :
    π a * π.nonUnitalMultiplierExtension m = π (m.snd a) := by
  rw [nonUnitalMultiplierExtension_eq_extendByZero, ← π.extendByZero_restrictEssentialSubspace a,
    ← map_mul, mul_multiplierExtension_eq_snd, π.extendByZero_restrictEssentialSubspace]

/-- `π.nonUnitalMultiplierExtension m` sends `π a ξ` to `π (m.fst a) ξ`. -/
@[simp]
theorem nonUnitalMultiplierExtension_apply_apply (m : 𝓜(ℂ, A)) (a : A) (ξ : H) :
    π.nonUnitalMultiplierExtension m (π a ξ) = π (m.fst a) ξ :=
  congr($(π.nonUnitalMultiplierExtension_mul_eq_fst m a) ξ)

/-- `π.nonUnitalMultiplierExtension m` vanishes on `π.essentialSubspaceᗮ`. -/
theorem nonUnitalMultiplierExtension_apply_eq_zero (m : 𝓜(ℂ, A)) {ξ : H}
    (hξ : ξ ∈ π.essentialSubspaceᗮ) : π.nonUnitalMultiplierExtension m ξ = 0 :=
  π.essentialSubspace.extendByZero_apply_of_mem_orthogonal _ hξ

/-- Every operator `π.nonUnitalMultiplierExtension m` maps `H` into `π.essentialSubspace`. -/
theorem nonUnitalMultiplierExtension_apply_mem_essentialSubspace (m : 𝓜(ℂ, A)) (ξ : H) :
    π.nonUnitalMultiplierExtension m ξ ∈ π.essentialSubspace :=
  π.essentialSubspace.extendByZero_apply_mem _ ξ

/-- Uniqueness characterization of `π.nonUnitalMultiplierExtension m`. -/
theorem eq_nonUnitalMultiplierExtension_iff {m : 𝓜(ℂ, A)} {T : H →L[ℂ] H} :
    T = π.nonUnitalMultiplierExtension m ↔
      (∀ a, T * π a = π (m.fst a)) ∧ (∀ ξ ∈ π.essentialSubspaceᗮ, T ξ = 0) :=
  ⟨fun h => h ▸ ⟨π.nonUnitalMultiplierExtension_mul_eq_fst m,
      fun _ hξ => π.nonUnitalMultiplierExtension_apply_eq_zero m hξ⟩,
    fun ⟨hmul, horth⟩ => π.ext_of_orthogonal_essentialSubspace
      (fun a => by rw [hmul, π.nonUnitalMultiplierExtension_mul_eq_fst])
      (fun ξ hξ => by rw [horth ξ hξ, π.nonUnitalMultiplierExtension_apply_eq_zero m hξ])⟩

/-- `π.nonUnitalMultiplierExtension` restricts to `π` on `A`. -/
@[simp]
theorem nonUnitalMultiplierExtension_coe (a : A) :
    π.nonUnitalMultiplierExtension (a : 𝓜(ℂ, A)) = π a := by
  simp [nonUnitalMultiplierExtension]

/-- `π.nonUnitalMultiplierExtension` sends `1 : 𝓜(ℂ, A)` to the orthogonal projection onto
`π.essentialSubspace`. -/
@[simp]
theorem nonUnitalMultiplierExtension_one :
    π.nonUnitalMultiplierExtension 1 = π.essentialSubspace.starProjection := by
  simp [nonUnitalMultiplierExtension]

/-- Along any increasing approximate unit `e`, `π (m.fst e)` converges strongly on all of `H` to
`π.nonUnitalMultiplierExtension m`. -/
theorem tendsto_nonUnitalMultiplierExtension_apply [PartialOrder A] {l : Filter A}
    (hl : l.IsIncreasingApproximateUnit) (m : 𝓜(ℂ, A)) (ξ : H) :
    Tendsto (fun e => π (m.fst e) ξ) l (𝓝 (π.nonUnitalMultiplierExtension m ξ)) := by
  rw [π.nonUnitalMultiplierExtension_eq_extendByZero, Submodule.extendByZero_apply]
  have hlim := (π.essentialSubspace.subtypeL.continuous.tendsto _).comp
    (tendsto_multiplierExtension_apply π.isNondegenerate_restrictEssentialSubspace hl m
      (π.essentialSubspace.orthogonalProjectionOnto ξ))
  refine hlim.congr fun e => ?_
  calc (π.restrictEssentialSubspace (m.fst e)
        (π.essentialSubspace.orthogonalProjectionOnto ξ) : H)
      = π (m.fst e) (π.essentialSubspace.starProjection ξ) +
          π (m.fst e) (ξ - π.essentialSubspace.starProjection ξ) := by
        rw [π.coe_restrictEssentialSubspace_apply, Submodule.coe_orthogonalProjectionOnto_apply,
          π.apply_eq_zero_of_mem_orthogonal_essentialSubspace
            (π.essentialSubspace.sub_starProjection_mem_orthogonal ξ), add_zero]
    _ = π (m.fst e) ξ := by rw [← map_add, add_sub_cancel]

/-- Strict left continuity of a norm-bounded family of multipliers implies strong continuity under
`π.nonUnitalMultiplierExtension`. -/
theorem continuous_nonUnitalMultiplierExtension_apply {X : Type*} [TopologicalSpace X]
    {u : X → 𝓜(ℂ, A)} (hu : ∀ a, Continuous fun x => (u x).fst a) {C : ℝ}
    (hC : ∀ x, ‖u x‖ ≤ C) (ξ : H) :
    Continuous fun x => π.nonUnitalMultiplierExtension (u x) ξ := by
  simp_rw [π.nonUnitalMultiplierExtension_eq_extendByZero, Submodule.extendByZero_apply]
  exact π.essentialSubspace.subtypeL.continuous.comp <|
    continuous_multiplierExtension_apply π.isNondegenerate_restrictEssentialSubspace
      hu hC (π.essentialSubspace.orthogonalProjectionOnto ξ)

/-- When `π` is nondegenerate, `π.nonUnitalMultiplierExtension` agrees with the unital extension
`π.multiplierExtension hπ`. -/
theorem nonUnitalMultiplierExtension_eq_multiplierExtension (hπ : π.IsNondegenerate)
    (m : 𝓜(ℂ, A)) : π.nonUnitalMultiplierExtension m = π.multiplierExtension hπ m :=
  (eq_multiplierExtension_iff hπ).2 (π.nonUnitalMultiplierExtension_mul_eq_fst m)

end NonUnitalStarAlgHom
