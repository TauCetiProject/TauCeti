/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.GNS.Nondegenerate
import TauCeti.Analysis.CStarAlgebra.Representation.HilbertSum
import TauCeti.Analysis.CStarAlgebra.State.Spectrum

/-!
# Norm recovery, point separation and the Gelfand–Naimark theorem

Applying the GNS construction to a norm-attaining positive functional on `a * star a`
(`TauCeti.CStarAlgebra.exists_positiveContinuousLinearMap_apply_mul_self_eq_norm_sq`) gives, for
every `a` in a possibly nonunital C⋆-algebra `A`, a positive functional whose GNS representation
preserves the norm of `a` (`exists_norm_gnsNonUnitalStarAlgHom_apply_eq`). Since GNS
representations are nondegenerate (`PositiveLinearMap.isNondegenerate_gnsNonUnitalStarAlgHom`),
nondegenerate representations on Hilbert spaces in `A`'s universe recover norms and separate points
in `A` (`norm_le_iff_forall_isNondegenerate`, `eq_iff_forall_isNondegenerate`) and `𝓜(ℂ, A)`
(`DoubleCentralizer.norm_le_iff_forall_isNondegenerate`,
`DoubleCentralizer.eq_iff_forall_multiplierExtension_eq`).

The Hilbert direct sum `NonUnitalStarAlgHom.hilbertSum` of the GNS representations of all positive
functionals is therefore a single faithful nondegenerate representation: this is the
**Gelfand–Naimark theorem** `exists_faithful_nondegenerate_representation`, for every C⋆-algebra,
with no unit or separability assumption. For a unital algebra nondegeneracy forces the unit to act
as the identity, giving a faithful unital representation (`exists_faithful_representation`).
Faithful star homomorphisms between C⋆-algebras are isometric (`NonUnitalStarAlgHom.norm_map`), so
these representations embed `A` isometrically as a C⋆-subalgebra of bounded operators.

## References

* G. J. Murphy, *C⋆-Algebras and Operator Theory*, Section 3.4 (Theorem 3.4.1).
* J. Peterson, *Notes on von Neumann algebras*, Propositions 4.1.4–4.1.5, Theorem 4.1.6 and
  Corollary 4.1.7.
* Dana Williams, *Crossed Products of C*-Algebras*, Section 1.1 and Appendix A.
-/

public section

noncomputable section

open scoped CStarAlgebra ComplexOrder MultiplierAlgebra

universe w

namespace TauCeti.CStarAlgebra

variable {A : Type w} [NonUnitalCStarAlgebra A]

/-- **Norm-attaining GNS representations.** Every element `a` of a C⋆-algebra has a positive
functional `f` whose GNS representation preserves its norm: `‖π_f a‖ = ‖a‖`. -/
theorem exists_norm_gnsNonUnitalStarAlgHom_apply_eq [PartialOrder A] [StarOrderedRing A] (a : A) :
    ∃ f : A →ₚ[ℂ] ℂ, ‖f.gnsNonUnitalStarAlgHom a‖ = ‖a‖ := by
  rcases eq_or_ne a 0 with rfl | ha0
  · exact ⟨0, by simp⟩
  have : Nontrivial A := ⟨a, 0, ha0⟩
  have hx : 0 ≤ a * star a := by simp
  obtain ⟨ω, -, hω1, hω2⟩ := exists_positiveContinuousLinearMap_apply_mul_self_eq_norm_sq hx
  let f := ω.toPositiveLinearMap
  have hζ : ‖f.toGNS (star a)‖ = ‖a‖ := by
    simp [f, PositiveLinearMap.preGNS_norm_def', hω1, CStarRing.norm_self_mul_star]
  have hρζ : ‖f.gnsNonUnitalStarAlgHom a (f.toGNS (star a))‖ = ‖a‖ * ‖a‖ := by
    simp [f, PositiveLinearMap.preGNS_norm_def', hx.isSelfAdjoint.star_eq, hω2,
      CStarRing.norm_self_mul_star, Real.sqrt_sq (mul_self_nonneg ‖a‖)]
  refine ⟨f, le_antisymm (NonUnitalStarAlgHom.norm_apply_le _ a) ?_⟩
  refine le_of_mul_le_mul_right ?_ (norm_pos_iff.2 ha0)
  rw [← hρζ, ← hζ]
  exact (f.gnsNonUnitalStarAlgHom a).le_opNorm _

/-- The norm of `a : A` is bounded by `c` if and only if `‖ρ a‖ ≤ c` for every nondegenerate
representation `ρ` on a Hilbert space in the same universe. -/
theorem norm_le_iff_forall_isNondegenerate {a : A} {c : ℝ} :
    ‖a‖ ≤ c ↔ ∀ (H : Type w) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
      (ρ : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)), ρ.IsNondegenerate → ‖ρ a‖ ≤ c := by
  refine ⟨fun h H _ _ _ ρ _ => (NonUnitalStarAlgHom.norm_apply_le ρ a).trans h, fun h => ?_⟩
  let := _root_.CStarAlgebra.spectralOrder A
  have := _root_.CStarAlgebra.spectralOrderedRing A
  obtain ⟨f, hf⟩ := exists_norm_gnsNonUnitalStarAlgHom_apply_eq a
  exact hf ▸ h f.GNS f.gnsNonUnitalStarAlgHom f.isNondegenerate_gnsNonUnitalStarAlgHom

/-- Two elements in a possibly nonunital C⋆-algebra `A` are equal if and only if they agree under
every nondegenerate Hilbert-space representation of `A` in the same universe. -/
theorem eq_iff_forall_isNondegenerate {a b : A} :
    a = b ↔ ∀ (H : Type w) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
      (ρ : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)), ρ.IsNondegenerate → ρ a = ρ b :=
  ⟨fun h _ _ _ _ _ _ => h ▸ rfl, fun h => sub_eq_zero.1 <| norm_le_zero_iff.1 <|
    norm_le_iff_forall_isNondegenerate.2 fun H _ _ _ ρ hρ => by simp [map_sub, h H ρ hρ]⟩

variable (A) in
/-- **Gelfand–Naimark theorem.** Every C⋆-algebra `A`, possibly nonunital and nonseparable, has a
faithful nondegenerate representation on a Hilbert space in the universe of `A`: the Hilbert
direct sum of the GNS representations of all positive functionals on `A`. For the zero algebra the
Hilbert space is zero. -/
theorem exists_faithful_nondegenerate_representation :
    ∃ (H : Type w) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H) (_ : CompleteSpace H)
      (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)), Function.Injective π ∧ π.IsNondegenerate := by
  let := _root_.CStarAlgebra.spectralOrder A
  have := _root_.CStarAlgebra.spectralOrderedRing A
  let π := NonUnitalStarAlgHom.hilbertSum fun f : A →ₚ[ℂ] ℂ => f.gnsNonUnitalStarAlgHom
  refine ⟨_, inferInstance, inferInstance, inferInstance, π, ?_, ?_⟩
  · refine (NonUnitalStarAlgHom.injective_hilbertSum_iff _).2 fun a ha => ?_
    obtain ⟨f, hf⟩ := exists_norm_gnsNonUnitalStarAlgHom_apply_eq a
    simpa [ha f] using hf.symm
  · exact (NonUnitalStarAlgHom.isNondegenerate_hilbertSum_iff _).2 fun f =>
      f.isNondegenerate_gnsNonUnitalStarAlgHom

variable (B : Type w) [CStarAlgebra B] in
/-- **Gelfand–Naimark theorem, unital form.** Every unital C⋆-algebra `B` has a faithful unital
representation on a Hilbert space in the universe of `B`. -/
theorem exists_faithful_representation :
    ∃ (H : Type w) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H) (_ : CompleteSpace H)
      (π : B →⋆ₐ[ℂ] (H →L[ℂ] H)), Function.Injective π := by
  obtain ⟨H, _, _, _, π, hπ, hπn⟩ := exists_faithful_nondegenerate_representation B
  exact ⟨H, _, _, _, hπn.toStarAlgHom, by rwa [hπn.coe_toStarAlgHom]⟩

end TauCeti.CStarAlgebra

namespace DoubleCentralizer

variable {A : Type w} [NonUnitalCStarAlgebra A]

/-- The norm of `m : 𝓜(ℂ, A)` is bounded by `c` if and only if `‖ρ.multiplierExtension hρ m‖ ≤ c`
for every nondegenerate representation `ρ` of `A` on a Hilbert space in the same universe. -/
theorem norm_le_iff_forall_isNondegenerate {m : 𝓜(ℂ, A)} {c : ℝ} :
    ‖m‖ ≤ c ↔ ∀ (H : Type w) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
      (ρ : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (hρ : ρ.IsNondegenerate),
        ‖ρ.multiplierExtension hρ m‖ ≤ c := by
  refine ⟨fun h H _ _ _ ρ hρ =>
    (NonUnitalStarAlgHom.norm_apply_le (ρ.multiplierExtension hρ).toNonUnitalStarAlgHom m).trans h,
    fun h => ?_⟩
  have hc : 0 ≤ c := by
    simpa using (TauCeti.CStarAlgebra.norm_le_iff_forall_isNondegenerate (a := (0 : A))).2
      fun H _ _ _ ρ hρ => by simpa using (norm_nonneg _).trans (h H ρ hρ)
  rw [← norm_fst]
  refine m.fst.opNorm_le_bound hc fun a =>
    TauCeti.CStarAlgebra.norm_le_iff_forall_isNondegenerate.2 fun H _ _ _ ρ hρ => ?_
  rw [← ρ.multiplierExtension_mul_eq_fst hρ]
  exact (norm_mul_le _ _).trans <|
    mul_le_mul (h H ρ hρ) (NonUnitalStarAlgHom.norm_apply_le ρ a) (norm_nonneg _) hc

/-- Two multipliers in `𝓜(ℂ, A)` are equal if and only if they agree under the multiplier
extension of every nondegenerate Hilbert-space representation of `A` in the same universe. -/
theorem eq_iff_forall_multiplierExtension_eq {m n : 𝓜(ℂ, A)} :
    m = n ↔ ∀ (H : Type w) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
      (ρ : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (hρ : ρ.IsNondegenerate),
        ρ.multiplierExtension hρ m = ρ.multiplierExtension hρ n :=
  ⟨fun h _ _ _ _ _ _ => h ▸ rfl, fun h => sub_eq_zero.1 <| norm_le_zero_iff.1 <|
    norm_le_iff_forall_isNondegenerate.2 fun H _ _ _ ρ hρ => by simp [map_sub, h H ρ hρ]⟩

end DoubleCentralizer
