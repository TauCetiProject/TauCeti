/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.GNS.Basic
public import TauCeti.Analysis.CStarAlgebra.PositiveLinearFunctional
public import TauCeti.Analysis.CStarAlgebra.Representation.Nondegenerate

/-!
# Nondegeneracy of GNS representations and norm recovery

For every positive linear functional `f` on a possibly nonunital C⋆-algebra `A`, Mathlib's GNS
representation `f.gnsNonUnitalStarAlgHom : A →⋆ₙₐ[ℂ] (f.GNS →L[ℂ] f.GNS)` is nondegenerate
(`PositiveLinearMap.isNondegenerate_gnsNonUnitalStarAlgHom`), and its multiplier extension acts on
classes `[b]` as `[m.fst b]` (`PositiveLinearMap.multiplierExtension_gnsNonUnitalStarAlgHom_toGNS`).

Applying this to a norm-attaining positive functional on `a * star a`
(`TauCeti.CStarAlgebra.exists_positiveContinuousLinearMap_apply_mul_self_eq_norm_sq`) shows that
nondegenerate representations in `A`'s universe recover norms in `A` and `𝓜(ℂ, A)`
(`TauCeti.CStarAlgebra.norm_le_iff_forall_isNondegenerate`,
`DoubleCentralizer.norm_le_iff_forall_isNondegenerate`) and separate points of `𝓜(ℂ, A)`
(`DoubleCentralizer.eq_iff_forall_multiplierExtension_eq`).

## References

* G. J. Murphy, *C⋆-Algebras and Operator Theory*, Section 3.4 (states attaining the norm and the
  Gelfand–Naimark theorem).
* Dana Williams, *Crossed Products of C*-Algebras*, Section 1.1 and Appendix A.
-/

public section

noncomputable section

open Filter Topology
open scoped CStarAlgebra ComplexOrder MultiplierAlgebra

namespace PositiveLinearMap

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  (f : A →ₚ[ℂ] ℂ)

/-- The GNS representation acts on classes `f.toGNS b` by left multiplication. -/
theorem gnsNonUnitalStarAlgHom_toGNS (a b : A) :
    f.gnsNonUnitalStarAlgHom a (f.toGNS b) = f.toGNS (a * b) := by simp

/-- The norm of `f.toGNS b` in the GNS Hilbert space is `√‖f (star b * b)‖`. -/
theorem norm_toGNS (b : A) : ‖f.toGNS b‖ = √‖f (star b * b)‖ := by simp [preGNS_norm_def']

/-- The GNS representation of any positive linear functional on a C⋆-algebra is nondegenerate. -/
theorem isNondegenerate_gnsNonUnitalStarAlgHom : f.gnsNonUnitalStarAlgHom.IsNondegenerate := by
  rw [NonUnitalStarAlgHom.isNondegenerate_iff_dense]
  have hl := CStarAlgebra.increasingApproximateUnit A
  have := hl.neBot
  refine dense_closure.1 (f.denseRange_toGNS.mono ?_)
  rintro _ ⟨b, rfl⟩
  exact mem_closure_of_tendsto ((f.toGNS.continuous.tendsto b).comp (hl.tendsto_mul_right b)) <|
    .of_forall fun e => Submodule.subset_span <| Set.mem_iUnion.2 ⟨e, f.toGNS b, by simp⟩

/-- The multiplier extension of the GNS representation sends `f.toGNS b` to `f.toGNS (m.fst b)`. -/
theorem multiplierExtension_gnsNonUnitalStarAlgHom_toGNS (m : 𝓜(ℂ, A)) (b : A) :
    f.gnsNonUnitalStarAlgHom.multiplierExtension f.isNondegenerate_gnsNonUnitalStarAlgHom m
      (f.toGNS b) = f.toGNS (m.fst b) := by
  have hl := CStarAlgebra.increasingApproximateUnit A
  have := hl.neBot
  have hcont : Continuous fun x : A => f.toGNS (m.fst x) := by fun_prop
  exact tendsto_nhds_unique (f.gnsNonUnitalStarAlgHom.tendsto_multiplierExtension_apply
    f.isNondegenerate_gnsNonUnitalStarAlgHom hl m (f.toGNS b))
    (((hcont.tendsto b).comp (hl.tendsto_mul_right b)).congr fun e => by
      simp [DoubleCentralizer.fst_mul])

@[simp]
theorem multiplierExtension_gnsNonUnitalStarAlgHom_apply_coe (m : 𝓜(ℂ, A)) (b : A) :
    f.gnsNonUnitalStarAlgHom.multiplierExtension f.isNondegenerate_gnsNonUnitalStarAlgHom m
      (f.toPreGNS b : f.GNS) = (f.toPreGNS (m.fst b) : f.GNS) := by
  simpa only [toGNS_apply] using f.multiplierExtension_gnsNonUnitalStarAlgHom_toGNS m b

end PositiveLinearMap

namespace TauCeti.CStarAlgebra

universe w

variable {A : Type w} [NonUnitalCStarAlgebra A]

/-- The norm of an element `a : A` of a possibly nonunital C⋆-algebra is bounded by `c ≥ 0` if and
only if `‖ρ a‖ ≤ c` for every nondegenerate representation `ρ` on a Hilbert space in the same
universe. -/
theorem norm_le_iff_forall_isNondegenerate {a : A} {c : ℝ} (hc : 0 ≤ c) :
    ‖a‖ ≤ c ↔ ∀ (H : Type w) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
      (ρ : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)), ρ.IsNondegenerate → ‖ρ a‖ ≤ c := by
  refine ⟨fun h H _ _ _ ρ _ => (NonUnitalStarAlgHom.norm_apply_le ρ a).trans h, fun h => ?_⟩
  rcases eq_or_ne a 0 with rfl | ha0
  · simp [hc]
  have : Nontrivial A := ⟨a, 0, ha0⟩
  let := _root_.CStarAlgebra.spectralOrder A
  have := _root_.CStarAlgebra.spectralOrderedRing A
  have hx_nonneg : 0 ≤ a * star a := by simp
  have hx_norm : ‖a * star a‖ = ‖a‖ ^ 2 := by rw [CStarRing.norm_self_mul_star, sq]
  obtain ⟨ω, -, hω1, hω2⟩ := exists_positiveContinuousLinearMap_apply_mul_self_eq_norm_sq hx_nonneg
  let f : A →ₚ[ℂ] ℂ := ω
  have hζ : ‖f.toGNS (star a)‖ = ‖a‖ := by
    rw [f.norm_toGNS, star_star, show f (a * star a) = ω (a * star a) from rfl, hω1, hx_norm,
      Complex.norm_of_nonneg (sq_nonneg ‖a‖), Real.sqrt_sq (norm_nonneg a)]
  have hρζ : ‖f.gnsNonUnitalStarAlgHom a (f.toGNS (star a))‖ = ‖a‖ * ‖a‖ := by
    rw [f.gnsNonUnitalStarAlgHom_toGNS, f.norm_toGNS, hx_nonneg.isSelfAdjoint.star_eq,
      show f (a * star a * (a * star a)) = ω (a * star a * (a * star a)) from rfl, hω2, hx_norm,
      norm_pow, Complex.norm_of_nonneg (sq_nonneg ‖a‖), Real.sqrt_sq (sq_nonneg ‖a‖), sq]
  refine le_of_mul_le_mul_right ?_ (norm_pos_iff.2 ha0)
  rw [← hρζ, ← hζ]
  exact ((f.gnsNonUnitalStarAlgHom a).le_opNorm _).trans <| mul_le_mul_of_nonneg_right
    (h f.GNS f.gnsNonUnitalStarAlgHom f.isNondegenerate_gnsNonUnitalStarAlgHom) (norm_nonneg _)

end TauCeti.CStarAlgebra

namespace DoubleCentralizer

universe w

variable {A : Type w} [NonUnitalCStarAlgebra A]

/-- The norm of a multiplier `m : 𝓜(ℂ, A)` is bounded by `c ≥ 0` if and only if
`‖ρ.multiplierExtension hρ m‖ ≤ c` for every nondegenerate representation `ρ` of `A` on a Hilbert
space in the same universe. -/
theorem norm_le_iff_forall_isNondegenerate {m : 𝓜(ℂ, A)} {c : ℝ} (hc : 0 ≤ c) :
    ‖m‖ ≤ c ↔ ∀ (H : Type w) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
      (ρ : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (hρ : ρ.IsNondegenerate),
        ‖ρ.multiplierExtension hρ m‖ ≤ c := by
  refine ⟨fun h H _ _ _ ρ hρ =>
    (NonUnitalStarAlgHom.norm_apply_le (ρ.multiplierExtension hρ).toNonUnitalStarAlgHom m).trans h,
    fun h => ?_⟩
  rw [← norm_fst]
  refine m.fst.opNorm_le_bound hc fun a => ?_
  refine (TauCeti.CStarAlgebra.norm_le_iff_forall_isNondegenerate
    (mul_nonneg hc (norm_nonneg a))).2 fun H _ _ _ ρ hρ => ?_
  rw [← ρ.multiplierExtension_mul_eq_fst hρ]
  exact (norm_mul_le _ _).trans <|
    mul_le_mul (h H ρ hρ) (NonUnitalStarAlgHom.norm_apply_le ρ a) (norm_nonneg _) hc

/-- Two multipliers in `𝓜(ℂ, A)` are equal if and only if they agree under the multiplier
extension of every nondegenerate Hilbert-space representation of `A` in the same universe. -/
theorem eq_iff_forall_multiplierExtension_eq {m n : 𝓜(ℂ, A)} :
    m = n ↔ ∀ (H : Type w) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
      (ρ : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (hρ : ρ.IsNondegenerate),
        ρ.multiplierExtension hρ m = ρ.multiplierExtension hρ n := by
  refine ⟨fun h _ _ _ _ _ _ => h ▸ rfl, fun h => ?_⟩
  rw [← sub_eq_zero, ← norm_le_zero_iff]
  refine (norm_le_iff_forall_isNondegenerate le_rfl).2 fun H _ _ _ ρ hρ => ?_
  rw [map_sub, h H ρ hρ, sub_self, norm_zero]

end DoubleCentralizer
