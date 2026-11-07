/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.PositiveLinearFunctional
public import TauCeti.Analysis.CStarAlgebra.GNS
public import TauCeti.Analysis.CStarAlgebra.Representation.Nondegenerate
import Mathlib.Analysis.CStarAlgebra.GelfandDuality
import Mathlib.Analysis.Normed.Module.HahnBanach

/-!
# Nondegeneracy of GNS representations and norm recovery

For every positive linear functional `f` on a possibly nonunital C⋆-algebra `A`, Mathlib's GNS
representation `f.gnsNonUnitalStarAlgHom : A →⋆ₙₐ[ℂ] (f.GNS →L[ℂ] f.GNS)` is nondegenerate: the
class map `f.toGNS` has dense range and `e * b → b` along an increasing approximate unit `e` of
`A`. Its multiplier extension acts on classes `[b]` as `[m.fst b]`.

On a nontrivial unital C⋆-algebra, every nonnegative element `a` admits a state `ω` taking the
value `‖a‖ ^ n` on each power `a ^ n` (constructed by extending a character on the generated
commutative C⋆-subalgebra via Hahn–Banach). Applying the GNS representation to states pulled back
from `𝓜(ℂ, A)` shows that nondegenerate representations in `A`'s own universe recover both the norm
of every element of `A` and, via `multiplierExtension`, the norm of every multiplier in `𝓜(ℂ, A)`.

## Main statements

* `PositiveLinearMap.isNondegenerate_gnsNonUnitalStarAlgHom`: the GNS representation of any
  positive functional on a C⋆-algebra is nondegenerate.
* `PositiveLinearMap.multiplierExtension_gnsNonUnitalStarAlgHom_toGNS`: the multiplier extension
  of the GNS representation sends `[b]` to `[m.fst b]`.
* `TauCeti.CStarAlgebra.exists_positiveContinuousLinearMap_apply_pow_eq_norm_pow`: existence of a
  state attaining `‖a‖ ^ n` on `a ^ n` for `0 ≤ a` in a nontrivial unital C⋆-algebra.
* `TauCeti.CStarAlgebra.norm_le_iff_forall_isNondegenerate` and
  `DoubleCentralizer.norm_le_iff_forall_isNondegenerate`: norm bounds in `A` and `𝓜(ℂ, A)` are
  tested on nondegenerate Hilbert-space representations in the same universe.
* `DoubleCentralizer.eq_iff_forall_multiplierExtension_eq`: nondegenerate representations separate
  points of `𝓜(ℂ, A)`.

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
@[simp]
theorem gnsNonUnitalStarAlgHom_toGNS (a b : A) :
    f.gnsNonUnitalStarAlgHom a (f.toGNS b) = f.toGNS (a * b) := by
  simp [toGNS_apply]

/-- The norm of `f.toGNS b` in the GNS Hilbert space is `√‖f (star b * b)‖`. -/
theorem norm_toGNS (b : A) : ‖f.toGNS b‖ = √‖f (star b * b)‖ := by
  simp [toGNS_apply, preGNS_norm_def']

/-- The GNS representation of any positive linear functional on a C⋆-algebra is nondegenerate. -/
theorem isNondegenerate_gnsNonUnitalStarAlgHom : f.gnsNonUnitalStarAlgHom.IsNondegenerate := by
  rw [NonUnitalStarAlgHom.isNondegenerate_iff_dense]
  have hl := CStarAlgebra.increasingApproximateUnit A
  have := hl.neBot
  set S := (Submodule.span ℂ (⋃ a, Set.range (f.gnsNonUnitalStarAlgHom a)) : Set f.GNS)
  have hrange : Set.range f.toGNS ⊆ closure S := by
    rintro _ ⟨b, rfl⟩
    refine mem_closure_of_tendsto ((f.toGNS.continuous.tendsto b).comp (hl.tendsto_mul_right b)) ?_
    exact .of_forall fun e => Submodule.subset_span <|
      Set.mem_iUnion.2 ⟨e, f.toGNS b, by simp⟩
  exact dense_closure.1 (f.denseRange_toGNS.mono hrange)

/-- The multiplier extension of the GNS representation sends `f.toGNS b` to `f.toGNS (m.fst b)`. -/
@[simp]
theorem multiplierExtension_gnsNonUnitalStarAlgHom_toGNS (m : 𝓜(ℂ, A)) (b : A) :
    f.gnsNonUnitalStarAlgHom.multiplierExtension f.isNondegenerate_gnsNonUnitalStarAlgHom m
      (f.toGNS b) = f.toGNS (m.fst b) := by
  have hl := CStarAlgebra.increasingApproximateUnit A
  have := hl.neBot
  have h1 := f.gnsNonUnitalStarAlgHom.tendsto_multiplierExtension_apply
    f.isNondegenerate_gnsNonUnitalStarAlgHom hl m (f.toGNS b)
  have h2 : Tendsto (fun e => f.gnsNonUnitalStarAlgHom (m.fst e) (f.toGNS b))
      (CStarAlgebra.approximateUnit A) (𝓝 (f.toGNS (m.fst b))) := by
    have hcont : Continuous fun x : A => f.toGNS (m.fst x) := by fun_prop
    refine ((hcont.tendsto b).comp (hl.tendsto_mul_right b)).congr fun e => ?_
    simp [DoubleCentralizer.fst_mul]
  exact tendsto_nhds_unique h1 h2

end PositiveLinearMap

namespace TauCeti.CStarAlgebra

section State

variable {M : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M] [Nontrivial M]

/-- On a nontrivial unital C⋆-algebra, every nonnegative element `a` admits a state `ω` satisfying
`ω (a ^ n) = ‖a‖ ^ n` for every `n : ℕ`. -/
theorem exists_positiveContinuousLinearMap_apply_pow_eq_norm_pow {a : M} (ha : 0 ≤ a) :
    ∃ ω : M →P[ℂ] ℂ, ω 1 = 1 ∧ ‖(ω : M →L[ℂ] ℂ)‖ = 1 ∧
      ∀ n : ℕ, ω (a ^ n) = (‖a‖ : ℂ) ^ n := by
  have : IsStarNormal a := ha.isSelfAdjoint.isStarNormal
  set S := StarAlgebra.elemental ℂ a
  have : IsClosed (S : Set M) := StarAlgebra.elemental.isClosed ℂ a
  have haS : a ∈ S := StarAlgebra.elemental.self_mem ℂ a
  have hz : (‖a‖ : ℂ) ∈ spectrum ℂ (⟨a, haS⟩ : S) := by
    rw [StarSubalgebra.spectrum_eq]
    exact spectrum.algebraMap_mem ℂ (_root_.CStarAlgebra.norm_mem_spectrum_of_nonneg a ha)
  obtain ⟨χ, hχa⟩ := WeakDual.CharacterSpace.mem_spectrum_iff_exists.1 hz
  set φS : StrongDual ℂ S.toSubmodule := (WeakDual.CharacterSpace.toAlgHom χ).toContinuousLinearMap
  have hφS_norm : ‖φS‖ = 1 := AlgHom.toContinuousLinearMap_norm _
  obtain ⟨g, hg_ext, hg_norm⟩ := exists_extension_norm_eq S.toSubmodule φS
  rw [hφS_norm] at hg_norm
  have hg_one : g 1 = 1 :=
    (hg_ext ⟨1, S.one_mem⟩).trans (map_one χ)
  have hg_mono : Monotone g :=
    ContinuousLinearMap.monotone_iff_opNorm_eq_map_one.2 (by simp [hg_norm, hg_one])
  refine ⟨{ __ := g, monotone' := hg_mono }, hg_one, hg_norm, fun n => ?_⟩
  have han : a ^ n ∈ S := S.pow_mem haS n
  have hsub : (⟨a ^ n, han⟩ : S) = (⟨a, haS⟩ : S) ^ n := rfl
  calc g (a ^ n) = φS ⟨a ^ n, han⟩ := hg_ext ⟨a ^ n, han⟩
    _ = χ ((⟨a, haS⟩ : S) ^ n) := by rw [← hsub]; rfl
    _ = (‖a‖ : ℂ) ^ n := by rw [map_pow, hχa]

/-- On a nontrivial unital C⋆-algebra, every nonnegative element `a` admits a state `ω` with
`ω a = ‖a‖`. -/
theorem exists_positiveContinuousLinearMap_apply_eq_norm {a : M} (ha : 0 ≤ a) :
    ∃ ω : M →P[ℂ] ℂ, ω 1 = 1 ∧ ‖(ω : M →L[ℂ] ℂ)‖ = 1 ∧ ω a = ‖a‖ := by
  obtain ⟨ω, h1, hn, hp⟩ := exists_positiveContinuousLinearMap_apply_pow_eq_norm_pow ha
  exact ⟨ω, h1, hn, by simpa using hp 1⟩

end State

section NormLeIff

universe w

variable {A : Type w} [NonUnitalCStarAlgebra A]

private theorem exists_positiveLinearMap_pow_eq {x : A}
    [PartialOrder A] [StarOrderedRing A] (hx_nonneg : 0 ≤ x) (hx0 : 0 < ‖x‖) :
    ∃ f : A →ₚ[ℂ] ℂ, f x = ‖x‖ ∧ f (x * x) = (‖x‖ : ℂ) ^ 2 := by
  let := _root_.CStarAlgebra.spectralOrder 𝓜(ℂ, A)
  have := _root_.CStarAlgebra.spectralOrderedRing 𝓜(ℂ, A)
  have : Nontrivial 𝓜(ℂ, A) := by
    refine ⟨(x : 𝓜(ℂ, A)), 0, fun h0 => hx0.ne' ?_⟩
    rw [← DoubleCentralizer.norm_coe (𝕜 := ℂ), h0, norm_zero]
  have hxM_nonneg : 0 ≤ (x : 𝓜(ℂ, A)) := by
    rw [← DoubleCentralizer.coeHom_apply (𝕜 := ℂ)]
    exact map_nonneg (DoubleCentralizer.coeHom (𝕜 := ℂ) : A →⋆ₙₐ[ℂ] 𝓜(ℂ, A)) hx_nonneg
  obtain ⟨ω, -, -, hω⟩ := exists_positiveContinuousLinearMap_apply_pow_eq_norm_pow hxM_nonneg
  refine ⟨(ω : 𝓜(ℂ, A) →ₚ[ℂ] ℂ).comp
    (.ofClass (DoubleCentralizer.coeHom (𝕜 := ℂ) : A →⋆ₙₐ[ℂ] 𝓜(ℂ, A))), ?_, ?_⟩
  · have h1 := hω 1
    rw [pow_one, pow_one, DoubleCentralizer.norm_coe] at h1
    exact h1
  · have h2 := hω 2
    rw [sq, ← DoubleCentralizer.coe_mul, DoubleCentralizer.norm_coe] at h2
    exact h2

/-- The norm of an element `a : A` of a possibly nonunital C⋆-algebra is bounded by `c ≥ 0` if and
only if `‖ρ a‖ ≤ c` for every nondegenerate representation `ρ` on a Hilbert space in the same
universe. -/
theorem norm_le_iff_forall_isNondegenerate {a : A} {c : ℝ} (hc : 0 ≤ c) :
    ‖a‖ ≤ c ↔ ∀ (H : Type w) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
      (ρ : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)), ρ.IsNondegenerate → ‖ρ a‖ ≤ c := by
  refine ⟨fun h H _ _ _ ρ _ => (NonUnitalStarAlgHom.norm_apply_le ρ a).trans h, fun h => ?_⟩
  by_cases ha0 : a = 0
  · simp [ha0, hc]
  let := _root_.CStarAlgebra.spectralOrder A
  have := _root_.CStarAlgebra.spectralOrderedRing A
  let x : A := a * star a
  have hx_def : a * star a = x := rfl
  have hx_nonneg : 0 ≤ x := by simp [x]
  have hx_norm : ‖x‖ = ‖a‖ ^ 2 := by simp [x, CStarRing.norm_self_mul_star, sq]
  have ha_pos : 0 < ‖a‖ := norm_pos_iff.2 ha0
  have hx_pos : 0 < ‖x‖ := hx_norm ▸ pow_pos ha_pos 2
  obtain ⟨f, hfx1, hfx2⟩ := exists_positiveLinearMap_pow_eq hx_nonneg hx_pos
  have hζ : ‖f.toGNS (star a)‖ = ‖a‖ := by
    rw [f.norm_toGNS, star_star, hx_def, hfx1, hx_norm,
      Complex.norm_of_nonneg (sq_nonneg ‖a‖), Real.sqrt_sq (norm_nonneg a)]
  have hρζ : ‖f.gnsNonUnitalStarAlgHom a (f.toGNS (star a))‖ = ‖a‖ ^ 2 := by
    rw [f.gnsNonUnitalStarAlgHom_toGNS, hx_def, f.norm_toGNS,
      hx_nonneg.isSelfAdjoint.star_eq, hfx2, hx_norm, norm_pow,
      Complex.norm_of_nonneg (sq_nonneg ‖a‖), Real.sqrt_sq (sq_nonneg ‖a‖)]
  have hbound : ‖f.gnsNonUnitalStarAlgHom a (f.toGNS (star a))‖ ≤ c * ‖a‖ :=
    calc ‖f.gnsNonUnitalStarAlgHom a (f.toGNS (star a))‖
        ≤ ‖f.gnsNonUnitalStarAlgHom a‖ * ‖f.toGNS (star a)‖ :=
          (f.gnsNonUnitalStarAlgHom a).le_opNorm _
      _ ≤ c * ‖a‖ := by
          rw [hζ]
          exact mul_le_mul_of_nonneg_right
            (h f.GNS f.gnsNonUnitalStarAlgHom f.isNondegenerate_gnsNonUnitalStarAlgHom)
            (norm_nonneg a)
  rw [hρζ, sq] at hbound
  exact le_of_mul_le_mul_right hbound ha_pos

end NormLeIff

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
