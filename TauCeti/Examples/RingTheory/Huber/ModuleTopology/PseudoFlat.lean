/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.ModuleTopology.ProProjective
public import TauCeti.RingTheory.Huber.Padic.TateAlgebra
public import TauCeti.RingTheory.Huber.Restricted.TateAlgebra
public import TauCeti.RingTheory.Huber.Restricted.TwoSidedSeries.Ring
public import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.PairOfDefinition

/-!
# Checks and non-examples for pseudoflat and pro-projective modules

Concrete instances, coordinate evaluations, and counterexamples exercising `IsPseudoFlat`,
`IsProProjective`, `RestrictedLaurentSeries`, `restrictedPowerSeriesTensorToNull`, and
`restrictedLaurentSeriesTensorToNull`:

* compatibility with flatness (`IsPseudoFlat.of_flat`) and degenerate zero modules (`PUnit`);
* pro-projectivity and `2`-pseudoflatness of the `p`-adic Tate algebra `ℚ_p⟨X₁, …, Xₖ⟩` and the
  two-sided restricted Laurent algebra `ℚ_p⟨T, T⁻¹⟩`, together with explicit coefficient extraction
  on pure tensors in both `ℚ_p⟨T⟩ ⊗ M` and `ℚ_p⟨T, T⁻¹⟩ ⊗ M`;
* a stably `⊤`-pseudocoherent cyclic quotient `ℚ_p⟨T⟩ ⧸ (T)` over the strongly noetherian Tate
  algebra `ℚ_p⟨T⟩` that fails both `⊤`-pseudoflatness and `2`-pseudoflatness;
* failure of `IsProProjective` when a nontrivial module carries the indiscrete uniformity `⊤`,
  even though the zero projectors have finite projective image and converge to every element.
-/

public section

noncomputable section

open TensorProduct Topology UniformSpace
open TauCeti.Huber

namespace TauCeti.Examples

section DegenerateAndFlat

-- Every flat module (and in particular every finite free module) is `m`-pseudoflat for all `m`.
example (A : Type*) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] (r : ℕ) (m : ℕ∞) :
    IsPseudoFlat A (Fin r → A) m :=
  IsPseudoFlat.of_flat

-- The zero module `PUnit` is pro-projective over `ℚ_[p]` and `2`-pseudoflat.
example (p : ℕ) [Fact p.Prime] :
    IsProProjective ℚ_[p] PUnit ∧ IsPseudoFlat ℚ_[p] PUnit 2 :=
  ⟨IsProProjective.of_projective, IsPseudoFlat.of_isProProjective IsProProjective.of_projective⟩

end DegenerateAndFlat

section PadicRestrictedSeries

variable (p : ℕ) [Fact p.Prime]

-- Both `ℚ_p⟨X₁, …, Xₖ⟩` and `ℚ_p⟨T, T⁻¹⟩`, and their product, are pro-projective and
-- `2`-pseudoflat over `ℚ_[p]`.
example (k : ℕ) :
    IsProProjective ℚ_[p] (restrictedMvPowerSeriesCompletion k ℚ_[p]) ∧
      IsProProjective ℚ_[p] (RestrictedLaurentSeries ℚ_[p]) ∧
      IsPseudoFlat ℚ_[p]
        (restrictedMvPowerSeriesCompletion k ℚ_[p] × RestrictedLaurentSeries ℚ_[p]) 2 :=
  ⟨isProProjective_restrictedMvPowerSeriesCompletion k ℚ_[p],
    isProProjective_restrictedLaurentSeries ℚ_[p],
    (isPseudoFlat_restrictedMvPowerSeriesCompletion k ℚ_[p]).prod
      (isPseudoFlat_restrictedLaurentSeries ℚ_[p])⟩

-- Coordinate extraction on the variable `X` in `ℚ_p⟨X⟩` and pure-tensor evaluation into null
-- sequences.
example (m : ℚ_[p]) :
    let X : restrictedMvPowerSeriesCompletion 1 ℚ_[p] :=
      ((weightedX (fun _ : Fin 1 ↦ ({1} : Set ℚ_[p])) isWeightFamily_one_weight 0 :
          weightedRestrictedSubring _ _) :
        restrictedMvPowerSeriesCompletion 1 ℚ_[p])
    restrictedCoeff (A := ℚ_[p]) 1 X = 1 ∧
      restrictedCoeff (A := ℚ_[p]) 0 X = 0 ∧
      (restrictedPowerSeriesTensorToNull (X ⊗ₜ[ℚ_[p]] m)).1 1 = m ∧
      (restrictedPowerSeriesTensorToNull (X ⊗ₜ[ℚ_[p]] m)).1 0 = 0 ∧
      Function.Bijective
        (restrictedPowerSeriesTensorToNull (A := ℚ_[p]) (M := ℚ_[p])) := by
  intro X
  have h1 : restrictedCoeff (A := ℚ_[p]) 1 X = 1 := by
    rw [restrictedCoeff_coe, coe_weightedX]
    simp [MvPowerSeries.coeff_X]
  have h0 : restrictedCoeff (A := ℚ_[p]) 0 X = 0 := by
    rw [restrictedCoeff_coe, coe_weightedX, Finsupp.single_zero]
    exact MvPowerSeries.coeff_zero_X (R := ℚ_[p]) 0
  refine ⟨h1, h0, ?_, ?_, restrictedPowerSeriesTensorToNull_bijective .of_projective⟩
  · rw [coe_restrictedPowerSeriesTensorToNull_tmul, h1, one_smul]
  · rw [coe_restrictedPowerSeriesTensorToNull_tmul, h0, zero_smul]

-- Pure-tensor evaluation on negative-degree Laurent monomials `a T⁻¹ ⊗ m` in `ℚ_p⟨T, T⁻¹⟩ ⊗ M`.
example (a m : ℚ_[p]) :
    let Tinv : RestrictedLaurentSeries ℚ_[p] := ⟨twoSidedMonomial (-1) a⟩
    (restrictedLaurentSeriesTensorToNull
        (Tinv.toTwoSided ⊗ₜ[ℚ_[p]] m)).1 (-1) = a • m ∧
      (restrictedLaurentSeriesTensorToNull
        (Tinv.toTwoSided ⊗ₜ[ℚ_[p]] m)).1 1 = 0 ∧
      Function.Bijective
        (restrictedLaurentSeriesTensorToNull (A := ℚ_[p]) (M := ℚ_[p])) := by
  intro Tinv
  refine ⟨?_, ?_, restrictedLaurentSeriesTensorToNull_bijective .of_projective⟩
  · rw [restrictedLaurentSeriesTensorToNull_tmul]
    simp [Tinv, coe_twoSidedMonomial]
  · rw [restrictedLaurentSeriesTensorToNull_tmul]
    simp [Tinv, coe_twoSidedMonomial]

end PadicRestrictedSeries

section NonExamples

-- Over the strongly noetherian Tate algebra `A = ℚ_p⟨T⟩`, the cyclic quotient `A ⧸ (T)` equipped
-- with the module topology is stably `⊤`-pseudocoherent, yet neither `⊤`-pseudoflat nor
-- `2`-pseudoflat over `A`.
example (p : ℕ) [Fact p.Prime] :
    let A := restrictedMvPowerSeriesCompletion 1 ℚ_[p]
    let X : A :=
      ((weightedX (fun _ : Fin 1 ↦ ({1} : Set ℚ_[p])) isWeightFamily_one_weight 0 :
          weightedRestrictedSubring _ _) : A)
    let Q := A ⧸ Ideal.span ({X} : Set A)
    letI : TopologicalSpace Q := moduleTopology A Q
    haveI : IsModuleTopology A Q := ⟨rfl⟩
    IsStablyPseudoCoherent A Q ⊤ ∧ ¬ IsPseudoFlat A Q ⊤ ∧ ¬ IsPseudoFlat A Q 2 := by
  intro A X Q
  let : TopologicalSpace Q := moduleTopology A Q
  have : IsModuleTopology A Q := ⟨rfl⟩
  have : IsTopologicalAddGroup Q := IsModuleTopology.isTopologicalAddGroup A Q
  let : UniformSpace Q := IsTopologicalAddGroup.rightUniformSpace Q
  have : IsUniformAddGroup Q := isUniformAddGroup_of_addCommGroup
  have : Module.Finite A Q :=
    Module.Finite.of_surjective (Submodule.mkQ _) (Submodule.mkQ_surjective _)
  have hQ_spc : IsStablyPseudoCoherent A Q ⊤ :=
    IsStablyPseudoCoherent.of_isStronglyNoetherian
  have hX_coeff1 : restrictedCoeff (A := ℚ_[p]) 1 X = 1 := by
    rw [restrictedCoeff_coe, coe_weightedX]
    simp [MvPowerSeries.coeff_X]
  have hX_ne : X ≠ 0 := fun h0 ↦
    (one_ne_zero : (1 : ℚ_[p]) ≠ 0) (by simpa [h0] using hX_coeff1.symm)
  have hX_reg : IsSMulRegular A X := fun a b (hab : X * a = X * b) ↦
    mul_left_cancel₀ hX_ne hab
  have hX_not_unit : ¬ IsUnit X := by
    rintro ⟨u, hu⟩
    have hmul : X * (u⁻¹ : Units A) = 1 := by simp [← hu]
    have heq := congrArg (restrictedMvPowerSeriesCompletionEquiv 1 ℚ_[p]) hmul
    rw [map_mul, map_one, restrictedMvPowerSeriesCompletionEquiv_coe] at heq
    have hc := congrArg (fun f : weightedRestrictedSubring _ _ ↦
      MvPowerSeries.coeff (0 : Fin 1 →₀ ℕ) f.1) heq
    simp [Subring.coe_mul, coe_weightedX] at hc
  exact ⟨hQ_spc,
    not_isPseudoFlat_quotient_span_singleton hX_reg hX_not_unit hQ_spc,
    not_isPseudoFlat_quotient_span_singleton hX_reg hX_not_unit (hQ_spc.mono le_top)⟩

-- Without Hausdorffness (`T0Space`), any nontrivial `ℚ_[p]`-module equipped with the indiscrete
-- uniformity `⊤` fails `IsProProjective`, even though the zero projector family has finite
-- projective image and converges to every element.
example (p : ℕ) [Fact p.Prime] (B : Type*) [AddCommGroup B] [Module ℚ_[p] B] [Nontrivial B] :
    letI : UniformSpace B := ⊤
    haveI : IsUniformAddGroup B := ⟨fun _ hs ↦ Filter.mem_top.mp hs ▸ Filter.univ_mem⟩
    ¬ IsProProjective ℚ_[p] B := by
  let : UniformSpace B := ⊤
  have : IsUniformAddGroup B := ⟨fun _ hs ↦ Filter.mem_top.mp hs ▸ Filter.univ_mem⟩
  refine IsProProjective.not_of_not_t2Space fun hT2 ↦ ?_
  obtain ⟨x, y, hxy⟩ := exists_pair_ne B
  obtain ⟨U, V, hU, hV, hxU, hyV, hUV⟩ := hT2.t2 hxy
  rcases (TopologicalSpace.isOpen_top_iff U).mp hU with rfl | rfl
  · exact hxU
  · rcases (TopologicalSpace.isOpen_top_iff V).mp hV with rfl | rfl
    · exact hyV
    · exact Set.disjoint_left.mp hUV (Set.mem_univ x) (Set.mem_univ x)

end NonExamples

end TauCeti.Examples
