/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Abelian.Injective.Dimension
public import Mathlib.RingTheory.Regular.IsSMulRegular
public import TauCeti.Algebra.Category.ModuleCat.Injective.Torsion
import Mathlib.Algebra.Category.ModuleCat.EnoughInjectives
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import TauCeti.Algebra.Homology.ShortComplex.ShortExact
import TauCeti.Algebra.Module.Torsion.Snake
import TauCeti.RingTheory.Flat.NonZeroDivisors
import TauCeti.RingTheory.QuotSMulTop

/-!
# Injective dimension along the quotient by a nonzerodivisor

For `x ∈ nonZeroDivisors R` regular on an `R`-module `M`, reducing `M` modulo `x` satisfies Rees's
inequality `injectiveDimension (M ⧸ x M) + 1 ≤ injectiveDimension M`
(`ModuleCat.injectiveDimension_quotient_smul_top_add_one_le`,
`ModuleCat.hasInjectiveDimensionLE_quotient_smul_top_of_succ`). For `M = R`, the quotient of an
Iwanaga–Gorenstein commutative ring by a nonzerodivisor remains Iwanaga–Gorenstein, with any
positive bound on the self-injective dimension lowered by one
(`ModuleCat.hasInjectiveDimensionLE_quotient_span_singleton_of_succ`).

## References

* D. Rees, *A theorem of homological algebra*, Proc. Cambridge Philos. Soc. **52** (1956), 605–610.
* H. Matsumura, *Commutative Ring Theory*, Section 18, Lemma 2 preceding Theorem 18.2.
* W. Bruns and J. Herzog, *Cohen–Macaulay Rings*, Section 3.1, Lemma 3.1.16.
-/

public section

universe v u

open CategoryTheory Ideal Pointwise

namespace ModuleCat

variable {R : Type u} [CommRing R] [Small.{v} R]

private theorem cokernelSequence_injective_ι_step {x : R} (hx : x ∈ nonZeroDivisors R) (n : ℕ)
    (M : ModuleCat.{v} R) [HasInjectiveDimensionLE M (n + 1)] :
    Function.Surjective (fun z : (ShortComplex.cokernelSequence (Injective.ι M)).X₃ ↦ x • z) ∧
      HasInjectiveDimensionLE (ShortComplex.cokernelSequence (Injective.ι M)).X₃ n := by
  set S := ShortComplex.cokernelSequence (Injective.ι M)
  have hS : S.ShortExact := TauCeti.cokernelSequence_shortExact (Injective.ι M)
  have hInjX₂ : Injective S.X₂ := by rw [ShortComplex.cokernelSequence_X₂]; infer_instance
  refine ⟨fun z ↦ ?_, ?_⟩
  · obtain ⟨y, rfl⟩ := (ModuleCat.epi_iff_surjective S.g).mp hS.epi_g z
    obtain ⟨y₀, hy₀⟩ := surjective_smul_of_injective hx S.X₂ y
    exact ⟨S.g.hom y₀, (S.g.hom.map_smul x y₀).symm.trans (congrArg S.g.hom hy₀)⟩
  · have : HasInjectiveDimensionLE S.X₁ (n + 1) := by
      rw [ShortComplex.cokernelSequence_X₁]; infer_instance
    exact hS.hasInjectiveDimensionLT_X₃ (n + 1)
      (hasInjectiveDimensionLT_of_ge S.X₂ 1 (n + 1) (by omega)) ‹_›

/-- If `x ∈ nonZeroDivisors R` and `x • ·` is surjective on `C` of injective dimension `≤ n`, then
`Submodule.torsionBy R C x` has injective dimension `≤ n` over `R ⧸ (x)`. -/
theorem hasInjectiveDimensionLE_torsionBy_of_surjective_smul {x : R} (hx : x ∈ nonZeroDivisors R)
    (n : ℕ) (C : ModuleCat.{v} R) (hC : Function.Surjective (fun y : C ↦ x • y))
    [HasInjectiveDimensionLE C n] :
    HasInjectiveDimensionLE (of (R ⧸ span {x}) (Submodule.torsionBy R C x)) n := by
  induction n generalizing C with
  | zero =>
    have : Injective C := injective_iff_hasInjectiveDimensionLT_one.mpr ‹_›
    exact injective_iff_hasInjectiveDimensionLT_one.mp (injective_torsionBy_of_injective x C)
  | succ n ih =>
    set S := ShortComplex.cokernelSequence (Injective.ι C)
    have hS : S.ShortExact := TauCeti.cokernelSequence_shortExact (Injective.ι C)
    obtain ⟨hC'_surj, _⟩ := cokernelSequence_injective_ι_step hx n C
    have := ih S.X₃ hC'_surj
    have hInjX₂ : Injective S.X₂ := by rw [ShortComplex.cokernelSequence_X₂]; infer_instance
    have := injective_torsionBy_of_injective x S.X₂
    have hSex := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).mp hS.exact
    have hf_inj : Function.Injective S.f.hom := (ModuleCat.mono_iff_injective S.f).mp hS.mono_f
    have hg_surj : Function.Surjective S.g.hom := (ModuleCat.epi_iff_surjective S.g).mp hS.epi_g
    have hC₁ : Function.Surjective (fun y : S.X₁ ↦ x • y) := by
      rw [ShortComplex.cokernelSequence_X₁]; exact hC
    let fK := TauCeti.torsionByLinearMap x S.f.hom; let gK := TauCeti.torsionByLinearMap x S.g.hom
    have hexK : Function.Exact fK gK := by
      simpa [fK, gK] using TauCeti.exact_torsionByMap hSex hf_inj
    have hT : (shortComplexOfCompEqZero fK gK hexK.linearMap_comp_eq_zero).ShortExact :=
      shortComplex_shortExact _ hexK (by simpa [fK] using TauCeti.injective_torsionByMap hf_inj)
        (by simpa [gK] using TauCeti.surjective_torsionByMap_of_surjective_smul hSex hg_surj hC₁)
    have hRes := hT.hasInjectiveDimensionLT_X₁ (n + 1) ‹_›
      (hasInjectiveDimensionLT_of_ge _ 1 (n + 2) (by omega))
    dsimp only [shortComplexOfCompEqZero, ShortComplex.moduleCatMk] at hRes
    rwa [ShortComplex.cokernelSequence_X₁] at hRes

/-- **Rees's change-of-rings bound:** if `x ∈ nonZeroDivisors R` is regular on `M` of injective
dimension `≤ n + 1`, then `M ⧸ x M` has injective dimension `≤ n` over `R ⧸ (x)`. -/
theorem hasInjectiveDimensionLE_quotient_smul_top_of_succ {x : R} (hx : x ∈ nonZeroDivisors R)
    (n : ℕ) (M : ModuleCat.{v} R) (hM : IsSMulRegular M x) [HasInjectiveDimensionLE M (n + 1)] :
    HasInjectiveDimensionLE (of (R ⧸ span {x}) (M ⧸ span {x} • (⊤ : Submodule R M))) n := by
  set S := ShortComplex.cokernelSequence (Injective.ι M)
  have hS : S.ShortExact := TauCeti.cokernelSequence_shortExact (Injective.ι M)
  obtain ⟨hC_surj, _⟩ := cokernelSequence_injective_ι_step hx n M
  have := hasInjectiveDimensionLE_torsionBy_of_surjective_smul hx n S.X₃ hC_surj
  have hInjX₂ : Injective S.X₂ := by rw [ShortComplex.cokernelSequence_X₂]; infer_instance
  have := injective_torsionBy_of_injective x S.X₂
  have hSex := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).mp hS.exact
  have hf_inj : Function.Injective S.f.hom := (ModuleCat.mono_iff_injective S.f).mp hS.mono_f
  have hg_surj : Function.Surjective S.g.hom := (ModuleCat.epi_iff_surjective S.g).mp hS.epi_g
  have hX₁ : Function.Injective (fun y : S.X₁ ↦ x • y) := by
    rw [ShortComplex.cokernelSequence_X₁]; exact fun _ _ h ↦ hM h
  let gK := TauCeti.torsionByLinearMap x S.g.hom
  let e := (QuotSMulTop.quotSpanSingletonSMulTopEquiv x S.X₁).symm
  let δ := e.toLinearMap ∘ₗ TauCeti.torsionByδLinearMap x hSex hf_inj hg_surj
  have hex : Function.Exact gK δ := fun c ↦ by
    simp only [gK, δ, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
      LinearEquiv.map_eq_zero_iff, TauCeti.coe_torsionByLinearMap, TauCeti.coe_torsionByδLinearMap]
    exact TauCeti.exact_torsionByMap_torsionByδ hSex hf_inj hg_surj c
  have hT : (shortComplexOfCompEqZero gK δ hex.linearMap_comp_eq_zero).ShortExact :=
    shortComplex_shortExact _ hex
      (by simpa [gK] using TauCeti.injective_torsionByMap_of_injective_smul hSex hf_inj hX₁)
      (e.surjective.comp (by simpa using
        TauCeti.surjective_torsionByδ hSex hf_inj hg_surj (surjective_smul_of_injective hx S.X₂)))
  have hRes := hT.hasInjectiveDimensionLT_X₃ (n + 1) ‹_›
    (hasInjectiveDimensionLT_of_ge _ 1 (n + 2) (by omega))
  dsimp only [shortComplexOfCompEqZero, ShortComplex.moduleCatMk] at hRes
  rwa [ShortComplex.cokernelSequence_X₁] at hRes

/-- If `x ∈ nonZeroDivisors R` is regular on `M` of injective dimension `≤ n`, then `M ⧸ x M` has
injective dimension `≤ n` over `R ⧸ (x)`. -/
theorem hasInjectiveDimensionLE_quotient_smul_top {x : R} (hx : x ∈ nonZeroDivisors R)
    (n : ℕ) (M : ModuleCat.{v} R) (hM : IsSMulRegular M x) [HasInjectiveDimensionLE M n] :
    HasInjectiveDimensionLE (of (R ⧸ span {x}) (M ⧸ span {x} • (⊤ : Submodule R M))) n := by
  rcases n with _ | n
  · have : Injective M := injective_iff_hasInjectiveDimensionLT_one.mpr ‹_›
    have := (isZero_quotient_smul_top_of_injective hx M).hasInjectiveDimensionLT_zero
    exact hasInjectiveDimensionLT_of_ge _ 0 1 (by omega)
  · have := hasInjectiveDimensionLE_quotient_smul_top_of_succ hx n M hM
    exact hasInjectiveDimensionLT_of_ge _ (n + 1) (n + 2) (by omega)

/-- **Rees's inequality:** `injectiveDimension (M ⧸ x M) + 1 ≤ injectiveDimension M` for
`x ∈ nonZeroDivisors R` regular on `M`. -/
theorem injectiveDimension_quotient_smul_top_add_one_le {x : R} (hx : x ∈ nonZeroDivisors R)
    (M : ModuleCat.{v} R) (hM : IsSMulRegular M x) :
    injectiveDimension (of (R ⧸ span {x}) (M ⧸ span {x} • (⊤ : Submodule R M))) + 1 ≤
      injectiveDimension M := by
  induction hd : injectiveDimension M using WithBot.recBotCoe with
  | bot =>
    have := (hasInjectiveDimensionLT_zero_iff_isZero M).mpr
      ((injectiveDimension_eq_bot_iff M).mp hd)
    have : Injective M :=
      injective_iff_hasInjectiveDimensionLT_one.mpr (hasInjectiveDimensionLT_of_ge M 0 1 (by omega))
    rw [(injectiveDimension_eq_bot_iff _).mpr (isZero_quotient_smul_top_of_injective hx M)]
    exact bot_le
  | coe d =>
    cases d with
    | top => exact le_top
    | coe n =>
      have : HasInjectiveDimensionLE M n := (injectiveDimension_le_iff M n).mp hd.le
      rcases n with _ | n
      · have : Injective M := injective_iff_hasInjectiveDimensionLT_one.mpr ‹_›
        rw [(injectiveDimension_eq_bot_iff _).mpr (isZero_quotient_smul_top_of_injective hx M)]
        exact bot_le
      · exact (add_le_add_left ((injectiveDimension_le_iff _ n).mpr
          (hasInjectiveDimensionLE_quotient_smul_top_of_succ hx n M hM)) 1).trans_eq (by norm_cast)

omit [CommRing R] [Small.{v} R] in
/-- If `x ∈ nonZeroDivisors S` and `S` has self-injective dimension `≤ n + 1`, then `S ⧸ (x)` has
self-injective dimension `≤ n`. -/
theorem hasInjectiveDimensionLE_quotient_span_singleton_of_succ {S : Type u} [CommRing S] {x : S}
    (hx : x ∈ nonZeroDivisors S) (n : ℕ) [HasInjectiveDimensionLE (of S S) (n + 1)] :
    HasInjectiveDimensionLE (of (S ⧸ span {x}) (S ⧸ span {x})) n := by
  have := hasInjectiveDimensionLE_quotient_smul_top_of_succ hx n (of S S)
    (Module.Flat.isSMulRegular_of_nonZeroDivisors hx)
  exact hasInjectiveDimensionLT_of_iso ((span {x}).quotSMulTopSelfEquiv).toModuleIso (n + 1)

omit [CommRing R] [Small.{v} R] in
/-- If `x ∈ nonZeroDivisors S` and `S` has self-injective dimension `≤ n`, then `S ⧸ (x)` has
self-injective dimension `≤ n`. -/
theorem hasInjectiveDimensionLE_quotient_span_singleton {S : Type u} [CommRing S] {x : S}
    (hx : x ∈ nonZeroDivisors S) (n : ℕ) [HasInjectiveDimensionLE (of S S) n] :
    HasInjectiveDimensionLE (of (S ⧸ span {x}) (S ⧸ span {x})) n := by
  have := hasInjectiveDimensionLE_quotient_smul_top hx n (of S S)
    (Module.Flat.isSMulRegular_of_nonZeroDivisors hx)
  exact hasInjectiveDimensionLT_of_iso ((span {x}).quotSMulTopSelfEquiv).toModuleIso (n + 1)

end ModuleCat
