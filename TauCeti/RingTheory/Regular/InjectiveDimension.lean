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

Let `x` be a nonzerodivisor of a commutative ring `R`, and let `M` be an `R`-module on which `x` is
regular. Reducing `M` modulo `x` lowers any positive bound on the injective dimension by one:

```text
id_{R ⧸ (x)} (M ⧸ x M) + 1 ≤ id_R M.
```

In particular, if `M` has injective dimension at most `n + 1` over `R`, then `M ⧸ x M` has
injective dimension at most `n` over `R ⧸ (x)`; if `M` is injective over `R`, it is divisible by
`x` and `M ⧸ x M` is zero. Applied to `M = R`, this is the change-of-rings step showing that the
quotient of an Iwanaga–Gorenstein commutative ring by a nonzerodivisor is again
Iwanaga–Gorenstein, with any positive bound on the self-injective dimension lowered by one.

Using `ModuleCat.injective_torsionBy_of_injective` and `ModuleCat.surjective_smul_of_injective`,
along an injective copresentation `0 → C → E → C' → 0` of a module `C` on which multiplication by
`x` is surjective, multiplication by `x` stays surjective on `C'` and `TauCeti.torsionByLinearMap`
exhibits the `x`-torsion submodules as a short exact sequence `0 → K(C) → K(E) → K(C') → 0` over
`R ⧸ (x)`, so `K(C)` has injective dimension at most `id_R C` over `R ⧸ (x)`. For an `x`-regular
module `M`, an injective copresentation `0 → M → E → C → 0` then gives a short exact connecting
sequence `0 → K(E) → K(C) → M ⧸ x M → 0` over `R ⧸ (x)` via `TauCeti.torsionByδLinearMap`,
shifting the injective dimension bound by one.

## Main results

* `ModuleCat.hasInjectiveDimensionLE_torsionBy_of_surjective_smul`: if `x` is a nonzerodivisor and
  multiplication by `x` is surjective on `C`, then the `x`-torsion submodule of `C` has injective
  dimension over `R ⧸ (x)` at most that of `C` over `R`.
* `ModuleCat.hasInjectiveDimensionLE_quotient_smul_top_of_succ`: **Rees's reduction bound**: if `x`
  is a nonzerodivisor regular on an `R`-module `M` of injective dimension at most `n + 1`, then
  `M ⧸ x M` has injective dimension at most `n` over `R ⧸ (x)`.
* `ModuleCat.hasInjectiveDimensionLE_quotient_smul_top`: if `x` is a nonzerodivisor regular on `M`
  and `M` has injective dimension at most `n`, then `M ⧸ x M` has injective dimension at most `n`
  over `R ⧸ (x)`.
* `ModuleCat.injectiveDimension_quotient_smul_top_add_one_le`:
  `injectiveDimension (M ⧸ x M) + 1 ≤ injectiveDimension M` for an `x`-regular module `M`.
* `ModuleCat.hasInjectiveDimensionLE_quotient_span_singleton_of_succ`: if `R` has self-injective
  dimension at most `n + 1`, then `R ⧸ (x)` has self-injective dimension at most `n`.
* `ModuleCat.hasInjectiveDimensionLE_quotient_span_singleton`: if `R` has self-injective dimension
  at most `n`, then `R ⧸ (x)` has self-injective dimension at most `n`.

No finiteness or locality is assumed: the bounds hold for all modules.

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

/-- On the cokernel of the canonical embedding `Injective.ι M : M ⟶ Injective.under M`,
multiplication by any nonzerodivisor `x` is surjective, and an injective-dimension bound `n + 1`
on `M` shifts to `n`. -/
private theorem cokernelSequence_injective_ι_step {x : R} (hx : x ∈ nonZeroDivisors R)
    (n : ℕ) (M : ModuleCat.{v} R) [HasInjectiveDimensionLE M (n + 1)] :
    Function.Surjective (fun z : (ShortComplex.cokernelSequence (Injective.ι M)).X₃ ↦ x • z) ∧
      HasInjectiveDimensionLE (ShortComplex.cokernelSequence (Injective.ι M)).X₃ n := by
  set S := ShortComplex.cokernelSequence (Injective.ι M)
  have hS : S.ShortExact := TauCeti.cokernelSequence_shortExact (Injective.ι M)
  have hg_surj : Function.Surjective S.g.hom := (ModuleCat.epi_iff_surjective S.g).mp hS.epi_g
  have hInjX₂ : Injective S.X₂ := by
    rw [ShortComplex.cokernelSequence_X₂]
    infer_instance
  refine ⟨fun z ↦ ?_, ?_⟩
  · obtain ⟨y, rfl⟩ := hg_surj z
    obtain ⟨y₀, hy₀⟩ := surjective_smul_of_injective hx S.X₂ y
    exact ⟨S.g.hom y₀, (S.g.hom.map_smul x y₀).symm.trans (congrArg S.g.hom hy₀)⟩
  · have : HasInjectiveDimensionLE S.X₁ (n + 1) := by
      rw [ShortComplex.cokernelSequence_X₁]
      infer_instance
    exact hS.hasInjectiveDimensionLT_X₃ (n + 1)
      (hasInjectiveDimensionLT_of_ge S.X₂ 1 (n + 1) (by omega)) ‹_›

/-- If `x` is a nonzerodivisor of `R` and multiplication by `x` is surjective on an `R`-module `C`
of injective dimension at most `n`, then the `x`-torsion submodule of `C` has injective dimension at
most `n` over `R ⧸ (x)`. -/
theorem hasInjectiveDimensionLE_torsionBy_of_surjective_smul {x : R} (hx : x ∈ nonZeroDivisors R)
    (n : ℕ) (C : ModuleCat.{v} R) (hC : Function.Surjective (fun y : C ↦ x • y))
    [HasInjectiveDimensionLE C n] :
    HasInjectiveDimensionLE (of (R ⧸ span {x}) (Submodule.torsionBy R C x)) n := by
  induction n generalizing C with
  | zero =>
    have : Injective C := injective_iff_hasInjectiveDimensionLT_one.mpr ‹_›
    have := injective_torsionBy_of_injective x C
    exact injective_iff_hasInjectiveDimensionLT_one.mp this
  | succ n ih =>
    set S := ShortComplex.cokernelSequence (Injective.ι C)
    have hS : S.ShortExact := TauCeti.cokernelSequence_shortExact (Injective.ι C)
    obtain ⟨hC'_surj, _⟩ := cokernelSequence_injective_ι_step hx n C
    have := ih S.X₃ hC'_surj
    have hInjX₂ : Injective S.X₂ := by
      rw [ShortComplex.cokernelSequence_X₂]
      infer_instance
    have := injective_torsionBy_of_injective x S.X₂
    have hSex := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).mp hS.exact
    have hf_inj : Function.Injective S.f.hom := (ModuleCat.mono_iff_injective S.f).mp hS.mono_f
    have hg_surj : Function.Surjective S.g.hom := (ModuleCat.epi_iff_surjective S.g).mp hS.epi_g
    have hC₁ : Function.Surjective (fun y : S.X₁ ↦ x • y) := by
      rw [ShortComplex.cokernelSequence_X₁]
      exact hC
    let fK := TauCeti.torsionByLinearMap x S.f.hom
    let gK := TauCeti.torsionByLinearMap x S.g.hom
    have hexK := TauCeti.exact_torsionByLinearMap (r := x) hSex hf_inj
    have hT : (shortComplexOfCompEqZero fK gK hexK.linearMap_comp_eq_zero).ShortExact :=
      shortComplex_shortExact _ hexK
        (TauCeti.injective_torsionByLinearMap hf_inj)
        (TauCeti.surjective_torsionByLinearMap_of_surjective_smul hSex hf_inj hg_surj hC₁)
    have hRes := hT.hasInjectiveDimensionLT_X₁ (n + 1) ‹_›
      (hasInjectiveDimensionLT_of_ge _ 1 (n + 2) (by omega))
    dsimp only [shortComplexOfCompEqZero, ShortComplex.moduleCatMk] at hRes
    rwa [ShortComplex.cokernelSequence_X₁] at hRes

/-- **Rees's change-of-rings bound for injective dimension.** If `x` is a nonzerodivisor of `R`
which is regular on an `R`-module `M` of injective dimension at most `n + 1`, then `M ⧸ x M` has
injective dimension at most `n` over `R ⧸ (x)`. -/
theorem hasInjectiveDimensionLE_quotient_smul_top_of_succ {x : R} (hx : x ∈ nonZeroDivisors R)
    (n : ℕ) (M : ModuleCat.{v} R) (hM : IsSMulRegular M x)
    [HasInjectiveDimensionLE M (n + 1)] :
    HasInjectiveDimensionLE (of (R ⧸ span {x}) (M ⧸ span {x} • (⊤ : Submodule R M))) n := by
  set S := ShortComplex.cokernelSequence (Injective.ι M)
  have hS : S.ShortExact := TauCeti.cokernelSequence_shortExact (Injective.ι M)
  obtain ⟨hC_surj, _⟩ := cokernelSequence_injective_ι_step hx n M
  have := hasInjectiveDimensionLE_torsionBy_of_surjective_smul hx n S.X₃ hC_surj
  have hInjX₂ : Injective S.X₂ := by
    rw [ShortComplex.cokernelSequence_X₂]
    infer_instance
  have := injective_torsionBy_of_injective x S.X₂
  have hSex := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).mp hS.exact
  have hf_inj : Function.Injective S.f.hom := (ModuleCat.mono_iff_injective S.f).mp hS.mono_f
  have hg_surj : Function.Surjective S.g.hom := (ModuleCat.epi_iff_surjective S.g).mp hS.epi_g
  have hX₁ : Function.Injective (fun y : S.X₁ ↦ x • y) := by
    rw [ShortComplex.cokernelSequence_X₁]
    exact fun _ _ h ↦ hM h
  let gK := TauCeti.torsionByLinearMap x S.g.hom
  let e := (QuotSMulTop.quotSpanSingletonSMulTopEquiv x S.X₁).symm
  let δ := e.toLinearMap ∘ₗ TauCeti.torsionByδLinearMap x hSex hf_inj hg_surj
  have hex : Function.Exact gK δ := fun c ↦ by
    simp only [δ, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, LinearEquiv.map_eq_zero_iff]
    exact TauCeti.exact_torsionByLinearMap_torsionByδLinearMap hSex hf_inj hg_surj c
  have hT : (shortComplexOfCompEqZero gK δ hex.linearMap_comp_eq_zero).ShortExact :=
    shortComplex_shortExact _ hex
      (TauCeti.injective_torsionByLinearMap_of_injective_smul hSex hf_inj hX₁)
      (e.surjective.comp
        (TauCeti.surjective_torsionByδLinearMap hSex hf_inj hg_surj
          (surjective_smul_of_injective hx S.X₂)))
  have hRes := hT.hasInjectiveDimensionLT_X₃ (n + 1) ‹_›
    (hasInjectiveDimensionLT_of_ge _ 1 (n + 2) (by omega))
  dsimp only [shortComplexOfCompEqZero, ShortComplex.moduleCatMk] at hRes
  rwa [ShortComplex.cokernelSequence_X₁] at hRes

/-- **Change of rings for injective dimension, by reduction.** If `x` is a nonzerodivisor of `R`
which is regular on an `R`-module `M` of injective dimension at most `n`, then `M ⧸ x M` has
injective dimension at most `n` over `R ⧸ (x)`. -/
theorem hasInjectiveDimensionLE_quotient_smul_top {x : R} (hx : x ∈ nonZeroDivisors R)
    (n : ℕ) (M : ModuleCat.{v} R) (hM : IsSMulRegular M x) [HasInjectiveDimensionLE M n] :
    HasInjectiveDimensionLE (of (R ⧸ span {x}) (M ⧸ span {x} • (⊤ : Submodule R M))) n := by
  rcases n with _ | n
  · have : Injective M := injective_iff_hasInjectiveDimensionLT_one.mpr ‹_›
    have := (isZero_quotient_smul_top_of_injective hx M).hasInjectiveDimensionLT_zero
    exact hasInjectiveDimensionLT_of_ge _ 0 1 (by omega)
  · have := hasInjectiveDimensionLE_quotient_smul_top_of_succ hx n M hM
    exact hasInjectiveDimensionLT_of_ge _ (n + 1) (n + 2) (by omega)

/-- **Rees's inequality for injective dimension.** For a nonzerodivisor `x` of `R` that is regular
on `M`, reducing `M` modulo `x` satisfies
`injectiveDimension (M ⧸ x M) + 1 ≤ injectiveDimension M`. -/
theorem injectiveDimension_quotient_smul_top_add_one_le {x : R} (hx : x ∈ nonZeroDivisors R)
    (M : ModuleCat.{v} R) (hM : IsSMulRegular M x) :
    injectiveDimension (of (R ⧸ span {x}) (M ⧸ span {x} • (⊤ : Submodule R M))) + 1 ≤
      injectiveDimension M := by
  induction hd : injectiveDimension M using WithBot.recBotCoe with
  | bot =>
    have := (hasInjectiveDimensionLT_zero_iff_isZero M).mpr
      ((injectiveDimension_eq_bot_iff M).mp hd)
    have : Injective M :=
      injective_iff_hasInjectiveDimensionLT_one.mpr
        (hasInjectiveDimensionLT_of_ge M 0 1 (by omega))
    rw [(injectiveDimension_eq_bot_iff _).mpr (isZero_quotient_smul_top_of_injective hx M)]
    exact bot_le
  | coe d =>
    induction d with
    | top => exact le_top
    | coe n =>
      have : HasInjectiveDimensionLE M n := (injectiveDimension_le_iff M n).mp hd.le
      rcases n with _ | n
      · have : Injective M := injective_iff_hasInjectiveDimensionLT_one.mpr ‹_›
        rw [(injectiveDimension_eq_bot_iff _).mpr (isZero_quotient_smul_top_of_injective hx M)]
        exact bot_le
      · have hQ := (injectiveDimension_le_iff _ n).mpr
          (hasInjectiveDimensionLE_quotient_smul_top_of_succ hx n M hM)
        exact (add_le_add_left hQ 1).trans_eq (by norm_cast)

omit [CommRing R] [Small.{v} R] in
/-- If `x` is a nonzerodivisor of `S` and the regular module `S` has injective dimension at most
`n + 1`, then the regular module of `S ⧸ (x)` has injective dimension at most `n`. -/
theorem hasInjectiveDimensionLE_quotient_span_singleton_of_succ {S : Type u} [CommRing S]
    {x : S} (hx : x ∈ nonZeroDivisors S) (n : ℕ)
    [HasInjectiveDimensionLE (of S S) (n + 1)] :
    HasInjectiveDimensionLE (of (S ⧸ span {x}) (S ⧸ span {x})) n := by
  have := hasInjectiveDimensionLE_quotient_smul_top_of_succ hx n (of S S)
    (Module.Flat.isSMulRegular_of_nonZeroDivisors hx)
  exact hasInjectiveDimensionLT_of_iso ((span {x}).quotSMulTopSelfEquiv).toModuleIso (n + 1)

omit [CommRing R] [Small.{v} R] in
/-- If `x` is a nonzerodivisor of `S` and the regular module `S` has injective dimension at most
`n`, then the regular module of `S ⧸ (x)` has injective dimension at most `n`. -/
theorem hasInjectiveDimensionLE_quotient_span_singleton {S : Type u} [CommRing S]
    {x : S} (hx : x ∈ nonZeroDivisors S) (n : ℕ)
    [HasInjectiveDimensionLE (of S S) n] :
    HasInjectiveDimensionLE (of (S ⧸ span {x}) (S ⧸ span {x})) n := by
  have := hasInjectiveDimensionLE_quotient_smul_top hx n (of S S)
    (Module.Flat.isSMulRegular_of_nonZeroDivisors hx)
  exact hasInjectiveDimensionLT_of_iso ((span {x}).quotSMulTopSelfEquiv).toModuleIso (n + 1)

end ModuleCat
