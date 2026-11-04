/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.CartanMap.ProjectiveDimension
public import TauCeti.RingTheory.LocalRing.Module

/-!
# Minimal finite resolutions over a local ring

Let `(R, 𝔪, k)` be a local ring. A finite resolution

```text
K₁ ↪ Q₀ ↠ M,   K₂ ↪ Q₁ ↠ K₁,   …,   Kₙ ↪ Qₙ₋₁ ↠ Kₙ₋₁
```

of an `R`-module `M` is *minimal* if every syzygy `Kᵢ₊₁` lies in `𝔪 • Qᵢ`. In the spliced complex
`0 → Kₙ → Qₙ₋₁ → ⋯ → Q₀ → M → 0` the image of each differential other than the augmentation
`Q₀ ↠ M` is a syzygy (the maps `Qᵢ ↠ Kᵢ` are surjective), so minimality says exactly that every
differential of the unaugmented complex `0 → Kₙ → Qₙ₋₁ → ⋯ → Q₀ → 0` has image in `𝔪` times its
target, i.e. that these differentials vanish after applying `k ⊗ -`. This is the form in which
minimality enters the proof that the projective dimension of `k` is at least the embedding
dimension `dim_k 𝔪/𝔪²` (Stacks 00OA): a comparison map from a Koszul complex into a minimal
resolution of `k` stays injective after applying `k ⊗ -`.

The main result is that over a Noetherian local ring, a finite module of projective dimension at
most `n` has a minimal resolution of length at most `n` by finite projective, hence finite free,
modules. The resolution is built directly from minimal covers: at each step, `M` is covered by
`R ^ μ(M)` with kernel in `𝔪 • R ^ μ(M)`
(`TauCeti.IsLocalRing.exists_surjective_ker_le_maximalIdeal_smul`), and dimension shifting makes
the last syzygy projective. This refines
`TauCeti.exists_finiteProjectiveResolution_of_hasProjectiveDimensionLE`, which uses arbitrary
finite free covers.

## Main definitions

* `TauCeti.ExactStructure.FiniteResolution.IsMinimal`: a finite resolution of modules over a local
  ring is minimal when each of its syzygies lies in `𝔪` times the next resolving term.

## Main results

* `TauCeti.ExactStructure.FiniteResolution.isMinimal_step_iff`: the recursive characterisation of
  minimality.
* `TauCeti.exists_minimal_finiteProjectiveResolution_of_hasProjectiveDimensionLE`: over a Noetherian
  local ring, a finite module of projective dimension at most `n` has a minimal resolution of
  length at most `n` by finite projective modules.

## References

* The Stacks Project, Tag 00MT, for minimal finite free resolutions over a local ring.
* Winfried Bruns and Jürgen Herzog, *Cohen–Macaulay Rings*, Section 1.3, for minimal free
  resolutions.
-/

public section

open CategoryTheory IsLocalRing

namespace TauCeti

universe u v

namespace ExactStructure.FiniteResolution

variable {R : Type u} [CommRing R] [IsLocalRing R]
  {E : ExactStructure (ModuleCat.{v} R)} {P : ObjectProperty (ModuleCat.{v} R)}

/-- A finite resolution `K₁ ↪ Q₀ ↠ X, K₂ ↪ Q₁ ↠ K₁, …` of modules over a local ring `(R, 𝔪)` is
*minimal* if every syzygy lies in `𝔪` times the following resolving term: the image of each
inclusion `Kᵢ₊₁ ↪ Qᵢ` is contained in `𝔪 • Qᵢ`. Equivalently, every differential of the spliced
unaugmented complex `0 → Kₙ → Qₙ₋₁ → ⋯ → Q₀` has image in `𝔪` times its target; the augmentation
`Q₀ ↠ X` is excluded, being surjective. -/
inductive IsMinimal : ∀ {X : ModuleCat.{v} R}, FiniteResolution E P X → Prop
  /-- A resolution of length zero is minimal. -/
  | base {X : ModuleCat.{v} R} (hX : P X) : IsMinimal (.base hX)
  /-- Prepending a conflation `K ↪ Q ↠ X` with `K` landing in `𝔪 • Q` to a minimal resolution of
  `K` gives a minimal resolution of `X`. -/
  | step {K Q X : ModuleCat.{v} R} (hQ : P Q) (i : K ⟶ Q) (p : Q ⟶ X) (zero : i ≫ p = 0)
      (hp : E.Conflation (ShortComplex.mk i p zero)) {r : FiniteResolution E P K}
      (hi : LinearMap.range i.hom ≤ maximalIdeal R • ⊤) (hr : IsMinimal r) :
      IsMinimal (.step hQ i p zero hp r)

@[simp] theorem isMinimal_base {X : ModuleCat.{v} R} (hX : P X) :
    (base (E := E) hX).IsMinimal :=
  .base hX

@[simp] theorem isMinimal_step_iff {K Q X : ModuleCat.{v} R} (hQ : P Q) (i : K ⟶ Q) (p : Q ⟶ X)
    (zero : i ≫ p = 0) (hp : E.Conflation (ShortComplex.mk i p zero))
    (r : FiniteResolution E P K) :
    (step hQ i p zero hp r).IsMinimal ↔
      LinearMap.range i.hom ≤ maximalIdeal R • ⊤ ∧ r.IsMinimal := by
  refine ⟨fun h ↦ ?_, fun h ↦ .step hQ i p zero hp h.1 h.2⟩
  cases h with
  | step _ _ _ _ _ hi hr => exact ⟨hi, hr⟩

end ExactStructure.FiniteResolution

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

/-- **Minimal finite resolutions.** Over a Noetherian local ring `(R, 𝔪)`, a finite module of
projective dimension at most `n` has a minimal resolution of length at most `n` by finite
projective modules: every syzygy lies in `𝔪` times the following resolving term.

Over a local ring the finite projective terms are free (`Module.free_of_flat_of_isLocalRing`). -/
theorem exists_minimal_finiteProjectiveResolution_of_hasProjectiveDimensionLE
    {M : ModuleCat.{u} R} [Module.Finite R M] {n : ℕ} (hM : HasProjectiveDimensionLE M n) :
    ∃ r : (ExactStructure.abelian (ModuleCat.{u} R)).FiniteResolution
      (finiteProjectiveModules R) M, r.length ≤ n ∧ r.IsMinimal := by
  induction n generalizing M with
  | zero =>
    have : Projective M := (projective_iff_hasProjectiveDimensionLE_zero M).2 hM
    have : Module.Projective R M := ModuleCat.projective_of_module_projective M
    exact ⟨.base (finiteProjectiveModules_iff.2 ⟨inferInstance, inferInstance⟩), by simp, by simp⟩
  | succ n ih =>
    -- Cover `M` minimally by a finite free module and resolve the kernel.
    obtain ⟨f, hf, hker⟩ := IsLocalRing.exists_surjective_ker_le_maximalIdeal_smul R M
    let S := f.shortComplexKer
    have hS : S.ShortExact := f.shortExact_shortComplexKer hf
    have : Module.Finite R S.X₁ := inferInstanceAs (Module.Finite R (LinearMap.ker f))
    have : Projective S.X₂ := ModuleCat.projective_of_categoryTheory_projective _
    obtain ⟨r, hr, hmin⟩ := ih ((hS.hasProjectiveDimensionLT_X₃_iff n inferInstance).1 hM)
    refine ⟨.step (finiteProjectiveModules_iff.2 ⟨inferInstance, inferInstance⟩)
      S.f S.g S.zero ((ExactStructure.abelian_conflation S).2 hS) r, by simpa using hr,
      .step _ _ _ _ _ (by simpa [S] using hker) hmin⟩

end TauCeti
