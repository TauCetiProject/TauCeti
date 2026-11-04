/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.TotallyAcyclic.Basic
public import TauCeti.Algebra.Homology.ShortComplex.Splice
public import TauCeti.LinearAlgebra.Exact

/-!
# Complete resolutions from syzygies and cosyzygies

Let `A` be a ring. Splicing short exact sequences `0 ⟶ Xₙ ⟶ Pₙ ⟶ Xₙ₊₁ ⟶ 0` of `A`-modules, with
`Pₙ` finitely generated projective and every functional on `Xₙ` extending to `Pₙ`, gives a totally
acyclic complex: it is acyclic, and its `A`-dual is acyclic because a functional on `Pₙ` vanishing
on `Xₙ` factors through `Xₙ₊₁`, where it extends to `Pₙ₊₁`.

Consequently, a module is Gorenstein-projective as soon as it lies in a class `R` of modules that
admit such sequences `0 ⟶ X ⟶ P ⟶ X' ⟶ 0` with `X'` again in `R` (cosyzygies), inside a class `L`
of modules that admit such sequences `0 ⟶ X' ⟶ P ⟶ X ⟶ 0` with `X'` again in `L` (syzygies).

## Main results

* `CochainComplex.isTotallyAcyclic_splice`: a splice of short exact sequences with finitely
  generated projective middle terms, along which functionals extend, is totally acyclic.
* `TauCeti.isGorensteinProjective_of_isCompleteResolutionStep`: modules with iterated syzygies
  and cosyzygies of this form are Gorenstein-projective.
-/

public section

open CategoryTheory

universe v u

namespace CochainComplex

variable {A : Type u} [Ring A] (S : ℤ → ShortComplex (ModuleCat.{v} A))
  (e : ∀ n, (S n).X₃ ≅ (S (n + 1)).X₁)

/-- **Splices along which functionals extend are totally acyclic**: splicing short exact
sequences with finitely generated projective middle terms, such that every functional on the
first term of each sequence extends to the middle term, gives a totally acyclic complex. -/
theorem isTotallyAcyclic_splice (hS : ∀ n, (S n).ShortExact)
    (hfin : ∀ n, Module.Finite A (S n).X₂) (hproj : ∀ n, Projective (S n).X₂)
    (hext : ∀ n (φ : (S n).X₁ →ₗ[A] A), ∃ ψ : (S n).X₂ →ₗ[A] A, ψ ∘ₗ (S n).f.hom = φ) :
    (splice S e).IsTotallyAcyclic where
  finite := hfin
  projective := hproj
  acyclic := acyclic_splice S e hS
  exact_dual i j k hij hjk := by
    subst hij hjk
    rw [splice_d, splice_d]
    intro φ
    simp only [LinearMap.lcomp_apply', Set.mem_range]
    refine ⟨fun hφ ↦ ?_, ?_⟩
    · -- `φ` vanishes on the first term of the `(i + 1)`-st sequence, the image of the differential.
      have h₁ : φ ∘ₗ (S (i + 1)).f.hom = 0 := by
        ext x
        obtain ⟨y, hy⟩ := (hS i).moduleCat_surjective_g ((e i).inv x)
        have := LinearMap.congr_fun hφ y
        simp only [ModuleCat.hom_comp, LinearMap.comp_apply, LinearMap.zero_apply] at this
        simpa [hy] using this
      -- So `φ` factors through the last term, and extends across the next sequence.
      obtain ⟨φ', hφ'⟩ := ((((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
        (hS (i + 1)).exact).lcomp_of_surjective (T := Aᵐᵒᵖ) A (hS (i + 1)).moduleCat_surjective_g)
          φ).1 h₁
      obtain ⟨ψ, hψ⟩ := hext (i + 1 + 1) (φ' ∘ₗ (e (i + 1)).inv.hom)
      refine ⟨ψ, ?_⟩
      rw [← hφ']
      ext x
      have := LinearMap.congr_fun hψ ((e (i + 1)).hom ((S (i + 1)).g x))
      simp only [LinearMap.comp_apply] at this
      simp [this]
    · rintro ⟨ψ, rfl⟩
      ext x
      simp

end CochainComplex

namespace TauCeti

variable {A : Type u} [Ring A]

/-- A short exact sequence `0 ⟶ X₁ ⟶ P ⟶ X₃ ⟶ 0` with `P` finitely generated projective, along
which every functional on `X₁` extends to `P`. -/
structure IsCompleteResolutionStep (S : ShortComplex (ModuleCat.{v} A)) : Prop where
  shortExact : S.ShortExact
  finite : Module.Finite A S.X₂
  projective : Projective S.X₂
  exists_comp_eq (φ : S.X₁ →ₗ[A] A) : ∃ ψ : S.X₂ →ₗ[A] A, ψ ∘ₗ S.f.hom = φ

/-- **Gorenstein-projective modules from syzygies and cosyzygies.** Let `R ≤ L` be classes of
modules. Suppose every module `X` in `L` is the last term of a sequence `0 ⟶ X' ⟶ P ⟶ X ⟶ 0` with
`X'` in `L`, and every `X` in `R` is the first term of a sequence `0 ⟶ X ⟶ P ⟶ X' ⟶ 0` with `X'` in
`R`, where `P` is finitely generated projective and functionals extend from the first term to `P`.
Then every module in `R` is Gorenstein-projective. -/
theorem isGorensteinProjective_of_isCompleteResolutionStep (L R : ObjectProperty (ModuleCat.{v} A))
    (hRL : R ≤ L)
    (hL : ∀ X, L X → ∃ S : ShortComplex (ModuleCat.{v} A), IsCompleteResolutionStep S ∧ L S.X₁ ∧
      Nonempty (S.X₃ ≅ X))
    (hR : ∀ X, R X → ∃ S : ShortComplex (ModuleCat.{v} A), IsCompleteResolutionStep S ∧ R S.X₃ ∧
      Nonempty (S.X₁ ≅ X))
    {M : ModuleCat.{v} A} (hM : R M) : IsGorensteinProjective A M := by
  choose fL hfL hLX₁ eL using hL
  choose fR hfR hRX₃ eR using hR
  -- The cosyzygies `Rn n` and syzygies `Ln n` of `M`.
  let Rn : ℕ → {X // R X} := fun n ↦ Nat.rec ⟨M, hM⟩ (fun _ X ↦ ⟨_, hRX₃ X.1 X.2⟩) n
  let Ln : ℕ → {X // L X} := fun n ↦ Nat.rec ⟨M, hRL _ hM⟩ (fun _ X ↦ ⟨_, hLX₁ X.1 X.2⟩) n
  let S : ℤ → ShortComplex (ModuleCat.{v} A) := fun n ↦ match n with
    | .ofNat n => fR (Rn n).1 (Rn n).2
    | .negSucc n => fL (Ln n).1 (Ln n).2
  -- The branches type-check by computation: `Int.ofNat n + 1`, `Int.negSucc 0 + 1` and
  -- `Int.negSucc (n + 1) + 1` reduce to `.ofNat (n + 1)`, `.ofNat 0` and `.negSucc n`, and `Rn 0`,
  -- `Ln 0` reduce to `M` through `Nat.rec`. The same splicing pattern is used by
  -- `TauCeti.ExactStructure.IsFrobenius.completeResolution`.
  let e : ∀ n, (S n).X₃ ≅ (S (n + 1)).X₁ := fun n ↦ match n with
    | .ofNat n => (Classical.choice (eR (Rn (n + 1)).1 (Rn (n + 1)).2)).symm
    | .negSucc 0 => Classical.choice (eL (Ln 0).1 (Ln 0).2) ≪≫
        (Classical.choice (eR (Rn 0).1 (Rn 0).2)).symm
    | .negSucc (n + 1) => Classical.choice (eL (Ln (n + 1)).1 (Ln (n + 1)).2)
  have hS (n : ℤ) : IsCompleteResolutionStep (S n) := by
    cases n with
    | ofNat n => exact hfR _ _
    | negSucc n => exact hfL _ _
  refine (isGorensteinProjective_iff M).2 ⟨CochainComplex.splice S e,
    CochainComplex.isTotallyAcyclic_splice S e (fun n ↦ (hS n).shortExact) (fun n ↦ (hS n).finite)
      (fun n ↦ (hS n).projective) (fun n ↦ (hS n).exists_comp_eq),
    ⟨(CochainComplex.spliceCyclesIso S e (fun n ↦ (hS n).shortExact) 0).symm ≪≫
      Classical.choice (eR (Rn 0).1 (Rn 0).2)⟩⟩

end TauCeti
