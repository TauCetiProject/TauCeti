/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.CategoryTheory.Abelian.Projective.Dimension
public import Mathlib.CategoryTheory.Monoidal.Tor

import Mathlib.Algebra.Category.ModuleCat.Descent
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import Mathlib.CategoryTheory.Adjunction.FullyFaithful
import Mathlib.CategoryTheory.Preadditive.Projective.Preserves
import Mathlib.RingTheory.Flat.Basic
import TauCeti.Algebra.Category.ModuleCat.ChangeOfRings
import TauCeti.Algebra.Category.ModuleCat.Monoidal.Tor
import TauCeti.Algebra.Category.ModuleCat.RestrictScalars
import TauCeti.CategoryTheory.Abelian.Projective.Dimension

/-!
# Projective dimension under `Tor`-independent base change

Let `f : R →+* S` be a homomorphism of commutative rings and `M` an `R`-module such that
`Tor_{i+1}^R(M, S) = 0` for all `i : ℕ`. Then tensoring a projective resolution of `M` with `S`
remains exact, so the projective dimension does not increase under extension of scalars:

```text
pd_S (S ⊗[R] M) ≤ pd_R M.
```

In particular, if `f : R →+* S` is a surjective homological epimorphism—meaning `f` is surjective
and `Tor_{i+1}^R(S, S) = 0` for all `i` (for instance, any surjection of perfect rings in
characteristic `p`)—then `Tor_{i+1}^R(M|_R, S) = 0` for every `S`-module `M`, and the counit
`S ⊗[R] M|_R ≅ M` is an isomorphism, yielding `pd_S M ≤ pd_R (M|_R)`.

## Main results

* `ModuleCat.hasProjectiveDimensionLT_extendScalars_of_isZero_Tor`: if `Tor_{i+1}^R(M, S) = 0` for
  all `i`, then `HasProjectiveDimensionLT M n` implies
  `HasProjectiveDimensionLT ((extendScalars f).obj M) n`.
* `ModuleCat.projectiveDimension_extendScalars_le_of_isZero_Tor`: the corresponding inequality
  `projectiveDimension ((extendScalars f).obj M) ≤ projectiveDimension M`.
* `ModuleCat.hasProjectiveDimensionLT_of_surjective_of_isZero_Tor_succ`: for a surjective
  homological epimorphism `f : R →+* S` and an `S`-module `M`,
  `HasProjectiveDimensionLT ((restrictScalars f).obj M) n` implies `HasProjectiveDimensionLT M n`.
* `ModuleCat.projectiveDimension_le_restrictScalars_of_surjective_of_isZero_Tor_succ`: the
  corresponding inequality
  `projectiveDimension M ≤ projectiveDimension ((restrictScalars f).obj M)`.
-/

public section

namespace ModuleCat

open CategoryTheory Limits

universe u

variable {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)

/-- **`Tor`-independent base change does not increase projective dimension.** If `M` is an
`R`-module with `Tor_{i+1}^R(M, S) = 0` for every `i`, and `M` has projective dimension less
than `n`, then `(extendScalars f).obj M` has projective dimension less than `n`. -/
theorem hasProjectiveDimensionLT_extendScalars_of_isZero_Tor (M : ModuleCat.{u} R) {n : ℕ}
    (hM : HasProjectiveDimensionLT M n)
    (hTor : ∀ i, IsZero (((Tor (ModuleCat.{u} R) (i + 1)).obj M).obj
      ((restrictScalars f).obj (of S S)))) :
    HasProjectiveDimensionLT ((extendScalars.{u, u, u} f).obj M) n := by
  have : PreservesColimitsOfSize.{0, 0} (extendScalars.{u, u, u} f) :=
    (extendRestrictScalarsAdj.{u, u, u} f).leftAdjoint_preservesColimits
  have : PreservesFiniteColimits (extendScalars.{u, u, u} f) :=
    PreservesColimitsOfSize.preservesFiniteColimits _
  have : (extendScalars.{u, u, u} f).PreservesProjectiveObjects :=
    Functor.preservesProjectiveObjects_of_adjunction_of_preservesEpimorphisms
      (extendRestrictScalarsAdj.{u, u, u} f)
  induction n generalizing M with
  | zero =>
    rw [hasProjectiveDimensionLT_zero_iff_isZero] at hM ⊢
    exact (extendScalars.{u, u, u} f).map_isZero hM
  | succ n ih =>
    cases n with
    | zero =>
      have : Projective M := projective_iff_hasProjectiveDimensionLT_one.mpr hM
      exact projective_iff_hasProjectiveDimensionLT_one.mp inferInstance
    | succ d =>
      -- Shift along a projective presentation `0 → K → P → M → 0`; vanishing `Tor₁(M, S)` makes
      -- `S ⊗ K → S ⊗ P` injective, and dimension shifting propagates vanishing `Tor_{i+1}(-, S)`
      -- from `M` to `K`.
      let g := (Projective.π M).hom
      have hg : Function.Surjective g := (ModuleCat.epi_iff_surjective _).mp inferInstance
      let S₀ := g.shortComplexKer
      have hS₀ : S₀.ShortExact := g.shortExact_shortComplexKer hg
      have hP : Projective S₀.X₂ := inferInstanceAs (Projective (Projective.over M))
      have hK : HasProjectiveDimensionLT S₀.X₁ (d + 1) :=
        (hS₀.hasProjectiveDimensionLT_X₃_iff d hP).mp hM
      have hPFlat : Module.Flat R S₀.X₂ :=
        have : Module.Projective R S₀.X₂ := (IsProjective.iff_projective S₀.X₂).mpr hP
        Module.Flat.of_projective
      have hKTor : ∀ i, IsZero (((Tor (ModuleCat.{u} R) (i + 1)).obj S₀.X₁).obj
          ((restrictScalars f).obj (of S S))) := fun i ↦
        hS₀.isZero_Tor_X₁ _ (hTor (i + 1)) (isZero_Tor_succ_of_flat S₀.X₂ _ i)
      obtain ⟨hex, hepi⟩ :=
        (Functor.preservesFiniteColimits_iff_forall_exact_map_and_epi
          (extendScalars.{u, u, u} f)).mp inferInstance S₀ hS₀
      have hmono : Mono ((extendScalars.{u, u, u} f).map S₀.f) :=
        (mono_extendScalars_map_iff_rTensor_injective f S₀.f).mpr
          (hS₀.rTensor_injective_of_isZero_Tor_one _ (hTor 0))
      have hS₁ : (S₀.map (extendScalars.{u, u, u} f)).ShortExact :=
        { exact := hex, mono_f := hmono, epi_g := hepi }
      have hK' : HasProjectiveDimensionLT ((extendScalars.{u, u, u} f).obj S₀.X₁) (d + 1) :=
        ih S₀.X₁ hK hKTor
      have hP' : Projective ((extendScalars.{u, u, u} f).obj S₀.X₂) := inferInstance
      exact (hS₁.hasProjectiveDimensionLT_X₃_iff d hP').mpr hK'

/-- **`Tor`-independent base change does not increase projective dimension**:
`pd_S (S ⊗[R] M) ≤ pd_R M` whenever `Tor_{i+1}^R(M, S) = 0` for all `i`. -/
theorem projectiveDimension_extendScalars_le_of_isZero_Tor (M : ModuleCat.{u} R)
    (hTor : ∀ i, IsZero (((Tor (ModuleCat.{u} R) (i + 1)).obj M).obj
      ((restrictScalars f).obj (of S S)))) :
    projectiveDimension ((extendScalars.{u, u, u} f).obj M) ≤ projectiveDimension M :=
  projectiveDimension_le_of_hasProjectiveDimensionLT fun _ hM ↦
    hasProjectiveDimensionLT_extendScalars_of_isZero_Tor f M hM hTor

/-- **Projective dimension bound along a surjective homological epimorphism.** Let `f : R →+* S`
be a surjective ring homomorphism with `Tor_{i+1}^R(S, S) = 0` for all `i`. If an `S`-module `M`
has projective dimension less than `n` over `R`, then it has projective dimension less than `n`
over `S`. -/
theorem hasProjectiveDimensionLT_of_surjective_of_isZero_Tor_succ (hf : Function.Surjective f)
    (hS : ∀ i, IsZero (((Tor (ModuleCat.{u} R) (i + 1)).obj
      ((restrictScalars f).obj (of S S))).obj ((restrictScalars f).obj (of S S))))
    (M : ModuleCat.{u} S) {n : ℕ}
    (hM : HasProjectiveDimensionLT ((restrictScalars f).obj M) n) :
    HasProjectiveDimensionLT M n := by
  have : (restrictScalars.{u} f).Full := f.full_restrictScalars hf
  have : HasProjectiveDimensionLT
      ((restrictScalars.{u} f ⋙ extendScalars.{u, u, u} f).obj M) n :=
    hasProjectiveDimensionLT_extendScalars_of_isZero_Tor f ((restrictScalars f).obj M) hM
      (isZero_Tor_succ_restrictScalars_of_surjective f hf hS M)
  exact hasProjectiveDimensionLT_of_iso
    (asIso ((extendRestrictScalarsAdj.{u, u, u} f).counit.app M)) n

/-- **Projective dimension along a surjective homological epimorphism**: if `f : R →+* S` is
surjective and `Tor_{i+1}^R(S, S) = 0` for all `i`, then `pd_S M ≤ pd_R (M|_R)` for every
`S`-module `M`. -/
theorem projectiveDimension_le_restrictScalars_of_surjective_of_isZero_Tor_succ
    (hf : Function.Surjective f)
    (hS : ∀ i, IsZero (((Tor (ModuleCat.{u} R) (i + 1)).obj
      ((restrictScalars f).obj (of S S))).obj ((restrictScalars f).obj (of S S))))
    (M : ModuleCat.{u} S) :
    projectiveDimension M ≤ projectiveDimension ((restrictScalars f).obj M) :=
  projectiveDimension_le_of_hasProjectiveDimensionLT fun _ hM ↦
    hasProjectiveDimensionLT_of_surjective_of_isZero_Tor_succ f hf hS M hM

end ModuleCat
