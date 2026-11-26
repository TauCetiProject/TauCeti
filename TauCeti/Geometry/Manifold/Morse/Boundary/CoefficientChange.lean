/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Boundary.SignedChainComplex
public import TauCeti.Algebra.Category.ModuleCat.ChangeOfRings

/-!
# Change of coefficients in the integral Morse complex

Let `f` be a Morse function on a compact boundaryless manifold, `X` a pseudo-gradient adapted to
`f`, and `𝔬 : TauCeti.MorseOrientation f X` orientations of the unstable manifolds. The coefficients
of the integral Morse boundary `TauCeti.IsAdaptedPseudoGradient.signedMorseBoundary` are integers,
the signed counts of trajectories, so the Morse chain complexes
`TauCeti.IsAdaptedPseudoGradient.signedMorseComplex` with coefficients in different rings are
determined by a single integral matrix. This file makes this precise.

* **`∂² = 0` passes along ring homomorphisms.** If the boundary with coefficients in `R` squares to
  zero, so does the boundary with coefficients in any ring `S` receiving a ring homomorphism from
  `R` (`signedMorseBoundary_comp_signedMorseBoundary_eq_zero_of_ringHom`). In particular `∂² = 0`
  over `ℤ` gives `∂² = 0` with coefficients in every ring, along `Int.castRingHom`.
* **The complex with coefficients in `S` is the extension of scalars of the complex with
  coefficients in `R`.** For an `R`-algebra `S`, extending the scalars of the Morse complex with
  coefficients in `R` to `S` gives the Morse complex with coefficients in `S`
  (`signedMorseComplexBaseChangeIso`): the term of degree `n` of the first is
  `S ⊗_R (R-chains of index n)`, and `s ⊗ c` corresponds to `s` times the chain `c` with its
  coefficients mapped to `S`. For `R = ℤ` this says that the Morse complex with coefficients in a
  commutative ring `S` is `S ⊗_ℤ CM_*(f; ℤ)`.
* **Reduction modulo two.** Under the Morse–Smale condition, extending the scalars of the integral
  Morse complex to `ZMod 2` gives the mod-two Morse complex
  `TauCeti.IsAdaptedPseudoGradient.IsMorseSmale.morseComplex`, whatever the orientations
  (`IsMorseSmale.signedMorseComplexBaseChangeIsoMorseComplex`).

## Main declarations

In the namespace `TauCeti.IsAdaptedPseudoGradient`:

* `signedMorseBoundary_comp_signedMorseBoundary_eq_zero_of_ringHom`: `∂² = 0` passes along ring
  homomorphisms.
* `signedMorseComplexBaseChangeIso`: the extension of scalars of the Morse complex.
* `signedMorseComplexBaseChangeIso_hom_f_tmul`, `signedMorseComplexBaseChangeIso_inv_f_single`:
  its values on `s ⊗ c` and, for its inverse, on `s • p`.
* `IsMorseSmale.signedMorseComplexBaseChangeIsoMorseComplex`: the reduction modulo two, with
  values `IsMorseSmale.signedMorseComplexBaseChangeIsoMorseComplex_hom_f_tmul` and
  `IsMorseSmale.signedMorseComplexBaseChangeIsoMorseComplex_inv_f_single`.

## References

* M. Hutchings, *Lecture notes on Morse homology (with an eye towards Floer theory and
  pseudoholomorphic curves)*, 2002, §2.3 (the Morse complex over `ℤ` and with other
  coefficients).
* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Chapter 4 (the Morse complex with integer coefficients).
-/

public section

open CategoryTheory
open scoped ContDiff Manifold TensorProduct ChangeOfRings

universe u

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] [T2Space M]
  {f : M → ℝ} {X : (x : M) → TangentSpace 𝓘(ℝ, E) x}

namespace IsAdaptedPseudoGradient

variable {hX : IsAdaptedPseudoGradient f X} {𝔬 : MorseOrientation f X}
  {hf : IsMorse 𝓘(ℝ, E) f}

/-- **`∂² = 0` passes along ring homomorphisms.** If the integral Morse boundary with coefficients
in `R` squares to zero, then so does the boundary with coefficients in `S`, for any ring
homomorphism `g : R →+* S`. The boundary of the chain `a • p` with coefficients in `S` is `a` times
the image under `g` of the boundary of `p` with coefficients in `R`. In particular `∂² = 0` over `ℤ`
gives `∂² = 0` with coefficients in every ring, along `Int.castRingHom`. -/
theorem signedMorseBoundary_comp_signedMorseBoundary_eq_zero_of_ringHom {R S : Type*} [Ring R]
    [Ring S] (g : R →+* S)
    (hsq : hX.signedMorseBoundary 𝔬 hf R ∘ₗ hX.signedMorseBoundary 𝔬 hf R = 0) :
    hX.signedMorseBoundary 𝔬 hf S ∘ₗ hX.signedMorseBoundary 𝔬 hf S = 0 := by
  refine Finsupp.lhom_ext fun p a ↦ ?_
  -- `mapRange g` intertwines `∂ ∘ ∂` with coefficients in `R` and in `S`, and `single p a` is
  -- `a` times the image of `single p 1`.
  have := congrArg (Finsupp.mapRange g (map_zero g)) (LinearMap.congr_fun hsq (Finsupp.single p 1))
  simp only [LinearMap.comp_apply, LinearMap.zero_apply, Finsupp.mapRange_zero,
    mapRange_signedMorseBoundary, Finsupp.mapRange_single, map_one] at this
  rw [LinearMap.comp_apply, ← Finsupp.smul_single_one, map_smul, map_smul, this, smul_zero,
    LinearMap.zero_apply]

section BaseChange

-- Mathlib's `ModuleCat.extendScalars` raises the universe of the modules to that of `S`, so the two
-- coefficient rings share a universe for the extended complex to be compared with the complex
-- with coefficients in `S`.
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
  (hsq : hX.signedMorseBoundary 𝔬 hf R ∘ₗ hX.signedMorseBoundary 𝔬 hf R = 0)

variable (hX 𝔬 hf S) in
/-- **Change of coefficients in the Morse complex.** For an `R`-algebra `S`, extending the scalars
of the integral Morse complex with coefficients in `R` to `S` gives the integral Morse complex with
coefficients in `S`. In each degree it is `ModuleCat.extendScalarsFinsuppIso`, which sends `s ⊗ c`
to `s` times the chain `c` with its coefficients mapped to `S`; these commute with the
differentials, because both differentials are given by the same integral matrix. For `R = ℤ`, the
Morse complex with coefficients in a commutative ring `S` is thus `S ⊗_ℤ CM_*(f; ℤ)`. -/
noncomputable def signedMorseComplexBaseChangeIso :
    ((ModuleCat.extendScalars (algebraMap R S)).mapHomologicalComplex
        (ComplexShape.down ℕ)).obj (hX.signedMorseComplex 𝔬 hf R hsq) ≅
      hX.signedMorseComplex 𝔬 hf S
        (signedMorseBoundary_comp_signedMorseBoundary_eq_zero_of_ringHom (algebraMap R S) hsq) :=
  HomologicalComplex.Hom.isoOfComponents (fun _ ↦ ModuleCat.extendScalarsFinsuppIso _) <| by
    rintro _ n rfl
    rw [Functor.mapHomologicalComplex_obj_d, signedMorseComplex_d, signedMorseComplex_d]
    exact (ModuleCat.extendScalarsFinsuppIso_hom_naturality _ _
      (mapRange_signedMorseBoundaryAt hf (algebraMap R S))).symm

/-- The change of coefficients `signedMorseComplexBaseChangeIso` sends `s ⊗ c` to `s` times the
chain `c` with its coefficients mapped to `S`. -/
-- Not `@[simp]`: `simp` rewrites the terms of the extended complex inside the type of the
-- left-hand side (`Functor.mapHomologicalComplex_obj_X`), so it is not in simp-normal form.
theorem signedMorseComplexBaseChangeIso_hom_f_tmul (n : ℕ) (s : S)
    (c : {p : criticalPoints 𝓘(ℝ, E) f // manifoldMorseIndex 𝓘(ℝ, E) f p = n} →₀ R) :
    (hX.signedMorseComplexBaseChangeIso 𝔬 hf S hsq).hom.f n (s ⊗ₜ[R, algebraMap R S] c) =
      s • Finsupp.mapRange (algebraMap R S) (map_zero _) c :=
  ModuleCat.extendScalarsFinsuppIso_hom_tmul _ s c

/-- The inverse of the change of coefficients `signedMorseComplexBaseChangeIso` sends the chain
`s • p` with coefficients in `S` to `s ⊗ p`. -/
-- Not `@[simp]`, for the same reason as `signedMorseComplexBaseChangeIso_hom_f_tmul`.
theorem signedMorseComplexBaseChangeIso_inv_f_single (n : ℕ)
    (p : {p : criticalPoints 𝓘(ℝ, E) f // manifoldMorseIndex 𝓘(ℝ, E) f p = n}) (s : S) :
    (hX.signedMorseComplexBaseChangeIso 𝔬 hf S hsq).inv.f n (Finsupp.single p s) =
      s ⊗ₜ[R, algebraMap R S] (Finsupp.single p 1 : (hX.signedMorseComplex 𝔬 hf R hsq).X n) :=
  ModuleCat.extendScalarsFinsuppIso_inv_single _ p s

end BaseChange

namespace IsMorseSmale

variable (h : hX.IsMorseSmale)

variable (𝔬 hf) in
/-- **The reduction of the integral Morse complex modulo two.** Under the Morse–Smale condition,
extending the scalars of the integral Morse complex to `ZMod 2` gives the mod-two Morse complex,
whatever the orientations: modulo two the signs of the trajectories disappear, and the signed
counts become the numbers of trajectories. -/
noncomputable def signedMorseComplexBaseChangeIsoMorseComplex
    (hsq : hX.signedMorseBoundary 𝔬 hf ℤ ∘ₗ hX.signedMorseBoundary 𝔬 hf ℤ = 0) :
    ((ModuleCat.extendScalars (algebraMap ℤ (ZMod 2))).mapHomologicalComplex
        (ComplexShape.down ℕ)).obj (hX.signedMorseComplex 𝔬 hf ℤ hsq) ≅ h.morseComplex hf :=
  hX.signedMorseComplexBaseChangeIso 𝔬 hf (ZMod 2) hsq ≪≫
    eqToIso (h.signedMorseComplex_zmod_two _)

/-- The reduction modulo two `signedMorseComplexBaseChangeIsoMorseComplex` sends `s ⊗ c` to `s`
times the chain `c` reduced modulo two. -/
-- Not `@[simp]`, for the same reason as `signedMorseComplexBaseChangeIso_hom_f_tmul`. The
-- right-hand side is stated in `_ →₀ ZMod 2`: with the module structure of the term of the
-- mod-two complex, checking the proof would compare the two complexes, differentials included.
theorem signedMorseComplexBaseChangeIsoMorseComplex_hom_f_tmul
    (hsq : hX.signedMorseBoundary 𝔬 hf ℤ ∘ₗ hX.signedMorseBoundary 𝔬 hf ℤ = 0) (n : ℕ)
    (s : ZMod 2)
    (c : {p : criticalPoints 𝓘(ℝ, E) f // manifoldMorseIndex 𝓘(ℝ, E) f p = n} →₀ ℤ) :
    (h.signedMorseComplexBaseChangeIsoMorseComplex 𝔬 hf hsq).hom.f n
        (s ⊗ₜ[ℤ, algebraMap ℤ (ZMod 2)] c) =
      (s • Finsupp.mapRange (algebraMap ℤ (ZMod 2)) (map_zero _) c :
        {p : criticalPoints 𝓘(ℝ, E) f // manifoldMorseIndex 𝓘(ℝ, E) f p = n} →₀ ZMod 2) := by
  simp only [signedMorseComplexBaseChangeIsoMorseComplex, Iso.trans_hom, eqToIso.hom,
    HomologicalComplex.comp_f, HomologicalComplex.eqToHom_f, ModuleCat.hom_comp]
  exact signedMorseComplexBaseChangeIso_hom_f_tmul (hsq := hsq) n s c

/-- The inverse of the reduction modulo two `signedMorseComplexBaseChangeIsoMorseComplex` sends the
chain `s • p` with coefficients in `ZMod 2` to `s ⊗ p`. -/
-- Not `@[simp]`, for the same reason as `signedMorseComplexBaseChangeIso_hom_f_tmul`.
theorem signedMorseComplexBaseChangeIsoMorseComplex_inv_f_single
    (hsq : hX.signedMorseBoundary 𝔬 hf ℤ ∘ₗ hX.signedMorseBoundary 𝔬 hf ℤ = 0) (n : ℕ)
    (p : {p : criticalPoints 𝓘(ℝ, E) f // manifoldMorseIndex 𝓘(ℝ, E) f p = n}) (s : ZMod 2) :
    (h.signedMorseComplexBaseChangeIsoMorseComplex 𝔬 hf hsq).inv.f n (Finsupp.single p s) =
      s ⊗ₜ[ℤ, algebraMap ℤ (ZMod 2)]
        (Finsupp.single p 1 : (hX.signedMorseComplex 𝔬 hf ℤ hsq).X n) := by
  simp only [signedMorseComplexBaseChangeIsoMorseComplex, Iso.trans_inv, eqToIso.inv,
    HomologicalComplex.comp_f, HomologicalComplex.eqToHom_f, ModuleCat.hom_comp]
  exact signedMorseComplexBaseChangeIso_inv_f_single (hsq := hsq) n p s

end IsMorseSmale

end IsAdaptedPseudoGradient

end TauCeti
