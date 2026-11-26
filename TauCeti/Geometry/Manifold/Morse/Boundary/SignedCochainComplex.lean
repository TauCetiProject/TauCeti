/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Boundary.Cochain
public import TauCeti.Geometry.Manifold.Morse.Boundary.SignedChainComplex
public import TauCeti.LinearAlgebra.Finsupp.IntLinearMap

/-!
# The integral Morse cochain complex

Let `f` be a Morse function on a compact boundaryless manifold `M`, `X` a pseudo-gradient adapted
to `f`, and `𝔬 : TauCeti.MorseOrientation f X` orientations of the unstable manifolds, and suppose
that the integral Morse boundary squares to zero, so that the integral Morse chain complex
`CM_*(f; ℤ)` (`TauCeti.IsAdaptedPseudoGradient.signedMorseComplex`) is defined. For a ring `R`, the
**Morse cochain complex with coefficients in `R`**
(`TauCeti.IsAdaptedPseudoGradient.signedMorseCochainComplex`) is

`C^n_M(f; R) = Hom_ℤ(CM_n(f; ℤ), R)`, with coboundary `δa = a ∘ ∂`.

Its cohomology is the Morse cohomology of `(f, X)` with coefficients in `R`. The cochains are the
additive maps on the integral chains, so the construction only uses `∂² = 0` over `ℤ`, and the
signs of the trajectories enter through the integral boundary. It makes no orientability
assumption on `M`. The cochains of index `n` form an `R`-module through the values, and the
coboundary from index `n` to index `n + 1` is the transpose of the graded integral boundary
`TauCeti.IsAdaptedPseudoGradient.signedMorseBoundaryAt`.

**Change of coefficients.** For a commutative ring `R`, an additive map on the free abelian group
on the critical points of index `n` is determined by its values on the critical points, and so is
an `R`-linear form on the free `R`-module on them. This identifies the integral cochains with the
`R`-linear forms on the Morse chains with coefficients in `R`, compatibly with the coboundaries,
because the boundary with coefficients in `R` is the integral boundary with its coefficients cast
into `R` (`TauCeti.IsAdaptedPseudoGradient.mapRange_signedMorseBoundaryAt`). So the integral Morse
cochain complex is the `R`-dual of the Morse chain complex with coefficients in `R`
(`TauCeti.IsAdaptedPseudoGradient.signedMorseCochainComplexIso`). With coefficients in `ZMod 2`
and under the Morse–Smale condition, it is the mod-two Morse cochain complex
`TauCeti.IsAdaptedPseudoGradient.IsMorseSmale.morseCochainComplex`, whatever the orientations
(`TauCeti.IsAdaptedPseudoGradient.IsMorseSmale.signedMorseCochainComplexIsoMorseCochainComplex`).

The cochains, and so the Morse cohomology, vanish above the dimension of `M`.

## Main declarations

In the namespace `TauCeti.IsAdaptedPseudoGradient`:

* `signedMorseCochainComplex`: the Morse cochain complex `Hom_ℤ(CM_*(f; ℤ), R)`.
* `signedMorseCochainComplex_X`, `signedMorseCochainComplex_d_apply`: its terms and its coboundary
  `δa = a ∘ ∂`.
* `isZero_homology_signedMorseCochainComplex_of_finrank_lt`: the Morse cohomology vanishes above
  the dimension.
* `nonempty_linearEquiv_homology_zero_signedMorseCochainComplex`: with a unique minimum and zero
  boundary into degree `0`, the Morse cohomology in degree `0` is `R`.
* `signedMorseCochainComplexIso`: over a commutative ring `R`, the integral Morse cochain complex
  is the `R`-dual of the Morse chain complex with coefficients in `R`.
* `IsMorseSmale.signedMorseCochainComplexIsoMorseCochainComplex`: with coefficients in `ZMod 2` it
  is the mod-two Morse cochain complex.

## References

* M. Hutchings, *Lecture notes on Morse homology (with an eye towards Floer theory and
  pseudoholomorphic curves)*, 2002, §3 (Morse cohomology as the homology of the dual complex).
* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Chapter 4 (the Morse complex with integer coefficients and Morse cohomology).
-/

public section

universe u v

open CategoryTheory Limits Module
open scoped ContDiff Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type u} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] [T2Space M]
  {f : M → ℝ} {X : (x : M) → TangentSpace 𝓘(ℝ, E) x}

namespace IsAdaptedPseudoGradient

variable {hX : IsAdaptedPseudoGradient f X} {𝔬 : MorseOrientation f X}
  {hf : IsMorse 𝓘(ℝ, E) f} {R : Type v} [Ring R]

variable (hX 𝔬 hf R) in
/-- **The Morse cochain complex with coefficients in a ring `R`.** When the integral Morse boundary
squares to zero, the cochain complex of `R`-modules whose term in degree `n` is the module
`Hom_ℤ(CM_n(f; ℤ), R)` of additive maps from the integral Morse chains of index `n` to `R`, with
coboundary `δa = a ∘ ∂` given by precomposition with the graded integral Morse boundary. Its
cohomology is the Morse cohomology of `f` and the pseudo-gradient with coefficients in `R`. -/
-- The body is exposed so that the terms of the complex compute to the modules of additive maps on
-- the integral Morse chains, which the statements of `signedMorseCochainComplex_X` and
-- `signedMorseCochainComplex_d` need.
@[expose]
noncomputable def signedMorseCochainComplex
    (hsq : hX.signedMorseBoundary 𝔬 hf ℤ ∘ₗ hX.signedMorseBoundary 𝔬 hf ℤ = 0) :
    CochainComplex (ModuleCat R) ℕ :=
  CochainComplex.of
    (fun n ↦ ModuleCat.of R
      (({p : criticalPoints 𝓘(ℝ, E) f // manifoldMorseIndex 𝓘(ℝ, E) f p = n} →₀ ℤ) →ₗ[ℤ] R))
    (fun n ↦ ModuleCat.ofHom (LinearMap.lcomp R R (hX.signedMorseBoundaryAt 𝔬 hf ℤ n)))
    fun n ↦ by
      have h := (signedMorseBoundaryAt_comp_signedMorseBoundaryAt_eq_zero_iff hf).2 hsq n
      ext a p
      -- The composite sends `a` to `a ∘ ∂ ∘ ∂ = 0`.
      exact (congrArg a (LinearMap.congr_fun h _)).trans (map_zero a)

variable (hsq : hX.signedMorseBoundary 𝔬 hf ℤ ∘ₗ hX.signedMorseBoundary 𝔬 hf ℤ = 0)

/-- The term of the Morse cochain complex in degree `n` is the module of additive maps from the
integral Morse chains of index `n` to `R`. -/
@[simp]
theorem signedMorseCochainComplex_X (n : ℕ) :
    (hX.signedMorseCochainComplex 𝔬 hf R hsq).X n = ModuleCat.of R
      (({p : criticalPoints 𝓘(ℝ, E) f // manifoldMorseIndex 𝓘(ℝ, E) f p = n} →₀ ℤ) →ₗ[ℤ] R) :=
  (rfl)

/-- The coboundary of the Morse cochain complex from degree `n` to degree `n + 1` is the transpose
of the graded integral Morse boundary from index `n + 1` to index `n`. -/
theorem signedMorseCochainComplex_d (n : ℕ) :
    (hX.signedMorseCochainComplex 𝔬 hf R hsq).d n (n + 1) =
      ModuleCat.ofHom (LinearMap.lcomp R R (hX.signedMorseBoundaryAt 𝔬 hf ℤ n)) := by
  simp [signedMorseCochainComplex]

/-- The Morse coboundary of a cochain `a` of index `n` is `a ∘ ∂`, its composite with the graded
integral Morse boundary from index `n + 1`. -/
@[simp]
theorem signedMorseCochainComplex_d_apply (n : ℕ)
    (a : ({p : criticalPoints 𝓘(ℝ, E) f // manifoldMorseIndex 𝓘(ℝ, E) f p = n} →₀ ℤ) →ₗ[ℤ] R) :
    (hX.signedMorseCochainComplex 𝔬 hf R hsq).d n (n + 1) a =
      a ∘ₗ hX.signedMorseBoundaryAt 𝔬 hf ℤ n := by
  rw [signedMorseCochainComplex_d]
  -- As in `signedMorseComplex_d_apply`, the morphism is typed between the terms of the complex,
  -- which are the modules of additive maps only by definition, so `simp` does not fire.
  exact ModuleCat.ofHom_apply _ a

/-- The Morse cochain complex vanishes above the dimension of `M`. -/
theorem isZero_signedMorseCochainComplex_X_of_finrank_lt {n : ℕ} (hn : finrank ℝ E < n) :
    IsZero ((hX.signedMorseCochainComplex 𝔬 hf R hsq).X n) := by
  rw [signedMorseCochainComplex_X, ModuleCat.isZero_iff_subsingleton]
  have : IsEmpty {p : criticalPoints 𝓘(ℝ, E) f // manifoldMorseIndex 𝓘(ℝ, E) f p = n} :=
    ⟨fun p ↦ (manifoldMorseIndex_le_finrank.trans_lt hn).ne p.property⟩
  infer_instance

/-- The Morse cohomology vanishes above the dimension of `M`. -/
theorem isZero_homology_signedMorseCochainComplex_of_finrank_lt {n : ℕ}
    (hn : finrank ℝ E < n) :
    IsZero ((hX.signedMorseCochainComplex 𝔬 hf R hsq).homology n) :=
  (HomologicalComplex.ExactAt.of_isZero
    (isZero_signedMorseCochainComplex_X_of_finrank_lt hsq hn)).isZero_homology

/-- **`H⁰ = R` with a unique minimum.** If `f` has a unique critical point `p` of index `0` and the
graded integral Morse boundary into index `0` vanishes, the Morse cohomology in degree `0` with
coefficients in `R` is `R`: the coboundary out of degree `0` is the transpose of that boundary, and
a cochain of index `0` is its value at `p`. -/
theorem nonempty_linearEquiv_homology_zero_signedMorseCochainComplex
    (h0 : hX.signedMorseBoundaryAt 𝔬 hf ℤ 0 = 0)
    (p : {p : criticalPoints 𝓘(ℝ, E) f // manifoldMorseIndex 𝓘(ℝ, E) f p = 0})
    (hp : ∀ q : {p : criticalPoints 𝓘(ℝ, E) f // manifoldMorseIndex 𝓘(ℝ, E) f p = 0}, q = p) :
    Nonempty ((hX.signedMorseCochainComplex 𝔬 hf R hsq).homology 0 ≃ₗ[R] R) := by
  let : Unique {p : criticalPoints 𝓘(ℝ, E) f // manifoldMorseIndex 𝓘(ℝ, E) f p = 0} := ⟨⟨p⟩, hp⟩
  set K := hX.signedMorseCochainComplex 𝔬 hf R hsq
  -- No coboundary enters degree `0`, and the coboundary out of it is the transpose of the
  -- boundary into degree `0`, which vanishes.
  have h₁ : K.d ((ComplexShape.up ℕ).prev 0) 0 = 0 := K.shape _ _ (by simp)
  have h₂ : K.d 0 ((ComplexShape.up ℕ).next 0) = 0 := by
    rw [CochainComplex.next, signedMorseCochainComplex_d, h0]
    ext a c
    -- Both sides are zero; the zero morphism is typed between the terms of `K`.
    simp only [ModuleCat.hom_ofHom, LinearMap.lcomp_apply', LinearMap.comp_zero]
    rfl
  exact ⟨(K.XIsoHomologyOfDEqZero 0 h₁ h₂).toLinearEquiv.symm.trans
    ((Finsupp.llift R ℤ R _).symm.trans (LinearEquiv.funUnique _ R R))⟩

/-! ### Change of coefficients -/

section CommRing

variable {R : Type v} [CommRing R]

/-- `Finsupp.intLinearMapEquiv`, with its values read as morphisms of modules into `R` lifted to
the universe of `S`, the form in which the Morse chain complex with coefficients in `R` is
dualized. -/
private noncomputable def intLinearMapEquivModuleCat (S : Type u) :
    ((S →₀ ℤ) →ₗ[ℤ] R) ≃ₗ[R]
      (ModuleCat.of R (S →₀ R) ⟶ ModuleCat.of R (ULift.{u} R)) :=
  Finsupp.intLinearMapEquiv S R R ≪≫ₗ (LinearEquiv.congrRight ULift.moduleEquiv).symm ≪≫ₗ
    (ModuleCat.homLinearEquiv (S := R) (M := ModuleCat.of R (S →₀ R))
      (N := ModuleCat.of R (ULift.{u} R))).symm

/-- The value of `intLinearMapEquivModuleCat` is that of `Finsupp.intLinearMapEquiv`. -/
private theorem intLinearMapEquivModuleCat_apply {S : Type u} (a : (S →₀ ℤ) →ₗ[ℤ] R)
    (c : S →₀ R) :
    (intLinearMapEquivModuleCat S a c).down = Finsupp.intLinearMapEquiv S R R a c :=
  -- The two outer equivalences only wrap the linear map into a morphism of `ModuleCat` and its
  -- values into `ULift`, and `simp` does not see through the coercion of the morphism to a function
  -- (`ConcreteCategory.hom`), so the identity is closed by unfolding.
  (rfl)

/-- The `R`-linear form associated with an integral cochain `a`, evaluated on the boundary of
`r • p` with coefficients in `R`, is `r` times the value of `a` on the integral boundary of `p`:
it is the value at `r • p` of the form associated with the coboundary `a ∘ ∂`. -/
private theorem intLinearMapEquiv_signedMorseBoundaryAt {n : ℕ}
    (a : ({q : criticalPoints 𝓘(ℝ, E) f // manifoldMorseIndex 𝓘(ℝ, E) f q = n} →₀ ℤ) →ₗ[ℤ] R)
    (p : {p : criticalPoints 𝓘(ℝ, E) f // manifoldMorseIndex 𝓘(ℝ, E) f p = n + 1}) (r : R) :
    (intLinearMapEquivModuleCat _ a
        (hX.signedMorseBoundaryAt 𝔬 hf R n (Finsupp.single p r))).down =
      (intLinearMapEquivModuleCat _ (a ∘ₗ hX.signedMorseBoundaryAt 𝔬 hf ℤ n)
        (Finsupp.single p r)).down := by
  have hp : hX.signedMorseBoundaryAt 𝔬 hf R n (Finsupp.single p r) =
      r • Finsupp.mapRange (Int.castAddHom R) (map_zero _)
        (hX.signedMorseBoundaryAt 𝔬 hf ℤ n (Finsupp.single p 1)) := by
    rw [mapRange_signedMorseBoundaryAt, ← map_smul]
    simp
  rw [intLinearMapEquivModuleCat_apply, intLinearMapEquivModuleCat_apply, hp, map_smul,
    Finsupp.intLinearMapEquiv_apply_mapRange, Finsupp.intLinearMapEquiv_apply_single,
    LinearMap.comp_apply]

variable (R) in
/-- **The integral Morse cochains are the `R`-dual of the Morse chains with coefficients in `R`.**
For a commutative ring `R`, reading an additive map from the integral Morse chains to `R` as the
`R`-linear form on the Morse chains with coefficients in `R` with the same values on the critical
points is an isomorphism from the Morse cochain complex `Hom_ℤ(CM_*(f; ℤ), R)` to the `R`-dual
`Hom_R(CM_*(f; R), R)` of the Morse chain complex with coefficients in `R`. Here `R` is lifted to
the universe of the chains. -/
noncomputable def signedMorseCochainComplexIso :
    hX.signedMorseCochainComplex 𝔬 hf R hsq ≅
      (hX.signedMorseComplex 𝔬 hf R
        (signedMorseBoundary_comp_signedMorseBoundary_eq_zero_of_int hsq R)).linearYonedaObj R
        (ModuleCat.of R (ULift.{u} R)) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n ↦ (intLinearMapEquivModuleCat
      {p : criticalPoints 𝓘(ℝ, E) f // manifoldMorseIndex 𝓘(ℝ, E) f p = n}).toModuleIso)
    fun i j hij ↦ by
      obtain rfl : i + 1 = j := hij
      rw [ChainComplex.linearYonedaObj_d, signedMorseComplex_d, signedMorseCochainComplex_d]
      ext a : 2
      refine ModuleCat.hom_ext (Finsupp.lhom_ext fun p r ↦ ULift.ext ?_)
      -- The terms of both complexes are the modules of `intLinearMapEquivModuleCat` only by
      -- definition (`signedMorseCochainComplex_X`, `signedMorseComplex_X`), so the elementwise
      -- identity is applied with `exact` rather than rewritten into the goal.
      exact intLinearMapEquiv_signedMorseBoundaryAt a p r

/-- The `R`-linear form associated with an integral cochain `a` of index `n` takes the value
`r * a p` at `r • p`, for every critical point `p` of index `n`. -/
-- The value of the isomorphism is a morphism of modules out of the chains with coefficients in `R`,
-- which are the terms of `signedMorseComplex` only by definition, so the source and target of the
-- morphism applied are named.
@[simp]
theorem signedMorseCochainComplexIso_hom_f_apply_single {n : ℕ}
    (a : ({p : criticalPoints 𝓘(ℝ, E) f // manifoldMorseIndex 𝓘(ℝ, E) f p = n} →₀ ℤ) →ₗ[ℤ] R)
    (p : {p : criticalPoints 𝓘(ℝ, E) f // manifoldMorseIndex 𝓘(ℝ, E) f p = n}) (r : R) :
    (ConcreteCategory.hom (X := ModuleCat.of R (_ →₀ R)) (Y := ModuleCat.of R (ULift.{u} R))
      ((hX.signedMorseCochainComplexIso hsq R).hom.f n a) (Finsupp.single p r)).down =
      r * a (Finsupp.single p 1) :=
  (intLinearMapEquivModuleCat_apply a _).trans (Finsupp.intLinearMapEquiv_apply_single a p r)

end CommRing

namespace IsMorseSmale

/-- **The integral Morse cochain complex modulo two is the mod-two Morse cochain complex.** Under
the Morse–Smale condition, the Morse cochain complex `Hom_ℤ(CM_*(f; ℤ), ZMod 2)` is isomorphic to
the mod-two Morse cochain complex `Hom(CM_*(f; ZMod 2), ZMod 2)`, whatever the orientations of the
unstable manifolds. -/
noncomputable def signedMorseCochainComplexIsoMorseCochainComplex (h : hX.IsMorseSmale) :
    hX.signedMorseCochainComplex 𝔬 hf (ZMod 2) hsq ≅ h.morseCochainComplex hf :=
  hX.signedMorseCochainComplexIso hsq (ZMod 2) ≪≫ eqToIso
    (congrArg (fun K ↦ K.linearYonedaObj (ZMod 2) (ModuleCat.of (ZMod 2) (ULift.{u} (ZMod 2))))
      (h.signedMorseComplex_zmod_two _))

end IsMorseSmale

end IsAdaptedPseudoGradient

end TauCeti
