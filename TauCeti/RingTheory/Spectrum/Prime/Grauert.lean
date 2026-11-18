/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
public import TauCeti.LinearAlgebra.TensorProduct.Homology

import TauCeti.RingTheory.Flat.Extensions
import TauCeti.RingTheory.Flat.Reduced
import TauCeti.RingTheory.Spectrum.Prime.Semicontinuity
import TauCeti.Topology.Semicontinuity.Basic

/-!
# Grauert's theorem for complexes of modules

Let `R` be a reduced ring and `M₁ --f--> M₂ --g--> M₃` a complex of `R`-modules with `M₂` finite
and `M₃` finite projective. Suppose that the dimension of the fibre homology

`p ↦ dim H(κ(p) ⊗ M₁ → κ(p) ⊗ M₂ → κ(p) ⊗ M₃)`

is a locally constant function on `Spec R`. Then the homology `H = H(M₁ → M₂ → M₃)` is flat
(`LinearMap.flat_homology_of_isLocallyConstant_finrank_fiber_homology`), and projective when `M₁`
is finite and `M₂` finitely presented
(`LinearMap.projective_homology_of_isLocallyConstant_finrank_fiber_homology`). Its formation
commutes with every base change: for every `R`-algebra `S` the base change map
`S ⊗[R] H → H(S ⊗[R] M₁ → S ⊗[R] M₂ → S ⊗[R] M₃)` is bijective
(`LinearMap.homologyBaseChange_bijective_of_isLocallyConstant_finrank_fiber_homology`). In
particular the rank of `H` at `p` is the dimension of the fibre homology at `p`
(`LinearMap.rankAtStalk_homology_eq_finrank_fiber_homology`).

Moreover the cokernel `M₂ ⧸ range f` is flat
(`LinearMap.flat_quotient_range_of_isLocallyConstant_finrank_fiber_homology`). For a longer complex
`M₀ → M₁ → M₂ → M₃` with `M₂` flat, `LinearMap.homologyBaseChange_bijective` then shows that the
homology at `M₁` also commutes with every base change.

When a bounded complex of finite projective modules computes the cohomology of a proper flat family
over `Spec R` and of all its base changes, this is Grauert's theorem: if `R` is reduced and the
dimension of `Hⁱ` on the fibres is locally constant, then the `i`th higher direct image is locally
free and commutes with base change, and so does the `(i - 1)`st.

The proof: at each prime the fibre homology dimension plus `dim κ(p) ⊗ M₃` is the sum of the fibre
dimensions of the two cokernels `M₂ ⧸ range f` and `M₃ ⧸ range g`
(`LinearMap.finrank_fiber_homology_add_finrank_fiber`). The rank of `M₃` is locally constant, so
the sum of these two upper semicontinuous functions is locally constant, hence so is each summand.
Over a reduced ring a finite module with locally constant fibre dimension is flat
(`Module.flat_of_isLocallyConstant_finrank_fiber`), so both cokernels are flat, and the results of
`TauCeti.LinearAlgebra.TensorProduct.Homology` apply.

## References

* D. Mumford, *Abelian Varieties*, §5, Corollary 2.
* R. Hartshorne, *Algebraic Geometry*, Theorem III.12.9.
-/

public section

open TensorProduct Module

namespace LinearMap

variable {R M₁ M₂ M₃ : Type*} [CommRing R] [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂]
  [Module R M₂] [AddCommGroup M₃] [Module R M₃] [Module.Finite R M₂] [Module.Finite R M₃]
  [Module.Projective R M₃] {f : M₁ →ₗ[R] M₂} {g : M₂ →ₗ[R] M₃}

/-- If the fibre homology of `M₁ → M₂ → M₃` has locally constant dimension, then so do the fibres
of both cokernels `M₂ ⧸ range f` and `M₃ ⧸ range g`. -/
private theorem isLocallyConstant_finrank_fiber_quotient_range (hfg : g ∘ₗ f = 0)
    (h : IsLocallyConstant fun p : PrimeSpectrum R ↦ finrank p.asIdeal.ResidueField
      ((ker (g.baseChange p.asIdeal.ResidueField)).map
        (range (f.baseChange p.asIdeal.ResidueField)).mkQ)) :
    (IsLocallyConstant fun p : PrimeSpectrum R ↦
        finrank p.asIdeal.ResidueField (p.asIdeal.Fiber (M₂ ⧸ range f))) ∧
      IsLocallyConstant fun p : PrimeSpectrum R ↦
        finrank p.asIdeal.ResidueField (p.asIdeal.Fiber (M₃ ⧸ range g)) := by
  have := Module.finitePresentation_of_projective R M₃
  -- The sum of the two cokernel dimensions is the fibre homology dimension plus the locally
  -- constant rank of `M₃`.
  have hsum : IsLocallyConstant fun p : PrimeSpectrum R ↦
      finrank p.asIdeal.ResidueField (p.asIdeal.Fiber (M₂ ⧸ range f)) +
        finrank p.asIdeal.ResidueField (p.asIdeal.Fiber (M₃ ⧸ range g)) := by
    convert h.add (isLocallyConstant_rankAtStalk (R := R) (M := M₃)) using 1
    funext p
    rw [Pi.add_apply, rankAtStalk_eq, finrank_fiber_homology_add_finrank_fiber f g hfg p]
  have hu := upperSemicontinuous_finrank_fiber (R := R) (M₂ ⧸ range f)
  have hv := upperSemicontinuous_finrank_fiber (R := R) (M₃ ⧸ range g)
  refine ⟨hu.isLocallyConstant_of_isLocallyConstant_add hv hsum,
    hv.isLocallyConstant_of_isLocallyConstant_add hu ?_⟩
  simpa only [add_comm] using hsum

variable [IsReduced R]

/-- **The incoming cokernel is flat.** Over a reduced ring, for a complex `M₁ → M₂ → M₃` with
`M₂` finite and `M₃` finite projective whose fibre homology has locally constant dimension, the
cokernel `M₂ ⧸ range f` is flat. -/
theorem flat_quotient_range_of_isLocallyConstant_finrank_fiber_homology (hfg : g ∘ₗ f = 0)
    (h : IsLocallyConstant fun p : PrimeSpectrum R ↦ finrank p.asIdeal.ResidueField
      ((ker (g.baseChange p.asIdeal.ResidueField)).map
        (range (f.baseChange p.asIdeal.ResidueField)).mkQ)) :
    Module.Flat R (M₂ ⧸ range f) :=
  flat_of_isLocallyConstant_finrank_fiber _ (isLocallyConstant_finrank_fiber_quotient_range hfg h).1

/-- Under the hypotheses of Grauert's theorem, the outgoing cokernel `M₃ ⧸ range g` is
projective. -/
private theorem projective_quotient_range (hfg : g ∘ₗ f = 0)
    (h : IsLocallyConstant fun p : PrimeSpectrum R ↦ finrank p.asIdeal.ResidueField
      ((ker (g.baseChange p.asIdeal.ResidueField)).map
        (range (f.baseChange p.asIdeal.ResidueField)).mkQ)) :
    Module.Projective R (M₃ ⧸ range g) := by
  have := Module.finitePresentation_of_projective R M₃
  have : Module.FinitePresentation R (M₃ ⧸ range g) :=
    Module.finitePresentation_of_surjective _ (range g).mkQ_surjective (by
      rw [Submodule.ker_mkQ]
      exact Module.Finite.iff_fg.1 inferInstance)
  exact projective_of_isLocallyConstant_finrank_fiber _
    (isLocallyConstant_finrank_fiber_quotient_range hfg h).2

/-- Under the hypotheses of Grauert's theorem, the image `range g` is projective and finitely
presented, as a direct summand of `M₃`. -/
private theorem projective_range (hfg : g ∘ₗ f = 0)
    (h : IsLocallyConstant fun p : PrimeSpectrum R ↦ finrank p.asIdeal.ResidueField
      ((ker (g.baseChange p.asIdeal.ResidueField)).map
        (range (f.baseChange p.asIdeal.ResidueField)).mkQ)) :
    Module.Projective R (range g) ∧ Module.FinitePresentation R (range g) := by
  have := Module.finitePresentation_of_projective R M₃
  have := projective_quotient_range hfg h
  have : Module.FinitePresentation R (range g) :=
    Module.finitePresentation_of_projective_of_exact _ _ (Submodule.injective_subtype _)
      (range g).mkQ_surjective (exact_subtype_mkQ _)
  have : Module.Flat R (range g) := (exact_subtype_mkQ _).flat_left_of_injective_of_surjective
    (Submodule.injective_subtype _) (range g).mkQ_surjective
  exact ⟨Module.Flat.projective_of_finitePresentation, inferInstance⟩

/-- **Grauert's theorem: homology is flat.** Over a reduced ring, for a complex `M₁ → M₂ → M₃`
with `M₂` finite and `M₃` finite projective whose fibre homology has locally constant dimension,
the homology at `M₂` is flat. -/
theorem flat_homology_of_isLocallyConstant_finrank_fiber_homology (hfg : g ∘ₗ f = 0)
    (h : IsLocallyConstant fun p : PrimeSpectrum R ↦ finrank p.asIdeal.ResidueField
      ((ker (g.baseChange p.asIdeal.ResidueField)).map
        (range (f.baseChange p.asIdeal.ResidueField)).mkQ)) :
    Module.Flat R ((ker g).map (range f).mkQ) :=
  have := flat_quotient_range_of_isLocallyConstant_finrank_fiber_homology hfg h
  have := (projective_range hfg h).1
  flat_homology hfg

/-- **Grauert's theorem: homology commutes with base change.** Over a reduced ring, for a complex
`M₁ → M₂ → M₃` with `M₂` finite and `M₃` finite projective whose fibre homology has locally
constant dimension, the base change map
`S ⊗[R] H(M₁ → M₂ → M₃) → H(S ⊗[R] M₁ → S ⊗[R] M₂ → S ⊗[R] M₃)` is bijective for every
`R`-algebra `S`. -/
theorem homologyBaseChange_bijective_of_isLocallyConstant_finrank_fiber_homology
    (S : Type*) [CommRing S] [Algebra R S] (hfg : g ∘ₗ f = 0)
    (h : IsLocallyConstant fun p : PrimeSpectrum R ↦ finrank p.asIdeal.ResidueField
      ((ker (g.baseChange p.asIdeal.ResidueField)).map
        (range (f.baseChange p.asIdeal.ResidueField)).mkQ)) :
    Function.Bijective (homologyBaseChange S f g) :=
  have := projective_quotient_range hfg h
  homologyBaseChange_bijective S hfg

/-- **Grauert's theorem: the rank of homology.** Over a reduced ring, for a complex
`M₁ → M₂ → M₃` with `M₂` finite and `M₃` finite projective whose fibre homology has locally
constant dimension, the rank of the homology at `M₂` at a prime `p` is the dimension of the fibre
homology at `p`. -/
theorem rankAtStalk_homology_eq_finrank_fiber_homology (hfg : g ∘ₗ f = 0)
    (h : IsLocallyConstant fun p : PrimeSpectrum R ↦ finrank p.asIdeal.ResidueField
      ((ker (g.baseChange p.asIdeal.ResidueField)).map
        (range (f.baseChange p.asIdeal.ResidueField)).mkQ)) (p : PrimeSpectrum R) :
    rankAtStalk ((ker g).map (range f).mkQ) p = finrank p.asIdeal.ResidueField
      ((ker (g.baseChange p.asIdeal.ResidueField)).map
        (range (f.baseChange p.asIdeal.ResidueField)).mkQ) := by
  have := flat_homology_of_isLocallyConstant_finrank_fiber_homology hfg h
  have := (projective_range hfg h).2
  have := finite_homology hfg
  rw [rankAtStalk_eq]
  exact (LinearEquiv.ofBijective _
    (homologyBaseChange_bijective_of_isLocallyConstant_finrank_fiber_homology _ hfg h)).finrank_eq

/-- **Grauert's theorem: homology is projective.** Over a reduced ring, for a complex
`M₁ → M₂ → M₃` with `M₁` finite, `M₂` finitely presented and `M₃` finite projective whose fibre
homology has locally constant dimension, the homology at `M₂` is a finite projective module. -/
theorem projective_homology_of_isLocallyConstant_finrank_fiber_homology [Module.Finite R M₁]
    [Module.FinitePresentation R M₂] (hfg : g ∘ₗ f = 0)
    (h : IsLocallyConstant fun p : PrimeSpectrum R ↦ finrank p.asIdeal.ResidueField
      ((ker (g.baseChange p.asIdeal.ResidueField)).map
        (range (f.baseChange p.asIdeal.ResidueField)).mkQ)) :
    Module.Projective R ((ker g).map (range f).mkQ) := by
  have := flat_homology_of_isLocallyConstant_finrank_fiber_homology hfg h
  have := (projective_range hfg h).1
  have : Module.FinitePresentation R (M₂ ⧸ range f) :=
    Module.finitePresentation_of_surjective _ (range f).mkQ_surjective (by
      rw [Submodule.ker_mkQ]
      exact Module.Finite.iff_fg.1 inferInstance)
  have := finitePresentation_homology hfg
  exact Module.Flat.projective_of_finitePresentation

end LinearMap
