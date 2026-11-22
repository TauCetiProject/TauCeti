/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Etale.Pi
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.RingTheory.Smooth.Flat
public import TauCeti.RingTheory.TensorProduct.Pi

/-!
# Étale matrix splittings of algebras from finite étale covers

An Azumaya algebra `R` over a commutative ring `A` becomes a matrix algebra étale locally on
`Spec A` (Grothendieck, *Le groupe de Brauer I*, Théorème 5.1(ii)–(iii)). Étale locally means on
the charts `Spec Bᵢ → Spec A` of an étale cover, and since `Spec A` is quasi-compact finitely
many charts suffice. This file passes from such a finite cover to a single splitting algebra:
the product `B = ∏ᵢ Bᵢ` is étale over `A`, faithfully flat because the charts jointly cover
`Spec A`, and splits `R` because each factor does.

## Main declarations

* `IsAzumaya.etale_matrix_splitting_of_finite_cover`: if finitely many étale `A`-algebras `Bᵢ`
  have spectra jointly covering `Spec A` and each splits `R` as `n × n` matrices, then `∏ᵢ Bᵢ` is
  étale and faithfully flat over `A` and splits `R` as `n × n` matrices.

The splitting hypothesis is all the proof uses, so the theorem is stated without `IsAzumaya A R`:
an algebra with such a cover is Azumaya by descent, which is not proved here.

## References

* A. Grothendieck, *Le groupe de Brauer I : algèbres d'Azumaya et interprétations diverses*,
  Séminaire Bourbaki 290, 1964/65, Théorème 5.1, p. 210.
-/

public section

open scoped TensorProduct

/-- **A finite étale cover splitting an algebra gives one étale, faithfully flat splitting
algebra.** If finitely many étale `A`-algebras `B i` have spectra jointly covering `Spec A` and
each splits `R`, that is `B i ⊗[A] R ≃ₐ[B i] Matrix n n (B i)`, then the product `∀ i, B i` is
étale and faithfully flat over `A` and splits `R` in the same way. This is the passage from an
affine étale cover to a single algebra in Grothendieck, *Le groupe de Brauer I*,
Théorème 5.1. -/
theorem IsAzumaya.etale_matrix_splitting_of_finite_cover {A R ι : Type*} [CommRing A]
    [Semiring R] [Algebra A R] {n : Type*} [Fintype n] [DecidableEq n] [Finite ι]
    {B : ι → Type*} [∀ i, CommRing (B i)] [∀ i, Algebra A (B i)] [∀ i, Algebra.Etale A (B i)]
    (hcover : ∀ p : PrimeSpectrum A, ∃ i, ∃ q : PrimeSpectrum (B i),
      q.asIdeal.comap (algebraMap A (B i)) = p.asIdeal)
    (hsplit : ∀ i, Nonempty (B i ⊗[A] R ≃ₐ[B i] Matrix n n (B i))) :
    Algebra.Etale A (∀ i, B i) ∧ Module.FaithfullyFlat A (∀ i, B i) ∧
      Nonempty ((∀ i, B i) ⊗[A] R ≃ₐ[∀ i, B i] Matrix n n (∀ i, B i)) := by
  classical
  have := Fintype.ofFinite ι
  refine ⟨inferInstance, .of_comap_surjective fun p ↦ ?_,
    ⟨Algebra.TensorProduct.piLeftMatrixEquiv fun i ↦ (hsplit i).some⟩⟩
  obtain ⟨i, q, hq⟩ := hcover p
  exact ⟨PrimeSpectrum.comap (Pi.evalRingHom B i) q, PrimeSpectrum.ext hq⟩
