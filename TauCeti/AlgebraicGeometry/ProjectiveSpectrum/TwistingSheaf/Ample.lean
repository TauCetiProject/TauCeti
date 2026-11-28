/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.TwistingSheaf.NonvanishingLocus
public import TauCeti.AlgebraicGeometry.LineBundle.Ample
public import TauCeti.AlgebraicGeometry.LineBundle.GlobalGeneration.Basic

/-!
# Positivity of twisting sheaves

When degree-one standard opens cover `Proj A`, the nonvanishing locus of the section of
`𝒪(n)` associated to a homogeneous element `r ∈ Aₙ` is exactly `D₊(r)`. Consequently all
nonnegative twists are globally generated, and every positive twist is ample if `Proj A`
is quasi-compact. In particular these conclusions apply to the projective spectrum of the
symmetric algebra of a finite module, over any commutative ring.

This connects the local-fraction construction of twisting sheaves to positivity of line
bundles. The standard affine opens are the affine nonvanishing loci needed for ampleness,
which underlies generation and vanishing after sufficiently positive twisting.

## References

* R. Hartshorne, *Algebraic Geometry*, Chapter II, Sections 5 and 7.
* The Stacks Project, Tags 01MM and 01PS.
-/

public section

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace AlgebraicGeometry.Proj

universe u

variable {A : Type u} {σ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  {𝒜 : ℕ → σ} [GradedRing 𝒜]
  {ι : Type u} (f : ι → A) (hf : ∀ i, f i ∈ 𝒜 1)
  (hcover : ⨆ i, basicOpen 𝒜 (f i) = ⊤)

/-- If degree-one standard opens cover `Proj A`, every nonnegative twist is globally
generated. No quasi-compactness or Noetherian hypothesis is needed. -/
theorem isGloballyGenerated_twistingSheaf (n : ℕ) :
    TauCeti.AlgebraicGeometry.InvertibleSheaf.IsGloballyGenerated
      ⟨twistingSheaf 𝒜 (n : ℤ),
        isInvertible_twistingSheaf_of_iSup_eq_top f hf hcover n⟩ := by
  have := isInvertible_twistingSheaf_of_iSup_eq_top f hf hcover (n : ℤ)
  rw [TauCeti.AlgebraicGeometry.InvertibleSheaf.isGloballyGenerated_iff]
  intro x
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (hcover.symm ▸ Opens.mem_top x)
  refine ⟨toTwistingSheaf 𝒜 rfl ⊤
    ⟨f i ^ n, by simpa using SetLike.pow_mem_graded n (hf i)⟩, ?_⟩
  rw [twistingSheaf.nonvanishingLocus_toTwistingSheaf f hf hcover]
  exact fun h ↦ hi (x.isPrime.mem_of_pow_mem n h)

/-- On a quasi-compact `Proj` covered by degree-one standard opens, every positive twist
is ample. This applies without a Noetherian or domain hypothesis. -/
theorem isAmple_twistingSheaf [CompactSpace (Proj 𝒜)] {n : ℕ} (hn : 0 < n) :
    (TauCeti.AlgebraicGeometry.LineBundleClass.mk
      ⟨twistingSheaf 𝒜 (n : ℤ),
        isInvertible_twistingSheaf_of_iSup_eq_top f hf hcover n⟩).IsAmple := by
  have := isInvertible_twistingSheaf_of_iSup_eq_top f hf hcover (n : ℤ)
  refine ⟨inferInstance, fun x ↦ ?_⟩
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (hcover.symm ▸ Opens.mem_top x)
  refine ⟨1, Nat.one_pos, ⟨twistingSheaf 𝒜 (n : ℤ), inferInstance⟩,
    (pow_one _).symm, toTwistingSheaf 𝒜 rfl ⊤
      ⟨f i ^ n, by simpa using SetLike.pow_mem_graded n (hf i)⟩, ?_, ?_⟩
  · rw [twistingSheaf.nonvanishingLocus_toTwistingSheaf f hf hcover]
    exact fun h ↦ hi (x.isPrime.mem_of_pow_mem n h)
  · rw [twistingSheaf.nonvanishingLocus_toTwistingSheaf f hf hcover]
    exact isAffineOpen_basicOpen 𝒜 _
      (by simpa using SetLike.pow_mem_graded n (hf i)) hn

end AlgebraicGeometry.Proj

namespace TauCeti.SymmetricAlgebra

variable (R M : Type u) [CommRing R] [AddCommMonoid M] [Module R M] [Module.Finite R M]

/-- Positive twisting sheaves on the projective spectrum of the symmetric algebra of a
finite module are ample, even when the module is not free. -/
theorem isAmple_twistingSheaf {n : ℕ} (hn : 0 < n) :
    (AlgebraicGeometry.LineBundleClass.mk
      ⟨Proj.twistingSheaf (homogeneousSubmodule R M) (n : ℤ), inferInstance⟩).IsAmple :=
  Proj.isAmple_twistingSheaf (_root_.SymmetricAlgebra.ι R M)
    (ι_mem_homogeneousSubmodule R M) (iSup_basicOpen_ι_eq_top R M id (by simp)) hn

end TauCeti.SymmetricAlgebra
