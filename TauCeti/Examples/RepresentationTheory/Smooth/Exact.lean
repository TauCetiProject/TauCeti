/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Padics.QuotientTower
public import TauCeti.RepresentationTheory.Augmentation.Basic
public import TauCeti.RepresentationTheory.Smooth.Exact

/-!
# Examples for kernels and cokernels of smooth representations

Let `G = ℤ_p`, written multiplicatively, act on the finite set `ℤ_p ⧸ p ℤ_p ≅ ℤ/p`, and let
`ε : A[ℤ/p] → A` be the sum of the coefficients, a morphism of smooth representations to the
trivial representation. Its kernel in `SmoothRep A G` is the augmentation submodule of the vectors
whose coefficients sum to zero, with its induced action, and its cokernel is zero: both are
computed on the underlying `A`-modules (`TauCeti.SmoothRep.range_kernel_ι`,
`TauCeti.SmoothRep.ker_cokernel_π`).
-/

public section

open CategoryTheory Limits Representation

namespace TauCeti.Examples.SmoothRepExact

variable (A : Type) [Ring A] (p : ℕ) [Fact p.Prime]

/-- The finite quotient `ℤ_p ⧸ p ℤ_p` of `ℤ_p`, written multiplicatively. -/
abbrev X : Type :=
  Multiplicative ℤ_[p] ⧸ ((FiniteQuotientTower.padicTower p).ker 1).toSubgroup

/-- The coefficient sum `A[ℤ/p] → A` as a morphism of smooth representations of `ℤ_p`. -/
noncomputable abbrev ε :
    SmoothRep.of (ofMulAction A (Multiplicative ℤ_[p]) (X p)) ⟶
      SmoothRep.of (trivial A (Multiplicative ℤ_[p]) A) :=
  ObjectProperty.homMk (permutationAugmentation A (Multiplicative ℤ_[p]) (X p))

/-- The coefficient sum `ε` is surjective. -/
private theorem ε_surjective : Function.Surjective (ε A p).hom.hom := by
  rw [ObjectProperty.homMk_hom]
  exact (Rep.epi_iff_surjective _).1 (permutationAugmentation_epi A _ (X p))

/-- The kernel of `ε` in `SmoothRep A ℤ_p` is the augmentation submodule of `A[ℤ/p]`. -/
example : LinearMap.range (kernel.ι (ε A p)).hom.hom.toLinearMap =
    (augmentationSubrepresentation A (Multiplicative ℤ_[p]) (X p)).toSubmodule := by
  rw [SmoothRep.range_kernel_ι, toSubmodule_augmentationSubrepresentation]
  ext v
  simp only [LinearMap.mem_ker, ObjectProperty.homMk_hom,
    Representation.IntertwiningMap.toLinearMap_apply]
  rw [permutationAugmentation_apply]

/-- The cokernel of `ε` in `SmoothRep A ℤ_p` is zero: `ε` is surjective. -/
example : IsZero (cokernel (ε A p)) := by
  have : Epi (ε A p) := (SmoothRep.epi_iff_surjective _).2 (ε_surjective A p)
  exact isZero_cokernel_of_epi _

/-- Read on the underlying modules, the cokernel map of `ε` kills exactly the image of `ε`, which
is all of `A`. -/
example : LinearMap.ker (cokernel.π (ε A p)).hom.hom.toLinearMap = ⊤ := by
  rw [SmoothRep.ker_cokernel_π, LinearMap.range_eq_top]
  exact ε_surjective A p

end TauCeti.Examples.SmoothRepExact
