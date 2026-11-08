/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Adjoin.Basic
public import Mathlib.RingTheory.IsTensorProduct

/-!
# Spans of a base change of a submodule

If a submodule `K'` of an `R'`-algebra `A'` is a base change to `R'` of a submodule `K` of an
`R`-algebra `A`, compatibly with `A → A'`, then `K'` lies in the `R'`-span of the image of `K`.

## Main results

* `Submodule.mem_span_image_of_isBaseChange`: the elements of `K'` lie in the `R'`-span of the
  image of `K`.
-/

public section

namespace Submodule

/-- If `h : K →ₗ[R] K'` is a base change to `R'` of a submodule `K` of an `R`-algebra `A` into an
`R'`-submodule `K'` of `A'`, compatible with `A → A'`, then every element of `K'` lies in the
`R'`-span of the image of `K`. -/
theorem mem_span_image_of_isBaseChange {R A R' A' : Type*} [CommSemiring R] [CommSemiring A]
    [CommSemiring R'] [CommSemiring A'] [Algebra R A] [Algebra R R'] [Algebra R' A']
    [Algebra A A'] (K : Submodule R A) {K' : Submodule R' A'} [Module R K']
    [IsScalarTower R R' K'] (h : K →ₗ[R] K') (hbc : IsBaseChange R' h)
    (hh : ∀ x, (h x : A') = algebraMap A A' x) (n : K') :
    (n : A') ∈ span R' (algebraMap A A' '' (K : Set A)) := by
  induction n using hbc.inductionOn with
  | tmul a => exact hh a ▸ subset_span ⟨a, a.2, rfl⟩
  | smul r n hn => exact Submodule.smul_mem _ r hn
  | add n₁ n₂ h₁ h₂ => exact Submodule.add_mem _ h₁ h₂

end Submodule
