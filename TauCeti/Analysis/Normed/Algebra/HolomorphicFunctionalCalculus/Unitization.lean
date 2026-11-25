/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Algebra.HolomorphicFunctionalCalculus.Basic
public import TauCeti.Analysis.Normed.Algebra.Unitization.Basic

/-!
# The holomorphic functional calculus in the `ℓ¹` unitization

For an element `u` of the external `ℓ¹` unitization `WithLp 1 (Unitization ℂ A)` of a nonunital
complex Banach algebra `A`, applying naturality of `holomorphicCalculus` to the scalar
augmentation `WithLp.unitizationFstA ℂ A` shows that the scalar coordinate of `g(u)` is
`g(WithLp.unitizationFstA ℂ A u)`. Consequently, `g(u)` lies in the embedded copy of `A`
(and is recovered by projecting onto `A` and re-embedding) if and only if
`g(WithLp.unitizationFstA ℂ A u) = 0`. When the calculus is evaluated at an embedded element
`u = WithLp.unitizationInrL ℂ A a`, `WithLp.unitizationFstA ℂ A u = 0`, so vanishing at `0`
suffices; for general `u`, the germ must vanish at its scalar coordinate
`WithLp.unitizationFstA ℂ A u`.

## Main results

* `WithLp.holomorphicCalculus_mem_range_unitizationInrL_iff` and
  `WithLp.holomorphicCalculusOn_mem_range_unitizationInrL_iff`: membership in the image of `A` is
  equivalent to vanishing at the scalar coordinate `WithLp.unitizationFstA ℂ A u` (and at `0`
  when evaluated at `WithLp.unitizationInrL ℂ A a`), via `AlgHom.map_holomorphicCalculus_eq_eval`.

## References

* H. G. Dales, *Banach Algebras and Automatic Continuity*, §2.4.
* J. B. Conway, *A Course in Functional Analysis*, second edition, VII.4.
-/

public noncomputable section

open TopologicalSpace

namespace WithLp

open TauCeti HolomorphicFunctions

variable {A : Type*} [NonUnitalNormedRing A] [NormedSpace ℂ A]
  [IsScalarTower ℂ A A] [SMulCommClass ℂ A A] [CompleteSpace A]

/-- **Unitized holomorphic calculus range criterion (germ form).** The holomorphic calculus of
`u : WithLp 1 (Unitization ℂ A)` lies in the image of `A` if and only if the germ vanishes at
`WithLp.unitizationFstA ℂ A u`. -/
theorem holomorphicCalculus_mem_range_unitizationInrL_iff (u : WithLp 1 (Unitization ℂ A))
    (g : holomorphicGerms (spectrum ℂ u)) :
    holomorphicCalculus u g ∈ Set.range (unitizationInrL ℂ A) ↔
      holomorphicGerms.eval (unitizationFstA ℂ A u)
        (AlgHom.apply_mem_spectrum (unitizationFstA ℂ A) u) g = 0 := by
  rw [mem_range_unitizationInrL_iff,
    AlgHom.map_holomorphicCalculus_eq_eval (unitizationFstA ℂ A)]

/-- **Unitized holomorphic calculus range criterion (open-domain form).** The calculus of
`u : WithLp 1 (Unitization ℂ A)` at `f : holomorphicFunctions U` lies in the image of `A` if and
only if `f` vanishes at `WithLp.unitizationFstA ℂ A u`. -/
theorem holomorphicCalculusOn_mem_range_unitizationInrL_iff (u : WithLp 1 (Unitization ℂ A))
    (U : Opens ℂ) (ha : spectrum ℂ u ⊆ U) (f : holomorphicFunctions U) :
    holomorphicCalculusOn u U ha f ∈ Set.range (unitizationInrL ℂ A) ↔
      f.val ⟨unitizationFstA ℂ A u,
        ha (AlgHom.apply_mem_spectrum (unitizationFstA ℂ A) u)⟩ = 0 := by
  rw [← holomorphicCalculus_toGerm, u.holomorphicCalculus_mem_range_unitizationInrL_iff,
    eval_toGerm]

end WithLp
