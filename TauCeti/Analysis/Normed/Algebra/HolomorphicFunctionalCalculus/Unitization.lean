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

For an element `a` of a nonunital complex Banach algebra `A`, applying naturality of
`holomorphicCalculus` to the scalar augmentation `WithLp.unitizationFstA ℂ A` of the `ℓ¹`
unitization shows that the scalar coordinate of `f(a)` is `f(0)`. Consequently, the unitized
holomorphic calculus of `a` at `f` lies in `A` if and only if `f(0) = 0`.

## Main results

* `TauCeti.unitizationFstA_holomorphicCalculus_unitizationInrL`: the scalar coordinate of the
  unitized calculus at `g` is `g(0)`.
* `TauCeti.holomorphicCalculus_unitizationInrL_mem_range_iff` and
  `TauCeti.holomorphicCalculusOn_unitizationInrL_mem_range_iff`: membership in the image of `A` is
  equivalent to vanishing at `0`.

## References

* H. G. Dales, *Banach Algebras and Automatic Continuity*, §2.4.
* J. B. Conway, *A Course in Functional Analysis*, second edition, VII.4.
-/

public noncomputable section

open TopologicalSpace

namespace TauCeti

open HolomorphicFunctions

variable {A : Type*} [NonUnitalNormedRing A] [NormedSpace ℂ A]
  [IsScalarTower ℂ A A] [SMulCommClass ℂ A A] [CompleteSpace A]

/-- The scalar coordinate of the unitized holomorphic calculus of `a : A` at `g` is `g(0)`. -/
theorem unitizationFstA_holomorphicCalculus_unitizationInrL (a : A)
    (g : holomorphicGerms (spectrum ℂ (WithLp.unitizationInrL ℂ A a))) :
    WithLp.unitizationFstA ℂ A (holomorphicCalculus (WithLp.unitizationInrL ℂ A a) g) =
      holomorphicGerms.eval 0 (WithLp.zero_mem_spectrum_unitizationInrL a) g := by
  rw [ContinuousAlgHom.map_holomorphicCalculus, holomorphicCalculus_complex]
  obtain ⟨U, haU, f, rfl⟩ := holomorphicGerms.exists_toGerm_eq g
  simp

/-- **Nonunital holomorphic calculus criterion (germ form).** For `a` in a nonunital complex Banach
algebra `A`, the holomorphic calculus of `WithLp.unitizationInrL ℂ A a` in the `ℓ¹` unitization
lies in the image of `A` if and only if the germ vanishes at `0`. -/
theorem holomorphicCalculus_unitizationInrL_mem_range_iff (a : A)
    (g : holomorphicGerms (spectrum ℂ (WithLp.unitizationInrL ℂ A a))) :
    holomorphicCalculus (WithLp.unitizationInrL ℂ A a) g ∈
      Set.range (WithLp.unitizationInrL ℂ A) ↔
      holomorphicGerms.eval 0 (WithLp.zero_mem_spectrum_unitizationInrL a) g = 0 := by
  rw [WithLp.mem_range_unitizationInrL_iff, unitizationFstA_holomorphicCalculus_unitizationInrL]

/-- **Nonunital holomorphic calculus criterion (open-domain form).** The unitized calculus of
`a : A` at `f : holomorphicFunctions U` lies in the image of `A` if and only if `f(0) = 0`. -/
theorem holomorphicCalculusOn_unitizationInrL_mem_range_iff (a : A) (U : Opens ℂ)
    (ha : spectrum ℂ (WithLp.unitizationInrL ℂ A a) ⊆ U) (f : holomorphicFunctions U) :
    holomorphicCalculusOn (WithLp.unitizationInrL ℂ A a) U ha f ∈
      Set.range (WithLp.unitizationInrL ℂ A) ↔
      f.val ⟨0, ha (WithLp.zero_mem_spectrum_unitizationInrL a)⟩ = 0 := by
  rw [← holomorphicCalculus_toGerm, holomorphicCalculus_unitizationInrL_mem_range_iff, eval_toGerm]

end TauCeti
