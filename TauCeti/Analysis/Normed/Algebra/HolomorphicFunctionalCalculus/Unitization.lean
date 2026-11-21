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
`g(WithLp.unitizationFstA ℂ A u) = 0`. Specializing to `u = WithLp.unitizationInrL ℂ A a`
recovers evaluation at `0`.

## Main results

* `TauCeti.unitizationFstA_holomorphicCalculus` and
  `TauCeti.unitizationFstA_holomorphicCalculus_unitizationInrL`: the scalar coordinate of `g(u)`
  is `g(WithLp.unitizationFstA ℂ A u)` (and `g(0)` for `u = WithLp.unitizationInrL ℂ A a`).
* `TauCeti.unitizationInrL_unitizationSndL_holomorphicCalculus_of_eval_eq_zero` and
  `TauCeti.unitizationInrL_unitizationSndL_holomorphicCalculus_of_eval_zero`: projecting and
  re-embedding recovers the unitized calculus value when the germ vanishes at the scalar
  coordinate.
* `TauCeti.holomorphicCalculus_mem_range_unitizationInrL_iff`,
  `TauCeti.holomorphicCalculusOn_mem_range_unitizationInrL_iff`,
  `TauCeti.holomorphicCalculus_unitizationInrL_mem_range_iff`, and
  `TauCeti.holomorphicCalculusOn_unitizationInrL_mem_range_iff`: membership in the image of `A`
  is equivalent to vanishing at the scalar coordinate (respectively `0`).

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

/-- The scalar coordinate of the unitized holomorphic calculus of `u : WithLp 1 (Unitization ℂ A)`
at `g` is `g(WithLp.unitizationFstA ℂ A u)`. -/
theorem unitizationFstA_holomorphicCalculus (u : WithLp 1 (Unitization ℂ A))
    (g : holomorphicGerms (spectrum ℂ u)) :
    WithLp.unitizationFstA ℂ A (holomorphicCalculus u g) =
      holomorphicGerms.eval (WithLp.unitizationFstA ℂ A u)
        (WithLp.unitizationFstA_mem_spectrum u) g := by
  rw [ContinuousAlgHom.map_holomorphicCalculus, holomorphicCalculus_complex]
  obtain ⟨U, haU, f, rfl⟩ := holomorphicGerms.exists_toGerm_eq g
  simp

/-- The scalar coordinate of the unitized holomorphic calculus of `a : A` at `g` is `g(0)`. -/
theorem unitizationFstA_holomorphicCalculus_unitizationInrL (a : A)
    (g : holomorphicGerms (spectrum ℂ (WithLp.unitizationInrL ℂ A a))) :
    WithLp.unitizationFstA ℂ A (holomorphicCalculus (WithLp.unitizationInrL ℂ A a) g) =
      holomorphicGerms.eval 0 (WithLp.zero_mem_spectrum_unitizationInrL a) g := by
  simpa using unitizationFstA_holomorphicCalculus (WithLp.unitizationInrL ℂ A a) g

/-- When a holomorphic germ vanishes at the scalar coordinate of `u`, projecting the unitized
calculus value to `A` and re-embedding recovers it. -/
theorem unitizationInrL_unitizationSndL_holomorphicCalculus_of_eval_eq_zero
    (u : WithLp 1 (Unitization ℂ A)) {g : holomorphicGerms (spectrum ℂ u)}
    (hg : holomorphicGerms.eval (WithLp.unitizationFstA ℂ A u)
      (WithLp.unitizationFstA_mem_spectrum u) g = 0) :
    WithLp.unitizationInrL ℂ A (WithLp.unitizationSndL ℂ A (holomorphicCalculus u g)) =
      holomorphicCalculus u g :=
  WithLp.unitizationInrL_unitizationSndL_of_fst_eq_zero <| by
    simpa only [WithLp.unitizationFstA_apply] using
      (unitizationFstA_holomorphicCalculus u g).trans hg

/-- When a holomorphic germ vanishes at `0`, projecting its unitized calculus value to `A` and
re-embedding recovers the unitized calculus value. -/
theorem unitizationInrL_unitizationSndL_holomorphicCalculus_of_eval_zero (a : A)
    {g : holomorphicGerms (spectrum ℂ (WithLp.unitizationInrL ℂ A a))}
    (hg : holomorphicGerms.eval 0 (WithLp.zero_mem_spectrum_unitizationInrL a) g = 0) :
    WithLp.unitizationInrL ℂ A (WithLp.unitizationSndL ℂ A
        (holomorphicCalculus (WithLp.unitizationInrL ℂ A a) g)) =
      holomorphicCalculus (WithLp.unitizationInrL ℂ A a) g :=
  unitizationInrL_unitizationSndL_holomorphicCalculus_of_eval_eq_zero
    (WithLp.unitizationInrL ℂ A a) (by simpa using hg)

/-- **Unitized holomorphic calculus range criterion (germ form).** The holomorphic calculus of
`u : WithLp 1 (Unitization ℂ A)` lies in the image of `A` if and only if the germ vanishes at
`WithLp.unitizationFstA ℂ A u`. -/
theorem holomorphicCalculus_mem_range_unitizationInrL_iff (u : WithLp 1 (Unitization ℂ A))
    (g : holomorphicGerms (spectrum ℂ u)) :
    holomorphicCalculus u g ∈ Set.range (WithLp.unitizationInrL ℂ A) ↔
      holomorphicGerms.eval (WithLp.unitizationFstA ℂ A u)
        (WithLp.unitizationFstA_mem_spectrum u) g = 0 := by
  rw [WithLp.mem_range_unitizationInrL_iff, unitizationFstA_holomorphicCalculus]

/-- **Nonunital holomorphic calculus criterion (germ form).** For `a` in a nonunital complex Banach
algebra `A`, the holomorphic calculus of `WithLp.unitizationInrL ℂ A a` in the `ℓ¹` unitization
lies in the image of `A` if and only if the germ vanishes at `0`. -/
theorem holomorphicCalculus_unitizationInrL_mem_range_iff (a : A)
    (g : holomorphicGerms (spectrum ℂ (WithLp.unitizationInrL ℂ A a))) :
    holomorphicCalculus (WithLp.unitizationInrL ℂ A a) g ∈
      Set.range (WithLp.unitizationInrL ℂ A) ↔
      holomorphicGerms.eval 0 (WithLp.zero_mem_spectrum_unitizationInrL a) g = 0 := by
  simpa using holomorphicCalculus_mem_range_unitizationInrL_iff (WithLp.unitizationInrL ℂ A a) g

/-- **Unitized holomorphic calculus range criterion (open-domain form).** The calculus of
`u : WithLp 1 (Unitization ℂ A)` at `f : holomorphicFunctions U` lies in the image of `A` if and
only if `f` vanishes at `WithLp.unitizationFstA ℂ A u`. -/
theorem holomorphicCalculusOn_mem_range_unitizationInrL_iff (u : WithLp 1 (Unitization ℂ A))
    (U : Opens ℂ) (ha : spectrum ℂ u ⊆ U) (f : holomorphicFunctions U) :
    holomorphicCalculusOn u U ha f ∈ Set.range (WithLp.unitizationInrL ℂ A) ↔
      f.val ⟨WithLp.unitizationFstA ℂ A u, ha (WithLp.unitizationFstA_mem_spectrum u)⟩ = 0 := by
  rw [← holomorphicCalculus_toGerm, holomorphicCalculus_mem_range_unitizationInrL_iff, eval_toGerm]

/-- **Nonunital holomorphic calculus criterion (open-domain form).** The unitized calculus of
`a : A` at `f : holomorphicFunctions U` lies in the image of `A` if and only if `f(0) = 0`. -/
theorem holomorphicCalculusOn_unitizationInrL_mem_range_iff (a : A) (U : Opens ℂ)
    (ha : spectrum ℂ (WithLp.unitizationInrL ℂ A a) ⊆ U) (f : holomorphicFunctions U) :
    holomorphicCalculusOn (WithLp.unitizationInrL ℂ A a) U ha f ∈
      Set.range (WithLp.unitizationInrL ℂ A) ↔
      f.val ⟨0, ha (WithLp.zero_mem_spectrum_unitizationInrL a)⟩ = 0 := by
  simpa using holomorphicCalculusOn_mem_range_unitizationInrL_iff
    (WithLp.unitizationInrL ℂ A a) U ha f

end TauCeti
