/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Free
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import TauCeti.AlgebraicTopology.Singular.Triple
public import TauCeti.LinearAlgebra.FreeModule.PID

/-!
# Freeness of relative homology along the long exact sequence of a triple

Let `B ⊆ A ⊆ X` be a triple of spaces and `V` a module over a principal ideal ring `k` without
zero divisors, such as `ℤ`. Write `Hᵢ(-)` for relative singular homology with coefficients in `V`.
If `Hₙ₊₁(X, A)` vanishes, the long exact sequence of the triple begins

`0 ⟶ Hₙ(A, B) ⟶ Hₙ(X, B) ⟶ Hₙ(X, A)`,

and then `Hₙ(X, B)` is free as soon as `Hₙ(A, B)` and `Hₙ(X, A)` are
(`TauCeti.TopTriple.free_singularHomology_totalPair`). The image of `Hₙ(X, B)` in the free module
`Hₙ(X, A)` is free because every submodule of a free module over such a ring is free, in any rank
(`Submodule.free_of_isPrincipalIdealRing`), and an extension of free modules is free.

This is the step that propagates freeness of homology in the top degree of a filtration, for
instance along the sublevels of a Morse function all of whose critical points have index at most
`n`.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 2.1, the long exact sequence of a triple.
-/

public section

noncomputable section

open CategoryTheory Limits

universe w

namespace TauCeti.TopTriple

variable (T : TopTriple.{w}) {k : Type*} [CommRing k] [NoZeroDivisors k] [IsPrincipalIdealRing k]
  (V : ModuleCat.{w} k)

/-- **Freeness along a triple.** Over a principal ideal ring without zero divisors, if
`Hₙ₊₁(X, A)` vanishes and `Hₙ(A, B)` and `Hₙ(X, A)` are free, then `Hₙ(X, B)` is free. -/
theorem free_singularHomology_totalPair (n : ℕ)
    [Module.Free k ((innerPair.obj T).singularHomology V n : ModuleCat k)]
    [Module.Free k ((outerPair.obj T).singularHomology V n : ModuleCat k)]
    (h : IsZero ((outerPair.obj T).singularHomology V (n + 1))) :
    Module.Free k ((totalPair.obj T).singularHomology V n : ModuleCat k) := by
  set f := (TopPair.singularHomologyMap (innerToTotal.app T) V n).hom
  set g := (TopPair.singularHomologyMap (totalToOuter.app T) V n).hom
  -- The connecting morphism out of `Hₙ₊₁(X, A) = 0` vanishes, so `Hₙ(A, B) ⟶ Hₙ(X, B)` is
  -- injective.
  have hf : Function.Injective f := (ModuleCat.mono_iff_injective _).1
    ((T.singularHomology_exact_inner V (n + 1) n).mono_g (h.eq_of_src _ _))
  have hfg : Function.Exact f g := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
    (T.singularHomology_exact_total V n)
  -- So `Hₙ(X, B)` is an extension of the image of `g`, a submodule of a free module, by `Hₙ(A, B)`.
  have hfg' : Function.Exact f g.rangeRestrict :=
    (LinearMap.range g).injective_subtype.comp_exact_iff_exact.1 hfg
  have : Module.Free k (LinearMap.range g) := Submodule.free_of_isPrincipalIdealRing _
  let S : ShortComplex (ModuleCat k) :=
    .mk (ModuleCat.ofHom f) (ModuleCat.ofHom g.rangeRestrict)
      (ModuleCat.hom_ext (LinearMap.ext hfg'.apply_apply_eq_zero))
  have hS : S.ShortExact :=
    { exact := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).2 hfg'
      mono_f := (ModuleCat.mono_iff_injective _).2 hf
      epi_g := (ModuleCat.epi_iff_surjective _).2 g.surjective_rangeRestrict }
  exact ModuleCat.free_shortExact hS

end TauCeti.TopTriple
