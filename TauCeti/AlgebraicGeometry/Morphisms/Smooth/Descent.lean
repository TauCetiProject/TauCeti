/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent
public import TauCeti.AlgebraicGeometry.Morphisms.Smooth.PureRelativeDimension
import TauCeti.AlgebraicGeometry.Morphisms.Syntomic.Descent

/-!
# Descent of smooth relative dimension

Being smooth of relative dimension `n` descends along fpqc morphisms on the base, and hence also
along fppf and étale covers. A morphism is smooth of relative dimension `n` exactly when it is
smooth and has pure relative dimension `n`
(`TauCeti.AlgebraicGeometry.smoothOfRelativeDimension_iff_smooth_and_pureRelativeDimension`), and
both smoothness and syntomicity of relative dimension `n` satisfy fpqc descent.

## Main results

* `AlgebraicGeometry.SmoothOfRelativeDimension.descendsAlong_surjective_inf_flat_inf_quasicompact`:
  smoothness of relative dimension `n` satisfies fpqc descent on the target.

## References

* [Stacks Project, Tag 02VL](https://stacks.math.columbia.edu/tag/02VL): descent of smoothness.
-/

public section

open CategoryTheory Limits MorphismProperty AlgebraicGeometry TauCeti.AlgebraicGeometry

universe u

namespace AlgebraicGeometry.SmoothOfRelativeDimension

/-- **Smooth morphisms of relative dimension `n` satisfy fpqc descent.** If the base change of
`g` along a surjective, flat, quasi-compact morphism is smooth of relative dimension `n`, then so
is `g`. By Mathlib's general reduction from fpqc to fppf descent for target-local properties, the
same holds along surjective, flat morphisms locally of finite presentation. -/
instance descendsAlong_surjective_inf_flat_inf_quasicompact (n : ℕ) :
    MorphismProperty.DescendsAlong (@SmoothOfRelativeDimension.{u} n)
      (@Surjective ⊓ @Flat ⊓ @QuasiCompact) where
  of_isPullback {_ _ _ _ fst _ _ g} hpb hf h := by
    have : SmoothOfRelativeDimension n fst := h
    have hsm : Smooth fst := SmoothOfRelativeDimension.smooth n fst
    have hsyn : SyntomicOfRelativeDimension n fst := inferInstance
    have : Smooth g := of_isPullback_of_descendsAlong hpb hf hsm
    have : SyntomicOfRelativeDimension n g := of_isPullback_of_descendsAlong hpb hf hsyn
    exact (smoothOfRelativeDimension_iff_smooth_and_pureRelativeDimension g).mpr
      ⟨‹_›, inferInstance⟩

end AlgebraicGeometry.SmoothOfRelativeDimension
