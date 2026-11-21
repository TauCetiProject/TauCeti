/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Continuous.Basic
public import TauCeti.Analysis.Normed.Lp.ProdLp

/-!
# Direct sums of two continuous representations

Two continuous representations `π` and `ρ` of a monoid `G` on seminormed modules `E` and `F` act
componentwise on the `L^p` product `WithLp p (E × F)`, each operator being the block sum
`ContinuousLinearMap.withLpProdMap` of `π g` and `ρ g`. This is the direct sum
`ContRepresentation.withLpProd`, strongly continuous when `π` and `ρ` are. For `p = 2` and inner
product spaces it is the Hilbert direct sum, unitary when `π` and `ρ` are
(`ContRepresentation.IsUnitary.withLpProd`).

## Main declarations

* `ContRepresentation.withLpProd`: the direct sum `π ⊕ ρ` on `WithLp p (E × F)`.
* `ContRepresentation.continuous_withLpProd_apply`: the direct sum of strongly continuous
  representations is strongly continuous.
-/

public section

open scoped ENNReal

namespace ContRepresentation

variable (p : ℝ≥0∞) [Fact (1 ≤ p)] {R G E F : Type*} [Ring R] [Monoid G]
  [SeminormedAddCommGroup E] [Module R E] [SeminormedAddCommGroup F] [Module R F]

/-- The **direct sum** `π ⊕ ρ` of two continuous representations, acting componentwise on the
`L^p` product `WithLp p (E × F)`. For `p = 2` it is the Hilbert direct sum, unitary when `π` and
`ρ` are (`ContRepresentation.IsUnitary.withLpProd`). -/
def withLpProd (π : ContRepresentation R G E) (ρ : ContRepresentation R G F) :
    ContRepresentation R G (WithLp p (E × F)) :=
  .ofMonoidHom
    { toFun g := (π g).withLpProdMap p (ρ g)
      map_one' := ContinuousLinearMap.ext fun x ↦ by
        simp only [map_one, ContinuousLinearMap.withLpProdMap_apply, one_apply_eq_self]
        exact WithLp.toLp_ofLp p x
      map_mul' g h := by
        ext x
        simp }

variable {p} {π : ContRepresentation R G E} {ρ : ContRepresentation R G F}

@[simp]
theorem withLpProd_apply (g : G) (x : WithLp p (E × F)) :
    π.withLpProd p ρ g x = WithLp.toLp p (π g x.fst, ρ g x.snd) :=
  ContinuousLinearMap.withLpProdMap_apply (π g) (ρ g) x

/-- The direct sum of two strongly continuous representations is strongly continuous. -/
theorem continuous_withLpProd_apply [TopologicalSpace G] (hπ : ∀ v, Continuous fun g ↦ π g v)
    (hρ : ∀ w, Continuous fun g ↦ ρ g w) (x : WithLp p (E × F)) :
    Continuous fun g ↦ π.withLpProd p ρ g x := by
  simp only [withLpProd_apply]
  exact (WithLp.prod_continuous_toLp p E F).comp ((hπ _).prodMk (hρ _))

end ContRepresentation
