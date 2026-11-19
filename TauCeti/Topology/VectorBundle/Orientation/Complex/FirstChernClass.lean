/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.Orientation.Complex.FiberwiseEquiv

/-!
# The first Chern class of a complex line bundle

Let `L → B` be a complex line bundle over a topological space `B`, with model fibre `F` of complex
dimension one. Its underlying real bundle `L_ℝ` is an oriented real plane bundle, each fibre being
oriented by `(v, i v)` for any nonzero `v` (`TauCeti.VectorBundleOrientation.complex`). The
**first Chern class** `c₁(L) ∈ H²(B; ℤ)` (`TauCeti.lineFirstChernClass`) is the Euler class of this
oriented plane bundle, which is `TauCeti.complexEulerClass` in complex rank one.

The laws are the canonical Euler-class laws at `r := 0`, applied directly through
`TauCeti.lineFirstChernClass_def`:

* `TauCeti.complexEulerClass_pullback` and
  `TauCeti.complexEulerClass_eq_singularCohomologyMap_of_fiberwise` give naturality under
  continuous pullback and fibrewise complex-linear isomorphisms over a continuous base map;
* `TauCeti.complexEulerClass_eq_of_fiberwise` gives invariance under bundle isomorphism;
* `TauCeti.complexEulerClass_eq_zero_of_forall_ne_zero` and
  `TauCeti.complexEulerClass_trivial` give vanishing for a nowhere-zero section and a trivial line;
* `TauCeti.complexEulerClass_eq_neg_of_finrank_eq_one_of_conjugateFiberwise` gives
  `c₁(L') = -c₁(L)` under a fibrewise conjugate-linear isomorphism; for a continuous base map use
  `TauCeti.complexEulerClass_eq_neg_one_pow_smul_singularCohomologyMap_of_conjugateFiberwise`
  at `r := 0`, simplifying `pow_one` and `neg_one_zsmul`.

The conjugate statement is phrased for an abstract fibrewise conjugate-linear isomorphism, so it
applies to every model of the conjugate line `conj L`, and, through the conjugate-linear Riesz
isomorphism of a Hermitian metric, to the dual line `L*`.

## Implementation notes

The class is named `lineFirstChernClass` because it is the first Chern class of a line bundle,
defined directly as an Euler class. The first Chern class of a complex vector bundle `E` of higher
constant rank is to be the class of its determinant line, `c₁(E) = c₁(det E)`, and on a line the
two agree through `det L ≃ L`. The rank hypothesis is `finrank ℂ F = 1`, and the class lives in
degree `2`, definitionally the degree `2 * 0 + 2` of `complexEulerClass` in rank `0 + 1`.
Integral coefficients are `ULift ℤ`, as for the Euler class.

## Main definitions

* `TauCeti.lineFirstChernClass`: the first Chern class `c₁(L) ∈ H²(B; ℤ)` of a complex line bundle,
  the Euler class of its underlying real plane bundle with the complex orientation.

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §14 (the top Chern class as the Euler class of the underlying real bundle, and
  Lemma 14.9 on the conjugate bundle).
* R. Bott, L. W. Tu, *Differential Forms in Algebraic Topology*, Graduate Texts in Mathematics 82,
  Springer (1982), §20 (the first Chern class of a complex line bundle as its Euler class).
-/

public section

noncomputable section

open Bundle Module

universe w

namespace TauCeti

variable {B : Type w} [TopologicalSpace B]

section Definition

variable (F : Type w) [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F]
  [IsScalarTower ℝ ℂ F] [FiniteDimensional ℂ F]
  (E : B → Type w) [TopologicalSpace (TotalSpace F E)] [∀ b, AddCommGroup (E b)]
  [∀ b, Module ℝ (E b)] [∀ b, Module ℂ (E b)] [∀ b, IsScalarTower ℝ ℂ (E b)]
  [∀ b, TopologicalSpace (E b)] [FiberBundle F E] [VectorBundle ℂ F E]
  (hF : finrank ℂ F = 1)

/-- **The first Chern class of a complex line bundle** `L → B`: the class `c₁(L) ∈ H²(B; ℤ)`, the
Euler class of the underlying oriented real plane bundle `L_ℝ` with its complex orientation
`(v, i v)`, that is `complexEulerClass` in complex rank one. -/
def lineFirstChernClass :
    (TopCat.of B).singularCohomology (ModuleCat.of ℤ (ULift.{w} ℤ)) ℤ
      (ModuleCat.of ℤ (ULift.{w} ℤ)) 2 :=
  complexEulerClass F E (r := 0) hF

/-- The first Chern class of a complex line bundle is the Euler class of its underlying real plane
bundle with the complex orientation. -/
theorem lineFirstChernClass_def :
    lineFirstChernClass F E hF = complexEulerClass F E (r := 0) hF :=
  (rfl)

end Definition

end TauCeti
