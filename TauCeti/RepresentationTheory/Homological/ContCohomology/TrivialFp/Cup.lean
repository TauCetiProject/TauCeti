/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.GroupAction.Trivial
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Cup.Naturality
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Cup.RestrictScalars
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Cup.TrivialFp.Basic
public import TauCeti.RepresentationTheory.Homological.ContCohomology.TrivialFp.Explicit

/-!
# The cup product with trivial `𝔽_p` coefficients on the explicit models

The cup square `cupFp p G : H¹(G, 𝔽_p) × H¹(G, 𝔽_p) → H²(G, 𝔽_p)` is the canonical cup product of
Mathlib's continuous cohomology at the multiplication pairing of the trivial coefficient object
`trivialFp p G`, and the Demushkin condition on a pro-`p` group is stated against it. The explicit
models `H1 G (ZMod p)` and `H2 G (ZMod p)` of the same groups, identified with `cohomFp p G 1` and
`cohomFp p G 2` by `TauCeti.cohomFpAddEquivH1` and `TauCeti.cohomFpAddEquivH2`, carry the explicit
`(1,1)` cup product `TauCeti.ContCohomology.explicitCup11` of multiplication,
`(a ⌣ b) (g, h) = a g * b h` on continuous characters `a`, `b : G → 𝔽_p`. This file proves that
the two agree: **the cup square of two classes of `H¹(G, 𝔽_p)` is the class of the product cocycle
of the corresponding characters**.

This is what lets the cup product on `cohomFp` be computed on characters, for instance through a
Heisenberg cochain and the transgression of a minimal presentation, which is how the cup matrix of
a one-relator pro-`p` group is read off its relator.

## Main results

* `TauCeti.cohomFpAddEquivH2_cupFp`: under the identifications of `H¹(G, 𝔽_p)` and `H²(G, 𝔽_p)`
  with their explicit models, `cupFp p G` is the explicit `(1,1)` cup product of multiplication.
* `TauCeti.cupFp_cohomFpAddEquivH1_symm`: the same identity read from the explicit side.
* `TauCeti.cupFp_eq_zero_iff`: the cup square of two classes vanishes exactly when the explicit
  cup product of the corresponding explicit classes does.
* `TauCeti.explicitCup11_mul_bijective_iff`: the explicit cup square is a perfect pairing exactly
  when `cupFp p G` is.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., Springer (2008),
  Chapter I, §4, for the inhomogeneous cup product formula.
* J.-P. Serre, *Galois Cohomology*, Springer (1997), Chapter I, §4.5.
-/

public section

namespace TauCeti

open CategoryTheory TauCeti.ContCohomology _root_.ContinuousCohomology

universe u

attribute [local instance] TopRep.distribMulAction

-- Preferring the ring path keeps a single additive structure on `ZMod p`.
attribute [local instance 2000] Ring.toAddCommGroup

section Mul

variable (p : ℕ) (G : Type u) [Group G]

/-- The multiplication pairing `fpPairing p G` with its scalars forgotten, a biadditive map on the
lifted carrier of `trivialFp p G`. -/
private noncomputable def trivialFpMul :
    (trivialFp p G).V →+ (trivialFp p G).V →+ (trivialFp p G).V :=
  LinearMap.toAddMonoidHom'.comp (fpPairing p G).bil.toAddMonoidHom

/-- The multiplication pairing `fpPairing p G` has the values of `trivialFpMul`. -/
private theorem trivialFpMul_eq (x y : (trivialFp p G).V) :
    trivialFpMul p G x y = (fpPairing p G).bil x y :=
  (rfl)

/-- The universe lift intertwines `trivialFpMul` with multiplication in `ZMod p`. -/
private theorem trivialFpEquiv_trivialFpMul (x y : (trivialFp p G).V) :
    trivialFpEquiv p G (trivialFpMul p G x y) = trivialFpEquiv p G x * trivialFpEquiv p G y := by
  rw [trivialFpMul_eq, fpPairing_bil_apply, LinearEquiv.apply_symm_apply]

end Mul

variable (p : ℕ) (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G]

attribute [local instance] continuousSMul_trivialFp

variable [DistribMulAction G (ZMod p)] [ContinuousSMul G (ZMod p)]
  (htriv : ∀ (g : G) (m : ZMod p), g • m = m)
include htriv

/-- **The cup square on the explicit models.** Under the identifications
`TauCeti.cohomFpAddEquivH1` and `TauCeti.cohomFpAddEquivH2` of `H¹(G, 𝔽_p)` and `H²(G, 𝔽_p)` with
`H1 G (ZMod p)` and `H2 G (ZMod p)`, for any trivial action of `G` on `ZMod p`, the cup square
`cupFp p G` is the explicit `(1,1)` cup product of multiplication in `ZMod p`: the cup square of
two classes is the class of the cocycle `(g, h) ↦ a g * b h`, for the corresponding characters
`a` and `b`. -/
theorem cohomFpAddEquivH2_cupFp (a b : cohomFp p G 1) :
    cohomFpAddEquivH2 p G htriv (cupFp p G a b) =
      explicitCup11 G (ZMod p) (ZMod p) (ZMod p) AddMonoidHom.mul continuous_mul
        (smul_mul_smul_of_smul_eq_self htriv) (cohomFpAddEquivH1 p G htriv a)
        (cohomFpAddEquivH1 p G htriv b) := by
  obtain ⟨x, rfl⟩ := (trivialFp p G).explicitH1AddEquivContinuousCohomologyOfDiscrete.surjective a
  obtain ⟨y, rfl⟩ := (trivialFp p G).explicitH1AddEquivContinuousCohomologyOfDiscrete.surjective b
  rw [cupFp_def, (fpPairing p G).cup_one_one_explicitH1AddEquivContinuousCohomologyOfDiscrete
    (trivialFpMul p G) (trivialFpMul_eq p G) x y,
    cohomFpAddEquivH2_explicitH2AddEquivContinuousCohomologyOfDiscrete,
    cohomFpAddEquivH1_explicitH1AddEquivContinuousCohomologyOfDiscrete,
    cohomFpAddEquivH1_explicitH1AddEquivContinuousCohomologyOfDiscrete, explicitMap1Equiv_apply,
    explicitMap1Equiv_apply, explicitMap2Equiv_apply]
  -- naturality of the explicit cup product along the universe lift, from the pairing
  -- `trivialFpMul` to multiplication in `ZMod p`, intertwined by `trivialFpEquiv`; the group does
  -- not move, and the continuity and equivariance hypotheses are those of the goal
  exact explicitMap2_explicitCup11 (μ := trivialFpMul p G) (H := G) (M' := ZMod p) (N' := ZMod p)
    (P' := ZMod p) (μ' := AddMonoidHom.mul) (hequiv' := smul_mul_smul_of_smul_eq_self htriv)
    (fM := (trivialFpEquiv p G).toAddEquiv.toAddMonoidHom)
    (fN := (trivialFpEquiv p G).toAddEquiv.toAddMonoidHom)
    (fP := (trivialFpEquiv p G).toAddEquiv.toAddMonoidHom)
    (hpair := trivialFpEquiv_trivialFpMul p G) (a := x) (b := y) ..

/-- **The cup square on the explicit models, read from the explicit side**: the cup square of the
classes corresponding to two explicit classes `x`, `y` corresponds to their explicit `(1,1)` cup
product of multiplication. -/
theorem cupFp_cohomFpAddEquivH1_symm (x y : H1 G (ZMod p)) :
    cupFp p G ((cohomFpAddEquivH1 p G htriv).symm x) ((cohomFpAddEquivH1 p G htriv).symm y) =
      (cohomFpAddEquivH2 p G htriv).symm
        (explicitCup11 G (ZMod p) (ZMod p) (ZMod p) AddMonoidHom.mul continuous_mul
          (smul_mul_smul_of_smul_eq_self htriv) x y) := by
  rw [AddEquiv.eq_symm_apply, cohomFpAddEquivH2_cupFp, AddEquiv.apply_symm_apply,
    AddEquiv.apply_symm_apply]

/-- The cup square of two classes of `H¹(G, 𝔽_p)` vanishes exactly when the explicit `(1,1)` cup
product of the corresponding explicit classes vanishes. -/
theorem cupFp_eq_zero_iff (a b : cohomFp p G 1) :
    cupFp p G a b = 0 ↔
      explicitCup11 G (ZMod p) (ZMod p) (ZMod p) AddMonoidHom.mul continuous_mul
        (smul_mul_smul_of_smul_eq_self htriv) (cohomFpAddEquivH1 p G htriv a)
        (cohomFpAddEquivH1 p G htriv b) = 0 := by
  rw [← cohomFpAddEquivH2_cupFp, map_eq_zero_iff _ (cohomFpAddEquivH2 p G htriv).injective]

/-- **The explicit cup square is a perfect pairing exactly when the cup square is**: under the
identifications `TauCeti.cohomFpAddEquivH1` and `TauCeti.cohomFpAddEquivH2`, the explicit `(1,1)`
cup product of multiplication, `x ↦ (y ↦ x ⌣ y)`, is a bijection from `H1 G (ZMod p)` onto the
additive homomorphisms `H1 G (ZMod p) →+ H2 G (ZMod p)` exactly when `cupFp p G` is a bijection
from `H¹(G, 𝔽_p)` onto the linear maps `H¹(G, 𝔽_p) →ₗ H²(G, 𝔽_p)`. -/
theorem explicitCup11_mul_bijective_iff :
    Function.Bijective (explicitCup11 G (ZMod p) (ZMod p) (ZMod p) AddMonoidHom.mul continuous_mul
      (smul_mul_smul_of_smul_eq_self htriv)) ↔ Function.Bijective (cupFp p G) := by
  -- the explicit cup square is `cupFp` conjugated by the two identifications
  have h : ⇑(explicitCup11 G (ZMod p) (ZMod p) (ZMod p) AddMonoidHom.mul continuous_mul
      (smul_mul_smul_of_smul_eq_self htriv)) =
      ((AddMonoidHom.toZModLinearMapEquiv p).symm.trans
        ((cohomFpAddEquivH1 p G htriv).addMonoidHomCongrLeft.trans
          (cohomFpAddEquivH2 p G htriv).addMonoidHomCongrRight)) ∘ cupFp p G ∘
        (cohomFpAddEquivH1 p G htriv).symm :=
    funext fun x => AddMonoidHom.ext fun y => by
      simp [AddMonoidHom.toZModLinearMapEquiv, cupFp_cohomFpAddEquivH1_symm p G htriv]
  rw [h, EquivLike.comp_bijective, EquivLike.bijective_comp]

end TauCeti
