/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.Evens.Norm.Cup
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Evens.Norm.DegreeZero

/-!
# The Evens norm as a homomorphism of graded monoids

For a compact open subgroup `U` of finite index `l` in a topological group `G`, the Evens norm
`N_U^G : Hⁿ(U, 𝔽₂) → H^{l n}(G, 𝔽₂)` is unital (`OpenSubgroup.evensNorm_one`) and multiplicative
(`OpenSubgroup.evensNorm_cup`). Together these make the norm a homomorphism of graded monoids: on
the graded monoid of homogeneous classes, `(n, x) ↦ (l n, N_U^G x)` is a monoid homomorphism
`OpenSubgroup.evensNormMonoidHom`. In this form the norm of a finite product of homogeneous
classes is the product of their norms (`map_prod`). It is not additive, so it is not a ring
homomorphism of the graded cohomology algebras.

## Main definitions

* `OpenSubgroup.evensNormMonoidHom`: the Evens norm as a homomorphism of the graded monoids of
  homogeneous mod-two cohomology classes.

## References

* L. Evens, *A generalization of the transfer map in the cohomology of groups*,
  Trans. Amer. Math. Soc. **108** (1963), §6.
-/

public section

namespace OpenSubgroup

open TauCeti

universe u

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (U : OpenSubgroup G) [U.toSubgroup.FiniteIndex] [CompactSpace U.toSubgroup]
  [Fintype (G ⧸ U.toSubgroup)]

/-- **The Evens norm as a homomorphism of graded monoids**: on homogeneous mod-two classes, the
map `(n, x) ↦ ([G : U] n, N_U^G x)` preserves the unit (`OpenSubgroup.evensNorm_one`) and cup
products (`OpenSubgroup.evensNorm_cup`). The norm is not additive, so this is not a ring
homomorphism of the graded cohomology algebras. -/
noncomputable def evensNormMonoidHom :
    GradedMonoid (cohomF2 U.toSubgroup) →* GradedMonoid (cohomF2 G) where
  toFun x := .mk (Fintype.card (G ⧸ U.toSubgroup) * x.fst) (U.evensNorm x.snd)
  map_one' := Sigma.ext (mul_zero _) <| by
    rw [GradedMonoid.snd_one, GradedMonoid.snd_one, cohomF2.gOne_eq_one, cohomF2.one_eq_one,
      evensNorm_one, cohomF2.gOne_eq_one, cohomF2.one_eq_one]
    exact ContinuousCohomology.degreeCast_hom_apply_heq _ _
  map_mul' x y := by
    rw [GradedMonoid.mk_mul_mk]
    refine Sigma.ext (mul_add _ _ _) ?_
    rw [GradedMonoid.snd_mul, cohomF2.gMul_eq_cup, cohomF2.gMul_eq_cup, evensNorm_cup]
    exact ContinuousCohomology.degreeCast_hom_apply_heq _ _

/-- The graded Evens norm of a homogeneous class `x` of degree `n` is `N_U^G x`, in degree
`[G : U] n`. -/
@[simp]
theorem evensNormMonoidHom_mk {n : ℕ} (x : cohomF2 U.toSubgroup n) :
    U.evensNormMonoidHom (GradedMonoid.mk n x) =
      GradedMonoid.mk (Fintype.card (G ⧸ U.toSubgroup) * n) (U.evensNorm x) :=
  (rfl)

end OpenSubgroup
