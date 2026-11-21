/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.Cup.TrivialF2.Zero
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Evens.Norm.Cup

/-!
# The Evens norm in degree zero, and the norm of the unit

For a compact open subgroup `U` of finite index `l` in a topological group `G`, the Evens norm
`N_U^G : Hⁿ(U, 𝔽₂) → H^{l n}(G, 𝔽₂)` is the identity in degree zero: under the identifications
`H⁰(U, 𝔽₂) ≅ 𝔽₂ ≅ H⁰(G, 𝔽₂)` it sends `a` to `a ^ l = a`, after transporting the degree `l * 0`
to `0`. In particular the norm is unital, `N_U^G 1 = 1`.

Together with multiplicativity (`OpenSubgroup.evensNorm_cup`), this makes the norm a homomorphism
of graded monoids: on the graded monoid of homogeneous classes, `(n, x) ↦ (l n, N_U^G x)` is a
monoid homomorphism `OpenSubgroup.evensNormMonoidHom`. In this form the norm of a finite product
of homogeneous classes is the product of their norms (`map_prod`). It is not additive, so it is
not a ring homomorphism of the graded cohomology algebras.

## Main definitions

* `OpenSubgroup.evensNormMonoidHom`: the Evens norm as a homomorphism of the graded monoids of
  homogeneous mod-two cohomology classes.

## Main results

* `OpenSubgroup.cohomF2ZeroLinearEquiv_degreeCast_evensNorm`: in degree zero the norm is the
  identity of `𝔽₂`.
* `OpenSubgroup.evensNorm_one`: the norm of the unit class is the unit class.

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

/-- **The Evens norm in degree zero is the identity of `𝔽₂`**: under the identifications
`H⁰(U, 𝔽₂) ≅ 𝔽₂ ≅ H⁰(G, 𝔽₂)` of `TauCeti.cohomF2ZeroLinearEquiv`, the norm of a degree-zero class,
transported from degree `[G : U] * 0` to `0`, has the same coefficient as the class. -/
-- Not `@[simp]`: `simp` rewrites `[G : U] * 0` to `0` and then drops the transport itself.
theorem cohomF2ZeroLinearEquiv_degreeCast_evensNorm (x : cohomF2 U.toSubgroup 0) :
    cohomF2ZeroLinearEquiv G
        ((ContinuousCohomology.degreeCast (trivialF2 G) (mul_zero _)).hom (U.evensNorm x)) =
      cohomF2ZeroLinearEquiv U.toSubgroup x := by
  obtain ⟨z, hz, rfl⟩ := TopRep.exists_cochainClass_eq x
  -- `tensorNormCocycleClass_eq_degreeZeroClass` already reads `[G : U] * 0` as `0`, the value of
  -- `Nat.mul` at `0`, so the remaining transport is along `0 = 0`.
  rw [evensNorm_cochainClass U default, tensorNormCocycleClass_eq_degreeZeroClass,
    ContinuousCohomology.degreeCast_rfl, CategoryTheory.Iso.refl_hom,
    CategoryTheory.ConcreteCategory.id_apply,
    TopRep.cochainClass_eq_degreeZeroClass _ z hz (z.1 1)
      (fun g ↦ trivialF2_ρ_apply_apply U.toSubgroup g _) rfl,
    cohomF2ZeroLinearEquiv_degreeZeroClass, cohomF2ZeroLinearEquiv_degreeZeroClass,
    AddEquiv.apply_symm_apply]

/-- **The Evens norm is unital**: `N_U^G 1 = 1`, with the unit of `H⁰(G, 𝔽₂)` transported to the
degree `[G : U] * 0` of the norm. -/
@[simp]
theorem evensNorm_one : U.evensNorm (1 : cohomF2 U.toSubgroup 0) =
    (ContinuousCohomology.degreeCast (trivialF2 G) (mul_zero _).symm).hom (1 : cohomF2 G 0) := by
  have h := cohomF2ZeroLinearEquiv_degreeCast_evensNorm U 1
  rw [cohomF2ZeroLinearEquiv_one, ← cohomF2ZeroLinearEquiv_one G] at h
  rw [← (cohomF2ZeroLinearEquiv G).injective h,
    ContinuousCohomology.degreeCast_hom_degreeCast_hom_apply,
    ContinuousCohomology.degreeCast_rfl, CategoryTheory.Iso.refl_hom,
    CategoryTheory.ConcreteCategory.id_apply]

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
