/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Grassmannian.Points
public import TauCeti.RingTheory.Grassmannian.Dual

/-!
# The dual Grassmannian

Let `M` be a finite projective module over a commutative ring `R`, of constant rank `k + l`, with
dual `M^∨`. This file constructs the isomorphism of Grassmannian schemes over `Spec R`

`G(k, M) ≅ G(l, M^∨)` (`Module.Grassmannian.schemeDualIso`).

A point of `G(k, M)` over an `R`-algebra `A` is a submodule `N ⊆ A ⊗[R] M` with finite projective
quotient of rank `k`; `N` is then a subbundle of rank `l`
(`Module.Grassmannian.rankAtStalk_toSubmodule`). The isomorphism sends the point classifying `N`
to the point classifying its annihilator `N^⊥ ⊆ A ⊗[R] M^∨`, the kernel of the restriction
`(A ⊗[R] M)^∨ → N^∨` (`Module.Grassmannian.toSchemeHom_comp_schemeDualIso_hom`), and its inverse
sends the point classifying `K` to the point classifying the coannihilator of `K`
(`Module.Grassmannian.toSchemeHom_comp_schemeDualIso_inv`). So over every `A`, the point of
`G(l, M^∨)` classifying `K` is the annihilator of the point of `G(k, M)` classifying `N` exactly
when `N` is the coannihilator of `K`.

The maps of points are natural in `A` (`Module.Grassmannian.baseChangeDualEquiv_map`), so each is
composition with a morphism of schemes (`Module.Grassmannian.homOfPoints`), and the two
composites are identities because they are on points (`Module.Grassmannian.scheme_hom_ext`).

## Main definitions

* `Module.Grassmannian.schemeDualIso h`: the isomorphism `G(k, M) ≅ G(l, M^∨)` for `M` finite
  projective of constant rank `k + l`.

## Main results

* `Module.Grassmannian.toSchemeHom_comp_schemeDualIso_hom` and
  `Module.Grassmannian.toSchemeHom_comp_schemeDualIso_inv`: the isomorphism on points.
* `Module.Grassmannian.schemeDualIso_hom_toSpec` and
  `Module.Grassmannian.schemeDualIso_inv_toSpec`: the isomorphism lies over `Spec R`.

## References

* A. Grothendieck, J. Dieudonné, *Éléments de géométrie algébrique I* (Springer, 1971), 9.7.
* [The Stacks Project, Tag 089R](https://stacks.math.columbia.edu/tag/089R), for the Grassmannian
  functor.
-/

public section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct

namespace Module.Grassmannian

variable {R : Type u} [CommRing R] {M M' : Type u} [AddCommGroup M] [Module R M]
  [AddCommGroup M'] [Module R M'] {k l : ℕ}

variable [Module.Finite R M] [Module.Projective R M]

/-- **The dual Grassmannian.** If `M` is finite projective of constant rank `k + l` over `R`, then
`G(k, M) ≅ G(l, M^∨)` over `Spec R` (`Module.Grassmannian.schemeDualIso_hom_toSpec`). It sends
the point classifying `N` to the point classifying the annihilator of `N`
(`Module.Grassmannian.toSchemeHom_comp_schemeDualIso_hom`), and its inverse takes coannihilators
(`Module.Grassmannian.toSchemeHom_comp_schemeDualIso_inv`). -/
noncomputable def schemeDualIso (h : ∀ p, rankAtStalk (R := R) M p = k + l) :
    scheme R M k ≅ scheme R (Module.Dual R M) l where
  hom := homOfPoints (fun A _ _ N ↦ toSchemeHom (baseChangeDualEquiv A h N))
    fun _ _ _ _ _ _ f N ↦ by rw [baseChangeDualEquiv_map, toSchemeHom_map]
  inv := homOfPoints (fun A _ _ K ↦ toSchemeHom ((baseChangeDualEquiv A h).symm K))
    fun _ _ _ _ _ _ f K ↦ by rw [baseChangeDualEquiv_symm_map, toSchemeHom_map]
  hom_inv_id := scheme_hom_ext fun A _ _ N ↦ by simp
  inv_hom_id := scheme_hom_ext fun A _ _ K ↦ by simp

/-- **`schemeDualIso` on points.** The morphism classifying `N` over an `R`-algebra `A`, composed
with `schemeDualIso h`, classifies the annihilator of `N` in `A ⊗[R] M^∨`
(`Module.Grassmannian.mem_baseChangeDualEquiv_iff`). -/
@[reassoc (attr := simp)]
theorem toSchemeHom_comp_schemeDualIso_hom (h : ∀ p, rankAtStalk (R := R) M p = k + l)
    {A : Type u} [CommRing A] [Algebra R A] (N : G(k, A ⊗[R] M; A)) :
    toSchemeHom N ≫ (schemeDualIso h).hom = toSchemeHom (baseChangeDualEquiv A h N) :=
  toSchemeHom_comp_homOfPoints _ _ N

/-- **The inverse of `schemeDualIso` on points.** The morphism classifying `K` over an
`R`-algebra `A`, composed with the inverse of `schemeDualIso h`, classifies the point of
`G(k, M)` whose annihilator is `K`. -/
@[reassoc (attr := simp)]
theorem toSchemeHom_comp_schemeDualIso_inv (h : ∀ p, rankAtStalk (R := R) M p = k + l)
    {A : Type u} [CommRing A] [Algebra R A] (K : G(l, A ⊗[R] Module.Dual R M; A)) :
    toSchemeHom K ≫ (schemeDualIso h).inv = toSchemeHom ((baseChangeDualEquiv A h).symm K) :=
  toSchemeHom_comp_homOfPoints _ _ K

/-- `schemeDualIso h` lies over `Spec R`. -/
@[reassoc (attr := simp)]
theorem schemeDualIso_hom_toSpec (h : ∀ p, rankAtStalk (R := R) M p = k + l) :
    (schemeDualIso h).hom ≫ toSpec R (Module.Dual R M) l = toSpec R M k :=
  scheme_hom_ext fun A _ _ N ↦ by simp

/-- The inverse of `schemeDualIso h` lies over `Spec R`. -/
@[reassoc (attr := simp)]
theorem schemeDualIso_inv_toSpec (h : ∀ p, rankAtStalk (R := R) M p = k + l) :
    (schemeDualIso h).inv ≫ toSpec R M k = toSpec R (Module.Dual R M) l := by
  rw [Iso.inv_comp_eq, schemeDualIso_hom_toSpec]

end Module.Grassmannian
