/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Bialgebra.MonoidAlgebra

/-!
# Graded coactions of monoid algebras

Any homomorphism of monoids `w : M →* L` equips the monoid algebra `R[M]` with a canonical
`R[L]`-comodule algebra map `MonoidAlgebra.gradedCoaction R w : R[M] →ₐ[R] R[L] ⊗[R] R[M]`,
sending `single m r` to `single (w m) 1 ⊗ₜ single m r` (additively
`AddMonoidAlgebra.gradedCoaction`). It satisfies the counit, coassociativity, and naturality laws
with respect to Mathlib's bialgebra structure on `R[L]`, specializing to
`Bialgebra.comulAlgHom R R[L]` when `w = id`.

## Main declarations

* `MonoidAlgebra.gradedCoaction` / `AddMonoidAlgebra.gradedCoaction`: graded coaction induced by
  a monoid homomorphism `w : M →* L` (or `w : M →+ L`).
* `MonoidAlgebra.lid_comp_map_counit_gradedCoaction` /
  `AddMonoidAlgebra.lid_comp_map_counit_gradedCoaction`: counit law.
* `MonoidAlgebra.assoc_comp_map_gradedCoaction` /
  `AddMonoidAlgebra.assoc_comp_map_gradedCoaction`: coassociativity law.
* `MonoidAlgebra.map_mapDomain_comp_gradedCoaction` /
  `AddMonoidAlgebra.map_mapDomain_comp_gradedCoaction`: naturality under compatible homomorphisms.

## References

* W. Bruns and J. Gubeladze, *Polytopes, Rings, and K-Theory*, Chapters 2 and 4.
* D. Cox, J. Little and H. Schenck, *Toric Varieties*, §§1.1 and 3.1.
* W. Fulton, *Introduction to Toric Varieties*, §§1.2–1.3.
-/

public section

open scoped TensorProduct

namespace MonoidAlgebra

variable (R : Type*) [CommSemiring R]

/-- For a monoid homomorphism `w : M →* L`, `gradedCoaction R w` is the `R`-algebra comodule map
`R[M] →ₐ[R] R[L] ⊗[R] R[M]` sending `single m r` to `single (w m) 1 ⊗ₜ single m r`. -/
@[to_additive (dont_translate := R)
/-- For an additive monoid homomorphism `w : M →+ L`, `gradedCoaction R w` is the `R`-algebra
comodule map `R[M] →ₐ[R] R[L] ⊗[R] R[M]` sending `single m r` to `single (w m) 1 ⊗ₜ single m r`. -/]
noncomputable def gradedCoaction {M L : Type*} [Monoid M] [Monoid L] (w : M →* L) :
    MonoidAlgebra R M →ₐ[R] MonoidAlgebra R L ⊗[R] MonoidAlgebra R M :=
  (Algebra.TensorProduct.map (mapDomainAlgHom R R w) (AlgHom.id R _)).comp
    (Bialgebra.comulAlgHom R (MonoidAlgebra R M))

/-- `gradedCoaction R w` sends `single m r` to `single (w m) 1 ⊗ₜ single m r`. -/
@[to_additive (dont_translate := R) (attr := simp)
/-- `gradedCoaction R w` sends `single m r` to `single (w m) 1 ⊗ₜ single m r`. -/]
theorem gradedCoaction_single {M L : Type*} [Monoid M] [Monoid L] (w : M →* L)
    (m : M) (r : R) :
    gradedCoaction R w (single m r) = single (w m) 1 ⊗ₜ[R] single m r := by simp [gradedCoaction]

/-- For the identity homomorphism, `gradedCoaction` recovers the bialgebra comultiplication. -/
@[to_additive (dont_translate := R) (attr := simp)
/-- For the identity homomorphism, `gradedCoaction` recovers the bialgebra comultiplication. -/]
theorem gradedCoaction_id (L : Type*) [Monoid L] :
    gradedCoaction R (MonoidHom.id L) = Bialgebra.comulAlgHom R (MonoidAlgebra R L) := by
  ext; simp

/-- Counit axiom for `gradedCoaction`: applying the counit of `R[L]` on the left recovers the
identity on `R[M]`. -/
@[to_additive (dont_translate := R) (attr := simp)
/-- Counit axiom for `gradedCoaction`: applying the counit of `R[L]` on the left recovers the
identity on `R[M]`. -/]
theorem lid_comp_map_counit_gradedCoaction {M L : Type*} [Monoid M] [Monoid L] (w : M →* L) :
    (Algebra.TensorProduct.lid R (MonoidAlgebra R M)).toAlgHom.comp
      ((Algebra.TensorProduct.map (Bialgebra.counitAlgHom R (MonoidAlgebra R L))
        (AlgHom.id R _)).comp (gradedCoaction R w)) = AlgHom.id R (MonoidAlgebra R M) := by
  ext; simp

/-- Coassociativity of `gradedCoaction` with respect to the comultiplication of `R[L]`. -/
@[to_additive (dont_translate := R)
/-- Coassociativity of `gradedCoaction` with respect to the comultiplication of `R[L]`. -/]
theorem assoc_comp_map_gradedCoaction {M L : Type*} [Monoid M] [Monoid L] (w : M →* L) :
    (Algebra.TensorProduct.assoc R R R (MonoidAlgebra R L) (MonoidAlgebra R L)
      (MonoidAlgebra R M)).toAlgHom.comp
      ((Algebra.TensorProduct.map (Bialgebra.comulAlgHom R (MonoidAlgebra R L))
        (AlgHom.id R _)).comp (gradedCoaction R w)) =
      (Algebra.TensorProduct.map (AlgHom.id R _) (gradedCoaction R w)).comp
        (gradedCoaction R w) := by
  ext; simp

/-- Naturality of `gradedCoaction` under compatible monoid homomorphisms. -/
@[to_additive (dont_translate := R)
/-- Naturality of `gradedCoaction` under compatible additive monoid homomorphisms. -/]
theorem map_mapDomain_comp_gradedCoaction {M₁ M₂ L₁ L₂ : Type*} [Monoid M₁]
    [Monoid M₂] [Monoid L₁] [Monoid L₂] {w₁ : M₁ →* L₁} {w₂ : M₂ →* L₂}
    {g : L₁ →* L₂} {f : M₁ →* M₂} (h : w₂.comp f = g.comp w₁) :
    (Algebra.TensorProduct.map (mapDomainAlgHom R R g) (mapDomainAlgHom R R f)).comp
      (gradedCoaction R w₁) = (gradedCoaction R w₂).comp (mapDomainAlgHom R R f) := by
  ext m
  have hm : w₂ (f m) = g (w₁ m) := DFunLike.congr_fun h m
  simp [hm]

end MonoidAlgebra
