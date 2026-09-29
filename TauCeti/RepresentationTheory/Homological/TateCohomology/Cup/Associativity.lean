/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.RepresentationTheory.Homological.TateCohomology.Cup.Product

/-!
# Associativity of the Tate cup product with two degree-zero classes

The tensor associator identifies the two ways to cup a class of arbitrary degree with two
degree-zero classes. This is a base case of associativity for the Tate cup product.

See Artin and Tate, *Class Field Theory*, Preliminaries §2, and Brown,
*Cohomology of Groups*, Chapter VI, §5.
-/

public noncomputable section

universe u

open CategoryTheory MonoidalCategory Rep
open scoped TensorProduct

namespace TauCeti.TateCohomology

variable {k G : Type u} [CommRing k] [Group G] [Fintype G]

/-- Cup product with two degree-zero Tate classes is associative, after applying the tensor
associator to the coefficient representation. -/
@[simp]
theorem cupH0_assoc_zero (M N P : Rep k G) (p : ℤ)
    (x : tateCohomology M p) (y : tateCohomology N 0)
    (z : tateCohomology P 0) :
    (tateCohomologyFunctor p).map (α_ M N P).hom
      (cupH0 (M ⊗ N) P p (cupH0 M N p x y) z) =
      cupH0 M (N ⊗ P) p x (cupH0 N P 0 y z) := by
  induction y using H0_induction_on with
  | h y =>
    induction z using H0_induction_on with
    | h z =>
      let yz : (N ⊗ P).ρ.invariants := ⟨(y : N.V) ⊗ₜ[k] (z : P.V), by
        intro g
        simp [Representation.tprod_apply, y.2 g, z.2 g]⟩
      have h : Rep.tensorInvariant M y ≫ Rep.tensorInvariant (M ⊗ N) z ≫
          (α_ M N P).hom = Rep.tensorInvariant M yz := by
        ext m
        simp only [Rep.hom_comp, Representation.IntertwiningMap.comp_toLinearMap,
          LinearMap.comp_apply, Representation.IntertwiningMap.toLinearMap_apply]
        have hy : (Rep.tensorInvariant M y).hom m = m ⊗ₜ[k] (y : N.V) :=
          Rep.tensorInvariant_hom_apply M y m
        have hz (v : (M ⊗ N).V) :
            (Rep.tensorInvariant (M ⊗ N) z).hom v = v ⊗ₜ[k] (z : P.V) :=
          Rep.tensorInvariant_hom_apply (M ⊗ N) z v
        have hyz : (Rep.tensorInvariant M yz).hom m =
            m ⊗ₜ[k] ((y : N.V) ⊗ₜ[k] (z : P.V)) :=
          Rep.tensorInvariant_hom_apply M _ m
        rw [hy, hz, hyz, Rep.hom_hom_associator]
        exact Representation.TensorProduct.assoc_apply M.ρ N.ρ P.ρ m
          (y : N.V) (z : P.V)
      rw [cupH0_H0π, cupH0_H0π, cupH0_H0π_H0π, cupH0_H0π,
        ← ModuleCat.comp_apply, ← Functor.map_comp,
        ← ModuleCat.comp_apply, ← Functor.map_comp]
      exact congrArg (fun f : M ⟶ M ⊗ (N ⊗ P) ↦ (tateCohomologyFunctor p).map f x) h

/-- Associativity of the Tate cup product in tridegrees `(p, 0, 0)`. -/
theorem cup_assoc_zero_zero (M N P : Rep k G) (p : ℤ)
    (x : tateCohomology M p) (y : tateCohomology N 0)
    (z : tateCohomology P 0) :
    (tateCohomologyFunctor p).map (α_ M N P).hom
      (cup (M ⊗ N) P p 0 p (by omega)
        (cup M N p 0 p (by omega) x y) z) =
      cup M (N ⊗ P) p 0 p (by omega) x
        (cup N P 0 0 0 (by omega) y z) := by
  simpa only [cup_zero_right] using cupH0_assoc_zero M N P p x y z

end TauCeti.TateCohomology
