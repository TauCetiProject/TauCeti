/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Group.Equiv.Pi
public import TauCeti.RingTheory.Etale.Torsor.Tensor
public import TauCeti.RingTheory.Etale.Torsor.Trivial
public import TauCeti.RingTheory.PiTensorProduct.Equiv
public import TauCeti.RingTheory.PiTensorProduct.MulSemiringAction

import TauCeti.Algebra.Group.Pi.Lemmas

/-!
# Finite tensor products of finite étale torsors

If `B i` is a finite étale `G i`-torsor over `A` for each `i` in a finite type `ι`, then the
tensor product `⨂[A] i, B i` is a finite étale torsor under the product group `∀ i, G i`, acting
factorwise (`PiTensorProduct.piMulSemiringAction`). Geometrically, the fibre product over
`Spec A` of finitely many torsors is a torsor under the product of their groups. The empty tensor
product is `A`, a torsor under the trivial group.

For a map `f : σ → τ` of finite index types, multiplication along the fibres of `f`,
`PiTensorProduct.fiberwiseMul f : ⨂[A] i, B (f i) → ⨂[A] j, B j`, is equivariant along the
restriction `g ↦ g ∘ f`, which is surjective when `f` is injective. In that case the inclusion of
tensor factors makes `⨂[A] j, B j` a finite étale torsor over `⨂[A] i, B (f i)` under the
elements of `∀ j, G j` that are trivial on the range of `f`. In particular it is injective and
faithfully flat.

These are the levels and transition maps of the tower of finite étale torsors indexed by the
finite sets of finite étale `A`-algebras, whose colimit has no nonsplit finite étale covers.

## Main results

* `TauCeti.Algebra.IsFiniteEtaleTorsor.piTensorProduct`: `⨂[A] i, B i` is a finite étale
  `(∀ i, G i)`-torsor over `A`.
* `TauCeti.Algebra.IsFiniteEtaleTorsor.fiberwiseMul`: for injective `f : σ → τ`,
  `⨂[A] j, B j` is a finite étale torsor over `⨂[A] i, B (f i)` under the kernel of the
  restriction `(∀ j, G j) →* ∀ i, G (f i)`.

## References

* S. U. Chase, D. K. Harrison and A. Rosenberg, *Galois theory and Galois cohomology of
  commutative rings*, Mem. Amer. Math. Soc. **52** (1965), 15–33, Theorem 1.3.
* P. Scholze, *Étale cohomology of diamonds*, Lemma 15.3.
-/

public section

open TensorProduct PiTensorProduct

namespace TauCeti.Algebra

namespace IsFiniteEtaleTorsor

attribute [local instance] piMulSemiringAction Algebra.TensorProduct.prodMulSemiringAction
  rightRegularMulSemiringAction

universe u v w

variable {A : Type*} [CommRing A]

/-- `IsFiniteEtaleTorsor.piTensorProduct`, with the finiteness of the product group as a
separate instance so that the statement does not depend on the instance `Finite ι`, which lets
the proof induct on `ι`. -/
private theorem piTensorProduct_aux (ι : Type u) [Finite ι] {G : ι → Type v} {B : ι → Type w}
    [∀ i, Group (G i)] [∀ i, Finite (G i)] [Finite (∀ i, G i)] [∀ i, CommRing (B i)]
    [∀ i, Algebra A (B i)] [∀ i, MulSemiringAction (G i) (B i)] [∀ i, SMulCommClass (G i) A (B i)]
    [∀ i, IsFiniteEtaleTorsor (G i) A (B i)] :
    IsFiniteEtaleTorsor (∀ i, G i) A (⨂[A] i, B i) := by
  induction ι using Finite.induction_empty_option with
  | @of_equiv α β e ih =>
    -- Reindex along `e`: slot `i` of the source is slot `e i` of the target.
    -- `e.symm.symm` is `e`, written so that the reindexed tensor product matches the source.
    let φ := (MulEquiv.piCongrLeft G e.symm.symm).symm
    have : Finite (∀ i, G (e.symm.symm i)) := .of_equiv _ φ.toEquiv
    have := ih (G := fun i ↦ G (e.symm.symm i)) (B := fun i ↦ B (e.symm.symm i))
    refine of_mulEquiv_algEquiv φ (reindexAlgEquiv B e.symm) fun g x ↦ ?_
    simp only [piMulSemiringAction_smul_def, reindexAlgEquiv_mapAlgHom, φ,
      MulEquiv.piCongrLeft_symm_apply]
  | h_empty =>
    -- The empty tensor product is `A`, the split torsor `(∀ i, G i) → A` of the trivial group.
    let e : (⨂[A] i, B i) ≃ₐ[A] ((∀ i : PEmpty, G i) → A) := (isEmptyAlgEquiv PEmpty B).trans
      (AlgEquiv.funUnique (ι := ∀ i : PEmpty, G i) (R := A) (S := A)).symm
    refine of_mulEquiv_algEquiv (.refl _) e fun g x ↦ ?_
    rw [Subsingleton.elim g 1, MulEquiv.refl_apply, one_smul, one_smul]
  | h_option ih =>
    -- Split off the factor at `none` and use the binary tensor product of torsors.
    have := ih (G := fun i ↦ G (some i)) (B := fun i ↦ B (some i))
    let φ : (∀ i, G i) ≃* (∀ i, G (some i)) × G none :=
      MulEquiv.piOptionEquivProd.trans MulEquiv.prodComm
    refine of_mulEquiv_algEquiv φ (optionAlgEquiv B) fun g x ↦ ?_
    induction x using PiTensorProduct.induction_on with
    | smul_tprod r a => simp [φ, smul_comm _ r]
    | add x y hx hy =>
      rw [smul_add, map_add, map_add, hx, hy]
      -- The goal's action is an `SMulZeroClass` on the tensor product, and neither `rw [smul_add]`
      -- nor unification with the goal can recover the `DistribSMul` instance `smul_add` needs;
      -- naming the tensor product lets instance synthesis find it.
      exact (smul_add (A := (⨂[A] i, B (some i)) ⊗[A] B none) (φ g) _ _).symm

/-- **Finite tensor products of torsors.** If `B i` is a finite étale `G i`-torsor over `A` for
each `i` in a finite type `ι`, then `⨂[A] i, B i` is a finite étale `(∀ i, G i)`-torsor over `A`,
with `∀ i, G i` acting factorwise (`PiTensorProduct.piMulSemiringAction`). The empty tensor
product is `A`, a torsor under the trivial group. -/
instance piTensorProduct {ι : Type u} [Finite ι] {G : ι → Type v} {B : ι → Type w}
    [∀ i, Group (G i)] [∀ i, Finite (G i)] [∀ i, CommRing (B i)] [∀ i, Algebra A (B i)]
    [∀ i, MulSemiringAction (G i) (B i)] [∀ i, SMulCommClass (G i) A (B i)]
    [∀ i, IsFiniteEtaleTorsor (G i) A (B i)] :
    IsFiniteEtaleTorsor (∀ i, G i) A (⨂[A] i, B i) :=
  piTensorProduct_aux ι

section FiberwiseMul

variable {σ τ : Type*} [Fintype σ] [Finite τ] [DecidableEq τ] {G : τ → Type*} {B : τ → Type*}
  [∀ j, Group (G j)] [∀ j, Finite (G j)] [∀ j, CommRing (B j)] [∀ j, Algebra A (B j)]
  [∀ j, MulSemiringAction (G j) (B j)] [∀ j, SMulCommClass (G j) A (B j)]
  [∀ j, IsFiniteEtaleTorsor (G j) A (B j)]

/-- **Transitions between finite tensor products of torsors.** For an injective map `f : σ → τ`
of finite index types, the inclusion of tensor factors `fiberwiseMul f` makes `⨂[A] j, B j` a
finite étale torsor over `⨂[A] i, B (f i)` under the kernel of the restriction
`(∀ j, G j) →* ∀ i, G (f i)`, `g ↦ g ∘ f`: the elements of `∀ j, G j` that are trivial on the
range of `f`. In particular `fiberwiseMul f` is injective and faithfully flat. -/
theorem fiberwiseMul {f : σ → τ} (hf : Function.Injective f) :
    letI := (PiTensorProduct.fiberwiseMul (R := A) (A := B) f).toAlgebra
    haveI := smulCommClass_ker (B := ⨂[A] i, B (f i)) (B' := ⨂[A] j, B j)
      (π := MonoidHom.pi fun i ↦ Pi.evalMonoidHom G (f i))
      fun g x ↦ (fiberwiseMul_piMulSemiringAction_smul f g x).symm
    IsFiniteEtaleTorsor (MonoidHom.pi fun i ↦ Pi.evalMonoidHom G (f i)).ker
      (⨂[A] i, B (f i)) (⨂[A] j, B j) := by
  let := (PiTensorProduct.fiberwiseMul (R := A) (A := B) f).toAlgebra
  have : IsScalarTower A (⨂[A] i, B (f i)) (⨂[A] j, B j) :=
    .of_algebraMap_eq' (PiTensorProduct.fiberwiseMul f).comp_algebraMap.symm
  exact of_surjective (A := A) (MonoidHom.pi_evalMonoidHom_surjective_of_injective hf)
    fun g x ↦ (fiberwiseMul_piMulSemiringAction_smul f g x).symm

variable (G) in
include G in
/-- For an injective map `f : σ → τ` of finite index types, the inclusion of tensor factors
`fiberwiseMul f : ⨂[A] i, B (f i) → ⨂[A] j, B j` between finite tensor products of torsors is
injective. -/
theorem injective_fiberwiseMul {f : σ → τ} (hf : Function.Injective f) :
    Function.Injective (PiTensorProduct.fiberwiseMul (R := A) (A := B) f) :=
  letI := (PiTensorProduct.fiberwiseMul (R := A) (A := B) f).toAlgebra
  haveI := (fiberwiseMul (A := A) (G := G) (B := B) hf).faithfullyFlat
  FaithfulSMul.algebraMap_injective (⨂[A] i, B (f i)) (⨂[A] j, B j)

end FiberwiseMul

end IsFiniteEtaleTorsor

end TauCeti.Algebra
