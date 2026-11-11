/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Etale.Torsor.Descent
public import TauCeti.RingTheory.Unramified.Frame
import TauCeti.RingTheory.Spectrum.Prime.FreeLocus
import Mathlib.RingTheory.TotallySplit

/-!
# The frame algebra of a finite étale algebra is a torsor

Let `S` be a finite étale `R`-algebra of constant rank `n` and `ι` a type with `n` elements. The
frame algebra `TauCeti.Algebra.FrameAlgebra R S ι`, the ring of functions on the `ι`-tuples of
pairwise distinct points of `Spec S` over `Spec R`, is a finite étale `Perm ι`-torsor over `R`
(`TauCeti.Algebra.FrameAlgebra.isFiniteEtaleTorsor`). It is the ring-theoretic Galois closure of
`S`: for a finite separable field extension `L / K` of degree `n` with Galois closure `M`, it is a
product of copies of `M`.

The proof is faithfully flat descent. After a faithfully flat finite étale base change `R → T`
the algebra splits, `T ⊗[R] S ≃ₐ[T] (ι → T)` (Mathlib's
`Algebra.IsFiniteSplit.exists_tensorProduct_of_etale`). The frame algebra commutes with base change
(`TauCeti.Algebra.FrameAlgebra.baseChangeEquiv`), and the frame algebra of the split algebra
`ι → T` is the trivial torsor `Perm ι → T` (`TauCeti.Algebra.FrameAlgebra.permEquiv`). Both
identifications are equivariant, so `TauCeti.Algebra.IsFiniteEtaleTorsor.of_baseChange_algEquiv_pi`
applies.

## Main results

* `TauCeti.Algebra.FrameAlgebra.isFiniteEtaleTorsor`: the frame algebra of a finite étale algebra
  of constant rank `Fintype.card ι` is a finite étale `Perm ι`-torsor.

## References

* [Stacks Project, Tag 0BN2](https://stacks.math.columbia.edu/tag/0BN2), for the Galois closure
  of a connected object of a Galois category.
* H. W. Lenstra, *Galois theory for schemes*, Proposition 5.10, for the splitting cover.
* P. Scholze, *Étale cohomology of diamonds*, proof of Lemma 15.3.
-/

public section

open scoped TensorProduct

universe u

namespace TauCeti.Algebra.FrameAlgebra

attribute [local instance] Algebra.TensorProduct.rightMulSemiringAction

/-- **The frame algebra is a torsor.** For a finite étale `R`-algebra `S` of constant rank
`Fintype.card ι`, the frame algebra of `ι`-tuples of pairwise distinct points of `S` is a finite
étale `Perm ι`-torsor over `R`. -/
theorem isFiniteEtaleTorsor {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.Etale R S] [Module.Finite R S] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (h : Module.rankAtStalk (R := R) S = Fintype.card ι) :
    IsFiniteEtaleTorsor (Equiv.Perm ι) R (FrameAlgebra R S ι) := by
  cases subsingleton_or_nontrivial R
  · infer_instance
  obtain ⟨T, _, _, _, _, _, hT⟩ := Algebra.IsFiniteSplit.exists_tensorProduct_of_etale h
  obtain ⟨m, ⟨f⟩⟩ := Algebra.IsFiniteSplit.nonempty_algEquiv_fun T (T ⊗[R] S)
  have : Nontrivial T := (FaithfulSMul.algebraMap_injective R T).nontrivial
  obtain rfl : m = Fintype.card ι := by
    simpa using TauCeti.Module.card_eq_of_rankAtStalk_eq_of_linearEquiv h f.toLinearEquiv
  -- Over `T`, the frame algebra is that of the split algebra `ι → T`, the trivial torsor.
  let g : T ⊗[R] S ≃ₐ[T] (ι → T) :=
    f.trans (AlgEquiv.piCongrLeft' T (fun _ ↦ T) (Fintype.equivFin ι).symm)
  refine .of_baseChange_algEquiv_pi T
    ((baseChangeEquiv R S ι T).trans ((FrameAlgebra.congr ι g).trans (permEquiv T ι)))
    fun σ x τ ↦ ?_
  rw [AlgEquiv.trans_apply, AlgEquiv.trans_apply, baseChangeEquiv_smul, congr_smul, permEquiv_smul,
    AlgEquiv.trans_apply, AlgEquiv.trans_apply]

end TauCeti.Algebra.FrameAlgebra
