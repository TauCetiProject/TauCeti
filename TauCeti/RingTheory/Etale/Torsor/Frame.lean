/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Etale.Torsor.Descent
public import TauCeti.RingTheory.Unramified.Frame

/-!
# The frame algebra of a locally split algebra is a torsor

Let `S` be an `R`-algebra which becomes split of rank `|ι|` after a faithfully flat extension
`R → T`, that is `T ⊗[R] S ≃ₐ[T] (ι → T)`. Then the frame algebra
`TauCeti.Algebra.FrameAlgebra R S ι` of `ι`-tuples of pairwise distinct points of `Spec S` is a
finite étale `Equiv.Perm ι`-torsor over `R`
(`TauCeti.Algebra.FrameAlgebra.isFiniteEtaleTorsor_of_algEquiv_pi`).

Indeed, forming frame algebras commutes with base change
(`TauCeti.Algebra.FrameAlgebra.baseChangeEquiv`), so `T ⊗[R] FrameAlgebra R S ι` is the frame
algebra of the split algebra `ι → T`, which is the trivial torsor `Equiv.Perm ι → T`
(`TauCeti.Algebra.FrameAlgebra.permEquiv`); being a torsor descends along faithfully flat
extensions (`TauCeti.Algebra.IsFiniteEtaleTorsor.of_baseChange_algEquiv_pi`).

For `S` finite étale of constant rank `n` and `ι = Fin n`, this is the ring-theoretic Galois
closure of `S`: a finite étale `Perm (Fin n)`-torsor, as soon as `S` is split by a faithfully flat
extension of the base.

## References

* [Stacks Project, Tag 0BN2](https://stacks.math.columbia.edu/tag/0BN2), for the Galois closure
  of a connected object of a Galois category.
* P. Scholze, *Étale cohomology of diamonds*, proof of Lemma 15.3.
-/

public section

open scoped TensorProduct

namespace TauCeti.Algebra

namespace FrameAlgebra

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] [Algebra.EssFiniteType R S]
  [Algebra.FormallyUnramified R S] {ι : Type*} [Fintype ι] [DecidableEq ι]

attribute [local instance] Algebra.TensorProduct.rightMulSemiringAction in
/-- **The frame algebra of a locally split algebra is a torsor.** If `S` becomes isomorphic to the
split algebra `ι → T` after a faithfully flat extension `R → T`, then the frame algebra of
`ι`-tuples of pairwise distinct points of `Spec S` is a finite étale `Equiv.Perm ι`-torsor
over `R`. -/
theorem isFiniteEtaleTorsor_of_algEquiv_pi (T : Type*) [CommRing T] [Algebra R T]
    [Module.FaithfullyFlat R T] (e : T ⊗[R] S ≃ₐ[T] (ι → T)) :
    IsFiniteEtaleTorsor (Equiv.Perm ι) R (FrameAlgebra R S ι) :=
  IsFiniteEtaleTorsor.of_baseChange_algEquiv_pi T
    (((baseChangeEquiv R S T ι).trans (congr ι e)).trans (permEquiv T ι)) fun σ x τ ↦ by
      have hσ : MulSemiringAction.toAlgHom R (FrameAlgebra R S ι) σ =
          (permAlgEquiv R S ι σ).toAlgHom :=
        AlgHom.ext (smul_def σ)
      simp only [AlgEquiv.trans_apply, Algebra.TensorProduct.rightMulSemiringAction_smul_def, hσ,
        baseChangeEquiv_map_permAlgEquiv, congr_smul, permEquiv_smul]

end FrameAlgebra

end TauCeti.Algebra
