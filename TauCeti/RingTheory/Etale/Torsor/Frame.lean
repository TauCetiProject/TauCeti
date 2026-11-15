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

Every finite étale algebra `S` of constant rank `Fintype.card ι` is split by a faithfully flat
finite étale extension (Mathlib's `Algebra.IsFiniteSplit.exists_tensorProduct_of_etale`), so its
frame algebra is a finite étale `Perm ι`-torsor
(`TauCeti.Algebra.FrameAlgebra.isFiniteEtaleTorsor`). It is the ring-theoretic Galois closure of
`S`: for a finite separable field extension `L / K` of degree `n` with Galois closure `M`, it is a
product of copies of `M`. The splitting cover is stated for `S` in the universe of `R`. A finite
algebra is isomorphic to one in that universe (`Shrink`), and the frame algebra is invariant under
isomorphisms (`TauCeti.Algebra.FrameAlgebra.congr`), so the result holds for `S` in any universe.

## Main results

* `TauCeti.Algebra.FrameAlgebra.isFiniteEtaleTorsor_of_algEquiv_pi`: the frame algebra of an
  algebra split by a faithfully flat extension is a finite étale `Perm ι`-torsor.
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

namespace TauCeti.Algebra

namespace FrameAlgebra

section LocallySplit

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

end LocallySplit

/-- `TauCeti.Algebra.FrameAlgebra.isFiniteEtaleTorsor` for `R` and `S` in the same universe, in
which Mathlib's splitting cover `Algebra.IsFiniteSplit.exists_tensorProduct_of_etale` applies. -/
private theorem isFiniteEtaleTorsor_aux {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.Etale R S] [Module.Finite R S] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (h : Module.rankAtStalk (R := R) S = Fintype.card ι) :
    IsFiniteEtaleTorsor (Equiv.Perm ι) R (FrameAlgebra R S ι) := by
  cases subsingleton_or_nontrivial R
  · infer_instance
  obtain ⟨T, _, _, _, _, _, hT⟩ := Algebra.IsFiniteSplit.exists_tensorProduct_of_etale h
  obtain ⟨m, ⟨f⟩⟩ := Algebra.IsFiniteSplit.nonempty_algEquiv_fun T (T ⊗[R] S)
  have : Nontrivial T := (FaithfulSMul.algebraMap_injective R T).nontrivial
  obtain rfl : m = Fintype.card ι := by
    simpa using f.toLinearEquiv.finrank_eq.symm.trans
      (TauCeti.Module.finrank_tensorProduct_eq_of_rankAtStalk_eq h)
  exact isFiniteEtaleTorsor_of_algEquiv_pi T
    (f.trans (AlgEquiv.piCongrLeft' T (fun _ ↦ T) (Fintype.equivFin ι).symm))

/-- **The frame algebra is a torsor.** For a finite étale `R`-algebra `S` of constant rank
`Fintype.card ι`, the frame algebra of `ι`-tuples of pairwise distinct points of `S` is a finite
étale `Perm ι`-torsor over `R`. -/
theorem isFiniteEtaleTorsor {R : Type u} {S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.Etale R S] [Module.Finite R S] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (h : Module.rankAtStalk (R := R) S = Fintype.card ι) :
    IsFiniteEtaleTorsor (Equiv.Perm ι) R (FrameAlgebra R S ι) := by
  -- The finite algebra `S` is isomorphic to an algebra in the universe of `R`, and the frame
  -- algebra is invariant under isomorphisms.
  have : Small.{u} S := Module.Finite.small R S
  let e : Shrink.{u} S ≃ₐ[R] S := Shrink.algEquiv R S
  have : Algebra.Etale R (Shrink.{u} S) := .of_equiv e.symm
  have : Module.Finite R (Shrink.{u} S) := .equiv e.symm.toLinearEquiv
  have := isFiniteEtaleTorsor_aux (ι := ι)
    ((Module.rankAtStalk_eq_of_equiv e.toLinearEquiv).trans h)
  exact .of_algEquiv (FrameAlgebra.congr ι e) (FrameAlgebra.congr_smul e)

end FrameAlgebra

end TauCeti.Algebra
