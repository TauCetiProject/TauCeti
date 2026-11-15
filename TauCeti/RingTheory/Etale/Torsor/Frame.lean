/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.TotallySplit
public import TauCeti.RingTheory.Etale.FiniteEtaleSplit.Basic
public import TauCeti.RingTheory.Etale.Torsor.Descent
public import TauCeti.RingTheory.Unramified.Frame
import Mathlib.Algebra.Algebra.Shrink
import Mathlib.RingTheory.Finiteness.Prod
import Mathlib.RingTheory.Finiteness.Small
import TauCeti.RingTheory.Etale.FiniteEtaleSplit.ConstantRank

/-!
# The frame algebra of a finite étale algebra is a splitting torsor

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

Every finite étale algebra `S` of constant rank `Fintype.card ι` is split as `ι → T` by a
faithfully flat finite étale extension (`TauCeti.Algebra.exists_algEquiv_pi_of_etale`), so its
frame algebra is a finite étale `Perm ι`-torsor
(`TauCeti.Algebra.FrameAlgebra.isFiniteEtaleTorsor`), and the universal frame map over it is an
isomorphism
`FrameAlgebra R S ι ⊗[R] S ≃ₐ[FrameAlgebra R S ι] (ι → FrameAlgebra R S ι)`
(`TauCeti.Algebra.FrameAlgebra.tensorProductEquivPi`). Thus `FrameAlgebra R S ι` is the
ring-theoretic Galois closure of `S`: for a finite separable field extension `L / K` of degree `n`
with Galois closure `M`, it is a product of copies of `M`.

For a general finite étale `A`-algebra `S` whose rank may vary over `Spec A`, padding `S` by a
product of quotients by idempotents yields a constant-rank finite étale algebra
(`TauCeti.Algebra.exists_etale_rankAtStalk_prod_pi_quotient_eq`) having `S` as a direct factor.
Taking the frame algebra of the padded algebra produces a finite étale torsor `P` over `A` such
that `P ⊗[A] S` is totally split over `P`
(`TauCeti.Algebra.exists_isFiniteEtaleTorsor_isTotallySplit`).

## Main definitions

* `TauCeti.Algebra.FrameAlgebra.tensorProductEquivPi`: the universal frame isomorphism
  `FrameAlgebra R S ι ⊗[R] S ≃ₐ[FrameAlgebra R S ι] (ι → FrameAlgebra R S ι)` for a finite étale
  algebra `S` of constant rank `Fintype.card ι`.

## Main results

* `TauCeti.Algebra.FrameAlgebra.isFiniteEtaleTorsor_of_algEquiv_pi`: the frame algebra of an
  algebra split by a faithfully flat extension is a finite étale `Perm ι`-torsor.
* `TauCeti.Algebra.FrameAlgebra.isFiniteEtaleTorsor`: the frame algebra of a finite étale algebra
  of constant rank `Fintype.card ι` is a finite étale `Perm ι`-torsor.
* `TauCeti.Algebra.FrameAlgebra.isFiniteSplit_tensorProduct`,
  `TauCeti.Algebra.FrameAlgebra.isTotallySplit_tensorProduct`: a constant-rank finite étale algebra
  splits over its frame algebra.
* `TauCeti.Algebra.exists_isFiniteEtaleTorsor_isTotallySplit`: every finite étale algebra (of
  possibly varying rank) becomes totally split over a finite étale torsor.

## References

* [Stacks Project, Tag 0BN2](https://stacks.math.columbia.edu/tag/0BN2), for the Galois closure
  of a connected object of a Galois category.
* H. W. Lenstra, *Galois theory for schemes*, Proposition 5.10, for the splitting cover.
* K. S. Kedlaya and R. Liu, *Relative p-adic Hodge theory: foundations*, Remark 1.4.7(c).
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

section ConstantRank

variable {R : Type u} {S : Type*} [CommRing R] [CommRing S] [Algebra R S] [Algebra.Etale R S]
  [Module.Finite R S] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The frame algebra is a torsor.** For a finite étale `R`-algebra `S` of constant rank
`Fintype.card ι`, the frame algebra of `ι`-tuples of pairwise distinct points of `S` is a finite
étale `Perm ι`-torsor over `R`. -/
theorem isFiniteEtaleTorsor (h : Module.rankAtStalk (R := R) S = Fintype.card ι) :
    IsFiniteEtaleTorsor (Equiv.Perm ι) R (FrameAlgebra R S ι) := by
  obtain ⟨T, _, _, _, _, _, ⟨e⟩⟩ :=
    exists_algEquiv_pi_of_etale (Nat.card_eq_fintype_card (α := ι) ▸ h)
  exact isFiniteEtaleTorsor_of_algEquiv_pi T e

/-- **The universal frame of a constant-rank finite étale algebra is bijective.** For a finite
étale `R`-algebra `S` of constant rank `Fintype.card ι`, the universal frame map
`FrameAlgebra R S ι ⊗[R] S →ₐ[FrameAlgebra R S ι] (ι → FrameAlgebra R S ι)` is bijective. -/
theorem bijective_tensorToPi (h : Module.rankAtStalk (R := R) S = Fintype.card ι) :
    Function.Bijective (tensorToPi R S ι) := by
  obtain ⟨T, _, _, _, _, _, ⟨e⟩⟩ :=
    exists_algEquiv_pi_of_etale (Nat.card_eq_fintype_card (α := ι) ▸ h)
  exact bijective_tensorToPi_of_algEquiv_pi T e

/-- **The universal frame isomorphism.** For a finite étale `R`-algebra `S` of constant rank
`Fintype.card ι`, the universal frame map is an isomorphism of `FrameAlgebra R S ι`-algebras
`FrameAlgebra R S ι ⊗[R] S ≃ₐ[FrameAlgebra R S ι] (ι → FrameAlgebra R S ι)`, splitting `S` into
`|ι|` copies of the frame algebra. -/
noncomputable def tensorProductEquivPi (h : Module.rankAtStalk (R := R) S = Fintype.card ι) :
    FrameAlgebra R S ι ⊗[R] S ≃ₐ[FrameAlgebra R S ι] (ι → FrameAlgebra R S ι) :=
  AlgEquiv.ofBijective (tensorToPi R S ι) (bijective_tensorToPi h)

/-- The underlying map of `TauCeti.Algebra.FrameAlgebra.tensorProductEquivPi` is
`TauCeti.Algebra.FrameAlgebra.tensorToPi`. -/
theorem coe_tensorProductEquivPi (h : Module.rankAtStalk (R := R) S = Fintype.card ι) :
    ⇑(tensorProductEquivPi h) = tensorToPi R S ι := (rfl)

/-- `TauCeti.Algebra.FrameAlgebra.tensorProductEquivPi` sends `p ⊗ s` to
`i ↦ p * singleAlgHom R S i s`. -/
@[simp]
theorem tensorProductEquivPi_tmul (h : Module.rankAtStalk (R := R) S = Fintype.card ι)
    (p : FrameAlgebra R S ι) (s : S) (i : ι) :
    tensorProductEquivPi h (p ⊗ₜ s) i = p * singleAlgHom R S i s := by
  simp [coe_tensorProductEquivPi]

/-- A finite étale `R`-algebra `S` of constant rank `Fintype.card ι` becomes finite split after
base change to its frame algebra `FrameAlgebra R S ι`. -/
theorem isFiniteSplit_tensorProduct (h : Module.rankAtStalk (R := R) S = Fintype.card ι) :
    Algebra.IsFiniteSplit (FrameAlgebra R S ι) (FrameAlgebra R S ι ⊗[R] S) :=
  .of_algEquiv (tensorProductEquivPi h).symm

/-- A finite étale `R`-algebra `S` of constant rank `Fintype.card ι` becomes totally split after
base change to its frame algebra `FrameAlgebra R S ι`. -/
theorem isTotallySplit_tensorProduct (h : Module.rankAtStalk (R := R) S = Fintype.card ι) :
    IsTotallySplit (FrameAlgebra R S ι) (FrameAlgebra R S ι ⊗[R] S) := by
  have := isFiniteSplit_tensorProduct h
  exact .of_isFiniteSplit

end ConstantRank

end FrameAlgebra

/-- **Every finite étale algebra is split by a finite étale torsor.** For every finite étale
`A`-algebra `S` (whose rank on `Spec A` need not be constant), there are a finite group `G` and a
finite étale `G`-torsor `P` over `A`, both in the universe of `A`, such that `P ⊗[A] S` is totally
split over `P`. -/
theorem exists_isFiniteEtaleTorsor_isTotallySplit (A : Type u) (S : Type*) [CommRing A]
    [CommRing S] [Algebra A S] [Algebra.Etale A S] [Module.Finite A S] :
    ∃ (G : Type u) (_ : Group G) (_ : Finite G) (P : Type u) (_ : CommRing P)
      (_ : Algebra A P) (_ : MulSemiringAction G P) (_ : SMulCommClass G A P),
      IsFiniteEtaleTorsor G A P ∧ IsTotallySplit P (P ⊗[A] S) := by
  have : Small.{u} S := Module.Finite.small A S
  let e₀ : Shrink.{u} S ≃ₐ[A] S := Shrink.algEquiv A S
  have : Algebra.Etale A (Shrink.{u} S) := .of_equiv e₀.symm
  have : Module.Finite A (Shrink.{u} S) := .equiv e₀.symm.toLinearEquiv
  -- Pad `Shrink.{u} S` to a finite étale `A`-algebra `B` of constant rank `n`, and split `B` by
  -- its frame algebra `FrameAlgebra A B (ULift (Fin n))`.
  obtain ⟨n, e, -, _, hrank⟩ := exists_etale_rankAtStalk_prod_pi_quotient_eq A (Shrink.{u} S)
  let B : Type u := Shrink.{u} S × Π j : Fin n, A ⧸ Ideal.span {1 - e j}
  have ⟨G, _, _, P, _, _, _, _, hP, hsplit⟩ :
      ∃ (G : Type u) (_ : Group G) (_ : Finite G) (P : Type u) (_ : CommRing P)
        (_ : Algebra A P) (_ : MulSemiringAction G P) (_ : SMulCommClass G A P),
        IsFiniteEtaleTorsor G A P ∧ IsTotallySplit P (P ⊗[A] B) := by
    let ι : Type u := ULift.{u} (Fin n)
    have h' : Module.rankAtStalk (R := A) B = Fintype.card ι := by
      rw [hrank, Fintype.card_ulift (Fin n), Fintype.card_fin]
    exact ⟨Equiv.Perm ι, inferInstance, inferInstance, FrameAlgebra A B ι, inferInstance,
      inferInstance, inferInstance, inferInstance, FrameAlgebra.isFiniteEtaleTorsor h',
      FrameAlgebra.isTotallySplit_tensorProduct h'⟩
  exact ⟨G, _, _, P, _, _, _, _, hP, ((hsplit.of_algEquiv
    (Algebra.TensorProduct.prodRight A P P (Shrink.{u} S) _)).of_prod_fst).of_algEquiv
    (Algebra.TensorProduct.congr AlgEquiv.refl e₀)⟩

end TauCeti.Algebra
