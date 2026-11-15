/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Etale.FiniteEtaleSplit.ConstantRank
public import TauCeti.RingTheory.Etale.Torsor.Descent
public import TauCeti.RingTheory.Unramified.Frame
import Mathlib.Algebra.Algebra.Shrink
import Mathlib.Data.Fintype.EquivFin
import Mathlib.RingTheory.Finiteness.Prod
import Mathlib.RingTheory.Finiteness.Small

/-!
# Splitting finite étale algebras by frame torsors

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
finite étale extension (`TauCeti.Algebra.exists_faithfullyFlat_etale_algEquiv_pi`), so its frame
algebra is a finite étale `Perm ι`-torsor (`TauCeti.Algebra.FrameAlgebra.isFiniteEtaleTorsor`), and
the universal frame identifies `FrameAlgebra R S ι ⊗[R] S` with `ι → FrameAlgebra R S ι`
(`TauCeti.Algebra.FrameAlgebra.universalFrameEquiv`). This is the ring-theoretic Galois closure of
`S`: for a finite separable field extension `L / K` of degree `n` with Galois closure `M`, it is a
product of copies of `M`.

For a general finite étale `A`-algebra `S` whose stalk rank varies across clopen components of
`Spec A`, shrinking `S` to the universe of `A` and padding by idempotent quotients
`∏_{j < n} A ⧸ (1 - e j)` embeds `S` as a direct factor of a finite étale `A`-algebra `S'` of
constant rank `n` (`TauCeti.Algebra.exists_etale_rankAtStalk_prod_pi_quotient_eq`). Base change to
the `Perm (Fin n)`-torsor `FrameAlgebra A S' (Fin n)` splits `S'` into `n` copies of the torsor and
hence makes its direct factor `S` totally split (`TauCeti.Algebra.IsTotallySplit`). Reindexing the
slots by `ULift.{u} (Fin n)` places both the group and the torsor in the universe of `A`, as needed
to assemble directed towers of finite étale torsors over `A`.

## Main results

* `TauCeti.Algebra.FrameAlgebra.isFiniteEtaleTorsor_of_algEquiv_pi`: the frame algebra of an
  algebra split by a faithfully flat extension is a finite étale `Perm ι`-torsor.
* `TauCeti.Algebra.FrameAlgebra.isFiniteEtaleTorsor`: the frame algebra of a finite étale algebra
  of constant rank `Fintype.card ι` is a finite étale `Perm ι`-torsor.
* `TauCeti.Algebra.FrameAlgebra.universalFrameEquiv`: the universal frame splits a finite étale
  algebra of constant rank `Fintype.card ι` into `ι → FrameAlgebra R S ι`.
* `TauCeti.Algebra.exists_perm_isFiniteEtaleTorsor_isTotallySplit`: every finite étale `A`-algebra
  becomes totally split over a finite étale `Perm (Fin n)`-torsor over `A`.
* `TauCeti.Algebra.exists_isFiniteEtaleTorsor_isTotallySplit`: every finite étale `A`-algebra
  becomes totally split over a finite étale `G`-torsor `P` over `A`, with `G` and `P` in the
  universe of `A`.

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
  obtain ⟨T, _, _, _, _, _, ⟨e⟩⟩ := exists_faithfullyFlat_etale_algEquiv_pi h
  exact isFiniteEtaleTorsor_of_algEquiv_pi T e

/-- **The universal frame of a constant-rank finite étale algebra is bijective.** For a finite
étale `R`-algebra `S` of constant stalk rank `Fintype.card ι`, the universal frame
`FrameAlgebra R S ι ⊗[R] S →ₐ[FrameAlgebra R S ι] (ι → FrameAlgebra R S ι)` is bijective. -/
theorem bijective_universalFrame (h : Module.rankAtStalk (R := R) S = Fintype.card ι) :
    Function.Bijective (universalFrame R S ι) := by
  obtain ⟨T, _, _, _, _, _, ⟨e⟩⟩ := exists_faithfullyFlat_etale_algEquiv_pi h
  exact bijective_universalFrame_of_algEquiv_pi T e

/-- **The universal frame splits a constant-rank finite étale algebra.** Base change to
`FrameAlgebra R S ι` identifies a finite étale `R`-algebra `S` of constant rank `Fintype.card ι`
with `ι → FrameAlgebra R S ι` via the universal frame. -/
noncomputable def universalFrameEquiv (h : Module.rankAtStalk (R := R) S = Fintype.card ι) :
    FrameAlgebra R S ι ⊗[R] S ≃ₐ[FrameAlgebra R S ι] (ι → FrameAlgebra R S ι) :=
  AlgEquiv.ofBijective (universalFrame R S ι) (bijective_universalFrame h)

/-- The underlying function of `TauCeti.Algebra.FrameAlgebra.universalFrameEquiv` is
`TauCeti.Algebra.FrameAlgebra.universalFrame`. -/
theorem coe_universalFrameEquiv (h : Module.rankAtStalk (R := R) S = Fintype.card ι) :
    ⇑(universalFrameEquiv h) = universalFrame R S ι := (rfl)

/-- `TauCeti.Algebra.FrameAlgebra.universalFrameEquiv` sends `p ⊗ s` at slot `i` to
`p * slot R S i s`. -/
@[simp]
theorem universalFrameEquiv_tmul (h : Module.rankAtStalk (R := R) S = Fintype.card ι)
    (p : FrameAlgebra R S ι) (s : S) (i : ι) :
    universalFrameEquiv h (p ⊗ₜ s) i = p * slot R S i s :=
  universalFrame_tmul p s i

/-- Base change to `TauCeti.Algebra.FrameAlgebra R S ι` makes a finite étale `R`-algebra `S` of
constant rank `Fintype.card ι` split in the sense of `Algebra.IsFiniteSplit`. -/
theorem isFiniteSplit_tensorProduct (h : Module.rankAtStalk (R := R) S = Fintype.card ι) :
    Algebra.IsFiniteSplit (FrameAlgebra R S ι) (FrameAlgebra R S ι ⊗[R] S) :=
  ⟨Fintype.card ι, ⟨(universalFrameEquiv h).trans
    (AlgEquiv.piCongrLeft' (FrameAlgebra R S ι) (fun _ ↦ FrameAlgebra R S ι)
      (Fintype.equivFin ι))⟩⟩

/-- Base change to `TauCeti.Algebra.FrameAlgebra R S ι` makes a finite étale `R`-algebra `S` of
constant rank `Fintype.card ι` totally split. -/
theorem isTotallySplit_tensorProduct (h : Module.rankAtStalk (R := R) S = Fintype.card ι) :
    IsTotallySplit (FrameAlgebra R S ι) (FrameAlgebra R S ι ⊗[R] S) :=
  have := isFiniteSplit_tensorProduct h
  .of_isFiniteSplit

end ConstantRank

end FrameAlgebra

/-- For a finite étale `A`-algebra `S' : Type u` of constant stalk rank `Fintype.card ι`, its frame
algebra provides an `Equiv.Perm ι`-torsor `P` over `A` over which `S'` becomes totally split.
Packaging `P` existentially here keeps `FrameAlgebra` opaque in downstream tensor-product
manipulations. -/
private theorem exists_isFiniteEtaleTorsor_isTotallySplit_of_rankAtStalk_eq.{v}
    {A S' : Type u} [CommRing A] [CommRing S'] [Algebra A S'] [Algebra.Etale A S']
    [Module.Finite A S'] (ι : Type v) [Fintype ι]
    (h : Module.rankAtStalk (R := A) S' = Fintype.card ι) :
    ∃ (P : Type (max u v)) (_ : CommRing P) (_ : Algebra A P)
      (_ : MulSemiringAction (Equiv.Perm ι) P) (_ : SMulCommClass (Equiv.Perm ι) A P),
      IsFiniteEtaleTorsor (Equiv.Perm ι) A P ∧ IsTotallySplit P (P ⊗[A] S') := by
  classical
  exact ⟨FrameAlgebra A S' ι, inferInstance, inferInstance, inferInstance, inferInstance,
    FrameAlgebra.isFiniteEtaleTorsor h, FrameAlgebra.isTotallySplit_tensorProduct h⟩

/-- Auxiliary construction for `exists_perm_isFiniteEtaleTorsor_isTotallySplit` and
`exists_isFiniteEtaleTorsor_isTotallySplit`, parametrized by the family `ι` of finite slot index
types of each cardinality `n`. -/
private theorem exists_isFiniteEtaleTorsor_isTotallySplit_aux.{v}
    (A : Type u) (S : Type*) [CommRing A] [CommRing S] [Algebra A S] [Algebra.Etale A S]
    [Module.Finite A S] (ι : ℕ → Type v) [∀ n, Fintype (ι n)]
    (hcard : ∀ n, Fintype.card (ι n) = n) :
    ∃ (n : ℕ) (P : Type (max u v)) (_ : CommRing P) (_ : Algebra A P)
      (_ : MulSemiringAction (Equiv.Perm (ι n)) P)
      (_ : SMulCommClass (Equiv.Perm (ι n)) A P),
      IsFiniteEtaleTorsor (Equiv.Perm (ι n)) A P ∧ IsTotallySplit P (P ⊗[A] S) := by
  have : Small.{u} S := Module.Finite.small A S
  let eS : Shrink.{u} S ≃ₐ[A] S := Shrink.algEquiv A S
  have : Algebra.Etale A (Shrink.{u} S) := .of_equiv eS.symm
  have : Module.Finite A (Shrink.{u} S) := .equiv eS.symm.toLinearEquiv
  obtain ⟨n, e, -, _, hrank⟩ := exists_etale_rankAtStalk_prod_pi_quotient_eq A (Shrink.{u} S)
  obtain ⟨P, _, _, _, _, htor, hsplit⟩ :=
    exists_isFiniteEtaleTorsor_isTotallySplit_of_rankAtStalk_eq
      (S' := Shrink.{u} S × Π j : Fin n, A ⧸ Ideal.span {1 - e j}) (ι n)
      (by simpa [hcard n] using hrank)
  have hS₀ : IsTotallySplit P (P ⊗[A] Shrink.{u} S) :=
    (hsplit.of_algEquiv (Algebra.TensorProduct.prodRight A P P _ _)).of_prod_fst
  exact ⟨n, P, inferInstance, inferInstance, inferInstance, inferInstance, htor,
    hS₀.of_algEquiv (Algebra.TensorProduct.congr AlgEquiv.refl eS)⟩

/-- **Every finite étale algebra is split by a symmetric-group torsor.** For any commutative ring
`A : Type u` and finite étale `A`-algebra `S` (in any universe, of possibly varying rank), there
exist `n : ℕ` and a finite étale `Equiv.Perm (Fin n)`-torsor `P : Type u` over `A` such that
`P ⊗[A] S` is totally split over `P`. -/
theorem exists_perm_isFiniteEtaleTorsor_isTotallySplit (A : Type u) (S : Type*) [CommRing A]
    [CommRing S] [Algebra A S] [Algebra.Etale A S] [Module.Finite A S] :
    ∃ (n : ℕ) (P : Type u) (_ : CommRing P) (_ : Algebra A P)
      (_ : MulSemiringAction (Equiv.Perm (Fin n)) P)
      (_ : SMulCommClass (Equiv.Perm (Fin n)) A P),
      IsFiniteEtaleTorsor (Equiv.Perm (Fin n)) A P ∧ IsTotallySplit P (P ⊗[A] S) :=
  exists_isFiniteEtaleTorsor_isTotallySplit_aux A S Fin Fintype.card_fin

/-- **Every finite étale algebra is split by a finite étale torsor.** For any commutative ring
`A : Type u` and finite étale `A`-algebra `S` (in any universe, of possibly varying rank), there
exist a finite group `G : Type u` and a finite étale `G`-torsor `P : Type u` over `A` such that
`P ⊗[A] S` is totally split over `P`. Both `G` and `P` live in the universe of `A`. -/
theorem exists_isFiniteEtaleTorsor_isTotallySplit (A : Type u) (S : Type*) [CommRing A]
    [CommRing S] [Algebra A S] [Algebra.Etale A S] [Module.Finite A S] :
    ∃ (G : Type u) (_ : Group G) (_ : Finite G) (P : Type u) (_ : CommRing P)
      (_ : Algebra A P) (_ : MulSemiringAction G P) (_ : SMulCommClass G A P),
      IsFiniteEtaleTorsor G A P ∧ IsTotallySplit P (P ⊗[A] S) := by
  obtain ⟨n, P, _, _, _, _, htor, hsplit⟩ :=
    exists_isFiniteEtaleTorsor_isTotallySplit_aux A S
      (fun m ↦ ULift.{u} (Fin m)) fun m ↦ (Fintype.card_ulift (Fin m)).trans (Fintype.card_fin m)
  exact ⟨Equiv.Perm (ULift.{u} (Fin n)), inferInstance, inferInstance, P, inferInstance,
    inferInstance, inferInstance, inferInstance, htor, hsplit⟩

end TauCeti.Algebra
