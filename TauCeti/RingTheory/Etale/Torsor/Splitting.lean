/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Etale.Torsor.Frame
import Mathlib.Algebra.Algebra.Shrink
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Finiteness.Prod
import Mathlib.RingTheory.Finiteness.Small
import TauCeti.RingTheory.Etale.FiniteEtaleSplit.ConstantRank

/-!
# Splitting every finite étale algebra by a finite étale torsor

Every finite étale algebra `S` over a commutative ring `A` becomes totally split after base change
to some finite étale torsor `P` over `A` under a finite symmetric group
(`TauCeti.Algebra.exists_isFiniteEtaleTorsor_isTotallySplit`,
`TauCeti.Algebra.exists_perm_isFiniteEtaleTorsor_isTotallySplit`). No connectedness, Noetherianity,
or nontriviality hypothesis on `A` is assumed, and the rank of `S` may vary across clopen subsets
of `Spec A`.

The construction combines two steps:
1. Padding to constant rank (`TauCeti.Algebra.exists_etale_rankAtStalk_prod_pi_quotient_eq`):
   after shrinking `S` to the universe of `A`, `S` is a direct factor of a finite étale
   `A`-algebra `S' = S_0 × ∏_{j < n} A ⧸ (1 - e j)` of constant stalk rank `n`.
2. Frame torsor of a constant-rank cover (`TauCeti.Algebra.FrameAlgebra.isFiniteEtaleTorsor`,
   `TauCeti.Algebra.FrameAlgebra.isTotallySplit_tensorProduct`): for any finite index type `ι` of
   cardinality `n`, the frame algebra `P = FrameAlgebra A S' ι` is a finite étale `Perm ι`-torsor
   over `A` such that `P ⊗[A] S' ≃ₐ[P] (ι → P)`. Keeping the first factor of
   `P ⊗[A] S' ≃ (P ⊗[A] S) × ⋯` shows that `P ⊗[A] S` is totally split over `P`.

Taking `ι = Fin n` exhibits the splitting group explicitly as `Equiv.Perm (Fin n)`, while taking
`ι = ULift.{u} (Fin n)` places both `G` and `P` in the universe `Type u` of `A`. When `Spec A` is
preconnected, the stalk rank of `S` is already constant, so `FrameAlgebra` splits `P ⊗[A] S` into
a constant-rank product (`Algebra.IsFiniteSplit`) without padding
(`TauCeti.Algebra.exists_isFiniteEtaleTorsor_isFiniteSplit`).

## Main results

* `TauCeti.Algebra.exists_perm_isFiniteEtaleTorsor_isTotallySplit`: every finite étale `A`-algebra
  is totally split by a finite étale `Equiv.Perm (Fin n)`-torsor over `A`.
* `TauCeti.Algebra.exists_isFiniteEtaleTorsor_isTotallySplit`: every finite étale `A`-algebra is
  totally split by a finite étale `G`-torsor `P` over `A`, with `G, P : Type u`.
* `TauCeti.Algebra.exists_perm_isFiniteEtaleTorsor_isFiniteSplit`,
  `TauCeti.Algebra.exists_isFiniteEtaleTorsor_isFiniteSplit`: over a ring with preconnected prime
  spectrum, the base change `P ⊗[A] S` has constant split rank (`Algebra.IsFiniteSplit`).

## References

* [Stacks Project, Tag 0BN2](https://stacks.math.columbia.edu/tag/0BN2).
* H. W. Lenstra, *Galois theory for schemes*, Proposition 5.10.
* K. S. Kedlaya and R. Liu, *Relative p-adic Hodge theory: foundations*, Remark 1.4.7(c).
* P. Scholze, *Étale cohomology of diamonds*, proof of Lemma 15.3.
-/

public section

open scoped TensorProduct

universe u v

namespace TauCeti.Algebra

/-- If `S'` is isomorphic to `S × B` over `A` and `P ⊗[A] S'` is totally split over `P`, then
`P ⊗[A] S` is totally split over `P`. -/
private theorem isTotallySplit_of_prod {A P S' S B : Type*} [CommRing A] [CommRing P]
    [Algebra A P] [CommRing S'] [Algebra A S'] [CommRing S] [Algebra A S]
    [CommRing B] [Algebra A B] (e : S' ≃ₐ[A] S × B) (h : IsTotallySplit P (P ⊗[A] S')) :
    IsTotallySplit P (P ⊗[A] S) :=
  ((h.of_algEquiv (Algebra.TensorProduct.congr (AlgEquiv.refl : P ≃ₐ[P] P) e)).of_algEquiv
    (Algebra.TensorProduct.prodRight A P P S B)).of_prod_fst

/-- An `A`-algebra isomorphism `S₀ ≃ₐ[A] S` transfers `Algebra.IsFiniteSplit P (P ⊗[A] S₀)` to
`Algebra.IsFiniteSplit P (P ⊗[A] S)`. -/
private theorem isFiniteSplit_of_algEquiv_right {A P S₀ S : Type*} [CommRing A] [CommRing P]
    [Algebra A P] [CommRing S₀] [Algebra A S₀] [CommRing S] [Algebra A S] (e : S₀ ≃ₐ[A] S)
    [Algebra.IsFiniteSplit P (P ⊗[A] S₀)] :
    Algebra.IsFiniteSplit P (P ⊗[A] S) :=
  .of_algEquiv (Algebra.TensorProduct.congr (AlgEquiv.refl : P ≃ₐ[P] P) e)

/-- Core padding-and-frame construction splitting a finite étale `A`-algebra by a symmetric-group
frame torsor, parameterized by an index family `ι` with `|ι n| = n`. -/
private theorem exists_perm_family_isFiniteEtaleTorsor_isTotallySplit (A : Type u) (S : Type*)
    [CommRing A] [CommRing S] [Algebra A S] [Algebra.Etale A S] [Module.Finite A S]
    (ι : ℕ → Type v) [∀ n, Fintype (ι n)] (hι : ∀ n, Fintype.card (ι n) = n) :
    ∃ (n : ℕ) (P : Type (max u v)) (_ : CommRing P) (_ : Algebra A P)
      (_ : MulSemiringAction (Equiv.Perm (ι n)) P)
      (_ : SMulCommClass (Equiv.Perm (ι n)) A P),
      IsFiniteEtaleTorsor (Equiv.Perm (ι n)) A P ∧ IsTotallySplit P (P ⊗[A] S) := by
  classical
  have : Small.{u} S := Module.Finite.small A S
  let eS : Shrink.{u} S ≃ₐ[A] S := Shrink.algEquiv A S
  have : Algebra.Etale A (Shrink.{u} S) := .of_equiv eS.symm
  have : Module.Finite A (Shrink.{u} S) := .equiv eS.symm.toLinearEquiv
  obtain ⟨n, e, -, _, hrank⟩ := exists_etale_rankAtStalk_prod_pi_quotient_eq A (Shrink.{u} S)
  let B : Type u := Π j : Fin n, A ⧸ Ideal.span {1 - e j}
  let S' : Type u := Shrink.{u} S × B
  have hrank' : Module.rankAtStalk (R := A) S' = Fintype.card (ι n) := by
    simpa [S', B, hι n] using hrank
  refine ⟨n, FrameAlgebra A S' (ι n), inferInstance, inferInstance, inferInstance,
    inferInstance, FrameAlgebra.isFiniteEtaleTorsor hrank',
    isTotallySplit_of_prod (eS.prodCongr AlgEquiv.refl)
      (FrameAlgebra.isTotallySplit_tensorProduct hrank')⟩

/-- **Splitting a finite étale algebra by a symmetric-group torsor.** Every finite étale
`A`-algebra `S` becomes totally split after base change to a finite étale
`Equiv.Perm (Fin n)`-torsor `P : Type u` over `A`. -/
theorem exists_perm_isFiniteEtaleTorsor_isTotallySplit (A : Type u) (S : Type*) [CommRing A]
    [CommRing S] [Algebra A S] [Algebra.Etale A S] [Module.Finite A S] :
    ∃ (n : ℕ) (P : Type u) (_ : CommRing P) (_ : Algebra A P)
      (_ : MulSemiringAction (Equiv.Perm (Fin n)) P)
      (_ : SMulCommClass (Equiv.Perm (Fin n)) A P),
      IsFiniteEtaleTorsor (Equiv.Perm (Fin n)) A P ∧ IsTotallySplit P (P ⊗[A] S) :=
  exists_perm_family_isFiniteEtaleTorsor_isTotallySplit A S Fin Fintype.card_fin

/-- **Every finite étale algebra is split by a finite étale torsor.** For every commutative ring
`A : Type u` and every finite étale `A`-algebra `S`, there exist a finite group `G : Type u` and a
finite étale `G`-torsor `P : Type u` over `A` such that `P ⊗[A] S` is totally split over `P`. -/
theorem exists_isFiniteEtaleTorsor_isTotallySplit (A : Type u) (S : Type*) [CommRing A]
    [CommRing S] [Algebra A S] [Algebra.Etale A S] [Module.Finite A S] :
    ∃ (G : Type u) (_ : Group G) (_ : Finite G) (P : Type u) (_ : CommRing P)
      (_ : Algebra A P) (_ : MulSemiringAction G P) (_ : SMulCommClass G A P),
      IsFiniteEtaleTorsor G A P ∧ IsTotallySplit P (P ⊗[A] S) := by
  obtain ⟨n, P, _, _, _, _, htor, hsplit⟩ :=
    exists_perm_family_isFiniteEtaleTorsor_isTotallySplit A S (fun n ↦ ULift.{u} (Fin n))
      fun n ↦ by simp
  exact ⟨Equiv.Perm (ULift.{u} (Fin n)), inferInstance, inferInstance, P, inferInstance,
    inferInstance, inferInstance, inferInstance, htor, hsplit⟩

section Preconnected

/-- Over a ring with preconnected prime spectrum, every finitely presented flat module has constant
stalk rank. -/
private theorem exists_rankAtStalk_eq_of_preconnectedSpace (A : Type*) [CommRing A]
    [PreconnectedSpace (PrimeSpectrum A)] (M : Type*) [AddCommGroup M] [Module A M]
    [Module.FinitePresentation A M] [Module.Flat A M] :
    ∃ n : ℕ, Module.rankAtStalk (R := A) M = n := by
  by_cases hne : Nonempty (PrimeSpectrum A)
  · obtain ⟨p₀⟩ := hne
    exact ⟨Module.rankAtStalk M p₀, funext fun p ↦
      IsLocallyConstant.apply_eq_of_preconnectedSpace
        (Module.isLocallyConstant_rankAtStalk (R := A) (M := M)) p p₀⟩
  · exact ⟨0, funext fun p ↦ (hne ⟨p⟩).elim⟩

/-- Core frame construction giving constant-rank splitting (`Algebra.IsFiniteSplit`) over a base
with preconnected prime spectrum, parameterized by an index family `ι` with `|ι n| = n`. -/
private theorem exists_perm_family_isFiniteEtaleTorsor_isFiniteSplit (A : Type u) [CommRing A]
    [PreconnectedSpace (PrimeSpectrum A)] (S : Type*) [CommRing S] [Algebra A S]
    [Algebra.Etale A S] [Module.Finite A S]
    (ι : ℕ → Type v) [∀ n, Fintype (ι n)] (hι : ∀ n, Fintype.card (ι n) = n) :
    ∃ (n : ℕ) (P : Type (max u v)) (_ : CommRing P) (_ : Algebra A P)
      (_ : MulSemiringAction (Equiv.Perm (ι n)) P)
      (_ : SMulCommClass (Equiv.Perm (ι n)) A P),
      IsFiniteEtaleTorsor (Equiv.Perm (ι n)) A P ∧ Algebra.IsFiniteSplit P (P ⊗[A] S) := by
  classical
  have : Small.{u} S := Module.Finite.small A S
  let eS : Shrink.{u} S ≃ₐ[A] S := Shrink.algEquiv A S
  have : Algebra.Etale A (Shrink.{u} S) := .of_equiv eS.symm
  have : Module.Finite A (Shrink.{u} S) := .equiv eS.symm.toLinearEquiv
  have : Module.FinitePresentation A (Shrink.{u} S) := .of_finite_of_finitePresentation A _
  obtain ⟨n, hrank⟩ := exists_rankAtStalk_eq_of_preconnectedSpace A (Shrink.{u} S)
  have hrank' : Module.rankAtStalk (R := A) (Shrink.{u} S) = Fintype.card (ι n) := by
    simpa [hι n] using hrank
  let P : Type (max u v) := FrameAlgebra A (Shrink.{u} S) (ι n)
  have : Algebra.IsFiniteSplit P (P ⊗[A] Shrink.{u} S) :=
    FrameAlgebra.isFiniteSplit_tensorProduct hrank'
  exact ⟨n, P, inferInstance, inferInstance, inferInstance, inferInstance,
    FrameAlgebra.isFiniteEtaleTorsor hrank', isFiniteSplit_of_algEquiv_right eS⟩

/-- Over a ring `A : Type u` with preconnected prime spectrum, every finite étale `A`-algebra `S`
becomes split of constant rank (`Algebra.IsFiniteSplit`) after base change to a finite étale
`Equiv.Perm (Fin n)`-torsor `P : Type u` over `A`. -/
theorem exists_perm_isFiniteEtaleTorsor_isFiniteSplit (A : Type u) [CommRing A]
    [PreconnectedSpace (PrimeSpectrum A)] (S : Type*) [CommRing S] [Algebra A S]
    [Algebra.Etale A S] [Module.Finite A S] :
    ∃ (n : ℕ) (P : Type u) (_ : CommRing P) (_ : Algebra A P)
      (_ : MulSemiringAction (Equiv.Perm (Fin n)) P)
      (_ : SMulCommClass (Equiv.Perm (Fin n)) A P),
      IsFiniteEtaleTorsor (Equiv.Perm (Fin n)) A P ∧ Algebra.IsFiniteSplit P (P ⊗[A] S) :=
  exists_perm_family_isFiniteEtaleTorsor_isFiniteSplit A S Fin Fintype.card_fin

/-- Over a ring `A : Type u` with preconnected prime spectrum, every finite étale `A`-algebra `S`
becomes split of constant rank (`Algebra.IsFiniteSplit`) after base change to a finite étale
`G`-torsor `P : Type u` over `A`, with `G : Type u`. -/
theorem exists_isFiniteEtaleTorsor_isFiniteSplit (A : Type u) [CommRing A]
    [PreconnectedSpace (PrimeSpectrum A)] (S : Type*) [CommRing S] [Algebra A S]
    [Algebra.Etale A S] [Module.Finite A S] :
    ∃ (G : Type u) (_ : Group G) (_ : Finite G) (P : Type u) (_ : CommRing P)
      (_ : Algebra A P) (_ : MulSemiringAction G P) (_ : SMulCommClass G A P),
      IsFiniteEtaleTorsor G A P ∧ Algebra.IsFiniteSplit P (P ⊗[A] S) := by
  obtain ⟨n, P, _, _, _, _, htor, hsplit⟩ :=
    exists_perm_family_isFiniteEtaleTorsor_isFiniteSplit A S (fun n ↦ ULift.{u} (Fin n))
      fun n ↦ by simp
  exact ⟨Equiv.Perm (ULift.{u} (Fin n)), inferInstance, inferInstance, P, inferInstance,
    inferInstance, inferInstance, inferInstance, htor, hsplit⟩

end Preconnected

end TauCeti.Algebra
