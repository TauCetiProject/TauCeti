/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Etale.FiniteEtaleSplit.ConstantRank
public import TauCeti.RingTheory.Etale.Torsor.Frame

import Mathlib.Algebra.Algebra.Shrink
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Finiteness.Prod
import Mathlib.RingTheory.Finiteness.Small

/-!
# Splitting a finite étale algebra by a finite étale torsor

Every finite étale algebra `S` over a commutative ring `A` becomes totally split after base change
to some finite étale torsor `P` over `A` under a finite group `G`
(`TauCeti.Algebra.exists_isFiniteEtaleTorsor_isTotallySplit`). Geometrically, every finite étale
cover `Spec S → Spec A` is dominated, in the sense that pullback trivializes it into a finite
disjoint union of clopen pieces, by a finite étale Galois cover `Spec P → Spec A`.

When `S` has constant rank `n` on `Spec A`, the frame algebra of `n`-tuples of pairwise distinct
points of `Spec S` (`TauCeti.Algebra.FrameAlgebra`) is a finite étale symmetric-group torsor over
`A` whose universal frame gives `P ⊗[A] S ≃ₐ[P] (Fin n → P)`, so `P ⊗[A] S` is finite split in
Mathlib's sense (`TauCeti.Algebra.exists_isFiniteEtaleTorsor_isFiniteSplit`). This applies in
particular whenever `Spec A` is preconnected, for instance over a local ring, an integral domain,
or a field (`TauCeti.Algebra.exists_isFiniteEtaleTorsor_isFiniteSplit_of_preconnectedSpace`).

Over a general commutative ring `A`, the stalk rank of `S` is locally constant on the compact space
`Spec A`, hence bounded by some `n`, and padding `S` by idempotent quotients embeds `S` as a direct
factor of a finite étale `A`-algebra `S' = S × ∏_{j < n} A ⧸ (1 - e_j)` of constant rank `n`
(`TauCeti.Algebra.exists_etale_rankAtStalk_prod_pi_quotient_eq`). Taking `P` to be the frame
algebra of `S'`, the base change `P ⊗[A] S'` is finite split, hence totally split
(`TauCeti.Algebra.IsTotallySplit.of_isFiniteSplit`), and its direct factor `P ⊗[A] S` is therefore
totally split over `P` (`TauCeti.Algebra.IsTotallySplit.of_prod_fst`).

Shrinking `S` to the universe of `A` (`Shrink`) and indexing frames by `ULift (Fin n)` places both
`G` and `P` in the universe of `A`, while allowing `S` to live in an arbitrary universe.

## Main results

* `TauCeti.Algebra.exists_isFiniteEtaleTorsor_isFiniteSplit`: a finite étale `A`-algebra `S` of
  constant rank becomes finite split after base change to a finite étale torsor over `A`.
* `TauCeti.Algebra.exists_isFiniteEtaleTorsor_isFiniteSplit_of_preconnectedSpace`: over a ring with
  preconnected prime spectrum, every finite étale algebra becomes finite split after base change to
  a finite étale torsor.
* `TauCeti.Algebra.exists_isFiniteEtaleTorsor_isTotallySplit`: every finite étale `A`-algebra `S`
  becomes totally split after base change to a finite étale torsor over `A`.

## References

* P. Scholze, *Étale cohomology of diamonds*, §15, proof of Lemma 15.3.
* K. S. Kedlaya and R. Liu, *Relative p-adic Hodge theory: foundations*, Remark 1.4.7(c).
* H. W. Lenstra, *Galois theory for schemes*, Proposition 5.10.
* [Stacks Project, Tag 0BN2](https://stacks.math.columbia.edu/tag/0BN2).
-/

public section

open scoped TensorProduct

universe u

namespace TauCeti.Algebra

/-- **A finite étale algebra of constant rank is finite split by a finite étale torsor.** If `S` is
a finite étale `A`-algebra of constant stalk rank `n`, there exist a finite group `G` and a finite
étale `G`-torsor `P` over `A`, both in the universe of `A`, such that `P ⊗[A] S` is finite split
over `P`. -/
theorem exists_isFiniteEtaleTorsor_isFiniteSplit (A : Type u) (S : Type*) [CommRing A] [CommRing S]
    [Algebra A S] [Algebra.Etale A S] [Module.Finite A S] {n : ℕ}
    (h : Module.rankAtStalk (R := A) S = n) :
    ∃ (G : Type u) (_ : Group G) (_ : Finite G) (P : Type u) (_ : CommRing P)
      (_ : Algebra A P) (_ : MulSemiringAction G P) (_ : SMulCommClass G A P),
      IsFiniteEtaleTorsor G A P ∧ Algebra.IsFiniteSplit P (P ⊗[A] S) := by
  -- Shrink `S` to the universe of `A` and index frames by `ULift (Fin n)` so both `G` and `P`
  -- live in `Type u`.
  have : Small.{u} S := Module.Finite.small A S
  let S₀ : Type u := Shrink.{u} S
  let e : S₀ ≃ₐ[A] S := Shrink.algEquiv A S
  have : Algebra.Etale A S₀ := .of_equiv e.symm
  have : Module.Finite A S₀ := .equiv e.symm.toLinearEquiv
  let ι : Type u := ULift.{u} (Fin n)
  have hι : Module.rankAtStalk (R := A) S₀ = Fintype.card ι := by
    rw [Module.rankAtStalk_eq_of_equiv e.toLinearEquiv, h, Fintype.card_ulift, Fintype.card_fin]
  let P : Type u := FrameAlgebra A S₀ ι
  let f : P ⊗[A] S ≃ₐ[P] (Fin n → P) :=
    ((Algebra.TensorProduct.congr (AlgEquiv.refl : P ≃ₐ[P] P) e.symm).trans
      (FrameAlgebra.universalFrameEquiv hι)).trans
      (AlgEquiv.piCongrLeft' P (fun _ ↦ P) Equiv.ulift)
  exact ⟨Equiv.Perm ι, inferInstance, inferInstance, P, inferInstance, inferInstance,
    inferInstance, inferInstance, FrameAlgebra.isFiniteEtaleTorsor hι, ⟨n, ⟨f⟩⟩⟩

/-- **Over a ring with preconnected spectrum, every finite étale algebra is finite split by a
finite étale torsor.** Over a ring `A` whose prime spectrum is preconnected (for instance a local
ring, an integral domain, or a field), the stalk rank of a finite étale `A`-algebra `S` is constant,
so `S` becomes finite split after base change to a finite étale torsor over `A`. -/
theorem exists_isFiniteEtaleTorsor_isFiniteSplit_of_preconnectedSpace (A : Type u) (S : Type*)
    [CommRing A] [PreconnectedSpace (PrimeSpectrum A)] [CommRing S] [Algebra A S]
    [Algebra.Etale A S] [Module.Finite A S] :
    ∃ (G : Type u) (_ : Group G) (_ : Finite G) (P : Type u) (_ : CommRing P)
      (_ : Algebra A P) (_ : MulSemiringAction G P) (_ : SMulCommClass G A P),
      IsFiniteEtaleTorsor G A P ∧ Algebra.IsFiniteSplit P (P ⊗[A] S) := by
  have : Module.FinitePresentation A S := .of_finite_of_finitePresentation A S
  by_cases hA : Nonempty (PrimeSpectrum A)
  · obtain ⟨p₀⟩ := hA
    refine exists_isFiniteEtaleTorsor_isFiniteSplit A S (n := Module.rankAtStalk (R := A) S p₀)
      (funext fun q ↦ ?_)
    exact IsLocallyConstant.apply_eq_of_preconnectedSpace
      (Module.isLocallyConstant_rankAtStalk (R := A) (M := S)) q p₀
  · exact exists_isFiniteEtaleTorsor_isFiniteSplit A S (n := 0) (funext fun q ↦ (hA ⟨q⟩).elim)

/-- **Every finite étale algebra is totally split by a finite étale torsor.** For every finite
étale `A`-algebra `S`, there exist a finite group `G` and a finite étale `G`-torsor `P` over `A`,
both in the universe of `A`, such that `P ⊗[A] S` is totally split over `P`. Unlike in
`TauCeti.Algebra.exists_isFiniteEtaleTorsor_isFiniteSplit`, the stalk rank of `S` may vary across
clopen pieces of `Spec A`. -/
theorem exists_isFiniteEtaleTorsor_isTotallySplit (A : Type u) (S : Type*) [CommRing A]
    [CommRing S] [Algebra A S] [Algebra.Etale A S] [Module.Finite A S] :
    ∃ (G : Type u) (_ : Group G) (_ : Finite G) (P : Type u) (_ : CommRing P)
      (_ : Algebra A P) (_ : MulSemiringAction G P) (_ : SMulCommClass G A P),
      IsFiniteEtaleTorsor G A P ∧ IsTotallySplit P (P ⊗[A] S) := by
  -- Pad `S` by idempotent quotients to obtain a finite étale algebra of constant rank `n`,
  -- split that algebra over its frame torsor `P`, and project back to the factor `P ⊗[A] S`.
  obtain ⟨n, e, -, _, hrank⟩ := exists_etale_rankAtStalk_prod_pi_quotient_eq A S
  obtain ⟨G, _, _, P, _, _, _, _, hP, _⟩ := exists_isFiniteEtaleTorsor_isFiniteSplit A _ hrank
  have htot : IsTotallySplit P (P ⊗[A] (S × Π j, A ⧸ Ideal.span {1 - e j})) := .of_isFiniteSplit
  exact ⟨G, _, _, P, _, _, _, _, hP,
    (htot.of_algEquiv (Algebra.TensorProduct.prodRight A P P _ _)).of_prod_fst⟩

end TauCeti.Algebra
