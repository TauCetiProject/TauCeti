/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.MassFormula.Eisenstein.Basic
public import TauCeti.FieldTheory.IntermediateField.Isomorphic

/-!
# The isomorphism classes of the counted extensions

Serre's mass formula has two forms: a sum over the totally ramified extensions `L ∈ σ_K(n)` of a
local field `K` inside a fixed separable closure, and a sum over their `K`-isomorphism classes
weighted by `1 / #Aut_K(L)`. This file proves the orbit count relating them: the isomorphism class
of `L` inside `σ_K(n)` has `n / #Aut_K(L)` members.

The family `σ_K(n)` is closed under `K`-isomorphism, so the isomorphism class of `L` inside it is
its isomorphism class among all subextensions of `SeparableClosure K`. The orbit count is then
`IntermediateField.ncard_isomorphic_mul_natCard_algEquiv_of_isSepClosed` for the separable
extension `L / K` of degree `n`.

## Main results

* `TauCeti.mem_totallyRamifiedOfDegree_of_algEquiv`: `σ_K(n)` is closed under `K`-isomorphism.
* `TauCeti.ncard_isomorphic_mul_natCard_algEquiv`: for `L ∈ σ_K(n)`, the number of members of
  `σ_K(n)` that are `K`-isomorphic to `L`, times `#Aut_K(L)`, is `n`.
* `TauCeti.setOf_isomorphic_eq_singleton_of_normal`: a Galois member of `σ_K(n)` is alone in its
  isomorphism class.

## References

* J.-P. Serre, *Une « formule de masse » pour les extensions totalement ramifiées de degré donné
  d'un corps local*, C. R. Acad. Sci. Paris Sér. A **286** (1978), 1031–1036, Remarque 3°.
-/

public section

namespace TauCeti

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- `σ_K(n)` is closed under `K`-isomorphism: a subextension of `SeparableClosure K` that is
`K`-isomorphic to a member of `σ_K(n)` is again a member. -/
theorem mem_totallyRamifiedOfDegree_of_algEquiv {n : ℕ}
    {L M : IntermediateField K (SeparableClosure K)} (hL : L ∈ totallyRamifiedOfDegree K n)
    (e : L ≃ₐ[K] M) : M ∈ totallyRamifiedOfDegree K n :=
  ((IntermediateField.algHomFieldRangeEquiv M).symm e).2 ▸
    AlgHom.fieldRange_mem_totallyRamifiedOfDegree _ hL

/-- The members of `σ_K(n)` that are `K`-isomorphic to a member `L` are all the subextensions of
`SeparableClosure K` that are `K`-isomorphic to `L`. -/
theorem setOf_mem_totallyRamifiedOfDegree_isomorphic {n : ℕ}
    {L : IntermediateField K (SeparableClosure K)} (hL : L ∈ totallyRamifiedOfDegree K n) :
    {M ∈ totallyRamifiedOfDegree K n | Nonempty (L ≃ₐ[K] M)} =
      {M : IntermediateField K (SeparableClosure K) | Nonempty (L ≃ₐ[K] M)} :=
  Set.ext fun _ ↦ and_iff_right_of_imp fun ⟨e⟩ ↦ mem_totallyRamifiedOfDegree_of_algEquiv hL e

/-- **The orbit count** ([Serre 1978, Remarque 3°]): for `L ∈ σ_K(n)`, the isomorphism class of `L`
inside `σ_K(n)` has `n / #Aut_K(L)` members, in multiplied form. The extension `L / K` is separable
of degree `n`, so it has `n` embeddings into `SeparableClosure K`; their images are the members of
the class, and the embeddings with a given image form a torsor under `Aut_K(L)`. -/
theorem ncard_isomorphic_mul_natCard_algEquiv {n : ℕ}
    {L : IntermediateField K (SeparableClosure K)} (hL : L ∈ totallyRamifiedOfDegree K n) :
    {M ∈ totallyRamifiedOfDegree K n | Nonempty (L ≃ₐ[K] M)}.ncard * Nat.card (L ≃ₐ[K] L) =
      n := by
  have hL' := mem_totallyRamifiedOfDegree_iff.1 hL
  have := hL'.2.finite
  rw [setOf_mem_totallyRamifiedOfDegree_isomorphic hL,
    IntermediateField.ncard_isomorphic_mul_natCard_algEquiv_of_isSepClosed, hL'.1]

/-- **The Galois case of the orbit count**: a member `L` of `σ_K(n)` that is normal over `K` is
the only member of its isomorphism class. -/
theorem setOf_isomorphic_eq_singleton_of_normal {n : ℕ}
    {L : IntermediateField K (SeparableClosure K)} (hL : L ∈ totallyRamifiedOfDegree K n)
    [Normal K L] : {M ∈ totallyRamifiedOfDegree K n | Nonempty (L ≃ₐ[K] M)} = {L} := by
  rw [setOf_mem_totallyRamifiedOfDegree_isomorphic hL,
    IntermediateField.setOf_isomorphic_eq_singleton_of_normal]

end TauCeti
