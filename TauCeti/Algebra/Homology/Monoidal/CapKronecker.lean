/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Kronecker
public import TauCeti.Algebra.Homology.Monoidal.Cap
public import TauCeti.Algebra.Homology.Monoidal.Cup

/-!
# The Kronecker pairing of cap and cup products

Let `D : E ⟶ A ⊗ B` be a diagonal of chain complexes in a `k`-linear monoidal category, let
`a : M ⊗ B ⟶ B'` be an action of the coefficient object `M`, and let `ν : M ⊗ N ⟶ N'` be a pairing
of coefficient objects.  Suppose that a cochain `ψ : B'_q ⟶ N'` and a cochain `ψ' : B_q ⟶ N` are
compatible with the action and the pairing, `a ≫ ψ = (M ◁ ψ') ≫ ν`.  Then evaluating `ψ` on the
cap product of a chain `x` of `E` with a cochain `φ : A_p ⟶ M` is evaluating the cup product of
`φ` and `ψ'` along `D` and `ν` on `x`:

`⟨ψ, x ⌢ φ⟩ = ⟨φ ⌣ ψ', x⟩`,

with no sign, since both sides take the component of `D` and project to the summand
`A_p ⊗ B_q`.  On homology, for cocycles `φ`, `ψ` and `ψ'`, the cap product with the class of `φ`
followed by the Kronecker map of the class of `ψ` is the Kronecker map of the cup product of the
classes of `φ` and `ψ'`.

The basic example is `B' = B`, `M = N = N'` the tensor unit, `a` the left unitor and `ν` the left
unitor, with `ψ' = ψ`; for singular chains this is `TopCat.singularCap_comp_singularKronecker`.

## Main results

* `TauCeti.ChainComplex.capChain_comp`: the identity `⟨ψ, x ⌢ φ⟩ = ⟨φ ⌣ ψ', x⟩` of cochains.
* `TauCeti.ChainComplex.cap_comp_kronecker`: the identity on homology and cohomology classes.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.3, the identity `ψ(σ ⌢ φ) = (φ ⌣ ψ)(σ)` defining the cap product.
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory HomologicalComplex

namespace TauCeti.ChainComplex

variable {C : Type*} [Category* C]

section Chain

variable [Preadditive C] [MonoidalCategory C] [MonoidalPreadditive C] {A B B' E : ChainComplex C ℕ}
  [A.HasTensor B] {M N N' : C} {k : Type*} [CommSemiring k] [Linear k C] [MonoidalLinear k C]
  (D : E ⟶ HomologicalComplex.tensorObj A B)
  (a : ((tensorLeft M).mapHomologicalComplex _).obj B ⟶ B') (ν : M ⊗ N ⟶ N')

/-- **The Kronecker pairing of a cap product of chains and cochains**,
`⟨ψ, x ⌢ φ⟩ = ⟨φ ⌣ ψ', x⟩`: if the cochain `ψ : B'_q ⟶ N'` is obtained from `ψ' : B_q ⟶ N`
through the action `a` and the pairing `ν`, then the cap product with `φ` followed by `ψ` is the
cup product of `φ` and `ψ'` along `D` and `ν`. -/
lemma capChain_comp (p q n : ℕ) (h : p + q = n) (φ : A.X p ⟶ M) (ψ : B'.X q ⟶ N')
    (ψ' : B.X q ⟶ N) (hψ : a.f q ≫ ψ = (M ◁ ψ') ≫ ν) :
    capChain k D a p q n h φ ≫ ψ = cupCochain k D ν p q n h φ ψ' := by
  rw [capChain_apply, cupCochain_apply, Category.assoc, tensorCochain_comp, hψ,
    tensorCochain_whiskerLeft_comp, Category.id_comp]

end Chain

section Homology

variable [Abelian C] [MonoidalCategory C] [MonoidalPreadditive C] {A B B' E : ChainComplex C ℕ}
  [A.HasTensor B] {M N N' : C} {k : Type*} [CommRing k] [Linear k C] [MonoidalLinear k C]
  (D : E ⟶ HomologicalComplex.tensorObj A B)
  (a : ((tensorLeft M).mapHomologicalComplex _).obj B ⟶ B') (ν : M ⊗ N ⟶ N')

/-- **The Kronecker pairing of a cap product on homology**, `⟨[ψ], x ⌢ [φ]⟩ = ⟨[φ] ⌣ [ψ'], x⟩`:
if the cocycle `ψ` of `Hom(B', N')` is obtained from the cocycle `ψ'` of `Hom(B, N)` through the
action `a` and the pairing `ν`, then capping with the class of `φ` and applying the Kronecker map
of the class of `ψ` is the Kronecker map of the cup product of the classes of `φ` and `ψ'`. -/
lemma cap_comp_kronecker (p q n : ℕ) (h : p + q = n) (φ : (A.linearYonedaObj k M).cycles p)
    (ψ : (B'.linearYonedaObj k N').cycles q) (ψ' : (B.linearYonedaObj k N).cycles q)
    (hψ : a.f q ≫ (B'.linearYonedaObj k N').iCycles q ψ =
      (M ◁ (B.linearYonedaObj k N).iCycles q ψ') ≫ ν) :
    cap k D a p q n h ((A.linearYonedaObj k M).homologyπ p φ) ≫
        kronecker k B' N' q ((B'.linearYonedaObj k N').homologyπ q ψ) =
      kronecker k E N' n (cup k D ν p q n h ((A.linearYonedaObj k M).homologyπ p φ)
        ((B.linearYonedaObj k N).homologyπ q ψ')) := by
  rw [← cancel_epi (E.homologyπ n), cap_homologyπ_assoc, kronecker_homologyπ, cup_homologyπ,
    kronecker_homologyπ, iCycles_cupCycles]
  exact (capCycles_i_assoc D a p q n h φ _).trans
    (congrArg (E.iCycles n ≫ ·) (capChain_comp D a ν p q n h _ _ _ hψ))

end Homology

end TauCeti.ChainComplex
