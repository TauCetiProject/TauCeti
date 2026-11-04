/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Etale.Torsor.Trivial
import Mathlib.RingTheory.Etale.Descent
import TauCeti.RingTheory.Flat.Descent

/-!
# Finite étale torsors are local for the fpqc topology

Being a finite étale `G`-torsor can be checked after a faithfully flat extension of the base:
if `A → A'` is faithfully flat and `A' ⊗[A] B` is a finite étale `G`-torsor over `A'`, then `B`
is a finite étale `G`-torsor over `A`
(`TauCeti.Algebra.IsFiniteEtaleTorsor.of_baseChange`). Each condition in the definition
descends: finiteness, étaleness and faithful flatness by faithfully flat descent, and the
bijectivity of the Galois map because the Galois map of `A' ⊗[A] B` is the base change of the
Galois map of `B` (`TauCeti.MulSemiringAction.bijective_tensorToPi_baseChange_iff`).

Consequently a finite étale torsor is the same as a `G`-algebra that is locally trivial for the
fpqc topology: `B` is a finite étale `G`-torsor over `A` exactly when, for some faithfully flat
`A`-algebra `A'`, the base change `A' ⊗[A] B` is `G`-equivariantly isomorphic to the trivial
torsor `G → A'` (`TauCeti.Algebra.isFiniteEtaleTorsor_iff_exists_algEquiv_pi`). A torsor is
trivialised by itself: its Galois map `B ⊗[A] B ≃ (G → B)` is such an equivariant isomorphism.
This is the form in which torsors are recognised in practice, for instance a torsor constructed
from a finite étale algebra is shown to be one after base change to a faithfully flat algebra
over which the finite étale algebra splits.

Throughout, `G` acts on `A' ⊗[A] B` through the right factor and on `G → A'` by right
translation `(h • f) g = f (g * h)`, the actions of `TauCeti.Algebra.IsFiniteEtaleTorsor.baseChange`
and `TauCeti.Algebra.IsFiniteEtaleTorsor.trivial`.

## Main results

* `TauCeti.Algebra.IsFiniteEtaleTorsor.of_baseChange`,
  `TauCeti.Algebra.isFiniteEtaleTorsor_baseChange_iff`: faithfully flat descent of torsors.
* `TauCeti.Algebra.isFiniteEtaleTorsor_iff_exists_algEquiv_pi`: torsors are the fpqc-locally
  trivial `G`-algebras.
-/

public section

open TensorProduct

universe v

namespace TauCeti

namespace Algebra

variable {G A B : Type*} [Group G] [Finite G] [CommRing A] [CommRing B] [Algebra A B]
  [MulSemiringAction G B] [SMulCommClass G A B]

namespace IsFiniteEtaleTorsor

attribute [local instance] Algebra.TensorProduct.rightMulSemiringAction

/-- **Faithfully flat descent of torsors.** If `A → A'` is faithfully flat and `A' ⊗[A] B` is a
finite étale `G`-torsor over `A'`, with `G` acting on the right factor, then `B` is a finite étale
`G`-torsor over `A`. -/
theorem of_baseChange (A' : Type*) [CommRing A'] [Algebra A A'] [Module.FaithfullyFlat A A']
    [h : IsFiniteEtaleTorsor G A' (A' ⊗[A] B)] : IsFiniteEtaleTorsor G A B := by
  have := h.etale
  have := h.finite
  have := h.faithfullyFlat
  exact ⟨.of_etale_tensorProduct_of_faithfullyFlat A',
    .of_finite_tensorProduct_of_faithfullyFlat A', .of_tensorProduct A A' B,
    (MulSemiringAction.bijective_tensorToPi_baseChange_iff A').mp h.bijective_tensorToPi⟩

/-- A `G`-algebra that becomes isomorphic to the trivial torsor `G → A'` after a faithfully flat
extension `A → A'` of the base, compatibly with the actions of `G`, is a finite étale `G`-torsor
over `A`. -/
theorem of_baseChange_algEquiv_pi (A' : Type*) [CommRing A'] [Algebra A A']
    [Module.FaithfullyFlat A A'] (e : A' ⊗[A] B ≃ₐ[A'] (G → A'))
    (he : ∀ (g : G) (x : A' ⊗[A] B) (k : G), e (g • x) k = e x (k * g)) :
    IsFiniteEtaleTorsor G A B := by
  let := rightRegularMulSemiringAction G A'
  have : IsFiniteEtaleTorsor G A' (A' ⊗[A] B) := of_algEquiv (h := .trivial G A') e.symm
    fun g f ↦ e.injective <| funext fun k ↦ by
      rw [he, AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply,
        rightRegularMulSemiringAction_smul_apply]
  exact of_baseChange A'

end IsFiniteEtaleTorsor

attribute [local instance] Algebra.TensorProduct.rightMulSemiringAction

/-- Finite étale torsors descend and ascend along faithfully flat extensions of the base: for
`A → A'` faithfully flat, `A' ⊗[A] B` is a finite étale `G`-torsor over `A'`, with `G` acting on
the right factor, exactly when `B` is a finite étale `G`-torsor over `A`. -/
theorem isFiniteEtaleTorsor_baseChange_iff (A' : Type*) [CommRing A'] [Algebra A A']
    [Module.FaithfullyFlat A A'] :
    IsFiniteEtaleTorsor G A' (A' ⊗[A] B) ↔ IsFiniteEtaleTorsor G A B :=
  ⟨fun _ ↦ .of_baseChange A', fun _ ↦ inferInstance⟩

/-- **Torsors are fpqc-locally trivial.** `B` is a finite étale `G`-torsor over `A` exactly when,
after some faithfully flat extension `A → A'`, the algebra `A' ⊗[A] B` is `G`-equivariantly
isomorphic to the trivial torsor `G → A'`, on which `G` acts by right translation. A torsor is
trivialised over `A' = B` by its own Galois map. -/
theorem isFiniteEtaleTorsor_iff_exists_algEquiv_pi {B : Type v} [CommRing B] [Algebra A B]
    [MulSemiringAction G B] [SMulCommClass G A B] :
    IsFiniteEtaleTorsor G A B ↔
      ∃ (A' : Type v) (_ : CommRing A') (_ : Algebra A A') (_ : Module.FaithfullyFlat A A')
        (e : A' ⊗[A] B ≃ₐ[A'] (G → A')),
          ∀ (g : G) (x : A' ⊗[A] B) (k : G), e (g • x) k = e x (k * g) := by
  refine ⟨fun h ↦ ?_, fun ⟨A', _, _, _, e, he⟩ ↦ .of_baseChange_algEquiv_pi A' e he⟩
  have := h.faithfullyFlat
  -- The Galois map `B ⊗[A] B → (G → B)` intertwines the right-factor action with right
  -- translation: `b * k • (g • b') = b * (k * g) • b'`.
  refine ⟨B, inferInstance, inferInstance, inferInstance,
    AlgEquiv.ofBijective _ h.bijective_tensorToPi, fun g x k ↦ ?_⟩
  rw [AlgEquiv.ofBijective_apply, AlgEquiv.ofBijective_apply,
    Algebra.TensorProduct.rightMulSemiringAction_smul_def]
  exact MulSemiringAction.tensorToPi_map_toAlgHom g x k

end Algebra

end TauCeti
