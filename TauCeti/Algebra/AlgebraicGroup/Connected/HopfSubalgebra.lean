/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.HopfAlgebra.TensorProduct
public import TauCeti.Algebra.AlgebraicGroup.Connected.CommHopfAlgCat
public import TauCeti.Algebra.HopfAlgebra.Subalgebra
import Mathlib.RingTheory.Finiteness.Descent
import TauCeti.Algebra.AlgebraicGroup.CommHopfAlgCat.FiniteType
import TauCeti.Algebra.AlgebraicGroup.Connected.BaseChange
import TauCeti.Algebra.AlgebraicGroup.Connected.Descent
import TauCeti.Algebra.AlgebraicGroup.Connected.Finite
import TauCeti.Algebra.AlgebraicGroup.Connected.Normal
import TauCeti.Algebra.AlgebraicGroup.FiniteType.BaseChange
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Coinvariants.BaseChange
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Coinvariants.Components
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Normal.Descent
import TauCeti.Algebra.AlgebraicGroup.Smooth.CharZero
import TauCeti.LinearAlgebra.TensorProduct.Range
import TauCeti.RingTheory.TensorProduct.Maps

/-!
# Connectedness and finite Hopf subalgebras

A Hopf subalgebra `A` of a commutative Hopf algebra `H` over a field is the coordinate ring of a
quotient `Spec H → Spec A` of affine groups. When `A` is finite-dimensional this quotient is a
finite group scheme. This file relates connectedness of `Spec H` to the absence of nontrivial
finite quotients, that is, of finite-dimensional Hopf subalgebras other than `⊥`.

* In characteristic zero, a connected affine group has no nontrivial finite quotient. A
  finite-dimensional Hopf algebra in characteristic zero is reduced (Cartier), and a finite,
  reduced, connected affine group is trivial.
* Over a perfect field, in particular over a field of characteristic zero or an algebraically
  closed field, an affine group without nontrivial finite quotients is connected. A nontrivial
  idempotent lies in a finite-type Hopf subalgebra `L`. Over a perfect field the identity
  component of `Spec L` is defined over the base field, by Galois descent from the algebraic
  closure, and the functions on `Spec L` invariant under it form a finite-dimensional Hopf
  subalgebra containing every idempotent: after base change they are the functions on the finite
  component group.

Together they characterize connectedness over any field of characteristic zero, and geometric
connectedness over such a field by base change to an algebraically closed extension.
Characteristic zero is needed for the first statement: in characteristic `p` the Frobenius kernel
`αₚ` is connected and is its own nontrivial finite quotient.

On the representation side, a finite quotient of `Spec H` corresponds to a finite tensor
subcategory of the finite comodules of `H`, so these statements are the Hopf-algebraic content of
the connectedness criterion for neutral Tannakian categories (Deligne–Milne, Corollary 2.22).

The statements without nontrivial finite quotients reduce to finite type through
`CommHopfAlgCat.exists_finiteType_injective_range_contains`, and so take the coordinate algebra in
the universe of the base field.

## Main declarations

* `Subalgebra.IsHopfSubalgebra.eq_bot_of_connectedSpace`: in characteristic zero, a
  finite-dimensional Hopf subalgebra of a Hopf algebra with connected spectrum is `⊥`.
* `IsIdempotentElem.exists_isHopfSubalgebra_finiteDimensional_mem`: over a perfect field, every
  idempotent lies in a finite-dimensional Hopf subalgebra.
* `TauCeti.HopfAlgebra.connectedSpace_primeSpectrum_of_forall_isHopfSubalgebra_eq_bot`: over a
  perfect field, a Hopf algebra whose only finite-dimensional Hopf subalgebra is `⊥` has
  connected spectrum.
* `TauCeti.HopfAlgebra.connectedSpace_primeSpectrum_iff_forall_isHopfSubalgebra_eq_bot`: the
  resulting characterization over a field of characteristic zero.
* `TauCeti.geometricallyConnectedCommHopfAlgProperty_iff_forall_isHopfSubalgebra_eq_bot`: in
  characteristic zero, geometric connectedness means that the scalar extension to an
  algebraically closed field has no finite-dimensional Hopf subalgebra other than `⊥`.

## References

* P. Deligne and J. S. Milne, *Tannakian categories*, Corollary 2.22.
* W. C. Waterhouse, *Introduction to Affine Group Schemes*, §§6.7, 11.4 and 16.3.
* J. S. Milne, *Algebraic Groups* (2017), Proposition 2.37, Chapter 3 (Cartier's theorem) and
  Appendix A (Galois descent).
-/

public section

open scoped TensorProduct

universe u v

namespace Subalgebra.IsHopfSubalgebra

variable {k : Type u} {H : Type v} [Field k] [CommRing H] [HopfAlgebra k H] {A : Subalgebra k H}

/-- **A connected affine group in characteristic zero has no nontrivial finite quotient.** Over a
field of characteristic zero, a finite-dimensional Hopf subalgebra of a commutative Hopf algebra
with connected prime spectrum is `⊥`. -/
theorem eq_bot_of_connectedSpace [CharZero k] [ConnectedSpace (PrimeSpectrum H)]
    (hA : A.IsHopfSubalgebra) [FiniteDimensional k A] : A = ⊥ := by
  let : HopfAlgebra k A := hA.hopfAlgebra
  have : IsReduced A := TauCeti.HopfAlgebra.isReduced_of_charZero k A
  have : Nontrivial H := Bialgebra.nontrivial k
  have : ConnectedSpace (PrimeSpectrum A) :=
    TauCeti.connectedSpace_primeSpectrum_iff_idempotent_eq_zero_or_one.mpr fun e he ↦
      (he.map A.val).eq_zero_or_eq_one_of_preconnectedSpace.imp Subtype.ext Subtype.ext
  have haug := TauCeti.HopfIdeal.augmentation_eq_bot_of_moduleFinite (k := k) (H := A)
  rw [eq_bot_iff]
  intro x hx
  have hmem : (⟨x, hx⟩ : A) - algebraMap k A (Coalgebra.counit (R := k) (⟨x, hx⟩ : A)) ∈
      TauCeti.HopfIdeal.augmentation k A := by
    simp [TauCeti.HopfIdeal.mem_augmentation]
  rw [haug, TauCeti.HopfIdeal.mem_bot, sub_eq_zero] at hmem
  exact Algebra.mem_bot.mpr ⟨_, (congrArg Subtype.val hmem).symm⟩

end Subalgebra.IsHopfSubalgebra

namespace TauCeti.HopfAlgebra

variable {k : Type u} [Field k]

variable (k) in
/-- **Idempotents factor through finite quotients.** Over a perfect field `k`, every idempotent
of a commutative Hopf algebra `H` lies in a finite-dimensional Hopf subalgebra.

For `H` of finite type, this is the algebra of functions invariant under the identity component.
That component is defined over `k` by Galois descent from the algebraic closure, and after base
change its invariant functions are the functions on the finite component group. -/
theorem _root_.IsIdempotentElem.exists_isHopfSubalgebra_finiteDimensional_mem [PerfectField k]
    {H : Type u} [CommRing H] [_root_.HopfAlgebra k H] {e : H} (he : IsIdempotentElem e) :
    ∃ A : Subalgebra k H, A.IsHopfSubalgebra ∧ FiniteDimensional k A ∧ e ∈ A := by
  -- Reduce to a finite-type Hopf algebra `L` embedded in `H` through `e`.
  obtain ⟨L, hL, i, hi, hsub⟩ := CommHopfAlgCat.exists_finiteType_injective_range_contains
    (_root_.CommHopfAlgCat.of k H) {e} (Set.finite_singleton e)
  obtain ⟨e', he'⟩ := hsub rfl
  have he'e : i.hom e' = e := he'
  have hidem : IsIdempotentElem e' := hi (by rw [map_mul, he'e, he.eq])
  -- Descend the identity component of `Spec L` from the algebraic closure `Ω`.
  let Ω := AlgebraicClosure k
  let LΩ : FiniteTypeCommHopfAlgCat.{u, u} Ω := FiniteTypeCommHopfAlgCat.baseChange ⟨L, hL⟩
  obtain ⟨I, hI, -⟩ :=
    CommHopfAlgCat.existsUnique_baseChangeHopfIdeal_eq_identityComponentHopfIdeal (A := L)
  have hN : I.IsNormal := CommHopfAlgCat.isNormal_of_baseChangeHopfIdeal (K := Ω)
    (hI ▸ isNormal_identityComponentHopfIdeal)
  -- Its invariant functions are finite-dimensional, since they are after base change to `Ω`.
  have : Module.Finite Ω (CommHopfAlgCat.baseChangeHopfIdeal (K := Ω) I).coinvariants := by
    rw [hI]
    exact FiniteTypeCommHopfAlgCat.moduleFinite_coinvariants_of_le_identityComponentHopfIdeal
      LΩ _ le_rfl
  have : Module.Finite Ω (Ω ⊗[k] I.coinvariants) :=
    Module.Finite.equiv (CommHopfAlgCat.coinvariantsBaseChangeEquiv I).symm.toLinearEquiv
  have : FiniteDimensional k I.coinvariants :=
    Module.Finite.of_finite_tensorProduct_of_faithfullyFlat Ω
  -- They contain `e'`, since every idempotent is invariant after base change to `Ω`.
  have h2 : (1 : Ω) ⊗ₜ[k] e' ∈
      (identityComponentHopfIdeal (k := Ω) (H := LΩ)).coinvariants := by
    rw [FiniteTypeCommHopfAlgCat.coinvariants_identityComponentHopfIdeal_eq_range LΩ]
    exact FiniteTypeCommHopfAlgCat.mem_range_componentCoordinateMap_of_isIdempotentElem LΩ
      (hidem.map (Algebra.TensorProduct.includeRight : L →ₐ[k] Ω ⊗[k] L))
  have h1 : (1 : Ω) ⊗ₜ[k] e' ∈
      (CommHopfAlgCat.baseChangeHopfIdeal (K := Ω) I).coinvariants := by
    -- The coordinate algebra of the bundled `LΩ` is `CommHopfAlgCat.baseChange L` by definition.
    rw [hI]
    exact h2
  rw [CommHopfAlgCat.coinvariants_baseChangeHopfIdeal, ← Subalgebra.mem_toSubmodule,
    Subalgebra.toSubmodule_baseChange, Submodule.one_tmul_mem_baseChange_iff] at h1
  -- Their image in `H` is the required Hopf subalgebra.
  refine ⟨I.coinvariants.map (i.hom : L →ₐ[k] H),
    hN.isHopfSubalgebra_coinvariants.map i.hom, ?_, ⟨e', h1, he'e⟩⟩
  exact Module.Finite.of_surjective
    ((i.hom : L →ₐ[k] H).subalgebraMap I.coinvariants).toLinearMap
    ((i.hom : L →ₐ[k] H).subalgebraMap_surjective _)

/-- **An affine group without nontrivial finite quotients is connected.** Over a perfect field
`k`, for instance a field of characteristic zero or an algebraically closed field, a commutative
Hopf algebra whose only finite-dimensional Hopf subalgebra is `⊥` has connected prime spectrum.
No finite-type hypothesis is needed. -/
theorem connectedSpace_primeSpectrum_of_forall_isHopfSubalgebra_eq_bot [PerfectField k]
    {H : Type u} [CommRing H] [_root_.HopfAlgebra k H]
    (h : ∀ A : Subalgebra k H, A.IsHopfSubalgebra → FiniteDimensional k A → A = ⊥) :
    ConnectedSpace (PrimeSpectrum H) := by
  have : Nontrivial H := Bialgebra.nontrivial k
  refine TauCeti.connectedSpace_primeSpectrum_iff_idempotent_eq_zero_or_one.mpr fun e he ↦ ?_
  obtain ⟨A, hA, hfin, heA⟩ := he.exists_isHopfSubalgebra_finiteDimensional_mem k
  rw [h A hA hfin] at heA
  obtain ⟨c, rfl⟩ := Algebra.mem_bot.mp heA
  have hc : IsIdempotentElem c := (algebraMap k H).injective (by rw [map_mul, he.eq])
  rcases IsIdempotentElem.iff_eq_zero_or_one.mp hc with rfl | rfl
  · exact .inl (map_zero _)
  · exact .inr (map_one _)

/-- **Connectedness by finite quotients.** Over a field of characteristic zero, a commutative Hopf
algebra has connected prime spectrum exactly when its only finite-dimensional Hopf subalgebra is
`⊥`. -/
theorem connectedSpace_primeSpectrum_iff_forall_isHopfSubalgebra_eq_bot [CharZero k]
    {H : Type u} [CommRing H] [_root_.HopfAlgebra k H] :
    ConnectedSpace (PrimeSpectrum H) ↔
      ∀ A : Subalgebra k H, A.IsHopfSubalgebra → FiniteDimensional k A → A = ⊥ :=
  ⟨fun _ _ hA _ ↦ hA.eq_bot_of_connectedSpace,
    connectedSpace_primeSpectrum_of_forall_isHopfSubalgebra_eq_bot⟩

end TauCeti.HopfAlgebra

namespace TauCeti

/-- **Geometric connectedness by finite quotients.** Over a field `k` of characteristic zero, a
commutative Hopf algebra `H` is geometrically connected exactly when, after scalar extension to
an algebraically closed field `K`, the only finite-dimensional Hopf subalgebra of `K ⊗[k] H` is
`⊥`. -/
theorem geometricallyConnectedCommHopfAlgProperty_iff_forall_isHopfSubalgebra_eq_bot
    (k : Type u) [Field k] [CharZero k] (K : Type u) [Field K] [Algebra k K] [IsAlgClosed K]
    (H : CommHopfAlgCat.{u} k) :
    geometricallyConnectedCommHopfAlgProperty k H ↔
      ∀ A : Subalgebra K (K ⊗[k] (H : Type u)), A.IsHopfSubalgebra → FiniteDimensional K A →
        A = ⊥ := by
  have : CharZero K := charZero_of_injective_algebraMap (algebraMap k K).injective
  rw [geometricallyConnectedCommHopfAlgProperty_iff_connectedSpace_baseChange k K H]
  exact HopfAlgebra.connectedSpace_primeSpectrum_iff_forall_isHopfSubalgebra_eq_bot

end TauCeti
