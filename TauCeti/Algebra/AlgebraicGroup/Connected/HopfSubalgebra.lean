/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.HopfAlgebra.TensorProduct
public import TauCeti.Algebra.AlgebraicGroup.Connected.CommHopfAlgCat
public import TauCeti.Algebra.HopfAlgebra.Subalgebra
import TauCeti.Algebra.AlgebraicGroup.CommHopfAlgCat.FiniteType
import TauCeti.Algebra.AlgebraicGroup.Connected.BaseChange
import TauCeti.Algebra.AlgebraicGroup.Connected.ComponentGroup.Coordinate
import TauCeti.Algebra.AlgebraicGroup.Connected.Finite
import TauCeti.Algebra.AlgebraicGroup.FiniteType.ConnectedComponents
import TauCeti.Algebra.AlgebraicGroup.Smooth.CharZero
import TauCeti.Topology.ConnectedComponents

/-!
# Connectedness and finite Hopf subalgebras

A Hopf subalgebra `A` of a commutative Hopf algebra `H` over a field is the coordinate ring of a
quotient `Spec H → Spec A` of affine groups. When `A` is finite-dimensional this quotient is a
finite group scheme. This file relates connectedness of `Spec H` to the absence of nontrivial
finite quotients, that is, of finite-dimensional Hopf subalgebras other than `⊥`.

* In characteristic zero, a connected affine group has no nontrivial finite quotient. A
  finite-dimensional Hopf algebra in characteristic zero is reduced (Cartier), and a finite,
  reduced, connected affine group is trivial.
* Over an algebraically closed field of any characteristic, an affine group without nontrivial
  finite quotients is connected. A nontrivial idempotent lies in a finite-type Hopf subalgebra,
  whose component group is a nontrivial finite quotient.

Together they characterize connectedness over an algebraically closed field of characteristic
zero, and geometric connectedness over any field of characteristic zero by base change to an
algebraically closed extension. Characteristic zero is needed for the first statement: in
characteristic `p` the Frobenius kernel `αₚ` is connected and is its own nontrivial finite
quotient.

On the representation side, a finite quotient of `Spec H` corresponds to a finite tensor
subcategory of the finite comodules of `H`, so these statements are the Hopf-algebraic content of
the connectedness criterion for neutral Tannakian categories (Deligne–Milne, Corollary 2.22).

The statements over an algebraically closed field reduce to finite type through
`CommHopfAlgCat.exists_finiteType_injective_range_contains`, and so take the coordinate algebra in
the universe of the base field.

## Main declarations

* `Subalgebra.IsHopfSubalgebra.eq_bot_of_connectedSpace`: in characteristic zero, a
  finite-dimensional Hopf subalgebra of a Hopf algebra with connected spectrum is `⊥`.
* `TauCeti.HopfAlgebra.connectedSpace_primeSpectrum_of_forall_isHopfSubalgebra_eq_bot`: over an
  algebraically closed field, a Hopf algebra whose only finite-dimensional Hopf subalgebra is `⊥`
  has connected spectrum.
* `TauCeti.HopfAlgebra.connectedSpace_primeSpectrum_iff_forall_isHopfSubalgebra_eq_bot`: the
  resulting characterization over an algebraically closed field of characteristic zero.
* `TauCeti.geometricallyConnectedCommHopfAlgProperty_iff_forall_isHopfSubalgebra_eq_bot`: in
  characteristic zero, geometric connectedness means that the scalar extension to an
  algebraically closed field has no finite-dimensional Hopf subalgebra other than `⊥`.

## References

* P. Deligne and J. S. Milne, *Tannakian categories*, Corollary 2.22.
* W. C. Waterhouse, *Introduction to Affine Group Schemes*, §§6.7, 11.4 and 16.3.
* J. S. Milne, *Algebraic Groups* (2017), Proposition 2.37 and Chapter 3 (Cartier's theorem).
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

/-- Over an algebraically closed field, if the only finite-dimensional Hopf subalgebra of `H` is
`⊥`, then every finite-type commutative Hopf algebra embedding in `H` has preconnected spectrum:
its component group would otherwise give a nontrivial finite Hopf subalgebra. -/
private theorem preconnectedSpace_of_injective_of_forall_isHopfSubalgebra_eq_bot [IsAlgClosed k]
    {H : Type u} [CommRing H] [_root_.HopfAlgebra k H]
    (h : ∀ A : Subalgebra k H, A.IsHopfSubalgebra → FiniteDimensional k A → A = ⊥)
    (L : FiniteTypeCommHopfAlgCat.{u, u} k) (i : L →ₐc[k] H) (hi : Function.Injective i) :
    PreconnectedSpace (PrimeSpectrum L) := by
  let G := ConnectedComponents (PrimeSpectrum L)
  have : Fintype G := Fintype.ofFinite G
  let f : ConstantGroup.coordinateRing k G →ₐc[k] H :=
    i.comp (FiniteTypeCommHopfAlgCat.componentCoordinateBialgHom L)
  have hf : Function.Injective f :=
    hi.comp (FiniteTypeCommHopfAlgCat.componentCoordinateBialgHom_injective L)
  let r := (f : ConstantGroup.coordinateRing k G →ₐ[k] H).rangeRestrict
  have : FiniteDimensional k (ConstantGroup.coordinateRing k G) :=
    Module.Finite.equiv (ConstantGroup.functionLinearEquiv k G).symm
  have : FiniteDimensional k (f : ConstantGroup.coordinateRing k G →ₐ[k] H).range :=
    Module.Finite.of_surjective r.toLinearMap (AlgHom.rangeRestrict_surjective _)
  have hA := Subalgebra.IsHopfSubalgebra.of_finiteDimensional
    (A := (f : ConstantGroup.coordinateRing k G →ₐ[k] H).range) <| by
      rintro _ ⟨y, rfl⟩
      exact ⟨TensorProduct.map r.toLinearMap r.toLinearMap (Coalgebra.comul (R := k) y), by
        rw [← LinearMap.comp_apply, ← TensorProduct.map_comp]
        exact CoalgHomClass.map_comp_comul_apply f y⟩
  have hrange : Module.finrank k (f : ConstantGroup.coordinateRing k G →ₐ[k] H).range = 1 := by
    have : Nontrivial H := Bialgebra.nontrivial k
    rw [h _ hA inferInstance, Subalgebra.finrank_bot]
  have hcard : Fintype.card G ≤ 1 := by
    have hle := LinearMap.finrank_le_finrank_of_injective (f := r.toLinearMap)
      fun x y hxy ↦ hf (congrArg Subtype.val hxy)
    rwa [(ConstantGroup.functionLinearEquiv k G).finrank_eq, Module.finrank_fintype_fun_eq_card,
      hrange] at hle
  exact TauCeti.preconnectedSpace_iff_subsingleton_connectedComponents.mpr
    (Fintype.card_le_one_iff_subsingleton.mp hcard)

/-- **An affine group without nontrivial finite quotients is connected.** Over an algebraically
closed field `k`, a commutative Hopf algebra whose only finite-dimensional Hopf subalgebra is `⊥`
has connected prime spectrum. No finite-type hypothesis is needed. -/
theorem connectedSpace_primeSpectrum_of_forall_isHopfSubalgebra_eq_bot [IsAlgClosed k]
    {H : Type u} [CommRing H] [_root_.HopfAlgebra k H]
    (h : ∀ A : Subalgebra k H, A.IsHopfSubalgebra → FiniteDimensional k A → A = ⊥) :
    ConnectedSpace (PrimeSpectrum H) := by
  have : Nontrivial H := Bialgebra.nontrivial k
  refine TauCeti.connectedSpace_primeSpectrum_iff_idempotent_eq_zero_or_one.mpr fun e he ↦ ?_
  obtain ⟨L, hL, i, hi, hsub⟩ := CommHopfAlgCat.exists_finiteType_injective_range_contains
    (_root_.CommHopfAlgCat.of k H) {e} (Set.finite_singleton e)
  obtain ⟨e', he'⟩ := hsub rfl
  have he'e : i.hom e' = e := he'
  have := preconnectedSpace_of_injective_of_forall_isHopfSubalgebra_eq_bot h ⟨L, hL⟩ i.hom hi
  have hidem : IsIdempotentElem e' := hi (by rw [map_mul, he'e, he.eq])
  rcases hidem.eq_zero_or_eq_one_of_preconnectedSpace with h0 | h1
  · exact .inl (by rw [← he'e, h0, map_zero])
  · exact .inr (by rw [← he'e, h1, map_one])

/-- **Connectedness by finite quotients.** Over an algebraically closed field of characteristic
zero, a commutative Hopf algebra has connected prime spectrum exactly when its only
finite-dimensional Hopf subalgebra is `⊥`. -/
theorem connectedSpace_primeSpectrum_iff_forall_isHopfSubalgebra_eq_bot [IsAlgClosed k]
    [CharZero k] {H : Type u} [CommRing H] [_root_.HopfAlgebra k H] :
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
