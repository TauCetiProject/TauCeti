/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.AlgebraicClosure
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.RingTheory.AlgebraicIndependent.Defs
public import Mathlib.RingTheory.EssentialFiniteness
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.LinearDisjoint
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.LinearAlgebra.Dimension.Localization
import Mathlib.RingTheory.AlgebraicIndependent.AlgebraicClosure
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.RingTheory.TensorProduct.MvPolynomial
import TauCeti.FieldTheory.Minpoly.IsIntegrallyClosedIn

/-!
# Relative algebraic closure: finiteness and extension of scalars

Let `K / k` be a field extension, and write `algebraicClosure k K` for the relative algebraic
closure of `k` in `K`: the elements of `K` algebraic over `k`.

If `K / k` is finitely generated (`Algebra.EssFiniteType k K`), then `algebraicClosure k K` is a
finite extension of `k`. Choose a transcendence basis `x` of `K / k`. It stays algebraically
independent over the algebraic extension `algebraicClosure k K`, which makes
`algebraicClosure k K` linearly disjoint from the polynomial ring `k[x]` inside `K`. So
`[algebraicClosure k K : k]` is the rank of `k[x][algebraicClosure k K]` over `k[x]`, which is at
most the rank of `K` over `k[x]`, that is, the degree of `K` over the fraction field `k(x)`. That
degree is finite because `K` is a finitely generated algebraic extension of `k(x)`. This
finiteness is what reduces integral closures in finitely generated field extensions to integral
closures in finite ones, as in Stacks, Lemma 10.162.2 (03GH).

Second, let `L` be an algebraically closed field containing `k`. If `K ⊗[k] L` is a domain, then
`k` is algebraically closed in `K`: the relative algebraic closure `algebraicClosure k K` is `⊥`.

Indeed, `E = algebraicClosure k K` is algebraic over `k`, and `L ⊗[k] E` embeds in the domain
`L ⊗[k] K` because every `k`-module is flat. So `L ⊗[k] E` is a domain that is integral over the
algebraically closed field `L`, hence equal to `L`; comparing dimensions, `[E : k] = 1`.

This is the field-theoretic content of the fact that the function field of a geometrically
integral scheme over `k` contains no nontrivial algebraic extension of `k`: there `K ⊗[k] L` is a
localization of the ring of functions on an affine open of the base change of the scheme to `L`,
which is integral.

Conversely, exact constants ensure that `K ⊗[k] L` is a domain for every separable algebraic
extension `L / k`. This follows from
`TauCeti.linearDisjoint_fieldRange_of_isIntegrallyClosedIn`, by embedding `L` in an algebraic
closure of `K`, and Mathlib's `IntermediateField.LinearDisjoint.isDomain`.

## Main results

* `AlgebraicIndependent.linearDisjoint_algebraicClosure`: an algebraically independent family
  generates a subalgebra linearly disjoint from the relative algebraic closure.
* `TauCeti.finiteDimensional_algebraicClosure`: the relative algebraic closure of `k` in a
  finitely generated field extension is finite over `k`.
* `TauCeti.algebraicClosure_eq_bot_of_isDomain_tensorProduct`: if `K ⊗[k] L` is a domain for an
  algebraically closed field `L` over `k`, then `algebraicClosure k K = ⊥`.
* `TauCeti.isDomain_tensorProduct_of_isIntegrallyClosedIn`: exact constants give a domain after
  a separable algebraic extension of scalars.

## References

* [Stacks Project, Lemma 10.162.2 (03GH)](https://stacks.math.columbia.edu/tag/03GH), whose proof
  uses the finiteness of the algebraic part of a finitely generated field extension.
* H. Stichtenoth, *Algebraic Function Fields and Codes*, second edition, Section III.6.
-/

public section

open scoped TensorProduct

section Finite

open scoped IntermediateField.algebraAdjoinAdjoin

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

/-- A family `x` of elements of `K` algebraically independent over `k` generates a subalgebra
`k[x]` linearly disjoint from the relative algebraic closure of `k` in `K`: the multiplication map
`algebraicClosure k K ⊗[k] k[x] → K` is injective. -/
theorem AlgebraicIndependent.linearDisjoint_algebraicClosure {ι : Type*} {x : ι → K}
    (hx : AlgebraicIndependent k x) :
    (algebraicClosure k K).toSubalgebra.LinearDisjoint (Algebra.adjoin k (Set.range x)) := by
  set A := (algebraicClosure k K).toSubalgebra
  have : Algebra.IsAlgebraic k A := (inferInstance : Algebra.IsAlgebraic k (algebraicClosure k K))
  -- Through `k[x] ≃ k[X]` and `A ⊗[k] k[X] ≃ A[X]`, the multiplication map becomes evaluation at
  -- `x` on `A[X]`, which is injective since `x` stays algebraically independent over `A`.
  let f : A ⊗[k] Algebra.adjoin k (Set.range x) →ₐ[k] K :=
    ((MvPolynomial.aeval x).restrictScalars k).comp
      (((MvPolynomial.algebraTensorAlgEquiv (σ := ι) k A).toAlgHom.restrictScalars k).comp
        (Algebra.TensorProduct.congr AlgEquiv.refl hx.aevalEquiv.symm).toAlgHom)
  have hf : Function.Injective f :=
    (algebraicIndependent_iff_injective_aeval.mp (hx.extendScalars A)).comp
      ((MvPolynomial.algebraTensorAlgEquiv (σ := ι) k A).injective.comp
        (Algebra.TensorProduct.congr AlgEquiv.refl hx.aevalEquiv.symm).injective)
  have : A.mulMap (Algebra.adjoin k (Set.range x)) = f := by
    refine Algebra.TensorProduct.ext' fun a b ↦ ?_
    obtain ⟨p, rfl⟩ := hx.aevalEquiv.surjective b
    simp [f, MvPolynomial.aeval_map_algebraMap, Algebra.smul_def]
  rw [Subalgebra.linearDisjoint_iff_injective, this]
  exact hf

namespace TauCeti

/-- The relative algebraic closure of `k` in a finitely generated field extension `K` is a finite
extension of `k`. -/
instance finiteDimensional_algebraicClosure [Algebra.EssFiniteType k K] :
    FiniteDimensional k (algebraicClosure k K) := by
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis k K
  set B := Algebra.adjoin k (Set.range ((↑) : s → K))
  set F := IntermediateField.adjoin k (Set.range ((↑) : s → K))
  -- `K` is a finite extension of the fraction field `F = k(s)` of `B = k[s]`.
  have : Algebra.IsAlgebraic F K := hs.isAlgebraic_field
  have : Algebra.EssFiniteType F K := .of_comp k F K
  have : Module.Finite F K := Algebra.finite_of_essFiniteType_of_isAlgebraic
  have hK : Module.rank B K < Cardinal.aleph0 := by
    rw [← IsFractionRing.rank_right_eq B F K]
    exact Module.rank_lt_aleph0 F K
  -- By linear disjointness, `[algebraicClosure k K : k]` is the rank of a `B`-submodule of `K`.
  have hle := Submodule.rank_le (Subalgebra.toSubmodule
    (Algebra.adjoin B ((algebraicClosure k K).toSubalgebra : Set K)))
  have : Module.rank k (algebraicClosure k K).toSubalgebra < Cardinal.aleph0 :=
    hs.1.linearDisjoint_algebraicClosure.adjoin_rank_eq_rank_left ▸ hle.trans_lt hK
  exact Module.rank_lt_aleph0_iff.mp this

end TauCeti

end Finite

namespace TauCeti

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

/-- A field with exact constants stays a domain after extending scalars by a separable
algebraic extension of the constants. -/
theorem isDomain_tensorProduct_of_isIntegrallyClosedIn (hex : IsIntegrallyClosedIn k K)
    (L : Type*) [Field L] [Algebra k L] [Algebra.IsSeparable k L] :
    IsDomain (K ⊗[k] L) := by
  let e : L →ₐ[k] AlgebraicClosure K := IsAlgClosed.lift
  algebraize [e.toRingHom]
  have : IsScalarTower k L (AlgebraicClosure K) :=
    IsScalarTower.of_algebraMap_eq fun c ↦ (e.commutes c).symm
  have h := linearDisjoint_fieldRange_of_isIntegrallyClosedIn
    (k' := L) (E := AlgebraicClosure K) hex
  have : IsDomain (e.fieldRange ⊗[k] K) := h.isDomain
  exact ((Algebra.TensorProduct.congr e.equivFieldRange.symm (AlgEquiv.refl : K ≃ₐ[k] K)).trans
    (Algebra.TensorProduct.comm k L K)).symm.toMulEquiv.isDomain

/-- If `K ⊗[k] L` is a domain for some algebraically closed field `L` over `k`, then `k` is
algebraically closed in `K`. -/
theorem algebraicClosure_eq_bot_of_isDomain_tensorProduct (L : Type*) [Field L] [Algebra k L]
    [IsAlgClosed L] [IsDomain (K ⊗[k] L)] : algebraicClosure k K = ⊥ := by
  let E := algebraicClosure k K
  -- `L ⊗[k] E` is a subring of the domain `L ⊗[k] K`, since `L` is flat over the field `k`.
  let f : L ⊗[k] E →ₐ[L] L ⊗[k] K :=
    Algebra.TensorProduct.map (AlgHom.id L L) (IsScalarTower.toAlgHom k E K)
  have hf : Function.Injective f :=
    Module.Flat.lTensor_preserves_injective_linearMap (M := L)
      (IsScalarTower.toAlgHom k E K).toLinearMap Subtype.val_injective
  have : IsDomain (L ⊗[k] K) :=
    (Algebra.TensorProduct.comm k K L).toMulEquiv.isDomain_iff.mp inferInstance
  have : IsDomain (L ⊗[k] E) := hf.isDomain f.toRingHom
  -- A domain integral over the algebraically closed field `L` is `L` itself.
  have hrank := (LinearEquiv.ofBijective (Algebra.linearMap L (L ⊗[k] E))
    (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := L) (K := L ⊗[k] E))).lift_rank_eq
  rw [Module.rank_self, Module.rank_baseChange, Cardinal.lift_one, Cardinal.lift_lift,
    eq_comm, Cardinal.lift_eq_one] at hrank
  exact IntermediateField.rank_eq_one_iff.mp hrank

end TauCeti
