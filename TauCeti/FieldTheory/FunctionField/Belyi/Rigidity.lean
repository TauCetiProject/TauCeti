/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Belyi.Descent
import TauCeti.Algebra.Algebra.Equiv

/-!
# Rigid Belyi pairs are defined over their field of moduli

An algebraic Belyi pair `X = (F, t)` over a field `k` of characteristic zero is **rigid** when its
only automorphism over `k(t)` is the identity, that is when `F ≃ₐ[k(t)] F` is a subsingleton. Then
every pair has at most one isomorphism onto `X` (`AlgEquiv.subsingleton_of_subsingleton_aut`).

Let `L / K` be a finite Galois extension and suppose that every `σ ∈ Gal(L/K)` fixes the
isomorphism class of a rigid pair `X` over `L`, so that there is an isomorphism `f_σ : X^σ ≃ X`
from the conjugate pair. Each `f_σ` is then unique, and so the family `(f_σ)` satisfies the
cocycle condition `f_{στ} = f_σ ∘ σ(f_τ)` automatically: both sides are isomorphisms from `X^{στ}`
to `X`. It is a descent datum
(`TauCeti.AlgebraicBelyiPair.DescentDatum.ofSubsingleton`), and Weil descent
(`TauCeti.AlgebraicBelyiPair.DescentDatum.model`) makes `X` defined over `K`.

For the field of moduli `M` of the class of `X`, the automorphisms of `k` fixing `M` are exactly the
stabilizer of the class as soon as `k` is finite over `ℚ`, and `k` is Galois over `M` as over the
fixed field of any group of automorphisms. So a rigid pair over a finite extension of `ℚ` is defined
over its field of moduli (`TauCeti.AlgebraicBelyiPair.IsoClass.isDefinedOver_fieldOfModuli`).
Since every field of definition `K ⊆ k` with `k / K` Galois contains the field of moduli, the field
of moduli is then the smallest field of definition among the subfields over which `k` is Galois
(`TauCeti.AlgebraicBelyiPair.IsoClass.isDefinedOver_iff_fieldOfModuli_le`). Over an infinite
algebraic extension of `ℚ`, such as `AlgebraicClosure ℚ`, the descent here applies to a model of
the pair over a finite Galois extension of the field of moduli, once the isomorphisms `f_σ` are
defined over that extension.

Rigidity is what makes the family `(f_σ)` a cocycle. When `X` has nontrivial automorphisms, the
isomorphisms `f_σ` are determined only up to them, a cocycle need not exist, and there are Belyi
pairs that are not defined over their field of moduli. The model need not be a map from the
projective line over the smaller field, even in genus zero: a Belyi pair over `K` is a function
field over `K`, which can be the function field of a conic without a rational point.

## Main definitions

* `TauCeti.AlgebraicBelyiPair.DescentDatum.ofSubsingleton`: the descent datum of a rigid pair
  whose class is fixed by `Gal(L/K)`.

## Main results

* `TauCeti.AlgebraicBelyiPair.nonempty_model_of_subsingleton`: a rigid pair over `L` whose class is
  fixed by `Gal(L/K)` has a model over `K`.
* `TauCeti.AlgebraicBelyiPair.IsoClass.isDefinedOver_of_fixingSubgroup_le`: a rigid pair over `k`
  is defined over every subfield `K` with `k / K` finite Galois whose automorphism group fixes its
  class.
* `TauCeti.AlgebraicBelyiPair.IsoClass.isDefinedOver_fieldOfModuli`: over a finite extension of
  `ℚ`, a rigid pair is defined over its field of moduli.
* `TauCeti.AlgebraicBelyiPair.IsoClass.isDefinedOver_iff_fieldOfModuli_le`: over a finite extension
  of `ℚ`, a rigid pair is defined over exactly those subfields, among the ones over which the
  extension is Galois, that contain its field of moduli.

## References

* A. Weil, *The field of definition of a variety*, American Journal of Mathematics 78 (1956),
  509–524.
* J.-M. Couveignes, *Calcul et rationalité de fonctions de Belyi en genre 0*, Annales de
  l'Institut Fourier 44 (1994), Théorème 3 (critère de Weil) and Théorème 8.
* B. Köck, *Belyi's theorem revisited*, Beiträge zur Algebra und Geometrie 45 (2004), 253–265,
  (1.9) Theorem.
-/

public section

universe u

namespace TauCeti

namespace AlgebraicBelyiPair

variable {K L : Type u} [Field K] [Field L] [CharZero L] [Algebra K L] {X : AlgebraicBelyiPair L}

/-- Isomorphisms from conjugates onto a rigid pair compose: the isomorphism from the conjugate
along `ρ₂` followed by `ρ₁` is the one from the conjugate along `ρ₂`, conjugated along `ρ₁`, then
followed by the one from the conjugate along `ρ₁`. -/
private theorem apply_conjRingEquiv_eq_of_subsingleton [Subsingleton (X ≃ₐ[RatFunc L] X)]
    {ρ₁ ρ₂ ρ : L ≃+* L} (hρ : ρ₂.trans ρ₁ = ρ) (f₁ : X.conj ρ₁ ≃ₐ[RatFunc L] X)
    (f₂ : X.conj ρ₂ ≃ₐ[RatFunc L] X) (f : X.conj ρ ≃ₐ[RatFunc L] X) (x : X) :
    f (conjRingEquiv ρ X x) = f₁ (conjRingEquiv ρ₁ X (f₂ (conjRingEquiv ρ₂ X x))) := by
  subst hρ
  have := AlgEquiv.subsingleton_of_subsingleton_aut (R := RatFunc L)
    (A := X.conj (ρ₂.trans ρ₁)) (B := X)
  rw [Subsingleton.elim f ((conjTrans ρ₂ X ρ₁).symm.trans ((conjAlgEquiv ρ₁ f₂).trans f₁)),
    ← conjTrans_conjRingEquiv ρ₂ X ρ₁ x]
  simp only [AlgEquiv.trans_apply, AlgEquiv.symm_apply_apply, conjAlgEquiv_conjRingEquiv]

variable (K) in
/-- **The descent datum of a rigid pair.** If an algebraic Belyi pair `X` over `L` has no
nontrivial automorphisms and each `σ ∈ Gal(L/K)` fixes its isomorphism class, then the
isomorphisms `f_σ : X^σ ≃ X` are unique, so they satisfy the cocycle condition and form a descent
datum. -/
noncomputable def DescentDatum.ofSubsingleton [Subsingleton (X ≃ₐ[RatFunc L] X)]
    (h : ∀ σ : L ≃ₐ[K] L, Nonempty (X.conj (σ : L ≃+* L) ≃ₐ[RatFunc L] X)) : DescentDatum K X where
  iso σ := (h σ).some
  iso_mul σ τ :=
    apply_conjRingEquiv_eq_of_subsingleton (AlgEquiv.toRingEquiv_mul σ τ).symm _ _ _

/-- **Rigid pairs descend.** Let `L / K` be a finite Galois extension of fields of characteristic
zero. If an algebraic Belyi pair `X` over `L` has no nontrivial automorphisms and each
`σ ∈ Gal(L/K)` fixes its isomorphism class, then `X` has a model over `K`. -/
theorem nonempty_model_of_subsingleton [CharZero K] [FiniteDimensional K L] [IsGalois K L]
    [Subsingleton (X ≃ₐ[RatFunc L] X)]
    (h : ∀ σ : L ≃ₐ[K] L, Nonempty (X.conj (σ : L ≃+* L) ≃ₐ[RatFunc L] X)) :
    Nonempty (Model K X) := by
  let : Algebra K X := ((algebraMap L X).comp (algebraMap K L)).toAlgebra
  have : IsScalarTower K L X := .of_algebraMap_eq fun _ ↦ rfl
  exact ⟨(DescentDatum.ofSubsingleton K h).model⟩

namespace IsoClass

variable {k : Type u} [Field k] [CharZero k] {X : AlgebraicBelyiPair k}
  [Subsingleton (X ≃ₐ[RatFunc k] X)]

/-- **Rigid pairs are defined over fields fixing their class.** If an algebraic Belyi pair `X` over
`k` has no nontrivial automorphisms, then its class is defined over every subfield `K` of `k` with
`k / K` finite Galois such that the automorphisms of `k` fixing `K` fix the class. -/
theorem isDefinedOver_of_fixingSubgroup_le {K : IntermediateField ℚ k} [FiniteDimensional K k]
    [IsGalois K k] (h : K.fixingSubgroup ≤ MulAction.stabilizer (k ≃ₐ[ℚ] k) (mk X)) :
    (mk X).IsDefinedOver K :=
  isDefinedOver_mk_iff.mpr <| nonempty_model_of_subsingleton fun σ ↦ by
    have hσ : σ.restrictScalars ℚ ∈ K.fixingSubgroup :=
      (IntermediateField.mem_fixingSubgroup_iff K _).mpr fun x hx ↦ σ.commutes ⟨x, hx⟩
    -- `σ.restrictScalars ℚ` has the ring automorphism of `σ`
    -- (`AlgEquiv.toRingEquiv_restrictScalars` is `rfl`), so the conjugates agree.
    exact smul_mk_eq_mk_iff.mp (h hσ)

variable [FiniteDimensional ℚ k]

/-- **A rigid pair is defined over its field of moduli.** Over a finite extension `k` of `ℚ`, an
algebraic Belyi pair with no nontrivial automorphisms is defined over its field of moduli. -/
theorem isDefinedOver_fieldOfModuli : (mk X).IsDefinedOver (mk X).fieldOfModuli :=
  isDefinedOver_of_fixingSubgroup_le (fixingSubgroup_fieldOfModuli _).le

/-- **The field of moduli of a rigid pair is its smallest field of definition over which `k` is
Galois.** Over a finite extension `k` of `ℚ`, an algebraic Belyi pair with no nontrivial
automorphisms is defined over a subfield `K` of `k` over which `k` is Galois exactly when `K`
contains its field of moduli. -/
theorem isDefinedOver_iff_fieldOfModuli_le {K : IntermediateField ℚ k} [IsGalois K k] :
    (mk X).IsDefinedOver K ↔ (mk X).fieldOfModuli ≤ K :=
  ⟨IsDefinedOver.fieldOfModuli_le, fun hK ↦ isDefinedOver_of_fixingSubgroup_le <|
    (IntermediateField.fixingSubgroup_antitone hK).trans (fixingSubgroup_fieldOfModuli _).le⟩

end IsoClass

end AlgebraicBelyiPair

end TauCeti
