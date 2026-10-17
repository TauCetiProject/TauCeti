/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Affinoid.Continuity
public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.ClosedIdeal
public import Mathlib.Topology.Algebra.Algebra.Equiv

import TauCeti.Topology.Algebra.Ring.Ideal

/-!
# Quotient norms and the topology of affinoid algebras

A Tate presentation `π : K⟨X₁, …, Xₙ⟩ → A` of an affinoid algebra gives the residue algebra
`K⟨X₁, …, Xₙ⟩ ⧸ ker π` its quotient Gauss norm, a complete ultrametric algebra norm (the
instances are assembled in `TauCeti.RingTheory.MvPowerSeries.TateAlgebra.ClosedIdeal`). This file
proves that the resulting topology does not depend on the presentation, and more generally that
the topology of an affinoid algebra carrying any complete ultrametric algebra norm is determined
by its algebra structure.

All statements follow from automatic continuity, `TauCeti.IsAffinoidAlgebra.continuous_algHom`,
and the Banach open mapping theorem. Equivalent norms need not be equal or isometric.

## Main results

* `TauCeti.IsAffinoidAlgebra.isOpenQuotientMap`: a surjective algebra homomorphism from a
  noetherian ultrametric Banach algebra onto a completely normed affinoid algebra is an open
  quotient map, so the target carries the quotient topology.
* `TauCeti.IsAffinoidAlgebra.quotientKerContinuousAlgEquiv`: for such a surjection `f : A → B`,
  the first isomorphism theorem `A ⧸ ker f ≃ B` is a homeomorphism.
* `TauCeti.IsAffinoidAlgebra.toContinuousAlgEquiv`: every algebra isomorphism between completely
  normed affinoid algebras is a homeomorphism; in particular complete ultrametric algebra norms on
  an affinoid algebra are equivalent.
* `TauCeti.IsAffinoidAlgebra.presentationContinuousAlgEquiv`: two Tate presentations of the same
  algebra give homeomorphic residue algebras for their quotient Gauss norms.

## References

* [Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*][bosch-guntzer-remmert],
  §§2.8.1 and 6.1.3.
-/

public section

namespace TauCeti.IsAffinoidAlgebra

open _root_.MvPowerSeries Topology

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
    {A : Type*} [NormedCommRing A] [NormedAlgebra K A] [IsUltrametricDist A] [CompleteSpace A]
    {B : Type*} [NormedCommRing B] [NormedAlgebra K B] [IsUltrametricDist B] [CompleteSpace B]

section Surjective

variable [IsNoetherianRing A]

/-- A surjective algebra homomorphism from a noetherian ultrametric Banach algebra onto a
completely normed affinoid algebra is an open quotient map, so the target carries the quotient
topology induced by the homomorphism. -/
theorem isOpenQuotientMap (hB : IsAffinoidAlgebra K B) (f : A →ₐ[K] B)
    (hf : Function.Surjective f) : IsOpenQuotientMap f :=
  let g : A →L[K] B := ⟨f.toLinearMap, hB.continuous_algHom f⟩
  ⟨hf, g.continuous, g.isOpenMap hf⟩

/-- For a surjective algebra homomorphism `f` from a noetherian ultrametric Banach algebra onto a
completely normed affinoid algebra, the algebraic first isomorphism theorem `A ⧸ ker f ≃ B` is a
homeomorphism for the quotient topology on `A ⧸ ker f`. -/
noncomputable def quotientKerContinuousAlgEquiv (hB : IsAffinoidAlgebra K B) (f : A →ₐ[K] B)
    (hf : Function.Surjective f) : (A ⧸ RingHom.ker f) ≃A[K] B :=
  let e := Ideal.quotientKerAlgEquivOfSurjective hf
  have he : (e : A ⧸ RingHom.ker f → B) = RingHom.kerLift (f : A →+* B) := by
    funext x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [Ideal.quotientKerAlgEquivOfSurjective_mk]
    exact (RingHom.kerLift_mk (f : A →+* B) a).symm
  have h : IsHomeomorph e := he ▸
    RingHom.isHomeomorph_kerLift (hB.isOpenQuotientMap f hf).isQuotientMap
  { e with
    continuous_toFun := h.continuous
    continuous_invFun :=
      (e.toEquiv.toHomeomorphOfContinuousOpen h.continuous h.isOpenMap).symm.continuous }

/-- The first isomorphism theorem sends the class of `a` to `f a`. -/
@[simp]
theorem quotientKerContinuousAlgEquiv_mk (hB : IsAffinoidAlgebra K B) (f : A →ₐ[K] B)
    (hf : Function.Surjective f) (a : A) :
    hB.quotientKerContinuousAlgEquiv f hf (Ideal.Quotient.mk _ a) = f a := (rfl)

/-- The underlying algebra isomorphism is the algebraic first isomorphism theorem. -/
@[simp]
theorem toAlgEquiv_quotientKerContinuousAlgEquiv (hB : IsAffinoidAlgebra K B) (f : A →ₐ[K] B)
    (hf : Function.Surjective f) :
    (hB.quotientKerContinuousAlgEquiv f hf).toAlgEquiv =
      Ideal.quotientKerAlgEquivOfSurjective hf := (rfl)

end Surjective

/-- **Equivalence of complete affinoid norms.** An algebra isomorphism between completely normed
affinoid algebras is a homeomorphism, whatever complete ultrametric algebra norms they carry.
Applied to two such norms on one algebra, this says that they define the same topology. -/
noncomputable def toContinuousAlgEquiv (hB : IsAffinoidAlgebra K B) (e : A ≃ₐ[K] B) :
    A ≃A[K] B :=
  have hA : IsAffinoidAlgebra K A := hB.of_surjective e.symm.toAlgHom e.symm.surjective
  have := hA.isNoetherianRing
  have := hB.isNoetherianRing
  { e with
    continuous_toFun := hB.continuous_algHom e.toAlgHom
    continuous_invFun := hA.continuous_algHom e.symm.toAlgHom }

/-- The homeomorphism attached to an algebra isomorphism has the same underlying function. -/
@[simp]
theorem coe_toContinuousAlgEquiv (hB : IsAffinoidAlgebra K B) (e : A ≃ₐ[K] B) :
    ⇑(hB.toContinuousAlgEquiv e) = e := (rfl)

/-- The homeomorphism attached to an algebra isomorphism has that isomorphism as its underlying
algebra isomorphism. -/
@[simp]
theorem toAlgEquiv_toContinuousAlgEquiv (hB : IsAffinoidAlgebra K B) (e : A ≃ₐ[K] B) :
    (hB.toContinuousAlgEquiv e).toAlgEquiv = e := (rfl)

section Presentation

local notation "Tate " σ:max => IsRestricted.subring (R := K) (fun _ : σ ↦ 1)

/-- **Independence of presentation.** Two Tate presentations of the same algebra give residue
algebras whose quotient Gauss norms define the same topology: the canonical algebra isomorphism
between them, compatible with both presentations, is a homeomorphism. -/
noncomputable def presentationContinuousAlgEquiv {σ τ : Type*} [Finite σ] [Finite τ]
    {C : Type*} [CommRing C] [Algebra K C] (π₁ : Tate σ →ₐ[K] C) (hπ₁ : Function.Surjective π₁)
    (π₂ : Tate τ →ₐ[K] C) (hπ₂ : Function.Surjective π₂) :
    (Tate σ ⧸ RingHom.ker π₁) ≃A[K] (Tate τ ⧸ RingHom.ker π₂) :=
  toContinuousAlgEquiv (K := K) (A := Tate σ ⧸ RingHom.ker π₁) (B := Tate τ ⧸ RingHom.ker π₂)
    (isAffinoidAlgebra_tate.quotient _) ((Ideal.quotientKerAlgEquivOfSurjective hπ₁).trans
      (Ideal.quotientKerAlgEquivOfSurjective hπ₂).symm)

/-- The presentation comparison is characterized by compatibility with both presentations. -/
@[simp]
theorem kerLiftAlg_presentationContinuousAlgEquiv {σ τ : Type*} [Finite σ] [Finite τ]
    {C : Type*} [CommRing C] [Algebra K C] (π₁ : Tate σ →ₐ[K] C) (hπ₁ : Function.Surjective π₁)
    (π₂ : Tate τ →ₐ[K] C) (hπ₂ : Function.Surjective π₂) (x : Tate σ ⧸ RingHom.ker π₁) :
    Ideal.kerLiftAlg π₂ (presentationContinuousAlgEquiv π₁ hπ₁ π₂ hπ₂ x) =
      Ideal.kerLiftAlg π₁ x :=
by
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨g, hg⟩ := hπ₂ (π₁ f)
  simp [presentationContinuousAlgEquiv, ← hg]

end Presentation

end TauCeti.IsAffinoidAlgebra
