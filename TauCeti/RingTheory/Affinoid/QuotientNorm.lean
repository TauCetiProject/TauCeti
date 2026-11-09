/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Ring.Quotient
public import TauCeti.RingTheory.Affinoid.Continuity
public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.ClosedIdeal
public import Mathlib.Topology.Algebra.Algebra.Equiv

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
* `TauCeti.IsAffinoidAlgebra.residueNormedCommRing`: every affinoid algebra carries a complete
  ultrametric algebra norm, transported from the residue algebra of a chosen Tate presentation.

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
homeomorphism for the quotient topology on `A ⧸ ker f`. This is
`ContinuousAlgHom.quotientKerEquivOfSurjective` applied to `f`, which is automatically
continuous. -/
noncomputable def quotientKerContinuousAlgEquiv (hB : IsAffinoidAlgebra K B) (f : A →ₐ[K] B)
    (hf : Function.Surjective f) : (A ⧸ RingHom.ker f) ≃A[K] B :=
  ContinuousAlgHom.quotientKerEquivOfSurjective ⟨f, hB.continuous_algHom f⟩ hf

/-- The first isomorphism theorem sends the class of `a` to `f a`. -/
@[simp]
theorem quotientKerContinuousAlgEquiv_mk (hB : IsAffinoidAlgebra K B) (f : A →ₐ[K] B)
    (hf : Function.Surjective f) (a : A) :
    hB.quotientKerContinuousAlgEquiv f hf (Ideal.Quotient.mk _ a) = f a :=
  ContinuousAlgHom.quotientKerEquivOfSurjective_mk ⟨f, hB.continuous_algHom f⟩ hf a

/-- The underlying algebra isomorphism is the algebraic first isomorphism theorem. -/
@[simp]
theorem toAlgEquiv_quotientKerContinuousAlgEquiv (hB : IsAffinoidAlgebra K B) (f : A →ₐ[K] B)
    (hf : Function.Surjective f) :
    (hB.quotientKerContinuousAlgEquiv f hf).toAlgEquiv =
      Ideal.quotientKerAlgEquivOfSurjective hf :=
  ContinuousAlgHom.toAlgEquiv_quotientKerEquivOfSurjective ⟨f, hB.continuous_algHom f⟩ hf

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

section ResidueNorm

variable {D : Type*} [CommRing D] [Algebra K D] (hD : IsAffinoidAlgebra K D)

/-- The isomorphism of an affinoid algebra `D` with the residue algebra `K⟨X₁, …, Xₙ⟩ ⧸ ker π`
of a chosen Tate presentation `π : K⟨X₁, …, Xₙ⟩ → D`. -/
noncomputable def residueAlgEquiv :
    D ≃ₐ[K] IsRestricted.subring (R := K)
        (fun _ : Fin ((isAffinoidAlgebra_iff K D).mp hD).choose ↦ 1) ⧸
      RingHom.ker ((isAffinoidAlgebra_iff K D).mp hD).choose_spec.choose :=
  (Ideal.quotientKerAlgEquivOfSurjective
    ((isAffinoidAlgebra_iff K D).mp hD).choose_spec.choose_spec).symm

/-- **The residue norm on an affinoid algebra.** The norm `‖x‖ = ‖residueAlgEquiv hD x‖` on `D`,
transported from the quotient Gauss norm of a chosen Tate presentation. It is a complete
ultrametric `K`-algebra norm (`TauCeti.IsAffinoidAlgebra.residueNormedAlgebra`,
`TauCeti.IsAffinoidAlgebra.isUltrametricDist_residueNormedCommRing`,
`TauCeti.IsAffinoidAlgebra.completeSpace_residueNormedCommRing`). It is not an instance, since it
depends on the chosen presentation; all such norms define the same topology
(`TauCeti.IsAffinoidAlgebra.toContinuousAlgEquiv`). -/
noncomputable abbrev residueNormedCommRing : NormedCommRing D :=
  NormedCommRing.induced D _ hD.residueAlgEquiv hD.residueAlgEquiv.injective

/-- The residue norm `TauCeti.IsAffinoidAlgebra.residueNormedCommRing` is a `K`-algebra norm. -/
noncomputable abbrev residueNormedAlgebra :
    letI := hD.residueNormedCommRing
    NormedAlgebra K D :=
  letI := hD.residueNormedCommRing
  NormedAlgebra.induced K D _ hD.residueAlgEquiv

/-- `TauCeti.IsAffinoidAlgebra.residueAlgEquiv` preserves the residue norm. -/
theorem norm_residueAlgEquiv (x : D) :
    letI := hD.residueNormedCommRing
    ‖residueAlgEquiv hD x‖ = ‖x‖ :=
  (rfl)

/-- The residue norm on an affinoid algebra is ultrametric. -/
theorem isUltrametricDist_residueNormedCommRing :
    letI := hD.residueNormedCommRing
    IsUltrametricDist D :=
  letI := hD.residueNormedCommRing
  IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm fun x y ↦ by
    simpa only [← hD.norm_residueAlgEquiv, map_add] using
      IsUltrametricDist.norm_add_le_max (residueAlgEquiv hD x) (residueAlgEquiv hD y)

/-- An affinoid algebra is complete for its residue norm. -/
theorem completeSpace_residueNormedCommRing :
    letI := hD.residueNormedCommRing
    CompleteSpace D :=
  letI := hD.residueNormedCommRing
  let e : D ≃ᵢ _ :=
    { hD.residueAlgEquiv.toEquiv with
      isometry_toFun := AddMonoidHomClass.isometry_of_norm hD.residueAlgEquiv
        hD.norm_residueAlgEquiv }
  e.completeSpace_iff.mpr inferInstance

end ResidueNorm

end TauCeti.IsAffinoidAlgebra
