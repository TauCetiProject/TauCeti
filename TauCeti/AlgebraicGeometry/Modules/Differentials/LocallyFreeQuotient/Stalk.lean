/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.Differentials.LocallyFreeQuotient.Spec
public import TauCeti.AlgebraicGeometry.Modules.AffineGlobalSections
public import TauCeti.AlgebraicGeometry.Scheme.BaseAlgebra
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import TauCeti.RingTheory.Kaehler.SpreadSurjection

/-!
# The stalk criterion for locally free quotients of the differentials, local step

Let `X` be a scheme locally of finite presentation over `Spec k` and `x` a point of `X`. A
surjective `𝒪_{X,x}`-linear map `Ω[𝒪_{X,x}⁄k] → 𝒪_{X,x}^d` spreads out to a neighbourhood of
`x`: there is an open `V ∋ x` such that `Ω_{V/k}` admits a locally free quotient of rank `d`.
This is the local step of the backward direction of the stalk criterion of NashBlowups §0.7; the
global statement glues these local quotients by the uniqueness bullet of §0.7.

On an affine open `U ∋ x`, the stalk `𝒪_{X,x}` is the localization of `A = Γ(X, U)` at the prime
of `x`, so the surjection spreads out to a surjection `Ω[A_s⁄k] → A_s^d` for some `s` not in
that prime (`KaehlerDifferential.exists_notMem_away_surjective`). The basic open `D(s) ∋ x` is
affine with ring of sections `A_s`, and a surjection `Ω[B⁄k] → B^d` for the sections `B` of an
affine open `V` gives a locally free quotient on `V` through `Spec B ≅ V`
(`hasLocallyFreeQuotientOfDifferentials_Spec_of_surjective`).

## Main declarations

* `TauCeti.AlgebraicGeometry.hasLocallyFreeQuotientOfDifferentials_affineOpen_of_surjective`: a
  surjection `Ω[Γ(X, V)⁄k] → Γ(X, V)^d` on an affine open `V` gives a locally free quotient of
  rank `d` of `Ω_{V/k}`.
* `TauCeti.AlgebraicGeometry.exists_mem_hasLocallyFreeQuotientOfDifferentials_of_surjective`: a
  surjection `Ω[𝒪_{X,x}⁄k] → 𝒪_{X,x}^d` gives a locally free quotient of rank `d` of `Ω_{V/k}`
  on an open neighbourhood `V` of `x`.

## References

* The Stacks Project, *Commutative Algebra*, Lemma 10.10.2 (Tag 0583) and Lemma 10.40.5
  (Tag 00L2).
-/

public section

open CategoryTheory Opposite AlgebraicGeometry

namespace TauCeti.AlgebraicGeometry

universe u

noncomputable section

variable {k : Type u} [CommRing k] {X : Scheme.{u}} [X.Over (Spec (.of k))]

/-- **A surjection of the Kähler differentials of an affine open onto a free module gives a
locally free quotient.** For an affine open `V` of a scheme `X` over `Spec k`, with `Γ(X, V)` a
`k`-algebra through the base-ring map, a surjective `Γ(X, V)`-linear map
`Ω[Γ(X, V)⁄k] → Γ(X, V)^d` gives a locally free quotient of rank `d` of `Ω_{V/k}`. -/
theorem hasLocallyFreeQuotientOfDifferentials_affineOpen_of_surjective (V : X.affineOpens)
    {d : ℕ}
    (g : letI : Algebra k Γ(X, V) :=
        ((X.baseRingToStructurePresheaf k).app (op V.val)).hom.toAlgebra
      Ω[Γ(X, V)⁄k] →ₗ[Γ(X, V)] (Fin d → Γ(X, V)))
    (hg : Function.Surjective g) :
    HasLocallyFreeQuotientOfDifferentials k V.val d := by
  let : Algebra k Γ(X, V) := ((X.baseRingToStructurePresheaf k).app (op V.val)).hom.toAlgebra
  have hSpec := hasLocallyFreeQuotientOfDifferentials_Spec_of_surjective k Γ(X, V) g hg
  have hV : IsAffineOpen V.val := V.property
  have e : hV.isoSpec.hom ≫ hV.fromSpec = V.val.ι := by
    rw [← hV.isoSpec_inv_ι, Iso.hom_inv_id_assoc]
  have : hV.isoSpec.hom.IsOver (Spec (.of k)) := by
    have h := isOver_fromSpec k X V
    rw [Scheme.Hom.isOver_iff] at h ⊢
    rw [← h, ← Category.assoc, e]
    rfl
  exact hSpec.of_isOpenImmersion hV.isoSpec.hom

/-- **The stalk criterion, local step.** Let `X` be locally of finite presentation over `Spec k`.
A surjective `𝒪_{X,x}`-linear map `Ω[𝒪_{X,x}⁄k] → 𝒪_{X,x}^d` at a point `x` spreads out: there is
an open neighbourhood `V` of `x` such that `Ω_{V/k}` admits a locally free quotient of rank `d`. -/
theorem exists_mem_hasLocallyFreeQuotientOfDifferentials_of_surjective
    [LocallyOfFinitePresentation (X ↘ Spec (.of k))] {d : ℕ} (x : X)
    (g : Ω[X.presheaf.stalk x⁄k] →ₗ[X.presheaf.stalk x] (Fin d → X.presheaf.stalk x))
    (hg : Function.Surjective g) :
    ∃ V : X.Opens, x ∈ V ∧ HasLocallyFreeQuotientOfDifferentials k V d := by
  obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset (x := x) (U := ⊤) trivial
  let : Algebra k Γ(X, U) := ((X.baseRingToStructurePresheaf k).app (op U)).hom.toAlgebra
  -- `Γ(X, U)` is a finitely presented `k`-algebra.
  have : Algebra.FinitePresentation k Γ(X, U) := by
    let : hU.fromSpec.IsOver (Spec (.of k)) := isOver_fromSpec k X ⟨U, hU⟩
    have hc : LocallyOfFinitePresentation (hU.fromSpec ≫ X ↘ Spec (.of k)) := inferInstance
    rw [HomIsOver.comp_over (f := hU.fromSpec) (S := Spec (.of k))] at hc
    exact RingHom.finitePresentation_algebraMap.mp
      ((LocallyOfFinitePresentation.SpecMap_iff _).mp hc)
  -- The stalk is the localization of `Γ(X, U)` at the prime of `x`, compatibly with `k`.
  let : Algebra Γ(X, U) (X.presheaf.stalk x) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨x, hxU⟩
  have : IsLocalization.AtPrime (X.presheaf.stalk x) (hU.primeIdealOf ⟨x, hxU⟩).asIdeal :=
    hU.isLocalization_stalk ⟨x, hxU⟩
  have : IsScalarTower k Γ(X, U) (X.presheaf.stalk x) :=
    Scheme.isScalarTower_base_section_stalk k X ⟨x, hxU⟩
  obtain ⟨s, hs, h⟩ := KaehlerDifferential.exists_notMem_away_surjective
    (hU.primeIdealOf ⟨x, hxU⟩).asIdeal (X.presheaf.stalk x) g hg
  -- The basic open `D(s)` is affine, with sections the localization of `Γ(X, U)` at `s`.
  let V : X.affineOpens := ⟨X.basicOpen s, hU.basicOpen s⟩
  let : Algebra k Γ(X, V) := ((X.baseRingToStructurePresheaf k).app (op V.val)).hom.toAlgebra
  have : IsLocalization.Away s Γ(X, X.basicOpen s) := hU.isLocalization_basicOpen s
  have : IsScalarTower k Γ(X, U) Γ(X, X.basicOpen s) := by
    refine IsScalarTower.of_algebraMap_eq fun r ↦ ?_
    change ((X.baseRingToStructurePresheaf k).app (op V.val)) r =
      X.presheaf.map (homOfLE (X.basicOpen_le s)).op
        (((X.baseRingToStructurePresheaf k).app (op U)) r)
    rw [← CommRingCat.comp_apply, ← (X.baseRingToStructurePresheaf k).naturality]
    rfl
  obtain ⟨g', hg'⟩ := h Γ(X, X.basicOpen s)
  refine ⟨X.basicOpen s, ?_,
    hasLocallyFreeQuotientOfDifferentials_affineOpen_of_surjective V g' hg'⟩
  rw [Scheme.mem_basicOpen' X s ⟨x, hxU⟩]
  exact (IsLocalization.AtPrime.isUnit_to_map_iff (X.presheaf.stalk x) _ s).mpr hs

end

end TauCeti.AlgebraicGeometry
