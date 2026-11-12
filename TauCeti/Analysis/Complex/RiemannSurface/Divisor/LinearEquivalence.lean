/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.RiemannSurface.Divisor.Cohomology
public import TauCeti.Analysis.Complex.RiemannSurface.Divisor.Trivialization
public import TauCeti.Analysis.Complex.RiemannSurface.FunctionField.Order

/-!
# Divisor sheaves of linearly equivalent divisors

Let `X` be a compact connected Riemann surface and `f` a nonzero meromorphic function on `X`,
with principal divisor `(f)`. Multiplication by `f` sends a meromorphic function `s` with
`(s) ≥ -D` to `f s`, whose divisor is at least `-(D - (f))`. This identifies the divisor sheaves
`𝒪(D) ≅ 𝒪(D - (f))` as sheaves of complex vector spaces, so linearly equivalent divisors have
isomorphic divisor sheaves, and hence isomorphic Čech cohomology in every degree.

The isomorphism is multiplication by the finite part of `f`, followed by the normalization of
divisor sections (filling removable singularities and fixing the values at allowed poles). In
degree `0`, under the identification of `H⁰` with global sections, the induced isomorphism is
that multiplication on global sections.

Consequently `h⁰` and `h¹` of a divisor sheaf depend only on the linear equivalence class of the
divisor, and so does finite-dimensionality of each cohomology group. These are the
isomorphism-invariance statements consumed by Riemann–Roch for `𝒪(K - D)` and by Serre duality.

## Main definitions

* `TauCeti.RiemannSurface.divisorSheafIsoOfPrincipalDivisorEq`: if `(f) = D - E`, then
  multiplication by `f` gives `𝒪(D) ≅ 𝒪(E)`.
* `TauCeti.RiemannSurface.divisorSheafIsoSubPrincipalDivisor`: `𝒪(D) ≅ 𝒪(D - (f))`.
* `TauCeti.RiemannSurface.divisorSheafIsoOfLinearlyEquivalent`: `𝒪(D) ≅ 𝒪(E)` for linearly
  equivalent `D` and `E`.
* `TauCeti.RiemannSurface.divisorCechCohomologyIsoOfPrincipalDivisorEq` and
  `TauCeti.RiemannSurface.divisorCechCohomologyIsoOfLinearlyEquivalent`: the induced
  isomorphisms `Hⁿ(X, 𝒪(D)) ≅ Hⁿ(X, 𝒪(E))`.

## Main results

* `cechCohomologyZeroIso_hom_comp_divisorCechCohomologyIsoOfPrincipalDivisorEq_hom`: in degree
  `0` the isomorphism is multiplication by `f` on global sections.
* `TauCeti.RiemannSurface.finrank_divisorCechCohomology_eq_of_linearlyEquivalent` and
  `TauCeti.RiemannSurface.finiteDimensional_divisorCechCohomology_iff_of_linearlyEquivalent`.

## References

* Otto Forster, *Lectures on Riemann Surfaces*, Graduate Texts in Mathematics 81, Springer, 1981,
  §16 (the sheaves `𝒪_D`, and `𝒪_D ≅ 𝒪_D'` for equivalent divisors).
-/

public noncomputable section

open CategoryTheory Filter OnePoint Opposite TopologicalSpace Topology
open TauCeti.Topology
open scoped Manifold

namespace TauCeti.RiemannSurface

open TauCeti.AlgebraicGeometry (WeilDivisor)
open TauCeti.AlgebraicGeometry.WeilDivisor (OrderSystem)

universe u

section Sheaf

variable {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]
  [ConnectedSpace X] [CompactSpace X]

/-- The order of the finite part of a nonzero meromorphic function is the coefficient of its
principal divisor. -/
private theorem meromorphicOrderAt_finitePart_eq {D E : WeilDivisor X}
    (f : Additive (MeromorphicFunction X)ˣ)
    (hf : (MeromorphicFunction.orderSystem X).principalDivisor f = D - E) (x : X) :
    meromorphicOrderAt (f.toMul : MeromorphicFunction X).finitePart x =
      ((D x - E x : ℤ) : WithTop ℤ) := by
  rw [← MeromorphicFunction.order_apply,
    ← MeromorphicFunction.coe_coeff_principalDivisor_orderSystem, hf, WeilDivisor.coeff,
    Finsupp.sub_apply]

/-- If the principal divisor of `f` is `D - E`, multiplication by `f` identifies the divisor
sheaves `𝒪(D) ≅ 𝒪(E)`. Sections are normalized after multiplication. -/
def divisorSheafIsoOfPrincipalDivisorEq {D E : WeilDivisor X}
    (f : Additive (MeromorphicFunction X)ˣ)
    (hf : (MeromorphicFunction.orderSystem X).principalDivisor f = D - E) :
    divisorSheaf D ≅ divisorSheaf E :=
  divisorSheafGlobalMulIso D E (f.toMul : MeromorphicFunction X).finitePart
    (fun x ↦ (f.toMul : MeromorphicFunction X).meromorphicAt_finitePart x)
    (meromorphicOrderAt_finitePart_eq f hf)

/-- `divisorSheafIsoOfPrincipalDivisorEq` multiplies a section by the finite part of `f`, fills
removable singularities and sets the values at the allowed poles of `E` to zero. -/
theorem divisorSheafIsoOfPrincipalDivisorEq_hom_app {D E : WeilDivisor X}
    (f : Additive (MeromorphicFunction X)ˣ)
    (hf : (MeromorphicFunction.orderSystem X).principalDivisor f = D - E) (U : Opens X)
    (s : (divisorSheaf D).obj.obj (op U)) :
    (divisorSheafSectionsEquiv E U
        ((divisorSheafIsoOfPrincipalDivisorEq f hf).hom.hom.app (op U) s)).1 =
      fun y : U ↦ if E y ≤ 0 then affineChart (sphereMap
        ((f.toMul : MeromorphicFunction X).finitePart *
          Subtype.val.extend (divisorSheafSectionsEquiv D U s).1 0) y) else 0 :=
  divisorSheafGlobalMulIso_hom_app _ _ _ U s

/-- On a punctured neighbourhood of each point, `divisorSheafIsoOfPrincipalDivisorEq` sends a
section `s` of `𝒪(D)` to `f s`. -/
theorem divisorSheafIsoOfPrincipalDivisorEq_hom_app_eventuallyEq {D E : WeilDivisor X}
    (f : Additive (MeromorphicFunction X)ˣ)
    (hf : (MeromorphicFunction.orderSystem X).principalDivisor f = D - E) (U : Opens X)
    (s : (divisorSheaf D).obj.obj (op U)) (x : U) :
    (divisorSheafSectionsEquiv E U
        ((divisorSheafIsoOfPrincipalDivisorEq f hf).hom.hom.app (op U) s)).1 =ᶠ[𝓝[≠] x]
      fun y ↦ (f.toMul : MeromorphicFunction X).finitePart y *
        (divisorSheafSectionsEquiv D U s).1 y :=
  divisorSheafGlobalMulIso_hom_app_eventuallyEq _ _ _ U s x

/-- The inverse of `divisorSheafIsoOfPrincipalDivisorEq` is multiplication by the reciprocal of
the finite part of `f`, followed by normalization. -/
theorem divisorSheafIsoOfPrincipalDivisorEq_inv_app {D E : WeilDivisor X}
    (f : Additive (MeromorphicFunction X)ˣ)
    (hf : (MeromorphicFunction.orderSystem X).principalDivisor f = D - E) (U : Opens X)
    (s : (divisorSheaf E).obj.obj (op U)) :
    (divisorSheafSectionsEquiv D U
        ((divisorSheafIsoOfPrincipalDivisorEq f hf).inv.hom.app (op U) s)).1 =
      fun y : U ↦ if D y ≤ 0 then affineChart (sphereMap
        ((f.toMul : MeromorphicFunction X).finitePart⁻¹ *
          Subtype.val.extend (divisorSheafSectionsEquiv E U s).1 0) y) else 0 :=
  divisorSheafGlobalMulIso_inv_app _ _ _ U s

/-- **`𝒪(D) ≅ 𝒪(D - (f))`.** Multiplication by a nonzero meromorphic function `f` identifies
the divisor sheaf of `D` with that of `D` minus the principal divisor of `f`. -/
def divisorSheafIsoSubPrincipalDivisor (D : WeilDivisor X)
    (f : Additive (MeromorphicFunction X)ˣ) :
    divisorSheaf D ≅
      divisorSheaf (D - (MeromorphicFunction.orderSystem X).principalDivisor f) :=
  divisorSheafIsoOfPrincipalDivisorEq f (sub_sub_cancel D _).symm

/-- **Linearly equivalent divisors have isomorphic divisor sheaves.** The isomorphism is
multiplication by a chosen meromorphic function whose principal divisor is `D - E`. -/
def divisorSheafIsoOfLinearlyEquivalent {D E : WeilDivisor X}
    (h : (MeromorphicFunction.orderSystem X).LinearlyEquivalent D E) :
    divisorSheaf D ≅ divisorSheaf E :=
  divisorSheafIsoOfPrincipalDivisorEq _
    ((OrderSystem.linearlyEquivalent_iff_exists_principalDivisor _).mp h).choose_spec

/-- `divisorSheafIsoOfLinearlyEquivalent` is multiplication by a meromorphic function whose
principal divisor is `D - E`. -/
theorem exists_divisorSheafIsoOfLinearlyEquivalent_eq {D E : WeilDivisor X}
    (h : (MeromorphicFunction.orderSystem X).LinearlyEquivalent D E) :
    ∃ (f : Additive (MeromorphicFunction X)ˣ)
      (hf : (MeromorphicFunction.orderSystem X).principalDivisor f = D - E),
      divisorSheafIsoOfLinearlyEquivalent h = divisorSheafIsoOfPrincipalDivisorEq f hf :=
  ⟨_, _, rfl⟩

/-- Linearly equivalent divisors have global section spaces of the same dimension. -/
theorem finrank_divisorSheaf_globalSections_eq_of_linearlyEquivalent {D E : WeilDivisor X}
    (h : (MeromorphicFunction.orderSystem X).LinearlyEquivalent D E) :
    Module.finrank ℂ ((divisorSheaf D).obj.obj (op ⊤)) =
      Module.finrank ℂ ((divisorSheaf E).obj.obj (op ⊤)) :=
  (((sheafToPresheaf _ _).mapIso (divisorSheafIsoOfLinearlyEquivalent h)).app
    (op ⊤)).toLinearEquiv.finrank_eq

end Sheaf

section Cohomology

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]
  [ConnectedSpace X] [CompactSpace X]

/-- If the principal divisor of `f` is `D - E`, multiplication by `f` induces
`Hⁿ(X, 𝒪(D)) ≅ Hⁿ(X, 𝒪(E))` on Čech cohomology in every degree. -/
def divisorCechCohomologyIsoOfPrincipalDivisorEq {D E : WeilDivisor X}
    (f : Additive (MeromorphicFunction X)ˣ)
    (hf : (MeromorphicFunction.orderSystem X).principalDivisor f = D - E) (n : ℕ) :
    divisorCechCohomology D n ≅ divisorCechCohomology E n :=
  (cechCohomology (TopCat.of X) (ModuleCat.{0} ℂ) n).mapIso
    ((sheafToPresheaf _ _).mapIso (divisorSheafIsoOfPrincipalDivisorEq f hf))

/-- The cohomology isomorphism is induced by the multiplication isomorphism of sheaves. -/
@[simp]
theorem divisorCechCohomologyIsoOfPrincipalDivisorEq_hom {D E : WeilDivisor X}
    (f : Additive (MeromorphicFunction X)ˣ)
    (hf : (MeromorphicFunction.orderSystem X).principalDivisor f = D - E) (n : ℕ) :
    (divisorCechCohomologyIsoOfPrincipalDivisorEq f hf n).hom =
      (cechCohomology (TopCat.of X) (ModuleCat.{0} ℂ) n).map
        (divisorSheafIsoOfPrincipalDivisorEq f hf).hom.hom :=
  (rfl)

/-- The inverse cohomology isomorphism is induced by the inverse multiplication isomorphism. -/
@[simp]
theorem divisorCechCohomologyIsoOfPrincipalDivisorEq_inv {D E : WeilDivisor X}
    (f : Additive (MeromorphicFunction X)ˣ)
    (hf : (MeromorphicFunction.orderSystem X).principalDivisor f = D - E) (n : ℕ) :
    (divisorCechCohomologyIsoOfPrincipalDivisorEq f hf n).inv =
      (cechCohomology (TopCat.of X) (ModuleCat.{0} ℂ) n).map
        (divisorSheafIsoOfPrincipalDivisorEq f hf).inv.hom :=
  (rfl)

/-- **In degree `0` the isomorphism is multiplication by `f` on global sections.** Identifying
`H⁰` of each divisor sheaf with its global sections, the isomorphism
`H⁰(X, 𝒪(D)) ≅ H⁰(X, 𝒪(E))` is the multiplication map `s ↦ f s` of global sections. -/
@[reassoc]
theorem cechCohomologyZeroIso_hom_comp_divisorCechCohomologyIsoOfPrincipalDivisorEq_hom
    {D E : WeilDivisor X} (f : Additive (MeromorphicFunction X)ˣ)
    (hf : (MeromorphicFunction.orderSystem X).principalDivisor f = D - E) :
    (cechCohomologyZeroIso (divisorSheaf D)).hom ≫
        (divisorCechCohomologyIsoOfPrincipalDivisorEq f hf 0).hom =
      (divisorSheafIsoOfPrincipalDivisorEq f hf).hom.hom.app (op ⊤) ≫
        (cechCohomologyZeroIso (divisorSheaf E)).hom :=
  (cechCohomologyZeroIso_hom_naturality _ _).symm

/-- **Linearly equivalent divisors have isomorphic Čech cohomology** in every degree, through
the multiplication isomorphism of divisor sheaves. -/
def divisorCechCohomologyIsoOfLinearlyEquivalent {D E : WeilDivisor X}
    (h : (MeromorphicFunction.orderSystem X).LinearlyEquivalent D E) (n : ℕ) :
    divisorCechCohomology D n ≅ divisorCechCohomology E n :=
  divisorCechCohomologyIsoOfPrincipalDivisorEq _
    ((OrderSystem.linearlyEquivalent_iff_exists_principalDivisor _).mp h).choose_spec n

/-- The cohomology isomorphism of linearly equivalent divisors is induced by the sheaf
isomorphism. -/
@[simp]
theorem divisorCechCohomologyIsoOfLinearlyEquivalent_hom {D E : WeilDivisor X}
    (h : (MeromorphicFunction.orderSystem X).LinearlyEquivalent D E) (n : ℕ) :
    (divisorCechCohomologyIsoOfLinearlyEquivalent h n).hom =
      (cechCohomology (TopCat.of X) (ModuleCat.{0} ℂ) n).map
        (divisorSheafIsoOfLinearlyEquivalent h).hom.hom :=
  divisorCechCohomologyIsoOfPrincipalDivisorEq_hom _ _ n

/-- The inverse cohomology isomorphism of linearly equivalent divisors is induced by the inverse
sheaf isomorphism. -/
@[simp]
theorem divisorCechCohomologyIsoOfLinearlyEquivalent_inv {D E : WeilDivisor X}
    (h : (MeromorphicFunction.orderSystem X).LinearlyEquivalent D E) (n : ℕ) :
    (divisorCechCohomologyIsoOfLinearlyEquivalent h n).inv =
      (cechCohomology (TopCat.of X) (ModuleCat.{0} ℂ) n).map
        (divisorSheafIsoOfLinearlyEquivalent h).inv.hom :=
  divisorCechCohomologyIsoOfPrincipalDivisorEq_inv _ _ n

/-- In degree `0` the cohomology isomorphism of linearly equivalent divisors is the sheaf
isomorphism on global sections. -/
@[reassoc]
theorem cechCohomologyZeroIso_hom_comp_divisorCechCohomologyIsoOfLinearlyEquivalent_hom
    {D E : WeilDivisor X} (h : (MeromorphicFunction.orderSystem X).LinearlyEquivalent D E) :
    (cechCohomologyZeroIso (divisorSheaf D)).hom ≫
        (divisorCechCohomologyIsoOfLinearlyEquivalent h 0).hom =
      (divisorSheafIsoOfLinearlyEquivalent h).hom.hom.app (op ⊤) ≫
        (cechCohomologyZeroIso (divisorSheaf E)).hom :=
  cechCohomologyZeroIso_hom_comp_divisorCechCohomologyIsoOfPrincipalDivisorEq_hom _ _

/-- Linearly equivalent divisors have Čech cohomology of the same dimension in every degree.
For infinite-dimensional cohomology both sides are `0`; finiteness is not assumed. -/
theorem finrank_divisorCechCohomology_eq_of_linearlyEquivalent {D E : WeilDivisor X}
    (h : (MeromorphicFunction.orderSystem X).LinearlyEquivalent D E) (n : ℕ) :
    Module.finrank ℂ (divisorCechCohomology D n) =
      Module.finrank ℂ (divisorCechCohomology E n) :=
  (divisorCechCohomologyIsoOfLinearlyEquivalent h n).toLinearEquiv.finrank_eq

/-- Finite-dimensionality of each Čech cohomology group of a divisor sheaf depends only on the
linear equivalence class of the divisor. -/
theorem finiteDimensional_divisorCechCohomology_iff_of_linearlyEquivalent {D E : WeilDivisor X}
    (h : (MeromorphicFunction.orderSystem X).LinearlyEquivalent D E) (n : ℕ) :
    FiniteDimensional ℂ (divisorCechCohomology D n) ↔
      FiniteDimensional ℂ (divisorCechCohomology E n) :=
  ⟨fun _ ↦ (divisorCechCohomologyIsoOfLinearlyEquivalent h n).toLinearEquiv.finiteDimensional,
    fun _ ↦ (divisorCechCohomologyIsoOfLinearlyEquivalent h n).toLinearEquiv.symm.finiteDimensional⟩

end Cohomology

end TauCeti.RiemannSurface
