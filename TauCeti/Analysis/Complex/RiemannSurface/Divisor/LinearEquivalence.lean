/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.RiemannSurface.Divisor.Cohomology.Basic
public import TauCeti.Analysis.Complex.RiemannSurface.Divisor.Meromorphic
public import TauCeti.Analysis.Complex.RiemannSurface.Divisor.Trivialization
public import TauCeti.Analysis.Complex.RiemannSurface.FunctionField.Order
import TauCeti.Topology.ContinuousOn.PuncturedNhds

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

More generally, a meromorphic function `g` whose order is at least `D - E` everywhere gives a
morphism `𝒪(D) ⟶ 𝒪(E)`, for example `𝒪(D) ⟶ 𝒪(D + P)` when `P` is effective and `(g) ≥ -P`. It is
additive in `g`, is `c` times the inclusion for a constant `c`, commutes with the inclusions
`𝒪(D) ⟶ 𝒪(D')`, and for `g ≠ 0` is the isomorphism `𝒪(D) ≅ 𝒪(D - (g))` followed by an
inclusion. These are the multiplication maps of the proof that every class in `H¹(X, 𝒪(D))`
comes from a Mittag-Leffler distribution (Forster, Theorem 17.3).

Consequently `h⁰` and `h¹` of a divisor sheaf depend only on the linear equivalence class of the
divisor, and so does finite-dimensionality of each cohomology group. These are the
isomorphism-invariance statements consumed by Riemann–Roch for `𝒪(K - D)` and by Serre duality.

## Main definitions

* `TauCeti.RiemannSurface.divisorSheafIsoOfPrincipalDivisorEq`: if `(f) = D - E`, then
  multiplication by `f` gives `𝒪(D) ≅ 𝒪(E)`.
* `TauCeti.RiemannSurface.divisorSheafIsoSubPrincipalDivisor`: `𝒪(D) ≅ 𝒪(D - (f))`.
* `TauCeti.RiemannSurface.divisorSheafIsoOfLinearlyEquivalent`: `𝒪(D) ≅ 𝒪(E)` for linearly
  equivalent `D` and `E`.
* `TauCeti.RiemannSurface.divisorSheafMeromorphicMul`: multiplication by a meromorphic function
  `g` whose order is at least `D - E`, as a morphism `𝒪(D) ⟶ 𝒪(E)`.
* `TauCeti.RiemannSurface.divisorCechCohomologyIsoOfPrincipalDivisorEq` and
  `TauCeti.RiemannSurface.divisorCechCohomologyIsoOfLinearlyEquivalent`: the induced
  isomorphisms `Hⁿ(X, 𝒪(D)) ≅ Hⁿ(X, 𝒪(E))`.

## Main results

* `TauCeti.RiemannSurface.divisorSheafIsoOfPrincipalDivisorEq_zero`,
  `TauCeti.RiemannSurface.divisorSheafIsoOfPrincipalDivisorEq_symm` and
  `TauCeti.RiemannSurface.divisorSheafIsoOfPrincipalDivisorEq_trans`: the isomorphism is the
  identity for `f = 1`, and is compatible with inverses and products of multipliers.
* `TauCeti.RiemannSurface.toMeromorphic_divisorSheafIsoOfPrincipalDivisorEq_hom_app_top`: on
  global sections, viewed as meromorphic functions, the isomorphism is multiplication by `f`.
* `TauCeti.RiemannSurface.divisorSheafMeromorphicMul_add`,
  `divisorSheafMeromorphicMul_comp`, `divisorSheafMeromorphicMul_algebraMap_hom`,
  `divisorSheafMapOfLE_comp_divisorSheafMeromorphicMul` and
  `divisorSheafMeromorphicMul_comp_divisorSheafMapOfLE`: multiplication is additive in the
  multiplier, takes products to composites, is `c` times the inclusion for a constant `c`, and
  commutes with the inclusions of divisor sheaves.
* `TauCeti.RiemannSurface.divisorSheafIsoOfPrincipalDivisorEq_hom_comp_divisorSheafMapOfLE`:
  multiplication by a nonzero `f` is the isomorphism `𝒪(D) ≅ 𝒪(D - (f))` followed by an
  inclusion.
* `cechCohomologyZeroIso_hom_comp_divisorCechCohomologyIsoOfPrincipalDivisorEq_hom`: in degree
  `0` the isomorphism is multiplication by `f` on global sections.
* `TauCeti.RiemannSurface.finrank_divisorCechCohomology_eq_of_linearlyEquivalent` and
  `TauCeti.RiemannSurface.finiteDimensional_divisorCechCohomology_iff_of_linearlyEquivalent`.

## References

* Otto Forster, *Lectures on Riemann Surfaces*, Graduate Texts in Mathematics 81, Springer, 1981,
  §16 (the sheaves `𝒪_D`, and `𝒪_D ≅ 𝒪_D'` for equivalent divisors) and the proof of Theorem 17.3
  (multiplication maps `𝒪_D ⟶ 𝒪_{D + P}`).
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
        ((divisorSheafIsoOfPrincipalDivisorEq f hf).hom.hom.app (op U) s)).val =
      fun y : U ↦ if E y ≤ 0 then affineChart (sphereMap
        ((f.toMul : MeromorphicFunction X).finitePart *
          Subtype.val.extend (divisorSheafSectionsEquiv D U s).val 0) y) else 0 :=
  divisorSheafGlobalMulIso_hom_app _ _ _ U s

/-- On a punctured neighbourhood of each point, `divisorSheafIsoOfPrincipalDivisorEq` sends a
section `s` of `𝒪(D)` to `f s`. -/
theorem divisorSheafIsoOfPrincipalDivisorEq_hom_app_eventuallyEq {D E : WeilDivisor X}
    (f : Additive (MeromorphicFunction X)ˣ)
    (hf : (MeromorphicFunction.orderSystem X).principalDivisor f = D - E) (U : Opens X)
    (s : (divisorSheaf D).obj.obj (op U)) (x : U) :
    (divisorSheafSectionsEquiv E U
        ((divisorSheafIsoOfPrincipalDivisorEq f hf).hom.hom.app (op U) s)).val =ᶠ[𝓝[≠] x]
      fun y ↦ (f.toMul : MeromorphicFunction X).finitePart y *
        (divisorSheafSectionsEquiv D U s).val y :=
  divisorSheafGlobalMulIso_hom_app_eventuallyEq _ _ _ U s x

/-- The inverse of `divisorSheafIsoOfPrincipalDivisorEq` is multiplication by the reciprocal of
the finite part of `f`, followed by normalization. -/
theorem divisorSheafIsoOfPrincipalDivisorEq_inv_app {D E : WeilDivisor X}
    (f : Additive (MeromorphicFunction X)ˣ)
    (hf : (MeromorphicFunction.orderSystem X).principalDivisor f = D - E) (U : Opens X)
    (s : (divisorSheaf E).obj.obj (op U)) :
    (divisorSheafSectionsEquiv D U
        ((divisorSheafIsoOfPrincipalDivisorEq f hf).inv.hom.app (op U) s)).val =
      fun y : U ↦ if D y ≤ 0 then affineChart (sphereMap
        ((f.toMul : MeromorphicFunction X).finitePart⁻¹ *
          Subtype.val.extend (divisorSheafSectionsEquiv E U s).val 0) y) else 0 :=
  divisorSheafGlobalMulIso_inv_app _ _ _ U s

/-- On a punctured neighbourhood of each point, the inverse of
`divisorSheafIsoOfPrincipalDivisorEq` sends a section `s` of `𝒪(E)` to `f⁻¹ s`. -/
theorem divisorSheafIsoOfPrincipalDivisorEq_inv_app_eventuallyEq {D E : WeilDivisor X}
    (f : Additive (MeromorphicFunction X)ˣ)
    (hf : (MeromorphicFunction.orderSystem X).principalDivisor f = D - E) (U : Opens X)
    (s : (divisorSheaf E).obj.obj (op U)) (x : U) :
    (divisorSheafSectionsEquiv D U
        ((divisorSheafIsoOfPrincipalDivisorEq f hf).inv.hom.app (op U) s)).val =ᶠ[𝓝[≠] x]
      fun y ↦ ((f.toMul : MeromorphicFunction X).finitePart y)⁻¹ *
        (divisorSheafSectionsEquiv E U s).val y :=
  divisorSheafGlobalMulIso_inv_app_eventuallyEq _ _ _ U s x

/-- Multiplication by the constant function `1` is the identity of `𝒪(D)`. -/
@[simp]
theorem divisorSheafIsoOfPrincipalDivisorEq_zero {D : WeilDivisor X}
    (hf : (MeromorphicFunction.orderSystem X).principalDivisor 0 = D - D) :
    divisorSheafIsoOfPrincipalDivisorEq 0 hf = Iso.refl _ :=
  divisorSheafGlobalMulIso_eq_refl _ _ fun x ↦ by
    rw [toMul_zero, Units.val_one, MeromorphicFunction.finitePart_one]

/-- The inverse of multiplication by `f` is multiplication by `f⁻¹`, written `-f` in the
additive group of nonzero meromorphic functions. -/
theorem divisorSheafIsoOfPrincipalDivisorEq_symm {D E : WeilDivisor X}
    (f : Additive (MeromorphicFunction X)ˣ)
    (hf : (MeromorphicFunction.orderSystem X).principalDivisor f = D - E)
    (hf' : (MeromorphicFunction.orderSystem X).principalDivisor (-f) = E - D) :
    (divisorSheafIsoOfPrincipalDivisorEq f hf).symm =
      divisorSheafIsoOfPrincipalDivisorEq (-f) hf' :=
  divisorSheafGlobalMulIso_symm _ _ _ _ fun x ↦ by
    rw [toMul_neg, Units.val_inv_eq_inv_val]
    exact MeromorphicFunction.finitePart_inv_eventuallyEq _ x

/-- Multiplying by `f` and then by `g` is multiplication by `f g`, written `f + g` in the
additive group of nonzero meromorphic functions. -/
theorem divisorSheafIsoOfPrincipalDivisorEq_trans {D E F : WeilDivisor X}
    (f g : Additive (MeromorphicFunction X)ˣ)
    (hf : (MeromorphicFunction.orderSystem X).principalDivisor f = D - E)
    (hg : (MeromorphicFunction.orderSystem X).principalDivisor g = E - F)
    (hfg : (MeromorphicFunction.orderSystem X).principalDivisor (f + g) = D - F) :
    divisorSheafIsoOfPrincipalDivisorEq f hf ≪≫ divisorSheafIsoOfPrincipalDivisorEq g hg =
      divisorSheafIsoOfPrincipalDivisorEq (f + g) hfg :=
  divisorSheafGlobalMulIso_trans _ _ _ _ _ _ fun x ↦ by
    rw [toMul_add, Units.val_mul]
    exact MeromorphicFunction.finitePart_mul_eventuallyEq _ _ x

omit [CompactSpace X] in
/-- A global section `t` of `𝒪(E)` which agrees with `k s` on punctured neighbourhoods, for a
global section `s` of `𝒪(D)`, embeds into meromorphic functions as `k` times the image of `s`. -/
private theorem toMeromorphic_eq_mul_of_eventuallyEq {D E : WeilDivisor X}
    (k : MeromorphicFunction X) {g : X → ℂ} (hk : ∀ x, k.finitePart =ᶠ[𝓝[≠] x] g)
    (s : divisorSections D ⊤) (t : divisorSections E ⊤)
    (ht : ∀ x : (⊤ : Opens X), t.val =ᶠ[𝓝[≠] x] fun y ↦ g y * s.val y) :
    divisorSections.toMeromorphic E t = k * divisorSections.toMeromorphic D s := by
  refine MeromorphicFunction.eq_of_eventuallyEq_finitePart fun x ↦ ?_
  have hx : Tendsto (fun y : X ↦ (⟨y, trivial⟩ : (⊤ : Opens X))) (𝓝[≠] x)
      (𝓝[≠] ⟨x, trivial⟩) :=
    (continuous_id.subtype_mk _).continuousAt.tendsto_nhdsNE fun _ _ hxy ↦ congrArg Subtype.val hxy
  filter_upwards [divisorSections.finitePart_toMeromorphic_eventuallyEq t x,
    MeromorphicFunction.finitePart_mul_eventuallyEq k (divisorSections.toMeromorphic D s) x,
    hk x, divisorSections.finitePart_toMeromorphic_eventuallyEq s x,
    hx.eventually (ht ⟨x, trivial⟩)] with y ht' hks hk' hs hts
  rw [ht', hks, Pi.mul_apply, hk', hs]
  exact hts

/-- On global sections, `divisorSheafIsoOfPrincipalDivisorEq` is multiplication by `f` in the
field of meromorphic functions. -/
theorem toMeromorphic_divisorSheafIsoOfPrincipalDivisorEq_hom_app_top {D E : WeilDivisor X}
    (f : Additive (MeromorphicFunction X)ˣ)
    (hf : (MeromorphicFunction.orderSystem X).principalDivisor f = D - E)
    (s : (divisorSheaf D).obj.obj (op ⊤)) :
    divisorSections.toMeromorphic E (divisorSheafSectionsEquiv E ⊤
        ((divisorSheafIsoOfPrincipalDivisorEq f hf).hom.hom.app (op ⊤) s)) =
      (f.toMul : MeromorphicFunction X) *
        divisorSections.toMeromorphic D (divisorSheafSectionsEquiv D ⊤ s) :=
  toMeromorphic_eq_mul_of_eventuallyEq _ (fun _ ↦ EventuallyEq.rfl) _ _
    (divisorSheafIsoOfPrincipalDivisorEq_hom_app_eventuallyEq f hf ⊤ s)

/-- On global sections, the inverse of `divisorSheafIsoOfPrincipalDivisorEq` is multiplication
by `f⁻¹` in the field of meromorphic functions. -/
theorem toMeromorphic_divisorSheafIsoOfPrincipalDivisorEq_inv_app_top {D E : WeilDivisor X}
    (f : Additive (MeromorphicFunction X)ˣ)
    (hf : (MeromorphicFunction.orderSystem X).principalDivisor f = D - E)
    (s : (divisorSheaf E).obj.obj (op ⊤)) :
    divisorSections.toMeromorphic D (divisorSheafSectionsEquiv D ⊤
        ((divisorSheafIsoOfPrincipalDivisorEq f hf).inv.hom.app (op ⊤) s)) =
      (f.toMul : MeromorphicFunction X)⁻¹ *
        divisorSections.toMeromorphic E (divisorSheafSectionsEquiv E ⊤ s) :=
  toMeromorphic_eq_mul_of_eventuallyEq _ (MeromorphicFunction.finitePart_inv_eventuallyEq _) _ _
    (divisorSheafIsoOfPrincipalDivisorEq_inv_app_eventuallyEq f hf ⊤ s)

/-- **`𝒪(D) ≅ 𝒪(D - (f))`.** Multiplication by a nonzero meromorphic function `f` identifies
the divisor sheaf of `D` with that of `D` minus the principal divisor of `f`. -/
def divisorSheafIsoSubPrincipalDivisor (D : WeilDivisor X)
    (f : Additive (MeromorphicFunction X)ˣ) :
    divisorSheaf D ≅
      divisorSheaf (D - (MeromorphicFunction.orderSystem X).principalDivisor f) :=
  divisorSheafIsoOfPrincipalDivisorEq f (sub_sub_cancel D _).symm

/-- `divisorSheafIsoSubPrincipalDivisor` is `divisorSheafIsoOfPrincipalDivisorEq` for the
divisors `D` and `D - (f)`. -/
theorem divisorSheafIsoSubPrincipalDivisor_def (D : WeilDivisor X)
    (f : Additive (MeromorphicFunction X)ˣ) :
    divisorSheafIsoSubPrincipalDivisor D f =
      divisorSheafIsoOfPrincipalDivisorEq f (sub_sub_cancel D _).symm :=
  (rfl)

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

/-! ### Multiplication by a meromorphic function -/

section Multiplication

variable {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]
  [ConnectedSpace X]

/-- **Multiplication by a meromorphic function, `𝒪_D ⟶ 𝒪_E`.** If the order of the meromorphic
function `g` is at least `D - E` at every point, multiplication by `g` sends sections of `𝒪_D` to
sections of `𝒪_E`. For an effective divisor `P` with `(g) ≥ -P` this is the multiplication map
`𝒪_D ⟶ 𝒪_{D + P}`. It is `divisorSheafGlobalMul` for the finite part of `g`, so it is defined on
the whole surface; `g` may be zero. -/
def divisorSheafMeromorphicMul {D E : WeilDivisor X} (g : MeromorphicFunction X)
    (hg : ∀ x, ((D x - E x : ℤ) : WithTop ℤ) ≤ MeromorphicFunction.order x g) :
    divisorSheaf D ⟶ divisorSheaf E :=
  divisorSheafGlobalMul D E g.finitePart g.meromorphicAt_finitePart fun x ↦
    (hg x).trans_eq (MeromorphicFunction.order_apply x g)

/-- `divisorSheafMeromorphicMul` is `divisorSheafGlobalMul` for the finite part of `g`. -/
theorem divisorSheafMeromorphicMul_def {D E : WeilDivisor X} (g : MeromorphicFunction X)
    (hg : ∀ x, ((D x - E x : ℤ) : WithTop ℤ) ≤ MeromorphicFunction.order x g) :
    divisorSheafMeromorphicMul g hg =
      divisorSheafGlobalMul D E g.finitePart g.meromorphicAt_finitePart
        fun x ↦ (hg x).trans_eq (MeromorphicFunction.order_apply x g) :=
  (rfl)

/-- On a punctured neighbourhood of each point, `divisorSheafMeromorphicMul` sends a section `s`
of `𝒪_D` to `g s`. -/
theorem divisorSheafMeromorphicMul_hom_app_eventuallyEq {D E : WeilDivisor X}
    (g : MeromorphicFunction X)
    (hg : ∀ x, ((D x - E x : ℤ) : WithTop ℤ) ≤ MeromorphicFunction.order x g) (U : Opens X)
    (s : (divisorSheaf D).obj.obj (op U)) (x : U) :
    (divisorSheafSectionsEquiv E U ((divisorSheafMeromorphicMul g hg).hom.app (op U) s)).val
      =ᶠ[𝓝[≠] x] fun y ↦ g.finitePart y * (divisorSheafSectionsEquiv D U s).val y :=
  divisorSheafGlobalMul_hom_app_eventuallyEq _ _ _ U s x

/-- On global sections, `divisorSheafMeromorphicMul` is multiplication by `g` in the field of
meromorphic functions. -/
theorem toMeromorphic_divisorSheafMeromorphicMul_hom_app_top {D E : WeilDivisor X}
    (g : MeromorphicFunction X)
    (hg : ∀ x, ((D x - E x : ℤ) : WithTop ℤ) ≤ MeromorphicFunction.order x g)
    (s : (divisorSheaf D).obj.obj (op ⊤)) :
    divisorSections.toMeromorphic E (divisorSheafSectionsEquiv E ⊤
        ((divisorSheafMeromorphicMul g hg).hom.app (op ⊤) s)) =
      g * divisorSections.toMeromorphic D (divisorSheafSectionsEquiv D ⊤ s) :=
  toMeromorphic_eq_mul_of_eventuallyEq _ (fun _ ↦ EventuallyEq.rfl) _ _
    (divisorSheafMeromorphicMul_hom_app_eventuallyEq g hg ⊤ s)

/-- **Additivity in the multiplier.** Multiplication by `g₁ + g₂` is the sum of the
multiplications by `g₁` and by `g₂`. -/
theorem divisorSheafMeromorphicMul_add {D E : WeilDivisor X} (g₁ g₂ : MeromorphicFunction X)
    (hg₁ : ∀ x, ((D x - E x : ℤ) : WithTop ℤ) ≤ MeromorphicFunction.order x g₁)
    (hg₂ : ∀ x, ((D x - E x : ℤ) : WithTop ℤ) ≤ MeromorphicFunction.order x g₂) :
    divisorSheafMeromorphicMul (g₁ + g₂)
        (fun x ↦ (le_min (hg₁ x) (hg₂ x)).trans ((MeromorphicFunction.order x).map_add _ _)) =
      divisorSheafMeromorphicMul g₁ hg₁ + divisorSheafMeromorphicMul g₂ hg₂ := by
  rw [divisorSheafMeromorphicMul_def, divisorSheafMeromorphicMul_def,
    divisorSheafMeromorphicMul_def, ← divisorSheafGlobalMul_add]
  exact divisorSheafGlobalMul_congr _ _ _ _ fun x ↦
    MeromorphicFunction.finitePart_add_eventuallyEq g₁ g₂ x

/-- Multiplication by `g₁ - g₂` is the difference of the multiplications by `g₁` and by `g₂`. -/
theorem divisorSheafMeromorphicMul_sub {D E : WeilDivisor X} (g₁ g₂ : MeromorphicFunction X)
    (hg₁ : ∀ x, ((D x - E x : ℤ) : WithTop ℤ) ≤ MeromorphicFunction.order x g₁)
    (hg₂ : ∀ x, ((D x - E x : ℤ) : WithTop ℤ) ≤ MeromorphicFunction.order x g₂) :
    divisorSheafMeromorphicMul (g₁ - g₂)
        (fun x ↦ (le_min (hg₁ x) (hg₂ x)).trans ((MeromorphicFunction.order x).map_sub _ _)) =
      divisorSheafMeromorphicMul g₁ hg₁ - divisorSheafMeromorphicMul g₂ hg₂ := by
  rw [eq_sub_iff_add_eq, ← divisorSheafMeromorphicMul_add]
  congr 1
  exact sub_add_cancel g₁ g₂

/-- Order bounds of meromorphic multipliers add up along products: if `g₁` and `g₂` satisfy the
bounds `D - E` and `E - F` at `x`, then `g₁ g₂` satisfies the bound `D - F`. -/
theorem sub_le_order_mul {D E F : WeilDivisor X} {g₁ g₂ : MeromorphicFunction X} {x : X}
    (hg₁ : ((D x - E x : ℤ) : WithTop ℤ) ≤ MeromorphicFunction.order x g₁)
    (hg₂ : ((E x - F x : ℤ) : WithTop ℤ) ≤ MeromorphicFunction.order x g₂) :
    ((D x - F x : ℤ) : WithTop ℤ) ≤ MeromorphicFunction.order x (g₁ * g₂) := by
  rw [(MeromorphicFunction.order x).map_mul, ← sub_add_sub_cancel (D x) (E x) (F x),
    WithTop.coe_add]
  exact add_le_add hg₁ hg₂

/-- **Composition.** Multiplying by `g₁` and then by `g₂` is multiplication by `g₁ g₂`. -/
@[reassoc (attr := simp)]
theorem divisorSheafMeromorphicMul_comp {D E F : WeilDivisor X} (g₁ g₂ : MeromorphicFunction X)
    (hg₁ : ∀ x, ((D x - E x : ℤ) : WithTop ℤ) ≤ MeromorphicFunction.order x g₁)
    (hg₂ : ∀ x, ((E x - F x : ℤ) : WithTop ℤ) ≤ MeromorphicFunction.order x g₂) :
    divisorSheafMeromorphicMul g₁ hg₁ ≫ divisorSheafMeromorphicMul g₂ hg₂ =
      divisorSheafMeromorphicMul (g₁ * g₂) fun x ↦ sub_le_order_mul (hg₁ x) (hg₂ x) := by
  rw [divisorSheafMeromorphicMul_def, divisorSheafMeromorphicMul_def,
    divisorSheafMeromorphicMul_def, divisorSheafGlobalMul_comp]
  exact divisorSheafGlobalMul_congr _ _ _ _ fun x ↦
    (MeromorphicFunction.finitePart_mul_eventuallyEq g₁ g₂ x).symm

/-- A constant multiplier satisfies the order bound `D - E` of a multiplication `𝒪_D ⟶ 𝒪_E`
when `D ≤ E`. -/
theorem sub_le_order_algebraMap {D E : WeilDivisor X} (hDE : D ≤ E) (c : ℂ) (x : X) :
    ((D x - E x : ℤ) : WithTop ℤ) ≤
      MeromorphicFunction.order x (algebraMap ℂ (MeromorphicFunction X) c) := by
  rw [MeromorphicFunction.order_apply, MeromorphicFunction.finitePart_algebraMap]
  exact sub_le_meromorphicOrderAt_const hDE c x

/-- **Constant multipliers.** For `D ≤ E`, multiplication by a constant `c` is `c` times the
inclusion `𝒪_D ⟶ 𝒪_E`, as morphisms of the underlying presheaves, whose category is
`ℂ`-linear. -/
theorem divisorSheafMeromorphicMul_algebraMap_hom {D E : WeilDivisor X} (hDE : D ≤ E) (c : ℂ) :
    (divisorSheafMeromorphicMul (algebraMap ℂ (MeromorphicFunction X) c)
      (sub_le_order_algebraMap hDE c)).hom = c • (divisorSheafMapOfLE hDE).hom := by
  rw [← divisorSheafGlobalMul_const_hom hDE c, divisorSheafMeromorphicMul_def]
  congr 1
  exact divisorSheafGlobalMul_congr _ _ _ _ fun x ↦ by
    rw [MeromorphicFunction.finitePart_algebraMap]

/-- For `D ≤ E`, multiplication by `1` is the inclusion `𝒪_D ⟶ 𝒪_E`. -/
@[simp]
theorem divisorSheafMeromorphicMul_one {D E : WeilDivisor X} (hDE : D ≤ E) :
    divisorSheafMeromorphicMul 1
        (fun x ↦ map_one (algebraMap ℂ (MeromorphicFunction X)) ▸ sub_le_order_algebraMap hDE 1 x) =
      divisorSheafMapOfLE hDE := by
  apply Sheaf.hom_ext
  rw [← one_smul ℂ (divisorSheafMapOfLE hDE).hom,
    ← divisorSheafMeromorphicMul_algebraMap_hom hDE 1]
  simp only [map_one]

/-- Multiplication by `g` commutes with the inclusions of divisor sheaves in the source. -/
@[reassoc (attr := simp)]
theorem divisorSheafMapOfLE_comp_divisorSheafMeromorphicMul {D D' E : WeilDivisor X}
    (hDD' : D ≤ D') (g : MeromorphicFunction X)
    (hg : ∀ x, ((D' x - E x : ℤ) : WithTop ℤ) ≤ MeromorphicFunction.order x g) :
    divisorSheafMapOfLE hDD' ≫ divisorSheafMeromorphicMul g hg =
      divisorSheafMeromorphicMul g
        (fun x ↦ (WithTop.coe_le_coe.2 (sub_le_sub_right (hDD' x) _)).trans (hg x)) :=
  divisorSheafMapOfLE_comp_divisorSheafGlobalMul hDD' _ _ _

/-- Multiplication by `g` commutes with the inclusions of divisor sheaves in the target. -/
@[reassoc (attr := simp)]
theorem divisorSheafMeromorphicMul_comp_divisorSheafMapOfLE {D E E' : WeilDivisor X}
    (g : MeromorphicFunction X)
    (hg : ∀ x, ((D x - E x : ℤ) : WithTop ℤ) ≤ MeromorphicFunction.order x g) (hEE' : E ≤ E') :
    divisorSheafMeromorphicMul g hg ≫ divisorSheafMapOfLE hEE' =
      divisorSheafMeromorphicMul g
        (fun x ↦ (WithTop.coe_le_coe.2 (sub_le_sub_left (hEE' x) _)).trans (hg x)) :=
  divisorSheafGlobalMul_comp_divisorSheafMapOfLE _ _ _ hEE'

/-- **Nonzero multipliers.** If the principal divisor of `f` is `D - F` and `F ≤ E`, then
multiplication by `f` as a morphism `𝒪_D ⟶ 𝒪_E` is the isomorphism `𝒪_D ≅ 𝒪_F` of
`divisorSheafIsoOfPrincipalDivisorEq` followed by the inclusion `𝒪_F ⟶ 𝒪_E`. -/
theorem divisorSheafIsoOfPrincipalDivisorEq_hom_comp_divisorSheafMapOfLE [CompactSpace X]
    {D E F : WeilDivisor X} (f : Additive (MeromorphicFunction X)ˣ)
    (hf : (MeromorphicFunction.orderSystem X).principalDivisor f = D - F) (hFE : F ≤ E) :
    (divisorSheafIsoOfPrincipalDivisorEq f hf).hom ≫ divisorSheafMapOfLE hFE =
      divisorSheafMeromorphicMul (f.toMul : MeromorphicFunction X) (fun x ↦ by
        rw [← MeromorphicFunction.coe_coeff_principalDivisor_orderSystem, hf,
          WeilDivisor.coeff, Finsupp.sub_apply]
        exact_mod_cast sub_le_sub_left (hFE x) _) := by
  rw [divisorSheafIsoOfPrincipalDivisorEq, divisorSheafGlobalMulIso_hom,
    divisorSheafGlobalMul_comp_divisorSheafMapOfLE, divisorSheafMeromorphicMul_def]

end Multiplication

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
theorem divisorCechCohomologyIsoOfPrincipalDivisorEq_hom {D E : WeilDivisor X}
    (f : Additive (MeromorphicFunction X)ˣ)
    (hf : (MeromorphicFunction.orderSystem X).principalDivisor f = D - E) (n : ℕ) :
    (divisorCechCohomologyIsoOfPrincipalDivisorEq f hf n).hom =
      (cechCohomology (TopCat.of X) (ModuleCat.{0} ℂ) n).map
        (divisorSheafIsoOfPrincipalDivisorEq f hf).hom.hom :=
  (rfl)

/-- The inverse cohomology isomorphism is induced by the inverse multiplication isomorphism. -/
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
theorem divisorCechCohomologyIsoOfLinearlyEquivalent_hom {D E : WeilDivisor X}
    (h : (MeromorphicFunction.orderSystem X).LinearlyEquivalent D E) (n : ℕ) :
    (divisorCechCohomologyIsoOfLinearlyEquivalent h n).hom =
      (cechCohomology (TopCat.of X) (ModuleCat.{0} ℂ) n).map
        (divisorSheafIsoOfLinearlyEquivalent h).hom.hom :=
  divisorCechCohomologyIsoOfPrincipalDivisorEq_hom _ _ n

/-- The inverse cohomology isomorphism of linearly equivalent divisors is induced by the inverse
sheaf isomorphism. -/
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
