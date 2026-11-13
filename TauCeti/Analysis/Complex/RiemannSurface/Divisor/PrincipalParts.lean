/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.RiemannSurface.Divisor.Meromorphic
public import TauCeti.Analysis.Complex.RiemannSurface.FunctionField.Germ
public import TauCeti.Analysis.Meromorphic.OrderFiltration
public import Mathlib.LinearAlgebra.DFinsupp
import TauCeti.Data.DFinsupp.Basic

/-!
# Mittag-Leffler principal parts relative to a divisor

Let `X` be a Riemann surface and `D` a divisor on `X`. A *principal part relative to `D`* at a
point `x` is a meromorphic germ at `x`, read in the preferred chart at `x`, modulo the germs of
order at least `-D x`, that is, modulo the stalk of `𝒪_D` at `x`
(`TauCeti.RiemannSurface.LocalPrincipalPart`). A *Mittag-Leffler distribution* relative to `D`
is a family of such local principal parts, almost all zero
(`TauCeti.RiemannSurface.PrincipalParts`). For `D = 0` these are Forster's Mittag-Leffler
distributions: a local principal part is a Laurent tail `∑_{k < 0} c_k z^k`.

On a compact connected Riemann surface, a meromorphic function `f` has a principal part at
every point, nonzero only at the finitely many poles of `f` and points of the support of `D`
(`TauCeti.RiemannSurface.MeromorphicFunction.principalParts`). The functions with zero
principal parts are exactly the global sections of `𝒪_D`
(`TauCeti.RiemannSurface.MeromorphicFunction.ker_principalParts`), so that
`0 → H⁰(X, 𝒪_D) → 𝓜(X) → PrincipalParts D` is exact. The cokernel of the second map is
`H¹(X, 𝒪_D)` (Forster, Theorem 17.3), which is how the residue pairing of principal parts with
differentials descends to Serre duality.

For `D ≤ E` there is a surjection `PrincipalParts D → PrincipalParts E`
(`TauCeti.RiemannSurface.PrincipalParts.mapOfLE`), compatible with taking principal parts of
meromorphic functions.

## References

* Otto Forster, *Lectures on Riemann Surfaces*, Graduate Texts in Mathematics 81, Springer, 1981,
  §§16-18 (Mittag-Leffler distributions and the residue pairing).
-/

public noncomputable section

open Filter OnePoint Set Topology
open scoped Manifold

namespace TauCeti.RiemannSurface

open TauCeti.AlgebraicGeometry (WeilDivisor)

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]

/-- A **local principal part relative to `D`** at `x`: a meromorphic germ at `x`, in the
preferred chart at `x`, modulo the germs of order at least `-D x`. -/
abbrev LocalPrincipalPart (D : WeilDivisor X) (x : X) : Type :=
  meromorphicGerms ℂ (chartAt ℂ x x) ⧸ meromorphicGerms.orderGE (chartAt ℂ x x) (-D x)

/-- The **Mittag-Leffler distributions relative to `D`**: families of local principal parts
relative to `D`, almost all of which are zero. -/
abbrev PrincipalParts (D : WeilDivisor X) : Type _ :=
  Π₀ x, LocalPrincipalPart D x

namespace LocalPrincipalPart

variable {D E : WeilDivisor X}

/-- For `D ≤ E`, the projection of local principal parts relative to `D` onto those relative
to `E`: the germs of order at least `-D x` have order at least `-E x`. -/
def mapOfLE (h : D ≤ E) (x : X) : LocalPrincipalPart D x →ₗ[ℂ] LocalPrincipalPart E x :=
  Submodule.factor (meromorphicGerms.orderGE_antitone _ (neg_le_neg (h x)))

@[simp]
theorem mapOfLE_mk (h : D ≤ E) (x : X) (φ : meromorphicGerms ℂ (chartAt ℂ x x)) :
    mapOfLE h x (Submodule.Quotient.mk φ) = Submodule.Quotient.mk φ :=
  (rfl)

theorem mapOfLE_surjective (h : D ≤ E) (x : X) : Function.Surjective (mapOfLE h x) :=
  Submodule.factor_surjective (meromorphicGerms.orderGE_antitone _ (neg_le_neg (h x)))

end LocalPrincipalPart

namespace PrincipalParts

variable {D E F : WeilDivisor X}

/-- For `D ≤ E`, the projection of Mittag-Leffler distributions relative to `D` onto those
relative to `E`, pointwise by `TauCeti.RiemannSurface.LocalPrincipalPart.mapOfLE`. -/
def mapOfLE (h : D ≤ E) : PrincipalParts D →ₗ[ℂ] PrincipalParts E :=
  DFinsupp.mapRange.linearMap fun x ↦ LocalPrincipalPart.mapOfLE h x

@[simp]
theorem mapOfLE_apply (h : D ≤ E) (μ : PrincipalParts D) (x : X) :
    mapOfLE h μ x = LocalPrincipalPart.mapOfLE h x (μ x) :=
  (rfl)

/-- The projection of Mittag-Leffler distributions to a larger divisor is surjective. -/
theorem mapOfLE_surjective (h : D ≤ E) : Function.Surjective (mapOfLE h) :=
  (DFinsupp.mapRange_surjective _ fun _ ↦ map_zero _).2 fun x ↦
    LocalPrincipalPart.mapOfLE_surjective h x

@[simp]
theorem mapOfLE_refl : mapOfLE (le_refl D) = LinearMap.id := by
  ext μ x : 2
  rw [mapOfLE_apply, LinearMap.id_apply]
  induction μ x using Submodule.Quotient.induction_on with
  | _ φ => rw [LocalPrincipalPart.mapOfLE_mk]

@[simp]
theorem mapOfLE_comp (hDE : D ≤ E) (hEF : E ≤ F) :
    (mapOfLE hEF).comp (mapOfLE hDE) = mapOfLE (hDE.trans hEF) := by
  ext μ x : 2
  simp only [LinearMap.comp_apply, mapOfLE_apply]
  induction μ x using Submodule.Quotient.induction_on with
  | _ φ => simp only [LocalPrincipalPart.mapOfLE_mk]

end PrincipalParts

namespace MeromorphicFunction

variable [IsManifold 𝓘(ℂ) 1 X] [ConnectedSpace X]

/-- The principal part of `f` relative to `D` vanishes at `x` exactly when `f` satisfies the
order bound of `𝒪_D` at `x`. -/
theorem mk_toChartGerm_eq_zero_iff {D : WeilDivisor X} {x : X} {f : MeromorphicFunction X} :
    (Submodule.Quotient.mk (toChartGerm x f) : LocalPrincipalPart D x) = 0 ↔
      ((-D x : ℤ) : WithTop ℤ) ≤ order x f := by
  rw [Submodule.Quotient.mk_eq_zero, meromorphicGerms.mem_orderGE, order_toChartGerm]

/-- Away from the poles of `f` and the support of `D`, the order bound of `𝒪_D` holds. -/
private theorem neg_le_order_of_ne_infty_of_eq_zero {D : WeilDivisor X} {x : X}
    {f : MeromorphicFunction X} (hf : f x ≠ ∞) (hD : D x = 0) :
    ((-D x : ℤ) : WithTop ℤ) ≤ order x f := by
  rw [hD, neg_zero, WithTop.coe_zero]
  exact order_nonneg_iff.2 hf

variable [CompactSpace X]

/-- On a compact surface, the points where a meromorphic function violates the order bound
of `𝒪_D` form a finite set: they are poles of `f` or points of the support of `D`. -/
theorem finite_setOf_not_neg_le_order (D : WeilDivisor X) (f : MeromorphicFunction X) :
    {x | ¬((-D x : ℤ) : WithTop ℤ) ≤ order x f}.Finite := by
  refine (f.finite_setOf_eq_infty.union D.support.finite_toSet).subset fun x hx ↦ ?_
  by_contra hmem
  simp only [mem_union, mem_ofPred_eq, Finset.mem_coe, Finsupp.mem_support_iff, not_or,
    not_not] at hmem
  exact hx (neg_le_order_of_ne_infty_of_eq_zero hmem.1 hmem.2)

/-- The **principal parts** of a meromorphic function on a compact connected Riemann surface,
relative to a divisor `D`: at each point, the coordinate germ modulo the stalk of `𝒪_D`. Only
the poles of `f` and the points of the support of `D` contribute. -/
def principalParts (D : WeilDivisor X) : MeromorphicFunction X →ₗ[ℂ] PrincipalParts D where
  toFun f := DFinsupp.ofSupportFinite (fun x ↦ Submodule.Quotient.mk (toChartGerm x f))
    ((finite_setOf_not_neg_le_order D f).subset fun _ hx h ↦ hx (mk_toChartGerm_eq_zero_iff.2 h))
  map_add' f g := by
    ext x
    simp only [map_add, Submodule.Quotient.mk_add, DFinsupp.ofSupportFinite_apply,
      DFinsupp.coe_add, Pi.add_apply]
  map_smul' c f := by
    ext x
    simp only [map_smul, Submodule.Quotient.mk_smul, DFinsupp.ofSupportFinite_apply,
      DFinsupp.coe_smul, Pi.smul_apply, RingHom.id_apply]

@[simp]
theorem principalParts_apply (D : WeilDivisor X) (f : MeromorphicFunction X) (x : X) :
    principalParts D f x = Submodule.Quotient.mk (toChartGerm x f) :=
  DFinsupp.ofSupportFinite_apply _ _ x

/-- The principal part of `f` relative to `D` vanishes at `x` exactly when `f` satisfies the
order bound of `𝒪_D` at `x`. -/
theorem principalParts_apply_eq_zero_iff {D : WeilDivisor X} {f : MeromorphicFunction X}
    {x : X} : principalParts D f x = 0 ↔ ((-D x : ℤ) : WithTop ℤ) ≤ order x f := by
  rw [principalParts_apply, mk_toChartGerm_eq_zero_iff]

/-- Principal parts vanish away from the poles and the support of the divisor. -/
theorem principalParts_apply_eq_zero {D : WeilDivisor X} {f : MeromorphicFunction X} {x : X}
    (hf : f x ≠ ∞) (hD : D x = 0) : principalParts D f x = 0 :=
  principalParts_apply_eq_zero_iff.2 (neg_le_order_of_ne_infty_of_eq_zero hf hD)

/-- Taking principal parts commutes with the projection to a larger divisor. -/
@[simp]
theorem mapOfLE_principalParts {D E : WeilDivisor X} (h : D ≤ E) (f : MeromorphicFunction X) :
    PrincipalParts.mapOfLE h (principalParts D f) = principalParts E f :=
  DFinsupp.ext fun x ↦ by
    rw [PrincipalParts.mapOfLE_apply, principalParts_apply, principalParts_apply,
      LocalPrincipalPart.mapOfLE_mk]

/-- **Left exactness of the Mittag-Leffler sequence.** The meromorphic functions with zero
principal parts relative to `D` are exactly the global sections of `𝒪_D`:
`0 → H⁰(X, 𝒪_D) → 𝓜(X) → PrincipalParts D` is exact. -/
theorem ker_principalParts (D : WeilDivisor X) :
    LinearMap.ker (principalParts D) = LinearMap.range (divisorSections.toMeromorphic D) := by
  ext f
  rw [LinearMap.mem_ker, divisorSections.mem_range_toMeromorphic_iff, DFinsupp.ext_iff]
  exact forall_congr' fun x ↦ principalParts_apply_eq_zero_iff

end MeromorphicFunction

end TauCeti.RiemannSurface
