/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.TensorProduct
public import TauCeti.AlgebraicGeometry.IdealSheaf.Colon
import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.FinitePresentation
import TauCeti.AlgebraicGeometry.IdealSheaf.Comap
import TauCeti.RingTheory.Ideal.Colon

/-!
# Division by effective Cartier divisors

Every effective Cartier divisor `J` on an arbitrary scheme `X` is locally finitely generated on
every affine open (`IsEffectiveCartier.fg_ideal`), so the colon ideal sheaf `I.colon J hJ.fg_ideal`
is defined for any ideal sheaf `I`. Since `J` is locally principal, `J * (I : J) = I ⊓ J`
(`IsEffectiveCartier.mul_colon_eq_inf`), and when `I ≤ J` this yields the exact factorization
`J * (I : J) = I` (`IsEffectiveCartier.mul_colon_eq_of_le`), uniquely determined by cancellation
for effective Cartier divisors (`IsEffectiveCartier.eq_colon_of_mul_eq`).

When both `I` and `J` are effective Cartier divisors with `I ≤ J`, the quotient `(I : J)` is again
an effective Cartier divisor (`IsEffectiveCartier.isEffectiveCartier_colon`), corresponding to the
difference divisor `D - E`, and its line-bundle class is `[I] * [J]⁻¹`
(`TauCeti.AlgebraicGeometry.LineBundleClass.mk_toInvertibleSheaf_colon`). Moreover, whenever `I ≤ J`
and the pullback `J.comap f` along a morphism `f : X ⟶ Y` remains effective Cartier, the colon
ideal sheaf commutes with pullback without any flatness assumption
(`IsEffectiveCartier.comap_colon_of_le`).

## Main results

* `AlgebraicGeometry.Scheme.IdealSheafData.IsEffectiveCartier.fg_ideal`: an effective Cartier
  divisor has finitely generated sections on every affine open.
* `AlgebraicGeometry.Scheme.IdealSheafData.IsEffectiveCartier.mul_colon_eq_inf`:
  `J * (I : J) = I ⊓ J`.
* `AlgebraicGeometry.Scheme.IdealSheafData.IsEffectiveCartier.mul_colon_eq_of_le`:
  if `I ≤ J`, then `J * (I : J) = I`.
* `AlgebraicGeometry.Scheme.IdealSheafData.IsEffectiveCartier.eq_colon_of_mul_eq`:
  if `J * K = I`, then `K = (I : J)`.
* `AlgebraicGeometry.Scheme.IdealSheafData.IsEffectiveCartier.isEffectiveCartier_colon`:
  if `I` and `J` are effective Cartier divisors with `I ≤ J`, then `(I : J)` is effective Cartier.
* `AlgebraicGeometry.Scheme.IdealSheafData.IsEffectiveCartier.comap_colon_of_le`:
  pullback along any morphism preserving effectiveness of `J` commutes with dividing by `J`.
* `TauCeti.AlgebraicGeometry.LineBundleClass.mk_toInvertibleSheaf_colon`:
  `[(I : J)] = [I] * [J]⁻¹` in the Picard group.

## References

* [The Stacks Project, Tag 01WQ](https://stacks.math.columbia.edu/tag/01WQ): effective Cartier
  divisors and their ideal sheaves.
-/

public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

noncomputable section

variable {X Y : Scheme.{u}}

/-- The defining ideal sheaf of an effective Cartier divisor is finitely generated on every
affine open, without any noetherian hypothesis. -/
theorem IsEffectiveCartier.fg_ideal {J : X.IdealSheafData} (hJ : J.IsEffectiveCartier)
    (U : X.affineOpens) : (J.ideal U).FG := by
  have := TauCeti.locallyOfFinitePresentation_subschemeι_of_isEffectiveCartier hJ
  simpa only [J.ker_subschemeι] using
    IsClosedImmersion.locallyOfFinitePresentation_iff.mp this U

/-- For an effective Cartier divisor `J` and any ideal sheaf `I`, `J * (I : J) = I ⊓ J`. -/
theorem IsEffectiveCartier.mul_colon_eq_inf {J : X.IdealSheafData} (hJ : J.IsEffectiveCartier)
    (I : X.IdealSheafData) : J * I.colon J hJ.fg_ideal = I ⊓ J :=
  mul_colon_eq_inf_of_exists_eq_span_singleton I J hJ.fg_ideal fun x ↦ by
    obtain ⟨U, hxU, a, -, hJa⟩ := (isEffectiveCartier_iff J).mp hJ x
    exact ⟨U, hxU, a, hJa⟩

/-- **Exact factorization by an effective Cartier divisor.** If `I ≤ J` and `J` is an effective
Cartier divisor, then `J * (I : J) = I`. -/
theorem IsEffectiveCartier.mul_colon_eq_of_le {I J : X.IdealSheafData} (hJ : J.IsEffectiveCartier)
    (hIJ : I ≤ J) : J * I.colon J hJ.fg_ideal = I := by
  rw [hJ.mul_colon_eq_inf, inf_eq_left.mpr hIJ]

/-- **Uniqueness of division by an effective Cartier divisor.** If `J * K = I` and `J` is an
effective Cartier divisor, then `K = (I : J)`. -/
theorem IsEffectiveCartier.eq_colon_of_mul_eq {I J K : X.IdealSheafData} (hJ : J.IsEffectiveCartier)
    (h : J * K = I) : K = I.colon J hJ.fg_ideal :=
  hJ.mul_left_cancel (h.trans (hJ.mul_colon_eq_of_le (h ▸ fun _ ↦ Ideal.mul_le_left)).symm)

/-- Dividing `J * K` by an effective Cartier divisor `J` recovers `K`. -/
@[simp]
theorem IsEffectiveCartier.colon_mul_left {J : X.IdealSheafData} (hJ : J.IsEffectiveCartier)
    (K : X.IdealSheafData) : (J * K).colon J hJ.fg_ideal = K :=
  (hJ.eq_colon_of_mul_eq rfl).symm

/-- Dividing `K * J` by an effective Cartier divisor `J` recovers `K`. -/
@[simp]
theorem IsEffectiveCartier.colon_mul_right {J : X.IdealSheafData} (hJ : J.IsEffectiveCartier)
    (K : X.IdealSheafData) : (K * J).colon J hJ.fg_ideal = K := by
  rw [mul_comm, hJ.colon_mul_left]

/-- **Difference of effective Cartier divisors.** If `I` and `J` are effective Cartier divisors
with `I ≤ J` (geometrically `E ≤ D`), then the colon ideal sheaf `(I : J)` is again an effective
Cartier divisor (cutting out `D - E`). -/
theorem IsEffectiveCartier.isEffectiveCartier_colon {I J : X.IdealSheafData}
    (hI : I.IsEffectiveCartier) (hJ : J.IsEffectiveCartier) (hIJ : I ≤ J) :
    (I.colon J hJ.fg_ideal).IsEffectiveCartier := by
  rw [isEffectiveCartier_iff]
  intro x
  obtain ⟨U, hxU, a, ha, hJa⟩ := (isEffectiveCartier_iff J).mp hJ x
  obtain ⟨V, hVU, hxV, c, hc, hIc⟩ := hI.exists_eq_span_singleton_le U.1 hxU
  let a' : Γ(X, V) := X.presheaf.map (homOfLE hVU).op a
  have ha' : IsSMulRegular Γ(X, V) a' := U.2.isSMulRegular_map hVU ha
  have hJa' : J.ideal V = Ideal.span {a'} := by
    rw [← J.map_ideal hVU, hJa, Ideal.map_span, Set.image_singleton]
    rfl
  have hcJ : c ∈ Ideal.span {a'} := by
    rw [← hJa']
    exact hIJ V (hIc ▸ Ideal.subset_span (Set.mem_singleton c))
  obtain ⟨b, hcb⟩ := Ideal.mem_span_singleton.mp hcJ
  have hb : IsSMulRegular Γ(X, V) b := IsSMulRegular.of_mul (a := a') (hcb ▸ hc)
  refine ⟨V, hxV, b, hb, ?_⟩
  rw [ideal_colon, hIc, hcb, hJa', ← Ideal.span_singleton_mul_span_singleton]
  exact Ideal.colon_span_singleton_mul_of_isLeftRegular ha'

/-- **Pullback compatibility of division by an effective Cartier divisor.** If `I ≤ J`, `J` is an
effective Cartier divisor on `Y`, and its pullback `J.comap f` along `f : X ⟶ Y` is still an
effective Cartier divisor, then `(I : J).comap f = (I.comap f : J.comap f)`. No flatness assumption
on `f` is needed. -/
theorem IsEffectiveCartier.comap_colon_of_le {I J : Y.IdealSheafData} (hJ : J.IsEffectiveCartier)
    (hIJ : I ≤ J) (f : X ⟶ Y) (hJf : (J.comap f).IsEffectiveCartier) :
    (I.colon J hJ.fg_ideal).comap f = (I.comap f).colon (J.comap f) hJf.fg_ideal :=
  hJf.eq_colon_of_mul_eq (by rw [← comap_mul, hJ.mul_colon_eq_of_le hIJ])

end

end AlgebraicGeometry.Scheme.IdealSheafData

namespace TauCeti.AlgebraicGeometry.LineBundleClass

open _root_.AlgebraicGeometry _root_.AlgebraicGeometry.Scheme.IdealSheafData

variable {X : Scheme.{u}} {I J : X.IdealSheafData}

/-- The line-bundle class of the quotient `(I : J)` of two effective Cartier divisors with `I ≤ J`
is `[I] * [J]⁻¹` in the Picard group. -/
theorem mk_toInvertibleSheaf_colon (hI : I.IsEffectiveCartier) (hJ : J.IsEffectiveCartier)
    (hIJ : I ≤ J) :
    mk (hI.isEffectiveCartier_colon hJ hIJ).toInvertibleSheaf =
      mk hI.toInvertibleSheaf * (mk hJ.toInvertibleSheaf)⁻¹ := by
  rw [eq_mul_inv_iff_mul_eq, mul_comm,
    ← mk_toInvertibleSheaf_mul hJ (hI.isEffectiveCartier_colon hJ hIJ)]
  exact mk_toInvertibleSheaf_congr _ hI (hJ.mul_colon_eq_of_le hIJ)

end TauCeti.AlgebraicGeometry.LineBundleClass
