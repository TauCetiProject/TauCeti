/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Jie Xu, Shitan Xu
-/
module

public import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.FinitePresentation
public import TauCeti.AlgebraicGeometry.IdealSheaf.Colon
import TauCeti.RingTheory.Ideal.Colon

/-!
# Subtraction of effective Cartier divisors

If `D ≤ E` are ideals of effective Cartier divisors, their colon is again effective Cartier and
`D = (D : E) * E`. In divisor notation this subtracts the divisor of `E` from the divisor of `D`.
No reducedness or Noetherian assumption is required.

This is the local-equation step in subtracting contained finite flat divisors on a relative
curve. Flatness, finiteness and the residual degree require their own arguments.

## References

* The Stacks Project, Tag 02ON.
-/

public section

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace AlgebraicGeometry.Scheme.IdealSheafData

universe u

variable {X : Scheme.{u}} {D E : X.IdealSheafData}

/-- An effective Cartier ideal has finitely generated section ideals on every affine open. -/
theorem IsEffectiveCartier.fg_ideal (hE : E.IsEffectiveCartier) (U : X.affineOpens) :
    (E.ideal U).FG := by
  have hfp := TauCeti.locallyOfFinitePresentation_subschemeι_of_isEffectiveCartier hE
  simpa only [E.ker_subschemeι] using
    (IsClosedImmersion.locallyOfFinitePresentation_iff (f := E.subschemeι)).mp hfp U

/-- Nested effective Cartier ideals admit simultaneous equations `(v * g)` and `(v)`. -/
private theorem exists_eq_span_mul (hD : D.IsEffectiveCartier) (hE : E.IsEffectiveCartier)
    (hle : D ≤ E) (x : X) :
    ∃ W : X.affineOpens, x ∈ W.1 ∧ ∃ v g : Γ(X, W),
      IsSMulRegular Γ(X, W) v ∧ IsSMulRegular Γ(X, W) g ∧
      E.ideal W = Ideal.span {v} ∧ D.ideal W = Ideal.span {v * g} := by
  obtain ⟨U, hxU, v, hv, hE⟩ := (isEffectiveCartier_iff E).mp hE x
  obtain ⟨W, hWU, hxW, w, hw, hD⟩ := hD.exists_eq_span_singleton_le U.1 hxU
  let v' := X.presheaf.map (homOfLE hWU).op v
  have hv' : IsSMulRegular Γ(X, W) v' := U.2.isSMulRegular_map hWU hv
  have hE' : E.ideal W = Ideal.span {v'} := by
    rw [← E.map_ideal hWU, hE, Ideal.map_span, Set.image_singleton]
    rfl
  obtain ⟨g, hg⟩ := Ideal.mem_span_singleton'.mp
    (hE' ▸ hle W (hD ▸ Ideal.mem_span_singleton_self w))
  refine ⟨W, hxW, v', g, hv', ?_, hE', ?_⟩
  · apply IsSMulRegular.of_mul (a := v')
    simpa only [← hg, smul_eq_mul, mul_comm] using hw
  · rw [hD, ← hg, mul_comm]

/-- On simultaneous local equations, colon subtraction divides by the regular factor. -/
private theorem ideal_colon_eq_span (hEf : ∀ U, (E.ideal U).FG)
    {W : X.affineOpens} {v g : Γ(X, W)}
    (hv : IsSMulRegular Γ(X, W) v) (hE : E.ideal W = Ideal.span {v})
    (hD : D.ideal W = Ideal.span {v * g}) :
    (D.colon E hEf).ideal W = Ideal.span {g} := by
  rw [ideal_colon, hE, hD, Ideal.colon_span]
  apply Ideal.colon_singleton_eq_of_inf_span_singleton_eq hv.isLeftRegular
  rw [← Ideal.span_singleton_mul_span_singleton]
  exact inf_eq_left.mpr Ideal.mul_le_left

/-- Subtracting nested effective Cartier divisors factors their ideal sheaves. -/
theorem IsEffectiveCartier.eq_colon_mul (hD : D.IsEffectiveCartier)
    (hE : E.IsEffectiveCartier) (hle : D ≤ E) : D = D.colon E hE.fg_ideal * E := by
  choose W hxW v g hv _hg hEW hDW using exists_eq_span_mul hD hE hle
  refine ext_of_iSup_eq_top W (eq_top_iff.mpr fun x _ ↦ Opens.mem_iSup.mpr ⟨x, hxW x⟩)
    fun x ↦ ?_
  rw [ideal_mul, Pi.mul_apply,
    ideal_colon_eq_span hE.fg_ideal (hv x) (hEW x) (hDW x), hEW x, hDW x,
    Ideal.span_singleton_mul_span_singleton, mul_comm]

/-- The difference of nested effective Cartier divisors is effective Cartier. -/
theorem IsEffectiveCartier.colon (hD : D.IsEffectiveCartier)
    (hE : E.IsEffectiveCartier) (hle : D ≤ E) :
    (D.colon E hE.fg_ideal).IsEffectiveCartier := by
  rw [isEffectiveCartier_iff]
  intro x
  obtain ⟨W, hxW, v, g, hv, hg, hEW, hDW⟩ := exists_eq_span_mul hD hE hle x
  exact ⟨W, hxW, g, hg, ideal_colon_eq_span hE.fg_ideal hv hEW hDW⟩

end AlgebraicGeometry.Scheme.IdealSheafData
