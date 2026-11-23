/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Jie Xu, Shitan Xu
-/
module

public import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Basic
public import TauCeti.AlgebraicGeometry.IdealSheaf.Colon
import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.FinitePresentation
import TauCeti.AlgebraicGeometry.IdealSheaf.Comap

/-!
# Subtraction of effective Cartier divisors

If `D ≤ E`, `D` is effective Cartier and `E` is locally principal, their colon is effective
Cartier and `D = (D : E) * E`. This subtracts the divisor of `E` from the divisor of `D`.
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

/-- A Cartier subideal of a locally principal ideal admits regular equations `(v * g)` and `(v)`. -/
theorem IsEffectiveCartier.exists_eq_span_mul_le (hD : D.IsEffectiveCartier)
    (hE : ∀ x : X, ∃ U : X.affineOpens, x ∈ U.val ∧
      ∃ a : Γ(X, U), E.ideal U = Ideal.span {a})
    (hle : D ≤ E) (U₀ : X.Opens) {x : X} (hx : x ∈ U₀) :
    ∃ W : X.affineOpens, W.val ≤ U₀ ∧ x ∈ W.val ∧ ∃ v g : Γ(X, W),
      IsSMulRegular Γ(X, W) v ∧ IsSMulRegular Γ(X, W) g ∧
      E.ideal W = Ideal.span {v} ∧ D.ideal W = Ideal.span {v * g} := by
  obtain ⟨U, hUU₀, hxU, v, hE⟩ :=
    E.exists_eq_span_singleton_le_of_locallyPrincipal hE U₀ hx
  obtain ⟨W, hWU, hxW, w, hw, hD⟩ := hD.exists_eq_span_singleton_le U.val hxU
  let v' := X.presheaf.map (homOfLE hWU).op v
  have hE' : E.ideal W = Ideal.span {v'} := E.ideal_eq_span_singleton_of_le hWU hE
  obtain ⟨g, hg⟩ := Ideal.mem_span_singleton'.mp
    (hE' ▸ hle W (hD ▸ Ideal.mem_span_singleton_self w))
  have hvg : IsSMulRegular Γ(X, W) (v' * g) := by
    simpa only [← hg, smul_eq_mul, mul_comm] using hw
  refine ⟨W, hWU.trans hUU₀, hxW, v', g, ?_, IsSMulRegular.of_mul hvg, hE', ?_⟩
  · exact IsSMulRegular.of_mul (by simpa only [mul_comm] using hvg)
  · rw [hD, ← hg, mul_comm]

/-- Subtracting a locally principal divisor from a containing effective Cartier divisor
gives an effective Cartier divisor. -/
theorem IsEffectiveCartier.colon (hD : D.IsEffectiveCartier)
    (hE : ∀ x : X, ∃ U : X.affineOpens, x ∈ U.val ∧
      ∃ a : Γ(X, U), E.ideal U = Ideal.span {a}) (hle : D ≤ E) :
    (D.colon E).IsEffectiveCartier := by
  have := E.locallyOfFinitePresentation_subschemeι_of_locallyPrincipal hE
  rw [isEffectiveCartier_iff]
  intro x
  obtain ⟨W, -, hxW, v, g, hv, hg, hEW, hDW⟩ :=
    hD.exists_eq_span_mul_le hE hle ⊤ (Set.mem_univ x)
  refine ⟨W, hxW, g, hg, ?_⟩
  apply ideal_colon_eq_of_eq_span_mul (E.fg_ideal) hv hEW
  rw [Ideal.span_singleton_mul_span_singleton]
  exact hDW

/-- A Cartier factor cancels on the right from a product followed by colon. -/
@[simp]
theorem IsEffectiveCartier.mul_colon_cancel_right (hE : E.IsEffectiveCartier)
    (D : X.IdealSheafData) : (D * E).colon E = D := by
  apply hE.mul_left_cancel
  rw [mul_comm E ((D * E).colon E),
    ← eq_colon_mul _ _ hE.locallyPrincipal (fun _ ↦ Ideal.mul_le_right), mul_comm]

/-- A Cartier factor cancels on the left from a product followed by colon. -/
@[simp]
theorem IsEffectiveCartier.mul_colon_cancel_left (hE : E.IsEffectiveCartier)
    (D : X.IdealSheafData) : (E * D).colon E = D := by
  rw [mul_comm E D, hE.mul_colon_cancel_right]

/-- Containment in a locally principal ideal is divisibility by an effective Cartier ideal. -/
theorem IsEffectiveCartier.le_iff_exists_eq_mul (hD : D.IsEffectiveCartier)
    (hE : ∀ x : X, ∃ U : X.affineOpens, x ∈ U.val ∧
      ∃ a : Γ(X, U), E.ideal U = Ideal.span {a}) :
    D ≤ E ↔ ∃ C : X.IdealSheafData, C.IsEffectiveCartier ∧ D = C * E := by
  constructor
  · intro hle
    exact ⟨D.colon E, hD.colon hE hle, D.eq_colon_mul E hE hle⟩
  · rintro ⟨C, -, rfl⟩ U
    exact Ideal.mul_le_right

/-- For a subideal `D ≤ E` of a locally principal ideal, colon subtraction commutes with
pullback whenever the denominator pulls back to an effective Cartier ideal. -/
theorem comap_colon (D E : X.IdealSheafData)
    (hE : ∀ x : X, ∃ U : X.affineOpens, x ∈ U.val ∧
      ∃ a : Γ(X, U), E.ideal U = Ideal.span {a}) (hle : D ≤ E)
    {Y : Scheme.{u}} (g : Y ⟶ X) (hEg : (E.comap g).IsEffectiveCartier) :
    (D.colon E).comap g = (D.comap g).colon (E.comap g) := by
  symm
  calc
    (D.comap g).colon (E.comap g) =
        (((D.colon E) * E).comap g).colon (E.comap g) := by rw [← D.eq_colon_mul E hE hle]
    _ = (D.colon E).comap g := by rw [comap_mul, hEg.mul_colon_cancel_right]

end AlgebraicGeometry.Scheme.IdealSheafData
