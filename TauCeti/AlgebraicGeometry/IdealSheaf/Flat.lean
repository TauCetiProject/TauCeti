/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, Axel Delaval, Jie Xu, Shitan Xu
-/
module

public import TauCeti.AlgebraicGeometry.IdealSheaf.Colon
public import TauCeti.AlgebraicGeometry.IdealSheaf.BaseChange
import TauCeti.AlgebraicGeometry.IdealSheaf.Affine
import TauCeti.AlgebraicGeometry.Morphisms.ClosedImmersion.FinitePresentation
import TauCeti.RingTheory.Flat.QuotientRegular

/-!
# Flatness of colon subschemes

For a locally principal denominator, flatness of a closed subscheme and its intersection with
the denominator implies flatness of the colon subscheme. The ideal sheaves need not be Cartier.
The affine reduction adapts the product-flatness argument of the Tau Ceti contributors in
`TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Sum`.
-/

public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X S : Scheme.{u}}

/-- The residual closed subscheme is flat when the denominator is locally principal and
both the original subscheme and its intersection with the denominator are flat over the base.
Neither regularity of the equations nor containment of the ideal sheaves is required. -/
theorem flat_colon_subschemeι_comp (D E : X.IdealSheafData) (f : X ⟶ S)
    (hE : ∀ x : X, ∃ U : X.affineOpens, x ∈ U.val ∧
      ∃ a : Γ(X, U), E.ideal U = Ideal.span {a})
    [Flat (D.subschemeι ≫ f)] [Flat ((D ⊔ E).subschemeι ≫ f)] :
    Flat ((D.colon E).subschemeι ≫ f) := by
  have := E.locallyOfFinitePresentation_subschemeι_of_locallyPrincipal hE
  apply (D.colon E).flat_subschemeι_comp_of_forall_exists f
  intro W x hxW
  obtain ⟨U, hUW, hxU, v, hEv⟩ :=
    E.exists_eq_span_singleton_le_of_locallyPrincipal hE (f ⁻¹ᵁ W.val) hxW
  refine ⟨U, hUW, hxU, ?_⟩
  let _ : Algebra Γ(S, W) Γ(X, U) := (f.appLE W U hUW).hom.toAlgebra
  have : Module.Flat Γ(S, W) (Γ(X, U) ⧸ D.ideal U) :=
    (Scheme.Hom.flat_appLE_comp_ofHom_quotient_mk_iff f W U hUW _).mp
      (D.flat_appLE_comp_ofHom_quotient_mk f W.property U hUW)
  have hflat := (Scheme.Hom.flat_appLE_comp_ofHom_quotient_mk_iff f W U hUW _).mp
    ((D ⊔ E).flat_appLE_comp_ofHom_quotient_mk f W.property U hUW)
  rw [ideal_sup, Pi.sup_apply, hEv] at hflat
  have : Module.Flat Γ(S, W) (Γ(X, U) ⧸ (D.ideal U ⊔ Ideal.span {v})) := hflat
  rw [ideal_colon D E (E.fg_ideal), hEv, Ideal.colon_span]
  exact Ideal.flat_quotient_colon_span_singleton (R := Γ(S, W)) (D.ideal U) v

end AlgebraicGeometry.Scheme.IdealSheafData
