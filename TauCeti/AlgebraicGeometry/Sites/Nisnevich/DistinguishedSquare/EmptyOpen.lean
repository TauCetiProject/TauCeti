/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Sites.Nisnevich.DistinguishedSquare
import TauCeti.AlgebraicGeometry.Morphisms.OpenImmersion

/-!
# Elementary distinguished squares with empty open part

Let `Q` be an elementary distinguished square over a reduced scheme `X` whose open part `U` is
empty. The reduced closed complement of `U` is then `X` itself, so the condition that `p` is an
isomorphism over it says that `p : V ⟶ X` is an isomorphism
(`TauCeti.AlgebraicGeometry.Scheme.ElementaryDistinguishedSquare.isIso_p_of_isEmpty`).

So an étale morphism onto a reduced scheme that is not an isomorphism, such as
`Spec L ⟶ Spec K` for a separable field extension of degree two, or a morphism with two points
over a one-point base, is never the `p` of a distinguished square with empty `U`, even when it
has a unique point with trivial residue field extension over every point.
-/

public section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace

universe u

namespace TauCeti.AlgebraicGeometry.Scheme.ElementaryDistinguishedSquare

variable {X : AlgebraicGeometry.Scheme.{u}} (Q : ElementaryDistinguishedSquare X)

/-- **The map `p` of an elementary distinguished square with empty open part over a reduced
scheme is an isomorphism**: the reduced closed complement of `U = ∅` is `X`, over which `p` is an
isomorphism. -/
theorem isIso_p_of_isEmpty [IsReduced X] [IsEmpty Q.U] : IsIso Q.p := by
  set I := AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal Q.j.opensRange.compl
  have hI : IsIso I.subschemeι := by
    rw [AlgebraicGeometry.Scheme.isIso_subschemeι_iff_eq_bot]
    have : Q.j.opensRange.compl = ⊤ := by
      rw [AlgebraicGeometry.Scheme.Hom.opensRange_eq_bot_of_isEmpty]
      ext
      simp
    simp only [I, this, AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal_top,
      AlgebraicGeometry.Scheme.nilradical_eq_bot]
  have : IsIso (pullback.fst Q.p I.subschemeι ≫ Q.p) := by
    rw [pullback.condition]
    infer_instance
  exact IsIso.of_isIso_comp_left (pullback.fst Q.p I.subschemeι) Q.p

/-- A morphism `q : V ⟶ X` to a reduced scheme that is not an isomorphism is not, up to
isomorphism over `X`, the `p` of an elementary distinguished square with empty open part. -/
theorem isEmpty_iso_of_not_isIso [IsReduced X] [IsEmpty Q.U] {V : AlgebraicGeometry.Scheme.{u}}
    (q : V ⟶ X) (hq : ¬ IsIso q) : IsEmpty (Over.mk Q.p ≅ Over.mk q) := by
  refine ⟨fun e ↦ hq ?_⟩
  have := Q.isIso_p_of_isEmpty
  have h : e.inv.left ≫ Q.p = q := Over.w e.inv
  rw [← h]
  infer_instance

end TauCeti.AlgebraicGeometry.Scheme.ElementaryDistinguishedSquare
