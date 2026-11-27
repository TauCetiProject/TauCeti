/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.DeligneTorus.MumfordTate.Connected
public import TauCeti.Algebra.AlgebraicGroup.Reductive.StandardComodule
public import TauCeti.Geometry.Hodge.MumfordTate.Stabilizer
public import TauCeti.Geometry.Hodge.Orthogonal

/-!
# Reductivity of the Mumford–Tate group of a polarizable Hodge structure

Let `V` be a rational Hodge structure, pure of weight `n`, with a basis `b` of `V_ℚ`, so that
`GL_V ≅ GL_d`. Its Mumford–Tate group `MT(V) ⊆ GL_d` is the smallest closed `ℚ`-subgroup through
whose real extension `h_V : S → GL_{d,ℝ}` factors
(`TauCeti.Hodge.HodgeStructureOn.mumfordTateHopfIdeal`). This file proves that if `V` is
polarizable, `MT(V)` is reductive, which is
`TauCeti.Hodge.HodgeStructureOn.reductiveCommHopfAlgProperty_quotient_mumfordTateHopfIdeal`.

`MT(V)` is geometrically connected
(`TauCeti.DeligneTorus.geometricallyConnectedCommHopfAlgProperty_quotient_mumfordTateHopfIdeal`),
so it is reductive exactly when its standard representation on `ℚ^d` is completely reducible
(`TauCeti.reductiveCommHopfAlgProperty_iff_isCompletelyReducible_corestrictStandardComodule`).
By
`TauCeti.Hodge.HodgeStructureOn.stabilizerHopfIdeal_le_mumfordTateHopfIdeal_iff_eq_iSup_inf_piece`,
an `MT(V)`-stable subspace is a rational sub-Hodge structure. A polarization gives it a
complementary rational sub-Hodge structure (`TauCeti.Hodge.exists_isCompl_of_isPolarizable`), and
that complement is again `MT(V)`-stable.

## References

* J. S. Milne, *Introduction to Shimura varieties*, §2, p. 31 (the aside after Definition 2.16).
* P. Deligne, *Hodge cycles on abelian varieties* (notes by J. S. Milne), Proposition 3.6,
  pp. 24–25.
-/

public section

open CategoryTheory TauCeti.DeligneTorus TauCeti.GeneralLinear

namespace TauCeti.Hodge.HodgeStructureOn

variable {Vℤ Vℚ Vℂ : Type*} [AddCommGroup Vℤ] [AddCommGroup Vℚ] [Module ℚ Vℚ]
  [AddCommGroup Vℂ] [Module ℂ Vℂ] {ιℚ : Vℤ →ₗ[ℤ] Vℚ} {ιℂ : Vℤ →ₗ[ℤ] Vℂ}
  (hℚ : IsBaseChange ℚ ιℚ) {hℂ : IsBaseChange ℂ ιℂ} {n : ℤ} {d : ℕ}
  (b : Module.Basis (Fin d) ℚ Vℚ) (hs : HodgeStructureOn Vℂ (latticeConjugation hℂ) n)

/-- **The Mumford–Tate group of a polarizable Hodge structure is reductive.** For a polarizable
rational Hodge structure `V` with a basis `b` of `V_ℚ`, the closed subgroup `MT(V) ⊆ GL_d` cut
out by `TauCeti.Hodge.HodgeStructureOn.mumfordTateHopfIdeal` is reductive. -/
theorem reductiveCommHopfAlgProperty_quotient_mumfordTateHopfIdeal (hpol : IsPolarizable hℂ hs) :
    reductiveCommHopfAlgProperty ℚ
      (FiniteTypeCommHopfAlgCat.quotient
        (⟨coordinateHopfAlgebra ℚ d,
          inferInstanceAs (Algebra.FiniteType ℚ (coordinateHopfAlgebra ℚ d))⟩ :
          FiniteTypeCommHopfAlgCat ℚ)
        (hs.mumfordTateHopfIdeal hℚ b)) := by
  have _ : Module.Finite ℚ Vℚ := Module.Finite.of_basis b
  have hconn : geometricallyConnectedCommHopfAlgProperty ℚ
      (_root_.CommHopfAlgCat.quotient (coordinateHopfAlgebra ℚ d)
        (hs.mumfordTateHopfIdeal hℚ b)) := by
    rw [mumfordTateHopfIdeal_eq_mumfordTateHopfIdeal_deligneHom]
    exact geometricallyConnectedCommHopfAlgProperty_quotient_mumfordTateHopfIdeal
      (hs.deligneHom hℚ b)
  rw [reductiveCommHopfAlgProperty_iff_isCompletelyReducible_corestrictStandardComodule _ hconn
    (_root_.CommHopfAlgCat.mkQuotient (coordinateHopfAlgebra ℚ d)
      (hs.mumfordTateHopfIdeal hℚ b)).hom
    (_root_.CommHopfAlgCat.mkQuotient_surjective _ _)]
  let _ := standardComodule ℚ d
  refine (Comodule.isCompletelyReducible_corestrict_mkQuotient_iff _).mpr fun W hW ↦ ?_
  obtain ⟨-, W'', hc, -, -⟩ := exists_isCompl_of_isPolarizable hpol
    ⟨W.map b.equivFun.symm.toLinearMap,
      (hs.stabilizerHopfIdeal_le_mumfordTateHopfIdeal_iff_eq_iSup_inf_piece hℚ b W).mp hW⟩
  refine ⟨W''.WQ.map b.equivFun.toLinearMap, ?_, ?_⟩
  · have := (Submodule.orderIsoMapComap b.equivFun).isCompl_iff.mp hc
    simpa [Submodule.orderIsoMapComap_apply, ← Submodule.map_comp] using this
  · rw [hs.stabilizerHopfIdeal_le_mumfordTateHopfIdeal_iff_eq_iSup_inf_piece hℚ b,
      ← Submodule.map_comp]
    simpa using W''.hodge_spanning

end TauCeti.Hodge.HodgeStructureOn
