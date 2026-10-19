/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Homological.TateCohomology.Basic

/-!
# Finiteness of Tate cohomology

Tate cohomology of a finite representation of a finite group is finite in every degree
(`TauCeti.TateCohomology.finite_tateCohomology`). Its orders are then positive, which is what the
Herbrand quotient of a finite cyclic group uses: a finite representation has Herbrand quotient one
(`TauCeti.TateCohomology.herbrandQuotient_eq_one_of_finite`), and a finite kernel or cokernel does
not change the quotient (`TauCeti.TateCohomology.herbrandQuotient_eq_of_shortExact_of_finite_X₁`
and its relatives).

Along a short exact sequence, the connecting map also makes `Ĥⁿ⁺¹(G, X₁)` finite when
`Ĥⁿ(G, X₃)` is finite and `Ĥⁿ⁺¹(G, X₂)` vanishes
(`TauCeti.TateCohomology.finite_tateCohomology_X₁_of_shortExact_of_isZero_X₂`).
-/

public section

universe u

open CategoryTheory Limits

namespace TauCeti.TateCohomology

variable {R G : Type u} [CommRing R] [Group G] [Fintype G]

/-- Tate cohomology of a finite representation is finite in every degree. -/
instance finite_tateCohomology (M : Rep R G) [Finite M] (n : ℤ) : Finite (tateCohomology M n) := by
  -- The Tate complex is glued from Mathlib's inhomogeneous cochains in degrees `n ≥ 0` and its
  -- inhomogeneous chains in degrees `-(n + 1)`, so its term in degree `n` is by definition
  -- `(Fin n → G) → M` or `(Fin n → G) →₀ M` (the gluing lemmas `CochainComplex.ConnectData.X_ofNat`
  -- and `X_negSucc` are `rfl`). Mathlib states no lemma naming these carriers, so `change` is
  -- what exposes them.
  have : Finite ((tateComplex M).sc n).X₂ := by
    rcases n with n | n
    · change Finite ((Fin n → G) → M)
      infer_instance
    · change Finite ((Fin n → G) →₀ M)
      exact Finite.of_injective _ DFunLike.coe_injective
  have : Finite (LinearMap.ker ((tateComplex M).sc n).g.hom) :=
    Finite.of_injective _ Subtype.val_injective
  have : Finite ((tateComplex M).sc n).moduleCatLeftHomologyData.H :=
    Finite.of_surjective _ (Submodule.mkQ_surjective _)
  exact ((tateComplex M).sc n).moduleCatHomologyIso.toLinearEquiv.toEquiv.finite_iff.mpr this

/-- In a short exact sequence, if `Ĥⁿ(G, X₃)` is finite and `Ĥⁿ⁺¹(G, X₂)` vanishes, then
`Ĥⁿ⁺¹(G, X₁)` is finite, since the connecting map onto it is surjective. -/
theorem finite_tateCohomology_X₁_of_shortExact_of_isZero_X₂ {S : ShortComplex (Rep R G)}
    (hS : S.ShortExact) (n : ℤ) (hzero : IsZero (tateCohomology S.X₂ (n + 1)))
    [Finite (tateCohomology S.X₃ n)] : Finite (tateCohomology S.X₁ (n + 1)) := by
  have hepi := (_root_.TateCohomology.map_tateComplexFunctor_shortExact hS).epi_δ
    n (n + 1) rfl hzero
  exact Finite.of_surjective (_root_.TateCohomology.δ hS n)
    ((ModuleCat.epi_iff_surjective _).1 hepi)

end TauCeti.TateCohomology
