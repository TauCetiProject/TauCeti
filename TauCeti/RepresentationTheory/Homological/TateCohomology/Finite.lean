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

Along a short exact sequence, `tateCohomology X₁ (n + 1)` is finite whenever
`tateCohomology X₃ n` and `tateCohomology X₂ (n + 1)` are
(`TauCeti.TateCohomology.finite_tateCohomology_X₁_of_shortExact`).
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
  have : Finite ((tateComplex M).X n) := by
    rcases n with n | n
    · change Finite ((Fin n → G) → M)
      infer_instance
    · change Finite ((Fin n → G) →₀ M)
      exact Finite.of_injective _ DFunLike.coe_injective
  have : Finite ((tateComplex M).cycles n) :=
    .of_injective _ <| (ModuleCat.mono_iff_injective ((tateComplex M).iCycles n)).1 inferInstance
  exact .of_surjective _ <| (ModuleCat.epi_iff_surjective ((tateComplex M).homologyπ n)).1
    inferInstance

/-- For a short exact sequence `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` of representations and `m = n + 1`, if
`tateCohomology X₃ n` and `tateCohomology X₂ m` are finite, then so is `tateCohomology X₁ m`. -/
theorem finite_tateCohomology_X₁_of_shortExact {S : ShortComplex (Rep R G)}
    (hS : S.ShortExact) (n m : ℤ) (hnm : n + 1 = m) [Finite (tateCohomology S.X₃ n)]
    [Finite (tateCohomology S.X₂ m)] : Finite (tateCohomology S.X₁ m) := by
  subst hnm
  have := Fintype.ofFinite (tateCohomology S.X₃ n)
  have := Fintype.ofFinite (tateCohomology S.X₂ (n + 1))
  have := AddGroup.fintypeOfKerLeRange (_root_.TateCohomology.δ hS n).hom.toAddMonoidHom
    ((tateCohomologyFunctor (n + 1)).map S.f).hom.toAddMonoidHom
    ((ShortComplex.moduleCat_exact_iff_ker_sub_range _).1 (_root_.TateCohomology.exact₁ hS n))
  infer_instance

end TauCeti.TateCohomology
