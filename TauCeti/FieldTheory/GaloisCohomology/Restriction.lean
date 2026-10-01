/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.FiniteExtension
public import TauCeti.RepresentationTheory.Homological.ContCohomology.TrivialF2

/-!
# Restriction across a finite extension of fields

A finite extension `L/K` and an embedding `σ : L →ₐ[K] Kˢ` identify `G_L` with the open
subgroup of `G_K` fixing `σ(L)`. This file transports continuous cohomology with trivial
`𝔽₂` coefficients across that identification and defines restriction from `G_K` to `G_L`.

The formula for `galoisRes` is restriction to `galoisSubgroup K L σ`, followed by transport
along `galoisSubgroupEquiv K L σ`. Its direct compatible-pair form pulls back along the
composite `G_L → G_K`. The chosen embedding is part of both formulas.

## Main definitions

* `TauCeti.galoisF2Iso`: transport of trivial-coefficient cohomology from the fixing subgroup
  to `G_L`.
* `TauCeti.galoisRes`: restriction from `G_K` to `G_L`.

## Reference

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed.,
  Chapter I, §5, for restriction through the open subgroup associated to a finite extension.
-/

public section

noncomputable section

namespace TauCeti

open CategoryTheory

universe u

variable (K : Type u) [Field K] (L : Type u) [Field L] [Algebra K L]
  (σ : L →ₐ[K] SeparableClosure K) [FiniteDimensional K L]

/-- Cohomology of the fixing subgroup of `σ(L)` identified with cohomology of `G_L`,
with trivial `𝔽₂` coefficients, in every degree. -/
def galoisF2Iso (n : ℕ) :
    continuousCohomology n (trivialF2 ↥(galoisSubgroup K L σ).toSubgroup) ≅
      continuousCohomology n (trivialF2 (AbsoluteGaloisGroup L)) :=
  trivialF2Iso (galoisSubgroupEquiv K L σ).symm n

/-- The forward transport is cohomological pullback along `G_L ≃ galoisSubgroup K L σ`. -/
@[simp]
theorem galoisF2Iso_hom (n : ℕ) :
    (galoisF2Iso K L σ n).hom =
      trivialF2Map (ContinuousMonoidHom.toContinuousMonoidHom
        (galoisSubgroupEquiv K L σ)) n := by
  rw [galoisF2Iso, trivialF2Iso_hom]
  rfl

/-- The inverse transport is pullback along the inverse topological group isomorphism. -/
@[simp]
theorem galoisF2Iso_inv (n : ℕ) :
    (galoisF2Iso K L σ n).inv =
      trivialF2Map (ContinuousMonoidHom.toContinuousMonoidHom
        (galoisSubgroupEquiv K L σ).symm) n := by
  rw [galoisF2Iso, trivialF2Iso_inv]

/-- Restriction on `𝔽₂`-cohomology for the finite extension `L/K`, relative to `σ`.
It is subgroup restriction followed by the canonical identification with `G_L`. -/
def galoisRes (n : ℕ) :
    continuousCohomology n (trivialF2 (AbsoluteGaloisGroup K)) ⟶
      continuousCohomology n (trivialF2 (AbsoluteGaloisGroup L)) :=
  trivialF2ResMap (AbsoluteGaloisGroup K) (galoisSubgroup K L σ).toSubgroup n ≫
    (galoisF2Iso K L σ n).hom

/-- The definition of field-extension restriction as subgroup restriction followed by
transport to the absolute Galois group of `L`. -/
theorem galoisRes_def (n : ℕ) :
    galoisRes K L σ n =
      trivialF2ResMap (AbsoluteGaloisGroup K) (galoisSubgroup K L σ).toSubgroup n ≫
        (galoisF2Iso K L σ n).hom :=
  (rfl)

/-- Field-extension restriction is the compatible-pair map along the composite
`G_L → galoisSubgroup K L σ → G_K`. -/
theorem galoisRes_eq_map (n : ℕ) :
    galoisRes K L σ n =
      trivialF2Map
        ((ContinuousMonoidHom.subgroupSubtype (galoisSubgroup K L σ).toSubgroup).comp
          (ContinuousMonoidHom.toContinuousMonoidHom (galoisSubgroupEquiv K L σ))) n := by
  rw [galoisRes_def, ← trivialF2Map_subgroupSubtype, galoisF2Iso_hom,
    ← trivialF2Map_comp]

end TauCeti
