/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.NumberTheory.Cyclotomic.Basic
public import Mathlib.RepresentationTheory.Irreducible
import TauCeti.GroupTheory.Solvable
import TauCeti.RepresentationTheory.SolvableImage

/-!
# Galois representations with nonsolvable image under solvable base change

Let `ρ` be a representation of a Galois group `Gal(L/F)` whose image is not solvable, and let
`K` be an intermediate field, normal over `F`, with `Gal(K/F)` solvable. Restricting `ρ` to the
subgroup `Gal(L/K)` of `Gal(L/F)` fixing `K` keeps its image nonsolvable: `Gal(L/K)` is the kernel
of the restriction map to `Gal(K/F)`, so the quotient by it embeds in a solvable group. When `ρ`
is two-dimensional, the restriction is therefore irreducible. Cyclotomic extensions are abelian,
so this applies in particular to `K = F(ζ_n)`.

Take for `ρ` a residual representation of `G_ℚ`, so that `L` is an algebraic closure of `ℚ`, on a
two-dimensional vector space over an algebraic closure `k` of `𝔽_p`, with nonsolvable image. Over
the algebraically closed field `k` irreducibility is absolute irreducibility, so this says that
the residual representation stays absolutely irreducible, with nonsolvable image, on `G_K` for
every solvable Galois extension `K/ℚ`, for instance on `G_{ℚ(ζ_{p^n})}`. The
nonsolvable-image hypothesis in modularity lifting theorems for two-dimensional Galois
representations is used in this form: it survives the solvable base changes of their proofs, and
implies the irreducibility over `ℚ(ζ_p)` that those theorems also need.

No continuity is involved: the statements hold for the abstract group `Gal(L/F)`, so they apply
to continuous representations of profinite Galois groups as well.

## Main results

* `Representation.not_isSolvable_range_asGroupHom_comp_fixingSubgroup`: restriction to
  `Gal(L/K)` with `K/F` normal and `Gal(K/F)` solvable keeps the image nonsolvable.
* `Representation.isIrreducible_comp_fixingSubgroup_of_not_isSolvable_range_asGroupHom`: a
  two-dimensional representation with nonsolvable image stays irreducible on such a `Gal(L/K)`.
* `Representation.isIrreducible_comp_fixingSubgroup_of_isCyclotomicExtension`: the same for a
  cyclotomic intermediate field `K`.

## References

* L. V. Dieulefait, A. M. Pacetti, *A simplified proof of Serre's conjecture*,
  arXiv:2108.07577v2, Theorem 1.5 and its proof, p. 4.
-/

public section

open Module

namespace Representation

variable {k F L V : Type*} [Field F] [Field L] [Algebra F L] [AddCommGroup V]

/-- Restricting a representation of `Gal(L/F)` with nonsolvable image to the subgroup fixing an
intermediate field `K`, normal over `F` with solvable Galois group, keeps the image
nonsolvable. -/
theorem not_isSolvable_range_asGroupHom_comp_fixingSubgroup [CommSemiring k] [Module k V]
    {ρ : Representation k (L ≃ₐ[F] L) V} (K : IntermediateField F L) [Normal F K]
    [Group.IsSolvable (K ≃ₐ[F] K)] (h : ¬ Group.IsSolvable ρ.asGroupHom.range) :
    ¬ Group.IsSolvable (asGroupHom (ρ.comp K.fixingSubgroup.subtype)).range := by
  have hker := K.restrictNormalHom_ker
  have : K.fixingSubgroup.Normal := hker ▸ (AlgEquiv.restrictNormalHom K).normal_ker
  have : Group.IsSolvable ((L ≃ₐ[F] L) ⧸ K.fixingSubgroup) := by
    have : Group.IsSolvable ((L ≃ₐ[F] L) ⧸ (AlgEquiv.restrictNormalHom K).ker) :=
      Group.isSolvable_of_isSolvable_injective (QuotientGroup.kerLift_injective _)
    exact (QuotientGroup.quotientMulEquivOfEq hker).isSolvable_congr.mp this
  exact not_isSolvable_range_asGroupHom_comp_subtype K.fixingSubgroup h

/-- A two-dimensional representation of `Gal(L/F)` with nonsolvable image stays irreducible on
the subgroup fixing an intermediate field `K`, normal over `F` with solvable Galois group. -/
theorem isIrreducible_comp_fixingSubgroup_of_not_isSolvable_range_asGroupHom [Field k]
    [Module k V] {ρ : Representation k (L ≃ₐ[F] L) V} (hV : finrank k V = 2)
    (K : IntermediateField F L) [Normal F K] [Group.IsSolvable (K ≃ₐ[F] K)]
    (h : ¬ Group.IsSolvable ρ.asGroupHom.range) :
    IsIrreducible (ρ.comp K.fixingSubgroup.subtype) :=
  isIrreducible_of_not_isSolvable_range_asGroupHom hV
    (not_isSolvable_range_asGroupHom_comp_fixingSubgroup K h)

/-- A two-dimensional representation of `Gal(L/F)` with nonsolvable image stays irreducible on
the subgroup fixing a cyclotomic intermediate field `K`, such as `F(ζ_n)`. -/
theorem isIrreducible_comp_fixingSubgroup_of_isCyclotomicExtension [Field k] [Module k V]
    {ρ : Representation k (L ≃ₐ[F] L) V} (hV : finrank k V = 2) (S : Set ℕ)
    (K : IntermediateField F L) [IsCyclotomicExtension S F K]
    (h : ¬ Group.IsSolvable ρ.asGroupHom.range) :
    IsIrreducible (ρ.comp K.fixingSubgroup.subtype) :=
  have := (IsCyclotomicExtension.isGalois S F K).to_normal
  have := IsCyclotomicExtension.isMulCommutative S F K
  isIrreducible_comp_fixingSubgroup_of_not_isSolvable_range_asGroupHom hV K h

end Representation
