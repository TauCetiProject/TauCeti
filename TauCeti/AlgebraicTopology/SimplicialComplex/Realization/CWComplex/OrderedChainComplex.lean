/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Basis.SMul
public import TauCeti.AlgebraicTopology.Cellular.Comparison
public import TauCeti.AlgebraicTopology.SimplicialComplex.ChainComplex
public import TauCeti.AlgebraicTopology.SimplicialComplex.Realization.CWComplex.AlternatingIncidence

/-!
# Cellular chains of a simplicial realization are ordered simplicial chains

For an abstract simplicial complex `K` with linearly ordered vertices, the cellular chain complex
of the CW structure on its weak realization `|K|` is isomorphic to the ordered simplicial chain
complex of `K`, whose boundary is `∂[v₀, …, vₙ₊₁] = ∑ⱼ (-1) ^ j [v₀, …, v̂ⱼ, …, vₙ₊₁]`.

The incidence coefficient of the `j`-th deleted-vertex face of an `(n + 1)`-cell is
`(-1) ^ j * εₙ` for a unit `εₙ = TauCeti.realizationFaceIncidence R n` of the coefficient ring
which depends only on `n`: it is computed once on the standard `(n + 1)`-simplex, and transported
to every cell of every complex along the increasing vertex map onto that cell
(`TauCeti.cellularIncidence_realization_face_eq_neg_one_pow_mul_realizationFaceIncidence`).
Rescaling the cellular basis vector of each `n`-cell by `sₙ = εₙ₋₁ ⋯ ε₀`
(`TauCeti.realizationChainScale`) absorbs these units, giving the isomorphism of chain complexes
`TauCeti.cellularChainComplexRealizationIso`. Composed with the comparison of cellular and
singular homology, the homology of the ordered simplicial chain complex of `K` is the singular
homology of `|K|` (`TauCeti.orderedSimplicialHomologyIsoSingularHomology`).

## Main definitions

* `TauCeti.realizationChainScale`: the units `sₙ`, with `s₀ = 1` and `sₙ₊₁ = εₙ * sₙ`.
* `TauCeti.cellularChainComplexRealizationIso`: the cellular chain complex of `|K|` is the
  ordered simplicial chain complex of `K`.
* `TauCeti.orderedSimplicialHomologyIsoSingularHomology`: ordered simplicial homology is
  singular homology of the realization.

## References

* A. Hatcher, *Algebraic Topology*, Section 2.1 (simplicial homology) and Section 2.2 (cellular
  homology, and its equivalence with simplicial homology).
-/

public section

noncomputable section

open CategoryTheory Set Topology Topology.RelCWComplex Finsupp

universe u

namespace TauCeti

open _root_.AbstractSimplicialComplex

section Scale

variable (R : Type u) [Ring R]

/-- The units `sₙ` rescaling the cellular basis of a simplicial realization into the ordered
simplicial basis: `s₀ = 1` and `sₙ₊₁ = εₙ * sₙ`, with `εₙ = TauCeti.realizationFaceIncidence R n`.
-/
def realizationChainScale : ℕ → Rˣ
  | 0 => 1
  | n + 1 => (isUnit_realizationFaceIncidence R n).unit * realizationChainScale n

/-- The scale in degree `0` is `1`. -/
@[simp]
theorem realizationChainScale_zero : realizationChainScale R 0 = 1 :=
  (rfl)

/-- The scale in degree `n + 1` is `εₙ * sₙ`. -/
@[simp]
theorem coe_realizationChainScale_succ (n : ℕ) :
    (realizationChainScale R (n + 1) : R) =
      realizationFaceIncidence R n * realizationChainScale R n :=
  (rfl)

end Scale

section ChainComplex

variable {ι : Type u} [LinearOrder ι] (K : _root_.AbstractSimplicialComplex ι)
  (R : Type u) [Ring R]

/-- The cellular chain group of `|K|` in degree `n` is the module of ordered simplicial
`n`-chains of `K`: the cellular basis vector of a cell goes to the cell with coefficient
`sₙ = TauCeti.realizationChainScale R n`. -/
def cellularChainRealizationLinearEquiv (n : ℕ) :
    letI := realizationCWComplex K
    (cellularChainGroup (univ : Set (Realization K)) (ModuleCat.of R R) n : ModuleCat R) ≃ₗ[R]
      OrderedSimplicialChain K R n :=
  letI := realizationCWComplex K
  (cellularChainBasis (univ : Set (Realization K)) R n).equiv
    (Finsupp.basisSingleOne.unitsSMul fun _ ↦ realizationChainScale R n)
    (realizationCellEquiv K n)

variable {K R}

/-- The image of the cellular basis vector of a cell is the cell with coefficient `sₙ`.
This is not a simp lemma: its left-hand side is not in simp normal form, since the simp lemma
`TauCeti.cellularChainBasis_apply` unfolds the basis vector. -/
theorem cellularChainRealizationLinearEquiv_cellularChainBasis {n : ℕ}
    (c : RealizationCell K n) :
    letI := realizationCWComplex K
    cellularChainRealizationLinearEquiv K R n
        (cellularChainBasis (univ : Set (Realization K)) R n ((realizationCellEquiv K n).symm c)) =
      single c (realizationChainScale R n : R) := by
  simp only [cellularChainRealizationLinearEquiv, Module.Basis.equiv_apply, Equiv.apply_symm_apply,
    Module.Basis.unitsSMul_apply, Finsupp.coe_basisSingleOne, Units.smul_def, smul_single,
    smul_eq_mul, mul_one]

/-- The cellular chain corresponding to the ordered simplicial chain `r • [c]` is
`r * sₙ⁻¹` times the cellular basis vector of `c`. -/
@[simp]
theorem cellularChainRealizationLinearEquiv_symm_single {n : ℕ} (c : RealizationCell K n)
    (r : R) :
    letI := realizationCWComplex K
    (cellularChainRealizationLinearEquiv K R n).symm (single c r) =
      (r * ↑(realizationChainScale R n)⁻¹) • cellularChainBasis (univ : Set (Realization K)) R n
        ((realizationCellEquiv K n).symm c) := by
  rw [LinearEquiv.symm_apply_eq, map_smul,
    cellularChainRealizationLinearEquiv_cellularChainBasis, smul_single, smul_eq_mul, mul_assoc,
    Units.inv_mul, mul_one]

variable (K R)

/-- **The cellular chain complex of a simplicial realization is the ordered simplicial chain
complex.** In degree `n` the cellular basis vector of a cell goes to that cell with coefficient
`sₙ = TauCeti.realizationChainScale R n`. -/
def cellularChainComplexRealizationIso :
    letI := realizationCWComplex K
    cellularChainComplex (univ : Set (Realization K)) (ModuleCat.of R R) ≅
      orderedSimplicialChainComplex K R :=
  letI := realizationCWComplex K
  HomologicalComplex.Hom.isoOfComponents
    (fun n ↦ eqToIso (cellularChainComplex_X _ _ n) ≪≫
      (cellularChainRealizationLinearEquiv K R n).toModuleIso ≪≫
        eqToIso (orderedSimplicialChainComplex_X R n).symm) (by
      rintro _ n rfl
      -- The chain groups agree with the cellular chain groups only through `eqToHom`, since the
      -- body of `TauCeti.cellularChainComplex` is not exposed; cancel the transports, then compare
      -- the two maps on the cellular basis.
      simp only [cellularChainComplex_d, orderedSimplicialChainComplex_d, Iso.trans_hom,
        eqToIso.hom, Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
      rw [cancel_epi, ← Category.assoc, ← Category.assoc, cancel_mono]
      refine ModuleCat.hom_ext ((cellularChainBasis _ R (n + 1)).ext fun i ↦ ?_)
      obtain ⟨c, rfl⟩ := (realizationCellEquiv K (n + 1)).symm.surjective i
      simp only [ModuleCat.hom_comp, LinearMap.comp_apply, LinearEquiv.toModuleIso_hom,
        ModuleCat.hom_ofHom, LinearEquiv.coe_coe]
      rw [cellularChainRealizationLinearEquiv_cellularChainBasis,
        OrderedSimplicialChain.boundary_single, cellularDifferential_realization_cellularChainBasis,
        map_sum]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      rw [map_smul, cellularChainRealizationLinearEquiv_cellularChainBasis,
        cellularIncidence_realization_face_eq_neg_one_pow_mul_realizationFaceIncidence,
        coe_realizationChainScale_succ, smul_single, smul_single, smul_eq_mul, smul_eq_mul,
        mul_assoc])

/-- In degree `n`, the isomorphism `TauCeti.cellularChainComplexRealizationIso` is
`TauCeti.cellularChainRealizationLinearEquiv`, up to the identifications of the chain groups. -/
theorem cellularChainComplexRealizationIso_hom_f (n : ℕ) :
    letI := realizationCWComplex K
    (cellularChainComplexRealizationIso K R).hom.f n =
      eqToHom (cellularChainComplex_X _ _ n) ≫
        (cellularChainRealizationLinearEquiv K R n).toModuleIso.hom ≫
          eqToHom (orderedSimplicialChainComplex_X R n).symm :=
  (rfl)

/-- In degree `n`, the inverse of `TauCeti.cellularChainComplexRealizationIso` is the inverse of
`TauCeti.cellularChainRealizationLinearEquiv`, up to the identifications of the chain groups. -/
theorem cellularChainComplexRealizationIso_inv_f (n : ℕ) :
    letI := realizationCWComplex K
    (cellularChainComplexRealizationIso K R).inv.f n =
      eqToHom (orderedSimplicialChainComplex_X R n) ≫
        (cellularChainRealizationLinearEquiv K R n).toModuleIso.inv ≫
          eqToHom (cellularChainComplex_X _ _ n).symm :=
  (rfl)

/-- **Simplicial homology is singular homology.** The homology of the ordered simplicial chain
complex of `K` is the singular homology of its realization `|K|`, through the cellular chain
complex of `|K|`. -/
def orderedSimplicialHomologyIsoSingularHomology (n : ℕ) :
    (orderedSimplicialChainComplex K R).homology n ≅
      ((AlgebraicTopology.singularHomologyFunctor.{u} (ModuleCat.{u} R) n).obj
        (ModuleCat.of R R)).obj (TopCat.of (Realization K)) :=
  letI := realizationCWComplex K
  (HomologicalComplex.homologyFunctor _ _ n).mapIso (cellularChainComplexRealizationIso K R).symm ≪≫
    cellularSingularHomologyIsoUniv (ModuleCat.of R R) n

end ChainComplex

end TauCeti
