/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Homotopy.Hurewicz.One.Naturality
public import TauCeti.AlgebraicTopology.UniversalCover.Torus.FundamentalGroup

/-!
# The first homology of a torus, naturally in integer matrices

For a family of nonzero periods `p : ι → ℝ`, the first singular homology group with integer
coefficients of the torus `Tⁱ = ∀ i, AddCircle (p i)` is `ι → ℤ`
(`TauCeti.torusFirstHomologyEquiv`). The isomorphism is the composite of the Hurewicz isomorphism
`H₁(Tⁱ; ℤ) ≅ π₁(Tⁱ, 0)ᵃᵇ` (`TauCeti.HurewiczOne.hurewiczHomologyAddEquiv`) with the computation
`π₁(Tⁱ, 0) ≅ ℤⁱ` (`AddCircle.piFundamentalGroupMulEquivZero`), the fundamental group being already
commutative. It sends the class of the straight loop `TauCeti.torusLoop p n`, which winds `n i`
times around the `i`-th circle, to `n` (`TauCeti.torusFirstHomologyEquiv_loopClass`).

For a common period `p`, an integer matrix `A : Matrix κ ι ℤ` induces the map of tori
`Matrix.smulVecHom A (AddCircle p) : Tⁱ → Tᵏ`, and under these identifications the map it
induces on first homology is `n ↦ A *ᵥ n`
(`TauCeti.torusFirstHomologyEquiv_homologyMap_smulVecHom`). This is the action of integer matrices
on the first homology of a torus; the higher homology of a torus is the exterior algebra on it,
which is not proved here. The torus is modelled here as a product of
additive circles, on which integer matrices act. The ranks of all homology groups of the
homeomorphic product of unit spheres are computed in `ModuleCat.finrank_singularHomology_torus`.

## Main definitions and results

* `TauCeti.torusFirstHomologyEquiv`: the isomorphism `H₁(Tⁱ; ℤ) ≃ₗ[ℤ] (ι → ℤ)`.
* `TauCeti.torusFirstHomologyEquiv_loopClass`, `TauCeti.torusFirstHomologyEquiv_symm_apply`: the
  class of the straight loop of `n` corresponds to `n`.
* `TauCeti.torusFirstHomologyEquiv_homologyMap_smulVecHom`: naturality in integer matrices.

## References

* A. Hatcher, *Algebraic Topology*, Theorem 2A.1 for the Hurewicz isomorphism in degree one, and
  Proposition 1.12 for the fundamental group of a product.
-/

public section

noncomputable section

open CategoryTheory Matrix TauCeti.HurewiczOne

namespace TauCeti

variable {ι : Type} (p : ι → ℝ) (hp : ∀ i, p i ≠ 0)

/-- The first singular homology group with integer coefficients of the torus
`∀ i, AddCircle (p i)` is `ι → ℤ`. -/
def torusFirstHomologyEquiv :
    ((singularChains ℤ).obj (TopCat.of (∀ i, AddCircle (p i)))).homology 1 ≃ₗ[ℤ] (ι → ℤ) :=
  ((hurewiczHomologyAddEquiv (X := TopCat.of (∀ i, AddCircle (p i))) 0).symm.trans
    (AddEquiv.toMultiplicativeRight.symm
      ((AddCircle.piFundamentalGroupMulEquivZero hp).abelianizationCongr.trans
        (Abelianization.equivOfComm.symm.trans
          (MulEquiv.funMultiplicative ι ℤ).symm)))).toIntLinearEquiv

/-- The class of the straight loop `TauCeti.torusLoop p n` corresponds to `n`. -/
@[simp]
theorem torusFirstHomologyEquiv_loopClass (n : ι → ℤ) :
    torusFirstHomologyEquiv p hp
        (H₁AddEquivHomology _ (loopClass (X := TopCat.of (∀ i, AddCircle (p i)))
          (torusLoop p n))) = n := by
  have h := (AddEquiv.symm_apply_eq _).2
    (hurewiczHomologyAddEquiv_ofMul_of_mk (X := TopCat.of (∀ i, AddCircle (p i)))
      (torusLoop p n)).symm
  rw [torusFirstHomologyEquiv, AddEquiv.coe_toIntLinearEquiv, AddEquiv.trans_apply, h]
  funext i
  simp

/-- The inverse of `TauCeti.torusFirstHomologyEquiv` sends `n` to the class of the straight loop
`TauCeti.torusLoop p n`, which winds `n i` times around the `i`-th circle. -/
theorem torusFirstHomologyEquiv_symm_apply (n : ι → ℤ) :
    (torusFirstHomologyEquiv p hp).symm n =
      H₁AddEquivHomology _ (loopClass (X := TopCat.of (∀ i, AddCircle (p i))) (torusLoop p n)) := by
  rw [LinearEquiv.symm_apply_eq, torusFirstHomologyEquiv_loopClass]

/-- **The first homology of a torus is natural in integer matrices.** Under the identifications
`H₁(Tⁱ; ℤ) ≅ ℤⁱ` of `TauCeti.torusFirstHomologyEquiv`, the map induced on first homology by the
map of tori `Matrix.smulVecHom A (AddCircle p)` is multiplication by the matrix `A`. -/
theorem torusFirstHomologyEquiv_homologyMap_smulVecHom [Fintype ι] {κ : Type} (A : Matrix κ ι ℤ)
    {p : ℝ} (hp : p ≠ 0) (x : ((singularChains ℤ).obj (TopCat.of (ι → AddCircle p))).homology 1) :
    torusFirstHomologyEquiv (fun _ : κ ↦ p) (fun _ ↦ hp)
        ((HomologicalComplex.homologyMap ((singularChains ℤ).map
          (TopCat.ofHom
            (A.smulVecHom (AddCircle p) : C(ι → AddCircle p, κ → AddCircle p)))) 1).hom x) =
      A *ᵥ torusFirstHomologyEquiv (fun _ : ι ↦ p) (fun _ ↦ hp) x := by
  obtain ⟨n, rfl⟩ := (torusFirstHomologyEquiv (fun _ : ι ↦ p) (fun _ ↦ hp)).symm.surjective x
  rw [torusFirstHomologyEquiv_symm_apply, homologyMap_H₁AddEquivHomology_loopClass]
  -- The image of the straight loop of `n` is the straight loop of `A *ᵥ n`, based at the image
  -- of `0`; loops with the same underlying map have the same homology class. The underlying map
  -- of `Path.map` is the composite (`Path.map_coe`), so its chain is that of the composite.
  have h : loopClass ((torusLoop (fun _ : ι ↦ p) n).map
      (TopCat.ofHom
        (A.smulVecHom (AddCircle p) : C(ι → AddCircle p, κ → AddCircle p))).hom.continuous) =
      loopClass (X := TopCat.of (κ → AddCircle p)) (torusLoop (fun _ ↦ p) (A *ᵥ n)) := by
    rw [loopClass_eq_iff,
      sub_eq_zero.2 (congrArg (pathChain ℤ) (smulVecHom_comp_torusLoop A p n))]
    exact zero_mem _
  rw [h, torusFirstHomologyEquiv_loopClass, torusFirstHomologyEquiv_loopClass]

end TauCeti
