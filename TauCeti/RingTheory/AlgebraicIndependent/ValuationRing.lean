/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.AlgebraicIndependent.Defs
public import Mathlib.RingTheory.Valuation.ValuationRing
public import Mathlib.Algebra.Module.Torsion.Free
import Mathlib.RingTheory.MvPolynomial.Tower
import TauCeti.RingTheory.Valuation.FinsetDvd

/-!
# Algebraic independence over a valuation ring through a residue field

Let `R` be a valuation ring and `A` a torsion-free `R`-algebra. If the image of a family `x` of
elements of `A` in some algebra over a residue field `κ` of `R` is algebraically independent over
`κ`, then `x` is algebraically independent over `R`
(`AlgebraicIndependent.of_comp_of_valuationRing`).

The proof divides a polynomial relation `G` among the `x i` by a coefficient `c` of `G` dividing
all the others, which exists because divisibility is total in a valuation ring. The quotient `H`
is again a relation, since `A` is torsion-free, and has a coefficient equal to `1`, so its image
over `κ` is a nonzero relation among the images of the `x i`.

This is what bounds the dimension of every fibre of a flat finitely generated algebra over a
valuation ring by the dimension of its generic fibre: elements algebraically independent in a
special fibre lift to elements algebraically independent in the generic fibre.
-/

public section

namespace AlgebraicIndependent

/-- Let `R` be a valuation ring and `A` a torsion-free `R`-algebra. A family `x` in `A` whose image
under an `R`-algebra map `f : A → B` is algebraically independent over some nontrivial `R`-algebra
`S`, for instance a residue field of `R`, is algebraically independent over `R`. -/
theorem of_comp_of_valuationRing {ι R S A B : Type*} [CommRing R] [IsDomain R] [ValuationRing R]
    [CommRing S] [Nontrivial S] [Algebra R S] [CommRing A] [Algebra R A]
    [Module.IsTorsionFree R A] [CommRing B] [Algebra R B] [Algebra S B] [IsScalarTower R S B]
    (f : A →ₐ[R] B) {x : ι → A} (hx : AlgebraicIndependent S fun i ↦ f (x i)) :
    AlgebraicIndependent R x := by
  -- Divide a nonzero relation `G` by a coefficient `c` dividing all others: the quotient `H` is
  -- still a relation, since `A` is torsion-free, and has a coefficient `1`, so it stays nonzero
  -- over `S`.
  refine algebraicIndependent_iff.mpr fun G hG ↦ by_contra fun hG0 ↦ ?_
  obtain ⟨m, hm, hdvd⟩ := TauCeti.PreValuationRing.exists_mem_forall_dvd
    (MvPolynomial.support_nonempty.mpr hG0) G.coeff
  obtain ⟨H, hGH⟩ := (MvPolynomial.C_dvd_iff_dvd_coeff _ _).mpr fun i ↦ by
    by_cases hi : i ∈ G.support
    · exact hdvd i hi
    · rw [MvPolynomial.notMem_support_iff.mp hi]
      exact dvd_zero _
  have hc : G.coeff m ≠ 0 := MvPolynomial.mem_support_iff.mp hm
  have hHm : H.coeff m = 1 := by
    refine mul_left_cancel₀ hc ?_
    conv_rhs => rw [mul_one, hGH]
    rw [MvPolynomial.coeff_C_mul]
  have hH : MvPolynomial.aeval x H = 0 := by
    rw [hGH, map_mul, MvPolynomial.aeval_C, ← Algebra.smul_def] at hG
    exact Module.IsTorsionFree.isSMulRegular (IsRegular.of_ne_zero hc)
      (hG.trans (smul_zero _).symm)
  have hmap : MvPolynomial.map (algebraMap R S) H = 0 := by
    refine algebraicIndependent_iff.mp hx _ ?_
    rw [MvPolynomial.aeval_map_algebraMap, ← MvPolynomial.comp_aeval_apply, hH, map_zero]
  simpa [MvPolynomial.coeff_map, hHm] using congr($hmap |>.coeff m)

end AlgebraicIndependent
