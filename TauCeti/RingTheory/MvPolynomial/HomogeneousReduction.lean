/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.RingTheory.MvPolynomial.MonomialOrder
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.RingTheory.LocalRing.RingHom.Basic

/-!
# Reduction of homogeneous polynomials modulo an ideal via leading monomials

Let `φ : A →+* k` be a local ring homomorphism between commutative rings, `ρ : A →+* B` a ring
homomorphism, `o : MonomialOrder J` a monomial order on finitely many variables `J`, and
`I : Ideal (MvPolynomial J B)`. Suppose that for every exponent `m ∈ W` of total degree `d` there
exists a homogeneous degree-`d` polynomial `g : MvPolynomial J A` whose image `g.map ρ` lies in `I`
and whose reduction `g.map φ` has leading monomial `o.degree (g.map φ) = m` with unit leading
coefficient. Then the coefficients of these forms at exponents of degree `d` in `W` form a square
matrix that is lower triangular modulo `φ` with unit diagonal; since `φ` is a local homomorphism,
its determinant is a unit in `A`, hence its image over `B` is invertible. Subtracting a `B`-linear
combination of the images `g.map ρ ∈ I` eliminates all monomials in `W`, showing that the degree-`d`
monomials outside `W` span the image of `homogeneousSubmodule J B d` modulo `I`.

## Main results

* `MvPolynomial.map_homogeneousSubmodule_eq_map_restrictSupport`: modulo `I`, the forms of degree
  `d` have the same image as those supported on degree-`d` monomials outside `W`.

## Provenance

Adapted from `grh-lean` (https://github.com/lsernau/grh-lean at commit
`72fead102f663d5c7a407964a13dc0cf9d977207`, Apache 2.0, Copyright 2026 Anthropic, PBC), file
`src/Lib/Shimura/ThetaModuli/FlatClosure.lean` (`imageMod_homogeneousSubmodule_eq`), generalized
from a field codomain `k` and a fixed ideal `T` to any commutative ring `k` with unit leading
coefficients, universe-polymorphic rings `A`, `k`, `B` and index `J`.
-/

public section

open MvPolynomial Matrix

namespace MvPolynomial

/-- Division with remainder for homogeneous polynomials: if `φ : A →+* k` is a local homomorphism
and every exponent `m ∈ W` of degree `d` is the `o`-leading monomial (with unit leading
coefficient) of `g.map φ` for some degree-`d` homogeneous `g : MvPolynomial J A` with
`g.map ρ ∈ I`, then modulo `I` the degree-`d` forms are spanned by monomials of degree `d` outside
`W`. -/
theorem map_homogeneousSubmodule_eq_map_restrictSupport
    {J A k B : Type*} [Finite J] [CommRing A] [CommRing k] [CommRing B]
    (φ : A →+* k) [IsLocalHom φ] (ρ : A →+* B) (o : MonomialOrder J)
    (I : Ideal (MvPolynomial J B)) (d : ℕ) {W : Set (J →₀ ℕ)}
    (hlead : ∀ m ∈ W, m.degree = d → ∃ g : MvPolynomial J A,
      g.map ρ ∈ I ∧ o.degree (g.map φ) = m ∧ g.IsHomogeneous d ∧ IsUnit ((g.map φ).coeff m)) :
    (homogeneousSubmodule J B d).map (Ideal.Quotient.mkₐ B I).toLinearMap =
      (restrictSupport B (Finsupp.degree ⁻¹' {d} \ W)).map
        (Ideal.Quotient.mkₐ B I).toLinearMap := by
  classical
  let V : Set (J →₀ ℕ) := Finsupp.degree ⁻¹' {d} ∩ W
  have hVfin : Finite V := by
    let ι : V → (J → Fin (d + 1)) := fun m j ↦
      ⟨m.val j, Nat.lt_succ_of_le (by
        have hm : m.val.degree = d := m.prop.left
        rw [← hm, Finsupp.degree]
        by_cases hj : j ∈ m.val.support
        · exact Finset.single_le_sum (f := fun j ↦ m.val j) (fun _ _ ↦ Nat.zero_le _) hj
        · simp [Finsupp.notMem_support_iff.1 hj])⟩
    exact Finite.of_injective ι fun m₁ m₂ h ↦
      Subtype.ext (Finsupp.ext fun j ↦ congrArg Fin.val (congrFun h j))
  let _ : Fintype V := Fintype.ofFinite V
  have hchoice (m : V) : ∃ g : MvPolynomial J A,
      g.map ρ ∈ I ∧ o.degree (g.map φ) = m.val ∧ g.IsHomogeneous d ∧
        IsUnit ((g.map φ).coeff m.val) :=
    hlead m.val m.prop.right m.prop.left
  choose g hgI hg_lead hg_form hg_unit using hchoice
  have hle : restrictSupport B (Finsupp.degree ⁻¹' {d} \ W) ≤ homogeneousSubmodule J B d :=
    (restrictSupport_mono B Set.sdiff_subset).trans
      (homogeneousSubmodule_eq_finsupp_supported J B d).ge
  refine (Submodule.map_mono hle).antisymm' ?_
  rintro x ⟨f, hf, hfx⟩
  let G : Matrix V V A := Matrix.of fun m m' : V ↦ (g m).coeff m'.val
  let ordV : LinearOrder V := LinearOrder.lift' (fun m : V ↦ o.toSyn m.val)
    fun m₁ m₂ h ↦ Subtype.ext (o.toSyn.injective h)
  have htri : @IsLowerTriangular V k _ ordV.toLT (φ.mapMatrix G) := fun m m' hlt ↦ by
    have hlt' : o.toSyn (o.degree ((g m).map φ)) < o.toSyn m'.val := by rwa [hg_lead m]
    simpa [G, coeff_map] using o.coeff_eq_zero_of_lt hlt'
  have hdet_k : IsUnit (φ G.det) := by
    rw [φ.map_det, @det_of_isLowerTriangular V k _ _ _ ordV (φ.mapMatrix G) htri]
    exact Finset.prod_induction _ IsUnit (fun _ _ ↦ IsUnit.mul) isUnit_one fun m _ ↦ by
      simpa [G, coeff_map] using hg_unit m
  have hG : IsUnit (ρ.mapMatrix G) :=
    (G.isUnit_iff_isUnit_det.2 (IsUnit.of_map φ G.det hdet_k)).map ρ.mapMatrix
  obtain ⟨c, hc⟩ := vecMul_surjective_iff_isUnit.2 hG fun m : V ↦ f.coeff m.val
  have hform : f - ∑ m : V, c m • (g m).map ρ ∈ homogeneousSubmodule J B d :=
    sub_mem hf (Submodule.sum_smul_mem _ c fun m _ ↦ (hg_form m).map ρ)
  refine ⟨f - ∑ m : V, c m • (g m).map ρ, (mem_restrictSupport_iff B).2 fun a ha ↦ ?_, ?_⟩
  · have hadeg : a ∈ Finsupp.degree ⁻¹' {d} := (hform.degree_eq_sum_deg_support ha).symm
    refine ⟨hadeg, fun haW ↦ ?_⟩
    have hcoeff : ∑ m : V, c m * ρ ((g m).coeff a) = f.coeff a := by
      simpa [vecMul_eq_sum, G] using congrFun hc ⟨a, hadeg, haW⟩
    simp [← hcoeff, coeff_map] at ha
  · have hsum : ∑ m : V, c m • (g m).map ρ ∈ I :=
      sum_mem fun m _ ↦ Submodule.smul_of_tower_mem I _ (hgI m)
    rwa [AlgHom.toLinearMap_apply, map_sub, Ideal.Quotient.mkₐ_eq_mk,
      Ideal.Quotient.eq_zero_iff_mem.2 hsum, sub_zero]

end MvPolynomial
