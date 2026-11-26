/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Dieudonne.GaussJordan
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.DieudonneDeterminant

/-!
# Further properties of the Dieudonné determinant over a division ring

Extending `TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.DieudonneDeterminant`, this file proves
uniqueness, block-matrix and permutation formulas, naturality under ring homomorphisms, comparison
with the ordinary determinant over fields, and the finite-rank quotient isomorphism for
`TauCeti.dieudonneDet : GL n D →* Group.Abelianization Dˣ`.

For stabilization invariance and further properties on `AlgebraicK₁`, see
`TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Dieudonne.AlgebraicK1`.

## Main definitions

* `TauCeti.quotientElementarySubgroupDieudonneEquiv`: the canonical isomorphism
  `GL n D ⧸ TauCeti.elementarySubgroup n D ≃* Group.Abelianization Dˣ` for `2 ≤ Fintype.card n`.

## Main results

* `TauCeti.elementarySubgroup_le_ker_dieudonneDet`,
  `TauCeti.dieudonneDet_of_mem_elementarySubgroup`,
  `TauCeti.dieudonneDet_eq_one_iff`: membership in `elementarySubgroup n D` vs. `dieudonneDet = 1`.
* `TauCeti.dieudonneDet_scalar`, `TauCeti.dieudonneDet_permutationGL`,
  `TauCeti.dieudonneDet_upperBlockGL`, `TauCeti.dieudonneDet_lowerBlockGL`,
  `TauCeti.dieudonneDet_fromBlocksGL`, `TauCeti.dieudonneDet_unitsMap_mapMatrix`: values on
  scalar, permutation, block-unipotent, block-diagonal, and ring-mapped matrices.
* `TauCeti.elementarySubgroup_le_ker_of_nontrivial`: when `Dˣ` is nontrivial, every homomorphism
  from `GL n D` to a commutative group vanishes on `elementarySubgroup n D`.
* `TauCeti.eq_dieudonneDet`: uniqueness of `dieudonneDet` among homomorphisms
  `GL n D →* Group.Abelianization Dˣ` determined by their values on single-entry diagonal matrices.
* `TauCeti.dieudonneDet_map`, `TauCeti.dieudonneDet_eq_abelianizationOf_det`: over a field,
  `dieudonneDet` is `Group.Abelianization.of ∘ det`.

## References

* J. Dieudonné, *Les déterminants sur un corps non commutatif*, Bull. Soc. Math. France **71**
  (1943), 27–45.
* E. Artin, *Geometric Algebra*, Interscience (1957), Chapter IV, §1–§2.
* J. Rosenberg, *Algebraic K-Theory and Its Applications*, GTM 147 (1994), §2.2.
* C. A. Weibel, *The K-book: An Introduction to Algebraic K-Theory*, GSM 145 (2013), Chapter III,
  1.2.4, Example 1.3.5, and Exercise 1.2.
-/

public section

noncomputable section

open Matrix

namespace TauCeti

section DivisionRing

variable {n : Type*} [Fintype n] [DecidableEq n] {D : Type*} [DivisionRing D]

/-- The elementary subgroup is contained in the kernel of the Dieudonné determinant. -/
theorem elementarySubgroup_le_ker_dieudonneDet :
    elementarySubgroup n D ≤ (dieudonneDet n D).ker :=
  elementarySubgroup_le_iff.2 fun _ _ hij c ↦ dieudonneDet_transvectionUnit hij c

/-- Every matrix in the elementary subgroup has Dieudonné determinant `1`. -/
theorem dieudonneDet_of_mem_elementarySubgroup {g : GL n D}
    (hg : g ∈ elementarySubgroup n D) : dieudonneDet n D g = 1 :=
  elementarySubgroup_le_ker_dieudonneDet hg

/-- In rank at least two, an invertible matrix over a division ring has Dieudonné determinant `1`
if and only if it belongs to the elementary subgroup. -/
theorem dieudonneDet_eq_one_iff (hn : 2 ≤ Fintype.card n) {g : GL n D} :
    dieudonneDet n D g = 1 ↔ g ∈ elementarySubgroup n D := by
  rw [← MonoidHom.mem_ker, ker_dieudonneDet hn]

/-- A scalar matrix `scalar n u` has Dieudonné determinant
`Group.Abelianization.of u ^ Fintype.card n`. -/
@[simp]
theorem dieudonneDet_scalar (u : Dˣ) :
    dieudonneDet n D (Matrix.GeneralLinearGroup.scalar n u) =
      Group.Abelianization.of u ^ Fintype.card n := by
  rw [← diagGL_const, dieudonneDet_diagGL, Finset.prod_const, Finset.card_univ]

/-- When `Dˣ` is nontrivial, every homomorphism from `GL n D` into a commutative group vanishes on
`TauCeti.elementarySubgroup n D`. (Over `𝔽₂` in rank `2`, `GL₂(𝔽₂) = E₂(𝔽₂) ≅ S₃` admits the
nontrivial sign homomorphism to `ℤˣ`, so `[Nontrivial Dˣ]` cannot be dropped.) -/
theorem elementarySubgroup_le_ker_of_nontrivial [Nontrivial Dˣ] {G : Type*} [CommGroup G]
    (φ : GL n D →* G) :
    elementarySubgroup n D ≤ φ.ker := by
  obtain ⟨u, hu⟩ := exists_ne (1 : Dˣ)
  have hu_sub : (u : D) - 1 ≠ 0 := sub_ne_zero.2 fun h ↦ hu (Units.ext h)
  refine elementarySubgroup_le_iff.2 fun a b hab c ↦ ?_
  let c' : D := ((u : D) - 1)⁻¹ * c
  have hconj := congrArg φ
    (diagGL_mul_transvectionUnit_mul_inv hab (Pi.mulSingle a u) c')
  simp only [map_mul, map_inv, mul_inv_cancel_comm, Pi.mulSingle_eq_same,
    Pi.mulSingle_eq_of_ne hab.symm, inv_one, Units.val_one, mul_one] at hconj
  have hc : c + c' = (u : D) * c' := by
    have hcc' : ((u : D) - 1) * c' = c := mul_inv_cancel_left₀ hu_sub c
    rw [← hcc', sub_one_mul, sub_add_cancel]
  have hmul : φ (transvectionUnit hab c) * φ (transvectionUnit hab c') =
      φ (transvectionUnit hab c') := by
    rw [← map_mul, ← transvectionUnit_add, hc, ← hconj]
  exact mul_right_cancel (hmul.trans (one_mul _).symm)

/-- **Uniqueness of the Dieudonné determinant.** A homomorphism
`GL n D →* Group.Abelianization Dˣ` that sends `diagGL (Pi.mulSingle i u)` to
`Group.Abelianization.of u` at some index `i : n` equals `dieudonneDet n D`. -/
theorem eq_dieudonneDet {φ : GL n D →* Group.Abelianization Dˣ} (i : n)
    (hdiag : ∀ u : Dˣ, φ (diagGL (Pi.mulSingle i u)) = Group.Abelianization.of u) :
    φ = dieudonneDet n D := by
  rcases subsingleton_or_nontrivial Dˣ with hsub | hnt
  · have : Subsingleton (Group.Abelianization Dˣ) :=
      (Group.Abelianization.surjective_of Dˣ).subsingleton
    ext g
    exact Subsingleton.elim _ _
  · exact Matrix.GeneralLinearGroup.hom_ext_of_elementarySubgroup_le_ker
      (elementarySubgroup_le_ker_of_nontrivial φ)
      elementarySubgroup_le_ker_dieudonneDet i fun u ↦
        (hdiag u).trans (dieudonneDet_diagGL_mulSingle i u).symm

/-- The Dieudonné determinant of a permutation matrix is the image of `Equiv.Perm.sign σ`. -/
@[simp]
theorem dieudonneDet_permutationGL (σ : Equiv.Perm n) :
    dieudonneDet n D (permutationGL (k := D) σ) =
      Group.Abelianization.of (Units.map (Int.castRingHom D).toMonoidHom (Equiv.Perm.sign σ)) := by
  induction σ using Equiv.Perm.swap_induction_on with
  | one => simp
  | swap_mul τ i j hij ih =>
    have hweyl :
        dieudonneDet n D (permutationGL (k := D) (Equiv.swap i j)) =
          Group.Abelianization.of (-1 : Dˣ) := by
      have h := congrArg (dieudonneDet n D)
        (transvectionWeylElement_eq_diagGL_mul_permutationGL (A := D) hij)
      have h1 : dieudonneDet n D (transvectionWeylElement (A := D) hij) = 1 := by
        simp [transvectionWeylElement_def]
      rw [h1, map_mul, dieudonneDet_diagGL_mulSingle] at h
      have hsq : Group.Abelianization.of (-1 : Dˣ) * Group.Abelianization.of (-1 : Dˣ) = 1 := by
        rw [← map_mul, neg_mul_neg, one_mul, map_one]
      calc dieudonneDet n D (permutationGL (k := D) (Equiv.swap i j))
          = (Group.Abelianization.of (-1 : Dˣ) * Group.Abelianization.of (-1 : Dˣ)) *
              dieudonneDet n D (permutationGL (k := D) (Equiv.swap i j)) := by rw [hsq, one_mul]
        _ = Group.Abelianization.of (-1 : Dˣ) := by rw [mul_assoc, ← h, mul_one]
    rw [map_mul, map_mul, hweyl, ih, map_mul Equiv.Perm.sign, Equiv.Perm.sign_swap hij,
      map_mul (Units.map _), Group.Abelianization.of.map_mul]
    simp

/-- Every upper block-unipotent matrix has Dieudonné determinant `1`. -/
@[simp]
theorem dieudonneDet_upperBlockGL {m : Type*} [Fintype m] [DecidableEq m] (X : Matrix n m D) :
    dieudonneDet (n ⊕ m) D (Matrix.upperBlockGL X) = 1 :=
  dieudonneDet_of_mem_elementarySubgroup (Matrix.upperBlockGL_mem_elementarySubgroup X)

/-- Every lower block-unipotent matrix has Dieudonné determinant `1`. -/
@[simp]
theorem dieudonneDet_lowerBlockGL {m : Type*} [Fintype m] [DecidableEq m] (Y : Matrix m n D) :
    dieudonneDet (n ⊕ m) D (Matrix.lowerBlockGL Y) = 1 :=
  dieudonneDet_of_mem_elementarySubgroup (Matrix.lowerBlockGL_mem_elementarySubgroup Y)

/-- The Dieudonné determinant is multiplicative across block-diagonal sums `u ⊕ v`. -/
@[simp]
theorem dieudonneDet_fromBlocksGL {m : Type*} [Fintype m] [DecidableEq m]
    (u : GL n D) (v : GL m D) :
    dieudonneDet (n ⊕ m) D (fromBlocksGL (u, v)) = dieudonneDet n D u * dieudonneDet m D v := by
  obtain ⟨eu, heu, d₁, rfl⟩ := exists_mem_elementarySubgroup_mul_diagGL u
  obtain ⟨ev, hev, d₂, rfl⟩ := exists_mem_elementarySubgroup_mul_diagGL v
  have hprod : (eu * diagGL d₁, ev * diagGL d₂) =
      (eu, (1 : GL m D)) * ((1 : GL n D), ev) * (diagGL d₁, diagGL d₂) := by
    ext <;> simp
  have heu' : fromBlocksGL (eu, (1 : GL m D)) ∈ elementarySubgroup (n ⊕ m) D :=
    map_elementarySubgroup_le_elementarySubgroup ⟨eu, heu, rfl⟩
  have hev' : fromBlocksGL ((1 : GL n D), ev) ∈ elementarySubgroup (n ⊕ m) D :=
    map_elementarySubgroup_le_elementarySubgroup_inr ⟨ev, hev, rfl⟩
  rw [hprod]
  simp [-Prod.mk_mul_mk, dieudonneDet_of_mem_elementarySubgroup heu',
    dieudonneDet_of_mem_elementarySubgroup hev', dieudonneDet_of_mem_elementarySubgroup heu,
    dieudonneDet_of_mem_elementarySubgroup hev, dieudonneDet_diagGL, Fintype.prod_sum_type]

/-- The Dieudonné determinant is natural with respect to ring homomorphisms `D →+* E` between
division rings. -/
@[simp]
theorem dieudonneDet_unitsMap_mapMatrix {E : Type*} [DivisionRing E] (f : D →+* E) (g : GL n D) :
    dieudonneDet n E (Units.map (f.mapMatrix (m := n) : Matrix n n D →* Matrix n n E) g) =
      Group.Abelianization.map (Units.map (f : D →* E)) (dieudonneDet n D g) := by
  obtain ⟨e, he, d, rfl⟩ := exists_mem_elementarySubgroup_mul_diagGL g
  have hfe : Units.map (f.mapMatrix (m := n) : Matrix n n D →* Matrix n n E) e ∈
      elementarySubgroup n E :=
    f.map_elementarySubgroup_le ⟨e, he, rfl⟩
  have hmap_diag :
      Units.map (f.mapMatrix (m := n) : Matrix n n D →* Matrix n n E) (diagGL d) =
        diagGL (fun i ↦ Units.map (f : D →* E) (d i)) := by
    ext a b; simp
  simp [dieudonneDet_of_mem_elementarySubgroup hfe, dieudonneDet_of_mem_elementarySubgroup he,
    hmap_diag, dieudonneDet_diagGL]

end DivisionRing

section Field

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Naturality of the Dieudonné determinant under `Matrix.GeneralLinearGroup.map` over fields. -/
@[simp]
theorem dieudonneDet_map {F K : Type*} [Field F] [Field K] (f : F →+* K) (g : GL n F) :
    dieudonneDet n K (Matrix.GeneralLinearGroup.map f g) =
      Group.Abelianization.map (Units.map (f : F →* K)) (dieudonneDet n F g) :=
  dieudonneDet_unitsMap_mapMatrix f g

/-- Over a field `F`, the Dieudonné determinant agrees with the ordinary determinant followed by
`Group.Abelianization.of : Fˣ →* Group.Abelianization Fˣ`. -/
theorem dieudonneDet_eq_abelianizationOf_det {F : Type*} [Field F] (g : GL n F) :
    dieudonneDet n F g = Group.Abelianization.of g.det := by
  obtain ⟨e, he, d, rfl⟩ := exists_mem_elementarySubgroup_mul_diagGL g
  have hdet_e : e.det = 1 := MonoidHom.mem_ker.1 (elementarySubgroup_le_ker_det he)
  simp [dieudonneDet_of_mem_elementarySubgroup he, hdet_e, det_diagGL, dieudonneDet_diagGL]

end Field

/-! ## Finite-rank quotient by the elementary subgroup -/

/-- In rank at least two, the Dieudonné determinant descends to a canonical isomorphism
`GL n D ⧸ elementarySubgroup n D ≃* Group.Abelianization Dˣ`. -/
def quotientElementarySubgroupDieudonneEquiv (n : Type*) [Fintype n] [DecidableEq n]
    (D : Type*) [DivisionRing D] (hn : 2 ≤ Fintype.card n) :
    GL n D ⧸ elementarySubgroup n D ≃* Group.Abelianization Dˣ :=
  haveI : Nonempty n := Fintype.card_pos_iff.mp (by omega)
  (QuotientGroup.quotientMulEquivOfEq (ker_dieudonneDet (n := n) (D := D) hn).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective (dieudonneDet n D) dieudonneDet_surjective)

/-- `TauCeti.quotientElementarySubgroupDieudonneEquiv` evaluates on a coset `QuotientGroup.mk g` as
`dieudonneDet n D g`. -/
@[simp]
theorem quotientElementarySubgroupDieudonneEquiv_mk {n : Type*} [Fintype n] [DecidableEq n]
    {D : Type*} [DivisionRing D] (hn : 2 ≤ Fintype.card n) (g : GL n D) :
    quotientElementarySubgroupDieudonneEquiv n D hn (QuotientGroup.mk g) =
      dieudonneDet n D g := by
  simp [quotientElementarySubgroupDieudonneEquiv, QuotientGroup.quotientKerEquivOfSurjective]

/-- The inverse of `TauCeti.quotientElementarySubgroupDieudonneEquiv` sends
`Group.Abelianization.of u` to the coset of `diagGL (Pi.mulSingle i u)` at any index `i : n`. -/
theorem quotientElementarySubgroupDieudonneEquiv_symm_of {n : Type*} [Fintype n] [DecidableEq n]
    {D : Type*} [DivisionRing D] (hn : 2 ≤ Fintype.card n) (i : n) (u : Dˣ) :
    (quotientElementarySubgroupDieudonneEquiv n D hn).symm (Group.Abelianization.of u) =
      QuotientGroup.mk (diagGL (Pi.mulSingle i u)) := by
  rw [← dieudonneDet_diagGL_mulSingle i u,
    ← quotientElementarySubgroupDieudonneEquiv_mk hn, MulEquiv.symm_apply_apply]

end TauCeti

end
