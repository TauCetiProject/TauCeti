/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.IntegralLattice.RootLattice.TypeE.CosetMinimum
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.E7.MinusculeWeight

/-!
# The E₇ minuscule orbit in the literal dual lattice

Pairing with the Bourbaki simple roots identifies the dual E₇ lattice with the integral weight
lattice in fundamental-weight coordinates. Under this identification the existing 56-entry
minuscule weight table gives distinct dual vectors, all in the discriminant class of `ϖ₇`, of
squared norm `3/2`. They are therefore shortest representatives of the nonzero class.

The realization commutes with simple reflections. The norm and discriminant-class equations
follow along the reflection paths of the existing weight table, rather than a second enumeration.
Negation preserves the realized family. Conversely every dual vector of squared norm `3/2`
belongs to this family: positivity bounds its integral simple-root pairings by `-1` and `1`,
and the inverse Cartan matrix reduces exhaustiveness to a checked finite calculation.

## References

* J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, Chapter 4, §8.2.
* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4–6*, Plate VI.

The weight table and reflection paths are `TauCeti.DynkinType.e7MinusculeWeight` and
`TauCeti.DynkinType.exists_e7MinusculeReflections_eq`. The dual-coordinate construction uses
`IntegralLattice.dualPairingEquiv` and adapts the parallel E₆ realization by the Tau Ceti
contributors in https://github.com/TauCetiProject/TauCeti/pull/30723.
-/

public section

namespace TauCeti.IntegralLattice

open Module DynkinType

private noncomputable def e7Basis : Basis (Fin 7) ℤ typeE₇RootLattice :=
  (ofGramMatrix.basis (Pi.basisFun ℚ (Fin 7)) (CartanMatrix.E 7)
    (CartanMatrix.E_isSymm 7)).map
      (LinearEquiv.ofEq _ _ (by
        ext x
        rw [mem_typeE₇RootLattice_carrier_iff, mem_ofGramMatrix_basisFun_carrier_iff]))

private theorem coe_e7Basis (i : Fin 7) : (e7Basis i : Fin 7 → ℚ) = typeE₇SimpleRoot i := by
  simp only [e7Basis, Basis.map_apply, LinearEquiv.coe_ofEq_apply, ofGramMatrix.coe_basis]
  ext j
  simp [typeE₇SimpleRoot_apply, Pi.basisFun_apply, Pi.single_apply]

/-- The dual E₇ lattice identified with fundamental-weight coordinates by simple-root pairing. -/
noncomputable def typeE₇DualWeightEquiv : typeE₇RootLattice.dualCarrier ≃ₗ[ℤ] (Fin 7 → ℤ) :=
  typeE₇RootLattice.dualPairingEquiv.trans e7Basis.dualBasis.equivFun

/-- Fundamental-weight coordinates are the integral pairings with the simple roots. -/
@[simp]
theorem typeE₇DualWeightEquiv_apply (x : typeE₇RootLattice.dualCarrier) (i : Fin 7) :
    (typeE₇DualWeightEquiv x i : ℚ) = typeE₇RootLattice.form x (typeE₇SimpleRoot i) := by
  simp only [typeE₇DualWeightEquiv, LinearEquiv.trans_apply, Basis.dualBasis_equivFun,
    dualPairingEquiv_cast, coe_e7Basis]

/-- The 56 minuscule weights, realized as vectors of the literal dual E₇ lattice. -/
noncomputable def typeE₇MinusculeDual (a : Fin 56) : typeE₇RootLattice.dualCarrier :=
  typeE₇DualWeightEquiv.symm (e7MinusculeWeight a)

/-- The realized weight has the fundamental coordinates of the original weight table. -/
@[simp]
theorem typeE₇DualWeightEquiv_minusculeDual (a : Fin 56) :
    typeE₇DualWeightEquiv (typeE₇MinusculeDual a) = e7MinusculeWeight a :=
  typeE₇DualWeightEquiv.apply_symm_apply _

/-- Simple-root pairings of realized minuscule weights read off their table entries. -/
@[simp]
theorem form_typeE₇MinusculeDual_simpleRoot (a : Fin 56) (i : Fin 7) :
    typeE₇RootLattice.form (typeE₇MinusculeDual a) (typeE₇SimpleRoot i) =
      (e7MinusculeWeight a i : ℚ) := by
  rw [← typeE₇DualWeightEquiv_apply, typeE₇DualWeightEquiv_minusculeDual]

/-- The realization preserves distinctness of minuscule weights. -/
theorem typeE₇MinusculeDual_injective : Function.Injective typeE₇MinusculeDual := by
  intro a b h
  apply e7MinusculeWeight_injective
  simpa only [typeE₇DualWeightEquiv_minusculeDual] using congrArg typeE₇DualWeightEquiv h

/-- The highest table weight is the previously chosen dual representative `ϖ₇`. -/
@[simp]
theorem typeE₇MinusculeDual_zero : typeE₇MinusculeDual 0 = typeE₇MinusculeWeightDual := by
  apply typeE₇DualWeightEquiv.injective
  ext i
  apply Int.cast_injective (α := ℚ)
  rw [typeE₇DualWeightEquiv_minusculeDual, typeE₇DualWeightEquiv_apply,
    coe_typeE₇MinusculeWeightDual, form_typeE₇MinusculeWeight_typeE₇SimpleRoot,
    e7MinusculeWeight_zero]
  simp [Pi.single_apply]

private noncomputable def e7SimpleDual (i : Fin 7) : typeE₇RootLattice.dualCarrier :=
  ⟨e7Basis i, typeE₇RootLattice.le_dualCarrier (e7Basis i).property⟩

private theorem weight_e7SimpleDual (i : Fin 7) :
    typeE₇DualWeightEquiv (e7SimpleDual i) = CartanMatrix.E 7 i := by
  ext j
  apply Int.cast_injective (α := ℚ)
  rw [typeE₇DualWeightEquiv_apply]
  exact (congrArg (fun x ↦ typeE₇RootLattice.form x (typeE₇SimpleRoot j)) (coe_e7Basis i)).trans
    (form_typeE₇SimpleRoot_typeE₇SimpleRoot i j)

private theorem minusculeDual_reflection (i : Fin 7) (a : Fin 56) :
    typeE₇MinusculeDual (e7MinusculeReflection i a) =
      typeE₇MinusculeDual a - e7MinusculeWeight a i • e7SimpleDual i := by
  apply typeE₇DualWeightEquiv.injective
  simp only [typeE₇DualWeightEquiv_minusculeDual, map_sub, map_zsmul, weight_e7SimpleDual]
  exact (e7MinusculeWeight_reflection i a).trans (by rw [root_e7SimpleIndex])

/-- A simple reflection of the table realizes the corresponding root reflection in the dual
lattice: subtract the simple-root pairing times that simple root. -/
theorem typeE₇MinusculeDual_reflection (i : Fin 7) (a : Fin 56) :
    (typeE₇MinusculeDual (e7MinusculeReflection i a) : Fin 7 → ℚ) =
      (typeE₇MinusculeDual a : Fin 7 → ℚ) -
        (e7MinusculeWeight a i : ℚ) • typeE₇SimpleRoot i := by
  rw [minusculeDual_reflection]
  simp only [Submodule.coe_sub, SetLike.val_smul, e7SimpleDual, coe_e7Basis,
    Int.cast_smul_eq_zsmul]

private theorem norm_minusculeDual_reflection (i : Fin 7) (a : Fin 56) :
    typeE₇RootLattice.form (typeE₇MinusculeDual (e7MinusculeReflection i a))
        (typeE₇MinusculeDual (e7MinusculeReflection i a)) =
      typeE₇RootLattice.form (typeE₇MinusculeDual a) (typeE₇MinusculeDual a) := by
  have hii : (CartanMatrix.E 7) i i = 2 := by revert i; decide
  rw [typeE₇MinusculeDual_reflection]
  simp only [LinearMap.BilinForm.sub_left, LinearMap.BilinForm.sub_right,
    LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_right,
    form_typeE₇MinusculeDual_simpleRoot,
    typeE₇RootLattice.isSymm.eq (typeE₇SimpleRoot i) (typeE₇MinusculeDual a),
    form_typeE₇SimpleRoot_typeE₇SimpleRoot, hii]
  ring

private theorem mk_minusculeDual_reflection (i : Fin 7) (a : Fin 56) :
    (Submodule.Quotient.mk (typeE₇MinusculeDual (e7MinusculeReflection i a)) :
        typeE₇RootLattice.DiscriminantGroup) =
      Submodule.Quotient.mk (typeE₇MinusculeDual a) := by
  have hi : (Submodule.Quotient.mk (e7SimpleDual i) : typeE₇RootLattice.DiscriminantGroup) = 0 :=
    (typeE₇RootLattice.discriminantGroup_mk_eq_zero_iff _).mpr (e7Basis i).property
  simp [minusculeDual_reflection, Submodule.Quotient.mk_sub, Submodule.Quotient.mk_smul, hi]

private theorem minusculeDual_norm_and_class (a : Fin 56) :
    typeE₇RootLattice.form (typeE₇MinusculeDual a) (typeE₇MinusculeDual a) = 3 / 2 ∧
      (Submodule.Quotient.mk (typeE₇MinusculeDual a) : typeE₇RootLattice.DiscriminantGroup) =
        typeE₇MinusculeWeightClass := by
  obtain ⟨l, rfl⟩ := exists_e7MinusculeReflections_eq a
  induction l using List.reverseRecOn with
  | nil => simp
  | append_singleton l i ih =>
      simpa only [List.foldl_append, List.foldl_cons, List.foldl_nil,
        norm_minusculeDual_reflection, mk_minusculeDual_reflection] using ih

/-- Every realized minuscule weight has squared norm `3/2`. -/
@[simp]
theorem form_typeE₇MinusculeDual_self (a : Fin 56) :
    typeE₇RootLattice.form (typeE₇MinusculeDual a) (typeE₇MinusculeDual a) = 3 / 2 :=
  (minusculeDual_norm_and_class a).1

/-- All realized minuscule weights represent the same nonzero discriminant class. -/
@[simp]
theorem mk_typeE₇MinusculeDual (a : Fin 56) :
    (Submodule.Quotient.mk (typeE₇MinusculeDual a) : typeE₇RootLattice.DiscriminantGroup) =
      typeE₇MinusculeWeightClass :=
  (minusculeDual_norm_and_class a).2

/-- A realized minuscule weight is a shortest representative of its discriminant class. -/
theorem form_typeE₇MinusculeDual_le (a : Fin 56) (y : typeE₇RootLattice.dualCarrier)
    (hy : (Submodule.Quotient.mk y : typeE₇RootLattice.DiscriminantGroup) =
      Submodule.Quotient.mk (typeE₇MinusculeDual a)) :
    typeE₇RootLattice.form (typeE₇MinusculeDual a) (typeE₇MinusculeDual a) ≤
      typeE₇RootLattice.form y y := by
  rw [form_typeE₇MinusculeDual_self]
  exact isLeast_form_self_typeE₇MinusculeWeightClass.2 ⟨y, hy.trans (mk_typeE₇MinusculeDual a), rfl⟩

/-- The realized family is closed under negation, as is the original E₇ minuscule table. -/
theorem exists_typeE₇MinusculeDual_eq_neg (a : Fin 56) :
    ∃ b, typeE₇MinusculeDual b = -typeE₇MinusculeDual a := by
  obtain ⟨b, hb⟩ := exists_e7MinusculeWeight_eq_neg a
  exact ⟨b, typeE₇DualWeightEquiv.injective (by
    simp only [typeE₇DualWeightEquiv_minusculeDual, map_neg, hb])⟩

/-! ## Exhaustiveness of the minimal vectors -/

-- Twice the inverse Cartan matrix, used only to make the finite exhaustion executable.
private def e7TwiceInverse : Matrix (Fin 7) (Fin 7) ℤ := !![
  4, 4, 6, 8, 6, 4, 2;
  4, 7, 8, 12, 9, 6, 3;
  6, 8, 12, 16, 12, 8, 4;
  8, 12, 16, 24, 18, 12, 6;
  6, 9, 12, 18, 15, 10, 5;
  4, 6, 8, 12, 10, 8, 4;
  2, 3, 4, 6, 5, 4, 3]

private def e7Coordinates (w : Fin 7 → ℤ) (j : Fin 7) : ℚ :=
  (∑ i, (e7TwiceInverse j i : ℚ) * w i) / 2

private theorem e7Coordinates_pairing (w : Fin 7 → ℤ) (j : Fin 7) :
    ∑ i, (CartanMatrix.E 7 j i : ℚ) * e7Coordinates w i = w j := by
  fin_cases j <;>
    norm_num [e7Coordinates, e7TwiceInverse, Fin.sum_univ_succ, CartanMatrix.E] <;> ring

private theorem simpleRoot_eq_basisFun (i : Fin 7) :
    typeE₇SimpleRoot i = Pi.basisFun ℚ (Fin 7) i := by
  ext j
  simp [typeE₇SimpleRoot_apply, Pi.basisFun_apply, Pi.single_apply]

private theorem e7Form_eq_ofGramMatrix :
    typeE₇RootLattice.form =
      (ofGramMatrix (Pi.basisFun ℚ (Fin 7)) (CartanMatrix.E 7) (CartanMatrix.E_isSymm 7)).form := by
  apply LinearMap.BilinForm.ext_basis (Pi.basisFun ℚ (Fin 7))
  intro i j
  have h := form_typeE₇SimpleRoot_typeE₇SimpleRoot i j
  rw [simpleRoot_eq_basisFun, simpleRoot_eq_basisFun] at h
  exact h.trans (form_ofGramMatrix_basisFun_basisFun _ _ i j).symm

private theorem coe_eq_e7Coordinates (x : typeE₇RootLattice.dualCarrier) :
    (x : Fin 7 → ℚ) = e7Coordinates (typeE₇DualWeightEquiv x) := by
  apply sub_eq_zero.mp
  apply typeE₇RootLattice.form_nondegenerate.1
  have h : typeE₇RootLattice.form
      ((x : Fin 7 → ℚ) - e7Coordinates (typeE₇DualWeightEquiv x)) = 0 := by
    apply (Pi.basisFun ℚ (Fin 7)).ext
    intro i
    rw [LinearMap.BilinForm.sub_left, ← simpleRoot_eq_basisFun]
    rw [← typeE₇DualWeightEquiv_apply]
    rw [simpleRoot_eq_basisFun, e7Form_eq_ofGramMatrix, form_ofGramMatrix_basisFun_right,
      e7Coordinates_pairing]
    simp
  exact fun y ↦ LinearMap.congr_fun h y

private theorem norm_eq_e7Coordinates (x : typeE₇RootLattice.dualCarrier) :
    typeE₇RootLattice.form x x =
      ∑ i, e7Coordinates (typeE₇DualWeightEquiv x) i * typeE₇DualWeightEquiv x i := by
  rw [coe_eq_e7Coordinates x, e7Form_eq_ofGramMatrix, form_ofGramMatrix_basisFun_apply]
  simp only [e7Coordinates_pairing]

private theorem two_mul_norm_eq (x : typeE₇RootLattice.dualCarrier) :
    2 * typeE₇RootLattice.form x x =
      ((∑ i, (∑ j, e7TwiceInverse i j * typeE₇DualWeightEquiv x j) *
        typeE₇DualWeightEquiv x i : ℤ) : ℚ) := by
  rw [norm_eq_e7Coordinates, Finset.mul_sum]
  push_cast
  apply Finset.sum_congr rfl
  intro i _
  rw [e7Coordinates]
  ring

private theorem bounded_weights_exhaustion : ∀ w : Fin 7 → Fin 3,
    (∑ i, (∑ j, e7TwiceInverse i j * ((w j : ℤ) - 1)) * ((w i : ℤ) - 1)) = 3 →
      ∃ a, e7MinusculeWeight a = fun j ↦ (w j : ℤ) - 1 := by
  unfold e7TwiceInverse
  simp only [Fin.forall_fin_succ_pi, Fin.forall_fin_zero_pi]
  decide +kernel

private theorem minuscule_pairing_bounds (x : typeE₇RootLattice.dualCarrier)
    (hx : typeE₇RootLattice.form x x = 3 / 2) (i : Fin 7) :
    -1 ≤ typeE₇DualWeightEquiv x i ∧ typeE₇DualWeightEquiv x i ≤ 1 := by
  have hii : (CartanMatrix.E 7) i i = 2 := by revert i; decide
  have hm := isPosDef_typeE₇RootLattice.nonneg
    ((x : Fin 7 → ℚ) - typeE₇SimpleRoot i)
  have hp := isPosDef_typeE₇RootLattice.nonneg
    ((x : Fin 7 → ℚ) + typeE₇SimpleRoot i)
  simp only [LinearMap.BilinMap.toQuadraticMap_apply,
    LinearMap.BilinForm.sub_left, LinearMap.BilinForm.sub_right,
    LinearMap.BilinForm.add_left, LinearMap.BilinForm.add_right,
    typeE₇RootLattice.isSymm.eq (typeE₇SimpleRoot i) x,
    form_typeE₇SimpleRoot_typeE₇SimpleRoot, hii, hx,
    ← typeE₇DualWeightEquiv_apply] at hm hp
  have h : (-2 : ℚ) < typeE₇DualWeightEquiv x i ∧
      (typeE₇DualWeightEquiv x i : ℚ) < 2 := by constructor <;> linarith
  have hi : (-2 : ℤ) < typeE₇DualWeightEquiv x i ∧ typeE₇DualWeightEquiv x i < 2 := by
    exact_mod_cast h
  omega

/-- The 56 realized minuscule weights exhaust the dual vectors of squared norm `3/2`. -/
theorem form_self_eq_three_halves_iff_mem_range_typeE₇MinusculeDual
    (x : typeE₇RootLattice.dualCarrier) :
    typeE₇RootLattice.form x x = 3 / 2 ↔ x ∈ Set.range typeE₇MinusculeDual := by
  constructor
  · intro hx
    let w : Fin 7 → Fin 3 := fun i ↦
      ⟨(typeE₇DualWeightEquiv x i + 1).toNat, by
        have := minuscule_pairing_bounds x hx i
        omega⟩
    have hw : (fun i ↦ (w i : ℤ) - 1) = typeE₇DualWeightEquiv x := by
      funext i
      have := minuscule_pairing_bounds x hx i
      simp only [w]
      omega
    have hn : (∑ i, (∑ j, e7TwiceInverse i j * typeE₇DualWeightEquiv x j) *
        typeE₇DualWeightEquiv x i : ℤ) = 3 := by
      have h := two_mul_norm_eq x
      rw [hx, show (2 : ℚ) * (3 / 2) = 3 by norm_num] at h
      exact_mod_cast h.symm
    obtain ⟨a, ha⟩ := bounded_weights_exhaustion w (by simpa only [← hw] using hn)
    refine ⟨a, typeE₇DualWeightEquiv.injective ?_⟩
    rw [typeE₇DualWeightEquiv_minusculeDual, ha, hw]
  · rintro ⟨a, rfl⟩
    exact form_typeE₇MinusculeDual_self a

/-- There are exactly 56 dual vectors of squared norm `3/2`, not just 56 known examples. -/
theorem ncard_form_self_eq_three_halves_typeE₇RootLattice :
    {x : typeE₇RootLattice.dualCarrier | typeE₇RootLattice.form x x = 3 / 2}.ncard = 56 := by
  simp only [form_self_eq_three_halves_iff_mem_range_typeE₇MinusculeDual, Set.ofPred_mem_eq]
  simpa using Set.ncard_range_of_injective typeE₇MinusculeDual_injective

end TauCeti.IntegralLattice
