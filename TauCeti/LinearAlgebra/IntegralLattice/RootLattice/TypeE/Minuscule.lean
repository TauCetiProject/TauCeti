/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.IntegralLattice.RootLattice.TypeE.CosetMinimum
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.E6.MinusculeWeight
import TauCeti.LinearAlgebra.IntegralLattice.Isometry.Reflection

/-!
# The 27 minuscule weights as dual vectors of the E₆ lattice

The minuscule weight table of the pinned E₆ root datum uses fundamental-weight coordinates,
whereas the integral root lattice uses simple-root coordinates. Pairing with the simple roots
identifies the literal dual carrier with the weight lattice. This identification realizes the
27 weights as distinct vectors of norm `4/3` in the class of `ϖ₁`; their negatives give 27
shortest representatives in the other nonzero discriminant class.

The realization intertwines the table's simple reflections with lattice root reflections.
Thus the norm and discriminant class are transported along the already checked reflection
paths, without introducing another weight table. The coset minimum theorem proves that all
these representatives are shortest. No assertion that these exhaust the minimizers is made here.

## References

* J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*,
  Chapter 4, §8.3.
* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate V.

The weight table and reflection paths are those of
`TauCeti.DynkinType.e6MinusculeWeight` and `exists_e6MinusculeReflections_eq`.
-/

public section

namespace TauCeti.IntegralLattice

open Module DynkinType

private noncomputable def e6Basis : Basis (Fin 6) ℤ typeE₆RootLattice :=
  (ofGramMatrix.basis (Pi.basisFun ℚ (Fin 6)) (CartanMatrix.E 6)
    (CartanMatrix.E_isSymm 6)).map
      (LinearEquiv.ofEq _ _ (by
        ext x
        rw [mem_typeE₆RootLattice_carrier_iff, mem_ofGramMatrix_basisFun_carrier_iff]))

private theorem coe_e6Basis (i : Fin 6) : (e6Basis i : Fin 6 → ℚ) = typeE₆SimpleRoot i := by
  simp only [e6Basis, Basis.map_apply, LinearEquiv.coe_ofEq_apply, ofGramMatrix.coe_basis]
  ext j
  simp [typeE₆SimpleRoot_apply, Pi.basisFun_apply, Pi.single_apply]

/-- Pairing with the six simple roots identifies the dual E₆ lattice with the weight lattice
in fundamental-weight coordinates. -/
noncomputable def typeE₆DualWeightEquiv : typeE₆RootLattice.dualCarrier ≃ₗ[ℤ] (Fin 6 → ℤ) :=
  typeE₆RootLattice.dualPairingEquiv.trans e6Basis.dualBasis.equivFun

/-- The fundamental-weight coordinates of a dual vector are its simple-root pairings. -/
@[simp]
theorem typeE₆DualWeightEquiv_apply (x : typeE₆RootLattice.dualCarrier) (i : Fin 6) :
    (typeE₆DualWeightEquiv x i : ℚ) =
      typeE₆RootLattice.form x (typeE₆SimpleRoot i) := by
  simp only [typeE₆DualWeightEquiv, LinearEquiv.trans_apply, Basis.dualBasis_equivFun,
    dualPairingEquiv_cast, coe_e6Basis]

/-- The minuscule weight table of the E₆ root datum, realized in the literal dual lattice. -/
noncomputable def typeE₆MinusculeDual (a : Fin 27) : typeE₆RootLattice.dualCarrier :=
  typeE₆DualWeightEquiv.symm (e6MinusculeWeight a)

/-- The realized weight has exactly the fundamental coordinates of the pinned weight table. -/
@[simp]
theorem typeE₆DualWeightEquiv_minusculeDual (a : Fin 27) :
    typeE₆DualWeightEquiv (typeE₆MinusculeDual a) = e6MinusculeWeight a :=
  typeE₆DualWeightEquiv.apply_symm_apply _

/-- Pairing a realized minuscule weight with a simple root reads its table entry. -/
@[simp]
theorem form_typeE₆MinusculeDual_simpleRoot (a : Fin 27) (i : Fin 6) :
    typeE₆RootLattice.form (typeE₆MinusculeDual a) (typeE₆SimpleRoot i) =
      (e6MinusculeWeight a i : ℚ) := by
  rw [← typeE₆DualWeightEquiv_apply, typeE₆DualWeightEquiv_minusculeDual]

/-- Distinct table weights give distinct vectors in the literal dual carrier. -/
theorem typeE₆MinusculeDual_injective : Function.Injective typeE₆MinusculeDual := by
  intro a b h
  apply e6MinusculeWeight_injective
  simpa only [typeE₆DualWeightEquiv_minusculeDual] using congrArg typeE₆DualWeightEquiv h

/-- The highest table weight realizes the previously chosen discriminant generator `ϖ₁`. -/
@[simp]
theorem typeE₆MinusculeDual_zero : typeE₆MinusculeDual 0 = typeE₆MinusculeWeightDual := by
  apply typeE₆DualWeightEquiv.injective
  ext i
  apply Int.cast_injective (α := ℚ)
  rw [typeE₆DualWeightEquiv_minusculeDual, typeE₆DualWeightEquiv_apply,
    coe_typeE₆MinusculeWeightDual, form_typeE₆MinusculeWeight_typeE₆SimpleRoot,
    e6MinusculeWeight_zero]
  simp [Pi.single_apply]

private noncomputable def e6SimpleDual (i : Fin 6) : typeE₆RootLattice.dualCarrier :=
  ⟨e6Basis i, typeE₆RootLattice.le_dualCarrier (e6Basis i).property⟩

private theorem weight_e6SimpleDual (i : Fin 6) :
    typeE₆DualWeightEquiv (e6SimpleDual i) = CartanMatrix.E 6 i := by
  ext j
  apply Int.cast_injective (α := ℚ)
  rw [typeE₆DualWeightEquiv_apply]
  exact (congrArg (fun x ↦ typeE₆RootLattice.form x (typeE₆SimpleRoot j)) (coe_e6Basis i)).trans
    (form_typeE₆SimpleRoot_typeE₆SimpleRoot i j)

private theorem minusculeDual_reflection (i : Fin 6) (a : Fin 27) :
    typeE₆MinusculeDual (e6MinusculeReflection i a) =
      typeE₆MinusculeDual a - e6MinusculeWeight a i • e6SimpleDual i := by
  apply typeE₆DualWeightEquiv.injective
  simp only [typeE₆DualWeightEquiv_minusculeDual, map_sub, map_zsmul, weight_e6SimpleDual]
  exact (e6MinusculeWeight_reflection i a).trans
    (by rw [root_e6SimpleIndex])

/-- In simple-root coordinates the table reflection subtracts its coroot value times the
simple root, exactly the lattice root-reflection formula. -/
theorem typeE₆MinusculeDual_reflection (i : Fin 6) (a : Fin 27) :
    (typeE₆MinusculeDual (e6MinusculeReflection i a) : Fin 6 → ℚ) =
      (typeE₆MinusculeDual a : Fin 6 → ℚ) -
        (e6MinusculeWeight a i : ℚ) • typeE₆SimpleRoot i := by
  rw [minusculeDual_reflection]
  simp only [Submodule.coe_sub, SetLike.val_smul, e6SimpleDual, coe_e6Basis,
    Int.cast_smul_eq_zsmul]

private theorem e6Simple_norm (i : Fin 6) : typeE₆RootLattice.integralNorm (e6Basis i) = 2 := by
  apply Int.cast_injective (α := ℚ)
  rw [integralNorm_cast, norm_apply, coe_e6Basis, form_typeE₆SimpleRoot_typeE₆SimpleRoot]
  have h : (CartanMatrix.E 6) i i = 2 := by revert i; decide
  rw [h]

private theorem norm_minusculeDual_reflection (i : Fin 6) (a : Fin 27) :
    typeE₆RootLattice.form (typeE₆MinusculeDual (e6MinusculeReflection i a))
        (typeE₆MinusculeDual (e6MinusculeReflection i a)) =
      typeE₆RootLattice.form (typeE₆MinusculeDual a) (typeE₆MinusculeDual a) := by
  have h (a : Fin 27) :
      (typeE₆RootLattice.rootReflection (e6Basis i) (e6Simple_norm i))
          (typeE₆MinusculeDual a) = typeE₆MinusculeDual (e6MinusculeReflection i a) := by
    rw [rootReflection_apply, coe_e6Basis, typeE₆RootLattice.isSymm.eq,
      form_typeE₆MinusculeDual_simpleRoot, typeE₆MinusculeDual_reflection]
  rw [← h]
  exact Isometry.map_app _ _ _

private theorem mk_minusculeDual_reflection (i : Fin 6) (a : Fin 27) :
    (Submodule.Quotient.mk (typeE₆MinusculeDual (e6MinusculeReflection i a)) :
        typeE₆RootLattice.DiscriminantGroup) =
      Submodule.Quotient.mk (typeE₆MinusculeDual a) := by
  have hi : (Submodule.Quotient.mk (e6SimpleDual i) : typeE₆RootLattice.DiscriminantGroup) = 0 :=
    (typeE₆RootLattice.discriminantGroup_mk_eq_zero_iff _).mpr (e6Basis i).property
  simp [minusculeDual_reflection, Submodule.Quotient.mk_sub, Submodule.Quotient.mk_smul, hi]

private theorem minusculeDual_norm_and_class (a : Fin 27) :
    typeE₆RootLattice.form (typeE₆MinusculeDual a) (typeE₆MinusculeDual a) = 4 / 3 ∧
      (Submodule.Quotient.mk (typeE₆MinusculeDual a) : typeE₆RootLattice.DiscriminantGroup) =
        typeE₆MinusculeWeightClass := by
  obtain ⟨l, rfl⟩ := exists_e6MinusculeReflections_eq a
  induction l using List.reverseRecOn with
  | nil => simp
  | append_singleton l i ih =>
      simpa only [List.foldl_append, List.foldl_cons, List.foldl_nil,
        norm_minusculeDual_reflection, mk_minusculeDual_reflection] using ih

/-- All 27 realized weights have squared norm `4/3`. -/
@[simp]
theorem form_typeE₆MinusculeDual_self (a : Fin 27) :
    typeE₆RootLattice.form (typeE₆MinusculeDual a) (typeE₆MinusculeDual a) = 4 / 3 :=
  (minusculeDual_norm_and_class a).1

/-- All 27 realized weights represent the class of `ϖ₁`. -/
@[simp]
theorem mk_typeE₆MinusculeDual (a : Fin 27) :
    (Submodule.Quotient.mk (typeE₆MinusculeDual a) : typeE₆RootLattice.DiscriminantGroup) =
      typeE₆MinusculeWeightClass :=
  (minusculeDual_norm_and_class a).2

/-- Every realized weight is a shortest representative of its discriminant class. -/
theorem form_typeE₆MinusculeDual_le (a : Fin 27) (y : typeE₆RootLattice.dualCarrier)
    (hy : (Submodule.Quotient.mk y : typeE₆RootLattice.DiscriminantGroup) =
      Submodule.Quotient.mk (typeE₆MinusculeDual a)) :
    typeE₆RootLattice.form (typeE₆MinusculeDual a) (typeE₆MinusculeDual a) ≤
      typeE₆RootLattice.form y y := by
  rw [form_typeE₆MinusculeDual_self]
  exact isLeast_form_self_typeE₆MinusculeWeightClass.2 ⟨y, hy.trans (mk_typeE₆MinusculeDual a), rfl⟩

/-- There are 27 distinct shortest representatives supplied by the minuscule table. -/
theorem ncard_range_typeE₆MinusculeDual : (Set.range typeE₆MinusculeDual).ncard = 27 := by
  simpa using Set.ncard_range_of_injective typeE₆MinusculeDual_injective

end TauCeti.IntegralLattice
