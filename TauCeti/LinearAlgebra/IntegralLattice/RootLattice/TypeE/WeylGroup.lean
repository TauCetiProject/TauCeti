/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.IntegralLattice.Isometry.Reflection
public import TauCeti.LinearAlgebra.IntegralLattice.RootLattice.TypeE.Roots
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.E8.Datum
import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.E8.Automorphism
import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.Reduced
import TauCeti.LinearAlgebra.RootSystem.Weyl.Automorphism

/-!
# The isometry group of the E₈ lattice is its Weyl group, of order 696729600

Every isometry of the integral E₈ lattice `typeE₈RootLattice` is a product of reflections in its
240 roots: `TauCeti.IntegralLattice.weylGroup_typeE₈RootLattice_eq_top` says that the Weyl group
of the lattice is its whole isometry group `O(E₈)`. In particular `-1` is a product of root
reflections.

The proof passes through the pinned E₈ root datum `TauCeti.DynkinType.e8SimplyConnectedRootDatum`.
Since the E₈ lattice is unimodular, the map sending a lattice vector to its pairings with the
simple roots identifies the lattice with the weight lattice of the datum, carrying the
enumerated lattice roots `TauCeti.IntegralLattice.typeE₈RootVector` to the roots of the datum.
Transport along this identification is a group isomorphism
`TauCeti.IntegralLattice.typeE₈IsometryEquivAut` from `O(E₈)` onto the automorphism group of the
datum, sending the reflection in a lattice root to the reflection of the datum in the same root.
Its surjectivity and the equality of the two Weyl groups with the full groups both come from the
rigidity of the E₈ diagram: every automorphism of a root system of type E₈ lies in its Weyl group
(`TauCeti.weylGroup_eq_top_of_hasCartanType_E8`).

The same isomorphism transports the order of the automorphism group of the datum,
`TauCeti.DynkinType.card_aut_e8SimplyConnectedRootDatum`, and its transitivity on the roots, so
`|O(E₈)| = |W(E₈)| = 240 · 126 · 23040 = 696729600`.

## Main definitions

* `TauCeti.IntegralLattice.typeE₈IsometryEquivAut`: the isomorphism from the isometry group of the
  E₈ lattice onto the automorphism group of the pinned E₈ root datum.

## Main results

* `TauCeti.IntegralLattice.typeE₈RootVector_typeE₈IsometryEquivAut_indexEquiv`: the isomorphism
  permutes the root indices as the isometry permutes the lattice roots.
* `TauCeti.IntegralLattice.typeE₈IsometryEquivAut_rootReflection`: it sends root reflections to
  root reflections.
* `TauCeti.IntegralLattice.weylGroup_typeE₈RootLattice_eq_top`: **the root reflections generate the
  isometry group of the E₈ lattice.**
* `TauCeti.IntegralLattice.neg_mem_weylGroup_typeE₈RootLattice`: `-1` lies in the Weyl group of
  the E₈ lattice.
* `TauCeti.IntegralLattice.exists_carrierEquiv_typeE₈RootVector_eq`: the isometry group acts
  transitively on the 240 roots.
* `TauCeti.IntegralLattice.card_isometry_typeE₈RootLattice` and
  `TauCeti.IntegralLattice.card_weylGroup_typeE₈RootLattice`: **`|O(E₈)| = |W(E₈)| = 696729600`.**

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Ch. VI, §4.10 and Plate VII.
* J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, Chapter 4, §8.1.
* W. Ebeling, *Lattices and Codes*, Chapter 1, §1.4.
-/

public section

namespace TauCeti.IntegralLattice

open _root_.Matrix DynkinType

/-! ## The weight lattice of the pinned datum -/

/-- Integer simple-root coordinates, as an identification of `ℤ⁸` with the E₈ lattice. -/
private noncomputable def typeE₈CoordinateEquiv : (Fin 8 → ℤ) ≃ₗ[ℤ] typeE₈RootLattice :=
  ofGramMatrixBasisFunEquiv (CartanMatrix.E 8) (CartanMatrix.E_isSymm 8) ≪≫ₗ
    LinearEquiv.ofEq _ _ (by rw [typeE₈RootLattice_carrier, ofGramMatrix_carrier])

private theorem coe_typeE₈CoordinateEquiv_apply (v : Fin 8 → ℤ) :
    (typeE₈CoordinateEquiv v : Fin 8 → ℚ) = fun j ↦ (v j : ℚ) := by
  simp [typeE₈CoordinateEquiv]

/-- The coordinates of an enumerated lattice root are those of the corresponding coroot. -/
private theorem typeE₈CoordinateEquiv_e8Coroot (i : Fin 240) :
    typeE₈CoordinateEquiv (e8Coroot i) = typeE₈RootVector i :=
  Subtype.ext (funext fun j ↦ by rw [coe_typeE₈CoordinateEquiv_apply, typeE₈RootVector_apply])

/-- The integral form of the E₈ lattice in simple-root coordinates is the Cartan form. -/
private theorem integralForm_typeE₈CoordinateEquiv (u w : Fin 8 → ℤ) :
    typeE₈RootLattice.integralForm (typeE₈CoordinateEquiv u) (typeE₈CoordinateEquiv w) =
      (u ᵥ* CartanMatrix.E 8) ⬝ᵥ w := by
  apply Int.cast_injective (α := ℚ)
  rw [integralForm_cast, coe_typeE₈CoordinateEquiv_apply, coe_typeE₈CoordinateEquiv_apply]
  exact form_typeE₈RootLattice_intCast u w

/-- Multiplication of row vectors by the E₈ Cartan matrix, a linear equivalence because the
Cartan matrix has determinant `1`. -/
private noncomputable def cartanVecMulEquiv : (Fin 8 → ℤ) ≃ₗ[ℤ] (Fin 8 → ℤ) :=
  LinearEquiv.ofBijective (CartanMatrix.E 8).vecMulLinear
    ⟨fun _ _ h ↦ sub_eq_zero.mp (Matrix.eq_zero_of_vecMul_eq_zero
        (by rw [CartanMatrix.E₈_det]; norm_num) (by rw [sub_vecMul]; exact sub_eq_zero.mpr h)),
      by
        rw [Matrix.coe_vecMulLinear, Matrix.vecMul_surjective_iff_isUnit,
          Matrix.isUnit_iff_isUnit_det, CartanMatrix.E₈_det]
        exact isUnit_one⟩

/-- The identification of the E₈ lattice with the weight lattice of the pinned E₈ datum, written
in the basis of fundamental weights: a lattice vector goes to its pairings with the simple roots. -/
private noncomputable def typeE₈WeightEquiv : typeE₈RootLattice ≃ₗ[ℤ] (Fin 8 → ℤ) :=
  typeE₈CoordinateEquiv.symm ≪≫ₗ cartanVecMulEquiv

private theorem typeE₈WeightEquiv_apply (x : typeE₈RootLattice) :
    typeE₈WeightEquiv x = typeE₈CoordinateEquiv.symm x ᵥ* CartanMatrix.E 8 :=
  (rfl)

/-- The weight identification carries the enumerated lattice roots to the roots of the datum. -/
private theorem typeE₈WeightEquiv_typeE₈RootVector (i : Fin 240) :
    typeE₈WeightEquiv (typeE₈RootVector i) = e8Root i := by
  rw [typeE₈WeightEquiv_apply, ← typeE₈CoordinateEquiv_e8Coroot, LinearEquiv.symm_apply_apply,
    e8Root_apply]

/-- The perfect pairing of the datum is the lattice form, read through the weight identification
on the left and simple-root coordinates on the right. -/
private theorem dotProduct_typeE₈WeightEquiv (x y : typeE₈RootLattice) :
    typeE₈WeightEquiv x ⬝ᵥ typeE₈CoordinateEquiv.symm y = typeE₈RootLattice.integralForm x y := by
  rw [typeE₈WeightEquiv_apply, ← integralForm_typeE₈CoordinateEquiv, LinearEquiv.apply_symm_apply,
    LinearEquiv.apply_symm_apply]

/-! ## Isometries as automorphisms of the datum -/

/-- The permutation of the 240 root indices induced by an isometry of the E₈ lattice. -/
private noncomputable def typeE₈RootPerm (g : Isometry typeE₈RootLattice typeE₈RootLattice) :
    Equiv.Perm (Fin 240) :=
  typeE₈RootEquiv.trans <| (g.carrierEquiv.toEquiv.subtypeEquiv fun x ↦
    (g.carrierEquiv_mem_vectorsOfNorm_iff x 2).symm).trans typeE₈RootEquiv.symm

private theorem typeE₈RootVector_typeE₈RootPerm
    (g : Isometry typeE₈RootLattice typeE₈RootLattice) (i : Fin 240) :
    typeE₈RootVector (typeE₈RootPerm g i) = g.carrierEquiv (typeE₈RootVector i) := by
  have h : (typeE₈RootEquiv (typeE₈RootPerm g i) : typeE₈RootLattice) =
      g.carrierEquiv (typeE₈RootEquiv i) := by
    simp only [typeE₈RootPerm, Equiv.trans_apply, Equiv.apply_symm_apply,
      Equiv.subtypeEquiv_apply, LinearEquiv.coe_toEquiv]
  simpa only [typeE₈RootEquiv_apply] using h

/-- The automorphism of the pinned E₈ datum induced by an isometry of the E₈ lattice: its weight
map is the isometry, transported along the weight identification. -/
private noncomputable def typeE₈IsometryToAut
    (g : Isometry typeE₈RootLattice typeE₈RootLattice) : e8SimplyConnectedRootDatum.Aut :=
  RootPairing.Equiv.mk' _ _ (typeE₈WeightEquiv.symm ≪≫ₗ g.carrierEquiv ≪≫ₗ typeE₈WeightEquiv)
    (typeE₈RootPerm g) fun i ↦ by
      simp [← typeE₈WeightEquiv_typeE₈RootVector, typeE₈RootVector_typeE₈RootPerm]

private theorem typeE₈IsometryToAut_weightMap_apply
    (g : Isometry typeE₈RootLattice typeE₈RootLattice) (x : typeE₈RootLattice) :
    (typeE₈IsometryToAut g).weightMap (typeE₈WeightEquiv x) =
      typeE₈WeightEquiv (g.carrierEquiv x) := by
  simp [typeE₈IsometryToAut, RootPairing.Equiv.mk']

private theorem typeE₈IsometryToAut_indexEquiv
    (g : Isometry typeE₈RootLattice typeE₈RootLattice) :
    (typeE₈IsometryToAut g).indexEquiv = typeE₈RootPerm g :=
  rfl

private theorem typeE₈IsometryToAut_mul (g h : Isometry typeE₈RootLattice typeE₈RootLattice) :
    typeE₈IsometryToAut (g * h) = typeE₈IsometryToAut g * typeE₈IsometryToAut h := by
  apply RootPairing.Equiv.weightHom_injective
  ext1 m
  obtain ⟨x, rfl⟩ := typeE₈WeightEquiv.surjective m
  simp [typeE₈IsometryToAut_weightMap_apply, Isometry.mul_def]

private theorem typeE₈IsometryToAut_injective : Function.Injective typeE₈IsometryToAut := by
  intro g h hgh
  apply Isometry.carrierEquiv_injective
  ext1 x
  apply typeE₈WeightEquiv.injective
  rw [← typeE₈IsometryToAut_weightMap_apply, ← typeE₈IsometryToAut_weightMap_apply, hgh]

/-- Pairing with a coroot of the datum is the lattice form with the corresponding lattice root. -/
private theorem dotProduct_typeE₈WeightEquiv_e8Coroot (y : typeE₈RootLattice) (i : Fin 240) :
    typeE₈WeightEquiv y ⬝ᵥ e8Coroot i = typeE₈RootLattice.integralForm y (typeE₈RootVector i) := by
  rw [← dotProduct_typeE₈WeightEquiv, ← typeE₈CoordinateEquiv_e8Coroot,
    LinearEquiv.symm_apply_apply]

private theorem typeE₈IsometryToAut_rootReflection (i : Fin 240) :
    typeE₈IsometryToAut (rootReflection _ (integralNorm_typeE₈RootVector i)) =
      RootPairing.Equiv.reflection _ i := by
  apply RootPairing.Equiv.weightHom_injective
  ext1 m
  obtain ⟨y, rfl⟩ := typeE₈WeightEquiv.surjective m
  simp [typeE₈IsometryToAut_weightMap_apply, typeE₈WeightEquiv_typeE₈RootVector,
    RootPairing.reflection_apply, dotProduct_typeE₈WeightEquiv_e8Coroot,
    typeE₈RootLattice.isSymm_integralForm.eq]

/-- `typeE₈IsometryToAut`, bundled as a monoid homomorphism. -/
private noncomputable def typeE₈IsometryToAutHom :
    Isometry typeE₈RootLattice typeE₈RootLattice →* e8SimplyConnectedRootDatum.Aut :=
  MonoidHom.mk' typeE₈IsometryToAut typeE₈IsometryToAut_mul

/-- The induced automorphisms of the datum make up its Weyl group, which is everything. -/
private theorem typeE₈IsometryToAutHom_surjective : Function.Surjective typeE₈IsometryToAutHom := by
  rw [← MonoidHom.range_eq_top, eq_top_iff,
    ← weylGroup_eq_top_of_hasCartanType_E8 hasCartanType_e8SimplyConnectedRootDatum,
    RootPairing.weylGroup, Subgroup.closure_le]
  rintro _ ⟨i, rfl⟩
  exact ⟨_, typeE₈IsometryToAut_rootReflection i⟩

/-- **The isometry group of the E₈ lattice is the automorphism group of the pinned E₈ root
datum.** An isometry acts on the weight lattice of the datum through the identification of the
lattice with the weight lattice by pairing with the simple roots. -/
noncomputable def typeE₈IsometryEquivAut :
    Isometry typeE₈RootLattice typeE₈RootLattice ≃* e8SimplyConnectedRootDatum.Aut :=
  MulEquiv.ofBijective typeE₈IsometryToAutHom
    ⟨typeE₈IsometryToAut_injective, typeE₈IsometryToAutHom_surjective⟩

private theorem typeE₈IsometryEquivAut_apply (g : Isometry typeE₈RootLattice typeE₈RootLattice) :
    typeE₈IsometryEquivAut g = typeE₈IsometryToAut g :=
  rfl

/-- **The isomorphism permutes the root indices as the isometry permutes the lattice roots.** This
characterizes it, since an automorphism of a root system is determined by its permutation of the
roots. -/
@[simp]
theorem typeE₈RootVector_typeE₈IsometryEquivAut_indexEquiv
    (g : Isometry typeE₈RootLattice typeE₈RootLattice) (i : Fin 240) :
    typeE₈RootVector ((typeE₈IsometryEquivAut g).indexEquiv i) =
      g.carrierEquiv (typeE₈RootVector i) := by
  rw [typeE₈IsometryEquivAut_apply, typeE₈IsometryToAut_indexEquiv,
    typeE₈RootVector_typeE₈RootPerm]

/-- **The isomorphism sends the reflection in a lattice root to the reflection of the datum in the
same root.** -/
@[simp]
theorem typeE₈IsometryEquivAut_rootReflection (i : Fin 240) :
    typeE₈IsometryEquivAut (rootReflection _ (integralNorm_typeE₈RootVector i)) =
      RootPairing.Equiv.reflection _ i := by
  rw [typeE₈IsometryEquivAut_apply, typeE₈IsometryToAut_rootReflection]

/-! ## The isometry group is generated by root reflections -/

/-- **The reflections in the 240 roots generate the isometry group of the E₈ lattice**: its Weyl
group is the whole of `O(E₈)`. -/
@[simp]
theorem weylGroup_typeE₈RootLattice_eq_top : typeE₈RootLattice.weylGroup = ⊤ := by
  -- The isomorphism carries the root reflections of the lattice onto the generators of the Weyl
  -- group of the datum, which is everything.
  apply Subgroup.map_injective (f := typeE₈IsometryEquivAut.toMonoidHom)
    typeE₈IsometryEquivAut.injective
  rw [Subgroup.map_top_of_surjective typeE₈IsometryEquivAut.toMonoidHom
      typeE₈IsometryEquivAut.surjective, eq_top_iff,
    ← weylGroup_eq_top_of_hasCartanType_E8 hasCartanType_e8SimplyConnectedRootDatum,
    RootPairing.weylGroup, Subgroup.closure_le]
  rintro _ ⟨i, rfl⟩
  exact ⟨_, rootReflection_mem_weylGroup _ _, typeE₈IsometryEquivAut_rootReflection i⟩

/-- **`-1` is a product of reflections in roots of the E₈ lattice.** -/
theorem neg_mem_weylGroup_typeE₈RootLattice :
    Isometry.neg typeE₈RootLattice ∈ typeE₈RootLattice.weylGroup := by
  simp

/-! ## The order of the isometry group -/

/-- **The isometry group of the E₈ lattice acts transitively on its 240 roots.** -/
theorem exists_carrierEquiv_typeE₈RootVector_eq (i j : Fin 240) :
    ∃ g : Isometry typeE₈RootLattice typeE₈RootLattice,
      g.carrierEquiv (typeE₈RootVector i) = typeE₈RootVector j := by
  obtain ⟨u, hu⟩ := MulAction.exists_smul_eq e8SimplyConnectedRootDatum.Aut i j
  refine ⟨typeE₈IsometryEquivAut.symm u, ?_⟩
  rw [← typeE₈RootVector_typeE₈IsometryEquivAut_indexEquiv, MulEquiv.apply_symm_apply]
  exact congrArg typeE₈RootVector hu

/-- **The isometry group of the E₈ lattice has order `240 · 126 · 23040 = 696729600`.** -/
theorem card_isometry_typeE₈RootLattice :
    Nat.card (Isometry typeE₈RootLattice typeE₈RootLattice) = 696729600 := by
  rw [Nat.card_congr typeE₈IsometryEquivAut.toEquiv, card_aut_e8SimplyConnectedRootDatum]

/-- **The Weyl group of the E₈ lattice has order `696729600`.** -/
theorem card_weylGroup_typeE₈RootLattice :
    Nat.card typeE₈RootLattice.weylGroup = 696729600 := by
  rw [weylGroup_typeE₈RootLattice_eq_top, Subgroup.card_top, card_isometry_typeE₈RootLattice]

end TauCeti.IntegralLattice
