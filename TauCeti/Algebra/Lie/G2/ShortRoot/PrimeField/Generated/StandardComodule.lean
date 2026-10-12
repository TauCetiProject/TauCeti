/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.StandardComodule
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Weight.Torus
public import TauCeti.Algebra.Lie.G2.ShortRoot.PrimeField.Generated.Basic
public import TauCeti.Algebra.Lie.G2.ShortRoot.PrimeField.PreservesTensors
import TauCeti.Algebra.Coalgebra.Subcomodule.Corestrict

/-!
# The standard representation of the generated short-root type-G2 subgroup

Let `k` be a commutative `𝔽₃`-algebra. The scalar extensions to `k` of the four numbered simple
root subgroups and of the weight torus of the short-root type-`G₂` carrier over `𝔽₃` generate a
closed subgroup of `GL₇` over `k`, whose coordinate Hopf algebra is
`TauCeti.G2ShortRoot.PrimeField.generatedCoordinateHopfAlgebra`. Its standard representation is
the corestriction of the standard `O(GL₇)`-comodule along the quotient coordinate morphism.

This file proves that the standard representation is faithful, and that it is simple over every
field of characteristic three. Restricted to the weight torus it is the direct sum of seven
distinct weight lines, the six short roots and zero, so a subcomodule is spanned by the
coordinate vectors it contains. The numbered root subgroups at parameter one then move each
coordinate vector to its neighbours in the weight string

```text
2α₁ + α₂,  α₁ + α₂,  α₁,  0,  -α₁,  -(α₁ + α₂),  -(2α₁ + α₂),
```

with coefficient one, except for the two steps out of the zero weight along `α₁` and `-α₁`, which
have coefficient two. Two is a unit in characteristic three, so every coordinate vector is reached
from every other one. (Over a field of characteristic two the same matrices kill the zero weight
vector, which then spans a subrepresentation.)

## Main declarations

* `TauCeti.G2ShortRoot.PrimeField.generatedWeightTorusCoordinateMap`: the weight torus factored
  through the generated subgroup.
* `TauCeti.G2ShortRoot.PrimeField.generatedStandardComodule`: its standard comodule on `k⁷`.
* `TauCeti.G2ShortRoot.PrimeField.isFaithful_generatedStandardComodule`: faithfulness.
* `TauCeti.G2ShortRoot.PrimeField.rootSubgroupPoints_mulVec_mem`: subcomodules are stable under
  the numbered root-subgroup points.
* `TauCeti.G2ShortRoot.PrimeField.generatedTorusCorestrict_eq_ofWeights`: the weight
  decomposition under the weight torus.
* `TauCeti.G2ShortRoot.PrimeField.instIsSimpleOrderGeneratedSubcomodule`: simplicity over a
  field of characteristic three.

## References

* J. E. Humphreys, *Linear Algebraic Groups*, §26.
* J. C. Jantzen, *Representations of Algebraic Groups*, I.2 and II.2.
* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate IX.

The corestriction and weight-line steps follow the simplicity proof for the type-`E₆` minuscule
carrier in `TauCeti.Algebra.Lie.E6.Minuscule.StandardComodule`.
-/

public section

open CategoryTheory WithConv
open scoped Matrix TensorProduct

namespace TauCeti.G2ShortRoot.PrimeField

universe u

section Construction

variable (k : Type u) [CommRing k] [Algebra (ZMod 3) k]

/-- The weight torus of the generated subgroup, as a coordinate morphism into the coordinate Hopf
algebra of the rank-two split torus formed directly over `k`. -/
noncomputable def generatedWeightTorusCoordinateMap :
    generatedCoordinateHopfAlgebra k ⟶
      (DiagonalizableGroup.coordinateRing k (SplitTorus.characterGroup (Fin 2))).obj :=
  baseChangeGeneratorLift k (.inr ()) ≫
    (DiagonalizableGroup.baseChangeCoordinateHopfAlgebraIso (ZMod 3) k
      (SplitTorus.characterGroup (Fin 2))).hom

/-- Restricted to the generated subgroup, the weight torus is the scalar extension to `k` of the
weight-torus coordinate map over `𝔽₃`. -/
@[reassoc (attr := simp)]
theorem generatedCoordinateMap_comp_generatedWeightTorusCoordinateMap :
    generatedCoordinateMap k ≫ generatedWeightTorusCoordinateMap k =
      GeneralLinear.weightTorusBaseChangeCoordinateMap (ZMod 3) k weight := by
  rw [generatedWeightTorusCoordinateMap, ← Category.assoc,
    generatedCoordinateMap_comp_baseChangeGeneratorLift, baseChangeGenerator_def, generator_inr,
    GeneralLinear.weightTorusBaseChangeCoordinateMap_eq ℤ (ZMod 3), Category.assoc,
    GeneralLinear.weightTorusBaseChangeCoordinateMap_def]

/-- The standard right comodule of the generated short-root type-`G₂` subgroup on `k⁷`. -/
@[instance_reducible]
noncomputable def generatedStandardComodule :
    Comodule k (generatedCoordinateHopfAlgebra k) (Fin 7 → k) :=
  GeneralLinear.corestrictStandardComodule k 7 (generatedCoordinateMap k).hom

attribute [local instance] generatedStandardComodule

/-- **The standard comodule of the generated short-root type-`G₂` subgroup is faithful.** -/
theorem isFaithful_generatedStandardComodule :
    Comodule.IsFaithful (k := k) (H := generatedCoordinateHopfAlgebra k) (V := Fin 7 → k) :=
  GeneralLinear.isFaithful_corestrictStandardComodule k 7 (generatedCoordinateMap k).hom
    (generatedCoordinateMap_surjective k)

/-- **A subcomodule of the standard comodule of the generated subgroup is stable under every
numbered root-subgroup point.** -/
theorem rootSubgroupPoints_mulVec_mem
    (N : Subcomodule k (generatedCoordinateHopfAlgebra k) (Fin 7 → k))
    (j : Fin 2 ⊕ Fin 2) (u : Multiplicative k) {w : Fin 7 → k} (hw : w ∈ N) :
    ((rootSubgroupPoints j k u : Matrix.GeneralLinearGroup (Fin 7) k) :
        Matrix (Fin 7) (Fin 7) k) *ᵥ w ∈ N := by
  set q := (AdditiveGroup.gaPointsMulEquiv (R := ZMod 3) (A := k)).symm u with hq
  -- The `k`-point of the scalar-extended root subgroup extending the `𝔽₃`-point `q`.
  let P : k ⊗[ZMod 3] AdditiveGroup.coordinateHopfAlgebra (ZMod 3) →ₐ[k] k :=
    Algebra.TensorProduct.lift (Algebra.ofId k k)
      (q.ofConv : AdditiveGroup.coordinateHopfAlgebra (ZMod 3) →ₐ[ZMod 3] k)
      fun _ _ ↦ Commute.all _ _
  have h := GeneralLinear.corestrictStandardComodule_mulVec_mem k 7 (generatedCoordinateMap k).hom
    N (toConv (P.comp (baseChangeGeneratorLift k (.inl j)).hom.toAlgHom)) hw
  have hu : u = AdditiveGroup.gaPointsMulEquiv (R := ZMod 3) q := by
    rw [hq, MulEquiv.apply_symm_apply]
  have hmat : (GeneralLinear.pointToGeneralLinear 7
      (AlgHom.mapDomain (generatedCoordinateMap k).hom
        (toConv (P.comp (baseChangeGeneratorLift k (.inl j)).hom.toAlgHom))) :
        Matrix (Fin 7) (Fin 7) k) =
      ((rootSubgroupPoints j k u : Matrix.GeneralLinearGroup (Fin 7) k) :
        Matrix (Fin 7) (Fin 7) k) := by
    have hid := CommHopfAlgCat.mapPointsFunctor_app_apply (generator (.inl j))
      (CommAlgCat.of (ZMod 3) k) q
    rw [hu, coe_rootSubgroupPoints_gaPointsMulEquiv, hid, GeneralLinear.pointsMulEquiv_apply,
      ← GeneralLinear.map_genericMatrix_eq_coe_pointToGeneralLinear, AlgHom.mapDomain_apply,
      ← GeneralLinear.map_genericMatrix_eq_coe_pointToGeneralLinear]
    ext a b
    have hgen := congrArg (fun φ ↦ φ.hom (GeneralLinear.coordinateHopfAlgebraAlgEquiv k 7
        (GeneralLinear.coordinateRingMap k 7 (MvPolynomial.X (a, b)))))
      (generatedCoordinateMap_comp_baseChangeGeneratorLift k (.inl j))
    simp only [_root_.CommHopfAlgCat.hom_comp, BialgHom.coe_comp, Function.comp_apply,
      baseChangeGenerator_def] at hgen
    rw [GeneralLinear.coordinateHopfAlgebraBaseChangeIso_inv_X,
      CommHopfAlgCat.baseChangeMap_apply_tmul] at hgen
    simp only [Matrix.map_apply, GeneralLinear.genericMatrix_apply, AlgHom.comp_apply,
      BialgHom.coe_toAlgHom, hgen]
    simp [P]
  rwa [hmat] at h

/-- **Restricting the standard comodule of the generated subgroup to the weight torus gives the
direct sum of the seven distinct weight lines** of the short-root diagram: the coordinate vector
at `a` spans the weight line of the torus character `weight a`. -/
theorem generatedTorusCorestrict_eq_ofWeights :
    Comodule.Corestrict (generatedWeightTorusCoordinateMap k).hom.toCoalgHom =
      Comodule.ofWeights (Pi.basisFun k (Fin 7))
        (fun a ↦ SplitTorus.weightCharacter (weight a)) := by
  apply GeneralLinear.corestrict_corestrict_standardComodule_eq_ofWeights
    (generatedCoordinateMap k).hom (generatedWeightTorusCoordinateMap k).hom weight
  rw [← _root_.CommHopfAlgCat.hom_comp,
    generatedCoordinateMap_comp_generatedWeightTorusCoordinateMap,
    GeneralLinear.hom_weightTorusBaseChangeCoordinateMap]

end Construction

/-! ## Simplicity in characteristic three -/

section Simple

variable (k : Type u) [Field k] [Algebra (ZMod 3) k]

attribute [local instance] generatedStandardComodule

/-- The integral matrix of the numbered root-subgroup point at parameter one. -/
private def unitRootMatrix : Fin 2 ⊕ Fin 2 → Matrix (Fin 7) (Fin 7) ℤ
  | .inl 0 => 1 + raisingMatrix 0 + Matrix.single 2 4 1
  | .inl 1 => 1 + raisingMatrix 1
  | .inr 0 => 1 + loweringMatrix 0 + Matrix.single 4 2 1
  | .inr 1 => 1 + loweringMatrix 1

private theorem coe_rootSubgroupPoints_one : ∀ j : Fin 2 ⊕ Fin 2,
    ((rootSubgroupPoints j k (Multiplicative.ofAdd 1) : Matrix.GeneralLinearGroup (Fin 7) k) :
        Matrix (Fin 7) (Fin 7) k) =
      (unitRootMatrix j).map (Int.cast : ℤ → k)
  | .inl 0 => by
    have hs : (Matrix.single (2 : Fin 7) (4 : Fin 7) (1 : ℤ)).map (Int.cast : ℤ → k) =
        Matrix.single 2 4 1 := by
      simpa using Matrix.map_single (2 : Fin 7) (4 : Fin 7) (1 : ℤ) (Int.castRingHom k)
    rw [coe_rootSubgroupPoints_inl_zero]
    rw [unitRootMatrix, Matrix.map_add _ Int.cast_add, Matrix.map_add _ Int.cast_add, hs]
    simp
  | .inl 1 => by
    rw [coe_rootSubgroupPoints_inl_one]
    simp [unitRootMatrix, Matrix.map_add]
  | .inr 0 => by
    have hs : (Matrix.single (4 : Fin 7) (2 : Fin 7) (1 : ℤ)).map (Int.cast : ℤ → k) =
        Matrix.single 4 2 1 := by
      simpa using Matrix.map_single (4 : Fin 7) (2 : Fin 7) (1 : ℤ) (Int.castRingHom k)
    rw [coe_rootSubgroupPoints_inr_zero]
    rw [unitRootMatrix, Matrix.map_add _ Int.cast_add, Matrix.map_add _ Int.cast_add, hs]
    simp
  | .inr 1 => by
    rw [coe_rootSubgroupPoints_inr_one]
    simp [unitRootMatrix, Matrix.map_add]

private theorem weightCharacter_weight_injective :
    Function.Injective fun a : Fin 7 ↦ SplitTorus.weightCharacter (weight a) := by
  intro a b h
  apply weight_injective
  funext i
  simpa only [SplitTorus.toAdd_weightCharacter] using
    congrArg (fun χ : Multiplicative (Fin 2 →₀ ℤ) ↦ Multiplicative.toAdd χ i) h

/-- The torus separates the weight lines, so a subcomodule contains the coordinate vector at every
index where one of its vectors is nonzero. -/
private theorem single_mem_of_apply_ne_zero
    (N : Subcomodule k (generatedCoordinateHopfAlgebra k) (Fin 7 → k))
    {v : Fin 7 → k} (hv : v ∈ N) {b : Fin 7} (hb : v b ≠ 0) : Pi.single b (1 : k) ∈ N := by
  have hbmem := Subcomodule.single_smul_mem_of_corestrict_eq_ofWeights
    (generatedWeightTorusCoordinateMap k).hom.toCoalgHom _ weightCharacter_weight_injective
    (generatedTorusCorestrict_eq_ofWeights k) N hv b
  have hscaled := N.toSubmodule.smul_mem (v b)⁻¹ hbmem
  rw [← Subcomodule.mem_toSubmodule]
  simpa only [inv_smul_smul₀ hb] using hscaled

/-- A root-subgroup point at parameter one moves the coordinate vector at `a` onto that at `b`
whenever its integral `(b, a)` entry is one or two, both units in characteristic three. -/
private theorem single_mem_of_unitRootMatrix
    (N : Subcomodule k (generatedCoordinateHopfAlgebra k) (Fin 7 → k))
    (j : Fin 2 ⊕ Fin 2) {a b : Fin 7}
    (hab : unitRootMatrix j b a = 1 ∨ unitRootMatrix j b a = 2)
    (ha : Pi.single a (1 : k) ∈ N) : Pi.single b (1 : k) ∈ N := by
  refine single_mem_of_apply_ne_zero k N
    (rootSubgroupPoints_mulVec_mem k N j (Multiplicative.ofAdd 1) ha) ?_
  rw [Matrix.mulVec_single_one, Matrix.col_apply, coe_rootSubgroupPoints_one,
    Matrix.map_apply]
  have htwo : (2 : k) ≠ 0 := by
    have h3 : ((3 : ℕ) : k) = 0 := by
      rw [← map_natCast (algebraMap (ZMod 3) k), ZMod.natCast_self, map_zero]
    intro h2
    exact one_ne_zero (by push_cast at h3; linear_combination h3 - h2 : (1 : k) = 0)
  rcases hab with h | h <;> rw [h]
  · simp
  · exact_mod_cast htwo

/-- The edges of the short-root weight string, as transpositions of adjacent indices. -/
private abbrev stringSwap (e : Fin 6) : Equiv.Perm (Fin 7) :=
  Equiv.swap e.castSucc e.succ

private theorem single_stringSwap_mem
    (N : Subcomodule k (generatedCoordinateHopfAlgebra k) (Fin 7 → k))
    (a : Fin 7) (e : Fin 6) (ha : Pi.single a (1 : k) ∈ N) :
    Pi.single (stringSwap e a) (1 : k) ∈ N := by
  by_cases hdown : a = e.castSucc
  · subst hdown
    rw [stringSwap, Equiv.swap_apply_left]
    fin_cases e
    · exact single_mem_of_unitRootMatrix k N (.inr 0) (by decide) ha
    · exact single_mem_of_unitRootMatrix k N (.inr 1) (by decide) ha
    · exact single_mem_of_unitRootMatrix k N (.inr 0) (by decide) ha
    · exact single_mem_of_unitRootMatrix k N (.inr 0) (by decide) ha
    · exact single_mem_of_unitRootMatrix k N (.inr 1) (by decide) ha
    · exact single_mem_of_unitRootMatrix k N (.inr 0) (by decide) ha
  by_cases hup : a = e.succ
  · subst hup
    rw [stringSwap, Equiv.swap_apply_right]
    fin_cases e
    · exact single_mem_of_unitRootMatrix k N (.inl 0) (by decide) ha
    · exact single_mem_of_unitRootMatrix k N (.inl 1) (by decide) ha
    · exact single_mem_of_unitRootMatrix k N (.inl 0) (by decide) ha
    · exact single_mem_of_unitRootMatrix k N (.inl 0) (by decide) ha
    · exact single_mem_of_unitRootMatrix k N (.inl 1) (by decide) ha
    · exact single_mem_of_unitRootMatrix k N (.inl 0) (by decide) ha
  rwa [stringSwap, Equiv.swap_apply_of_ne_of_ne hdown hup]

private theorem exists_foldl_stringSwap_eq (a : Fin 7) :
    ∃ l : List (Fin 6), l.foldl (fun b e ↦ stringSwap e b) 0 = a := by
  fin_cases a
  · exact ⟨[], rfl⟩
  · exact ⟨[0], by decide⟩
  · exact ⟨[0, 1], by decide⟩
  · exact ⟨[0, 1, 2], by decide⟩
  · exact ⟨[0, 1, 2, 3], by decide⟩
  · exact ⟨[0, 1, 2, 3, 4], by decide⟩
  · exact ⟨[0, 1, 2, 3, 4, 5], by decide⟩

/-- **The standard comodule of the generated short-root type-`G₂` subgroup is simple over every
field of characteristic three.** -/
instance instIsSimpleOrderGeneratedSubcomodule :
    IsSimpleOrder (Subcomodule k (generatedCoordinateHopfAlgebra k) (Fin 7 → k)) :=
  Subcomodule.isSimpleOrder_of_corestrict_eq_ofWeights
    (generatedWeightTorusCoordinateMap k).hom.toCoalgHom _ weightCharacter_weight_injective
    (generatedTorusCorestrict_eq_ofWeights k) (fun e a ↦ stringSwap e a)
    (fun _ ↦ Equiv.swap_apply_self _ _) (fun N a e ha ↦ single_stringSwap_mem k N a e ha) 0
    exists_foldl_stringSwap_eq

end Simple

end TauCeti.G2ShortRoot.PrimeField
