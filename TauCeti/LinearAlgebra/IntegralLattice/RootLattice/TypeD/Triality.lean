/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.IntegralLattice.Discriminant.OrthogonalGroup
public import TauCeti.LinearAlgebra.IntegralLattice.RootLattice.GlueAlphabet.Quaternary
public import TauCeti.LinearAlgebra.IntegralLattice.RootLattice.TypeD.SimpleRoots
public import TauCeti.LinearAlgebra.RootSystem.DiagramPermutations

/-!
# The triality isometry of `D₄`

The Dynkin diagram of `D₄` has a rotation of order three fixing the central node and cycling the
three outer nodes, the diagram symmetry `TauCeti.trialityPermD4`. In the Conway--Sloane
coordinates `D₄ = {x ∈ ℤ⁴ | ∑ xᵢ even}` it is induced by the rational orthogonal map

```text
τ(x) = (h, h - x₂ - x₃, h - x₁ - x₃, h - x₀ - x₃),    h = (x₀ + x₁ + x₂ + x₃) / 2,
```

which sends the Bourbaki simple roots `α₁ ↦ α₃ ↦ α₄ ↦ α₁` and fixes `α₂`. It preserves `D₄`, and
on the discriminant group it cycles the three nonzero classes,

```text
v ↦ c ↦ s ↦ v,
```

where `v`, `s`, `c` are the vector, spinor and cospinor classes. Under the identification of the
`D₄` glue labels `0, s, v, c` with `0, ω, 1, ω²` in a field `F₄` of four elements, this is
multiplication by `ω²`, and `τ² = τ⁻¹` is multiplication by `ω`. Triality is what lets the
`F₄`-scalar symmetries of a quaternary glue code, such as the coordinate scalings of the hexacode,
act on a lattice glued from copies of `D₄`.

## Main declarations

* `TauCeti.IntegralLattice.checkerboardTriality`: the isometry `τ` of the checkerboard lattice
  `D₄`, with coordinate formula `checkerboardTriality_apply`.
* `TauCeti.IntegralLattice.checkerboardTriality_checkerboardSimpleRoot`: `τ` permutes the simple
  roots by `trialityPermD4`.
* `TauCeti.IntegralLattice.checkerboardTriality_pow_three`: `τ³ = 1`.
* `discriminantGroupEquiv_checkerboardTriality_checkerboardVectorClass` and its two companions:
  `τ` acts on the discriminant classes by `v ↦ c ↦ s ↦ v`.
* `discriminantGroupEquiv_checkerboardTriality_typeD4QuaternaryDiscriminantQuadraticIsometry`:
  in the quaternary coordinates of the discriminant group, `τ` is multiplication by `ω²`.
* `TauCeti.DynkinType.typeD4Triality`: the triality isometry of the root lattice of type `D₄`,
  permuting the simple-root coordinates by `trialityPermD4` (`typeD4Triality_single`).
* `TauCeti.DynkinType.discriminantGroupEquiv_typeD4Triality_glueAlphabetIsometry`: on the `D₄` glue
  alphabet, read in `F₄`, it is multiplication by `ω²`; its powers give every nonzero scaling
  (`discriminantGroupEquiv_typeD4Triality_pow_glueAlphabetIsometry`).

## References

* J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, 3rd ed., Chapter 4,
  §§3 and 7.1, and Chapter 7, §§8–9.
* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate IV.
-/

public section

namespace TauCeti

namespace IntegralLattice

/-! ## Triality on the checkerboard lattice -/

/-- The linear map underlying triality on `ℚ⁴`. -/
private def trialityLinearMap : (Fin 4 → ℚ) →ₗ[ℚ] Fin 4 → ℚ where
  toFun x := ![(x 0 + x 1 + x 2 + x 3) / 2, (x 0 + x 1 - x 2 - x 3) / 2,
    (x 0 - x 1 + x 2 - x 3) / 2, (-x 0 + x 1 + x 2 - x 3) / 2]
  map_add' x y := by
    ext i
    fin_cases i <;> simp <;> ring
  map_smul' c x := by
    ext i
    fin_cases i <;> simp <;> ring

private theorem trialityLinearMap_apply (x : Fin 4 → ℚ) :
    trialityLinearMap x = ![(x 0 + x 1 + x 2 + x 3) / 2, (x 0 + x 1 - x 2 - x 3) / 2,
      (x 0 - x 1 + x 2 - x 3) / 2, (-x 0 + x 1 + x 2 - x 3) / 2] :=
  (rfl)

/-- Triality has order three on `ℚ⁴`. -/
private theorem trialityLinearMap_apply_apply_apply (x : Fin 4 → ℚ) :
    trialityLinearMap (trialityLinearMap (trialityLinearMap x)) = x := by
  ext i
  fin_cases i <;> simp [trialityLinearMap_apply] <;> ring

/-- Triality on `ℚ⁴` as a linear equivalence, with inverse its square. -/
private def trialityLinearEquiv : (Fin 4 → ℚ) ≃ₗ[ℚ] Fin 4 → ℚ :=
  LinearEquiv.ofLinearMap trialityLinearMap (trialityLinearMap ∘ₗ trialityLinearMap)
    (LinearMap.ext trialityLinearMap_apply_apply_apply)
    (LinearMap.ext trialityLinearMap_apply_apply_apply)

/-- Triality maps the checkerboard carrier into itself: with `h` half the coordinate sum, the
image `(h, h - x₂ - x₃, h - x₁ - x₃, h - x₀ - x₃)` is integral, of coordinate sum `2 (h - x₃)`. -/
private theorem trialityLinearMap_mem_checkerboardCarrier {x : Fin 4 → ℚ}
    (hx : x ∈ checkerboardCarrier 4) : trialityLinearMap x ∈ checkerboardCarrier 4 := by
  obtain ⟨hxZ, m, hm⟩ := (mem_checkerboardCarrier_iff x).1 hx
  choose z hz using hxZ
  simp only [Fin.sum_univ_four, hz] at hm
  have hm' : z 0 + z 1 + z 2 + z 3 = 2 * m := by exact_mod_cast hm
  refine mem_checkerboardCarrier_of ![m, m - z 2 - z 3, m - z 1 - z 3, m - z 0 - z 3]
    (fun i ↦ ?_) ⟨m - z 3, by simp only [Fin.sum_univ_four]; simp; linear_combination -hm'⟩
  fin_cases i <;> simp [trialityLinearMap_apply, hz] <;> linarith

/-- Triality preserves the dot product on `ℚ⁴`. -/
private theorem sum_trialityLinearMap_mul_trialityLinearMap (x y : Fin 4 → ℚ) :
    ∑ i, trialityLinearMap x i * trialityLinearMap y i = ∑ i, x i * y i := by
  simp only [Fin.sum_univ_four, trialityLinearMap_apply]
  simp
  ring

/-- **The triality isometry of `D₄`**: the isometry of the checkerboard lattice of rank four
given by `x ↦ (h, h - x₂ - x₃, h - x₁ - x₃, h - x₀ - x₃)`, where `h = (x₀ + x₁ + x₂ + x₃) / 2`.
It permutes the simple roots by the diagram symmetry `trialityPermD4`
(`checkerboardTriality_checkerboardSimpleRoot`) and cycles the nonzero discriminant classes
`v ↦ c ↦ s ↦ v`. -/
noncomputable def checkerboardTriality :
    Isometry (checkerboardLattice 4) (checkerboardLattice 4) where
  toIsometryEquiv :=
    { toLinearEquiv := trialityLinearEquiv
      map_app' x y := by
        rw [checkerboardLattice_form_apply, checkerboardLattice_form_apply]
        exact sum_trialityLinearMap_mul_trialityLinearMap x y }
  map_carrier := by
    rw [checkerboardLattice_carrier]
    refine le_antisymm ?_ fun x hx ↦ ⟨trialityLinearMap (trialityLinearMap x),
      trialityLinearMap_mem_checkerboardCarrier (trialityLinearMap_mem_checkerboardCarrier hx),
      trialityLinearMap_apply_apply_apply x⟩
    rintro _ ⟨x, hx, rfl⟩
    exact trialityLinearMap_mem_checkerboardCarrier hx

/-- The coordinate formula of triality: the matrix `½ [[1, 1, 1, 1], [1, 1, -1, -1],
[1, -1, 1, -1], [-1, 1, 1, -1]]`. -/
@[simp]
theorem checkerboardTriality_apply (x : Fin 4 → ℚ) :
    checkerboardTriality x = ![(x 0 + x 1 + x 2 + x 3) / 2, (x 0 + x 1 - x 2 - x 3) / 2,
      (x 0 - x 1 + x 2 - x 3) / 2, (-x 0 + x 1 + x 2 - x 3) / 2] :=
  (rfl)

/-- **Triality is the diagram rotation of `D₄`**: it permutes the simple roots by
`trialityPermD4`, sending the Bourbaki simple roots `α₁ ↦ α₃ ↦ α₄ ↦ α₁` and fixing the central
root `α₂`. -/
theorem checkerboardTriality_checkerboardSimpleRoot (i : Fin 4) :
    checkerboardTriality (checkerboardSimpleRoot 4 le_rfl i) =
      checkerboardSimpleRoot 4 le_rfl (trialityPermD4 i) := by
  ext j
  fin_cases i <;> fin_cases j <;>
    norm_num

/-- **Triality has order three.** -/
theorem checkerboardTriality_pow_three : checkerboardTriality ^ 3 = 1 :=
  Isometry.ext fun x ↦ by
    simp only [pow_three, Isometry.mul_apply, Isometry.one_apply]
    exact trialityLinearMap_apply_apply_apply x

/-! ## The action on the discriminant group -/

/-- Triality sends the vector class to the cospinor class. -/
@[simp]
theorem discriminantGroupEquiv_checkerboardTriality_checkerboardVectorClass :
    checkerboardTriality.discriminantGroupEquiv (checkerboardVectorClass 4) =
      checkerboardCospinorClass 4 := by
  rw [← (mk_eq_checkerboardVectorClass_iff ⟨_, checkerboardVector_mem_dualCarrier⟩).2
      (by simp), Isometry.discriminantGroupEquiv_mk,
    mk_eq_checkerboardCospinorClass_iff, Isometry.coe_dualCarrierEquiv_apply]
  refine mem_checkerboardCarrier_of ![0, -1, -1, 0] (fun i ↦ ?_) ⟨-1, by decide⟩
  fin_cases i <;> norm_num [Fin.ext_iff]

/-- Triality sends the spinor class to the vector class. -/
@[simp]
theorem discriminantGroupEquiv_checkerboardTriality_checkerboardSpinorClass :
    checkerboardTriality.discriminantGroupEquiv (checkerboardSpinorClass 4) =
      checkerboardVectorClass 4 := by
  rw [checkerboardSpinorClass_def, Isometry.discriminantGroupEquiv_mk,
    mk_eq_checkerboardVectorClass_iff, Isometry.coe_dualCarrierEquiv_apply]
  refine mem_checkerboardCarrier_of ![1, 0, 0, -1] (fun i ↦ ?_) ⟨0, by decide⟩
  fin_cases i <;> norm_num [Fin.ext_iff]

/-- Triality sends the cospinor class to the spinor class: it maps the cospinor vector
`(½, ½, ½, -½)` to the spinor vector `(½, ½, ½, ½)`. -/
@[simp]
theorem discriminantGroupEquiv_checkerboardTriality_checkerboardCospinorClass :
    checkerboardTriality.discriminantGroupEquiv (checkerboardCospinorClass 4) =
      checkerboardSpinorClass 4 := by
  rw [← (mk_eq_checkerboardCospinorClass_iff ⟨_, checkerboardCospinor_mem_dualCarrier⟩).2
      (by simp), Isometry.discriminantGroupEquiv_mk,
    mk_eq_checkerboardSpinorClass_iff, Isometry.coe_dualCarrierEquiv_apply]
  refine mem_checkerboardCarrier_of 0 (fun i ↦ ?_) ⟨0, by decide⟩
  fin_cases i <;> norm_num [Fin.ext_iff]

variable {F : Type*} [Field F] [Finite F] (hF : Nat.card F = 4) {ω : F} (hω : ω ^ 2 + ω + 1 = 0)

/-- **Triality is multiplication by `ω²`** on the discriminant group of `D₄`, read in the
quaternary coordinates sending `1, ω, ω²` to the vector, spinor and cospinor classes. -/
theorem discriminantGroupEquiv_checkerboardTriality_typeD4QuaternaryDiscriminantQuadraticIsometry
    (y : F) :
    checkerboardTriality.discriminantGroupEquiv
        (typeD4QuaternaryDiscriminantQuadraticIsometry hF hω y) =
      typeD4QuaternaryDiscriminantQuadraticIsometry hF hω (ω ^ 2 * y) := by
  obtain ⟨i, rfl⟩ := (finFourEquiv hF hω).surjective y
  have hω3 := pow_three_eq_one_of_sq_add_self_add_one_eq_zero hω
  have hω₁ : ω ^ 2 * ω = 1 := by linear_combination hω3
  have hω₂ : ω ^ 2 * ω ^ 2 = ω := by linear_combination ω * hω3
  fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, finFourEquiv_apply,
    Matrix.cons_val]
  · rw [mul_zero, map_zero]
    exact checkerboardTriality.discriminantGroupEquiv.map_zero
  · rw [mul_one, typeD4QuaternaryDiscriminantQuadraticIsometry_one,
      typeD4QuaternaryDiscriminantQuadraticIsometry_root_sq]
    exact discriminantGroupEquiv_checkerboardTriality_checkerboardVectorClass
  · rw [hω₁, typeD4QuaternaryDiscriminantQuadraticIsometry_root,
      typeD4QuaternaryDiscriminantQuadraticIsometry_one]
    exact discriminantGroupEquiv_checkerboardTriality_checkerboardSpinorClass
  · rw [hω₂, typeD4QuaternaryDiscriminantQuadraticIsometry_root_sq,
      typeD4QuaternaryDiscriminantQuadraticIsometry_root]
    exact discriminantGroupEquiv_checkerboardTriality_checkerboardCospinorClass

end IntegralLattice

/-! ## Triality on the root lattice of type `D₄` -/

namespace DynkinType

open IntegralLattice

variable (ht : (D 4).IsSimplyLaced)

/-- **The triality isometry of the root lattice of type `D₄`**: `checkerboardTriality`,
transported along the identification `rootLatticeIsometryCheckerboard` with the checkerboard
lattice. It is the diagram rotation of `D₄`, permuting the simple-root coordinates by
`trialityPermD4` (`typeD4Triality_single`). -/
noncomputable def typeD4Triality : Isometry ((D 4).rootLattice ht) ((D 4).rootLattice ht) :=
  (rootLatticeIsometryCheckerboard 4 le_rfl ht).symm.conjMulEquiv checkerboardTriality

/-- Triality on the root lattice is triality on the checkerboard lattice, conjugated by
`rootLatticeIsometryCheckerboard`. -/
theorem typeD4Triality_apply (x : Fin (D 4).rank → ℚ) :
    typeD4Triality ht x = (rootLatticeIsometryCheckerboard 4 le_rfl ht).symm
      (checkerboardTriality (rootLatticeIsometryCheckerboard 4 le_rfl ht x)) := by
  rw [typeD4Triality, Isometry.conjMulEquiv_apply, Isometry.symm_symm]

/-- **Triality permutes the simple roots of `D₄` by `trialityPermD4`**: `α₁ ↦ α₃ ↦ α₄ ↦ α₁`,
fixing `α₂`. -/
-- Not a `simp` lemma: `rank_D` rewrites the index type `Fin (D 4).rank` of `Pi.single`, so the
-- statement is not in simp-normal form.
theorem typeD4Triality_single (i : Fin 4) :
    typeD4Triality ht (Pi.single i 1) = Pi.single (trialityPermD4 i) 1 := by
  rw [typeD4Triality_apply, rootLatticeIsometryCheckerboard_single,
    checkerboardTriality_checkerboardSimpleRoot,
    ← rootLatticeIsometryCheckerboard_single 4 le_rfl ht, Isometry.symm_apply_apply]
  -- The two sides differ only in spelling the index type as `Fin 4` or `Fin (D 4).rank`.
  rfl

/-- **Triality has order three.** -/
theorem typeD4Triality_pow_three : typeD4Triality ht ^ 3 = 1 := by
  rw [typeD4Triality, ← map_pow, checkerboardTriality_pow_three, map_one]

variable (hv : (D 4).Valid) {F : Type*} [Field F] [Finite F] (hF : Nat.card F = 4) {ω : F}
  (hω : ω ^ 2 + ω + 1 = 0)

/-- **Triality acts on the `D₄` glue alphabet as multiplication by `ω²`**: read through the
identification `typeD4GlueAlphabetQuaternaryIsometry` of the labels `0, s, v, c` with
`0, ω, 1, ω²`, the induced action of `typeD4Triality` on the discriminant group is `y ↦ ω² y`. -/
theorem discriminantGroupEquiv_typeD4Triality_glueAlphabetIsometry
    (x : (D 4).glueAlphabet ht) :
    (typeD4Triality ht).discriminantGroupEquiv ((D 4).glueAlphabetIsometry hv ht x) =
      (D 4).glueAlphabetIsometry hv ht ((typeD4GlueAlphabetQuaternaryIsometry hF hω).symm
        (ω ^ 2 * typeD4GlueAlphabetQuaternaryIsometry hF hω x)) := by
  -- Both glue identifications factor through the quaternary coordinates of the checkerboard
  -- discriminant group.
  have hfactor (x : (D 4).glueAlphabet ht) :
      (D 4).glueAlphabetIsometry hv ht x =
        (rootLatticeIsometryCheckerboard 4 le_rfl ht).symm.discriminantGroupEquiv
          (typeD4QuaternaryDiscriminantQuadraticIsometry hF hω
            (typeD4GlueAlphabetQuaternaryIsometry hF hω x)) := by
    rw [glueAlphabetIsometry_D_apply_of_even 4 hv ht (by decide),
      typeD4QuaternaryDiscriminantQuadraticIsometry_apply,
      typeD4GlueAlphabetQuaternaryIsometry_apply]
    exact congrArg _ (congrArg _ (AddEquiv.symm_apply_apply _ _).symm)
  have hconj (z : (checkerboardLattice 4).DiscriminantGroup) :
      (typeD4Triality ht).discriminantGroupEquiv
          ((rootLatticeIsometryCheckerboard 4 le_rfl ht).symm.discriminantGroupEquiv z) =
        (rootLatticeIsometryCheckerboard 4 le_rfl ht).symm.discriminantGroupEquiv
          (checkerboardTriality.discriminantGroupEquiv z) := by
    rw [← Isometry.discriminantGroupHom_apply, typeD4Triality,
      Isometry.discriminantGroupHom_conjMulEquiv, LinearEquiv.trans_apply, LinearEquiv.trans_apply,
      LinearEquiv.symm_apply_apply, Isometry.discriminantGroupHom_apply]
  rw [hfactor, hfactor]
  refine (hconj _).trans (congrArg _ ((
    discriminantGroupEquiv_checkerboardTriality_typeD4QuaternaryDiscriminantQuadraticIsometry
      hF hω _).trans ?_))
  rw [QuadraticMap.IsometryEquiv.apply_symm_apply]

/-- **The powers of triality act on the `D₄` glue alphabet as multiplication by the powers of
`ω²`**, read through `typeD4GlueAlphabetQuaternaryIsometry`. Every nonzero element of `F₄` is a
power of `ω²`, so every nonzero scaling of the quaternary alphabet is induced by an isometry of the
root lattice. -/
theorem discriminantGroupEquiv_typeD4Triality_pow_glueAlphabetIsometry (k : ℕ)
    (x : (D 4).glueAlphabet ht) :
    (typeD4Triality ht ^ k).discriminantGroupEquiv ((D 4).glueAlphabetIsometry hv ht x) =
      (D 4).glueAlphabetIsometry hv ht ((typeD4GlueAlphabetQuaternaryIsometry hF hω).symm
        ((ω ^ 2) ^ k * typeD4GlueAlphabetQuaternaryIsometry hF hω x)) := by
  induction k generalizing x with
  | zero =>
    rw [pow_zero, pow_zero, one_mul, QuadraticMap.IsometryEquiv.symm_apply_apply,
      Isometry.one_def, Isometry.discriminantGroupEquiv_refl]
    -- `LinearEquiv.refl_apply` does not rewrite here: the argument is typed in the carrier of
    -- the discriminant quadratic module rather than in the discriminant group.
    rfl
  | succ k ih =>
    rw [pow_succ (typeD4Triality ht) k, Isometry.mul_def, Isometry.discriminantGroupEquiv_trans]
    -- The composite is applied in two steps: first `typeD4Triality`, then its `k`-th power.
    refine (congrArg _ (discriminantGroupEquiv_typeD4Triality_glueAlphabetIsometry ht hv hF hω
      x)).trans ((ih _).trans ?_)
    rw [QuadraticMap.IsometryEquiv.apply_symm_apply, pow_succ (ω ^ 2) k, mul_assoc]

end DynkinType

end TauCeti
