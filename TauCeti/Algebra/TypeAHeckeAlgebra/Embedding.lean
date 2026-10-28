/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.TypeAHeckeAlgebra.Basis
public import TauCeti.GroupTheory.Coxeter.Restriction

/-!
# The finite type-A Hecke algebras embed in the infinite one

The map `TauCeti.TypeAHeckeAlgebra.toInfinite R q n` from the Hecke algebra on `n` strands to the
infinite type-A Hecke algebra, `T i ↦ T i`, has image the stage of the first `n` strands. This file
proves that it is injective, over every commutative ring `R` and for every unit `q`. Hence the
finite presentation is isomorphic to the stage (`TauCeti.TypeAHeckeAlgebra.stageEquiv`), the stage
is a free module with basis the images of the elements `T_w`, and the tower maps are injective.

The proof extends Iwahori's regular representation to the infinite algebra. For a Coxeter system
of type `A_∞` on a group `W'` (`TauCeti.coxeterMatrixAInfty`), the left regular operators
`CoxeterSystem.heckeLeftMul` on `W' →₀ R` satisfy the defining relations of the infinite algebra,
which gives `TauCeti.InfiniteTypeAHeckeAlgebra.regularRep`. A Coxeter group `W` of type `A_(n-1)`
maps to `W'` by `s i ↦ s' i` (`CoxeterSystem.parabolicHom`), and this map is injective and
preserves lengths, because a standard parabolic subgroup is the Coxeter group of the restricted
Coxeter matrix. So a reduced word for `w : W` stays reduced in `W'`, and the image of `T_w` in the
infinite algebra sends the basis vector of `1` to the basis vector of the image of `w`
(`TauCeti.TypeAHeckeAlgebra.regularRep_toInfinite_Tw_apply_single_one`). These vectors are linearly
independent, and the elements `T_w` form a basis of the finite algebra, so `toInfinite` is
injective.

## Main definitions

* `TauCeti.InfiniteTypeAHeckeAlgebra.regularRep`: the regular representation of the infinite
  type-A Hecke algebra on `W' →₀ R`, for a Coxeter system of type `A_∞` on `W'`.
* `TauCeti.TypeAHeckeAlgebra.stageEquiv`: the isomorphism from the Hecke algebra on `n` strands to
  the stage of the first `n` strands of the infinite algebra.

## Main results

* `TauCeti.TypeAHeckeAlgebra.regularRep_toInfinite_Tw_apply_single_one`: the image of `T_w` in the
  infinite algebra takes the basis vector of `1` to that of the image of `w`.
* `TauCeti.TypeAHeckeAlgebra.toInfinite_injective`: **the finite Hecke algebra embeds in the
  infinite one.**
* `TauCeti.TypeAHeckeAlgebra.strandIncl_injective`: the tower maps are injective.
* `TauCeti.TypeAHeckeAlgebra.linearIndependent_toInfinite_Tw`: the images of the elements
  `T_w` are linearly independent in the infinite algebra, so they form a basis of the stage.
* `TauCeti.InfiniteTypeAHeckeAlgebra.finrank_stage_eq_natCard`: the rank of the stage is the order
  of the Coxeter group of type `A_(n-1)`.

## References

* N. Iwahori, *On the structure of a Hecke ring of a Chevalley group over a finite field*,
  J. Fac. Sci. Univ. Tokyo Sect. I 10 (1964), 215–236.
* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Chapter IV, §1, no. 8, Theorem 2, for
  the standard parabolic subgroups.
* V. F. R. Jones, *Hecke algebra representations of braid groups and link polynomials*,
  Ann. of Math. 126 (1987), 335–388, Section 4.
-/

public section

namespace TauCeti

open CoxeterSystem Finsupp

variable {R : Type*} [CommRing R] {q : Rˣ}

namespace InfiniteTypeAHeckeAlgebra

variable {W' : Type*} [Group W'] (cs' : CoxeterSystem coxeterMatrixAInfty W')

variable (q) in
/-- The **regular representation** of the infinite type-A Hecke algebra on the free module
`W' →₀ R` over a Coxeter group of type `A_∞`: the generator `T i` acts by the left regular operator
`CoxeterSystem.heckeLeftMul` with quadratic coefficient `q - q⁻¹`. -/
noncomputable def regularRep : InfiniteTypeAHeckeAlgebra R q →ₐ[R] Module.End R (W' →₀ R) :=
  lift (fun i ↦ cs'.heckeLeftMul ((q : R) - ↑q⁻¹) i) (fun i ↦ cs'.heckeLeftMul_mul_self _ i)
    (fun i ↦ by
      have hb := cs'.prod_map_heckeLeftMul_braidWord ((q : R) - ↑q⁻¹) i (i + 1)
      rw [braidWord, coxeterMatrixAInfty_eq_three (.inl rfl), braidWord,
        coxeterMatrixAInfty_eq_three (.inr rfl), prod_map_alternatingWord_three,
        prod_map_alternatingWord_three] at hb
      exact hb.symm)
    (fun {i j} h ↦ by
      have hb := cs'.prod_map_heckeLeftMul_braidWord ((q : R) - ↑q⁻¹) i j
      rw [braidWord, coxeterMatrixAInfty_eq_two (.inl h), braidWord,
        coxeterMatrixAInfty_eq_two (.inr h), prod_map_alternatingWord_two,
        prod_map_alternatingWord_two] at hb
      exact hb)

/-- The regular representation takes the generator `T i` to the left regular operator of the
simple reflection `s i`. -/
@[simp]
theorem regularRep_T (i : ℕ) :
    regularRep q cs' (T q i) = cs'.heckeLeftMul ((q : R) - ↑q⁻¹) i :=
  lift_T _ _ _ _ i

end InfiniteTypeAHeckeAlgebra

namespace TypeAHeckeAlgebra

variable {n : ℕ} {W W' : Type*} [Group W] [Group W']
variable (cs : CoxeterSystem (CoxeterMatrix.A (n - 1)) W)
variable (cs' : CoxeterSystem coxeterMatrixAInfty W')

/-- The image of `T_w` in the infinite type-A Hecke algebra takes, in the regular representation
of the infinite algebra, the basis vector of `1` to the basis vector of the image of `w` under the
inclusion `CoxeterSystem.parabolicHom` of Coxeter groups of types `A_(n-1)` and `A_∞`. -/
@[simp]
theorem regularRep_toInfinite_Tw_apply_single_one (w : W) :
    InfiniteTypeAHeckeAlgebra.regularRep q cs' (toInfinite R q n (Tw q cs w)) (single 1 1) =
      single (cs.parabolicHom cs' coxeterMatrixA_eq_coxeterMatrixAInfty w) (1 : R) := by
  obtain ⟨ω, hω, rfl⟩ := cs.exists_isReduced w
  have hT : (⇑(InfiniteTypeAHeckeAlgebra.regularRep q cs') ∘ ⇑(toInfinite R q n)) ∘ T q =
      cs'.heckeLeftMul ((q : R) - ↑q⁻¹) ∘ ((↑) : Fin (n - 1) → ℕ) :=
    funext fun i ↦ by simp
  rw [Tw_wordProd cs hω, map_list_prod, map_list_prod, List.map_map, List.map_map, hT,
    ← List.map_map, parabolicHom_wordProd, cs'.prod_map_heckeLeftMul_apply_single_one _
      ((cs.isReduced_map_iff coxeterMatrixA_eq_coxeterMatrixAInfty).2 hω)]

/-- Evaluation at the basis vector of `1` of the regular representation of the infinite algebra,
pulled back to the Hecke algebra on `n` strands, is the coordinate map of the basis `T_w` followed
by the inclusion of Coxeter groups. -/
private theorem regularRep_toInfinite_apply_single_one (x : TypeAHeckeAlgebra R q n) :
    InfiniteTypeAHeckeAlgebra.regularRep q cs' (toInfinite R q n x) (single 1 1) =
      mapDomain (cs.parabolicHom cs' coxeterMatrixA_eq_coxeterMatrixAInfty)
        ((basisTw q cs).repr x) := by
  have h : LinearMap.applyₗ (single 1 1) ∘ₗ
        (InfiniteTypeAHeckeAlgebra.regularRep q cs').toLinearMap ∘ₗ
          (toInfinite R q n).toLinearMap =
      lmapDomain R R (cs.parabolicHom cs' coxeterMatrixA_eq_coxeterMatrixAInfty) ∘ₗ
        ((basisTw q cs).repr : TypeAHeckeAlgebra R q n →ₗ[R] W →₀ R) :=
    (basisTw q cs).ext fun w ↦ by
      have hw := (basisTw q cs).repr_self w
      rw [coe_basisTw] at hw
      simp [hw]
  exact LinearMap.congr_fun h x

variable (R q n) in
/-- **The Hecke algebra on `n` strands embeds in the infinite type-A Hecke algebra**, over every
commutative ring and for every unit parameter. -/
theorem toInfinite_injective : Function.Injective (toInfinite R q n) := by
  let cs := (CoxeterMatrix.A (n - 1)).toCoxeterSystem
  let cs' := coxeterMatrixAInfty.toCoxeterSystem
  intro x y hxy
  refine (basisTw q cs).repr.injective <|
    mapDomain_injective (cs.parabolicHom_injective (cs' := cs')
      coxeterMatrixA_eq_coxeterMatrixAInfty) ?_
  rw [← regularRep_toInfinite_apply_single_one cs cs',
    ← regularRep_toInfinite_apply_single_one cs cs', hxy]

variable (R q n) in
/-- **The finite presentation is isomorphic to the stage**: the Hecke algebra on `n` strands is
isomorphic to the stage of the first `n` strands of the infinite type-A Hecke algebra, by the map
`T i ↦ T i`. -/
noncomputable def stageEquiv :
    TypeAHeckeAlgebra R q n ≃ₐ[R] InfiniteTypeAHeckeAlgebra.stage R q n :=
  (AlgEquiv.ofInjective _ (toInfinite_injective R q n)).trans
    (Subalgebra.equivOfEq _ _ range_toInfinite)

/-- The isomorphism `TauCeti.TypeAHeckeAlgebra.stageEquiv` is the map `toInfinite`. -/
@[simp]
theorem coe_stageEquiv_apply (x : TypeAHeckeAlgebra R q n) :
    (stageEquiv R q n x : InfiniteTypeAHeckeAlgebra R q) = toInfinite R q n x :=
  (rfl)

/-- The inverse of `TauCeti.TypeAHeckeAlgebra.stageEquiv` is a section of `toInfinite`. -/
@[simp]
theorem toInfinite_stageEquiv_symm_apply (x : InfiniteTypeAHeckeAlgebra.stage R q n) :
    toInfinite R q n ((stageEquiv R q n).symm x) = x := by
  rw [← coe_stageEquiv_apply, AlgEquiv.apply_symm_apply]

/-- The images in the infinite type-A Hecke algebra of the elements `T_w` of the Hecke algebra on
`n` strands are linearly independent. -/
theorem linearIndependent_toInfinite_Tw :
    LinearIndependent R fun w : W ↦ toInfinite R q n (Tw q cs w) :=
  (linearIndependent_Tw cs).map' (toInfinite R q n).toLinearMap
    (LinearMap.ker_eq_bot.2 (toInfinite_injective R q n))

variable (R q n) in
/-- The tower map from `n` to `n + 1` strands is injective. -/
theorem strandIncl_injective : Function.Injective (strandIncl R q n) :=
  .of_comp (f := toInfinite R q (n + 1)) <| by
    simpa only [Function.comp_def, toInfinite_strandIncl] using toInfinite_injective R q n

end TypeAHeckeAlgebra

namespace InfiniteTypeAHeckeAlgebra

open TypeAHeckeAlgebra

variable {n : ℕ} {W : Type*} [Group W] (cs : CoxeterSystem (CoxeterMatrix.A (n - 1)) W)

/-- The stage of the first `n` strands is a free module: the images of the elements `T_w` of the
Hecke algebra on `n` strands form a basis. -/
instance : Module.Free R (stage R q n) :=
  .of_basis ((basisTw q (CoxeterMatrix.A (n - 1)).toCoxeterSystem).map
    (stageEquiv R q n).toLinearEquiv)

include cs in
/-- Over a nontrivial commutative ring, the rank of the stage of the first `n` strands is the order
of the Coxeter group `W` of type `A_(n-1)`. -/
theorem finrank_stage_eq_natCard [Nontrivial R] : Module.finrank R (stage R q n) = Nat.card W := by
  rw [← (stageEquiv R q n).toLinearEquiv.finrank_eq, finrank_eq_natCard cs]

end InfiniteTypeAHeckeAlgebra

end TauCeti
