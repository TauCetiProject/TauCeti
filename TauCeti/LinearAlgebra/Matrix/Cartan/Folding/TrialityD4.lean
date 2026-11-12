/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.Cartan.Folding.Reflection
public import TauCeti.LinearAlgebra.Matrix.NormTwoShell.TrialityD4
public import TauCeti.LinearAlgebra.RootSystem.FiniteType.Classical

/-!
# Folding the D₄ Cartan datum and Weyl reflections along triality to G₂

Under the vertex-orbit enumeration `TauCeti.D4Triality.vertexOrbitEquiv` (`0` for the outer
three-cycle `{0, 2, 3}` and `1` for the central fixed node `{1}`), folding `CartanMatrix.D 4`
along `TauCeti.trialityPermD4` produces `CartanMatrix.G₂` on the nose, with Bourbaki's short simple
root at index `0` and long simple root at index `1`. Both orbits have folding scale `1`.

Specifically:
* `TauCeti.D4Triality.vertexOrbit`, `TauCeti.D4Triality.vertexRepresentative`, and
  `TauCeti.D4Triality.vertexOrbitEquiv` enumerate the two `TauCeti.trialityPermD4`-orbits on
  `Fin 4`, and `TauCeti.D4Triality.simpleOrbit` embeds them as the two simple root-orbit indices
  `0` and `1` in `Fin 6`.
* `TauCeti.D4Triality.foldingScale_eq_one`,
  `TauCeti.D4Triality.foldedCartanMatrix_vertexOrbitEquiv`, and
  `TauCeti.D4Triality.submatrix_transpose_foldedCartanMatrix_vertexOrbitEquiv` compute the folding
  scales and identify `(CartanMatrix.D 4).foldedCartanMatrix trialityPermD4` along
  `vertexOrbitEquiv` with `CartanMatrix.G₂` and its transpose with
  `TauCeti.DynkinType.G2.cartanMatrix`.
* `TauCeti.D4Triality.invariantCartanVec`, `TauCeti.D4Triality.coe_foldedCoroot_vertexOrbitEquiv`,
  and `TauCeti.D4Triality.foldedRootFunctional_foldedCoroot_vertexOrbitEquiv` identify the
  normalized folded coroots `Matrix.foldedCoroot` on the `trialityPermD4`-fixed Cartan coordinate
  lattice with the primitive orbit sums `![1, 0, 1, 1]` and `![0, 1, 0, 0]`
  (`Equiv.Perm.permutationFixedBasis`) and evaluate their pairings with
  `Matrix.foldedRootFunctional`.
* `TauCeti.D4Triality.trialityFoldedReflection` and
  `TauCeti.D4Triality.orderOf_trialityFoldedReflection_mul` construct the two integral folded Weyl
  reflections on the fixed Cartan coordinate lattice and prove that their product has Coxeter order
  `6` (acting by `-1` at its cube).

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plates IV and IX.
* V. G. Kac, *Infinite dimensional Lie algebras*, third edition, §7.9.
-/

public section

namespace TauCeti.D4Triality

open _root_.Matrix

/-! ### Vertex orbits, simple-orbit embedding, and invariant Cartan coordinates -/

/-- Orbit labels for `trialityPermD4`: `0` is the outer three-cycle `{0, 2, 3}` and `1` is the
central fixed vertex `{1}`. -/
@[expose] def vertexOrbit : Fin 4 → Fin 2 := ![0, 1, 0, 0]

/-- Chosen representatives `0` and `1` of the two `trialityPermD4`-orbits on `Fin 4`. -/
@[expose] def vertexRepresentative : Fin 2 → Fin 4 := ![0, 1]

@[simp]
theorem vertexOrbit_vertexRepresentative (k : Fin 2) :
    vertexOrbit (vertexRepresentative k) = k := by
  decide +revert

@[simp]
theorem vertexOrbit_trialityPermD4 (i : Fin 4) :
    vertexOrbit (trialityPermD4 i) = vertexOrbit i := by
  fin_cases i <;> simp [vertexOrbit]

/-- `vertexOrbit` distinguishes exactly the cycles of `trialityPermD4`. -/
theorem sameCycle_trialityPermD4_iff (i j : Fin 4) :
    trialityPermD4.SameCycle i j ↔ vertexOrbit i = vertexOrbit j := by
  constructor
  · exact fun h ↦ h.apply_eq_of_apply_eq vertexOrbit_trialityPermD4
  · intro h
    have h02 : trialityPermD4.SameCycle 0 2 := ⟨1, by simp⟩
    have h23 : trialityPermD4.SameCycle 2 3 := ⟨1, by simp⟩
    have h03 : trialityPermD4.SameCycle 0 3 := h02.trans h23
    fin_cases i <;> fin_cases j <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] at h ⊢
    all_goals first
      | exact Equiv.Perm.SameCycle.refl _ _
      | exact h02 | exact h02.symm | exact h23 | exact h23.symm | exact h03 | exact h03.symm
      | exact absurd h (by decide)

/-- Explicit enumeration of the two vertex orbits of `trialityPermD4`: `0` corresponds to the
outer three-cycle `{0, 2, 3}` and `1` to the central fixed vertex `{1}`. -/
def vertexOrbitEquiv : Fin 2 ≃ Quotient (Equiv.Perm.SameCycle.setoid trialityPermD4) where
  toFun k := Quotient.mk _ (vertexRepresentative k)
  invFun O := Quotient.liftOn O vertexOrbit fun _ _ h ↦ (sameCycle_trialityPermD4_iff _ _).mp h
  left_inv := vertexOrbit_vertexRepresentative
  right_inv O := Quotient.inductionOn O fun _ ↦
    Quotient.sound ((sameCycle_trialityPermD4_iff _ _).mpr (vertexOrbit_vertexRepresentative _))

theorem vertexOrbitEquiv_apply (k : Fin 2) :
    vertexOrbitEquiv k = Quotient.mk _ (vertexRepresentative k) :=
  (rfl)

@[simp]
theorem vertexOrbitEquiv_symm_mk (i : Fin 4) :
    vertexOrbitEquiv.symm (Quotient.mk _ i) = vertexOrbit i :=
  (rfl)

@[simp]
theorem vertexOrbit_out_vertexOrbitEquiv (k : Fin 2) :
    vertexOrbit (vertexOrbitEquiv k).out = k := by
  have h := congrArg vertexOrbitEquiv.symm (Quotient.out_eq (vertexOrbitEquiv k))
  rwa [vertexOrbitEquiv_symm_mk, Equiv.symm_apply_apply] at h

@[simp]
theorem sameCycle_vertexOrbitEquiv_out_iff (i : Fin 4) (k : Fin 2) :
    trialityPermD4.SameCycle i (vertexOrbitEquiv k).out ↔ vertexOrbit i = k := by
  rw [sameCycle_trialityPermD4_iff, vertexOrbit_out_vertexOrbitEquiv]

/-- Embedding of the two `trialityPermD4` vertex-orbit indices (`0` outer three-cycle, `1` central
vertex) as the two simple root-orbit indices `0` and `1` in `Fin 6`. -/
@[expose] def simpleOrbit (k : Fin 2) : Fin 6 :=
  k.castLE (by decide)

@[simp]
theorem simpleOrbit_zero : simpleOrbit 0 = 0 :=
  rfl

@[simp]
theorem simpleOrbit_one : simpleOrbit 1 = 1 :=
  rfl

@[simp]
theorem coe_simpleOrbit (k : Fin 2) : (simpleOrbit k : ℕ) = k :=
  rfl

/-- Coordinates of the two primitive `trialityPermD4`-invariant Cartan vectors:
`![1, 0, 1, 1]` for the outer three-cycle and `![0, 1, 0, 0]` for the central vertex. -/
@[expose] def invariantCartanVec : Fin 2 → Fin 4 → ℤ :=
  ![![1, 0, 1, 1], ![0, 1, 0, 0]]

@[simp]
theorem invariantCartanVec_comp_trialityPermD4_symm (k : Fin 2) :
    invariantCartanVec k ∘ trialityPermD4.symm = invariantCartanVec k := by
  ext i
  obtain ⟨i, rfl⟩ := trialityPermD4.surjective i
  simp only [Function.comp_apply, Equiv.symm_apply_apply]
  fin_cases k <;> fin_cases i <;> simp [invariantCartanVec]

/-! ### Folded Cartan matrix and folding scale -/

/-- Both vertex orbits of `trialityPermD4` on `CartanMatrix.D 4` have folding scale `1`: the outer
three-cycle consists of pairwise non-adjacent vertices and the central vertex is a singleton. -/
@[simp]
theorem foldingScale_eq_one
    (O : Quotient (Equiv.Perm.SameCycle.setoid trialityPermD4)) :
    (CartanMatrix.D 4).foldingScale trialityPermD4 O = 1 := by
  obtain ⟨k, rfl⟩ := vertexOrbitEquiv.surjective O
  have hk : trialityPermD4.SameCycle (vertexRepresentative k) (vertexOrbitEquiv k).out := by
    rw [sameCycle_vertexOrbitEquiv_out_iff, vertexOrbit_vertexRepresentative]
  rw [foldingScale_eq_of_sameCycle reindex_cartanMatrix hk]
  simp only [sameCycle_vertexOrbitEquiv_out_iff]
  fin_cases k <;> decide

/-- Under `vertexOrbitEquiv`, the `H`-row folded Cartan matrix of `D₄` triality is
`CartanMatrix.G₂`, with `0` the short simple root and `1` the long simple root. -/
@[simp]
theorem foldedCartanMatrix_vertexOrbitEquiv (i j : Fin 2) :
    (CartanMatrix.D 4).foldedCartanMatrix trialityPermD4
        (vertexOrbitEquiv i) (vertexOrbitEquiv j) =
      CartanMatrix.G₂ i j := by
  have hj : trialityPermD4.SameCycle (vertexRepresentative j) (vertexOrbitEquiv j).out := by
    rw [sameCycle_vertexOrbitEquiv_out_iff, vertexOrbit_vertexRepresentative]
  rw [foldedCartanMatrix_apply_of_sameCycle reindex_cartanMatrix (vertexOrbitEquiv i) hj,
    foldingScale_eq_one, one_mul]
  simp only [sameCycle_vertexOrbitEquiv_out_iff]
  fin_cases i <;> fin_cases j <;> decide

/-- Matrix form of `foldedCartanMatrix_vertexOrbitEquiv`. -/
@[simp]
theorem submatrix_foldedCartanMatrix_vertexOrbitEquiv :
    ((CartanMatrix.D 4).foldedCartanMatrix trialityPermD4).submatrix
        vertexOrbitEquiv vertexOrbitEquiv =
      CartanMatrix.G₂ := by
  ext i j
  exact foldedCartanMatrix_vertexOrbitEquiv i j

/-- Transposing the `H`-row folded Cartan matrix gives Bourbaki's root-row `G₂` Cartan matrix
`DynkinType.G2.cartanMatrix` without permuting the short and long nodes. -/
@[simp]
theorem submatrix_transpose_foldedCartanMatrix_vertexOrbitEquiv :
    ((CartanMatrix.D 4).foldedCartanMatrix trialityPermD4)ᵀ.submatrix
        vertexOrbitEquiv vertexOrbitEquiv =
      DynkinType.G2.cartanMatrix := by
  ext i j
  simp only [submatrix_apply, transpose_apply, foldedCartanMatrix_vertexOrbitEquiv]
  fin_cases i <;> fin_cases j <;> simp [DynkinType.cartanMatrix_G2, CartanMatrix.G₂]

/-! ### Folded coroots, root functionals, and integral Weyl reflections -/

/-- The normalized folded simple coroots of `D₄` triality are `invariantCartanVec 0 = ![1, 0, 1, 1]`
and `invariantCartanVec 1 = ![0, 1, 0, 0]`. -/
@[simp]
theorem coe_foldedCoroot_vertexOrbitEquiv (k : Fin 2) :
    ((CartanMatrix.D 4).foldedCoroot trialityPermD4 (vertexOrbitEquiv k) : Fin 4 → ℤ) =
      invariantCartanVec k := by
  rw [coe_foldedCoroot, foldingScale_eq_one, one_smul]
  ext j
  simp only [sameCycle_vertexOrbitEquiv_out_iff, Finset.sum_apply, Pi.single_apply]
  fin_cases k <;> fin_cases j <;> decide

/-- The normalized folded coroots of `D₄` triality coincide with the integral permutation-fixed
basis of the `D₄` Cartan coordinate lattice. -/
theorem foldedCoroot_eq_permutationFixedBasis
    (O : Quotient (Equiv.Perm.SameCycle.setoid trialityPermD4)) :
    (CartanMatrix.D 4).foldedCoroot trialityPermD4 O =
      trialityPermD4.permutationFixedBasis O := by
  simp [foldedCoroot_def]

/-- Pairing the `i`-th folded simple root functional with the `j`-th folded simple coroot produces
Bourbaki's `DynkinType.G2.cartanMatrix i j`. -/
@[simp]
theorem foldedRootFunctional_foldedCoroot_vertexOrbitEquiv (i j : Fin 2) :
    (CartanMatrix.D 4).foldedRootFunctional trialityPermD4 (vertexOrbitEquiv i)
        ((CartanMatrix.D 4).foldedCoroot trialityPermD4 (vertexOrbitEquiv j)) =
      DynkinType.G2.cartanMatrix i j := by
  rw [foldedRootFunctional_foldedCoroot _ _ (CartanMatrix.D_isSymm 4),
    foldedCartanMatrix_vertexOrbitEquiv]
  fin_cases i <;> fin_cases j <;> simp [DynkinType.cartanMatrix_G2, CartanMatrix.G₂]

/-- The two integral folded simple reflections (`0` short, `1` long) on the `trialityPermD4`-fixed
Cartan coordinate lattice. -/
noncomputable def trialityFoldedReflection (k : Fin 2) :
    (LinearEquiv.funCongrLeft ℤ ℤ trialityPermD4).toLinearMap.fixedSubmodule ≃ₗ[ℤ]
      (LinearEquiv.funCongrLeft ℤ ℤ trialityPermD4).toLinearMap.fixedSubmodule :=
  foldedReflection (posDef_cartanMatrix_D 4) (CartanMatrix.D_diag (n := 4))
    (CartanMatrix.D_off_diag_nonpos 4) reindex_cartanMatrix (vertexOrbitEquiv k)

/-- Each folded simple reflection negates its own folded simple coroot. -/
@[simp]
theorem trialityFoldedReflection_foldedCoroot_self (k : Fin 2) :
    trialityFoldedReflection k
        ((CartanMatrix.D 4).foldedCoroot trialityPermD4 (vertexOrbitEquiv k)) =
      -(CartanMatrix.D 4).foldedCoroot trialityPermD4 (vertexOrbitEquiv k) :=
  foldedReflection_apply_self _ _ _ _ _

/-- The short folded reflection `s₀` sends the long folded coroot `h₁` to `h₁ + h₀`. -/
@[simp]
theorem trialityFoldedReflection_zero_foldedCoroot_one :
    trialityFoldedReflection 0
        ((CartanMatrix.D 4).foldedCoroot trialityPermD4 (vertexOrbitEquiv 1)) =
      (CartanMatrix.D 4).foldedCoroot trialityPermD4 (vertexOrbitEquiv 1) +
        (CartanMatrix.D 4).foldedCoroot trialityPermD4 (vertexOrbitEquiv 0) := by
  rw [trialityFoldedReflection, foldedReflection_foldedCoroot,
    foldedCartanMatrix_vertexOrbitEquiv]
  have h10 : CartanMatrix.G₂ 1 0 = -1 := by simp [CartanMatrix.G₂]
  rw [h10, neg_one_smul, sub_neg_eq_add]

/-- The long folded reflection `s₁` sends the short folded coroot `h₀` to `h₀ + 3 • h₁`. -/
@[simp]
theorem trialityFoldedReflection_one_foldedCoroot_zero :
    trialityFoldedReflection 1
        ((CartanMatrix.D 4).foldedCoroot trialityPermD4 (vertexOrbitEquiv 0)) =
      (CartanMatrix.D 4).foldedCoroot trialityPermD4 (vertexOrbitEquiv 0) +
        (3 : ℤ) • (CartanMatrix.D 4).foldedCoroot trialityPermD4 (vertexOrbitEquiv 1) := by
  rw [trialityFoldedReflection, foldedReflection_foldedCoroot,
    foldedCartanMatrix_vertexOrbitEquiv]
  have h01 : CartanMatrix.G₂ 0 1 = -3 := by simp [CartanMatrix.G₂]
  rw [h01, neg_smul, sub_neg_eq_add]

/-- The cube of the folded Coxeter element `s₀ s₁` acts as `-1` on the fixed Cartan lattice. -/
theorem trialityFoldedReflection_mul_pow_three
    (v : (LinearEquiv.funCongrLeft ℤ ℤ trialityPermD4).toLinearMap.fixedSubmodule) :
    ((trialityFoldedReflection 0 * trialityFoldedReflection 1) ^ 3) v = -v := by
  classical
  let b := (trialityPermD4.permutationFixedBasis (R := ℤ)).reindex vertexOrbitEquiv.symm
  have hb (k : Fin 2) :
      b k = (CartanMatrix.D 4).foldedCoroot trialityPermD4 (vertexOrbitEquiv k) := by
    simp [b, foldedCoroot_eq_permutationFixedBasis]
  suffices (((trialityFoldedReflection 0 * trialityFoldedReflection 1) ^ 3).toLinearMap :
      _ →ₗ[ℤ] _) = -LinearMap.id from DFunLike.congr_fun this v
  refine b.ext fun k ↦ ?_
  fin_cases k <;>
    simp only [Fin.zero_eta, Fin.mk_one, hb, LinearEquiv.coe_coe, pow_succ, pow_zero, one_mul,
      mul_apply_eq_comp, map_add, map_neg, map_zsmul,
      trialityFoldedReflection_foldedCoroot_self,
      trialityFoldedReflection_zero_foldedCoroot_one,
      trialityFoldedReflection_one_foldedCoroot_zero, LinearMap.neg_apply, LinearMap.id_apply] <;>
    module

/-- The product of the two folded simple reflections on the fixed Cartan lattice has Coxeter order
`6`, matching the dihedral Weyl group of type `G₂`. -/
@[simp]
theorem orderOf_trialityFoldedReflection_mul :
    orderOf (trialityFoldedReflection 0 * trialityFoldedReflection 1) = 6 := by
  set c := trialityFoldedReflection 0 * trialityFoldedReflection 1
  let h₀ := (CartanMatrix.D 4).foldedCoroot trialityPermD4 (vertexOrbitEquiv 0)
  let h₁ := (CartanMatrix.D 4).foldedCoroot trialityPermD4 (vertexOrbitEquiv 1)
  have hc3 : c ^ 3 * c ^ 3 = 1 := by
    ext v
    simp [c, mul_apply_eq_comp, trialityFoldedReflection_mul_pow_three]
  have hc6 : c ^ 6 = 1 := (pow_add c 3 3).trans hc3
  refine orderOf_eq_of_pow_and_pow_div_prime hc6 fun p hp hdvd ↦ ?_
  have hp6 : p = 2 ∨ p = 3 := by
    have hle := Nat.le_of_dvd (by decide) hdvd
    rcases hp.eq_two_or_odd with rfl | hodd
    · exact Or.inl rfl
    · have hp2 := hp.two_le
      interval_cases p <;> simp_all
  rcases hp6 with rfl | rfl
  · intro h3
    have hval := congrFun (congrArg Subtype.val (LinearEquiv.congr_fun h3 h₀)) 0
    rw [trialityFoldedReflection_mul_pow_three] at hval
    simp [h₀, invariantCartanVec] at hval
  · intro h2
    have hc2 : (c ^ 2) h₀ = h₀ + (3 : ℤ) • h₁ := by
      simp only [c, h₀, h₁, sq, mul_apply_eq_comp, map_add, map_neg, map_zsmul,
        trialityFoldedReflection_foldedCoroot_self,
        trialityFoldedReflection_zero_foldedCoroot_one,
        trialityFoldedReflection_one_foldedCoroot_zero]
      module
    have hval := congrFun (congrArg Subtype.val (LinearEquiv.congr_fun h2 h₀)) 1
    rw [hc2] at hval
    simp [h₀, h₁, invariantCartanVec] at hval

end TauCeti.D4Triality
