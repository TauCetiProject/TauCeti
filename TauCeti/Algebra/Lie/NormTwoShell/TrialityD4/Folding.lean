/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.NormTwoShell.Folding
public import TauCeti.Algebra.Lie.NormTwoShell.TrialityD4.FixedBasis
public import TauCeti.LinearAlgebra.Matrix.Cartan.Folding.Reflection

/-!
# Folding D₄ triality to the Cartan datum and Serre system of G₂

Under the vertex-orbit enumeration `TauCeti.D4Triality.vertexOrbitEquiv` (`0` for the outer
three-cycle `{0, 2, 3}` and `1` for the central fixed node `{1}`), folding `CartanMatrix.D 4`
along `TauCeti.trialityPermD4` produces `CartanMatrix.G₂` on the nose, with Bourbaki's short simple
root at index `0` and long simple root at index `1`. Both orbits have folding scale `1`.

On the diagram-fixed Cartan coordinate lattice, the normalized folded coroots
`Matrix.foldedCoroot` are the primitive orbit sums `![1, 0, 1, 1]` and `![0, 1, 0, 0]`, their
pairings with `Matrix.foldedRootFunctional` give `TauCeti.DynkinType.G2.cartanMatrix`, and the
product of the two integral folded Weyl reflections has order `6` (acting by `-1` at its cube).

In `Matrix.ShellLieAlgebra (CartanMatrix.D 4)`, the folded Chevalley frame `(foldedH, foldedE,
foldedF)` evaluates along `vertexOrbitEquiv` to `invariantCartan` and the simple-orbit vectors
`invariantRoot false 0`, `invariantRoot false 1`, `invariantRoot true 0`, `invariantRoot true 1`.
Transporting `Matrix.ShellLieAlgebra.isSerreSystem_folded` across
`fixedSubalgebraBaseChangeLieEquiv` yields the `G₂` Serre comparison homomorphism
`TauCeti.D4Triality.g2SerreLift A` into the triality-fixed Lie subalgebra over every commutative
ring `A`.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plates IV and IX.
* V. G. Kac, *Infinite dimensional Lie algebras*, third edition, §7.9.
-/

public section

open scoped TensorProduct

namespace TauCeti.D4Triality

open _root_.Matrix

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
  classical
  obtain ⟨k, rfl⟩ := vertexOrbitEquiv.surjective O
  ext j
  rw [coe_foldedCoroot_vertexOrbitEquiv, Equiv.Perm.permutationFixedBasis_apply]
  have hmem : (Quotient.mk (Equiv.Perm.SameCycle.setoid trialityPermD4) j =
      vertexOrbitEquiv k) ↔ vertexOrbit j = k := by
    rw [← vertexOrbitEquiv.symm.apply_eq_iff_eq, vertexOrbitEquiv_symm_mk,
      Equiv.symm_apply_apply]
  rw [if_congr hmem rfl rfl]
  fin_cases k <;> fin_cases j <;> decide

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
  foldedReflection (Fact.out : (CartanMatrix.D 4).PosDef) (CartanMatrix.D_diag (n := 4))
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
  have hc6 : c ^ 6 = 1 := by
    ext v
    have h6' : (c ^ 6) v = - -v := by
      rw [show (6 : ℕ) = 3 + 3 by rfl, pow_add, mul_apply_eq_comp,
        trialityFoldedReflection_mul_pow_three, trialityFoldedReflection_mul_pow_three]
    simp [h6']
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

/-! ### Explicit evaluation of the folded Chevalley frame -/

/-- The folded Cartan generators of `D₄` triality are `invariantCartan 0` and
`invariantCartan 1`. -/
@[simp]
theorem foldedH_vertexOrbitEquiv (k : Fin 2) :
    ShellLieAlgebra.foldedH (CartanMatrix.D 4) trialityPermD4 (vertexOrbitEquiv k) =
      invariantCartan k := by
  rw [ShellLieAlgebra.foldedH_def, foldingScale_eq_one, one_smul, invariantCartan_eq_sum]
  refine Finset.sum_congr ?_ fun _ _ ↦ rfl
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, sameCycle_vertexOrbitEquiv_out_iff]

/-- The folded raising generators of `D₄` triality are `invariantRoot false 0` and
`invariantRoot false 1`. -/
@[simp]
theorem foldedE_vertexOrbitEquiv (k : Fin 2) :
    ShellLieAlgebra.foldedE (CartanMatrix.D_diag (n := 4)) trialityPermD4 (vertexOrbitEquiv k) =
      invariantRoot false (k.castLE (by decide)) := by
  refine (ShellLieAlgebra.basis (CartanMatrix.D 4)).repr.injective (Finsupp.ext fun idx ↦ ?_)
  rcases idx with i | a
  · simp [ShellLieAlgebra.foldedE_def, ShellLieAlgebra.chevalleyE_def,
      ← ShellLieAlgebra.basis_inr]
  · obtain ⟨⟨neg', j⟩, rfl⟩ := rootEquiv.surjective a
    rw [rootEquiv_apply, basis_repr_invariantRoot, ShellLieAlgebra.foldedE_def, map_sum,
      Finsupp.finsetSum_apply]
    simp only [sameCycle_vertexOrbitEquiv_out_iff, ShellLieAlgebra.chevalleyE_def,
      ← ShellLieAlgebra.basis_inr, Module.Basis.repr_self, Finsupp.single_apply, Sum.inr.injEq,
      Subtype.ext_iff, coe_root]
    cases neg' <;> fin_cases k <;> fin_cases j <;>
      decide

/-- The folded lowering generators of `D₄` triality are `invariantRoot true 0` and
`invariantRoot true 1`. -/
@[simp]
theorem foldedF_vertexOrbitEquiv (k : Fin 2) :
    ShellLieAlgebra.foldedF (CartanMatrix.D_diag (n := 4)) trialityPermD4 (vertexOrbitEquiv k) =
      invariantRoot true (k.castLE (by decide)) := by
  refine (ShellLieAlgebra.basis (CartanMatrix.D 4)).repr.injective (Finsupp.ext fun idx ↦ ?_)
  rcases idx with i | a
  · simp [ShellLieAlgebra.foldedF_def, ShellLieAlgebra.chevalleyF_def,
      ← ShellLieAlgebra.basis_inr]
  · obtain ⟨⟨neg', j⟩, rfl⟩ := rootEquiv.surjective a
    rw [rootEquiv_apply, basis_repr_invariantRoot, ShellLieAlgebra.foldedF_def,
      foldingScale_eq_one, one_smul, map_sum, Finsupp.finsetSum_apply]
    simp only [sameCycle_vertexOrbitEquiv_out_iff, ShellLieAlgebra.chevalleyF_def,
      ← ShellLieAlgebra.basis_inr, Module.Basis.repr_self, Finsupp.single_apply, Sum.inr.injEq,
      Subtype.ext_iff, coe_root]
    cases neg' <;> fin_cases k <;> fin_cases j <;>
      decide

/-! ### The folded `G₂` Serre system and homomorphism over any commutative ring -/

/-- `invariantCartan` and the simple-orbit vectors `invariantRoot false (0, 1)`,
`invariantRoot true (0, 1)` form an integral Serre system for `CartanMatrix.G₂` in
`Matrix.ShellLieAlgebra (CartanMatrix.D 4)`. -/
theorem isSerreSystem_g2 :
    IsSerreSystem ℤ CartanMatrix.G₂ invariantCartan
      (fun k : Fin 2 ↦ invariantRoot false (k.castLE (by decide)))
      (fun k : Fin 2 ↦ invariantRoot true (k.castLE (by decide))) := by
  have h := (ShellLieAlgebra.isSerreSystem_folded trialityPermD4
    (Fact.out : (CartanMatrix.D 4).PosDef) (CartanMatrix.D_diag (n := 4))
    (CartanMatrix.D_off_diag_nonpos 4) reindex_cartanMatrix).submatrix vertexOrbitEquiv.injective
  simpa only [submatrix_foldedCartanMatrix_vertexOrbitEquiv, Function.comp_def,
    foldedH_vertexOrbitEquiv, foldedE_vertexOrbitEquiv, foldedF_vertexOrbitEquiv] using h

/-- The folded `G₂` generators inside the integral triality-fixed Lie subring form a Serre system
for `CartanMatrix.G₂`. -/
theorem isSerreSystem_g2Fixed :
    IsSerreSystem ℤ CartanMatrix.G₂
      (fun k : Fin 2 ↦ fixedBasis (.inl k))
      (fun k : Fin 2 ↦ fixedBasis (.inr (false, k.castLE (by decide))))
      (fun k : Fin 2 ↦ fixedBasis (.inr (true, k.castLE (by decide)))) :=
  IsSerreSystem.of_injective trialityLieEquiv.toLieHom.fixedSubalgebra.incl Subtype.val_injective
    (by simpa only [Function.comp_def, LieSubalgebra.coe_incl, coe_fixedBasis_inl,
      coe_fixedBasis_inr] using isSerreSystem_g2)

private noncomputable def toFixedBaseChangeLieHom (A : Type*) [CommRing A] :
    trialityLieEquiv.toLieHom.fixedSubalgebra →ₗ⁅ℤ⁆
      (LieEquiv.baseChange A trialityLieEquiv).toLieHom.fixedSubalgebra where
  toFun v := fixedSubalgebraBaseChangeLieEquiv A (1 ⊗ₜ[ℤ] v)
  map_add' x y := by rw [TensorProduct.tmul_add, map_add]
  map_smul' n x := by simp only [RingHom.id_apply, TensorProduct.tmul_smul, map_zsmul]
  map_lie' {x y} := by
    rw [← (fixedSubalgebraBaseChangeLieEquiv A).map_lie, LieAlgebra.ExtendScalars.bracket_tmul,
      one_mul]

/-- Over any commutative ring `A`, the scalar-extended folded `G₂` generators in the triality-fixed
Lie subalgebra form an `A`-Serre system for `CartanMatrix.G₂`. -/
theorem isSerreSystem_g2FixedBaseChange (A : Type*) [CommRing A] :
    IsSerreSystem A CartanMatrix.G₂
      (fun k : Fin 2 ↦ fixedSubalgebraBaseChangeBasis A (.inl k))
      (fun k : Fin 2 ↦ fixedSubalgebraBaseChangeBasis A (.inr (false, k.castLE (by decide))))
      (fun k : Fin 2 ↦ fixedSubalgebraBaseChangeBasis A (.inr (true, k.castLE (by decide)))) := by
  have h := (isSerreSystem_g2Fixed.map (toFixedBaseChangeLieHom A)).changeScalars (S := A)
  simpa only [Function.comp_def, toFixedBaseChangeLieHom, fixedSubalgebraBaseChangeBasis_apply,
    LieHom.coe_mk, LinearMap.coe_mk, AddHom.coe_mk] using h

/-- **The folded `G₂` Serre comparison homomorphism over any commutative ring `A`**, mapping the
Serre presentation `Matrix.ToLieAlgebra A CartanMatrix.G₂` into the triality-fixed Lie subalgebra
of `A ⊗[ℤ] Matrix.ShellLieAlgebra (CartanMatrix.D 4)`. -/
noncomputable def g2SerreLift (A : Type*) [CommRing A] :
    Matrix.ToLieAlgebra A CartanMatrix.G₂ →ₗ⁅A⁆
      (LieEquiv.baseChange A trialityLieEquiv).toLieHom.fixedSubalgebra :=
  serreLift (isSerreSystem_g2FixedBaseChange A)

@[simp]
theorem g2SerreLift_serreH (A : Type*) [CommRing A] (k : Fin 2) :
    g2SerreLift A (serreH A CartanMatrix.G₂ k) =
      fixedSubalgebraBaseChangeBasis A (.inl k) :=
  serreLift_serreH _ k

@[simp]
theorem g2SerreLift_serreE (A : Type*) [CommRing A] (k : Fin 2) :
    g2SerreLift A (serreE A CartanMatrix.G₂ k) =
      fixedSubalgebraBaseChangeBasis A (.inr (false, k.castLE (by decide))) :=
  serreLift_serreE _ k

@[simp]
theorem g2SerreLift_serreF (A : Type*) [CommRing A] (k : Fin 2) :
    g2SerreLift A (serreF A CartanMatrix.G₂ k) =
      fixedSubalgebraBaseChangeBasis A (.inr (true, k.castLE (by decide))) :=
  serreLift_serreF _ k

theorem coe_g2SerreLift_serreH (A : Type*) [CommRing A] (k : Fin 2) :
    ((g2SerreLift A (serreH A CartanMatrix.G₂ k) :
        (LieEquiv.baseChange A trialityLieEquiv).toLieHom.fixedSubalgebra) :
        A ⊗[ℤ] ShellLieAlgebra (CartanMatrix.D 4)) =
      1 ⊗ₜ[ℤ] invariantCartan k := by
  simp

theorem coe_g2SerreLift_serreE (A : Type*) [CommRing A] (k : Fin 2) :
    ((g2SerreLift A (serreE A CartanMatrix.G₂ k) :
        (LieEquiv.baseChange A trialityLieEquiv).toLieHom.fixedSubalgebra) :
        A ⊗[ℤ] ShellLieAlgebra (CartanMatrix.D 4)) =
      1 ⊗ₜ[ℤ] invariantRoot false (k.castLE (by decide)) := by
  simp

theorem coe_g2SerreLift_serreF (A : Type*) [CommRing A] (k : Fin 2) :
    ((g2SerreLift A (serreF A CartanMatrix.G₂ k) :
        (LieEquiv.baseChange A trialityLieEquiv).toLieHom.fixedSubalgebra) :
        A ⊗[ℤ] ShellLieAlgebra (CartanMatrix.D 4)) =
      1 ⊗ₜ[ℤ] invariantRoot true (k.castLE (by decide)) := by
  simp

end TauCeti.D4Triality
