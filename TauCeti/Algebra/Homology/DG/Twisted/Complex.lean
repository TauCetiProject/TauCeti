/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DG.Twisted.Cocycle
public import TauCeti.Algebra.Homology.DG.Module.Right.Defs
public import TauCeti.Algebra.Homology.GradedCochainComplex

/-!
# The twisted complex of a twisting cocycle

Let `m` be a twisting cocycle with values in the differential graded algebra `(𝒜, d)`, on the
finite set `P` graded by `ind`, and let `(ℳ, dM)` be a differential graded right module over
`(𝒜, d)`.  The **twisted complex** `ℳ ⊗ ⟨P⟩` has underlying module `P → M`, the direct sum of one
copy of `M` for each generator, and differential

`D (α ⊗ x) = dM α ⊗ x + (-1) ^ |α| Σ_y (α · m x y) ⊗ y`

on a homogeneous elementary tensor `α ⊗ x`, written `Pi.single x α`.  The Koszul sign is carried by
the Koszul twist of parameter one, `(InternalGrading.ofDecomposition ℳ).koszulTwist 1`, which is
`α ↦ (-1) ^ |α| α` on `M`.  The total degree of `α ⊗ x` is `|α| - ind x`, so a generator of index
`k` sits in cohomological degree `-k`, and `D` raises the total degree by one.

The main theorem is that `D` squares to zero when `(ℳ, dM)` is a differential graded right module
and `m` satisfies the twisting equation; the twisted complex is then packaged as a cochain complex
of `R`-modules through `TauCeti.gradedCochainComplex`.  Right modules are represented as left
modules over `Aᵐᵒᵖ`, so `α · a` is written `MulOpposite.op a • α`.

## Main definitions

* `TauCeti.TwistingCocycle.totalGrading`: the grading of `P → M` by total degree.
* `TauCeti.TwistingCocycle.twistedDifferential`: the differential `D` of the twisted complex.
* `TauCeti.TwistingCocycle.twistedCochainComplex`: the twisted complex as a cochain complex of
  `R`-modules.

## Main results

* `TauCeti.TwistingCocycle.twistedDifferential_single`: the formula on a homogeneous elementary
  tensor.
* `TauCeti.TwistingCocycle.twistedDifferential_mem_totalGrading`: `D` raises the total degree by
  one.
* `TauCeti.TwistingCocycle.twistedDifferential_sq_zero`: `D ∘ D = 0`.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, Section 1.4.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Morse homology with differential graded
  coefficients*, Progress in Mathematics 360, Birkhäuser, 2025, Chapter 3.
-/

public section

open CategoryTheory DirectSum MulOpposite

namespace TauCeti

universe uR uA uM uP

variable {R : Type uR} {A : Type uA} {M : Type uM}
  [CommRing R] [Ring A] [Algebra R A]
  [AddCommGroup M] [Module R M]

namespace TwistingCocycle

variable [Module Aᵐᵒᵖ M] [IsScalarTower R Aᵐᵒᵖ M]
  {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜] {d : A →ₗ[R] A}
  {P : Type uP} [Fintype P] {ind : P → ℤ}

/-- The twisted complex `ℳ ⊗ ⟨P⟩`, identified with `P → M`, is graded in total degree `n` by
`f x ∈ ℳ (n + ind x)`: the generator `x` sits in cohomological degree `-ind x`. -/
def totalGrading (ℳ : ℤ → Submodule R M) (ind : P → ℤ) (n : ℤ) : Submodule R (P → M) :=
  Submodule.pi Set.univ fun x ↦ ℳ (n + ind x)

omit [Fintype P] in
theorem mem_totalGrading_iff {ℳ : ℤ → Submodule R M} {n : ℤ} {f : P → M} :
    f ∈ totalGrading ℳ ind n ↔ ∀ x, f x ∈ ℳ (n + ind x) := by
  rw [totalGrading, Submodule.mem_pi]
  simp only [Set.mem_univ, true_implies]

variable [SMulCommClass R Aᵐᵒᵖ M]

/-- The twisted differential on `ℳ ⊗ ⟨P⟩`, identified with `P → M`.  Its `y`-component is
`(D f) y = dM (f y) + Σ_x op (m x y) • ε (f x)`, where `ε` is the Koszul twist of parameter
one; on a homogeneous elementary tensor this is
`D (α ⊗ x) = dM α ⊗ x + (-1) ^ |α| Σ_y (α · m x y) ⊗ y` (`twistedDifferential_single`).  The right
`A`-action on `M` and its commutation with the `R`-scalars are parameters of the definition: the
map depends on the action, and `R`-linearity needs the commutation. -/
noncomputable def twistedDifferential (m : TwistingCocycle 𝒜 d P ind) (ℳ : ℤ → Submodule R M)
    [DirectSum.Decomposition ℳ] (dM : M →ₗ[R] M) : (P → M) →ₗ[R] (P → M) where
  toFun f y :=
    dM (f y) + ∑ x, op (m.m x y) • (InternalGrading.ofDecomposition ℳ).koszulTwist 1 (f x)
  map_add' f g := by
    funext y
    simp only [Pi.add_apply, map_add, smul_add, Finset.sum_add_distrib]
    abel
  map_smul' r f := by
    funext y
    simp only [Pi.smul_apply, map_smul, RingHom.id_apply, smul_add, Finset.smul_sum, smul_comm r]

variable (m : TwistingCocycle 𝒜 d P ind) {ℳ : ℤ → Submodule R M} [DirectSum.Decomposition ℳ]
  (dM : M →ₗ[R] M)

omit [Module Aᵐᵒᵖ M] [IsScalarTower R Aᵐᵒᵖ M] [GradedAlgebra 𝒜] [Fintype P]
  [SMulCommClass R Aᵐᵒᵖ M] in
/-- The Koszul twist of parameter one of `ℳ`, on an element of degree `q`. -/
private theorem koszulTwist_one_apply {q : ℤ} {α : M} (hα : α ∈ ℳ q) :
    (InternalGrading.ofDecomposition ℳ).koszulTwist 1 α = q.negOnePow • α :=
  InternalGrading.koszulTwist_one_apply_of_mem_negOnePow_smul _
    (by rwa [InternalGrading.ofDecomposition_piece])

omit [IsScalarTower R Aᵐᵒᵖ M] [GradedAlgebra 𝒜] in
theorem twistedDifferential_apply (f : P → M) (y : P) :
    twistedDifferential m ℳ dM f y =
      dM (f y) + ∑ x, op (m.m x y) • (InternalGrading.ofDecomposition ℳ).koszulTwist 1 (f x) := by
  rw [twistedDifferential]
  rfl

omit [IsScalarTower R Aᵐᵒᵖ M] [GradedAlgebra 𝒜] in
/-- Evaluation on a homogeneous elementary tensor `α ⊗ x`, with `α` of degree `q`. -/
theorem twistedDifferential_single [DecidableEq P] (x : P) {q : ℤ} {α : M} (hα : α ∈ ℳ q) :
    twistedDifferential m ℳ dM (Pi.single x α) =
      Pi.single x (dM α) + ∑ y, Pi.single y (q.negOnePow • (op (m.m x y) • α)) := by
  funext y'
  simp only [twistedDifferential_apply, Pi.add_apply, Finset.sum_apply, Pi.single_apply]
  rw [Finset.sum_eq_single x (fun x' _ hx' ↦ by simp [hx']) (by simp)]
  simp only [ite_true, koszulTwist_one_apply hα, smul_comm (op (m.m x y')) q.negOnePow]
  split_ifs with hxy <;> simp [hxy]

omit [IsScalarTower R Aᵐᵒᵖ M] [GradedAlgebra 𝒜] in
/-- The `z`-component of the twisted differential of a homogeneous elementary tensor `α ⊗ x`. -/
theorem twistedDifferential_single_apply [DecidableEq P] (x z : P) {q : ℤ} {α : M}
    (hα : α ∈ ℳ q) :
    twistedDifferential m ℳ dM (Pi.single x α) z =
      (Pi.single x (dM α) : P → M) z + q.negOnePow • (op (m.m x z) • α) := by
  rw [twistedDifferential_single m dM x hα, Pi.add_apply, Finset.sum_apply]
  simp [Pi.single_apply]

variable [SetLike.GradedSMul (InternalGrading.ofDecomposition 𝒜).opposite.piece ℳ]

variable {h : IsDGAlgebra 𝒜 d}

/-- The twisted differential raises the total degree by one. -/
theorem twistedDifferential_mem_totalGrading (hM : IsDGRightModule h ℳ dM)
    {n : ℤ} {f : P → M} (hf : f ∈ totalGrading ℳ ind n) :
    twistedDifferential m ℳ dM f ∈ totalGrading ℳ ind (n + 1) := by
  rw [mem_totalGrading_iff] at hf ⊢
  intro y
  rw [twistedDifferential_apply]
  refine add_mem ?_ (Submodule.sum_mem _ fun x _ ↦ ?_)
  · have := hM.isHomogeneous.map_mem (hf y)
    convert this using 2
    ring
  · have hα : (InternalGrading.ofDecomposition ℳ).koszulTwist 1 (f x) ∈ ℳ (n + ind x) := by
      rw [koszulTwist_one_apply (hf x)]
      exact Submodule.smul_of_tower_mem _ _ (hf x)
    have hm : op (m.m x y) ∈
        (InternalGrading.ofDecomposition 𝒜).opposite.piece (ind y - ind x + 1) := by
      rw [InternalGrading.op_mem_opposite_piece_iff, InternalGrading.ofDecomposition_piece]
      exact m.mem_graded x y
    have := SetLike.GradedSMul.smul_mem hm hα
    convert this using 2
    rw [vadd_eq_add]
    ring

/-- The twisted differential squares to zero when `(ℳ, dM)` is a differential graded right module
over `(𝒜, d)`. -/
theorem twistedDifferential_sq_zero (hM : IsDGRightModule h ℳ dM) (f : P → M) :
    twistedDifferential m ℳ dM (twistedDifferential m ℳ dM f) = 0 := by
  classical
  -- Reduce to a homogeneous elementary tensor `α ⊗ x`.
  suffices key : ∀ (x : P) {q : ℤ} {α : M}, α ∈ ℳ q →
      twistedDifferential m ℳ dM (twistedDifferential m ℳ dM (Pi.single x α)) = 0 by
    rw [← Finset.univ_sum_single f, map_sum, map_sum]
    refine Finset.sum_eq_zero fun x _ ↦ ?_
    generalize f x = α
    induction α using DirectSum.Decomposition.inductionOn ℳ with
    | zero => simp
    | @homogeneous i α => exact key x α.2
    | add a b ha hb => rw [Pi.single_add, map_add, map_add, ha, hb, add_zero]
  intro x q α hα
  funext z
  -- The `z`-component of `D (D (α ⊗ x))`, through `twistedDifferential_single_apply` twice.
  have hβ : ∀ y, q.negOnePow • (op (m.m x y) • α) ∈ ℳ (q + (ind y - ind x + 1)) := fun y ↦ by
    refine Submodule.smul_of_tower_mem _ _ ?_
    have hm : op (m.m x y) ∈
        (InternalGrading.ofDecomposition 𝒜).opposite.piece (ind y - ind x + 1) := by
      rw [InternalGrading.op_mem_opposite_piece_iff, InternalGrading.ofDecomposition_piece]
      exact m.mem_graded x y
    have := SetLike.GradedSMul.smul_mem hm hα
    rwa [vadd_eq_add, add_comm] at this
  rw [twistedDifferential_single m dM x hα, map_add, map_sum, Pi.add_apply, Finset.sum_apply,
    twistedDifferential_single_apply m dM x z (hM.isHomogeneous.map_mem hα), hM.sq_zero,
    Pi.single_zero, Pi.zero_apply, zero_add]
  simp only [fun y ↦ twistedDifferential_single_apply m dM y z (hβ y), Finset.sum_add_distrib,
    Pi.single_apply, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  -- The two terms in `dM α` cancel by the Leibniz rule.
  rw [LinearMap.map_smul_of_tower, hM.leibniz hα (m.m x z), smul_add, smul_smul,
    Int.units_mul_self, one_smul, Int.negOnePow_succ, Units.neg_smul,
    add_assoc (q.negOnePow • (op (m.m x z) • dM α)), neg_add_cancel_left]
  -- What remains is the twisting equation for `m x z`, acting on `α`.
  rw [m.twisting x z, Finset.op_sum, Finset.sum_smul, ← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun y _ ↦ ?_
  -- The sign of the `y`-term: the exponent is rearranged to isolate an even part.
  have hexp : q + (ind y - ind x + 1) + q = (ind x - ind y + 1) + 2 * (q + ind y - ind x) := by
    ring
  have hsign : (q + (ind y - ind x + 1)).negOnePow * q.negOnePow = -(ind x - ind y).negOnePow := by
    rw [← Int.negOnePow_add, ← Int.negOnePow_succ, hexp, Int.negOnePow_add,
      Int.negOnePow_two_mul, mul_one]
  rw [op_smul, smul_assoc, smul_comm (op (m.m y z)) q.negOnePow, smul_smul, smul_smul,
    ← op_mul, hsign, Units.neg_smul, add_neg_cancel]

/-- The twisted complex `ℳ ⊗ ⟨P⟩` as a cochain complex of `R`-modules: the degree-`n` term is
`totalGrading ℳ ind n` and the differential is the restriction of `twistedDifferential`. -/
noncomputable def twistedCochainComplex (hM : IsDGRightModule h ℳ dM) :
    CochainComplex (ModuleCat.{max uP uM} R) ℤ :=
  gradedCochainComplex (totalGrading ℳ ind) (twistedDifferential m ℳ dM)
    (LinearMap.isHomogeneous_def.mpr fun _ _ hf ↦ twistedDifferential_mem_totalGrading m dM hM hf)
    fun _ f ↦ twistedDifferential_sq_zero m dM hM f

@[simp]
theorem twistedCochainComplex_X (hM : IsDGRightModule h ℳ dM) (n : ℤ) :
    (twistedCochainComplex m dM hM).X n = ModuleCat.of R (totalGrading ℳ ind n) := by
  rw [twistedCochainComplex]
  exact gradedCochainComplex_X n

/-- The degree-`n` term of the twisted complex is the total-degree-`n` submodule of `P → M`, as a
linear equivalence. -/
noncomputable def twistedCochainComplexXEquiv (hM : IsDGRightModule h ℳ dM) (n : ℤ) :
    (twistedCochainComplex m dM hM).X n ≃ₗ[R] totalGrading ℳ ind n :=
  gradedCochainComplexXEquiv (ℳ := totalGrading ℳ ind) (dM := twistedDifferential m ℳ dM) n

/-- Under `twistedCochainComplexXEquiv`, the differential of the twisted complex is the twisted
differential. -/
theorem twistedCochainComplexXEquiv_d (hM : IsDGRightModule h ℳ dM) (n : ℤ)
    (f : (twistedCochainComplex m dM hM).X n) :
    (twistedCochainComplexXEquiv m dM hM (n + 1)
        (((twistedCochainComplex m dM hM).d n (n + 1)).hom f) : P → M) =
      twistedDifferential m ℳ dM (twistedCochainComplexXEquiv m dM hM n f) := by
  unfold twistedCochainComplexXEquiv
  exact gradedCochainComplexXEquiv_d n f

end TwistingCocycle

end TauCeti
