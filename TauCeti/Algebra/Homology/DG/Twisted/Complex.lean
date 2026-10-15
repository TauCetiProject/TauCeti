/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DG.Twisted.Cocycle
public import TauCeti.Algebra.Homology.DG.Module.Right.Defs
public import TauCeti.Algebra.Homology.GradedCochainComplex
import TauCeti.Algebra.Ring.NegOnePow

/-!
# The twisted complex of a twisting cocycle

Let `m : P → P → A` be a matrix of coefficients in the differential graded algebra `(𝒜, d)`,
indexed by the finite set `P` graded by `ind`, and let `(ℳ, dM)` be a differential graded right
module over `(𝒜, d)`.  The **twisted complex** `ℳ ⊗ ⟨P⟩` has underlying module `P → M`, the direct
sum of one copy of `M` for each generator, and differential

`D (α ⊗ x) = dM α ⊗ x + (-1) ^ |α| Σ_y (α · m x y) ⊗ y`

on a homogeneous elementary tensor `α ⊗ x`, written `Pi.single x α`.  The Koszul sign is carried by
the Koszul twist of parameter one, `(InternalGrading.ofDecomposition ℳ).koszulTwist 1`, which is
`α ↦ (-1) ^ |α| α` on `M`.  The total degree of `α ⊗ x` is `|α| - ind x`, so a generator of index
`k` sits in cohomological degree `-k`.

The differential is defined for any matrix.  It raises the total degree by one when the entries
are homogeneous of degree `ind y - ind x + 1`, and it squares to zero when in addition `m`
satisfies the twisting equation; the one-sidedness of a `TauCeti.TwistingCocycle` plays no role,
and the results for a twisting cocycle are the specializations to its matrix.  The twisted
complex is packaged as a cochain complex of `R`-modules through `TauCeti.gradedCochainComplex`.
Right modules are represented as left modules over `Aᵐᵒᵖ`, so `α · a` is written
`MulOpposite.op a • α`.

## Main definitions

* `TauCeti.twistedTotalGrading`: the grading of `P → M` by total degree, with its decomposition
  of `P → M` for finite `P` (`instDecompositionTwistedTotalGrading`, from
  `iSupIndep_twistedTotalGrading` and `iSup_twistedTotalGrading_eq_top`) and the compatibility of a
  pointwise left action with the degrees (`instGradedSMulTwistedTotalGrading`).
* `TauCeti.twistedDifferential`: the differential `D` of the twisted complex of a matrix.
* `TauCeti.twistedCochainComplex`: the twisted complex as a cochain complex of `R`-modules.
* `TauCeti.TwistingCocycle.twistedCochainComplex`: the same for a twisting cocycle.

## Main results

* `TauCeti.twistedDifferential_single`: the formula on a homogeneous elementary tensor.
* `TauCeti.twistedDifferential_mem_twistedTotalGrading`: `D` raises the total degree by one.
* `TauCeti.twistedDifferential_sq_zero`: `D ∘ D = 0` under the twisting equation, and
  `TauCeti.TwistingCocycle.twistedDifferential_sq_zero` for a twisting cocycle.

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

section TotalGrading

variable {R : Type uR} {M : Type uM} [Semiring R] [AddCommMonoid M] [Module R M]
  {P : Type uP} {ind : P → ℤ}

/-- The twisted complex `ℳ ⊗ ⟨P⟩`, identified with `P → M`, is graded in total degree `n` by
`f x ∈ ℳ (n + ind x)`: the generator `x` sits in cohomological degree `-ind x`. -/
def twistedTotalGrading (ℳ : ℤ → Submodule R M) (ind : P → ℤ) (n : ℤ) : Submodule R (P → M) :=
  Submodule.pi Set.univ fun x ↦ ℳ (n + ind x)

@[simp]
theorem mem_twistedTotalGrading_iff {ℳ : ℤ → Submodule R M} {n : ℤ} {f : P → M} :
    f ∈ twistedTotalGrading ℳ ind n ↔ ∀ x, f x ∈ ℳ (n + ind x) := by
  rw [twistedTotalGrading, Submodule.mem_pi]
  simp only [Set.mem_univ, true_implies]

section GradedSMul

variable {A : Type uA} [AddCommMonoid A] [Module R A] [SMul A M]
  {𝒜 : ℤ → Submodule R A} {ℳ : ℤ → Submodule R M}

/-- The pointwise left action on `P → M` adds degrees in the total grading, as soon as the action
on `M` does. -/
instance instGradedSMulTwistedTotalGrading [SetLike.GradedSMul 𝒜 ℳ] :
    SetLike.GradedSMul 𝒜 (twistedTotalGrading ℳ ind) where
  smul_mem := by
    intro i n a f ha hf
    rw [mem_twistedTotalGrading_iff] at hf ⊢
    intro x
    have := SetLike.GradedSMul.smul_mem ha (hf x)
    simpa only [vadd_eq_add, add_assoc, Pi.smul_apply] using this

end GradedSMul

section Decomposition

variable (ℳ : ℤ → Submodule R M) [DirectSum.Decomposition ℳ]

/-- The pieces of the total grading are independent. -/
theorem iSupIndep_twistedTotalGrading : iSupIndep (twistedTotalGrading ℳ ind) := by
  rw [iSupIndep_def]
  intro n
  rw [Submodule.disjoint_def]
  intro f hf hf'
  have hle : (⨆ (k) (_ : k ≠ n), twistedTotalGrading ℳ ind k) ≤
      Submodule.pi Set.univ fun x ↦ ⨆ (j) (_ : j ≠ n + ind x), ℳ j := by
    refine iSup₂_le fun k hk g hg ↦ ?_
    rw [mem_twistedTotalGrading_iff] at hg
    rw [Submodule.mem_pi]
    intro x _
    exact Submodule.mem_iSup_of_mem (k + ind x)
      (Submodule.mem_iSup_of_mem (fun h ↦ hk (add_right_cancel h)) (hg x))
  have hind := (DirectSum.Decomposition.isInternal ℳ).submodule_iSupIndep
  rw [iSupIndep_def] at hind
  rw [mem_twistedTotalGrading_iff] at hf
  funext x
  exact Submodule.disjoint_def.mp (hind (n + ind x)) (f x) (hf x)
    (Submodule.mem_pi.mp (hle hf') x (Set.mem_univ x))

variable [Finite P]

/-- The pieces of the total grading span `P → M` when `P` is finite. -/
theorem iSup_twistedTotalGrading_eq_top : (⨆ n, twistedTotalGrading ℳ ind n) = ⊤ := by
  classical
  let _ := Fintype.ofFinite P
  rw [eq_top_iff]
  intro f _
  rw [← Finset.univ_sum_single f]
  refine Submodule.sum_mem _ fun x _ ↦ ?_
  have hsum : (Pi.single x (f x) : P → M) =
      ∑ q ∈ (decompose ℳ (f x)).support, (Pi.single x (decompose ℳ (f x) q : M) : P → M) := by
    rw [← LinearMap.coe_single R (fun _ : P ↦ M), ← map_sum, DirectSum.sum_support_decompose]
  rw [hsum]
  refine Submodule.sum_mem _ fun q _ ↦ Submodule.mem_iSup_of_mem (q - ind x) ?_
  rw [mem_twistedTotalGrading_iff]
  intro y
  by_cases hy : y = x
  · subst hy
    rw [Pi.single_eq_same, sub_add_cancel]
    exact SetLike.coe_mem _
  · rw [Pi.single_eq_of_ne hy]
    exact zero_mem _

end Decomposition

end TotalGrading

section TotalGradingDecomposition

variable {R : Type uR} {M : Type uM} [Ring R] [AddCommGroup M] [Module R M]
  {P : Type uP} [Finite P] {ind : P → ℤ} (ℳ : ℤ → Submodule R M) [DirectSum.Decomposition ℳ]

/-- The total grading is an internal direct sum decomposition of `P → M` for finite `P`.  Over a
semiring, independence and spanning do not give an internal direct sum (see
`DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top`), so the instance is stated over a
ring. -/
noncomputable instance instDecompositionTwistedTotalGrading :
    DirectSum.Decomposition (twistedTotalGrading ℳ ind) :=
  (DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    (iSupIndep_twistedTotalGrading ℳ) (iSup_twistedTotalGrading_eq_top ℳ)).chooseDecomposition

end TotalGradingDecomposition

section Differential

variable {R : Type uR} {A : Type uA} {M : Type uM} [CommRing R] [Semiring A]
  {P : Type uP} [Fintype P]

section AddCommMonoid

variable [AddCommMonoid M] [Module R M] [Module Aᵐᵒᵖ M] [SMulCommClass R Aᵐᵒᵖ M]

/-- The twisted differential on `ℳ ⊗ ⟨P⟩`, identified with `P → M`, of a matrix `m`.  Its
`y`-component is `(D f) y = dM (f y) + Σ_x op (m x y) • ε (f x)`, where `ε` is the Koszul twist of
parameter one; on a homogeneous elementary tensor this is
`D (α ⊗ x) = dM α ⊗ x + (-1) ^ |α| Σ_y (α · m x y) ⊗ y` (`twistedDifferential_single`).  The right
`A`-action on `M` and its commutation with the `R`-scalars are parameters of the definition: the
map depends on the action, and `R`-linearity needs the commutation. -/
noncomputable def twistedDifferential (m : P → P → A) (ℳ : ℤ → Submodule R M)
    [DirectSum.Decomposition ℳ] (dM : M →ₗ[R] M) : (P → M) →ₗ[R] (P → M) where
  toFun f y :=
    dM (f y) + ∑ x, op (m x y) • (InternalGrading.ofDecomposition ℳ).koszulTwist 1 (f x)
  map_add' f g := by
    funext y
    simp only [Pi.add_apply, map_add, smul_add, Finset.sum_add_distrib]
    abel
  map_smul' r f := by
    funext y
    simp only [Pi.smul_apply, map_smul, RingHom.id_apply, smul_add, Finset.smul_sum, smul_comm r]

variable (m : P → P → A) {ℳ : ℤ → Submodule R M} [DirectSum.Decomposition ℳ] (dM : M →ₗ[R] M)

@[simp]
theorem twistedDifferential_apply (f : P → M) (y : P) :
    twistedDifferential m ℳ dM f y =
      dM (f y) + ∑ x, op (m x y) • (InternalGrading.ofDecomposition ℳ).koszulTwist 1 (f x) := by
  rw [twistedDifferential]
  rfl

end AddCommMonoid

variable [AddCommGroup M] [Module R M] [Module Aᵐᵒᵖ M] [SMulCommClass R Aᵐᵒᵖ M]
  (m : P → P → A) {ℳ : ℤ → Submodule R M} [DirectSum.Decomposition ℳ] (dM : M →ₗ[R] M)

/-- Evaluation on a homogeneous elementary tensor `α ⊗ x`, with `α` of degree `q`. -/
theorem twistedDifferential_single [DecidableEq P] (x : P) {q : ℤ} {α : M} (hα : α ∈ ℳ q) :
    twistedDifferential m ℳ dM (Pi.single x α) =
      Pi.single x (dM α) + ∑ y, Pi.single y (q.negOnePow • (op (m x y) • α)) := by
  -- The Koszul twist of parameter one acts on `α` by the `ℤˣ`-scalar `q.negOnePow`.
  have hα' : α ∈ (InternalGrading.ofDecomposition ℳ).piece q := by
    rwa [InternalGrading.ofDecomposition_piece]
  have hε : (InternalGrading.ofDecomposition ℳ).koszulTwist 1 α = q.negOnePow • α := by
    rw [InternalGrading.koszulTwist_one_apply_of_mem _ hα',
      negOnePow_smul_eq_negOnePowCast_smul (R := R), negOnePowCast_eq_intCast]
  funext y'
  simp only [twistedDifferential_apply, Pi.add_apply, Finset.sum_apply, Pi.single_apply]
  rw [Finset.sum_eq_single x (fun x' _ hx' ↦ by simp [hx']) (by simp)]
  simp only [ite_true, hε, smul_comm (op (m x y')) q.negOnePow]
  split_ifs with hxy <;> simp [hxy]

/-- The `z`-component of the twisted differential of a homogeneous elementary tensor `α ⊗ x`. -/
theorem twistedDifferential_single_apply [DecidableEq P] (x z : P) {q : ℤ} {α : M}
    (hα : α ∈ ℳ q) :
    twistedDifferential m ℳ dM (Pi.single x α) z =
      (Pi.single x (dM α) : P → M) z + q.negOnePow • (op (m x z) • α) := by
  rw [twistedDifferential_single m dM x hα, Pi.add_apply, Finset.sum_apply]
  simp [Pi.single_apply]

end Differential

variable {R : Type uR} {A : Type uA} {M : Type uM}
  [CommRing R] [Ring A] [Algebra R A]
  [AddCommGroup M] [Module R M]
  {P : Type uP} {ind : P → ℤ}
  [Fintype P] [Module Aᵐᵒᵖ M] [IsScalarTower R Aᵐᵒᵖ M] [SMulCommClass R Aᵐᵒᵖ M]
  (m : P → P → A) {ℳ : ℤ → Submodule R M} [DirectSum.Decomposition ℳ] (dM : M →ₗ[R] M)

variable {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜] {d : A →ₗ[R] A} {h : IsDGAlgebra 𝒜 d}
  [SetLike.GradedSMul (InternalGrading.ofDecomposition 𝒜).opposite.piece ℳ]

omit [IsScalarTower R Aᵐᵒᵖ M] in
/-- The twisted differential of a matrix with homogeneous entries of degree `ind y - ind x + 1`
raises the total degree by one, for any homogeneous `dM` of degree one. -/
theorem twistedDifferential_mem_twistedTotalGrading
    (hm : ∀ x y, m x y ∈ 𝒜 (ind y - ind x + 1)) (hdM : LinearMap.IsHomogeneous dM ℳ ℳ 1)
    {n : ℤ} {f : P → M} (hf : f ∈ twistedTotalGrading ℳ ind n) :
    twistedDifferential m ℳ dM f ∈ twistedTotalGrading ℳ ind (n + 1) := by
  rw [mem_twistedTotalGrading_iff] at hf ⊢
  intro y
  rw [twistedDifferential_apply]
  refine add_mem ?_ (Submodule.sum_mem _ fun x _ ↦ ?_)
  · have := hdM.map_mem (hf y)
    convert this using 2
    ring
  · -- The Koszul twist of parameter one preserves the degree: it acts by a sign.
    have hfx : f x ∈ (InternalGrading.ofDecomposition ℳ).piece (n + ind x) := by
      rw [InternalGrading.ofDecomposition_piece]
      exact hf x
    have hα : (InternalGrading.ofDecomposition ℳ).koszulTwist 1 (f x) ∈ ℳ (n + ind x) := by
      have := InternalGrading.koszulTwist_mem_piece _ hfx 1
      rwa [InternalGrading.ofDecomposition_piece] at this
    have hmxy : op (m x y) ∈
        (InternalGrading.ofDecomposition 𝒜).opposite.piece (ind y - ind x + 1) := by
      rw [InternalGrading.op_mem_opposite_piece_iff, InternalGrading.ofDecomposition_piece]
      exact hm x y
    have := SetLike.GradedSMul.smul_mem hmxy hα
    convert this using 2
    rw [vadd_eq_add]
    ring

/-- The twisted differential of a matrix with homogeneous entries which satisfies the twisting
equation squares to zero, when `(ℳ, dM)` is a differential graded right module over `(𝒜, d)`. -/
theorem twistedDifferential_sq_zero (hm : ∀ x y, m x y ∈ 𝒜 (ind y - ind x + 1))
    (htw : ∀ x y, d (m x y) = ∑ z, (ind x - ind z).negOnePow • (m x z * m z y))
    (hM : IsDGRightModule h ℳ dM) (f : P → M) :
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
  have hβ : ∀ y, q.negOnePow • (op (m x y) • α) ∈ ℳ (q + (ind y - ind x + 1)) := fun y ↦ by
    refine Submodule.smul_of_tower_mem _ _ ?_
    have hmxy : op (m x y) ∈
        (InternalGrading.ofDecomposition 𝒜).opposite.piece (ind y - ind x + 1) := by
      rw [InternalGrading.op_mem_opposite_piece_iff, InternalGrading.ofDecomposition_piece]
      exact hm x y
    have := SetLike.GradedSMul.smul_mem hmxy hα
    rwa [vadd_eq_add, add_comm] at this
  rw [twistedDifferential_single m dM x hα, map_add, map_sum, Pi.add_apply, Finset.sum_apply,
    twistedDifferential_single_apply m dM x z (hM.isHomogeneous.map_mem hα), hM.sq_zero,
    Pi.single_zero, Pi.zero_apply, zero_add]
  simp only [fun y ↦ twistedDifferential_single_apply m dM y z (hβ y), Finset.sum_add_distrib,
    Pi.single_apply, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  -- The two terms in `dM α` cancel by the Leibniz rule.
  rw [LinearMap.map_smul_of_tower, hM.leibniz hα (m x z), smul_add, smul_smul,
    Int.units_mul_self, one_smul, Int.negOnePow_succ, Units.neg_smul,
    add_assoc (q.negOnePow • (op (m x z) • dM α)), neg_add_cancel_left]
  -- What remains is the twisting equation for `m x z`, acting on `α`.
  rw [htw x z, Finset.op_sum, Finset.sum_smul, ← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun y _ ↦ ?_
  -- The sign of the `y`-term: the exponent is rearranged to isolate an even part.
  have hexp : q + (ind y - ind x + 1) + q = (ind x - ind y + 1) + 2 * (q + ind y - ind x) := by
    ring
  have hsign : (q + (ind y - ind x + 1)).negOnePow * q.negOnePow = -(ind x - ind y).negOnePow := by
    rw [← Int.negOnePow_add, ← Int.negOnePow_succ, hexp, Int.negOnePow_add,
      Int.negOnePow_two_mul, mul_one]
  rw [op_smul, smul_assoc, smul_comm (op (m y z)) q.negOnePow, smul_smul, smul_smul,
    ← op_mul, hsign, Units.neg_smul, add_neg_cancel]

variable {m dM} (hm : ∀ x y, m x y ∈ 𝒜 (ind y - ind x + 1))
  (htw : ∀ x y, d (m x y) = ∑ z, (ind x - ind z).negOnePow • (m x z * m z y))
  (hM : IsDGRightModule h ℳ dM)

/-- The twisted complex `ℳ ⊗ ⟨P⟩` of a matrix with homogeneous entries which satisfies the
twisting equation, as a cochain complex of `R`-modules: the degree-`n` term is
`twistedTotalGrading ℳ ind n` and the differential is the restriction of `twistedDifferential`. -/
noncomputable def twistedCochainComplex : CochainComplex (ModuleCat.{max uP uM} R) ℤ :=
  gradedCochainComplex (twistedTotalGrading ℳ ind) (twistedDifferential m ℳ dM)
    (LinearMap.isHomogeneous_def.mpr fun _ _ hf ↦
      twistedDifferential_mem_twistedTotalGrading m dM hm hM.isHomogeneous hf)
    fun _ f ↦ twistedDifferential_sq_zero m dM hm htw hM f

@[simp]
theorem twistedCochainComplex_X (n : ℤ) :
    (twistedCochainComplex hm htw hM).X n = ModuleCat.of R (twistedTotalGrading ℳ ind n) := by
  rw [twistedCochainComplex]
  exact gradedCochainComplex_X n

/-- The degree-`n` term of the twisted complex is the total-degree-`n` submodule of `P → M`, as a
linear equivalence. -/
noncomputable def twistedCochainComplexXEquiv (n : ℤ) :
    (twistedCochainComplex hm htw hM).X n ≃ₗ[R] twistedTotalGrading ℳ ind n :=
  gradedCochainComplexXEquiv (ℳ := twistedTotalGrading ℳ ind) (dM := twistedDifferential m ℳ dM) n

/-- Under `twistedCochainComplexXEquiv`, the differential of the twisted complex is the twisted
differential. -/
theorem twistedCochainComplexXEquiv_d (n : ℤ) (f : (twistedCochainComplex hm htw hM).X n) :
    (twistedCochainComplexXEquiv hm htw hM (n + 1)
        (((twistedCochainComplex hm htw hM).d n (n + 1)).hom f) : P → M) =
      twistedDifferential m ℳ dM (twistedCochainComplexXEquiv hm htw hM n f) := by
  unfold twistedCochainComplexXEquiv
  exact gradedCochainComplexXEquiv_d n f

namespace TwistingCocycle

variable (m : TwistingCocycle 𝒜 d P ind) (dM)

omit [IsScalarTower R Aᵐᵒᵖ M] in
/-- The twisted differential of a twisting cocycle raises the total degree by one, for any
homogeneous `dM` of degree one. -/
theorem twistedDifferential_mem_twistedTotalGrading (hdM : LinearMap.IsHomogeneous dM ℳ ℳ 1)
    {n : ℤ} {f : P → M} (hf : f ∈ twistedTotalGrading ℳ ind n) :
    twistedDifferential m.m ℳ dM f ∈ twistedTotalGrading ℳ ind (n + 1) :=
  TauCeti.twistedDifferential_mem_twistedTotalGrading m.m dM m.mem_graded hdM hf

/-- The twisted differential of a twisting cocycle squares to zero when `(ℳ, dM)` is a
differential graded right module over `(𝒜, d)`. -/
theorem twistedDifferential_sq_zero (hM : IsDGRightModule h ℳ dM) (f : P → M) :
    twistedDifferential m.m ℳ dM (twistedDifferential m.m ℳ dM f) = 0 :=
  TauCeti.twistedDifferential_sq_zero m.m dM m.mem_graded m.twisting hM f

/-- The twisted complex `ℳ ⊗ ⟨P⟩` of a twisting cocycle, as a cochain complex of `R`-modules. -/
noncomputable abbrev twistedCochainComplex (hM : IsDGRightModule h ℳ dM) :
    CochainComplex (ModuleCat.{max uP uM} R) ℤ :=
  TauCeti.twistedCochainComplex m.mem_graded m.twisting hM

end TwistingCocycle

end TauCeti
