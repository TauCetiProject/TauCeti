/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.StandardEtale.Basic

import Mathlib.Data.Fin.SuccPred
import Mathlib.Topology.Algebra.Group.Neighborhood
import TauCeti.RingTheory.Huber.WeightedEval.Continuous
import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.Complete

/-!
# Explicit Jacobian inverses for standard étale presentations

In a standard étale presentation $C = A\langle T_1, \dots, T_N\rangle /
\overline{(F_1, \dots, F_N)}$ over a complete Hausdorff Tate pair $(A, A^+)$ with
pseudo-uniformiser $\varpi$, the formal Jacobian determinant $J = \det(\partial F_i / \partial T_j)$
becomes invertible in $C$ with $\varpi^k \cdot \pi(J)^{-1} \in C^+$. Adjoining one restricted
variable $T_{N+1}$ and the equation $F'_{N+1} = T_{N+1} \cdot J - \varpi^k$ promotes this implicit
witness to an explicit coordinate without changing $(C, C^+)$, while squaring the formal Jacobian
determinant to $J^2$ with scale exponent $2k$. Conversely, for any $A^+$-integral system $F'$ and
$k' : \mathbb{N}$, the model quotient of `explicitInverse` automatically carries a canonical
`StandardEtalePresentation` with scale exponent $2k'$.

## Main definitions and results

* `TauCeti.Huber.explicitInverse`: enlarges `F' : Fin N' → tateSeries N' A` to
  `Fin (N' + 1) → tateSeries (N' + 1) A` by appending
  `T_{N'+1} * castSuccAlgHom (jacobian F') - algebraMap A _ (ϖ ^ k')`.
* `TauCeti.Huber.jacobian_explicitInverse`: the formal Jacobian determinant of
  `explicitInverse A ϖ F' k'` equals `tateSeries.castSuccAlgHom (tateSeries.jacobian F') ^ 2`.
* `TauCeti.Huber.StandardEtalePresentation.ofExplicitInverse`: canonical presentation of the model
  quotient pair of `explicitInverse A ϖ F' k'` with scale exponent `2 * k'`.
* `TauCeti.Huber.StandardEtalePresentation.withInverseHom` and
  `TauCeti.Huber.StandardEtalePresentation.withInverse`: upgrades any
  `P : StandardEtalePresentation Aplus ϖ Cplus` to a presentation of `Cplus` in `P.N + 1`
  variables using `explicitInverse A ϖ P.F P.k` and scale exponent `2 * P.k`.

## References

* R. Huber, *Étale Cohomology of Rigid Analytic Varieties and Adic Spaces*, Vieweg (1996),
  §1.6–1.7, Proposition 1.7.1.
* O. Gabber and L. Ramero, *Almost Ring Theory*, Lecture Notes in Math. **1800**, Springer (2003),
  Lemma 5.4.8.
* P. Scholze, *Perfectoid spaces*, Publ. Math. IHÉS **116** (2012), Proposition 6.4.
-/

public section

open scoped Topology

namespace TauCeti.Huber

section ExplicitInverse

variable {A : Type*} [CommRing A] [TopologicalSpace A] [NonarchimedeanRing A]

/-- **Enlarged system adjoining the relation `T_{N'} * J(F') = ϖ ^ k'`.** Given `ϖ : A`,
`F' : Fin N' → tateSeries N' A`, and an exponent `k' : ℕ`, this system in `N' + 1` restricted
variables keeps the embedded equations `F'_0, …, F'_{N'-1}` and appends
`T_{N'} * J(F') - ϖ ^ k'`. In a quotient where this system vanishes, the appended equation imposes
the relation `T_{N'} * J(F') = ϖ ^ k'`; when `ϖ` is a unit in `A` (in particular, a
pseudouniformiser of a Tate ring), this forces the image of `J(F')` to be invertible in the
quotient with `T_{N'} = ϖ ^ k' * J(F')⁻¹`. -/
noncomputable def explicitInverse (A : Type*) [CommRing A] [TopologicalSpace A]
    [NonarchimedeanRing A] (ϖ : A) {N' : ℕ} (F' : Fin N' → tateSeries N' A) (k' : ℕ) :
    Fin (N' + 1) → tateSeries (N' + 1) A :=
  Fin.snoc (fun i ↦ tateSeries.castSuccAlgHom (F' i))
    (tateSeries.X (N' + 1) A (Fin.last N') *
      tateSeries.castSuccAlgHom (tateSeries.jacobian F') -
      algebraMap A (tateSeries (N' + 1) A) (ϖ ^ k'))

@[simp]
theorem explicitInverse_castSucc (ϖ : A) {N' : ℕ} (F' : Fin N' → tateSeries N' A) (k' : ℕ)
    (i : Fin N') :
    explicitInverse A ϖ F' k' i.castSucc = tateSeries.castSuccAlgHom (F' i) := by
  simp [explicitInverse]

@[simp]
theorem explicitInverse_last (ϖ : A) {N' : ℕ} (F' : Fin N' → tateSeries N' A) (k' : ℕ) :
    explicitInverse A ϖ F' k' (Fin.last N') =
      tateSeries.X (N' + 1) A (Fin.last N') *
        tateSeries.castSuccAlgHom (tateSeries.jacobian F') -
        algebraMap A (tateSeries (N' + 1) A) (ϖ ^ k') := by
  simp [explicitInverse]

/-- If `ϖ ∈ Aplus` and every equation of `F'` has coefficients in `Aplus`, then every equation of
`explicitInverse A ϖ F' k'` has coefficients in `Aplus`. -/
theorem explicitInverse_mem_tateSeriesPlus {Aplus : Subring A} {ϖ : A} (hϖ : ϖ ∈ Aplus)
    {N' : ℕ} {F' : Fin N' → tateSeries N' A}
    (hF' : ∀ i, F' i ∈ tateSeriesPlus N' A Aplus) (k' : ℕ) (j : Fin (N' + 1)) :
    explicitInverse A ϖ F' k' j ∈ tateSeriesPlus (N' + 1) A Aplus := by
  refine Fin.lastCases ?_ (fun i ↦ ?_) j
  · rw [explicitInverse_last]
    exact sub_mem (mul_mem (tateSeries.X_mem_tateSeriesPlus Aplus _)
      (tateSeries.renameAlgHom_mem_tateSeriesPlus Fin.castSuccEmb
        (tateSeries.jacobian_mem_tateSeriesPlus hF')))
      (algebraMap_mem_tateSeriesPlus_iff.mpr (pow_mem hϖ k'))
  · rw [explicitInverse_castSucc]
    exact tateSeries.renameAlgHom_mem_tateSeriesPlus Fin.castSuccEmb (hF' i)

theorem pderiv_explicitInverse_castSucc_castSucc (ϖ : A) {N' : ℕ}
    (F' : Fin N' → tateSeries N' A) (k' : ℕ) (i j : Fin N') :
    tateSeries.pderiv j.castSucc (explicitInverse A ϖ F' k' i.castSucc) =
      tateSeries.castSuccAlgHom (tateSeries.pderiv j (F' i)) := by
  rw [explicitInverse_castSucc]
  exact tateSeries.pderiv_renameAlgHom_apply Fin.castSuccEmb j (F' i)

theorem pderiv_explicitInverse_castSucc_last (ϖ : A) {N' : ℕ}
    (F' : Fin N' → tateSeries N' A) (k' : ℕ) (i : Fin N') :
    tateSeries.pderiv (Fin.last N') (explicitInverse A ϖ F' k' i.castSucc) = 0 := by
  rw [explicitInverse_castSucc, tateSeries.pderiv_castSuccAlgHom_last]

theorem pderiv_explicitInverse_last_last (ϖ : A) {N' : ℕ}
    (F' : Fin N' → tateSeries N' A) (k' : ℕ) :
    tateSeries.pderiv (Fin.last N') (explicitInverse A ϖ F' k' (Fin.last N')) =
      tateSeries.castSuccAlgHom (tateSeries.jacobian F') := by
  rw [explicitInverse_last, map_sub, tateSeries.pderiv_mul, tateSeries.pderiv_X_self,
    tateSeries.pderiv_castSuccAlgHom_last, tateSeries.pderiv_algebraMap]
  simp

/-- **The formal Jacobian determinant of `explicitInverse A ϖ F' k'` is the square of the embedded
Jacobian determinant of `F'`.** -/
@[simp]
theorem jacobian_explicitInverse (ϖ : A) {N' : ℕ} (F' : Fin N' → tateSeries N' A) (k' : ℕ) :
    tateSeries.jacobian (explicitInverse A ϖ F' k') =
      tateSeries.castSuccAlgHom (tateSeries.jacobian F') ^ 2 := by
  rw [tateSeries.jacobian_def,
    Matrix.det_succ_column (tateSeries.jacobianMatrix (explicitInverse A ϖ F' k')) (Fin.last N'),
    Fin.sum_univ_castSucc]
  have htop : ∑ i : Fin N',
      (-1 : tateSeries (N' + 1) A) ^ ((i.castSucc : ℕ) + (Fin.last N' : ℕ)) *
        tateSeries.jacobianMatrix (explicitInverse A ϖ F' k') i.castSucc (Fin.last N') *
        ((tateSeries.jacobianMatrix (explicitInverse A ϖ F' k')).submatrix
          i.castSucc.succAbove (Fin.last N').succAbove).det = 0 :=
    Finset.sum_eq_zero fun i _ ↦ by simp [tateSeries.jacobianMatrix_apply]
  rw [htop, zero_add, Fin.val_last, ← two_mul, pow_mul, neg_one_sq, one_pow, one_mul,
    tateSeries.jacobianMatrix_apply, pderiv_explicitInverse_last_last, Fin.succAbove_last]
  have hsub : (tateSeries.jacobianMatrix (explicitInverse A ϖ F' k')).submatrix
      Fin.castSucc Fin.castSucc =
      tateSeries.castSuccAlgHom.toRingHom.mapMatrix (tateSeries.jacobianMatrix F') :=
    Matrix.ext fun i j ↦ by
      simp only [Matrix.submatrix_apply, RingHom.mapMatrix_apply, Matrix.map_apply,
        tateSeries.jacobianMatrix_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        pderiv_explicitInverse_castSucc_castSucc]
  rw [hsub, ← RingHom.map_det, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, ← tateSeries.jacobian_def,
    sq]

end ExplicitInverse

namespace StandardEtalePresentation

section OfExplicitInverse

variable {A : Type*} [CommRing A] [UniformSpace A] [IsUniformAddGroup A] [IsTopologicalRing A]
  [IsTateRing A] [CompleteSpace A] [T2Space A]

/-- **Canonical standard étale presentation of the quotient by `explicitInverse A ϖ F' k'`.**
For any `A⁺`-integral system `F' : Fin N' → tateSeries N' A` and `k' : ℕ`, the equation
`T_{N'} · J(F') = ϖ ^ k'` forces `J(F')` to divide the unit `ϖ ^ k'` in the quotient ring, so
`J(explicitInverse) = J(F') ^ 2` maps to a unit `u` with `ϖ ^ (2 * k') · u⁻¹ = T_{N'} ^ 2 ∈ plus`.
-/
noncomputable def ofExplicitInverse (Aplus : Pair A) {ϖ : A} (hϖ : IsPseudoUniformizer ϖ)
    {N' : ℕ} (F' : Fin N' → tateSeries N' A) (hF' : ∀ i, F' i ∈ tateSeriesPlus N' A Aplus.plus)
    (k' : ℕ) :
    StandardEtalePresentation Aplus ϖ
      ((tateSeriesPair (N' + 1) A Aplus).quotient
        (Ideal.span (Set.range (explicitInverse A ϖ F' k'))).closure) := by
  let F := explicitInverse A ϖ F' k'
  let I := (Ideal.span (Set.range F)).closure
  have hϖ_mem : ϖ ∈ Aplus.plus :=
    Aplus.isRingOfIntegralElements.mem_of_isTopologicallyNilpotent hϖ.isTopologicallyNilpotent
  refine ofQuotient Aplus hϖ F (explicitInverse_mem_tateSeriesPlus hϖ_mem hF' k') (2 * k') ?_
  let s : tateSeries (N' + 1) A ⧸ I :=
    Ideal.Quotient.mk I (tateSeries.X (N' + 1) A (Fin.last N'))
  let jbar : tateSeries (N' + 1) A ⧸ I :=
    Ideal.Quotient.mk I (tateSeries.castSuccAlgHom (tateSeries.jacobian F'))
  have hsj : s * jbar = algebraMap A (tateSeries (N' + 1) A ⧸ I) (ϖ ^ k') := by
    have h0 : Ideal.Quotient.mk I (F (Fin.last N')) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (subset_closure (Ideal.subset_span ⟨Fin.last N', rfl⟩))
    dsimp only [F] at h0
    rw [explicitInverse_last, map_sub, map_mul, Ideal.Quotient.mk_algebraMap] at h0
    exact sub_eq_zero.mp h0
  obtain ⟨u₀, hu₀⟩ := isUnit_of_mul_isUnit_right
    (hsj ▸ (hϖ.isUnit.pow k').map (algebraMap A (tateSeries (N' + 1) A ⧸ I)))
  refine ⟨u₀ ^ 2, by rw [Units.val_pow_eq_pow_val, hu₀, ← map_pow, ← jacobian_explicitInverse], ?_⟩
  have hinv : algebraMap A (tateSeries (N' + 1) A ⧸ I) (ϖ ^ (2 * k')) * ↑(u₀ ^ 2)⁻¹ = s ^ 2 := by
    apply (u₀ ^ 2).mul_left_inj.mp
    rw [mul_assoc, Units.inv_mul, mul_one, mul_comm 2 k', pow_mul, map_pow, ← hsj,
      Units.val_pow_eq_pow_val, hu₀]
    ring
  rw [hinv]
  refine ((tateSeriesPair (N' + 1) A Aplus).quotient I).plus.pow_mem ?_ 2
  dsimp only [s]
  rw [← Pair.Hom.toRingHom_quotientHom (tateSeriesPair (N' + 1) A Aplus) I]
  exact (Pair.quotientHom (tateSeriesPair (N' + 1) A Aplus) I).map_mem_plus _
    (by simpa only [tateSeriesPair_plus] using
      tateSeries.X_mem_tateSeriesPlus Aplus.plus (Fin.last N'))

@[simp]
theorem ofExplicitInverse_N (Aplus : Pair A) {ϖ : A} (hϖ : IsPseudoUniformizer ϖ)
    {N' : ℕ} (F' : Fin N' → tateSeries N' A) (hF' : ∀ i, F' i ∈ tateSeriesPlus N' A Aplus.plus)
    (k' : ℕ) :
    (ofExplicitInverse Aplus hϖ F' hF' k').N = N' + 1 := by
  simp [ofExplicitInverse]

@[simp]
theorem ofExplicitInverse_k (Aplus : Pair A) {ϖ : A} (hϖ : IsPseudoUniformizer ϖ)
    {N' : ℕ} (F' : Fin N' → tateSeries N' A) (hF' : ∀ i, F' i ∈ tateSeriesPlus N' A Aplus.plus)
    (k' : ℕ) :
    (ofExplicitInverse Aplus hϖ F' hF' k').k = 2 * k' := by
  simp [ofExplicitInverse]

/-- The defining equation family of `ofExplicitInverse` is `explicitInverse A ϖ F' k'`
(transported along `ofExplicitInverse_N`). -/
@[simp]
theorem ofExplicitInverse_F (Aplus : Pair A) {ϖ : A} (hϖ : IsPseudoUniformizer ϖ)
    {N' : ℕ} (F' : Fin N' → tateSeries N' A) (hF' : ∀ i, F' i ∈ tateSeriesPlus N' A Aplus.plus)
    (k' : ℕ) :
    cast (congrArg (fun n ↦ Fin n → tateSeries n A) (ofExplicitInverse_N Aplus hϖ F' hF' k'))
      (ofExplicitInverse Aplus hϖ F' hF' k').F = explicitInverse A ϖ F' k' := by
  simp [ofExplicitInverse]

/-- The presenting map of `ofExplicitInverse` evaluates on a series as `Ideal.Quotient.mk`
(transported along `ofExplicitInverse_N`). -/
@[simp]
theorem ofExplicitInverse_π_apply (Aplus : Pair A) {ϖ : A} (hϖ : IsPseudoUniformizer ϖ)
    {N' : ℕ} (F' : Fin N' → tateSeries N' A) (hF' : ∀ i, F' i ∈ tateSeriesPlus N' A Aplus.plus)
    (k' : ℕ) (f : tateSeries (N' + 1) A) :
    (ofExplicitInverse Aplus hϖ F' hF' k').π
      (cast (congrArg (tateSeries · A) (ofExplicitInverse_N Aplus hϖ F' hF' k').symm) f) =
      Ideal.Quotient.mk (Ideal.span (Set.range (explicitInverse A ϖ F' k'))).closure f := by
  unfold ofExplicitInverse
  exact ofQuotient_π_apply _ _ _ _ _ _ f

end OfExplicitInverse

section WithInverse

variable {A : Type*} [CommRing A] [UniformSpace A] [IsUniformAddGroup A] [IsTopologicalRing A]
  [IsTateRing A] [CompleteSpace A] [T2Space A]
  {Aplus : Pair A} {ϖ : A}
  {C : Type*} [CommRing C] [TopologicalSpace C] [IsTopologicalRing C] [IsHuberRing C]
  [Algebra A C] {Cplus : Pair C}

/-- Chosen `ϖ ^ P.k`-scaled inverse `ϖ ^ P.k · P.π(P.jacobian)⁻¹ ∈ Cplus.plus` associated to a
standard étale presentation `P`. -/
private noncomputable def scaledJacobianInv
    (P : StandardEtalePresentation Aplus ϖ Cplus) : C :=
  algebraMap A C (ϖ ^ P.k) * ↑P.exists_unit_π_jacobian.choose⁻¹

private theorem scaledJacobianInv_mem_plus
    (P : StandardEtalePresentation Aplus ϖ Cplus) :
    P.scaledJacobianInv ∈ Cplus.plus :=
  P.exists_unit_π_jacobian.choose_spec.2

private theorem mul_scaledJacobianInv (P : StandardEtalePresentation Aplus ϖ Cplus) :
    (P.exists_unit_π_jacobian.choose : C) * P.scaledJacobianInv = algebraMap A C (ϖ ^ P.k) := by
  rw [scaledJacobianInv, mul_left_comm, Units.mul_inv, mul_one]

private noncomputable def withInverseTuple
    (P : StandardEtalePresentation Aplus ϖ Cplus) : Fin (P.N + 1) → C :=
  Fin.snoc (fun i ↦ P.π (tateSeries.X P.N A i)) P.scaledJacobianInv

private theorem withInverseTuple_mem_plus
    (P : StandardEtalePresentation Aplus ϖ Cplus) (j : Fin (P.N + 1)) :
    P.withInverseTuple j ∈ Cplus.plus := by
  refine Fin.lastCases (by simpa [withInverseTuple] using P.scaledJacobianInv_mem_plus)
    (fun i ↦ ?_) j
  dsimp only [withInverseTuple]
  rw [Fin.snoc_castSucc, ← AlgHom.coe_toRingHom, ← P.toPairHom_toRingHom]
  exact P.toPairHom.map_mem_plus _
    (by rw [tateSeriesPair_plus]; exact tateSeries.X_mem_tateSeriesPlus Aplus.plus i)

private theorem isWeightBounded_withInverseTuple (P : StandardEtalePresentation Aplus ϖ Cplus) :
    IsWeightBounded (algebraMap A C) (fun _ : Fin (P.N + 1) ↦ ({1} : Set A)) P.withInverseTuple :=
  (isWeightBounded_one_weight_iff_forall_isPowerBounded _ _).mpr fun j ↦
    Cplus.isRingOfIntegralElements.isPowerBounded_of_mem (P.withInverseTuple_mem_plus j)

/-- **Extended `A`-algebra quotient homomorphism `tateSeries (P.N + 1) A →ₐ[A] C`** extending `P.π`
along `tateSeries.castSuccAlgHom` and sending `T_{P.N}` to `ϖ ^ P.k · P.π(P.jacobian)⁻¹ ∈ C⁺`. -/
noncomputable def withInverseHom (P : StandardEtalePresentation Aplus ϖ Cplus) :
    tateSeries (P.N + 1) A →ₐ[A] C := by
  let _ : UniformSpace C := IsTopologicalAddGroup.rightUniformSpace C
  have : IsUniformAddGroup C := isUniformAddGroup_of_addCommGroup
  have : T2Space C := P.t2Space
  have : CompleteSpace C := P.completeSpace
  let ev := weightedEvalHom isWeightFamily_one_weight P.continuous_algebraMap.continuousAt
    P.isWeightBounded_withInverseTuple
  exact
    { toFun := ev
      map_one' := ev.map_one
      map_mul' := ev.map_mul
      map_zero' := ev.map_zero
      map_add' := ev.map_add
      commutes' a := by rw [algebraMap_weightedRestrictedSubring, weightedEvalHom_weightedC] }

/-- `P.withInverseHom` is continuous. -/
theorem continuous_withInverseHom (P : StandardEtalePresentation Aplus ϖ Cplus) :
    Continuous P.withInverseHom := by
  let _ : UniformSpace C := IsTopologicalAddGroup.rightUniformSpace C
  have : IsUniformAddGroup C := isUniformAddGroup_of_addCommGroup
  have : T2Space C := P.t2Space
  have : CompleteSpace C := P.completeSpace
  exact continuous_weightedEvalHom isWeightFamily_one_weight P.continuous_algebraMap.continuousAt
    P.isWeightBounded_withInverseTuple

private theorem withInverseHom_apply
    (P : StandardEtalePresentation Aplus ϖ Cplus) (f : tateSeries (P.N + 1) A) :
    P.withInverseHom f =
      weightedEval (algebraMap A C) P.withInverseTuple
        (f : MvPowerSeries (Fin (P.N + 1)) A) := by
  let _ : UniformSpace C := IsTopologicalAddGroup.rightUniformSpace C
  have : IsUniformAddGroup C := isUniformAddGroup_of_addCommGroup
  have : T2Space C := P.t2Space
  have : CompleteSpace C := P.completeSpace
  exact coe_weightedEvalHom isWeightFamily_one_weight P.continuous_algebraMap.continuousAt
    P.isWeightBounded_withInverseTuple f

private theorem withInverseHom_X_apply
    (P : StandardEtalePresentation Aplus ϖ Cplus) (j : Fin (P.N + 1)) :
    P.withInverseHom (tateSeries.X (P.N + 1) A j) = P.withInverseTuple j := by
  rw [P.withInverseHom_apply, tateSeries.coe_X, weightedEval_X]

@[simp]
theorem withInverseHom_castSuccAlgHom
    (P : StandardEtalePresentation Aplus ϖ Cplus) (f : tateSeries P.N A) :
    P.withInverseHom (tateSeries.castSuccAlgHom f) = P.π f := by
  have : T2Space C := P.t2Space
  have hext : P.withInverseHom.toRingHom.comp tateSeries.castSuccAlgHom.toRingHom =
      P.π.toRingHom := by
    refine weightedRestrictedSubring_ringHom_ext_of_continuous isWeightFamily_one_weight
      (P.continuous_withInverseHom.comp (tateSeries.continuous_renameAlgHom Fin.castSuccEmb))
      P.isQuotientMap_π.continuous (fun a ↦ ?_) (fun i ↦ ?_)
    · simp [← algebraMap_weightedRestrictedSubring]
    · simp [← tateSeries.X_eq_weightedX, withInverseHom_X_apply, withInverseTuple]
  exact congrArg (fun φ : tateSeries P.N A →+* C ↦ φ f) hext

/-- On an original coordinate `i : Fin P.N`, `P.withInverseHom` agrees with `P.π`. -/
@[simp]
theorem withInverseHom_X_castSucc (P : StandardEtalePresentation Aplus ϖ Cplus) (i : Fin P.N) :
    P.withInverseHom (tateSeries.X (P.N + 1) A i.castSucc) = P.π (tateSeries.X P.N A i) := by
  rw [withInverseHom_X_apply, withInverseTuple, Fin.snoc_castSucc]

/-- On the newly adjoined variable `T_{P.N}`, `P.withInverseHom` satisfies the explicit inverse
relation `P.withInverseHom T_{P.N} * P.π P.jacobian = algebraMap A C (ϖ ^ P.k)`. -/
theorem withInverseHom_last_mul_jacobian (P : StandardEtalePresentation Aplus ϖ Cplus) :
    P.withInverseHom (tateSeries.X (P.N + 1) A (Fin.last P.N)) * P.π P.jacobian =
      algebraMap A C (ϖ ^ P.k) := by
  rw [withInverseHom_X_apply, withInverseTuple, Fin.snoc_last,
    ← P.exists_unit_π_jacobian.choose_spec.1, mul_comm, mul_scaledJacobianInv]

/-- On the newly adjoined variable `T_{P.N}`, `P.withInverseHom` evaluates to the `ϖ ^ P.k`-scaled
inverse of any unit `u : Cˣ` representing `P.π P.jacobian`. -/
theorem withInverseHom_last (P : StandardEtalePresentation Aplus ϖ Cplus)
    {u : Cˣ} (hu : (u : C) = P.π P.jacobian) :
    P.withInverseHom (tateSeries.X (P.N + 1) A (Fin.last P.N)) =
      algebraMap A C (ϖ ^ P.k) * ↑u⁻¹ := by
  apply u.mul_left_inj.mp
  calc
    P.withInverseHom (tateSeries.X (P.N + 1) A (Fin.last P.N)) * (u : C)
      = P.withInverseHom (tateSeries.X (P.N + 1) A (Fin.last P.N)) * P.π P.jacobian := by rw [hu]
    _ = algebraMap A C (ϖ ^ P.k) := P.withInverseHom_last_mul_jacobian
    _ = algebraMap A C (ϖ ^ P.k) * ↑u⁻¹ * (u : C) := by
        rw [mul_assoc, Units.inv_mul, mul_one]

/-- The extended homomorphism `P.withInverseHom` is a topological quotient map. -/
theorem isQuotientMap_withInverseHom (P : StandardEtalePresentation Aplus ϖ Cplus) :
    Topology.IsQuotientMap P.withInverseHom := by
  have hsurj : Function.Surjective P.withInverseHom := fun c ↦ by
    obtain ⟨g, rfl⟩ := P.surjective_π c
    exact ⟨tateSeries.castSuccAlgHom g, P.withInverseHom_castSuccAlgHom g⟩
  have hopen : IsOpenMap P.withInverseHom := by
    refine (IsTopologicalAddGroup.isOpenMap_iff_nhds_zero
      (f := P.withInverseHom.toRingHom.toAddMonoidHom)).mpr ?_
    have hπ_le : 𝓝 (0 : C) ≤ Filter.map P.π (𝓝 (0 : tateSeries P.N A)) :=
      (IsTopologicalAddGroup.isOpenMap_iff_nhds_zero
        (f := P.π.toRingHom.toAddMonoidHom)).mp P.isOpenQuotientMap_π.isOpenMap
    have hcast_le : Filter.map tateSeries.castSuccAlgHom (𝓝 (0 : tateSeries P.N A)) ≤
        𝓝 (0 : tateSeries (P.N + 1) A) := by
      have ht := (tateSeries.continuous_renameAlgHom
        (A := A) Fin.castSuccEmb).tendsto (0 : tateSeries P.N A)
      rwa [Filter.Tendsto, map_zero] at ht
    have hcomp : (P.π : tateSeries P.N A → C) =
        P.withInverseHom ∘ tateSeries.castSuccAlgHom :=
      funext fun g ↦ (P.withInverseHom_castSuccAlgHom g).symm
    calc
      𝓝 (0 : C) ≤ Filter.map P.π (𝓝 (0 : tateSeries P.N A)) := hπ_le
      _ = Filter.map P.withInverseHom
            (Filter.map tateSeries.castSuccAlgHom (𝓝 (0 : tateSeries P.N A))) := by
            rw [hcomp, ← Filter.map_map]
      _ ≤ Filter.map P.withInverseHom (𝓝 (0 : tateSeries (P.N + 1) A)) :=
            Filter.map_mono hcast_le
  exact IsOpenQuotientMap.isQuotientMap ⟨hsurj, P.continuous_withInverseHom, hopen⟩

private theorem ker_withInverseHom_le (P : StandardEtalePresentation Aplus ϖ Cplus) :
    RingHom.ker P.withInverseHom ≤
      (Ideal.span (Set.range (explicitInverse A ϖ P.F P.k))).closure := by
  have : T2Space C := P.t2Space
  let F := explicitInverse A ϖ P.F P.k
  let K' := (Ideal.span (Set.range F)).closure
  let u : Cˣ := P.exists_unit_π_jacobian.choose
  have hu_eq : (u : C) = P.π P.jacobian := P.exists_unit_π_jacobian.choose_spec.1
  have : IsClosed (K' : Set (tateSeries (P.N + 1) A)) := by
    rw [Ideal.coe_closure]; exact isClosed_closure
  -- Descend `castSuccAlgHom` through `P.ideal` to a continuous map `ψ : C →+* _ ⧸ K'`.
  let φ₀ : tateSeries P.N A →+* tateSeries (P.N + 1) A ⧸ K' :=
    (Ideal.Quotient.mk K').comp tateSeries.castSuccAlgHom.toRingHom
  have hφ₀_cont : Continuous φ₀ :=
    continuous_quotient_mk'.comp (tateSeries.continuous_renameAlgHom Fin.castSuccEmb)
  have hI_le : P.ideal ≤ RingHom.ker φ₀ := by
    have hclosed : IsClosed (RingHom.ker φ₀ : Set (tateSeries P.N A)) :=
      isClosed_singleton.preimage hφ₀_cont
    rw [← SetLike.coe_subset_coe, P.ideal_def, Ideal.coe_closure]
    refine hclosed.closure_subset_iff.mpr (SetLike.coe_subset_coe.mpr (Ideal.span_le.mpr ?_))
    rintro _ ⟨i, rfl⟩
    simp only [SetLike.mem_coe, RingHom.mem_ker, φ₀, RingHom.comp_apply, AlgHom.toRingHom_eq_coe,
      RingHom.coe_coe, ← explicitInverse_castSucc ϖ P.F P.k i, Ideal.Quotient.eq_zero_iff_mem]
    exact subset_closure (Ideal.subset_span ⟨i.castSucc, rfl⟩)
  let ψ : C →+* tateSeries (P.N + 1) A ⧸ K' :=
    (Ideal.Quotient.lift P.ideal φ₀ fun g hg ↦ hI_le hg).comp P.targetToQuotient.toRingHom
  have hψ_cont : Continuous ψ :=
    (Ideal.Quotient.continuous_lift P.ideal hφ₀_cont fun g hg ↦ hI_le hg).comp
      P.targetToQuotient.continuous_toRingHom
  have hψ_π (g : tateSeries P.N A) :
      ψ (P.π g) = Ideal.Quotient.mk K' (tateSeries.castSuccAlgHom g) := by simp [ψ, φ₀]
  -- Check `ψ ∘ P.withInverseHom = mk K'` on `A` and variables, cancelling `uQ` on `Fin.last P.N`.
  have hcomp : ψ.comp P.withInverseHom.toRingHom = Ideal.Quotient.mk K' := by
    refine weightedRestrictedSubring_ringHom_ext_of_continuous isWeightFamily_one_weight
      (hψ_cont.comp P.continuous_withInverseHom) continuous_quotient_mk'
      (fun a ↦ ?_) (fun j ↦ ?_)
    · rw [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        ← algebraMap_weightedRestrictedSubring, AlgHom.commutes, ← P.π.commutes, hψ_π,
        AlgHom.commutes]
    · rw [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, ← tateSeries.X_eq_weightedX]
      refine Fin.lastCases ?_ (fun i ↦ ?_) j
      · let uQ : (tateSeries (P.N + 1) A ⧸ K')ˣ := Units.map (ψ : C →* _) u
        have huQ : (uQ : tateSeries (P.N + 1) A ⧸ K') =
            Ideal.Quotient.mk K' (tateSeries.castSuccAlgHom P.jacobian) := by
          rw [Units.coe_map, MonoidHom.coe_ofClass, hu_eq, hψ_π]
        have hlast : Ideal.Quotient.mk K' (tateSeries.X (P.N + 1) A (Fin.last P.N)) *
            Ideal.Quotient.mk K' (tateSeries.castSuccAlgHom P.jacobian) =
            Ideal.Quotient.mk K' (algebraMap A (tateSeries (P.N + 1) A) (ϖ ^ P.k)) := by
          have h0 : Ideal.Quotient.mk K' (F (Fin.last P.N)) = 0 :=
            Ideal.Quotient.eq_zero_iff_mem.mpr
              (subset_closure (Ideal.subset_span ⟨Fin.last P.N, rfl⟩))
          dsimp only [F] at h0
          rw [explicitInverse_last, map_sub, map_mul, ← P.jacobian_def] at h0
          exact sub_eq_zero.mp h0
        apply uQ.mul_left_inj.mp
        rw [Units.coe_map, MonoidHom.coe_ofClass, hu_eq, ← map_mul,
          P.withInverseHom_last_mul_jacobian, ← P.π.commutes, hψ_π, AlgHom.commutes, ← hlast, ← huQ,
          Units.coe_map, MonoidHom.coe_ofClass, hu_eq, hψ_π]
      · have hi : i.castSucc = Fin.castSuccEmb i := rfl
        rw [hi, ← tateSeries.renameAlgHom_X Fin.castSuccEmb, withInverseHom_castSuccAlgHom, hψ_π]
  intro f hf
  exact Ideal.Quotient.eq_zero_iff_mem.mp
    (by rw [← hcomp]; simp [RingHom.comp_apply, RingHom.mem_ker.mp hf])

private theorem le_ker_withInverseHom (P : StandardEtalePresentation Aplus ϖ Cplus) :
    (Ideal.span (Set.range (explicitInverse A ϖ P.F P.k))).closure ≤
      RingHom.ker P.withInverseHom := by
  have : T2Space C := P.t2Space
  have hclosed : IsClosed (RingHom.ker P.withInverseHom : Set (tateSeries (P.N + 1) A)) :=
    isClosed_singleton.preimage P.continuous_withInverseHom
  refine hclosed.closure_subset_iff.mpr (Ideal.span_le.mpr ?_)
  rintro _ ⟨j, rfl⟩
  rw [SetLike.mem_coe, RingHom.mem_ker]
  refine Fin.lastCases ?_ (fun i ↦ by simp [P.π_F]) j
  simp only [explicitInverse_last, map_sub, map_mul, AlgHom.commutes, withInverseHom_castSuccAlgHom]
  rw [← P.jacobian_def, P.withInverseHom_last_mul_jacobian, sub_self]

/-- The kernel of `P.withInverseHom` is the closure of the ideal generated by the enlarged system
`explicitInverse A ϖ P.F P.k`. -/
theorem ker_withInverseHom (P : StandardEtalePresentation Aplus ϖ Cplus) :
    RingHom.ker P.withInverseHom =
      (Ideal.span (Set.range (explicitInverse A ϖ P.F P.k))).closure :=
  le_antisymm P.ker_withInverseHom_le P.le_ker_withInverseHom

/-- **Upgrade a `StandardEtalePresentation` by adjoining an explicit scaled Jacobian inverse.**
Given `P : StandardEtalePresentation Aplus ϖ Cplus`, this produces a new presentation of the *same*
Huber pair `Cplus` in `P.N + 1` variables with equations `explicitInverse A ϖ P.F P.k`, projection
`P.withInverseHom`, and scale exponent `2 * P.k`. -/
noncomputable def withInverse (P : StandardEtalePresentation Aplus ϖ Cplus) :
    StandardEtalePresentation Aplus ϖ Cplus where
  isPseudoUniformizer := P.isPseudoUniformizer
  N := P.N + 1
  F := explicitInverse A ϖ P.F P.k
  F_mem_plus := explicitInverse_mem_tateSeriesPlus P.mem_plus_pseudoUniformizer P.F_mem_plus P.k
  k := 2 * P.k
  π := P.withInverseHom
  isQuotientMap_π := P.isQuotientMap_withInverseHom
  ker_π := P.ker_withInverseHom
  mem_plus_iff c := by
    constructor
    · intro hc
      let R₁ := (tateSeriesPlus P.N A Aplus.plus).map P.π.toRingHom
      let R₂ := (tateSeriesPlus (P.N + 1) A Aplus.plus).map P.withInverseHom.toRingHom
      have hR : R₁ ≤ R₂ := by
        rintro _ ⟨g, hg, rfl⟩
        exact ⟨tateSeries.castSuccAlgHom g,
          tateSeries.renameAlgHom_mem_tateSeriesPlus Fin.castSuccEmb hg,
          P.withInverseHom_castSuccAlgHom g⟩
      let _ : Algebra R₁ R₂ := (Subring.inclusion hR).toAlgebra
      have : IsScalarTower R₁ R₂ C := .of_algebraMap_eq fun _ ↦ rfl
      exact IsIntegral.tower_top (R := R₁) (A := R₂) ((P.mem_plus_iff c).mp hc)
    · let _ : UniformSpace C := IsTopologicalAddGroup.rightUniformSpace C
      have : IsUniformAddGroup C := isUniformAddGroup_of_addCommGroup
      have : T2Space C := P.t2Space
      have : CompleteSpace C := P.completeSpace
      have := Cplus.isRingOfIntegralElements.isIntegrallyClosedIn
      have hb : IsWeightBounded P.toBasePairHom.toRingHom
          (fun _ : Fin (P.N + 1) ↦ ({1} : Set A)) P.withInverseTuple :=
        P.toBasePairHom_toRingHom.symm ▸ P.isWeightBounded_withInverseTuple
      have hmap_le : (tateSeriesPlus (P.N + 1) A Aplus.plus).map P.withInverseHom.toRingHom
          ≤ Cplus.plus := by
        rintro _ ⟨f, hf, rfl⟩
        have hval : P.withInverseHom.toRingHom f =
            weightedEvalHom isWeightFamily_one_weight
              P.toBasePairHom.continuous_toRingHom.continuousAt hb f := by
          rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, P.withInverseHom_apply,
            coe_weightedEvalHom, P.toBasePairHom_toRingHom]
        rw [hval]
        exact weightedEvalHom_mem_plus_of_mem_tateSeriesPlus Cplus P.toBasePairHom
          P.withInverseTuple_mem_plus hb hf
      exact fun hc ↦ Subring.integralClosure_subring_le_iff.mpr hmap_le
        ((mem_integralClosure_iff _ _).mpr hc)
  exists_unit_jacobian := by
    let u : Cˣ := P.exists_unit_π_jacobian.choose
    have hu_eq : (u : C) = P.π P.jacobian := P.exists_unit_π_jacobian.choose_spec.1
    refine ⟨u ^ 2, ?_, ?_⟩
    · rw [Units.val_pow_eq_pow_val, hu_eq, jacobian_explicitInverse, map_pow,
        withInverseHom_castSuccAlgHom, P.jacobian_def]
    · have hu_inv_sq : (↑(u ^ 2)⁻¹ : C) = (↑u⁻¹ : C) ^ 2 := by
        apply (u ^ 2).mul_right_inj.mp
        rw [Units.mul_inv, Units.val_pow_eq_pow_val, ← mul_pow, Units.mul_inv, one_pow]
      have hsq : algebraMap A C (ϖ ^ (2 * P.k)) * ↑(u ^ 2)⁻¹ = P.scaledJacobianInv ^ 2 := by
        rw [scaledJacobianInv, hu_inv_sq, mul_comm 2 P.k, pow_mul, map_pow]; ring
      rw [hsq]
      exact Cplus.plus.pow_mem P.scaledJacobianInv_mem_plus 2

@[simp]
theorem withInverse_N (P : StandardEtalePresentation Aplus ϖ Cplus) :
    P.withInverse.N = P.N + 1 := (rfl)

@[simp]
theorem withInverse_k (P : StandardEtalePresentation Aplus ϖ Cplus) :
    P.withInverse.k = 2 * P.k := (rfl)

/-- The defining equation family of `P.withInverse` is `explicitInverse A ϖ P.F P.k`
(transported along `P.withInverse_N`). -/
@[simp]
theorem withInverse_F (P : StandardEtalePresentation Aplus ϖ Cplus) :
    cast (congrArg (fun n ↦ Fin n → tateSeries n A) P.withInverse_N) P.withInverse.F =
      explicitInverse A ϖ P.F P.k := (rfl)

/-- The presenting map of `P.withInverse` evaluates on a series as `P.withInverseHom`
(transported along `P.withInverse_N`). -/
@[simp]
theorem withInverse_π_apply (P : StandardEtalePresentation Aplus ϖ Cplus)
    (f : tateSeries (P.N + 1) A) :
    P.withInverse.π (cast (congrArg (tateSeries · A) P.withInverse_N.symm) f) =
      P.withInverseHom f := (rfl)

omit [IsUniformAddGroup A] [CompleteSpace A] [T2Space A] in
private theorem tateSeries_X_cast {n m : ℕ} (h : n = m) (j : Fin m) :
    tateSeries.X n A (Fin.cast h.symm j) =
      cast (congrArg (tateSeries · A) h.symm) (tateSeries.X m A j) := by
  subst h; rfl

/-- On an original coordinate `i : Fin P.N`, `P.withInverse.π` agrees with `P.π`. -/
theorem withInverse_π_X_castSucc (P : StandardEtalePresentation Aplus ϖ Cplus) (i : Fin P.N) :
    P.withInverse.π (tateSeries.X P.withInverse.N A (Fin.cast P.withInverse_N.symm i.castSucc)) =
      P.π (tateSeries.X P.N A i) := by
  rw [tateSeries_X_cast P.withInverse_N i.castSucc, withInverse_π_apply,
    withInverseHom_X_castSucc]

/-- On the newly adjoined coordinate `T_{P.N}`, `P.withInverse.π` evaluates to the
`ϖ ^ P.k`-scaled inverse of any unit `u : Cˣ` representing `P.π P.jacobian`. -/
theorem withInverse_π_X_last (P : StandardEtalePresentation Aplus ϖ Cplus)
    {u : Cˣ} (hu : (u : C) = P.π P.jacobian) :
    P.withInverse.π
        (tateSeries.X P.withInverse.N A (Fin.cast P.withInverse_N.symm (Fin.last P.N))) =
      algebraMap A C (ϖ ^ P.k) * ↑u⁻¹ := by
  rw [tateSeries_X_cast P.withInverse_N (Fin.last P.N), withInverse_π_apply]
  exact P.withInverseHom_last hu

end WithInverse

end StandardEtalePresentation

end TauCeti.Huber

end
