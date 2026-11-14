/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.StandardEtale.Basic
public import TauCeti.RingTheory.Huber.WeightedEval.Hom

import Mathlib.Data.Fin.SuccPred
import Mathlib.Topology.Algebra.Group.Neighborhood
import TauCeti.RingTheory.Huber.Padic.Field
import TauCeti.RingTheory.Huber.WeightedEval.Continuous
import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.Complete
import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.FirstCountable
import TauCeti.Topology.Algebra.IsUniformGroup.Quotient

/-!
# Explicit Jacobian inverses for standard étale presentations

In a standard étale presentation $C = A\langle T_1, \dots, T_N\rangle /
\overline{(F_1, \dots, F_N)}$ over a complete Hausdorff Tate pair $(A, A^+)$ with
pseudo-uniformiser $\varpi$, the formal Jacobian determinant $J = \det(\partial F_i / \partial T_j)$
is only required to become invertible *after* projection to $C$, with
$\varpi^k \cdot \pi(J)^{-1} \in C^+$. When lifting or perturbing standard étale presentations across
topological quotients, it is convenient to promote that implicit invertibility witness into an
explicit coordinate of the presentation itself.

Adjoining one restricted power-series variable $T_{N+1}$ and the extra equation
$$F'_{N+1}(T_1, \dots, T_{N+1}) = T_{N+1} \cdot J(T_1, \dots, T_N) - \varpi^k$$
achieves this without changing the presented Huber pair $(C, C^+)$: sending $T_{N+1}$ to
$\varpi^k \cdot \pi(J)^{-1} \in C^+$ extends $\pi$ to an open quotient homomorphism
$A\langle T_1, \dots, T_{N+1}\rangle \to C$ whose kernel is the closure of the enlarged system.
Because the first $N$ equations do not involve $T_{N+1}$, the enlarged $(N+1) \times (N+1)$ formal
Jacobian matrix is block lower-triangular with upper-left block $(\partial F_i / \partial T_j)$ and
bottom-right entry $J$, so its determinant is $J^2$, with scaled inverse
$\varpi^{2k} \cdot \pi(J^2)^{-1} = (\varpi^k \cdot \pi(J)^{-1})^2 \in C^+$.

Conversely, for *any* system $F' : \operatorname{Fin} N' \to A^+\langle T_1, \dots, T_{N'}\rangle$
and any $k' : \mathbb{N}$, adjoining $T_{N'+1} \cdot J(F') - \varpi^{k'}$ forces $J(F')$ to divide
the unit $\varpi^{k'}$ in the quotient ring, so the model quotient pair of `explicitInverse`
automatically carries a canonical `StandardEtalePresentation` with scale exponent $2k'$.

## Main definitions and results

* `TauCeti.Huber.explicitInverse`: enlarges `F' : Fin N' → tateSeries N' A` to
  `Fin (N' + 1) → tateSeries (N' + 1) A` by appending
  `T_{N'+1} * castSuccAlgHom (jacobian F') - algebraMap A _ (ϖ ^ k')`.
* `TauCeti.Huber.jacobian_explicitInverse`: the formal Jacobian determinant of
  `explicitInverse A ϖ F' k'` equals `tateSeries.castSuccAlgHom (tateSeries.jacobian F') ^ 2`.
* `TauCeti.Huber.weightedEvalHom_mem_plus_of_mem_tateSeriesPlus`: evaluating an `A⁺`-integral
  restricted power series along a morphism of Huber pairs `(A, A⁺) → (U, U⁺)` into a complete
  Hausdorff Huber pair at tuple elements in `U⁺` lands in `U⁺`.
* `TauCeti.Huber.StandardEtalePresentation.ofExplicitInverse`: the model quotient pair cut out by
  `explicitInverse A ϖ F' k'` carries a canonical `StandardEtalePresentation` with exponent
  `2 * k'`, for any `A⁺`-integral system `F'`.
* `TauCeti.Huber.StandardEtalePresentation.withInverseHom` and
  `TauCeti.Huber.StandardEtalePresentation.withInverse`: upgrades any
  `P : StandardEtalePresentation Aplus ϖ Cplus` to a presentation of the *same* Huber pair `Cplus`
  in `P.N + 1` variables using `explicitInverse A ϖ P.F P.k` and scale exponent `2 * P.k`.

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

/-- **Enlarged standard étale system adjoining an explicit scaled Jacobian inverse.** Given
`F' : Fin N' → tateSeries N' A` and an exponent `k' : ℕ`, this system in `N' + 1` restricted
variables keeps the embedded equations `F'_0, …, F'_{N'-1}` and appends
`T_{N'} * J(F') - ϖ ^ k'`, forcing the new variable `T_{N'}` to equal `ϖ ^ k' · J(F')⁻¹` in the
quotient. -/
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
    refine sub_mem (mul_mem (tateSeries.X_mem_tateSeriesPlus Aplus _) ?_)
      (algebraMap_mem_tateSeriesPlus_iff.mpr (pow_mem hϖ k'))
    exact tateSeries.renameAlgHom_mem_tateSeriesPlus Fin.castSuccEmb
      (tateSeries.jacobian_mem_tateSeriesPlus hF')
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
Jacobian determinant of `F'`.** Because the first `N'` equations are independent of the last
variable while the `(N', N')` entry of the formal Jacobian matrix is `castSuccAlgHom (jacobian F')`,
the block lower-triangular Jacobian matrix has determinant `castSuccAlgHom (jacobian F') ^ 2`. -/
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
          i.castSucc.succAbove (Fin.last N').succAbove).det = 0 := by
    refine Finset.sum_eq_zero fun i _ ↦ ?_
    simp [tateSeries.jacobianMatrix_apply]
  rw [htop, zero_add, Fin.val_last, ← two_mul, pow_mul, neg_one_sq, one_pow, one_mul,
    tateSeries.jacobianMatrix_apply, pderiv_explicitInverse_last_last, Fin.succAbove_last]
  have hsub : (tateSeries.jacobianMatrix (explicitInverse A ϖ F' k')).submatrix
      Fin.castSucc Fin.castSucc =
      tateSeries.castSuccAlgHom.toRingHom.mapMatrix (tateSeries.jacobianMatrix F') := by
    refine Matrix.ext fun i j ↦ ?_
    rw [Matrix.submatrix_apply, RingHom.mapMatrix_apply, Matrix.map_apply,
      tateSeries.jacobianMatrix_apply, tateSeries.jacobianMatrix_apply,
      AlgHom.toRingHom_eq_coe, RingHom.coe_coe, pderiv_explicitInverse_castSucc_castSucc]
  rw [hsub, ← RingHom.map_det, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, ← tateSeries.jacobian_def]
  exact (sq (tateSeries.castSuccAlgHom (tateSeries.jacobian F'))).symm

end ExplicitInverse

namespace StandardEtalePresentation

section OfExplicitInverse

/-- **Canonical standard étale presentation of the quotient by `explicitInverse A ϖ F' k'`.**
For any `A⁺`-integral system `F' : Fin N' → tateSeries N' A` and any `k' : ℕ`, the equation
`T_{N'} · J(F') = ϖ ^ k'` forces `J(F')` to divide the unit `ϖ ^ k'` in the quotient ring, so
`J(explicitInverse) = J(F') ^ 2` maps to a unit `u` with `ϖ ^ (2 * k') · u⁻¹ = T_{N'} ^ 2 ∈ plus`.
-/
noncomputable def ofExplicitInverse
    {A : Type*} [CommRing A] [UniformSpace A] [IsUniformAddGroup A] [IsTopologicalRing A]
    [IsTateRing A] [CompleteSpace A] [T2Space A]
    (Aplus : Pair A) {ϖ : A} (hϖ : IsPseudoUniformizer ϖ)
    {N' : ℕ} (F' : Fin N' → tateSeries N' A) (hF' : ∀ i, F' i ∈ tateSeriesPlus N' A Aplus.plus)
    (k' : ℕ) :
    StandardEtalePresentation Aplus ϖ
      ((tateSeriesPair (N' + 1) A Aplus).quotient
        (Ideal.span (Set.range (explicitInverse A ϖ F' k'))).closure) := by
  let F := explicitInverse A ϖ F' k'
  let I := (Ideal.span (Set.range F)).closure
  have hϖ_mem : ϖ ∈ Aplus.plus :=
    Aplus.isRingOfIntegralElements.mem_of_isTopologicallyNilpotent hϖ.isTopologicallyNilpotent
  have hF : ∀ j, F j ∈ tateSeriesPlus (N' + 1) A Aplus.plus :=
    explicitInverse_mem_tateSeriesPlus hϖ_mem hF' k'
  refine ofQuotient Aplus hϖ F hF (2 * k') ?_
  let s : tateSeries (N' + 1) A ⧸ I :=
    Ideal.Quotient.mk I (tateSeries.X (N' + 1) A (Fin.last N'))
  let jbar : tateSeries (N' + 1) A ⧸ I :=
    Ideal.Quotient.mk I (tateSeries.castSuccAlgHom (tateSeries.jacobian F'))
  have hrel_mem : F (Fin.last N') ∈ I :=
    subset_closure (Ideal.subset_span ⟨Fin.last N', rfl⟩)
  have hrel_zero : Ideal.Quotient.mk I (F (Fin.last N')) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr hrel_mem
  have hsj : s * jbar = algebraMap A (tateSeries (N' + 1) A ⧸ I) (ϖ ^ k') := by
    dsimp only [F] at hrel_zero
    rw [explicitInverse_last, map_sub, map_mul, Ideal.Quotient.mk_algebraMap] at hrel_zero
    exact sub_eq_zero.mp hrel_zero
  have hpow_unit : IsUnit (algebraMap A (tateSeries (N' + 1) A ⧸ I) (ϖ ^ k')) :=
    (hϖ.isUnit.pow k').map (algebraMap A (tateSeries (N' + 1) A ⧸ I))
  have hj_unit : IsUnit jbar := isUnit_of_mul_isUnit_right (hsj ▸ hpow_unit)
  obtain ⟨u₀, hu₀⟩ := hj_unit
  refine ⟨u₀ ^ 2, ?_, ?_⟩
  · rw [Units.val_pow_eq_pow_val, hu₀, ← map_pow, ← jacobian_explicitInverse ϖ F' k']
  · have hinv : algebraMap A (tateSeries (N' + 1) A ⧸ I) (ϖ ^ (2 * k')) * ↑(u₀ ^ 2)⁻¹ =
        s ^ 2 := by
      apply (u₀ ^ 2).mul_left_inj.mp
      calc
        algebraMap A (tateSeries (N' + 1) A ⧸ I) (ϖ ^ (2 * k')) * ↑(u₀ ^ 2)⁻¹ * ↑(u₀ ^ 2)
          = algebraMap A (tateSeries (N' + 1) A ⧸ I) (ϖ ^ (2 * k')) *
              (↑(u₀ ^ 2)⁻¹ * ↑(u₀ ^ 2)) := by rw [mul_assoc]
        _ = algebraMap A (tateSeries (N' + 1) A ⧸ I) (ϖ ^ (2 * k')) := by
              rw [Units.inv_mul, mul_one]
        _ = (algebraMap A (tateSeries (N' + 1) A ⧸ I) (ϖ ^ k')) ^ 2 := by
              rw [← map_pow, ← pow_mul, mul_comm]
        _ = (s * jbar) ^ 2 := by rw [hsj]
        _ = s ^ 2 * ↑(u₀ ^ 2) := by
              rw [Units.val_pow_eq_pow_val, hu₀]
              ring
    rw [hinv]
    refine ((tateSeriesPair (N' + 1) A Aplus).quotient I).plus.pow_mem ?_ 2
    dsimp only [s]
    rw [← Pair.Hom.toRingHom_quotientHom (tateSeriesPair (N' + 1) A Aplus) I]
    exact (Pair.quotientHom (tateSeriesPair (N' + 1) A Aplus) I).map_mem_plus _
      (by simpa only [tateSeriesPair_plus] using
        tateSeries.X_mem_tateSeriesPlus Aplus.plus (Fin.last N'))

@[simp]
theorem ofExplicitInverse_N
    {A : Type*} [CommRing A] [UniformSpace A] [IsUniformAddGroup A] [IsTopologicalRing A]
    [IsTateRing A] [CompleteSpace A] [T2Space A]
    (Aplus : Pair A) {ϖ : A} (hϖ : IsPseudoUniformizer ϖ)
    {N' : ℕ} (F' : Fin N' → tateSeries N' A) (hF' : ∀ i, F' i ∈ tateSeriesPlus N' A Aplus.plus)
    (k' : ℕ) :
    (ofExplicitInverse Aplus hϖ F' hF' k').N = N' + 1 := by
  simp [ofExplicitInverse]

@[simp]
theorem ofExplicitInverse_k
    {A : Type*} [CommRing A] [UniformSpace A] [IsUniformAddGroup A] [IsTopologicalRing A]
    [IsTateRing A] [CompleteSpace A] [T2Space A]
    (Aplus : Pair A) {ϖ : A} (hϖ : IsPseudoUniformizer ϖ)
    {N' : ℕ} (F' : Fin N' → tateSeries N' A) (hF' : ∀ i, F' i ∈ tateSeriesPlus N' A Aplus.plus)
    (k' : ℕ) :
    (ofExplicitInverse Aplus hϖ F' hF' k').k = 2 * k' := by
  simp [ofExplicitInverse]

end OfExplicitInverse

end StandardEtalePresentation

/-- **Evaluation of `tateSeriesPlus` into a complete Hausdorff Huber pair:** if `z : (A, A⁺) →
(U, U⁺)` is a morphism of Huber pairs into a complete Hausdorff Huber pair and `b : Fin M → U` has
entries in `U⁺`, then `weightedEvalHom` carries `tateSeriesPlus M A Aplus.plus` into `U⁺`. -/
theorem weightedEvalHom_mem_plus_of_mem_tateSeriesPlus
    {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsHuberRing A]
    {Aplus : Pair A}
    {U : Type*} [CommRing U] [UniformSpace U] [IsUniformAddGroup U] [IsTopologicalRing U]
    [IsHuberRing U] [CompleteSpace U] [T2Space U]
    (Uplus : Pair U) (z : Pair.Hom Aplus Uplus) {M : ℕ} {b : Fin M → U}
    (hb_mem : ∀ i, b i ∈ Uplus.plus)
    (hb : IsWeightBounded z.toRingHom (fun _ : Fin M ↦ ({1} : Set A)) b)
    {f : tateSeries M A} (hf : f ∈ tateSeriesPlus M A Aplus.plus) :
    weightedEvalHom isWeightFamily_one_weight z.continuous_toRingHom.continuousAt hb f ∈
      Uplus.plus := by
  have hclosed : IsClosed (Uplus.plus : Set U) :=
    AddSubgroup.isClosed_of_isOpen Uplus.plus.toAddSubgroup Uplus.isRingOfIntegralElements.isOpen
  rw [coe_weightedEvalHom]
  refine hclosed.mem_of_tendsto
    (hasSum_weightedEval z.continuous_toRingHom.continuousAt hb
      (mem_weightedRestrictedSubring.mp f.property)) ?_
  filter_upwards with s
  refine Uplus.plus.sum_mem fun ν _ ↦ ?_
  rw [weightedEvalTerm_def]
  refine Uplus.plus.mul_mem (z.map_mem_plus _ (mem_tateSeriesPlus_iff.mp hf ν)) ?_
  exact Uplus.plus.prod_mem fun i _ ↦ Uplus.plus.pow_mem (hb_mem i) (ν i)

namespace StandardEtalePresentation

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

private theorem mul_scaledJacobianInv
    (P : StandardEtalePresentation Aplus ϖ Cplus) :
    (P.exists_unit_π_jacobian.choose : C) * P.scaledJacobianInv =
      algebraMap A C (ϖ ^ P.k) := by
  dsimp only [scaledJacobianInv]
  calc
    (P.exists_unit_π_jacobian.choose : C) *
        (algebraMap A C (ϖ ^ P.k) * ↑P.exists_unit_π_jacobian.choose⁻¹)
      = algebraMap A C (ϖ ^ P.k) *
          (↑P.exists_unit_π_jacobian.choose * ↑P.exists_unit_π_jacobian.choose⁻¹) := by ring
    _ = algebraMap A C (ϖ ^ P.k) := by simp

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

/-- **Extended `A`-algebra quotient homomorphism `tateSeries (P.N + 1) A →ₐ[A] C`** extending `P.π`
along `tateSeries.castSuccAlgHom` and sending `T_{P.N}` to `ϖ ^ P.k · P.π(P.jacobian)⁻¹ ∈ C⁺`. -/
noncomputable def withInverseHom
    (P : StandardEtalePresentation Aplus ϖ Cplus) :
    tateSeries (P.N + 1) A →ₐ[A] C := by
  let _ : UniformSpace C := IsTopologicalAddGroup.rightUniformSpace C
  have : IsUniformAddGroup C := isUniformAddGroup_of_addCommGroup
  have : T2Space C := P.t2Space
  have : CompleteSpace C := P.isOpenQuotientMap_π.completeSpace
  have hb : IsWeightBounded (algebraMap A C)
      (fun _ : Fin (P.N + 1) ↦ ({1} : Set A)) P.withInverseTuple :=
    (isWeightBounded_one_weight_iff_forall_isPowerBounded _ _).mpr fun j ↦
      Cplus.isRingOfIntegralElements.isPowerBounded_of_mem (P.withInverseTuple_mem_plus j)
  let ev := weightedEvalHom isWeightFamily_one_weight P.continuous_algebraMap.continuousAt hb
  exact
    { toFun := ev
      map_one' := ev.map_one
      map_mul' := ev.map_mul
      map_zero' := ev.map_zero
      map_add' := ev.map_add
      commutes' a := by
        rw [algebraMap_weightedRestrictedSubring, weightedEvalHom_weightedC] }

/-- `P.withInverseHom` is continuous. -/
theorem continuous_withInverseHom
    (P : StandardEtalePresentation Aplus ϖ Cplus) :
    Continuous P.withInverseHom := by
  let _ : UniformSpace C := IsTopologicalAddGroup.rightUniformSpace C
  have : IsUniformAddGroup C := isUniformAddGroup_of_addCommGroup
  have : T2Space C := P.t2Space
  have : CompleteSpace C := P.isOpenQuotientMap_π.completeSpace
  have hb : IsWeightBounded (algebraMap A C)
      (fun _ : Fin (P.N + 1) ↦ ({1} : Set A)) P.withInverseTuple :=
    (isWeightBounded_one_weight_iff_forall_isPowerBounded _ _).mpr fun j ↦
      Cplus.isRingOfIntegralElements.isPowerBounded_of_mem (P.withInverseTuple_mem_plus j)
  exact continuous_weightedEvalHom isWeightFamily_one_weight
    P.continuous_algebraMap.continuousAt hb

private theorem withInverseHom_X_apply
    (P : StandardEtalePresentation Aplus ϖ Cplus) (j : Fin (P.N + 1)) :
    P.withInverseHom (tateSeries.X (P.N + 1) A j) = P.withInverseTuple j := by
  let _ : UniformSpace C := IsTopologicalAddGroup.rightUniformSpace C
  have : IsUniformAddGroup C := isUniformAddGroup_of_addCommGroup
  have : T2Space C := P.t2Space
  have : CompleteSpace C := P.isOpenQuotientMap_π.completeSpace
  dsimp only [withInverseHom]
  rw [AlgHom.coe_mk, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, tateSeries.X_eq_weightedX,
    weightedEvalHom_weightedX]

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
    · rw [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        ← algebraMap_weightedRestrictedSubring, AlgHom.commutes, AlgHom.commutes, AlgHom.commutes]
    · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        ← tateSeries.X_eq_weightedX, tateSeries.renameAlgHom_X, withInverseHom_X_apply]
      simp [withInverseTuple]
  exact congrArg (fun φ : tateSeries P.N A →+* C ↦ φ f) hext

/-- On the newly adjoined variable `T_{P.N}`, `P.withInverseHom` satisfies the explicit inverse
relation `P.withInverseHom T_{P.N} * P.π P.jacobian = algebraMap A C (ϖ ^ P.k)`. -/
theorem withInverseHom_last_mul_jacobian
    (P : StandardEtalePresentation Aplus ϖ Cplus) :
    P.withInverseHom (tateSeries.X (P.N + 1) A (Fin.last P.N)) * P.π P.jacobian =
      algebraMap A C (ϖ ^ P.k) := by
  rw [withInverseHom_X_apply, withInverseTuple, Fin.snoc_last,
    ← P.exists_unit_π_jacobian.choose_spec.1, mul_comm, mul_scaledJacobianInv]

/-- The extended homomorphism `P.withInverseHom` is a topological quotient map. -/
theorem isQuotientMap_withInverseHom
    (P : StandardEtalePresentation Aplus ϖ Cplus) :
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

private theorem ker_withInverseHom_le
    (P : StandardEtalePresentation Aplus ϖ Cplus) :
    RingHom.ker P.withInverseHom ≤
      (Ideal.span (Set.range (explicitInverse A ϖ P.F P.k))).closure := by
  have : T2Space C := P.t2Space
  let F := explicitInverse A ϖ P.F P.k
  let K' := (Ideal.span (Set.range F)).closure
  let u : Cˣ := P.exists_unit_π_jacobian.choose
  have hu_eq : (u : C) = P.π P.jacobian := P.exists_unit_π_jacobian.choose_spec.1
  have : IsClosed (K' : Set (tateSeries (P.N + 1) A)) := by
    rw [Ideal.coe_closure]; exact isClosed_closure
  let φ₀ : tateSeries P.N A →+* tateSeries (P.N + 1) A ⧸ K' :=
    (Ideal.Quotient.mk K').comp tateSeries.castSuccAlgHom.toRingHom
  have hφ₀_cont : Continuous φ₀ :=
    continuous_quotient_mk'.comp (tateSeries.continuous_renameAlgHom Fin.castSuccEmb)
  have hI_le : P.ideal ≤ RingHom.ker φ₀ := by
    have hker_closed : IsClosed (RingHom.ker φ₀ : Set (tateSeries P.N A)) :=
      isClosed_singleton.preimage hφ₀_cont
    rw [← SetLike.coe_subset_coe, P.ideal_def, Ideal.coe_closure]
    refine hker_closed.closure_subset_iff.mpr (SetLike.coe_subset_coe.mpr (Ideal.span_le.mpr ?_))
    rintro _ ⟨i, rfl⟩
    rw [SetLike.mem_coe, RingHom.mem_ker]
    dsimp only [φ₀]
    rw [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      ← explicitInverse_castSucc ϖ P.F P.k i, Ideal.Quotient.eq_zero_iff_mem]
    exact subset_closure (Ideal.subset_span ⟨i.castSucc, rfl⟩)
  let ψ : C →+* tateSeries (P.N + 1) A ⧸ K' :=
    (Ideal.Quotient.lift P.ideal φ₀ fun g hg ↦ hI_le hg).comp P.targetToQuotient.toRingHom
  have hψ_cont : Continuous ψ :=
    (Ideal.Quotient.continuous_lift P.ideal hφ₀_cont fun g hg ↦ hI_le hg).comp
      P.targetToQuotient.continuous_toRingHom
  have hψ_π : ∀ g : tateSeries P.N A,
      ψ (P.π g) = Ideal.Quotient.mk K' (tateSeries.castSuccAlgHom g) := fun g ↦ by
    simp [ψ, φ₀]
  have hcomp : ψ.comp P.withInverseHom.toRingHom = Ideal.Quotient.mk K' := by
    refine weightedRestrictedSubring_ringHom_ext_of_continuous isWeightFamily_one_weight
      (hψ_cont.comp P.continuous_withInverseHom) continuous_quotient_mk'
      (fun a ↦ ?_) (fun j ↦ ?_)
    · rw [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        ← algebraMap_weightedRestrictedSubring, AlgHom.commutes, ← P.π.commutes, hψ_π,
        AlgHom.commutes]
    · rw [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        ← tateSeries.X_eq_weightedX]
      refine Fin.lastCases ?_ (fun i ↦ ?_) j
      · let uQ : (tateSeries (P.N + 1) A ⧸ K')ˣ := Units.map (ψ : C →* _) u
        have huQ : (uQ : tateSeries (P.N + 1) A ⧸ K') =
            Ideal.Quotient.mk K' (tateSeries.castSuccAlgHom P.jacobian) := by
          rw [Units.coe_map, MonoidHom.coe_ofClass, hu_eq, hψ_π]
        apply uQ.mul_left_inj.mp
        have hlast_eq : Ideal.Quotient.mk K' (tateSeries.X (P.N + 1) A (Fin.last P.N)) *
            Ideal.Quotient.mk K' (tateSeries.castSuccAlgHom P.jacobian) =
            Ideal.Quotient.mk K'
              (algebraMap A (tateSeries (P.N + 1) A) (ϖ ^ P.k)) := by
          have hlast_zero : Ideal.Quotient.mk K' (F (Fin.last P.N)) = 0 :=
            Ideal.Quotient.eq_zero_iff_mem.mpr
              (subset_closure (Ideal.subset_span ⟨Fin.last P.N, rfl⟩))
          dsimp only [F] at hlast_zero
          rw [explicitInverse_last, map_sub, map_mul, ← P.jacobian_def] at hlast_zero
          exact sub_eq_zero.mp hlast_zero
        calc
          ψ (P.withInverseHom (tateSeries.X (P.N + 1) A (Fin.last P.N))) * uQ
            = ψ (P.withInverseHom (tateSeries.X (P.N + 1) A (Fin.last P.N)) * P.π P.jacobian) := by
                rw [Units.coe_map, MonoidHom.coe_ofClass, ← map_mul, hu_eq]
          _ = ψ (algebraMap A C (ϖ ^ P.k)) := by rw [P.withInverseHom_last_mul_jacobian]
          _ = Ideal.Quotient.mk K' (algebraMap A (tateSeries (P.N + 1) A) (ϖ ^ P.k)) := by
                rw [← P.π.commutes, hψ_π, AlgHom.commutes]
          _ = Ideal.Quotient.mk K' (tateSeries.X (P.N + 1) A (Fin.last P.N)) * uQ := by
                rw [huQ, hlast_eq]
      · have hi : i.castSucc = Fin.castSuccEmb i := rfl
        rw [hi, ← tateSeries.renameAlgHom_X Fin.castSuccEmb, withInverseHom_castSuccAlgHom, hψ_π]
  intro f hf
  rw [RingHom.mem_ker] at hf
  exact Ideal.Quotient.eq_zero_iff_mem.mp (by rw [← hcomp]; simp [RingHom.comp_apply, hf])

private theorem le_ker_withInverseHom
    (P : StandardEtalePresentation Aplus ϖ Cplus) :
    (Ideal.span (Set.range (explicitInverse A ϖ P.F P.k))).closure ≤
      RingHom.ker P.withInverseHom := by
  have : T2Space C := P.t2Space
  have hker_closed :
      IsClosed (RingHom.ker P.withInverseHom : Set (tateSeries (P.N + 1) A)) :=
    isClosed_singleton.preimage P.continuous_withInverseHom
  refine hker_closed.closure_subset_iff.mpr (Ideal.span_le.mpr ?_)
  rintro _ ⟨j, rfl⟩
  rw [SetLike.mem_coe, RingHom.mem_ker]
  refine Fin.lastCases ?_ (fun i ↦ ?_) j
  · simp only [explicitInverse_last, map_sub, map_mul, AlgHom.commutes,
      withInverseHom_castSuccAlgHom]
    rw [← P.jacobian_def, P.withInverseHom_last_mul_jacobian, sub_self]
  · simp [P.π_F]

/-- The kernel of `P.withInverseHom` is the closure of the ideal generated by the enlarged system
`explicitInverse A ϖ P.F P.k`. -/
theorem ker_withInverseHom
    (P : StandardEtalePresentation Aplus ϖ Cplus) :
    RingHom.ker P.withInverseHom =
      (Ideal.span (Set.range (explicitInverse A ϖ P.F P.k))).closure :=
  le_antisymm P.ker_withInverseHom_le P.le_ker_withInverseHom

/-- **Upgrade a `StandardEtalePresentation` by adjoining an explicit scaled Jacobian inverse.**
Given `P : StandardEtalePresentation Aplus ϖ Cplus`, this produces a new presentation of the *same*
Huber pair `Cplus` in `P.N + 1` variables with equations `explicitInverse A ϖ P.F P.k`, projection
`P.withInverseHom`, and scale exponent `2 * P.k`. -/
noncomputable def withInverse
    (P : StandardEtalePresentation Aplus ϖ Cplus) :
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
      have : CompleteSpace C := P.isOpenQuotientMap_π.completeSpace
      have := Cplus.isRingOfIntegralElements.isIntegrallyClosedIn
      have hb : IsWeightBounded P.toBasePairHom.toRingHom
          (fun _ : Fin (P.N + 1) ↦ ({1} : Set A)) P.withInverseTuple :=
        (isWeightBounded_one_weight_iff_forall_isPowerBounded _ _).mpr fun j ↦
          Cplus.isRingOfIntegralElements.isPowerBounded_of_mem (P.withInverseTuple_mem_plus j)
      have hmap_le : (tateSeriesPlus (P.N + 1) A Aplus.plus).map P.withInverseHom.toRingHom
          ≤ Cplus.plus := by
        rintro _ ⟨f, hf, rfl⟩
        have hval : P.withInverseHom.toRingHom f =
            weightedEvalHom isWeightFamily_one_weight
              P.toBasePairHom.continuous_toRingHom.continuousAt hb f := by
          dsimp only [withInverseHom]
          rw [RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, coe_weightedEvalHom,
            coe_weightedEvalHom, P.toBasePairHom_toRingHom]
        rw [hval]
        exact weightedEvalHom_mem_plus_of_mem_tateSeriesPlus Cplus P.toBasePairHom
          P.withInverseTuple_mem_plus hb hf
      intro hc
      exact Subring.integralClosure_subring_le_iff.mpr hmap_le
        ((mem_integralClosure_iff _ _).mpr hc)
  exists_unit_jacobian := by
    let F := explicitInverse A ϖ P.F P.k
    let u : Cˣ := P.exists_unit_π_jacobian.choose
    have hu_eq : (u : C) = P.π P.jacobian := P.exists_unit_π_jacobian.choose_spec.1
    refine ⟨tateSeries.jacobian F, tateSeries.coe_jacobian F, u ^ 2, ?_, ?_⟩
    · rw [Units.val_pow_eq_pow_val, hu_eq, jacobian_explicitInverse, map_pow,
        withInverseHom_castSuccAlgHom, P.jacobian_def]
    · have hu_inv_sq : (↑(u ^ 2)⁻¹ : C) = (↑u⁻¹ : C) ^ 2 := by
        apply (u ^ 2).mul_right_inj.mp
        rw [Units.mul_inv, Units.val_pow_eq_pow_val]
        calc
          1 = ((u : C) * ↑u⁻¹) ^ 2 := by simp
          _ = (u : C) ^ 2 * (↑u⁻¹ : C) ^ 2 := by ring
      have hsq : algebraMap A C (ϖ ^ (2 * P.k)) * ↑(u ^ 2)⁻¹ = P.scaledJacobianInv ^ 2 := by
        dsimp only [scaledJacobianInv]
        rw [hu_inv_sq, mul_comm 2 P.k, pow_mul, map_pow]
        ring
      rw [hsq]
      exact Cplus.plus.pow_mem P.scaledJacobianInv_mem_plus 2

@[simp]
theorem withInverse_N (P : StandardEtalePresentation Aplus ϖ Cplus) :
    P.withInverse.N = P.N + 1 :=
  (rfl)

@[simp]
theorem withInverse_k (P : StandardEtalePresentation Aplus ϖ Cplus) :
    P.withInverse.k = 2 * P.k :=
  (rfl)

/-- The defining system of `P.withInverse` is `explicitInverse A ϖ P.F P.k` (heterogeneously equal
along `P.withInverse_N`). -/
theorem withInverse_F_heq (P : StandardEtalePresentation Aplus ϖ Cplus) :
    HEq P.withInverse.F (explicitInverse A ϖ P.F P.k) :=
  (HEq.rfl)

/-- The presenting map of `P.withInverse` is `P.withInverseHom` (heterogeneously equal along
`P.withInverse_N`). -/
theorem withInverse_π_heq (P : StandardEtalePresentation Aplus ϖ Cplus) :
    HEq P.withInverse.π P.withInverseHom :=
  (HEq.rfl)

end WithInverse

end StandardEtalePresentation

section Checks

variable {A : Type*} [CommRing A] [TopologicalSpace A] [NonarchimedeanRing A]

/-- Sanity check (`N' = 0`, `k' = 0`): adjoining an explicit inverse to the empty system yields the
single equation `T₀ - 1` with Jacobian determinant `1`. -/
example (ϖ : A) :
    explicitInverse A ϖ Fin.elim0 0 0 = tateSeries.X 1 A 0 - 1 ∧
      tateSeries.jacobian (explicitInverse A ϖ Fin.elim0 0) = 1 := by
  constructor
  · simpa using explicitInverse_last ϖ (Fin.elim0 : Fin 0 → tateSeries 0 A) 0
  · rw [jacobian_explicitInverse, tateSeries.jacobian_fin_zero, map_one, one_pow]

/-- Sanity check (`N' = 1`, `F' = ![T₀ ^ 2 - 2]`, `k' = 3`): the enlarged 2-variable system keeps
`T₀ ^ 2 - 2`, appends `T₁ * (2 * T₀) - ϖ ^ 3`, and has Jacobian determinant `(2 * T₀) ^ 2`. -/
example (ϖ : A) :
    let F' : Fin 1 → tateSeries 1 A := ![tateSeries.X 1 A 0 ^ 2 - 2]
    explicitInverse A ϖ F' 3 0 = tateSeries.X 2 A 0 ^ 2 - 2 ∧
      explicitInverse A ϖ F' 3 1 =
        tateSeries.X 2 A 1 * (2 * tateSeries.X 2 A 0) - algebraMap A (tateSeries 2 A) (ϖ ^ 3) ∧
      tateSeries.jacobian (explicitInverse A ϖ F' 3) = (2 * tateSeries.X 2 A 0) ^ 2 := by
  intro F'
  have hJ : tateSeries.jacobian F' = 2 * tateSeries.X 1 A 0 := by
    rw [tateSeries.jacobian_fin_one]
    dsimp only [F', Matrix.cons_val_zero]
    have h2 : (2 : tateSeries 1 A) = algebraMap A (tateSeries 1 A) 2 := (map_ofNat _ 2).symm
    rw [h2, map_sub, tateSeries.pderiv_pow, tateSeries.pderiv_X_self,
      tateSeries.pderiv_algebraMap, map_ofNat]
    ring
  have hX0 : tateSeries.castSuccAlgHom (tateSeries.X 1 A 0) = tateSeries.X 2 A 0 :=
    tateSeries.renameAlgHom_X Fin.castSuccEmb 0
  refine ⟨?_, ?_, ?_⟩
  · rw [← Fin.castSucc_zero, explicitInverse_castSucc]
    dsimp only [F', Matrix.cons_val_zero]
    rw [map_sub, map_pow, map_ofNat, hX0]
    rfl
  · have h1 := explicitInverse_last ϖ F' 3
    rw [hJ, map_mul, map_ofNat, hX0] at h1
    exact h1
  · rw [jacobian_explicitInverse, hJ, map_mul, map_ofNat, hX0]

/-- Sanity check over `ℚ_[p]`: `StandardEtalePresentation.ofExplicitInverse` turns any `ℚ_[p]°`-
integral equation in `ℚ_[p]⟨T₀⟩` into an explicit 2-variable standard étale presentation with
scale exponent `2 * k'`. -/
example (p : ℕ) [Fact p.Prime] (k' : ℕ) :
    let F' : Fin 1 → tateSeries 1 ℚ_[p] := ![tateSeries.X 1 ℚ_[p] 0 ^ 2 - 2]
    (StandardEtalePresentation.ofExplicitInverse (Pair.powerBounded ℚ_[p])
      Padic.isPseudoUniformizer_p F'
      (fun i ↦ by
        fin_cases i
        exact sub_mem
          (pow_mem (tateSeries.X_mem_tateSeriesPlus _ 0) 2)
          (ofNat_mem _ 2)) k').k = 2 * k' := by
  simp

end Checks

end TauCeti.Huber

end
