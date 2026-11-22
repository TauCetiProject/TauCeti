/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.QuadraticForm.IsometryEquiv
public import Mathlib.LinearAlgebra.QuadraticForm.Prod
public import Mathlib.LinearAlgebra.QuadraticForm.Radical
import Mathlib.LinearAlgebra.Determinant
import TauCeti.LinearAlgebra.Pi
import TauCeti.Logic.Equiv.Set

/-!
# Diagonal quadratic forms

This file provides general infrastructure for diagonal quadratic forms expressed as weighted sums
of squares.

## Main results

* `QuadraticMap.weightedSumSquares_eq_of_smul_one_eq`: a diagonal form depends on its weights only
  through their action on `1`.
* `QuadraticForm.isometryEquivWeightedSumSquaresReindex` and
  `QuadraticForm.equivalent_weightedSumSquares_of_comp_eq`: reindexing the weights along an
  equivalence of index types gives an isometric diagonal form.
* `TauCeti.isometryEquivWeightedSumSquaresOfPair` and
  `TauCeti.equivalent_weightedSumSquares_of_pair`: a binary isometry (equivalence) extends across
  fixed coordinates, by `LinearEquiv.piExtendOfInjective` along the pair.
* `TauCeti.weightedSumSquaresMulFiberIsometryEquiv`,
  `TauCeti.weightedSumSquaresMulFiberIsometryEquiv_apply`, and
  `TauCeti.weightedSumSquaresMulFiberIsometryEquiv_symm_apply`: fiberwise orthogonal-sum
  decomposition isometry for a scaled diagonal form over any commutative semiring, together with
  its forward and inverse coordinate characterizations.
* `TauCeti.equivalent_weightedSumSquares_mul_of_forall_fiber`: fiberwise equivalences of diagonal
  subforms assemble into an equivalence of scaled diagonal forms over any commutative semiring.
* `QuadraticMap.associated_weightedSumSquares`, `QuadraticForm.toMatrix'_weightedSumSquares`, and
  `QuadraticForm.discr'_weightedSumSquares`: over a ring in which two is invertible, the associated
  bilinear form of a diagonal form is the weighted dot product, its Gram matrix in the standard
  basis is the diagonal matrix of the weights (acting on `1`), and its discriminant is their
  product.
* `QuadraticMap.nondegenerate_weightedSumSquares`: over a ring in which two is invertible, a
  diagonal form with regular weights is nondegenerate; in particular so is `⟨1, a, -a⟩` for a unit
  `a` (`QuadraticMap.nondegenerate_weightedSumSquares_one_self_neg`).
* `QuadraticMap.weightedSumSquares_units`: unit weights may be replaced by the scalars they name.
* `QuadraticMap.smul_weightedSumSquares` and `QuadraticMap.neg_weightedSumSquares`: scaling or
  negating a diagonal form scales or negates its weights.
* `QuadraticMap.weightedSumSquares_apply_single`, `QuadraticMap.isOrtho_weightedSumSquares_single`,
  and `QuadraticMap.isOrthoᵢ_associated_weightedSumSquares`: single-coordinate evaluation and
  orthogonality of distinct coordinate vectors and of the standard coordinate basis `Pi.basisFun`.
* `QuadraticMap.weightedSumSquares_fin_two_apply`: evaluating a binary diagonal form.
* `QuadraticMap.weightedSumSquares_apply_three_single` and
  `QuadraticMap.not_anisotropic_weightedSumSquares_of_ternary_eq_zero`: evaluating a diagonal form
  on a linear combination of three distinct basis vectors, and deducing that a ternary solution with
  a nonzero third coordinate gives a nonzero isotropic vector.
* `TauCeti.isSquare_prod_mul_prod_of_equivalent`: isometric diagonal forms with unit weights have
  weight products differing by a square.
-/

public section

namespace TauCeti

universe u v w

open QuadraticMap

variable {R : Type u} {ι : Type v} {κ : Type w}

section PairExtension

variable [CommSemiring R] [Fintype ι] {S : Type*} [Monoid S] [DistribMulAction S R]
  [SMulCommClass S R R] {w w' : ι → S} {i j : ι}

/-- Replacing two distinct coefficients by those of an isometric binary form, while fixing all other
coefficients up to their action on `1`, gives an isometric diagonal form. The isometry is the
extension `LinearEquiv.piExtendOfInjective` of `e` along the pair `![i, j]`: it applies `e` to the
coordinates `i, j` and fixes the others
(`isometryEquivWeightedSumSquaresOfPair_apply_left`,
`isometryEquivWeightedSumSquaresOfPair_apply_right`,
`isometryEquivWeightedSumSquaresOfPair_apply_of_ne`). -/
noncomputable def isometryEquivWeightedSumSquaresOfPair (hij : i ≠ j)
    (e : (weightedSumSquares R ![w i, w j]).IsometryEquiv
      (weightedSumSquares R ![w' i, w' j]))
    (hrest : ∀ k, k ≠ i → k ≠ j → w k • (1 : R) = w' k • (1 : R)) :
    (weightedSumSquares R w).IsometryEquiv (weightedSumSquares R w') where
  toLinearEquiv := e.toLinearEquiv.piExtendOfInjective (Matrix.injective_pair_iff_ne.2 hij)
  map_app' x := by
    classical
    -- Split both sums along `Fin 2 ⊕ (Set.range ![i, j])ᶜ ≃ ι`: on the pair `i, j` the isometry
    -- `e` preserves the binary form, and off the pair the coordinates are fixed and the weights
    -- act alike.
    have he := e.map_app ![x i, x j]
    have hx : x ∘ ![i, j] = ![x i, x j] := (FinVec.map_eq x ![i, j]).symm
    simp only [weightedSumSquares_apply, Fin.sum_univ_two, Matrix.cons_val_zero,
      Matrix.cons_val_one] at he
    simp only [LinearMap.toFun_eq_coe, LinearEquiv.coe_coe, weightedSumSquares_apply,
      ← (Equiv.ofInjectiveSumCompl _ (Matrix.injective_pair_iff_ne.2 hij)).sum_comp,
      Fintype.sum_sum_type, Equiv.ofInjectiveSumCompl_apply_inl,
      Equiv.ofInjectiveSumCompl_apply_inr, LinearEquiv.piExtendOfInjective_apply_apply, hx,
      Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, IsometryEquiv.coe_toLinearEquiv]
    rw [he]
    congr 1
    refine Fintype.sum_congr _ _ fun k ↦ ?_
    rw [LinearEquiv.piExtendOfInjective_apply_of_notMem _ _ _ k.property, ← mul_smul_one,
      ← hrest k (fun h ↦ k.property ⟨0, h.symm⟩) (fun h ↦ k.property ⟨1, h.symm⟩), mul_smul_one]

/-- The linear equivalence underlying the pair-replacement isometry is the extension of `e` along
the pair `![i, j]`. -/
private theorem isometryEquivWeightedSumSquaresOfPair_toLinearEquiv (hij : i ≠ j)
    (e : (weightedSumSquares R ![w i, w j]).IsometryEquiv
      (weightedSumSquares R ![w' i, w' j]))
    (hrest : ∀ k, k ≠ i → k ≠ j → w k • (1 : R) = w' k • (1 : R)) :
    (isometryEquivWeightedSumSquaresOfPair hij e hrest).toLinearEquiv =
      e.toLinearEquiv.piExtendOfInjective (Matrix.injective_pair_iff_ne.2 hij) :=
  (rfl)

/-- The pair-replacement isometry acts on the first coordinate of the pair through `e`. -/
@[simp]
theorem isometryEquivWeightedSumSquaresOfPair_apply_left (hij : i ≠ j)
    (e : (weightedSumSquares R ![w i, w j]).IsometryEquiv
      (weightedSumSquares R ![w' i, w' j]))
    (hrest : ∀ k, k ≠ i → k ≠ j → w k • (1 : R) = w' k • (1 : R)) (x : ι → R) :
    isometryEquivWeightedSumSquaresOfPair hij e hrest x i = e ![x i, x j] 0 := by
  have h := e.toLinearEquiv.piExtendOfInjective_apply_apply (Matrix.injective_pair_iff_ne.2 hij) x 0
  have hx : x ∘ ![i, j] = ![x i, x j] := (FinVec.map_eq x ![i, j]).symm
  rw [← isometryEquivWeightedSumSquaresOfPair_toLinearEquiv hij e hrest, hx] at h
  simpa using h

/-- The pair-replacement isometry acts on the second coordinate of the pair through `e`. -/
@[simp]
theorem isometryEquivWeightedSumSquaresOfPair_apply_right (hij : i ≠ j)
    (e : (weightedSumSquares R ![w i, w j]).IsometryEquiv
      (weightedSumSquares R ![w' i, w' j]))
    (hrest : ∀ k, k ≠ i → k ≠ j → w k • (1 : R) = w' k • (1 : R)) (x : ι → R) :
    isometryEquivWeightedSumSquaresOfPair hij e hrest x j = e ![x i, x j] 1 := by
  have h := e.toLinearEquiv.piExtendOfInjective_apply_apply (Matrix.injective_pair_iff_ne.2 hij) x 1
  have hx : x ∘ ![i, j] = ![x i, x j] := (FinVec.map_eq x ![i, j]).symm
  rw [← isometryEquivWeightedSumSquaresOfPair_toLinearEquiv hij e hrest, hx] at h
  simpa using h

/-- The pair-replacement isometry fixes the coordinates outside the pair. -/
@[simp]
theorem isometryEquivWeightedSumSquaresOfPair_apply_of_ne (hij : i ≠ j)
    (e : (weightedSumSquares R ![w i, w j]).IsometryEquiv
      (weightedSumSquares R ![w' i, w' j]))
    (hrest : ∀ k, k ≠ i → k ≠ j → w k • (1 : R) = w' k • (1 : R)) (x : ι → R) {k : ι}
    (hki : k ≠ i) (hkj : k ≠ j) :
    isometryEquivWeightedSumSquaresOfPair hij e hrest x k = x k := by
  have h := e.toLinearEquiv.piExtendOfInjective_apply_of_notMem
    (Matrix.injective_pair_iff_ne.2 hij) x (i := k) (by simp [hki, hkj])
  rwa [← isometryEquivWeightedSumSquaresOfPair_toLinearEquiv hij e hrest,
    IsometryEquiv.coe_toLinearEquiv] at h

/-- The inverse of the pair-replacement isometry along `e` is the pair-replacement isometry along
`e.symm`. -/
@[simp]
theorem isometryEquivWeightedSumSquaresOfPair_symm_apply (hij : i ≠ j)
    (e : (weightedSumSquares R ![w i, w j]).IsometryEquiv
      (weightedSumSquares R ![w' i, w' j]))
    (hrest : ∀ k, k ≠ i → k ≠ j → w k • (1 : R) = w' k • (1 : R)) (x : ι → R) :
    (isometryEquivWeightedSumSquaresOfPair hij e hrest).symm x =
      isometryEquivWeightedSumSquaresOfPair hij e.symm (fun k hki hkj ↦ (hrest k hki hkj).symm)
        x := by
  simp only [← IsometryEquiv.coe_toLinearEquiv, ← IsometryEquiv.coe_symm_toLinearEquiv,
    isometryEquivWeightedSumSquaresOfPair_toLinearEquiv, LinearEquiv.piExtendOfInjective_symm]

/-- Replacing two distinct coefficients by an equivalent binary form, while fixing all other
coefficients up to their action on `1`, produces an equivalent diagonal form. -/
theorem equivalent_weightedSumSquares_of_pair (hij : i ≠ j)
    (hpair : (weightedSumSquares R ![w i, w j]).Equivalent
      (weightedSumSquares R ![w' i, w' j]))
    (hrest : ∀ k, k ≠ i → k ≠ j → w k • (1 : R) = w' k • (1 : R)) :
    (weightedSumSquares R w).Equivalent (weightedSumSquares R w') :=
  let ⟨e⟩ := hpair
  ⟨isometryEquivWeightedSumSquaresOfPair hij e hrest⟩

end PairExtension

section CommSemiring

variable [CommSemiring R] [Fintype ι] [Fintype κ]

section Reindex

variable {S : Type*} [Monoid S] [DistribMulAction S R] [SMulCommClass S R R]

/-- A weighted sum of squares depends on its weights only through their action on `1`. -/
theorem _root_.QuadraticMap.weightedSumSquares_eq_of_smul_one_eq {T : Type*} [Monoid T]
    [DistribMulAction T R] [SMulCommClass T R R] {w : ι → S} {w' : ι → T}
    (h : ∀ i, w i • (1 : R) = w' i • (1 : R)) :
    weightedSumSquares R w = weightedSumSquares R w' := by
  ext x
  simp only [weightedSumSquares_apply]
  refine Fintype.sum_congr _ _ fun i ↦ ?_
  rw [← mul_smul_one, h, mul_smul_one]

/-- Reindexing the weights of a weighted sum of squares along an equivalence of the index types
gives an isometric quadratic form.  The isometry is precomposition with the equivalence. -/
def _root_.QuadraticForm.isometryEquivWeightedSumSquaresReindex (w : ι → S) (e : κ ≃ ι) :
    IsometryEquiv (weightedSumSquares R w) (weightedSumSquares R (w ∘ e)) where
  __ := LinearEquiv.funCongrLeft R R e
  map_app' x := by
    simpa [weightedSumSquares_apply, LinearEquiv.funCongrLeft_apply, LinearMap.funLeft_apply]
      using e.sum_comp fun i ↦ w i • (x i * x i)

/-- The reindexing isometry acts on a vector by precomposition with the equivalence. -/
@[simp]
theorem _root_.QuadraticForm.isometryEquivWeightedSumSquaresReindex_apply (w : ι → S) (e : κ ≃ ι)
    (x : ι → R) (i : κ) :
    QuadraticForm.isometryEquivWeightedSumSquaresReindex w e x i = x (e i) :=
  -- The parentheses keep the proof opaque, so the definition need not be exposed.
  (rfl)

/-- The inverse of the reindexing isometry acts on a vector by precomposition with the inverse
equivalence. -/
@[simp]
theorem _root_.QuadraticForm.isometryEquivWeightedSumSquaresReindex_symm_apply (w : ι → S)
    (e : κ ≃ ι) (y : κ → R) (i : ι) :
    (QuadraticForm.isometryEquivWeightedSumSquaresReindex w e).symm y i = y (e.symm i) := by
  -- Evaluate `f (f.symm y) = y` at `e.symm i`, where `f` is the reindexing isometry.
  have h := QuadraticForm.isometryEquivWeightedSumSquaresReindex_apply w e
    ((QuadraticForm.isometryEquivWeightedSumSquaresReindex w e).symm y) (e.symm i)
  rwa [IsometryEquiv.apply_symm_apply, Equiv.apply_symm_apply, eq_comm] at h

/-- Weighted sums of squares whose weights agree after reindexing, up to their action on `1`, are
equivalent. -/
theorem _root_.QuadraticForm.equivalent_weightedSumSquares_of_comp_eq
    {w : ι → S} {w' : κ → S} (e : κ ≃ ι) (h : ∀ i, w (e i) • (1 : R) = w' i • (1 : R)) :
    (weightedSumSquares R w').Equivalent (weightedSumSquares R w) := by
  rw [← QuadraticMap.weightedSumSquares_eq_of_smul_one_eq (w := w ∘ e) h]
  exact ⟨(QuadraticForm.isometryEquivWeightedSumSquaresReindex w e).symm⟩

end Reindex

/-- Fiberwise orthogonal-sum decomposition of a scaled diagonal form `∑ᵢ uᵢ s(kᵢ) xᵢ²` over the
finite image of the scale profile `k`. -/
def weightedSumSquaresMulFiberIsometryEquiv {α : Type*} [DecidableEq α]
    (k : ι → α) (s : α → R) (u : ι → R) :
    (weightedSumSquares R fun i ↦ u i * s (k i)).IsometryEquiv
      (QuadraticMap.pi fun m : Finset.univ.image k ↦
        s m.val • weightedSumSquares R fun i : {i : ι // k i = m.val} ↦ u i.val) where
  toLinearEquiv :=
    let κ : ι → Finset.univ.image k := fun i ↦
      ⟨k i, Finset.mem_image_of_mem k (Finset.mem_univ i)⟩
    let fiberEquiv (m : Finset.univ.image k) : {i : ι // κ i = m} ≃ {i : ι // k i = m.val} :=
      Equiv.subtypeEquivRight fun _ ↦ Subtype.ext_iff
    ((LinearEquiv.funCongrLeft R R (Equiv.sigmaFiberEquiv κ)).trans
      (LinearEquiv.piCurry R fun m (_ : {i : ι // κ i = m}) ↦ R)).trans
      (LinearEquiv.piCongrRight fun m ↦ LinearEquiv.funCongrLeft R R (fiberEquiv m).symm)
  map_app' x := by
    -- Evaluate each fiber summand and reassemble the sum via `Finset.sum_fiberwise_of_maps_to`.
    rw [QuadraticMap.pi_apply, weightedSumSquares_apply]
    have hsum :
        ∑ m : Finset.univ.image k,
            s m.val * ∑ i : {i : ι // k i = m.val}, u i.val * (x i.val * x i.val) =
          ∑ i : ι, u i * s (k i) * (x i * x i) := by
      calc
        ∑ m : Finset.univ.image k,
            s m.val * ∑ i : {i : ι // k i = m.val}, u i.val * (x i.val * x i.val)
            = ∑ m ∈ Finset.univ.image k,
                s m * ∑ i with k i = m, u i * (x i * x i) := by
              rw [← Finset.sum_attach (Finset.univ.image k)]
              refine Finset.sum_congr rfl fun m _ ↦ ?_
              congr 1
              exact (Finset.sum_subtype {i : ι | k i = m.val} (fun _ ↦ by simp)
                (fun i ↦ u i * (x i * x i))).symm
        _ = ∑ m ∈ Finset.univ.image k,
              ∑ i with k i = m, u i * s (k i) * (x i * x i) := by
              refine Finset.sum_congr rfl fun m _ ↦ ?_
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl fun i hi ↦ ?_
              rw [(Finset.mem_filter.mp hi).2]
              ring
        _ = ∑ i : ι, u i * s (k i) * (x i * x i) :=
              Finset.sum_fiberwise_of_maps_to
                (fun i _ ↦ Finset.mem_image_of_mem k (Finset.mem_univ i)) _
    refine (Finset.sum_congr rfl fun m _ ↦ ?_).trans hsum
    rw [smul_apply, weightedSumSquares_apply, smul_eq_mul]
    refine congrArg (s m.val * ·) (Finset.sum_congr rfl fun i _ ↦ ?_)
    simp only [LinearMap.toFun_eq_coe, LinearEquiv.coe_coe, LinearEquiv.trans_apply,
      LinearEquiv.piCongrRight_apply, LinearEquiv.piCurry_apply, Sigma.curry,
      LinearEquiv.funCongrLeft_apply, LinearMap.funLeft_apply, Equiv.sigmaFiberEquiv_apply,
      Equiv.subtypeEquivRight_symm_apply_coe, smul_eq_mul]

/-- The forward map of `weightedSumSquaresMulFiberIsometryEquiv` restricts a vector to each fiber
of `k`. -/
@[simp]
theorem weightedSumSquaresMulFiberIsometryEquiv_apply {α : Type*} [DecidableEq α]
    (k : ι → α) (s : α → R) (u : ι → R) (x : ι → R)
    (m : Finset.univ.image k) (i : {i : ι // k i = m.val}) :
    weightedSumSquaresMulFiberIsometryEquiv k s u x m i = x i.val :=
  (rfl)

/-- The inverse map of `weightedSumSquaresMulFiberIsometryEquiv` reads the `i`-th coordinate from
the fiber over `k i`. -/
@[simp]
theorem weightedSumSquaresMulFiberIsometryEquiv_symm_apply {α : Type*} [DecidableEq α]
    (k : ι → α) (s : α → R) (u : ι → R)
    (y : (m : Finset.univ.image k) → {i : ι // k i = m.val} → R) (i : ι) :
    (weightedSumSquaresMulFiberIsometryEquiv k s u).symm y i =
      y ⟨k i, Finset.mem_image_of_mem k (Finset.mem_univ i)⟩ ⟨i, rfl⟩ := by
  have h := congrFun (congrFun ((weightedSumSquaresMulFiberIsometryEquiv k s u).apply_symm_apply y)
    ⟨k i, Finset.mem_image_of_mem k (Finset.mem_univ i)⟩) ⟨i, rfl⟩
  simpa only [weightedSumSquaresMulFiberIsometryEquiv_apply] using h

/-- Fiberwise equivalences of diagonal subforms assemble into an equivalence of scaled diagonal
forms `∑ᵢ wᵢ s(kᵢ) xᵢ²` and `∑ᵢ vᵢ s(kᵢ) xᵢ²`. -/
theorem equivalent_weightedSumSquares_mul_of_forall_fiber {α : Type*} [DecidableEq α]
    (k : ι → α) (s : α → R) (w v : ι → R)
    (hfiber : ∀ m : α,
      (weightedSumSquares R fun i : {i : ι // k i = m} ↦ w i.val).Equivalent
        (weightedSumSquares R fun i : {i : ι // k i = m} ↦ v i.val)) :
    (weightedSumSquares R fun i ↦ w i * s (k i)).Equivalent
      (weightedSumSquares R fun i ↦ v i * s (k i)) := by
  -- Split both forms into orthogonal sums indexed by the finite image of `k`, scale each fiber
  -- equivalence by `s m`, and recombine via `QuadraticMap.Equivalent.pi`.
  have hpi :
      (QuadraticMap.pi fun m : Finset.univ.image k ↦
          s m.val • weightedSumSquares R fun i : {i : ι // k i = m.val} ↦ w i.val).Equivalent
        (QuadraticMap.pi fun m : Finset.univ.image k ↦
          s m.val • weightedSumSquares R fun i : {i : ι // k i = m.val} ↦ v i.val) :=
    QuadraticMap.Equivalent.pi fun m ↦ by
      obtain ⟨e⟩ := hfiber m.val
      exact ⟨{ toLinearEquiv := e.toLinearEquiv
               map_app' := fun x ↦ by
                 simp only [smul_apply, LinearMap.toFun_eq_coe, LinearEquiv.coe_coe,
                   QuadraticMap.IsometryEquiv.coe_toLinearEquiv, e.map_app] }⟩
  exact QuadraticMap.Equivalent.trans ⟨weightedSumSquaresMulFiberIsometryEquiv k s w⟩
    (hpi.trans ⟨(weightedSumSquaresMulFiberIsometryEquiv k s v).symm⟩)

/-- A diagonal form with unit weights is the diagonal form with the underlying scalar weights. -/
theorem _root_.QuadraticMap.weightedSumSquares_units (w : ι → Rˣ) :
    QuadraticMap.weightedSumSquares R w
      = QuadraticMap.weightedSumSquares R fun i => ((w i : R)) := by
  ext x
  simp [QuadraticMap.weightedSumSquares_apply, Units.smul_def]

/-- Scaling a weighted sum of squares scales its weights. -/
theorem _root_.QuadraticMap.smul_weightedSumSquares {S T : Type*} [Monoid S] [Monoid T]
    [DistribMulAction S R] [SMulCommClass S R R]
    [DistribMulAction T R] [SMulCommClass T R R]
    [SMul S T] [IsScalarTower S T R] (c : S) (w : ι → T) :
    c • QuadraticMap.weightedSumSquares R w = QuadraticMap.weightedSumSquares R (c • w) := by
  ext x
  simp [Finset.smul_sum, smul_assoc]

/-- Evaluate a diagonal form on a single-coordinate vector `Pi.single i x`.

Not a `simp` lemma: Mathlib marks `QuadraticMap.weightedSumSquares_apply` as `@[simp]` for arbitrary
`v`, so a `simp` attribute here would form a critical pair with `weightedSumSquares_apply`. -/
theorem _root_.QuadraticMap.weightedSumSquares_apply_single {S : Type*} [Monoid S]
    [DistribMulAction S R] [SMulCommClass S R R] [DecidableEq ι] (w : ι → S) (i : ι) (x : R) :
    QuadraticMap.weightedSumSquares R w (Pi.single i x) = w i • (x * x) := by
  rw [QuadraticMap.weightedSumSquares_apply, Fintype.sum_eq_single i]
  · simp
  · intro j hji
    simp [hji]

/-- Distinct single-coordinate vectors are orthogonal for any diagonal quadratic form. -/
@[simp]
theorem _root_.QuadraticMap.isOrtho_weightedSumSquares_single {S : Type*} [Monoid S]
    [DistribMulAction S R] [SMulCommClass S R R] [DecidableEq ι] (w : ι → S)
    {i j : ι} (hij : i ≠ j) (x y : R) :
    (QuadraticMap.weightedSumSquares R w).IsOrtho (Pi.single i x) (Pi.single j y) := by
  rw [QuadraticMap.isOrtho_def]
  simp only [QuadraticMap.weightedSumSquares_apply, ← Finset.sum_add_distrib, Pi.add_apply]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rcases eq_or_ne k i with rfl | hki
  · simp [hij]
  rcases eq_or_ne k j with rfl | hkj
  · simp [hki]
  · simp [hki, hkj]

/-- Evaluate a binary diagonal form `⟨a, b⟩` on a vector of `R²`. -/
theorem _root_.QuadraticMap.weightedSumSquares_fin_two_apply (a b : R) (x : Fin 2 → R) :
    QuadraticMap.weightedSumSquares R ![a, b] x = a * (x 0 * x 0) + b * (x 1 * x 1) := by
  simp [QuadraticMap.weightedSumSquares_apply, Fin.sum_univ_two]

/-- Evaluate a diagonal form on a linear combination of three distinct coordinate vectors. -/
-- Apply before the generic `weightedSumSquares_apply` expansion.
@[simp high]
theorem _root_.QuadraticMap.weightedSumSquares_apply_three_single
    [DecidableEq ι] (a : ι → R)
    {i j k : ι} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (x y z : R) :
    QuadraticMap.weightedSumSquares R a
      (Pi.single i x + Pi.single j y + Pi.single k z) =
      a i * x ^ 2 + a j * y ^ 2 + a k * z ^ 2 := by
  classical
  rw [QuadraticMap.weightedSumSquares_apply,
    ← Finset.sum_subset (Finset.subset_univ {i, j, k})]
  · simp [Finset.sum_insert, hij, hik, hjk, smul_eq_mul, pow_two, add_assoc]
  · intro l _ hl
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hl
    simp [hl.1, hl.2.1, hl.2.2]

/-- A ternary solution with a nonzero third coordinate gives a nonzero isotropic vector in a
diagonal quadratic form. -/
theorem _root_.QuadraticMap.not_anisotropic_weightedSumSquares_of_ternary_eq_zero
    (a : ι → R) {i j k : ι} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    {x y z : R} (hz : z ≠ 0)
    (h : a i * x ^ 2 + a j * y ^ 2 + a k * z ^ 2 = 0) :
    ¬ (QuadraticMap.weightedSumSquares R a).Anisotropic := by
  classical
  let f : ι → R := Pi.single i x + Pi.single j y + Pi.single k z
  intro hanis
  have hf : f = 0 := hanis f <| by
    simpa [f, weightedSumSquares_apply_three_single a hij hik hjk x y z] using h
  have hz0 : z = 0 := by simpa [f, hik.symm, hjk.symm] using congrFun hf k
  exact hz hz0

end CommSemiring

section CommRing

variable [CommRing R] [Fintype ι]

/-- Negating a weighted sum of squares negates its weights. -/
theorem _root_.QuadraticMap.neg_weightedSumSquares {S : Type*} [Ring S] [Module S R]
    [SMulCommClass S R R] (w : ι → S) :
    -QuadraticMap.weightedSumSquares R w = QuadraticMap.weightedSumSquares R (-w) := by
  ext x
  simp [Finset.sum_neg_distrib]

end CommRing

section Discriminant

variable [CommRing R] [Invertible (2 : R)] [Fintype ι] [Fintype κ]

/-- The bilinear form associated with a diagonal quadratic form pairs the coordinates
diagonally: it is the weighted dot product. -/
@[simp]
theorem _root_.QuadraticMap.associated_weightedSumSquares {S : Type*} [Monoid S]
    [DistribMulAction S R] [SMulCommClass S R R] (w : ι → S) (x y : ι → R) :
    QuadraticMap.associated (R := R) (QuadraticMap.weightedSumSquares R w) x y =
      ∑ i, w i • (x i * y i) := by
  -- Each weight acts as multiplication by `w i • 1`. Then `weightedSumSquares R w` is by
  -- definition `∑ i, (w i • 1) • proj i i`, `associated` is linear, and `proj i i` is `linMulLin`
  -- of the `i`-th coordinate projection with itself.
  rw [QuadraticMap.weightedSumSquares_eq_of_smul_one_eq (w' := fun i ↦ w i • (1 : R))
    fun i ↦ by simp]
  simp [QuadraticMap.weightedSumSquares, QuadraticMap.proj, QuadraticMap.associated_linMulLin,
    mul_comm, mul_smul_one]

/-- The standard coordinate basis `Pi.basisFun R ι` is orthogonal for any diagonal quadratic
form. -/
theorem _root_.QuadraticMap.isOrthoᵢ_associated_weightedSumSquares {S : Type*} [Monoid S]
    [DistribMulAction S R] [SMulCommClass S R R] (w : ι → S) :
    (QuadraticMap.associated (QuadraticMap.weightedSumSquares R w)).IsOrthoᵢ
      (Pi.basisFun R ι) := by
  classical
  intro i j hij
  simpa [Function.onFun, Pi.basisFun_apply] using
    QuadraticMap.associated_isOrtho.mpr
      (QuadraticMap.isOrtho_weightedSumSquares_single w hij (1 : R) (1 : R))

/-- The matrix of a diagonal quadratic form in the standard basis is the diagonal matrix whose
entries are its weights acting on `1`, `w i • (1 : R)`. -/
@[simp]
theorem _root_.QuadraticForm.toMatrix'_weightedSumSquares {S : Type*} [Monoid S]
    [DistribMulAction S R] [SMulCommClass S R R] [DecidableEq ι] (w : ι → S) :
    QuadraticForm.toMatrix' (QuadraticMap.weightedSumSquares R w) =
      Matrix.diagonal fun i ↦ w i • (1 : R) := by
  ext i j
  rcases eq_or_ne i j with rfl | h
  · simp [QuadraticForm.toMatrix', Pi.single_apply]
  · simp [QuadraticForm.toMatrix', Pi.single_apply, h, h.symm]

/-- The discriminant of a diagonal quadratic form is the product of its weights acting on `1`,
`∏ i, w i • (1 : R)`. -/
@[simp]
theorem _root_.QuadraticForm.discr'_weightedSumSquares {S : Type*} [Monoid S]
    [DistribMulAction S R] [SMulCommClass S R R] [DecidableEq ι] (w : ι → S) :
    QuadraticForm.discr' (QuadraticMap.weightedSumSquares R w) = ∏ i, w i • (1 : R) := by
  rw [QuadraticForm.discr', QuadraticForm.toMatrix'_weightedSumSquares, Matrix.det_diagonal]

/-- A diagonal form with regular weights is nondegenerate when two is invertible. Over a
domain the hypothesis is that every weight is nonzero (`isRegular_iff_ne_zero`). -/
theorem _root_.QuadraticMap.nondegenerate_weightedSumSquares {w : ι → R}
    (hw : ∀ i, IsRegular (w i)) : (QuadraticMap.weightedSumSquares R w).Nondegenerate := by
  classical
  -- The associated bilinear form is the weighted dot product
  -- (`QuadraticMap.associated_weightedSumSquares`), so pairing a vector `x` with the basis vector
  -- `Pi.single i 1` isolates `w i * x i`, and regularity of `w i` forces `x i = 0`.
  rw [← QuadraticMap.nondegenerate_associated_iff,
    (QuadraticForm.associated_isSymm R _).isRefl.nondegenerate_iff_separatingLeft]
  intro x hx
  ext i
  simpa [QuadraticMap.associated_weightedSumSquares, Pi.single_apply,
    (hw i).left.mul_left_eq_zero_iff] using hx (Pi.single i 1)

/-- The form `⟨1, a, -a⟩` with `a` a unit is nondegenerate when two is invertible. -/
theorem _root_.QuadraticMap.nondegenerate_weightedSumSquares_one_self_neg (a : Rˣ) :
    (QuadraticMap.weightedSumSquares R ![1, (a : R), -(a : R)]).Nondegenerate :=
  QuadraticMap.nondegenerate_weightedSumSquares fun i => by
    fin_cases i
    · exact isRegular_one
    · exact a.isUnit.isRegular
    · exact (a.isUnit.neg).isRegular

/-- Isometric diagonal forms with unit weights have weight products differing by a square. An
isometry of the coordinate spaces changes the Gram matrix of a diagonal form by a congruence, so
it changes its determinant — the product of the weights — by the square of the determinant of that
isometry. -/
theorem isSquare_prod_mul_prod_of_equivalent {w : ι → Rˣ} {v : κ → Rˣ}
    (h : (QuadraticMap.weightedSumSquares R w).Equivalent
      (QuadraticMap.weightedSumSquares R v)) :
    IsSquare ((∏ i, w i) * ∏ i, v i) := by
  classical
  -- Over the zero ring every unit is a square; otherwise compare ranks to match the indices.
  rcases subsingleton_or_nontrivial R with _ | _
  · exact ⟨1, Subsingleton.elim _ _⟩
  obtain ⟨f⟩ := h
  let e : ι ≃ κ := Fintype.equivOfCardEq <| by
    simpa only [Module.finrank_fintype_fun_eq_card] using f.toLinearEquiv.finrank_eq
  -- Reindex `v` along `e`; then `g` is an isometry `⟨w⟩ ≅ ⟨v ∘ e⟩` on `ι → R`.
  let g := f.trans (QuadraticForm.isometryEquivWeightedSumSquaresReindex v e)
  have hg : weightedSumSquares R w =
      (weightedSumSquares R (v ∘ e)).comp g.toLinearEquiv.toLinearMap := by
    ext x
    exact (g.map_app x).symm
  -- Compare discriminants: `∏ w = det g ^ 2 * ∏ v`.
  have hdet := congrArg QuadraticForm.discr' hg
  simp only [QuadraticForm.discr'_comp, LinearMap.det_toMatrix', ← LinearEquiv.coe_det,
    QuadraticForm.discr'_weightedSumSquares, Units.smul_def, smul_eq_mul, mul_one,
    Function.comp_apply, Equiv.prod_comp e fun i => (v i : R)] at hdet
  refine ⟨LinearEquiv.det g.toLinearEquiv * ∏ i, v i, Units.ext ?_⟩
  push_cast
  rw [hdet]
  ring

end Discriminant

end TauCeti
