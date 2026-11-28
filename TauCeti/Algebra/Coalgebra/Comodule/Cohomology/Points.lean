/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Coalgebra.Comodule.Cohomology.Basic
public import TauCeti.Algebra.Coalgebra.Comodule.PointsAction
public import TauCeti.Algebra.Coalgebra.Convolution

/-!
# Evaluation of regular cochains in low degrees

Regular two- and three-cochains can be evaluated on algebra-valued points, retaining the
order of their Hopf factors. Evaluation intertwines the coefficient-first Hochschild
differential with the inhomogeneous group differential. In particular, the cocycle
identity is an identity on points of every value algebra, rather than just rational points.

The universal pair and triple detect equality of cochains, without any finiteness,
flatness or reducedness hypothesis. This is the dictionary needed to regard the factor
set of a regular section of a vector extension as an algebraic two-cocycle.

## References

* J. C. Jantzen, *Representations of Algebraic Groups*, Part I, §§4.14–4.16.
* J. S. Milne, *Algebraic Groups* (2017), §§15.9–15.10.
-/

public section

open scoped TensorProduct
open WithConv

namespace TauCeti.Comodule

universe u v w x

section Evaluation

variable {R : Type u} [CommSemiring R] {H : Type v} [Semiring H] [Algebra R H]
  (V : Type x) [AddCommMonoid V] [Module R V]
  {A : Type w} [CommSemiring A] [Algebra R A]

/-- Evaluation of a regular two-cochain at an ordered pair of algebra-valued points. -/
noncomputable def pointTwoCochain (g h : H →ₐ[R] A) :
    (V ⊗[R] H) ⊗[R] H →ₗ[R] A ⊗[R] V :=
  pointCochain V (Algebra.TensorProduct.lift g h (fun _ _ ↦ .all _ _)) ∘ₗ
    (TensorProduct.assoc R V H H).toLinearMap

@[simp]
theorem pointTwoCochain_tmul (g h : H →ₐ[R] A) (v : V) (x y : H) :
    pointTwoCochain V g h ((v ⊗ₜ[R] x) ⊗ₜ[R] y) = (g x * h y) ⊗ₜ[R] v := by
  simp [pointTwoCochain]

/-- Evaluating a coefficient-last tensor pushes its coordinate algebra through the pair. -/
@[simp]
theorem pointTwoCochain_assoc_symm_comm (g h : H →ₐ[R] A) (x : (H ⊗[R] H) ⊗[R] V) :
    pointTwoCochain V g h ((TensorProduct.assoc R V H H).symm
        (TensorProduct.comm R (H ⊗[R] H) V x)) =
      LinearMap.rTensor V
        (Algebra.TensorProduct.lift g h (fun _ _ ↦ .all _ _)).toLinearMap x := by
  rw [pointTwoCochain, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply, pointCochain_comm]

/-- Evaluation is natural in the value algebra. -/
@[simp]
theorem rTensor_pointTwoCochain {B : Type*} [CommSemiring B] [Algebra R B]
    (φ : A →ₐ[R] B) (g h : H →ₐ[R] A) (c : (V ⊗[R] H) ⊗[R] H) :
    LinearMap.rTensor V φ.toLinearMap (pointTwoCochain V g h c) =
      pointTwoCochain V (φ.comp g) (φ.comp h) c := by
  induction c using TensorProduct.inductionOn with
  | tmul b y =>
    induction b using TensorProduct.inductionOn with
    | tmul v x => simp
    | add b b' hb hb' => simp_all only [TensorProduct.add_tmul, map_add]
  | add c c' hc hc' => simp_all only [map_add]

/-- Evaluation of a regular three-cochain at an ordered triple of algebra-valued points. -/
noncomputable def pointThreeCochain (g h j : H →ₐ[R] A) :
    ((V ⊗[R] H) ⊗[R] H) ⊗[R] H →ₗ[R] A ⊗[R] V :=
  pointCochain V
      (Algebra.TensorProduct.lift
        (Algebra.TensorProduct.lift g h (fun _ _ ↦ .all _ _)) j (fun _ _ ↦ .all _ _)) ∘ₗ
    (TensorProduct.assoc R V (H ⊗[R] H) H).toLinearMap ∘ₗ
      (TensorProduct.assoc R V H H).toLinearMap.rTensor H

@[simp]
theorem pointThreeCochain_tmul (g h j : H →ₐ[R] A) (v : V) (x y z : H) :
    pointThreeCochain V g h j (((v ⊗ₜ[R] x) ⊗ₜ[R] y) ⊗ₜ[R] z) =
      (g x * h y * j z) ⊗ₜ[R] v := by
  simp [pointThreeCochain]

/-- Evaluating the last factor of a two-cochain multiplies the value of its first factor. -/
theorem pointTwoCochain_tmul_right (g h : H →ₐ[R] A) (b : V ⊗[R] H) (y : H) :
    pointTwoCochain V g h (b ⊗ₜ[R] y) = h y • pointCochain V g b := by
  induction b using TensorProduct.inductionOn with
  | tmul v x => simp [TensorProduct.smul_tmul', mul_comm]
  | add b b' hb hb' => simp_all only [TensorProduct.add_tmul, map_add, smul_add]

/-- Evaluating the last factor of a three-cochain multiplies the value of its first factor. -/
theorem pointThreeCochain_tmul_right (g h j : H →ₐ[R] A)
    (c : (V ⊗[R] H) ⊗[R] H) (z : H) :
    pointThreeCochain V g h j (c ⊗ₜ[R] z) = j z • pointTwoCochain V g h c := by
  induction c using TensorProduct.inductionOn with
  | tmul b y =>
    induction b using TensorProduct.inductionOn with
    | tmul v x => simp [TensorProduct.smul_tmul', mul_comm]
    | add b b' hb hb' => simp_all only [TensorProduct.add_tmul, map_add, smul_add]
  | add c c' hc hc' => simp_all only [TensorProduct.add_tmul, map_add, smul_add]

/-- The last two Hopf factors of a three-cochain can be evaluated together. -/
theorem pointThreeCochain_assoc_symm (g h j : H →ₐ[R] A)
    (b : V ⊗[R] H) (t : H ⊗[R] H) :
    pointThreeCochain V g h j ((TensorProduct.assoc R (V ⊗[R] H) H H).symm
        (b ⊗ₜ[R] t)) =
      Algebra.TensorProduct.lift h j (fun _ _ ↦ .all _ _) t • pointCochain V g b := by
  induction t using TensorProduct.inductionOn with
  | tmul y z =>
    simp only [TensorProduct.assoc_symm_tmul, pointThreeCochain_tmul_right,
      pointTwoCochain_tmul_right, Algebra.TensorProduct.lift_tmul, mul_smul]
    exact smul_comm _ _ _
  | add t t' ht ht' => simp_all only [TensorProduct.tmul_add, map_add, add_smul]

end Evaluation

section Universal

variable {R : Type u} [CommSemiring R] {H : Type v} [CommSemiring H] [Algebra R H]
  (V : Type x) [AddCommMonoid V] [Module R V]

/-- The universal pair evaluates a two-cochain by moving its coefficient to the last factor. -/
theorem pointTwoCochain_include (c : (V ⊗[R] H) ⊗[R] H) :
    pointTwoCochain V (Algebra.TensorProduct.includeLeft (S := R))
        Algebra.TensorProduct.includeRight c =
      TensorProduct.comm R V _ (TensorProduct.assoc R V H H c) := by
  induction c using TensorProduct.inductionOn with
  | tmul b y =>
    induction b using TensorProduct.inductionOn with
    | tmul v x => simp
    | add b b' hb hb' => simp_all only [TensorProduct.add_tmul, map_add]
  | add c c' hc hc' => simp_all only [map_add]

/-- Evaluation at the universal pair detects equality of two-cochains. -/
theorem pointTwoCochain_include_injective :
    Function.Injective (pointTwoCochain V
      (Algebra.TensorProduct.includeLeft (R := R) (S := R) (A := H) (B := H))
      Algebra.TensorProduct.includeRight) := by
  intro c c' h
  rw [pointTwoCochain_include, pointTwoCochain_include] at h
  exact (TensorProduct.assoc R V H H).injective
    ((TensorProduct.comm R V (H ⊗[R] H)).injective h)

/-- The universal triple evaluates a three-cochain by moving its coefficient to the end. -/
theorem pointThreeCochain_include (c : ((V ⊗[R] H) ⊗[R] H) ⊗[R] H) :
    pointThreeCochain V
        ((Algebra.TensorProduct.includeLeft (S := R)).comp
          (Algebra.TensorProduct.includeLeft (S := R)))
        ((Algebra.TensorProduct.includeLeft (S := R)).comp Algebra.TensorProduct.includeRight)
        Algebra.TensorProduct.includeRight c =
      TensorProduct.comm R V _
        (TensorProduct.assoc R V (H ⊗[R] H) H
          ((TensorProduct.assoc R V H H).toLinearMap.rTensor H c)) := by
  induction c using TensorProduct.inductionOn with
  | tmul b z =>
    induction b using TensorProduct.inductionOn with
    | tmul a y =>
      induction a using TensorProduct.inductionOn with
      | tmul v x => simp
      | add a a' ha ha' => simp_all only [TensorProduct.add_tmul, map_add]
    | add b b' hb hb' => simp_all only [TensorProduct.add_tmul, map_add]
  | add c c' hc hc' => simp_all only [map_add]

/-- Evaluation at the universal triple detects equality of three-cochains. -/
theorem pointThreeCochain_include_injective :
    Function.Injective (pointThreeCochain V
      ((Algebra.TensorProduct.includeLeft (R := R) (S := R) (A := H ⊗[R] H) (B := H)).comp
        (Algebra.TensorProduct.includeLeft (S := R)))
      ((Algebra.TensorProduct.includeLeft (S := R)).comp Algebra.TensorProduct.includeRight)
      Algebra.TensorProduct.includeRight) := by
  intro c c' h
  rw [pointThreeCochain_include, pointThreeCochain_include] at h
  exact ((TensorProduct.assoc R V H H).rTensor H).injective
    ((TensorProduct.assoc R V (H ⊗[R] H) H).injective
      ((TensorProduct.comm R V ((H ⊗[R] H) ⊗[R] H)).injective h))

end Universal

section Naturality

variable {R : Type u} [CommSemiring R] {H : Type v} [CommSemiring H] [Algebra R H]
  (V : Type x) [AddCommMonoid V] [Module R V]

/-- A natural vector-valued function on pairs of points is evaluation of a unique regular
two-cochain. Its coefficients are recovered from its value at the universal pair. -/
theorem existsUnique_pointTwoCochain_of_naturality
    (f : ∀ (A : Type v) [CommSemiring A] [Algebra R A],
      (H →ₐ[R] A) → (H →ₐ[R] A) → A ⊗[R] V)
    (hf : ∀ (A B : Type v) [CommSemiring A] [Algebra R A] [CommSemiring B] [Algebra R B]
      (φ : A →ₐ[R] B) (g h : H →ₐ[R] A),
      LinearMap.rTensor V φ.toLinearMap (f A g h) = f B (φ.comp g) (φ.comp h)) :
    ∃! c : (V ⊗[R] H) ⊗[R] H,
      ∀ (A : Type v) [CommSemiring A] [Algebra R A] (g h : H →ₐ[R] A),
        f A g h = pointTwoCochain V g h c := by
  let c := (TensorProduct.assoc R V H H).symm
    (TensorProduct.comm R (H ⊗[R] H) V
      (f (H ⊗[R] H) (Algebra.TensorProduct.includeLeft (S := R))
        Algebra.TensorProduct.includeRight))
  have hc : pointTwoCochain V (Algebra.TensorProduct.includeLeft (S := R))
      Algebra.TensorProduct.includeRight c =
        f (H ⊗[R] H) (Algebra.TensorProduct.includeLeft (S := R))
          Algebra.TensorProduct.includeRight := by
    rw [pointTwoCochain_include]
    simp [c]
  refine ⟨c, ?_, ?_⟩
  · intro A _ _ g h
    have hn := hf (H ⊗[R] H) A
      (Algebra.TensorProduct.lift g h (fun _ _ ↦ Commute.all _ _))
      (Algebra.TensorProduct.includeLeft (S := R)) Algebra.TensorProduct.includeRight
    rw [← hc, rTensor_pointTwoCochain] at hn
    simpa using hn.symm
  · intro c' hc'
    apply pointTwoCochain_include_injective V
    rw [hc, ← hc' (H ⊗[R] H)]

end Naturality

section Differential

variable {R : Type u} [CommRing R] {H : Type v} [Ring H] [Bialgebra R H]
  (V : Type v) [AddCommGroup V] [Module R V] [Comodule R H V]
  {A : Type w} [CommRing A] [Algebra R A]

/-- Evaluation of the degree-one differential is the inhomogeneous coboundary
`g • b(h) - b(gh) + b(g)`. -/
theorem pointTwoCochain_d_one (g h : WithConv (H →ₐ[R] A)) (b : V ⊗[R] H) :
    pointTwoCochain V g.ofConv h.ofConv (Cohomology.d R H V 1 b) =
      endOfPoint V g.ofConv (pointCochain V h.ofConv b) -
        pointCochain V (g * h).ofConv b + pointCochain V g.ofConv b := by
  induction b using TensorProduct.inductionOn with
  | add b b' hb hb' => simp only [map_add, hb, hb']; abel
  | tmul v x =>
    rw [Cohomology.d_succ_tmul, Cohomology.d_zero_apply]
    simp only [Nat.zero_add, pow_one, neg_smul, one_smul, map_sub, map_add, map_neg,
      TensorProduct.sub_tmul, pointCochain_tmul]
    have hcoact :
        pointTwoCochain V g.ofConv h.ofConv ((coact (R := R) (C := H) v) ⊗ₜ[R] x) =
          endOfPoint V g.ofConv (h.ofConv x ⊗ₜ[R] v) := by
      rw [endOfPoint_tmul]
      induction coact (R := R) (C := H) v using TensorProduct.inductionOn with
      | tmul w y => simp [TensorProduct.smul_tmul', mul_comm]
      | add c c' hc hc' => simp_all only [TensorProduct.add_tmul, map_add, smul_add]
    have hcomul :
        pointTwoCochain V g.ofConv h.ofConv
            ((TensorProduct.assoc R V H H).symm (v ⊗ₜ[R] Coalgebra.comul x)) =
          (g * h).ofConv x ⊗ₜ[R] v := by
      simp only [pointTwoCochain, LinearMap.comp_apply, LinearEquiv.coe_coe,
        LinearEquiv.apply_symm_apply, pointCochain_tmul]
      have hh := (Algebra.TensorProduct.lift g.ofConv h.ofConv
        (fun _ _ ↦ Commute.all _ _)).toConv_comp_comulAlgHom
      simpa using congrArg (fun q ↦ q.ofConv x ⊗ₜ[R] v) hh
    simp only [hcoact, hcomul, pointTwoCochain_tmul, map_one, one_mul, mul_one]
    abel

/-- Evaluation of the degree-two differential is the inhomogeneous cocycle expression. -/
theorem pointThreeCochain_d_two (g h j : WithConv (H →ₐ[R] A))
    (c : (V ⊗[R] H) ⊗[R] H) :
    pointThreeCochain V g.ofConv h.ofConv j.ofConv (Cohomology.d R H V 2 c) =
      endOfPoint V g.ofConv (pointTwoCochain V h.ofConv j.ofConv c) -
        pointTwoCochain V (g * h).ofConv j.ofConv c +
        pointTwoCochain V g.ofConv (h * j).ofConv c -
        pointTwoCochain V g.ofConv h.ofConv c := by
  induction c using TensorProduct.inductionOn with
  | add c c' hc hc' => simp only [map_add, hc, hc']; abel
  | tmul b y =>
    have hcomul :
        Algebra.TensorProduct.lift h.ofConv j.ofConv (fun _ _ ↦ Commute.all _ _)
            (Coalgebra.comul y) = (h * j).ofConv y := by
      have hh := (Algebra.TensorProduct.lift h.ofConv j.ofConv
        (fun _ _ ↦ Commute.all _ _)).toConv_comp_comulAlgHom
      simpa using congrArg (fun q ↦ q.ofConv y) hh
    rw [Cohomology.d_succ_tmul]
    simp only [Nat.reduceAdd, neg_one_sq, one_smul, map_add, map_sub,
      pointThreeCochain_tmul_right,
      pointThreeCochain_assoc_symm, hcomul, pointTwoCochain_tmul_right, map_one,
      one_smul, map_smul, smul_sub]
    rw [pointTwoCochain_d_one V g h]
    simp only [smul_add, smul_sub]
    abel

end Differential

section Detection

variable {R : Type u} [CommRing R] {H : Type v} [CommRing H] [Bialgebra R H]
  (V : Type v) [AddCommGroup V] [Module R V] [Comodule R H V]

/-- A regular two-cochain is closed exactly when its values satisfy the group cocycle
identity over every commutative value algebra. The test uses no field-point density. -/
theorem d_two_eq_zero_iff (c : (V ⊗[R] H) ⊗[R] H) :
    Cohomology.d R H V 2 c = 0 ↔
      ∀ (A : Type v) [CommRing A] [Algebra R A] (g h j : WithConv (H →ₐ[R] A)),
        endOfPoint V g.ofConv (pointTwoCochain V h.ofConv j.ofConv c) -
          pointTwoCochain V (g * h).ofConv j.ofConv c +
          pointTwoCochain V g.ofConv (h * j).ofConv c -
          pointTwoCochain V g.ofConv h.ofConv c = 0 := by
  constructor
  · intro hc A _ _ g h j
    rw [← pointThreeCochain_d_two V g h j, hc, map_zero]
  · intro hc
    apply pointThreeCochain_include_injective V
    let g := toConv ((Algebra.TensorProduct.includeLeft
      (R := R) (S := R) (A := H ⊗[R] H) (B := H)).comp
        (Algebra.TensorProduct.includeLeft (S := R)))
    let h := toConv ((Algebra.TensorProduct.includeLeft
      (R := R) (S := R) (A := H ⊗[R] H) (B := H)).comp
        Algebra.TensorProduct.includeRight)
    let j := toConv (Algebra.TensorProduct.includeRight
      (R := R) (A := H ⊗[R] H) (B := H))
    rw [map_zero]
    exact (pointThreeCochain_d_two V g h j c).trans (hc _ g h j)

/-- Equality to a regular coboundary can be checked on all pairs of algebra-valued points. -/
theorem d_one_eq_iff (b : V ⊗[R] H) (c : (V ⊗[R] H) ⊗[R] H) :
    Cohomology.d R H V 1 b = c ↔
      ∀ (A : Type v) [CommRing A] [Algebra R A] (g h : WithConv (H →ₐ[R] A)),
        endOfPoint V g.ofConv (pointCochain V h.ofConv b) -
          pointCochain V (g * h).ofConv b + pointCochain V g.ofConv b =
            pointTwoCochain V g.ofConv h.ofConv c := by
  constructor
  · intro hb A _ _ g h
    rw [← pointTwoCochain_d_one V g h, hb]
  · intro hb
    apply pointTwoCochain_include_injective V
    let g := toConv (Algebra.TensorProduct.includeLeft (R := R) (S := R) (A := H) (B := H))
    let h := toConv (Algebra.TensorProduct.includeRight (R := R) (A := H) (B := H))
    exact (pointTwoCochain_d_one V g h b).trans (hb _ g h)

end Detection

end TauCeti.Comodule
