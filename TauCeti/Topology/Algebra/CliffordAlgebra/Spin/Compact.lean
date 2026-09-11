/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.QuadraticForm.CartanDieudonne.Basic
public import TauCeti.Topology.Algebra.CliffordAlgebra.Spin.ReflectionPair
public import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Vector.Basic

/-!
# Compactness of compact real Spin groups

Every element of a positive-dimensional compact real Spin group is a product of uniformly many
normalized reflection-pair lifts. The normalized vectors range over a Euclidean unit sphere, so a
fixed finite product of pairs of spheres maps continuously and surjectively onto the Spin group.
Compactness follows.

The uniform bound comes from the bounded Cartan--Dieudonne factorization. Its reflection word has
even length over the special orthogonal group, hence can be grouped into pairs. One additional pair
accounts for the possible scalar `-1` in the kernel of the Spin projection. Repeated equal vectors
pad the product without changing it.

## Main result

* `CliffordAlgebra.instCompactSpaceRealCliffordSpinGroupZero` proves that `Spin(n)` is compact in
  every positive dimension.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, Section 2.
-/

public section

open Metric
open scoped Topology

namespace CliffordAlgebra

open TauCeti

noncomputable section

private abbrev realCliffordUnitSphere (n : ℕ) :=
  sphere (0 : EuclideanSpace ℝ (Fin n)) 1

private theorem realCliffordForm_zero_euclidean_norm_sq (n : ℕ)
    (u : EuclideanSpace ℝ (Fin n)) :
    realCliffordForm n 0 (EuclideanSpace.equiv (Fin n) ℝ u) = ‖u‖ ^ 2 := by
  rw [realCliffordForm_zero_eq_weightedSumSquares_one,
    QuadraticMap.weightedSumSquares_apply]
  simp only [Pi.one_apply, one_smul, PiLp.continuousLinearEquiv_apply]
  simpa only [pow_two] using (EuclideanSpace.real_norm_sq_eq u).symm

private theorem realCliffordUnitSphere_norm (n : ℕ) (u : realCliffordUnitSphere n) :
    realCliffordForm n 0 (EuclideanSpace.equiv (Fin n) ℝ u) = 1 := by
  rw [realCliffordForm_zero_euclidean_norm_sq]
  have hu : ‖(u : EuclideanSpace ℝ (Fin n))‖ = 1 := by
    simpa only [mem_sphere, dist_zero_right] using u.2
  rw [hu, one_pow]

private theorem euclidean_norm_eq_one_of_realCliffordForm_zero_eq_one {n : ℕ}
    {v : Fin n → ℝ} (hv : realCliffordForm n 0 v = 1) :
    ‖(EuclideanSpace.equiv (Fin n) ℝ).symm v‖ = 1 := by
  have hsquare : ‖(EuclideanSpace.equiv (Fin n) ℝ).symm v‖ ^ 2 = 1 := by
    rw [← realCliffordForm_zero_euclidean_norm_sq]
    simpa only [ContinuousLinearEquiv.apply_symm_apply] using hv
  nlinarith [norm_nonneg ((EuclideanSpace.equiv (Fin n) ℝ).symm v)]

private theorem normalizedVector_norm_one {n : ℕ} (v : Fin n → ℝ)
    (hv : realCliffordForm n 0 v ≠ 0) :
    realCliffordForm n 0 ((Real.sqrt (realCliffordForm n 0 v))⁻¹ • v) = 1 := by
  have hv0 : v ≠ 0 := fun h => hv (by simp [h])
  have hpos : 0 < realCliffordForm n 0 v :=
    posDef_realCliffordForm_zero n v hv0
  rw [QuadraticMap.map_smul, smul_eq_mul]
  calc
    (Real.sqrt (realCliffordForm n 0 v))⁻¹ *
          (Real.sqrt (realCliffordForm n 0 v))⁻¹ * realCliffordForm n 0 v =
        (Real.sqrt (realCliffordForm n 0 v) *
          Real.sqrt (realCliffordForm n 0 v))⁻¹ * realCliffordForm n 0 v := by
      rw [mul_inv_rev]
    _ = (realCliffordForm n 0 v)⁻¹ * realCliffordForm n 0 v := by
      rw [Real.mul_self_sqrt hpos.le]
    _ = 1 := inv_mul_cancel₀ hpos.ne'

private def normalizedVectorSphere {n : ℕ} (v : Fin n → ℝ)
    (hv : realCliffordForm n 0 v ≠ 0) : realCliffordUnitSphere n :=
  ⟨(EuclideanSpace.equiv (Fin n) ℝ).symm
      ((Real.sqrt (realCliffordForm n 0 v))⁻¹ • v), by
    rw [mem_sphere, dist_zero_right]
    exact euclidean_norm_eq_one_of_realCliffordForm_zero_eq_one
      (normalizedVector_norm_one v hv)⟩

private theorem reflectionOrthogonal_eq_of_vector_eq {n : ℕ} (v w : Fin n → ℝ)
    [Invertible (realCliffordForm n 0 v)] [Invertible (realCliffordForm n 0 w)]
    (h : v = w) :
    QuadraticMap.reflectionOrthogonal (realCliffordForm n 0) v =
      QuadraticMap.reflectionOrthogonal (realCliffordForm n 0) w := by
  subst w
  congr
  exact Subsingleton.elim _ _

private theorem reflectionOrthogonal_normalizedVectorSphere {n : ℕ}
    (v : Fin n → ℝ) [Invertible (realCliffordForm n 0 v)] :
    let u := normalizedVectorSphere v (isUnit_of_invertible _).ne_zero
    let _ : Invertible (realCliffordForm n 0
        (EuclideanSpace.equiv (Fin n) ℝ u)) :=
      (realCliffordUnitSphere_norm n u).symm ▸ invertibleOne
    QuadraticMap.reflectionOrthogonal (realCliffordForm n 0)
        (EuclideanSpace.equiv (Fin n) ℝ u) =
      QuadraticMap.reflectionOrthogonal (realCliffordForm n 0) v := by
  dsimp only
  have hv0 : v ≠ 0 := fun h => (isUnit_of_invertible (realCliffordForm n 0 v)).ne_zero (by
    simp [h])
  have hpos : 0 < realCliffordForm n 0 v := posDef_realCliffordForm_zero n v hv0
  let _ : Invertible (Real.sqrt (realCliffordForm n 0 v))⁻¹ :=
    invertibleOfNonzero (inv_ne_zero (Real.sqrt_pos.2 hpos).ne')
  let _ : Invertible (realCliffordForm n 0
      (EuclideanSpace.equiv (Fin n) ℝ
        (normalizedVectorSphere v (isUnit_of_invertible _).ne_zero))) :=
    (realCliffordUnitSphere_norm n
      (normalizedVectorSphere v (isUnit_of_invertible _).ne_zero)).symm ▸ invertibleOne
  let _ : Invertible (realCliffordForm n 0
      ((Real.sqrt (realCliffordForm n 0 v))⁻¹ • v)) := by
    rw [QuadraticMap.map_smul]
    let _ : Invertible ((Real.sqrt (realCliffordForm n 0 v))⁻¹ *
        (Real.sqrt (realCliffordForm n 0 v))⁻¹) := invertibleMul _ _
    exact invertibleMul _ _
  have hvec : EuclideanSpace.equiv (Fin n) ℝ
      (normalizedVectorSphere v (isUnit_of_invertible _).ne_zero) =
      (Real.sqrt (realCliffordForm n 0 v))⁻¹ • v := by
    simp only [normalizedVectorSphere, ContinuousLinearEquiv.apply_symm_apply]
  exact (reflectionOrthogonal_eq_of_vector_eq _ _ hvec).trans
    (QuadraticMap.reflectionOrthogonal_smul_eq (realCliffordForm n 0) v _)

private def unitSphereReflection (n : ℕ) (u : realCliffordUnitSphere n) :
    QuadraticMap.orthogonalGroup (realCliffordForm n 0) :=
  let _ : Invertible (realCliffordForm n 0
      (EuclideanSpace.equiv (Fin n) ℝ u)) :=
    (realCliffordUnitSphere_norm n u).symm ▸ invertibleOne
  QuadraticMap.reflectionOrthogonal (realCliffordForm n 0)
    (EuclideanSpace.equiv (Fin n) ℝ u)

private theorem exists_unitSphere_reflection_list
    (n : ℕ) (l : List (QuadraticMap.orthogonalGroup (realCliffordForm n 0)))
    (hl : ∀ r ∈ l, ∃ (v : Fin n → ℝ) (_ : Invertible (realCliffordForm n 0 v)),
      QuadraticMap.reflectionOrthogonal (realCliffordForm n 0) v = r) :
    ∃ u : List (realCliffordUnitSphere n), u.length = l.length ∧
      (u.map (unitSphereReflection n)).prod = l.prod := by
  induction l with
  | nil => exact ⟨[], rfl, by simp⟩
  | cons r l ih =>
      obtain ⟨v, hv, hvr⟩ := hl r (by simp)
      let _ : Invertible (realCliffordForm n 0 v) := hv
      have htail : ∀ s ∈ l, ∃ (w : Fin n → ℝ)
          (_ : Invertible (realCliffordForm n 0 w)),
          QuadraticMap.reflectionOrthogonal (realCliffordForm n 0) w = s := by
        intro s hs
        exact hl s (by simp [hs])
      obtain ⟨u, hulen, huprod⟩ := ih htail
      let w := normalizedVectorSphere v (isUnit_of_invertible _).ne_zero
      refine ⟨w :: u, by simp [hulen], ?_⟩
      simp only [List.map_cons, List.prod_cons, huprod]
      rw [← hvr]
      exact congrArg (fun s => s * l.prod)
        (reflectionOrthogonal_normalizedVectorSphere v)

private def pairList {A : Type*} : List A → List (A × A)
  | a :: b :: l => (a, b) :: pairList l
  | _ => []

private theorem pairList_map_prod {A B : Type*} [Monoid B] (f : A → B) :
    ∀ (l : List A), Even l.length →
      ((pairList l).map fun p => f p.1 * f p.2).prod = (l.map f).prod
  | [], _ => by simp [pairList]
  | [_], hl => by simp at hl
  | a :: b :: l, hl => by
      have htail : Even l.length := by
        obtain ⟨k, hk⟩ := hl
        use k - 1
        simp only [List.length_cons] at hk
        omega
      simp only [pairList, List.map_cons, List.prod_cons, pairList_map_prod f l htail, mul_assoc]

private theorem pairList_length {A : Type*} : ∀ (l : List A),
    2 * (pairList l).length ≤ l.length
  | [] => by simp [pairList]
  | [_] => by simp [pairList]
  | _ :: _ :: l => by
      have htail := pairList_length l
      simp only [pairList, List.length_cons]
      omega

private def realCliffordSpinSpherePair (n : ℕ)
    (p : realCliffordUnitSphere n × realCliffordUnitSphere n) :
    realCliffordSpinGroupZero n :=
  spinReflectionPair (realCliffordForm n 0)
    (EuclideanSpace.equiv (Fin n) ℝ p.1)
    (EuclideanSpace.equiv (Fin n) ℝ p.2)
    (realCliffordUnitSphere_norm n p.1) (realCliffordUnitSphere_norm n p.2)

private theorem continuous_realCliffordSpinSpherePair (n : ℕ) :
    Continuous (realCliffordSpinSpherePair n) := by
  apply continuous_induced_rng.mpr
  rw [show Subtype.val ∘ realCliffordSpinSpherePair n =
      fun p : realCliffordUnitSphere n × realCliffordUnitSphere n =>
        ι (realCliffordForm n 0) (EuclideanSpace.equiv (Fin n) ℝ p.1) *
          ι (realCliffordForm n 0) (EuclideanSpace.equiv (Fin n) ℝ p.2) by
    funext p
    simp only [Function.comp_apply, realCliffordSpinSpherePair, coe_spinReflectionPair]]
  exact ((continuous_ι (realCliffordForm n 0)).comp
      ((EuclideanSpace.equiv (Fin n) ℝ).continuous.comp
        (continuous_subtype_val.comp continuous_fst))).mul
    ((continuous_ι (realCliffordForm n 0)).comp
      ((EuclideanSpace.equiv (Fin n) ℝ).continuous.comp
        (continuous_subtype_val.comp continuous_snd)))

private theorem spinToOrthogonal_realCliffordSpinSpherePair (n : ℕ)
    (p : realCliffordUnitSphere n × realCliffordUnitSphere n) :
    spinToOrthogonal (realCliffordForm n 0) (realCliffordSpinSpherePair n p) =
      unitSphereReflection n p.1 * unitSphereReflection n p.2 := by
  exact spinToOrthogonal_spinReflectionPair _ _ _ _ _

private def realCliffordSpinCompactParam (n : ℕ) :
    (Fin (n + 1) → realCliffordUnitSphere n × realCliffordUnitSphere n) →
      realCliffordSpinGroupZero n :=
  fun f => (List.ofFn fun i => realCliffordSpinSpherePair n (f i)).prod

private theorem continuous_realCliffordSpinCompactParam (n : ℕ) :
    Continuous (realCliffordSpinCompactParam n) := by
  change Continuous (fun f : Fin (n + 1) →
      realCliffordUnitSphere n × realCliffordUnitSphere n =>
    (List.ofFn fun i => realCliffordSpinSpherePair n (f i)).prod)
  have h := continuous_list_prod (List.ofFn fun i : Fin (n + 1) => i)
    (fun i _ => (continuous_realCliffordSpinSpherePair n).comp (continuous_apply i))
  simpa only [List.map_ofFn, Function.comp_def] using h

private def negUnitSphere {n : ℕ} (u : realCliffordUnitSphere n) :
    realCliffordUnitSphere n :=
  ⟨-u, by simpa only [mem_sphere, dist_zero_right, norm_neg] using u.2⟩

private theorem realCliffordSpinSpherePair_self (n : ℕ) (u : realCliffordUnitSphere n) :
    realCliffordSpinSpherePair n (u, u) = 1 :=
  spinReflectionPair_self _ _ _

private theorem realCliffordSpinSpherePair_neg (n : ℕ) [NeZero n]
    (u : realCliffordUnitSphere n) :
    realCliffordSpinSpherePair n (u, negUnitSphere u) =
      spinGroup.negOne (realCliffordForm n 0) (nondegenerate_realCliffordForm n 0).ne_zero := by
  apply Subtype.ext
  simp only [realCliffordSpinSpherePair, coe_spinReflectionPair, negUnitSphere,
    ContinuousLinearEquiv.map_neg, spinGroup.coe_negOne]
  rw [map_neg, mul_neg, ι_sq_scalar, realCliffordUnitSphere_norm]
  simp

private def firstUnitSphere (n : ℕ) [NeZero n] : realCliffordUnitSphere n := by
  let i : Fin n := ⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩
  let v : Fin n → ℝ := Pi.single i 1
  have hv : realCliffordForm n 0 v = 1 := by
    rw [realCliffordForm_zero_eq_weightedSumSquares_one,
      QuadraticMap.weightedSumSquares_apply]
    classical
    rw [Finset.sum_eq_single i]
    · simp [v]
    · intro b _ hbi
      simp [v, hbi]
    · simp
  exact ⟨(EuclideanSpace.equiv (Fin n) ℝ).symm v, by
    rw [mem_sphere, dist_zero_right]
    exact euclidean_norm_eq_one_of_realCliffordForm_zero_eq_one hv⟩

private theorem exists_sphere_pair_list_prod_eq (n : ℕ) [NeZero n]
    (x : realCliffordSpinGroupZero n) :
    ∃ p : List (realCliffordUnitSphere n × realCliffordUnitSphere n),
      p.length ≤ n + 1 ∧ (p.map (realCliffordSpinSpherePair n)).prod = x := by
  let Q := realCliffordForm n 0
  let g := spinToSpecialOrthogonal Q x
  obtain ⟨l, hlrefl, hllen, hleven, hlprod⟩ :=
    QuadraticMap.exists_even_reflection_list_prod_eq Q
      (nondegenerate_realCliffordForm n 0) g
  obtain ⟨u, hulen, huprod⟩ := exists_unitSphere_reflection_list n l hlrefl
  let p := pairList u
  let z : realCliffordSpinGroupZero n := (p.map (realCliffordSpinSpherePair n)).prod
  have hpmap : (p.map fun q => unitSphereReflection n q.1 *
      unitSphereReflection n q.2).prod = l.prod := by
    calc
      _ = (u.map (unitSphereReflection n)).prod :=
        pairList_map_prod (unitSphereReflection n) u (by simpa [hulen])
      _ = l.prod := huprod
  have hzorth : spinToOrthogonal Q z = l.prod := by
    rw [← hpmap]
    simp only [z, map_list_prod, List.map_map]
    congr 1
    apply List.map_congr_left
    intro q _
    exact spinToOrthogonal_realCliffordSpinSpherePair n q
  have hzorthg : spinToOrthogonal Q z =
      ⟨g, (QuadraticMap.mem_specialOrthogonalGroup_iff.mp g.2).1⟩ :=
    hzorth.trans hlprod
  have hzproj : spinToSpecialOrthogonal Q z = g := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro m
    simpa only [coe_spinToSpecialOrthogonal_apply, coe_spinToOrthogonal_apply] using
      congrArg (fun h : QuadraticMap.orthogonalGroup Q => h.1 m)
        hzorthg
  have hplen : p.length ≤ n := by
    have hpair := pairList_length u
    rw [hulen] at hpair
    simpa using (Nat.le_of_mul_le_mul_left (hpair.trans hllen) (by decide : 0 < 2))
  rcases eq_or_eq_negOne_mul_of_spinToSpecialOrthogonal_eq Q
      (nondegenerate_realCliffordForm n 0) x z (by simpa only [g] using hzproj.symm) with hx | hx
  · exact ⟨p, hplen.trans (by omega), hx.symm⟩
  · let e := firstUnitSphere n
    refine ⟨(e, negUnitSphere e) :: p, by simp only [List.length_cons]; omega, ?_⟩
    rw [List.map_cons, List.prod_cons, realCliffordSpinSpherePair_neg]
    exact hx.symm

private theorem surjective_realCliffordSpinCompactParam (n : ℕ) [NeZero n] :
    Function.Surjective (realCliffordSpinCompactParam n) := by
  intro x
  obtain ⟨p, hplen, hpprod⟩ := exists_sphere_pair_list_prod_eq n x
  let e := firstUnitSphere n
  let filler : realCliffordUnitSphere n × realCliffordUnitSphere n := (e, e)
  let padded := p ++ List.replicate (n + 1 - p.length) filler
  have hpadded : padded.length = n + 1 := by
    simp only [padded, List.length_append, List.length_replicate]
    omega
  let v : List.Vector (realCliffordUnitSphere n × realCliffordUnitSphere n) (n + 1) :=
    ⟨padded, hpadded⟩
  refine ⟨v.get, ?_⟩
  change (List.ofFn fun i => realCliffordSpinSpherePair n (v.get i)).prod = x
  rw [List.ofFn_comp']
  have hv : List.ofFn v.get = padded := by
    have h := congrArg List.Vector.toList (List.Vector.ofFn_get v)
    have h' : List.ofFn v.get = v.toList := by
      simpa only [List.Vector.toList_ofFn] using h
    have hvlist : v.toList = padded := rfl
    exact h'.trans hvlist
  rw [hv]
  have hfiller : realCliffordSpinSpherePair n filler = 1 := by
    exact realCliffordSpinSpherePair_self n e
  simp only [padded, List.map_append, List.prod_append, List.map_replicate,
    List.prod_replicate, hpprod]
  rw [hfiller, one_pow, mul_one]

/-- The compact real Spin group is compact in every positive dimension. -/
instance instCompactSpaceRealCliffordSpinGroupZero (n : ℕ) [NeZero n] :
    CompactSpace (realCliffordSpinGroupZero n) := by
  exact (surjective_realCliffordSpinCompactParam n).compactSpace
    (continuous_realCliffordSpinCompactParam n)

end

end CliffordAlgebra
