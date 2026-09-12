/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.CliffordAlgebra.Spin.ReflectionPair
import TauCeti.Data.List.Pair
import TauCeti.LinearAlgebra.QuadraticForm.CartanDieudonne.SpecialOrthogonal
import Mathlib.Analysis.Normed.Group.BallSphere
import Mathlib.Analysis.Normed.Module.Normalize

/-!
# Compactness of compact real Spin groups

Every element of a positive-dimensional compact real Spin group is a product of uniformly many
normalized reflection-pair lifts. The normalized vectors range over a Euclidean unit sphere, so a
fixed finite product of pairs of spheres maps continuously and surjectively onto the Spin group.
In dimension zero the group is trivial, and therefore compact.

The uniform bound comes from the bounded Cartan--Dieudonne factorization. Its reflection word has
even length over the special orthogonal group, hence can be grouped into pairs. One additional pair
accounts for the possible scalar `-1` in the kernel of the Spin projection. Repeated equal vectors
pad the product without changing it.

## Main result

* `CliffordAlgebra.instCompactSpaceRealCliffordSpinGroupZero` proves that `Spin(n)` is compact in
  every dimension.

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

private def normalizedVectorSphere {n : ℕ} (v : Fin n → ℝ)
    (hv : realCliffordForm n 0 v ≠ 0) : realCliffordUnitSphere n :=
  ⟨NormedSpace.normalize ((EuclideanSpace.equiv (Fin n) ℝ).symm v), by
    rw [mem_sphere, dist_zero_right]
    apply NormedSpace.norm_normalize
    intro h
    apply hv
    have hvzero : v = 0 :=
      (EuclideanSpace.equiv (Fin n) ℝ).symm.map_eq_zero_iff.mp h
    simp only [hvzero, map_zero]⟩

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
      (realCliffordForm_zero_euclideanSpaceEquiv_eq_one u).symm ▸ invertibleOne
    QuadraticMap.reflectionOrthogonal (realCliffordForm n 0)
        (EuclideanSpace.equiv (Fin n) ℝ u) =
      QuadraticMap.reflectionOrthogonal (realCliffordForm n 0) v := by
  dsimp only
  have hv0 : v ≠ 0 := fun h => (isUnit_of_invertible (realCliffordForm n 0 v)).ne_zero (by
    simp [h])
  have hcoord : (EuclideanSpace.equiv (Fin n) ℝ).symm v ≠ 0 := by
    intro h
    exact hv0 ((EuclideanSpace.equiv (Fin n) ℝ).symm.map_eq_zero_iff.mp h)
  let _ : Invertible ‖(EuclideanSpace.equiv (Fin n) ℝ).symm v‖⁻¹ :=
    invertibleOfNonzero (inv_ne_zero (norm_ne_zero_iff.mpr hcoord))
  let _ : Invertible (realCliffordForm n 0
      (EuclideanSpace.equiv (Fin n) ℝ
        (normalizedVectorSphere v (isUnit_of_invertible _).ne_zero))) :=
    (realCliffordForm_zero_euclideanSpaceEquiv_eq_one
      (normalizedVectorSphere v (isUnit_of_invertible _).ne_zero)).symm ▸ invertibleOne
  let _ : Invertible (realCliffordForm n 0
      (‖(EuclideanSpace.equiv (Fin n) ℝ).symm v‖⁻¹ • v)) := by
    rw [QuadraticMap.map_smul]
    let _ : Invertible (‖(EuclideanSpace.equiv (Fin n) ℝ).symm v‖⁻¹ *
        ‖(EuclideanSpace.equiv (Fin n) ℝ).symm v‖⁻¹) := invertibleMul _ _
    exact invertibleMul _ _
  have hvec : EuclideanSpace.equiv (Fin n) ℝ
      (normalizedVectorSphere v (isUnit_of_invertible _).ne_zero) =
      ‖(EuclideanSpace.equiv (Fin n) ℝ).symm v‖⁻¹ • v := by
    simp only [normalizedVectorSphere, NormedSpace.normalize,
      ContinuousLinearEquiv.map_smul, ContinuousLinearEquiv.apply_symm_apply]
  exact (reflectionOrthogonal_eq_of_vector_eq _ _ hvec).trans
    (QuadraticMap.reflectionOrthogonal_smul_eq (realCliffordForm n 0) v _)

private def unitSphereReflection (n : ℕ) (u : realCliffordUnitSphere n) :
    QuadraticMap.orthogonalGroup (realCliffordForm n 0) :=
  let _ : Invertible (realCliffordForm n 0
      (EuclideanSpace.equiv (Fin n) ℝ u)) :=
    (realCliffordForm_zero_euclideanSpaceEquiv_eq_one u).symm ▸ invertibleOne
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

private def realCliffordSpinSpherePair (n : ℕ)
    (p : realCliffordUnitSphere n × realCliffordUnitSphere n) :
    realCliffordSpinGroupZero n :=
  spinReflectionPair (realCliffordForm n 0)
    (EuclideanSpace.equiv (Fin n) ℝ p.1)
    (EuclideanSpace.equiv (Fin n) ℝ p.2)
    (realCliffordForm_zero_euclideanSpaceEquiv_eq_one p.1)
    (realCliffordForm_zero_euclideanSpaceEquiv_eq_one p.2)

private theorem continuous_realCliffordSpinSpherePair (n : ℕ) :
    Continuous (realCliffordSpinSpherePair n) := by
  apply continuous_induced_rng.mpr
  -- Expose the underlying Clifford product to prove continuity in the subtype topology.
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

private def realCliffordSpinCompactParam (n : ℕ) :
    (Fin (n + 1) → realCliffordUnitSphere n × realCliffordUnitSphere n) →
      realCliffordSpinGroupZero n :=
  fun f => (List.ofFn fun i => realCliffordSpinSpherePair n (f i)).prod

private theorem continuous_realCliffordSpinCompactParam (n : ℕ) :
    Continuous (realCliffordSpinCompactParam n) := by
  -- Unfold the fixed-length ordered product before applying `continuous_list_prod`.
  change Continuous (fun f : Fin (n + 1) →
      realCliffordUnitSphere n × realCliffordUnitSphere n =>
    (List.ofFn fun i => realCliffordSpinSpherePair n (f i)).prod)
  have h := continuous_list_prod (List.ofFn fun i : Fin (n + 1) => i)
    (fun i _ => (continuous_realCliffordSpinSpherePair n).comp (continuous_apply i))
  simpa only [List.map_ofFn, Function.comp_def] using h

private theorem realCliffordSpinSpherePair_neg (n : ℕ) [NeZero n]
    (u : realCliffordUnitSphere n) :
    realCliffordSpinSpherePair n (u, -u) =
      spinGroup.negOne (realCliffordForm n 0) (nondegenerate_realCliffordForm n 0).ne_zero := by
  apply Subtype.ext
  simp only [realCliffordSpinSpherePair, coe_spinReflectionPair, coe_neg_sphere,
    ContinuousLinearEquiv.map_neg, spinGroup.coe_negOne]
  rw [map_neg, mul_neg, ι_sq_scalar, realCliffordForm_zero_euclideanSpaceEquiv_eq_one]
  simp

private noncomputable def firstUnitSphere (n : ℕ) [NeZero n] : realCliffordUnitSphere n :=
  Classical.choice (NormedSpace.sphere_nonempty.mpr zero_le_one).to_subtype

private theorem exists_sphere_pair_list_prod_eq (n : ℕ) [NeZero n]
    (x : realCliffordSpinGroupZero n) :
    ∃ p : List (realCliffordUnitSphere n × realCliffordUnitSphere n),
      p.length ≤ n + 1 ∧ (p.map (realCliffordSpinSpherePair n)).prod = x := by
  let Q := realCliffordForm n 0
  let g := spinToSpecialOrthogonal Q x
  obtain ⟨l, hlrefl, hllen, hleven, hlprod⟩ :=
    QuadraticMap.exists_even_reflectionOrthogonal_list_prod_eq Q
      (nondegenerate_realCliffordForm n 0) g
  obtain ⟨u, hulen, huprod⟩ := exists_unitSphere_reflection_list n l hlrefl
  let p := List.pairAdjacent u
  let z : realCliffordSpinGroupZero n := (p.map (realCliffordSpinSpherePair n)).prod
  have hpmap : (p.map fun q => unitSphereReflection n q.1 *
      unitSphereReflection n q.2).prod = l.prod := by
    calc
      _ = (u.map (unitSphereReflection n)).prod :=
        List.prod_map_pairAdjacent (unitSphereReflection n) u (by simpa [hulen])
      _ = l.prod := huprod
  have hzorth : spinToOrthogonal Q z = l.prod := by
    rw [← hpmap]
    simp only [z, map_list_prod, List.map_map]
    congr 1
    apply List.map_congr_left
    intro q _
    exact spinToOrthogonal_spinReflectionPair _ _ _ _ _
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
    have hpair : 2 * p.length ≤ l.length := by
      simp only [p, List.length_pairAdjacent, hulen]
      omega
    have hln : l.length ≤ n := by simpa using hllen
    omega
  rcases eq_or_eq_negOne_mul_of_spinToSpecialOrthogonal_eq Q
      (nondegenerate_realCliffordForm n 0) x z (by simpa only [g] using hzproj.symm) with hx | hx
  · exact ⟨p, hplen.trans (by omega), hx.symm⟩
  · let e := firstUnitSphere n
    refine ⟨(e, -e) :: p, by simp only [List.length_cons]; omega, ?_⟩
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
  -- Unfold the parameter map before identifying the padded vector with its list.
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
    exact spinReflectionPair_self _ _ _
  simp only [padded, List.map_append, List.prod_append, List.map_replicate,
    List.prod_replicate, hpprod]
  rw [hfiller, one_pow, mul_one]

private theorem subsingleton_realCliffordSpinGroupZero_zero :
    Subsingleton (realCliffordSpinGroupZero 0) := by
  let Q := realCliffordForm 0 0
  have hsource : ((↑) ⁻¹' Set.range (ι Q) : Set (CliffordAlgebra Q)ˣ) = ∅ := by
    ext u
    constructor
    · rintro ⟨v, hv⟩
      have hvzero : v = 0 := by
        ext i
        exact Fin.elim0 i
      subst v
      exact (Units.ne_zero u (by simpa using hv.symm)).elim
    · intro hu
      exact hu.elim
  have hlipschitz : lipschitzGroup Q = ⊥ := by
    rw [lipschitzGroup, hsource, Subgroup.closure_empty]
  constructor
  intro x y
  apply spinGroup.toUnits_injective
  have hx : spinGroup.toUnits x ∈ lipschitzGroup Q :=
    spinGroup.units_mem_lipschitzGroup x.2
  have hy : spinGroup.toUnits y ∈ lipschitzGroup Q :=
    spinGroup.units_mem_lipschitzGroup y.2
  rw [hlipschitz] at hx hy
  exact (Subgroup.mem_bot.mp hx).trans (Subgroup.mem_bot.mp hy).symm

/-- The compact real Spin group is compact in every dimension. -/
instance instCompactSpaceRealCliffordSpinGroupZero (n : ℕ) :
    CompactSpace (realCliffordSpinGroupZero n) := by
  cases n with
  | zero =>
      let _ := subsingleton_realCliffordSpinGroupZero_zero
      infer_instance
  | succ n =>
      let _ : NeZero (n + 1) := ⟨Nat.succ_ne_zero n⟩
      exact (surjective_realCliffordSpinCompactParam (n + 1)).compactSpace
        (continuous_realCliffordSpinCompactParam (n + 1))

end

end CliffordAlgebra
