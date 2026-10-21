/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.ComplexProjectiveSpace.Basic
public import TauCeti.Analysis.Normed.Module.Normalize

/-!
# Homogeneous-coordinate charts on complex projective space

On the open set where the homogeneous coordinate `k` is nonzero, the ratios `X_j / X_k`
give a homeomorphism with complex affine space. These charts are constructed directly on the
circle quotient of the unit sphere. The inverse inserts a coordinate equal to one and normalizes
the resulting vector to unit length. The other coordinates may vanish.

The chart sources cover projective space, including in dimension zero. Their overlap functions
are the usual homogeneous ratios; these formulas provide the complex atlas and the comparison
with homogeneous-coordinate charts of toric projective space.

## References

* D. Cox, J. Little and H. Schenck, *Toric Varieties*, §§3.1 and 3.4.
-/

public section

open Metric Set Topology

namespace TauCeti.ComplexProjectiveSpace

noncomputable section

variable {n : ℕ}

/-- The homogeneous ratio `X_j / X_k`. Outside the chart `X_k ≠ 0` it is zero, following
the convention for division in `ℂ`. -/
def ratio (k j : Fin (n + 1)) : ComplexProjectiveSpace n → ℂ :=
  ComplexProjectiveSpace.lift n (fun v ↦ v.1 j / v.1 k) fun c _ ↦
    mul_div_mul_left _ _ (ne_zero_of_mem_unit_sphere c)

/-- Homogeneous ratios can be computed on any unit-vector representative. -/
@[simp]
theorem ratio_mk (k j : Fin (n + 1))
    (v : sphere (0 : EuclideanSpace ℂ (Fin (n + 1))) 1) :
    ratio k j (mk n v) = v.1 j / v.1 k :=
  ComplexProjectiveSpace.lift_mk n _ _ v

/-- The standard affine open where the `k`th homogeneous coordinate is nonzero. -/
def affineOpen (k : Fin (n + 1)) : Set (ComplexProjectiveSpace n) :=
  {p | ratio k k p ≠ 0}

/-- A standard affine open is characterized by the nonvanishing of its normalizing ratio. -/
@[simp]
theorem mem_affineOpen_iff (k : Fin (n + 1)) (p : ComplexProjectiveSpace n) :
    p ∈ affineOpen k ↔ ratio k k p ≠ 0 := Iff.rfl

/-- The normalizing homogeneous ratio is one on its affine chart domain. -/
@[simp]
theorem ratio_self_eq_one (k : Fin (n + 1)) {p : ComplexProjectiveSpace n}
    (hp : p ∈ affineOpen k) : ratio k k p = 1 := by
  obtain ⟨v, rfl⟩ := mk_surjective n p
  have hk : v.1 k ≠ 0 := by simpa using hp
  simpa only [ratio_mk] using div_self hk

/-- The homogeneous-coordinate chart domains are open for the sphere-quotient topology. -/
theorem isOpen_affineOpen (k : Fin (n + 1)) : IsOpen (affineOpen k) := by
  apply (isOpenQuotientMap_mk n).isQuotientMap.isOpen_preimage.mp
  convert (isOpen_ne_fun
    ((PiLp.continuous_apply 2 (fun _ : Fin (n + 1) ↦ ℂ) k).comp continuous_subtype_val)
    (continuous_const (y := (0 : ℂ)))) using 1
  ext v
  simp

/-- Every projective point has a nonzero homogeneous coordinate. -/
theorem exists_mem_affineOpen (p : ComplexProjectiveSpace n) :
    ∃ k, p ∈ affineOpen k := by
  induction p using ComplexProjectiveSpace.inductionOn with
  | h v =>
    by_contra! h
    have hv : v.1 = 0 := by
      ext k
      simpa using h k
    simpa [hv] using v.2

/-- Homogeneous ratios are continuous on any chart where their denominator is nonzero. -/
theorem continuousOn_ratio (k j : Fin (n + 1)) : ContinuousOn (ratio k j) (affineOpen k) := by
  intro p hp
  obtain ⟨v, rfl⟩ := mk_surjective n p
  have hk : v.1 k ≠ 0 := by simpa using hp
  apply ContinuousAt.continuousWithinAt
  apply continuousAt_lift
  exact ((PiLp.continuous_apply 2 (fun _ : Fin (n + 1) ↦ ℂ) j).comp
    continuous_subtype_val).continuousAt.div
    (((PiLp.continuous_apply 2 (fun _ : Fin (n + 1) ↦ ℂ) k).comp
      continuous_subtype_val).continuousAt) hk

private def affineVector (k : Fin (n + 1)) (z : Fin n → ℂ) :
    EuclideanSpace ℂ (Fin (n + 1)) :=
  WithLp.toLp 2 (Fin.insertNth (α := fun _ ↦ ℂ) k 1 z)

private theorem affineVector_ne_zero (k : Fin (n + 1)) (z : Fin n → ℂ) :
    affineVector k z ≠ 0 := by
  intro h
  have := congrArg (fun v : EuclideanSpace ℂ (Fin (n + 1)) ↦ v k) h
  simp [affineVector] at this

private theorem continuous_affineVector (k : Fin (n + 1)) : Continuous (affineVector k) :=
  (PiLp.continuous_toLp 2 (fun _ : Fin (n + 1) ↦ ℂ)).comp
    (continuous_const.finInsertNth k continuous_id)

private def affineSphere (k : Fin (n + 1)) :
    C((Fin n → ℂ), sphere (0 : EuclideanSpace ℂ (Fin (n + 1))) 1) :=
  normalizeToSphere (affineVector k) (continuous_affineVector k) (affineVector_ne_zero k)

/-- The projective point whose `k`th coordinate is one and whose remaining coordinates are `z`.
The representative is normalized only to meet the unit-sphere carrier. -/
def affineParam (k : Fin (n + 1)) (z : Fin n → ℂ) : ComplexProjectiveSpace n :=
  mk n (affineSphere k z)

/-- The homogeneous ratios of a standard affine parametrization are ratios of its inserted
coordinates. -/
@[simp]
theorem ratio_affineParam (k l j : Fin (n + 1)) (z : Fin n → ℂ) :
    ratio l j (affineParam k z) =
      Fin.insertNth (α := fun _ ↦ ℂ) k 1 z j /
        Fin.insertNth (α := fun _ ↦ ℂ) k 1 z l := by
  have hn := norm_ne_zero_iff.2 (affineVector_ne_zero k z)
  simp only [affineParam, ratio_mk, affineSphere, coe_normalizeToSphere_apply,
    NormedSpace.normalize, PiLp.smul_apply, affineVector, Complex.real_smul]
  exact mul_div_mul_left _ _ (Complex.ofReal_ne_zero.mpr (inv_ne_zero hn))

/-- Standard affine parametrizations are continuous, including on all coordinate hyperplanes. -/
@[fun_prop]
theorem continuous_affineParam (k : Fin (n + 1)) : Continuous (affineParam k) := by
  exact (continuous_mk n).comp (affineSphere k).continuous

/-- Homogeneous ratios recover a point on their affine domain. -/
@[simp]
theorem affineParam_ratio (k : Fin (n + 1)) {p : ComplexProjectiveSpace n}
    (hp : p ∈ affineOpen k) :
    affineParam k (fun j ↦ ratio k (k.succAbove j) p) = p := by
  obtain ⟨v, rfl⟩ := mk_surjective n p
  have hk : v.1 k ≠ 0 := by simpa using hp
  simp only [ratio_mk]
  let z := fun j ↦ v.1 (k.succAbove j) / v.1 k
  let w := affineSphere k z
  have hw (j) : w.1 j = (‖affineVector k z‖⁻¹ : ℝ) • (v.1 j / v.1 k) := by
    induction j using k.succAboveCases with
    | x => simp [w, affineSphere, NormedSpace.normalize, affineVector, hk]
    | p j => simp [w, affineSphere, NormedSpace.normalize, affineVector, z]
  let c : ℂ := (‖affineVector k z‖⁻¹ : ℝ) / v.1 k
  have hsmul : c • v.1 = w.1 := by
    ext j
    rw [hw]
    simp [c, div_mul_eq_mul_div, mul_div_assoc]
  have hc : ‖c‖ = 1 := by
    have h := congrArg norm hsmul
    simpa only [norm_smul, mem_sphere_zero_iff_norm.1 v.2,
      mem_sphere_zero_iff_norm.1 w.2, mul_one] using h
  exact (mk_eq_mk_iff n w v).2 ⟨⟨c, mem_sphere_zero_iff_norm.2 hc⟩, Subtype.ext hsmul⟩

/-- The standard homogeneous-ratio chart on the sphere-quotient projective space. -/
def affineChart (k : Fin (n + 1)) :
    OpenPartialHomeomorph (ComplexProjectiveSpace n) (Fin n → ℂ) where
  toFun p j := ratio k (k.succAbove j) p
  invFun := affineParam k
  source := affineOpen k
  target := univ
  map_source' _ _ := mem_univ _
  map_target' z _ := by simp
  left_inv' _ hp := affineParam_ratio k hp
  right_inv' z _ := by ext j; simp
  open_source := isOpen_affineOpen k
  open_target := isOpen_univ
  continuousOn_toFun := continuousOn_pi.2 fun j ↦ continuousOn_ratio k (k.succAbove j)
  continuousOn_invFun := (continuous_affineParam k).continuousOn

/-- The source of the standard chart is its homogeneous-coordinate nonvanishing locus. -/
@[simp]
theorem affineChart_source (k : Fin (n + 1)) : (affineChart k).source = affineOpen k := (rfl)

/-- The standard chart takes values in the whole complex affine space. -/
@[simp]
theorem affineChart_target (k : Fin (n + 1)) : (affineChart k).target = univ := (rfl)

/-- The standard affine chart reads homogeneous ratios. -/
@[simp]
theorem affineChart_apply (k : Fin (n + 1)) (p : ComplexProjectiveSpace n) (j : Fin n) :
    affineChart k p j = ratio k (k.succAbove j) p := (rfl)

/-- The inverse standard chart inserts the normalizing coordinate one. -/
@[simp]
theorem affineChart_symm_apply (k : Fin (n + 1)) (z : Fin n → ℂ) :
    (affineChart k).symm z = affineParam k z := (rfl)

/-- On its domain, the standard chart together with the normalizing coordinate one gives all
homogeneous ratios. -/
theorem insertNth_affineChart (k : Fin (n + 1)) {p : ComplexProjectiveSpace n}
    (hp : p ∈ affineOpen k) (j : Fin (n + 1)) :
    Fin.insertNth (α := fun _ ↦ ℂ) k 1 (affineChart k p) j = ratio k j p := by
  induction j using k.succAboveCases with
  | x => simp [ratio_self_eq_one k hp]
  | p j => simp

/-- On a chart overlap the only restriction is nonvanishing of the new denominator. -/
@[simp↓]
theorem affineParam_mem_affineOpen_iff (k l : Fin (n + 1)) (z : Fin n → ℂ) :
    affineParam k z ∈ affineOpen l ↔ Fin.insertNth (α := fun _ ↦ ℂ) k 1 z l ≠ 0 := by
  simp [mem_affineOpen_iff]

/-- The transition between standard affine charts is the usual homogeneous-ratio formula. -/
@[simp↓]
theorem affineChart_transition (k l : Fin (n + 1)) (z : Fin n → ℂ) (j : Fin n) :
    affineChart l ((affineChart k).symm z) j =
      Fin.insertNth (α := fun _ ↦ ℂ) k 1 z (l.succAbove j) /
        Fin.insertNth (α := fun _ ↦ ℂ) k 1 z l := by
  simp only [affineChart_symm_apply, affineChart_apply, ratio_affineParam]

end

end TauCeti.ComplexProjectiveSpace
