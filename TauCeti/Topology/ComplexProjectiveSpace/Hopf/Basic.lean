/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Circle
public import TauCeti.Analysis.Normed.Module.Ball.Action
public import TauCeti.Analysis.Normed.Module.Normalize
public import TauCeti.Topology.ComplexProjectiveSpace.Charts
public import TauCeti.Topology.Homotopy.SerreFibration.FiberBundle

/-!
# The Hopf fibration `S¹ → S²ⁿ⁺¹ → CPⁿ`

Complex projective space `CPⁿ` is the quotient of the unit sphere `S²ⁿ⁺¹` of `ℂⁿ⁺¹` by the unit
complex numbers (`TauCeti.ComplexProjectiveSpace`), and the quotient map
`TauCeti.ComplexProjectiveSpace.mk` is the **Hopf fibration**. This file shows that it is a locally
trivial bundle with fibre the unit circle `S¹ ⊆ ℂ`, and hence a Serre fibration.

The charts live over the standard affine opens `{X_k ≠ 0}`. Over such an open, a point `[v]` has
a unique unit representative whose `k`th coordinate is a positive real number, namely
`(conj v_k / |v_k|) • v` (`TauCeti.ComplexProjectiveSpace.hopfSection`). Every unit vector `v`
with `v_k ≠ 0` is then the unit complex number `v_k / |v_k|` times this representative, which
gives the chart `v ↦ ([v], v_k / |v_k|)`
(`TauCeti.ComplexProjectiveSpace.hopfTrivialization`), with inverse `([v], u) ↦ u • σ_k [v]`.

## Main definitions

* `TauCeti.ComplexProjectiveSpace.hopfSection`: the unit representative of a point of `{X_k ≠ 0}`
  with positive real `k`th coordinate.
* `TauCeti.ComplexProjectiveSpace.hopfTrivialization`: the chart of the Hopf fibration over
  `{X_k ≠ 0}`, with fibre the unit circle.
* `TauCeti.ComplexProjectiveSpace.hopfFiberHomeomorph`: the fibre of the Hopf fibration over `[v]`
  is homeomorphic to the unit circle, through `u ↦ u • v`.

## Main results

* `TauCeti.ComplexProjectiveSpace.exists_trivialization_mk`: the Hopf fibration is locally trivial
  with fibre the unit circle.
* `TauCeti.ComplexProjectiveSpace.mk_mem_serreFibrations`: the Hopf fibration is a Serre
  fibration.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  §4.2, Example 4.45.
-/

public section

noncomputable section

open Metric Set Topology

namespace TauCeti.ComplexProjectiveSpace

variable {n : ℕ}

/-- The unit vector `e_k` of `ℂⁿ⁺¹`, an assigned value of `hopfSection k` off its chart. -/
private def unitSingle (k : Fin (n + 1)) : sphere (0 : EuclideanSpace ℂ (Fin (n + 1))) 1 :=
  ⟨EuclideanSpace.single k 1, by simp⟩

/-- The vector `conj v_k • v`, whose direction is `hopfSection k [v]`. -/
private def conjCoordSMul (k : Fin (n + 1)) (v : EuclideanSpace ℂ (Fin (n + 1))) :
    EuclideanSpace ℂ (Fin (n + 1)) :=
  (starRingEnd ℂ) (v k) • v

private theorem conjCoordSMul_smul (k : Fin (n + 1)) (c : sphere (0 : ℂ) 1)
    (v : sphere (0 : EuclideanSpace ℂ (Fin (n + 1))) 1) :
    conjCoordSMul k ((c • v : sphere (0 : EuclideanSpace ℂ (Fin (n + 1))) 1) :
      EuclideanSpace ℂ (Fin (n + 1))) = conjCoordSMul k v := by
  simp only [conjCoordSMul, Sphere.coe_sphere_smul, PiLp.smul_apply, smul_eq_mul, map_mul,
    smul_smul]
  rw [mul_comm ((starRingEnd ℂ) (c : ℂ)), mul_assoc, Complex.conj_mul_self_of_mem_sphere c.2,
    mul_one]

private theorem continuous_conjCoordSMul (k : Fin (n + 1)) :
    Continuous (conjCoordSMul (n := n) k) :=
  ((Complex.continuous_conj.comp (PiLp.continuous_apply 2 (fun _ : Fin (n + 1) ↦ ℂ) k)).smul
    continuous_id)

/-- `conj v_k • v` is `|v_k|` times the unit vector `(conj v_k / |v_k|) • v`. -/
private theorem conjCoordSMul_eq (k : Fin (n + 1))
    (v : sphere (0 : EuclideanSpace ℂ (Fin (n + 1))) 1) :
    conjCoordSMul k v = ‖v.1 k‖ •
      ((sphereDirection 1 ((starRingEnd ℂ) (v.1 k)) • v :
        sphere (0 : EuclideanSpace ℂ (Fin (n + 1))) 1) : EuclideanSpace ℂ (Fin (n + 1))) := by
  rw [conjCoordSMul, Sphere.coe_sphere_smul, ← smul_assoc, ← Complex.norm_conj,
    norm_smul_sphereDirection]

variable (k : Fin (n + 1))

/-- The **unit representative with positive real `k`th coordinate** of a point `[v]` of the affine
open `{X_k ≠ 0}` of `CPⁿ`: the direction of `conj v_k • v`, which is `(conj v_k / |v_k|) • v`
(`TauCeti.ComplexProjectiveSpace.hopfSection_mk`). It is a continuous section of the Hopf
fibration over `{X_k ≠ 0}`. Off that open it takes the value `e_k`. -/
def hopfSection : ComplexProjectiveSpace n → sphere (0 : EuclideanSpace ℂ (Fin (n + 1))) 1 :=
  ComplexProjectiveSpace.lift n (fun v ↦ sphereDirection (unitSingle k) (conjCoordSMul k v))
    fun c v ↦ by rw [conjCoordSMul_smul]

variable {k}

/-- On the affine open `{X_k ≠ 0}`, `hopfSection k [v]` is `(conj v_k / |v_k|) • v`. -/
theorem hopfSection_mk {v : sphere (0 : EuclideanSpace ℂ (Fin (n + 1))) 1} (hv : v.1 k ≠ 0) :
    hopfSection k (mk n v) = sphereDirection 1 ((starRingEnd ℂ) (v.1 k)) • v := by
  rw [hopfSection, ComplexProjectiveSpace.lift_mk, conjCoordSMul_eq,
    sphereDirection_smul_of_pos _ (norm_pos_iff.2 hv)]

/-- `hopfSection k` is a section of the Hopf fibration over the affine open `{X_k ≠ 0}`. -/
@[simp]
theorem mk_hopfSection {p : ComplexProjectiveSpace n} (hp : p ∈ affineOpen k) :
    mk n (hopfSection k p) = p := by
  obtain ⟨v, rfl⟩ := mk_surjective n p
  rw [hopfSection_mk ((mk_mem_affineOpen_iff k v).1 hp), mk_smul]

/-- On the affine open `{X_k ≠ 0}`, the `k`th coordinate of `hopfSection k [v]` is the positive
real number `|v_k|`. -/
theorem hopfSection_mk_apply_self {v : sphere (0 : EuclideanSpace ℂ (Fin (n + 1))) 1}
    (hv : v.1 k ≠ 0) : (hopfSection k (mk n v)).1 k = (‖v.1 k‖ : ℂ) := by
  have h := congrArg (fun w : EuclideanSpace ℂ (Fin (n + 1)) ↦ w k) (conjCoordSMul_eq k v)
  simp only [conjCoordSMul, PiLp.smul_apply, smul_eq_mul, Complex.conj_mul'] at h
  rw [hopfSection_mk hv]
  apply mul_left_cancel₀ (Complex.ofReal_ne_zero.2 (norm_ne_zero_iff.2 hv))
  rw [← Complex.real_smul, ← h, sq]

/-- `hopfSection k` is continuous on the affine open `{X_k ≠ 0}`. -/
theorem continuousOn_hopfSection : ContinuousOn (hopfSection k) (affineOpen k) := by
  intro p hp
  obtain ⟨v, rfl⟩ := mk_surjective n p
  have hv : v.1 k ≠ 0 := (mk_mem_affineOpen_iff k v).1 hp
  refine (continuousAt_lift n _ ?_).continuousWithinAt
  refine (continuousAt_sphereDirection _ ?_).comp
    ((continuous_conjCoordSMul k).comp continuous_subtype_val).continuousAt
  rw [conjCoordSMul_eq]
  exact smul_ne_zero (norm_ne_zero_iff.2 hv) (ne_zero_of_mem_unit_sphere _)

variable (k) in
/-- The **chart of the Hopf fibration** over the affine open `{X_k ≠ 0}` of `CPⁿ`, with fibre the
unit circle. It sends a unit vector `v` with `v_k ≠ 0` to `([v], v_k / |v_k|)`, and its inverse
sends `([v], u)` to `u • hopfSection k [v]`. -/
def hopfTrivialization : Bundle.Trivialization (sphere (0 : ℂ) 1) (mk n) where
  toFun v := (mk n v, sphereDirection 1 (v.1 k))
  invFun p := p.2 • hopfSection k p.1
  source := mk n ⁻¹' affineOpen k
  target := affineOpen k ×ˢ univ
  map_source' _ hv := ⟨hv, mem_univ _⟩
  map_target' p hp := by
    rw [mem_preimage, mk_smul, mk_hopfSection hp.1]
    exact hp.1
  left_inv' v hv := by
    have hv' : v.1 k ≠ 0 := (mk_mem_affineOpen_iff k v).1 hv
    apply Subtype.ext
    dsimp only
    rw [hopfSection_mk hv', Sphere.coe_sphere_smul, Sphere.coe_sphere_smul, smul_smul,
      ← Metric.unitSphere.coe_mul, sphereDirection_mul_sphereDirection_conj hv',
      Metric.unitSphere.coe_one, one_smul]
  right_inv' p hp := by
    obtain ⟨q, u⟩ := p
    obtain ⟨v, rfl⟩ := mk_surjective n q
    have hv : v.1 k ≠ 0 := (mk_mem_affineOpen_iff k v).1 hp.1
    refine Prod.ext (by dsimp only; rw [mk_smul, mk_hopfSection hp.1]) ?_
    dsimp only
    rw [Sphere.coe_sphere_smul, PiLp.smul_apply, smul_eq_mul, hopfSection_mk_apply_self hv,
      mul_comm, ← Complex.real_smul,
      sphereDirection_smul_of_pos _ (norm_pos_iff.2 hv)]
  open_source := (isOpen_affineOpen k).preimage (continuous_mk n)
  open_target := (isOpen_affineOpen k).prod isOpen_univ
  continuousOn_toFun := by
    refine (continuous_mk n).continuousOn.prodMk fun v hv ↦ ?_
    have hv' : v.1 k ≠ 0 := (mk_mem_affineOpen_iff k v).1 hv
    exact ((continuousAt_sphereDirection _ hv').comp
      (f := fun v : sphere (0 : EuclideanSpace ℂ (Fin (n + 1))) 1 ↦ v.1 k)
      ((PiLp.continuous_apply 2 (fun _ : Fin (n + 1) ↦ ℂ) k).comp
        continuous_subtype_val).continuousAt).continuousWithinAt
  continuousOn_invFun :=
    continuous_snd.continuousOn.smul
      (continuousOn_hopfSection.comp continuousOn_fst fun _ hp ↦ hp.1)
  baseSet := affineOpen k
  open_baseSet := isOpen_affineOpen k
  source_eq := rfl
  target_eq := rfl
  proj_toFun _ _ := rfl

@[simp]
theorem hopfTrivialization_baseSet : (hopfTrivialization (n := n) k).baseSet = affineOpen k :=
  (rfl)

/-- The fibre coordinate of the chart over `{X_k ≠ 0}` is the direction `v_k / |v_k|` of the
`k`th coordinate. -/
@[simp]
theorem hopfTrivialization_apply (v : sphere (0 : EuclideanSpace ℂ (Fin (n + 1))) 1) :
    hopfTrivialization k v = (mk n v, sphereDirection 1 (v.1 k)) :=
  (rfl)

/-- The inverse of the chart over `{X_k ≠ 0}` multiplies the section `hopfSection k` by the fibre
coordinate. -/
@[simp]
theorem hopfTrivialization_symm_apply (p : ComplexProjectiveSpace n × sphere (0 : ℂ) 1) :
    (hopfTrivialization k).toOpenPartialHomeomorph.symm p = p.2 • hopfSection k p.1 :=
  (rfl)

variable (n) in
/-- **The Hopf fibration is locally trivial**: every point of `CPⁿ` lies in the base of a chart of
`S²ⁿ⁺¹ → CPⁿ` with fibre the unit circle. -/
theorem exists_trivialization_mk (p : ComplexProjectiveSpace n) :
    ∃ e : Bundle.Trivialization (sphere (0 : ℂ) 1) (mk n), p ∈ e.baseSet :=
  let ⟨k, hk⟩ := exists_mem_affineOpen p
  ⟨hopfTrivialization k, hk⟩

variable (n) in
/-- The Hopf fibration `S²ⁿ⁺¹ → CPⁿ` as a morphism of `TopCat`. -/
abbrev hopfHom :
    _root_.TopCat.of (sphere (0 : EuclideanSpace ℂ (Fin (n + 1))) 1) ⟶
      _root_.TopCat.of (ComplexProjectiveSpace n) :=
  _root_.TopCat.ofHom ⟨mk n, continuous_mk n⟩

variable (n) in
/-- **The Hopf fibration `S²ⁿ⁺¹ → CPⁿ` is a Serre fibration**, being locally trivial with fibre the
unit circle. -/
theorem mk_mem_serreFibrations : TopCat.serreFibrations (hopfHom n) :=
  TopCat.mem_serreFibrations_of_exists_trivialization (exists_trivialization_mk n)

/-! ### The fibre -/

variable (v : sphere (0 : EuclideanSpace ℂ (Fin (n + 1))) 1)

/-- The orbit map `u ↦ u • v` of the unit circle on a unit vector `v` lands in the fibre of the Hopf
fibration over `[v]`. -/
private def orbitFiber (u : sphere (0 : ℂ) 1) : mk n ⁻¹' {mk n v} :=
  ⟨u • v, by simp⟩

/-- The **fibre of the Hopf fibration** over `[v]` is homeomorphic to the unit circle, through the
orbit map `u ↦ u • v`. -/
def hopfFiberHomeomorph : sphere (0 : ℂ) 1 ≃ₜ mk n ⁻¹' {mk n v} :=
  have hc : Continuous (orbitFiber v) :=
    (continuous_id.smul continuous_const).subtype_mk _
  have hb : Function.Bijective (orbitFiber v) := by
    refine ⟨fun u u' h ↦ ?_, fun w ↦ ?_⟩
    · have h' := congrArg (fun w : mk n ⁻¹' {mk n v} ↦ (w.1 : EuclideanSpace ℂ (Fin (n + 1)))) h
      simp only [orbitFiber, Sphere.coe_sphere_smul] at h'
      exact Subtype.ext (smul_left_injective ℂ (ne_zero_of_mem_unit_sphere v) h')
    · obtain ⟨c, hc⟩ := (mk_eq_mk_iff n w v).1 w.2
      exact ⟨c, Subtype.ext hc⟩
  hc.homeoOfEquivCompactToT2 (f := Equiv.ofBijective _ hb)

@[simp]
theorem coe_hopfFiberHomeomorph_apply (u : sphere (0 : ℂ) 1) :
    (hopfFiberHomeomorph v u : sphere (0 : EuclideanSpace ℂ (Fin (n + 1))) 1) = u • v :=
  (rfl)

/-- The unit `1` of the circle corresponds to `v` itself in the fibre over `[v]`. -/
@[simp]
theorem hopfFiberHomeomorph_one : hopfFiberHomeomorph v 1 = ⟨v, rfl⟩ :=
  Subtype.ext (one_smul _ v)

end TauCeti.ComplexProjectiveSpace
