/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Orthonormal.Family
public import TauCeti.Topology.ComplexProjectiveSpace.Homogeneous
public import TauCeti.Topology.Grassmannian.ForgetLast
public import TauCeti.Topology.MappingSpace.Evaluation
public import TauCeti.Topology.Sphere.Suspension

/-!
# The projective lines of `CPⁿ` as two-spheres

The **Hopf map** `h : S³ → S²` (`TauCeti.hopfSphere2`) sends a unit vector `(a, b)` of `ℂ²` to
`(|a|² - |b|², 2 Re (a conj b), 2 Im (a conj b))`. It is invariant under unit complex scalars and
its fibres are exactly the circle orbits, so it descends to a homeomorphism `CP¹ ≃ₜ S²`
(`TauCeti.ComplexProjectiveSpace.homeomorphSphere2`) sending `[e₀]` to the north pole
and `[e₁]` to the south pole.

An ordered orthonormal two-frame `f = (f₀, f₁)` of `ℂⁿ⁺¹` spans a complex plane, whose projective
line in `CPⁿ` is the image of `[a : b] ↦ [a f₀ + b f₁]`
(`TauCeti.ComplexProjectiveSpace.lineMap`). Read through `CP¹ ≃ₜ S²`, this parametrizes the line
by the two-sphere: the map `σ_f : S² → CPⁿ`, `h (a, b) ↦ [a f₀ + b f₁]`
(`TauCeti.ComplexProjectiveSpace.lineSphereFamily`), is injective, sends the north pole to `[f₀]`
and the south pole to `[f₁]`, depends continuously on the frame, and is unchanged when both
vectors of the frame are multiplied by the same unit complex number. It is equivariant under the
unitary group. On `CP¹` itself, `σ_f` is a bijection `S² → CP¹` for every frame.

In the proof of Proposition 6.38 of Barraud–Damian–Humilière–Oancea, a point `p` of `CPⁿ` and a
unit tangent vector at `p` determine a unique complex projective line through `p` tangent to it,
a round two-sphere, and these spheres form the family `σ : T¹CPⁿ → Map(S², CPⁿ)` over `CPⁿ`. In
the frame description, `p = [f₀]`, the unit tangent vectors at `p` are the unit vectors `f₁` of the
complex orthogonal complement of `f₀`, and the line through `p` tangent to `f₁` is the projective
line of `(f₀, f₁)`. The family `σ_f` of all frames lies over `CPⁿ` through evaluation at the north
pole (`TauCeti.ComplexProjectiveSpace.mappingSpaceEval_comp_lineSphereFamily`), and since it is
invariant under the diagonal circle it factors through the unit tangent bundle. Over the point
`p = [u]`, the based family `σ_p : S(u^⊥) → Map_*(S², CPⁿ)`, `w ↦ σ_{(u, w)}`
(`TauCeti.ComplexProjectiveSpace.lineSphereFamilyFiber`), is the family of two-spheres through `p`
whose class `σ_{p*}[S(u^⊥)]` the source shows to be nonzero in `H_{2n-1}(Ω²CPⁿ)`; that
computation is not part of this file.

## Main declarations

* `TauCeti.hopfSphere2`: the Hopf map `S³ → S²`, with `TauCeti.hopfSphere2_eq_hopfSphere2_iff`
  (its fibres are the circle orbits) and `TauCeti.hopfSphere2_surjective`.
* `TauCeti.ComplexProjectiveSpace.homeomorphSphere2`: `CP¹ ≃ₜ S²`, induced by the Hopf map.
* `TauCeti.ComplexProjectiveSpace.lineMap`: `(f, [a : b]) ↦ [a f₀ + b f₁]`, jointly continuous.
* `TauCeti.ComplexProjectiveSpace.lineSphereFamily`: the projective line of a frame as a map
  `S² → CPⁿ`, with `lineSphereFamily_apply_hopfSphere2`, `lineSphereFamily_apply_north`,
  `lineSphereFamily_apply_south`, `injective_lineSphereFamily`,
  `lineSphereFamily_eq_of_smul`, `lineSphereFamily_unitaryMap` and
  `bijective_lineSphereFamily`.
* `TauCeti.ComplexProjectiveSpace.lineSphereFamilyFiber`: the based family over a point.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §6.4.5, proof of Proposition 6.38.
* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Example 4.45 (the Hopf
  map) and Example 0.6 (`CP¹ = S²`).
-/

public section

noncomputable section

open Metric Real ComplexConjugate Matrix

namespace TauCeti

/-! ### The Hopf map and `CP¹ = S²` -/

section Hopf

/-- The coordinates `(|a|² - |b|², 2 Re (a conj b), 2 Im (a conj b))` of the Hopf map at
`(a, b)`. -/
private def hopfVector (a b : ℂ) : EuclideanSpace ℝ (Fin 3) :=
  !₂[‖a‖ ^ 2 - ‖b‖ ^ 2, 2 * (a * conj b).re, 2 * (a * conj b).im]

private theorem norm_hopfVector {a b : ℂ} (h : ‖a‖ ^ 2 + ‖b‖ ^ 2 = 1) :
    ‖hopfVector a b‖ = 1 := by
  have hz : (a * conj b).re ^ 2 + (a * conj b).im ^ 2 = ‖a‖ ^ 2 * ‖b‖ ^ 2 := by
    have h := Complex.normSq_apply (a * conj b)
    rw [Complex.normSq_eq_norm_sq, norm_mul, Complex.norm_conj] at h
    linear_combination -h
  rw [EuclideanSpace.norm_eq, Real.sqrt_eq_one]
  simp only [hopfVector, Fin.sum_univ_three, Real.norm_eq_abs, sq_abs]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.tail_cons, Matrix.head_cons]
  linear_combination (‖a‖ ^ 2 + ‖b‖ ^ 2 + 1) * h + 4 * hz

/-- The two coordinates of a unit vector of `ℂ²` have square norms summing to `1`. -/
private theorem norm_sq_add_norm_sq (v : sphere (0 : EuclideanSpace ℂ (Fin 2)) 1) :
    ‖(v : EuclideanSpace ℂ (Fin 2)) 0‖ ^ 2 + ‖(v : EuclideanSpace ℂ (Fin 2)) 1‖ ^ 2 = 1 := by
  have h := EuclideanSpace.norm_sq_eq (v : EuclideanSpace ℂ (Fin 2))
  rw [norm_eq_of_mem_sphere v, Fin.sum_univ_two] at h
  linarith

/-- **The Hopf map** `S³ → S²`, `(a, b) ↦ (|a|² - |b|², 2 Re (a conj b), 2 Im (a conj b))`, from
the unit sphere of `ℂ²` to the unit sphere of `ℝ³`. -/
def hopfSphere2 : C(sphere (0 : EuclideanSpace ℂ (Fin 2)) 1, Sphere2) where
  toFun v := ⟨hopfVector ((v : EuclideanSpace ℂ (Fin 2)) 0) ((v : EuclideanSpace ℂ (Fin 2)) 1),
    mem_sphere_zero_iff_norm.2 (norm_hopfVector (norm_sq_add_norm_sq v))⟩
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    have h0 : Continuous fun v : sphere (0 : EuclideanSpace ℂ (Fin 2)) 1 ↦
        (v : EuclideanSpace ℂ (Fin 2)) 0 :=
      (PiLp.continuous_apply 2 _ 0).comp continuous_subtype_val
    have h1 : Continuous fun v : sphere (0 : EuclideanSpace ℂ (Fin 2)) 1 ↦
        (v : EuclideanSpace ℂ (Fin 2)) 1 :=
      (PiLp.continuous_apply 2 _ 1).comp continuous_subtype_val
    refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i ↦ ?_)
    fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] <;>
      [exact (h0.norm.pow 2).sub (h1.norm.pow 2);
        exact continuous_const.mul (Complex.continuous_re.comp (h0.mul (h1.star)));
        exact continuous_const.mul (Complex.continuous_im.comp (h0.mul (h1.star)))]

/-- The Hopf map in terms of its coordinate formula. -/
private theorem coe_hopfSphere2 (v : sphere (0 : EuclideanSpace ℂ (Fin 2)) 1) :
    (hopfSphere2 v : EuclideanSpace ℝ (Fin 3)) =
      hopfVector ((v : EuclideanSpace ℂ (Fin 2)) 0) ((v : EuclideanSpace ℂ (Fin 2)) 1) :=
  (rfl)

/-- The coordinates of the Hopf map. -/
theorem coe_hopfSphere2_apply (v : sphere (0 : EuclideanSpace ℂ (Fin 2)) 1) :
    (hopfSphere2 v : EuclideanSpace ℝ (Fin 3)) =
      !₂[‖(v : EuclideanSpace ℂ (Fin 2)) 0‖ ^ 2 - ‖(v : EuclideanSpace ℂ (Fin 2)) 1‖ ^ 2,
        2 * ((v : EuclideanSpace ℂ (Fin 2)) 0 * conj ((v : EuclideanSpace ℂ (Fin 2)) 1)).re,
        2 * ((v : EuclideanSpace ℂ (Fin 2)) 0 * conj ((v : EuclideanSpace ℂ (Fin 2)) 1)).im] :=
  (rfl)

/-- **The Hopf map is invariant under unit complex scalars**: `|c a| = |a|`, `|c b| = |b|` and
`(c a) conj (c b) = |c|² a conj b = a conj b`. -/
@[simp]
theorem hopfSphere2_smul (c : sphere (0 : ℂ) 1) (v : sphere (0 : EuclideanSpace ℂ (Fin 2)) 1) :
    hopfSphere2 (c • v) = hopfSphere2 v := by
  have hc : ‖(c : ℂ)‖ = 1 := norm_eq_of_mem_sphere c
  have hcc : (c : ℂ) * conj (c : ℂ) = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hc]
    simp
  have h (a b : ℂ) : (c : ℂ) * a * conj ((c : ℂ) * b) = a * conj b := by
    rw [map_mul]
    linear_combination (a * conj b) * hcc
  refine Subtype.ext ?_
  simp only [coe_hopfSphere2_apply, Sphere.coe_sphere_smul, PiLp.smul_apply, smul_eq_mul,
    norm_mul, hc, one_mul, h]

/-- Two pairs `(a, b)`, `(a', b')` of complex numbers with `|a|² + |b|² = 1 = |a'|² + |b'|²`,
`|a|² - |b|² = |a'|² - |b'|²` and `a conj b = a' conj b'` differ by a unit complex scalar. -/
private theorem exists_norm_eq_one_mul_eq {a b a' b' : ℂ} (hv : ‖a‖ ^ 2 + ‖b‖ ^ 2 = 1)
    (hw : ‖a'‖ ^ 2 + ‖b'‖ ^ 2 = 1) (h0 : ‖a‖ ^ 2 - ‖b‖ ^ 2 = ‖a'‖ ^ 2 - ‖b'‖ ^ 2)
    (hz : a * conj b = a' * conj b') : ∃ c : ℂ, ‖c‖ = 1 ∧ c * a' = a ∧ c * b' = b := by
  have ha : ‖a‖ = ‖a'‖ := (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 (by linarith)
  have hb : ‖b‖ = ‖b'‖ := (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 (by linarith)
  by_cases ha' : a' = 0
  · -- Both first coordinates vanish, and the second coordinates are unit complex numbers.
    have ha0 : a = 0 := norm_eq_zero.1 (by rw [ha, ha', norm_zero])
    have hb' : ‖b'‖ = 1 := by
      rw [ha', norm_zero] at hw
      nlinarith [norm_nonneg b']
    have hb'0 : b' ≠ 0 := norm_ne_zero_iff.1 (by rw [hb']; exact one_ne_zero)
    exact ⟨b / b', by rw [norm_div, hb, hb', div_one], by rw [ha', ha0, mul_zero],
      div_mul_cancel₀ _ hb'0⟩
  · -- The scalar is `a / a'`; it carries `b'` to `b` because `a conj b = a' conj b'` and
    -- `|a| = |a'|`.
    have hnorm : a * conj a = a' * conj a' := by
      rw [Complex.mul_conj, Complex.mul_conj, Complex.normSq_eq_norm_sq,
        Complex.normSq_eq_norm_sq, ha]
    have hconj : conj a * b = conj a' * b' := by
      simpa [mul_comm] using congrArg conj hz
    have hkey : a' * conj a' * (a * b' - a' * b) = 0 := by
      linear_combination (-(a * a')) * hconj + (a' * b) * hnorm
    have hne : a' * conj a' ≠ 0 := by
      rw [Complex.mul_conj]
      exact_mod_cast (Complex.normSq_pos.2 ha').ne'
    have hb'b : a * b' = a' * b := sub_eq_zero.1 ((mul_eq_zero.1 hkey).resolve_left hne)
    refine ⟨a / a', by rw [norm_div, ha, div_self (norm_ne_zero_iff.2 ha')],
      div_mul_cancel₀ _ ha', ?_⟩
    rw [div_mul_eq_mul_div, hb'b, mul_div_cancel_left₀ _ ha']

/-- **The fibres of the Hopf map are the circle orbits**: two unit vectors of `ℂ²` have the same
image exactly when they differ by a unit complex scalar. -/
theorem hopfSphere2_eq_hopfSphere2_iff {v w : sphere (0 : EuclideanSpace ℂ (Fin 2)) 1} :
    hopfSphere2 v = hopfSphere2 w ↔ ∃ c : sphere (0 : ℂ) 1, c • w = v := by
  refine ⟨fun h ↦ ?_, fun ⟨c, hc⟩ ↦ by rw [← hc, hopfSphere2_smul]⟩
  have hcoord (i : Fin 3) := congrArg (fun x : Sphere2 ↦ (x : EuclideanSpace ℝ (Fin 3)) i) h
  have h1 := hcoord 1
  have h2 := hcoord 2
  simp only [coe_hopfSphere2_apply] at h1 h2
  obtain ⟨c, hc, hca, hcb⟩ := exists_norm_eq_one_mul_eq (norm_sq_add_norm_sq v)
    (norm_sq_add_norm_sq w) (by simpa [coe_hopfSphere2_apply] using hcoord 0)
    (Complex.ext (by simpa using h1) (by simpa using h2))
  refine ⟨⟨c, mem_sphere_zero_iff_norm.2 hc⟩, Subtype.ext ?_⟩
  ext i
  fin_cases i <;> simp [hca, hcb]

/-- The Hopf map at `(α, β conj z)`, for real `α`, `β` and a unit complex number `z`. -/
private theorem hopfVector_ofReal_mul_conj (α β : ℝ) {z : ℂ} (hz : ‖z‖ = 1) :
    hopfVector α (β * conj z) = !₂[α ^ 2 - β ^ 2, 2 * α * β * z.re, 2 * α * β * z.im] := by
  have h : (α : ℂ) * conj ((β : ℂ) * conj z) = ((α * β : ℝ) : ℂ) * z := by
    rw [map_mul, Complex.conj_conj, Complex.conj_ofReal]
    push_cast
    ring
  simp only [hopfVector, h, norm_mul, Complex.norm_conj, hz, mul_one, Complex.norm_real,
    Real.norm_eq_abs, sq_abs, Complex.re_ofReal_mul, Complex.im_ofReal_mul, mul_assoc]

/-- **The Hopf map is surjective**: the point `(cos πt, sin πt · z)` of `S²` is the image of
`(cos (πt / 2), sin (πt / 2) conj z)`. -/
theorem hopfSphere2_surjective : Function.Surjective hopfSphere2 := by
  intro x
  obtain ⟨⟨t, z⟩, rfl⟩ := suspensionToSphere_surjective x
  have hz : ‖(z : ℂ)‖ = 1 := Circle.norm_coe z
  set θ := π * (t : ℝ) / 2
  have hθ : π * (t : ℝ) = 2 * θ := by ring
  have hv : ‖(!₂[((cos θ : ℝ) : ℂ), ((sin θ : ℝ) : ℂ) * conj (z : ℂ)] :
      EuclideanSpace ℂ (Fin 2))‖ = 1 := by
    rw [EuclideanSpace.norm_eq, Real.sqrt_eq_one, Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, norm_mul, Complex.norm_conj, hz, mul_one,
      Complex.norm_real, Real.norm_eq_abs, sq_abs,
      cos_sq_add_sin_sq]
  refine ⟨⟨_, mem_sphere_zero_iff_norm.2 hv⟩, Subtype.ext ?_⟩
  rw [coe_hopfSphere2]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [hopfVector_ofReal_mul_conj _ _ hz]
  ext i
  fin_cases i <;>
    simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
      suspensionToSphere_apply_zero, suspensionToSphere_apply_one, suspensionToSphere_apply_two,
      hθ, cos_two_mul, cos_sq', sin_two_mul] <;>
    ring

/-- The Hopf map sends the first standard basis vector `e₀` of `ℂ²` to the north pole. -/
@[simp]
theorem hopfSphere2_single_zero :
    hopfSphere2 ⟨EuclideanSpace.single 0 1, by simp⟩ = Sphere2.north := by
  refine Subtype.ext ?_
  rw [coe_hopfSphere2_apply, Sphere2.coe_north]
  simp

/-- The Hopf map sends the second standard basis vector `e₁` of `ℂ²` to the south pole. -/
@[simp]
theorem hopfSphere2_single_one :
    hopfSphere2 ⟨EuclideanSpace.single 1 1, by simp⟩ = Sphere2.south := by
  refine Subtype.ext ?_
  rw [coe_hopfSphere2_apply, Sphere2.coe_south]
  simp

end Hopf

namespace ComplexProjectiveSpace

/-! ### `CP¹ = S²` -/

section Sphere2

/-- The Hopf map, descended to `CP¹`. -/
private def toSphere2 : ComplexProjectiveSpace 1 → Sphere2 :=
  ComplexProjectiveSpace.lift 1 hopfSphere2 hopfSphere2_smul

private theorem toSphere2_mk (v : sphere (0 : EuclideanSpace ℂ (Fin 2)) 1) :
    toSphere2 (mk 1 v) = hopfSphere2 v :=
  ComplexProjectiveSpace.lift_mk 1 _ _ v

private theorem continuous_toSphere2 : Continuous toSphere2 :=
  (isOpenQuotientMap_mk 1).isQuotientMap.continuous_iff.2 <|
    hopfSphere2.continuous.congr fun v ↦ (toSphere2_mk v).symm

private theorem bijective_toSphere2 : Function.Bijective toSphere2 := by
  refine ⟨fun p q h ↦ ?_, fun x ↦ ?_⟩
  · induction p using ComplexProjectiveSpace.inductionOn with | h v => ?_
    induction q using ComplexProjectiveSpace.inductionOn with | h w => ?_
    rw [toSphere2_mk, toSphere2_mk] at h
    exact (mk_eq_mk_iff 1 v w).2 (hopfSphere2_eq_hopfSphere2_iff.1 h)
  · obtain ⟨v, rfl⟩ := hopfSphere2_surjective x
    exact ⟨mk 1 v, toSphere2_mk v⟩

/-- **`CP¹` is the two-sphere**: the Hopf map `S³ → S²` descends to a homeomorphism from the circle
quotient `CP¹` of `S³`. -/
def homeomorphSphere2 : ComplexProjectiveSpace 1 ≃ₜ Sphere2 :=
  continuous_toSphere2.homeoOfEquivCompactToT2 (f := Equiv.ofBijective _ bijective_toSphere2)

/-- The homeomorphism `CP¹ ≃ₜ S²` sends `[v]` to the image of `v` under the Hopf map. -/
@[simp]
theorem homeomorphSphere2_mk (v : sphere (0 : EuclideanSpace ℂ (Fin 2)) 1) :
    homeomorphSphere2 (mk 1 v) = hopfSphere2 v :=
  toSphere2_mk v

/-- The inverse of `CP¹ ≃ₜ S²` sends the image of `v` under the Hopf map to `[v]`. -/
@[simp]
theorem homeomorphSphere2_symm_hopfSphere2 (v : sphere (0 : EuclideanSpace ℂ (Fin 2)) 1) :
    homeomorphSphere2.symm (hopfSphere2 v) = mk 1 v :=
  homeomorphSphere2.symm_apply_eq.2 (homeomorphSphere2_mk v).symm

/-- The base point `[e₀]` of `CP¹` goes to the north pole. -/
@[simp]
theorem homeomorphSphere2_basePoint : homeomorphSphere2 (basePoint 1) = Sphere2.north := by
  rw [basePoint_def, homeomorphSphere2_mk, hopfSphere2_single_zero]

end Sphere2

/-! ### The projective line of an orthonormal two-frame -/

section Line

variable {n : ℕ}

/-- The unit vector `a f₀ + b f₁` of the plane of an orthonormal two-frame `f`, for a unit vector
`(a, b)` of `ℂ²`. -/
private def lineVector (f : finiteOrthonormalFrame ℂ 2 (n + 1))
    (v : sphere (0 : EuclideanSpace ℂ (Fin 2)) 1) :
    sphere (0 : EuclideanSpace ℂ (Fin (n + 1))) 1 :=
  f.2.synthesisMapIsometry.unitSphereMap v

private theorem coe_lineVector (f : finiteOrthonormalFrame ℂ 2 (n + 1))
    (v : sphere (0 : EuclideanSpace ℂ (Fin 2)) 1) :
    (lineVector f v : EuclideanSpace ℂ (Fin (n + 1))) =
      (v : EuclideanSpace ℂ (Fin 2)) 0 • WithLp.toLp 2 (f.1 0) +
        (v : EuclideanSpace ℂ (Fin 2)) 1 • WithLp.toLp 2 (f.1 1) := by
  simp [lineVector, Fin.sum_univ_two]

private theorem lineVector_smul (f : finiteOrthonormalFrame ℂ 2 (n + 1)) (c : sphere (0 : ℂ) 1)
    (v : sphere (0 : EuclideanSpace ℂ (Fin 2)) 1) : lineVector f (c • v) = c • lineVector f v :=
  Subtype.ext <| by simp [lineVector]

private theorem lineVector_injective (f : finiteOrthonormalFrame ℂ 2 (n + 1)) :
    Function.Injective (lineVector f) :=
  (LinearIsometry.isometry_unitSphereMap _).injective

private theorem continuous_lineVector :
    Continuous fun q : finiteOrthonormalFrame ℂ 2 (n + 1) ×
        sphere (0 : EuclideanSpace ℂ (Fin 2)) 1 ↦
      lineVector q.1 q.2 := by
  refine continuous_induced_rng.2 ?_
  simp only [Function.comp_def, coe_lineVector]
  have hv (i : Fin 2) : Continuous fun q : finiteOrthonormalFrame ℂ 2 (n + 1) ×
      sphere (0 : EuclideanSpace ℂ (Fin 2)) 1 ↦ (q.2 : EuclideanSpace ℂ (Fin 2)) i :=
    (PiLp.continuous_apply 2 _ i).comp (continuous_subtype_val.comp continuous_snd)
  have hf (i : Fin 2) : Continuous fun q : finiteOrthonormalFrame ℂ 2 (n + 1) ×
      sphere (0 : EuclideanSpace ℂ (Fin 2)) 1 ↦
        (WithLp.toLp 2 (q.1.1 i) : EuclideanSpace ℂ (Fin (n + 1))) :=
    (PiLp.continuous_toLp 2 _).comp ((continuous_apply i).comp
      (continuous_subtype_val.comp continuous_fst))
  exact ((hv 0).smul (hf 0)).add ((hv 1).smul (hf 1))

variable (n) in
/-- **The projective line of an orthonormal two-frame**: `(f, [a : b]) ↦ [a f₀ + b f₁]`, as a
jointly continuous map `V₂(ℂⁿ⁺¹) × CP¹ → CPⁿ`. -/
def lineMap :
    C(finiteOrthonormalFrame ℂ 2 (n + 1) × ComplexProjectiveSpace 1, ComplexProjectiveSpace n) where
  toFun q := ComplexProjectiveSpace.lift 1 (fun v ↦ mk n (lineVector q.1 v))
    (fun c v ↦ by rw [lineVector_smul, mk_smul]) q.2
  continuous_toFun := by
    -- `id × mk` is a quotient map, through which the map is `(f, v) ↦ [a f₀ + b f₁]`.
    rw [(IsOpenQuotientMap.id.prodMap (isOpenQuotientMap_mk 1)).isQuotientMap.continuous_iff]
    exact ((continuous_mk n).comp continuous_lineVector).congr fun q ↦
      (ComplexProjectiveSpace.lift_mk 1 (fun v ↦ mk n (lineVector q.1 v)) _ q.2).symm

/-- The projective line of `f` sends `[a : b]` to `[a f₀ + b f₁]`. -/
theorem lineMap_mk (f : finiteOrthonormalFrame ℂ 2 (n + 1))
    (v : sphere (0 : EuclideanSpace ℂ (Fin 2)) 1)
    (x : sphere (0 : EuclideanSpace ℂ (Fin (n + 1))) 1)
    (hx : (x : EuclideanSpace ℂ (Fin (n + 1))) =
      (v : EuclideanSpace ℂ (Fin 2)) 0 • WithLp.toLp 2 (f.1 0) +
        (v : EuclideanSpace ℂ (Fin 2)) 1 • WithLp.toLp 2 (f.1 1)) :
    lineMap n (f, mk 1 v) = mk n x := by
  obtain rfl : x = lineVector f v := Subtype.ext (hx.trans (coe_lineVector f v).symm)
  exact ComplexProjectiveSpace.lift_mk 1 _ _ v

private theorem lineMap_mk_lineVector (f : finiteOrthonormalFrame ℂ 2 (n + 1))
    (v : sphere (0 : EuclideanSpace ℂ (Fin 2)) 1) :
    lineMap n (f, mk 1 v) = mk n (lineVector f v) :=
  lineMap_mk f v _ (coe_lineVector f v)

variable (n) in
/-- **The projective line of an orthonormal two-frame as a two-sphere**: the map
`σ_f : S² → CPⁿ`, `h (a, b) ↦ [a f₀ + b f₁]`, read through `CP¹ ≃ₜ S²`, depending continuously on
the frame `f`. -/
def lineSphereFamily :
    C(finiteOrthonormalFrame ℂ 2 (n + 1), C(Sphere2, ComplexProjectiveSpace n)) :=
  ((lineMap n).comp ((ContinuousMap.id _).prodMap
    (homeomorphSphere2.symm : C(Sphere2, ComplexProjectiveSpace 1)))).curry

/-- The two-sphere of a frame is its projective line, read through `CP¹ ≃ₜ S²`. -/
theorem lineSphereFamily_apply (f : finiteOrthonormalFrame ℂ 2 (n + 1)) (x : Sphere2) :
    lineSphereFamily n f x = lineMap n (f, homeomorphSphere2.symm x) :=
  (rfl)

/-- **The two-sphere of a frame `f` sends `h (a, b)` to `[a f₀ + b f₁]`**, where `h` is the Hopf
map. Since the Hopf map is onto, this determines the two-sphere. -/
theorem lineSphereFamily_apply_hopfSphere2 (f : finiteOrthonormalFrame ℂ 2 (n + 1))
    (v : sphere (0 : EuclideanSpace ℂ (Fin 2)) 1)
    (x : sphere (0 : EuclideanSpace ℂ (Fin (n + 1))) 1)
    (hx : (x : EuclideanSpace ℂ (Fin (n + 1))) =
      (v : EuclideanSpace ℂ (Fin 2)) 0 • WithLp.toLp 2 (f.1 0) +
        (v : EuclideanSpace ℂ (Fin 2)) 1 • WithLp.toLp 2 (f.1 1)) :
    lineSphereFamily n f (hopfSphere2 v) = mk n x := by
  rw [lineSphereFamily_apply, homeomorphSphere2_symm_hopfSphere2, lineMap_mk f v x hx]

private theorem lineSphereFamily_apply_hopfSphere2_lineVector
    (f : finiteOrthonormalFrame ℂ 2 (n + 1)) (v : sphere (0 : EuclideanSpace ℂ (Fin 2)) 1) :
    lineSphereFamily n f (hopfSphere2 v) = mk n (lineVector f v) :=
  lineSphereFamily_apply_hopfSphere2 f v _ (coe_lineVector f v)

/-- **The north pole of the two-sphere of `f` is `[f₀]`.** -/
@[simp]
theorem lineSphereFamily_apply_north (f : finiteOrthonormalFrame ℂ 2 (n + 1)) :
    lineSphereFamily n f Sphere2.north = mk n (f.toSphere 0) := by
  rw [← hopfSphere2_single_zero, lineSphereFamily_apply_hopfSphere2 f _ (f.toSphere 0) (by simp)]

/-- **The south pole of the two-sphere of `f` is `[f₁]`.** -/
@[simp]
theorem lineSphereFamily_apply_south (f : finiteOrthonormalFrame ℂ 2 (n + 1)) :
    lineSphereFamily n f Sphere2.south = mk n (f.toSphere 1) := by
  rw [← hopfSphere2_single_one, lineSphereFamily_apply_hopfSphere2 f _ (f.toSphere 1) (by simp)]

/-- **The family lies over `CPⁿ`**: evaluation at the north pole sends the two-sphere of `f` to
`[f₀]`. -/
theorem mappingSpaceEval_comp_lineSphereFamily :
    mappingSpaceEval Sphere2.north ∘ lineSphereFamily n =
      fun f : finiteOrthonormalFrame ℂ 2 (n + 1) ↦ mk n (f.toSphere 0) :=
  funext fun f ↦ (mappingSpaceEval_apply _ _).trans (lineSphereFamily_apply_north f)

/-- **The two-sphere of a frame is injective**: it parametrizes the projective line of the frame
once. -/
theorem injective_lineSphereFamily (f : finiteOrthonormalFrame ℂ 2 (n + 1)) :
    Function.Injective (lineSphereFamily n f) := by
  intro x y hxy
  obtain ⟨v, rfl⟩ := hopfSphere2_surjective x
  obtain ⟨w, rfl⟩ := hopfSphere2_surjective y
  rw [lineSphereFamily_apply_hopfSphere2_lineVector,
    lineSphereFamily_apply_hopfSphere2_lineVector, mk_eq_mk_iff] at hxy
  obtain ⟨c, hc⟩ := hxy
  rw [← lineVector_smul] at hc
  rw [← lineVector_injective f hc, hopfSphere2_smul]

/-- **The two-sphere depends only on the frame up to a unit scalar**: multiplying both vectors of
`f` by the same unit complex number `c` does not change it. So the family factors through the
quotient of the frames by the diagonal circle, the unit tangent bundle of `CPⁿ`. -/
theorem lineSphereFamily_eq_of_smul (c : sphere (0 : ℂ) 1)
    {f f' : finiteOrthonormalFrame ℂ 2 (n + 1)} (h : ∀ i, f'.1 i = (c : ℂ) • f.1 i) :
    lineSphereFamily n f' = lineSphereFamily n f := by
  ext1 x
  obtain ⟨v, rfl⟩ := hopfSphere2_surjective x
  rw [lineSphereFamily_apply_hopfSphere2 f' v (c • lineVector f v)
      (by simp [coe_lineVector, h, WithLp.toLp_smul, smul_add, smul_comm (c : ℂ)]),
    mk_smul, lineSphereFamily_apply_hopfSphere2_lineVector]

/-- **The family is equivariant under the unitary group**: applying a unitary matrix `A` to the
frame moves its two-sphere by `A`. -/
theorem lineSphereFamily_unitaryMap (A : unitaryGroup (Fin (n + 1)) ℂ)
    (f : finiteOrthonormalFrame ℂ 2 (n + 1)) (x : Sphere2) :
    lineSphereFamily n (finiteOrthonormalFrame.unitaryMap A f) x = A • lineSphereFamily n f x := by
  obtain ⟨v, rfl⟩ := hopfSphere2_surjective x
  rw [lineSphereFamily_apply_hopfSphere2_lineVector f v, smul_mk]
  refine lineSphereFamily_apply_hopfSphere2 _ v _ ?_
  simp [coe_lineVector, Matrix.mulVec_add, Matrix.mulVec_smul]

/-- **On `CP¹`, the two-sphere of every frame is a bijection `S² → CP¹`**: an orthonormal two-frame
of `ℂ²` is a basis, so every complex line of `ℂ²` is spanned by some `a f₀ + b f₁`. -/
theorem bijective_lineSphereFamily (f : finiteOrthonormalFrame ℂ 2 2) :
    Function.Bijective (lineSphereFamily 1 f) := by
  refine ⟨injective_lineSphereFamily f, fun p ↦ ?_⟩
  induction p using ComplexProjectiveSpace.inductionOn with | h y => ?_
  -- The coordinate isometry of the frame is an injective endomorphism of `ℂ²`, hence onto.
  obtain ⟨x, hx⟩ := LinearMap.surjective_of_injective
    (f := f.2.synthesisMapIsometry.toLinearMap) f.2.synthesisMapIsometry.injective
    (y : EuclideanSpace ℂ (Fin 2))
  have hx1 : x ∈ sphere (0 : EuclideanSpace ℂ (Fin 2)) 1 := by
    rw [mem_sphere_zero_iff_norm, ← f.2.synthesisMapIsometry.norm_map]
    exact (congrArg norm hx).trans (norm_eq_of_mem_sphere y)
  refine ⟨hopfSphere2 ⟨x, hx1⟩, ?_⟩
  rw [lineSphereFamily_apply_hopfSphere2_lineVector]
  exact congrArg (mk 1) (Subtype.ext (by simpa [lineVector] using hx))

/-- **The family of two-spheres through a point.** For a unit vector `u = f₀` of `ℂⁿ⁺¹`, the unit
vectors `w` of the complex orthogonal complement of `u` parametrize the unit tangent vectors of
`CPⁿ` at `[u]`; the two-sphere of the frame `(u, w)` is the projective line through `[u]` tangent
to `w`, a based map `(S², north) → (CPⁿ, [u])`. -/
def lineSphereFamilyFiber (f : finiteOrthonormalFrame ℂ 1 (n + 1)) :
    C(sphere (0 : f.complement) 1,
      BasedMap Sphere2 (ComplexProjectiveSpace n) Sphere2.north (mk n (f.toSphere 0))) where
  toFun w := ⟨lineSphereFamily n (f.snoc w),
    (lineSphereFamily_apply_north _).trans
      (congrArg (mk n) (f.toSphere_snoc_castSucc w 0))⟩
  continuous_toFun :=
    ((lineSphereFamily n).continuous.comp (finiteOrthonormalFrame.continuous_snoc f)).subtype_mk _

/-- On the fibre over `[u]`, the family of two-spheres is the two-sphere of the frame `(u, w)`. -/
@[simp]
theorem coe_lineSphereFamilyFiber_apply (f : finiteOrthonormalFrame ℂ 1 (n + 1))
    (w : sphere (0 : f.complement) 1) :
    (lineSphereFamilyFiber f w : C(Sphere2, ComplexProjectiveSpace n)) =
      lineSphereFamily n (f.snoc w) :=
  (rfl)

/-- The two-sphere through `[u]` tangent to `w` sends `h (a, b)` to `[a u + b w]`. -/
theorem lineSphereFamilyFiber_apply_hopfSphere2 (f : finiteOrthonormalFrame ℂ 1 (n + 1))
    (w : sphere (0 : f.complement) 1) (v : sphere (0 : EuclideanSpace ℂ (Fin 2)) 1)
    (x : sphere (0 : EuclideanSpace ℂ (Fin (n + 1))) 1)
    (hx : (x : EuclideanSpace ℂ (Fin (n + 1))) =
      (v : EuclideanSpace ℂ (Fin 2)) 0 • WithLp.toLp 2 (f.1 0) +
        (v : EuclideanSpace ℂ (Fin 2)) 1 • (w : EuclideanSpace ℂ (Fin (n + 1)))) :
    (lineSphereFamilyFiber f w : C(Sphere2, ComplexProjectiveSpace n)) (hopfSphere2 v) =
      mk n x := by
  rw [coe_lineSphereFamilyFiber_apply]
  refine lineSphereFamily_apply_hopfSphere2 _ v x ?_
  rw [hx]
  congr 2
  · simpa using (congrArg (WithLp.toLp 2) (f.snoc_castSucc w 0)).symm
  · simpa using (congrArg (WithLp.toLp 2) (f.snoc_last w)).symm

end Line

end ComplexProjectiveSpace

end TauCeti
