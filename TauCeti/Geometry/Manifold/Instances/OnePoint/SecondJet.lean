/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import TauCeti.Geometry.Manifold.Instances.OnePoint.FirstJet
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.ZPow
import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import TauCeti.Geometry.Manifold.MFDeriv.Chart.Deriv

/-!
# Second jets of Möbius transformations

Let `𝕜` be a proper nontrivially normed field, such as `ℂ`. This file computes the second
derivatives of Möbius transformations of the projective line `OnePoint 𝕜`, read in its preferred
charts (`writtenInExtChartAt`), and shows that a Möbius transformation is determined by its value,
derivative and second derivative at `0`. The derivative of the chart expression on `𝕜` is the
derivative `mfderiv` on the tangent vector `1` used for the first-jet coordinates in
`TauCeti.Geometry.Manifold.Instances.OnePoint.FirstJet`
(`MDifferentiableAt.mfderiv_apply_one_eq_deriv_writtenInExtChartAt`).

* At a finite point `z` with finite image, the second derivative of
  `z ↦ (a z + b) / (c z + d)` is `-2 c (a d - b c) / (c z + d) ^ 3`
  (`Matrix.GeneralLinearGroup.iteratedDeriv_two_writtenInExtChartAt_smul_coe`).
* **Composition laws.** Read in charts, the derivative of a product `g * h` at a point `x` is
  `g'(h x) h'(x)` (`OnePoint.deriv_writtenInExtChartAt_mul_smul`), while its second derivative is
  `g''(h x) h'(x) ^ 2 + g'(h x) h''(x)`
  (`OnePoint.iteratedDeriv_two_writtenInExtChartAt_mul_smul`), so second jets do not transform
  linearly. These are the chain rules in charts of `TauCeti.Manifold.deriv_writtenInExtChartAt_comp`
  and `TauCeti.Manifold.iteratedDeriv_two_writtenInExtChartAt_comp`, applied to Möbius
  transformations. Taking for `h` an element fixing `x`, these laws say how the jet at `x`
  changes under a Möbius reparametrization of the source fixing `x`; taking for `g` an element
  fixing `h • x`, how it changes under a Möbius reparametrization of the target.
* **Second-jet coordinates.** In characteristic different from two, for every point `p`, every
  nonzero `v` and every `w`, exactly one element of `PGL(2, 𝕜)` sends `0` to `p` and has, in the
  affine chart at `0` and the preferred chart at `p`, derivative `v` and second derivative `w` at
  `0` (`OnePoint.existsUnique_pgl_smul_zero_deriv_iteratedDeriv_eq`). So
  `g ↦ (g • 0, g'(0), g''(0))` identifies `PGL(2, 𝕜)` with the triples of a point, a nonzero
  first derivative and an arbitrary second derivative. This is the analogue, with two points
  replaced by the first and second derivatives at the remaining one, of the parametrization of
  `PGL(2, 𝕜)` by ordered triples of distinct points
  (`OnePoint.existsUnique_pgl_smul_zero_one_infty_eq`), and of the first-jet coordinates
  (`OnePoint.existsUnique_pgl_smul_zero_infty_mfderiv_eq`). Taking `p = 0`, it identifies the
  stabilizer of `0` with the pairs `(v, w)` with `v ≠ 0`. The derivative of a Möbius
  transformation in charts never vanishes (`OnePoint.deriv_writtenInExtChartAt_pgl_smul_ne_zero`),
  so these coordinates form an equivalence `PGL(2, 𝕜) ≃ OnePoint 𝕜 × 𝕜ˣ × 𝕜`
  (`OnePoint.pglSecondJetEquiv`).
* **Change of target chart.** When `g • z₀ = p` is finite and nonzero at a finite point `z₀`,
  both the affine chart and the inverted chart `z ↦ z⁻¹` apply at `p`. Read in the inverted chart,
  the first and second derivatives `v` and `w` at `z₀` become `-v / p ^ 2`, as computed in
  `TauCeti.Geometry.Manifold.Instances.OnePoint.FirstJet` (`OnePoint.deriv_invChart_pgl_smul_coe`),
  and `2 v ^ 2 / p ^ 3 - w / p ^ 2` (`OnePoint.iteratedDeriv_two_invChart_pgl_smul_coe`).

The proof of the second-jet coordinates
(`OnePoint.existsUnique_pgl_smul_zero_deriv_iteratedDeriv_eq`) reduces to the stabilizer of `0`:
its elements are the transformations `z ↦ a z / (c z + 1)` with `a ≠ 0`, whose derivative and
second derivative at `0` are `a` and `-2 c a`, and the composition laws move these coordinates
to any other element sending `0` to `p`. In characteristic two every second derivative of a
Möbius transformation vanishes, so the second jet carries no information there.

For the Riemann sphere, where `PGL(2, ℂ)` is the group of automorphisms, these coordinates
normalize the reparametrizations of a genus-zero domain carrying one marked point and a second
jet there, in the way that ordered triples normalize three marked points.

## Main definitions

* `OnePoint.pglSecondJetEquiv`: the second-jet coordinates `PGL(2, 𝕜) ≃ OnePoint 𝕜 × 𝕜ˣ × 𝕜`.

## Main results

* `Matrix.GeneralLinearGroup.iteratedDeriv_two_writtenInExtChartAt_smul_coe`: the second
  derivative of a Möbius transformation at a finite point with finite image.
* `OnePoint.deriv_writtenInExtChartAt_mul_smul` and
  `OnePoint.iteratedDeriv_two_writtenInExtChartAt_mul_smul`: the first- and second-order chain
  rules for a product of Möbius transformations.
* `OnePoint.existsUnique_pgl_smul_zero_deriv_iteratedDeriv_eq`: the second-jet coordinates of
  `PGL(2, 𝕜)`.
* `OnePoint.pglSecondJetEquiv_symm_smul_zero`,
  `OnePoint.deriv_writtenInExtChartAt_pglSecondJetEquiv_symm` and
  `OnePoint.iteratedDeriv_two_writtenInExtChartAt_pglSecondJetEquiv_symm`: the Möbius
  transformation with second jet `(p, v, w)` has value `p`, derivative `v` and second derivative
  `w` at `0`.
* `OnePoint.iteratedDeriv_two_invChart_pgl_smul_coe`: the change of the second derivative from
  the affine to the inverted chart at the target.

## References

* Otto Forster, *Lectures on Riemann Surfaces*, Graduate Texts in Mathematics 81,
  Springer, 1981, §§1–2.
* Alan Beardon, *The Geometry of Discrete Groups*, Graduate Texts in Mathematics 91,
  Springer, 1983, §§3.2 and 4.3.
-/

public section

open Filter Matrix MulAction Set Topology

open scoped Manifold MatrixGroups ContDiff

namespace Matrix.GeneralLinearGroup

open OnePoint

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [DecidableEq 𝕜] [ProperSpace 𝕜]

/-- Near a finite point `z` that is not a pole, the derivative of a Möbius transformation read in
the affine charts is `w ↦ (a d - b c) / (c w + d) ^ 2`. -/
private theorem deriv_writtenInExtChartAt_smul_coe_eventuallyEq (g : GL (Fin 2) 𝕜) {z : 𝕜}
    (hz : g 1 0 * z + g 1 1 ≠ 0) :
    deriv (writtenInExtChartAt 𝓘(𝕜) 𝓘(𝕜) (z : OnePoint 𝕜) fun x ↦ g • x) =ᶠ[𝓝 z]
      fun w ↦ (g : Matrix (Fin 2) (Fin 2) 𝕜).det / (g 1 0 * w + g 1 1) ^ 2 := by
  have hq : Continuous fun w : 𝕜 ↦ g 1 0 * w + g 1 1 := by fun_prop
  -- Near each such `w`, the chart expressions at `z` and at `w` are the same rational function.
  filter_upwards [(writtenInExtChartAt_smul_coe_eventuallyEq g hz).eventually_nhds,
    hq.continuousAt.eventually_ne hz] with w hw hw0
  rw [(EventuallyEq.trans hw (writtenInExtChartAt_smul_coe_eventuallyEq g hw0).symm).deriv_eq,
    (hasDerivAt_writtenInExtChartAt_smul_coe g hw0).deriv]

/-- **The second derivative of a Möbius transformation.** At a finite point `z` that is not a
pole, `z ↦ (a z + b) / (c z + d)` has second derivative `-2 c (a d - b c) / (c z + d) ^ 3`, read
in the affine charts at `z` and at its image. -/
theorem iteratedDeriv_two_writtenInExtChartAt_smul_coe (g : GL (Fin 2) 𝕜) {z : 𝕜}
    (hz : g 1 0 * z + g 1 1 ≠ 0) :
    iteratedDeriv 2 (writtenInExtChartAt 𝓘(𝕜) 𝓘(𝕜) (z : OnePoint 𝕜) fun x ↦ g • x) z =
      -2 * g 1 0 * (g : Matrix (Fin 2) (Fin 2) 𝕜).det / (g 1 0 * z + g 1 1) ^ 3 := by
  have hq' : HasDerivAt (fun w : 𝕜 ↦ g 1 0 * w + g 1 1) (g 1 0) z := by
    simpa using ((hasDerivAt_id z).const_mul (g 1 0)).add_const (g 1 1)
  have hsecond := (hasDerivAt_const z (g : Matrix (Fin 2) (Fin 2) 𝕜).det).fun_div
    (hq'.fun_pow 2) (pow_ne_zero 2 hz)
  rw [iteratedDeriv_succ, iteratedDeriv_one,
    (deriv_writtenInExtChartAt_smul_coe_eventuallyEq g hz).deriv_eq, hsecond.deriv]
  field_simp
  ring

end Matrix.GeneralLinearGroup

namespace OnePoint

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [DecidableEq 𝕜] [ProperSpace 𝕜]

/-- A Möbius transformation of `PGL(2, 𝕜)` is `C^n` for every `n`. -/
private theorem contMDiffAt_pgl_smul {n : WithTop ℕ∞} (g : PGL(2, 𝕜)) (x : OnePoint 𝕜) :
    ContMDiffAt 𝓘(𝕜) 𝓘(𝕜) n (fun y ↦ g • y) x :=
  (contMDiff_const_smul (I := 𝓘(𝕜)) (n := ω) g).of_le le_top x

omit [ProperSpace 𝕜] in
private theorem pgl_mul_smul_eq_comp (g h : PGL(2, 𝕜)) :
    (fun y : OnePoint 𝕜 ↦ (g * h) • y) = (fun y ↦ g • y) ∘ fun y ↦ h • y :=
  funext fun y ↦ mul_smul g h y

/-- **The chain rule for Möbius transformations.** Read in the preferred charts, the derivative
of `g * h` at `x` is `g'(h x) h'(x)`. -/
theorem deriv_writtenInExtChartAt_mul_smul (g h : PGL(2, 𝕜)) (x : OnePoint 𝕜) :
    deriv (writtenInExtChartAt 𝓘(𝕜) 𝓘(𝕜) x fun y ↦ (g * h) • y) (extChartAt 𝓘(𝕜) x x) =
      deriv (writtenInExtChartAt 𝓘(𝕜) 𝓘(𝕜) (h • x) fun y ↦ g • y)
          (extChartAt 𝓘(𝕜) (h • x) (h • x)) *
        deriv (writtenInExtChartAt 𝓘(𝕜) 𝓘(𝕜) x fun y ↦ h • y) (extChartAt 𝓘(𝕜) x x) := by
  rw [pgl_mul_smul_eq_comp, TauCeti.Manifold.deriv_writtenInExtChartAt_comp
    ((contMDiffAt_pgl_smul (n := 1) g _).mdifferentiableAt one_ne_zero)
    ((contMDiffAt_pgl_smul (n := 1) h x).mdifferentiableAt one_ne_zero), smul_eq_mul, mul_comm]

/-- **The second-order chain rule for Möbius transformations.** Read in the preferred charts, the
second derivative of `g * h` at `x` is `g''(h x) h'(x) ^ 2 + g'(h x) h''(x)`. -/
theorem iteratedDeriv_two_writtenInExtChartAt_mul_smul (g h : PGL(2, 𝕜)) (x : OnePoint 𝕜) :
    iteratedDeriv 2 (writtenInExtChartAt 𝓘(𝕜) 𝓘(𝕜) x fun y ↦ (g * h) • y)
        (extChartAt 𝓘(𝕜) x x) =
      iteratedDeriv 2 (writtenInExtChartAt 𝓘(𝕜) 𝓘(𝕜) (h • x) fun y ↦ g • y)
          (extChartAt 𝓘(𝕜) (h • x) (h • x)) *
          deriv (writtenInExtChartAt 𝓘(𝕜) 𝓘(𝕜) x fun y ↦ h • y) (extChartAt 𝓘(𝕜) x x) ^ 2 +
        deriv (writtenInExtChartAt 𝓘(𝕜) 𝓘(𝕜) (h • x) fun y ↦ g • y)
            (extChartAt 𝓘(𝕜) (h • x) (h • x)) *
          iteratedDeriv 2 (writtenInExtChartAt 𝓘(𝕜) 𝓘(𝕜) x fun y ↦ h • y)
            (extChartAt 𝓘(𝕜) x x) := by
  rw [pgl_mul_smul_eq_comp, TauCeti.Manifold.iteratedDeriv_two_writtenInExtChartAt_comp
    (contMDiffAt_pgl_smul g _) (contMDiffAt_pgl_smul h x), smul_eq_mul, smul_eq_mul]
  ring

omit [DecidableEq 𝕜] in
/-- The affine chart at `0` sends `0` to `0`. -/
private theorem extChartAt_coe_zero_self :
    extChartAt 𝓘(𝕜) ((0 : 𝕜) : OnePoint 𝕜) ((0 : 𝕜) : OnePoint 𝕜) = 0 := by
  simp

/-- The Möbius transformation `z ↦ a z / (c z + 1)`, which fixes `0`. -/
private noncomputable def stabZero (a : 𝕜ˣ) (c : 𝕜) : PGL(2, 𝕜) :=
  ProjGenLinGroup.mk (GeneralLinearGroup.mkOfDetNeZero !![(a : 𝕜), 0; c, 1] (by simp))

omit [ProperSpace 𝕜] in
private theorem stabZero_smul_zero (a : 𝕜ˣ) (c : 𝕜) :
    stabZero a c • ((0 : 𝕜) : OnePoint 𝕜) = ((0 : 𝕜) : OnePoint 𝕜) := by
  simp [stabZero, smul_some_eq_ite, GeneralLinearGroup.mkOfDetNeZero]

private theorem deriv_stabZero_smul_zero (a : 𝕜ˣ) (c : 𝕜) :
    deriv (writtenInExtChartAt 𝓘(𝕜) 𝓘(𝕜) ((0 : 𝕜) : OnePoint 𝕜)
      fun y ↦ stabZero a c • y) 0 = a := by
  simp only [stabZero, pglMk_smul]
  rw [(GeneralLinearGroup.deriv_writtenInExtChartAt_smul_coe_eventuallyEq _
    (by simp [GeneralLinearGroup.mkOfDetNeZero])).eq_of_nhds]
  simp [GeneralLinearGroup.mkOfDetNeZero]

private theorem iteratedDeriv_two_stabZero_smul_zero (a : 𝕜ˣ) (c : 𝕜) :
    iteratedDeriv 2 (writtenInExtChartAt 𝓘(𝕜) 𝓘(𝕜) ((0 : 𝕜) : OnePoint 𝕜)
      fun y ↦ stabZero a c • y) 0 = -2 * c * a := by
  simp only [stabZero, pglMk_smul]
  rw [GeneralLinearGroup.iteratedDeriv_two_writtenInExtChartAt_smul_coe _
    (by simp [GeneralLinearGroup.mkOfDetNeZero])]
  simp [GeneralLinearGroup.mkOfDetNeZero]

omit [ProperSpace 𝕜] in
/-- Every element of `PGL(2, 𝕜)` fixing `0` is a transformation `z ↦ a z / (c z + 1)`. -/
private theorem exists_eq_stabZero {k : PGL(2, 𝕜)}
    (hk : k • ((0 : 𝕜) : OnePoint 𝕜) = ((0 : 𝕜) : OnePoint 𝕜)) :
    ∃ (a : 𝕜ˣ) (c : 𝕜), k = stabZero a c := by
  obtain ⟨M, rfl⟩ := ProjGenLinGroup.mk_surjective k
  rw [pglMk_smul, smul_some_eq_ite] at hk
  simp only [mul_zero, zero_add] at hk
  split_ifs at hk with hd
  · exact absurd hk (infty_ne_coe 0)
  have hb : M 0 1 = 0 := by simpa [hd] using hk
  have hdet := M.det_ne_zero
  rw [det_fin_two, hb, zero_mul, sub_zero] at hdet
  refine ⟨Units.mk0 (M 0 0 / M 1 1) (div_ne_zero (left_ne_zero_of_mul hdet) hd),
    M 1 0 / M 1 1, (ProjGenLinGroup.mk_eq_mk_iff.2 ⟨Units.mk0 (M 1 1) hd, Units.ext ?_⟩).symm⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [GeneralLinearGroup.mkOfDetNeZero, hb, hd, Matrix.mul_apply, Fin.sum_univ_two]

/-- Precomposing with `z ↦ a z / (c z + 1)` multiplies the derivative at `0` by `a` and moves the
second derivative at `0` from `w` to `w a ^ 2 - 2 c a v`, where `v` is the derivative at `0`. -/
private theorem jets_mul_stabZero (g : PGL(2, 𝕜)) (a : 𝕜ˣ) (c : 𝕜) :
    (g * stabZero a c) • ((0 : 𝕜) : OnePoint 𝕜) = g • ((0 : 𝕜) : OnePoint 𝕜) ∧
      deriv (writtenInExtChartAt 𝓘(𝕜) 𝓘(𝕜) ((0 : 𝕜) : OnePoint 𝕜)
          fun y ↦ (g * stabZero a c) • y) 0 =
        deriv (writtenInExtChartAt 𝓘(𝕜) 𝓘(𝕜) ((0 : 𝕜) : OnePoint 𝕜) fun y ↦ g • y) 0 * a ∧
      iteratedDeriv 2 (writtenInExtChartAt 𝓘(𝕜) 𝓘(𝕜) ((0 : 𝕜) : OnePoint 𝕜)
          fun y ↦ (g * stabZero a c) • y) 0 =
        iteratedDeriv 2 (writtenInExtChartAt 𝓘(𝕜) 𝓘(𝕜) ((0 : 𝕜) : OnePoint 𝕜)
            fun y ↦ g • y) 0 * (a : 𝕜) ^ 2 +
          deriv (writtenInExtChartAt 𝓘(𝕜) 𝓘(𝕜) ((0 : 𝕜) : OnePoint 𝕜) fun y ↦ g • y) 0 *
            (-2 * c * a) := by
  have h0 := stabZero_smul_zero a c
  have hd := deriv_writtenInExtChartAt_mul_smul g (stabZero a c) ((0 : 𝕜) : OnePoint 𝕜)
  have hdd := iteratedDeriv_two_writtenInExtChartAt_mul_smul g (stabZero a c)
    ((0 : 𝕜) : OnePoint 𝕜)
  rw [h0, extChartAt_coe_zero_self, deriv_stabZero_smul_zero] at hd
  rw [h0, extChartAt_coe_zero_self, deriv_stabZero_smul_zero,
    iteratedDeriv_two_stabZero_smul_zero] at hdd
  exact ⟨by rw [mul_smul, h0], hd, hdd⟩

/-- **Second-jet coordinates of `PGL(2, 𝕜)`.** In characteristic different from two, for a point
`p` of the projective line, a nonzero `v` and any `w`, exactly one Möbius transformation sends `0`
to `p` and has, read in the affine chart at `0` and the preferred chart at `p`, derivative `v` and
second derivative `w` at `0`. -/
theorem existsUnique_pgl_smul_zero_deriv_iteratedDeriv_eq [NeZero (2 : 𝕜)] (p : OnePoint 𝕜)
    {v : 𝕜} (hv : v ≠ 0) (w : 𝕜) :
    ∃! g : PGL(2, 𝕜), g • ((0 : 𝕜) : OnePoint 𝕜) = p ∧
      deriv (writtenInExtChartAt 𝓘(𝕜) 𝓘(𝕜) ((0 : 𝕜) : OnePoint 𝕜) fun y ↦ g • y) 0 = v ∧
      iteratedDeriv 2 (writtenInExtChartAt 𝓘(𝕜) 𝓘(𝕜) ((0 : 𝕜) : OnePoint 𝕜)
        fun y ↦ g • y) 0 = w := by
  -- Some transformation `g₁` sends `0` to `p`; every other one is `g₁` followed by an element
  -- `z ↦ a z / (c z + 1)` of the stabilizer of `0`, and the jets determine `a` and `c`.
  obtain ⟨g₀, hg₀⟩ := exists_smul_eq PSL(2, 𝕜) ((0 : 𝕜) : OnePoint 𝕜) p
  set g₁ := ProjectiveSpecialLinearGroup.toPGL g₀
  have hg₁ : g₁ • ((0 : 𝕜) : OnePoint 𝕜) = p := by
    rw [ProjectiveSpecialLinearGroup.toPGL_smul, hg₀]
  obtain ⟨v₁, hv₁e⟩ : ∃ v₁, deriv (writtenInExtChartAt 𝓘(𝕜) 𝓘(𝕜) ((0 : 𝕜) : OnePoint 𝕜)
      fun y ↦ g₁ • y) 0 = v₁ := ⟨_, rfl⟩
  obtain ⟨w₁, hw₁e⟩ : ∃ w₁, iteratedDeriv 2 (writtenInExtChartAt 𝓘(𝕜) 𝓘(𝕜)
      ((0 : 𝕜) : OnePoint 𝕜) fun y ↦ g₁ • y) 0 = w₁ := ⟨_, rfl⟩
  have hv₁ : v₁ ≠ 0 := hv₁e ▸ deriv_writtenInExtChartAt_pgl_smul_coe_ne_zero g₁ 0
  have h2 : (2 : 𝕜) ≠ 0 := two_ne_zero
  set a : 𝕜ˣ := Units.mk0 (v / v₁) (div_ne_zero hv hv₁)
  have ha : (a : 𝕜) = v / v₁ := rfl
  have ha0 : (a : 𝕜) ≠ 0 := a.ne_zero
  set c : 𝕜 := (w₁ * (a : 𝕜) ^ 2 - w) / (2 * v₁ * a)
  have hc : w₁ * (a : 𝕜) ^ 2 + v₁ * (-2 * c * a) = w := by
    simp only [c]
    field_simp
    ring
  obtain ⟨hp, hd, hdd⟩ := jets_mul_stabZero g₁ a c
  rw [hv₁e] at hd hdd
  rw [hw₁e] at hdd
  refine ⟨g₁ * stabZero a c, ⟨hp.trans hg₁, ?_, ?_⟩, ?_⟩
  · rw [hd, ha]
    field_simp
  · rw [hdd, hc]
  · rintro g ⟨hg0, hgd, hgdd⟩
    have hk : (g₁⁻¹ * g) • ((0 : 𝕜) : OnePoint 𝕜) = ((0 : 𝕜) : OnePoint 𝕜) := by
      rw [mul_smul, hg0, ← hg₁, inv_smul_smul]
    obtain ⟨a', c', hk'⟩ := exists_eq_stabZero hk
    have hg : g = g₁ * stabZero a' c' := by rw [← hk', mul_inv_cancel_left]
    obtain ⟨-, hd', hdd'⟩ := jets_mul_stabZero g₁ a' c'
    rw [← hg, hgd, hv₁e] at hd'
    rw [← hg, hgdd, hv₁e, hw₁e, ← hc] at hdd'
    have haa : a' = a := Units.ext (by rw [ha, hd']; field_simp)
    subst haa
    have hcc : c' = c := by
      have : v₁ * (-2 * (a : 𝕜)) * (c' - c) = 0 := by linear_combination -hdd'
      simpa [hv₁, h2, ha0, sub_eq_zero] using this
    rw [hg, hcc]

/-- **The second-jet coordinates of `PGL(2, 𝕜)`.** In characteristic different from two, a Möbius
transformation `g` corresponds to the image `g • 0` and the derivative and second derivative at
`0` of `g`, read in the affine chart at `0` and the preferred chart at `g • 0`. -/
noncomputable def pglSecondJetEquiv [NeZero (2 : 𝕜)] : PGL(2, 𝕜) ≃ OnePoint 𝕜 × 𝕜ˣ × 𝕜 :=
  Equiv.ofBijective
    (fun g ↦ (g • ((0 : 𝕜) : OnePoint 𝕜),
      Units.mk0 _ (deriv_writtenInExtChartAt_pgl_smul_coe_ne_zero g 0),
      iteratedDeriv 2 (writtenInExtChartAt 𝓘(𝕜) 𝓘(𝕜) ((0 : 𝕜) : OnePoint 𝕜)
        fun y ↦ g • y) 0))
    ⟨fun g h hgh ↦ by
      simp only [Prod.mk.injEq, Units.ext_iff, Units.val_mk0] at hgh
      exact (existsUnique_pgl_smul_zero_deriv_iteratedDeriv_eq _
        (deriv_writtenInExtChartAt_pgl_smul_coe_ne_zero g 0) _).unique ⟨rfl, rfl, rfl⟩
          ⟨hgh.1.symm, hgh.2.1.symm, hgh.2.2.symm⟩,
    fun ⟨p, v, w⟩ ↦ by
      obtain ⟨g, hg0, hg1, hg2⟩ :=
        (existsUnique_pgl_smul_zero_deriv_iteratedDeriv_eq p v.ne_zero w).exists
      exact ⟨g, Prod.ext hg0 (Prod.ext (Units.ext hg1) hg2)⟩⟩

@[simp]
theorem pglSecondJetEquiv_apply [NeZero (2 : 𝕜)] (g : PGL(2, 𝕜)) :
    pglSecondJetEquiv g = (g • ((0 : 𝕜) : OnePoint 𝕜),
      Units.mk0 _ (deriv_writtenInExtChartAt_pgl_smul_coe_ne_zero g 0),
      iteratedDeriv 2 (writtenInExtChartAt 𝓘(𝕜) 𝓘(𝕜) ((0 : 𝕜) : OnePoint 𝕜)
        fun y ↦ g • y) 0) :=
  (rfl)

/-- The Möbius transformation with second jet `x = (p, v, w)` at `0` sends `0` to `p`. -/
@[simp]
theorem pglSecondJetEquiv_symm_smul_zero [NeZero (2 : 𝕜)] (x : OnePoint 𝕜 × 𝕜ˣ × 𝕜) :
    pglSecondJetEquiv.symm x • ((0 : 𝕜) : OnePoint 𝕜) = x.1 :=
  congrArg Prod.fst (pglSecondJetEquiv.apply_symm_apply x)

/-- The Möbius transformation with second jet `x = (p, v, w)` at `0` has derivative `v` at `0`. -/
theorem deriv_writtenInExtChartAt_pglSecondJetEquiv_symm [NeZero (2 : 𝕜)]
    (x : OnePoint 𝕜 × 𝕜ˣ × 𝕜) :
    deriv (writtenInExtChartAt 𝓘(𝕜) 𝓘(𝕜) ((0 : 𝕜) : OnePoint 𝕜)
      fun y ↦ pglSecondJetEquiv.symm x • y) 0 = x.2.1 :=
  congrArg (fun x ↦ (x.2.1 : 𝕜)) (pglSecondJetEquiv.apply_symm_apply x)

/-- The Möbius transformation with second jet `x = (p, v, w)` at `0` has second derivative `w` at
`0`. -/
theorem iteratedDeriv_two_writtenInExtChartAt_pglSecondJetEquiv_symm [NeZero (2 : 𝕜)]
    (x : OnePoint 𝕜 × 𝕜ˣ × 𝕜) :
    iteratedDeriv 2 (writtenInExtChartAt 𝓘(𝕜) 𝓘(𝕜) ((0 : 𝕜) : OnePoint 𝕜)
      fun y ↦ pglSecondJetEquiv.symm x • y) 0 = x.2.2 :=
  congrArg (fun x ↦ x.2.2) (pglSecondJetEquiv.apply_symm_apply x)

/-! ### Changing the chart at the target -/

private theorem contDiffAt_writtenInExtChartAt_pgl_smul_coe {n : WithTop ℕ∞} (g : PGL(2, 𝕜))
    (z : 𝕜) :
    ContDiffAt 𝕜 n (writtenInExtChartAt 𝓘(𝕜) 𝓘(𝕜) (z : OnePoint 𝕜) fun y ↦ g • y) z := by
  have h : extChartAt 𝓘(𝕜) (z : OnePoint 𝕜) (z : OnePoint 𝕜) = z := by simp
  simpa only [h] using
    (contMDiffAt_pgl_smul (n := n) g (z : OnePoint 𝕜)).contDiffAt_writtenInExtChartAt

/-- **Second jets in the inverted chart.** When `g • z₀ = p` is finite and nonzero, reading `g` in
the inverted chart at `p` instead of the affine chart changes its second derivative at `z₀` from
`w` to `2 v ^ 2 / p ^ 3 - w / p ^ 2`, where `v` is its derivative at `z₀`. -/
theorem iteratedDeriv_two_invChart_pgl_smul_coe {g : PGL(2, 𝕜)} {z₀ p : 𝕜} (hp0 : p ≠ 0)
    (hp : g • (z₀ : OnePoint 𝕜) = p) :
    iteratedDeriv 2 (fun z : 𝕜 ↦ invChart (g • (z : OnePoint 𝕜))) z₀ =
      2 * deriv (writtenInExtChartAt 𝓘(𝕜) 𝓘(𝕜) (z₀ : OnePoint 𝕜) fun y ↦ g • y) z₀ ^ 2 /
          p ^ 3 -
        iteratedDeriv 2 (writtenInExtChartAt 𝓘(𝕜) 𝓘(𝕜) (z₀ : OnePoint 𝕜)
          fun y ↦ g • y) z₀ / p ^ 2 := by
  have h0 : writtenInExtChartAt 𝓘(𝕜) 𝓘(𝕜) (z₀ : OnePoint 𝕜) (fun y ↦ g • y) z₀ = p :=
    writtenInExtChartAt_coe_self_of_eq_coe hp
  have hinv : ContDiffAt 𝕜 2 (fun x : 𝕜 ↦ x⁻¹)
      (writtenInExtChartAt 𝓘(𝕜) 𝓘(𝕜) (z₀ : OnePoint 𝕜) (fun y ↦ g • y) z₀) := by
    rw [h0]
    exact contDiffAt_inv 𝕜 hp0
  have hcomp := iteratedDeriv_comp_two hinv (contDiffAt_writtenInExtChartAt_pgl_smul_coe g z₀)
  rw [h0] at hcomp
  have hd2 : iteratedDeriv 2 (fun x : 𝕜 ↦ x⁻¹) p = 2 / p ^ 3 := by
    rw [iteratedDeriv_eq_iterate, iter_deriv_inv]
    simp only [even_two, Even.neg_pow, one_pow, Nat.factorial_two, Nat.cast_ofNat, one_mul,
      Int.reduceNeg, Int.reduceSub, _root_.zpow_neg, zpow_ofNat]
    ring
  have hfun : (fun z : 𝕜 ↦ invChart (g • (z : OnePoint 𝕜))) =
      (fun x : 𝕜 ↦ x⁻¹) ∘
        writtenInExtChartAt 𝓘(𝕜) 𝓘(𝕜) (z₀ : OnePoint 𝕜) (fun y ↦ g • y) :=
    funext (invChart_eq_inv_writtenInExtChartAt_coe (f := fun y ↦ g • y) (hp ▸ coe_ne_infty p))
  rw [hfun, hcomp, hd2, deriv_inv]
  field_simp
  ring

end OnePoint
