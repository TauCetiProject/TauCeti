/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Degree.SphereRotation
public import TauCeti.Geometry.Manifold.Instances.Stiefel.Rotation
import TauCeti.Analysis.Complex.Circle
import TauCeti.Geometry.Manifold.MFDeriv.IsInvertible
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace
import TauCeti.Geometry.Manifold.MFDeriv.Prod

/-!
# Regular values of the rotation family of the unit tangent bundle of a sphere

Let `E` be a real inner product space of dimension `n + 1 ≥ 2`, with unit sphere `Sⁿ`, whose unit
tangent bundle is the Stiefel manifold `TauCeti.stiefel E 2` of orthonormal pairs `(u, v)`. This
file studies the derivative and the regular values of the rotation family of the unit tangent
bundle (`TauCeti.stiefelRotationFamily`, defined in
`TauCeti.Geometry.Manifold.Instances.Stiefel.Rotation`)

`τ : T¹Sⁿ × S¹ → Sⁿ × Sⁿ`, `τ ((u, v), z) = (u, Re z • u + Im z • v)`.

Both sides have dimension `2n`. The derivative of `τ` is computed in
`TauCeti.mvfderiv_coe_stiefelRotationFamily_fst_apply` and
`TauCeti.mvfderiv_coe_stiefelRotationFamily_snd_apply`. It is injective, hence invertible, at every
point with `Im z ≠ 0` (`TauCeti.injective_mfderiv_stiefelRotationFamily`,
`TauCeti.isInvertible_mfderiv_stiefelRotationFamily`), while the points with
`Im z = 0` are sent to the diagonal and the antidiagonal of `Sⁿ × Sⁿ`. So every pair `(u, w)` with
`w ≠ ±u` is a regular value of `τ` (`TauCeti.isRegularValue_stiefelRotationFamily`), and it has
exactly two preimages, `((u, v₀), z₀)` and `((u, -v₀), conj z₀)`, which trace the great circle
through `u` and `w` in opposite directions (`TauCeti.ncard_preimage_stiefelRotationFamily`). For
any orientations of the source and target the degree of `τ` at such a value is therefore even
(`TauCeti.degreeAtRegularValue_stiefelRotationFamily_modEq`).

With `n - 1` in place of `n`, this is the map `T¹Sⁿ⁻¹ × S¹ → Sⁿ⁻¹ × Sⁿ⁻¹` through which
Barraud–Damian–Humilière–Oancea prove that the family of 2-spheres of an even-dimensional sphere
`Sⁿ` represents a nonzero class of `H_{2n-3}(Ω²Sⁿ)` (their Proposition 6.17): they show that its
degree is `±2` for even `n`, as the two preimages above contribute the same sign.

In the statements, `n = m + 1`, so that `Sⁿ` is modelled on `ℝᵐ⁺¹`, and the Stiefel manifold
carries its level-set structure, modelled on `ℝ^(2 (m + 2) - 3)`.

## Main declarations

* `TauCeti.ncard_preimage_stiefelRotationFamily`: a pair `(u, w)` with `w ≠ ±u` has exactly two
  preimages.
* `TauCeti.mvfderiv_coe_stiefelRotationFamily_fst_apply`,
  `TauCeti.mvfderiv_coe_stiefelRotationFamily_snd_apply`: the derivative, read in `E`.
* `TauCeti.injective_mfderiv_stiefelRotationFamily`,
  `TauCeti.isInvertible_mfderiv_stiefelRotationFamily`: the derivative is injective, hence
  invertible, where `Im z ≠ 0`.
* `TauCeti.isRegularValue_stiefelRotationFamily`: every pair `(u, w)` with `w ≠ ±u` is a regular
  value.
* `TauCeti.degreeAtRegularValue_stiefelRotationFamily_modEq`: the degree there is even, for any
  orientations.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §6.4 (Example 6.16 and the proof of
  Proposition 6.17).
* J. W. Milnor, *Topology from the Differentiable Viewpoint*, University Press of Virginia, 1965,
  §5 (the degree as a signed count of preimages).
-/

public section

noncomputable section

open Function Metric Module Set TauCeti.Manifold.Orientation
open scoped Manifold ContDiff RealInnerProductSpace

namespace TauCeti

attribute [local instance] finrank_real_complex_fact'

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ### Fibres -/

/-- **The regular preimages of the rotation family of the unit tangent bundle.** A pair `(u, w)` of
points of the sphere with `w ≠ ±u` has exactly two preimages, `((u, v), z)` and
`((u, -v), conj z)`. -/
theorem ncard_preimage_stiefelRotationFamily {p q : sphere (0 : E) 1} (hqp : q ≠ p)
    (hqp' : q ≠ -p) : (stiefelRotationFamily ⁻¹' {(p, q)}).ncard = 2 := by
  obtain ⟨x, hx, hxq⟩ := exists_stiefelRotationFamily_eq hqp hqp'
  obtain ⟨hu, hv, huv⟩ := mem_stiefel_two_iff.1 x.1.2
  -- The second preimage, obtained by the involution `((u, v), z) ↦ ((u, -v), conj z)`.
  let x' : stiefel E 2 × sphere (0 : ℂ) 1 :=
    (⟨![x.1.1 0, -x.1.1 1], mem_stiefel_two_iff.2 ⟨by simpa using hu, by simpa using hv,
        by simpa using huv⟩⟩,
      ⟨(starRingEnd ℂ) (x.2 : ℂ), by simp⟩)
  rw [Set.ncard_eq_two]
  refine ⟨x, x', fun h ↦ ?_, Set.ext fun y ↦ ?_⟩
  · have h' := congrArg (fun t : stiefel E 2 × sphere (0 : ℂ) 1 ↦ (t.2 : ℂ).im) h
    simp only [x', Complex.conj_im] at h'
    linarith
  · rw [mem_preimage, mem_singleton_iff, ← hxq,
      stiefelRotationFamily_eq_stiefelRotationFamily_iff hx.ne', mem_insert_iff,
      mem_singleton_iff]
    refine or_congr_right ⟨fun ⟨h₀, h₁, hz⟩ ↦ Prod.ext (Subtype.ext (funext fun i ↦ ?_))
      (Subtype.ext hz), ?_⟩
    · fin_cases i
      exacts [h₀, h₁]
    · rintro rfl
      exact ⟨rfl, rfl, rfl⟩

variable [FiniteDimensional ℝ E] {m : ℕ} [Fact (finrank ℝ E = m + 1 + 1)]

/-! ### The derivative -/

/-- The derivative of the projection of a pair `(x, z)` to the vector `x i` of the frame, read in
`E`: the `i`th component of the derivative of the inclusion of the Stiefel manifold. -/
private theorem mvfderiv_frameVector_apply (x : stiefel E 2 × sphere (0 : ℂ) 1)
    (w : TangentSpace (𝓘(ℝ, Fin (2 * finrank ℝ E - (2 + 1).choose 2) → ℝ).prod (𝓡 1)) x)
    (i : Fin 2) :
    mvfderiv (𝓘(ℝ, Fin (2 * finrank ℝ E - (2 + 1).choose 2) → ℝ).prod (𝓡 1))
        (fun y : stiefel E 2 × sphere (0 : ℂ) 1 ↦ y.1.1 i) x w =
      mvfderiv 𝓘(ℝ, Fin (2 * finrank ℝ E - (2 + 1).choose 2) → ℝ)
        ((↑) : stiefel E 2 → Fin 2 → E) x.1 (Manifold.tangentSpaceProdEquiv x w).1 i := by
  have hι := ((contMDiff_coe_stiefel E 2 (r := 1)) x.1).mdifferentiableAt one_ne_zero
  have h := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 ↦ E) i).mvfderiv_comp_apply hι
    (Manifold.tangentSpaceProdEquiv x w).1
  rw [Manifold.tangentSpaceProdEquiv_apply] at h ⊢
  -- The map is `proj i ∘ Subtype.val ∘ Prod.fst` by definition.
  exact (mvfderiv_comp_fst_apply
    (⇑(ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 ↦ E) i) ∘ Subtype.val) x w).trans h

/-- The derivative of the first component of the rotation family of the unit tangent bundle, read
in `E`: a tangent vector `(a, b)` at `((u, v), z)` is sent to the first vector `a₀` of `a`, where
`a = (a₀, a₁)` is read in `E × E` through the derivative of the inclusion. -/
theorem mvfderiv_coe_stiefelRotationFamily_fst_apply (x : stiefel E 2 × sphere (0 : ℂ) 1)
    (w : TangentSpace (𝓘(ℝ, Fin (2 * finrank ℝ E - (2 + 1).choose 2) → ℝ).prod (𝓡 1)) x) :
    mvfderiv (𝓘(ℝ, Fin (2 * finrank ℝ E - (2 + 1).choose 2) → ℝ).prod (𝓡 1))
        (fun y ↦ ((stiefelRotationFamily y).1 : E)) x w =
      mvfderiv 𝓘(ℝ, Fin (2 * finrank ℝ E - (2 + 1).choose 2) → ℝ)
        ((↑) : stiefel E 2 → Fin 2 → E) x.1 (Manifold.tangentSpaceProdEquiv x w).1 0 := by
  rw [show (fun y : stiefel E 2 × sphere (0 : ℂ) 1 ↦ ((stiefelRotationFamily y).1 : E)) =
    fun y ↦ y.1.1 0 from funext fun y ↦ by simp, mvfderiv_frameVector_apply]

/-- **The derivative of the rotation family of the unit tangent bundle**, second component, read
in `E`. A tangent vector `(a, b)` at `((u, v), z)` is sent to
`Re b • u + Im b • v + Re z • a₀ + Im z • a₁`, where `a = (a₀, a₁)` and `b` are read in `E × E` and
in `ℂ` through the derivatives of the inclusions. -/
theorem mvfderiv_coe_stiefelRotationFamily_snd_apply (x : stiefel E 2 × sphere (0 : ℂ) 1)
    (w : TangentSpace (𝓘(ℝ, Fin (2 * finrank ℝ E - (2 + 1).choose 2) → ℝ).prod (𝓡 1)) x) :
    mvfderiv (𝓘(ℝ, Fin (2 * finrank ℝ E - (2 + 1).choose 2) → ℝ).prod (𝓡 1))
        (fun y ↦ ((stiefelRotationFamily y).2 : E)) x w =
      (mvfderiv (𝓡 1) ((↑) : sphere (0 : ℂ) 1 → ℂ) x.2
          (Manifold.tangentSpaceProdEquiv x w).2).re • x.1.1 0 +
        (mvfderiv (𝓡 1) ((↑) : sphere (0 : ℂ) 1 → ℂ) x.2
          (Manifold.tangentSpaceProdEquiv x w).2).im • x.1.1 1 +
        (x.2 : ℂ).re • mvfderiv 𝓘(ℝ, Fin (2 * finrank ℝ E - (2 + 1).choose 2) → ℝ)
          ((↑) : stiefel E 2 → Fin 2 → E) x.1 (Manifold.tangentSpaceProdEquiv x w).1 0 +
        (x.2 : ℂ).im • mvfderiv 𝓘(ℝ, Fin (2 * finrank ℝ E - (2 + 1).choose 2) → ℝ)
          ((↑) : stiefel E 2 → Fin 2 → E) x.1 (Manifold.tangentSpaceProdEquiv x w).1 1 := by
  have hκ := (contMDiff_coe_sphere (E := ℂ) (n := 1) (m := 1) x.2).mdifferentiableAt one_ne_zero
  have hv (i : Fin 2) : MDifferentiableAt
      (𝓘(ℝ, Fin (2 * finrank ℝ E - (2 + 1).choose 2) → ℝ).prod (𝓡 1)) 𝓘(ℝ, E)
      (fun y : stiefel E 2 × sphere (0 : ℂ) 1 ↦ y.1.1 i) x :=
    (((ContinuousLinearMap.proj i).contDiff.contMDiff.comp
      (contMDiff_coe_stiefel E 2 (r := 1))).comp contMDiff_fst x).mdifferentiableAt one_ne_zero
  have hL (L : ℂ →L[ℝ] ℝ) : MDifferentiableAt
      (𝓘(ℝ, Fin (2 * finrank ℝ E - (2 + 1).choose 2) → ℝ).prod (𝓡 1)) 𝓘(ℝ)
      (fun y : stiefel E 2 × sphere (0 : ℂ) 1 ↦ L (y.2 : ℂ)) x :=
    (L.mdifferentiableAt.comp x.2 hκ).comp x mdifferentiableAt_snd
  have hL' (L : ℂ →L[ℝ] ℝ) : mvfderiv
      (𝓘(ℝ, Fin (2 * finrank ℝ E - (2 + 1).choose 2) → ℝ).prod (𝓡 1))
      (fun y : stiefel E 2 × sphere (0 : ℂ) 1 ↦ L (y.2 : ℂ)) x w =
      L (mvfderiv (𝓡 1) ((↑) : sphere (0 : ℂ) 1 → ℂ) x.2
        (Manifold.tangentSpaceProdEquiv x w).2) := by
    -- `mvfderiv_comp_snd_apply` rewrites the derivative of a composition `g ∘ Prod.snd`, so the
    -- map, a lambda, is first written definitionally in that form.
    rw [show (fun y : stiefel E 2 × sphere (0 : ℂ) 1 ↦ L (y.2 : ℂ)) =
      (L ∘ ((↑) : sphere (0 : ℂ) 1 → ℂ)) ∘ Prod.snd from rfl, mvfderiv_comp_snd_apply,
      Manifold.tangentSpaceProdEquiv_apply]
    exact L.mvfderiv_comp_apply hκ _
  -- Write the map as a sum of products of scalar and vector-valued functions.
  rw [show (fun y : stiefel E 2 × sphere (0 : ℂ) 1 ↦ ((stiefelRotationFamily y).2 : E)) =
    ((fun y : stiefel E 2 × sphere (0 : ℂ) 1 ↦ Complex.reCLM (y.2 : ℂ)) •
        fun y : stiefel E 2 × sphere (0 : ℂ) 1 ↦ y.1.1 0) +
      (fun y : stiefel E 2 × sphere (0 : ℂ) 1 ↦ Complex.imCLM (y.2 : ℂ)) •
        fun y : stiefel E 2 × sphere (0 : ℂ) 1 ↦ y.1.1 1 from funext fun y ↦ by simp,
    mvfderiv_add ((hL _).smul (hv 0)) ((hL _).smul (hv 1)),
    mvfderiv_smul (hL _) (hv 0), mvfderiv_smul (hL _) (hv 1)]
  simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply]
  rw [hL' Complex.reCLM, hL' Complex.imCLM, mvfderiv_frameVector_apply,
    mvfderiv_frameVector_apply]
  simp only [Complex.reCLM_apply, Complex.imCLM_apply]
  abel

/-! ### Regular values -/

/-- At a point `((u, v), z)` with `Im z ≠ 0`, the derivative of the rotation family of the unit
tangent bundle is injective. -/
theorem injective_mfderiv_stiefelRotationFamily {x : stiefel E 2 × sphere (0 : ℂ) 1}
    (hx : (x.2 : ℂ).im ≠ 0) :
    Injective (mfderiv (𝓘(ℝ, Fin (2 * finrank ℝ E - (2 + 1).choose 2) → ℝ).prod (𝓡 1))
      ((𝓡 (m + 1)).prod (𝓡 (m + 1))) stiefelRotationFamily x) := by
  have hτ := (contMDiff_stiefelRotationFamily (E := E) (n := m) x).mdifferentiableAt
    (by simp : (∞ : ℕ∞ω) ≠ 0)
  have hd (g : sphere (0 : E) 1 × sphere (0 : E) 1 → sphere (0 : E) 1)
      (hg : ContMDiff ((𝓡 (m + 1)).prod (𝓡 (m + 1))) (𝓡 (m + 1)) 1 g) :
      MDifferentiableAt ((𝓡 (m + 1)).prod (𝓡 (m + 1))) 𝓘(ℝ, E) (Subtype.val ∘ g)
        (stiefelRotationFamily x) :=
    ((contMDiff_coe_sphere.comp hg) _).mdifferentiableAt one_ne_zero
  -- A tangent vector `(a, b)` in the kernel has `a₀ = 0`; as `a` is tangent to the Stiefel
  -- manifold, `a₁` is then orthogonal to `u` and `v`, and the second component
  -- `Re b • u + Im b • v + Im z • a₁ = 0` forces `b = 0` and `a₁ = 0`.
  rw [injective_iff_map_eq_zero]
  intro w hw
  -- Both components of the derivative, read in `E`, vanish on `w`.
  have h₁ := mvfderiv_comp_apply x (hd Prod.fst contMDiff_fst) hτ w
  have h₂ := mvfderiv_comp_apply x (hd Prod.snd contMDiff_snd) hτ w
  rw [hw, map_zero] at h₁ h₂
  have h₁' := (mvfderiv_coe_stiefelRotationFamily_fst_apply x w).symm.trans h₁
  have h₂' := (mvfderiv_coe_stiefelRotationFamily_snd_apply x w).symm.trans h₂
  set a := mvfderiv 𝓘(ℝ, Fin (2 * finrank ℝ E - (2 + 1).choose 2) → ℝ)
    ((↑) : stiefel E 2 → Fin 2 → E) x.1 (Manifold.tangentSpaceProdEquiv x w).1 with ha
  set b := mvfderiv (𝓡 1) ((↑) : sphere (0 : ℂ) 1 → ℂ) x.2
    (Manifold.tangentSpaceProdEquiv x w).2 with hb
  rw [h₁', smul_zero, add_zero] at h₂'
  -- `a` is tangent to the Stiefel manifold, so `a₁` is orthogonal to `u` and to `v`.
  have hker :=
    gramSym2Deriv_mvfderiv_coe_stiefel_eq_zero x.1 (Manifold.tangentSpaceProdEquiv x w).1
  rw [← ha] at hker
  have h01 := congrFun hker s(0, 1)
  have h11 := congrFun hker s(1, 1)
  simp only [gramSym2Deriv_apply_mk, h₁', inner_zero_left, add_zero, Pi.zero_apply] at h01 h11
  have h11' : ⟪x.1.1 1, a 1⟫ = 0 := by
    rw [real_inner_comm (x.1.1 1) (a 1)] at h11
    linarith
  obtain ⟨hu, hv, huv⟩ := mem_stiefel_two_iff.1 x.1.2
  have hu' : ⟪x.1.1 0, x.1.1 0⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hu, one_pow]
  have hv' : ⟪x.1.1 1, x.1.1 1⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hv, one_pow]
  have hre : b.re = 0 := by
    have := congrArg (fun e ↦ ⟪x.1.1 0, e⟫) h₂'
    simp only [inner_add_right, real_inner_smul_right, hu', huv, h01, inner_zero_right] at this
    linarith
  have him : b.im = 0 := by
    have := congrArg (fun e ↦ ⟪x.1.1 1, e⟫) h₂'
    simp only [inner_add_right, real_inner_smul_right, hv', real_inner_comm (x.1.1 0), huv,
      h11', inner_zero_right] at this
    linarith
  rw [hre, him, zero_smul, zero_smul, zero_add, zero_add] at h₂'
  have ha1 : a 1 = 0 := (smul_eq_zero.1 h₂').resolve_left hx
  have hw₁ : (Manifold.tangentSpaceProdEquiv x w).1 = 0 :=
    (injective_iff_map_eq_zero _).1 (injective_mvfderiv_iff.2 (injective_mfderiv_coe_stiefel x.1))
      _ (funext fun i ↦ by
        fin_cases i
        exacts [h₁', ha1])
  have hw₂ : (Manifold.tangentSpaceProdEquiv x w).2 = 0 :=
    (injective_iff_map_eq_zero _).1 (injective_mvfderiv_subtypeVal_sphere x.2) _
      (Complex.ext hre him)
  exact (injective_iff_map_eq_zero _).1 (Manifold.tangentSpaceProdEquiv x).injective _
    (Prod.ext hw₁ hw₂)

/-- At a point `((u, v), z)` with `Im z ≠ 0`, the derivative of the rotation family of the unit
tangent bundle is invertible. The source and target both have dimension `2 (m + 1)`. -/
theorem isInvertible_mfderiv_stiefelRotationFamily {x : stiefel E 2 × sphere (0 : ℂ) 1}
    (hx : (x.2 : ℂ).im ≠ 0) :
    (mfderiv (𝓘(ℝ, Fin (2 * finrank ℝ E - (2 + 1).choose 2) → ℝ).prod (𝓡 1))
      ((𝓡 (m + 1)).prod (𝓡 (m + 1))) stiefelRotationFamily x).IsInvertible := by
  -- The source and the target are modelled on spaces of dimension `2 (m + 1)`.
  refine isInvertible_mfderiv_of_injective ?_ (injective_mfderiv_stiefelRotationFamily hx)
  have hE : finrank ℝ E = m + 1 + 1 := Fact.out
  rw [Module.finrank_prod, Module.finrank_prod, Module.finrank_fin_fun,
    finrank_euclideanSpace_fin, finrank_euclideanSpace_fin, hE]
  simp only [Nat.choose]
  omega

/-- Every pair `(u, w)` of points of the sphere with `w ≠ ±u` is a regular value of the rotation
family of the unit tangent bundle. -/
theorem isRegularValue_stiefelRotationFamily {p q : sphere (0 : E) 1} (hqp : q ≠ p)
    (hqp' : q ≠ -p) :
    IsRegularValue (𝓘(ℝ, Fin (2 * finrank ℝ E - (2 + 1).choose 2) → ℝ).prod (𝓡 1))
      ((𝓡 (m + 1)).prod (𝓡 (m + 1))) stiefelRotationFamily (p, q) := by
  rw [isRegularValue_iff]
  intro x hx
  have him : (x.2 : ℂ).im ≠ 0 := fun h0 ↦ by
    rcases stiefelRotationFamily_snd_eq_or_eq_neg_of_im_eq_zero h0 with h | h <;>
      · rw [hx] at h
        contradiction
  rw [isRegularPoint_iff]
  exact (isInvertible_mfderiv_stiefelRotationFamily him).surjective

/-- For any orientations of the source and target, the degree of the rotation family of the unit
tangent bundle at a pair `(u, w)` with `w ≠ ±u` is even: it is a sum of two signs. -/
theorem degreeAtRegularValue_stiefelRotationFamily_modEq {ι : Type*} [Fintype ι]
    (o : Manifold.Orientation (𝓘(ℝ, Fin (2 * finrank ℝ E - (2 + 1).choose 2) → ℝ).prod (𝓡 1))
      (stiefel E 2 × sphere (0 : ℂ) 1) ι)
    (o' : Manifold.Orientation ((𝓡 (m + 1)).prod (𝓡 (m + 1)))
      (sphere (0 : E) 1 × sphere (0 : E) 1) ι)
    {p q : sphere (0 : E) 1} (hqp : q ≠ p) (hqp' : q ≠ -p) :
    degreeAtRegularValue o o' stiefelRotationFamily (p, q) ≡ 0 [ZMOD 2] := by
  have hcard := ncard_preimage_stiefelRotationFamily hqp hqp'
  have h := degreeAtRegularValue_modEq_ncard (o := o) (o' := o')
    (isRegularValue_stiefelRotationFamily hqp hqp')
    (Set.finite_of_ncard_ne_zero (by rw [hcard]; norm_num))
  rw [hcard] at h
  exact h.trans (by decide)

end TauCeti
