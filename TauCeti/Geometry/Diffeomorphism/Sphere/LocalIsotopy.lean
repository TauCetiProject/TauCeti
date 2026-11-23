/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Instances.Sphere
public import TauCeti.Analysis.Normed.Module.Ball.Radial.Cone
public import TauCeti.Geometry.Diffeomorphism.Diffeotopy.Basic
public import TauCeti.Geometry.Diffeomorphism.Group
public import TauCeti.Geometry.Diffeomorphism.Topology
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import TauCeti.Analysis.InnerProductSpace.Normalize
import TauCeti.Geometry.Diffeomorphism.Composition
import TauCeti.Geometry.Diffeomorphism.Diffeotopy.Path
import TauCeti.Geometry.Manifold.ContMDiffMap.Chart.Comp
import TauCeti.Geometry.Manifold.ContMDiffMap.WeakWhitney.Open
import TauCeti.Geometry.Manifold.Diffeomorph.Perturbation
import TauCeti.Geometry.Manifold.Instances.Sphere

/-!
# Diffeomorphisms of a sphere near the identity are diffeotopic to it

Let `Sⁿ` be the unit sphere of a real inner product space `E` of dimension `n + 1`, and let `f` be
a `C^k` diffeomorphism of `Sⁿ`, `1 ≤ k`. Its displacement `x ↦ f x - x` extends to `E` as the cone
`u = TauCeti.sphereCone (fun x ↦ f x - x)`, positively homogeneous of degree one. When `u` is
`L`-Lipschitz with `L < 1`, every map `y ↦ y + c • u y`, `0 ≤ c ≤ 1`, is a homeomorphism of `E`
(`LipschitzWith.idAddHomeomorph`) commuting with positive dilations, so

`x ↦ (x + c • (f x - x)) / ‖x + c • (f x - x)‖`

is a bijection of `Sⁿ`, with inverse the normalized inverse of `y ↦ y + c • u y`. Running `c` from
`0` to `1` along the analytic weight `sin (π t / 2) ^ 2` gives a diffeotopy from the identity to
`f` (`TauCeti.sphereInterpolationDiffeotopy`): the inverses depend smoothly on `(t, y)` by the
inverse function theorem applied to `(s, y) ↦ (s, y + c(s) • u y)` away from the origin.

The weak Whitney topology controls the first derivatives of `f` on the sphere, read in `E` through
the radial projection of the punctured space, so for `f` near the identity the displacement is
small and `1 / 4`-Lipschitz, and its cone is `5 / 8`-Lipschitz (`TauCeti.lipschitzWith_sphereCone`).
This is the **local isotopy lemma** for spheres: every diffeomorphism in a neighbourhood of the
identity of `Diff(Sⁿ)` is the final diffeomorphism of a diffeotopy
(`TauCeti.eventually_exists_diffeotopy_final_eq`). Translating it by the group structure, the
classes of diffeomorphisms related by diffeotopies are open, hence closed, in `Diff(Sⁿ)`: two
diffeomorphisms of `Sⁿ` are joined by a path in the weak Whitney topology exactly when they differ
by the final diffeomorphism of a diffeotopy (`TauCeti.joined_iff_exists_diffeotopy_mul_final_eq`).
So `π₀ Diff(Sⁿ)` is the set of smooth isotopy classes.

## Main definitions

* `TauCeti.sphereInterpolationDiffeotopy`: the diffeotopy
  `(t, x) ↦ normalize (x + sin (π t / 2) ^ 2 • (f x - x))` from the identity to a diffeomorphism
  `f` of the sphere whose displacement has a cone of Lipschitz constant less than one.

## Main results

* `TauCeti.coe_sphereInterpolationDiffeotopy_apply`, `TauCeti.sphereInterpolationDiffeotopy_final`:
  the formula of the diffeotopy, and that it ends at `f`.
* `TauCeti.eventually_exists_diffeotopy_final_eq`: the local isotopy lemma.
* `TauCeti.joined_iff_exists_diffeotopy_mul_final_eq`: the path components of `Diff(Sⁿ)` are the
  diffeotopy classes.

## References

* M. Hirsch, *Differential Topology*, Springer GTM 33 (1976), Chapter 2, §1, for the weak `C^k`
  topology, and Chapter 8, §8.1, for isotopies.
-/

public section

noncomputable section

open Metric Module Set Filter Topology TopologicalSpace NormedSpace
open scoped Manifold ContDiff NNReal unitInterval TauCeti.ManifoldWeakWhitney
  TauCeti.DiffeomorphWeakWhitney

namespace TauCeti

variable {k : ℕ∞ω}

/-! ### The interpolating homeomorphisms of a Banach space -/

section Interpolation

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The weight `sin (π s / 2) ^ 2`: analytic, with values in `[0, 1]`, vanishing at `0` and equal
to `1` at `1`. -/
private def weight (s : ℝ) : ℝ := Real.sin (Real.pi * s / 2) ^ 2

private theorem weight_def (s : ℝ) : weight s = Real.sin (Real.pi * s / 2) ^ 2 :=
  (rfl)

private theorem weight_zero : weight 0 = 0 := by simp [weight]

private theorem weight_one : weight 1 = 1 := by simp [weight]

private theorem norm_weight_le_one (s : ℝ) : ‖weight s‖ ≤ 1 := by
  unfold weight
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  exact Real.sin_sq_le_one _

private theorem contDiff_weight : ContDiff ℝ k weight :=
  (Real.contDiff_sin.comp ((contDiff_const.mul contDiff_id).div_const 2)).pow 2

variable {u : V → V} {L : ℝ≥0}

/-- Scaling a perturbation by the weight keeps its Lipschitz constant. -/
private theorem lipschitzWith_weight_smul (hu : LipschitzWith L u) (s : ℝ) :
    LipschitzWith L fun y ↦ weight s • u y := by
  have h : ‖weight s‖₊ ≤ 1 := by exact_mod_cast norm_weight_le_one s
  exact ((lipschitzWith_smul (weight s)).comp hu).weaken
    (mul_le_of_le_one_left zero_le h)

variable [CompleteSpace V]

/-- The homeomorphism `y ↦ y + weight s • u y` of `E`. -/
private def slice (hu : LipschitzWith L u) (hL : L < 1) (s : ℝ) : V ≃ₜ V :=
  (lipschitzWith_weight_smul hu s).idAddHomeomorph ℝ hL

private theorem slice_apply (hu : LipschitzWith L u) (hL : L < 1) (s : ℝ) (y : V) :
    slice hu hL s y = y + weight s • u y := by
  simp only [slice, LipschitzWith.coe_idAddHomeomorph]

/-- The inverses of the slices depend continuously on the parameter and the point: by the
antilipschitz bound, `‖slice s⁻¹ y - a₀‖ ≤ (1 - L)⁻¹ ‖y - slice s a₀‖`. -/
private theorem continuous_slice_symm (hu : LipschitzWith L u) (hL : L < 1) :
    Continuous fun p : ℝ × V ↦ (slice hu hL p.1).symm p.2 := by
  refine continuous_iff_continuousAt.2 fun p₀ ↦ ?_
  set a₀ := (slice hu hL p₀.1).symm p₀.2
  have hle (p : ℝ × V) : ‖(slice hu hL p.1).symm p.2 - a₀‖ ≤
      ((1 - L)⁻¹ : ℝ≥0) * ‖p.2 - (a₀ + weight p.1 • u a₀)‖ := by
    have h := ((lipschitzWith_weight_smul hu p.1).antilipschitzWith_id_add hL).le_mul_dist
      ((slice hu hL p.1).symm p.2) a₀
    rwa [dist_eq_norm, dist_eq_norm, ← slice_apply hu hL, Homeomorph.apply_symm_apply] at h
  have hc : Continuous fun p : ℝ × V ↦ p.2 - (a₀ + weight p.1 • u a₀) :=
    continuous_snd.sub (continuous_const.add
      (((contDiff_weight (k := 0)).continuous.comp continuous_fst).smul continuous_const))
  have h0 : p₀.2 - (a₀ + weight p₀.1 • u a₀) = 0 := by
    rw [← slice_apply hu hL, Homeomorph.apply_symm_apply, sub_self]
  refine tendsto_iff_norm_sub_tendsto_zero.2 (squeeze_zero (fun _ ↦ norm_nonneg _) hle ?_)
  simpa using ((hc.tendsto p₀).mono_right (congrArg 𝓝 h0).le).norm.const_mul
    (((1 - L)⁻¹ : ℝ≥0) : ℝ)

/-- The level-preserving homeomorphism `(s, y) ↦ (s, y + weight s • u y)` of `ℝ × E`. -/
private def total (hu : LipschitzWith L u) (hL : L < 1) : (ℝ × V) ≃ₜ (ℝ × V) where
  toFun p := (p.1, p.2 + weight p.1 • u p.2)
  invFun p := (p.1, (slice hu hL p.1).symm p.2)
  left_inv p := by simp [← slice_apply hu hL]
  right_inv p := by simp [← slice_apply hu hL]
  continuous_toFun := continuous_fst.prodMk (continuous_snd.add
    (((contDiff_weight (k := 0)).continuous.comp continuous_fst).smul
      (hu.continuous.comp continuous_snd)))
  continuous_invFun := continuous_fst.prodMk (continuous_slice_symm hu hL)

/-- At a point where `u` is differentiable, the derivative of `total` is the block triangular
equivalence `(ds, dy) ↦ (ds, dy + weight s • Du dy + weight' s ds • u a)`. -/
private theorem exists_hasFDerivAt_total (hu : LipschitzWith L u) (hL : L < 1) {s : ℝ} {a : V}
    (ha : DifferentiableAt ℝ u a) :
    ∃ T : (ℝ × V) ≃L[ℝ] (ℝ × V), HasFDerivAt (total hu hL) (T : (ℝ × V) →L[ℝ] (ℝ × V)) (s, a) := by
  have hw : HasFDerivAt weight (fderiv ℝ weight s) s :=
    ((contDiff_weight (k := 1)).differentiable one_ne_zero s).hasFDerivAt
  have hlip := lipschitzWith_weight_smul hu s
  refine ⟨(ContinuousLinearEquiv.refl ℝ ℝ).skewProd (hlip.idAddFDerivEquiv ℝ hL a)
    ((fderiv ℝ weight s).smulRight (u a)), ?_⟩
  have hfst : HasFDerivAt (Prod.fst : ℝ × V → ℝ) (ContinuousLinearMap.fst ℝ ℝ V) (s, a) :=
    hasFDerivAt_fst
  have hsnd : HasFDerivAt (Prod.snd : ℝ × V → V) (ContinuousLinearMap.snd ℝ ℝ V) (s, a) :=
    hasFDerivAt_snd
  have hD := hfst.prodMk (hsnd.add ((hw.comp (s, a) hfst).smul (ha.hasFDerivAt.comp (s, a) hsnd)))
  refine hD.congr_fderiv (ContinuousLinearMap.ext fun q ↦ Prod.ext rfl ?_)
  simp [fderiv_fun_const_smul ha, add_assoc]

/-- The inverses of the slices are `C^k` in the parameter and the point away from the origin, by
the inverse function theorem for `total`. -/
private theorem contDiffAt_slice_symm (hu : LipschitzWith L u) (hL : L < 1) (hk : 1 ≤ k)
    (hd : ∀ y ≠ 0, ContDiffAt ℝ k u y) (h0 : u 0 = 0) {p : ℝ × V} (hp : p.2 ≠ 0) :
    ContDiffAt ℝ k (fun p : ℝ × V ↦ (slice hu hL p.1).symm p.2) p := by
  set a := (slice hu hL p.1).symm p.2
  have ha : a ≠ 0 := by
    rintro h
    apply hp
    have hpa : p.2 = slice hu hL p.1 a := ((slice hu hL p.1).apply_symm_apply p.2).symm
    rw [hpa, h, slice_apply, h0, smul_zero, add_zero]
  have hc : ContDiffAt ℝ k (total hu hL) (p.1, a) :=
    contDiffAt_fst.prodMk (contDiffAt_snd.add
      ((contDiff_weight.contDiffAt.comp _ contDiffAt_fst).smul
        ((hd a ha).comp (p.1, a) (contDiffAt_snd (p := (p.1, a))))))
  obtain ⟨T, hT⟩ := exists_hasFDerivAt_total hu hL (s := p.1)
    ((hd a ha).differentiableAt (zero_lt_one.trans_le hk).ne')
  have h := (total hu hL).toOpenPartialHomeomorph.contDiffAt_symm (mem_univ p) hT hc
  exact contDiffAt_snd.comp p h

/-- A slice fixes the origin when `u` does. -/
private theorem slice_ne_zero (hu : LipschitzWith L u) (hL : L < 1) (h0 : u 0 = 0) (s : ℝ)
    {y : V} (hy : y ≠ 0) : slice hu hL s y ≠ 0 := fun h ↦
  hy ((slice hu hL s).injective (h.trans (by rw [slice_apply, h0, smul_zero, add_zero])))

private theorem slice_symm_ne_zero (hu : LipschitzWith L u) (hL : L < 1) (h0 : u 0 = 0) (s : ℝ)
    {y : V} (hy : y ≠ 0) : (slice hu hL s).symm y ≠ 0 := fun h ↦
  hy (by rw [← (slice hu hL s).apply_symm_apply y, h, slice_apply, h0, smul_zero, add_zero])

/-- A slice commutes with dilations by nonnegative scalars when `u` does. -/
private theorem slice_smul (hu : LipschitzWith L u) (hL : L < 1)
    (hh : ∀ c : ℝ, 0 ≤ c → ∀ y, u (c • y) = c • u y) (s : ℝ) {c : ℝ} (hc : 0 ≤ c) (y : V) :
    slice hu hL s (c • y) = c • slice hu hL s y := by
  rw [slice_apply, slice_apply, hh c hc, smul_add, smul_comm]

private theorem slice_symm_smul (hu : LipschitzWith L u) (hL : L < 1)
    (hh : ∀ c : ℝ, 0 ≤ c → ∀ y, u (c • y) = c • u y) (s : ℝ) {c : ℝ} (hc : 0 ≤ c) (y : V) :
    (slice hu hL s).symm (c • y) = c • (slice hu hL s).symm y := by
  rw [Homeomorph.symm_apply_eq, slice_smul hu hL hh s hc, Homeomorph.apply_symm_apply]

omit [CompleteSpace V] in
/-- A map commuting with nonnegative dilations commutes with `normalize` up to normalization. -/
private theorem normalize_apply_normalize {g : V → V}
    (hg : ∀ c : ℝ, 0 ≤ c → ∀ y, g (c • y) = c • g y) (z : V) :
    normalize (g (normalize z)) = normalize (g z) := by
  rcases eq_or_ne z 0 with rfl | hz
  · simp
  calc normalize (g (normalize z)) = normalize (g (‖z‖⁻¹ • z)) := (rfl)
    _ = normalize (g z) := by
      rw [hg _ (inv_nonneg.2 (norm_nonneg z)),
        normalize_smul_of_pos (inv_pos.2 (norm_pos_iff.2 hz))]

end Interpolation

/-! ### The interpolation diffeotopy of the sphere -/

section Sphere

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
  [Fact (finrank ℝ E = n + 1)]

/-- The cone over the displacement `x ↦ f x - x` of a `C^k` self-map of the sphere is `C^k` away
from the origin. -/
private theorem contDiffAt_sphereCone_sub {f : sphere (0 : E) 1 → sphere (0 : E) 1}
    (hf : ContMDiff (𝓡 n) (𝓡 n) k f) {y : E} (hy : y ≠ 0) :
    ContDiffAt ℝ k (sphereCone fun x ↦ (f x : E) - x) y := by
  have hg : ContMDiff (𝓡 n) 𝓘(ℝ, E) k fun x : sphere (0 : E) 1 ↦ (f x : E) - x :=
    (contMDiff_coe_sphere.comp hf).sub contMDiff_coe_sphere
  exact ((contDiffAt_norm ℝ hy).smul (contDiffAt_sphereExtend hy (hg _))).congr_of_eventuallyEq
    (.of_forall fun z ↦ sphereCone_eq_norm_smul_sphereExtend _ z)

/-- The pair `(s, x) ↦ (s, x)` of a parameter and a point of the sphere, read in `ℝ × E`. -/
private theorem contMDiff_prodMk_coe_sphere :
    ContMDiff (𝓘(ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ × E) k fun p : ℝ × sphere (0 : E) 1 ↦ (p.1, (p.2 : E)) :=
  contMDiff_fst.prodMk_space (contMDiff_coe_sphere.comp contMDiff_snd)

/-- A finite-dimensional sphere lives in a complete space. -/
private theorem completeSpace_of_fact (n : ℕ) [Fact (finrank ℝ E = n + 1)] : CompleteSpace E :=
  haveI := FiniteDimensional.of_fact_finrank_eq_succ (K := ℝ) (V := E) n
  FiniteDimensional.completeSpace ℝ E

/-- A `C^k` family indexed by `ℝ`, restricted to the times in `[0, 1]`. -/
private theorem contMDiff_comp_coe_Icc {g : ℝ × sphere (0 : E) 1 → sphere (0 : E) 1}
    (hg : ContMDiff (𝓘(ℝ).prod (𝓡 n)) (𝓡 n) k g) :
    ContMDiff ((𝓡∂ 1).prod (𝓡 n)) (𝓡 n) k fun p : I × sphere (0 : E) 1 ↦ g ((p.1 : ℝ), p.2) :=
  hg.comp ((contMDiff_subtypeVal_Icc.comp contMDiff_fst).prodMk contMDiff_snd)

variable [CompleteSpace E] {f : sphere (0 : E) 1 → sphere (0 : E) 1} {L : ℝ≥0}

/-- The slice at `s` of the interpolation, read on the sphere:
`x ↦ normalize (x + weight s • (f x - x))`. -/
private def sphereSlice (hu : LipschitzWith L (sphereCone fun x ↦ (f x : E) - x)) (hL : L < 1)
    (s : ℝ) (x : sphere (0 : E) 1) : sphere (0 : E) 1 :=
  ⟨normalize (slice hu hL s x), mem_sphere_zero_iff_norm.2 (norm_normalize
    (slice_ne_zero hu hL (sphereCone_zero _) s (ne_zero_of_mem_unit_sphere x)))⟩

/-- The inverse of `sphereSlice`: the normalized inverse of the slice of `E`. -/
private def sphereSliceSymm (hu : LipschitzWith L (sphereCone fun x ↦ (f x : E) - x))
    (hL : L < 1) (s : ℝ) (y : sphere (0 : E) 1) : sphere (0 : E) 1 :=
  ⟨normalize ((slice hu hL s).symm y), mem_sphere_zero_iff_norm.2 (norm_normalize
    (slice_symm_ne_zero hu hL (sphereCone_zero _) s (ne_zero_of_mem_unit_sphere y)))⟩

private theorem sphereSliceSymm_sphereSlice
    (hu : LipschitzWith L (sphereCone fun x ↦ (f x : E) - x)) (hL : L < 1) (s : ℝ)
    (x : sphere (0 : E) 1) : sphereSliceSymm hu hL s (sphereSlice hu hL s x) = x := by
  refine Subtype.ext ?_
  change normalize ((slice hu hL s).symm (normalize (slice hu hL s x))) = x
  rw [normalize_apply_normalize fun c hc z ↦
      slice_symm_smul hu hL (fun c hc y ↦ sphereCone_smul hc y) s hc z,
    Homeomorph.symm_apply_apply, normalize_eq_self_of_norm_eq_one (norm_eq_of_mem_sphere x)]

private theorem sphereSlice_sphereSliceSymm
    (hu : LipschitzWith L (sphereCone fun x ↦ (f x : E) - x)) (hL : L < 1) (s : ℝ)
    (y : sphere (0 : E) 1) : sphereSlice hu hL s (sphereSliceSymm hu hL s y) = y := by
  refine Subtype.ext ?_
  change normalize (slice hu hL s (normalize ((slice hu hL s).symm y))) = y
  rw [normalize_apply_normalize fun c hc z ↦
      slice_smul hu hL (fun c hc y ↦ sphereCone_smul hc y) s hc z,
    Homeomorph.apply_symm_apply, normalize_eq_self_of_norm_eq_one (norm_eq_of_mem_sphere y)]

private theorem sphereSlice_zero (hu : LipschitzWith L (sphereCone fun x ↦ (f x : E) - x))
    (hL : L < 1) (x : sphere (0 : E) 1) : sphereSlice hu hL 0 x = x := by
  refine Subtype.ext ?_
  change normalize (slice hu hL 0 x) = x
  rw [slice_apply, weight_zero, zero_smul, add_zero,
    normalize_eq_self_of_norm_eq_one (norm_eq_of_mem_sphere x)]

private theorem contMDiff_sphereSlice (hf : ContMDiff (𝓡 n) (𝓡 n) k f)
    (hu : LipschitzWith L (sphereCone fun x ↦ (f x : E) - x)) (hL : L < 1) :
    ContMDiff (𝓘(ℝ).prod (𝓡 n)) (𝓡 n) k fun p : ℝ × sphere (0 : E) 1 ↦
      sphereSlice hu hL p.1 p.2 := by
  refine ContMDiff.codRestrict_sphere (f := fun p : ℝ × sphere (0 : E) 1 ↦
    normalize (slice hu hL p.1 p.2)) (fun p ↦ ?_) _
  have hne : (p.2 : E) + weight p.1 • sphereCone (fun x ↦ (f x : E) - x) p.2 ≠ 0 := by
    rw [← slice_apply hu hL]
    exact slice_ne_zero hu hL (sphereCone_zero _) p.1 (ne_zero_of_mem_unit_sphere p.2)
  have hF : ContDiffAt ℝ k (fun q : ℝ × E ↦ normalize (slice hu hL q.1 q.2)) (p.1, (p.2 : E)) := by
    refine ((contDiffAt_normalize hne).comp (p.1, (p.2 : E)) (contDiffAt_snd.add
      ((contDiff_weight.contDiffAt.comp _ contDiffAt_fst).smul
        ((contDiffAt_sphereCone_sub hf (ne_zero_of_mem_unit_sphere p.2)).comp (p.1, (p.2 : E))
          (contDiffAt_snd (p := (p.1, (p.2 : E)))))))).congr_of_eventuallyEq
      (.of_forall fun q ↦ ?_)
    dsimp only [Function.comp_apply]
    rw [slice_apply]
    rfl
  exact hF.contMDiffAt.comp p (contMDiff_prodMk_coe_sphere (n := n) p)

private theorem contMDiff_sphereSliceSymm (hk : 1 ≤ k) (hf : ContMDiff (𝓡 n) (𝓡 n) k f)
    (hu : LipschitzWith L (sphereCone fun x ↦ (f x : E) - x)) (hL : L < 1) :
    ContMDiff (𝓘(ℝ).prod (𝓡 n)) (𝓡 n) k fun p : ℝ × sphere (0 : E) 1 ↦
      sphereSliceSymm hu hL p.1 p.2 := by
  refine ContMDiff.codRestrict_sphere (f := fun p : ℝ × sphere (0 : E) 1 ↦
    normalize ((slice hu hL p.1).symm p.2)) (fun p ↦ ?_) _
  have hne := slice_symm_ne_zero hu hL (sphereCone_zero _) p.1 (ne_zero_of_mem_unit_sphere p.2)
  have h₁ : ContDiffAt ℝ k (fun q : ℝ × E ↦ (slice hu hL q.1).symm q.2) (p.1, (p.2 : E)) :=
    contDiffAt_slice_symm hu hL hk (fun _ hy ↦ contDiffAt_sphereCone_sub hf hy)
      (sphereCone_zero _) (ne_zero_of_mem_unit_sphere p.2)
  have hF : ContDiffAt ℝ k (NormedSpace.normalize ∘ fun q : ℝ × E ↦ (slice hu hL q.1).symm q.2)
      (p.1, (p.2 : E)) :=
    (contDiffAt_normalize hne).comp (p.1, (p.2 : E)) h₁
  exact hF.contMDiffAt.comp p (contMDiff_prodMk_coe_sphere (n := n) p)

variable (f : Diff (𝓡 n) (sphere (0 : E) 1) k) {L : ℝ≥0} (hL : L < 1)
  (hlip : LipschitzWith L (sphereCone fun x ↦ (f x : E) - x)) (hk : 1 ≤ k)

omit [CompleteSpace E] in
/-- **Interpolation from the identity to a diffeomorphism of the sphere.** Let `f` be a `C^k`
diffeomorphism of the unit sphere, `1 ≤ k`, whose displacement `x ↦ f x - x` has an `L`-Lipschitz
cone `TauCeti.sphereCone`, `L < 1`. Then `(t, x) ↦ normalize (x + sin (π t / 2) ^ 2 • (f x - x))`
is a `C^k` diffeotopy of the sphere from the identity to `f`
(`TauCeti.coe_sphereInterpolationDiffeotopy_apply`, `TauCeti.sphereInterpolationDiffeotopy_final`).
-/
def sphereInterpolationDiffeotopy : Diffeotopy (𝓡 n) k (sphere (0 : E) 1) :=
  letI := completeSpace_of_fact (E := E) n
  { toDiffeomorph :=
      { toFun := fun p ↦ (p.1, sphereSlice hlip hL (p.1 : ℝ) p.2)
        invFun := fun p ↦ (p.1, sphereSliceSymm hlip hL (p.1 : ℝ) p.2)
        left_inv := fun p ↦ Prod.ext rfl (sphereSliceSymm_sphereSlice hlip hL _ p.2)
        right_inv := fun p ↦ Prod.ext rfl (sphereSlice_sphereSliceSymm hlip hL _ p.2)
        contMDiff_toFun := contMDiff_fst.prodMk
          (contMDiff_comp_coe_Icc (contMDiff_sphereSlice f.contMDiff hlip hL))
        contMDiff_invFun := contMDiff_fst.prodMk
          (contMDiff_comp_coe_Icc (contMDiff_sphereSliceSymm hk f.contMDiff hlip hL)) }
    fst_apply _ := rfl
    snd_apply_zero' x := sphereSlice_zero hlip hL x }

omit [CompleteSpace E] in
/-- At time `t`, the interpolation diffeotopy sends `x` to the normalization of
`x + sin (π t / 2) ^ 2 • (f x - x)`. -/
@[simp]
theorem coe_sphereInterpolationDiffeotopy_apply (p : I × sphere (0 : E) 1) :
    (sphereInterpolationDiffeotopy f hL hlip hk p : E) =
      normalize ((p.2 : E) + Real.sin (Real.pi * p.1 / 2) ^ 2 • ((f p.2 : E) - p.2)) := by
  let := completeSpace_of_fact (E := E) n
  rw [← sphereCone_coe (f := fun x ↦ (f x : E) - x) p.2, ← weight_def, ← slice_apply hlip hL]
  rfl

omit [CompleteSpace E] in
/-- The interpolation diffeotopy ends at `f`. -/
@[simp]
theorem sphereInterpolationDiffeotopy_final :
    (sphereInterpolationDiffeotopy f hL hlip hk).final = f :=
  _root_.Diffeomorph.ext fun x ↦ Subtype.ext <| by
    rw [Diffeotopy.final_apply, coe_sphereInterpolationDiffeotopy_apply, Set.Icc.coe_one, mul_one,
      Real.sin_pi_div_two, one_pow, one_smul, add_sub_cancel,
      normalize_eq_self_of_norm_eq_one (norm_eq_of_mem_sphere _)]

end Sphere

/-! ### The local isotopy lemma -/

section Local

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
  [Fact (finrank ℝ E = n + 1)]

/-- Points of a chord of length at most one between two unit vectors have norm at least
`1 / 2`. -/
private theorem norm_mem_Icc_of_mem_segment {p q z : E} (hp : ‖p‖ = 1) (hq : ‖q‖ = 1)
    (hpq : ‖p - q‖ ≤ 1) (hz : z ∈ segment ℝ p q) : 1 / 2 ≤ ‖z‖ ∧ ‖z‖ ≤ 1 := by
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := hz
  obtain rfl : a = 1 - b := by linarith
  have h₁ := norm_le_norm_add_norm_sub' p ((1 - b) • p + b • q)
  rw [show p - ((1 - b) • p + b • q) = b • (p - q) by module, norm_smul,
    Real.norm_of_nonneg hb] at h₁
  have h₂ := norm_le_norm_add_norm_sub' q ((1 - b) • p + b • q)
  rw [show q - ((1 - b) • p + b • q) = (1 - b) • (q - p) by module, norm_smul,
    Real.norm_of_nonneg ha, norm_sub_rev] at h₂
  have h₃ : ‖(1 - b) • p + b • q‖ ≤ 1 := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, norm_smul, hp, hq, Real.norm_of_nonneg ha, Real.norm_of_nonneg hb]
    linarith
  constructor <;> nlinarith

variable [FiniteDimensional ℝ E]

/-- The punctured space `E \ {0}`, as an open subset of `E`. -/
private abbrev punctured (E : Type*) [NormedAddCommGroup E] : Opens E :=
  ⟨{0}ᶜ, isOpen_compl_singleton⟩

omit [FiniteDimensional ℝ E] in
/-- The inclusion of the sphere into `E`, as a `C^k` map. -/
private def coeSphereMap : C^k⟮𝓡 n, sphere (0 : E) 1; 𝓘(ℝ, E), E⟯ :=
  ⟨_, contMDiff_coe_sphere⟩

omit [FiniteDimensional ℝ E] in
/-- The radial projection of the punctured space onto the sphere, as a `C^k` map. -/
private def normalizeMap : C^k⟮𝓘(ℝ, E), punctured E; 𝓡 n, sphere (0 : E) 1⟯ :=
  ⟨_, contMDiff_normalize_sphere⟩

omit [FiniteDimensional ℝ E] in
/-- The displacement `y ↦ f (y / ‖y‖) - y / ‖y‖` of `f`, read on the punctured space through the
radial projection, as a `C^k` map. -/
private def displacement (f : Diff (𝓡 n) (sphere (0 : E) 1) k) :
    C^k⟮𝓘(ℝ, E), punctured E; 𝓘(ℝ, E), E⟯ :=
  ContMDiffMap.comp (ContMDiffMap.comp coeSphereMap f.toContMDiffMap - coeSphereMap) normalizeMap

/-- The displacement depends continuously on `f`. -/
private theorem continuous_displacement :
    Continuous (displacement : Diff (𝓡 n) (sphere (0 : E) 1) k → _) := by
  have h₁ : Continuous fun g : C^k⟮𝓡 n, sphere (0 : E) 1; 𝓡 n, sphere (0 : E) 1⟯ ↦
      ContMDiffMap.comp coeSphereMap g :=
    ContMDiffMap.continuous_comp_manifoldWeakWhitney.comp (continuous_const.prodMk continuous_id)
  have h₂ : Continuous fun g : C^k⟮𝓡 n, sphere (0 : E) 1; 𝓘(ℝ, E), E⟯ ↦ g - coeSphereMap :=
    ContMDiffMap.continuous_sub_manifoldWeakWhitney.comp (continuous_id.prodMk continuous_const)
  have h₃ : Continuous fun g : C^k⟮𝓡 n, sphere (0 : E) 1; 𝓘(ℝ, E), E⟯ ↦
      ContMDiffMap.comp g (normalizeMap (E := E)) :=
    ContMDiffMap.continuous_comp_manifoldWeakWhitney.comp (continuous_id.prodMk continuous_const)
  exact h₃.comp (h₂.comp (h₁.comp Diffeomorph.continuous_toContMDiffMap))

omit [FiniteDimensional ℝ E] in
/-- On the punctured space, the displacement is the `0`-homogeneous extension of `x ↦ f x - x`. -/
private theorem extend_displacement_eqOn (f : Diff (𝓡 n) (sphere (0 : E) 1) k) :
    EqOn (Function.extend Subtype.val (displacement f) fun _ ↦ (0 : E))
      (sphereExtend fun x ↦ (f x : E) - x) (punctured E) := fun y hy ↦ by
  refine (Subtype.val_injective.extend_apply (displacement f) (fun _ ↦ (0 : E)) ⟨y, hy⟩).trans ?_
  rw [sphereExtend_of_ne_zero _ hy]
  rfl

/-- Near the identity, the jets of order at most one of the displacement are small on the closed
annulus `1 / 2 ≤ ‖y‖ ≤ 1`, a compact subset of the punctured space. -/
private theorem eventually_forall_norm_iteratedFDerivWithin_lt (m : ℕ) (hm : (m : ℕ∞ω) ≤ k)
    {r : ℝ} (hr : 0 < r) :
    ∀ᶠ f in 𝓝 (1 : Diff (𝓡 n) (sphere (0 : E) 1) k), ∀ y : E, 1 / 2 ≤ ‖y‖ → ‖y‖ ≤ 1 →
      ‖iteratedFDerivWithin ℝ m (sphereExtend fun x ↦ (f x : E) - (x : E)) (punctured E) y‖ <
        r := by
  set A : Set (punctured E) := Subtype.val ⁻¹' (closedBall (0 : E) 1 ∩ {y | 1 / 2 ≤ ‖y‖})
  have hA : IsCompact A := IsInducing.subtypeVal.isCompact_preimage'
    ((isCompact_closedBall 0 1).inter_right (isClosed_le continuous_const continuous_norm))
    fun y hy ↦ ⟨⟨y, fun h ↦ by norm_num [show y = 0 from h] at hy⟩, rfl⟩
  have hc : Continuous fun f : Diff (𝓡 n) (sphere (0 : E) 1) k ↦
      ContMDiffMap.openIteratedFDerivContinuousMap (punctured E) (displacement f) m hm :=
    ((continuous_apply (⟨m, hm⟩ : {m : ℕ // (m : ℕ∞ω) ≤ k})).comp
      ((ContMDiffMap.continuous_openWeakWhitneyJet (punctured E)).comp
        continuous_displacement)).congr fun f ↦
          ContMDiffMap.openWeakWhitneyJet_apply (punctured E) (displacement f) ⟨m, hm⟩
  -- The jet at a point of the punctured space is that of the `0`-homogeneous extension.
  have hjet (f : Diff (𝓡 n) (sphere (0 : E) 1) k) (y : punctured E) :
      ContMDiffMap.openIteratedFDerivContinuousMap (punctured E) (displacement f) m hm y =
        iteratedFDerivWithin ℝ m (sphereExtend fun x ↦ (f x : E) - (x : E)) (punctured E) y := by
    rw [ContMDiffMap.openIteratedFDerivContinuousMap_apply,
      iteratedFDerivWithin_congr (extend_displacement_eqOn f) y.property]
  have h₁ : MapsTo (ContMDiffMap.openIteratedFDerivContinuousMap (punctured E) (displacement 1) m
      hm) A (ball 0 r) := fun y _ ↦ by
    have h0 : (fun x : sphere (0 : E) 1 ↦ ((1 : Diff (𝓡 n) (sphere (0 : E) 1) k) x : E) - x) = 0 :=
      funext fun x ↦ sub_self _
    rw [mem_ball_zero_iff, hjet, h0, sphereExtend_zero_fun, iteratedFDerivWithin_zero,
      Pi.zero_apply, norm_zero]
    exact hr
  filter_upwards [((ContinuousMap.isOpen_setOfPred_mapsTo hA isOpen_ball).preimage hc).mem_nhds
    h₁] with f hf y hy₁ hy₂
  have hy : y ≠ 0 := fun h ↦ by norm_num [h] at hy₁
  simpa only [mem_ball_zero_iff, hjet] using hf (show (⟨y, hy⟩ : punctured E) ∈ A from
    ⟨mem_closedBall_zero_iff.2 hy₂, hy₁⟩)

omit [FiniteDimensional ℝ E] in
/-- **The mean value theorem on short chords.** If the derivative of the `0`-homogeneous extension
of a `C^k` map `g` on the sphere, `1 ≤ k`, is bounded by `c` on the closed annulus
`1 / 2 ≤ ‖y‖ ≤ 1`, then `‖g p - g q‖ ≤ c ‖p - q‖` whenever `‖p - q‖ ≤ 1`. -/
private theorem norm_sub_le_of_norm_fderiv_sphereExtend_le (hk : 1 ≤ k)
    {g : sphere (0 : E) 1 → E} (hg : ContMDiff (𝓡 n) 𝓘(ℝ, E) k g) {c : ℝ}
    (hc : ∀ y : E, 1 / 2 ≤ ‖y‖ → ‖y‖ ≤ 1 → ‖fderiv ℝ (sphereExtend g) y‖ ≤ c)
    {p q : sphere (0 : E) 1} (hpq : ‖(p : E) - q‖ ≤ 1) : ‖g p - g q‖ ≤ c * ‖(p : E) - q‖ := by
  have hmem {z : E} (hz : z ∈ segment ℝ (q : E) p) := norm_mem_Icc_of_mem_segment
    (norm_eq_of_mem_sphere q) (norm_eq_of_mem_sphere p) (by rwa [norm_sub_rev]) hz
  have hne {z : E} (hz : z ∈ segment ℝ (q : E) p) : z ≠ 0 := fun h ↦ by
    have h' := (hmem hz).1
    rw [h, norm_zero] at h'
    norm_num at h'
  rw [← sphereExtend_coe g p, ← sphereExtend_coe g q]
  exact (convex_segment (q : E) p).norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ)
    (fun z hz ↦ (contDiffAt_sphereExtend (hne hz) (hg _)).differentiableAt
      (zero_lt_one.trans_le hk).ne')
    (fun z hz ↦ hc z (hmem hz).1 (hmem hz).2) (left_mem_segment ℝ _ _) (right_mem_segment ℝ _ _)

/-- Near the identity, the displacement `x ↦ f x - x` is bounded by `1 / 8` and `1 / 4`-Lipschitz
on the sphere, so its cone is Lipschitz with constant `1 / 8 + 2 / 4 < 1`. -/
private theorem eventually_exists_lipschitzWith_sphereCone_sub (hk : 1 ≤ k) :
    ∀ᶠ f in 𝓝 (1 : Diff (𝓡 n) (sphere (0 : E) 1) k),
      ∃ L : ℝ≥0, L < 1 ∧ LipschitzWith L (sphereCone fun x ↦ (f x : E) - (x : E)) := by
  filter_upwards [eventually_forall_norm_iteratedFDerivWithin_lt (E := E) (n := n) 0 zero_le
    (r := 1 / 8) (by norm_num), eventually_forall_norm_iteratedFDerivWithin_lt (E := E) (n := n)
    1 (by exact_mod_cast hk) (r := 1 / 4) (by norm_num)] with f h₀ h₁
  set g := fun x : sphere (0 : E) 1 ↦ (f x : E) - x
  have hg : ContMDiff (𝓡 n) 𝓘(ℝ, E) k g := (contMDiff_coe_sphere.comp f.contMDiff).sub
    contMDiff_coe_sphere
  have hg₀ (x : sphere (0 : E) 1) : ‖g x‖ ≤ 1 / 8 := by
    have h := h₀ x (by norm_num [norm_eq_of_mem_sphere x]) (norm_eq_of_mem_sphere x).le
    rw [norm_iteratedFDerivWithin_zero, sphereExtend_coe] at h
    exact h.le
  have hd (y : E) (hy₁ : 1 / 2 ≤ ‖y‖) (hy₂ : ‖y‖ ≤ 1) : ‖fderiv ℝ (sphereExtend g) y‖ ≤ 1 / 4 := by
    have hy : y ≠ 0 := fun h ↦ by norm_num [h] at hy₁
    have h := h₁ y hy₁ hy₂
    rw [norm_iteratedFDerivWithin_one _ ((punctured E).isOpen.uniqueDiffWithinAt hy),
      fderivWithin_of_isOpen (punctured E).isOpen hy] at h
    exact h.le
  -- Far apart points are handled by the bound on `g`, close ones by the mean value theorem.
  have hg₁ : LipschitzWith (1 / 4) g := LipschitzWith.of_dist_le_mul fun p q ↦ by
    rw [dist_eq_norm, Subtype.dist_eq, dist_eq_norm, NNReal.coe_div, NNReal.coe_one,
      NNReal.coe_ofNat]
    rcases le_or_gt ‖(p : E) - q‖ 1 with hpq | hpq
    · exact norm_sub_le_of_norm_fderiv_sphereExtend_le hk hg hd hpq
    · linarith [norm_sub_le (g p) (g q), hg₀ p, hg₀ q]
  refine ⟨1 / 8 + 2 * (1 / 4), ?_, lipschitzWith_sphereCone (fun x ↦ ?_) hg₁⟩
  · rw [← NNReal.coe_lt_coe]
    push_cast
    norm_num
  · push_cast
    exact hg₀ x

/-- **The local isotopy lemma for spheres.** Every `C^k` diffeomorphism of the unit sphere close
enough to the identity in the weak Whitney topology, `1 ≤ k`, is the final diffeomorphism of a
`C^k` diffeotopy (`TauCeti.sphereInterpolationDiffeotopy`). -/
theorem eventually_exists_diffeotopy_final_eq (hk : 1 ≤ k) :
    ∀ᶠ f in 𝓝 (1 : Diff (𝓡 n) (sphere (0 : E) 1) k),
      ∃ Φ : Diffeotopy (𝓡 n) k (sphere (0 : E) 1), Φ.final = f :=
  (eventually_exists_lipschitzWith_sphereCone_sub hk).mono fun f ⟨_, hL, hlip⟩ ↦
    ⟨sphereInterpolationDiffeotopy f hL hlip hk, sphereInterpolationDiffeotopy_final f hL hlip hk⟩

/-- Near every diffeomorphism `h` of the sphere, every diffeomorphism is `h` followed by the final
diffeomorphism of a diffeotopy. -/
private theorem eventually_exists_diffeotopy_mul_final_eq (hk : 1 ≤ k)
    (h : Diff (𝓡 n) (sphere (0 : E) 1) k) :
    ∀ᶠ h' in 𝓝 h, ∃ Ψ : Diffeotopy (𝓡 n) k (sphere (0 : E) 1), h * Ψ.final = h' := by
  have ht : Tendsto (fun h' ↦ h⁻¹ * h') (𝓝 h) (𝓝 1) := by
    simpa only [inv_mul_cancel] using (continuous_const_mul h⁻¹).tendsto h
  filter_upwards [ht.eventually (eventually_exists_diffeotopy_final_eq hk)] with h' ⟨Ψ, hΨ⟩
  exact ⟨Ψ, by rw [hΨ, mul_inv_cancel_left]⟩

/-- **The path components of `Diff(Sⁿ)` are its diffeotopy classes.** Two `C^k` diffeomorphisms
`f` and `g` of the unit sphere, `1 ≤ k`, are joined by a path in the weak Whitney topology exactly
when `g = f ∘ φ₁` for the final diffeomorphism `φ₁` of a `C^k` diffeotopy. -/
theorem joined_iff_exists_diffeotopy_mul_final_eq (hk : 1 ≤ k)
    {f g : Diff (𝓡 n) (sphere (0 : E) 1) k} :
    Joined f g ↔ ∃ Φ : Diffeotopy (𝓡 n) k (sphere (0 : E) 1), f * Φ.final = g := by
  refine ⟨fun hfg ↦ ?_, fun ⟨Φ, hΦ⟩ ↦ hΦ ▸ by
    simpa only [mul_one] using Φ.joined_one_final.map (continuous_const_mul f)⟩
  -- The diffeomorphisms diffeotopic to `f` form a clopen set, so they contain its path component.
  set C := {h | ∃ Φ : Diffeotopy (𝓡 n) k (sphere (0 : E) 1), f * Φ.final = h}
  have hC : IsClopen C := by
    refine ⟨isOpen_compl_iff.1 (isOpen_iff_mem_nhds.2 fun h hh ↦ ?_),
      isOpen_iff_mem_nhds.2 fun h ⟨Φ, hΦ⟩ ↦ ?_⟩
    · filter_upwards [eventually_exists_diffeotopy_mul_final_eq hk h] with h' ⟨Ψ, hΨ⟩ ⟨Φ, hΦ⟩
      exact hh ⟨Ψ.symm.trans Φ, by
        rw [Diffeotopy.final_symm_trans, ← mul_assoc, hΦ, ← hΨ, mul_inv_cancel_right]⟩
    · filter_upwards [eventually_exists_diffeotopy_mul_final_eq hk h] with h' ⟨Ψ, hΨ⟩
      exact ⟨Ψ.trans Φ, by
        rw [Diffeotopy.final_trans, ← _root_.Diffeomorph.mul_def, ← mul_assoc, hΦ, hΨ]⟩
  refine hC.connectedComponent_subset ⟨Diffeotopy.refl _ _ _, ?_⟩
    (pathComponent_subset_component f (mem_pathComponent_iff.2 hfg))
  rw [Diffeotopy.final_refl, ← _root_.Diffeomorph.one_def, mul_one]

end Local

end TauCeti
