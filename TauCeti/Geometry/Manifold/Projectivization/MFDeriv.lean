/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.MFDeriv.Defs
public import TauCeti.Geometry.Manifold.Instances.Projectivization
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import TauCeti.Geometry.Manifold.MFDeriv.ModelChart

/-!
# The derivative of the projection onto projective space

The projection `w ↦ [w]` from the nonzero vectors of `𝕜ⁿ⁺¹` onto projective space
`ℙⁿ = ℙ 𝕜 (Fin (n + 1) → 𝕜)`, with its manifold structure of standard affine charts, has at
every `v ≠ 0` a derivative `Projectivization.mfderivMk v : 𝕜ⁿ⁺¹ → T_[v] ℙⁿ`. It is onto
(`Projectivization.surjective_mfderivMk`), and its kernel is the line `𝕜 v`
(`Projectivization.ker_mfderivMk`), the direction in which `[w]` does not move. So it identifies
the tangent space of `ℙⁿ` at `[v]` with the quotient `𝕜ⁿ⁺¹ / 𝕜 v`: this is the Euler sequence
`0 → 𝕜 v → 𝕜ⁿ⁺¹ → T_[v] ℙⁿ → 0` at the point `[v]`.

A map `f` to projective space that near a point `x` sends `y` to `[F y]`, for homogeneous
coordinates `F` differentiable at `x`, therefore has the derivative
`mfderivMk (F x) ∘ dF` at `x` (`Projectivization.hasMFDerivAt_of_eventually_eq_mk`,
`Projectivization.mfderiv_eq_mfderivMk_comp`). Its kernel consists
of the tangent vectors that `dF` sends into the line `𝕜 (F x)`
(`Projectivization.ker_mfderiv_of_eventually_eq_mk`), and it is onto exactly when the range of
`dF` and the line `𝕜 (F x)` together span `𝕜ⁿ⁺¹`
(`Projectivization.surjective_mfderiv_iff_of_eventually_eq_mk`). This reduces derivatives of maps
to projective space given in homogeneous coordinates, such as the evaluation maps of lines and the
maps induced by linear maps, to linear algebra in `𝕜ⁿ⁺¹`.

In the standard affine chart at a coordinate `i` with `v i ≠ 0` the projection reads
`w ↦ (w (i.succAbove k) / w i)_k`, whose derivative at `v` sends `h` to
`(h (i.succAbove k) / v i - v (i.succAbove k) h i / (v i)²)_k`; the kernel and the surjectivity
are read off from this formula, the inverse chart having an invertible derivative.

## Main declarations

* `Projectivization.mfderivMk`: the derivative of the projection `w ↦ [w]` at a vector `v`.
* `Projectivization.ker_mfderivMk`, `Projectivization.surjective_mfderivMk`: at `v ≠ 0` it is onto
  with kernel `𝕜 v`.
* `Projectivization.hasMFDerivAt_of_eventually_eq_mk`, `Projectivization.mfderiv_eq_mfderivMk_comp`:
  the chain rule for maps given in homogeneous coordinates.
* `Projectivization.isInvertible_mfderiv_affineChart_symm`: the inverse of each standard affine
  chart has an invertible derivative.

## References

* P. Griffiths and J. Harris, *Principles of Algebraic Geometry*, Wiley, 1978, Chapter 0,
  Section 1 (projective space, its affine charts and the tangent spaces of its points) and
  Section 2 (the Euler sequence).
-/

public section

open Set Function Filter Submodule
open scoped Manifold Topology LinearAlgebra.Projectivization

namespace Projectivization

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {n : ℕ}

open scoped Classical in
/-- **The derivative of the projection onto projective space** at a vector `v` of `𝕜ⁿ⁺¹`: the
derivative at `v` of the map `w ↦ [w]` to `ℙⁿ`, with values in the tangent space of `ℙⁿ` at
`[v]`. The map is given the value `[e₀]` at `w = 0`, where `[w]` is undefined; this does not affect
its derivative at `v ≠ 0`, which is onto with kernel `𝕜 v` (`Projectivization.surjective_mfderivMk`,
`Projectivization.ker_mfderivMk`). -/
noncomputable def mfderivMk (v : Fin (n + 1) → 𝕜) : (Fin (n + 1) → 𝕜) →L[𝕜] Fin n → 𝕜 :=
  mfderiv 𝓘(𝕜, Fin (n + 1) → 𝕜) 𝓘(𝕜, Fin n → 𝕜)
    (fun w ↦ if hw : w = 0 then mk 𝕜 (Pi.single 0 1) (by simp) else mk 𝕜 w hw) v

open scoped Classical in
/-- The projection with the value `[e₀]` at `0` is `[w]` near every nonzero `v`. -/
private theorem eventually_dite_eq_mk {v : Fin (n + 1) → 𝕜} (hv : v ≠ 0) :
    ∀ᶠ w in 𝓝 v, ∃ hw : w ≠ 0,
      (if hw : w = 0 then mk 𝕜 (Pi.single 0 1) (by simp) else mk 𝕜 w hw) = mk 𝕜 w hw := by
  filter_upwards [isOpen_ne.mem_nhds hv] with w hw
  exact ⟨hw, by simp [hw]⟩

section ChainRule

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H} [TopologicalSpace M] [ChartedSpace H M]
  {f : M → ℙ 𝕜 (Fin (n + 1) → 𝕜)} {F : M → Fin (n + 1) → 𝕜} {x : M}

open scoped Classical in
/-- **The chain rule for maps given in homogeneous coordinates.** If a map `f` to projective space
sends `y` to `[F y]` near `x`, for homogeneous coordinates `F` with derivative `F'` at `x`, then `f`
has at `x` the derivative `F'` followed by the derivative of the projection at `F x`. -/
theorem hasMFDerivAt_of_eventually_eq_mk
    {F' : TangentSpace I x →L[𝕜] Fin (n + 1) → 𝕜}
    (hF : HasMFDerivAt I 𝓘(𝕜, Fin (n + 1) → 𝕜) F x F')
    (hf : ∀ᶠ y in 𝓝 x, ∃ hy : F y ≠ 0, f y = mk 𝕜 (F y) hy) :
    HasMFDerivAt I 𝓘(𝕜, Fin n → 𝕜) f x ((mfderivMk (F x)).comp F') := by
  set g : (Fin (n + 1) → 𝕜) → ℙ 𝕜 (Fin (n + 1) → 𝕜) :=
    fun w ↦ if hw : w = 0 then mk 𝕜 (Pi.single 0 1) (by simp) else mk 𝕜 w hw
  obtain ⟨hx, -⟩ := hf.self_of_nhds
  have hg : MDifferentiableAt 𝓘(𝕜, Fin (n + 1) → 𝕜) 𝓘(𝕜, Fin n → 𝕜) g (F x) :=
    (contMDiffAt_of_eventually_eq_mk (r := 1) contMDiffAt_id (eventually_dite_eq_mk hx))
      |>.mdifferentiableAt one_ne_zero
  have hfg : f =ᶠ[𝓝 x] g ∘ F := hf.mono fun y ⟨hy, hfy⟩ ↦ by simp [g, hy, hfy]
  rw [mfderivMk]
  exact (hg.hasMFDerivAt.comp x hF).congr_of_eventuallyEq hfg

/-- A map to projective space given near `x` by homogeneous coordinates differentiable at `x` is
differentiable at `x`. -/
theorem mdifferentiableAt_of_eventually_eq_mk
    (hF : MDifferentiableAt I 𝓘(𝕜, Fin (n + 1) → 𝕜) F x)
    (hf : ∀ᶠ y in 𝓝 x, ∃ hy : F y ≠ 0, f y = mk 𝕜 (F y) hy) :
    MDifferentiableAt I 𝓘(𝕜, Fin n → 𝕜) f x :=
  (hasMFDerivAt_of_eventually_eq_mk hF.hasMFDerivAt hf).mdifferentiableAt

/-- **The chain rule for maps given in homogeneous coordinates**, for `mfderiv`. If a map `f` to
projective space sends `y` to `[F y]` near `x`, for homogeneous coordinates `F` differentiable at
`x`, then its derivative at `x` is the derivative `dF` followed by the derivative of the projection
at `F x`. -/
theorem mfderiv_eq_mfderivMk_comp (hF : MDifferentiableAt I 𝓘(𝕜, Fin (n + 1) → 𝕜) F x)
    (hf : ∀ᶠ y in 𝓝 x, ∃ hy : F y ≠ 0, f y = mk 𝕜 (F y) hy) :
    mfderiv I 𝓘(𝕜, Fin n → 𝕜) f x =
      (mfderivMk (F x)).comp (mfderiv I 𝓘(𝕜, Fin (n + 1) → 𝕜) F x) :=
  (hasMFDerivAt_of_eventually_eq_mk hF.hasMFDerivAt hf).mfderiv

end ChainRule

/-! ### The projection in an affine chart -/

/-- The derivative at `v` of the affine coordinates `w ↦ (w (i.succAbove k) / w i)_k` of the
chart at `i`: it sends `h` to `(h (i.succAbove k) / v i - v (i.succAbove k) h i / (v i)²)_k`. -/
private noncomputable def ratioFDeriv (i : Fin (n + 1)) (v : Fin (n + 1) → 𝕜) :
    (Fin (n + 1) → 𝕜) →L[𝕜] Fin n → 𝕜 :=
  ContinuousLinearMap.pi fun k ↦ (v i)⁻¹ • ContinuousLinearMap.proj (i.succAbove k) -
    ((v i ^ 2)⁻¹ * v (i.succAbove k)) • ContinuousLinearMap.proj i

private theorem ratioFDeriv_apply (i : Fin (n + 1)) (v h : Fin (n + 1) → 𝕜) (k : Fin n) :
    ratioFDeriv i v h k = (v i)⁻¹ * h (i.succAbove k) - (v i ^ 2)⁻¹ * v (i.succAbove k) * h i := by
  simp [ratioFDeriv, mul_assoc]

private theorem hasFDerivAt_ratio {i : Fin (n + 1)} {v : Fin (n + 1) → 𝕜} (hvi : v i ≠ 0) :
    HasFDerivAt (fun w : Fin (n + 1) → 𝕜 ↦ fun k ↦ w (i.succAbove k) / w i)
      (ratioFDeriv i v) v := by
  refine hasFDerivAt_pi.2 fun k ↦ ?_
  have h := (hasFDerivAt_apply (𝕜 := 𝕜) (i.succAbove k) v).mul
    ((hasFDerivAt_inv hvi).comp v (hasFDerivAt_apply (𝕜 := 𝕜) i v))
  simp only [div_eq_mul_inv]
  refine h.congr_fderiv (ContinuousLinearMap.ext fun h ↦ ?_)
  simp
  ring

/-- At a vector `v` with `v i ≠ 0` the kernel of the derivative of the affine coordinates of the
chart at `i` is the line `𝕜 v`. -/
private theorem ker_ratioFDeriv {i : Fin (n + 1)} {v : Fin (n + 1) → 𝕜} (hvi : v i ≠ 0) :
    (ratioFDeriv i v).ker = 𝕜 ∙ v := by
  refine le_antisymm (fun h hh ↦ ?_) ((span_singleton_le_iff_mem _ _).2 ?_)
  · rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe] at hh
    refine mem_span_singleton.2 ⟨h i / v i, funext fun j ↦ ?_⟩
    rcases Fin.eq_self_or_eq_succAbove i j with rfl | ⟨k, rfl⟩
    · simp [hvi]
    · have hk := congr_fun hh k
      rw [ratioFDeriv_apply, Pi.zero_apply] at hk
      -- `hk` says `h (i.succAbove k) / v i = v (i.succAbove k) h i / (v i)²`.
      rw [Pi.smul_apply, smul_eq_mul, div_mul_eq_mul_div, div_eq_iff hvi]
      field_simp at hk
      linear_combination -hk
  · rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe]
    funext k
    rw [ratioFDeriv_apply, Pi.zero_apply]
    field_simp
    ring

/-- At a vector `v` with `v i ≠ 0` the derivative of the affine coordinates of the chart at `i`
is onto: `h = v i • (0 at i, z elsewhere)` is sent to `z`. -/
private theorem surjective_ratioFDeriv {i : Fin (n + 1)} {v : Fin (n + 1) → 𝕜} (hvi : v i ≠ 0) :
    Surjective (ratioFDeriv i v) := fun z ↦
  ⟨Fin.insertNth (α := fun _ ↦ 𝕜) i 0 (v i • z), funext fun k ↦ by
    rw [ratioFDeriv_apply]
    simp [hvi]⟩

/-- At a vector `v` with `v i ≠ 0` the derivative of the projection is the derivative of the
affine coordinates of the chart at `i` followed by the derivative of the inverse chart. -/
private theorem mfderivMk_eq_comp {i : Fin (n + 1)} {v : Fin (n + 1) → 𝕜} (hvi : v i ≠ 0) :
    mfderivMk v = (mfderiv 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, Fin n → 𝕜) (affineChart (K := 𝕜) i).symm
      (fun k ↦ v (i.succAbove k) / v i) : (Fin n → 𝕜) →L[𝕜] Fin n → 𝕜).comp
        (ratioFDeriv i v) := by
  have hchart := ((contMDiff_affineChart_symm (𝕜 := 𝕜) i 1).mdifferentiableAt one_ne_zero
    (x := fun k ↦ v (i.succAbove k) / v i)).hasMFDerivAt
  refine ((hchart.comp v (hasFDerivAt_ratio hvi).hasMFDerivAt).congr_of_eventuallyEq ?_).mfderiv
  have hv : v ≠ 0 := fun h ↦ hvi (by simp [h])
  filter_upwards [eventually_dite_eq_mk hv,
    (continuous_apply i).continuousAt.eventually_ne hvi] with w ⟨hw, hgw⟩ hwi
  rw [hgw, comp_apply, affineChart_symm_apply, eq_comm, mk_eq_mk_iff']
  exact ⟨(w i)⁻¹, (Fin.insertNth_one_div_eq_inv_smul i w hwi).symm⟩

/-- The inverse `z ↦ [Fin.insertNth i 1 z]` of the standard affine chart at `i` of projective
space has an invertible derivative at every point. -/
theorem isInvertible_mfderiv_affineChart_symm (i : Fin (n + 1)) (z : Fin n → 𝕜) :
    (mfderiv 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, Fin n → 𝕜) (affineChart (K := 𝕜) i).symm z).IsInvertible := by
  rw [← coe_affineOpenPartialHomeomorph_symm]
  exact TauCeti.isInvertible_mfderiv_chart_symm
    (affineOpenPartialHomeomorph_mem_maximalAtlas (I := 𝓘(𝕜, Fin n → 𝕜)) (r := 1) i) (by simp)

/-- **The kernel of the derivative of the projection.** At `v ≠ 0` the derivative of `w ↦ [w]`
vanishes exactly on the line `𝕜 v`. -/
theorem ker_mfderivMk {v : Fin (n + 1) → 𝕜} (hv : v ≠ 0) :
    (mfderivMk v).ker = 𝕜 ∙ v := by
  obtain ⟨i, hvi⟩ := Function.ne_iff.1 hv
  have hJ := isInvertible_mfderiv_affineChart_symm (𝕜 := 𝕜) i fun k ↦ v (i.succAbove k) / v i
  rw [mfderivMk_eq_comp hvi]
  exact (LinearMap.ker_comp_of_ker_eq_bot _ (LinearMap.ker_eq_bot.2 hJ.injective)).trans
    (ker_ratioFDeriv hvi)

/-- **The derivative of the projection is onto.** At `v ≠ 0` every tangent vector of
projective space at `[v]` is the derivative of `w ↦ [w]` along some vector of `𝕜ⁿ⁺¹`. -/
theorem surjective_mfderivMk {v : Fin (n + 1) → 𝕜} (hv : v ≠ 0) : Surjective (mfderivMk v) := by
  obtain ⟨i, hvi⟩ := Function.ne_iff.1 hv
  have hJ := isInvertible_mfderiv_affineChart_symm (𝕜 := 𝕜) i fun k ↦ v (i.succAbove k) / v i
  rw [mfderivMk_eq_comp hvi]
  exact hJ.surjective.comp (surjective_ratioFDeriv hvi)

/-! ### Maps given in homogeneous coordinates -/

section HomogeneousCoordinates

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H} [TopologicalSpace M] [ChartedSpace H M]
  {f : M → ℙ 𝕜 (Fin (n + 1) → 𝕜)} {F : M → Fin (n + 1) → 𝕜} {x : M}

/-- **The kernel of the derivative of a map given in homogeneous coordinates.** If `f` sends `y`
to `[F y]` near `x`, for `F` differentiable at `x`, a tangent vector at `x` is killed by the
derivative of `f` exactly when `dF` sends it into the line `𝕜 (F x)`. -/
theorem ker_mfderiv_of_eventually_eq_mk (hF : MDifferentiableAt I 𝓘(𝕜, Fin (n + 1) → 𝕜) F x)
    (hf : ∀ᶠ y in 𝓝 x, ∃ hy : F y ≠ 0, f y = mk 𝕜 (F y) hy) :
    (mfderiv I 𝓘(𝕜, Fin n → 𝕜) f x).ker =
      (𝕜 ∙ F x).comap (mfderiv I 𝓘(𝕜, Fin (n + 1) → 𝕜) F x).toLinearMap := by
  rw [mfderiv_eq_mfderivMk_comp hF hf, ← ker_mfderivMk hf.self_of_nhds.1]
  exact LinearMap.ker_comp _ _

/-- **A map given in homogeneous coordinates is a submersion at `x`** exactly when the range of
the derivative of its homogeneous coordinates `F` and the line `𝕜 (F x)` together span
`𝕜ⁿ⁺¹`. -/
theorem surjective_mfderiv_iff_of_eventually_eq_mk
    (hF : MDifferentiableAt I 𝓘(𝕜, Fin (n + 1) → 𝕜) F x)
    (hf : ∀ᶠ y in 𝓝 x, ∃ hy : F y ≠ 0, f y = mk 𝕜 (F y) hy) :
    Surjective (mfderiv I 𝓘(𝕜, Fin n → 𝕜) f x) ↔
      (mfderiv I 𝓘(𝕜, Fin (n + 1) → 𝕜) F x).range ⊔ 𝕜 ∙ F x = ⊤ := by
  have hx := hf.self_of_nhds.1
  have hT := surjective_mfderivMk hx
  -- For the surjective `T = mfderivMk (F x)`, `T ∘ dF` is onto exactly when
  -- `map T (range dF) = ⊤`, that is when `range dF ⊔ ker T = ⊤`.
  have key (G : TangentSpace I x →ₗ[𝕜] Fin (n + 1) → 𝕜) :
      Surjective ((mfderivMk (F x)).toLinearMap ∘ₗ G) ↔ LinearMap.range G ⊔ 𝕜 ∙ F x = ⊤ := by
    rw [← ker_mfderivMk hx, ← LinearMap.map_eq_top_iff (LinearMap.range_eq_top.2 hT),
      ← LinearMap.range_comp, LinearMap.range_eq_top]
  rw [mfderiv_eq_mfderivMk_comp hF hf]
  exact key _

end HomogeneousCoordinates

end Projectivization
