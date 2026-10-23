/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita.Nondegenerate.Basic
import TauCeti.Analysis.Calculus.ContinuousLinearMapInverse
import TauCeti.Analysis.Calculus.FDeriv.ContinuousLinearMap
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace
import TauCeti.Geometry.Manifold.MFDeriv.Parametric
import TauCeti.Geometry.Manifold.VectorBundle.NondegenerateMetric.Musical

/-!
# The first variation of the Levi-Civita connection

Let `g_s` be a one-parameter family of smooth nondegenerate metrics on `M`, of any signature,
jointly `C²` in `(s, x)` as a map into the bundle of bilinear forms on `TM`, and let `∇ˢ` be a
Levi-Civita connection of `g_s` for each `s`. Write `h = ∂ₛ g_s` for the parameter derivative at
`s = t`, a symmetric field of bilinear forms. This file proves that for a vector field `Y` which is
differentiable at `x`, the curve `s ↦ ∇ˢ_v Y` in `T_x M` is differentiable at `t`, and that its
derivative `(∂ₜ∇)_v Y` satisfies the **first variation formula**

`2 g_t((∂ₜ∇)_v Y, w) = (∇ᵗ_v h)(Y, w) + (∇ᵗ_Y h)(v, w) - (∇ᵗ_w h)(v, Y)`,

where `∇ᵗh` is the covariant derivative `CovariantDerivative.derivBilinearTensor` of `h`. In index
notation this is the classical variation `∂ₜΓ^k_ij = ½ g^kl (∇_i h_jl + ∇_j h_il - ∇_l h_ij)` of the
Christoffel symbols. A family of metrics over a parameter manifold is varied along a parameter curve
by applying these results to the restricted family.

The proof differentiates the Koszul formula `2 g_s(∇ˢ_X Y, Z) = K_{g_s}(X, Y, Z)` in `s`. The
parameter derivative of the Koszul expression is the Koszul expression of `h`
(`TauCeti.Manifold.hasDerivAt_koszulBilinear`); this rests on commuting the parameter derivative
with the differentials of the pairings, `TauCeti.Manifold.hasDerivAt_mvfderiv_apply`.
Differentiability of `s ↦ ∇ˢ_v Y` comes from writing it as `g_s⁻¹` applied to half the Koszul
covector, and the identity
`TauCeti.Manifold.koszulBilinear_sub_two_mul_apply_eq_derivBilinearTensor` turns
`K_h(v, Y, w) - 2 h(∇ᵗ_v Y, w)` into the right-hand side. No positivity is used. Since the
difference `∇ˢ - ∇ᵗ` is tensorial, `s ↦ ∇ˢ_v Y` differs by a constant from the same curve for any
smooth extension of `Y x`, so only differentiability of `Y` at `x` is needed.

## Main results

* `TauCeti.Manifold.contMDiffAt_uncurry_apply_apply`: pairing two `C^n` vector fields with a jointly
  `C^n` family of fields of bilinear forms gives a jointly `C^n` family of functions.
* `TauCeti.Manifold.hasDerivAt_koszulBilinear`: the parameter derivative of the Koszul expression
  of a jointly `C²` family of fields of bilinear forms is the Koszul expression of its derivative.
* `TauCeti.Manifold.contMDiffAt_of_hasDerivAt_family`: the parameter derivative of a jointly `C^n`
  family of fields of bilinear forms is a `C^m` field for `m + 1 ≤ n`.
* `TauCeti.Manifold.differentiableAt_covariantDerivative_apply_of_isLeviCivitaConnection`: a
  family of Levi-Civita connections of a jointly `C²` family of nondegenerate metrics varies
  differentiably.
* `TauCeti.Manifold.two_mul_apply_deriv_eq_derivBilinearTensor_of_isLeviCivitaConnection`: the
  first variation formula for the Levi-Civita connection.

## References

* A. L. Besse, *Einstein Manifolds*, Springer (1987), Section 1.K, Theorem 1.174.
* B. Chow and D. Knopf, *The Ricci Flow: An Introduction*, AMS (2004), Chapter 3, Lemma 3.2.
* B. O'Neill, *Semi-Riemannian Geometry with Applications to Relativity*, Academic Press, 1983,
  Ch. 3, Thm. 11: the Koszul formula for nondegenerate metrics.
-/

public section

noncomputable section

open Bundle FiberBundle Filter VectorField
open scoped ContDiff Manifold Topology

namespace TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {b : ℝ → (x : M) → TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ}
  {h : (x : M) → TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ} {t : ℝ} {x : M}

/-! ### Families of fields of bilinear forms -/

variable [IsManifold I ∞ M]

/-- Pairing two `C^n` vector fields with a jointly `C^n` family of fields of bilinear forms gives
a jointly `C^n` family of functions. -/
theorem contMDiffAt_uncurry_apply_apply {n : WithTop ℕ∞}
    (hb : ContMDiffAt (𝓘(ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) n
      (fun q : ℝ × M ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun y : M ↦ TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ) q.2 (b q.1 q.2)) (t, x))
    {V W : Π x : M, TangentSpace I x} (hV : CMDiffAt n (T% V) x) (hW : CMDiffAt n (T% W) x) :
    ContMDiffAt (𝓘(ℝ).prod I) 𝓘(ℝ) n (Function.uncurry fun s y ↦ b s y (V y) (W y)) (t, x) := by
  have hV' : ContMDiffAt (𝓘(ℝ).prod I) (I.prod 𝓘(ℝ, E)) n
      (fun q : ℝ × M ↦ TotalSpace.mk' E q.2 (V q.2)) (t, x) := hV.comp (t, x) contMDiffAt_snd
  have hW' : ContMDiffAt (𝓘(ℝ).prod I) (I.prod 𝓘(ℝ, E)) n
      (fun q : ℝ × M ↦ TotalSpace.mk' E q.2 (W q.2)) (t, x) := hW.comp (t, x) contMDiffAt_snd
  have h := ContMDiffAt.clm_bundle_apply₂ (F₃ := ℝ) (E₃ := fun _ : M ↦ ℝ) hb hV' hW'
  simpa [Function.uncurry_def] using (contMDiffAt_totalSpace.mp h).2

/-- The parameter curve `s ↦ b s x u w` of a family of fields of bilinear forms, jointly `C¹` at
`(t, x)`, is differentiable at `t`. -/
theorem differentiableAt_apply_apply_of_contMDiffAt {n : WithTop ℕ∞} (hn : 1 ≤ n)
    (hb : ContMDiffAt (𝓘(ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) n
      (fun q : ℝ × M ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun y : M ↦ TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ) q.2 (b q.1 q.2))
      (t, x))
    (u w : TangentSpace I x) : DifferentiableAt ℝ (fun s ↦ b s x u w) t := by
  have hpair := contMDiffAt_uncurry_apply_apply hb (contMDiffAt_extend I E u)
    (contMDiffAt_extend I E w)
  have hcurve := ((hpair.of_le hn).comp t (contMDiffAt_id.prodMk contMDiffAt_const)
    |>.mdifferentiableAt one_ne_zero).differentiableAt
  simpa [Function.uncurry_def, Function.comp_def] using hcurve

/-- For a family of fields of bilinear forms, jointly `C²` at `(t, x)`, and vector fields `V`, `W`
that are `C²` at `x`, the parameter derivative of the differential at `x` of the pairing
`y ↦ b_s(V, W)` is the differential of the parameter derivative of the pairing. -/
private theorem hasDerivAt_mvfderiv_apply_apply
    (hb : ContMDiffAt (𝓘(ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) 2
      (fun q : ℝ × M ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun y : M ↦ TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ) q.2 (b q.1 q.2))
      (t, x))
    {V W : Π x : M, TangentSpace I x} (hV : CMDiffAt 2 (T% V) x) (hW : CMDiffAt 2 (T% W) x)
    (u : TangentSpace I x) :
    HasDerivAt (fun s ↦ mvfderiv I (fun y ↦ b s y (V y) (W y)) x u)
      (mvfderiv I (fun y ↦ deriv (fun s ↦ b s y (V y) (W y)) t) x u) t := by
  refine hasDerivAt_mvfderiv_apply ?_ u
  rw [minSmoothness_of_isRCLikeNormedField]
  exact contMDiffAt_uncurry_apply_apply hb hV hW

/-- The Koszul expression `K_{b_s}(X, Y, Z)` at `x` of a family of fields of bilinear forms,
jointly `C²` at `(t, x)`, is differentiable in the parameter at `t`, for vector fields `X`, `Y`, `Z`
that are `C²` at `x`. -/
theorem differentiableAt_koszulBilinear
    (hb : ContMDiffAt (𝓘(ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) 2
      (fun q : ℝ × M ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun y : M ↦ TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ) q.2 (b q.1 q.2))
      (t, x))
    {X Y Z : Π x : M, TangentSpace I x} (hX : CMDiffAt 2 (T% X) x) (hY : CMDiffAt 2 (T% Y) x)
    (hZ : CMDiffAt 2 (T% Z) x) :
    DifferentiableAt ℝ (fun s ↦ koszulBilinear I (b s) X Y Z x) t := by
  have hd {V W : Π x : M, TangentSpace I x} (U : Π x : M, TangentSpace I x)
      (hV : CMDiffAt 2 (T% V) x) (hW : CMDiffAt 2 (T% W) x) :
      DifferentiableAt ℝ (fun s ↦ mvfderiv I (fun y ↦ b s y (V y) (W y)) x (U x)) t :=
    (hasDerivAt_mvfderiv_apply_apply hb hV hW (U x)).differentiableAt
  have hp (u w : TangentSpace I x) :=
    differentiableAt_apply_apply_of_contMDiffAt (by norm_num) hb u w
  simp only [koszulBilinear_apply]
  exact ((((hd X hY hZ).add (hd Y hZ hX)).sub (hd Z hX hY)).add (hp _ _)).sub (hp _ _) |>.sub
    (hp _ _)

/-- **Variation of the Koszul expression.** Let `b_s` be a family of fields of bilinear forms on
`TM`, jointly `C²` in `(s, y)` at `(t, x)`, with parameter derivative `h = ∂ₛ b` at `s = t` near
`x`. Then for vector fields `X`, `Y`, `Z` that are `C²` at `x`, the parameter derivative of the
Koszul expression `K_{b_s}(X, Y, Z)` at `x` is the Koszul expression `K_h(X, Y, Z)` of `h`. -/
theorem hasDerivAt_koszulBilinear
    (hb : ContMDiffAt (𝓘(ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) 2
      (fun q : ℝ × M ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun y : M ↦ TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ) q.2 (b q.1 q.2)) (t, x))
    (hh : ∀ᶠ y in 𝓝 x, ∀ v w, HasDerivAt (fun s ↦ b s y v w) (h y v w) t)
    {X Y Z : Π x : M, TangentSpace I x} (hX : CMDiffAt 2 (T% X) x) (hY : CMDiffAt 2 (T% Y) x)
    (hZ : CMDiffAt 2 (T% Z) x) :
    HasDerivAt (fun s ↦ koszulBilinear I (b s) X Y Z x) (koszulBilinear I h X Y Z x) t := by
  -- The derivative terms: commute the parameter derivative with the differential.
  have hd {V W : Π x : M, TangentSpace I x} (U : Π x : M, TangentSpace I x)
      (hV : CMDiffAt 2 (T% V) x) (hW : CMDiffAt 2 (T% W) x) :
      HasDerivAt (fun s ↦ mvfderiv I (fun y ↦ b s y (V y) (W y)) x (U x))
        (mvfderiv I (fun y ↦ h y (V y) (W y)) x (U x)) t := by
    have hderiv := hasDerivAt_mvfderiv_apply_apply hb hV hW (U x)
    have heq : (fun y ↦ deriv (fun s ↦ b s y (V y) (W y)) t) =ᶠ[𝓝 x]
        fun y ↦ h y (V y) (W y) :=
      hh.mono fun y hy ↦ (hy (V y) (W y)).deriv
    rwa [heq.mvfderiv_eq] at hderiv
  -- The bracket terms: the parameter derivative of the pairing at `x`.
  have hp (u w : TangentSpace I x) : HasDerivAt (fun s ↦ b s x u w) (h x u w) t :=
    hh.self_of_nhds u w
  simp only [koszulBilinear_apply]
  exact ((((hd X hY hZ).add (hd Y hZ hX)).sub (hd Z hX hY)).add (hp _ _)).sub (hp _ _) |>.sub
    (hp _ _)

section FiniteDimensional

variable [FiniteDimensional ℝ E]

/-- **Regularity of the parameter derivative of a family of bilinear forms.** Let `b_s` be a family
of fields of bilinear forms on `TM`, jointly `C^n` in `(s, y)` at `(t, x)`, and let `h` be its
parameter derivative at `s = t` near `x`. Then `h` is a `C^m` field of bilinear forms at `x`
whenever `m + 1 ≤ n`. -/
theorem contMDiffAt_of_hasDerivAt_family {m n : WithTop ℕ∞}
    (hb : ContMDiffAt (𝓘(ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) n
      (fun q : ℝ × M ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun y : M ↦ TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ) q.2 (b q.1 q.2))
      (t, x))
    (hmn : m + 1 ≤ n) (hh : ∀ᶠ y in 𝓝 x, ∀ v w, HasDerivAt (fun s ↦ b s y v w) (h y v w) t) :
    ContMDiffAt I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) m
      (fun y ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun y : M ↦ TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ) y (h y)) x := by
  rw [contMDiffAt_hom_bundle] at hb ⊢
  refine ⟨contMDiffAt_id, ?_⟩
  -- `B s y` is `b s y` read in the tangent trivialization at `x`.
  set B : ℝ → M → E →L[ℝ] E →L[ℝ] ℝ := fun s y ↦ ContinuousLinearMap.inCoordinates E
    (TangentSpace I) (E →L[ℝ] ℝ) (fun z : M ↦ TangentSpace I z →L[ℝ] ℝ) x y x y (b s y)
  have hreg := contMDiffAt_deriv_of_contMDiffAt_uncurry (F := B) (t := t) (x := x) hb.2 hmn
  refine hreg.congr_of_eventuallyEq ?_
  filter_upwards [hh, (chartAt H x).open_source.mem_nhds (mem_chart_source H x)] with y hy hyx
  have key (φ : TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ) (a c : E) :
      ContinuousLinearMap.inCoordinates E (TangentSpace I) (E →L[ℝ] ℝ)
        (fun z : M ↦ TangentSpace I z →L[ℝ] ℝ) x y x y φ a c =
        φ ((trivializationAt E (TangentSpace I) x).symm y a)
          ((trivializationAt E (TangentSpace I) x).symm y c) := by
    rw [inCoordinates_apply_eq₂ (F₃ := ℝ) (E₃ := fun _ : M ↦ ℝ)
      (by simpa using hyx) (by simpa using hyx) (by simp)]
    simp
  -- Each evaluation of `B · y` is a parameter curve of `b` at `y`, with derivative given by `h`.
  have hcurve (a c : E) : HasDerivAt (fun s ↦ B s y a c)
      (h y ((trivializationAt E (TangentSpace I) x).symm y a)
        ((trivializationAt E (TangentSpace I) x).symm y c)) t := by
    simpa only [B, key] using hy _ _
  have hD := (differentiableAt_clm_apply.mpr fun a ↦
    differentiableAt_clm_apply.mpr fun c ↦ (hcurve a c).differentiableAt).hasDerivAt
  ext a c
  rw [key]
  exact (hcurve a c).unique (hasDerivAt_clm_apply₂.mp hD a c)

/-- The parameter derivative `h` of a family of fields of bilinear forms, jointly `C²` at `(t, x)`,
pairs vector fields differentiable at `x` to a function differentiable at `x`. -/
private theorem mdifferentiableAt_apply_of_hasDerivAt_family
    (hb : ContMDiffAt (𝓘(ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) 2
      (fun q : ℝ × M ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun y : M ↦ TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ) q.2 (b q.1 q.2))
      (t, x))
    (hh : ∀ᶠ y in 𝓝 x, ∀ v w, HasDerivAt (fun s ↦ b s y v w) (h y v w) t) :
    ∀ ⦃V W : Π x : M, TangentSpace I x⦄, MDiffAt (T% V) x → MDiffAt (T% W) x →
      MDiffAt (fun y ↦ h y (V y) (W y)) x := fun V W hV hW ↦ by
  have hreg := (contMDiffAt_of_hasDerivAt_family (m := 1) hb (by norm_num) hh).mdifferentiableAt
    one_ne_zero
  simpa [mdifferentiableAt_section] using hreg.clm_bundle_apply₂ hV hW

/-! ### Families of Levi-Civita connections -/

variable {g : ℝ → ContMDiffNondegenerateMetric (I := I) (M := M)}
  {cov : ℝ → CovariantDerivative I E (fun x : M ↦ TangentSpace I x)}
  {Y : Π x : M, TangentSpace I x}

/-- In a family of Levi-Civita connections of a family of nondegenerate metrics, the pairing
`2 g_s(∇ˢ_v Y, w)` is the Koszul expression of `g_s` on extensions of `v` and `w`. -/
private theorem two_mul_apply_eq_koszulBilinear_extend
    (hcov : ∀ s, (g s).IsLeviCivitaConnection (cov s)) (hY : MDiffAt (T% Y) x)
    (s : ℝ) (v w : TangentSpace I x) :
    2 * g s x (cov s Y x v) w = koszulBilinear I (g s) (extend E v) Y (extend E w) x := by
  have h := (hcov s).two_apply_eq_koszul (mdifferentiableAt_extend I E v) hY
    (mdifferentiableAt_extend I E w)
  rw [ContMDiffNondegenerateMetric.koszul_apply, ← koszulBilinear_apply] at h
  simpa using h

/-- The curve `s ↦ ∇ˢ_v Y` differs by a constant from the curve `s ↦ ∇ˢ_v Y₀` for the extension
`Y₀` of `Y x`: the difference `∇ˢ - ∇ᵗ` is tensorial, so `∇ˢ_v Y - ∇ᵗ_v Y` depends on `Y` only
through `Y x`. -/
private theorem apply_eq_apply_extend_add (hY : MDiffAt (T% Y) x) (s : ℝ) (v : TangentSpace I x) :
    cov s Y x v = cov s (extend E (Y x)) x v + (cov t Y x v - cov t (extend E (Y x)) x v) := by
  have hd {Z : Π x : M, TangentSpace I x} (hZ : MDiffAt (T% Z) x) :=
    IsCovariantDerivativeOn.difference_apply (cov s).isCovariantDerivativeOnUniv
      (cov t).isCovariantDerivativeOnUniv (Set.mem_univ x) hZ
  have h := (hd hY).symm.trans (extend_apply_self (F := E) (Y x) ▸ hd
    (mdifferentiableAt_extend I E (Y x)))
  have h' := congr($h v)
  simp only [sub_apply] at h'
  rw [← sub_add_cancel (cov s Y x v) (cov t Y x v), h']
  abel

/-- Levi-Civita connections vary differentiably with the metric, for vector fields `C²` at `x`. -/
private theorem differentiableAt_covariantDerivative_apply_of_contMDiffAt
    (hcov : ∀ s, (g s).IsLeviCivitaConnection (cov s))
    (hg : ContMDiffAt (𝓘(ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) 2
      (fun q : ℝ × M ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun y : M ↦ TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ) q.2 (g q.1 q.2))
      (t, x))
    (hY : CMDiffAt 2 (T% Y) x) (v : TangentSpace I x) :
    DifferentiableAt ℝ (fun s ↦ cov s Y x v) t := by
  -- The metrics at `x`, as a curve of bilinear forms on the model space.
  set G : ℝ → E →L[ℝ] E →L[ℝ] ℝ := fun s ↦ g s x
  have hG : DifferentiableAt ℝ G t := differentiableAt_clm_apply₂.mpr
    (differentiableAt_apply_apply_of_contMDiffAt (b := fun s ↦ g s) (by norm_num) hg)
  -- The covectors `g_s(∇ˢ_v Y, ·)`, which are half the Koszul expressions.
  have hφ : DifferentiableAt ℝ (fun s ↦ G s (cov s Y x v)) t := by
    refine differentiableAt_clm_apply.mpr fun c ↦ ?_
    have hK := (differentiableAt_koszulBilinear (b := fun s ↦ g s) hg (contMDiffAt_extend I E v) hY
      (contMDiffAt_extend I E c)).const_mul (1 / 2 : ℝ)
    refine hK.congr_of_eventuallyEq (Eventually.of_forall fun s ↦ ?_)
    have := two_mul_apply_eq_koszulBilinear_extend hcov (hY.mdifferentiableAt two_ne_zero) s v c
    dsimp only
    rw [← this, one_div, inv_mul_cancel_left₀ two_ne_zero]
    -- `G s` is `g s x` with the tangent space at `x` read as the model space.
    rfl
  have hinv := (DifferentiableAt.clm_inverse_of_completeSpace hG
    ((g t).isInvertible x)).clm_apply hφ
  refine hinv.congr_of_eventuallyEq (Eventually.of_forall fun s ↦ ?_)
  exact (((g s).isInvertible x).inverse_apply_self _).symm

/-- The first variation of the Levi-Civita connection, for vector fields `C²` at `x`. -/
private theorem two_mul_apply_deriv_eq_of_contMDiffAt
    (hcov : ∀ s, (g s).IsLeviCivitaConnection (cov s))
    (hg : ContMDiffAt (𝓘(ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) 2
      (fun q : ℝ × M ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun y : M ↦ TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ) q.2 (g q.1 q.2))
      (t, x))
    (hh : ∀ y v w, HasDerivAt (fun s ↦ g s y v w) (h y v w) t)
    (hY : CMDiffAt 2 (T% Y) x) (v w : TangentSpace I x) :
    2 * g t x (deriv (fun s ↦ cov s Y x v) t) w =
      (cov t).derivBilinearTensor h x (Y x) w v + (cov t).derivBilinearTensor h x v w (Y x) -
        (cov t).derivBilinearTensor h x v (Y x) w := by
  -- The curve `s ↦ ∇ˢ_v Y` and the metrics at `x`, read in the model space.
  set u : ℝ → E := fun s ↦ cov s Y x v
  have hu' : DifferentiableAt ℝ u t :=
    differentiableAt_covariantDerivative_apply_of_contMDiffAt hcov hg hY v
  have hu : HasDerivAt u (deriv u t) t := hu'.hasDerivAt
  set G : ℝ → E →L[ℝ] E →L[ℝ] ℝ := fun s ↦ g s x
  have hG : HasDerivAt G (h x) t := hasDerivAt_clm_apply₂.mpr (hh x)
  -- Differentiate `2 g_s(∇ˢ_v Y, w)` directly ...
  have hleft : HasDerivAt (fun s ↦ 2 * g s x (cov s Y x v) w)
      (2 * (h x (cov t Y x v) w + g t x (deriv u t) w)) t := by
    have := ((hG.clm_apply hu).clm_apply
      (hasDerivAt_const (x := t) (c := tangentSpaceCastModel I x w))).const_mul 2
    simp only [map_zero, add_zero, add_apply] at this
    -- `G s`, `u s` and `tangentSpaceCastModel I x w` are `g s x`, `∇ˢ_v Y` and `w`.
    exact this
  -- ... and as the Koszul expression of `g_s`, whose derivative is that of `h`.
  have hright := hasDerivAt_koszulBilinear (b := fun s ↦ g s) hg (Eventually.of_forall hh)
    (contMDiffAt_extend I E v) hY (contMDiffAt_extend I E w)
  have hK := hleft.unique (hright.congr_of_eventuallyEq (Eventually.of_forall fun s ↦
    two_mul_apply_eq_koszulBilinear_extend hcov (hY.mdifferentiableAt two_ne_zero) s v w))
  -- Rewrite the Koszul expression of the symmetric field `h` along the torsion-free `∇ᵗ`.
  have hsymm (y : M) (a c : TangentSpace I y) : h y a c = h y c a :=
    (hh y a c).unique ((hh y c a).congr_of_eventuallyEq
      (Eventually.of_forall fun s ↦ (g s).apply_comm y a c))
  have hid := koszulBilinear_sub_two_mul_apply_eq_derivBilinearTensor (hcov t).torsion hsymm
    (mdifferentiableAt_apply_of_hasDerivAt_family (b := fun s ↦ g s) hg (Eventually.of_forall hh))
    (mdifferentiableAt_extend I E v) (hY.mdifferentiableAt two_ne_zero)
    (mdifferentiableAt_extend I E w)
  simp only [extend_apply_self] at hid
  have key : 2 * g t x (deriv u t) w =
      (cov t).derivBilinearTensor h x (Y x) w v + (cov t).derivBilinearTensor h x v w (Y x) -
        (cov t).derivBilinearTensor h x v (Y x) w := by
    linarith
  -- The derivative of `u` is that of `s ↦ ∇ˢ_v Y`, with the tangent space read as `E`.
  exact key

/-- For a vector field `Y` differentiable at `x`, the curve `s ↦ ∇ˢ_v Y` has the same derivative at
`t` as the curve `s ↦ ∇ˢ_v Y₀` for the extension `Y₀` of `Y x`. -/
private theorem hasDerivAt_apply_of_extend
    (hcov : ∀ s, (g s).IsLeviCivitaConnection (cov s))
    (hg : ContMDiffAt (𝓘(ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) 2
      (fun q : ℝ × M ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun y : M ↦ TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ) q.2 (g q.1 q.2))
      (t, x))
    (hY : MDiffAt (T% Y) x) (v : TangentSpace I x) :
    HasDerivAt (fun s ↦ cov s Y x v) (deriv (fun s ↦ cov s (extend E (Y x)) x v) t) t := by
  -- `s ↦ ∇ˢ_v Y` and `s ↦ ∇ˢ_v Y₀` for the extension `Y₀` of `Y x` differ by a constant.
  set u : ℝ → E := fun s ↦ cov s (extend E (Y x)) x v
  set c : E := cov t Y x v - cov t (extend E (Y x)) x v
  have hu : DifferentiableAt ℝ u t := differentiableAt_covariantDerivative_apply_of_contMDiffAt
    hcov hg (contMDiffAt_extend I E (Y x)) v
  -- Elaborated without the goal as expected type, so that `u` fixes the codomain as `E`.
  have h := (hu.hasDerivAt.add_const c).congr_of_eventuallyEq
    (Eventually.of_forall fun s ↦ apply_eq_apply_extend_add hY s v)
  exact h

/-- **Levi-Civita connections vary differentiably with the metric.** Let `g_s` be a family of
smooth nondegenerate metrics, jointly `C²` in `(s, y)` at `(t, x)`, and let `∇ˢ` be a Levi-Civita
connection of `g_s` for every `s`. Then for every vector field `Y` which is differentiable at `x`
and every `v ∈ T_x M`, the curve `s ↦ ∇ˢ_v Y` in `T_x M` is differentiable at `t`. -/
theorem differentiableAt_covariantDerivative_apply_of_isLeviCivitaConnection
    (hcov : ∀ s, (g s).IsLeviCivitaConnection (cov s))
    (hg : ContMDiffAt (𝓘(ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) 2
      (fun q : ℝ × M ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun y : M ↦ TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ) q.2 (g q.1 q.2))
      (t, x))
    (hY : MDiffAt (T% Y) x) (v : TangentSpace I x) :
    DifferentiableAt ℝ (fun s ↦ cov s Y x v) t :=
  -- The tangent space at `x` is read as the normed space `E`.
  HasDerivAt.differentiableAt (F := E) (hasDerivAt_apply_of_extend hcov hg hY v)

/-- **The first variation of the Levi-Civita connection.** Let `g_s` be a family of smooth
nondegenerate metrics, jointly `C²` in `(s, y)` at `(t, x)`, with parameter derivative
`h = ∂ₛ g_s` at `s = t`, and let `∇ˢ` be a Levi-Civita connection of `g_s` for every `s`. Then for
every vector field `Y` which is differentiable at `x` and all `v, w ∈ T_x M`,

`2 g_t((∂ₜ∇)_v Y, w) = (∇ᵗ_v h)(Y, w) + (∇ᵗ_Y h)(v, w) - (∇ᵗ_w h)(v, Y)`,

where `(∂ₜ∇)_v Y` is the derivative at `t` of `s ↦ ∇ˢ_v Y` and `∇ᵗh` is the covariant derivative
`CovariantDerivative.derivBilinearTensor` of `h` along `∇ᵗ`. -/
theorem two_mul_apply_deriv_eq_derivBilinearTensor_of_isLeviCivitaConnection
    (hcov : ∀ s, (g s).IsLeviCivitaConnection (cov s))
    (hg : ContMDiffAt (𝓘(ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) 2
      (fun q : ℝ × M ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun y : M ↦ TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ) q.2 (g q.1 q.2))
      (t, x))
    (hh : ∀ y v w, HasDerivAt (fun s ↦ g s y v w) (h y v w) t)
    (hY : MDiffAt (T% Y) x) (v w : TangentSpace I x) :
    2 * g t x (deriv (fun s ↦ cov s Y x v) t) w =
      (cov t).derivBilinearTensor h x (Y x) w v + (cov t).derivBilinearTensor h x v w (Y x) -
        (cov t).derivBilinearTensor h x v (Y x) w := by
  have hderiv : deriv (fun s ↦ cov s Y x v) t = deriv (fun s ↦ cov s (extend E (Y x)) x v) t :=
    HasDerivAt.deriv (F := E) (hasDerivAt_apply_of_extend hcov hg hY v)
  rw [hderiv]
  simpa only [extend_apply_self] using
    two_mul_apply_deriv_eq_of_contMDiffAt hcov hg hh (contMDiffAt_extend I E (Y x)) v w

end FiniteDimensional

end TauCeti.Manifold
