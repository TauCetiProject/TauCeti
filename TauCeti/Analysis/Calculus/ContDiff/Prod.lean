/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import TauCeti.Analysis.Calculus.FDeriv.Prod

/-!
# Smoothness of slices of a map on a product

If a map `H` on a product is smooth near every point of `s ×ˢ I`, then each of its slices
`H (·, t)` with `t ∈ I` is smooth on `s` (`TauCeti.contDiffOn_comp_prodMk_left`). For instance,
the time slices of a homotopy smooth near `s × [0, 1]` are smooth on `s`.

For a family `F : P × E → X` smooth at `(p, x)`, the spatial differential
`(q, y) ↦ fderiv (F (q, ·)) y` is smooth jointly (`ContDiffAt.fderiv_slice`), smoothness persists
along a graph over the parameter (`ContDiffAt.eventually_contDiffAt_graph`), and the vertical part
of the derivative of a `C¹` map is continuous along a continuous graph
(`ContDiffAt.continuousAt_fderiv_comp_inr`).
The partial derivative in the second variable, applied to a fixed vector, is then `C^m` jointly
whenever `m + 1 ≤ n` (`ContDiffAt.fderiv_snd_apply`). If `f` is `C^(n+2)` and a `C^(n+1)` graph
`ψ` is critical for `f` in the second variable, the critical value `q ↦ f (q, ψ q)` is
`C^(n+2)` (`ContDiffAt.comp_graph_of_fderiv_right_eq_zero`).

For a scalar factor, `ContDiffAt.contDiffAt_deriv_snd` and
`ContDiffAt.contDiffAt_deriv_fst` give joint `C^m` regularity of the corresponding partial
derivative of a `C^n` map, for `m + 1 ≤ n`.

If a separated sum `φ ∘ Prod.fst + ψ ∘ Prod.snd` is `Cⁿ` at `(a, b)`, then each summand is `Cⁿ` at
its point (`ContDiffAt.of_comp_fst_add_comp_snd_left` and
`ContDiffAt.of_comp_fst_add_comp_snd_right`).

A compactly supported `C³` function on `E × ℝ` has compactly supported spatial first and second
derivative fields and a time derivative field of lower smoothness, computing its slice derivatives
at every point (`ContDiff.exists_derivative_fields_of_hasCompactSupport`).
-/

public section

namespace TauCeti

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  {n : WithTop ℕ∞} {s : Set E} {I : Set G} {H : E × G → F}

/-- **Slices of a map smooth near `s ×ˢ I` are smooth**: for `t ∈ I`, the slice `H (·, t)` is
smooth on `s`. -/
theorem contDiffOn_comp_prodMk_left (hH : ∀ p ∈ s ×ˢ I, ContDiffAt 𝕜 n H p) {t : G}
    (ht : t ∈ I) : ContDiffOn 𝕜 n (fun x ↦ H (x, t)) s :=
  fun x hx ↦ ((hH (x, t) ⟨hx, ht⟩).comp x (contDiff_prodMk_left t).contDiffAt).contDiffWithinAt

end TauCeti

namespace ContDiffAt

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {P : Type*} [NormedAddCommGroup P] [NormedSpace 𝕜 P]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X] {p : P} {x : E}

/-- The spatial differential of a `C^n` family is `C^m` jointly in the parameter and the spatial
variable, for `m + 1 ≤ n`. -/
theorem fderiv_slice {n m : WithTop ℕ∞} {F : P × E → X}
    (hF : ContDiffAt 𝕜 n F (p, x)) (hmn : m + 1 ≤ n) :
    ContDiffAt 𝕜 m (fun q : P × E ↦ fderiv 𝕜 (fun y ↦ F (q.1, y)) q.2) (p, x) := by
  apply ContDiffAt.fderiv (n := n) (m := m) (x₀ := (p, x))
    (f := fun q : P × E ↦ fun y : E ↦ F (q.1, y)) (g := fun q : P × E ↦ q.2)
  · exact hF.comp ((p, x), x) (by fun_prop)
  · fun_prop
  · exact hmn

/-- For a `C^n` map on a product with a scalar second factor, the partial derivative in the
second variable is jointly `C^m` for `m + 1 ≤ n`. -/
theorem contDiffAt_deriv_snd {m n : WithTop ℕ∞} {g : E × 𝕜 → X} {z : E × 𝕜}
    (hg : ContDiffAt 𝕜 n g z) (hmn : m + 1 ≤ n) :
    ContDiffAt 𝕜 m (fun w : E × 𝕜 ↦ deriv (fun r ↦ g (w.1, r)) w.2) z := by
  exact ((hg.fderiv_slice hmn).clm_apply (contDiffAt_const (c := (1 : 𝕜))))
    |>.congr_of_eventuallyEq (Filter.Eventually.of_forall fun _ ↦ fderiv_apply_one_eq_deriv.symm)

/-- For a `C^n` map on a product with a scalar first factor, the partial derivative in the
first variable is jointly `C^m` for `m + 1 ≤ n`. -/
theorem contDiffAt_deriv_fst {m n : WithTop ℕ∞} {g : 𝕜 × E → X} {z : 𝕜 × E}
    (hg : ContDiffAt 𝕜 n g z) (hmn : m + 1 ≤ n) :
    ContDiffAt 𝕜 m (fun w : 𝕜 × E ↦ deriv (fun r ↦ g (r, w.2)) w.1) z := by
  have hswap : ContDiffAt 𝕜 n (fun w : E × 𝕜 ↦ g (w.2, w.1)) (z.2, z.1) :=
    hg.comp (z.2, z.1) (contDiffAt_snd.prodMk contDiffAt_fst)
  exact (hswap.contDiffAt_deriv_snd hmn).comp z (contDiffAt_snd.prodMk contDiffAt_fst)

/-- A function that is `C^n` at `(p, ψ p)` is `C^n` at `(q, ψ q)` for `q` near `p`, when `ψ` is
continuous at `p`. -/
theorem eventually_contDiffAt_graph {f : P × E → X} {ψ : P → E} {n : ℕ}
    (hf : ContDiffAt 𝕜 n f (p, ψ p)) (hψ : ContinuousAt ψ p) :
    ∀ᶠ q in nhds p, ContDiffAt 𝕜 n f (q, ψ q) :=
  (continuousAt_id.prodMk hψ).eventually (hf.eventually (by norm_num))

/-- The vertical part of the derivative of a `C¹` map is continuous along a continuous graph. -/
theorem continuousAt_fderiv_comp_inr {G : P × E → X} {ψ : P → E}
    (hG : ContDiffAt 𝕜 1 G (p, ψ p)) (hψ : ContinuousAt ψ p) :
    ContinuousAt (fun q ↦ (fderiv 𝕜 G (q, ψ q)).comp (ContinuousLinearMap.inr 𝕜 P E)) p :=
  ((hG.continuousAt_fderiv (by norm_num)).comp_of_eq
    (f := fun q ↦ (q, ψ q)) (continuousAt_id.prodMk hψ) rfl).clm_comp
    continuousAt_const

/-- The partial derivative in the second variable of a function of `(r.1, z)`, applied to a fixed
vector, is as differentiable in `r` as the function allows. -/
theorem fderiv_snd_apply {n m : WithTop ℕ∞} {f : P × E → X} {r : P × E}
    (hf : ContDiffAt 𝕜 n f r) (hmn : m + 1 ≤ n) (v : E) :
    ContDiffAt 𝕜 m (fun r : P × E ↦ fderiv 𝕜 (fun z ↦ f (r.1, z)) r.2 v) r :=
  (hf.fderiv_slice hmn).clm_apply contDiffAt_const

/-- **Envelope regularity.** If `f` is `C^(n+2)` at `(p, ψ p)`, `ψ` is `C^(n+1)` at `p`, and
the derivative of `f` in its second variable vanishes along the graph of `ψ` near `p`, then the
critical value `q ↦ f (q, ψ q)` is `C^(n+2)` at `p`, one order more than the chain rule gives:
its derivative is the first-variable derivative of `f` along the graph, which is `C^(n+1)`. -/
theorem comp_graph_of_fderiv_right_eq_zero {n : WithTop ℕ∞} {f : P × E → X} {ψ : P → E}
    (hf : ContDiffAt 𝕜 (n + 2) f (p, ψ p)) (hψ : ContDiffAt 𝕜 (n + 1) ψ p)
    (hcrit : ∀ᶠ q in nhds p, fderiv 𝕜 (fun y ↦ f (q, y)) (ψ q) = 0) :
    ContDiffAt 𝕜 (n + 2) (fun q ↦ f (q, ψ q)) p := by
  have hgraph : ContDiffAt 𝕜 (n + 1) (fun q ↦ (q, ψ q)) p := contDiffAt_id.prodMk hψ
  induction n using WithTop.recTopCoe with
  | top => exact hf.comp p hgraph
  | coe n =>
    induction n using ENat.recTopCoe with
    | top => exact hf.comp p hgraph
    | coe n =>
      have h₂ : ((n : ℕ∞) : WithTop ℕ∞) + 2 = ((n + 1 : ℕ) : WithTop ℕ∞) + 1 := by norm_cast
      rw [h₂] at hf ⊢
      let d : P → P →L[𝕜] X := fun q ↦
        fderiv 𝕜 f (q, ψ q) ∘L ContinuousLinearMap.inl 𝕜 P E
      have hd : ContDiffAt 𝕜 ((n + 1 : ℕ)) d p :=
        ((hf.fderiv_right (m := (n + 1 : ℕ)) le_rfl).comp p hgraph).clm_comp contDiffAt_const
      -- Along the graph the vertical derivative vanishes, leaving the horizontal derivative `d`.
      have hhas : ∀ᶠ q in nhds p, HasFDerivAt (fun q ↦ f (q, ψ q)) (d q) q := by
        have hf₁ : ContDiffAt 𝕜 1 f (p, ψ p) := hf.of_le le_add_self
        have hψ₁ : ContDiffAt 𝕜 1 ψ p := hψ.of_le (by simp)
        filter_upwards [hcrit, hgraph.continuousAt.eventually (hf₁.eventually (by simp)),
          hψ₁.eventually (by simp)] with q hq hfq hψq
        have hfq' := hfq.differentiableAt one_ne_zero
        have hψq' := hψq.differentiableAt one_ne_zero
        have hcomp : DifferentiableAt 𝕜 (fun q ↦ f (q, ψ q)) q :=
          hfq'.comp q (differentiableAt_id.prodMk hψq')
        convert hcomp.hasFDerivAt using 1
        rw [hfq'.hasFDerivAt.fderiv_comp_graph_eq_fderiv_slice_of_fderiv_right_eq_zero hψq' hq,
          TauCeti.fderiv_slice_left hfq']
      exact contDiffAt_succ_iff_hasFDerivAt.2 ⟨d, Filter.eventually_iff_exists_mem.1 hhas, hd⟩

/-- If a separated sum `φ ∘ Prod.fst + ψ ∘ Prod.snd` is `Cⁿ` at `(a, b)`, then `φ` is `Cⁿ` at `a`:
restrict to the slice `y = b` and subtract the constant `ψ b`. -/
theorem of_comp_fst_add_comp_snd_left {n : WithTop ℕ∞} {F : Type*} [NormedAddCommGroup F]
    [NormedSpace 𝕜 F] {φ : E → X} {ψ : F → X} {a : E} {b : F}
    (h : ContDiffAt 𝕜 n (φ ∘ Prod.fst + ψ ∘ Prod.snd) (a, b)) : ContDiffAt 𝕜 n φ a := by
  have hφ : ContDiffAt 𝕜 n (fun x ↦ φ x + ψ b) a := by
    simpa [Function.comp_def] using h.comp (f := fun x : E ↦ (x, b)) a (by fun_prop)
  simpa using hφ.sub (contDiffAt_const (c := ψ b))

/-- If a separated sum `φ ∘ Prod.fst + ψ ∘ Prod.snd` is `Cⁿ` at `(a, b)`, then `ψ` is `Cⁿ` at `b`:
restrict to the slice `x = a` and subtract the constant `φ a`. -/
theorem of_comp_fst_add_comp_snd_right {n : WithTop ℕ∞} {F : Type*} [NormedAddCommGroup F]
    [NormedSpace 𝕜 F] {φ : E → X} {ψ : F → X} {a : E} {b : F}
    (h : ContDiffAt 𝕜 n (φ ∘ Prod.fst + ψ ∘ Prod.snd) (a, b)) : ContDiffAt 𝕜 n ψ b := by
  have hψ : ContDiffAt 𝕜 n (fun y ↦ φ a + ψ y) b := by
    simpa [Function.comp_def] using h.comp (f := fun y : F ↦ (a, y)) b (by fun_prop)
  simpa using hψ.sub (contDiffAt_const (c := φ a))

end ContDiffAt

noncomputable section DerivativeFields

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

-- These shortcuts keep nested operator-space instance search shallow.
private local instance : NormedAddCommGroup (E →L[ℝ] F) := inferInstance
private local instance : NormedSpace ℝ (E →L[ℝ] F) := inferInstance
private local instance : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] F) := inferInstance
private local instance : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] F) := inferInstance

/-- The spatial first and second derivative fields and the time derivative field of a compactly
supported `C³` function on a product with a real second factor are compactly supported, of the
expected smoothness, and compute its slice derivatives at every point. -/
theorem ContDiff.exists_derivative_fields_of_hasCompactSupport {f : E × ℝ → F}
    (hf : ContDiff ℝ 3 f) (hs : HasCompactSupport f) :
    ∃ (fx : E × ℝ → E →L[ℝ] F) (fxx : E × ℝ → E →L[ℝ] E →L[ℝ] F) (ft : E × ℝ → F),
      ContDiff ℝ 2 fx ∧ HasCompactSupport fx ∧ ContDiff ℝ 1 fxx ∧ HasCompactSupport fxx ∧
      ContDiff ℝ 2 ft ∧ HasCompactSupport ft ∧
      (∀ p : E × ℝ, HasFDerivAt (fun y ↦ f (y, p.2)) (fx p) p.1) ∧
      (∀ p : E × ℝ, HasFDerivAt (fun y ↦ fx (y, p.2)) (fxx p) p.1) ∧
      (∀ p : E × ℝ, HasDerivAt (fun s : ℝ ↦ f (p.1, s)) (ft p) p.2) := by
  -- Restrict the ordinary derivatives to spatial directions and to the unit time direction.
  let ι : E →L[ℝ] E × ℝ := ContinuousLinearMap.inl ℝ E ℝ
  let R : (E × ℝ →L[ℝ] F) →L[ℝ] E →L[ℝ] F := ι.precomp F
  let S : (E × ℝ →L[ℝ] E →L[ℝ] F) →L[ℝ] E →L[ℝ] E →L[ℝ] F :=
    ι.precomp (E →L[ℝ] F)
  let fx : E × ℝ → E →L[ℝ] F := R ∘ fderiv ℝ f
  have hfx : ContDiff ℝ 2 fx :=
    (R.contDiff (n := 2)).comp (hf.fderiv_right (by norm_num))
  have hsfx : HasCompactSupport fx := (hs.fderiv ℝ).comp_left (map_zero R)
  let fxx : E × ℝ → E →L[ℝ] E →L[ℝ] F := S ∘ fderiv ℝ fx
  have hfxx : ContDiff ℝ 1 fxx :=
    (S.contDiff (n := 1)).comp (hfx.fderiv_right (by norm_num))
  have hsfxx : HasCompactSupport fxx :=
    (hsfx.fderiv ℝ).comp_left (map_zero S)
  let ft : E × ℝ → F := (ContinuousLinearMap.apply ℝ F ((0, 1) : E × ℝ)) ∘ fderiv ℝ f
  have hft : ContDiff ℝ 2 ft :=
    ((ContinuousLinearMap.apply ℝ F ((0, 1) : E × ℝ)).contDiff (n := 2)).comp
      (hf.fderiv_right (by norm_num))
  have hsft : HasCompactSupport ft :=
    (hs.fderiv ℝ).comp_left (map_zero (ContinuousLinearMap.apply ℝ F ((0, 1) : E × ℝ)))
  refine ⟨fx, fxx, ft, hfx, hsfx, hfxx, hsfxx, hft, hsft, fun p ↦ ?_, fun p ↦ ?_, fun p ↦ ?_⟩
  · simpa [fx, R, ι, Function.comp_def] using
      (hf.differentiable (by norm_num) p).hasFDerivAt_slice_fst
  · simpa [fxx, S, ι, Function.comp_def] using
      (hfx.differentiable (by norm_num) p).hasFDerivAt_slice_fst
  · simpa [ft, Function.comp_def] using
      ((hf.differentiable (by simp) _).hasFDerivAt.comp p.2
        ((hasFDerivAt_const p.1 p.2).prodMk (hasFDerivAt_id p.2))).hasDerivAt

end DerivativeFields
