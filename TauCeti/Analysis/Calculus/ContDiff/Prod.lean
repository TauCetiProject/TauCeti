/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import TauCeti.Analysis.Calculus.FDeriv.Prod

/-!
# Smoothness of slices of a map on a product

If a map `H` on a product is smooth near every point of `s ×ˢ I`, then each of its slices
`H (·, t)` with `t ∈ I` is smooth on `s` (`TauCeti.contDiffOn_comp_prodMk_left`). For instance,
the time slices of a homotopy smooth near `s × [0, 1]` are smooth on `s`. Likewise, a field
`J z x` that is smooth near the graph of a map `u` smooth on `s` gives a map `z ↦ J z (u z)`
smooth on `s` (`TauCeti.contDiffOn_comp_graph`). The slices `(x, y) ↦ H ((p, x), y)` of a `Cⁿ`
family `H` on `(P × E) × G` at a fixed parameter `p` are `Cⁿ`
(`TauCeti.contDiff_comp_prodMap_prodMk_right`), and so are the uncurried slices `uncurry (H p)`
of a curried family `(p, x, y) ↦ H p x y` that is `Cⁿ` on `P × E × G`
(`TauCeti.contDiff_uncurry_apply`). A map that the slices `f p` of a jointly `Cⁿ` family equal
eventually along a nontrivial filter is `Cⁿ`
(`TauCeti.contDiff_of_contDiff_uncurry_of_eventually_eq`).

A slice `f p` of a family `f : P → E → X` that is jointly `C^n` at `(p, x)` is `C^n` at `x`
(`ContDiffAt.uncurry_left`), and so is the slice `(x, y) ↦ H ((p, x), y)` of a family `H` on
`(P × E) × G` that is `C^n` at `((p, x), y)` (`ContDiffAt.comp_prodMap_prodMk_right`).

For a family `F : P × E → X` smooth at `(p, x)`, the spatial differential
`(q, y) ↦ fderiv (F (q, ·)) y` is smooth jointly (`ContDiffAt.fderiv_slice`), smoothness persists
along a graph over the parameter (`ContDiffAt.eventually_contDiffAt_graph`), and the vertical part
of the derivative of a `C¹` map is continuous along a continuous graph
(`ContDiffAt.continuousAt_fderiv_comp_inr`). Along two continuous graphs meeting at `p`, the
values of a family `C¹` there differ near `p` by at most a multiple of the distance between the
graphs (`ContDiffAt.exists_eventually_norm_sub_le`).
The partial derivative in the second variable, applied to a fixed vector, is then `C^m` jointly
whenever `m + 1 ≤ n` (`ContDiffAt.fderiv_snd_apply`).

For a scalar factor, `ContDiffAt.contDiffAt_deriv_snd` and
`ContDiffAt.contDiffAt_deriv_fst` give joint `C^m` regularity of the corresponding partial
derivative of a `C^n` map, for `m + 1 ≤ n`, and `ContDiffAt.contDiffAt_iterate_deriv_fst` gives
joint `C^m` regularity of the `k`-th partial derivative in the first variable, for `m + k ≤ n`.

If a separated sum `φ ∘ Prod.fst + ψ ∘ Prod.snd` is `Cⁿ` at `(a, b)`, then each summand is `Cⁿ` at
its point (`ContDiffAt.of_comp_fst_add_comp_snd_left` and
`ContDiffAt.of_comp_fst_add_comp_snd_right`). Subtracting a jointly `C^n` family of maps `g p`
from a jointly `C^n` family `f t` gives a family that is jointly `C^n` in `(t, p)` and the point
(`ContDiffAt.sub_uncurry_prod`).

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

/-- **Composition with a graph**: a field `J z x` that is `Cⁿ` near the graph of a map `u` which is
`Cⁿ` on `s` gives a map `z ↦ J z (u z)` that is `Cⁿ` on `s`. -/
theorem contDiffOn_comp_graph {J : E → G → F} {u : E → G}
    (hJ : ∀ z ∈ s, ContDiffAt 𝕜 n (fun p : E × G ↦ J p.1 p.2) (z, u z))
    (hu : ContDiffOn 𝕜 n u s) : ContDiffOn 𝕜 n (fun z ↦ J z (u z)) s :=
  fun z hz ↦ (hJ z hz).comp₂_contDiffWithinAt contDiffWithinAt_id (hu z hz)

/-- **Slices of a family at a fixed parameter**: if `H` is `Cⁿ` on `(P × E) × G`, then for every
`p : P` the slice `(x, y) ↦ H ((p, x), y)` is `Cⁿ` on `E × G`. -/
theorem contDiff_comp_prodMap_prodMk_right {P : Type*} [NormedAddCommGroup P] [NormedSpace 𝕜 P]
    {H : (P × E) × G → F} (hH : ContDiff 𝕜 n H) (p : P) :
    ContDiff 𝕜 n fun q : E × G ↦ H ((p, q.1), q.2) :=
  hH.comp ((contDiff_prodMk_right p).prodMap contDiff_id)

/-- **Uncurried slices of a curried family at a fixed parameter**: if `(p, x, y) ↦ H p x y` is `Cⁿ`
on `P × E × G`, then for every `p : P` the uncurried slice `uncurry (H p)` is `Cⁿ` on `E × G`. -/
theorem contDiff_uncurry_apply {P : Type*} [NormedAddCommGroup P] [NormedSpace 𝕜 P]
    {H : P → E → G → F} (hH : ContDiff 𝕜 n fun q : P × E × G ↦ H q.1 q.2.1 q.2.2) (p : P) :
    ContDiff 𝕜 n (Function.uncurry (H p)) := by
  -- The uncurried slice is the joint map composed with `q ↦ (p, q)`.
  have heq : Function.uncurry (H p) = (fun q : P × E × G ↦ H q.1 q.2.1 q.2.2) ∘ (p, ·) := by
    funext q
    simp only [Function.uncurry_def, Function.comp_apply]
  rw [heq]
  exact hH.comp (contDiff_prodMk_right p)

/-- **An eventual slice of a jointly smooth family is smooth**: if `(p, x) ↦ f p x` is `Cⁿ` and
`f p = g` for `p` eventually along a nontrivial filter, then `g` is `Cⁿ`. For instance, the end
Hamiltonian of a jointly `C²` family that is constant near `±∞` is `C²`. -/
theorem contDiff_of_contDiff_uncurry_of_eventually_eq {P : Type*} [NormedAddCommGroup P]
    [NormedSpace 𝕜 P] {f : P → E → F} {g : E → F} {l : Filter P} [l.NeBot]
    (hf : ContDiff 𝕜 n (Function.uncurry f)) (hl : ∀ᶠ p in l, f p = g) : ContDiff 𝕜 n g := by
  obtain ⟨p, rfl⟩ := hl.exists
  exact hf.comp (contDiff_prodMk_right p)

end TauCeti

namespace ContDiffAt

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {P : Type*} [NormedAddCommGroup P] [NormedSpace 𝕜 P]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X] {p : P} {x : E}

/-- A slice `f p` of a family that is jointly `C^n` at `(p, x)` is `C^n` at `x`. -/
theorem uncurry_left {n : WithTop ℕ∞} {f : P → E → X}
    (hf : ContDiffAt 𝕜 n (Function.uncurry f) (p, x)) : ContDiffAt 𝕜 n (f p) x :=
  hf.comp x (contDiffAt_const.prodMk contDiffAt_id)

/-- A slice `(x, y) ↦ H ((p, x), y)` of a family `H` on `(P × E) × G` that is jointly `C^n` at
`((p, x), y)` is `C^n` at `(x, y)`. -/
theorem comp_prodMap_prodMk_right {n : WithTop ℕ∞} {G : Type*} [NormedAddCommGroup G]
    [NormedSpace 𝕜 G] {H : (P × E) × G → X} {y : G} (hH : ContDiffAt 𝕜 n H ((p, x), y)) :
    ContDiffAt 𝕜 n (fun q : E × G ↦ H ((p, q.1), q.2)) (x, y) :=
  hH.comp (x, y) ((contDiff_prodMk_right p).prodMap contDiff_id).contDiffAt

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

/-- For a `C^n` map on a product with a scalar first factor, the `k`-th partial derivative in the
first variable is jointly `C^m` for `m + k ≤ n`. -/
theorem contDiffAt_iterate_deriv_fst {m n : WithTop ℕ∞} {g : 𝕜 × E → X} {z : 𝕜 × E}
    (hg : ContDiffAt 𝕜 n g z) {k : ℕ} (hmn : m + k ≤ n) :
    ContDiffAt 𝕜 m (fun w : 𝕜 × E ↦ deriv^[k] (fun r ↦ g (r, w.2)) w.1) z := by
  induction k generalizing n g with
  | zero => simpa using hg.of_le (by simpa using hmn)
  | succ k ih =>
    refine ih (hg.contDiffAt_deriv_fst (m := m + k) ?_) le_rfl
    rw [add_assoc]
    exact_mod_cast hmn

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

/-- Subtracting the members `g p` of a family of maps that is `C^n` jointly in the parameter `p`
and the point from a family `f t` that is jointly `C^n` gives a family that is jointly `C^n` in
both parameters and the point. -/
theorem sub_uncurry_prod {n : WithTop ℕ∞} {T : Type*} [NormedAddCommGroup T] [NormedSpace 𝕜 T]
    {f : T → E → X} {g : P → E → X} {t : T}
    (hf : ContDiffAt 𝕜 n (Function.uncurry f) (t, x))
    (hg : ContDiffAt 𝕜 n (fun q : P × E ↦ g q.1 q.2) (p, x)) :
    ContDiffAt 𝕜 n (fun q : (T × P) × E ↦ f q.1.1 q.2 - g q.1.2 q.2) ((t, p), x) :=
  (hf.comp ((t, p), x) (contDiffAt_fst.fst.prodMk contDiffAt_snd)).sub
    (hg.comp ((t, p), x) (contDiffAt_fst.snd.prodMk contDiffAt_snd))

end ContDiffAt

namespace ContDiffAt

open scoped NNReal

variable {𝕂 : Type*} [RCLike 𝕂]
  {P : Type*} [NormedAddCommGroup P] [NormedSpace 𝕂 P]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕂 E]
  {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕂 X] {p : P}

/-- **A `C¹` family is Lipschitz between two graphs meeting at a point.** If `f` is `C¹` at
`(p, ψ p)` and two maps `ψ` and `φ`, continuous at `p`, agree at `p`, then near `p` the values of
`f` along the two graphs differ by at most a fixed multiple of `‖ψ q - φ q‖`. -/
theorem exists_eventually_norm_sub_le {f : P × E → X} {ψ φ : P → E}
    (hf : ContDiffAt 𝕂 1 f (p, ψ p)) (hψ : ContinuousAt ψ p) (hφ : ContinuousAt φ p)
    (h : ψ p = φ p) :
    ∃ K : ℝ≥0, ∀ᶠ q in nhds p, ‖f (q, ψ q) - f (q, φ q)‖ ≤ K * ‖ψ q - φ q‖ := by
  obtain ⟨K, t, ht, hK⟩ := hf.exists_lipschitzOnWith
  have hψ' : ∀ᶠ q in nhds p, (q, ψ q) ∈ t := (continuousAt_id.prodMk hψ).preimage_mem_nhds ht
  have hφ' : ∀ᶠ q in nhds p, (q, φ q) ∈ t :=
    (continuousAt_id.prodMk hφ).preimage_mem_nhds (by simpa [h] using ht)
  refine ⟨K, ?_⟩
  filter_upwards [hψ', hφ'] with q h₁ h₂
  simpa [dist_eq_norm, Prod.dist_eq] using hK.dist_le_mul _ h₁ _ h₂

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
