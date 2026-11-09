/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Invertible
public import Mathlib.Topology.OpenPartialHomeomorph.Basic
public import TauCeti.Analysis.Calculus.NormalExtension
public import TauCeti.LinearAlgebra.TotallyReal.Basic
import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import TauCeti.LinearAlgebra.TotallyReal.Frame

/-!
# Coordinates adapted to a totally real submanifold

Let `γ : V → W` parametrize a submanifold of `W` near `x₀` and let `J : W → End W` be an almost
complex structure, both in coordinates. The adapted extension
`Φ (x, y) = γ x + J (γ x) (Dγ x y)` (`TauCeti.adaptedNormalExtension`) maps the zero section
`V × {0}` onto the image of `γ`, and its derivative along the zero section intertwines the
standard structure `(v, w) ↦ (-w, v)` of `V × V` with `J`. When `Dγ x₀` is injective with maximal
totally real image for `J (γ x₀)`, this derivative is invertible
(`TauCeti.isInvertible_fderiv_adaptedNormalExtension_zero`), so by the inverse function theorem
`Φ` is a local diffeomorphism near `(x₀, 0)`. Its inverse `ψ` is a chart of `W` near `γ x₀` which
straightens the submanifold, `ψ (γ x) = (x, 0)`, and whose derivative along the submanifold
intertwines `J` with the standard structure (`TauCeti.exists_adaptedChart`). When `γ` induces the
topology of its domain, as an embedding does, the chart can be chosen so that the part of the
submanifold in its domain is exactly the part of the zero section in its range
(`TauCeti.exists_adaptedChart_of_isInducing`).

The structure `J` read in this chart is `adaptedStructure γ J p = DΦ(p)⁻¹ ∘ J (Φ p) ∘ DΦ(p)`.
It is the standard structure along the zero section
(`TauCeti.adaptedStructure_zero_apply`), squares to `-1` wherever `J` does
(`TauCeti.adaptedStructure_apply_adaptedStructure`), and costs one derivative: for a `C^(n+1)`
parametrization and a `C^n` structure it is `C^m` whenever `m + 1 ≤ n`
(`TauCeti.contDiffOn_adaptedStructure`). This loss of a derivative is why boundary regularity
for pseudoholomorphic curves with totally real boundary conditions starts at `C²` structures.

In the elliptic boundary theory these charts reduce a totally real boundary condition
`u (∂Σ) ⊆ L` to the linear condition `u (∂Σ) ⊆ V × {0}` with `J = i` along `V × {0}`.

## Main results

* `TauCeti.isInvertible_fderiv_adaptedNormalExtension_zero`: the derivative of the adapted
  extension along the zero section is invertible at a point of maximal total reality.
* `TauCeti.adaptedStructure`: the structure `J` in the coordinates of the adapted extension.
* `TauCeti.adaptedStructure_zero_apply`: it is the standard structure along the zero section.
* `TauCeti.contDiffOn_adaptedStructure`: it loses one derivative.
* `TauCeti.exists_adaptedChart`: the adapted extension restricts to a local diffeomorphism near
  `(x₀, 0)`, whose inverse straightens the submanifold and is complex linear along it.
* `TauCeti.exists_adaptedChart_of_isInducing`: for an embedded submanifold, the chart carries the
  submanifold onto the zero section.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Exercise B.4.10.
-/

public noncomputable section

open Set Filter
open scoped Topology ContDiff

namespace TauCeti

variable {𝕜 V W : Type*} [RCLike 𝕜]
  [NormedAddCommGroup V] [NormedSpace 𝕜 V]
  [NormedAddCommGroup W] [NormedSpace 𝕜 W]
  {γ : V → W} {J : W → W →L[𝕜] W}

/-! ### Invertibility along the zero section -/

/-- **Invertibility of the adapted first jet.** If `γ` is `C¹` at `x` with injective derivative
whose image is maximal totally real for `J (γ x)`, a square root of `-1`, then the derivative of
`adaptedNormalExtension γ J` at `(x, 0)` is invertible. -/
theorem isInvertible_fderiv_adaptedNormalExtension_zero [CompleteSpace V] [CompleteSpace W]
    {x : V} (hγ : ContDiffAt 𝕜 1 γ x) (hJ : ContinuousAt J (γ x))
    (hsq : ∀ v, J (γ x) (J (γ x) v) = -v) (hinj : Function.Injective (fderiv 𝕜 γ x))
    (hL : IsMaximalTotallyReal (J (γ x)).toLinearMap (fderiv 𝕜 γ x).range) :
    (fderiv 𝕜 (adaptedNormalExtension γ J) (x, 0)).IsInvertible := by
  rw [fderiv_adaptedNormalExtension_zero hγ hJ]
  have hJinj : Function.Injective (J (γ x)) :=
    Function.LeftInverse.injective (g := fun v ↦ -J (γ x) v) fun v ↦ by simp [hsq]
  have hb := hL.bijective_coprod (A := (fderiv 𝕜 γ x).toLinearMap) hinj (hJinj.comp hinj)
  set D := (fderiv 𝕜 γ x).coprod ((J (γ x)).comp (fderiv 𝕜 γ x))
  have hD : Function.Bijective D := by
    convert hb using 1
    funext p
    simp [D]
  exact ⟨ContinuousLinearEquiv.ofBijective D (LinearMap.ker_eq_bot.mpr hD.1)
    (LinearMap.range_eq_top.mpr hD.2), rfl⟩

/-! ### The structure in adapted coordinates -/

/-- The almost complex structure `J` in the coordinates of the adapted extension
`Φ = adaptedNormalExtension γ J`: at `p` it is `DΦ(p)⁻¹ ∘ J (Φ p) ∘ DΦ(p)`. It is meaningful where
`DΦ(p)` is invertible, in particular on the source of an adapted chart
(`TauCeti.exists_adaptedChart`); elsewhere the inverse is taken to be zero. -/
def adaptedStructure (γ : V → W) (J : W → W →L[𝕜] W) (p : V × V) : V × V →L[𝕜] V × V :=
  (fderiv 𝕜 (adaptedNormalExtension γ J) p).inverse ∘L
    (J (adaptedNormalExtension γ J p) ∘L fderiv 𝕜 (adaptedNormalExtension γ J) p)

theorem adaptedStructure_def (γ : V → W) (J : W → W →L[𝕜] W) (p : V × V) :
    adaptedStructure γ J p = (fderiv 𝕜 (adaptedNormalExtension γ J) p).inverse ∘L
      (J (adaptedNormalExtension γ J p) ∘L fderiv 𝕜 (adaptedNormalExtension γ J) p) := (rfl)

/-- Where the derivative of the adapted extension is invertible, it carries `adaptedStructure`
to `J`. -/
theorem fderiv_adaptedNormalExtension_apply_adaptedStructure {p : V × V}
    (hp : (fderiv 𝕜 (adaptedNormalExtension γ J) p).IsInvertible) (v : V × V) :
    fderiv 𝕜 (adaptedNormalExtension γ J) p (adaptedStructure γ J p v) =
      J (adaptedNormalExtension γ J p) (fderiv 𝕜 (adaptedNormalExtension γ J) p v) := by
  simp only [adaptedStructure, ContinuousLinearMap.comp_apply, hp.self_apply_inverse]

/-- Conversely, the adapted structure is the unique endomorphism carried to `J` by an invertible
derivative of the adapted extension. -/
theorem adaptedStructure_eq_of_forall_fderiv_apply {p : V × V}
    (hp : (fderiv 𝕜 (adaptedNormalExtension γ J) p).IsInvertible) {T : V × V →L[𝕜] V × V}
    (hT : ∀ v, fderiv 𝕜 (adaptedNormalExtension γ J) p (T v) =
      J (adaptedNormalExtension γ J p) (fderiv 𝕜 (adaptedNormalExtension γ J) p v)) :
    adaptedStructure γ J p = T :=
  ContinuousLinearMap.ext fun v ↦ hp.injective <| by
    rw [fderiv_adaptedNormalExtension_apply_adaptedStructure hp, hT]

/-- The adapted structure squares to `-1` wherever the derivative of the adapted extension is
invertible and `J` squares to `-1`. -/
theorem adaptedStructure_apply_adaptedStructure {p : V × V}
    (hp : (fderiv 𝕜 (adaptedNormalExtension γ J) p).IsInvertible)
    (hsq : ∀ v, J (adaptedNormalExtension γ J p) (J (adaptedNormalExtension γ J p) v) = -v)
    (v : V × V) :
    adaptedStructure γ J p (adaptedStructure γ J p v) = -v := by
  apply hp.injective
  rw [fderiv_adaptedNormalExtension_apply_adaptedStructure hp,
    fderiv_adaptedNormalExtension_apply_adaptedStructure hp, hsq, map_neg]

/-- **Along the zero section the adapted structure is standard.** At a point of maximal total
reality, `adaptedStructure γ J (x, 0)` is the standard structure `(v, w) ↦ (-w, v)`. -/
theorem adaptedStructure_zero_apply [CompleteSpace V] [CompleteSpace W] {x : V}
    (hγ : ContDiffAt 𝕜 1 γ x) (hJ : ContinuousAt J (γ x))
    (hsq : ∀ v, J (γ x) (J (γ x) v) = -v) (hinj : Function.Injective (fderiv 𝕜 γ x))
    (hL : IsMaximalTotallyReal (J (γ x)).toLinearMap (fderiv 𝕜 γ x).range)
    (v : V × V) :
    adaptedStructure γ J (x, 0) v = (-v.2, v.1) := by
  have hp := isInvertible_fderiv_adaptedNormalExtension_zero hγ hJ hsq hinj hL
  refine congrArg (· v) (adaptedStructure_eq_of_forall_fderiv_apply hp
    (T := (-ContinuousLinearMap.snd 𝕜 V V).prod (ContinuousLinearMap.fst 𝕜 V V)) fun w ↦ ?_)
  rw [adaptedNormalExtension_zero]
  exact fderiv_adaptedNormalExtension_intertwines hγ hJ hsq w.1 w.2

/-- **The adapted structure loses one derivative.** For a `C^n` structure `J` on an open set `Ω`
and a `C^(n+1)` parametrization `γ` of an open set `U` into `Ω`, the adapted structure is `C^m`
for `m + 1 ≤ n` on every set of points of `U × V` where the derivative of the adapted extension
is invertible and the adapted extension takes values in `Ω`. -/
theorem contDiffOn_adaptedStructure [CompleteSpace V] {U : Set V} {Ω : Set W}
    {s : Set (V × V)} {m n : WithTop ℕ∞} (hU : IsOpen U) (hγ : ContDiffOn 𝕜 (n + 1) γ U)
    (hJ : ContDiffOn 𝕜 n J Ω) (hγΩ : MapsTo γ U Ω) (hmn : m + 1 ≤ n) (hsU : s ⊆ U ×ˢ univ)
    (hsΩ : MapsTo (adaptedNormalExtension γ J) s Ω)
    (hs : ∀ p ∈ s, (fderiv 𝕜 (adaptedNormalExtension γ J) p).IsInvertible) :
    ContDiffOn 𝕜 m (adaptedStructure γ J) s := by
  have hΦ := contDiffOn_adaptedNormalExtension hU hγ hJ hγΩ
  have hDΦ : ContDiffOn 𝕜 m (fderiv 𝕜 (adaptedNormalExtension γ J)) s :=
    (hΦ.fderiv_of_isOpen (hU.prod isOpen_univ) hmn).mono hsU
  have hm : m ≤ n := le_trans le_self_add hmn
  have hJΦ : ContDiffOn 𝕜 m (fun p ↦ J (adaptedNormalExtension γ J p)) s :=
    (hJ.comp (hΦ.mono hsU) hsΩ).of_le hm
  have hinv : ContDiffOn 𝕜 m (fun p ↦ (fderiv 𝕜 (adaptedNormalExtension γ J) p).inverse) s :=
    fun p hp ↦ ((hs p hp).contDiffAt_map_inverse.of_le le_top).comp_contDiffWithinAt p
      (hDΦ p hp)
  exact hinv.clm_comp (hJΦ.clm_comp hDΦ)

/-! ### The adapted chart -/

section Chart

variable [CompleteSpace V] [CompleteSpace W] {U : Set V} {Ω : Set W} {n : WithTop ℕ∞}

omit [CompleteSpace W] in
/-- The points of `U × V` at which the adapted extension lands in `Ω` and has invertible
derivative form an open set, when `γ` is `C^(n+1)` on `U` and `J` is `C^n` on an open `Ω`. -/
private theorem isOpen_adaptedChartDomain (hU : IsOpen U) (hΩ : IsOpen Ω)
    (hγ : ContDiffOn 𝕜 (n + 1) γ U) (hJ : ContDiffOn 𝕜 n J Ω) (hγΩ : MapsTo γ U Ω)
    (hn : 1 ≤ n) :
    IsOpen ((U ×ˢ univ) ∩ (adaptedNormalExtension γ J ⁻¹' Ω ∩
      fderiv 𝕜 (adaptedNormalExtension γ J) ⁻¹' {T | T.IsInvertible})) := by
  have hUV : IsOpen (U ×ˢ (univ : Set V)) := hU.prod isOpen_univ
  have hΦ := contDiffOn_adaptedNormalExtension hU hγ hJ hγΩ
  rw [inter_inter_distrib_left]
  exact (hΦ.continuousOn.isOpen_inter_preimage hUV hΩ).inter
    ((hΦ.continuousOn_fderiv_of_isOpen hUV hn).isOpen_inter_preimage hUV
      ContinuousLinearMap.isOpen_setOfPred_isInvertible)

omit [CompleteSpace V] [CompleteSpace W] in
/-- If the derivative `D` of an open partial homeomorphism at `e.symm a` carries the standard
structure of `V × V` to `T`, then the derivative of the inverse at `a` carries `T` back to the
standard structure. -/
private theorem fderiv_symm_apply_of_hasFDerivAt (e : OpenPartialHomeomorph (V × V) W) {a : W}
    (ha : a ∈ e.target) {D : (V × V) ≃L[𝕜] W} (hD : HasFDerivAt e (↑D : V × V →L[𝕜] W) (e.symm a))
    {T : W →L[𝕜] W} (hT : ∀ v w, D (-w, v) = T (D (v, w))) (b : W) :
    fderiv 𝕜 e.symm a (T b) = (-(fderiv 𝕜 e.symm a b).2, (fderiv 𝕜 e.symm a b).1) := by
  rw [(e.hasFDerivAt_symm ha hD).fderiv]
  apply D.injective
  simp only [ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply, hT,
    Prod.mk.eta]

/-- **Adapted coordinates along a totally real submanifold** (McDuff–Salamon, Exercise B.4.10).
Let `J` be a `C^n` structure on an open set `Ω`, with `1 ≤ n`, and let `γ` be a `C^(n+1)`
parametrization of an open set `U` into `Ω` whose derivative at `x₀` is injective with maximal
totally real image for `J (γ x₀)`, a square root of `-1` along `γ`. Then the adapted extension
`Φ = adaptedNormalExtension γ J` restricts to a `C^n` open partial homeomorphism `e` from a
neighbourhood of `(x₀, 0)` in `U × V` onto an open subset of `Ω`, with invertible derivative on
its source and `C^n` inverse. The inverse chart straightens the submanifold,
`e.symm (γ x) = (x, 0)`, and its derivative there intertwines `J (γ x)` with the standard
structure `(v, w) ↦ (-w, v)` of `V × V`. -/
theorem exists_adaptedChart {x₀ : V} (hU : IsOpen U) (hx₀ : x₀ ∈ U) (hΩ : IsOpen Ω)
    (hγ : ContDiffOn 𝕜 (n + 1) γ U) (hJ : ContDiffOn 𝕜 n J Ω) (hγΩ : MapsTo γ U Ω)
    (hn : 1 ≤ n) (hsq : ∀ x ∈ U, ∀ v, J (γ x) (J (γ x) v) = -v)
    (hinj : Function.Injective (fderiv 𝕜 γ x₀))
    (hL : IsMaximalTotallyReal (J (γ x₀)).toLinearMap (fderiv 𝕜 γ x₀).range) :
    ∃ e : OpenPartialHomeomorph (V × V) W,
      ⇑e = adaptedNormalExtension γ J ∧ (x₀, 0) ∈ e.source ∧ e.source ⊆ U ×ˢ univ ∧
      e.target ⊆ Ω ∧
      (∀ p ∈ e.source, (fderiv 𝕜 (adaptedNormalExtension γ J) p).IsInvertible) ∧
      ContDiffOn 𝕜 n e e.source ∧ ContDiffOn 𝕜 n e.symm e.target ∧
      (∀ x, (x, 0) ∈ e.source → e.symm (γ x) = (x, 0)) ∧
      (∀ x, (x, 0) ∈ e.source → ∀ w,
        fderiv 𝕜 e.symm (γ x) (J (γ x) w) =
          (-(fderiv 𝕜 e.symm (γ x) w).2, (fderiv 𝕜 e.symm (γ x) w).1)) := by
  set Φ := adaptedNormalExtension γ J with hΦdef
  have hΦat : ∀ p ∈ U ×ˢ (univ : Set V), ContDiffAt 𝕜 n Φ p := fun p hp ↦
    (contDiffOn_adaptedNormalExtension hU hγ hJ hγΩ).contDiffAt
      ((hU.prod isOpen_univ).mem_nhds hp)
  have hn0 : n ≠ 0 := (zero_lt_one.trans_le hn).ne'
  have hD : ∀ p ∈ U ×ˢ (univ : Set V), ∀ D : (V × V) ≃L[𝕜] W,
      (↑D : V × V →L[𝕜] W) = fderiv 𝕜 Φ p → HasFDerivAt Φ (↑D : V × V →L[𝕜] W) p :=
    fun p hp D hDe ↦ hDe ▸ ((hΦat p hp).differentiableAt (by simpa using hn0)).hasFDerivAt
  -- First jets along the zero section.
  have hγ1 : ∀ x ∈ U, ContDiffAt 𝕜 1 γ x := fun x hx ↦
    (hγ.contDiffAt (hU.mem_nhds hx)).of_le (hn.trans le_self_add)
  have hJc : ∀ x ∈ U, ContinuousAt J (γ x) := fun x hx ↦
    hJ.continuousOn.continuousAt (hΩ.mem_nhds (hγΩ hx))
  have hx₀' : (x₀, (0 : V)) ∈ U ×ˢ (univ : Set V) := ⟨hx₀, mem_univ _⟩
  obtain ⟨D₀, hD₀⟩ := isInvertible_fderiv_adaptedNormalExtension_zero (hγ1 x₀ hx₀)
    (hJc x₀ hx₀) (hsq x₀ hx₀) hinj hL
  -- The inverse function theorem at `(x₀, 0)`, restricted to the open set where `Φ` lands in
  -- `Ω` with invertible derivative.
  let e := ((hΦat _ hx₀').toOpenPartialHomeomorph Φ (hD _ hx₀' D₀ hD₀) hn0).restrOpen _
    (isOpen_adaptedChartDomain hU hΩ hγ hJ hγΩ hn)
  have hsrc : e.source ⊆ (U ×ˢ univ) ∩ (Φ ⁻¹' Ω ∩ fderiv 𝕜 Φ ⁻¹' {T | T.IsInvertible}) :=
    inter_subset_right
  have he (x : V) : e (x, 0) = γ x := adaptedNormalExtension_zero γ J x
  have hsymm (x : V) (hx : (x, 0) ∈ e.source) : e.symm (γ x) = (x, 0) :=
    he x ▸ e.left_inv hx
  refine ⟨e, rfl, ⟨(hΦat _ hx₀').mem_toOpenPartialHomeomorph_source _ hn0, hx₀', ?_, D₀, hD₀⟩,
    fun p hp ↦ (hsrc hp).1, fun a ha ↦ e.right_inv ha ▸ (hsrc (e.map_target ha)).2.1,
    fun p hp ↦ (hsrc hp).2.2, fun p hp ↦ (hΦat p (hsrc hp).1).contDiffWithinAt, ?_, hsymm, ?_⟩
  · simpa [hΦdef, adaptedNormalExtension_zero] using hγΩ hx₀
  · intro a ha
    obtain ⟨D, hDe⟩ := (hsrc (e.map_target ha)).2.2
    exact (e.contDiffAt_symm ha (hD _ (hsrc (e.map_target ha)).1 D hDe)
      (hΦat _ (hsrc (e.map_target ha)).1)).contDiffWithinAt
  · intro x hx w
    have hxU : x ∈ U := (hsrc hx).1.1
    have ha : γ x ∈ e.target := he x ▸ e.map_source hx
    obtain ⟨D, hDe⟩ := (hsrc hx).2.2
    have hDx : HasFDerivAt e (↑D : V × V →L[𝕜] W) (e.symm (γ x)) := by
      rw [hsymm x hx]
      exact hD _ (hsrc hx).1 D hDe
    refine fderiv_symm_apply_of_hasFDerivAt e ha hDx (fun v w ↦ ?_) w
    rw [← ContinuousLinearEquiv.coe_coe, hDe]
    exact fderiv_adaptedNormalExtension_intertwines (hγ1 x hxU) (hJc x hxU) (hsq x hxU) v w

/-- **Adapted coordinates along an embedded totally real submanifold.** If moreover `γ` induces
the topology of `U` (for instance, if it restricts to an embedding of `U`), the chart of
`TauCeti.exists_adaptedChart` can be chosen so that it straightens all of `γ (U)` inside its
target: every point `γ x` of the target with `x ∈ U` comes from the zero section of the source.
Thus `e.symm` maps `γ (U) ∩ e.target` onto `e.source ∩ (V × {0})`. -/
theorem exists_adaptedChart_of_isInducing {x₀ : V} (hU : IsOpen U) (hx₀ : x₀ ∈ U)
    (hΩ : IsOpen Ω) (hγ : ContDiffOn 𝕜 (n + 1) γ U) (hJ : ContDiffOn 𝕜 n J Ω)
    (hγΩ : MapsTo γ U Ω) (hn : 1 ≤ n) (hsq : ∀ x ∈ U, ∀ v, J (γ x) (J (γ x) v) = -v)
    (hinj : Function.Injective (fderiv 𝕜 γ x₀))
    (hL : IsMaximalTotallyReal (J (γ x₀)).toLinearMap (fderiv 𝕜 γ x₀).range)
    (hind : Topology.IsInducing fun x : U ↦ γ x) :
    ∃ e : OpenPartialHomeomorph (V × V) W,
      ⇑e = adaptedNormalExtension γ J ∧ (x₀, 0) ∈ e.source ∧ e.source ⊆ U ×ˢ univ ∧
      e.target ⊆ Ω ∧
      (∀ p ∈ e.source, (fderiv 𝕜 (adaptedNormalExtension γ J) p).IsInvertible) ∧
      ContDiffOn 𝕜 n e e.source ∧ ContDiffOn 𝕜 n e.symm e.target ∧
      (∀ x, (x, 0) ∈ e.source → e.symm (γ x) = (x, 0)) ∧
      (∀ x, (x, 0) ∈ e.source → ∀ w,
        fderiv 𝕜 e.symm (γ x) (J (γ x) w) =
          (-(fderiv 𝕜 e.symm (γ x) w).2, (fderiv 𝕜 e.symm (γ x) w).1)) ∧
      ∀ x ∈ U, γ x ∈ e.target → (x, 0) ∈ e.source := by
  obtain ⟨e, he, h₀, hsU, htΩ, hinv, hc, hcs, hstr, hint⟩ :=
    exists_adaptedChart hU hx₀ hΩ hγ hJ hγΩ hn hsq hinj hL
  have hγe (x : V) : e (x, 0) = γ x := by rw [he, adaptedNormalExtension_zero]
  -- The parameters whose zero-section point lies in the source are cut out of `U` by an open `O`.
  obtain ⟨O, hO, hOS⟩ := hind.isOpen_iff.mp
    (e.open_source.preimage (by fun_prop : Continuous fun y : U ↦ ((y : V), (0 : V))))
  have hmem (x : V) (hx : x ∈ U) : γ x ∈ O ↔ (x, 0) ∈ e.source :=
    Set.ext_iff.mp hOS ⟨x, hx⟩
  let e' := e.restrOpen (e.source ∩ e ⁻¹' O) (e.isOpen_inter_preimage hO)
  have hsrc : e'.source ⊆ e.source := fun p hp ↦ hp.1
  have htgt : e'.target ⊆ e.target := fun a ha ↦ ha.1
  have hsrc' (x : V) (hx : x ∈ U) (hxe : (x, 0) ∈ e.source) : (x, 0) ∈ e'.source := by
    refine ⟨hxe, hxe, ?_⟩
    rw [mem_preimage, hγe]
    exact (hmem x hx).mpr hxe
  refine ⟨e', he, hsrc' x₀ hx₀ h₀, hsrc.trans hsU,
    htgt.trans htΩ, fun p hp ↦ hinv p (hsrc hp), hc.mono hsrc, hcs.mono htgt,
    fun x hx ↦ hstr x (hsrc hx), fun x hx ↦ hint x (hsrc hx), fun x hx ha ↦ ?_⟩
  have hO : γ x ∈ O := by
    have h := ha.2.2
    rwa [mem_preimage, e.right_inv ha.1] at h
  exact hsrc' x hx ((hmem x hx).mp hO)

end Chart

end TauCeti
