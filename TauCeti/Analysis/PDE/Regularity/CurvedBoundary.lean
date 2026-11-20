/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Regularity.FlatBoundary
public import TauCeti.Analysis.Sobolev.LipschitzDomain.Basic
import TauCeti.Analysis.InnerProductSpace.HalfSpace
import TauCeti.Analysis.PDE.EnergyForm.ChangeOfVariables
import TauCeti.Analysis.PDE.Regularity.Interior
import TauCeti.Analysis.Sobolev.LipschitzDomain.Flattening
import TauCeti.Analysis.Sobolev.Wkp.Gluing

/-!
# `H²` regularity up to a `C²` boundary

Let `Ω ⊆ ℝⁿ` be open, let `a` be uniformly elliptic and Lipschitz, let `b, c ∈ L∞(Ω)` and
`f ∈ L²(Ω)`, and let `u ∈ H¹(Ω)` be a weak solution of

`-∂ᵢ(aⁱʲ ∂ⱼu) + ⟨b, ∇u⟩ + c u = f` in `Ω`.

This file proves that `u` is `H²` up to every part of `∂Ω` that is a `C²` graph and on which `u`
vanishes (`TauCeti.PDE.UniformlyEllipticOn.exists_lowerOrder_eq_restrictL_of_contDiff_graph`), and
hence that the weak solution `u ∈ H¹₀(Ω)` of the Dirichlet problem on a bounded open set with `C²`
boundary lies in `H²(Ω)` (`TauCeti.PDE.UniformlyEllipticOn.exists_lowerOrder_eq_of_contDiff_graph`).
A `C²` boundary is described as in Evans, Appendix C.1: near each boundary point, in rigid
coordinates `e : ℝⁿ ≃ ℝ × E` centred there, `Ω` is the region above the graph of a `C²` function
`γ : E → ℝ` with `γ 0 = 0`, inside a normal cylinder. Only the qualitative statement is proved:
no estimate of the `H²` norm is given.

## The argument

The classical proof (Evans, §6.3.2, Theorem 4) flattens the boundary.

* **Flattening.** The shear `Ψ(t, y) = (t - γ y, y)` and its inverse `Φ`, conjugated by `e`, are
  changes of variables of order two with Jacobian one
  (`TauCeti.exists_isChangeOfVariables_of_contDiff`), and `Φ` maps the half-space
  `{0 < (e x).fst}` near the boundary point onto `Ω` near it.
* **The transformed equation.** The function `u ∘ Φ` is a weak solution of an equation of the same
  form on the flat side (`TauCeti.PDE.energyFormH1_compL_eq_setIntegral`), whose principal
  coefficient is again uniformly elliptic (`TauCeti.PDE.UniformlyEllipticOn.pullbackPrincipal`) and
  Lipschitz (`TauCeti.PDE.exists_lipschitzOnWith_matrixBilinearForm_pullbackPrincipal`), since `DΦ`
  is `C¹` and so Lipschitz on compact convex sets, and whose lower-order terms and right-hand side
  stay bounded and square integrable. Zero boundary values are carried along by cutting off
  near the image of the support and pulling back.
* **The flat case.** Near the flat boundary, `u ∘ Φ` is `H²`
  (`TauCeti.PDE.UniformlyEllipticOn.exists_lowerOrder_eq_restrictL_of_halfSpace`), and
  precomposing with `Ψ`, a change of variables of order two (`TauCeti.Wkp.compL`), carries this
  back to `u` near the boundary point (`TauCeti.Wkp.exists_lowerOrder_eq_restrictL_of_w1pCompL`).
* **Gluing.** On a bounded domain finitely many such neighbourhoods, together with balls inside
  `Ω` where interior regularity applies
  (`TauCeti.PDE.UniformlyEllipticOn.exists_lowerOrder_eq_restrictL_of_locallyLipschitzOn`), cover
  the compact closure, and the local second derivatives glue (`TauCeti.Wkp.exists_glue`).

## Main declarations

* `TauCeti.PDE.UniformlyEllipticOn.exists_lowerOrder_eq_restrictL_of_contDiff_graph`: local `H²`
  regularity near a `C²` boundary portion on which the solution vanishes.
* `TauCeti.PDE.UniformlyEllipticOn.exists_lowerOrder_eq_of_contDiff_graph`: `H²` regularity of
  the Dirichlet problem on a bounded open set with `C²` boundary.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., §6.3.2, Theorem 4, and Appendix C.1.
* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Theorem 8.12.
-/

public section

noncomputable section

open Filter InnerProductSpace MeasureTheory Metric Set TopologicalSpace
open scoped ContDiff Gradient InnerProductSpace NNReal

namespace TauCeti

namespace PDE

variable {ι : Type*} [Fintype ι] {mu : Measure (EuclideanSpace ℝ ι)} [mu.IsAddHaarMeasure]

section Local

variable [DecidableEq ι] {Omega W : Opens (EuclideanSpace ℝ ι)}
  {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ}
  {lam Lam : ℝ} {K : ℝ≥0} {b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι}
  {c : EuclideanSpace ℝ ι → ℝ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Local `H²` regularity near a straightened boundary portion.** Let `Φ` and `Ψ` be mutually
inverse changes of variables of order two between open sets `U'` and `U`, with Jacobian
determinants at least one in absolute value, such that `Φ` maps the part of `U'` in the half-space
`H = {c₀ < ⟪x, ν⟫}` onto `Ω ∩ U`. Let `y₀ ∈ U'` lie in the closure of `H`, with `Φ y₀ ∈ W`. Under
the hypotheses of `UniformlyEllipticOn.exists_lowerOrder_eq_restrictL_of_contDiff_graph`, `u` is
`H²` on `Ω ∩ V` for an open neighbourhood `V` of `Φ y₀`. -/
private theorem exists_lowerOrder_eq_restrictL_of_isChangeOfVariables [Nonempty ι]
    {U' U : Opens (EuclideanSpace ℝ ι)} {Φ Ψ : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} {L : ℝ}
    (hΦ : Wkp.IsChangeOfVariables 2 U' U Φ L 1) (hΨ : Wkp.IsChangeOfVariables 2 U U' Ψ L 1)
    (hΨΦ : ∀ x, Ψ (Φ x) = x) (hΦΨ : ∀ y, Φ (Ψ y) = y) (hΦc : Continuous Φ) (hΨc : Continuous Ψ)
    {ν : EuclideanSpace ℝ ι} (hν : ν ≠ 0) {c₀ : ℝ}
    (himage : Φ '' ({x | c₀ < ⟪x, ν⟫_ℝ} ∩ U') = (Omega : Set (EuclideanSpace ℝ ι)) ∩ U)
    {y₀ : EuclideanSpace ℝ ι} (hy₀ : y₀ ∈ (U' : Set (EuclideanSpace ℝ ι)))
    (hy₀H : y₀ ∈ closure {x | c₀ < ⟪x, ν⟫_ℝ}) (hy₀W : Φ y₀ ∈ W)
    (ha : UniformlyEllipticOn ((Omega : Set (EuclideanSpace ℝ ι)) ∩ W) a lam Lam)
    (hK : LipschitzOnWith K (fun x => matrixBilinearForm (a x))
      ((Omega : Set (EuclideanSpace ℝ ι)) ∩ W))
    (hb : MemLp b ⊤ (mu.restrict Omega)) (hc : MemLp c ⊤ (mu.restrict Omega))
    {f : Lp ℝ 2 (mu.restrict Omega)} {u : W1p mu Omega 2}
    (hu : ∀ v : W1p0 mu Omega 2, energyFormH1 a b c u (v : W1p mu Omega 2) =
      ∫ x in Omega, f x * W1p.value (v : W1p mu Omega 2) x ∂mu)
    (hu0 : ∀ ψ : EuclideanSpace ℝ ι → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ W → ∃ v : W1p0 mu Omega 2,
        W1p.value (v : W1p mu Omega 2) =ᵐ[mu.restrict Omega] fun x => ψ x * W1p.value u x) :
    ∃ V : Opens (EuclideanSpace ℝ ι), Φ y₀ ∈ V ∧
      ∃ w : Wkp mu (Omega ⊓ V) 2 2, Wkp.lowerOrder 1 w = W1p.restrictL inf_le_left u := by
  -- A closed ball about `y₀` in `U'` on which `Φ` lands in `W`.
  obtain ⟨r, hr, hrB⟩ : ∃ r > 0, closedBall y₀ r ⊆ (U' : Set _) ∩ Φ ⁻¹' W :=
    nhds_basis_closedBall.mem_iff.1 ((U'.isOpen.inter (W.isOpen.preimage hΦc)).mem_nhds
      ⟨hy₀, hy₀W⟩)
  -- The flat domain `Ω' = H ∩ B(y₀, r)` and the curved one `D = Ω ∩ O`, `O = U ∩ Ψ⁻¹ B(y₀, r)`.
  let H : Opens (EuclideanSpace ℝ ι) := ⟨{x | c₀ < ⟪x, ν⟫_ℝ}, isOpen_lt continuous_const
    (continuous_id.inner continuous_const)⟩
  let B'' : Opens (EuclideanSpace ℝ ι) := ⟨ball y₀ r, isOpen_ball⟩
  let Ω' : Opens (EuclideanSpace ℝ ι) := H ⊓ B''
  let O : Opens (EuclideanSpace ℝ ι) := ⟨U ∩ Ψ ⁻¹' ball y₀ r,
    hΨc.continuousOn.isOpen_inter_preimage U.isOpen isOpen_ball⟩
  let D : Opens (EuclideanSpace ℝ ι) := Omega ⊓ O
  have hBU' : (B'' : Set (EuclideanSpace ℝ ι)) ⊆ U' :=
    ball_subset_closedBall.trans (hrB.trans inter_subset_left)
  have hOW : (O : Set (EuclideanSpace ℝ ι)) ⊆ W := fun y hy => by
    simpa [hΦΨ] using (hrB (ball_subset_closedBall hy.2)).2
  have hΦmaps : MapsTo Φ Ω' D := fun x hx => by
    have hmem : Φ x ∈ (Omega : Set _) ∩ U := himage ▸ mem_image_of_mem _ ⟨hx.1, hBU' hx.2⟩
    exact ⟨hmem.1, hmem.2, by rw [mem_preimage, hΨΦ]; exact hx.2⟩
  have hΨmaps : MapsTo Ψ D Ω' := fun y hy => by
    have hy' : y ∈ Φ '' ({x | c₀ < ⟪x, ν⟫_ℝ} ∩ U') := by rw [himage]; exact ⟨hy.1, hy.2.1⟩
    obtain ⟨x, ⟨hxH, -⟩, rfl⟩ := hy'
    exact ⟨by rw [hΨΦ]; exact hxH, hy.2.2⟩
  have hDU : D ≤ U := fun y hy => hy.2.1
  have hΦ' := hΦ.mono_set (fun x hx => hBU' hx.2 : Ω' ≤ U') hΦmaps
  have hΨ' := hΨ.mono_set hDU hΨmaps
  -- On the flat side, `u ∘ Φ` solves an equation of the same form, with uniformly elliptic and
  -- Lipschitz principal coefficient, and has zero boundary values.
  obtain ⟨hb', hc', f', hu₁⟩ := exists_forall_energyFormH1_compL_restrictL_eq (mu := mu)
    (inf_le_left : D ≤ Omega) (hΦ'.mono one_le_two) (hΨ'.mono one_le_two) (fun x _ => hΨΦ x)
    (fun y _ => hΦΨ y) hb hc hu
  obtain ⟨z, hzH, hz⟩ := Metric.mem_closure_iff.1 hy₀H r hr
  obtain ⟨lam', Lam', K', hellip, hK'⟩ :=
    exists_uniformlyEllipticOn_and_lipschitzOnWith_pullbackPrincipal (hΦ.mono one_le_two) hΨ
      (fun x _ => hΨΦ x) (fun y _ => hΦΨ y) (isCompact_closedBall y₀ r)
      (convex_closedBall y₀ r)
      (hrB.trans inter_subset_left)
      (fun x (hx : x ∈ (Ω' : Set (EuclideanSpace ℝ ι)) ∩ B'') => ball_subset_closedBall hx.2)
      (by exact ⟨z, ⟨hzH, mem_ball_comm.1 hz⟩, mem_ball_comm.1 hz⟩)
      (t := (Omega : Set (EuclideanSpace ℝ ι)) ∩ W)
      (fun x hx => ⟨(hΦmaps hx.1).1, hOW (hΦmaps hx.1).2⟩) ha hK
  have hu0' := (hΦ'.mono one_le_two).exists_w1p0_value_ae_eq_mul_value_w1pCompL
    ENNReal.ofNat_ne_top hΦc.continuousOn hΨc.continuousOn hΨmaps (fun x _ => hΨΦ x)
    (fun x hx => ⟨hΦ.mapsTo (hBU' hx), by rw [mem_preimage, hΨΦ]; exact hx⟩ : MapsTo Φ B'' O)
    (fun χ hχ hχc hχs => hu0 χ hχ hχc (hχs.trans hOW))
  -- `H²` regularity near the flat boundary, on `Ω' ∩ B(y₀, r / 2)`.
  let V'' : Opens (EuclideanSpace ℝ ι) := ⟨ball y₀ (r / 2), isOpen_ball⟩
  have hV''c : closure (V'' : Set (EuclideanSpace ℝ ι)) ⊆ closedBall y₀ (r / 2) :=
    closure_ball_subset_closedBall
  obtain ⟨w'', hw''⟩ := UniformlyEllipticOn.exists_lowerOrder_eq_restrictL_of_halfSpace
    (Omega := Ω') (H := H) (U := B'') (V := V'') hν (fun _ => Iff.rfl)
    (by rw [Opens.coe_inf, inter_assoc, inter_self]) hellip hK' hb' hc' hu₁ hu0'
    ((isCompact_closedBall y₀ (r / 2)).of_isClosed_subset isClosed_closure hV''c)
    (hV''c.trans (closedBall_subset_ball (half_lt_self hr)))
  -- Push forward to `Ω ∩ V` with `V = U ∩ Ψ⁻¹(B(y₀, r / 2))`.
  let V : Opens (EuclideanSpace ℝ ι) := ⟨U ∩ Ψ ⁻¹' ball y₀ (r / 2),
    hΨc.continuousOn.isOpen_inter_preimage U.isOpen isOpen_ball⟩
  have hVD' : ((Omega ⊓ V : Opens _) : Set (EuclideanSpace ℝ ι)) ⊆ D := fun y hy => by
    simp only [D, O, V, Opens.coe_inf, Opens.coe_mk, mem_inter_iff, mem_preimage] at hy ⊢
    exact ⟨hy.1, hy.2.1, ball_subset_ball (half_le_self hr.le) hy.2.2⟩
  have hVD : Omega ⊓ V ≤ D := SetLike.coe_subset_coe.mp hVD'
  obtain ⟨w, hw⟩ := Wkp.exists_lowerOrder_eq_restrictL_of_w1pCompL (Omega := Omega) (D := D)
    (V := V) (Ω' := Ω') (V'' := V'') ENNReal.ofNat_ne_top inf_le_left hVD (hΦ'.mono one_le_two)
    (hΨ.mono_set (hVD.trans hDU) fun y hy => ⟨hΨmaps (hVD' hy), hy.2.2⟩) (fun y _ => hΦΨ y)
    (u := u)
    (w := w'') hw''
  exact ⟨V, ⟨hΦ.mapsTo hy₀, by rw [mem_preimage, hΨΦ]; exact mem_ball_self (half_pos hr)⟩, w, hw⟩

/-- **Local `H²` regularity near a `C²` boundary portion.** Let `Ω` be open, and suppose that in
rigid coordinates `e` centred at `x₀ = e⁻¹ 0`, inside the normal cylinder of half-height `h₀` and
radius `r₀`, `Ω` is the region above the graph of a `C²` function `γ` with `γ 0 = 0`. Let `W` be
an open neighbourhood of `x₀`, let `a` be uniformly elliptic on `Ω ∩ W`, with `x ↦ a(x)` Lipschitz
on `Ω ∩ W` in the operator norm of its bilinear forms, let `b, c ∈ L∞(Ω)`, and let `u ∈ H¹(Ω)` be
a weak solution of

`-∂ᵢ(aⁱʲ ∂ⱼu) + ⟨b, ∇u⟩ + c u = f` in `Ω`, with `f ∈ L²(Ω)`,

such that `ψ u ∈ H¹₀(Ω)` for every smooth `ψ` compactly supported in `W`: `u` vanishes on
`∂Ω ∩ W`. Then there is an open neighbourhood `V` of `x₀` such that the restriction of `u` to
`Ω ∩ V` is the first-order part of an element of `W^{2,2}(Ω ∩ V)`. -/
theorem UniformlyEllipticOn.exists_lowerOrder_eq_restrictL_of_contDiff_graph
    {e : EuclideanSpace ℝ ι ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × E)} {γ : E → ℝ} {h₀ r₀ : ℝ} (hh₀ : 0 < h₀)
    (hr₀ : 0 < r₀) (hγ0 : γ 0 = 0) (hγ : ContDiff ℝ 2 γ)
    (hgraph : ∀ z ∈ normalCylinder h₀ r₀, (e.symm z ∈ Omega ↔ γ z.snd < z.fst))
    (hW : e.symm 0 ∈ W)
    (ha : UniformlyEllipticOn ((Omega : Set (EuclideanSpace ℝ ι)) ∩ W) a lam Lam)
    (hK : LipschitzOnWith K (fun x => matrixBilinearForm (a x))
      ((Omega : Set (EuclideanSpace ℝ ι)) ∩ W))
    (hb : MemLp b ⊤ (mu.restrict Omega)) (hc : MemLp c ⊤ (mu.restrict Omega))
    {f : Lp ℝ 2 (mu.restrict Omega)} {u : W1p mu Omega 2}
    (hu : ∀ v : W1p0 mu Omega 2, energyFormH1 a b c u (v : W1p mu Omega 2) =
      ∫ x in Omega, f x * W1p.value (v : W1p mu Omega 2) x ∂mu)
    (hu0 : ∀ ψ : EuclideanSpace ℝ ι → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ W → ∃ v : W1p0 mu Omega 2,
        W1p.value (v : W1p mu Omega 2) =ᵐ[mu.restrict Omega] fun x => ψ x * W1p.value u x) :
    ∃ V : Opens (EuclideanSpace ℝ ι), e.symm 0 ∈ V ∧
      ∃ w : Wkp mu (Omega ⊓ V) 2 2, Wkp.lowerOrder 1 w = W1p.restrictL inf_le_left u := by
  -- `E` is finite-dimensional, being a factor of `ℝ × E ≃ ℝⁿ`, and `ι` is nonempty.
  have : FiniteDimensional ℝ (WithLp 2 (ℝ × E)) :=
    e.linearIsometryEquiv.toLinearEquiv.finiteDimensional
  have : FiniteDimensional ℝ E := Module.Finite.of_surjective (WithLp.sndₗ 2 ℝ ℝ E)
    fun y => ⟨WithLp.toLp 2 (0, y), rfl⟩
  have : Nonempty ι := by
    by_contra hι
    rw [not_nonempty_iff] at hι
    have h : e.symm (WithLp.toLp 2 (1, 0)) = e.symm 0 := by
      ext i
      exact isEmptyElim i
    simpa using congrArg WithLp.fst (e.symm.injective h)
  -- Flatten the boundary: `Φ` maps the flat side `U'` into `U`, inverse to `Ψ`, and fixes `x₀`.
  obtain ⟨U', U, L, hx₀U, -, hΦ, hΨ, himage⟩ :=
    exists_isChangeOfVariables_of_contDiff (k := 2) one_le_two hh₀ hr₀ hγ0 hγ hgraph
  set G := graphFlattening γ hγ.continuous
  have hΨΦ (x : EuclideanSpace ℝ ι) : (e.symm ∘ G ∘ e) ((e.symm ∘ G.symm ∘ e) x) = x := by simp
  have hΦΨ (y : EuclideanSpace ℝ ι) : (e.symm ∘ G.symm ∘ e) ((e.symm ∘ G ∘ e) y) = y := by simp
  have hΨx₀ : (e.symm ∘ G ∘ e) (e.symm 0) = e.symm 0 := by simp [G, hγ0]
  have hΦx₀ : (e.symm ∘ G.symm ∘ e) (e.symm 0) = e.symm 0 := by
    have h := hΦΨ (e.symm 0)
    rwa [hΨx₀] at h
  -- In rigid coordinates the flat side is the half-space `{-(e 0).fst < ⟪x, ν⟫}`.
  set ν := e.linearIsometryEquiv.symm (WithLp.toLp 2 (1, 0))
  have hHν (x : EuclideanSpace ℝ ι) : 0 < (e x).fst ↔ -(e 0).fst < ⟪x, ν⟫_ℝ := by
    rw [e.fst_apply_eq_inner_add]
    constructor <;> intro h <;> linarith
  have hH : {x | 0 < (e x).fst} = {x | -(e 0).fst < ⟪x, ν⟫_ℝ} := Set.ext hHν
  -- `x₀` is a limit of the points `e⁻¹ (t, 0)`, `t > 0`, of the flat side.
  have hx₀H : e.symm 0 ∈ closure {x | -(e 0).fst < ⟪x, ν⟫_ℝ} := by
    refine Metric.mem_closure_iff.2 fun ε hε => ⟨e.symm (WithLp.toLp 2 (ε / 2, 0)), ?_, ?_⟩
    · exact (hHν _).1 (by simpa using half_pos hε)
    · rw [dist_comm, e.symm.dist_map, dist_zero_right]
      simpa [WithLp.prod_norm_eq_of_L2, abs_of_pos hε] using half_lt_self hε
  have h := exists_lowerOrder_eq_restrictL_of_isChangeOfVariables hΦ hΨ hΨΦ hΦΨ
    (e.symm.continuous.comp (G.symm.continuous.comp e.continuous))
    (e.symm.continuous.comp (G.continuous.comp e.continuous)) (by simp [ν]) (hH ▸ himage)
    (hΨx₀ ▸ hΨ.mapsTo hx₀U) (hΨx₀ ▸ hx₀H) (by rwa [hΦx₀]) ha hK hb hc hu hu0
  rwa [hΦx₀] at h

/-- **`H²` regularity up to a `C²` boundary.** Let `Ω` be a bounded open set with `C²` boundary:
at every boundary point `x`, in rigid coordinates `e` with `e x = 0`, inside a normal cylinder,
`Ω` is the region above the graph of a `C²` function `γ` with `γ 0 = 0`. Let `a` be uniformly
elliptic on `Ω` and Lipschitz on `Ω` in the operator norm of its bilinear forms, let
`b, c ∈ L∞(Ω)`, and let `u ∈ H¹₀(Ω)` be a weak solution of the Dirichlet problem

`-∂ᵢ(aⁱʲ ∂ⱼu) + ⟨b, ∇u⟩ + c u = f` in `Ω`, `u = 0` on `∂Ω`, with `f ∈ L²(Ω)`.

Then `u ∈ H²(Ω)`: it is the first-order part of an element of `W^{2,2}(Ω)`. -/
theorem UniformlyEllipticOn.exists_lowerOrder_eq_of_contDiff_graph
    (hΩ : Bornology.IsBounded (Omega : Set (EuclideanSpace ℝ ι)))
    (hbdry : ∀ x ∈ frontier (Omega : Set (EuclideanSpace ℝ ι)),
      ∃ (e : EuclideanSpace ℝ ι ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × E)) (γ : E → ℝ) (h₀ r₀ : ℝ),
        e x = 0 ∧ 0 < h₀ ∧ 0 < r₀ ∧ γ 0 = 0 ∧ ContDiff ℝ 2 γ ∧
          ∀ z ∈ normalCylinder h₀ r₀, (e.symm z ∈ Omega ↔ γ z.snd < z.fst))
    (ha : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (hK : LipschitzOnWith K (fun x => matrixBilinearForm (a x)) Omega)
    (hb : MemLp b ⊤ (mu.restrict Omega)) (hc : MemLp c ⊤ (mu.restrict Omega))
    {f : Lp ℝ 2 (mu.restrict Omega)} {u : W1p mu Omega 2} (hu0 : u ∈ w1p0Submodule mu Omega 2)
    (hu : ∀ v : W1p0 mu Omega 2, energyFormH1 a b c u (v : W1p mu Omega 2) =
      ∫ x in Omega, f x * W1p.value (v : W1p mu Omega 2) x ∂mu) :
    ∃ w : Wkp mu Omega 2 2, Wkp.lowerOrder 1 w = u := by
  -- Every point of `closure Ω` has a neighbourhood `V` with `u ∈ H²(Ω ∩ V)`.
  have hloc (x : EuclideanSpace ℝ ι) (hx : x ∈ closure (Omega : Set (EuclideanSpace ℝ ι))) :
      ∃ V : Opens (EuclideanSpace ℝ ι), x ∈ V ∧
        ∃ w : Wkp mu (Omega ⊓ V) 2 2, Wkp.lowerOrder 1 w = W1p.restrictL inf_le_left u := by
    by_cases hxΩ : x ∈ (Omega : Set (EuclideanSpace ℝ ι))
    · -- Interior points, by interior regularity on a small ball.
      obtain ⟨ρ, hρ, hρΩ⟩ := nhds_basis_closedBall.mem_iff.1 (Omega.isOpen.mem_nhds hxΩ)
      have hcl : closure ((Omega ⊓ ⟨ball x ρ, isOpen_ball⟩ : Opens (EuclideanSpace ℝ ι)) :
          Set (EuclideanSpace ℝ ι)) ⊆ closedBall x ρ :=
        (closure_mono inter_subset_right).trans closure_ball_subset_closedBall
      exact ⟨⟨ball x ρ, isOpen_ball⟩, mem_ball_self hρ,
        ha.exists_lowerOrder_eq_restrictL_of_locallyLipschitzOn
          (fun _ _ => ⟨K, _, self_mem_nhdsWithin, hK⟩) hb hc hu
          ((isCompact_closedBall x ρ).of_isClosed_subset isClosed_closure hcl) (hcl.trans hρΩ)⟩
    · -- Boundary points, by flattening the boundary.
      obtain ⟨e, γ, h₀, r₀, hex, hh₀, hr₀, hγ0, hγ, hgraph⟩ :=
        hbdry x ⟨hx, by rwa [Omega.isOpen.interior_eq]⟩
      have hx₀ : e.symm 0 = x := by rw [← hex, e.symm_apply_apply]
      obtain ⟨V, hV, hw⟩ :=
        (ha.mono_set inter_subset_left).exists_lowerOrder_eq_restrictL_of_contDiff_graph
        (W := ⊤) hh₀ hr₀ hγ0 hγ hgraph trivial (hK.mono inter_subset_left) hb hc hu
        fun ψ hψ hψc _ => W1p.exists_w1p0_value_ae_eq_mul_of_mem_w1p0Submodule hψ hψc hu0
      exact ⟨V, hx₀ ▸ hV, hw⟩
  -- Finitely many such neighbourhoods cover the compact set `closure Ω`; glue.
  choose V hxV w hw using hloc
  obtain ⟨t, ht⟩ := hΩ.isCompact_closure.elim_nhds_subcover' (fun x hx => (V x hx : Set _))
    fun x hx => (V x hx).isOpen.mem_nhds (hxV x hx)
  have hcov : Omega ≤ ⨆ i : t, Omega ⊓ V i.val.val i.val.property := fun y hy => by
    obtain ⟨x, hxt, hyx⟩ := mem_iUnion₂.1 (ht (subset_closure hy))
    exact Opens.mem_iSup.2 ⟨⟨x, hxt⟩, Opens.mem_inf.2 ⟨hy, hyx⟩⟩
  obtain ⟨v, hv, -, -⟩ := Wkp.exists_glue (fun _ => inf_le_left) hcov 2
    (fun i => w i.val.val i.val.property) (u := W1p.value u) fun i => by
      rw [Wkp.value_succ, Wkp.value_one, hw]
      exact W1p.value_restrictL_ae inf_le_left u
  exact ⟨v, W1p.ext_value (Lp.ext (by rw [Wkp.value_lowerOrder_one]; exact hv))⟩

end Local

end PDE

end TauCeti
