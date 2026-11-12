/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.DifferentialForm.Basic
public import Mathlib.Geometry.Manifold.Diffeomorph
public import Mathlib.RepresentationTheory.Continuous.Basic
import TauCeti.Analysis.Calculus.DifferentialForm.Invariant
import TauCeti.Analysis.Normed.Module.Alternating.Curry
import TauCeti.Analysis.Calculus.Moser
import TauCeti.Dynamics.Flow.RestPoint
import TauCeti.Geometry.Manifold.Diffeomorph.NormedSpace
import TauCeti.RepresentationTheory.Continuous.InvariantNeighborhood
import TauCeti.Topology.Algebra.Module.BilinearForm

/-!
# Darboux's theorem

Let `ω` be a closed differential two-form on an open subset `W` of a finite-dimensional real
normed space `V`, of class `C^r` with `r ≥ 1`, and nondegenerate at a point `x₀ ∈ W`. **Darboux's
theorem** says that near `x₀` the form `ω` is constant in suitable coordinates: there is a `C^r`
diffeomorphism `ψ` of `V` fixing `x₀` with `ψ^* ω = ω(x₀)` on a neighbourhood of `x₀`
(`TauCeti.exists_diffeomorph_eventually_compContinuousLinearMap_fderiv_eq`). Its inverse is
therefore a chart around `x₀` in which `ω` is the constant form `ω(x₀)`. Choosing a symplectic
basis of the constant nondegenerate form `ω(x₀)` is a separate linear step, which turns these
coordinates into the classical ones with `ω = ∑ dxᵢ ∧ dyᵢ`.

The proof is Moser's deformation argument, which this file states in its local form
(`TauCeti.exists_diffeomorph_eventually_compContinuousLinearMap_fderiv_eq_of_extDeriv_eq`). Let
`ω₀`, `ω₁` be closed two-forms near `x₀` which agree and are nondegenerate at `x₀`, and let `α` be
a one-form with `dα = ω₁ - ω₀` and `α(x₀) = 0`. Along the straight-line family
`ωₜ = (1 - t) ω₀ + t ω₁`, which is nondegenerate near `x₀` for all `t ∈ [0, 1]`, the Moser field
`Xₜ` is defined by `ι_{Xₜ} ωₜ = -α` (`TauCeti.exists_contDiffOn_moserField`). It vanishes wherever
`α` does, in particular at `x₀`, so its time-dependent flow `ψₜ` exists near `x₀` up to time one and
fixes the zeros of `α` (`TauCeti.exists_eventually_forall_hasDerivAt_fderiv_of_contDiffOn`), and
Moser's identity (`TauCeti.compContinuousLinearMap_fderiv_eq_of_curryLeft_eq_neg`) gives
`ψ₁^* ω₁ = ψ₀^* ω₀ = ω₀` near `x₀`. For Darboux's theorem, `ω₀` is the constant form `ω(x₀)`,
`ω₁ = ω`, and the Poincaré lemma near `x₀` supplies `α`. Choosing `α` to vanish along a
submanifold instead gives the relative Darboux theorem, in
`TauCeti.Geometry.Symplectic.Darboux.Relative`.

Both theorems are proved in an **equivariant** form, of which the plain statements are the case
of the trivial group. Let a group `G` act on `V` through a continuous representation `ρ` whose
operators form a bounded set, as for a finite group or a compact group acting continuously, and
let `x₀` be fixed by `G`; after Bochner linearization this is the model of a compact group acting
near a fixed point. If the forms and the primitive are `ρ`-invariant, then the Moser field is
`ρ`-equivariant, by uniqueness of the solution of `ι_{Xₜ} ωₜ = -α`
(`TauCeti.moserField_map_eq`), and so is its flow on a small invariant neighbourhood of `x₀`, by
uniqueness of solutions of the flow equation. This gives the **equivariant Moser lemma**
(`TauCeti.exists_equivariant_diffeomorph_compContinuousLinearMap_fderiv_eq_of_extDeriv_eq`). The
invariant Poincaré lemma (`StarConvex.exists_invariant_contDiffOn_forall_extDeriv_eq`) supplies an
invariant primitive on an invariant convex neighbourhood
(`ContRepresentation.nhds_basis_isOpen_convex_mapsTo`), so a `ρ`-invariant closed form
nondegenerate at `x₀` is constant in coordinates which are `ρ`-equivariant on an invariant
neighbourhood of `x₀`: this is the **equivariant Darboux theorem**
(`TauCeti.exists_equivariant_diffeomorph_compContinuousLinearMap_fderiv_eq`). Choosing a
symplectic basis of `ω(x₀)` then conjugates `ρ` into a representation by linear symplectic maps
of the standard symplectic space; the basis itself need not be `ρ`-invariant.

Forms are Mathlib's continuous alternating maps, `V [⋀^Fin 2]→L[ℝ] ℝ`, with Mathlib's exterior
derivative `extDeriv`, and the pullback of `ω` along `ψ` at `x` is
`(ω (ψ x)).compContinuousLinearMap (fderiv ℝ ψ x)`. Nondegeneracy of `ω(x₀)` is the statement that
no nonzero vector `v` has `ω(x₀)(v, w) = 0` for every `w`.

## References

* D. McDuff and D. Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford, 2017,
  Section 3.2 (Moser's argument and Darboux's theorem).
* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Theorem 22.13 (Darboux's theorem).
* V. Guillemin and S. Sternberg, *Symplectic Techniques in Physics*, Cambridge University Press,
  1984 (the equivariant Darboux theorem, by an equivariant Moser argument).
-/

public section

open Set Filter Topology Metric
open scoped Manifold

namespace TauCeti

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

section Equivariant

variable {G : Type*} [Group G] {ρ : ContRepresentation ℝ G V}

/-- **Moser's lemma**, local equivariant form. Let a group `G` act on a finite-dimensional real
normed space through a continuous representation `ρ` whose operators form a bounded set (for
instance a finite group, or a compact group acting continuously), fixing a point `x₀`. Let `ω₀`,
`ω₁` be closed `C^r` two-forms (`r ≥ 1`) on an open set `W ∋ x₀`, with `ω₁ - ω₀ = dα` on `W` for a
`C^r` one-form `α` vanishing at `x₀`, where `ω₀`, `ω₁` and `α` are invariant under every `ρ g` at
the points of `W`. If `ω₀` and `ω₁` agree at `x₀` and are nondegenerate there, then some `C^r`
diffeomorphism `ψ` of the space pulls `ω₁` back to `ω₀` on a `ρ`-invariant open neighbourhood
`U ⊆ W` of `x₀`, commutes with every `ρ g` on `U`, and fixes every point of `U` at which `α`
vanishes; in particular `ψ x₀ = x₀`. -/
theorem exists_equivariant_diffeomorph_compContinuousLinearMap_fderiv_eq_of_extDeriv_eq
    (hρ : Bornology.IsBounded (range ρ)) {ω₀ ω₁ : V → V [⋀^Fin 2]→L[ℝ] ℝ}
    {α : V → V [⋀^Fin 1]→L[ℝ] ℝ} {W : Set V} {x₀ : V} (hρx₀ : ∀ g, ρ g x₀ = x₀) {r : ℕ∞}
    (hr : 1 ≤ r) (hW : IsOpen W) (hx₀ : x₀ ∈ W) (hω₀ : ContDiffOn ℝ r ω₀ W)
    (hω₁ : ContDiffOn ℝ r ω₁ W) (hα : ContDiffOn ℝ r α W) (hdω₀ : ∀ x ∈ W, extDeriv ω₀ x = 0)
    (hdω₁ : ∀ x ∈ W, extDeriv ω₁ x = 0) (hdα : ∀ x ∈ W, extDeriv α x = ω₁ x - ω₀ x)
    (hα₀ : α x₀ = 0) (heq : ω₁ x₀ = ω₀ x₀) (hnd : ∀ v, (∀ w, ω₀ x₀ ![v, w] = 0) → v = 0)
    (hω₀ρ : ∀ g, ∀ y ∈ W, (ω₀ (ρ g y)).compContinuousLinearMap (ρ g) = ω₀ y)
    (hω₁ρ : ∀ g, ∀ y ∈ W, (ω₁ (ρ g y)).compContinuousLinearMap (ρ g) = ω₁ y)
    (hαρ : ∀ g, ∀ y ∈ W, (α (ρ g y)).compContinuousLinearMap (ρ g) = α y) :
    ∃ (ψ : V ≃ₘ^r⟮𝓘(ℝ, V), 𝓘(ℝ, V)⟯ V) (U : Set V), IsOpen U ∧ x₀ ∈ U ∧ U ⊆ W ∧
      (∀ g, MapsTo (ρ g) U U) ∧ (∀ x ∈ U, α x = 0 → ψ x = x) ∧
      (∀ g, ∀ x ∈ U, ψ (ρ g x) = ρ g (ψ x)) ∧
      ∀ x ∈ U, (ω₁ (ψ x)).compContinuousLinearMap (fderiv ℝ ψ x) = ω₀ x := by
  -- The proof is Moser's argument. Solve `ι_{Xₜ} ωₜ = -α` near `x₀`; by invariance of the data
  -- and uniqueness of the solution, `Xₜ` is equivariant. Flow along `Xₜ` up to time one inside a
  -- small invariant neighbourhood, on which the field is Lipschitz; there both `ρ g ∘ ψₜ` and
  -- `ψₜ ∘ ρ g` solve the same ODE with the same initial value, so they agree. Moser's identity
  -- then gives `ψ₁^* ω₁ = ω₀`.
  have hr0 : (r : WithTop ℕ∞) ≠ 0 := by
    have : (1 : WithTop ℕ∞) ≤ r := by exact_mod_cast hr
    exact (lt_of_lt_of_le zero_lt_one this).ne'
  have hbasis := ContRepresentation.nhds_basis_isOpen_convex_mapsTo ρ hρ hρx₀
  -- The forms as bilinear maps, as the Moser field equation takes them.
  let e : (V [⋀^Fin 1]→L[ℝ] ℝ) →L[ℝ] V →L[ℝ] ℝ :=
    (ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := ℝ) (E := V) (F := ℝ)
      (0 : Fin 1)).symm.toContinuousLinearEquiv.toContinuousLinearMap
  have he (a : V [⋀^Fin 1]→L[ℝ] ℝ) (m : Fin 1 → V) : e a (m 0) = a m := by
    simp only [e, ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
      ContinuousAlternatingMap.ofSubsingletonLIE_symm_apply,
      ContinuousAlternatingMap.ofSubsingleton_symm_apply_apply]
    congr 1
    funext i
    rw [Subsingleton.elim i 0]
  let B₀ : V → V →L[ℝ] V →L[ℝ] ℝ := fun y ↦ ContinuousAlternatingMap.flatL ℝ V ℝ (ω₀ y)
  let B₁ : V → V →L[ℝ] V →L[ℝ] ℝ := fun y ↦ ContinuousAlternatingMap.flatL ℝ V ℝ (ω₁ y)
  have hL : (B₀ x₀).IsInvertible := ContinuousLinearMap.isInvertible_of_injective <|
    (injective_iff_map_eq_zero (B₀ x₀)).2 fun v hv ↦
      hnd v fun w ↦ by rw [← ContinuousAlternatingMap.flatL_apply_apply, hv]; rfl
  -- The source and target of `flatL` are given explicitly, so that their normed instances are used.
  have hflat := ContinuousLinearMap.contDiff (𝕜 := ℝ) (n := r) (E := V [⋀^Fin 2]→L[ℝ] ℝ)
    (F := V →L[ℝ] V →L[ℝ] ℝ) (ContinuousAlternatingMap.flatL ℝ V ℝ)
  obtain ⟨T, U, X, hT, hU, hTI, hxU, hUW, hX, hXeq⟩ := exists_contDiffOn_moserField hL hW hx₀
    (hflat.comp_contDiffOn hω₀) (hflat.comp_contDiffOn hω₁) rfl (congrArg _ heq)
    (e.contDiff.comp_contDiffOn hα)
  -- The Moser field vanishes wherever `α` does.
  have hXα (t : ℝ) (ht : t ∈ T) (y : V) (hy : y ∈ U) (hαy : α y = 0) : X (t, y) = 0 :=
    ((hXeq (t, y) ⟨ht, hy⟩ 0).1 fun w ↦ by simp [hαy]).symm
  -- Read the bilinear Moser equation back as an equation of one-forms.
  have hXω (p : ℝ × V) (hp : p ∈ T ×ˢ U) :
      ((1 - p.1) • ω₀ p.2 + p.1 • ω₁ p.2).curryLeft (X p) = -α p.2 := by
    have hp' := (hXeq p hp (X p)).2 rfl
    ext m
    have hm : m = ![m 0] := by
      funext i
      rw [Subsingleton.elim i 0]
      rfl
    rw [hm, ContinuousAlternatingMap.curryLeft_apply_apply, ContinuousAlternatingMap.neg_apply,
      ← he (α p.2) ![m 0]]
    simpa [B₀, B₁] using hp' (m 0)
  -- The Moser field is equivariant at the points `y` with `y, ρ g y ∈ U`.
  have hXρ (t : ℝ) (ht : t ∈ T) (g : G) (y : V) (hy : y ∈ U) (hgy : ρ g y ∈ U) :
      X (t, ρ g y) = ρ g (X (t, y)) := by
    -- Every vector is `ρ g u` for `u = ρ g⁻¹ w`.
    have hρs : Function.Surjective (ρ g) := fun w ↦
      ⟨ρ g⁻¹ w, by rw [← mul_apply_eq_comp, ← map_mul, mul_inv_cancel, map_one, one_apply_eq_self]⟩
    refine moserField_map_eq hXeq ht hρs hy hgy (fun v w ↦ ?_) fun w ↦ ?_
    · have hvw : ρ g ∘ ![v, w] = ![ρ g v, ρ g w] := by
        funext i
        fin_cases i <;> rfl
      have h₀ := congrArg (· ![v, w]) (hω₀ρ g y (hUW hy))
      have h₁ := congrArg (· ![v, w]) (hω₁ρ g y (hUW hy))
      simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply, hvw] at h₀ h₁
      simp [ContinuousAlternatingMap.flatL_apply_apply, h₀, h₁]
    · have h := congrArg (· ![w]) (hαρ g y (hUW hy))
      simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply] at h
      -- `e a w` is `a ![w]`, and `ρ g ∘ ![w]` evaluates at `0` to `ρ g w`.
      exact (he _ (ρ g ∘ ![w])).trans (h.trans (he _ ![w]).symm)
  -- A closed ball on which the field is Lipschitz, uniformly in time, and an invariant open
  -- neighbourhood `U₂` inside it.
  obtain ⟨ε, hε, hεU⟩ := nhds_basis_closedBall.mem_iff.1 (hU.mem_nhds hxU)
  obtain ⟨U₂, ⟨hU₂o, -, hxU₂, hU₂ρ⟩, hU₂ε⟩ := hbasis.mem_iff.1 (ball_mem_nhds x₀ hε)
  have hU₂U : U₂ ⊆ U := hU₂ε.trans (ball_subset_closedBall.trans hεU)
  obtain ⟨K, hK⟩ := (hX.mono (prod_mono hTI hεU)).exists_lipschitzOnWith hr0
    ((convex_Icc 0 1).prod (convex_closedBall x₀ ε))
    (isCompact_Icc.prod (isCompact_closedBall x₀ ε))
  have hKt (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      LipschitzOnWith K (fun y ↦ X (t, y)) (closedBall x₀ ε) := by
    have hKt := hK.comp (LipschitzWith.prodMk_left t).lipschitzOnWith fun y hy ↦ ⟨ht, hy⟩
    rw [mul_one] at hKt
    exact hKt
  -- The time-dependent flow of the Moser field, and an invariant neighbourhood `U₃` of `x₀` on
  -- which its orbits up to time one stay in `U₂`.
  obtain ⟨ψ, ψ', hψ, hψ', hψl, hψr, hψ0, hψfix, hev⟩ :=
    exists_eventually_forall_hasDerivAt_fderiv_of_contDiffOn (X := fun t y ↦ X (t, y)) hr hT hU₂o
      hTI hxU₂ (hX.mono (prod_mono subset_rfl hU₂U)) fun t ht ↦ hXα t ht x₀ hxU hα₀
  obtain ⟨U₃, ⟨hU₃o, -, hxU₃, hU₃ρ⟩, hU₃⟩ := hbasis.mem_iff.1 hev
  have hU₃U₂ : U₃ ⊆ U₂ := fun x hx ↦ by
    simpa [hψ0] using ((hU₃ hx) 0 ⟨le_rfl, zero_le_one⟩).1
  refine ⟨⟨⟨ψ 1, ψ', hψl, hψr⟩, hψ.contMDiff, hψ'.contMDiff⟩, U₃, hU₃o, hxU₃,
    hU₃U₂.trans (hU₂U.trans hUW), hU₃ρ, fun y hy hαy ↦ ?_, fun g x hx ↦ ?_, fun x hx ↦ ?_⟩
  · exact hψfix y (fun t ht ↦ hXα t ht y (hU₂U (hU₃U₂ hy)) hαy) 1
  · -- `t ↦ ρ g (ψₜ x)` and `t ↦ ψₜ (ρ g x)` solve the same ODE from `ρ g x`.
    have hx' := hU₃ hx
    have hgx := hU₃ (hU₃ρ g hx)
    have hf (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
        HasDerivAt (fun s ↦ ρ g (ψ s x)) (X (t, ρ g (ψ t x))) t := by
      rw [hXρ t (hTI ht) g _ (hU₂U (hx' t ht).1) (hU₂U (hU₂ρ g (hx' t ht).1))]
      exact (ρ g).hasFDerivAt.comp_hasDerivAt t (hx' t ht).2.1
    have hEq := ODE_solution_unique_of_mem_Icc_right (v := fun t y ↦ X (t, y))
      (s := fun _ ↦ closedBall x₀ ε) (fun t ht ↦ hKt t (Ico_subset_Icc_self ht))
      (fun t ht ↦ (hf t ht).continuousAt.continuousWithinAt)
      (fun t ht ↦ (hf t (Ico_subset_Icc_self ht)).hasDerivWithinAt)
      (fun t ht ↦ ball_subset_closedBall
        (hU₂ε (hU₂ρ g (hx' t (Ico_subset_Icc_self ht)).1)))
      (fun t ht ↦ (hgx t ht).2.1.continuousAt.continuousWithinAt)
      (fun t ht ↦ (hgx t (Ico_subset_Icc_self ht)).2.1.hasDerivWithinAt)
      (fun t ht ↦ ball_subset_closedBall (hU₂ε (hgx t (Ico_subset_Icc_self ht)).1))
      (by simp [hψ0])
    exact (hEq ⟨zero_le_one, le_rfl⟩).symm
  -- Moser's identity along the flow: `ψ₁^* ω₁ = ψ₀^* ω₀ = ω₀`.
  have hx' := hU₃ hx
  have hmem (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : ψ t x ∈ U := hU₂U (hx' t ht).1
  have h := compContinuousLinearMap_fderiv_eq_of_curryLeft_eq_neg (ω₀ := ω₀) (ω₁ := ω₁)
    (α := α) (ψ := ψ) (X := fun t y ↦ X (t, y)) (x := x)
    (fun t ht ↦ (hω₀.differentiableOn hr0).differentiableAt (hW.mem_nhds (hUW (hmem t ht))))
    (fun t ht ↦ (hω₁.differentiableOn hr0).differentiableAt (hW.mem_nhds (hUW (hmem t ht))))
    (fun t ht ↦ hdω₀ _ (hUW (hmem t ht))) (fun t ht ↦ hdω₁ _ (hUW (hmem t ht)))
    (fun t ht ↦ hdα _ (hUW (hmem t ht)))
    (fun t ht ↦ Filter.mem_of_superset (hU.mem_nhds (hmem t ht)) fun y hy ↦
      hXω (t, y) ⟨hTI ht, hy⟩)
    (fun t ht ↦ ((hX.differentiableOn hr0).differentiableAt
      ((hT.prod hU).mem_nhds ⟨hTI ht, hmem t ht⟩)).comp (ψ t x)
        ((differentiableAt_const t).prodMk differentiableAt_id))
    (fun t ht ↦ (hx' t ht).2.1) (fun t ht ↦ (hx' t ht).2.2)
  rw [hψ0, fderiv_id] at h
  refine h.trans ?_
  ext v
  simp

/-- **Darboux's theorem**, equivariant form. Let a group `G` act on a finite-dimensional real
normed space through a continuous representation `ρ` whose operators form a bounded set (for
instance a finite group, or a compact group acting continuously), fixing a point `x₀`. A closed
`C^r` two-form `ω` (`r ≥ 1`) on an open set `W ∋ x₀`, invariant under every `ρ g` at the points of
`W` and nondegenerate at `x₀`, is constant in equivariant coordinates near `x₀`: there is a `C^r`
diffeomorphism `ψ` of the space fixing `x₀` and a `ρ`-invariant open neighbourhood `U ⊆ W` of `x₀`
such that `ψ` commutes with every `ρ g` on `U` and the pullback `ψ^* ω` equals the constant form
`ω(x₀)` on `U`. -/
theorem exists_equivariant_diffeomorph_compContinuousLinearMap_fderiv_eq
    (hρ : Bornology.IsBounded (range ρ)) {ω : V → V [⋀^Fin 2]→L[ℝ] ℝ} {W : Set V} {x₀ : V}
    (hρx₀ : ∀ g, ρ g x₀ = x₀) {r : ℕ∞} (hr : 1 ≤ r) (hW : IsOpen W) (hx₀ : x₀ ∈ W)
    (hω : ContDiffOn ℝ r ω W) (hdω : ∀ x ∈ W, extDeriv ω x = 0)
    (hnd : ∀ v, (∀ w, ω x₀ ![v, w] = 0) → v = 0)
    (hωρ : ∀ g, ∀ y ∈ W, (ω (ρ g y)).compContinuousLinearMap (ρ g) = ω y) :
    ∃ (ψ : V ≃ₘ^r⟮𝓘(ℝ, V), 𝓘(ℝ, V)⟯ V) (U : Set V), IsOpen U ∧ x₀ ∈ U ∧ U ⊆ W ∧
      (∀ g, MapsTo (ρ g) U U) ∧ ψ x₀ = x₀ ∧ (∀ g, ∀ x ∈ U, ψ (ρ g x) = ρ g (ψ x)) ∧
      ∀ x ∈ U, (ω (ψ x)).compContinuousLinearMap (fderiv ℝ ψ x) = ω x₀ := by
  -- An invariant primitive of `ω - ω x₀`, vanishing at `x₀`, on an invariant convex
  -- neighbourhood of `x₀` (the invariant Poincaré lemma).
  obtain ⟨U₀, ⟨hU₀o, hU₀c, hxU₀, hU₀ρ⟩, hU₀W⟩ :=
    (ContRepresentation.nhds_basis_isOpen_convex_mapsTo ρ hρ hρx₀).mem_iff.1 (hW.mem_nhds hx₀)
  have hconst (g : G) : (ω x₀).compContinuousLinearMap (ρ g) = ω x₀ := by
    simpa [hρx₀ g] using hωρ g x₀ hx₀
  have hηc : ∀ y ∈ U₀, extDeriv (fun x ↦ ω x - ω x₀) y = 0 := fun y hy ↦ by
    simpa only [extDeriv, fderiv_sub_const] using hdω y (hU₀W hy)
  obtain ⟨α, hα, hα₀, hαρ, hdα⟩ :=
    (hU₀c.starConvex hxU₀).exists_invariant_contDiffOn_forall_extDeriv_eq hU₀o hρx₀ hU₀ρ hr
      ((hω.mono hU₀W).sub contDiffOn_const) hηc fun g y hy ↦ by
      ext m
      have h₁ := congrArg (· m) (hωρ g y (hU₀W hy))
      have h₂ := congrArg (· m) (hconst g)
      simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply] at h₁ h₂ ⊢
      simp [h₁, h₂]
  -- Equivariant Moser's lemma for the constant form `ω x₀` and `ω`.
  obtain ⟨ψ, U, hUo, hxU, hUU₀, hUρ, hfix, hψρ, hψ⟩ :=
    exists_equivariant_diffeomorph_compContinuousLinearMap_fderiv_eq_of_extDeriv_eq
      (ω₀ := fun _ ↦ ω x₀) hρ hρx₀ hr hU₀o hxU₀ contDiffOn_const (hω.mono hU₀W) hα
      (fun x _ ↦ by
        rw [extDeriv, fderiv_const_apply,
          ← ContinuousAlternatingMap.alternatizeUncurryFinCLM_apply, map_zero])
      (fun x hx ↦ hdω x (hU₀W hx)) hdα hα₀ rfl hnd (fun g _ _ ↦ hconst g)
      (fun g y hy ↦ hωρ g y (hU₀W hy)) hαρ
  exact ⟨ψ, U, hUo, hxU, hUU₀.trans hU₀W, hUρ, hfix x₀ hxU hα₀, hψρ, hψ⟩

end Equivariant

/-- **Moser's lemma**, local form. Let `ω₀`, `ω₁` be closed `C^r` two-forms (`r ≥ 1`) on an open
subset `W` of a finite-dimensional real normed space, with `ω₁ - ω₀ = dα` on `W` for a `C^r`
one-form `α` vanishing at `x₀ ∈ W`. If `ω₀` and `ω₁` agree at `x₀` and are nondegenerate there,
then some `C^r` diffeomorphism `ψ` of the space pulls `ω₁` back to `ω₀` on a neighbourhood of `x₀`.
Moreover `ψ` fixes, near `x₀`, every point at which `α` vanishes; in particular `ψ x₀ = x₀`. -/
theorem exists_diffeomorph_eventually_compContinuousLinearMap_fderiv_eq_of_extDeriv_eq
    {ω₀ ω₁ : V → V [⋀^Fin 2]→L[ℝ] ℝ} {α : V → V [⋀^Fin 1]→L[ℝ] ℝ} {W : Set V} {x₀ : V}
    {r : ℕ∞} (hr : 1 ≤ r) (hW : IsOpen W) (hx₀ : x₀ ∈ W) (hω₀ : ContDiffOn ℝ r ω₀ W)
    (hω₁ : ContDiffOn ℝ r ω₁ W) (hα : ContDiffOn ℝ r α W) (hdω₀ : ∀ x ∈ W, extDeriv ω₀ x = 0)
    (hdω₁ : ∀ x ∈ W, extDeriv ω₁ x = 0) (hdα : ∀ x ∈ W, extDeriv α x = ω₁ x - ω₀ x)
    (hα₀ : α x₀ = 0) (heq : ω₁ x₀ = ω₀ x₀) (hnd : ∀ v, (∀ w, ω₀ x₀ ![v, w] = 0) → v = 0) :
    ∃ ψ : V ≃ₘ^r⟮𝓘(ℝ, V), 𝓘(ℝ, V)⟯ V, (∀ᶠ x in 𝓝 x₀, α x = 0 → ψ x = x) ∧
      ∀ᶠ x in 𝓝 x₀, (ω₁ (ψ x)).compContinuousLinearMap (fderiv ℝ ψ x) = ω₀ x := by
  obtain ⟨ψ, U, hUo, hxU, -, -, hfix, -, hψ⟩ :=
    exists_equivariant_diffeomorph_compContinuousLinearMap_fderiv_eq_of_extDeriv_eq
      (ρ := ContRepresentation.trivial ℝ Unit V) (finite_range _).isBounded (fun _ ↦ rfl) hr hW
      hx₀ hω₀ hω₁ hα hdω₀ hdω₁ hdα hα₀ heq hnd (fun _ _ _ ↦ by ext; simp [Function.comp_def])
      (fun _ _ _ ↦ by ext; simp [Function.comp_def]) (fun _ _ _ ↦ by ext; simp [Function.comp_def])
  exact ⟨ψ, eventually_of_mem (hUo.mem_nhds hxU) hfix, eventually_of_mem (hUo.mem_nhds hxU) hψ⟩

/-- **Darboux's theorem.** A closed `C^r` two-form `ω` (`r ≥ 1`) on an open subset of a
finite-dimensional real normed space, nondegenerate at `x₀`, is constant in suitable coordinates
near `x₀`: there is a `C^r` diffeomorphism `ψ` of the space fixing `x₀` such that the pullback
`ψ^* ω` equals the constant form `ω(x₀)` on a neighbourhood of `x₀`. -/
theorem exists_diffeomorph_eventually_compContinuousLinearMap_fderiv_eq
    {ω : V → V [⋀^Fin 2]→L[ℝ] ℝ} {W : Set V} {x₀ : V} {r : ℕ∞} (hr : 1 ≤ r) (hW : IsOpen W)
    (hx₀ : x₀ ∈ W) (hω : ContDiffOn ℝ r ω W) (hdω : ∀ x ∈ W, extDeriv ω x = 0)
    (hnd : ∀ v, (∀ w, ω x₀ ![v, w] = 0) → v = 0) :
    ∃ ψ : V ≃ₘ^r⟮𝓘(ℝ, V), 𝓘(ℝ, V)⟯ V, ψ x₀ = x₀ ∧
      ∀ᶠ x in 𝓝 x₀, (ω (ψ x)).compContinuousLinearMap (fderiv ℝ ψ x) = ω x₀ := by
  obtain ⟨ψ, U, hUo, hxU, -, -, hψx₀, -, hψ⟩ :=
    exists_equivariant_diffeomorph_compContinuousLinearMap_fderiv_eq
      (ρ := ContRepresentation.trivial ℝ Unit V) (finite_range _).isBounded (fun _ ↦ rfl) hr hW
      hx₀ hω hdω hnd (fun _ _ _ ↦ by ext; simp [Function.comp_def])
  exact ⟨ψ, hψx₀, eventually_of_mem (hUo.mem_nhds hxU) hψ⟩

/-- **Darboux's theorem, centred inverse form.** In the situation of
`exists_diffeomorph_eventually_compContinuousLinearMap_fderiv_eq`, subtracting `x₀` from the inverse
of the diffeomorphism gives a `C^r` diffeomorphism `Φ` of the space with `Φ x₀ = 0` such that the
form `ω` is, on an open neighbourhood `V₀ ⊆ W` of `x₀`, the pullback of the constant form `ω(x₀)`
by `Φ`. -/
theorem exists_diffeomorph_centered_forall_mem_eq_compContinuousLinearMap_fderiv
    {ω : V → V [⋀^Fin 2]→L[ℝ] ℝ} {W : Set V} {x₀ : V} {r : ℕ∞} (hr : 1 ≤ r) (hW : IsOpen W)
    (hx₀ : x₀ ∈ W) (hω : ContDiffOn ℝ r ω W) (hdω : ∀ x ∈ W, extDeriv ω x = 0)
    (hnd : ∀ v, (∀ w, ω x₀ ![v, w] = 0) → v = 0) :
    ∃ (Φ : V ≃ₘ^r⟮𝓘(ℝ, V), 𝓘(ℝ, V)⟯ V) (V₀ : Set V), Φ x₀ = 0 ∧ IsOpen V₀ ∧ x₀ ∈ V₀ ∧
      V₀ ⊆ W ∧ ∀ y ∈ V₀, ω y = (ω x₀).compContinuousLinearMap (fderiv ℝ Φ y) := by
  obtain ⟨ψ, hψx₀, hev⟩ :=
    exists_diffeomorph_eventually_compContinuousLinearMap_fderiv_eq hr hW hx₀ hω hdω hnd
  have hψsymm : ψ.symm x₀ = x₀ := ψ.symm_apply_eq.2 hψx₀.symm
  have hnhds : {y : V | (ω (ψ (ψ.symm y))).compContinuousLinearMap (fderiv ℝ ψ (ψ.symm y)) =
      ω x₀} ∩ W ∈ 𝓝 x₀ := by
    refine Filter.inter_mem ?_ (hW.mem_nhds hx₀)
    have hcont : ContinuousAt ψ.symm x₀ := ψ.symm.continuous.continuousAt
    rw [ContinuousAt, hψsymm] at hcont
    exact hcont hev
  obtain ⟨V₀, hV₀_sub, hV₀_open, hx₀V₀⟩ := _root_.mem_nhds_iff.1 hnhds
  have hr0 : (r : WithTop ℕ∞) ≠ 0 := by
    have : (1 : WithTop ℕ∞) ≤ r := by exact_mod_cast hr
    exact (lt_of_lt_of_le zero_lt_one this).ne'
  let Φ : V ≃ₘ^r⟮𝓘(ℝ, V), 𝓘(ℝ, V)⟯ V :=
    ψ.symm.trans (Diffeomorph.smulAdd r (1 : ℝ) (-x₀) one_ne_zero)
  have hΦ_coe : ⇑Φ = fun y ↦ ψ.symm y - x₀ := by
    ext y
    simp [Φ, sub_eq_add_neg]
  refine ⟨Φ, V₀, by rw [hΦ_coe]; simp [hψsymm], hV₀_open, hx₀V₀, fun y hy ↦ (hV₀_sub hy).2,
    fun y hy ↦ ?_⟩
  have hzy : (ω y).compContinuousLinearMap (fderiv ℝ ψ (ψ.symm y)) = ω x₀ := by
    have := (hV₀_sub hy).1
    simpa only [mem_ofPred_eq, ψ.apply_symm_apply] using this
  rw [hΦ_coe, fderiv_sub_const, ← hzy]
  ext v
  simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply]
  congr 1
  ext i
  exact (ψ.fderiv_apply_fderiv_symm_apply hr0 y (v i)).symm

end TauCeti
