/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.DifferentialForm.Basic
public import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Analysis.Calculus.AddTorsor.AffineMap
import TauCeti.Analysis.Calculus.DifferentialForm.Const
import TauCeti.Analysis.Calculus.DifferentialForm.Flow
import TauCeti.Analysis.Calculus.DifferentialForm.Regularity
import TauCeti.Analysis.Normed.Module.Alternating.ContactFlat
import TauCeti.Analysis.ODE.ScalarLinear
import TauCeti.Dynamics.Flow.RestPoint

/-!
# The local contact Moser lemma

Let `α₀`, `α₁` be one-forms on an open subset `W` of a finite-dimensional real normed space with
equal values and equal exterior derivatives at `x₀ ∈ W`, `α₁(x₀) = α₀(x₀)` and
`dα₁(x₀) = dα₀(x₀)`, and with `α₀` contact at `x₀`: `α₀(x₀) ≠ 0` and `dα₀(x₀)` is nondegenerate
on `ker α₀(x₀)`. The **contact Moser lemma**
(`TauCeti.exists_diffeomorph_eventually_compContinuousLinearMap_fderiv_eq_smul`) gives a
diffeomorphism `ψ` fixing `x₀` with `ψ^* α₁ = g α₀` near `x₀`, for a positive function `g`.

Along the straight-line family `αₜ = (1 - t) α₀ + t α₁`, the contact flat maps
`v ↦ ι_v dαₜ + αₜ(v) αₜ` (`ContinuousAlternatingMap.contactFlatMap`) agree at `x₀` with an
invertible map, so they stay invertible near `x₀` for all `t ∈ [0, 1]`. Inverting them gives the
Reeb candidate `Rₜ` and the jointly smooth field `Xₜ` solving the horizontal contact-Moser
equations `αₜ(Xₜ) = 0` and `ι_{Xₜ} dαₜ = μₜ αₜ - (α₁ - α₀)`, with `μₜ = (α₁ - α₀)(Rₜ)`. It
vanishes at `x₀`, so its time-dependent flow `ψₜ` exists near `x₀` up to time one
(`TauCeti.exists_eventually_forall_hasDerivAt_fderiv_of_contDiffOn`). By Cartan's formula,
`∂ₜ αₜ + L_{Xₜ} αₜ = μₜ αₜ`, so the pullbacks `ψₜ^* αₜ` solve the scalar linear equation
`P' = (μₜ ∘ ψₜ) P` (`TauCeti.hasDerivAt_compContinuousLinearMap_fderiv`), and the integrating
factor (`TauCeti.eq_exp_integral_smul_of_hasDerivWithinAt_smul`) gives
`ψ₁^* α₁ = exp (∫₀¹ μₜ ∘ ψₜ dt) α₀`.

Forms are Mathlib's continuous alternating maps, with Mathlib's exterior derivative `extDeriv`,
and the pullback of `α` along `ψ` at `x` is `(α (ψ x)).compContinuousLinearMap (fderiv ℝ ψ x)`.
Nothing is assumed away from a neighbourhood of `x₀`; the diffeomorphism is global only because
the Moser field is cut off away from `x₀`. This is the local, finite-regularity counterpart on a
model space of the horizontal contact-Moser vector field
`TauCeti.SmoothForm.contactMoserVectorField` of `TauCeti.Geometry.Contact.Moser`.

## Main results

* `TauCeti.exists_diffeomorph_eventually_compContinuousLinearMap_fderiv_eq_smul`: the contact
  Moser lemma, `ψ^* α₁ = g α₀` near `x₀` with `g > 0`.

## References

* H. Geiges, *An Introduction to Contact Topology*, Cambridge University Press, 2008,
  Theorem 2.2.2 (the Moser argument in Gray stability).
* D. McDuff and D. Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford, 2017,
  Section 3.2 (Moser's argument).
-/

public section

open Set Filter Topology ContinuousAlternatingMap
open scoped Manifold

namespace TauCeti

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-! ### The local contact Moser field -/

/-- **Gray's equation along the straight-line family.** Let `αₜ = (1 - t) α₀ + t α₁`. If the
field `X` lies in `ker αₜ` near `y` and `ι_X dαₜ = μ αₜ - (α₁ - α₀)` at `y`, then
`∂ₜ αₜ + L_X αₜ = μ αₜ` at `y`. -/
private theorem deriv_add_lieDerivForm_lineFamily {α₀ α₁ : V → V [⋀^Fin 1]→L[ℝ] ℝ}
    {X : V → V} {t μ : ℝ} {y : V} (h₀ : DifferentiableAt ℝ α₀ y)
    (h₁ : DifferentiableAt ℝ α₁ y) (hX : DifferentiableAt ℝ X y)
    (hker : ∀ᶠ z in 𝓝 y, ((1 - t) • α₀ z + t • α₁ z) ![X z] = 0)
    (hι : ((1 - t) • extDeriv α₀ y + t • extDeriv α₁ y).curryLeft (X y) =
      μ • ((1 - t) • α₀ y + t • α₁ y) - (α₁ y - α₀ y)) :
    deriv (fun s ↦ (1 - s) • α₀ y + s • α₁ y) t +
        lieDerivForm X (fun z ↦ (1 - t) • α₀ z + t • α₁ z) y =
      μ • ((1 - t) • α₀ y + t • α₁ y) := by
  -- The time derivative of the family is `α₁ - α₀`.
  have hdt : deriv (fun s ↦ (1 - s) • α₀ y + s • α₁ y) t = α₁ y - α₀ y := by
    have hd : HasDerivAt (fun s ↦ (1 - s) • α₀ y + s • α₁ y)
        ((-1 : ℝ) • α₀ y + (1 : ℝ) • α₁ y) t :=
      (((hasDerivAt_id t).const_sub 1).smul_const (α₀ y)).add
        ((hasDerivAt_id t).smul_const (α₁ y))
    rw [hd.deriv]
    module
  -- Cartan's formula: `αₜ(X) = 0` near `y`, so `L_X αₜ = ι_X dαₜ`.
  have h₀' : DifferentiableAt ℝ ((1 - t) • α₀) y := h₀.const_smul _
  have h₁' : DifferentiableAt ℝ (t • α₁) y := h₁.const_smul _
  have hd : extDeriv (fun z ↦ (1 - t) • α₀ z + t • α₁ z) y =
      (1 - t) • extDeriv α₀ y + t • extDeriv α₁ y := by
    have e : (fun z ↦ (1 - t) • α₀ z + t • α₁ z) = (1 - t) • α₀ + t • α₁ := rfl
    rw [e, extDeriv_add h₀' h₁', extDeriv_smul, extDeriv_smul]
  have hιz : (fun z ↦ ((1 - t) • α₀ z + t • α₁ z).curryLeft (X z)) =ᶠ[𝓝 y] fun _ ↦ 0 := by
    filter_upwards [hker] with z hz
    ext m
    rw [curryLeft_apply_apply, ContinuousAlternatingMap.coe_zero, Pi.zero_apply]
    have hm : Matrix.vecCons (X z) m = ![X z] := by
      funext i
      rw [Subsingleton.elim i 0]
      rfl
    rw [hm]
    exact hz
  have hFt : DifferentiableAt ℝ (fun z ↦ (1 - t) • α₀ z + t • α₁ z) y := h₀'.add h₁'
  rw [lieDerivForm_eq_curryLeft_extDeriv_add hFt hX, hdt, hd, hιz.extDeriv_eq,
    congrFun (extDeriv_const 0) y, hι]
  simp only [Pi.zero_apply, add_zero, add_sub_cancel]

variable [FiniteDimensional ℝ V]

/-- The contact flat maps of a continuous family `(aₚ, ωₚ)`, equal to a contact pair `(a₀, ω₀)`
along `[0, 1] × {x₀}`, stay invertible, with a Reeb candidate on which `aₚ` does not vanish, on a
product neighbourhood of `[0, 1] × {x₀}`. -/
private theorem exists_tube_isInvertible_contactFlatMap {a : ℝ × V → V [⋀^Fin 1]→L[ℝ] ℝ}
    {ω : ℝ × V → V [⋀^Fin 2]→L[ℝ] ℝ} {W : Set V} {x₀ : V} {a₀ : V [⋀^Fin 1]→L[ℝ] ℝ}
    {ω₀ : V [⋀^Fin 2]→L[ℝ] ℝ} (hW : IsOpen W) (hx₀ : x₀ ∈ W)
    (ha : ContinuousOn a (univ ×ˢ W)) (hω : ContinuousOn ω (univ ×ˢ W))
    (ha₀ : ∀ t, a (t, x₀) = a₀) (hω₀ : ∀ t, ω (t, x₀) = ω₀) (hne : a₀ ≠ 0)
    (hnd : ∀ v, a₀ ![v] = 0 → (∀ w, a₀ ![w] = 0 → ω₀ ![v, w] = 0) → v = 0) :
    ∃ (T : Set ℝ) (U : Set V), IsOpen T ∧ IsOpen U ∧ Icc 0 1 ⊆ T ∧ x₀ ∈ U ∧ U ⊆ W ∧
      ∀ p ∈ T ×ˢ U, (contactFlatMap (a p) (ω p)).IsInvertible ∧
        a p ![(contactFlatMap (a p) (ω p)).inverse (toDual (a p))] ≠ 0 := by
  set A : ℝ × V → V →L[ℝ] V →L[ℝ] ℝ := fun p ↦ contactFlatMap (a p) (ω p) with hA_def
  have hAc : ContinuousOn A (univ ×ˢ W) :=
    (contDiffOn_contactFlatMap (contDiffOn_zero.2 ha) (contDiffOn_zero.2 hω)).continuousOn
  have hA₀ := isInvertible_contactFlatMap hne hnd
  -- The set where the contact flat map is invertible and the Reeb candidate is transverse.
  let N : Set (ℝ × V) :=
    {p | p.2 ∈ W ∧ (A p).IsInvertible ∧ a p ![(A p).inverse (toDual (a p))] ≠ 0}
  have hN : IsOpen N := by
    rw [isOpen_iff_mem_nhds]
    rintro p ⟨hpW, hpA, hp0⟩
    have hpn : univ ×ˢ W ∈ 𝓝 p := (isOpen_univ.prod hW).mem_nhds ⟨mem_univ _, hpW⟩
    have hAp : ContinuousAt A p := hAc.continuousAt hpn
    have hap : ContinuousAt a p := ha.continuousAt hpn
    have hinv : ContinuousAt (fun q ↦ (A q).inverse) p :=
      (hpA.contDiffAt_map_inverse (n := 0)).continuousAt.comp hAp
    have hf : ContinuousAt (fun q ↦ a q ![(A q).inverse (toDual (a q))]) p := by
      have h := (toDual.continuous.continuousAt.comp hap).clm_apply
        (hinv.clm_apply (toDual.continuous.continuousAt.comp hap))
      refine h.congr (Eventually.of_forall fun q ↦ ?_)
      simp [toDual_apply]
    exact inter_mem ((hW.preimage continuous_snd).mem_nhds hpW) <| inter_mem
      (hAp (ContinuousLinearMap.isOpen_setOfPred_isInvertible.mem_nhds hpA))
      (hf (isOpen_ne.mem_nhds hp0))
  have hline : Icc (0 : ℝ) 1 ×ˢ {x₀} ⊆ N := by
    rintro p ⟨-, hp⟩
    have hpx : p = (p.1, x₀) := Prod.ext rfl (mem_singleton_iff.1 hp)
    rw [hpx]
    have hAt : A (p.1, x₀) = contactFlatMap a₀ ω₀ := by simp only [hA_def, ha₀, hω₀]
    refine ⟨hx₀, by rw [hAt]; exact hA₀, ?_⟩
    rw [hAt, ha₀]
    exact apply_ne_zero_of_contactFlatMap_apply_eq hne hnd (hA₀.self_apply_inverse _)
  obtain ⟨T, U, hT, hU, hIT, hxU, hTU⟩ :=
    generalized_tube_lemma isCompact_Icc isCompact_singleton hN hline
  exact ⟨T, U ∩ W, hT, hU.inter hW, hIT, ⟨hxU (mem_singleton x₀), hx₀⟩, inter_subset_right,
    fun p hp ↦ (hTU ⟨hp.1, hp.2.1⟩).2⟩

/-- **The local contact Moser field.** Let `α₀`, `α₁` be `C^(r+1)` one-forms on an open set `W`
with equal values and exterior derivatives at `x₀ ∈ W`, `α₁(x₀) = α₀(x₀)` and
`dα₁(x₀) = dα₀(x₀)`, with `α₀` contact at `x₀`. Along the straight-line family
`αₜ = (1 - t) α₀ + t α₁`, there is a jointly `C^r` field `Xₜ` on an open time neighbourhood of
`[0, 1]` and a neighbourhood of `x₀`, vanishing at `x₀`, and a continuous function `μ`, such that
`αₜ(Xₜ) = 0` and `ι_{Xₜ} dαₜ = μₜ αₜ - (α₁ - α₀)`. -/
private theorem exists_contactMoserField {α₀ α₁ : V → V [⋀^Fin 1]→L[ℝ] ℝ} {W : Set V} {x₀ : V}
    {r : ℕ∞} (hW : IsOpen W) (hx₀ : x₀ ∈ W) (hα₀ : ContDiffOn ℝ (r + 1) α₀ W)
    (hα₁ : ContDiffOn ℝ (r + 1) α₁ W) (heq : α₁ x₀ = α₀ x₀)
    (hdeq : extDeriv α₁ x₀ = extDeriv α₀ x₀) (hne : α₀ x₀ ≠ 0)
    (hnd : ∀ v, α₀ x₀ ![v] = 0 → (∀ w, α₀ x₀ ![w] = 0 → extDeriv α₀ x₀ ![v, w] = 0) → v = 0) :
    ∃ (T : Set ℝ) (U : Set V) (X : ℝ × V → V) (μ : ℝ × V → ℝ),
      IsOpen T ∧ IsOpen U ∧ Icc 0 1 ⊆ T ∧ x₀ ∈ U ∧ U ⊆ W ∧ ContDiffOn ℝ r X (T ×ˢ U) ∧
        ContinuousOn μ (T ×ˢ U) ∧ (∀ t, X (t, x₀) = 0) ∧
        ∀ p ∈ T ×ˢ U, ((1 - p.1) • α₀ p.2 + p.1 • α₁ p.2) ![X p] = 0 ∧
          ((1 - p.1) • extDeriv α₀ p.2 + p.1 • extDeriv α₁ p.2).curryLeft (X p) =
            μ p • ((1 - p.1) • α₀ p.2 + p.1 • α₁ p.2) - (α₁ p.2 - α₀ p.2) := by
  set a : ℝ × V → V [⋀^Fin 1]→L[ℝ] ℝ := fun p ↦ (1 - p.1) • α₀ p.2 + p.1 • α₁ p.2 with ha_def
  set ω : ℝ × V → V [⋀^Fin 2]→L[ℝ] ℝ :=
    fun p ↦ (1 - p.1) • extDeriv α₀ p.2 + p.1 • extDeriv α₁ p.2 with hω_def
  set A : ℝ × V → V →L[ℝ] V →L[ℝ] ℝ := fun p ↦ contactFlatMap (a p) (ω p) with hA_def
  have hr : (r : WithTop ℕ∞) ≤ r + 1 := le_self_add
  have hsnd : MapsTo (Prod.snd : ℝ × V → V) (univ ×ˢ W) W := fun _ hp ↦ (mem_prod.1 hp).2
  have has : ContDiffOn ℝ r a (univ ×ˢ W) := by
    simpa [ha_def, AffineMap.lineMap_apply_module] using ((hα₀.of_le hr).comp contDiffOn_snd
      hsnd).lineMap ((hα₁.of_le hr).comp contDiffOn_snd hsnd) contDiffOn_fst
  have hωs : ContDiffOn ℝ r ω (univ ×ˢ W) := by
    simpa [hω_def, AffineMap.lineMap_apply_module] using
      ((contDiffOn_extDeriv hα₀ hW le_rfl).comp contDiffOn_snd hsnd).lineMap
        ((contDiffOn_extDeriv hα₁ hW le_rfl).comp contDiffOn_snd hsnd) contDiffOn_fst
  have hAs : ContDiffOn ℝ r A (univ ×ˢ W) := contDiffOn_contactFlatMap has hωs
  -- At `x₀` every member of the family is the contact covector `α₀(x₀)` with `dα₀(x₀)`.
  have hax₀ (t : ℝ) : a (t, x₀) = α₀ x₀ := by
    simp only [ha_def, heq, ← add_smul, sub_add_cancel, one_smul]
  have hωx₀ (t : ℝ) : ω (t, x₀) = extDeriv α₀ x₀ := by
    simp only [hω_def, hdeq, ← add_smul, sub_add_cancel, one_smul]
  obtain ⟨T, U, hT, hU, hIT, hxU, hUW, hTU⟩ := exists_tube_isInvertible_contactFlatMap hW hx₀
    has.continuousOn hωs.continuousOn hax₀ hωx₀ hne hnd
  replace hTU : ∀ p ∈ T ×ˢ U, (A p).IsInvertible ∧ a p ![(A p).inverse (toDual (a p))] ≠ 0 := hTU
  have hTUW : T ×ˢ U ⊆ univ ×ˢ W := fun p hp ↦ ⟨mem_univ _, hUW hp.2⟩
  -- The Reeb candidate `R`, the rate `μ` and the Moser field `X`.
  set b : V → V [⋀^Fin 1]→L[ℝ] ℝ := fun x ↦ α₁ x - α₀ x with hb_def
  set R : ℝ × V → V := fun p ↦ (A p).inverse (toDual (a p))
  set μ : ℝ × V → ℝ := fun p ↦ toDual (b p.2) (R p) with hμ_def
  set X : ℝ × V → V := fun p ↦ (A p).inverse (μ p • toDual (a p) - toDual (b p.2)) with hX_def
  have hinv : ContDiffOn ℝ r (fun p ↦ (A p).inverse) (T ×ˢ U) := fun p hp ↦
    (hTU p hp).1.contDiffAt_map_inverse.comp_contDiffWithinAt p (hAs.mono hTUW p hp)
  have hda : ContDiffOn ℝ r (fun p ↦ toDual (a p)) (T ×ˢ U) :=
    (has.mono hTUW).continuousLinearMap_comp (toDual : (V [⋀^Fin 1]→L[ℝ] ℝ) →L[ℝ] V →L[ℝ] ℝ)
  have hdb : ContDiffOn ℝ r (fun p : ℝ × V ↦ toDual (b p.2)) (T ×ˢ U) :=
    (((hα₁.of_le hr).sub (hα₀.of_le hr)).comp contDiffOn_snd
      fun p (hp : p ∈ T ×ˢ U) ↦ hUW hp.2).continuousLinearMap_comp
        (toDual : (V [⋀^Fin 1]→L[ℝ] ℝ) →L[ℝ] V →L[ℝ] ℝ)
  have hRs : ContDiffOn ℝ r R (T ×ˢ U) := hinv.clm_apply hda
  have hμs : ContDiffOn ℝ r μ (T ×ˢ U) := hdb.clm_apply hRs
  have hXs : ContDiffOn ℝ r X (T ×ˢ U) := hinv.clm_apply ((hμs.smul hda).sub hdb)
  refine ⟨T, U, X, μ, hT, hU, hIT, hxU, hUW, hXs, hμs.continuousOn, fun t ↦ ?_, fun p hp ↦ ?_⟩
  · simp [hX_def, hμ_def, hb_def, heq]
  obtain ⟨hpA, hp0⟩ := hTU p hp
  have h := contactMoser_of_contactFlatMap_apply_eq (hpA.self_apply_inverse _) hp0
    (hpA.self_apply_inverse (μ p • toDual (a p) - toDual (b p.2)))
  have hμp : μ p = (α₁ p.2 - α₀ p.2) ![R p] := toDual_apply _ _
  rw [hμp]
  exact h

/-- **The contact Moser lemma**, local form. Let `α₀`, `α₁` be `C^(r+1)` one-forms (`r ≥ 1`) on an
open subset `W` of a finite-dimensional real normed space, with equal values and exterior
derivatives at `x₀ ∈ W`: `α₁(x₀) = α₀(x₀)` and `dα₁(x₀) = dα₀(x₀)`. If `α₀` is a contact form
at `x₀`, that is `α₀(x₀) ≠ 0` and `dα₀(x₀)` is nondegenerate on `ker α₀(x₀)`, then some `C^r`
diffeomorphism `ψ` of the space fixing `x₀` pulls `α₁` back to a positive multiple of `α₀` near
`x₀`: `ψ^* α₁ = g α₀` with `g > 0`. In particular `ψ` carries the contact structure `ker α₀` to
`ker α₁` near `x₀`, preserving coorientations. -/
theorem exists_diffeomorph_eventually_compContinuousLinearMap_fderiv_eq_smul
    {α₀ α₁ : V → V [⋀^Fin 1]→L[ℝ] ℝ} {W : Set V} {x₀ : V} {r : ℕ∞} (hr : 1 ≤ r)
    (hW : IsOpen W) (hx₀ : x₀ ∈ W) (hα₀ : ContDiffOn ℝ (r + 1) α₀ W)
    (hα₁ : ContDiffOn ℝ (r + 1) α₁ W) (heq : α₁ x₀ = α₀ x₀)
    (hdeq : extDeriv α₁ x₀ = extDeriv α₀ x₀) (hne : α₀ x₀ ≠ 0)
    (hnd : ∀ v, α₀ x₀ ![v] = 0 → (∀ w, α₀ x₀ ![w] = 0 → extDeriv α₀ x₀ ![v, w] = 0) → v = 0) :
    ∃ (ψ : V ≃ₘ^r⟮𝓘(ℝ, V), 𝓘(ℝ, V)⟯ V) (g : V → ℝ), ψ x₀ = x₀ ∧
      ∀ᶠ x in 𝓝 x₀, 0 < g x ∧ (α₁ (ψ x)).compContinuousLinearMap (fderiv ℝ ψ x) = g x • α₀ x := by
  obtain ⟨T, U, X, μ, hT, hU, hTI, hxU, hUW, hX, hμ, hX₀, hXeq⟩ :=
    exists_contactMoserField hW hx₀ hα₀ hα₁ heq hdeq hne hnd
  obtain ⟨ψ, ψ', hψ, hψ', hψl, hψr, hψ0, hψfix, hev⟩ :=
    exists_eventually_forall_hasDerivAt_fderiv_of_contDiffOn (X := fun t y ↦ X (t, y)) hr hT hU
      hTI hxU hX fun t _ ↦ hX₀ t
  have hr0 : (r : WithTop ℕ∞) ≠ 0 := by
    have : (1 : WithTop ℕ∞) ≤ r := by exact_mod_cast hr
    exact (lt_of_lt_of_le zero_lt_one this).ne'
  have hr1 : (1 : WithTop ℕ∞) ≤ r + 1 := le_add_self
  let Ψ : V ≃ₘ^r⟮𝓘(ℝ, V), 𝓘(ℝ, V)⟯ V := ⟨⟨ψ 1, ψ', hψl, hψr⟩, hψ.contMDiff, hψ'.contMDiff⟩
  have hsnd : MapsTo (Prod.snd : ℝ × V → V) (univ ×ˢ W) W := fun _ hp ↦ (mem_prod.1 hp).2
  have hF : ContDiffOn ℝ 1 (fun p : ℝ × V ↦ (1 - p.1) • α₀ p.2 + p.1 • α₁ p.2) (univ ×ˢ W) := by
    simpa [AffineMap.lineMap_apply_module] using ((hα₀.of_le hr1).comp contDiffOn_snd
      hsnd).lineMap ((hα₁.of_le hr1).comp contDiffOn_snd hsnd) contDiffOn_fst
  have key : ∀ᶠ x in 𝓝 x₀, ∃ c : ℝ, 0 < c ∧
      (α₁ (Ψ x)).compContinuousLinearMap (fderiv ℝ Ψ x) = c • α₀ x := by
    filter_upwards [hev] with x hx
    -- The pullbacks `Pₜ = ψₜ^* αₜ` along the flow solve `P' = μₜ(ψₜ x) • P`.
    have hP (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
        HasDerivAt (fun s ↦ ((1 - s) • α₀ (ψ s x) + s • α₁ (ψ s x)).compContinuousLinearMap
            (fderiv ℝ (ψ s) x))
          (μ (t, ψ t x) • ((1 - t) • α₀ (ψ t x) + t • α₁ (ψ t x)).compContinuousLinearMap
            (fderiv ℝ (ψ t) x)) t := by
      obtain ⟨hyU, hψt, hDψt⟩ := hx t ht
      set y := ψ t x
      have hp : (t, y) ∈ T ×ˢ U := ⟨hTI ht, hyU⟩
      have hyW : W ∈ 𝓝 y := hW.mem_nhds (hUW hyU)
      have hFd : DifferentiableAt ℝ (fun p : ℝ × V ↦ (1 - p.1) • α₀ p.2 + p.1 • α₁ p.2) (t, y) :=
        (hF.differentiableOn one_ne_zero).differentiableAt
          ((isOpen_univ.prod hW).mem_nhds ⟨mem_univ _, hUW hyU⟩)
      have h := hasDerivAt_compContinuousLinearMap_fderiv
        (ω := fun s z ↦ (1 - s) • α₀ z + s • α₁ z) (X := fun s z ↦ X (s, z)) hFd hψt hDψt
      convert h using 1
      have hXd : DifferentiableAt ℝ (fun z ↦ X (t, z)) y :=
        ((hX.differentiableOn hr0).differentiableAt ((hT.prod hU).mem_nhds hp)).comp y
          ((differentiableAt_const t).prodMk differentiableAt_id)
      rw [deriv_add_lieDerivForm_lineFamily
        (((hα₀.of_le hr1).differentiableOn one_ne_zero).differentiableAt hyW)
        (((hα₁.of_le hr1).differentiableOn one_ne_zero).differentiableAt hyW) hXd
        (Filter.mem_of_superset (hU.mem_nhds hyU) fun z hz ↦ (hXeq (t, z) ⟨hTI ht, hz⟩).1)
        (hXeq (t, y) hp).2]
      ext m
      simp only [compContinuousLinearMap_apply, ContinuousAlternatingMap.smul_apply,
        ContinuousAlternatingMap.add_apply, smul_eq_mul]
    -- The coefficient `μₜ(ψₜ x)` is continuous on `[0, 1]`.
    have hm : ContinuousOn (fun t ↦ μ (t, ψ t x)) (Icc 0 1) := fun t ht ↦
      ((hμ.continuousAt ((hT.prod hU).mem_nhds ⟨hTI ht, (hx t ht).1⟩)).comp
        (continuousAt_id.prodMk (hx t ht).2.1.continuousAt)).continuousWithinAt
    have h := eq_exp_integral_smul_of_hasDerivWithinAt_smul zero_le_one hm
      (P := fun s ↦ ((1 - s) • α₀ (ψ s x) + s • α₁ (ψ s x)).compContinuousLinearMap
        (fderiv ℝ (ψ s) x)) fun t ht ↦ (hP t ht).hasDerivWithinAt
    refine ⟨_, Real.exp_pos (∫ u in (0 : ℝ)..1, μ (u, ψ u x)), ?_⟩
    rw [hψ0] at h
    simp only [sub_zero, one_smul, zero_smul, add_zero, sub_self, zero_add, id_eq, fderiv_id] at h
    refine h.trans ?_
    ext v
    simp
  choose! g hg using fun x (hx : ∃ c : ℝ, 0 < c ∧
    (α₁ (Ψ x)).compContinuousLinearMap (fderiv ℝ Ψ x) = c • α₀ x) ↦ hx
  exact ⟨Ψ, g, hψfix x₀ (fun t _ ↦ hX₀ t) 1, key.mono fun x hx ↦ hg x hx⟩

end TauCeti
