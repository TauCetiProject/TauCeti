/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.DifferentialForm.Basic
public import Mathlib.Geometry.Manifold.Diffeomorph
public import TauCeti.Geometry.Contact.Standard
import Mathlib.Analysis.Calculus.ContDiff.Operations
import TauCeti.Analysis.Calculus.DifferentialForm.Const
import TauCeti.Analysis.Calculus.DifferentialForm.Flow
import TauCeti.Analysis.Calculus.DifferentialForm.Regularity
import TauCeti.Analysis.Normed.Module.Alternating.Curry
import TauCeti.Analysis.ODE.ScalarLinear
import TauCeti.Dynamics.Flow.RestPoint
import TauCeti.Geometry.Manifold.Diffeomorph.NormedSpace
import TauCeti.LinearAlgebra.BilinearForm.Contact.NormalForm
import TauCeti.Topology.Algebra.Module.BilinearForm

/-!
# The contact Darboux theorem

Let `α` be a one-form on an open subset `W` of a finite-dimensional real normed space `V`, of
class `C^(r+1)` with `r ≥ 1`, which is a contact form at `x₀ ∈ W`: `α(x₀) ≠ 0` and `dα(x₀)` is
nondegenerate on the hyperplane `ker α(x₀)`. The **contact Darboux theorem**
(`TauCeti.exists_diffeomorph_eventually_innerProductContactForm_apply_fderiv_eq_mul`) gives a
`C^r` diffeomorphism `Φ : V ≃ ℝⁿ × ℝⁿ × ℝ` with `Φ x₀ = 0` which pulls the standard contact form
`dz - Σᵢ pᵢ dqᵢ` (`TauCeti.innerProductContactForm`) back to `g α` near `x₀`, for a positive
function `g`. So near `x₀` the contact structure `ker α` is the standard one in the coordinates
`Φ`, with matching coorientations. This is the Darboux theorem for the contact structure; the
sharper form-level statement, in which the factor `g` is removed by a further change of
coordinates, is not proved here.

The proof is the contact version of Moser's argument, stated in its local form as the **contact
Moser lemma** (`TauCeti.exists_diffeomorph_eventually_compContinuousLinearMap_fderiv_eq_smul`).
Let `α₀`, `α₁` be one-forms which agree to first order at `x₀`, `α₁(x₀) = α₀(x₀)` and
`dα₁(x₀) = dα₀(x₀)`, with `α₀` contact at `x₀`. Along the straight-line family
`αₜ = (1 - t) α₀ + t α₁`, the contact flat maps `v ↦ ι_v dαₜ + αₜ(v) αₜ` agree at `x₀` with an
invertible map, so they stay invertible near `x₀` for all `t ∈ [0, 1]`. Inverting them gives the
Reeb candidate `Rₜ` and the jointly smooth field `Xₜ` solving the horizontal contact-Moser
equations `αₜ(Xₜ) = 0` and `ι_{Xₜ} dαₜ = μₜ αₜ - (α₁ - α₀)`, with `μₜ = (α₁ - α₀)(Rₜ)`. It
vanishes at `x₀`, so its time-dependent flow `ψₜ` exists near `x₀` up to time one
(`TauCeti.exists_eventually_forall_hasDerivAt_fderiv_of_contDiffOn`). By Cartan's formula,
`∂ₜ αₜ + L_{Xₜ} αₜ = μₜ αₜ`, so the pullbacks `ψₜ^* αₜ` solve the scalar linear equation
`P' = (μₜ ∘ ψₜ) P` (`TauCeti.hasDerivAt_compContinuousLinearMap_fderiv`), and the integrating
factor (`TauCeti.eq_exp_integral_smul_of_hasDerivAt_smul_of_le`) gives
`ψ₁^* α₁ = exp (∫₀¹ μₜ ∘ ψₜ dt) α₀`. For the Darboux theorem, `α₁ = α` and `α₀` is the standard
form pulled back along affine coordinates centred at `x₀` in which `α(x₀)` and `dα(x₀)` are the
standard `dz` and `Σᵢ dqᵢ ∧ dpᵢ` (`Module.Dual.IsContact.exists_linearEquiv_eq_stdContact`).

Forms are Mathlib's continuous alternating maps, with Mathlib's exterior derivative `extDeriv`,
and the pullback of `α` along `ψ` at `x` is `(α (ψ x)).compContinuousLinearMap (fderiv ℝ ψ x)`.
Nothing is assumed away from a neighbourhood of `x₀`; the diffeomorphisms are global only
because the Moser field is cut off away from `x₀`.

## Main results

* `TauCeti.exists_diffeomorph_eventually_compContinuousLinearMap_fderiv_eq_smul`: the contact
  Moser lemma, `ψ^* α₁ = g α₀` near `x₀` with `g > 0`.
* `TauCeti.exists_diffeomorph_eventually_innerProductContactForm_apply_fderiv_eq_mul`: the contact
  Darboux theorem.

## References

* H. Geiges, *An Introduction to Contact Topology*, Cambridge University Press, 2008,
  Theorem 2.2.2 (the Moser argument in Gray stability) and Section 2.5 (Darboux's theorem).
* D. McDuff and D. Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford, 2017,
  Section 3.2 (Moser's argument).
-/

public section

open Set Filter Topology ContinuousAlternatingMap
open scoped Manifold

namespace TauCeti

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-! ### The contact flat map of a covector and a two-form -/

section Flat

/-- A one-form at a point, read as a continuous linear functional. -/
private noncomputable def toDual : (V [⋀^Fin 1]→L[ℝ] ℝ) →L[ℝ] V →L[ℝ] ℝ :=
  (ofSubsingletonLIE (𝕜 := ℝ) (E := V) (F := ℝ) (ι := Fin 1)
    0).symm.toContinuousLinearEquiv.toContinuousLinearMap

private theorem toDual_apply (a : V [⋀^Fin 1]→L[ℝ] ℝ) (v : V) : toDual a v = a ![v] := by
  simp only [toDual, ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
    ofSubsingletonLIE_symm_apply, ofSubsingleton_symm_apply_apply]
  congr 1
  funext i
  rw [Subsingleton.elim i 0]
  rfl

/-- The contact flat map `v ↦ ι_v ω + a(v) a` of a covector `a` and a two-form `ω`, with values
in the dual. -/
private noncomputable def contactFlatMap (a : V [⋀^Fin 1]→L[ℝ] ℝ) (ω : V [⋀^Fin 2]→L[ℝ] ℝ) :
    V →L[ℝ] V →L[ℝ] ℝ :=
  flatL ℝ V ℝ ω + (toDual a).smulRight (toDual a)

private theorem contactFlatMap_apply_apply (a : V [⋀^Fin 1]→L[ℝ] ℝ) (ω : V [⋀^Fin 2]→L[ℝ] ℝ)
    (v w : V) : contactFlatMap a ω v w = ω ![v, w] + a ![v] * a ![w] := by
  simp [contactFlatMap, toDual_apply]

/-- A two-form, read as a bilinear form, is alternating. -/
private theorem isAlt_toLinearMap₁₂_flatL (ω : V [⋀^Fin 2]→L[ℝ] ℝ) :
    LinearMap.BilinForm.IsAlt (flatL ℝ V ℝ ω).toLinearMap₁₂ := fun v ↦ by
  simp [ω.map_eq_zero_of_eq ![v, v] (i := 0) (j := 1) rfl Fin.zero_ne_one]

/-- The pointwise contact condition, `a ≠ 0` with `ω` nondegenerate on `ker a`, as the linear
contact condition `Module.Dual.IsContact`. -/
private theorem isContact_toDual {a : V [⋀^Fin 1]→L[ℝ] ℝ} {ω : V [⋀^Fin 2]→L[ℝ] ℝ} (hne : a ≠ 0)
    (hnd : ∀ v, a ![v] = 0 → (∀ w, a ![w] = 0 → ω ![v, w] = 0) → v = 0) :
    Module.Dual.IsContact (toDual a : V →ₗ[ℝ] ℝ) (flatL ℝ V ℝ ω).toLinearMap₁₂ := by
  refine (Module.Dual.isContact_iff_of_isRefl (isAlt_toLinearMap₁₂_flatL ω).isRefl).2
    ⟨fun h0 ↦ hne ?_, fun v hv hvw ↦ hnd v (by simpa [toDual_apply] using hv) fun w hw ↦ by
      simpa using hvw w (by simpa [toDual_apply] using hw)⟩
  ext m
  have hm : m = ![m 0] := by
    funext i
    rw [Subsingleton.elim i 0]
    rfl
  rw [hm, ← toDual_apply]
  exact LinearMap.congr_fun h0 (m 0)

variable [FiniteDimensional ℝ V] in
/-- At a contact covector `a` for an alternating form `ω`, the contact flat map is invertible. -/
private theorem isInvertible_contactFlatMap {a : V [⋀^Fin 1]→L[ℝ] ℝ} {ω : V [⋀^Fin 2]→L[ℝ] ℝ}
    (hne : a ≠ 0) (hnd : ∀ v, a ![v] = 0 → (∀ w, a ![w] = 0 → ω ![v, w] = 0) → v = 0) :
    (contactFlatMap a ω).IsInvertible := by
  have hsep := (isContact_toDual hne hnd).separatingLeft_add_smulRight
    (isAlt_toLinearMap₁₂_flatL ω)
  refine ContinuousLinearMap.isInvertible_of_injective <|
    (injective_iff_map_eq_zero _).2 fun v hv ↦ hsep v fun w ↦ ?_
  have h := contactFlatMap_apply_apply a ω v w
  rw [hv, zero_apply] at h
  simpa [toDual_apply] using h.symm

/-- The vector `R` with `ι_R ω + a(R) a = a` satisfies the Reeb equations `a(R) = 1`,
`ι_R ω = 0`, as soon as `a(R) ≠ 0`. -/
private theorem reeb_of_contactFlatMap_apply_eq {a : V [⋀^Fin 1]→L[ℝ] ℝ}
    {ω : V [⋀^Fin 2]→L[ℝ] ℝ} {R : V} (hR : contactFlatMap a ω R = toDual a) (h0 : a ![R] ≠ 0) :
    a ![R] = 1 ∧ ∀ w, ω ![R, w] = 0 := by
  have hR' (w : V) : ω ![R, w] + a ![R] * a ![w] = a ![w] := by
    rw [← contactFlatMap_apply_apply, hR, toDual_apply]
  have h1 : a ![R] = 1 := by
    have := hR' R
    rw [ω.map_eq_zero_of_eq ![R, R] (i := 0) (j := 1) rfl Fin.zero_ne_one, zero_add] at this
    exact (mul_eq_left₀ h0).1 this
  exact ⟨h1, fun w ↦ by simpa [h1] using hR' w⟩

/-- At a contact covector `a` for `ω`, the vector `R` solving `ι_R ω + a(R) a = a` is the Reeb
vector, so `a(R) = 1 ≠ 0`. -/
private theorem apply_ne_zero_of_contactFlatMap_apply_eq {a : V [⋀^Fin 1]→L[ℝ] ℝ}
    {ω : V [⋀^Fin 2]→L[ℝ] ℝ} (hne : a ≠ 0)
    (hnd : ∀ v, a ![v] = 0 → (∀ w, a ![w] = 0 → ω ![v, w] = 0) → v = 0) {R : V}
    (hR : contactFlatMap a ω R = toDual a) : a ![R] ≠ 0 := by
  have h := ((isContact_toDual hne hnd).add_smulRight_apply_eq_self_iff
    (isAlt_toLinearMap₁₂_flatL ω) (r := R)).1 <| LinearMap.ext fun w ↦ by
      simpa [toDual_apply, contactFlatMap_apply_apply] using
        (congrArg (fun f : V →L[ℝ] ℝ ↦ f w) hR)
  rw [← toDual_apply]
  exact h.1 ▸ one_ne_zero

/-- **The contact Moser equation, pointwise.** Let `A` be the contact flat map of `a` and `ω`,
let `R` solve `A R = a` with `a(R) ≠ 0`, and let `X` solve `A X = b(R) a - b`. Then `X` lies in
`ker a` and `ι_X ω = b(R) a - b`. -/
private theorem contactMoser_of_contactFlatMap {a b : V [⋀^Fin 1]→L[ℝ] ℝ}
    {ω : V [⋀^Fin 2]→L[ℝ] ℝ} {R X : V} (hR : contactFlatMap a ω R = toDual a) (h0 : a ![R] ≠ 0)
    (hX : contactFlatMap a ω X = toDual b R • toDual a - toDual b) :
    a ![X] = 0 ∧ ω.curryLeft X = b ![R] • a - b := by
  obtain ⟨h1, hRω⟩ := reeb_of_contactFlatMap_apply_eq hR h0
  have hX' (w : V) : ω ![X, w] + a ![X] * a ![w] = b ![R] * a ![w] - b ![w] := by
    rw [← contactFlatMap_apply_apply, hX]
    simp [toDual_apply]
  have hXa : a ![X] = 0 := by
    have := hX' R
    have hswap : ω ![X, R] = -ω ![R, X] := by
      simpa using ω.map_swap ![R, X] (i := 0) (j := 1) Fin.zero_ne_one
    rw [hswap, hRω, neg_zero, zero_add, h1, mul_one, mul_one, sub_self] at this
    exact this
  refine ⟨hXa, ?_⟩
  ext m
  have hm : m = ![m 0] := by
    funext i
    rw [Subsingleton.elim i 0]
    rfl
  rw [curryLeft_apply_apply, hm]
  simpa [hXa] using hX' (m 0)

end Flat

/-! ### The local contact Moser field -/

section Moser

/-- The straight-line family `(t, x) ↦ (1 - t) • β₀ x + t • β₁ x` of two `C^n` families of
alternating maps is jointly `C^n` on `ℝ × W`. -/
private theorem contDiffOn_lineFamily {k : ℕ} {β₀ β₁ : V → V [⋀^Fin k]→L[ℝ] ℝ} {W : Set V}
    {n : WithTop ℕ∞} (h₀ : ContDiffOn ℝ n β₀ W) (h₁ : ContDiffOn ℝ n β₁ W) :
    ContDiffOn ℝ n (fun p : ℝ × V ↦ (1 - p.1) • β₀ p.2 + p.1 • β₁ p.2) (univ ×ˢ W) :=
  ((contDiffOn_const.sub contDiffOn_fst).smul
      (h₀.comp contDiffOn_snd fun _ hp ↦ (mem_prod.1 hp).2)).add
    (contDiffOn_fst.smul (h₁.comp contDiffOn_snd fun _ hp ↦ (mem_prod.1 hp).2))

/-- The contact flat map depends smoothly on the covector and the two-form. -/
private theorem contDiffOn_contactFlatMap {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : WithTop ℕ∞} {s : Set E} {a : E → V [⋀^Fin 1]→L[ℝ] ℝ} {ω : E → V [⋀^Fin 2]→L[ℝ] ℝ}
    (ha : ContDiffOn ℝ n a s) (hω : ContDiffOn ℝ n ω s) :
    ContDiffOn ℝ n (fun p ↦ contactFlatMap (a p) (ω p)) s :=
  (hω.continuousLinearMap_comp (flatL ℝ V ℝ)).add
    ((ha.continuousLinearMap_comp toDual).smulRight (ha.continuousLinearMap_comp toDual))

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
which agree to first order at `x₀ ∈ W`, `α₁(x₀) = α₀(x₀)` and `dα₁(x₀) = dα₀(x₀)`, with `α₀` contact
at `x₀`. Along the straight-line family `αₜ = (1 - t) α₀ + t α₁`, there is a jointly `C^r` field
`Xₜ` on an open time neighbourhood of `[0, 1]` and a neighbourhood of `x₀`, vanishing at `x₀`, and a
continuous function `μ`, such that `αₜ(Xₜ) = 0` and `ι_{Xₜ} dαₜ = μₜ αₜ - (α₁ - α₀)`. -/
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
  have has : ContDiffOn ℝ r a (univ ×ˢ W) := contDiffOn_lineFamily (hα₀.of_le hr) (hα₁.of_le hr)
  have hωs : ContDiffOn ℝ r ω (univ ×ˢ W) :=
    contDiffOn_lineFamily (contDiffOn_extDeriv hα₀ hW le_rfl) (contDiffOn_extDeriv hα₁ hW le_rfl)
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
  have h := contactMoser_of_contactFlatMap (hpA.self_apply_inverse _) hp0
    (hpA.self_apply_inverse (μ p • toDual (a p) - toDual (b p.2)))
  have hμp : μ p = (α₁ p.2 - α₀ p.2) ![R p] := toDual_apply _ _
  rw [hμp]
  exact h

/-- **The contact Moser lemma**, local form. Let `α₀`, `α₁` be `C^(r+1)` one-forms (`r ≥ 1`) on an
open subset `W` of a finite-dimensional real normed space, which agree to first order at
`x₀ ∈ W`: `α₁(x₀) = α₀(x₀)` and `dα₁(x₀) = dα₀(x₀)`. If `α₀` is a contact form at `x₀`, that is
`α₀(x₀) ≠ 0` and `dα₀(x₀)` is nondegenerate on `ker α₀(x₀)`, then some `C^r` diffeomorphism `ψ`
of the space fixing `x₀` pulls `α₁` back to a positive multiple of `α₀` near `x₀`:
`ψ^* α₁ = g α₀` with `g > 0`. In particular `ψ` carries the contact structure `ker α₀` to
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
  have hF : ContDiffOn ℝ 1 (fun p : ℝ × V ↦ (1 - p.1) • α₀ p.2 + p.1 • α₁ p.2) (univ ×ˢ W) :=
    contDiffOn_lineFamily (hα₀.of_le hr1) (hα₁.of_le hr1)
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
    have h := eq_exp_integral_smul_of_hasDerivAt_smul_of_le zero_le_one hm
      (P := fun s ↦ ((1 - s) • α₀ (ψ s x) + s • α₁ (ψ s x)).compContinuousLinearMap
        (fderiv ℝ (ψ s) x)) hP
    refine ⟨_, Real.exp_pos (∫ u in (0 : ℝ)..1, μ (u, ψ u x)), ?_⟩
    rw [hψ0] at h
    simp only [sub_zero, one_smul, zero_smul, add_zero, sub_self, zero_add, id_eq, fderiv_id] at h
    refine h.trans ?_
    ext v
    simp
  choose! g hg using fun x (hx : ∃ c : ℝ, 0 < c ∧
    (α₁ (Ψ x)).compContinuousLinearMap (fderiv ℝ Ψ x) = c • α₀ x) ↦ hx
  exact ⟨Ψ, g, hψfix x₀ (fun t _ ↦ hX₀ t) 1, key.mono fun x hx ↦ hg x hx⟩

end Moser

/-! ### The contact Darboux theorem -/

section Darboux

variable [FiniteDimensional ℝ V]

/-- A covector `a` which is contact for an alternating form `ω` is the standard covector `dz`, and
`ω` the standard form `Σᵢ dqᵢ ∧ dpᵢ`, in suitable linear coordinates `V ≃ ℝⁿ × ℝⁿ × ℝ`. -/
private theorem exists_continuousLinearEquiv_stdContact {a : V [⋀^Fin 1]→L[ℝ] ℝ}
    {ω : V [⋀^Fin 2]→L[ℝ] ℝ} (hne : a ≠ 0)
    (hnd : ∀ v, a ![v] = 0 → (∀ w, a ![w] = 0 → ω ![v, w] = 0) → v = 0) :
    ∃ (n : ℕ) (e : V ≃L[ℝ] EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) × ℝ),
      (∀ v, a ![v] = (e v).2.2) ∧
        ∀ v w, ω ![v, w] = ∑ i, ((e v).1 i * (e w).2.1 i - (e v).2.1 i * (e w).1 i) := by
  let B : LinearMap.BilinForm ℝ V := (flatL ℝ V ℝ ω).toLinearMap₁₂
  have hB (v w : V) : B v w = ω ![v, w] := flatL_apply_apply ω v w
  have hBalt : B.IsAlt := isAlt_toLinearMap₁₂_flatL ω
  have hcon : Module.Dual.IsContact (toDual a : V →ₗ[ℝ] ℝ) B := isContact_toDual hne hnd
  obtain ⟨n, e₁, ha₁, hB₁⟩ := hcon.exists_linearEquiv_eq_stdContact hBalt
  let L := (EuclideanSpace.equiv (Fin n) ℝ).symm
  let e : V ≃L[ℝ] EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) × ℝ :=
    e₁.toContinuousLinearEquiv.trans (L.prodCongr (L.prodCongr (ContinuousLinearEquiv.refl ℝ ℝ)))
  refine ⟨n, e, fun v ↦ ?_, fun v w ↦ ?_⟩
  · have h := LinearMap.congr_fun ha₁ v
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, stdContactCovector_apply,
      ContinuousLinearMap.coe_coe] at h
    rw [← toDual_apply, ← h]
    simp [e]
  · rw [← hB, ← LinearMap.congr_fun₂ hB₁ v w]
    simp [e, L, stdContactBilinForm_apply, dotProduct, Finset.sum_sub_distrib]

/-- **The contact Darboux theorem**, local form. Let `α` be a `C^(r+1)` one-form (`r ≥ 1`) on an
open subset `W` of a finite-dimensional real normed space, which is a contact form at `x₀ ∈ W`:
`α(x₀) ≠ 0` and `dα(x₀)` is nondegenerate on `ker α(x₀)`. Then there are `n` and a `C^r`
diffeomorphism `Φ` of the space onto `ℝⁿ × ℝⁿ × ℝ` with `Φ x₀ = 0` which, near `x₀`, pulls the
standard contact form `dz - Σᵢ pᵢ dqᵢ` back to a positive multiple `g α` of `α`. So `Φ` is a chart
near `x₀` carrying the contact structure `ker α` to the standard one and preserving
coorientations. -/
theorem exists_diffeomorph_eventually_innerProductContactForm_apply_fderiv_eq_mul
    {α : V → V [⋀^Fin 1]→L[ℝ] ℝ} {W : Set V} {x₀ : V} {r : ℕ∞} (hr : 1 ≤ r) (hW : IsOpen W)
    (hx₀ : x₀ ∈ W) (hα : ContDiffOn ℝ (r + 1) α W) (hne : α x₀ ≠ 0)
    (hnd : ∀ v, α x₀ ![v] = 0 → (∀ w, α x₀ ![w] = 0 → extDeriv α x₀ ![v, w] = 0) → v = 0) :
    ∃ (n : ℕ) (Φ : V ≃ₘ^r⟮𝓘(ℝ, V),
        𝓘(ℝ, EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) × ℝ)⟯
        EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) × ℝ) (g : V → ℝ), Φ x₀ = 0 ∧
      ∀ᶠ x in 𝓝 x₀, 0 < g x ∧ ∀ v : V,
        (innerProductContactForm (EuclideanSpace ℝ (Fin n))).1 (Φ x) ![fderiv ℝ Φ x v] =
          g x * α x ![v] := by
  obtain ⟨n, e, hae, hωe⟩ := exists_continuousLinearEquiv_stdContact hne hnd
  set P := EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) × ℝ
  set σ : P → P [⋀^Fin 1]→L[ℝ] ℝ := (innerProductContactForm (EuclideanSpace ℝ (Fin n))).1
  have hσ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) σ :=
    isSmoothForm_modelSpace_iff.1 (innerProductContactForm (EuclideanSpace ℝ (Fin n))).isSmoothForm
  -- The standard form and its exterior derivative, read on the model space itself.
  have hσapp (x v : P) : σ x ![v] = v.2.2 - inner ℝ x.2.1 v.1 :=
    innerProductContactForm_apply _ x v
  have hdσ (u w : P) : extDeriv σ 0 ![u, w] = ∑ i, (u.1 i * w.2.1 i - u.2.1 i * w.1 i) := by
    have h := mextDeriv_innerProductContactForm_euclideanSpace_apply (0 : P) u w
    rw [mextDeriv_eq_extDeriv] at h
    exact h
  have hr0 : (r : WithTop ℕ∞) ≠ 0 := by
    have : (1 : WithTop ℕ∞) ≤ r := by exact_mod_cast hr
    exact (lt_of_lt_of_le zero_lt_one this).ne'
  -- The linear coordinates centred at `x₀`, and the pullback `α₀` of the standard form.
  set f : V → P := fun x ↦ e (x - x₀) with hf_def
  have hfd (x : V) : HasFDerivAt f (e : V →L[ℝ] P) x := by
    simpa [hf_def, Function.comp_def] using
      (e : V →L[ℝ] P).hasFDerivAt.comp x ((hasFDerivAt_id x).sub_const x₀)
  have htop (k : ℕ∞) : (k : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := WithTop.coe_le_coe.2 le_top
  have hfs {k : WithTop ℕ∞} : ContDiff ℝ k f := e.contDiff.comp (contDiff_id.sub contDiff_const)
  set α₀ : V → V [⋀^Fin 1]→L[ℝ] ℝ :=
    fun x ↦ (σ (f x)).compContinuousLinearMap (fderiv ℝ f x) with hα₀_def
  have hα₀e : α₀ = fun x ↦ compContinuousLinearMapCLM (e : V →L[ℝ] P) (σ (f x)) := by
    funext x
    simp only [hα₀_def, (hfd x).fderiv, compContinuousLinearMapCLM_apply]
  have hle : (r : WithTop ℕ∞) + 1 ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by exact_mod_cast htop (r + 1)
  have hα₀s : ContDiffOn ℝ (r + 1) α₀ W := by
    rw [hα₀e]
    exact ((compContinuousLinearMapCLM (e : V →L[ℝ] P)).contDiff.comp
      (hσ.comp hfs)).contDiffOn.of_le hle
  have hfx₀ : f x₀ = 0 := by simp [hf_def]
  -- `α₀` agrees with `α` to first order at `x₀`.
  have hm1 (m : Fin 1 → V) : m = ![m 0] := by
    funext i
    rw [Subsingleton.elim i 0]
    rfl
  have hm2 (m : Fin 2 → V) : m = ![m 0, m 1] := by
    funext i
    fin_cases i <;> rfl
  have hvec1 (v : V) : ⇑(e : V →L[ℝ] P) ∘ ![v] = ![e v] := by
    funext i
    fin_cases i
    rfl
  have hvec2 (v w : V) : ⇑(e : V →L[ℝ] P) ∘ ![v, w] = ![e v, e w] := by
    funext i
    fin_cases i <;> rfl
  have hα₀x₀ : α₀ x₀ = α x₀ := by
    ext m
    simp only [hα₀_def]
    rw [hm1 m, compContinuousLinearMap_apply, (hfd x₀).fderiv, hfx₀, hae, hvec1, hσapp]
    simp
  have hdα₀x₀ : extDeriv α₀ x₀ = extDeriv α x₀ := by
    rw [hα₀_def, extDeriv_pullback (hσ.differentiable (by simp)).differentiableAt
      (hfs.contDiffAt : ContDiffAt ℝ 2 f x₀) (by simp)]
    ext m
    rw [hm2 m, compContinuousLinearMap_apply, (hfd x₀).fderiv, hvec2, hfx₀, hωe, hdσ]
  have hne₀ : α₀ x₀ ≠ 0 := hα₀x₀ ▸ hne
  have hnd₀ : ∀ v, α₀ x₀ ![v] = 0 → (∀ w, α₀ x₀ ![w] = 0 → extDeriv α₀ x₀ ![v, w] = 0) →
      v = 0 := by
    rw [hα₀x₀, hdα₀x₀]
    exact hnd
  -- The contact Moser lemma deforms `α₀` into a positive multiple of `α`.
  obtain ⟨ψ, g, hψx₀, hev⟩ := exists_diffeomorph_eventually_compContinuousLinearMap_fderiv_eq_smul
    hr hW hx₀ hα₀s hα hα₀x₀.symm hdα₀x₀.symm hne₀ hnd₀
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : V ≃ₘ^r⟮𝓘(ℝ, V), 𝓘(ℝ, P)⟯ P, ⇑Φ = f ∘ ψ.symm :=
    ⟨ψ.symm.trans ((Diffeomorph.smulAdd r (1 : ℝ) (-x₀) one_ne_zero).trans
      (e.toContDiffDiffeomorph r)), by funext y; simp [hf_def, sub_eq_add_neg]⟩
  have hψsymm : ψ.symm x₀ = x₀ := ψ.symm_apply_eq.2 hψx₀.symm
  refine ⟨n, Φ, fun y ↦ (g (ψ.symm y))⁻¹, by rw [hΦ, Function.comp_apply, hψsymm, hfx₀], ?_⟩
  have hev' : ∀ᶠ y in 𝓝 x₀, 0 < g (ψ.symm y) ∧
      (α (ψ (ψ.symm y))).compContinuousLinearMap (fderiv ℝ ψ (ψ.symm y)) =
        g (ψ.symm y) • α₀ (ψ.symm y) := by
    have hc : Tendsto ψ.symm (𝓝 x₀) (𝓝 x₀) := by
      simpa [hψsymm] using ψ.symm.continuous.tendsto x₀
    exact hc.eventually hev
  filter_upwards [hev'] with y ⟨hg, hy⟩
  refine ⟨inv_pos.2 hg, fun v ↦ ?_⟩
  rw [ψ.apply_symm_apply] at hy
  -- Unwind `Φ^* σ = (ψ⁻¹)^* α₀ = (g ∘ ψ⁻¹)⁻¹ α`, evaluated on `v`.
  have hΦd : fderiv ℝ Φ y = (e : V →L[ℝ] P) ∘L fderiv ℝ ψ.symm y := by
    rw [hΦ, fderiv_comp y (hfd _).differentiableAt
      ((ψ.symm.differentiable hr0) y), (hfd _).fderiv]
  have hcomp (F : V → V) (z : V) : F ∘ ![z] = ![F z] := by
    funext i
    fin_cases i
    rfl
  have h := congrArg (fun β ↦ β ![fderiv ℝ ψ.symm y v]) hy
  simp only [hα₀_def, compContinuousLinearMap_apply, ContinuousAlternatingMap.smul_apply, hcomp,
    (hfd _).fderiv, hvec1, ψ.fderiv_apply_fderiv_symm_apply hr0, smul_eq_mul] at h
  have key : σ (Φ y) ![fderiv ℝ Φ y v] = (g (ψ.symm y))⁻¹ * α y ![v] := by
    rw [hΦd, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe, hΦ,
      Function.comp_apply, h, ← mul_assoc,
      inv_mul_cancel₀ hg.ne', one_mul]
  exact key

end Darboux

end TauCeti
