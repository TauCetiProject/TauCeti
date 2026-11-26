/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.SeibergWitten.CutoffCurrent
public import TauCeti.Geometry.Symplectic.JHolomorphic.Normal.Taming
import TauCeti.Analysis.Calculus.DifferentialForm.Basic
import TauCeti.Analysis.Calculus.DifferentialForm.Regularity
import TauCeti.Analysis.Normed.Module.Alternating.Curry
import TauCeti.Data.Fin.VecNotation

/-!
# The coupling form of a Hermitian connection on the normal line

Let `C` be an embedded pseudoholomorphic curve in a symplectic four-manifold, read in coordinates
`(z, w) ∈ E × ℂ` in which `C` is the zero section and the normal line is trivialized by a unitary
frame. A Hermitian connection on the normal line is `d + i A` for a real one-form `A` on the base,
and with `w = ρ e^(iθ)` its covariant derivative of the fibre coordinate is
`∇w = dw + i A w`. The **coupling primitive**

`λ = Im (conj w ∇w) / 2 = (ρ² / 2) (dθ + A)`

(`TauCeti.normalCouplingPrimitive`) is smooth across the zero section, and for a two-form `ω` on
the base the **coupling form** is

`ω_N = π^* ω + dλ`

(`TauCeti.normalCouplingForm`). This is Sternberg's minimal coupling form of the connection. It
is the model symplectic form on the normal disk bundle of `C` with which Taubes compares the
ambient symplectic form, and the taming form `Ω = K π^* ω + dλ` controlling the mass of the
currents near `C`. This file computes it and proves:

* **Value.** On a pair of tangent vectors `u = (v, n)`, `u' = (v', n')` at `(z, w)`,
  `ω_N(u, u') = ω(v, v') + Im (conj (∇_u w) ∇_{u'} w) + (|w|² / 2) dA(v, v')`, with
  `∇_{(v, n)} w = n + i A(v) w` (`TauCeti.normalCouplingForm_apply_pair`). This rests on the
  differential of the phase form weighted by `|α|²`,
  `TauCeti.SeibergWitten.extDeriv_cutoffPhaseForm_id_apply_pair`.
* **The fibres.** On each normal fibre `ω_N` restricts to the area form `Im (conj n n')` of `ℂ`
  (`TauCeti.normalCouplingForm_apply_inr_inr`), and so it tames multiplication by `i` there,
  `ω_N((0, n), (0, i n)) = |n|²` (`TauCeti.normalCouplingForm_apply_inr_inr_I_mul`).
* **Horizontal and vertical.** The horizontal lift `(v, -i A(v) w)` of `v`, the kernel of `∇w`, is
  `ω_N`-orthogonal to the fibre (`TauCeti.normalCouplingForm_apply_horizontal_inr`), and on two
  horizontal lifts `ω_N` is `ω + (|w|² / 2) dA` (`TauCeti.normalCouplingForm_apply_horizontal`).
  Hence the kernel of `ω_N` at `(z, w)` consists of the horizontal lifts of the kernel of
  `ω + (|w|² / 2) dA` at `z` (`TauCeti.forall_normalCouplingForm_apply_eq_zero_iff`): `ω_N` is
  nondegenerate at `(z, w)` exactly when `ω + (|w|² / 2) dA` is nondegenerate at `z`. For a flat
  connection, `dA = 0`, this is nondegeneracy of `ω`, on the whole normal line.
* **Regularity.** `ω_N` is `C^n` where `ω` is `C^n` and `A` is `C^(n+1)`
  (`TauCeti.contDiffAt_normalCouplingForm`, `TauCeti.contDiff_normalCouplingForm`).
* **Closedness.** `ω_N` is closed where `ω` is (`TauCeti.extDeriv_normalCouplingForm_eq_zero`),
  being the sum of a pullback of `ω` and an exact form.
* **Taming.** If `ω` tames the complex structure of the curve and the almost complex structure
  `J` acts by `i` on the normal fibres along `C`, then for every large `K` the coupling form of
  `K ω` tames the normal linearization `J_N` of `J` on each disk bundle over a compact set of
  base points (`TauCeti.exists_forall_div_two_mul_norm_sq_le_normalCouplingForm`), by
  `TauCeti.exists_forall_div_two_mul_norm_sq_le_normalLinearization`.

Under a change of unitary frame `w ↦ e^(iφ(z)) w` the connection form becomes `A - dφ`. Since
`λ` is half the cutoff phase form for `χ = id` of the pair `(π^* A, w)`
(`TauCeti.normalCouplingPrimitive_eq_smul_cutoffPhaseForm`), its gauge invariance
`TauCeti.SeibergWitten.cutoffPhaseForm_sub_phaseForm_mul`, which only needs `χ 0 = 0`, and its
naturality under pullback `TauCeti.SeibergWitten.cutoffPhaseForm_comp` relate the coupling
primitives of the two frames. The comparison is stated at the level of coupling forms, not
primitives, in `Normal/Connection.lean`: the gauge transformation `TauCeti.normalModelGauge`
pulls the coupling form of `A - dφ` back to that of `A` where the two have the same curvature
(`TauCeti.normalCouplingForm_normalModelGauge_apply`).

## Main definitions

* `TauCeti.normalCouplingPrimitive A`: the one-form `λ = Im (conj w ∇w) / 2` on `E × ℂ`.
* `TauCeti.normalCouplingForm ω A`: the two-form `ω_N = π^* ω + dλ` on `E × ℂ`.

## References

* S. Sternberg, *Minimal coupling and the symplectic mechanics of a classical particle in the
  presence of a Yang–Mills field*, Proc. Nat. Acad. Sci. U.S.A. 74 (1977), 5253–5254.
* C. H. Taubes, *SW ⇒ Gr: from the Seiberg–Witten equations to pseudo-holomorphic curves*,
  J. Amer. Math. Soc. 9 (1996), 845–918.
* C. H. Taubes, *Counting pseudo-holomorphic submanifolds in dimension 4*, J. Differential Geom.
  44 (1996), 818–893.
-/

public section

noncomputable section

open ContinuousAlternatingMap Complex Set
open scoped ComplexConjugate

namespace TauCeti

open SeibergWitten

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {ω : E → E [⋀^Fin 2]→L[ℝ] ℝ} {A : E → E [⋀^Fin 1]→L[ℝ] ℝ} {z : E} {w : ℂ}

/-! ### The coupling primitive -/

/-- The **coupling primitive** `λ = Im (conj w ∇w) / 2 = (|w|² / 2) (dθ + A)` of the connection
`d + i A` on the trivial line over `E`, a one-form on the total space `E × ℂ`. It is half the
cutoff phase form for `χ = id` of the fibre coordinate `w` and the pulled-back connection form
`π^* A`. -/
def normalCouplingPrimitive (A : E → E [⋀^Fin 1]→L[ℝ] ℝ) : E × ℂ → (E × ℂ) [⋀^Fin 1]→L[ℝ] ℝ :=
  (2⁻¹ : ℝ) • cutoffPhaseForm id
    (fun p ↦ (A p.1).compContinuousLinearMap (ContinuousLinearMap.fst ℝ E ℂ)) Prod.snd

/-- The coupling primitive is half the cutoff phase form for `χ = id` of the fibre coordinate and
the pulled-back connection form `π^* A`. -/
theorem normalCouplingPrimitive_eq_smul_cutoffPhaseForm (A : E → E [⋀^Fin 1]→L[ℝ] ℝ) :
    normalCouplingPrimitive A = (2⁻¹ : ℝ) • cutoffPhaseForm id
      (fun p ↦ (A p.1).compContinuousLinearMap (ContinuousLinearMap.fst ℝ E ℂ)) Prod.snd :=
  (rfl)

/-- The coupling primitive on a vector `(v, n)` at `(z, w)` is `Im (conj w (n + i A(v) w)) / 2`. -/
@[simp]
theorem normalCouplingPrimitive_apply (A : E → E [⋀^Fin 1]→L[ℝ] ℝ) (z : E) (w : ℂ) (v : E)
    (n : ℂ) :
    normalCouplingPrimitive A (z, w) (fun _ ↦ (v, n)) =
      (conj w * (n + I * A z (fun _ ↦ v) * w)).im / 2 := by
  rw [normalCouplingPrimitive_eq_smul_cutoffPhaseForm, Pi.smul_apply,
    ContinuousAlternatingMap.smul_apply, cutoffPhaseForm_id_apply_eq_im, covariantDeriv_apply,
    fderiv_snd]
  simp only [compContinuousLinearMap_apply, Function.comp_def, ContinuousLinearMap.coe_fst',
    ContinuousLinearMap.coe_snd', smul_eq_mul, Complex.real_smul]
  ring_nf

/-- The coupling primitive of a connection form that is `C^n` at `z` is `C^n` at every point
`(z, w)` of the fibre over `z`. -/
theorem contDiffAt_normalCouplingPrimitive {n : WithTop ℕ∞} (hA : ContDiffAt ℝ n A z) (w : ℂ) :
    ContDiffAt ℝ n (normalCouplingPrimitive A) (z, w) :=
  (contDiffAt_cutoffPhaseForm_id contDiff_snd.contDiffAt
    (contDiffAt_pullback_continuousLinearMap (ContinuousLinearMap.fst ℝ E ℂ) hA)).const_smul
    (2⁻¹ : ℝ)

/-- The coupling primitive of a `C^n` connection form is `C^n`. -/
theorem contDiff_normalCouplingPrimitive {n : WithTop ℕ∞} (hA : ContDiff ℝ n A) :
    ContDiff ℝ n (normalCouplingPrimitive A) :=
  contDiff_iff_contDiffAt.2 fun p ↦ contDiffAt_normalCouplingPrimitive hA.contDiffAt p.2

/-- **The differential of the coupling primitive.** Where `A` is differentiable,

`dλ((v, n), (v', n')) = Im (conj (n + i A(v) w) (n' + i A(v') w)) + (|w|² / 2) dA(v, v')`. -/
theorem extDeriv_normalCouplingPrimitive_apply_pair (hA : DifferentiableAt ℝ A z) (v v' : E)
    (n n' : ℂ) :
    extDeriv (normalCouplingPrimitive A) (z, w) ![(v, n), (v', n')] =
      (conj (n + I * A z (fun _ ↦ v) * w) * (n' + I * A z (fun _ ↦ v') * w)).im +
        normSq w / 2 * extDeriv A z ![v, v'] := by
  have hb := differentiableAt_pullback_continuousLinearMap (ContinuousLinearMap.fst ℝ E ℂ)
    (x := (z, w)) hA
  have hpull := (ContinuousLinearMap.fst ℝ E ℂ).extDeriv_pullback (ω := A) (x := (z, w)) hA
  simp only [ContinuousLinearMap.coe_fst'] at hb hpull
  rw [normalCouplingPrimitive_eq_smul_cutoffPhaseForm, extDeriv_smul,
    ContinuousAlternatingMap.smul_apply,
    extDeriv_cutoffPhaseForm_id_apply_pair contDiff_snd.contDiffAt hb]
  simp only [covariantDeriv_apply, fderiv_snd, ContinuousLinearMap.coe_snd',
    compContinuousLinearMap_apply, Function.comp_def, ContinuousLinearMap.coe_fst',
    Complex.real_smul]
  rw [hpull, compContinuousLinearMap_apply, ContinuousLinearMap.coe_fst', Matrix.comp_vec2,
    smul_eq_mul]
  ring_nf

/-- On a normal fibre, the differential of the coupling primitive is the area form of `ℂ`:
`dλ((0, n), (0, n')) = Im (conj n n')`. -/
theorem extDeriv_normalCouplingPrimitive_apply_inr_inr (hA : DifferentiableAt ℝ A z) (n n' : ℂ) :
    extDeriv (normalCouplingPrimitive A) (z, w) ![(0, n), (0, n')] = (conj n * n').im := by
  have hA₀ : A z (fun _ ↦ 0) = 0 := (A z).map_coord_zero 0 rfl
  have hdA₀ : extDeriv A z ![0, 0] = 0 := (extDeriv A z).map_coord_zero 0 rfl
  rw [extDeriv_normalCouplingPrimitive_apply_pair hA, hA₀, hdA₀]
  simp

/-! ### The coupling form -/

/-- The **coupling form** `ω_N = π^* ω + dλ` on `E × ℂ` of a two-form `ω` on the base and the
connection `d + i A` on the trivial line, where `λ` is the coupling primitive. -/
def normalCouplingForm (ω : E → E [⋀^Fin 2]→L[ℝ] ℝ) (A : E → E [⋀^Fin 1]→L[ℝ] ℝ) (p : E × ℂ) :
    (E × ℂ) [⋀^Fin 2]→L[ℝ] ℝ :=
  (ω p.1).compContinuousLinearMap (ContinuousLinearMap.fst ℝ E ℂ) +
    extDeriv (normalCouplingPrimitive A) p

/-- The coupling form of a two-form that is `C^n` at `z` and a connection form that is `C^(n+1)`
at `z` is `C^n` at every point `(z, w)` of the fibre over `z`. -/
theorem contDiffAt_normalCouplingForm {n : WithTop ℕ∞} (hω : ContDiffAt ℝ n ω z)
    (hA : ContDiffAt ℝ (n + 1) A z) (w : ℂ) :
    ContDiffAt ℝ n (normalCouplingForm ω A) (z, w) :=
  (contDiffAt_pullback_continuousLinearMap (ContinuousLinearMap.fst ℝ E ℂ) hω).add
    (contDiffAt_extDeriv (contDiffAt_normalCouplingPrimitive hA w) le_rfl)

/-- The coupling form of a `C^n` two-form and a `C^(n+1)` connection form is `C^n`. -/
theorem contDiff_normalCouplingForm {n : WithTop ℕ∞} (hω : ContDiff ℝ n ω)
    (hA : ContDiff ℝ (n + 1) A) : ContDiff ℝ n (normalCouplingForm ω A) :=
  contDiff_iff_contDiffAt.2 fun p ↦
    contDiffAt_normalCouplingForm hω.contDiffAt hA.contDiffAt p.2

/-- The coupling form is `π^* ω + dλ`, evaluated on vectors. -/
@[simp]
theorem normalCouplingForm_apply (ω : E → E [⋀^Fin 2]→L[ℝ] ℝ) (A : E → E [⋀^Fin 1]→L[ℝ] ℝ)
    (p : E × ℂ) (u : Fin 2 → E × ℂ) :
    normalCouplingForm ω A p u =
      ω p.1 (Prod.fst ∘ u) + extDeriv (normalCouplingPrimitive A) p u := (rfl)

/-- **The coupling form on a pair of vectors.** Where `A` is differentiable,

`ω_N((v, n), (v', n')) = ω(v, v') + Im (conj (∇_u w) ∇_{u'} w) + (|w|² / 2) dA(v, v')`,

where `∇_u w = n + i A(v) w` and `∇_{u'} w = n' + i A(v') w` for `u = (v, n)`, `u' = (v', n')`. -/
theorem normalCouplingForm_apply_pair (hA : DifferentiableAt ℝ A z) (v v' : E) (n n' : ℂ) :
    normalCouplingForm ω A (z, w) ![(v, n), (v', n')] =
      ω z ![v, v'] +
        (conj (n + I * A z (fun _ ↦ v) * w) * (n' + I * A z (fun _ ↦ v') * w)).im +
          normSq w / 2 * extDeriv A z ![v, v'] := by
  rw [normalCouplingForm_apply, Matrix.comp_vec2, extDeriv_normalCouplingPrimitive_apply_pair hA,
    add_assoc]

/-- **The coupling form on a normal fibre** is the area form of `ℂ`:
`ω_N((0, n), (0, n')) = Im (conj n n')`. -/
theorem normalCouplingForm_apply_inr_inr (hA : DifferentiableAt ℝ A z) (n n' : ℂ) :
    normalCouplingForm ω A (z, w) ![(0, n), (0, n')] = (conj n * n').im := by
  rw [normalCouplingForm_apply, Matrix.comp_vec2,
    extDeriv_normalCouplingPrimitive_apply_inr_inr hA, (ω z).map_coord_zero 0 rfl, zero_add]

/-- The coupling form tames multiplication by `i` on the normal fibres:
`ω_N((0, n), (0, i n)) = |n|²`. -/
theorem normalCouplingForm_apply_inr_inr_I_mul (hA : DifferentiableAt ℝ A z) (n : ℂ) :
    normalCouplingForm ω A (z, w) ![(0, n), (0, I * n)] = ‖n‖ ^ 2 := by
  rw [normalCouplingForm_apply_inr_inr hA, ← normSq_eq_norm_sq, normSq_apply]
  simp only [mul_im, mul_re, conj_re, conj_im, I_re, I_im]
  ring

/-- **Horizontal lifts are orthogonal to the fibres.** The horizontal lift `(v, -i A(v) w)` of `v`
at `(z, w)`, on which `∇w` vanishes, is `ω_N`-orthogonal to every vertical vector `(0, n)`. -/
theorem normalCouplingForm_apply_horizontal_inr (hA : DifferentiableAt ℝ A z) (v : E) (n : ℂ) :
    normalCouplingForm ω A (z, w) ![(v, -(I * A z (fun _ ↦ v) * w)), (0, n)] = 0 := by
  rw [normalCouplingForm_apply_pair hA]
  have h₀ : ω z ![v, 0] = 0 := by
    simpa using (ω z).map_coord_zero 1 (m := ![v, 0]) rfl
  have h₁ : extDeriv A z ![v, 0] = 0 := by
    simpa using (extDeriv A z).map_coord_zero 1 (m := ![v, 0]) rfl
  simp [h₀, h₁]

/-- **The coupling form on horizontal lifts** is `ω + (|w|² / 2) dA`: on the horizontal lifts
`(v, -i A(v) w)` and `(v', -i A(v') w)` at `(z, w)` it takes the value
`ω(v, v') + (|w|² / 2) dA(v, v')`. For a flat connection this is `ω(v, v')`. -/
theorem normalCouplingForm_apply_horizontal (hA : DifferentiableAt ℝ A z) (v v' : E) :
    normalCouplingForm ω A (z, w)
        ![(v, -(I * A z (fun _ ↦ v) * w)), (v', -(I * A z (fun _ ↦ v') * w))] =
      ω z ![v, v'] + normSq w / 2 * extDeriv A z ![v, v'] := by
  rw [normalCouplingForm_apply_pair hA]
  simp

/-- **The kernel of the coupling form.** Where `A` is differentiable, a vector `(v, n)` at `(z, w)`
pairs to zero with every vector under `ω_N` exactly when it is the horizontal lift of `v`,
`n = -i A(v) w`, and `v` pairs to zero with every vector under `ω + (|w|² / 2) dA`. So `ω_N` is
nondegenerate at `(z, w)` exactly when `ω + (|w|² / 2) dA` is nondegenerate at `z`. -/
theorem forall_normalCouplingForm_apply_eq_zero_iff (hA : DifferentiableAt ℝ A z) (v : E)
    (n : ℂ) :
    (∀ u : E × ℂ, normalCouplingForm ω A (z, w) ![(v, n), u] = 0) ↔
      n = -(I * A z (fun _ ↦ v) * w) ∧
        ∀ v' : E, ω z ![v, v'] + normSq w / 2 * extDeriv A z ![v, v'] = 0 := by
  constructor
  · intro h
    -- Pairing with the vertical vector `(0, i ∇w)` gives `|∇w|² = 0`.
    set c := n + I * A z (fun _ ↦ v) * w with hc
    have hvert := h (0, I * c)
    rw [normalCouplingForm_apply, Matrix.comp_vec2, (ω z).map_coord_zero 1 rfl, zero_add,
      extDeriv_normalCouplingPrimitive_apply_pair hA,
      (A z).map_coord_zero (m := fun _ ↦ (0 : E)) 0 rfl,
      (extDeriv A z).map_coord_zero 1 rfl, ← hc] at hvert
    have hc0 : c = 0 := by
      rw [← normSq_eq_zero, normSq_apply]
      simp only [ofReal_zero, mul_zero, zero_mul, add_zero, mul_im, mul_re, conj_re, conj_im,
        I_re, I_im] at hvert
      linarith
    refine ⟨by linear_combination hc0, fun v' ↦ ?_⟩
    have hhor := h (v', -(I * A z (fun _ ↦ v') * w))
    rw [normalCouplingForm_apply_pair hA, ← hc, hc0] at hhor
    simpa using hhor
  · rintro ⟨hn, hv⟩ ⟨v', n'⟩
    rw [normalCouplingForm_apply_pair hA, hn]
    simpa using hv v'

/-- **The coupling form is closed** where `ω` is: if `ω` is differentiable and closed at `z` and
`A` is `C²` at `z`, then `dω_N = 0` at every point `(z, w)` of the fibre over `z`. -/
theorem extDeriv_normalCouplingForm_eq_zero (hω : DifferentiableAt ℝ ω z)
    (hdω : extDeriv ω z = 0) (hA : ContDiffAt ℝ 2 A z) :
    extDeriv (normalCouplingForm ω A) (z, w) = 0 := by
  have hlam := contDiffAt_normalCouplingPrimitive hA w
  have hpull := differentiableAt_pullback_continuousLinearMap (ContinuousLinearMap.fst ℝ E ℂ)
    (x := (z, w)) hω
  have hdlam : DifferentiableAt ℝ (extDeriv (normalCouplingPrimitive A)) (z, w) :=
    (contDiffAt_extDeriv hlam (r := 1) (by norm_num)).differentiableAt one_ne_zero
  have hsum : normalCouplingForm ω A =
      (fun p : E × ℂ ↦ (ω (ContinuousLinearMap.fst ℝ E ℂ p)).compContinuousLinearMap
        (ContinuousLinearMap.fst ℝ E ℂ)) + extDeriv (normalCouplingPrimitive A) := by
    funext p
    simp [normalCouplingForm]
  rw [hsum, extDeriv_add hpull hdlam, extDeriv_extDeriv_apply hlam (by simp), add_zero]
  exact (ContinuousLinearMap.fst ℝ E ℂ).extDeriv_pullback_eq_zero hω hdω

/-! ### Taming the normal linearization -/

/-- **The coupling form tames the normal linearization on disk bundles.** Let `B` be a compact
set of base points, along which `z ↦ J(z, 0)` and `z ↦ dJ(z, 0)` are continuous, `J(z, 0)` acts
by multiplication by `i` on the normal fibre, and `ω` tames the structure of the zero section,
`ω(v, j(z) v) ≥ m |v|²` with `m > 0`. If `A` is `C¹` at the points of `B`, then for every large
`K` the coupling form of `K ω` and `A`, that is `K π^* ω + dλ`, tames the normal linearization
`J_N` with constant `min m 1 / 2` at every point of the disk bundle of radius `R` over `B`. -/
theorem exists_forall_div_two_mul_norm_sq_le_normalCouplingForm
    {J : E × ℂ → E × ℂ →L[ℝ] E × ℂ} {B : Set E} {m R : ℝ} (hB : IsCompact B)
    (hJ : ContinuousOn (fun z ↦ J (z, 0)) B) (hdJ : ContinuousOn (fun z ↦ fderiv ℝ J (z, 0)) B)
    (hA : ∀ z ∈ B, ContDiffAt ℝ 1 A z) (hm : 0 < m)
    (hω : ∀ z ∈ B, ∀ v, m * ‖v‖ ^ 2 ≤ ω z ![v, (J (z, 0) (v, 0)).1])
    (hJN : ∀ z ∈ B, ∀ n, (J (z, 0) (0, n)).2 = I * n) :
    ∃ K₀ : ℝ, ∀ K : ℝ, K₀ ≤ K → ∀ z ∈ B, ∀ w : ℂ, ‖w‖ ≤ R → ∀ u : E × ℂ,
      min m 1 / 2 * ‖u‖ ^ 2 ≤
        normalCouplingForm (K • ω) A (z, w) ![u, normalLinearization J (z, w) u] := by
  set σ : E × ℂ → E × ℂ →L[ℝ] E × ℂ →L[ℝ] ℝ :=
    fun p ↦ flatL ℝ (E × ℂ) ℝ (extDeriv (normalCouplingPrimitive A) p) with hσ
  have hσc : ContinuousOn σ (B ×ˢ Metric.closedBall 0 R) := fun p hp ↦
    ((flatL ℝ (E × ℂ) ℝ).continuous.continuousAt.comp
      ((contDiffAt_extDeriv (contDiffAt_normalCouplingPrimitive (hA p.1 hp.1) p.2) (r := 0)
        (by simp)).continuousAt)).continuousWithinAt
  -- The codomain is named to select its norm topology.
  obtain ⟨S, hS⟩ := (hB.prod (isCompact_closedBall (0 : ℂ) R)).exists_bound_of_continuousOn
    (E := E × ℂ →L[ℝ] E × ℂ →L[ℝ] ℝ) hσc
  have hm' : 0 < min m 1 := lt_min hm one_pos
  obtain ⟨K₀, hK₀⟩ := exists_forall_div_two_mul_norm_sq_le_normalLinearization
    (ω := fun z ↦ flatL ℝ E ℝ (ω z)) (σ := σ) (R := R) (S := S) hB hJ hdJ hm'
    (fun z hz v ↦ by
      rw [flatL_apply_apply]
      exact (mul_le_mul_of_nonneg_right (min_le_left m 1) (by positivity)).trans (hω z hz v))
    (fun z hz W _ n ↦ by
      rw [hσ, flatL_apply_apply, hJN z hz,
        extDeriv_normalCouplingPrimitive_apply_inr_inr
          ((hA z hz).differentiableAt one_ne_zero),
        ← normSq_eq_norm_sq, normSq_apply]
      simp only [mul_im, mul_re, conj_re, conj_im, I_re, I_im]
      nlinarith [min_le_right m 1, mul_self_nonneg n.re, mul_self_nonneg n.im])
    (fun z hz W hW ↦ hS (z, W) ⟨hz, mem_closedBall_zero_iff.2 hW⟩)
  refine ⟨K₀, fun K hK z hz w hw u ↦ ?_⟩
  have h := hK₀ K hK z hz w hw u
  rw [normalCouplingForm_apply, Matrix.comp_vec2, Pi.smul_apply,
    ContinuousAlternatingMap.smul_apply, smul_eq_mul]
  simpa [hσ] using h

end TauCeti
