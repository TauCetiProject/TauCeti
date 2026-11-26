/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.HeisenbergModel.Model
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Weil operators of a multiplier

Let `G` act on `W` by automorphisms that preserve the Heisenberg datum `β` and the Haar measure `μ`,
let `Δ` be a multiplier for this action and `e` a vacuum. The *Weil operator* of `g ∈ G` on the
reproducing model `M(β, e)` is `ω(g) v = Δ g • ∫ v y • ϱ (g • y) e dμ(y)`.

Since `g` preserves `β` and `μ`, `ω(g)` carries `ϱ x` to `ϱ (g • x)`; so `ω((gh)⁻¹) ω(g) ω(h)`
commutes with the Heisenberg operators and is, by Schur's lemma, the scalar read off at the vacuum:
the cocycle `c g h` of `Δ` (`TauCeti.ReproducingModel.weilOp_inv_mul_weilOp_mul_weilOp`). This
replaces the usual comparison with a Schrödinger model on a parabolic subgroup. When `c = 1`, the
Weil operators form a representation `TauCeti.ReproducingModel.weilRep` that preserves `⟨·, ·⟩`,
intertwines `ϱ x` with `ϱ (g • x)`, has operator norm at most `‖e‖ * ‖Δ g‖`, and is jointly
continuous when `G` is first countable.

## Main definitions

* `TauCeti.HeisenbergDatum.Representation.twist`: the representation `x ↦ ϱ (g • x)`.
* `TauCeti.ReproducingModel.weilOp`: the Weil operator `ω(g)` of a multiplier.
* `TauCeti.ReproducingModel.cocycleRadical`: the subgroup of the `s` with `c g s = 1` for all `g`.
* `TauCeti.ReproducingModel.weilRep`: the Weil representation of a multiplier with cocycle `1`.

## Main results

* `TauCeti.ReproducingModel.weilOp_inv_mul_weilOp_mul_weilOp`: `ω((gh)⁻¹) ω(g) ω(h) = c g h`.
* `TauCeti.ReproducingModel.weilOp_mul`, `TauCeti.ReproducingModel.innerSL_weilOp`: if
  `c g 1 = 1` for all `g`, then `ω(g) ω(h) = c g h • ω(gh)` and `ω(g)` preserves `⟨·, ·⟩`.
* `TauCeti.ReproducingModel.weilRep_heisenbergRep`, `TauCeti.ReproducingModel.weilRep_apply`,
  `TauCeti.ReproducingModel.weilRep_apply_of_vacuum`,
  `TauCeti.ReproducingModel.conj_mul_weilRep_vacuum_apply_zero`,
  `TauCeti.ReproducingModel.norm_weilRep_le`, `TauCeti.ReproducingModel.continuous_weilRep`:
  the properties of the Weil representation.

## Provenance

Adapted from grh-lean (https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026
Anthropic, PBC), file `src/Lib/Weil/Construction/WeilOperators.lean` (`New.Heisenberg.Rep.moveBy`,
`New.Heisenberg.IsVacuum.weilOp`, `New.Heisenberg.IsVacuum.weilOp_inv_mul_weilOp_mul_weilOp`,
`New.Heisenberg.IsVacuum.weilOp_mul`, `New.Heisenberg.IsVacuum.modelInner_weilOp`,
`New.Heisenberg.IsVacuum.cocycleRadical`, `New.Heisenberg.IsVacuum.weilRep` and its lemmas).

## References

* A. Weil, *Sur certains groupes d'opérateurs unitaires*, Acta Math. 111 (1964), 143–211.
* S. Kudla, *Notes on the local theta correspondence*, lectures at the European School in Group
  Theory (1996).
-/

public noncomputable section

open MeasureTheory Filter Topology
open scoped ComplexConjugate

namespace TauCeti

variable {W : Type*} [AddCommGroup W] [TopologicalSpace W] [MeasurableSpace W]
  {β : HeisenbergDatum W} {μ : Measure W} {e : W → ℂ}
  {G : Type*} [Group G] [TopologicalSpace G] [DistribMulAction G W] [ContinuousSMul G W]

namespace HeisenbergDatum.Representation

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] (ϱ : β.Representation X)
  (Δ : β.Multiplier μ G) (g : G)

/-- The representation `x ↦ ϱ (g • x)` of `β`, for `g` in a group whose action preserves `β`. -/
def twist : β.Representation X where
  toFun x := ϱ (g • x)
  apply_apply' x y v := by rw [ϱ.apply_apply, Δ.apply_smul_smul, smul_add]
  norm_apply' x v := ϱ.norm_apply _ v
  continuous_uncurry' := by fun_prop

@[simp]
theorem twist_apply (x : W) (v : X) : ϱ.twist Δ g x v = ϱ (g • x) v := (rfl)

@[simp]
theorem twist_one : ϱ.twist Δ 1 = ϱ := by
  cases ϱ
  simp [twist]

end HeisenbergDatum.Representation

namespace ReproducingModel

open HeisenbergDatum.Representation

variable [IsTopologicalAddGroup W] [BorelSpace W] [SecondCountableTopology W] [he : β.IsVacuum μ e]
  [μ.IsAddLeftInvariant] (Δ : β.Multiplier μ G) (g h : G) (x : W) (v w : ReproducingModel β μ e)

variable (e) in
/-- The *Weil operator* `ω(g) v = Δ g • ∫ v y • ϱ (g • y) e dμ(y)` of a multiplier `Δ` on the
reproducing model, where `ϱ` is the Heisenberg representation and `e` the vacuum vector. -/
def weilOp : ReproducingModel β μ e →L[ℂ] ReproducingModel β μ e :=
  Δ g • (((heisenbergRep (β := β) (μ := μ) (e := e)).twist Δ g).integrated μ e).flip vacuum

theorem weilOp_apply_eq : weilOp e Δ g v =
    Δ g • ((heisenbergRep (β := β) (μ := μ) (e := e)).twist Δ g).integrated μ e v vacuum := by
  simp [weilOp]

/-- The value of a Weil operator at a point:
`(ω(g) v) x = Δ g * ∫ v y * (β (g • y) x * e (x - g • y)) dμ(y)`. -/
theorem weilOp_apply : weilOp e Δ g v x = Δ g * ∫ y, v y * (β (g • y) x * e (x - g • y)) ∂μ := by
  simp [weilOp_apply_eq, integrated_apply_apply]

/-- A bounded functional applied to the twisted integrated action:
`T (∫ w y • ϱ (g • y) v dμ(y)) = ∫ w (g⁻¹ • y) * T (ϱ y v) dμ(y)`. -/
theorem map_integrated_twist (T : ReproducingModel β μ e →L[ℂ] ℂ) :
    T (((heisenbergRep (β := β) (μ := μ) (e := e)).twist Δ g).integrated μ e w v) =
      ∫ y, w (g⁻¹ • y) * T (heisenbergRep y v) ∂μ := by
  rw [← (Δ.measurePreserving_smul g).integral_comp' (f := .smul g)]
  simp [map_integrated]

/-- `P_g (P_k w v) = P_{gk} w ∘ P_g v` at every point, where `P_g w = ∫ w y • ϱ (g • y) dμ(y)`. -/
private theorem integrated_twist_integrated (k : G) (u : ReproducingModel β μ e) :
    ((heisenbergRep (β := β) (μ := μ) (e := e)).twist Δ g).integrated μ e
        (((heisenbergRep (β := β) (μ := μ) (e := e)).twist Δ k).integrated μ e w v) u =
      ((heisenbergRep (β := β) (μ := μ) (e := e)).twist Δ (g * k)).integrated μ e w
        (((heisenbergRep (β := β) (μ := μ) (e := e)).twist Δ g).integrated μ e v u) := by
  rw [← ContinuousLinearMap.flip_apply, map_integrated_of_intertwines]
  · rfl
  · simp [mul_smul]

/-- The Weil operators move the Heisenberg operators: `ω(g) ϱ(x) = ϱ(g • x) ω(g)`. -/
theorem weilOp_heisenbergRep :
    weilOp e Δ g (heisenbergRep x v) = heisenbergRep (g • x) (weilOp e Δ g v) := by
  simp [weilOp_apply_eq]

theorem weilOp_one : weilOp e Δ 1 = 1 := by
  refine hom_ext fun y ↦ ?_
  simp [weilOp_apply_eq, he.apply_zero]

/-- The scalar of the cocycle relation, evaluated as a double integral at the vacuum. -/
private theorem weilOp_inv_mul_weilOp_mul_weilOp_vacuum :
    (weilOp e Δ (g * h)⁻¹ * weilOp e Δ g * weilOp e Δ h) vacuum 0 = Δ.cocycle e g h := by
  set P := fun k : G ↦ ((heisenbergRep (β := β) (μ := μ) (e := e)).twist Δ k).integrated μ e
  have hP_apply (k : G) (w v : ReproducingModel β μ e) (x : W) :
      P k w v x = ∫ y, w (k⁻¹ • y) * heisenbergRep y v x ∂μ := by
    simpa using map_integrated_twist Δ k v w (evalCLM x)
  have hP_comp (k l : G) (u v w : ReproducingModel β μ e) :
      P k (P l w v) u = P (k * l) w (P k v u) :=
    integrated_twist_integrated Δ k v w l u
  have hP_one (w v : ReproducingModel β μ e) : P 1 w v = v 0 • w := by simp [P]
  have h_inner (x : W) : P (g * h)⁻¹ vacuum vacuum (-x) =
      ∫ y, e ((g * h) • y) * (β x y * e (x + y)) ∂μ := by
    simp only [hP_apply, inv_inv, vacuum_apply, heisenbergRep_apply, β.apply_neg, ← neg_add',
      he.apply_neg]
  have h_value : P h⁻¹ vacuum (P (g * h)⁻¹ vacuum vacuum) 0 =
      ∫ x, ∫ y, e (h • x) * e ((g * h) • y) * β x y * e (x + y) ∂μ ∂μ := by
    rw [hP_apply]
    simp only [inv_inv, vacuum_apply, heisenbergRep_apply, β.apply_zero, one_mul, zero_sub, h_inner,
      mul_assoc, integral_const_mul]
  calc (weilOp e Δ (g * h)⁻¹ * weilOp e Δ g * weilOp e Δ h) vacuum 0
    _ = Δ g * Δ h * Δ (g * h)⁻¹ * P (g * h)⁻¹ (P g (P h vacuum vacuum) vacuum) vacuum 0 := by
      simp only [mul_apply_eq_comp, weilOp_apply_eq, map_smul, P, smul_apply]
      ring
    _ = Δ g * Δ h * Δ (g * h)⁻¹ * P 1 vacuum (P h⁻¹ vacuum (P (g * h)⁻¹ vacuum vacuum)) 0 := by
      rw [hP_comp g h, hP_comp, hP_comp, inv_mul_cancel, mul_inv_rev, inv_mul_cancel_right]
    _ = Δ.cocycle e g h := by
      rw [hP_one, smul_apply, vacuum_apply, he.apply_zero, mul_one, h_value,
        HeisenbergDatum.Multiplier.cocycle_def]

/-- The *cocycle relation*: `ω((gh)⁻¹) ω(g) ω(h)` is the scalar `c g h`. -/
theorem weilOp_inv_mul_weilOp_mul_weilOp :
    weilOp e Δ (g * h)⁻¹ * weilOp e Δ g * weilOp e Δ h = Δ.cocycle e g h • 1 := by
  have h_move (k : G) (y : W) :
      weilOp e Δ k * heisenbergRep y = heisenbergRep (k • y) * weilOp e Δ k := by
    ext1 v
    exact weilOp_heisenbergRep Δ k y v
  have h_commute (y : W) :
      Commute (weilOp e Δ (g * h)⁻¹ * weilOp e Δ g * weilOp e Δ h) (heisenbergRep y) := by
    rw [commute_iff_eq, mul_assoc, h_move, ← mul_assoc, mul_assoc _ (weilOp e Δ g), h_move,
      ← mul_assoc, h_move, ← mul_smul g h, inv_smul_smul]
    simp only [mul_assoc]
  rw [eq_smul_one_of_commute _ h_commute, weilOp_inv_mul_weilOp_mul_weilOp_vacuum]

/-- If `c g 1 = 1` for every `g`, the Weil operators multiply up to the cocycle:
`ω(g) ω(h) = c g h • ω(gh)`. -/
theorem weilOp_mul (hc : ∀ g, Δ.cocycle e g 1 = 1) :
    weilOp e Δ g * weilOp e Δ h = Δ.cocycle e g h • weilOp e Δ (g * h) := by
  have h_inv : weilOp e Δ (g * h) * weilOp e Δ (g * h)⁻¹ = 1 := by
    simpa [weilOp_one, hc] using weilOp_inv_mul_weilOp_mul_weilOp (e := e) Δ (g * h)⁻¹ 1
  rw [← mul_smul_one, ← weilOp_inv_mul_weilOp_mul_weilOp Δ g h, ← mul_assoc, ← mul_assoc, h_inv,
    one_mul]

/-- If `c g 1 = 1`, the Weil operator `ω(g)` preserves `⟨·, ·⟩`: `ω(g⁻¹)` is both a left inverse
and an adjoint of `ω(g)`. -/
theorem innerSL_weilOp (hc : Δ.cocycle e g 1 = 1) :
    innerSL (weilOp e Δ g v) (weilOp e Δ g w) = innerSL v w := by
  have h_inv : weilOp e Δ g⁻¹ (weilOp e Δ g v) = v := by
    simpa [weilOp_one, hc] using
      DFunLike.congr_fun (weilOp_inv_mul_weilOp_mul_weilOp (e := e) Δ g 1) v
  have h_coeff (u : ReproducingModel β μ e) (y : W) :
      innerSL u (heisenbergRep y vacuum) = conj (u y) := by
    rw [← conj_innerSL, innerSL_heisenbergRep_vacuum]
  have h_adjoint (u : ReproducingModel β μ e) :
      innerSL u (weilOp e Δ g w) = conj (innerSL w (weilOp e Δ g⁻¹ u)) := by
    calc innerSL u (weilOp e Δ g w)
      _ = Δ g * ∫ y, w (g⁻¹ • y) * conj (u y) ∂μ := by
        simp [weilOp_apply_eq, map_integrated_twist, h_coeff]
      _ = conj (innerSL w (weilOp e Δ g⁻¹ u)) := by
        simp [weilOp_apply_eq, map_integrated, h_coeff, ← integral_conj, mul_comm, Δ.map_inv]
  rw [h_adjoint, h_inv, conj_innerSL]

/-- For a multiplier with `c g 1 = 1` for every `g`, the subgroup of the `s ∈ G` with `c g s = 1`
for every `g`. It is closed under products and inverses by the cocycle identity of `c`, which
follows from associativity of the Weil operators. -/
def cocycleRadical (hc : ∀ g, Δ.cocycle e g 1 = 1) : Subgroup G :=
  have h_cocycle (g h k : G) :
      Δ.cocycle e g h * Δ.cocycle e (g * h) k = Δ.cocycle e h k * Δ.cocycle e g (h * k) := by
    have h_assoc := mul_assoc (weilOp e Δ g) (weilOp e Δ h) (weilOp e Δ k)
    rw [weilOp_mul Δ g h hc, weilOp_mul Δ h k hc, smul_mul_assoc, weilOp_mul Δ _ k hc,
      mul_smul_comm, weilOp_mul Δ g _ hc, ← mul_assoc g h k, smul_smul, smul_smul] at h_assoc
    have h_unit : innerSL (weilOp e Δ (g * h * k) vacuum) (weilOp e Δ (g * h * k) vacuum) = 1 := by
      rw [innerSL_weilOp Δ _ _ _ (hc _), innerSL_vacuum, vacuum_apply, he.apply_zero]
    have h := congr(innerSL (weilOp e Δ (g * h * k) vacuum) ($h_assoc vacuum))
    simpa only [_root_.smul_apply, map_smul, smul_eq_mul, h_unit, mul_one] using h
  { carrier := {s | ∀ g, Δ.cocycle e g s = 1}
    one_mem' := hc
    mul_mem' {s t} hs ht g := by simpa [hs g, ht _] using (h_cocycle g s t).symm
    inv_mem' {s} hs g := by simpa [hs _, hc] using h_cocycle g s⁻¹ s }

@[simp]
theorem mem_cocycleRadical (hc : ∀ g, Δ.cocycle e g 1 = 1) (s : G) :
    s ∈ cocycleRadical Δ hc ↔ ∀ g, Δ.cocycle e g s = 1 := Iff.rfl

/-! ### The Weil representation -/

section WeilRep

variable (hc : ∀ g h, Δ.cocycle e g h = 1)

variable (e) in
/-- The *Weil representation* of a multiplier `Δ` with cocycle `1`: the homomorphism `g ↦ ω(g)`
from `G` to the bounded operators on the reproducing model. -/
def weilRep : G →* ReproducingModel β μ e →L[ℂ] ReproducingModel β μ e where
  toFun := weilOp e Δ
  map_one' := weilOp_one Δ
  map_mul' g h := by simp [weilOp_mul Δ g h fun g ↦ hc g 1, hc]

theorem weilRep_apply_eq : weilRep e Δ hc g v = weilOp e Δ g v := (rfl)

/-- The Weil representation carries `ϱ x` to `ϱ (g • x)`. -/
theorem weilRep_heisenbergRep :
    weilRep e Δ hc g (heisenbergRep x v) = heisenbergRep (g • x) (weilRep e Δ hc g v) :=
  weilOp_heisenbergRep Δ g x v

/-- The Weil representation preserves `⟨·, ·⟩`. -/
@[simp]
theorem innerSL_weilRep : innerSL (weilRep e Δ hc g v) (weilRep e Δ hc g w) = innerSL v w :=
  innerSL_weilOp Δ g v w (hc g 1)

/-- `(ω(g) v) x = Δ g * ∫ v y * (β (g • y) x * e (x - g • y)) dμ(y)`. -/
theorem weilRep_apply :
    weilRep e Δ hc g v x = Δ g * ∫ y, v y * (β (g • y) x * e (x - g • y)) ∂μ :=
  weilOp_apply Δ g x v

/-- An element `g` that fixes the vacuum acts by substitution times its multiplier:
`(ω(g) v) x = Δ g * v (g⁻¹ • x)`. -/
theorem weilRep_apply_of_vacuum (hg : ∀ y, e (g • y) = e y) :
    weilRep e Δ hc g v x = Δ g * v (g⁻¹ • x) := by
  have h_kernel (y : W) : β (g • y) x * e (x - g • y) = β y (g⁻¹ • x) * e (g⁻¹ • x - y) := by
    rw [← Δ.apply_smul_smul g y, ← hg (g⁻¹ • x - y), smul_sub, smul_inv_smul]
  rw [weilRep_apply]
  simp_rw [h_kernel, v.integral_mul_kernel]

/-- The overlap of `ω(g) e` with the vacuum is the inverse of `conj (Δ g)`:
`conj (Δ g) * (ω(g) e) 0 = 1`. -/
theorem conj_mul_weilRep_vacuum_apply_zero : conj (Δ g) * weilRep e Δ hc g vacuum 0 = 1 := by
  -- `ω(g)` is unitary and moves `ϱ y` to `ϱ (g • y)`; applying it to `integrated_eq_smul` gives
  -- `∫ e y • ϱ (g • y) e dμ(y) = conj ((ω(g) e) 0) • ω(g) e`.
  set ω := weilRep e Δ hc g with hω
  obtain ⟨u, hu⟩ : ∃ u, ω u = vacuum := ⟨weilRep e Δ hc g⁻¹ vacuum, by
    rw [hω, ← mul_apply_eq_comp, ← map_mul, mul_inv_cancel, map_one,
      one_apply_eq_self]⟩
  have h_overlap : u 0 = conj (ω vacuum 0) := by
    rw [← innerSL_vacuum, ← innerSL_weilRep Δ g vacuum u hc, ← hω, hu, ← conj_innerSL,
      innerSL_vacuum]
  have h_eq : ω vacuum = (Δ g * conj (ω vacuum 0)) • ω vacuum := by
    calc ω vacuum = Δ g • ((heisenbergRep (β := β) (μ := μ) (e := e)).twist Δ g).integrated μ e
          vacuum (ω u) := by rw [hu, hω, weilRep_apply_eq, weilOp_apply_eq]
      _ = Δ g • ω ((heisenbergRep (β := β) (μ := μ) (e := e)).integrated μ e vacuum u) := by
        rw [map_integrated_of_intertwines _ ω vacuum u (ϱ' := heisenbergRep.twist Δ g)
          fun y f ↦ by rw [twist_apply]; exact weilRep_heisenbergRep Δ g y f hc]
      _ = (Δ g * conj (ω vacuum 0)) • ω vacuum := by
        rw [integrated_eq_smul, map_smul, h_overlap, mul_smul]
  have h_unit : innerSL (ω vacuum) (ω vacuum) = 1 := by
    rw [hω, innerSL_weilRep, innerSL_vacuum, vacuum_apply, he.apply_zero]
  have h_one : Δ g * conj (ω vacuum 0) = 1 := by
    calc Δ g * conj (ω vacuum 0) = innerSL (ω vacuum) ((Δ g * conj (ω vacuum 0)) • ω vacuum) := by
          rw [map_smul, h_unit, smul_eq_mul, mul_one]
      _ = 1 := by rw [← h_eq, h_unit]
  simpa using congr(conj $h_one)

private theorem norm_integrated_twist_le :
    ‖((heisenbergRep (β := β) (μ := μ) (e := e)).twist Δ g).integrated μ e v vacuum‖ ≤
      ‖(vacuum : ReproducingModel β μ e)‖ * ‖v‖ := by
  rw [mul_comm]
  exact ((ContinuousLinearMap.le_opNorm _ _).trans
    (mul_le_mul_of_nonneg_right (norm_integrated_le _ v) (norm_nonneg _)))

/-- The operator norm bound `‖ω(g)‖ ≤ ‖e‖ * ‖Δ g‖`. -/
theorem norm_weilRep_le : ‖weilRep e Δ hc g‖ ≤ ‖(vacuum : ReproducingModel β μ e)‖ * ‖Δ g‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v ↦ ?_
  rw [weilRep_apply_eq, weilOp_apply_eq, norm_smul, mul_comm ‖vacuum‖, mul_assoc]
  exact mul_le_mul_of_nonneg_left (norm_integrated_twist_le Δ g v) (norm_nonneg _)

/-- For a first countable group `G`, the Weil representation is jointly continuous: the integral
defining `ω(g) v` is Lipschitz in `v` uniformly in `g`, and continuous in `g` for fixed `v` by
dominated convergence. -/
theorem continuous_weilRep [FirstCountableTopology G] :
    Continuous fun p : G × ReproducingModel β μ e ↦ weilRep e Δ hc p.1 p.2 := by
  let L (g : G) := (((heisenbergRep (β := β) (μ := μ) (e := e)).twist Δ g).integrated μ e).flip
    vacuum
  have h_lip (g : G) : LipschitzWith ‖(vacuum : ReproducingModel β μ e)‖₊ (L g) :=
    LipschitzWith.of_dist_le_mul fun v w ↦ by
      rw [dist_eq_norm, dist_eq_norm, ← map_sub]
      exact norm_integrated_twist_le Δ g (v - w)
  have h_cont (v : ReproducingModel β μ e) : Continuous fun g ↦ L g v := by
    simp only [L, ContinuousLinearMap.flip_apply, integrated_apply, twist_apply]
    refine continuous_of_dominated (bound := fun y ↦ ‖v y‖ * ‖(vacuum : ReproducingModel β μ e)‖)
      (fun g ↦ (integrable_smul_apply (heisenbergRep.twist Δ g) v vacuum).1)
      (fun g ↦ .of_forall fun y ↦ by simp [norm_smul])
      (v.integrable.norm.mul_const _) (.of_forall fun y ↦ by fun_prop)
  have h := (Δ.continuous.comp continuous_fst).smul
    (continuous_prod_of_continuous_lipschitzWith' (fun p ↦ L p.1 p.2) _ (fun g ↦ h_lip g) h_cont)
  refine h.congr fun p ↦ ?_
  simp [L, weilRep_apply_eq, weilOp_apply_eq]

end WeilRep

end ReproducingModel

end TauCeti
