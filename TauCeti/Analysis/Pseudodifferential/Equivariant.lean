/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Group.Integral
public import TauCeti.Analysis.Pseudodifferential.Integral
public import TauCeti.Analysis.Pseudodifferential.LinearChange
public import TauCeti.Analysis.Pseudodifferential.Symbol.Map
public import TauCeti.Topology.Algebra.Module.Equiv.Group
import TauCeti.Analysis.Calculus.IteratedFDeriv.Prod

/-!
# Equivariant symbols and averaging over a compact group

Let a group `G` act linearly on the positions `ℝⁿ` through `ρ : G →* (ℝⁿ ≃L[ℝ] ℝⁿ)` and on the
coefficient spaces through `σV : G →* (V ≃L[ℂ] V)` and `σW : G →* (W ≃L[ℂ] W)`. Then `G` acts on
`V`-valued Schwartz functions by `(g • u)(x) = σV g (u ((ρ g)⁻¹ x))` (`TauCeti.schwartzRep`), and
on symbols of order `m` by

`(g • a)(x, ξ) = σW g ∘ a((ρ g)⁻¹ x, (ρ g)ᵀ ξ) ∘ (σV g)⁻¹`

(`TauCeti.Symbol.act`): positions transform by `ρ g` and frequencies, being covectors, by the
inverse transpose of `ρ g`. The two actions are compatible with quantization: `Op(g • a)` is the
conjugate `g ∘ Op(a) ∘ g⁻¹` (`TauCeti.Symbol.quantizeSchwartzValue_act`), and each `g` acts
`ℂ`-linearly (`TauCeti.Symbol.act_add`, `TauCeti.Symbol.act_smul`). A symbol is *invariant*
if `g • a = a` for every `g` (`TauCeti.Symbol.IsInvariant`); its quantization then commutes with
the action of `G` (`TauCeti.Symbol.IsInvariant.quantizeSchwartzValue_schwartzRep`).

For a compact topological group `G`, with representations continuous in the operator norm, and a
finite measure `μ` on `G`, `TauCeti.Symbol.average` integrates the orbit `g ↦ g • a` against `μ`.
It is again a symbol of order `m`: the jets of the orbit are jointly continuous
(`TauCeti.Symbol.continuous_iteratedFDeriv_coefficient_act`), and the symbol estimates of `g • a`
on a compact set of positions hold with constants independent of `g`
(`TauCeti.Symbol.exists_norm_mixedDeriv_coefficient_act_le`). The average depends `ℂ`-linearly
on `a` (`TauCeti.Symbol.average_add`, `TauCeti.Symbol.average_smul`). For a left-invariant
probability measure, such as the normalized Haar measure,

* the average is invariant (`TauCeti.Symbol.isInvariant_average`);
* an invariant symbol is its own average, so averaging is a projection onto the invariant symbols
  (`TauCeti.Symbol.IsInvariant.average_eq`, `TauCeti.Symbol.average_eq_self_iff`);
* the quantization of the average is the average `∫ g ∘ Op(a) ∘ g⁻¹ dμ(g)` of the conjugates of
  `Op(a)` (`TauCeti.Symbol.quantizeSchwartzValue_average`).

For a probability measure the average also keeps every seminorm bound that holds uniformly along
the orbit (`TauCeti.Symbol.seminorm_average_le`).

Averaging thus turns a symbol into an invariant symbol of the same order, and its quantization
into an equivariant operator, without changing an operator that is already equivariant.

## References

* M. F. Atiyah and I. M. Singer, *The index of elliptic operators: I*, Ann. of Math. 87 (1968),
  (5.5)–(5.6), pp. 516–517: averaging pseudodifferential operators over a compact group.
* H. B. Lawson, Jr. and M.-L. Michelsohn, *Spin Geometry*, Chapter III, proof of Theorem 9.7,
  p. 214: compact-group averaging of operators and their symbols.
-/

public section

noncomputable section

open MeasureTheory
open scoped ContDiff SchwartzMap

namespace TauCeti

variable {G : Type*} [Group G] {n : ℕ} {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [NormedAddCommGroup W] [NormedSpace ℂ W] {m : ℝ}
  (ρ : G →* (CoordinateSpace n ≃L[ℝ] CoordinateSpace n)) (σV : G →* (V ≃L[ℂ] V))
  (σW : G →* (W ≃L[ℂ] W))

/-! ### The action on Schwartz functions -/

section Schwartz

/-- The representation of `G` on `V`-valued Schwartz functions induced by `ρ` and `σV`:
`(g • u)(x) = σV g (u ((ρ g)⁻¹ x))`. -/
def schwartzRep : G →* (𝓢(CoordinateSpace n, V) →L[ℂ] 𝓢(CoordinateSpace n, V)) where
  toFun g := (SchwartzMap.postcompCLM (σV g : V →L[ℂ] V)).comp
    (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (ρ g).symm)
  map_one' := by
    ext u x
    simp [ContinuousLinearEquiv.one_eq_refl]
  map_mul' g h := by
    ext u x
    simp [ContinuousLinearEquiv.mul_eq_trans]

@[simp]
theorem schwartzRep_apply (g : G) (u : 𝓢(CoordinateSpace n, V)) (x : CoordinateSpace n) :
    schwartzRep ρ σV g u x = σV g (u ((ρ g).symm x)) := by
  simp [schwartzRep]

end Schwartz

namespace Symbol

/-! ### The action on symbols -/

section Action

/-- The action of `g` on a symbol of order `m`:
`(g • a)(x, ξ) = σW g ∘ a((ρ g)⁻¹ x, (ρ g)ᵀ ξ) ∘ (σV g)⁻¹`. Positions transform by `ρ g`, and
frequencies by the inverse transpose of `ρ g`. -/
def act (g : G) (a : Symbol n V W m) : Symbol n V W m :=
  (compProdMap ((ρ g).symm : CoordinateSpace n →L[ℝ] CoordinateSpace n) (ρ g).adjointEquiv
    a).map (((σV g).arrowCongr (σW g)).toContinuousLinearMap.restrictScalars ℝ)

@[simp]
theorem coefficient_act (g : G) (a : Symbol n V W m) (p : CoordinateSpace n × CoordinateSpace n) :
    (act ρ σV σW g a).coefficient p =
      (σV g).arrowCongr (σW g) (a.coefficient ((ρ g).symm p.1, (ρ g).adjointEquiv p.2)) := by
  simp [act]

@[simp]
theorem act_one (a : Symbol n V W m) : act ρ σV σW 1 a = a := by
  ext p v
  simp [ContinuousLinearEquiv.one_eq_refl, ContinuousLinearMap.adjoint_id]

/-- `g • (h • a) = (g * h) • a`: `act` is an action of `G` on symbols. -/
theorem act_mul (g h : G) (a : Symbol n V W m) :
    act ρ σV σW (g * h) a = act ρ σV σW g (act ρ σV σW h a) := by
  -- The frequencies transform by `(ρ (g * h))ᵀ = (ρ h)ᵀ ∘ (ρ g)ᵀ`.
  have hadj : ContinuousLinearMap.adjoint (ρ (g * h) : CoordinateSpace n →L[ℝ] CoordinateSpace n) =
      ContinuousLinearMap.adjoint (ρ h : CoordinateSpace n →L[ℝ] CoordinateSpace n) ∘L
        ContinuousLinearMap.adjoint (ρ g : CoordinateSpace n →L[ℝ] CoordinateSpace n) := by
    rw [map_mul, ContinuousLinearEquiv.toContinuousLinearMap_mul, ContinuousLinearMap.mul_def,
      ContinuousLinearMap.adjoint_comp]
  ext p v
  simp only [coefficient_act, ContinuousLinearEquiv.adjointEquiv_apply, hadj]
  simp [ContinuousLinearEquiv.mul_eq_trans]

@[simp]
theorem act_zero (g : G) : act ρ σV σW g (0 : Symbol n V W m) = 0 := by
  ext p v
  simp

@[simp]
theorem act_add (g : G) (a b : Symbol n V W m) :
    act ρ σV σW g (a + b) = act ρ σV σW g a + act ρ σV σW g b := by
  ext p v
  simp [coefficient_add]

@[simp]
theorem act_smul (g : G) (c : ℂ) (a : Symbol n V W m) :
    act ρ σV σW g (c • a) = c • act ρ σV σW g a := by
  ext p v
  simp [coefficient_smul]

/-- A symbol is invariant under `G` if `g • a = a` for every `g`. Its quantization then commutes
with the action of `G` on Schwartz functions
(`TauCeti.Symbol.IsInvariant.quantizeSchwartzValue_schwartzRep`). -/
def IsInvariant (a : Symbol n V W m) : Prop :=
  ∀ g, act ρ σV σW g a = a

/-- A symbol is invariant exactly when
`σW g ∘ a((ρ g)⁻¹ x, (ρ g)ᵀ ξ) ∘ (σV g)⁻¹ = a(x, ξ)` for all `g`, `x` and `ξ`. -/
theorem isInvariant_iff {a : Symbol n V W m} :
    IsInvariant ρ σV σW a ↔ ∀ g p, (σV g).arrowCongr (σW g)
      (a.coefficient ((ρ g).symm p.1, (ρ g).adjointEquiv p.2)) = a.coefficient p := by
  simp only [IsInvariant, Symbol.ext_iff, funext_iff, coefficient_act]

/-- **Quantization intertwines the actions.** Quantizing `g • a` on `g • u` gives `g • Op(a) u`:
`Op(g • a)(g • u)(ρ g x) = σW g (Op(a) u x)`. -/
theorem quantizeSchwartzValue_act_schwartzRep (g : G) (a : Symbol n V W m)
    (u : 𝓢(CoordinateSpace n, V)) (x : CoordinateSpace n) :
    quantizeSchwartzValue (act ρ σV σW g a).coefficient (schwartzRep ρ σV g u) (ρ g x) =
      σW g (quantizeSchwartzValue a.coefficient u x) := by
  have hu : SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (ρ g)
      (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (ρ g).symm u) = u := by
    ext y
    simp
  have hrep : schwartzRep ρ σV g u =
      (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (ρ g).symm u).postcompCLM
        (σV g : V →L[ℂ] V) := by
    ext y
    simp
  rw [act, coefficient_map_arrowCongr, hrep, quantizeSchwartzValue_arrowCongr,
    quantizeSchwartzValue_compProdMap_symm_adjointEquiv, hu]

/-- **The quantization of `g • a` is the conjugate of `Op(a)` by `g`:**
`Op(g • a) u (x) = σW g (Op(a) (g⁻¹ • u) ((ρ g)⁻¹ x))`. -/
theorem quantizeSchwartzValue_act (g : G) (a : Symbol n V W m) (u : 𝓢(CoordinateSpace n, V))
    (x : CoordinateSpace n) :
    quantizeSchwartzValue (act ρ σV σW g a).coefficient u x =
      σW g (quantizeSchwartzValue a.coefficient (schwartzRep ρ σV g⁻¹ u) ((ρ g).symm x)) := by
  rw [← quantizeSchwartzValue_act_schwartzRep, ← mul_apply_eq_comp, ← map_mul, mul_inv_cancel,
    map_one, one_apply_eq_self, ContinuousLinearEquiv.apply_symm_apply]

/-- **Invariant symbols quantize to equivariant operators:** if `a` is invariant, then
`Op(a)(g • u)(ρ g x) = σW g (Op(a) u x)`. -/
theorem IsInvariant.quantizeSchwartzValue_schwartzRep {a : Symbol n V W m}
    (ha : IsInvariant ρ σV σW a) (g : G) (u : 𝓢(CoordinateSpace n, V)) (x : CoordinateSpace n) :
    quantizeSchwartzValue a.coefficient (schwartzRep ρ σV g u) (ρ g x) =
      σW g (quantizeSchwartzValue a.coefficient u x) := by
  rw [← quantizeSchwartzValue_act_schwartzRep, ha g]

end Action

/-! ### Regularity of the orbit of a symbol -/

section Orbit

variable [TopologicalSpace G] {ρ σV σW}
  (hρ : Continuous fun g ↦ (ρ g : CoordinateSpace n →L[ℝ] CoordinateSpace n))
  (hσV : Continuous fun g ↦ (σV g : V →L[ℂ] V)) (hσW : Continuous fun g ↦ (σW g : W →L[ℂ] W))

include hρ hσV hσW in
/-- The jets of the orbit `g ↦ g • a` of a symbol are jointly continuous in `g` and in the
position and frequency. -/
theorem continuous_iteratedFDeriv_coefficient_act [IsTopologicalGroup G] (a : Symbol n V W m)
    (k : ℕ) :
    Continuous fun q : G × (CoordinateSpace n × CoordinateSpace n) ↦
      iteratedFDeriv ℝ k (act ρ σV σW q.1 a).coefficient q.2 := by
  -- The coefficient of `g • a` at `p` is `F (((σW g, (σV g)⁻¹), M g), p)`, where
  -- `F (((A, B), M), p) = A ∘ a (M p) ∘ B` and `M g` is the linear change of positions and
  -- frequencies. The map `F` is smooth jointly in the operators `A`, `B`, `M` and in `p`, and
  -- these operators depend continuously on `g`.
  let c₃ : (W →L[ℂ] W) × (V →L[ℂ] W) × (V →L[ℂ] V) → V →L[ℂ] W := fun q ↦ q.1 ∘L q.2.1 ∘L q.2.2
  have hc₃ : ContDiff ℝ ∞ c₃ :=
    (contDiff_fst.clm_comp (contDiff_snd.fst.clm_comp contDiff_snd.snd) :
      ContDiff ℂ ∞ c₃).restrict_scalars ℝ
  let F : (((W →L[ℂ] W) × (V →L[ℂ] V)) ×
      (CoordinateSpace n × CoordinateSpace n →L[ℝ] CoordinateSpace n × CoordinateSpace n)) ×
      (CoordinateSpace n × CoordinateSpace n) → V →L[ℂ] W :=
    fun z ↦ c₃ (z.1.1.1, a.coefficient (z.1.2 z.2), z.1.1.2)
  have hF : ContDiff ℝ ∞ F := hc₃.comp (contDiff_fst.fst.fst.prodMk
    ((a.contDiff_coefficient.comp (contDiff_fst.snd.clm_apply contDiff_snd)).prodMk
      contDiff_fst.fst.snd))
  have hcoef (g : G) : (act ρ σV σW g a).coefficient = fun p ↦
      F ((((σW g : W →L[ℂ] W), ((σV g).symm : V →L[ℂ] V)),
        ((ρ g).symm : CoordinateSpace n →L[ℝ] CoordinateSpace n).prodMap
          ((ρ g).adjointEquiv : CoordinateSpace n →L[ℝ] CoordinateSpace n)), p) := by
    funext ⟨x, ξ⟩
    ext v
    simp [F, c₃]
  simp_rw [hcoef]
  exact (hF.continuous_iteratedFDeriv_prod_right k (mod_cast le_top)).comp
    ((((hσW.prodMk (MonoidHom.continuous_symm hσV)).prodMk
      ((ContinuousLinearMap.prodMapL ℝ _ _ _ _).continuous.comp
        ((MonoidHom.continuous_symm hρ).prodMk
          (ContinuousLinearEquiv.continuous_adjointEquiv hρ)))).comp
      continuous_fst).prodMk continuous_snd)

variable [IsTopologicalGroup G] [CompactSpace G]

include hρ hσV hσW in
/-- **Uniform symbol estimates along the orbit.** For a compact group, the symbols `g • a`
satisfy the symbol estimates of order `m` on each compact set of positions with constants
independent of `g`. -/
theorem exists_norm_mixedDeriv_coefficient_act_le (a : Symbol n V W m)
    {K : Set (CoordinateSpace n)} (hK : IsCompact K) (α β : List (Fin n)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ g : G, ∀ x ∈ K, ∀ ξ,
      ‖mixedDeriv α β (act ρ σV σW g a).coefficient x ξ‖ ≤
        C * (1 + ‖ξ‖ ^ 2) ^ ((m - β.length) / 2) := by
  -- Bound the representations uniformly over the compact group.
  obtain ⟨c, hc⟩ := isCompact_univ.exists_bound_of_continuousOn hρ.continuousOn
  obtain ⟨bW, hbW⟩ := isCompact_univ.exists_bound_of_continuousOn hσW.continuousOn
  obtain ⟨bV, hbV⟩ :=
    isCompact_univ.exists_bound_of_continuousOn (MonoidHom.continuous_symm hσV).continuousOn
  -- The positions `(ρ g)⁻¹ x`, `x ∈ K`, lie in a compact set `K'`.
  set K' := (fun q : G × CoordinateSpace n ↦ (ρ q.1).symm q.2) '' (Set.univ ×ˢ K)
  have hK' : IsCompact K' := (isCompact_univ.prod hK).image
    (((MonoidHom.continuous_symm hρ).comp continuous_fst).clm_apply continuous_snd)
  choose C _ hC using fun α' β' ↦ a.exists_bound K' hK' α' β'
  obtain ⟨B, hB0, hB⟩ := exists_norm_mixedDeriv_comp_prodMap_le a.contDiff_coefficient c C α β
  refine ⟨max bW 0 * max bV 0 * B, by positivity, fun g x hx ξ ↦ ?_⟩
  set Φ := ((σV g).arrowCongr (σW g)).toContinuousLinearMap.restrictScalars ℝ
  set P := ((ρ g).symm : CoordinateSpace n →L[ℝ] CoordinateSpace n)
  set Q := (ρ g).adjointEquiv
  have hP : ‖P‖ ≤ c := by
    simpa [P, ← ContinuousLinearEquiv.inv_def, ← map_inv] using hc g⁻¹ (Set.mem_univ _)
  have hQ : ‖(Q : CoordinateSpace n →L[ℝ] CoordinateSpace n)‖ ≤ c := by
    simpa [Q] using hc g (Set.mem_univ _)
  have hQ' : ‖(Q.symm : CoordinateSpace n →L[ℝ] CoordinateSpace n)‖ ≤ c := by
    simpa [Q] using hP
  -- The conjugation `Φ = σW g ∘ · ∘ (σV g)⁻¹` has norm at most `‖σW g‖ ‖(σV g)⁻¹‖`.
  have hΦ : ‖Φ‖ ≤ max bW 0 * max bV 0 := by
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun T ↦ ?_
    have hT : Φ T = (σW g : W →L[ℂ] W) ∘L T ∘L ((σV g).symm : V →L[ℂ] V) := by
      ext v
      simp [Φ]
    rw [hT]
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
    refine (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _)
      (norm_nonneg _)).trans ?_
    have hW := (hbW g (Set.mem_univ _)).trans (le_max_left bW 0)
    have hV := (hbV g (Set.mem_univ _)).trans (le_max_left bV 0)
    calc _ ≤ max bW 0 * (‖T‖ * max bV 0) := by gcongr
      _ = _ := by ring
  have hcoef : (act ρ σV σW g a).coefficient =
      Φ ∘ (a.coefficient ∘ P.prodMap (Q : CoordinateSpace n →L[ℝ] CoordinateSpace n)) := by
    funext ⟨y, η⟩
    simp [Φ, P, Q]
  rw [hcoef, Φ.mixedDeriv_comp_left (a.contDiff_coefficient.comp (ContinuousLinearMap.contDiff _)),
    mul_assoc]
  exact (Φ.le_opNorm _).trans (mul_le_mul hΦ
    (hB P Q hP hQ hQ' x (fun α' β' η ↦ hC α' β' _ ⟨(g, x), ⟨Set.mem_univ _, hx⟩, rfl⟩ η) ξ)
    (norm_nonneg _) (by positivity))

end Orbit

/-! ### Averaging over a compact group -/

section Average

variable [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [MeasurableSpace G]
  [OpensMeasurableSpace G] (μ : Measure G) [IsFiniteMeasure μ]
  {ρ σV σW}
  (hρ : Continuous fun g ↦ (ρ g : CoordinateSpace n →L[ℝ] CoordinateSpace n))
  (hσV : Continuous fun g ↦ (σV g : V →L[ℂ] V)) (hσW : Continuous fun g ↦ (σW g : W →L[ℂ] W))

/-- The average `∫ g • a dμ(g)` of the orbit of a symbol `a` of order `m` over a compact group, a
symbol of order `m`. For the normalized Haar measure it is an invariant symbol
(`TauCeti.Symbol.isInvariant_average`), equal to `a` when `a` is invariant
(`TauCeti.Symbol.IsInvariant.average_eq`). -/
def average (a : Symbol n V W m) : Symbol n V W m :=
  integral μ (fun g ↦ act ρ σV σW g a) (continuous_iteratedFDeriv_coefficient_act hρ hσV hσW a)
    fun _ hK α β ↦ exists_norm_mixedDeriv_coefficient_act_le hρ hσV hσW a hK α β

@[simp]
theorem coefficient_average (a : Symbol n V W m) (p : CoordinateSpace n × CoordinateSpace n) :
    (average μ hρ hσV hσW a).coefficient p = ∫ g, (act ρ σV σW g a).coefficient p ∂μ := by
  simp [average]

include hρ hσV hσW in
private theorem integrable_coefficient_act (a : Symbol n V W m)
    (p : CoordinateSpace n × CoordinateSpace n) :
    Integrable (fun g ↦ (act ρ σV σW g a).coefficient p) μ := by
  -- The coefficient at `p` is the zeroth jet at `p`, which is continuous in `g`.
  have h := ((continuous_iteratedFDeriv_coefficient_act hρ hσV hσW a 0).comp
    (continuous_id.prodMk (continuous_const (y := p)))).eval
      (continuous_const (y := (0 : Fin 0 → CoordinateSpace n × CoordinateSpace n)))
  simp only [Function.comp_def, iteratedFDeriv_zero_apply] at h
  exact h.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

@[simp]
theorem average_zero : average μ hρ hσV hσW (0 : Symbol n V W m) = 0 := by
  ext1
  funext p
  simp

@[simp]
theorem average_add (a b : Symbol n V W m) :
    average μ hρ hσV hσW (a + b) = average μ hρ hσV hσW a + average μ hρ hσV hσW b := by
  ext1
  funext p
  simp only [coefficient_average, act_add, coefficient_add, Pi.add_apply]
  exact MeasureTheory.integral_add (integrable_coefficient_act μ hρ hσV hσW a p)
    (integrable_coefficient_act μ hρ hσV hσW b p)

@[simp]
theorem average_smul (c : ℂ) (a : Symbol n V W m) :
    average μ hρ hσV hσW (c • a) = c • average μ hρ hσV hσW a := by
  ext1
  funext p
  simp only [coefficient_average, act_smul, coefficient_smul, Pi.smul_apply,
    MeasureTheory.integral_smul]

/-- **The average of the conjugates.** The quantization of the average of `a` is the average
`∫ g ∘ Op(a) ∘ g⁻¹ dμ(g)` of the conjugates of `Op(a)`. -/
theorem quantizeSchwartzValue_average (a : Symbol n V W m) (u : 𝓢(CoordinateSpace n, V))
    (x : CoordinateSpace n) :
    quantizeSchwartzValue (average μ hρ hσV hσW a).coefficient u x =
      ∫ g, σW g (quantizeSchwartzValue a.coefficient (schwartzRep ρ σV g⁻¹ u) ((ρ g).symm x))
        ∂μ := by
  simp only [average, quantizeSchwartzValue_integral, quantizeSchwartzValue_act]

/-- **Seminorm control.** Averaging over a probability measure preserves every bound on the
seminorms `p_{K,α,β}` of the symbols `g • a` that is uniform in `g`. -/
theorem seminorm_average_le [IsProbabilityMeasure μ] (a : Symbol n V W m)
    (K : TopologicalSpace.Compacts (CoordinateSpace n)) (α β : List (Fin n)) {C : ℝ}
    (hC : 0 ≤ C) (h : ∀ g, Symbol.seminorm K α β (act ρ σV σW g a) ≤ C) :
    Symbol.seminorm K α β (average μ hρ hσV hσW a) ≤ C := by
  unfold average
  exact seminorm_integral_le_of_probability μ _ _ _ K α β hC h

variable [MeasurableMul G] [μ.IsMulLeftInvariant]

/-- Averaging over a left-invariant measure gives a symbol fixed by every `g`. -/
@[simp]
theorem act_average (g : G) (a : Symbol n V W m) :
    act ρ σV σW g (average μ hρ hσV hσW a) = average μ hρ hσV hσW a := by
  ext1
  funext p
  rw [coefficient_act, coefficient_average, coefficient_average, ←
    ContinuousLinearEquiv.integral_comp_comm]
  simp_rw [← coefficient_act, ← act_mul]
  exact integral_mul_left_eq_self (fun h ↦ (act ρ σV σW h a).coefficient p) g

/-- The average of a symbol over a left-invariant measure is invariant. -/
theorem isInvariant_average (a : Symbol n V W m) :
    IsInvariant ρ σV σW (average μ hρ hσV hσW a) :=
  fun g ↦ act_average μ hρ hσV hσW g a

variable [IsProbabilityMeasure μ] [CompleteSpace W]

omit [MeasurableMul G] [μ.IsMulLeftInvariant] in
/-- An invariant symbol is its own average over a probability measure. -/
theorem IsInvariant.average_eq {a : Symbol n V W m} (ha : IsInvariant ρ σV σW a) :
    average μ hρ hσV hσW a = a := by
  ext1
  funext p
  simp [ha _]

/-- For a left-invariant probability measure, such as the normalized Haar measure, a symbol is
invariant exactly when it is its own average. -/
theorem average_eq_self_iff {a : Symbol n V W m} :
    average μ hρ hσV hσW a = a ↔ IsInvariant ρ σV σW a :=
  ⟨fun h ↦ h ▸ isInvariant_average μ hρ hσV hσW a, IsInvariant.average_eq μ hρ hσV hσW⟩

/-- Averaging is idempotent. -/
@[simp]
theorem average_average (a : Symbol n V W m) :
    average μ hρ hσV hσW (average μ hρ hσV hσW a) = average μ hρ hσV hσW a :=
  (isInvariant_average μ hρ hσV hσW a).average_eq μ hρ hσV hσW

end Average

end Symbol

end TauCeti
