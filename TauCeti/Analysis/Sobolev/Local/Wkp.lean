/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Local.Basic
public import TauCeti.Analysis.Sobolev.Wkp.Restriction
import Mathlib.Topology.MetricSpace.ProperSpace.Lemmas
import TauCeti.Analysis.Sobolev.WeakDeriv.Local

/-!
# Local Sobolev classes and the scalar spaces `W^{k,p}`

For a real function `u` on an open planar set `Ω`, this file compares the local Sobolev class
`TauCeti.MemWkpLoc p Ω k u`, whose iterated weak derivatives take values in iterated continuous
linear maps `ℂ →L[ℝ] ⋯ →L[ℝ] ℝ`, with the library's scalar Sobolev spaces `TauCeti.Wkp`, whose
iterated weak derivatives are recorded as iterated gradients in `TauCeti.IteratedGradient ℂ i`.

The two chains of derivatives match through the Riesz isometry
`InnerProductSpace.toDual ℝ ℂ : ℂ ≃ₗᵢ[ℝ] (ℂ →L[ℝ] ℝ)` applied in the innermost slot: the first weak
derivative of `u` is `z ↦ innerSL ℝ (G 0 z)` for the weak gradient `G 0 : ℂ → ℂ`, and each later
field `G (i + 1) : ℂ → IteratedGradient ℂ (i + 1) = ℂ →L[ℝ] IteratedGradient ℂ i` is the weak
derivative of `G i`. `TauCeti.memWkpLoc_succ_iff_exists_iteratedGradient` describes
`MemWkpLoc p Ω (k + 1) u` by such a chain `G 0, …, G k`, each field locally `Lᵖ` on `Ω`. The chain
describing an element of `Wkp` is `TauCeti.Wkp.exists_iteratedGradient_chain`, and conversely
`TauCeti.Wkp.exists_value_iteratedGradient_ae_eq_of_chain` assembles an element of `Wkp` from an
`Lᵖ` chain, by induction on the order. These hold on any open subset of a finite-dimensional real
inner product space.

The comparison theorem `TauCeti.memWkpLoc_iff_forall_wkp` then says that `u` lies in
`MemWkpLoc p Ω k` exactly when, for every open `W` whose closure is compact and contained in `Ω`,
the restriction of `u` to `W` is represented by an element of `Wkp volume W p k`. The forward
direction is `TauCeti.MemWkpLoc.exists_wkp_iteratedGradient_ae_eq`, which also matches the highest
recorded derivative with the chain of `u`. The converse glues the local weak derivatives with
`TauCeti.exists_hasWeakFDerivOn_iff_locally`, using their uniqueness on overlaps.

On the unit disc `D₁` this gives `TauCeti.memWkpLoc_ball_one_iff`: membership in
`MemWkpLoc p D₁ k` is equivalent to membership of the restrictions to the discs `D_r`, `r < 1`, in
`Wkp volume D_r p k`; in particular `TauCeti.MemWkpLoc.exists_wkp_ball_half` restricts a member to
`D_{1/2}`.

## Main declarations

* `TauCeti.Wkp.exists_iteratedGradient_chain`: the weak derivative chain of an element of `Wkp`.
* `TauCeti.Wkp.exists_value_iteratedGradient_ae_eq_of_chain`: an `Lᵖ` weak derivative chain is
  represented by an element of `Wkp`.
* `TauCeti.memWkpLoc_succ_iff_exists_iteratedGradient`: `MemWkpLoc` through iterated gradients.
* `TauCeti.MemWkpLoc.exists_wkp_iteratedGradient_ae_eq`, `TauCeti.MemWkpLoc.exists_wkp`: a member
  is represented by an element of `Wkp` on every relatively compact open subset.
* `TauCeti.memWkpLoc_of_forall_wkp`, `TauCeti.memWkpLoc_iff_forall_wkp`: the comparison.
* `TauCeti.memWkpLoc_ball_one_iff`, `TauCeti.MemWkpLoc.exists_wkp_ball_half`: the unit disc.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix B.1 (local Sobolev spaces).
* L. C. Evans, *Partial Differential Equations*, Chapter 5, §5.2.
-/

public section

noncomputable section

open Metric Set MeasureTheory TopologicalSpace
open scoped ENNReal

namespace TauCeti

/-! ### Iterated gradient chains of `Wkp` -/

section Wkp

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] {mu : Measure E} [mu.IsAddHaarMeasure]
  {Omega : Opens E} {p : ℝ≥0∞} [Fact (1 ≤ p)]

namespace Wkp

/-- **The weak derivative chain of a Sobolev function.** An element `v` of `W^{n+1,p}(Ω)` has
`Lᵖ` iterated weak gradients `G 0, …, G n`: the value of `v` has weak derivative
`innerSL ℝ ∘ G 0`, each `G (i + 1)` is the weak derivative of `G i`, and `G n` is the highest
recorded derivative of `v`. -/
theorem exists_iteratedGradient_chain (n : ℕ) (v : Wkp mu Omega p (n + 1)) :
    ∃ G : (i : ℕ) → E → IteratedGradient E i,
      HasWeakFDerivOn mu Omega (value (n + 1) v) (fun x => innerSL ℝ (G 0 x)) ∧
      (∀ i < n, HasWeakFDerivOn mu Omega (G i) (G (i + 1))) ∧
      (∀ i ≤ n, MemLp (G i) p (mu.restrict Omega)) ∧
      G n =ᵐ[mu.restrict Omega] iteratedGradient n v := by
  induction n with
  | zero =>
    refine ⟨Function.update (fun i _ => 0) 0 (iteratedGradient 0 v), ?_, fun i hi => absurd hi
      (Nat.not_lt_zero i), fun i hi => ?_, ?_⟩
    · simpa only [Function.update_self] using hasWeakFDerivOn_value v
    · obtain rfl := Nat.le_zero.1 hi
      simpa only [Function.update_self] using Lp.memLp (iteratedGradient 0 v)
    · simp only [Function.update_self, Filter.EventuallyEq.rfl]
  | succ n ih =>
    obtain ⟨G, h0, hG, hGp, htop⟩ := ih (lowerOrder (n + 1) v)
    refine ⟨Function.update G (n + 1) (iteratedGradient (n + 1) v), ?_, fun i hi => ?_,
      fun i hi => ?_, ?_⟩
    · rw [Function.update_of_ne (Nat.succ_ne_zero n).symm, value_succ]
      exact h0
    · rw [Function.update_of_ne (by omega)]
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
      · rw [Function.update_of_ne (by omega)]
        exact hG i hi
      · rw [Function.update_self]
        exact (hasWeakFDerivOn_iteratedGradient i v).congr_ae htop.symm
    · rcases Nat.lt_or_eq_of_le hi with hi | rfl
      · rw [Function.update_of_ne (by omega)]
        exact hGp i (by omega)
      · rw [Function.update_self]
        exact Lp.memLp _
    · simp only [Function.update_self, Filter.EventuallyEq.rfl]

/-- **An `Lᵖ` weak derivative chain is a Sobolev function.** If `u ∈ Lᵖ(Ω)` has weak derivative
`innerSL ℝ ∘ G 0`, each `G (i + 1)` is the weak derivative of `G i` for `i < n`, and every `G i`
with `i ≤ n` is in `Lᵖ(Ω)`, then `u` is represented by an element of `W^{n+1,p}(Ω)` whose highest
recorded derivative is `G n`. -/
theorem exists_value_iteratedGradient_ae_eq_of_chain (n : ℕ) {u : E → ℝ}
    {G : (i : ℕ) → E → IteratedGradient E i} (hu : MemLp u p (mu.restrict Omega))
    (h0 : HasWeakFDerivOn mu Omega u (fun x => innerSL ℝ (G 0 x)))
    (hG : ∀ i < n, HasWeakFDerivOn mu Omega (G i) (G (i + 1)))
    (hGp : ∀ i ≤ n, MemLp (G i) p (mu.restrict Omega)) :
    ∃ v : Wkp mu Omega p (n + 1), value (n + 1) v =ᵐ[mu.restrict Omega] u ∧
      iteratedGradient n v =ᵐ[mu.restrict Omega] G n := by
  induction n with
  | zero =>
    have hg : MemLp (G 0 : E → E) p (mu.restrict Omega) := hGp 0 le_rfl
    have hw : HasWeakFDerivOn mu Omega (hu.toLp u) fun x => innerSL ℝ (hg.toLp (G 0) x) := by
      refine (h0.congr_ae hu.coeFn_toLp.symm).congr_ae_deriv ?_
      filter_upwards [hg.coeFn_toLp] with x hx
      rw [hx]
    refine ⟨W1p.mk _ _ hw, ?_, ?_⟩
    · exact (Filter.EventuallyEq.of_eq (congrArg (fun f : Lp ℝ p (mu.restrict Omega) => (f : E → ℝ))
        ((value_one (W1p.mk _ _ hw)).trans (W1p.value_mk _ _ hw)))).trans hu.coeFn_toLp
    · exact (Filter.EventuallyEq.of_eq (congrArg (fun f : Lp E p (mu.restrict Omega) => (f : E → E))
        ((iteratedGradient_zero (W1p.mk _ _ hw)).trans (W1p.gradient_mk _ _ hw)))).trans
        hg.coeFn_toLp
  | succ n ih =>
    obtain ⟨v, hv, htop⟩ := ih (fun i hi => hG i (by omega)) (fun i hi => hGp i (by omega))
    have hg := hGp (n + 1) le_rfl
    refine ⟨mk n v (hg.toLp (G (n + 1)))
      (((hG n (Nat.lt_succ_self n)).congr_ae htop.symm).congr_ae_deriv hg.coeFn_toLp.symm), ?_, ?_⟩
    · rw [value_mk]
      exact hv
    · rw [iteratedGradient_mk]
      exact hg.coeFn_toLp

end Wkp

end Wkp

/-! ### Local Sobolev classes through iterated gradients -/

section Local

variable {p : ℝ≥0∞} {Ω : Opens ℂ} {k : ℕ}

/-- Every compact subset of an open planar set lies in an open set whose closure is compact and
contained in the open set. -/
private theorem exists_opens_superset_isCompact_closure {K : Set ℂ} (hK : IsCompact K)
    (hKΩ : K ⊆ Ω) :
    ∃ W : Opens ℂ, K ⊆ W ∧ IsCompact (closure (W : Set ℂ)) ∧ closure (W : Set ℂ) ⊆ Ω := by
  obtain ⟨V, hVo, hKV, hVΩ, hVc⟩ := exists_open_between_and_isCompact_closure hK Ω.isOpen hKΩ
  exact ⟨⟨V, hVo⟩, hKV, hVc, hVΩ⟩

/-- `Lᵖ` membership on the compact closure of `W` gives `Lᵖ` membership on `W`. -/
private theorem MemLpLoc.memLp_restrict_opens {F : Type*} [NormedAddCommGroup F] {f : ℂ → F}
    (hf : MemLpLoc p Ω f) {W : Opens ℂ} (hWc : IsCompact (closure (W : Set ℂ)))
    (hWΩ : closure (W : Set ℂ) ⊆ Ω) : MemLp f p (volume.restrict (W : Set ℂ)) :=
  (memLpLoc_iff.1 hf _ hWΩ hWc).mono_measure (Measure.restrict_mono subset_closure le_rfl)

/-- A function that is `Lᵖ`, up to an almost-everywhere change, on every relatively compact open
subset of `Ω` is locally `Lᵖ` on `Ω`. -/
private theorem memLpLoc_of_forall_opens {F : Type*} [NormedAddCommGroup F] {f : ℂ → F}
    (h : ∀ W : Opens ℂ, IsCompact (closure (W : Set ℂ)) → closure (W : Set ℂ) ⊆ Ω →
      ∃ g : ℂ → F, MemLp g p (volume.restrict (W : Set ℂ)) ∧ g =ᵐ[volume.restrict W] f) :
    MemLpLoc p Ω f := by
  refine memLpLoc_iff.2 fun K hKΩ hK => ?_
  obtain ⟨W, hKW, hWc, hWΩ⟩ := exists_opens_superset_isCompact_closure hK hKΩ
  obtain ⟨g, hg, hgf⟩ := h W hWc hWΩ
  have hmono : volume.restrict K ≤ volume.restrict (W : Set ℂ) := Measure.restrict_mono hKW le_rfl
  exact (hg.ae_eq hgf).mono_measure hmono

/-- A relatively compact open subset of `Ω` lies in `Ω`. -/
private theorem opens_le_of_closure_subset {W : Opens ℂ} (hWΩ : closure (W : Set ℂ) ⊆ Ω) :
    W ≤ Ω :=
  SetLike.coe_subset_coe.1 (subset_closure.trans hWΩ)

/-- `MemWkpLoc` for an iterated-gradient-valued field, through a chain of iterated gradients
indexed by absolute level: a field `g` at level `j` is in `MemWkpLoc p Ω n` exactly when it is the
level-`j` member of a chain whose fields from level `j` through `j + n` are locally `Lᵖ`, each the
weak derivative of the previous one. -/
private theorem memWkpLoc_iff_exists_chain (n : ℕ) : ∀ (j : ℕ) (g : ℂ → IteratedGradient ℂ j),
    MemWkpLoc p Ω n g ↔ ∃ G : (i : ℕ) → ℂ → IteratedGradient ℂ i, G j = g ∧
      (∀ i, j ≤ i → i < j + n → HasWeakFDerivOn volume Ω (G i) (G (i + 1))) ∧
      ∀ i, j ≤ i → i ≤ j + n → MemLpLoc p Ω (G i) := by
  induction n with
  | zero =>
    intro j g
    refine ⟨fun hg => ⟨Function.update (fun i _ => 0) j g, Function.update_self .., fun i hji hi =>
      absurd hi (by omega), fun i hji hi => ?_⟩, fun ⟨G, hGj, _, hGp⟩ => ?_⟩
    · obtain rfl : i = j := by omega
      simpa only [Function.update_self] using memWkpLoc_zero_iff.1 hg
    · subst hGj
      exact memWkpLoc_zero_iff.2 (hGp j le_rfl (by omega))
  | succ n ih =>
    intro j g
    rw [memWkpLoc_succ_iff_of_isOpen]
    constructor
    · rintro ⟨hg, D, hD, hDn⟩
      obtain ⟨G, hGD, hG, hGp⟩ := (ih (j + 1) D).1 hDn
      refine ⟨Function.update G j g, Function.update_self .., fun i hji hi => ?_,
        fun i hji hi => ?_⟩
      · rcases Nat.lt_or_eq_of_le hji with hji | rfl
        · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
          exact hG i hji (by omega)
        · rw [Function.update_self, Function.update_of_ne (by omega), hGD]
          exact hD
      · rcases Nat.lt_or_eq_of_le hji with hji | rfl
        · rw [Function.update_of_ne (by omega)]
          exact hGp i hji (by omega)
        · rw [Function.update_self]
          exact hg
    · rintro ⟨G, rfl, hG, hGp⟩
      exact ⟨hGp j le_rfl (by omega), G (j + 1), hG j le_rfl (by omega),
        (ih (j + 1) (G (j + 1))).2 ⟨G, rfl, fun i hji hi => hG i (by omega) (by omega),
          fun i hji hi => hGp i (by omega) (by omega)⟩⟩

/-- The Riesz isometry identifies `innerSL ℝ` with its own inverse on real linear functionals. -/
private theorem innerSL_toDual_symm (f : ℂ →L[ℝ] ℝ) :
    innerSL ℝ ((InnerProductSpace.toDual ℝ ℂ).symm f) = f := by
  ext w
  rw [innerSL_apply_apply, InnerProductSpace.toDual_symm_apply]

/-- **`MemWkpLoc` through iterated gradients.** A real function `u` lies in
`MemWkpLoc p Ω (n + 1)` exactly when it is locally `Lᵖ` on `Ω` and has locally `Lᵖ` iterated weak
gradients `G 0, …, G n` on `Ω`: the weak derivative of `u` is `innerSL ℝ ∘ G 0`, and each
`G (i + 1)` is the weak derivative of `G i`. The `(i + 1)`st weak derivative of `u` in the sense of
`MemWkpLoc` is `G i` with the Riesz isometry applied in the innermost slot. -/
theorem memWkpLoc_succ_iff_exists_iteratedGradient (n : ℕ) {u : ℂ → ℝ} :
    MemWkpLoc p Ω (n + 1) u ↔ MemLpLoc p Ω u ∧
      ∃ G : (i : ℕ) → ℂ → IteratedGradient ℂ i,
        HasWeakFDerivOn volume Ω u (fun z => innerSL ℝ (G 0 z)) ∧
        (∀ i < n, HasWeakFDerivOn volume Ω (G i) (G (i + 1))) ∧
        ∀ i ≤ n, MemLpLoc p Ω (G i) := by
  rw [memWkpLoc_succ_iff_of_isOpen]
  refine and_congr_right fun _ => ⟨fun ⟨D, hD, hDn⟩ => ?_, fun ⟨G, h0, hG, hGp⟩ => ?_⟩
  · obtain ⟨G, hG0, hG, hGp⟩ := (memWkpLoc_iff_exists_chain n 0
      (fun z => (InnerProductSpace.toDual ℝ ℂ).symm (D z))).1
      (hDn.clm_comp
        (InnerProductSpace.toDual ℝ ℂ).symm.toContinuousLinearEquiv.toContinuousLinearMap)
    refine ⟨G, ?_, fun i hi => hG i (Nat.zero_le i) (by omega),
      fun i hi => hGp i (Nat.zero_le i) (by omega)⟩
    simpa only [hG0, innerSL_toDual_symm] using hD
  · have hG0 := (memWkpLoc_iff_exists_chain n 0 (G 0)).2
      ⟨G, rfl, fun i _ hi => hG i (by omega), fun i _ hi => hGp i (by omega)⟩
    exact ⟨_, h0, hG0.clm_comp (innerSL ℝ (E := ℂ))⟩

/-- The gluing step for iterated-gradient-valued fields: a field `g` at level `j` that, on every
relatively compact open `W ⊆ Ω`, agrees almost everywhere with the level-`j` member of a chain of
`Lᵖ(W)` fields through level `j + n`, each the weak derivative on `W` of the previous one, lies in
`MemWkpLoc p Ω n`. -/
private theorem memWkpLoc_of_forall_chain (n : ℕ) : ∀ (j : ℕ) (g : ℂ → IteratedGradient ℂ j),
    (∀ W : Opens ℂ, IsCompact (closure (W : Set ℂ)) → closure (W : Set ℂ) ⊆ Ω →
      ∃ G : (i : ℕ) → ℂ → IteratedGradient ℂ i, G j =ᵐ[volume.restrict W] g ∧
        (∀ i, j ≤ i → i < j + n → HasWeakFDerivOn volume W (G i) (G (i + 1))) ∧
        ∀ i, j ≤ i → i ≤ j + n → MemLp (G i) p (volume.restrict (W : Set ℂ))) →
    MemWkpLoc p Ω n g := by
  induction n with
  | zero =>
    intro j g h
    exact memWkpLoc_zero_iff.2 <| memLpLoc_of_forall_opens fun W hWc hWΩ => by
      obtain ⟨G, hGj, -, hGp⟩ := h W hWc hWΩ
      exact ⟨G j, hGp j le_rfl le_rfl, hGj⟩
  | succ n ih =>
    intro j g h
    have hgp : MemLpLoc p Ω g := memLpLoc_of_forall_opens fun W hWc hWΩ => by
      obtain ⟨G, hGj, -, hGp⟩ := h W hWc hWΩ
      exact ⟨G j, hGp j le_rfl (by omega), hGj⟩
    have hloc : ∀ W : Opens ℂ, IsCompact (closure (W : Set ℂ)) → closure (W : Set ℂ) ⊆ Ω →
        ∃ G : (i : ℕ) → ℂ → IteratedGradient ℂ i, HasWeakFDerivOn volume W g (G (j + 1)) ∧
          (∀ i, j + 1 ≤ i → i < j + 1 + n → HasWeakFDerivOn volume W (G i) (G (i + 1))) ∧
          ∀ i, j + 1 ≤ i → i ≤ j + 1 + n → MemLp (G i) p (volume.restrict (W : Set ℂ)) := by
      intro W hWc hWΩ
      obtain ⟨G, hGj, hG, hGp⟩ := h W hWc hWΩ
      exact ⟨G, (hG j le_rfl (by omega)).congr_ae hGj, fun i hji hi => hG i (by omega)
        (by omega), fun i hji hi => hGp i (by omega) (by omega)⟩
    obtain ⟨D, hD⟩ : ∃ D : ℂ → ℂ →L[ℝ] IteratedGradient ℂ j, HasWeakFDerivOn volume Ω g D := by
      refine exists_hasWeakFDerivOn_iff_locally.2 fun x hx => ?_
      obtain ⟨W, hxW, hWc, hWΩ⟩ :=
        exists_opens_superset_isCompact_closure isCompact_singleton (singleton_subset_iff.2 hx)
      obtain ⟨G, hG0, -⟩ := hloc W hWc hWΩ
      exact ⟨W, hxW rfl, _, hG0⟩
    refine memWkpLoc_succ_iff_of_isOpen.2 ⟨hgp, D, hD, ih (j + 1) D fun W hWc hWΩ => ?_⟩
    obtain ⟨G, hG0, hG, hGp⟩ := hloc W hWc hWΩ
    exact ⟨G, hG0.ae_eq (hD.mono (opens_le_of_closure_subset hWΩ)), hG, hGp⟩

variable [Fact (1 ≤ p)]

/-- **Local Sobolev functions are Sobolev on relatively compact subdomains, with matching
derivatives.** Let `u ∈ MemWkpLoc p Ω (n + 1)` be real, with iterated weak gradients `G` on `Ω` as
in `TauCeti.memWkpLoc_succ_iff_exists_iteratedGradient`. On every open `W` whose closure is compact
and contained in `Ω`, `u` is represented by an element of `Wkp volume W p (n + 1)` whose highest
recorded derivative is `G n`. -/
theorem MemWkpLoc.exists_wkp_iteratedGradient_ae_eq (n : ℕ) {u : ℂ → ℝ}
    (hu : MemLpLoc p Ω u) {G : (i : ℕ) → ℂ → IteratedGradient ℂ i}
    (h0 : HasWeakFDerivOn volume Ω u (fun z => innerSL ℝ (G 0 z)))
    (hG : ∀ i < n, HasWeakFDerivOn volume Ω (G i) (G (i + 1)))
    (hGp : ∀ i ≤ n, MemLpLoc p Ω (G i)) {W : Opens ℂ}
    (hWc : IsCompact (closure (W : Set ℂ))) (hWΩ : closure (W : Set ℂ) ⊆ Ω) :
    ∃ v : Wkp volume W p (n + 1), Wkp.value (n + 1) v =ᵐ[volume.restrict W] u ∧
      Wkp.iteratedGradient n v =ᵐ[volume.restrict W] G n :=
  Wkp.exists_value_iteratedGradient_ae_eq_of_chain n (hu.memLp_restrict_opens hWc hWΩ)
    (h0.mono (opens_le_of_closure_subset hWΩ))
    (fun i hi => (hG i hi).mono (opens_le_of_closure_subset hWΩ))
    (fun i hi => (hGp i hi).memLp_restrict_opens hWc hWΩ)

/-- **A local Sobolev function is Sobolev on relatively compact subdomains.** If
`u ∈ MemWkpLoc p Ω k` is real, then on every open `W` whose closure is compact and contained in
`Ω`, `u` is represented by an element of `Wkp volume W p k`. -/
theorem MemWkpLoc.exists_wkp {u : ℂ → ℝ} (hu : MemWkpLoc p Ω k u) {W : Opens ℂ}
    (hWc : IsCompact (closure (W : Set ℂ))) (hWΩ : closure (W : Set ℂ) ⊆ Ω) :
    ∃ v : Wkp volume W p k, Wkp.value k v =ᵐ[volume.restrict W] u := by
  cases k with
  | zero =>
    have hW := MemLpLoc.memLp_restrict_opens (memWkpLoc_zero_iff.1 hu) hWc hWΩ
    exact ⟨hW.toLp u, by rw [Wkp.value_zero]; exact hW.coeFn_toLp⟩
  | succ n =>
    obtain ⟨hu, G, h0, hG, hGp⟩ := (memWkpLoc_succ_iff_exists_iteratedGradient n).1 hu
    obtain ⟨v, hv, -⟩ := MemWkpLoc.exists_wkp_iteratedGradient_ae_eq n hu h0 hG hGp hWc hWΩ
    exact ⟨v, hv⟩

/-- **Local Sobolev membership from Sobolev membership on relatively compact subdomains.** If the
restriction of a real function `u` to every open `W` whose closure is compact and contained in `Ω`
is represented by an element of `Wkp volume W p k`, then `u ∈ MemWkpLoc p Ω k`. -/
theorem memWkpLoc_of_forall_wkp {u : ℂ → ℝ}
    (h : ∀ W : Opens ℂ, IsCompact (closure (W : Set ℂ)) → closure (W : Set ℂ) ⊆ Ω →
      ∃ v : Wkp volume W p k, Wkp.value k v =ᵐ[volume.restrict W] u) :
    MemWkpLoc p Ω k u := by
  have hup : MemLpLoc p Ω u := memLpLoc_of_forall_opens fun W hWc hWΩ => by
    obtain ⟨v, hv⟩ := h W hWc hWΩ
    exact ⟨_, Lp.memLp (Wkp.value k v), hv⟩
  cases k with
  | zero => exact memWkpLoc_zero_iff.2 hup
  | succ n =>
    have hloc : ∀ W : Opens ℂ, IsCompact (closure (W : Set ℂ)) → closure (W : Set ℂ) ⊆ Ω →
        ∃ G : (i : ℕ) → ℂ → IteratedGradient ℂ i,
          HasWeakFDerivOn volume W u (fun z => innerSL ℝ (G 0 z)) ∧
          (∀ i < n, HasWeakFDerivOn volume W (G i) (G (i + 1))) ∧
          ∀ i ≤ n, MemLp (G i) p (volume.restrict (W : Set ℂ)) := by
      intro W hWc hWΩ
      obtain ⟨v, hv⟩ := h W hWc hWΩ
      obtain ⟨G, h0, hG, hGp, -⟩ := Wkp.exists_iteratedGradient_chain n v
      exact ⟨G, h0.congr_ae hv, hG, hGp⟩
    obtain ⟨D, hD⟩ : ∃ D : ℂ → ℂ →L[ℝ] ℝ, HasWeakFDerivOn volume Ω u D := by
      refine exists_hasWeakFDerivOn_iff_locally.2 fun x hx => ?_
      obtain ⟨W, hxW, hWc, hWΩ⟩ :=
        exists_opens_superset_isCompact_closure isCompact_singleton (singleton_subset_iff.2 hx)
      obtain ⟨G, h0, -⟩ := hloc W hWc hWΩ
      exact ⟨W, hxW rfl, _, h0⟩
    have hD' : MemWkpLoc p Ω n fun z => (InnerProductSpace.toDual ℝ ℂ).symm (D z) :=
      memWkpLoc_of_forall_chain n 0 _ fun W hWc hWΩ => by
        obtain ⟨G, h0, hG, hGp⟩ := hloc W hWc hWΩ
        refine ⟨G, ?_, fun i _ hi => hG i (by omega), fun i _ hi => hGp i (by omega)⟩
        filter_upwards [h0.ae_eq (hD.mono (opens_le_of_closure_subset hWΩ))] with z hz
        exact innerSL_inj.1 (hz.trans (innerSL_toDual_symm (D z)).symm)
    refine memWkpLoc_succ_iff_of_isOpen.2 ⟨hup, D, hD, ?_⟩
    have hDeq : (fun z => innerSL ℝ ((InnerProductSpace.toDual ℝ ℂ).symm (D z))) = D :=
      funext fun z => innerSL_toDual_symm (D z)
    simpa only [hDeq] using hD'.clm_comp (innerSL ℝ (E := ℂ))

/-- **Comparison with `Wkp`.** A real function lies in `MemWkpLoc p Ω k` exactly when its
restriction to every open `W` whose closure is compact and contained in `Ω` is represented by an
element of `Wkp volume W p k`. -/
theorem memWkpLoc_iff_forall_wkp {u : ℂ → ℝ} :
    MemWkpLoc p Ω k u ↔ ∀ W : Opens ℂ, IsCompact (closure (W : Set ℂ)) →
      closure (W : Set ℂ) ⊆ Ω → ∃ v : Wkp volume W p k, Wkp.value k v =ᵐ[volume.restrict W] u :=
  ⟨fun hu _ hWc hWΩ => hu.exists_wkp hWc hWΩ, memWkpLoc_of_forall_wkp⟩

/-- The open disc of radius `r` about the origin of `ℂ`, as an open set. -/
private abbrev disc (r : ℝ) : Opens ℂ := ⟨ball 0 r, isOpen_ball⟩

/-- **The comparison on the unit disc.** A real function lies in `MemWkpLoc p D₁ k` exactly when
its restriction to every disc `D_r` with `r < 1` is represented by an element of
`Wkp volume D_r p k`. -/
theorem memWkpLoc_ball_one_iff {u : ℂ → ℝ} :
    MemWkpLoc p (ball 0 1) k u ↔ ∀ r < 1,
      ∃ v : Wkp volume ⟨ball (0 : ℂ) r, isOpen_ball⟩ p k,
        Wkp.value k v =ᵐ[volume.restrict (ball 0 r)] u := by
  refine ⟨fun hu r hr => ?_, fun h => memWkpLoc_of_forall_wkp (Ω := disc 1) fun W hWc hWΩ => ?_⟩
  · exact hu.exists_wkp (Ω := disc 1) (W := disc r) ((isCompact_closedBall 0 r).of_isClosed_subset
      isClosed_closure closure_ball_subset_closedBall)
      (closure_ball_subset_closedBall.trans (closedBall_subset_ball hr))
  · obtain ⟨r, hr, hWr⟩ := exists_lt_subset_ball isClosed_closure hWΩ
    obtain ⟨v, hv⟩ := h r hr
    have hWr' : W ≤ disc r := SetLike.coe_subset_coe.1 (subset_closure.trans hWr)
    exact ⟨Wkp.restrictL hWr' k v, (Wkp.value_restrictL_ae hWr' k v).trans
      (ae_restrict_of_ae_restrict_of_subset (SetLike.coe_subset_coe.2 hWr') hv)⟩

/-- **The library check on `D_{1/2}`.** The restriction to `D_{1/2}` of a real member of
`MemWkpLoc p D₁ k` is represented by an element of `Wkp volume D_{1/2} p k`. The converse direction,
from all the discs `D_r` with `r < 1`, is `TauCeti.memWkpLoc_ball_one_iff`. -/
theorem MemWkpLoc.exists_wkp_ball_half {u : ℂ → ℝ}
    (hu : MemWkpLoc p (ball 0 1) k u) :
    ∃ v : Wkp volume ⟨ball (0 : ℂ) (1 / 2), isOpen_ball⟩ p k,
      Wkp.value k v =ᵐ[volume.restrict (ball 0 (1 / 2))] u :=
  memWkpLoc_ball_one_iff.1 hu (1 / 2) (by norm_num)

end Local

end TauCeti
