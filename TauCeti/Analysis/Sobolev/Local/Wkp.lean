/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Local.Basic
public import TauCeti.Analysis.Sobolev.Wkp.Restriction
import Mathlib.Topology.MetricSpace.ProperSpace.Lemmas
import TauCeti.Analysis.Normed.Operator.LinearIsometry
import TauCeti.Analysis.InnerProductSpace.Dual
import TauCeti.Analysis.Sobolev.Wkp.Chain
import TauCeti.Analysis.Sobolev.WeakDeriv.Local
import TauCeti.MeasureTheory.Function.LpSeminorm.Comp

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
`MemWkpLoc p Ω (k + 1) u` by such a chain `G 0, …, G k`, each field locally `Lᵖ` on `Ω`. The
corresponding chains of `Lᵖ` fields describing elements of `Wkp` are
`TauCeti.Wkp.exists_iteratedGradient_chain` and
`TauCeti.Wkp.exists_value_iteratedGradient_ae_eq_of_chain`, from
`TauCeti.Analysis.Sobolev.Wkp.Chain`.

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

* `TauCeti.memWkpLoc_succ_iff_exists_iteratedGradient`: `MemWkpLoc` through iterated gradients;
  `TauCeti.memWkpLoc_succ_iff_exists_iteratedGradient_interior` is the form on an arbitrary set.
* `TauCeti.memWkpLoc_of_iteratedGradient_chain`: a locally `Lᵖ` chain of iterated weak gradients on
  the interior of an arbitrary set `U` gives `MemWkpLoc` on `U`.
* `TauCeti.WeakDerivChainLe.eLpNorm_iteratedGradient_le`: a chain bound
  `TauCeti.WeakDerivChainLe` between two real functions bounds every level of their chains of
  iterated weak gradients.
* `TauCeti.MemWkpLoc.exists_wkp_iteratedGradient_ae_eq`, `TauCeti.MemWkpLoc.exists_wkp`: a member
  is represented by an element of `Wkp` on every relatively compact open subset.
* `TauCeti.memWkpLoc_of_forall_wkp`, `TauCeti.memWkpLoc_iff_forall_wkp`: the comparison.
* `TauCeti.Wkp.memWkpLoc_value_of_ae_le`: an element of `Wkp` on the interior of a set `U` that
  differs from `U` by a null set lies in `MemWkpLoc p U k`, as for a relatively open subset of the
  closed upper half-plane.
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

/-! ### Local Sobolev classes through iterated gradients -/

section Local

variable {p : ℝ≥0∞} {Ω : Opens ℂ} {k : ℕ}

/-- **`MemWkpLoc` from a chain of iterated gradients.** A chain of iterated-gradient-valued fields
`G j, …, G (j + n)`, each locally `Lᵖ` on `U` and each the weak derivative of the previous one on
the interior of `U`, gives `G j ∈ MemWkpLoc p U n`. The set `U` need not be open. -/
theorem memWkpLoc_of_iteratedGradient_chain {U : Set ℂ} (n j : ℕ)
    (G : (i : ℕ) → ℂ → IteratedGradient ℂ i)
    (hG : ∀ i, j ≤ i → i < j + n → HasWeakFDerivOn volume (Opens.interior U) (G i) (G (i + 1)))
    (hGp : ∀ i, j ≤ i → i ≤ j + n → MemLpLoc p U (G i)) : MemWkpLoc p U n (G j) := by
  induction n generalizing j with
  | zero => exact memWkpLoc_zero_iff.2 (hGp j le_rfl (by omega))
  | succ n ih =>
    exact memWkpLoc_succ_iff.2 ⟨hGp j le_rfl (by omega), G (j + 1), hG j le_rfl (by omega),
      ih (j + 1) (fun i hji hi => hG i (by omega) (by omega))
        fun i hji hi => hGp i (by omega) (by omega)⟩

/-- A field `g` at level `j` in `MemWkpLoc p U n` is the level-`j` member of a chain of iterated
gradients, indexed by absolute level, whose fields from level `j` through `j + n` are locally `Lᵖ`
on `U`, each the weak derivative on `interior U` of the previous one. The converse is
`TauCeti.memWkpLoc_of_iteratedGradient_chain`. -/
private theorem exists_iteratedGradient_chain_of_memWkpLoc {U : Set ℂ} (n : ℕ) (j : ℕ)
    (g : ℂ → IteratedGradient ℂ j) :
    MemWkpLoc p U n g → ∃ G : (i : ℕ) → ℂ → IteratedGradient ℂ i, G j = g ∧
      (∀ i, j ≤ i → i < j + n → HasWeakFDerivOn volume (Opens.interior U) (G i) (G (i + 1))) ∧
      ∀ i, j ≤ i → i ≤ j + n → MemLpLoc p U (G i) := by
  induction n generalizing j g with
  | zero =>
    intro hg
    refine ⟨Function.update (fun i _ => 0) j g, Function.update_self .., fun i hji hi =>
      absurd hi (by omega), fun i hji hi => ?_⟩
    obtain rfl : i = j := by omega
    simpa only [Function.update_self] using memWkpLoc_zero_iff.1 hg
  | succ n ih =>
    intro h
    obtain ⟨hg, D, hD, hDn⟩ := memWkpLoc_succ_iff.1 h
    obtain ⟨G, hGD, hG, hGp⟩ := ih (j + 1) D hDn
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

/-- **`MemWkpLoc` through iterated gradients, on an arbitrary set.** A real function `u` lies in
`MemWkpLoc p U (n + 1)` exactly when it is locally `Lᵖ` on `U` and has iterated weak gradients
`G 0, …, G n` on `interior U`, each locally `Lᵖ` on `U` itself: the weak derivative of `u` is
`innerSL ℝ ∘ G 0`, and each `G (i + 1)` is the weak derivative of `G i`. For a half-disc
`Ω ∩ {0 ≤ im}` the `Lᵖ` bounds reach the real axis while the derivatives live on `Ω ∩ {0 < im}`. -/
theorem memWkpLoc_succ_iff_exists_iteratedGradient_interior (n : ℕ) {U : Set ℂ} {u : ℂ → ℝ} :
    MemWkpLoc p U (n + 1) u ↔ MemLpLoc p U u ∧
      ∃ G : (i : ℕ) → ℂ → IteratedGradient ℂ i,
        HasWeakFDerivOn volume (Opens.interior U) u (fun z => innerSL ℝ (G 0 z)) ∧
        (∀ i < n, HasWeakFDerivOn volume (Opens.interior U) (G i) (G (i + 1))) ∧
        ∀ i ≤ n, MemLpLoc p U (G i) := by
  rw [memWkpLoc_succ_iff]
  refine and_congr_right fun _ => ⟨fun ⟨D, hD, hDn⟩ => ?_, fun ⟨G, h0, hG, hGp⟩ => ?_⟩
  · obtain ⟨G, hG0, hG, hGp⟩ := exists_iteratedGradient_chain_of_memWkpLoc n 0
      (fun z => InnerProductSpace.toDualSymmL (D z)) (hDn.clm_comp InnerProductSpace.toDualSymmL)
    refine ⟨G, ?_, fun i hi => hG i (Nat.zero_le i) (by omega),
      fun i hi => hGp i (Nat.zero_le i) (by omega)⟩
    simpa only [hG0, InnerProductSpace.toDualSymmL_apply,
      InnerProductSpace.innerSL_toDual_symm] using hD
  · exact ⟨_, h0, (memWkpLoc_of_iteratedGradient_chain n 0 G (fun i _ hi => hG i (by omega))
      fun i _ hi => hGp i (by omega)).clm_comp (innerSL ℝ (E := ℂ))⟩

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
  simpa only [Opens.interior_coe] using
    memWkpLoc_succ_iff_exists_iteratedGradient_interior n (p := p) (U := (Ω : Set ℂ))

/-- Chain bounds through iterated gradients, by induction on the level: let `Gf` and `Gg` be chains
of iterated weak gradients from level `j` through level `j + n`, on the interiors of `S` and `T`
respectively. If the level-`j` fields, read through a linear isometry `L`, satisfy the chain bound
`WeakDerivChainLe p S T C n`, then every level `i` of `Gf` from `j` through `j + n` has `Lᵖ(S)` norm
at most `C` times the `Lᵖ(T)` norm of the same level of `Gg`. -/
private theorem eLpNorm_le_of_weakDerivChainLe_iteratedGradient {S T : Set ℂ} {C : ℝ≥0∞}
    (n j : ℕ) {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (L : IteratedGradient ℂ j →ₗᵢ[ℝ] F) (Gf Gg : (i : ℕ) → ℂ → IteratedGradient ℂ i)
    (h : WeakDerivChainLe p S T C n (fun z => L (Gf j z)) (fun z => L (Gg j z)))
    (hGf : ∀ i, j ≤ i → i < j + n →
      HasWeakFDerivOn volume (Opens.interior S) (Gf i) (Gf (i + 1)))
    (hGg : ∀ i, j ≤ i → i < j + n →
      HasWeakFDerivOn volume (Opens.interior T) (Gg i) (Gg (i + 1)))
    (i : ℕ) (hji : j ≤ i) (hi : i ≤ j + n) :
    eLpNorm (Gf i) p (volume.restrict S) ≤ C * eLpNorm (Gg i) p (volume.restrict T) := by
  induction n generalizing j F with
  | zero =>
    obtain rfl : i = j := by omega
    simpa only [LinearIsometry.eLpNorm_comp] using h.eLpNorm_le
  | succ n ih =>
    rcases Nat.lt_or_eq_of_le hji with hji | rfl
    · have hf := (hGf j le_rfl (by omega)).clm_comp L.toContinuousLinearMap
      have hg := (hGg j le_rfl (by omega)).clm_comp L.toContinuousLinearMap
      simp only [LinearIsometry.coe_toContinuousLinearMap,
        ← LinearIsometry.postcomp_eq_comp (σ₁₃ := RingHom.id ℝ)] at hf hg
      exact ih (j + 1) (LinearIsometry.postcomp L) (h.weakFDeriv hf hg)
        (fun i hji hi => hGf i (by omega) (by omega))
        (fun i hji hi => hGg i (by omega) (by omega)) (by omega) (by omega)
    · simpa only [LinearIsometry.eLpNorm_comp] using h.eLpNorm_le

/-- **Chain bounds through iterated gradients.** Let `f` and `g` be real functions with iterated
weak gradients `Gf 0, …, Gf n` on the interior of `S` and `Gg 0, …, Gg n` on the interior of `T`:
the weak derivatives of `f` and `g` are `innerSL ℝ ∘ Gf 0` and `innerSL ℝ ∘ Gg 0`, and each level
is the weak derivative of the previous one. If `f` and `g` satisfy the chain bound
`WeakDerivChainLe p S T C (n + 1)`, then every `Gf i` with `i ≤ n` has `Lᵖ(S)` norm at most `C`
times the `Lᵖ(T)` norm of `Gg i`. -/
theorem WeakDerivChainLe.eLpNorm_iteratedGradient_le {S T : Set ℂ} {C : ℝ≥0∞} {n : ℕ}
    {f g : ℂ → ℝ} (h : WeakDerivChainLe p S T C (n + 1) f g)
    {Gf Gg : (i : ℕ) → ℂ → IteratedGradient ℂ i}
    (hf : HasWeakFDerivOn volume (Opens.interior S) f (fun z => innerSL ℝ (Gf 0 z)))
    (hg : HasWeakFDerivOn volume (Opens.interior T) g (fun z => innerSL ℝ (Gg 0 z)))
    (hGf : ∀ i < n, HasWeakFDerivOn volume (Opens.interior S) (Gf i) (Gf (i + 1)))
    (hGg : ∀ i < n, HasWeakFDerivOn volume (Opens.interior T) (Gg i) (Gg (i + 1)))
    {i : ℕ} (hi : i ≤ n) :
    eLpNorm (Gf i) p (volume.restrict S) ≤ C * eLpNorm (Gg i) p (volume.restrict T) := by
  have hc := h.weakFDeriv hf hg
  simp only [← InnerProductSpace.toContinuousLinearMap_toDualMap,
    LinearIsometry.coe_toContinuousLinearMap] at hc
  exact eLpNorm_le_of_weakDerivChainLe_iteratedGradient n 0 (InnerProductSpace.toDualMap ℝ ℂ)
    Gf Gg hc (fun i _ hi => hGf i (by omega)) (fun i _ hi => hGg i (by omega)) i (Nat.zero_le i)
    (by omega)

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
      obtain ⟨W, hWo, hxW, hWΩ, hWc⟩ := exists_open_between_and_isCompact_closure
        isCompact_singleton Ω.isOpen (singleton_subset_iff.2 hx)
      obtain ⟨G, hG0, -⟩ := hloc ⟨W, hWo⟩ hWc hWΩ
      exact ⟨⟨W, hWo⟩, hxW rfl, _, hG0⟩
    refine memWkpLoc_succ_iff_of_isOpen.2 ⟨hgp, D, hD, ih (j + 1) D fun W hWc hWΩ => ?_⟩
    obtain ⟨G, hG0, hG, hGp⟩ := hloc W hWc hWΩ
    exact ⟨G, hG0.ae_eq (hD.mono (SetLike.coe_subset_coe.1 (subset_closure.trans hWΩ))), hG, hGp⟩

variable [Fact (1 ≤ p)]

/-- **Sobolev functions on the interior are locally Sobolev on the whole set.** If a set `U` with
interior `O` is contained in `O` up to a null set, every element of `W^{k,p}(O)` lies in the local
Sobolev class `MemWkpLoc p U k`, whose `Lᵖ` bounds are taken on compact subsets of `U`, including
those leaving `O`. -/
theorem Wkp.memWkpLoc_value_of_ae_le {U : Set ℂ} {O : Opens ℂ} (hO : Opens.interior U = O)
    (hUO : U ≤ᵐ[volume] (O : Set ℂ)) (v : Wkp volume O p k) :
    MemWkpLoc p U k (Wkp.value k v : ℂ → ℝ) := by
  cases k with
  | zero => exact memWkpLoc_zero_iff.2 ((Lp.memLp _).memLpLoc_of_ae_le hUO)
  | succ n =>
    obtain ⟨G, h0, hG, hGp, -, -⟩ := Wkp.exists_iteratedGradient_chain n v
    exact memWkpLoc_succ_iff.2 ⟨(Lp.memLp _).memLpLoc_of_ae_le hUO, _, hO ▸ h0,
      (memWkpLoc_of_iteratedGradient_chain n 0 G (fun i _ hi => hO ▸ hG i (by omega))
        fun i _ hi => (hGp i (by omega)).memLpLoc_of_ae_le hUO).clm_comp (innerSL ℝ (E := ℂ))⟩

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
      Wkp.iteratedGradient n v =ᵐ[volume.restrict W] G n := by
  obtain ⟨v, hv, htop, -⟩ := Wkp.exists_value_iteratedGradient_ae_eq_of_chain n
    (hu.memLp_restrict_of_isCompact_closure hWc hWΩ)
    (h0.mono (SetLike.coe_subset_coe.1 (subset_closure.trans hWΩ)))
    (fun i hi => (hG i hi).mono (SetLike.coe_subset_coe.1 (subset_closure.trans hWΩ)))
    (fun i hi => (hGp i hi).memLp_restrict_of_isCompact_closure hWc hWΩ)
  exact ⟨v, hv, htop⟩

/-- **A local Sobolev function is Sobolev on relatively compact subdomains.** If
`u ∈ MemWkpLoc p Ω k` is real, then on every open `W` whose closure is compact and contained in
`Ω`, `u` is represented by an element of `Wkp volume W p k`. -/
theorem MemWkpLoc.exists_wkp {u : ℂ → ℝ} (hu : MemWkpLoc p Ω k u) {W : Opens ℂ}
    (hWc : IsCompact (closure (W : Set ℂ))) (hWΩ : closure (W : Set ℂ) ⊆ Ω) :
    ∃ v : Wkp volume W p k, Wkp.value k v =ᵐ[volume.restrict W] u := by
  cases k with
  | zero =>
    have hW := MemLpLoc.memLp_restrict_of_isCompact_closure (memWkpLoc_zero_iff.1 hu) hWc hWΩ
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
      obtain ⟨G, h0, hG, hGp, -, -⟩ := Wkp.exists_iteratedGradient_chain n v
      exact ⟨G, h0.congr_ae hv, hG, hGp⟩
    obtain ⟨D, hD⟩ : ∃ D : ℂ → ℂ →L[ℝ] ℝ, HasWeakFDerivOn volume Ω u D := by
      refine exists_hasWeakFDerivOn_iff_locally.2 fun x hx => ?_
      obtain ⟨W, hWo, hxW, hWΩ, hWc⟩ := exists_open_between_and_isCompact_closure
        isCompact_singleton Ω.isOpen (singleton_subset_iff.2 hx)
      obtain ⟨G, h0, -⟩ := hloc ⟨W, hWo⟩ hWc hWΩ
      exact ⟨⟨W, hWo⟩, hxW rfl, _, h0⟩
    have hD' : MemWkpLoc p Ω n fun z => (InnerProductSpace.toDual ℝ ℂ).symm (D z) :=
      memWkpLoc_of_forall_chain n 0 _ fun W hWc hWΩ => by
        obtain ⟨G, h0, hG, hGp⟩ := hloc W hWc hWΩ
        refine ⟨G, ?_, fun i _ hi => hG i (by omega), fun i _ hi => hGp i (by omega)⟩
        filter_upwards [h0.ae_eq (hD.mono (SetLike.coe_subset_coe.1
          (subset_closure.trans hWΩ)))] with z hz
        exact innerSL_inj.1 (hz.trans (InnerProductSpace.innerSL_toDual_symm (D z)).symm)
    refine memWkpLoc_succ_iff_of_isOpen.2 ⟨hup, D, hD, ?_⟩
    have hDeq : (fun z => innerSL ℝ ((InnerProductSpace.toDual ℝ ℂ).symm (D z))) = D :=
      funext fun z => InnerProductSpace.innerSL_toDual_symm (D z)
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
  refine ⟨fun hu r hr => ?_, fun h => memWkpLoc_of_forall_wkp (Ω := disc 1) fun W _ hWΩ => ?_⟩
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
