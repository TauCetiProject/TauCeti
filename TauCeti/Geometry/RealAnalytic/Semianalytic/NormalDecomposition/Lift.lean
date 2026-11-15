/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.RealAlgebraic.Stack.Sectors
public import TauCeti.Geometry.RealAnalytic.Semianalytic.NormalDecomposition.Basic
public import TauCeti.Geometry.RealAnalytic.Semianalytic.Stack

import Mathlib.Topology.TietzeExtension
import TauCeti.Analysis.Analytic.Submanifold.Dimension
import TauCeti.Topology.Algebra.Polynomial.Basic
import TauCeti.Topology.Algebra.Polynomial.Root.Extension
import TauCeti.Topology.Connected.FiniteFamily
import TauCeti.Topology.Order.RegionBetween

/-!
# Cylindrical lifting of normal decompositions along monic polynomial delineations

Let `𝒟` be a normal decomposition of `B ⊆ ℝⁿ`, let `B₀` be an open neighborhood of `closure B`,
and let `P : ι → ℝⁿ → ℝ[X]` be a finite family of monic polynomials of constant degrees `d k` on
`B₀` with analytic coefficients on `B₀`, whose real roots over `B` lie in `[a', b'] ⊂ (a, b)`. If
over each base piece `S ∈ 𝒟` the family `P` admits a delineation `D S hS`, then clipping the stack
cells of `D S hS` to the open height interval `(a, b)` yields a normal decomposition of the cylinder
`{v : ℝⁿ⁺¹ | Fin.tail v ∈ B ∧ v 0 ∈ Ioo a b}` on every piece of which all evaluations
`v ↦ (P k (Fin.tail v)).eval (v 0)` are sign-invariant (`TauCeti.IsNormalDecomposition.lift`).

Unlike simple-root stratification, distinct real roots on a base piece `S₁` may coalesce on a
frontier piece `S₀ ⊆ closure S₁`, and complex conjugate roots over `S₁` may collide at `S₀` to
create new real roots on `S₀` that are not limits of real roots on `S₁`. Both phenomena are
accommodated without refining the projection family:

* Because `S₁` has preconnected approach regions and `P k x ≠ 0` on `closure S₁ ⊆ B₀`, every
  bounded root function `(D S₁ hS₁).root i` extends continuously to `closure S₁`
  (`TauCeti.continuousOn_extendFrom_of_polynomial_root`) and remains a root of the same `P k x`
  there (`TauCeti.eval_extendFrom_eq_zero`).
* Over a connected piece `S₀ ⊆ closure S₁`, the extended root takes values in the finite distinct
  family `(D S₀ hS₀).root`, so by `TauCeti.eq_of_continuous_mem_range` it agrees with a single
  section of `D S₀ hS₀` throughout `S₀`.
* Augmenting each stack by the constant lower and upper bounds `a` and `b` turns every clipped
  sector into an open band between globally continuous endpoints, whose closure is the closed band
  over `closure S₁` (`TauCeti.closure_regionBetween`). Monotonicity of the induced map of augmented
  indices from `S₁` to `S₀` then yields both containment and strict dimension drop in the frontier
  condition.

## Main declarations

* `TauCeti.isPreconnectedApproachAt_of_notMem_closure`: trivial preconnected approach regions away
  from the closure.
* `TauCeti.IsPreconnectedApproachAt.cons_graph`, `TauCeti.IsPreconnectedApproachAt.cons_Ioo`:
  lifting preconnected approach regions to continuous graphs and open bands.
* `TauCeti.boundedStackCells`: stack cells clipped to an open height interval.
* `TauCeti.signInvariant_eval_of_mem_boundedStackCells`: sign-invariance of polynomial evaluations
  on clipped stack cells.
* `TauCeti.IsNormalDecomposition.lift`: lifting a normal decomposition by delineations of a monic
  analytic-coefficient polynomial family with bounded roots.

## References

* S. Łojasiewicz, *Ensembles semi-analytiques*, IHÉS lecture notes, 1965, §16–18.
* S. Łojasiewicz, *Triangulation of semi-analytic sets*, Annali della Scuola Normale Superiore di
  Pisa (3) 18 (1964), 449–474, §1–2.
* E. Bierstone and P. D. Milman, *Semianalytic and subanalytic sets*, Publications Mathématiques de
  l'IHÉS 67 (1988), 5–42, §2.
-/

public section

open Filter Function Polynomial Set Topology

namespace TauCeti

/-! ### Lifting preconnected approach regions to graphs and bands -/

/-- Outside `closure U`, a set is locally empty and therefore has preconnected approach regions. -/
theorem isPreconnectedApproachAt_of_notMem_closure {X : Type*} [TopologicalSpace X] {U : Set X}
    {x : X} (hx : x ∉ closure U) : IsPreconnectedApproachAt U x := by
  rw [isPreconnectedApproachAt_def]
  intro s hs
  refine ⟨s ∩ (closure U)ᶜ, inter_mem hs (isClosed_closure.isOpen_compl.mem_nhds hx),
    inter_subset_left, ?_⟩
  convert isPreconnected_empty (α := X) using 1
  exact eq_empty_iff_forall_notMem.2 fun z ⟨hzU, _, hzc⟩ ↦ hzc (subset_closure hzU)

private def consHomeomorph (n : ℕ) : ((Fin n → ℝ) × ℝ) ≃ₜ (Fin (n + 1) → ℝ) :=
  ((ContinuousLinearEquiv.prodComm ℝ (Fin n → ℝ) ℝ).trans
    (Fin.consEquivL ℝ fun _ : Fin (n + 1) ↦ ℝ)).toHomeomorph

private theorem consHomeomorph_apply {n : ℕ} (p : (Fin n → ℝ) × ℝ) :
    consHomeomorph n p = Fin.cons p.2 p.1 :=
  rfl

private theorem closure_cons_graph {n : ℕ} {S : Set (Fin n → ℝ)} {φ : (Fin n → ℝ) → ℝ}
    (hφ : Continuous φ) :
    closure {v : Fin (n + 1) → ℝ | Fin.tail v ∈ S ∧ v 0 = φ (Fin.tail v)} =
      {v : Fin (n + 1) → ℝ | Fin.tail v ∈ closure S ∧ v 0 = φ (Fin.tail v)} := by
  let g : (Fin n → ℝ) → Fin (n + 1) → ℝ := fun x ↦ Fin.cons (φ x) x
  have himg (A : Set (Fin n → ℝ)) :
      g '' A = {v : Fin (n + 1) → ℝ | Fin.tail v ∈ A ∧ v 0 = φ (Fin.tail v)} := by
    ext v
    refine ⟨?_, fun ⟨hvA, hv0⟩ ↦ ⟨Fin.tail v, hvA, ?_⟩⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨by simpa [g] using hx, by simp [g]⟩
    · dsimp only [g]
      rw [← hv0, Fin.cons_self_tail]
  have hleft : Function.LeftInverse (Fin.tail : (Fin (n + 1) → ℝ) → Fin n → ℝ) g :=
    fun x ↦ by simp [g]
  have hcl : IsClosedEmbedding g := hleft.isClosedEmbedding (by fun_prop) (by fun_prop)
  rw [← himg S, ← himg (closure S), hcl.closure_image_eq]

private theorem closure_cons_Ioo {n : ℕ} {S : Set (Fin n → ℝ)} {φ ψ : (Fin n → ℝ) → ℝ}
    (hφ : Continuous φ) (hψ : Continuous ψ) (hφψ : ∀ x ∈ S, φ x < ψ x) :
    closure {v : Fin (n + 1) → ℝ | Fin.tail v ∈ S ∧ φ (Fin.tail v) < v 0 ∧ v 0 < ψ (Fin.tail v)} =
      {v : Fin (n + 1) → ℝ |
        Fin.tail v ∈ closure S ∧ φ (Fin.tail v) ≤ v 0 ∧ v 0 ≤ ψ (Fin.tail v)} := by
  have hopen : {v : Fin (n + 1) → ℝ |
      Fin.tail v ∈ S ∧ φ (Fin.tail v) < v 0 ∧ v 0 < ψ (Fin.tail v)} =
      consHomeomorph n '' regionBetween φ ψ S := by
    ext v
    refine ⟨fun h ↦ ⟨(Fin.tail v, v 0), by simpa [regionBetween] using h, Fin.cons_self_tail v⟩, ?_⟩
    rintro ⟨⟨a, b⟩, hab, rfl⟩
    simpa [consHomeomorph_apply, regionBetween] using hab
  rw [hopen, ← (consHomeomorph n).image_closure,
    closure_regionBetween hφ.continuousOn hψ.continuousOn hφψ]
  ext v
  refine ⟨?_, fun h ↦ ⟨(Fin.tail v, v 0), by simpa using h, Fin.cons_self_tail v⟩⟩
  rintro ⟨⟨a, b⟩, hab, rfl⟩
  simpa [consHomeomorph_apply] using hab

/-- If `S ⊆ ℝⁿ` has preconnected approach regions everywhere and `φ : ℝⁿ → ℝ` is continuous, then
the graph of `φ` over `S` in `ℝⁿ⁺¹` has preconnected approach regions everywhere. -/
theorem IsPreconnectedApproachAt.cons_graph {n : ℕ} {S : Set (Fin n → ℝ)} {φ : (Fin n → ℝ) → ℝ}
    (hS : ∀ x, IsPreconnectedApproachAt S x) (hφ : Continuous φ) (y : Fin (n + 1) → ℝ) :
    IsPreconnectedApproachAt
      {v : Fin (n + 1) → ℝ | Fin.tail v ∈ S ∧ v 0 = φ (Fin.tail v)} y := by
  set E : Set (Fin (n + 1) → ℝ) := {v | Fin.tail v ∈ S ∧ v 0 = φ (Fin.tail v)}
  let g : (Fin n → ℝ) → Fin (n + 1) → ℝ := fun x ↦ Fin.cons (φ x) x
  by_cases hy : y ∈ closure E
  · rw [closure_cons_graph hφ] at hy
    have hE : E = g '' S := by
      ext v
      refine ⟨fun ⟨hvS, hv0⟩ ↦ ⟨Fin.tail v, hvS, ?_⟩, ?_⟩
      · dsimp only [g]
        rw [← hv0, Fin.cons_self_tail]
      · rintro ⟨x, hxS, rfl⟩
        exact ⟨by simpa [g] using hxS, by simp [g]⟩
    have hy_eq : g (Fin.tail y) = y := by
      dsimp only [g]
      rw [← hy.2, Fin.cons_self_tail]
    rw [hE, ← hy_eq]
    have hg : Continuous g := by fun_prop
    exact (hS (Fin.tail y)).image hg.continuousAt hg.continuousOn
      (by fun_prop : Continuous (Fin.tail : (Fin (n + 1) → ℝ) → Fin n → ℝ)).continuousAt
      (Fin.tail_cons _ _) fun x _ ↦ Fin.tail_cons _ _
  · exact isPreconnectedApproachAt_of_notMem_closure hy

private theorem image_bandInterp_eq {n : ℕ} {A : Set (Fin n → ℝ)} {α β : (Fin n → ℝ) → ℝ}
    (hαβ : ∀ x ∈ A, α x < β x) :
    (fun p : (Fin n → ℝ) × ℝ ↦
      (Fin.cons (α p.1 + p.2 * (β p.1 - α p.1)) p.1 : Fin (n + 1) → ℝ)) ''
      (A ×ˢ Ioo (0 : ℝ) 1) =
      {v : Fin (n + 1) → ℝ | Fin.tail v ∈ A ∧ α (Fin.tail v) < v 0 ∧ v 0 < β (Fin.tail v)} := by
  ext v
  refine ⟨?_, fun ⟨hvA, hαv, hvβ⟩ ↦ ?_⟩
  · rintro ⟨⟨x, s⟩, ⟨hxA, hs0, hs1⟩, rfl⟩
    have hpos : 0 < β x - α x := sub_pos.2 (hαβ x hxA)
    simp only [mem_ofPred_eq, Fin.tail_cons, Fin.cons_zero]
    exact ⟨hxA, by linarith [mul_pos hs0 hpos], by nlinarith⟩
  · have hpos : 0 < β (Fin.tail v) - α (Fin.tail v) := sub_pos.2 (hαβ _ hvA)
    refine ⟨(Fin.tail v, (v 0 - α (Fin.tail v)) / (β (Fin.tail v) - α (Fin.tail v))),
      ⟨hvA, div_pos (sub_pos.2 hαv) hpos, (div_lt_one hpos).2 (sub_lt_sub_right hvβ _)⟩, ?_⟩
    simp only [div_mul_cancel₀ _ hpos.ne', add_sub_cancel, Fin.cons_self_tail]

/-- If `S ⊆ ℝⁿ` has preconnected approach regions everywhere and `φ < ψ` on `S` with `φ, ψ`
continuous on `ℝⁿ`, then the open band
`{v | Fin.tail v ∈ S ∧ φ (Fin.tail v) < v 0 ∧ v 0 < ψ (Fin.tail v)}` has preconnected approach
regions everywhere, including at frontier points where `φ` and `ψ` coalesce. -/
theorem IsPreconnectedApproachAt.cons_Ioo {n : ℕ} {S : Set (Fin n → ℝ)} {φ ψ : (Fin n → ℝ) → ℝ}
    (hS : ∀ x, IsPreconnectedApproachAt S x) (hφ : Continuous φ) (hψ : Continuous ψ)
    (hφψ : ∀ x ∈ S, φ x < ψ x) (y : Fin (n + 1) → ℝ) :
    IsPreconnectedApproachAt
      {v : Fin (n + 1) → ℝ | Fin.tail v ∈ S ∧ φ (Fin.tail v) < v 0 ∧ v 0 < ψ (Fin.tail v)} y := by
  set E : Set (Fin (n + 1) → ℝ) :=
    {v | Fin.tail v ∈ S ∧ φ (Fin.tail v) < v 0 ∧ v 0 < ψ (Fin.tail v)}
  by_cases hy : y ∈ closure E
  · rw [closure_cons_Ioo hφ hψ hφψ] at hy
    obtain ⟨_, hyφ, hyψ⟩ := hy
    rw [isPreconnectedApproachAt_def]
    intro W hW
    have hW' : (consHomeomorph n) ⁻¹' W ∈ 𝓝 (Fin.tail y, y 0) :=
      (consHomeomorph n).continuous.continuousAt.preimage_mem_nhds
        (by simpa [consHomeomorph_apply, Fin.cons_self_tail] using hW)
    obtain ⟨U₀, hU₀, J, hJ, hUJ⟩ := mem_nhds_prod_iff.1 hW'
    obtain ⟨ε, hε, hεJ⟩ := Metric.mem_nhds_iff.1 hJ
    rw [Real.ball_eq_Ioo] at hεJ
    have hU₁ : {x | φ x < y 0 + ε ∧ y 0 - ε < ψ x} ∈ 𝓝 (Fin.tail y) :=
      ((isOpen_lt hφ continuous_const).inter (isOpen_lt continuous_const hψ)).mem_nhds
        ⟨show φ (Fin.tail y) < y 0 + ε by linarith, show y 0 - ε < ψ (Fin.tail y) by linarith⟩
    obtain ⟨T, hT, hTU, hST⟩ := isPreconnectedApproachAt_def.1 (hS (Fin.tail y))
      (U₀ ∩ {x | φ x < y 0 + ε ∧ y 0 - ε < ψ x}) (inter_mem hU₀ hU₁)
    have htail : Continuous (Fin.tail : (Fin (n + 1) → ℝ) → Fin n → ℝ) := by fun_prop
    refine ⟨{v : Fin (n + 1) → ℝ | Fin.tail v ∈ T ∧ v 0 ∈ Ioo (y 0 - ε) (y 0 + ε)},
      inter_mem (htail.continuousAt.preimage_mem_nhds hT)
        ((continuous_apply 0).continuousAt.preimage_mem_nhds (Ioo_mem_nhds (by linarith)
          (by linarith))),
      fun v ⟨hvT, hvI⟩ ↦ ?_, ?_⟩
    · have hp : (Fin.tail v, v 0) ∈ U₀ ×ˢ J := ⟨(hTU hvT).1, hεJ hvI⟩
      simpa [consHomeomorph_apply, Fin.cons_self_tail] using hUJ hp
    · have hαβ : ∀ x ∈ S ∩ T, max (φ x) (y 0 - ε) < min (ψ x) (y 0 + ε) := fun x ⟨hxS, hxT⟩ ↦
        lt_min (max_lt (hφψ x hxS) (hTU hxT).2.2) (max_lt (hTU hxT).2.1 (by linarith))
      have heq : E ∩ {v : Fin (n + 1) → ℝ | Fin.tail v ∈ T ∧ v 0 ∈ Ioo (y 0 - ε) (y 0 + ε)} =
          {v : Fin (n + 1) → ℝ | Fin.tail v ∈ S ∩ T ∧ max (φ (Fin.tail v)) (y 0 - ε) < v 0 ∧
            v 0 < min (ψ (Fin.tail v)) (y 0 + ε)} := by
        ext v
        simp only [E, mem_inter_iff, mem_ofPred_eq, mem_Ioo, max_lt_iff, lt_min_iff]
        tauto
      rw [heq, ← image_bandInterp_eq hαβ]
      have hmap : Continuous fun p : (Fin n → ℝ) × ℝ ↦
          (Fin.cons (max (φ p.1) (y 0 - ε) +
            p.2 * (min (ψ p.1) (y 0 + ε) - max (φ p.1) (y 0 - ε))) p.1 : Fin (n + 1) → ℝ) := by
        fun_prop
      exact (hST.prod isPreconnected_Ioo).image _ hmap.continuousOn
  · exact isPreconnectedApproachAt_of_notMem_closure hy

/-! ### Augmented stacks and clipped stack cells -/

/-- The cells of a stack `θ` over `S ⊆ ℝⁿ` clipped to the height interval `Ioo a b`. When all
values of `θ` lie in `Ioo a b`, sections are unchanged and sectors become bounded open bands. -/
noncomputable def boundedStackCells {n m : ℕ} (a b : ℝ) (S : Set (Fin n → ℝ)) (θ : Fin m → S → ℝ) :
    Set (Set (Fin (n + 1) → ℝ)) :=
  (· ∩ {v | v 0 ∈ Ioo a b}) '' stackCells S θ

/-- Polynomial evaluations of a delineation remain sign-invariant on every clipped stack cell. -/
theorem signInvariant_eval_of_mem_boundedStackCells {n : ℕ} {ι : Type*} {a b : ℝ}
    {S : Set (Fin n → ℝ)} {P : ι → (Fin n → ℝ) → ℝ[X]}
    (D : Delineation fun k (x : S) ↦ P k x) (k : ι) {E : Set (Fin (n + 1) → ℝ)}
    (hE : E ∈ boundedStackCells a b S D.root) :
    SignInvariant (fun v ↦ (P k (Fin.tail v)).eval (v 0)) E := by
  obtain ⟨T, hT, rfl⟩ := hE
  refine SignInvariant.mono ?_ inter_subset_left
  rcases mem_stackCells.1 hT with ⟨i, rfl⟩ | ⟨j, rfl⟩
  · rw [signInvariant_image]
    exact (D.signInvariant_sectionSet k i).congr fun z _ ↦ by simp
  · rw [signInvariant_image]
    exact (D.signInvariant_sectorSet k j).congr fun z _ ↦ by simp

private def augmentedStack {X : Type*} (a b : ℝ) {m : ℕ} (θ : Fin m → X → ℝ) :
    Fin (m + 2) → X → ℝ :=
  Fin.cons (fun _ ↦ a) (Fin.snoc θ (fun _ ↦ b))

private theorem augmentedStack_zero {X : Type*} (a b : ℝ) {m : ℕ} (θ : Fin m → X → ℝ) (x : X) :
    augmentedStack a b θ 0 x = a :=
  rfl

private theorem augmentedStack_inner {X : Type*} (a b : ℝ) {m : ℕ} (θ : Fin m → X → ℝ)
    (i : Fin m) (x : X) :
    augmentedStack a b θ i.castSucc.succ x = θ i x := by
  simp [augmentedStack]

private theorem augmentedStack_last {X : Type*} (a b : ℝ) {m : ℕ} (θ : Fin m → X → ℝ) (x : X) :
    augmentedStack a b θ (Fin.last (m + 1)) x = b := by
  rw [← Fin.succ_last m]
  simp [augmentedStack]

private theorem augmentedStack_congr {n m : ℕ} {a b : ℝ} {S : Set (Fin n → ℝ)}
    {θ : Fin m → S → ℝ} {G : Fin m → (Fin n → ℝ) → ℝ} (hG : ∀ i (x : S), G i x = θ i x)
    (r : Fin (m + 2)) (x : S) :
    augmentedStack a b G r x = augmentedStack a b θ r x := by
  refine r.cases rfl fun s ↦ s.lastCases ?_ fun i ↦ ?_
  · simp [Fin.succ_last, augmentedStack_last]
  · simp [augmentedStack_inner, hG i x]

private theorem continuous_augmentedStack {X : Type*} [TopologicalSpace X] {a b : ℝ} {m : ℕ}
    {θ : Fin m → X → ℝ} (hc : ∀ i, Continuous (θ i)) (r : Fin (m + 2)) :
    Continuous (augmentedStack a b θ r) := by
  induction r using Fin.cases with
  | zero => exact continuous_const
  | succ s =>
    induction s using Fin.lastCases with
    | last =>
      rw [Fin.succ_last, funext (augmentedStack_last a b θ)]
      exact continuous_const
    | cast i => simpa [augmentedStack] using hc i

private theorem strictMono_augmentedStack {X : Type*} {a b : ℝ} {m : ℕ} {θ : Fin m → X → ℝ}
    (hab : a < b) (hθ : ∀ x, StrictMono fun i ↦ θ i x) (hbnd : ∀ i x, θ i x ∈ Ioo a b) (x : X) :
    StrictMono fun r ↦ augmentedStack a b θ r x := by
  intro r₁ r₂ hlt
  induction r₁ using Fin.cases with
  | zero =>
    induction r₂ using Fin.cases with
    | zero => exact absurd hlt (lt_irrefl _)
    | succ s₂ =>
      induction s₂ using Fin.lastCases with
      | last => simpa [augmentedStack_zero, Fin.succ_last, augmentedStack_last] using hab
      | cast i₂ => simpa [augmentedStack_zero, augmentedStack_inner] using (hbnd i₂ x).1
  | succ s₁ =>
    induction r₂ using Fin.cases with
    | zero => exact absurd hlt (Fin.not_lt_zero _)
    | succ s₂ =>
      have hs : s₁ < s₂ := Fin.succ_lt_succ_iff.1 hlt
      induction s₁ using Fin.lastCases with
      | last => exact absurd hs (not_lt_of_ge (Fin.le_last _))
      | cast i₁ =>
        induction s₂ using Fin.lastCases with
        | last =>
          simpa [augmentedStack_inner, Fin.succ_last, augmentedStack_last] using (hbnd i₁ x).2
        | cast i₂ =>
          simpa [augmentedStack_inner] using hθ x (Fin.castSucc_lt_castSucc_iff.1 hs)

private theorem sectionSet_inter_Ioo_eq {n m : ℕ} {a b : ℝ} {S : Set (Fin n → ℝ)}
    {θ : Fin m → S → ℝ} (hbnd : ∀ i x, θ i x ∈ Ioo a b) (i : Fin m) :
    cylinder S '' sectionSet θ i ∩ {v | v 0 ∈ Ioo a b} = cylinder S '' sectionSet θ i :=
  inter_eq_left.2 fun v hv ↦ by
    obtain ⟨hx, hv0⟩ := mem_image_cylinder.1 hv
    rw [mem_sectionSet] at hv0
    dsimp only at hv0
    rw [mem_ofPred_eq, ← hv0]
    exact hbnd i ⟨Fin.tail v, hx⟩

private theorem sectorLower_iff {X : Type*} {a b : ℝ} {m : ℕ} {θ : Fin m → X → ℝ}
    (hbnd : ∀ i x, θ i x ∈ Ioo a b) (j : Fin (m + 1)) (x : X) (t : ℝ) :
    ((∀ i : Fin m, i.succ = j → θ i x < t) ∧ a < t) ↔
      augmentedStack a b θ j.castSucc x < t := by
  refine j.cases ?_ fun i₀ ↦ ?_
  · simp [augmentedStack_zero]
  · simp only [Fin.succ_inj, forall_eq, ← Fin.succ_castSucc, augmentedStack_inner]
    exact ⟨fun h ↦ h.1, fun h ↦ ⟨h, (hbnd i₀ x).1.trans h⟩⟩

private theorem sectorUpper_iff {X : Type*} {a b : ℝ} {m : ℕ} {θ : Fin m → X → ℝ}
    (hbnd : ∀ i x, θ i x ∈ Ioo a b) (j : Fin (m + 1)) (x : X) (t : ℝ) :
    ((∀ i : Fin m, i.castSucc = j → t < θ i x) ∧ t < b) ↔
      t < augmentedStack a b θ j.succ x := by
  refine j.lastCases ?_ fun i₀ ↦ ?_
  · simp [Fin.succ_last, augmentedStack_last, Fin.castSucc_ne_last]
  · simp only [Fin.castSucc_inj, forall_eq, augmentedStack_inner]
    exact ⟨fun h ↦ h.1, fun h ↦ ⟨h, h.trans (hbnd i₀ x).2⟩⟩

private theorem sectorSet_inter_Ioo_eq {n m : ℕ} {a b : ℝ} {S : Set (Fin n → ℝ)}
    {θ : Fin m → S → ℝ} (hab : a < b) (hθ : ∀ x, StrictMono fun i ↦ θ i x)
    (hbnd : ∀ i x, θ i x ∈ Ioo a b) (j : Fin (m + 1)) :
    cylinder S '' sectorSet θ j ∩ {v | v 0 ∈ Ioo a b} =
      cylinder S '' sectorSet (augmentedStack a b θ) j.castSucc.succ := by
  have hmono : ∀ x, Monotone fun r ↦ augmentedStack a b θ r x :=
    fun x ↦ (strictMono_augmentedStack hab hθ hbnd x).monotone
  ext v
  simp only [mem_inter_iff, mem_image_cylinder, mem_ofPred_eq, mem_Ioo,
    sectorSet_castSucc_succ hmono, mem_sectorSet_iff_of_monotone fun x ↦ (hθ x).monotone]
  refine ⟨fun ⟨⟨hx, hl, hu⟩, ha, hb⟩ ↦ ⟨hx, (sectorLower_iff hbnd j ⟨_, hx⟩ _).1 ⟨hl, ha⟩,
    (sectorUpper_iff hbnd j ⟨_, hx⟩ _).1 ⟨hu, hb⟩⟩, fun ⟨hx, hl, hu⟩ ↦ ?_⟩
  obtain ⟨hl', ha⟩ := (sectorLower_iff hbnd j ⟨_, hx⟩ _).2 hl
  obtain ⟨hu', hb⟩ := (sectorUpper_iff hbnd j ⟨_, hx⟩ _).2 hu
  exact ⟨⟨hx, hl', hu'⟩, ha, hb⟩

private theorem mem_boundedStackCells_iff {n m : ℕ} {a b : ℝ} {S : Set (Fin n → ℝ)}
    {θ : Fin m → S → ℝ} (hab : a < b) (hθ : ∀ x, StrictMono fun i ↦ θ i x)
    (hbnd : ∀ i x, θ i x ∈ Ioo a b) {E : Set (Fin (n + 1) → ℝ)} :
    E ∈ boundedStackCells a b S θ ↔
      (∃ i : Fin m, cylinder S '' sectionSet θ i = E) ∨
        ∃ j : Fin (m + 1),
          cylinder S '' sectorSet (augmentedStack a b θ) j.castSucc.succ = E := by
  simp only [boundedStackCells, mem_image, mem_stackCells]
  constructor
  · rintro ⟨T, (⟨i, rfl⟩ | ⟨j, rfl⟩), rfl⟩
    · exact Or.inl ⟨i, (sectionSet_inter_Ioo_eq hbnd i).symm⟩
    · exact Or.inr ⟨j, (sectorSet_inter_Ioo_eq hab hθ hbnd j).symm⟩
  · rintro (⟨i, rfl⟩ | ⟨j, rfl⟩)
    · exact ⟨_, Or.inl ⟨i, rfl⟩, sectionSet_inter_Ioo_eq hbnd i⟩
    · exact ⟨_, Or.inr ⟨j, rfl⟩, sectorSet_inter_Ioo_eq hab hθ hbnd j⟩

private theorem image_tail_of_mem_boundedStackCells {n m : ℕ} {a b : ℝ} {S : Set (Fin n → ℝ)}
    {θ : Fin m → S → ℝ} (hab : a < b) (hθ : ∀ x, StrictMono fun i ↦ θ i x)
    (hbnd : ∀ i x, θ i x ∈ Ioo a b) {E : Set (Fin (n + 1) → ℝ)}
    (hE : E ∈ boundedStackCells a b S θ) : Fin.tail '' E = S := by
  rcases (mem_boundedStackCells_iff hab hθ hbnd).1 hE with ⟨i, rfl⟩ | ⟨j, rfl⟩
  · exact image_tail_of_mem_stackCells hθ (image_cylinder_sectionSet_mem_stackCells i)
  · exact image_tail_of_mem_stackCells (strictMono_augmentedStack hab hθ hbnd)
      (image_cylinder_sectorSet_mem_stackCells j.castSucc.succ)

/-! ### Continuous extension and frontier comparison of delineation roots -/

private theorem exists_continuous_root_extension {n : ℕ} {ι : Type*} {a a' b' b : ℝ}
    {B₀ S : Set (Fin n → ℝ)} {d : ι → ℕ} {P : ι → (Fin n → ℝ) → ℝ[X]}
    (hB₀ : IsOpen B₀) (hScl : closure S ⊆ B₀) (hab' : a < a') (hb'b : b' < b)
    (hmonic : ∀ k, ∀ x ∈ B₀, (P k x).Monic)
    (hdeg : ∀ k, ∀ x ∈ B₀, (P k x).natDegree = d k)
    (hcoeff : ∀ k j, j ≤ d k → ContinuousOn (fun x ↦ (P k x).coeff j) B₀)
    (hroots : ∀ k, ∀ x ∈ S, ∀ t, (P k x).IsRoot t → t ∈ Icc a' b')
    (happ : ∀ x, IsPreconnectedApproachAt S x)
    (D : Delineation fun k (x : S) ↦ P k x) :
    ∃ G : Fin D.count → (Fin n → ℝ) → ℝ,
      (∀ i, Continuous (G i)) ∧
      (∀ i (x : S), G i x = D.root i x) ∧
      (∀ i, ∀ x ∈ closure S, G i x ∈ Ioo a b) ∧
      ∀ i, ∀ x ∈ closure S, ∃ k, (P k x).IsRoot (G i x) := by
  classical
  have hsingle (i : Fin D.count) : ∃ g : (Fin n → ℝ) → ℝ,
      Continuous g ∧ (∀ x : S, g x = D.root i x) ∧
      (∀ x ∈ closure S, g x ∈ Ioo a b) ∧ ∀ x ∈ closure S, ∃ k, (P k x).IsRoot (g x) := by
    obtain ⟨k₀, hk₀⟩ := D.exists_multiplicity_pos i
    let f₀ : (Fin n → ℝ) → ℝ := Function.extend Subtype.val (D.root i) fun _ ↦ 0
    have hf₀ (x : S) : f₀ x = D.root i x := Subtype.val_injective.extend_apply _ _ x
    have hf₀c : ContinuousOn f₀ S :=
      continuousOn_iff_continuous_domRestrict.2 ((D.continuous_root i).congr fun x ↦ (hf₀ x).symm)
    have hrt (y : Fin n → ℝ) (hy : y ∈ S) : (P k₀ y).IsRoot (f₀ y) := by
      rw [hf₀ ⟨y, hy⟩]
      exact (rootMultiplicity_pos'.1 (D.rootMultiplicity_root k₀ i ⟨y, hy⟩ ▸ hk₀)).2
    have himg : f₀ '' S ⊆ Icc a' b' := by
      rintro _ ⟨y, hy, rfl⟩
      exact hroots k₀ y hy _ (hrt y hy)
    have hp : ContinuousOn (fun z : (Fin n → ℝ) × ℝ ↦ (P k₀ z.1).eval z.2)
        (closure S ×ˢ univ) := fun z hz ↦
      (Polynomial.continuousAt_eval
        (fun j hj ↦ ((hcoeff k₀ j hj).continuousAt (hB₀.mem_nhds (hScl hz.1))).comp_of_eq
          continuous_fst.continuousAt rfl)
        (continuous_fst.continuousAt.eventually
          (Filter.mem_of_superset (hB₀.mem_nhds (hScl hz.1)) fun y hy ↦ (hdeg k₀ y hy).le))
        continuous_snd.continuousAt).continuousWithinAt
    have hExt : ContinuousOn (extendFrom S f₀) (closure S) :=
      continuousOn_extendFrom_of_polynomial_root hp hf₀c hrt (isCompact_Icc.isBounded.subset himg)
        (fun x hx ↦ (hmonic k₀ x (hScl hx)).ne_zero) fun x _ ↦ happ x
    have hextEq : EqOn (extendFrom S f₀) f₀ S := extendFrom_extends hf₀c
    obtain ⟨g, hg⟩ := (⟨_, hExt.domRestrict⟩ : C(closure S, ℝ)).exists_restrict_eq isClosed_closure
    have hgEq : EqOn g (extendFrom S f₀) (closure S) := fun x hx ↦ congr($hg ⟨x, hx⟩)
    refine ⟨g, g.continuous, fun x ↦ ?_, fun x hx ↦ ?_, fun x hx ↦ ⟨k₀, ?_⟩⟩
    · rw [hgEq (subset_closure x.2), hextEq x.2, hf₀ x]
    · have hmem : extendFrom S f₀ x ∈ Icc a' b' :=
        closure_minimal ((hextEq.image_eq ▸ himg : extendFrom S f₀ '' S ⊆ Icc a' b')) isClosed_Icc
          (hExt.image_closure (mem_image_of_mem _ hx))
      rw [hgEq hx]
      exact ⟨hab'.trans_le hmem.1, hmem.2.trans_lt hb'b⟩
    · rw [hgEq hx]
      exact eval_extendFrom_eq_zero hp hf₀c hrt hExt hx
  choose G hGc hGeq hGbnd hGroot using hsingle
  exact ⟨G, hGc, hGeq, hGbnd, hGroot⟩

private theorem exists_monotone_index_map {n m₁ : ℕ} {ι : Type*} {a b : ℝ}
    {B₀ S₀ S₁ : Set (Fin n → ℝ)} {P : ι → (Fin n → ℝ) → ℝ[X]}
    (D₀ : Delineation fun k (x : S₀) ↦ P k x) {G₁ : Fin m₁ → (Fin n → ℝ) → ℝ}
    (hab : a < b) (hS₀ : IsConnected S₀) (hS₀B₀ : S₀ ⊆ B₀) (hS₀₁ : S₀ ⊆ closure S₁)
    (hmonic : ∀ k, ∀ x ∈ B₀, (P k x).Monic)
    (hbnd₀ : ∀ i x, D₀.root i x ∈ Ioo a b)
    (hG₁c : ∀ i, Continuous (G₁ i))
    (hG₁root : ∀ i, ∀ x ∈ closure S₁, ∃ k, (P k x).IsRoot (G₁ i x))
    (hG₁mono : ∀ r₁ r₂ : Fin (m₁ + 2), r₁ ≤ r₂ →
      ∀ x ∈ closure S₁, augmentedStack a b G₁ r₁ x ≤ augmentedStack a b G₁ r₂ x) :
    ∃ ρ : Fin (m₁ + 2) → Fin (D₀.count + 2),
      Monotone ρ ∧
      (∀ i : Fin m₁, ∃ l : Fin D₀.count, ρ i.castSucc.succ = l.castSucc.succ) ∧
      ∀ r (x : S₀), augmentedStack a b G₁ r x = augmentedStack a b D₀.root (ρ r) x := by
  classical
  let := isPreconnected_iff_preconnectedSpace.1 hS₀.isPreconnected
  obtain ⟨x₀⟩ := hS₀.nonempty.to_subtype
  have hinterior (i : Fin m₁) : ∃ l : Fin D₀.count, ∀ x : S₀, D₀.root l x = G₁ i x := by
    have hmem (x : S₀) : G₁ i x ∈ range fun l ↦ D₀.root l x := by
      obtain ⟨k, hk⟩ := hG₁root i x (hS₀₁ x.2)
      exact D₀.exists_root_eq k x (hmonic k x (hS₀B₀ x.2)).ne_zero _ hk
    obtain ⟨l₀, hl₀⟩ := hmem x₀
    refine ⟨l₀, fun x ↦ congrFun (eq_of_continuous_mem_range D₀.continuous_root
      ((hG₁c i).comp continuous_subtype_val)
      (fun y j hj ↦ (D₀.strictMono_root y).injective hj) hmem hl₀) x⟩
  choose l hl using hinterior
  let ρ : Fin (m₁ + 2) → Fin (D₀.count + 2) :=
    Fin.cons 0 (Fin.snoc (fun i ↦ (l i).castSucc.succ) (Fin.last (D₀.count + 1)))
  have hρeq (r : Fin (m₁ + 2)) (x : S₀) :
      augmentedStack a b G₁ r x = augmentedStack a b D₀.root (ρ r) x := by
    refine r.cases rfl fun s ↦ s.lastCases ?_ fun i ↦ ?_
    · simp [ρ, Fin.succ_last, augmentedStack_last]
    · simp [ρ, augmentedStack_inner, hl i x]
  refine ⟨ρ, fun r₁ r₂ hr ↦ ?_, fun i ↦ ⟨l i, by simp [ρ]⟩, hρeq⟩
  have hle := hG₁mono r₁ r₂ hr x₀ (hS₀₁ x₀.2)
  rw [hρeq r₁ x₀, hρeq r₂ x₀] at hle
  exact (strictMono_augmentedStack hab D₀.strictMono_root hbnd₀ x₀).le_iff_le.1 hle

private theorem section_eq_cons_graph {n m : ℕ} {S : Set (Fin n → ℝ)} {θ : Fin m → S → ℝ}
    {G : Fin m → (Fin n → ℝ) → ℝ} (hG : ∀ i (x : S), G i x = θ i x) (i : Fin m) :
    cylinder S '' sectionSet θ i =
      {v : Fin (n + 1) → ℝ | Fin.tail v ∈ S ∧ v 0 = G i (Fin.tail v)} := by
  ext v
  simp only [mem_image_cylinder, mem_sectionSet, mem_ofPred_eq]
  exact ⟨fun ⟨hx, hv⟩ ↦ ⟨hx, hv.symm.trans (hG i ⟨_, hx⟩).symm⟩,
    fun ⟨hx, hv⟩ ↦ ⟨hx, (hG i ⟨_, hx⟩).symm.trans hv.symm⟩⟩

private theorem sector_eq_cons_Ioo {n m : ℕ} {a b : ℝ} {S : Set (Fin n → ℝ)} {θ : Fin m → S → ℝ}
    {G : Fin m → (Fin n → ℝ) → ℝ} (hab : a < b) (hθ : ∀ x, StrictMono fun i ↦ θ i x)
    (hbnd : ∀ i x, θ i x ∈ Ioo a b) (hG : ∀ i (x : S), G i x = θ i x) (j : Fin (m + 1)) :
    cylinder S '' sectorSet (augmentedStack a b θ) j.castSucc.succ =
      {v : Fin (n + 1) → ℝ | Fin.tail v ∈ S ∧
        augmentedStack a b G j.castSucc (Fin.tail v) < v 0 ∧
        v 0 < augmentedStack a b G j.succ (Fin.tail v)} := by
  have hmono : ∀ x, Monotone fun r ↦ augmentedStack a b θ r x :=
    fun x ↦ (strictMono_augmentedStack hab hθ hbnd x).monotone
  ext v
  simp only [mem_image_cylinder, sectorSet_castSucc_succ hmono, mem_ofPred_eq]
  exact ⟨fun ⟨hx, hl, hu⟩ ↦ ⟨hx, by rwa [augmentedStack_congr hG _ ⟨_, hx⟩],
      by rwa [augmentedStack_congr hG _ ⟨_, hx⟩]⟩,
    fun ⟨hx, hl, hu⟩ ↦ ⟨hx, by rwa [← augmentedStack_congr hG _ ⟨_, hx⟩],
      by rwa [← augmentedStack_congr hG _ ⟨_, hx⟩]⟩⟩

private theorem isSemianalytic_height_mem_Ioo {n : ℕ} (a b : ℝ) :
    IsSemianalytic {v : Fin (n + 1) → ℝ | v 0 ∈ Ioo a b} := by
  have h0 : AnalyticOnNhd ℝ (fun v : Fin (n + 1) → ℝ ↦ v 0) univ :=
    fun v _ ↦ (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (n + 1) ↦ ℝ) 0).analyticAt v
  have h1 := (h0.sub (analyticOnNhd_const (v := a))).isSemianalytic_setOf_pos
  have h2 := ((analyticOnNhd_const (v := b)).sub h0).isSemianalytic_setOf_pos
  convert h1.inter h2 using 1
  ext v
  simp only [mem_ofPred_eq, mem_Ioo, mem_inter_iff, Pi.sub_apply, sub_pos]

private theorem frontier_containment_section {n m₀ m₁ : ℕ} {a b : ℝ} {S₀ S₁ : Set (Fin n → ℝ)}
    {θ₀ : Fin m₀ → S₀ → ℝ} {θ₁ : Fin m₁ → S₁ → ℝ} {G₁ : Fin m₁ → (Fin n → ℝ) → ℝ}
    {ρ : Fin (m₁ + 2) → Fin (m₀ + 2)} (hab : a < b)
    (hθ₀ : ∀ x, StrictMono fun i ↦ θ₀ i x) (hbnd₀ : ∀ i x, θ₀ i x ∈ Ioo a b)
    (hG₁c : ∀ i, Continuous (G₁ i)) (hG₁ : ∀ i (x : S₁), G₁ i x = θ₁ i x)
    (hS₀₁ : S₀ ⊆ closure S₁) (i₁ : Fin m₁) {l₀ : Fin m₀}
    (hl₀ : ρ i₁.castSucc.succ = l₀.castSucc.succ)
    (hρeq : ∀ r (x : S₀), augmentedStack a b G₁ r x = augmentedStack a b θ₀ (ρ r) x)
    {E₀ : Set (Fin (n + 1) → ℝ)} (hE₀ : E₀ ∈ boundedStackCells a b S₀ θ₀)
    (hne : (E₀ ∩ closure (cylinder S₁ '' sectionSet θ₁ i₁)).Nonempty) :
    E₀ ⊆ closure (cylinder S₁ '' sectionSet θ₁ i₁) := by
  obtain ⟨v₀, hv₀E₀, hv₀cl⟩ := hne
  rw [section_eq_cons_graph hG₁ i₁, closure_cons_graph (hG₁c i₁)] at hv₀cl ⊢
  have hv₀sec : v₀ ∈ cylinder S₀ '' sectionSet θ₀ l₀ := by
    have hx₀ : Fin.tail v₀ ∈ S₀ := by
      rw [← image_tail_of_mem_boundedStackCells hab hθ₀ hbnd₀ hE₀]
      exact mem_image_of_mem _ hv₀E₀
    refine mem_image_cylinder.2 ⟨hx₀, ?_⟩
    rw [mem_sectionSet]
    dsimp only
    rw [← augmentedStack_inner a b θ₀ l₀, ← hl₀, ← hρeq _ ⟨_, hx₀⟩, augmentedStack_inner]
    exact hv₀cl.2.symm
  have hdisj : (boundedStackCells a b S₀ θ₀).PairwiseDisjoint id := by
    rintro _ ⟨A, hA, rfl⟩ _ ⟨B, hB, rfl⟩ hAB
    exact (pairwiseDisjoint_stackCells (fun x ↦ (hθ₀ x).injective) hA hB
      fun h ↦ hAB (h ▸ rfl)).mono inter_subset_left inter_subset_left
  have hsec : E₀ = cylinder S₀ '' sectionSet θ₀ l₀ :=
    hdisj.eq hE₀ ((mem_boundedStackCells_iff hab hθ₀ hbnd₀).2 (Or.inl ⟨l₀, rfl⟩))
      (not_disjoint_iff.2 ⟨v₀, hv₀E₀, hv₀sec⟩)
  rw [hsec]
  intro v hv
  obtain ⟨hx, hv0⟩ := mem_image_cylinder.1 hv
  rw [mem_sectionSet] at hv0
  dsimp only at hv0
  refine ⟨hS₀₁ hx, ?_⟩
  rw [← hv0, ← augmentedStack_inner a b θ₀ l₀ ⟨_, hx⟩, ← hl₀, ← hρeq _ ⟨_, hx⟩,
    augmentedStack_inner]

private theorem frontier_containment_sector_of_section {n m₀ m₁ : ℕ} {a b : ℝ}
    {S₀ S₁ : Set (Fin n → ℝ)} {θ₀ : Fin m₀ → S₀ → ℝ} {G₁ : Fin m₁ → (Fin n → ℝ) → ℝ}
    {ρ : Fin (m₁ + 2) → Fin (m₀ + 2)} {v₀ : Fin (n + 1) → ℝ}
    (hstrict₀ : ∀ x : S₀, StrictMono fun r ↦ augmentedStack a b θ₀ r x) (hS₀₁ : S₀ ⊆ closure S₁)
    (j₁ : Fin (m₁ + 1)) (i₀ : Fin m₀)
    (hρeq : ∀ r (x : S₀), augmentedStack a b G₁ r x = augmentedStack a b θ₀ (ρ r) x)
    (hv₀E₀ : v₀ ∈ cylinder S₀ '' sectionSet θ₀ i₀)
    (hv₀cl₁ : augmentedStack a b G₁ j₁.castSucc (Fin.tail v₀) ≤ v₀ 0)
    (hv₀cl₂ : v₀ 0 ≤ augmentedStack a b G₁ j₁.succ (Fin.tail v₀)) :
    cylinder S₀ '' sectionSet θ₀ i₀ ⊆ {v : Fin (n + 1) → ℝ | Fin.tail v ∈ closure S₁ ∧
      augmentedStack a b G₁ j₁.castSucc (Fin.tail v) ≤ v 0 ∧
      v 0 ≤ augmentedStack a b G₁ j₁.succ (Fin.tail v)} := by
  obtain ⟨hx₀, hv₀0⟩ := mem_image_cylinder.1 hv₀E₀
  rw [mem_sectionSet] at hv₀0
  dsimp only at hv₀0
  have hle₁ : ρ j₁.castSucc ≤ i₀.castSucc.succ := (hstrict₀ ⟨_, hx₀⟩).le_iff_le.1 <| by
    rw [← hρeq _ ⟨_, hx₀⟩, augmentedStack_inner, hv₀0]; exact hv₀cl₁
  have hle₂ : i₀.castSucc.succ ≤ ρ j₁.succ := (hstrict₀ ⟨_, hx₀⟩).le_iff_le.1 <| by
    rw [← hρeq _ ⟨_, hx₀⟩, augmentedStack_inner, hv₀0]; exact hv₀cl₂
  intro v hv
  obtain ⟨hx, hv0⟩ := mem_image_cylinder.1 hv
  rw [mem_sectionSet] at hv0
  dsimp only at hv0
  refine ⟨hS₀₁ hx, ?_, ?_⟩
  · rw [hρeq _ ⟨_, hx⟩, ← hv0, ← augmentedStack_inner a b θ₀ i₀]
    exact (hstrict₀ ⟨_, hx⟩).monotone hle₁
  · rw [hρeq _ ⟨_, hx⟩, ← hv0, ← augmentedStack_inner a b θ₀ i₀]
    exact (hstrict₀ ⟨_, hx⟩).monotone hle₂

private theorem frontier_containment_sector_of_sector {n m₀ m₁ : ℕ} {a b : ℝ}
    {S₀ S₁ : Set (Fin n → ℝ)} {θ₀ : Fin m₀ → S₀ → ℝ} {G₁ : Fin m₁ → (Fin n → ℝ) → ℝ}
    {ρ : Fin (m₁ + 2) → Fin (m₀ + 2)} {v₀ : Fin (n + 1) → ℝ}
    (hstrict₀ : ∀ x : S₀, StrictMono fun r ↦ augmentedStack a b θ₀ r x) (hS₀₁ : S₀ ⊆ closure S₁)
    (j₁ : Fin (m₁ + 1)) (j₀ : Fin (m₀ + 1))
    (hρeq : ∀ r (x : S₀), augmentedStack a b G₁ r x = augmentedStack a b θ₀ (ρ r) x)
    (hv₀E₀ : v₀ ∈ cylinder S₀ '' sectorSet (augmentedStack a b θ₀) j₀.castSucc.succ)
    (hv₀cl₁ : augmentedStack a b G₁ j₁.castSucc (Fin.tail v₀) ≤ v₀ 0)
    (hv₀cl₂ : v₀ 0 ≤ augmentedStack a b G₁ j₁.succ (Fin.tail v₀)) :
    cylinder S₀ '' sectorSet (augmentedStack a b θ₀) j₀.castSucc.succ ⊆
      {v : Fin (n + 1) → ℝ | Fin.tail v ∈ closure S₁ ∧
        augmentedStack a b G₁ j₁.castSucc (Fin.tail v) ≤ v 0 ∧
        v 0 ≤ augmentedStack a b G₁ j₁.succ (Fin.tail v)} := by
  obtain ⟨hx₀, hsec₀⟩ := mem_image_cylinder.1 hv₀E₀
  rw [sectorSet_castSucc_succ fun x ↦ (hstrict₀ x).monotone] at hsec₀
  obtain ⟨hl₀, hu₀⟩ := hsec₀
  dsimp only [mem_ofPred_eq] at hl₀ hu₀
  have hlt₁ : (ρ j₁.castSucc).val < j₀.val + 1 := Fin.lt_def.1 <|
    (hstrict₀ ⟨_, hx₀⟩).lt_iff_lt.1 <| by
      calc augmentedStack a b θ₀ (ρ j₁.castSucc) ⟨Fin.tail v₀, hx₀⟩
          = augmentedStack a b G₁ j₁.castSucc (Fin.tail v₀) :=
            (hρeq j₁.castSucc ⟨Fin.tail v₀, hx₀⟩).symm
        _ ≤ v₀ 0 := hv₀cl₁
        _ < augmentedStack a b θ₀ j₀.succ ⟨Fin.tail v₀, hx₀⟩ := hu₀
  have hlt₂ : j₀.val < (ρ j₁.succ).val := Fin.lt_def.1 <|
    (hstrict₀ ⟨_, hx₀⟩).lt_iff_lt.1 <| by
      calc augmentedStack a b θ₀ j₀.castSucc ⟨Fin.tail v₀, hx₀⟩
          < v₀ 0 := hl₀
        _ ≤ augmentedStack a b G₁ j₁.succ (Fin.tail v₀) := hv₀cl₂
        _ = augmentedStack a b θ₀ (ρ j₁.succ) ⟨Fin.tail v₀, hx₀⟩ :=
            hρeq j₁.succ ⟨Fin.tail v₀, hx₀⟩
  intro v hv
  obtain ⟨hx, hsec⟩ := mem_image_cylinder.1 hv
  rw [sectorSet_castSucc_succ fun x ↦ (hstrict₀ x).monotone] at hsec
  obtain ⟨hl, hu⟩ := hsec
  dsimp only [mem_ofPred_eq] at hl hu
  refine ⟨hS₀₁ hx, ?_, ?_⟩
  · rw [hρeq j₁.castSucc ⟨_, hx⟩]
    exact ((hstrict₀ ⟨_, hx⟩).monotone
      (Fin.le_def.2 (by simp only [Fin.val_castSucc]; omega))).trans hl.le
  · rw [hρeq j₁.succ ⟨_, hx⟩]
    exact hu.le.trans ((hstrict₀ ⟨_, hx⟩).monotone
      (Fin.le_def.2 (by simp only [Fin.val_succ]; omega)))

private theorem frontier_containment_sector {n m₀ m₁ : ℕ} {a b : ℝ} {S₀ S₁ : Set (Fin n → ℝ)}
    {θ₀ : Fin m₀ → S₀ → ℝ} {θ₁ : Fin m₁ → S₁ → ℝ} {G₁ : Fin m₁ → (Fin n → ℝ) → ℝ}
    {ρ : Fin (m₁ + 2) → Fin (m₀ + 2)} (hab : a < b)
    (hθ₀ : ∀ x, StrictMono fun i ↦ θ₀ i x) (hbnd₀ : ∀ i x, θ₀ i x ∈ Ioo a b)
    (hθ₁ : ∀ x, StrictMono fun i ↦ θ₁ i x) (hbnd₁ : ∀ i x, θ₁ i x ∈ Ioo a b)
    (hG₁c : ∀ i, Continuous (G₁ i)) (hG₁ : ∀ i (x : S₁), G₁ i x = θ₁ i x)
    (hS₀₁ : S₀ ⊆ closure S₁) (j₁ : Fin (m₁ + 1))
    (hρeq : ∀ r (x : S₀), augmentedStack a b G₁ r x = augmentedStack a b θ₀ (ρ r) x)
    {E₀ : Set (Fin (n + 1) → ℝ)} (hE₀ : E₀ ∈ boundedStackCells a b S₀ θ₀)
    (hne : (E₀ ∩
      closure (cylinder S₁ '' sectorSet (augmentedStack a b θ₁) j₁.castSucc.succ)).Nonempty) :
    E₀ ⊆ closure (cylinder S₁ '' sectorSet (augmentedStack a b θ₁) j₁.castSucc.succ) := by
  have hstrict₀ := strictMono_augmentedStack hab hθ₀ hbnd₀
  have hstrict₁ := strictMono_augmentedStack hab hθ₁ hbnd₁
  have hGaugC := continuous_augmentedStack (a := a) (b := b) hG₁c
  have hGaugLt : ∀ x ∈ S₁,
      augmentedStack a b G₁ j₁.castSucc x < augmentedStack a b G₁ j₁.succ x := fun x hx ↦ by
    rw [augmentedStack_congr hG₁ _ ⟨x, hx⟩, augmentedStack_congr hG₁ _ ⟨x, hx⟩]
    exact hstrict₁ ⟨x, hx⟩ j₁.castSucc_lt_succ
  obtain ⟨v₀, hv₀E₀, hv₀cl⟩ := hne
  rw [sector_eq_cons_Ioo hab hθ₁ hbnd₁ hG₁ j₁,
    closure_cons_Ioo (hGaugC _) (hGaugC _) hGaugLt] at hv₀cl ⊢
  obtain ⟨_, hv₀cl₁, hv₀cl₂⟩ := hv₀cl
  rcases (mem_boundedStackCells_iff hab hθ₀ hbnd₀).1 hE₀ with ⟨i₀, rfl⟩ | ⟨j₀, rfl⟩
  · exact frontier_containment_sector_of_section hstrict₀ hS₀₁ j₁ i₀ hρeq hv₀E₀ hv₀cl₁ hv₀cl₂
  · exact frontier_containment_sector_of_sector hstrict₀ hS₀₁ j₁ j₀ hρeq hv₀E₀ hv₀cl₁ hv₀cl₂

private theorem not_sector_subset_cons_graph {n m₀ : ℕ} {a b : ℝ} {S₀ : Set (Fin n → ℝ)}
    {θ₀ : Fin m₀ → S₀ → ℝ} {C : Set (Fin n → ℝ)} {g : (Fin n → ℝ) → ℝ} (hab : a < b)
    (hS₀ne : S₀.Nonempty) (hθ₀ : ∀ x, StrictMono fun i ↦ θ₀ i x)
    (hbnd₀ : ∀ i x, θ₀ i x ∈ Ioo a b) (j₀ : Fin (m₀ + 1)) :
    ¬ cylinder S₀ '' sectorSet (augmentedStack a b θ₀) j₀.castSucc.succ ⊆
      {v | Fin.tail v ∈ C ∧ v 0 = g (Fin.tail v)} := by
  intro hsub
  obtain ⟨x₀, hx₀⟩ := hS₀ne
  have hstrict : ∀ x : S₀, StrictMono fun r ↦ augmentedStack a b θ₀ r x :=
    strictMono_augmentedStack hab hθ₀ hbnd₀
  have hlt := hstrict ⟨x₀, hx₀⟩ j₀.castSucc_lt_succ
  set α₀ := augmentedStack a b θ₀ j₀.castSucc ⟨x₀, hx₀⟩
  set β₀ := augmentedStack a b θ₀ j₀.succ ⟨x₀, hx₀⟩
  have hmem {t : ℝ} (hα : α₀ < t) (hβ : t < β₀) :
      Fin.cons t x₀ ∈ cylinder S₀ '' sectorSet (augmentedStack a b θ₀) j₀.castSucc.succ := by
    rw [mem_image_cylinder, sectorSet_castSucc_succ fun x ↦ (hstrict x).monotone]
    exact ⟨by simpa using hx₀, by simpa [α₀] using hα, by simpa [β₀] using hβ⟩
  have h1 : (2 * α₀ + β₀) / 3 = g x₀ :=
    by simpa using (hsub (hmem (by linarith) (by linarith))).2
  have h2 : (α₀ + 2 * β₀) / 3 = g x₀ :=
    by simpa using (hsub (hmem (by linarith) (by linarith))).2
  linarith [h1.trans h2.symm]

private theorem sector_eq_of_subset_closure_same_base {n m₀ : ℕ} {a b : ℝ} {S₀ : Set (Fin n → ℝ)}
    {θ₀ : Fin m₀ → S₀ → ℝ} {G₀ : Fin m₀ → (Fin n → ℝ) → ℝ} (hab : a < b) (hS₀ne : S₀.Nonempty)
    (hθ₀ : ∀ x, StrictMono fun i ↦ θ₀ i x) (hbnd₀ : ∀ i x, θ₀ i x ∈ Ioo a b)
    (hG₀c : ∀ i, Continuous (G₀ i)) (hG₀ : ∀ i (x : S₀), G₀ i x = θ₀ i x)
    {j₀ j₁ : Fin (m₀ + 1)}
    (hsub : cylinder S₀ '' sectorSet (augmentedStack a b θ₀) j₀.castSucc.succ ⊆
      closure (cylinder S₀ '' sectorSet (augmentedStack a b θ₀) j₁.castSucc.succ)) :
    j₀ = j₁ := by
  have hstrict : ∀ x : S₀, StrictMono fun r ↦ augmentedStack a b θ₀ r x :=
    strictMono_augmentedStack hab hθ₀ hbnd₀
  rw [sector_eq_cons_Ioo hab hθ₀ hbnd₀ hG₀ j₁,
    closure_cons_Ioo (continuous_augmentedStack hG₀c _) (continuous_augmentedStack hG₀c _)
      (fun x hx ↦ by
        rw [augmentedStack_congr hG₀ _ ⟨x, hx⟩, augmentedStack_congr hG₀ _ ⟨x, hx⟩]
        exact hstrict ⟨x, hx⟩ j₁.castSucc_lt_succ)] at hsub
  have := hS₀ne.to_subtype
  obtain ⟨v, hv⟩ := (sectorSet_nonempty hstrict j₀.castSucc.succ).image (cylinder S₀)
  obtain ⟨hx, hsec⟩ := mem_image_cylinder.1 hv
  rw [sectorSet_castSucc_succ fun x ↦ (hstrict x).monotone] at hsec
  obtain ⟨hl, hu⟩ := hsec
  have hcl := hsub hv
  dsimp only [mem_ofPred_eq] at hcl hl hu
  have hcl₁ : augmentedStack a b θ₀ j₁.castSucc ⟨Fin.tail v, hx⟩ ≤ v 0 := by
    rw [← augmentedStack_congr hG₀ _ ⟨Fin.tail v, hx⟩]
    exact hcl.2.1
  have hcl₂ : v 0 ≤ augmentedStack a b θ₀ j₁.succ ⟨Fin.tail v, hx⟩ := by
    rw [← augmentedStack_congr hG₀ _ ⟨Fin.tail v, hx⟩]
    exact hcl.2.2
  have hj₁ : j₁.val < j₀.val + 1 :=
    Fin.lt_def.1 ((hstrict ⟨_, hx⟩).lt_iff_lt.1 (hcl₁.trans_lt hu))
  have hj₂ : j₀.val < j₁.val + 1 :=
    Fin.lt_def.1 ((hstrict ⟨_, hx⟩).lt_iff_lt.1 (hl.trans_le hcl₂))
  exact Fin.ext (by omega)

private theorem coeff_analyticOnNhd_all {n : ℕ} {ι : Type*} {B₀ : Set (Fin n → ℝ)} {d : ι → ℕ}
    {P : ι → (Fin n → ℝ) → ℝ[X]} (hB₀ : IsOpen B₀) (hdeg : ∀ k, ∀ x ∈ B₀, (P k x).natDegree = d k)
    (hcoeff : ∀ k j, j ≤ d k → AnalyticOnNhd ℝ (fun x ↦ (P k x).coeff j) B₀) (k : ι) (j : ℕ) :
    AnalyticOnNhd ℝ (fun x ↦ (P k x).coeff j) B₀ := by
  by_cases hj : j ≤ d k
  · exact hcoeff k j hj
  · refine AnalyticOnNhd.congr hB₀ (analyticOnNhd_const (v := (0 : ℝ))) fun x hx ↦ ?_
    exact (coeff_eq_zero_of_natDegree_lt ((hdeg k x hx).trans_lt (not_le.1 hj))).symm

private theorem lift_sUnion_eq {n : ℕ} {ι : Type*} {a b : ℝ} {B : Set (Fin n → ℝ)}
    {𝒟 : Set (Set (Fin n → ℝ))} {P : ι → (Fin n → ℝ) → ℝ[X]} (hB : IsNormalDecomposition B 𝒟)
    (D : ∀ S ∈ 𝒟, Delineation fun k (x : S) ↦ P k x) :
    ⋃₀ (⋃ (S : Set (Fin n → ℝ)) (hS : S ∈ 𝒟), boundedStackCells a b S (D S hS).root) =
      {v : Fin (n + 1) → ℝ | Fin.tail v ∈ B ∧ v 0 ∈ Ioo a b} := by
  ext v
  simp only [sUnion_eq_biUnion, mem_iUnion, exists_prop, boundedStackCells, mem_image,
    mem_ofPred_eq]
  constructor
  · rintro ⟨_, ⟨S, hS, T, hT, rfl⟩, hvT, hvI⟩
    have hvS : v ∈ Fin.tail ⁻¹' S := by
      rw [← sUnion_stackCells fun x ↦ ((D S hS).strictMono_root x).monotone]
      exact ⟨T, hT, hvT⟩
    exact ⟨hB.subset_of_mem hS hvS, hvI⟩
  · rintro ⟨hvB, hvI⟩
    obtain ⟨S, hS, hvS⟩ := hB.exists_mem_of_mem hvB
    have hv : v ∈ ⋃₀ stackCells S (D S hS).root := by
      rw [sUnion_stackCells fun x ↦ ((D S hS).strictMono_root x).monotone]
      exact hvS
    obtain ⟨T, hT, hvT⟩ := hv
    exact ⟨_, ⟨S, hS, T, hT, rfl⟩, hvT, hvI⟩

private theorem base_subset_closure_of_nonempty_inter {n : ℕ} {ι : Type*} {a b : ℝ}
    {B : Set (Fin n → ℝ)} {𝒟 : Set (Set (Fin n → ℝ))} {P : ι → (Fin n → ℝ) → ℝ[X]} (hab : a < b)
    (hB : IsNormalDecomposition B 𝒟) (D : ∀ S ∈ 𝒟, Delineation fun k (x : S) ↦ P k x)
    (hbnd : ∀ (S : Set (Fin n → ℝ)) (hS : S ∈ 𝒟) i x, (D S hS).root i x ∈ Ioo a b)
    {S₀ S₁ : Set (Fin n → ℝ)} {E₀ E₁ : Set (Fin (n + 1) → ℝ)} (hS₀ : S₀ ∈ 𝒟) (hS₁ : S₁ ∈ 𝒟)
    (hE₀S : E₀ ∈ boundedStackCells a b S₀ (D S₀ hS₀).root)
    (hE₁S : E₁ ∈ boundedStackCells a b S₁ (D S₁ hS₁).root) (hne : (E₀ ∩ closure E₁).Nonempty) :
    S₀ ⊆ closure S₁ := by
  obtain ⟨v, hv₀, hv₁⟩ := hne
  refine hB.subset_closure_of_nonempty_inter hS₀ hS₁ ⟨Fin.tail v, ?_, ?_⟩
  · rw [← image_tail_of_mem_boundedStackCells hab (D S₀ hS₀).strictMono_root (hbnd S₀ hS₀) hE₀S]
    exact mem_image_of_mem _ hv₀
  · rw [← image_tail_of_mem_boundedStackCells hab (D S₁ hS₁).strictMono_root (hbnd S₁ hS₁) hE₁S]
    exact ((by fun_prop : Continuous (Fin.tail : (Fin (n + 1) → ℝ) → _)).continuousOn
      |>.image_closure (mem_image_of_mem _ hv₁))

private theorem lift_submanifold_cases {n : ℕ} {ι : Type*} {a b : ℝ} {B B₀ : Set (Fin n → ℝ)}
    {𝒟 : Set (Set (Fin n → ℝ))} {P : ι → (Fin n → ℝ) → ℝ[X]} (hab : a < b)
    (hB : IsNormalDecomposition B 𝒟) (hBB₀ : closure B ⊆ B₀)
    (hcoeffAll : ∀ k j, AnalyticOnNhd ℝ (fun x ↦ (P k x).coeff j) B₀)
    (D : ∀ S ∈ 𝒟, Delineation fun k (x : S) ↦ P k x)
    (hbnd : ∀ (S : Set (Fin n → ℝ)) (hS : S ∈ 𝒟) i x, (D S hS).root i x ∈ Ioo a b)
    {S : Set (Fin n → ℝ)} {dS : ℕ} {E : Set (Fin (n + 1) → ℝ)} (hS : S ∈ 𝒟)
    (hdS : IsAnalyticSubmanifold dS S) (hES : E ∈ boundedStackCells a b S (D S hS).root) :
    (∃ i : Fin (D S hS).count, cylinder S '' sectionSet (D S hS).root i = E ∧
      IsAnalyticSubmanifold dS E) ∨
      ∃ j : Fin ((D S hS).count + 1),
        cylinder S '' sectorSet (augmentedStack a b (D S hS).root) j.castSucc.succ = E ∧
        IsAnalyticSubmanifold (dS + 1) E := by
  have hSB₀ : S ⊆ B₀ := (hB.subset_of_mem hS).trans (subset_closure.trans hBB₀)
  rcases (mem_boundedStackCells_iff hab (D S hS).strictMono_root (hbnd S hS)).1 hES with
    ⟨i, rfl⟩ | ⟨j, rfl⟩
  · exact Or.inl ⟨i, rfl, (D S hS).isAnalyticSubmanifold_sectionSet hdS
      (fun k j ↦ ((hcoeffAll k j).mono hSB₀).analyticOnSubmanifold hdS) i⟩
  · exact Or.inr ⟨j, rfl, isAnalyticSubmanifold_image_cylinder_sectorSet hdS
      (continuous_augmentedStack (D S hS).continuous_root)
      (strictMono_augmentedStack hab (D S hS).strictMono_root (hbnd S hS)) j.castSucc.succ⟩

private theorem lift_pairwiseDisjoint_step {n : ℕ} {ι : Type*} {a b : ℝ} {B : Set (Fin n → ℝ)}
    {𝒟 : Set (Set (Fin n → ℝ))} {P : ι → (Fin n → ℝ) → ℝ[X]} (hab : a < b)
    (hB : IsNormalDecomposition B 𝒟) (D : ∀ S ∈ 𝒟, Delineation fun k (x : S) ↦ P k x)
    (hbnd : ∀ (S : Set (Fin n → ℝ)) (hS : S ∈ 𝒟) i x, (D S hS).root i x ∈ Ioo a b) :
    PairwiseDisjoint
      (⋃ (S : Set (Fin n → ℝ)) (hS : S ∈ 𝒟), boundedStackCells a b S (D S hS).root) id := by
  intro E₀ hE₀ E₁ hE₁ hne
  obtain ⟨S₀, hS₀, hE₀S⟩ := mem_iUnion₂.1 hE₀
  obtain ⟨S₁, hS₁, hE₁S⟩ := mem_iUnion₂.1 hE₁
  by_cases hSS : S₀ = S₁
  · subst hSS
    obtain ⟨T₀, hT₀, rfl⟩ := hE₀S
    obtain ⟨T₁, hT₁, rfl⟩ := hE₁S
    exact (pairwiseDisjoint_stackCells (fun x ↦ ((D S₀ hS₀).strictMono_root x).injective)
      hT₀ hT₁ fun h ↦ hne (h ▸ rfl)).mono inter_subset_left inter_subset_left
  · refine disjoint_left.2 fun v hv₀ hv₁ ↦ ?_
    have hx₀ : Fin.tail v ∈ S₀ := by
      rw [← image_tail_of_mem_boundedStackCells hab (D S₀ hS₀).strictMono_root (hbnd S₀ hS₀) hE₀S]
      exact mem_image_of_mem _ hv₀
    have hx₁ : Fin.tail v ∈ S₁ := by
      rw [← image_tail_of_mem_boundedStackCells hab (D S₁ hS₁).strictMono_root (hbnd S₁ hS₁) hE₁S]
      exact mem_image_of_mem _ hv₁
    exact disjoint_left.1 (hB.pairwiseDisjoint hS₀ hS₁ hSS) hx₀ hx₁

private theorem lift_subset_closure_step {n : ℕ} {ι : Type*} {a b : ℝ}
    {B B₀ : Set (Fin n → ℝ)} {𝒟 : Set (Set (Fin n → ℝ))} {P : ι → (Fin n → ℝ) → ℝ[X]}
    (hab : a < b) (hB : IsNormalDecomposition B 𝒟) (hBB₀ : closure B ⊆ B₀)
    (hmonic : ∀ k, ∀ x ∈ B₀, (P k x).Monic)
    (D : ∀ S ∈ 𝒟, Delineation fun k (x : S) ↦ P k x)
    (hbnd : ∀ (S : Set (Fin n → ℝ)) (hS : S ∈ 𝒟) i x, (D S hS).root i x ∈ Ioo a b)
    (G : ∀ (S : Set (Fin n → ℝ)) (hS : S ∈ 𝒟), Fin (D S hS).count → (Fin n → ℝ) → ℝ)
    (hGc : ∀ (S : Set (Fin n → ℝ)) (hS : S ∈ 𝒟) i, Continuous (G S hS i))
    (hGeq : ∀ (S : Set (Fin n → ℝ)) (hS : S ∈ 𝒟) i (x : S), G S hS i x = (D S hS).root i x)
    (hGroot : ∀ (S : Set (Fin n → ℝ)) (hS : S ∈ 𝒟) i,
      ∀ x ∈ closure S, ∃ k, (P k x).IsRoot (G S hS i x))
    {E₀ E₁ : Set (Fin (n + 1) → ℝ)}
    (hE₀ : E₀ ∈ ⋃ (S : Set (Fin n → ℝ)) (hS : S ∈ 𝒟), boundedStackCells a b S (D S hS).root)
    (hE₁ : E₁ ∈ ⋃ (S : Set (Fin n → ℝ)) (hS : S ∈ 𝒟), boundedStackCells a b S (D S hS).root)
    (hne : (E₀ ∩ closure E₁).Nonempty) :
    E₀ ⊆ closure E₁ := by
  obtain ⟨S₀, hS₀, hE₀S⟩ := mem_iUnion₂.1 hE₀
  obtain ⟨S₁, hS₁, hE₁S⟩ := mem_iUnion₂.1 hE₁
  have hS₀₁ := base_subset_closure_of_nonempty_inter hab hB D hbnd hS₀ hS₁ hE₀S hE₁S hne
  have hG₁mono (r₁ r₂) (hr : r₁ ≤ r₂) :
      ∀ x ∈ closure S₁, augmentedStack a b (G S₁ hS₁) r₁ x ≤
        augmentedStack a b (G S₁ hS₁) r₂ x :=
    closure_minimal (fun x hx ↦ by
      simpa [augmentedStack_congr (hGeq S₁ hS₁) _ ⟨x, hx⟩] using
        (strictMono_augmentedStack hab (D S₁ hS₁).strictMono_root (hbnd S₁ hS₁) ⟨x, hx⟩).monotone
          hr)
      (isClosed_le (continuous_augmentedStack (hGc S₁ hS₁) r₁)
        (continuous_augmentedStack (hGc S₁ hS₁) r₂))
  obtain ⟨ρ, -, hρinner, hρeq⟩ := exists_monotone_index_map (D S₀ hS₀) hab
    (hB.isConnected hS₀) ((hB.subset_of_mem hS₀).trans (subset_closure.trans hBB₀)) hS₀₁
    hmonic (hbnd S₀ hS₀) (hGc S₁ hS₁) (hGroot S₁ hS₁) hG₁mono
  rcases (mem_boundedStackCells_iff hab (D S₁ hS₁).strictMono_root (hbnd S₁ hS₁)).1 hE₁S with
    ⟨i₁, rfl⟩ | ⟨j₁, rfl⟩
  · obtain ⟨l₀, hl₀⟩ := hρinner i₁
    exact frontier_containment_section hab (D S₀ hS₀).strictMono_root (hbnd S₀ hS₀) (hGc S₁ hS₁)
      (hGeq S₁ hS₁) hS₀₁ i₁ hl₀ hρeq hE₀S hne
  · exact frontier_containment_sector hab (D S₀ hS₀).strictMono_root (hbnd S₀ hS₀)
      (D S₁ hS₁).strictMono_root (hbnd S₁ hS₁) (hGc S₁ hS₁) (hGeq S₁ hS₁) hS₀₁ j₁ hρeq hE₀S hne

private theorem lift_dim_lt_step {n : ℕ} {ι : Type*} {a b : ℝ} {B B₀ : Set (Fin n → ℝ)}
    {𝒟 : Set (Set (Fin n → ℝ))} {P : ι → (Fin n → ℝ) → ℝ[X]} (hab : a < b)
    (hB : IsNormalDecomposition B 𝒟) (hBB₀ : closure B ⊆ B₀)
    (hcoeffAll : ∀ k j, AnalyticOnNhd ℝ (fun x ↦ (P k x).coeff j) B₀)
    (D : ∀ S ∈ 𝒟, Delineation fun k (x : S) ↦ P k x)
    (hbnd : ∀ (S : Set (Fin n → ℝ)) (hS : S ∈ 𝒟) i x, (D S hS).root i x ∈ Ioo a b)
    (G : ∀ (S : Set (Fin n → ℝ)) (hS : S ∈ 𝒟), Fin (D S hS).count → (Fin n → ℝ) → ℝ)
    (hGc : ∀ (S : Set (Fin n → ℝ)) (hS : S ∈ 𝒟) i, Continuous (G S hS i))
    (hGeq : ∀ (S : Set (Fin n → ℝ)) (hS : S ∈ 𝒟) i (x : S), G S hS i x = (D S hS).root i x)
    {E₀ E₁ : Set (Fin (n + 1) → ℝ)}
    (hE₀ : E₀ ∈ ⋃ (S : Set (Fin n → ℝ)) (hS : S ∈ 𝒟), boundedStackCells a b S (D S hS).root)
    (hE₁ : E₁ ∈ ⋃ (S : Set (Fin n → ℝ)) (hS : S ∈ 𝒟), boundedStackCells a b S (D S hS).root)
    (hsub : E₀ ⊆ closure E₁) (hne : E₀ ≠ E₁) {dE₀ dE₁ : ℕ}
    (hdE₀ : IsAnalyticSubmanifold dE₀ E₀) (hdE₁ : IsAnalyticSubmanifold dE₁ E₁) :
    dE₀ < dE₁ := by
  obtain ⟨S₀, hS₀, hE₀S⟩ := mem_iUnion₂.1 hE₀
  obtain ⟨S₁, hS₁, hE₁S⟩ := mem_iUnion₂.1 hE₁
  obtain ⟨d₀, hd₀⟩ := hB.exists_isAnalyticSubmanifold hS₀
  obtain ⟨d₁, hd₁⟩ := hB.exists_isAnalyticSubmanifold hS₁
  have hS₀₁ := base_subset_closure_of_nonempty_inter hab hB D hbnd hS₀ hS₁ hE₀S hE₁S
    (hdE₀.nonempty.mono (subset_inter Subset.rfl hsub))
  have hcases₀ := lift_submanifold_cases hab hB hBB₀ hcoeffAll D hbnd hS₀ hd₀ hE₀S
  rcases lift_submanifold_cases hab hB hBB₀ hcoeffAll D hbnd hS₁ hd₁ hE₁S with
    ⟨i₁, rfl, hsubm₁⟩ | ⟨j₁, rfl, hsubm₁⟩
  · obtain rfl := hdE₁.dim_eq hsubm₁
    rw [section_eq_cons_graph (hGeq S₁ hS₁) i₁, closure_cons_graph (hGc S₁ hS₁ i₁)] at hsub
    rcases hcases₀ with ⟨i₀, rfl, hsubm₀⟩ | ⟨j₀, rfl, -⟩
    · obtain rfl := hdE₀.dim_eq hsubm₀
      refine hB.dim_lt_of_subset_closure hS₀ hS₁ hS₀₁ (fun hSS ↦ hne ?_) hd₀ hd₁
      subst hSS
      obtain ⟨v, hv⟩ := hdE₀.nonempty
      obtain ⟨hx, hv0⟩ := mem_image_cylinder.1 hv
      have heqi : i₀ = i₁ := ((D S₀ hS₀).strictMono_root ⟨_, hx⟩).injective <| by
        have hcl := (hsub hv).2
        rw [hGeq S₀ hS₀ i₁ ⟨_, hx⟩] at hcl
        exact (mem_sectionSet.1 hv0).trans hcl
      rw [heqi, section_eq_cons_graph (hGeq S₀ hS₀) i₁]
    · exact False.elim (not_sector_subset_cons_graph hab (hB.nonempty_of_mem hS₀)
        (D S₀ hS₀).strictMono_root (hbnd S₀ hS₀) j₀ hsub)
  · obtain rfl := hdE₁.dim_eq hsubm₁
    by_cases hSS : S₀ = S₁
    · subst hSS
      obtain rfl : d₀ = d₁ := hd₀.dim_eq hd₁
      rcases hcases₀ with ⟨i₀, rfl, hsubm₀⟩ | ⟨j₀, rfl, -⟩
      · have := hdE₀.dim_eq hsubm₀; omega
      · exact False.elim (hne (by
          rw [sector_eq_of_subset_closure_same_base hab (hB.nonempty_of_mem hS₀)
            (D S₀ hS₀).strictMono_root (hbnd S₀ hS₀) (hGc S₀ hS₀) (hGeq S₀ hS₀) hsub]))
    · have hlt := hB.dim_lt_of_subset_closure hS₀ hS₁ hS₀₁ hSS hd₀ hd₁
      rcases hcases₀ with ⟨_, rfl, hsubm₀⟩ | ⟨_, rfl, hsubm₀⟩ <;>
        (have := hdE₀.dim_eq hsubm₀; omega)

/-- **Cylindrical lifting of a normal decomposition.** Given a normal decomposition `𝒟` of `B ⊆ ℝⁿ`,
an open neighborhood `B₀` of `closure B`, and a finite family `P` of monic polynomials of constant
degrees `d k` and analytic coefficients on `B₀` whose real roots on `B` lie in `[a', b'] ⊂ (a, b)`,
choosing a delineation `D S hS` on each `S ∈ 𝒟` lifts `𝒟` to a normal decomposition of the cylinder
`{v | Fin.tail v ∈ B ∧ v 0 ∈ Ioo a b}`. -/
theorem IsNormalDecomposition.lift {n : ℕ} {ι : Type*} [Finite ι] {a a' b' b : ℝ}
    {B B₀ : Set (Fin n → ℝ)} {𝒟 : Set (Set (Fin n → ℝ))} {d : ι → ℕ}
    {P : ι → (Fin n → ℝ) → ℝ[X]} (hB : IsNormalDecomposition B 𝒟) (hB₀ : IsOpen B₀)
    (hBB₀ : closure B ⊆ B₀) (hab' : a < a') (ha'b' : a' ≤ b') (hb'b : b' < b)
    (hmonic : ∀ k, ∀ x ∈ B₀, (P k x).Monic) (hdeg : ∀ k, ∀ x ∈ B₀, (P k x).natDegree = d k)
    (hcoeff : ∀ k j, j ≤ d k → AnalyticOnNhd ℝ (fun x ↦ (P k x).coeff j) B₀)
    (hroots : ∀ k, ∀ x ∈ B, ∀ t, (P k x).IsRoot t → t ∈ Icc a' b')
    (D : ∀ S ∈ 𝒟, Delineation fun k (x : S) ↦ P k x) :
    IsNormalDecomposition {v : Fin (n + 1) → ℝ | Fin.tail v ∈ B ∧ v 0 ∈ Ioo a b}
      (⋃ (S : Set (Fin n → ℝ)) (hS : S ∈ 𝒟), boundedStackCells a b S (D S hS).root) := by
  classical
  have hab : a < b := hab'.trans_le (ha'b'.trans hb'b.le)
  have hbnd (S : Set (Fin n → ℝ)) (hS : S ∈ 𝒟) (i : Fin (D S hS).count) (x : S) :
      (D S hS).root i x ∈ Ioo a b := by
    obtain ⟨k, hk⟩ := (D S hS).exists_multiplicity_pos i
    have hrt := (rootMultiplicity_pos'.1 ((D S hS).rootMultiplicity_root k i x ▸ hk)).2
    have hIcc := hroots k x.1 (hB.subset_of_mem hS x.2) _ hrt
    exact ⟨hab'.trans_le hIcc.1, hIcc.2.trans_lt hb'b⟩
  choose G hGc hGeq _ hGroot using fun S (hS : S ∈ 𝒟) ↦
    exists_continuous_root_extension hB₀ ((closure_mono (hB.subset_of_mem hS)).trans hBB₀)
      hab' hb'b hmonic hdeg (fun k j hj ↦ (hcoeff k j hj).continuousOn)
      (fun k x hx ↦ hroots k x (hB.subset_of_mem hS hx)) (hB.isPreconnectedApproachAt hS)
      (D S hS)
  have hcoeffAll := coeff_analyticOnNhd_all hB₀ hdeg hcoeff
  refine
    { finite := hB.finite.biUnion' fun S hS ↦ (finite_stackCells S (D S hS).root).image _
      sUnion_eq := lift_sUnion_eq hB D
      pairwiseDisjoint := lift_pairwiseDisjoint_step hab hB D hbnd
      isConnected := fun hE ↦ ?_
      isSemianalytic := fun hE ↦ ?_
      exists_isAnalyticSubmanifold := fun hE ↦ ?_
      isPreconnectedApproachAt := fun hE y ↦ ?_
      subset_closure_of_nonempty_inter := fun {_} hE₀ {_} hE₁ hne ↦
        lift_subset_closure_step hab hB hBB₀ hmonic D hbnd G hGc hGeq hGroot hE₀ hE₁ hne
      dim_lt_of_subset_closure := fun {_} hE₀ {_} hE₁ hsub hne {_ _} hdE₀ hdE₁ ↦
        lift_dim_lt_step hab hB hBB₀ hcoeffAll D hbnd G hGc hGeq hE₀ hE₁ hsub hne hdE₀ hdE₁ }
  · obtain ⟨S, hS, hES⟩ := mem_iUnion₂.1 hE
    rcases (mem_boundedStackCells_iff hab (D S hS).strictMono_root (hbnd S hS)).1 hES with
      ⟨i, rfl⟩ | ⟨j, rfl⟩
    · exact isConnected_of_mem_stackCells (hB.isConnected hS) (D S hS).continuous_root
        (D S hS).strictMono_root (image_cylinder_sectionSet_mem_stackCells i)
    · exact isConnected_of_mem_stackCells (hB.isConnected hS)
        (continuous_augmentedStack (D S hS).continuous_root)
        (strictMono_augmentedStack hab (D S hS).strictMono_root (hbnd S hS))
        (image_cylinder_sectorSet_mem_stackCells j.castSucc.succ)
  · obtain ⟨S, hS, T, hT, rfl⟩ := mem_iUnion₂.1 hE
    have hScl : closure S ⊆ B₀ := (closure_mono (hB.subset_of_mem hS)).trans hBB₀
    exact ((D S hS).isSemianalytic_of_mem_stackCells (hB.isSemianalytic hS) (fun x hx ↦
      ⟨d, fun k j hj ↦ hcoeff k j hj x (hScl hx), fun k ↦
        Filter.mem_of_superset (hB₀.mem_nhds (hScl hx)) fun z hz ↦ (hdeg k z hz).le⟩) hT).inter
      (isSemianalytic_height_mem_Ioo a b)
  · obtain ⟨S, hS, hES⟩ := mem_iUnion₂.1 hE
    obtain ⟨dS, hdS⟩ := hB.exists_isAnalyticSubmanifold hS
    rcases lift_submanifold_cases hab hB hBB₀ hcoeffAll D hbnd hS hdS hES with
      ⟨_, _, hsubm⟩ | ⟨_, _, hsubm⟩
    · exact ⟨dS, hsubm⟩
    · exact ⟨dS + 1, hsubm⟩
  · obtain ⟨S, hS, hES⟩ := mem_iUnion₂.1 hE
    rcases (mem_boundedStackCells_iff hab (D S hS).strictMono_root (hbnd S hS)).1 hES with
      ⟨i, rfl⟩ | ⟨j, rfl⟩
    · rw [section_eq_cons_graph (hGeq S hS) i]
      exact IsPreconnectedApproachAt.cons_graph (hB.isPreconnectedApproachAt hS) (hGc S hS i) y
    · rw [sector_eq_cons_Ioo hab (D S hS).strictMono_root (hbnd S hS) (hGeq S hS) j]
      exact IsPreconnectedApproachAt.cons_Ioo (hB.isPreconnectedApproachAt hS)
        (continuous_augmentedStack (hGc S hS) _) (continuous_augmentedStack (hGc S hS) _)
        (fun x hx ↦ by
          simpa [augmentedStack_congr (hGeq S hS) _ ⟨x, hx⟩] using
            strictMono_augmentedStack hab (D S hS).strictMono_root (hbnd S hS) ⟨x, hx⟩
              j.castSucc_lt_succ) y

end TauCeti
