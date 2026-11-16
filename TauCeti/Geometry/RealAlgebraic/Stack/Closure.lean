/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.RealAlgebraic.Stack.Delineation
public import TauCeti.Topology.Algebra.Polynomial.Root.Extension

/-!
# Closures and approach regions of polynomial stack cells

Let `P k x` be a family of real polynomials over an ambient space `X`, delineated over a base
subset `T ⊆ X` by `D`. Suppose `B` is a subset with `T ⊆ B ⊆ closure T` on which every member not
nullified on `T` remains nonzero and along which `T` has preconnected approach regions
(`TauCeti.IsPreconnectedApproachAt`). If the root functions `D.root i` are bounded, then each
extends continuously to `B` as a root of some non-nullified member of `P`, preserving weak order
(`Delineation.exists_continuousOn_root_extension`).

Over any connected subset `S ⊆ B` carrying its own delineation `D_S` of `P`, each extended root
function agrees globally on `S` with a unique root function `D_S.root (σ i)`, where
`σ : Fin D.count → Fin D_S.count` is monotone (`Delineation.exists_monotone_root_eq_of_subset`).
Distinct roots of `D` may coalesce on `S` (`σ` need not be injective), and pairs of complex
conjugate roots on `T` may collide to create new real roots on `S` (`σ` need not be surjective).

In coordinate space `ℝ ^ (n + 1)` over `ℝ ^ n`, these continuous root extensions yield two
geometric consequences used in building cylindrical Whitney and normal decompositions:

1. Every section and every bounded sector over `T` again has preconnected approach regions at all
   points lying over `B` or outside `closure T`
   (`TauCeti.isPreconnectedApproachAt_image_cylinder_sectionSet`,
   `TauCeti.isPreconnectedApproachAt_image_cylinder_sectorSet_castSucc_succ`), even where the
   bounding roots of a sector merge into a single point on `B`.
2. Over a connected stratum `S ⊆ B` delineated by `D_S`, the trace on `Fin.tail ⁻¹' S` of the
   closure of a section over `T` is a single section of `D_S`, while the trace of the closure of
   the bounded sector between `D.root m.castSucc` and `D.root m.succ` is the closed band between
   `D_S.root (σ m.castSucc)` and `D_S.root (σ m.succ)`. Consequently every cell of `D_S` is
   either contained in the closure of the cell over `T` or disjoint from it.

## Main declarations

* `TauCeti.Delineation.exists_continuousOn_root_extension`: continuous extension of bounded
  delineation roots to `B` (`T ⊆ B ⊆ closure T`).
* `TauCeti.Delineation.exists_monotone_root_eq_of_subset`: monotone root-index matching along a
  connected stratum `S ⊆ B`.
* `TauCeti.isPreconnectedApproachAt_image_cylinder_sectionSet`,
  `TauCeti.isPreconnectedApproachAt_image_cylinder_sectorSet_castSucc_succ`: preconnected approach
  regions for ambient sections and bounded ambient sectors.
* `TauCeti.preimage_tail_inter_closure_image_cylinder_sectionSet`,
  `TauCeti.preimage_tail_inter_closure_image_cylinder_sectorSet_castSucc_succ`: exact fiberwise
  description of the closure of a section or bounded sector over a delineated stratum `S ⊆ B`.
* `TauCeti.subset_closure_or_disjoint_of_mem_stackCells_sectionSet`,
  `TauCeti.subset_closure_or_disjoint_of_mem_stackCells_sectorSet_castSucc_succ`: frontier dichotomy
  for stack cells over `S` relative to closures of sections and bounded sectors over `T`.

## References

* J. Bochnak, M. Coste, and M.-F. Roy, *Real Algebraic Geometry*, Springer (1998), §9.2.
* S. Łojasiewicz, *Triangulation of semi-analytic sets*, Annali della Scuola Normale Superiore di
  Pisa (3) 18 (1964), 449–474, §1.
-/

public section

open Filter Function Polynomial Set Topology

namespace TauCeti

section RootExtension

variable {X ι : Type*} [TopologicalSpace X] {P : ι → X → ℝ[X]} {T B : Set X}

/-- **Continuous extension of bounded delineation roots.** Let `D` be a delineation of `P` over
`T`, and let `B` satisfy `T ⊆ B` and `B ⊆ closure T`. Suppose the root functions of `D` have
bounded ranges, evaluation of each `P k` is jointly continuous on `closure T × ℝ`, every member
not nullified on `T` stays nonzero on `B`, and `T` has preconnected approach regions along `B`.
Then the root functions of `D` admit extensions `θ i : X → ℝ` continuous on `B`, weakly ordered
on `B`, and satisfying a non-nullified member equation on `B`. -/
theorem Delineation.exists_continuousOn_root_extension
    (D : Delineation fun k (x : T) ↦ P k x) (hTB : T ⊆ B) (hBT : B ⊆ closure T)
    (hbdd : ∀ i, Bornology.IsBounded (range (D.root i)))
    (hP : ∀ k, ContinuousOn (fun z : X × ℝ ↦ (P k z.1).eval z.2) (closure T ×ˢ univ))
    (hne : ∀ k, (∀ x : T, P k x ≠ 0) → ∀ x ∈ B, P k x ≠ 0)
    (hconn : ∀ x ∈ B, IsPreconnectedApproachAt T x) :
    ∃ θ : Fin D.count → X → ℝ,
      (∀ i, ContinuousOn (θ i) B) ∧
      (∀ i (x : T), θ i x.1 = D.root i x) ∧
      (∀ x ∈ B, Monotone fun i ↦ θ i x) ∧
      ∀ i, ∃ k, (∀ x : T, P k x ≠ 0) ∧ ∀ x ∈ B, (P k x).IsRoot (θ i x) := by
  classical
  -- Extend each `D.root i` by `0` outside `T` and then across `B` via `extendFrom T`.
  let f : Fin D.count → X → ℝ := fun i ↦ Function.extend Subtype.val (D.root i) 0
  have hf_apply (i : Fin D.count) (x : T) : f i x.1 = D.root i x :=
    Subtype.val_injective.extend_apply (D.root i) 0 x
  have hf_cont (i : Fin D.count) : ContinuousOn (f i) T := by
    rw [continuousOn_iff_continuous_domRestrict]
    exact (D.continuous_root i).congr fun x ↦ (hf_apply i x).symm
  have hf_bdd (i : Fin D.count) : Bornology.IsBounded (f i '' T) := by
    refine (hbdd i).subset ?_
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, (hf_apply i ⟨x, hx⟩).symm⟩
  -- Choose for each section `i` a member `k` in which `i` has positive multiplicity.
  have hmember (i : Fin D.count) :
      ∃ k, (∀ x : T, P k x ≠ 0) ∧ ∀ y ∈ T, (P k y).eval (f i y) = 0 := by
    obtain ⟨k, hk⟩ := D.exists_multiplicity_pos i
    rcases T.eq_empty_or_nonempty with rfl | ⟨x₀, hx₀⟩
    · exact ⟨k, fun x ↦ x.2.elim, fun _ hy ↦ hy.elim⟩
    · obtain ⟨hk0, -⟩ := (D.multiplicity_pos_iff ⟨x₀, hx₀⟩).1 hk
      have hk_all : ∀ x : T, P k x ≠ 0 :=
        (D.eq_zero_or_ne_zero k).resolve_left fun h ↦ hk0 (h ⟨x₀, hx₀⟩)
      refine ⟨k, hk_all, fun y hy ↦ ?_⟩
      rw [hf_apply i ⟨y, hy⟩]
      exact ((D.multiplicity_pos_iff ⟨y, hy⟩).1 hk).2
  choose k hk_ne hk_eval using hmember
  let θ : Fin D.count → X → ℝ := fun i ↦ extendFrom T (f i)
  have hθ_cont (i : Fin D.count) : ContinuousOn (θ i) B :=
    continuousOn_extendFrom_of_polynomial_root_of_subset hBT (hP (k i)) (hf_cont i) (hk_eval i)
      (hf_bdd i) (hne (k i) (hk_ne i)) hconn
  have hθ_eq (i : Fin D.count) (x : T) : θ i x.1 = D.root i x := by
    simp only [θ, extendFrom_extends (hf_cont i) x.1 x.2, hf_apply i x]
  refine ⟨θ, hθ_cont, hθ_eq, fun x hx i₁ i₂ hi ↦ ?_, fun i ↦ ⟨k i, hk_ne i, fun x hx ↦ ?_⟩⟩
  · -- Weak monotonicity passes to `B` from `T` along the nontrivial filter `𝓝[T] x`.
    have : (𝓝[T] x).NeBot := mem_closure_iff_nhdsWithin_neBot.1 (hBT hx)
    refine le_of_tendsto_of_tendsto ((hθ_cont i₁ x hx).mono hTB) ((hθ_cont i₂ x hx).mono hTB) ?_
    refine eventually_nhdsWithin_of_forall fun y hy ↦ ?_
    rw [← Subtype.coe_mk y hy, hθ_eq i₁ ⟨y, hy⟩, hθ_eq i₂ ⟨y, hy⟩]
    exact (D.strictMono_root ⟨y, hy⟩).monotone hi
  · exact eval_extendFrom_eq_zero_of_continuousWithinAt (hP (k i)) (hf_cont i) (hk_eval i)
      ((hθ_cont i x hx).mono hTB) (hBT hx)

/-- **Root matching along a connected frontier stratum.** Suppose continuous functions `θ i` on `B`
are pointwise monotone and each solves a polynomial `P k` that is nowhere zero on a connected
subset `S ⊆ B` delineated by `D_S`. Then there is a monotone map `σ : Fin m → Fin D_S.count` such
that `θ i` agrees on `S` with `D_S.root (σ i)` for every `i`. -/
theorem Delineation.exists_monotone_root_eq_of_subset {S : Set X}
    (D_S : Delineation fun k (x : S) ↦ P k x) (hS : IsConnected S) (hSB : S ⊆ B) {m : ℕ}
    {θ : Fin m → X → ℝ} (hθ : ∀ i, ContinuousOn (θ i) B)
    (hmono : ∀ x ∈ B, Monotone fun i ↦ θ i x)
    (hroot : ∀ i, ∃ k, (∀ x ∈ S, P k x ≠ 0) ∧ ∀ x ∈ S, (P k x).IsRoot (θ i x)) :
    ∃ σ : Fin m → Fin D_S.count, Monotone σ ∧ ∀ i (x : S), θ i x.1 = D_S.root (σ i) x := by
  let : ConnectedSpace S := isConnected_iff_connectedSpace.1 hS
  obtain ⟨x₀, hx₀⟩ := hS.nonempty
  -- For each `i`, the sets `{x : S | θ i x = D_S.root j x}` form a finite pairwise disjoint
  -- closed cover of the connected space `S`, so `S` lies in a single piece `σ i`.
  have hmatch (i : Fin m) : ∃ j, ∀ x : S, θ i x.1 = D_S.root j x := by
    obtain ⟨k, hkne, hkroot⟩ := hroot i
    have hcover (x : S) : ∃ j, D_S.root j x = θ i x.1 :=
      D_S.exists_root_eq k x (hkne x.1 x.2) (θ i x.1) (hkroot x.1 x.2)
    obtain ⟨j₀, hj₀⟩ := hcover ⟨x₀, hx₀⟩
    refine ⟨j₀, fun x ↦ ?_⟩
    let A : Fin D_S.count → Set S := fun j ↦ {y : S | D_S.root j y = θ i y.1}
    have hA_closed (j : Fin D_S.count) : IsClosed (A j) :=
      isClosed_eq (D_S.continuous_root j) ((hθ i).mono hSB).domRestrict
    have hB_closed : IsClosed (⋃ j : {j : Fin D_S.count // j ≠ j₀}, A j.1) :=
      isClosed_iUnion_of_finite fun j ↦ hA_closed j.1
    by_contra hx
    obtain ⟨j₁, hj₁⟩ := hcover x
    have hj₁_ne : j₁ ≠ j₀ := fun h ↦ hx (h ▸ hj₁.symm)
    obtain ⟨y, -, hy₀, hy₁⟩ := isPreconnected_closed_iff.1 isPreconnected_univ
      (A j₀) (⋃ j : {j : Fin D_S.count // j ≠ j₀}, A j.1) (hA_closed j₀) hB_closed
      (fun y _ ↦ by
        obtain ⟨j, hj⟩ := hcover y
        by_cases hjj : j = j₀
        · exact Or.inl (hjj ▸ hj)
        · exact Or.inr (mem_iUnion.2 ⟨⟨j, hjj⟩, hj⟩))
      ⟨⟨x₀, hx₀⟩, mem_univ _, hj₀⟩
      ⟨x, mem_univ _, mem_iUnion.2 ⟨⟨j₁, hj₁_ne⟩, hj₁⟩⟩
    obtain ⟨⟨j₂, hj₂_ne⟩, hy₂⟩ := mem_iUnion.1 hy₁
    exact hj₂_ne ((D_S.strictMono_root y).injective (hy₂.trans hy₀.symm))
  choose σ hσ using hmatch
  refine ⟨σ, fun i₁ i₂ hi ↦ ?_, hσ⟩
  rw [← (D_S.strictMono_root ⟨x₀, hx₀⟩).le_iff_le, ← hσ i₁ ⟨x₀, hx₀⟩, ← hσ i₂ ⟨x₀, hx₀⟩]
  exact hmono x₀ (hSB hx₀) hi

end RootExtension

section AmbientStack

variable {n k : ℕ} {T B S : Set (Fin n → ℝ)}

/-- Outside the closure of a set, preconnected approach regions hold vacuously because the empty
set is a neighbourhood trace. -/
private lemma isPreconnectedApproachAt_of_notMem_closure {X : Type*} [TopologicalSpace X]
    {E : Set X} {y : X} (hy : y ∉ closure E) : IsPreconnectedApproachAt E y := by
  rw [isPreconnectedApproachAt_def]
  refine fun s hs ↦ ⟨s ∩ (closure E)ᶜ,
    inter_mem hs (isClosed_closure.isOpen_compl.mem_nhds hy), inter_subset_left, ?_⟩
  convert isPreconnected_empty
  ext z
  simp only [mem_inter_iff, mem_compl_iff, mem_empty_iff_false, iff_false, not_and]
  exact fun hzE _ hzc ↦ hzc (subset_closure hzE)

/-- If a point `y` lies in the closure of an ambient section over `T` and its base projection lies
in `B` (where `T ⊆ B` and `θ_ext` extends the section continuously to `B`), then
`y 0 = θ_ext (Fin.tail y)`. -/
private lemma apply_zero_eq_of_mem_closure_sectionSet {θ : Fin k → T → ℝ} {i : Fin k}
    {θ_ext : (Fin n → ℝ) → ℝ} (hTB : T ⊆ B) (hθc : ContinuousOn θ_ext B)
    (hθeq : ∀ x : T, θ_ext x.1 = θ i x) {y : Fin (n + 1) → ℝ}
    (hy : y ∈ closure (cylinder T '' sectionSet θ i)) (hp : Fin.tail y ∈ B) :
    y 0 = θ_ext (Fin.tail y) := by
  set E := cylinder T '' sectionSet θ i
  have : (𝓝[E] y).NeBot := mem_closure_iff_nhdsWithin_neBot.1 hy
  have htail_cont : Continuous (Fin.tail : (Fin (n + 1) → ℝ) → Fin n → ℝ) := by fun_prop
  have htail_B : Tendsto Fin.tail (𝓝[E] y) (𝓝[B] (Fin.tail y)) :=
    tendsto_nhdsWithin_iff.2 ⟨htail_cont.continuousAt.mono_left nhdsWithin_le_nhds,
      eventually_nhdsWithin_of_forall fun z hz ↦ hTB (mem_image_cylinder.1 hz).1⟩
  have hlim_rhs : Tendsto (fun z : Fin (n + 1) → ℝ ↦ θ_ext (Fin.tail z)) (𝓝[E] y)
      (𝓝 (θ_ext (Fin.tail y))) := (hθc (Fin.tail y) hp).tendsto.comp htail_B
  have hlim_lhs : Tendsto (fun z : Fin (n + 1) → ℝ ↦ z 0) (𝓝[E] y) (𝓝 (y 0)) :=
    ((continuous_apply 0).continuousAt).mono_left nhdsWithin_le_nhds
  refine tendsto_nhds_unique hlim_lhs (hlim_rhs.congr' ?_)
  refine eventually_nhdsWithin_of_forall fun z hz ↦ ?_
  obtain ⟨hzT, hsec⟩ := mem_image_cylinder.1 hz
  dsimp only
  exact (hθeq ⟨Fin.tail z, hzT⟩).trans (mem_sectionSet.1 hsec)

/-- If a point `y` lies in the closure of the bounded ambient sector between `θ m.castSucc` and
`θ m.succ` over `T`, and its base projection lies in `B` where `a_ext` and `b_ext` continuously
extend those two bounding roots, then `a_ext (Fin.tail y) ≤ y 0 ≤ b_ext (Fin.tail y)`. -/
private lemma apply_zero_mem_Icc_of_mem_closure_sectorSet_castSucc_succ
    {θ : Fin (k + 1) → T → ℝ} (hmono : ∀ x, Monotone fun i ↦ θ i x) {m : Fin k}
    {a_ext b_ext : (Fin n → ℝ) → ℝ} (hTB : T ⊆ B) (hac : ContinuousOn a_ext B)
    (hbc : ContinuousOn b_ext B) (haeq : ∀ x : T, a_ext x.1 = θ m.castSucc x)
    (hbeq : ∀ x : T, b_ext x.1 = θ m.succ x) {y : Fin (n + 1) → ℝ}
    (hy : y ∈ closure (cylinder T '' sectorSet θ m.castSucc.succ)) (hp : Fin.tail y ∈ B) :
    a_ext (Fin.tail y) ≤ y 0 ∧ y 0 ≤ b_ext (Fin.tail y) := by
  set E := cylinder T '' sectorSet θ m.castSucc.succ
  have : (𝓝[E] y).NeBot := mem_closure_iff_nhdsWithin_neBot.1 hy
  have htail_cont : Continuous (Fin.tail : (Fin (n + 1) → ℝ) → Fin n → ℝ) := by fun_prop
  have htail_B : Tendsto Fin.tail (𝓝[E] y) (𝓝[B] (Fin.tail y)) :=
    tendsto_nhdsWithin_iff.2 ⟨htail_cont.continuousAt.mono_left nhdsWithin_le_nhds,
      eventually_nhdsWithin_of_forall fun z hz ↦ hTB (mem_image_cylinder.1 hz).1⟩
  have hlim_a : Tendsto (fun z : Fin (n + 1) → ℝ ↦ a_ext (Fin.tail z)) (𝓝[E] y)
      (𝓝 (a_ext (Fin.tail y))) := (hac (Fin.tail y) hp).tendsto.comp htail_B
  have hlim_b : Tendsto (fun z : Fin (n + 1) → ℝ ↦ b_ext (Fin.tail z)) (𝓝[E] y)
      (𝓝 (b_ext (Fin.tail y))) := (hbc (Fin.tail y) hp).tendsto.comp htail_B
  have hlim_0 : Tendsto (fun z : Fin (n + 1) → ℝ ↦ z 0) (𝓝[E] y) (𝓝 (y 0)) :=
    ((continuous_apply 0).continuousAt).mono_left nhdsWithin_le_nhds
  refine ⟨le_of_tendsto_of_tendsto hlim_a hlim_0 ?_, le_of_tendsto_of_tendsto hlim_0 hlim_b ?_⟩ <;>
    refine eventually_nhdsWithin_of_forall fun z hz ↦ ?_
  · obtain ⟨hzT, hsec⟩ := mem_image_cylinder.1 hz
    rw [sectorSet_castSucc_succ hmono] at hsec
    dsimp only
    exact (haeq ⟨Fin.tail z, hzT⟩).trans_le hsec.1.le
  · obtain ⟨hzT, hsec⟩ := mem_image_cylinder.1 hz
    rw [sectorSet_castSucc_succ hmono] at hsec
    dsimp only
    exact hsec.2.le.trans_eq (hbeq ⟨Fin.tail z, hzT⟩).symm

/-- **Preconnected approach regions of an ambient section.** Suppose `T ⊆ B`, `T` has preconnected
approach regions along `B`, and `θ i` extends continuously to `θ_ext` on `B`. Then the ambient
section `cylinder T '' sectionSet θ i` has preconnected approach regions at every `y` with
`Fin.tail y ∈ B` or `Fin.tail y ∉ closure T`. -/
theorem isPreconnectedApproachAt_image_cylinder_sectionSet {θ : Fin k → T → ℝ} {i : Fin k}
    {θ_ext : (Fin n → ℝ) → ℝ} (hTB : T ⊆ B) (hθc : ContinuousOn θ_ext B)
    (hθeq : ∀ x : T, θ_ext x.1 = θ i x) (hconn : ∀ x ∈ B, IsPreconnectedApproachAt T x)
    {y : Fin (n + 1) → ℝ} (hy : Fin.tail y ∈ B ∨ Fin.tail y ∉ closure T) :
    IsPreconnectedApproachAt (cylinder T '' sectionSet θ i) y := by
  set E := cylinder T '' sectionSet θ i
  by_cases hyE : y ∈ closure E
  swap
  · exact isPreconnectedApproachAt_of_notMem_closure hyE
  have hpT : Fin.tail y ∈ closure T := by
    have hsub : E ⊆ Fin.tail ⁻¹' closure T := fun z hz ↦
      subset_closure (mem_image_cylinder.1 hz).1
    have hcl : IsClosed (Fin.tail ⁻¹' closure T : Set (Fin (n + 1) → ℝ)) :=
      isClosed_closure.preimage (by fun_prop)
    exact closure_minimal hsub hcl hyE
  have hp : Fin.tail y ∈ B := hy.resolve_right (not_not.2 hpT)
  have hy0 : y 0 = θ_ext (Fin.tail y) :=
    apply_zero_eq_of_mem_closure_sectionSet hTB hθc hθeq hyE hp
  -- Write `E` as the graph image `φ '' T` of `φ x = Fin.cons (θ_ext x) x`, continuous on `B`.
  let φ : (Fin n → ℝ) → Fin (n + 1) → ℝ := fun x ↦ Fin.cons (θ_ext x) x
  have hφB : ContinuousOn φ B := by
    rw [continuousOn_pi]
    intro l
    cases l using Fin.cases with
    | zero => simpa [φ] using hθc
    | succ l =>
      have hc : Continuous fun x : Fin n → ℝ ↦ x l := continuous_apply l
      simpa [φ] using hc.continuousOn
  have hφp : φ (Fin.tail y) = y := by
    simpa only [φ, ← hy0] using Fin.cons_self_tail y
  have hE_eq : E = φ '' T := by
    ext z
    simp only [E, mem_image_cylinder, mem_sectionSet]
    rw [mem_image]
    refine ⟨fun ⟨hzT, hsec⟩ ↦ ⟨Fin.tail z, hzT, ?_⟩, ?_⟩
    · simp only [φ, hθeq ⟨Fin.tail z, hzT⟩, hsec, Fin.cons_self_tail]
    · rintro ⟨x, hxT, rfl⟩
      exact ⟨by simpa [φ] using hxT, by simp [φ, hθeq ⟨x, hxT⟩]⟩
  rw [isPreconnectedApproachAt_def]
  intro s hs
  have hpre : φ ⁻¹' s ∈ 𝓝[B] (Fin.tail y) :=
    (hφB (Fin.tail y) hp).preimage_mem_nhdsWithin (hφp.symm ▸ hs)
  obtain ⟨W₀, hW₀, hW₀s⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.1 hpre
  obtain ⟨W₁, hW₁, hW₁W₀, hTW₁⟩ := isPreconnectedApproachAt_def.1 (hconn (Fin.tail y) hp) W₀ hW₀
  have htail_cont : Continuous (Fin.tail : (Fin (n + 1) → ℝ) → Fin n → ℝ) := by fun_prop
  refine ⟨Fin.tail ⁻¹' W₁ ∩ s, inter_mem (htail_cont.continuousAt.preimage_mem_nhds hW₁) hs,
    inter_subset_right, ?_⟩
  have hinter : E ∩ (Fin.tail ⁻¹' W₁ ∩ s) = φ '' (T ∩ W₁) := by
    rw [hE_eq]
    ext z
    constructor
    · rintro ⟨⟨x, hxT, rfl⟩, hxW₁, -⟩
      exact ⟨x, ⟨hxT, by simpa [φ] using hxW₁⟩, rfl⟩
    · rintro ⟨x, ⟨hxT, hxW₁⟩, rfl⟩
      exact ⟨mem_image_of_mem φ hxT, by simpa [φ] using hxW₁, hW₀s ⟨hW₁W₀ hxW₁, hTB hxT⟩⟩
  rw [hinter]
  exact hTW₁.image φ (hφB.mono (inter_subset_left.trans hTB))

/-- **Preconnected approach regions of a bounded ambient sector.** Suppose `T ⊆ B`, `T` has
preconnected approach regions along `B`, and the two bounding roots `θ m.castSucc < θ m.succ`
extend continuously to `a_ext` and `b_ext` on `B`. Then the bounded sector
`cylinder T '' sectorSet θ m.castSucc.succ` has preconnected approach regions at every `y` with
`Fin.tail y ∈ B` or `Fin.tail y ∉ closure T`, even where `a_ext` and `b_ext` merge on `B`. -/
theorem isPreconnectedApproachAt_image_cylinder_sectorSet_castSucc_succ
    {θ : Fin (k + 1) → T → ℝ} (hmono : ∀ x, StrictMono fun i ↦ θ i x) {m : Fin k}
    {a_ext b_ext : (Fin n → ℝ) → ℝ} (hTB : T ⊆ B) (hac : ContinuousOn a_ext B)
    (hbc : ContinuousOn b_ext B) (haeq : ∀ x : T, a_ext x.1 = θ m.castSucc x)
    (hbeq : ∀ x : T, b_ext x.1 = θ m.succ x) (hconn : ∀ x ∈ B, IsPreconnectedApproachAt T x)
    {y : Fin (n + 1) → ℝ} (hy : Fin.tail y ∈ B ∨ Fin.tail y ∉ closure T) :
    IsPreconnectedApproachAt (cylinder T '' sectorSet θ m.castSucc.succ) y := by
  set E := cylinder T '' sectorSet θ m.castSucc.succ
  by_cases hyE : y ∈ closure E
  swap
  · exact isPreconnectedApproachAt_of_notMem_closure hyE
  have hpT : Fin.tail y ∈ closure T := by
    have hsub : E ⊆ Fin.tail ⁻¹' closure T := fun z hz ↦
      subset_closure (mem_image_cylinder.1 hz).1
    have hcl : IsClosed (Fin.tail ⁻¹' closure T : Set (Fin (n + 1) → ℝ)) :=
      isClosed_closure.preimage (by fun_prop)
    exact closure_minimal hsub hcl hyE
  have hp : Fin.tail y ∈ B := hy.resolve_right (not_not.2 hpT)
  obtain ⟨hay, hyb⟩ := apply_zero_mem_Icc_of_mem_closure_sectorSet_castSucc_succ
    (fun x ↦ (hmono x).monotone) hTB hac hbc haeq hbeq hyE hp
  rw [isPreconnectedApproachAt_def]
  intro s hs
  -- Choose a product box `(y 0 - ε, y 0 + ε) × W₀` inside `s` via `Fin.cons`.
  let consMap : ℝ × (Fin n → ℝ) → Fin (n + 1) → ℝ := fun q ↦ Fin.cons q.1 q.2
  have hcons_cont : Continuous consMap := by
    unfold consMap
    fun_prop
  have hcons_y : consMap (y 0, Fin.tail y) = y := Fin.cons_self_tail y
  obtain ⟨I, hI, W₀, hW₀, hIW₀⟩ := mem_nhds_prod_iff.1
    (hcons_cont.continuousAt.preimage_mem_nhds (hcons_y.symm ▸ hs))
  obtain ⟨ε, hε, hεI⟩ := Metric.mem_nhds_iff.1 hI
  -- On a smaller neighbourhood `W₁` of `Fin.tail y`, `a_ext < y 0 + ε` and `y 0 - ε < b_ext`.
  have ha_lt : a_ext ⁻¹' Iio (y 0 + ε) ∈ 𝓝[B] (Fin.tail y) :=
    (hac (Fin.tail y) hp).preimage_mem_nhdsWithin (isOpen_Iio.mem_nhds (mem_Iio.2 (by linarith)))
  have hb_gt : b_ext ⁻¹' Ioi (y 0 - ε) ∈ 𝓝[B] (Fin.tail y) :=
    (hbc (Fin.tail y) hp).preimage_mem_nhdsWithin (isOpen_Ioi.mem_nhds (mem_Ioi.2 (by linarith)))
  obtain ⟨W₁, hW₁, hW₁ab⟩ :=
    mem_nhdsWithin_iff_exists_mem_nhds_inter.1 (inter_mem ha_lt hb_gt)
  obtain ⟨W₂, hW₂, hW₂sub, hTW₂⟩ :=
    isPreconnectedApproachAt_def.1 (hconn (Fin.tail y) hp) (W₀ ∩ W₁) (inter_mem hW₀ hW₁)
  have htail_cont : Continuous (Fin.tail : (Fin (n + 1) → ℝ) → Fin n → ℝ) := by fun_prop
  let t : Set (Fin (n + 1) → ℝ) :=
    Fin.tail ⁻¹' W₂ ∩ (fun z : Fin (n + 1) → ℝ ↦ z 0) ⁻¹' Ioo (y 0 - ε) (y 0 + ε)
  have ht_nhds : t ∈ 𝓝 y := inter_mem (htail_cont.continuousAt.preimage_mem_nhds hW₂)
    (((continuous_apply 0).continuousAt).preimage_mem_nhds
      (isOpen_Ioo.mem_nhds ⟨by linarith, by linarith⟩))
  have ht_sub : t ⊆ s := fun z ⟨hzW₂, hzI⟩ ↦ by
    have hzball : z 0 ∈ Metric.ball (y 0) ε := by rwa [Real.ball_eq_Ioo]
    have hz_pair : (z 0, Fin.tail z) ∈ I ×ˢ W₀ := ⟨hεI hzball, (hW₂sub hzW₂).1⟩
    simpa only [mem_preimage, consMap, Fin.cons_self_tail] using hIW₀ hz_pair
  refine ⟨t, ht_nhds, ht_sub, ?_⟩
  -- Express `E ∩ t` as the bounded sector of the 2-section stack `max a_ext (y 0 - ε) <
  -- min b_ext (y 0 + ε)` over the preconnected base `C = T ∩ W₂`.
  set C := T ∩ W₂
  let : PreconnectedSpace C := isPreconnected_iff_preconnectedSpace.1 hTW₂
  let ψ : Fin 2 → C → ℝ :=
    Fin.cons (fun x : C ↦ max (a_ext x.1) (y 0 - ε))
      (Fin.cons (fun x : C ↦ min (b_ext x.1) (y 0 + ε)) Fin.elim0)
  have hψ0 (x : C) : ψ 0 x = max (a_ext x.1) (y 0 - ε) := rfl
  have hψ1 (x : C) : ψ 1 x = min (b_ext x.1) (y 0 + ε) := rfl
  have hψ_cont (i : Fin 2) : Continuous (ψ i) := by
    cases i using Fin.cases with
    | zero =>
      exact ((hac.mono (inter_subset_left.trans hTB)).domRestrict).max continuous_const
    | succ i =>
      cases i using Fin.cases with
      | zero =>
        exact ((hbc.mono (inter_subset_left.trans hTB)).domRestrict).min continuous_const
      | succ i => exact i.elim0
  have hψ_mono (x : C) : StrictMono fun i ↦ ψ i x := by
    refine Fin.strictMono_iff_lt_succ.2 fun i ↦ ?_
    cases i using Fin.cases with
    | zero =>
      change ψ 0 x < ψ 1 x
      rw [hψ0, hψ1, max_lt_iff, lt_min_iff, lt_min_iff]
      have hxT : x.1 ∈ T := x.2.1
      have hxab := hW₁ab ⟨(hW₂sub x.2.2).2, hTB hxT⟩
      have hab_T : a_ext x.1 < b_ext x.1 := by
        rw [haeq ⟨x.1, hxT⟩, hbeq ⟨x.1, hxT⟩]
        exact hmono ⟨x.1, hxT⟩ m.castSucc_lt_succ
      exact ⟨⟨hab_T, hxab.1⟩, ⟨hxab.2, by linarith⟩⟩
    | succ i => exact i.elim0
  have heq : E ∩ t = cylinder C '' sectorSet ψ (0 : Fin 1).castSucc.succ := by
    ext z
    rw [mem_image_cylinder, sectorSet_castSucc_succ fun x ↦ (hψ_mono x).monotone,
      show z ∈ E ∩ t ↔ z ∈ cylinder T '' sectorSet θ m.castSucc.succ ∧ z ∈ t from Iff.rfl,
      mem_image_cylinder, sectorSet_castSucc_succ fun x ↦ (hmono x).monotone]
    change (∃ h : Fin.tail z ∈ T,
        θ m.castSucc ⟨Fin.tail z, h⟩ < z 0 ∧ z 0 < θ m.succ ⟨Fin.tail z, h⟩) ∧
      (Fin.tail z ∈ W₂ ∧ (y 0 - ε < z 0 ∧ z 0 < y 0 + ε)) ↔
      ∃ _ : Fin.tail z ∈ T ∩ W₂,
        max (a_ext (Fin.tail z)) (y 0 - ε) < z 0 ∧ z 0 < min (b_ext (Fin.tail z)) (y 0 + ε)
    simp only [max_lt_iff, lt_min_iff]
    constructor
    · rintro ⟨⟨hzT, ha, hb⟩, hzW₂, hlo, hhi⟩
      rw [← haeq ⟨Fin.tail z, hzT⟩] at ha
      rw [← hbeq ⟨Fin.tail z, hzT⟩] at hb
      exact ⟨⟨hzT, hzW₂⟩, ⟨ha, hlo⟩, ⟨hb, hhi⟩⟩
    · rintro ⟨⟨hzT, hzW₂⟩, ⟨ha, hlo⟩, ⟨hb, hhi⟩⟩
      rw [haeq ⟨Fin.tail z, hzT⟩] at ha
      rw [hbeq ⟨Fin.tail z, hzT⟩] at hb
      exact ⟨⟨hzT, ha, hb⟩, hzW₂, hlo, hhi⟩
  rw [heq]
  exact (isPreconnected_sectorSet hψ_cont hψ_mono _).image _ continuous_cylinder.continuousOn

/-- **Exact closure trace of an ambient section over a frontier stratum.** Suppose `S ⊆ B ⊆
closure T` (`T ⊆ B`), `θ_ext` continuously extends `θ i` to `B`, and `θ_ext` agrees on `S` with
`φ j` for a stack `φ` on `S`. Then `(Fin.tail ⁻¹' S) ∩ closure (cylinder T '' sectionSet θ i)` is
precisely `cylinder S '' sectionSet φ j`. -/
theorem preimage_tail_inter_closure_image_cylinder_sectionSet {l : ℕ} {θ : Fin k → T → ℝ}
    {φ : Fin l → S → ℝ} {i : Fin k} {j : Fin l} {θ_ext : (Fin n → ℝ) → ℝ} (hTB : T ⊆ B)
    (hBT : B ⊆ closure T) (hSB : S ⊆ B) (hθc : ContinuousOn θ_ext B)
    (hθeq : ∀ x : T, θ_ext x.1 = θ i x) (hφeq : ∀ x : S, θ_ext x.1 = φ j x) :
    Fin.tail ⁻¹' S ∩ closure (cylinder T '' sectionSet θ i) = cylinder S '' sectionSet φ j := by
  ext y
  simp only [mem_inter_iff, mem_preimage, mem_image_cylinder, mem_sectionSet]
  refine ⟨fun ⟨hyS, hycl⟩ ↦ ⟨hyS, ?_⟩, fun ⟨hyS, hysec⟩ ↦ ⟨hyS, ?_⟩⟩
  · rw [← hφeq ⟨Fin.tail y, hyS⟩,
      apply_zero_eq_of_mem_closure_sectionSet hTB hθc hθeq hycl (hSB hyS)]
  · -- Approach `y` along `𝓝[T] (Fin.tail y)` by points `(x, θ_ext x)` of the section over `T`.
    have hp : Fin.tail y ∈ B := hSB hyS
    have : (𝓝[T] (Fin.tail y)).NeBot := mem_closure_iff_nhdsWithin_neBot.1 (hBT hp)
    let g : (Fin n → ℝ) → Fin (n + 1) → ℝ := fun x ↦ Fin.cons (θ_ext x) x
    have hg_tendsto : Tendsto g (𝓝[T] (Fin.tail y)) (𝓝 y) := by
      rw [tendsto_pi_nhds]
      intro m
      cases m using Fin.cases with
      | zero =>
        simp only [g, Fin.cons_zero]
        rw [← hysec, ← hφeq ⟨Fin.tail y, hyS⟩]
        exact (hθc (Fin.tail y) hp).mono hTB
      | succ m =>
        simp only [g, Fin.cons_succ]
        exact ((continuous_apply m).continuousAt).mono_left nhdsWithin_le_nhds
    refine mem_closure_of_tendsto hg_tendsto (eventually_nhdsWithin_of_forall fun x hxT ↦ ?_)
    rw [mem_image_cylinder]
    exact ⟨by simpa [g] using hxT, by simp [g, hθeq ⟨x, hxT⟩]⟩

/-- **Exact closure trace of a bounded ambient sector over a frontier stratum.** Suppose
`S ⊆ B ⊆ closure T` (`T ⊆ B`), the bounding roots `θ m.castSucc < θ m.succ` extend continuously to
`a_ext` and `b_ext` on `B`, and on `S` they agree with `φ j₁` and `φ j₂` (`φ j₁ x ≤ φ j₂ x`). Then
`(Fin.tail ⁻¹' S) ∩ closure (cylinder T '' sectorSet θ m.castSucc.succ)` is precisely the closed
band `{y | Fin.tail y ∈ S ∧ φ j₁ (Fin.tail y) ≤ y 0 ≤ φ j₂ (Fin.tail y)}`, including when
`φ j₁` and `φ j₂` coincide. -/
theorem preimage_tail_inter_closure_image_cylinder_sectorSet_castSucc_succ {l : ℕ}
    {θ : Fin (k + 1) → T → ℝ} (hmono : ∀ x, StrictMono fun i ↦ θ i x) {φ : Fin l → S → ℝ}
    {m : Fin k} {j₁ j₂ : Fin l} {a_ext b_ext : (Fin n → ℝ) → ℝ} (hTB : T ⊆ B)
    (hBT : B ⊆ closure T) (hSB : S ⊆ B) (hac : ContinuousOn a_ext B)
    (hbc : ContinuousOn b_ext B) (haeq : ∀ x : T, a_ext x.1 = θ m.castSucc x)
    (hbeq : ∀ x : T, b_ext x.1 = θ m.succ x) (hφ₁ : ∀ x : S, a_ext x.1 = φ j₁ x)
    (hφ₂ : ∀ x : S, b_ext x.1 = φ j₂ x) :
    Fin.tail ⁻¹' S ∩ closure (cylinder T '' sectorSet θ m.castSucc.succ) =
      {y : Fin (n + 1) → ℝ | ∃ hyS : Fin.tail y ∈ S,
        φ j₁ ⟨Fin.tail y, hyS⟩ ≤ y 0 ∧ y 0 ≤ φ j₂ ⟨Fin.tail y, hyS⟩} := by
  set E := cylinder T '' sectorSet θ m.castSucc.succ
  ext y
  simp only [mem_inter_iff, mem_preimage, mem_ofPred_eq]
  refine ⟨fun ⟨hyS, hycl⟩ ↦ ⟨hyS, ?_⟩, fun ⟨hyS, hlo, hhi⟩ ↦ ⟨hyS, ?_⟩⟩
  · obtain ⟨ha, hb⟩ := apply_zero_mem_Icc_of_mem_closure_sectorSet_castSucc_succ
      (fun x ↦ (hmono x).monotone) hTB hac hbc haeq hbeq hycl (hSB hyS)
    rw [← hφ₁ ⟨Fin.tail y, hyS⟩, ← hφ₂ ⟨Fin.tail y, hyS⟩]
    exact ⟨ha, hb⟩
  · set p := Fin.tail y
    have hpB : p ∈ B := hSB hyS
    have : (𝓝[T] p).NeBot := mem_closure_iff_nhdsWithin_neBot.1 (hBT hpB)
    rw [← hφ₁ ⟨p, hyS⟩] at hlo
    rw [← hφ₂ ⟨p, hyS⟩] at hhi
    rcases (hlo.trans hhi).eq_or_lt with heq_ab | hlt_ab
    · -- When `a_ext p = b_ext p`, `y 0` is their common value and the midpoint `(a_ext + b_ext)/2`
      -- over `T` converges to `y` from inside `E`.
      have hy0 : (a_ext p + b_ext p) / 2 = y 0 := by linarith
      let mid : (Fin n → ℝ) → Fin (n + 1) → ℝ := fun x ↦ Fin.cons ((a_ext x + b_ext x) / 2) x
      have hmid_lim : Tendsto mid (𝓝[T] p) (𝓝 y) := by
        rw [tendsto_pi_nhds]
        intro r
        cases r using Fin.cases with
        | zero =>
          simp only [mid, Fin.cons_zero, ← hy0]
          exact (((hac p hpB).mono hTB).add ((hbc p hpB).mono hTB)).div_const 2
        | succ r =>
          simp only [mid, Fin.cons_succ]
          exact ((continuous_apply r).continuousAt).mono_left nhdsWithin_le_nhds
      refine mem_closure_of_tendsto hmid_lim (eventually_nhdsWithin_of_forall fun x hxT ↦ ?_)
      rw [mem_image_cylinder, sectorSet_castSucc_succ fun z ↦ (hmono z).monotone]
      have hab_x : θ m.castSucc ⟨x, hxT⟩ < θ m.succ ⟨x, hxT⟩ :=
        hmono ⟨x, hxT⟩ m.castSucc_lt_succ
      refine ⟨by simpa [mid] using hxT, ?_⟩
      change θ m.castSucc ⟨x, hxT⟩ < (a_ext x + b_ext x) / 2 ∧
        (a_ext x + b_ext x) / 2 < θ m.succ ⟨x, hxT⟩
      rw [← haeq ⟨x, hxT⟩, ← hbeq ⟨x, hxT⟩] at hab_x ⊢
      constructor <;> linarith
    · -- When `a_ext p < b_ext p`, every height `s ∈ Ioo (a_ext p) (b_ext p)` gives
      -- `Fin.cons s p ∈ closure E`, so `Icc (a_ext p) (b_ext p)` maps into `closure E`.
      let lineAt : ℝ → Fin (n + 1) → ℝ := fun s ↦ Fin.cons s p
      have hIoo : Ioo (a_ext p) (b_ext p) ⊆ lineAt ⁻¹' closure E := by
        rintro s ⟨has, hsb⟩
        let horiz : (Fin n → ℝ) → Fin (n + 1) → ℝ := fun x ↦ Fin.cons s x
        have ha_ev : ∀ᶠ x in 𝓝[T] p, a_ext x < s :=
          ((hac p hpB).mono hTB).eventually (isOpen_Iio.mem_nhds (mem_Iio.2 has))
        have hb_ev : ∀ᶠ x in 𝓝[T] p, s < b_ext x :=
          ((hbc p hpB).mono hTB).eventually (isOpen_Ioi.mem_nhds (mem_Ioi.2 hsb))
        have hcons_cont : Continuous horiz := by
          unfold horiz
          fun_prop
        have hcons_lim : Tendsto horiz (𝓝[T] p) (𝓝 (lineAt s)) :=
          (hcons_cont.tendsto p).mono_left nhdsWithin_le_nhds
        refine mem_closure_of_tendsto hcons_lim ?_
        filter_upwards [self_mem_nhdsWithin, ha_ev, hb_ev] with x hxT hax hbx
        rw [mem_image_cylinder, sectorSet_castSucc_succ fun z ↦ (hmono z).monotone]
        refine ⟨by simpa [horiz] using hxT, ?_⟩
        change θ m.castSucc ⟨x, hxT⟩ < s ∧ s < θ m.succ ⟨x, hxT⟩
        rw [← haeq ⟨x, hxT⟩, ← hbeq ⟨x, hxT⟩]
        exact ⟨hax, hbx⟩
      have hline_cont : Continuous lineAt := by
        unfold lineAt
        fun_prop
      have hclosed : IsClosed (lineAt ⁻¹' closure E) := isClosed_closure.preimage hline_cont
      have hy0_mem : y 0 ∈ lineAt ⁻¹' closure E :=
        closure_minimal hIoo hclosed (by rw [closure_Ioo hlt_ab.ne]; exact ⟨hlo, hhi⟩)
      simpa only [mem_preimage, lineAt, p, Fin.cons_self_tail] using hy0_mem

/-- **Frontier dichotomy for stack cells over `S` relative to an ambient section over `T`.** Every
cell `F ∈ stackCells S φ` (with `φ` pointwise strictly monotone on `S`) is either equal to
`cylinder S '' sectionSet φ j` and contained in `closure (cylinder T '' sectionSet θ i)`, or
disjoint from `closure (cylinder T '' sectionSet θ i)`. -/
theorem subset_closure_or_disjoint_of_mem_stackCells_sectionSet {l : ℕ} {θ : Fin k → T → ℝ}
    {φ : Fin l → S → ℝ} (hφmono : ∀ x, StrictMono fun i ↦ φ i x) {i : Fin k} {j : Fin l}
    {θ_ext : (Fin n → ℝ) → ℝ} (hTB : T ⊆ B) (hBT : B ⊆ closure T) (hSB : S ⊆ B)
    (hθc : ContinuousOn θ_ext B) (hθeq : ∀ x : T, θ_ext x.1 = θ i x)
    (hφeq : ∀ x : S, θ_ext x.1 = φ j x) {F : Set (Fin (n + 1) → ℝ)} (hF : F ∈ stackCells S φ) :
    (F = cylinder S '' sectionSet φ j ∧ F ⊆ closure (cylinder T '' sectionSet θ i)) ∨
      Disjoint F (closure (cylinder T '' sectionSet θ i)) := by
  have htrace := preimage_tail_inter_closure_image_cylinder_sectionSet hTB hBT hSB hθc hθeq hφeq
  have hFS : F ⊆ Fin.tail ⁻¹' S := by
    rw [← sUnion_stackCells fun x ↦ (hφmono x).monotone]
    exact subset_sUnion_of_mem hF
  by_cases hFJ : F = cylinder S '' sectionSet φ j
  · refine Or.inl ⟨hFJ, ?_⟩
    rw [hFJ, ← htrace]
    exact inter_subset_right
  · refine Or.inr (disjoint_iff_inter_eq_empty.2 ?_)
    have heq : F ∩ closure (cylinder T '' sectionSet θ i) = F ∩ (cylinder S '' sectionSet φ j) := by
      rw [← htrace, ← inter_assoc, inter_eq_self_of_subset_left hFS]
    rw [heq, ← disjoint_iff_inter_eq_empty]
    exact pairwiseDisjoint_stackCells (fun x ↦ (hφmono x).injective) hF
      (image_cylinder_sectionSet_mem_stackCells j) hFJ

/-- **Frontier dichotomy for stack cells over `S` relative to a bounded ambient sector over `T`.**
Under the hypotheses of `preimage_tail_inter_closure_image_cylinder_sectorSet_castSucc_succ`, with
`φ` pointwise strictly monotone on `S`, every cell `F ∈ stackCells S φ` either satisfies
`F ⊆ closure (cylinder T '' sectorSet θ m.castSucc.succ)` — with `F` either a section of `φ` or a
sector `j` satisfying `j₁.castSucc < j ∧ j ≤ j₂.castSucc` — or is disjoint from that closure. -/
theorem subset_closure_or_disjoint_of_mem_stackCells_sectorSet_castSucc_succ {l : ℕ}
    {θ : Fin (k + 1) → T → ℝ} (hmono : ∀ x, StrictMono fun i ↦ θ i x) {φ : Fin l → S → ℝ}
    (hφmono : ∀ x, StrictMono fun i ↦ φ i x) {m : Fin k} {j₁ j₂ : Fin l}
    {a_ext b_ext : (Fin n → ℝ) → ℝ} (hTB : T ⊆ B) (hBT : B ⊆ closure T) (hSB : S ⊆ B)
    (hac : ContinuousOn a_ext B) (hbc : ContinuousOn b_ext B)
    (haeq : ∀ x : T, a_ext x.1 = θ m.castSucc x) (hbeq : ∀ x : T, b_ext x.1 = θ m.succ x)
    (hφ₁ : ∀ x : S, a_ext x.1 = φ j₁ x) (hφ₂ : ∀ x : S, b_ext x.1 = φ j₂ x)
    {F : Set (Fin (n + 1) → ℝ)} (hF : F ∈ stackCells S φ) :
    (F ⊆ closure (cylinder T '' sectorSet θ m.castSucc.succ) ∧
      ((∃ r, F = cylinder S '' sectionSet φ r) ∨
        ∃ j, j₁.castSucc < j ∧ j ≤ j₂.castSucc ∧ F = cylinder S '' sectorSet φ j)) ∨
      Disjoint F (closure (cylinder T '' sectorSet θ m.castSucc.succ)) := by
  set E := cylinder T '' sectorSet θ m.castSucc.succ
  have htrace := preimage_tail_inter_closure_image_cylinder_sectorSet_castSucc_succ hmono hTB hBT
    hSB hac hbc haeq hbeq hφ₁ hφ₂
  rcases mem_stackCells.1 hF with ⟨r, rfl⟩ | ⟨j, rfl⟩
  · by_cases hr : j₁ ≤ r ∧ r ≤ j₂
    · refine Or.inl ⟨fun y hy ↦ ?_, Or.inl ⟨r, rfl⟩⟩
      suffices y ∈ Fin.tail ⁻¹' S ∩ closure E from this.2
      rw [htrace]
      obtain ⟨hyS, hysec⟩ := mem_image_cylinder.1 hy
      simp only [mem_sectionSet] at hysec
      exact ⟨hyS, hysec ▸ (hφmono ⟨Fin.tail y, hyS⟩).monotone hr.1,
        hysec ▸ (hφmono ⟨Fin.tail y, hyS⟩).monotone hr.2⟩
    · refine Or.inr (disjoint_left.2 fun y hy hycl ↦ hr ?_)
      obtain ⟨hyS, hysec⟩ := mem_image_cylinder.1 hy
      simp only [mem_sectionSet] at hysec
      have hband : y ∈ Fin.tail ⁻¹' S ∩ closure E := ⟨hyS, hycl⟩
      rw [htrace] at hband
      obtain ⟨_, hlo, hhi⟩ := hband
      rw [← hysec, (hφmono ⟨Fin.tail y, hyS⟩).le_iff_le] at hlo hhi
      exact ⟨hlo, hhi⟩
  · by_cases hj : j₁.castSucc < j ∧ j ≤ j₂.castSucc
    · refine Or.inl ⟨fun y hy ↦ ?_, Or.inr ⟨j, hj.1, hj.2, rfl⟩⟩
      suffices y ∈ Fin.tail ⁻¹' S ∩ closure E from this.2
      rw [htrace]
      obtain ⟨hyS, hysec⟩ := mem_image_cylinder.1 hy
      rw [mem_sectorSet] at hysec
      exact ⟨hyS, (hysec.1 j₁ hj.1).le, (hysec.2 j₂ hj.2).le⟩
    · refine Or.inr (disjoint_left.2 fun y hy hycl ↦ hj ?_)
      obtain ⟨hyS, hysec⟩ := mem_image_cylinder.1 hy
      rw [mem_sectorSet] at hysec
      have hband : y ∈ Fin.tail ⁻¹' S ∩ closure E := ⟨hyS, hycl⟩
      rw [htrace] at hband
      obtain ⟨_, hlo, hhi⟩ := hband
      refine ⟨lt_of_not_ge fun hle ↦ (hysec.2 j₁ hle).not_ge hlo,
        le_of_not_gt fun hgt ↦ (hysec.1 j₂ hgt).not_ge hhi⟩

end AmbientStack

end TauCeti
