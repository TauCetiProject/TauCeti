/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.RealAlgebraic.Stack.Bounded
public import TauCeti.Geometry.RealAnalytic.Semianalytic.NormalDecomposition.Basic

import TauCeti.Analysis.Analytic.Submanifold.Dimension
import TauCeti.Geometry.RealAlgebraic.Stack.Analytic
import TauCeti.Geometry.RealAlgebraic.Stack.Frontier.Lifting
import TauCeti.Geometry.RealAnalytic.Semianalytic.Stack
import TauCeti.Topology.Algebra.Polynomial.Root.Extension

/-!
# Cylindrical lifting of normal decompositions along monic polynomial delineations

Let `𝒟` be a normal decomposition of `B ⊆ ℝⁿ`, let `B₀` be an open neighborhood of `closure B`,
and let `P : ι → ℝⁿ → ℝ[X]` be a finite family of monic polynomials of constant degrees `d k` on
`B₀` with analytic coefficients on `B₀`, whose real roots over `B` lie in `(a, b)`. If over each
base piece `S ∈ 𝒟` the family `P` admits a delineation `D S hS`, then clipping the stack cells of
`D S hS` to the open height interval `(a, b)` yields a normal decomposition of the cylinder
`{v : ℝⁿ⁺¹ | Fin.tail v ∈ B ∧ v 0 ∈ Ioo a b}` (`TauCeti.IsNormalDecomposition.lift`), on every piece
of which all evaluations `v ↦ (P k (Fin.tail v)).eval (v 0)` are sign-invariant via
`TauCeti.Delineation.signInvariant_eval_of_mem_boundedStackCells`.

Because each base piece `S₁ ∈ 𝒟` has preconnected approach regions at every ambient point and each
`P k` is monic of constant degree on `B₀ ⊇ closure S₁`, every root section `(D S₁ hS₁).root i`
converges along `S₁` at every point of `closure S₁` (`TauCeti.exists_tendsto_nhdsWithin_of_isRoot`).
Over a boundary piece `S₀ ⊆ closure S₁` in `𝒟`,
`TauCeti.Delineation.exists_root_tendsto_of_subset_closure` matches these boundary limits
monotonically to sections of `D S₀ hS₀`. Combining the ambient-stack frontier and dimension-drop
lifting theorems (`TauCeti.subset_closure_of_mem_biUnion_stackCells`,
`TauCeti.dim_lt_of_mem_biUnion_stackCells`) with openness of `{v | v 0 ∈ Ioo a b}` and clipped-stack
approach-region lifting (`TauCeti.isPreconnectedApproachAt_of_mem_boundedStackCells`) propagates
both parts of the frontier condition and preconnected approach regions at every point of `ℝⁿ⁺¹`.

## Main declarations

* `TauCeti.IsNormalDecomposition.lift`: lifting a normal decomposition to a bounded open cylinder
  along delineations of a monic analytic-coefficient polynomial family with roots in `Ioo a b`.

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

private theorem isSemianalytic_height_mem_Ioo {n : ℕ} (a b : ℝ) :
    IsSemianalytic {v : Fin (n + 1) → ℝ | v 0 ∈ Ioo a b} := by
  have h0 : AnalyticOnNhd ℝ (fun v : Fin (n + 1) → ℝ ↦ v 0) univ :=
    fun v _ ↦ (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (n + 1) ↦ ℝ) 0).analyticAt v
  have h1 := (h0.sub (analyticOnNhd_const (v := a))).isSemianalytic_setOf_pos
  have h2 := ((analyticOnNhd_const (v := b)).sub h0).isSemianalytic_setOf_pos
  convert h1.inter h2 using 1
  ext v
  simp only [mem_ofPred_eq, mem_Ioo, mem_inter_iff, Pi.sub_apply, sub_pos]

private theorem lift_sUnion_eq {n : ℕ} {ι : Type*} {a b : ℝ} {B : Set (Fin n → ℝ)}
    {𝒟 : Set (Set (Fin n → ℝ))} {P : ι → (Fin n → ℝ) → ℝ[X]} (hB : IsNormalDecomposition B 𝒟)
    (D : ∀ S ∈ 𝒟, Delineation fun k (x : S) ↦ P k x) :
    ⋃₀ (⋃ (S : Set (Fin n → ℝ)) (hS : S ∈ 𝒟), boundedStackCells a b S (D S hS).root) =
      {v : Fin (n + 1) → ℝ | Fin.tail v ∈ B ∧ v 0 ∈ Ioo a b} := by
  ext v
  simp only [mem_sUnion, mem_iUnion, mem_ofPred_eq]
  constructor
  · rintro ⟨E, ⟨S, hS, hES⟩, hvE⟩
    have hv : v ∈ ⋃₀ boundedStackCells a b S (D S hS).root := ⟨E, hES, hvE⟩
    rw [sUnion_boundedStackCells fun x ↦ ((D S hS).strictMono_root x).monotone] at hv
    exact ⟨hB.subset_of_mem hS hv.left, hv.right⟩
  · rintro ⟨hvB, hvI⟩
    obtain ⟨S, hS, hvS⟩ := hB.exists_mem_of_mem hvB
    have hv : v ∈ ⋃₀ boundedStackCells a b S (D S hS).root := by
      rw [sUnion_boundedStackCells fun x ↦ ((D S hS).strictMono_root x).monotone]
      exact ⟨hvS, hvI⟩
    obtain ⟨E, hES, hvE⟩ := hv
    exact ⟨E, ⟨S, hS, hES⟩, hvE⟩

private theorem lift_pairwiseDisjoint {n : ℕ} {ι : Type*} {a b : ℝ} {B : Set (Fin n → ℝ)}
    {𝒟 : Set (Set (Fin n → ℝ))} {P : ι → (Fin n → ℝ) → ℝ[X]} (hab : a < b)
    (hB : IsNormalDecomposition B 𝒟) (D : ∀ S ∈ 𝒟, Delineation fun k (x : S) ↦ P k x)
    (hbnd : ∀ (S : Set (Fin n → ℝ)) (hS : S ∈ 𝒟) i x, (D S hS).root i x ∈ Ioo a b) :
    PairwiseDisjoint
      (⋃ (S : Set (Fin n → ℝ)) (hS : S ∈ 𝒟), boundedStackCells a b S (D S hS).root) id := by
  intro E₀ hE₀ E₁ hE₁ hne
  obtain ⟨S₀, hS₀, hE₀S⟩ := mem_iUnion₂.mp hE₀
  obtain ⟨S₁, hS₁, hE₁S⟩ := mem_iUnion₂.mp hE₁
  by_cases hSS : S₀ = S₁
  · subst hSS
    exact pairwiseDisjoint_boundedStackCells (fun x ↦ ((D S₀ hS₀).strictMono_root x).injective)
      hE₀S hE₁S hne
  · refine disjoint_left.mpr fun v hv₀ hv₁ ↦ ?_
    have hx₀ : Fin.tail v ∈ S₀ := by
      rw [← image_tail_of_mem_boundedStackCells hab (D S₀ hS₀).strictMono_root (hbnd S₀ hS₀) hE₀S]
      exact mem_image_of_mem _ hv₀
    have hx₁ : Fin.tail v ∈ S₁ := by
      rw [← image_tail_of_mem_boundedStackCells hab (D S₁ hS₁).strictMono_root (hbnd S₁ hS₁) hE₁S]
      exact mem_image_of_mem _ hv₁
    exact disjoint_left.mp (hB.pairwiseDisjoint hS₀ hS₁ hSS) hx₀ hx₁

private theorem exists_root_tendsto_comap {n : ℕ} {ι : Type*} {B₀ S : Set (Fin n → ℝ)}
    {d : ι → ℕ} {P : ι → (Fin n → ℝ) → ℝ[X]} (hB₀ : IsOpen B₀) (hScl : closure S ⊆ B₀)
    (hmonic : ∀ k, ∀ x ∈ B₀, (P k x).Monic) (hdeg : ∀ k, ∀ x ∈ B₀, (P k x).natDegree = d k)
    (hcoeff : ∀ k j, j ≤ d k → AnalyticOnNhd ℝ (fun x ↦ (P k x).coeff j) B₀)
    (happ : ∀ x, IsPreconnectedApproachAt S x) (D : Delineation fun k (x : S) ↦ P k x)
    (x₀ : Fin n → ℝ) (i : Fin D.count) :
    ∃ L, Tendsto (D.root i) (comap Subtype.val (𝓝 x₀)) (𝓝 L) := by
  by_cases hx₀ : x₀ ∈ closure S
  · have hx₀B₀ : x₀ ∈ B₀ := hScl hx₀
    obtain ⟨k, hk⟩ := D.exists_multiplicity_pos i
    let f : (Fin n → ℝ) → ℝ := Function.extend Subtype.val (D.root i) fun _ ↦ 0
    have hf_apply (x : S) : f x = D.root i x := Subtype.val_injective.extend_apply _ _ x
    have hf_cont : ContinuousOn f S :=
      continuousOn_iff_continuous_domRestrict.mpr ((D.continuous_root i).congr fun x ↦
        (hf_apply x).symm)
    have hf_root : ∀ᶠ y in 𝓝[S] x₀, (P k y).eval (f y) = 0 :=
      eventually_nhdsWithin_of_forall fun y hy ↦ by
        rw [hf_apply ⟨y, hy⟩]
        exact ((D.multiplicity_pos_iff ⟨y, hy⟩).mp hk).right
    obtain ⟨L, -, hL⟩ := exists_tendsto_nhdsWithin_of_isRoot hx₀ (happ x₀) hf_cont hf_root
      (fun j hj ↦ ((hcoeff k j ((hdeg k x₀ hx₀B₀) ▸ hj)) x₀ hx₀B₀).continuousAt.tendsto.mono_left
        nhdsWithin_le_nhds)
      (nhdsWithin_le_nhds (eventually_of_mem (hB₀.mem_nhds hx₀B₀) fun y hy ↦ by
        rw [hdeg k y hy, hdeg k x₀ hx₀B₀]))
      (hmonic k x₀ hx₀B₀).ne_zero
    have hmap : map (Subtype.val : S → Fin n → ℝ) (comap Subtype.val (𝓝 x₀)) = 𝓝[S] x₀ := by
      rw [nhdsWithin, Filter.map_comap_setCoe_val]
    have hsub : Tendsto (f ∘ Subtype.val) (comap Subtype.val (𝓝 x₀)) (𝓝 L) :=
      tendsto_map'_iff.mp (hmap.symm ▸ hL)
    exact ⟨L, (funext hf_apply : f ∘ Subtype.val = D.root i) ▸ hsub⟩
  · have hbot : comap (Subtype.val : S → Fin n → ℝ) (𝓝 x₀) = ⊥ := by
      rw [← Filter.map_eq_bot_iff, Filter.map_comap_setCoe_val, ← nhdsWithin,
        ← notMem_closure_iff_nhdsWithin_eq_bot]
      exact hx₀
    exact ⟨0, hbot ▸ tendsto_bot⟩

private theorem exists_monotone_root_tendsto_of_monic {n : ℕ} {ι : Type*}
    {B₀ S₀ S₁ : Set (Fin n → ℝ)} {d : ι → ℕ} {P : ι → (Fin n → ℝ) → ℝ[X]} (hB₀ : IsOpen B₀)
    (hS₀B₀ : S₀ ⊆ B₀) (hS₀₁ : S₀ ⊆ closure S₁) (hS₀ : IsConnected S₀)
    (happ₁ : ∀ x, IsPreconnectedApproachAt S₁ x) (hmonic : ∀ k, ∀ x ∈ B₀, (P k x).Monic)
    (hdeg : ∀ k, ∀ x ∈ B₀, (P k x).natDegree = d k)
    (hcoeff : ∀ k j, j ≤ d k → AnalyticOnNhd ℝ (fun x ↦ (P k x).coeff j) B₀)
    (D₁ : Delineation fun k (x : S₁) ↦ P k x) (D₀ : Delineation fun k (x : S₀) ↦ P k x) :
    ∃ σ : Fin D₁.count → Fin D₀.count,
      ∀ i (x : S₀), Tendsto (D₁.root i) (comap Subtype.val (𝓝 x.val)) (𝓝 (D₀.root (σ i) x)) := by
  obtain ⟨σ, -, hσ⟩ := D₁.exists_root_tendsto_of_subset_closure D₀ hS₀₁ hS₀
    (fun x _ ↦ happ₁ x) fun i ↦ by
      obtain ⟨k, hk⟩ := D₁.exists_multiplicity_pos i
      refine ⟨k, hk, fun x hx ↦ (hmonic k x (hS₀B₀ hx)).ne_zero, fun x hx j hj ↦ ?_,
        fun x hx ↦ ?_⟩
      · exact ((hcoeff k j (hdeg k x (hS₀B₀ hx) ▸ hj)) x (hS₀B₀ hx)).continuousAt.tendsto.mono_left
          nhdsWithin_le_nhds
      · exact nhdsWithin_le_nhds (eventually_of_mem (hB₀.mem_nhds (hS₀B₀ hx)) fun y hy ↦ by
          rw [hdeg k y hy, hdeg k x (hS₀B₀ hx)])
  exact ⟨σ, hσ⟩

private theorem unclipped_subset_closure_and_dim_lt {n : ℕ} {ι : Type*}
    {B B₀ : Set (Fin n → ℝ)} {𝒟 : Set (Set (Fin n → ℝ))} {d : ι → ℕ}
    {P : ι → (Fin n → ℝ) → ℝ[X]} (hB : IsNormalDecomposition B 𝒟) (hB₀ : IsOpen B₀)
    (hBB₀ : closure B ⊆ B₀) (hmonic : ∀ k, ∀ x ∈ B₀, (P k x).Monic)
    (hdeg : ∀ k, ∀ x ∈ B₀, (P k x).natDegree = d k)
    (hcoeffAll : ∀ k j, AnalyticOnNhd ℝ (fun x ↦ (P k x).coeff j) B₀)
    (D : ∀ S ∈ 𝒟, Delineation fun k (x : S) ↦ P k x) :
    (∀ {S₀ S₁} (hS₀ : S₀ ∈ 𝒟) (hS₁ : S₁ ∈ 𝒟) {T₀ T₁},
      T₀ ∈ stackCells S₀ (D S₀ hS₀).root → T₁ ∈ stackCells S₁ (D S₁ hS₁).root →
      (T₀ ∩ closure T₁).Nonempty → T₀ ⊆ closure T₁) ∧
    (∀ {S₀ S₁} (hS₀ : S₀ ∈ 𝒟) (hS₁ : S₁ ∈ 𝒟) {T₀ T₁ dT₀ dT₁},
      T₀ ∈ stackCells S₀ (D S₀ hS₀).root → T₁ ∈ stackCells S₁ (D S₁ hS₁).root →
      IsAnalyticSubmanifold dT₀ T₀ → IsAnalyticSubmanifold dT₁ T₁ →
      T₀ ⊆ closure T₁ → T₀ ≠ T₁ → dT₀ < dT₁) := by
  classical
  let Θ : ∀ S : Set (Fin n → ℝ), Σ m, Fin m → S → ℝ :=
    fun S ↦ if hS : S ∈ 𝒟 then ⟨(D S hS).count, (D S hS).root⟩ else ⟨0, Fin.elim0⟩
  have hΘ (S : Set (Fin n → ℝ)) (hS : S ∈ 𝒟) : Θ S = ⟨(D S hS).count, (D S hS).root⟩ :=
    by simp [Θ, hS]
  have hSB₀ (S : Set (Fin n → ℝ)) (hS : S ∈ 𝒟) : S ⊆ B₀ :=
    (hB.subset_of_mem hS).trans (subset_closure.trans hBB₀)
  have hmatch : ∀ S₀ ∈ 𝒟, ∀ S₁ ∈ 𝒟, S₀ ⊆ closure S₁ → S₀ ≠ S₁ →
      ∃ σ : Fin (Θ S₁).fst → Fin (Θ S₀).fst,
        ∀ i (x : S₀), Tendsto ((Θ S₁).snd i) (comap Subtype.val (𝓝 x.val))
          (𝓝 ((Θ S₀).snd (σ i) x)) := fun S₀ hS₀ S₁ hS₁ hS₀₁ _ ↦ by
    rw [hΘ S₀ hS₀, hΘ S₁ hS₁]
    exact exists_monotone_root_tendsto_of_monic hB₀ (hSB₀ S₀ hS₀) hS₀₁ (hB.isConnected hS₀)
      (hB.isPreconnectedApproachAt hS₁) hmonic hdeg (fun k j _ ↦ hcoeffAll k j)
      (D S₁ hS₁) (D S₀ hS₀)
  choose dim hdim using fun S : Set (Fin n → ℝ) ↦ (em (S ∈ 𝒟)).elim
    (fun hS ↦ (hB.exists_isAnalyticSubmanifold hS).imp fun _ hd _ ↦ hd)
    fun hS ↦ ⟨0, fun h ↦ (hS h).elim⟩
  have hroot (S : Set (Fin n → ℝ)) (hS : S ∈ 𝒟) :
      ∀ i, ∃ r, (∀ y : S, r y = (Θ S).snd i y) ∧ AnalyticOnSubmanifold (dim S) r S := by
    rw [hΘ S hS]; intro i
    let r : (Fin n → ℝ) → ℝ := Function.extend Subtype.val ((D S hS).root i) fun _ ↦ 0
    have hr (y : S) : r y = (D S hS).root i y := Subtype.val_injective.extend_apply _ _ y
    exact ⟨r, hr, (D S hS).analyticOnSubmanifold_root (hdim S hS)
      (fun k j ↦ ((hcoeffAll k j).mono (hSB₀ S hS)).analyticOnSubmanifold (hdim S hS)) i hr⟩
  have hmem {S : Set (Fin n → ℝ)} (hS : S ∈ 𝒟) {T} (hT : T ∈ stackCells S (D S hS).root) :
      T ∈ ⋃ C ∈ 𝒟, stackCells C (Θ C).snd := mem_iUnion₂.mpr ⟨S, hS, by rwa [hΘ S hS]⟩
  refine ⟨fun {_ _} hS₀ hS₁ {_ _} hT₀ hT₁ hne ↦
      subset_closure_of_mem_biUnion_stackCells (k := fun C ↦ (Θ C).fst) (θ := fun C ↦ (Θ C).snd)
        (fun A hA C hC ↦ hB.subset_closure_of_nonempty_inter hA hC)
        (fun S hS ↦ by rw [hΘ S hS]; exact (D S hS).continuous_root)
        (fun S hS ↦ by rw [hΘ S hS]; exact (D S hS).strictMono_root) hmatch
        (hmem hS₀ hT₀) (hmem hS₁ hT₁) hne,
    fun {_ _} hS₀ hS₁ {_ _ _ _} hT₀ hT₁ hdT₀ hdT₁ hsub hne ↦
      dim_lt_of_mem_biUnion_stackCells (k := fun C ↦ (Θ C).fst) (θ := fun C ↦ (Θ C).snd)
        (d := dim) hdim (fun A hA C hC ↦ hB.subset_closure_of_nonempty_inter hA hC)
        (fun A hA C hC hAC hAC' ↦
          hB.dim_lt_of_subset_closure hA hC hAC hAC' (hdim A hA) (hdim C hC))
        hroot (fun S hS ↦ by rw [hΘ S hS]; exact (D S hS).strictMono_root) hmatch
        (hmem hS₀ hT₀) (hmem hS₁ hT₁) hdT₀ hdT₁ hsub hne⟩

private theorem lift_frontier_and_dim {n : ℕ} {ι : Type*} {a b : ℝ} {B B₀ : Set (Fin n → ℝ)}
    {𝒟 : Set (Set (Fin n → ℝ))} {d : ι → ℕ} {P : ι → (Fin n → ℝ) → ℝ[X]}
    (hB : IsNormalDecomposition B 𝒟) (hB₀ : IsOpen B₀) (hBB₀ : closure B ⊆ B₀) (hab : a < b)
    (hmonic : ∀ k, ∀ x ∈ B₀, (P k x).Monic) (hdeg : ∀ k, ∀ x ∈ B₀, (P k x).natDegree = d k)
    (hcoeffAll : ∀ k j, AnalyticOnNhd ℝ (fun x ↦ (P k x).coeff j) B₀)
    (D : ∀ S ∈ 𝒟, Delineation fun k (x : S) ↦ P k x)
    (hbnd : ∀ (S : Set (Fin n → ℝ)) (hS : S ∈ 𝒟) i x, (D S hS).root i x ∈ Ioo a b) :
    let 𝒞 := ⋃ (S : Set (Fin n → ℝ)) (hS : S ∈ 𝒟), boundedStackCells a b S (D S hS).root
    (∀ {E₀}, E₀ ∈ 𝒞 → ∀ {E₁}, E₁ ∈ 𝒞 → (E₀ ∩ closure E₁).Nonempty → E₀ ⊆ closure E₁) ∧
    (∀ {E₀}, E₀ ∈ 𝒞 → ∀ {E₁}, E₁ ∈ 𝒞 → E₀ ⊆ closure E₁ → E₀ ≠ E₁ →
      ∀ {dE₀ dE₁}, IsAnalyticSubmanifold dE₀ E₀ → IsAnalyticSubmanifold dE₁ E₁ → dE₀ < dE₁) := by
  intro 𝒞
  let H : Set (Fin (n + 1) → ℝ) := {v | v 0 ∈ Ioo a b}
  have hHo : IsOpen H := isOpen_Ioo.preimage (continuous_apply 0)
  have hSB₀ (S : Set (Fin n → ℝ)) (hS : S ∈ 𝒟) : S ⊆ B₀ :=
    (hB.subset_of_mem hS).trans (subset_closure.trans hBB₀)
  obtain ⟨hfront_unclipped, hdim_unclipped⟩ :=
    unclipped_subset_closure_and_dim_lt hB hB₀ hBB₀ hmonic hdeg hcoeffAll D
  refine ⟨fun {E₀} hE₀ {E₁} hE₁ hne ↦ ?_,
    fun {E₀} hE₀ {E₁} hE₁ hsub hne {dE₀ dE₁} hdE₀ hdE₁ ↦ ?_⟩
  · obtain ⟨S₀, hS₀, hE₀S⟩ := mem_iUnion₂.mp hE₀
    obtain ⟨S₁, hS₁, hE₁S⟩ := mem_iUnion₂.mp hE₁
    obtain ⟨T₀, hT₀, rfl⟩ := mem_boundedStackCells.mp hE₀S
    obtain ⟨T₁, hT₁, rfl⟩ := mem_boundedStackCells.mp hE₁S
    have hT₀₁ : T₀ ⊆ closure T₁ := hfront_unclipped hS₀ hS₁ hT₀ hT₁
      (hne.mono (inter_subset_inter inter_subset_left (closure_mono inter_subset_left)))
    intro w ⟨hwT₀, hwH⟩
    rw [inter_comm T₁ H]
    exact hHo.inter_closure ⟨hwH, hT₀₁ hwT₀⟩
  · obtain ⟨S₀, hS₀, hE₀S⟩ := mem_iUnion₂.mp hE₀
    obtain ⟨S₁, hS₁, hE₁S⟩ := mem_iUnion₂.mp hE₁
    obtain ⟨T₀, hT₀, rfl⟩ := mem_boundedStackCells.mp hE₀S
    obtain ⟨T₁, hT₁, rfl⟩ := mem_boundedStackCells.mp hE₁S
    obtain ⟨d₀, hd₀⟩ := hB.exists_isAnalyticSubmanifold hS₀
    obtain ⟨d₁, hd₁⟩ := hB.exists_isAnalyticSubmanifold hS₁
    have hT₀₁ : T₀ ⊆ closure T₁ := hfront_unclipped hS₀ hS₁ hT₀ hT₁
      (hdE₀.nonempty.mono fun w hw ↦
        ⟨inter_subset_left hw, closure_mono inter_subset_left (hsub hw)⟩)
    obtain ⟨dT₀, -, hdT₀⟩ := (D S₀ hS₀).exists_isAnalyticSubmanifold_of_mem_stackCells hd₀
      (fun k j ↦ ((hcoeffAll k j).mono (hSB₀ S₀ hS₀)).analyticOnSubmanifold hd₀) hT₀
    obtain ⟨dT₁, -, hdT₁⟩ := (D S₁ hS₁).exists_isAnalyticSubmanifold_of_mem_stackCells hd₁
      (fun k j ↦ ((hcoeffAll k j).mono (hSB₀ S₁ hS₁)).analyticOnSubmanifold hd₁) hT₁
    have hconn₁ := isConnected_of_mem_boundedStackCells (hB.isConnected hS₁)
      (D S₁ hS₁).continuous_root (D S₁ hS₁).strictMono_root hab (hbnd S₁ hS₁) hE₁S
    obtain rfl : dE₀ = dT₀ := hdE₀.dim_eq (hdT₀.inter hHo hdE₀.nonempty)
    obtain rfl : dE₁ = dT₁ := hdE₁.dim_eq (hdT₁.inter hHo hconn₁.nonempty)
    exact hdim_unclipped hS₀ hS₁ hT₀ hT₁ hdT₀ hdT₁ hT₀₁ fun hTT ↦ hne (hTT ▸ rfl)

/-- **Cylindrical lifting of a normal decomposition.** Given a normal decomposition `𝒟` of `B ⊆ ℝⁿ`,
an open neighborhood `B₀` of `closure B`, and a finite family `P` of monic polynomials of constant
degrees `d k` and analytic coefficients on `B₀` whose real roots on `B` lie in `Ioo a b`, choosing a
delineation `D S hS` on each `S ∈ 𝒟` lifts `𝒟` to a normal decomposition of the cylinder
`{v | Fin.tail v ∈ B ∧ v 0 ∈ Ioo a b}`. -/
theorem IsNormalDecomposition.lift {n : ℕ} {ι : Type*} [Finite ι] {a b : ℝ}
    {B B₀ : Set (Fin n → ℝ)} {𝒟 : Set (Set (Fin n → ℝ))} {d : ι → ℕ}
    {P : ι → (Fin n → ℝ) → ℝ[X]} (hB : IsNormalDecomposition B 𝒟) (hB₀ : IsOpen B₀)
    (hBB₀ : closure B ⊆ B₀) (hab : a < b)
    (hmonic : ∀ k, ∀ x ∈ B₀, (P k x).Monic) (hdeg : ∀ k, ∀ x ∈ B₀, (P k x).natDegree = d k)
    (hcoeff : ∀ k j, j ≤ d k → AnalyticOnNhd ℝ (fun x ↦ (P k x).coeff j) B₀)
    (hroots : ∀ k, ∀ x ∈ B, ∀ t, (P k x).IsRoot t → t ∈ Ioo a b)
    (D : ∀ S ∈ 𝒟, Delineation fun k (x : S) ↦ P k x) :
    IsNormalDecomposition {v : Fin (n + 1) → ℝ | Fin.tail v ∈ B ∧ v 0 ∈ Ioo a b}
      (⋃ (S : Set (Fin n → ℝ)) (hS : S ∈ 𝒟), boundedStackCells a b S (D S hS).root) := by
  classical
  have hbnd (S : Set (Fin n → ℝ)) (hS : S ∈ 𝒟) (i : Fin (D S hS).count) (x : S) :
      (D S hS).root i x ∈ Ioo a b := by
    obtain ⟨k, hk⟩ := (D S hS).exists_multiplicity_pos i
    exact hroots k x.val (hB.subset_of_mem hS x.property) _
      (((D S hS).multiplicity_pos_iff x).mp hk).right
  have hcoeffAll (k : ι) (j : ℕ) : AnalyticOnNhd ℝ (fun x ↦ (P k x).coeff j) B₀ := by
    by_cases hj : j ≤ d k
    · exact hcoeff k j hj
    · intro x hx
      exact (analyticAt_const (v := (0 : ℝ))).congr (eventuallyEq_of_mem (hB₀.mem_nhds hx)
        fun z hz ↦ (coeff_eq_zero_of_natDegree_lt ((hdeg k z hz).trans_lt (lt_of_not_ge hj))).symm)
  obtain ⟨hfront, hdim⟩ := lift_frontier_and_dim hB hB₀ hBB₀ hab hmonic hdeg hcoeffAll D hbnd
  have hHo : IsOpen {v : Fin (n + 1) → ℝ | v 0 ∈ Ioo a b} :=
    isOpen_Ioo.preimage (continuous_apply 0)
  refine
    { finite := hB.finite.biUnion' fun S hS ↦ finite_boundedStackCells a b S (D S hS).root
      sUnion_eq := lift_sUnion_eq hB D
      pairwiseDisjoint := lift_pairwiseDisjoint hab hB D hbnd
      isConnected := fun hE ↦ ?_
      isSemianalytic := fun hE ↦ ?_
      exists_isAnalyticSubmanifold := fun hE ↦ ?_
      isPreconnectedApproachAt := fun hE y ↦ ?_
      subset_closure_of_nonempty_inter := hfront
      dim_lt_of_subset_closure := hdim }
  · obtain ⟨S, hS, hES⟩ := mem_iUnion₂.mp hE
    exact isConnected_of_mem_boundedStackCells (hB.isConnected hS) (D S hS).continuous_root
      (D S hS).strictMono_root hab (hbnd S hS) hES
  · obtain ⟨S, hS, hES⟩ := mem_iUnion₂.mp hE
    obtain ⟨T, hT, rfl⟩ := mem_boundedStackCells.mp hES
    have hScl : closure S ⊆ B₀ := (closure_mono (hB.subset_of_mem hS)).trans hBB₀
    exact ((D S hS).isSemianalytic_of_mem_stackCells (hB.isSemianalytic hS) (fun x hx ↦
      ⟨d, fun k j hj ↦ hcoeff k j hj x (hScl hx), fun k ↦
        Filter.mem_of_superset (hB₀.mem_nhds (hScl hx)) fun z hz ↦ (hdeg k z hz).le⟩) hT).inter
      (isSemianalytic_height_mem_Ioo a b)
  · obtain ⟨S, hS, hES⟩ := mem_iUnion₂.mp hE
    obtain ⟨dS, hdS⟩ := hB.exists_isAnalyticSubmanifold hS
    have hSB₀ : S ⊆ B₀ := (hB.subset_of_mem hS).trans (subset_closure.trans hBB₀)
    have hconn := isConnected_of_mem_boundedStackCells (hB.isConnected hS)
      (D S hS).continuous_root (D S hS).strictMono_root hab (hbnd S hS) hES
    obtain ⟨T, hT, rfl⟩ := mem_boundedStackCells.mp hES
    obtain ⟨dE, -, hdT⟩ := (D S hS).exists_isAnalyticSubmanifold_of_mem_stackCells hdS
      (fun k j ↦ ((hcoeffAll k j).mono hSB₀).analyticOnSubmanifold hdS) hT
    exact ⟨dE, hdT.inter hHo hconn.nonempty⟩
  · obtain ⟨S, hS, hES⟩ := mem_iUnion₂.mp hE
    have hScl : closure S ⊆ B₀ := (closure_mono (hB.subset_of_mem hS)).trans hBB₀
    exact isPreconnectedApproachAt_of_mem_boundedStackCells (D S hS).continuous_root hab
      (D S hS).strictMono_root (hbnd S hS) hES (hB.isPreconnectedApproachAt hS (Fin.tail y))
      (exists_root_tendsto_comap hB₀ hScl hmonic hdeg hcoeff (hB.isPreconnectedApproachAt hS)
        (D S hS) (Fin.tail y))

end TauCeti
