/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Homotopy.Path
public import TauCeti.Analysis.Calculus.LocalPotentials.Basic

import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.UnitInterval

/-!
# Path integrals of covector fields with local potentials

Given a covector field `φ : E → E →L[ℝ] F` and a continuous path `γ : Path a b`, an open potential
subdivision of `γ` is a finite monotone partition `0 = t₀ ≤ t₁ ≤ ⋯ ≤ tₙ = 1` of the unit interval
together with open sets `uₖ` containing `γ '' [tₖ, tₖ₊₁]` and functions `gₖ : E → F` differentiating
to `φ` on `uₖ`. Because any two potentials of `φ` on open neighbourhoods of a preconnected set have
equal increments between points of that set (`TauCeti.sub_eq_sub_of_hasFDerivAt_of_isPreconnected`),
clamping one partition against another telescopes the double sum of endpoint differences and shows
that `∑ k, (gₖ(γ(tₖ₊₁)) - gₖ(γ(tₖ)))` depends neither on the partition, nor on the open sets, nor
on the chosen potentials.

`TauCeti.localPotentialIntegral φ γ` is defined as this common finite sum whenever an open potential
subdivision exists, and `0` otherwise. No differentiability of `γ`, no finite-dimensionality of `E`,
no completeness of `F`, and no measure theory are used. Every path in a domain `s` satisfying
`TauCeti.HasLocalPotentials s φ` admits a ball subdivision by compactness of the unit interval
(`TauCeti.HasLocalPotentials.exists_monotone_ball_subdivision`). On such domains the path integral
satisfies path reversal, concatenation, linearity, `C¹` pullback, and homotopy invariance: a
continuous map `I × I → s` is refined to a uniform square grid in potential balls via the Lebesgue
number lemma (`exists_monotone_Icc_subset_open_cover_unitInterval_prod_self`), where opposite
interior edges cancel in pairs.

## Main definitions and results

* `TauCeti.sub_eq_sub_of_hasFDerivAt_of_isPreconnected`: two potentials of `φ` on open
  neighbourhoods of a preconnected set have equal increments between any two points of that set.
* `TauCeti.localPotentialIntegral`: continuous path integral of `φ` along `γ : Path a b` by finite
  subdivision into open potential neighbourhoods.
* `TauCeti.localPotentialIntegral_eq_sum_sub`: evaluation of `localPotentialIntegral` on any open
  potential subdivision.
* `TauCeti.localPotentialIntegral_of_hasFDerivAt`: fundamental theorem of calculus along any
  continuous path in an open set carrying a global potential.
* `TauCeti.HasLocalPotentials.localPotentialIntegral_trans`,
  `TauCeti.HasLocalPotentials.localPotentialIntegral_pullback`: path concatenation and `C¹`
  pullback.
* `TauCeti.HasLocalPotentials.localPotentialIntegral_add_eq_of_homotopy`,
  `TauCeti.HasLocalPotentials.localPotentialIntegral_eq_of_homotopy`: boundary relation on a free
  homotopy square and homotopy invariance relative to endpoints.

## References

* Lars V. Ahlfors, *Complex Analysis*, 3rd ed., Chapter 4, §1.3 and §4.1 (line integrals of exact
  differentials along continuous curves by chaining local primitives on disks).
* Henri Cartan, *Elementary Theory of Analytic Functions of One or Several Complex Variables*,
  Chapter II, §1 (primitives along continuous paths and homotopy invariance by small squares).
-/

public section

open Set Metric Filter
open scoped Topology ContDiff unitInterval

section Uniqueness

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Two functions differentiating to the same covector field on an open preconnected set have equal
increments between any two points of that set. -/
theorem IsOpen.sub_eq_sub_of_hasFDerivAt {u : Set E} (hu : IsOpen u) (hconn : IsPreconnected u)
    {φ : E → E →L[ℝ] F} {g₁ g₂ : E → F}
    (hg₁ : ∀ z ∈ u, HasFDerivAt g₁ (φ z) z) (hg₂ : ∀ z ∈ u, HasFDerivAt g₂ (φ z) z)
    {x y : E} (hx : x ∈ u) (hy : y ∈ u) :
    g₁ y - g₁ x = g₂ y - g₂ x := by
  have hxy : (g₁ - g₂) x = (g₁ - g₂) y := by
    refine hu.is_const_of_fderiv_eq_zero (𝕜 := ℝ) hconn ?_ ?_ hx hy
    · exact fun z hz ↦ ((hg₁ z hz).sub (hg₂ z hz)).differentiableAt.differentiableWithinAt
    · intro z hz
      simpa using ((hg₁ z hz).sub (hg₂ z hz)).fderiv
  exact sub_eq_sub_iff_sub_eq_sub.mpr (by simpa using hxy.symm)

namespace TauCeti

/-- Two functions differentiating to `φ` on open sets `u₁` and `u₂` containing a preconnected set
`t` have equal increments between any two points of `t`, even if `u₁ ∩ u₂` is disconnected. -/
theorem sub_eq_sub_of_hasFDerivAt_of_isPreconnected {u₁ u₂ t : Set E}
    (hu₁ : IsOpen u₁) (hu₂ : IsOpen u₂) (ht : IsPreconnected t)
    (htu₁ : t ⊆ u₁) (htu₂ : t ⊆ u₂) {φ : E → E →L[ℝ] F} {g₁ g₂ : E → F}
    (hg₁ : ∀ z ∈ u₁, HasFDerivAt g₁ (φ z) z) (hg₂ : ∀ z ∈ u₂, HasFDerivAt g₂ (φ z) z)
    {x y : E} (hx : x ∈ t) (hy : y ∈ t) :
    g₁ y - g₁ x = g₂ y - g₂ x := by
  let u := u₁ ∩ u₂
  have hu : IsOpen u := hu₁.inter hu₂
  have htu : t ⊆ u := subset_inter htu₁ htu₂
  let d : E → F := g₁ - g₂
  have hd_diff : DifferentiableOn ℝ d u := fun z hz ↦
    ((hg₁ z hz.1).sub (hg₂ z hz.2)).differentiableAt.differentiableWithinAt
  have hd_zero : u.EqOn (fderiv ℝ d) 0 := fun z hz ↦ by
    simpa [d] using ((hg₁ z hz.1).sub (hg₂ z hz.2)).fderiv
  have hopen_eq : IsOpen (u ∩ d ⁻¹' {d x}) :=
    hu.isOpen_inter_preimage_of_fderiv_eq_zero hd_diff hd_zero {d x}
  have hopen_ne : IsOpen (u ∩ d ⁻¹' {d x}ᶜ) := by
    have hcont : ContinuousOn d u := hd_diff.continuousOn
    obtain ⟨v, hv_open, hv_eq⟩ := continuousOn_iff'.mp hcont {d x}ᶜ isClosed_singleton.isOpen_compl
    rw [inter_comm, hv_eq]
    exact hv_open.inter hu
  have hcov : t ⊆ (u ∩ d ⁻¹' {d x}) ∪ (u ∩ d ⁻¹' {d x}ᶜ) := fun z hz ↦ by
    by_cases hzx : d z = d x
    · exact Or.inl ⟨htu hz, hzx⟩
    · exact Or.inr ⟨htu hz, hzx⟩
  have hnonempty_eq : (t ∩ (u ∩ d ⁻¹' {d x})).Nonempty := ⟨x, hx, htu hx, rfl⟩
  have hempty_ne : ¬(t ∩ (u ∩ d ⁻¹' {d x}ᶜ)).Nonempty := by
    intro hne
    obtain ⟨z, -, hz₁, hz₂⟩ := ht _ _ hopen_eq hopen_ne hcov hnonempty_eq hne
    exact hz₂.2 hz₁.2
  have hdy : d y = d x := by
    by_contra hne
    exact hempty_ne ⟨y, hy, htu hy, hne⟩
  exact sub_eq_sub_iff_sub_eq_sub.mpr (by simpa [d] using hdy)

end TauCeti

end Uniqueness

namespace TauCeti

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
  {s : Set E} {φ ψ : E → E →L[ℝ] F}

/-- A private witness packaging an open potential subdivision of a path `γ`. -/
private structure PotentialSubdivision (φ : E → E →L[ℝ] F) {a b : E} (γ : Path a b) where
  n : ℕ
  t : ℕ → I
  ht_mono : Monotone t
  ht0 : t 0 = 0
  htn : t n = 1
  u : Fin n → Set E
  hu : ∀ k, IsOpen (u k)
  hγ : ∀ k : Fin n, MapsTo γ (Icc (t k) (t (k + 1))) (u k)
  g : Fin n → E → F
  hg : ∀ k : Fin n, ∀ x ∈ u k, HasFDerivAt (g k) (φ x) x

/-- Sum of potential increments across a `PotentialSubdivision`. -/
private def PotentialSubdivision.sum {a b : E} {γ : Path a b}
    (S : PotentialSubdivision φ γ) : F :=
  ∑ k : Fin S.n, (S.g k (γ (S.t (k + 1))) - S.g k (γ (S.t k)))

/-- Telescoping sum of increments over `Fin n`. -/
private theorem sum_fin_sub {G : Type*} [AddCommGroup G] {n : ℕ} (f : ℕ → G) :
    (∑ k : Fin n, (f (k + 1) - f k)) = f n - f 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [ih, sub_add_sub_cancel']

/-- Two open potential subdivisions of the same path have equal increment sums: clamping one
partition into each subinterval of the other produces a doubly indexed sum that telescopes in one
index to `S₁.sum` and in the other to `S₂.sum`. -/
private theorem PotentialSubdivision.sum_eq {a b : E} {γ : Path a b}
    (S₁ S₂ : PotentialSubdivision φ γ) : S₁.sum = S₂.sum := by
  let clamp₁ (i : Fin S₁.n) (j : ℕ) : I := max (S₁.t i) (min (S₁.t (i + 1)) (S₂.t j))
  let clamp₂ (i : ℕ) (j : Fin S₂.n) : I := max (S₂.t j) (min (S₂.t (j + 1)) (S₁.t i))
  have h₁_0 (i : Fin S₁.n) : clamp₁ i 0 = S₁.t i := by
    simp [clamp₁, S₂.ht0]
  have h₁_n (i : Fin S₁.n) : clamp₁ i S₂.n = S₁.t (i + 1) := by
    dsimp only [clamp₁]
    have hle1 : S₁.t (i + 1) ≤ 1 := unitInterval.le_one _
    rw [S₂.htn, min_eq_left hle1, max_eq_right (S₁.ht_mono (Nat.le_succ _))]
  have h₂_0 (j : Fin S₂.n) : clamp₂ 0 j = S₂.t j := by
    simp [clamp₂, S₁.ht0]
  have h₂_n (j : Fin S₂.n) : clamp₂ S₁.n j = S₂.t (j + 1) := by
    dsimp only [clamp₂]
    have hle1 : S₂.t (j + 1) ≤ 1 := unitInterval.le_one _
    rw [S₁.htn, min_eq_left hle1, max_eq_right (S₂.ht_mono (Nat.le_succ _))]
  have hcell (i : Fin S₁.n) (j : Fin S₂.n) :
      S₁.g i (γ (clamp₁ i (j + 1))) - S₁.g i (γ (clamp₁ i j)) =
        S₂.g j (γ (clamp₂ (i + 1) j)) - S₂.g j (γ (clamp₂ i j)) := by
    have hi : S₁.t i ≤ S₁.t (i + 1) := S₁.ht_mono (Nat.le_succ _)
    have hj : S₂.t j ≤ S₂.t (j + 1) := S₂.ht_mono (Nat.le_succ _)
    rcases le_or_gt (S₁.t (i + 1)) (S₂.t j) with hij | hij
    · have hc₁0 : clamp₁ i j = S₁.t (i + 1) := by
        simp [clamp₁, min_eq_left hij, max_eq_right hi]
      have hc₁1 : clamp₁ i (j + 1) = S₁.t (i + 1) := by
        simp [clamp₁, min_eq_left (hij.trans hj), max_eq_right hi]
      have hc₂0 : clamp₂ i j = S₂.t j := by
        simp [clamp₂, min_eq_right ((hi.trans hij).trans hj), max_eq_left (hi.trans hij)]
      have hc₂1 : clamp₂ (i + 1) j = S₂.t j := by
        simp [clamp₂, min_eq_right (hij.trans hj), max_eq_left hij]
      simp [hc₁0, hc₁1, hc₂0, hc₂1]
    · rcases le_or_gt (S₂.t (j + 1)) (S₁.t i) with hji | hji
      · have hc₁0 : clamp₁ i j = S₁.t i := by
          simp [clamp₁, min_eq_right ((hj.trans hji).trans hi), max_eq_left (hj.trans hji)]
        have hc₁1 : clamp₁ i (j + 1) = S₁.t i := by
          simp [clamp₁, min_eq_right (hji.trans hi), max_eq_left hji]
        have hc₂0 : clamp₂ i j = S₂.t (j + 1) := by
          simp [clamp₂, min_eq_left hji, max_eq_right hj]
        have hc₂1 : clamp₂ (i + 1) j = S₂.t (j + 1) := by
          simp [clamp₂, min_eq_left (hji.trans hi), max_eq_right hj]
        simp [hc₁0, hc₁1, hc₂0, hc₂1]
      · let lo : I := max (S₁.t i) (S₂.t j)
        let hi' : I := min (S₁.t (i + 1)) (S₂.t (j + 1))
        have hlo_le_hi : lo ≤ hi' := max_le (le_min hi hji.le) (le_min hij.le hj)
        have hc₁0 : clamp₁ i j = lo := by
          simp [clamp₁, lo, min_eq_right hij.le]
        have hc₂0 : clamp₂ i j = lo := by
          simp [clamp₂, lo, min_eq_right hji.le, max_comm]
        have hc₁1 : clamp₁ i (j + 1) = hi' :=
          max_eq_right ((le_max_left (S₁.t i) (S₂.t j)).trans hlo_le_hi)
        have hc₂1 : clamp₂ (i + 1) j = hi' := by
          dsimp only [clamp₂]
          have : min (S₂.t (j + 1)) (S₁.t (i + 1)) = hi' := min_comm _ _
          rw [this, max_eq_right ((le_max_right (S₁.t i) (S₂.t j)).trans hlo_le_hi)]
        rw [hc₁0, hc₁1, hc₂0, hc₂1]
        have hsub₁ : Icc lo hi' ⊆ Icc (S₁.t i) (S₁.t (i + 1)) :=
          Icc_subset_Icc (le_max_left _ _) (min_le_left _ _)
        have hsub₂ : Icc lo hi' ⊆ Icc (S₂.t j) (S₂.t (j + 1)) :=
          Icc_subset_Icc (le_max_right _ _) (min_le_right _ _)
        have hK : IsPreconnected (γ '' Icc lo hi') := by
          have hIcc : IsPreconnected (Icc lo hi') := by
            have heq : Subtype.val '' (Icc lo hi' : Set I) = Icc (lo : ℝ) (hi' : ℝ) := by
              ext x
              constructor
              · rintro ⟨y, ⟨hy1, hy2⟩, rfl⟩
                exact ⟨hy1, hy2⟩
              · rintro ⟨hx1, hx2⟩
                exact ⟨⟨x, (unitInterval.nonneg lo).trans hx1,
                  hx2.trans (unitInterval.le_one hi')⟩, ⟨hx1, hx2⟩, rfl⟩
            exact Topology.IsInducing.subtypeVal.isPreconnected_image.mp
              (heq ▸ isPreconnected_Icc)
          exact hIcc.image γ γ.continuous.continuousOn
        exact sub_eq_sub_of_hasFDerivAt_of_isPreconnected (S₁.hu i) (S₂.hu j) hK
          ((S₁.hγ i).mono_left hsub₁).image_subset ((S₂.hγ j).mono_left hsub₂).image_subset
          (S₁.hg i) (S₂.hg j) (mem_image_of_mem γ ⟨le_rfl, hlo_le_hi⟩)
          (mem_image_of_mem γ ⟨hlo_le_hi, le_rfl⟩)
  calc
    S₁.sum
      = ∑ i : Fin S₁.n, (S₁.g i (γ (clamp₁ i S₂.n)) - S₁.g i (γ (clamp₁ i 0))) := by
          simp_rw [h₁_n, h₁_0]; rfl
    _ = ∑ i : Fin S₁.n, ∑ j : Fin S₂.n,
          (S₁.g i (γ (clamp₁ i (j + 1))) - S₁.g i (γ (clamp₁ i j))) := by
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          exact (sum_fin_sub (fun j ↦ S₁.g i (γ (clamp₁ i j)))).symm
    _ = ∑ i : Fin S₁.n, ∑ j : Fin S₂.n,
          (S₂.g j (γ (clamp₂ (i + 1) j)) - S₂.g j (γ (clamp₂ i j))) := by
          refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ hcell i j
    _ = ∑ j : Fin S₂.n, ∑ i : Fin S₁.n,
          (S₂.g j (γ (clamp₂ (i + 1) j)) - S₂.g j (γ (clamp₂ i j))) := Finset.sum_comm
    _ = ∑ j : Fin S₂.n, (S₂.g j (γ (clamp₂ S₁.n j)) - S₂.g j (γ (clamp₂ 0 j))) := by
          refine Finset.sum_congr rfl fun j _ ↦ ?_
          exact sum_fin_sub (fun i ↦ S₂.g j (γ (clamp₂ i j)))
    _ = S₂.sum := by
          simp_rw [h₂_n, h₂_0]; rfl

/-- Compactness of the unit interval refines any continuous path in a `HasLocalPotentials` domain
into a monotone partition whose subintervals map into `C¹` potential balls. -/
theorem HasLocalPotentials.exists_monotone_ball_subdivision (hφ : HasLocalPotentials s φ)
    {a b : E} (γ : Path a b) (hγ : ∀ t, γ t ∈ s) :
    ∃ (n : ℕ) (t : ℕ → I) (c : Fin n → E) (r : Fin n → ℝ) (g : Fin n → E → F),
      Monotone t ∧ t 0 = 0 ∧ t n = 1 ∧
      (∀ k, 0 < r k) ∧ (∀ k, ball (c k) (r k) ⊆ s) ∧
      (∀ k : Fin n, MapsTo γ (Icc (t k) (t (k + 1))) (ball (c k) (r k))) ∧
      (∀ k, ContDiffOn ℝ 1 (g k) (ball (c k) (r k))) ∧
      ∀ k : Fin n, ∀ y ∈ ball (c k) (r k), HasFDerivAt (g k) (φ y) y := by
  classical
  choose R hRpos hRs G hGcont hGderiv using fun p : s ↦ hasLocalPotentials_iff.mp hφ p.1 p.2
  let cover (p : s) : Set I := γ ⁻¹' ball p.1 (R p)
  have hopen : ∀ p : s, IsOpen (cover p) := fun p ↦ isOpen_ball.preimage γ.continuous
  have huniv : (univ : Set I) ⊆ ⋃ p : s, cover p := fun x _ ↦
    mem_iUnion.mpr ⟨⟨γ x, hγ x⟩, mem_ball_self (hRpos ⟨γ x, hγ x⟩)⟩
  obtain ⟨t, ht0, ht_mono, ⟨n, htn⟩, hsub⟩ :=
    exists_monotone_Icc_subset_open_cover_unitInterval hopen huniv
  choose idx hidx using fun k : Fin n ↦ hsub k
  exact ⟨n, t, fun k ↦ (idx k).1, fun k ↦ R (idx k), fun k ↦ G (idx k),
    ht_mono, ht0, htn n le_rfl, fun k ↦ hRpos (idx k), fun k ↦ hRs (idx k),
    fun k x hx ↦ hidx k hx, fun k ↦ hGcont (idx k), fun k ↦ hGderiv (idx k)⟩

private theorem HasLocalPotentials.nonempty_potentialSubdivision (hφ : HasLocalPotentials s φ)
    {a b : E} (γ : Path a b) (hγ : ∀ t, γ t ∈ s) :
    Nonempty (PotentialSubdivision φ γ) := by
  obtain ⟨n, t, c, r, g, ht_mono, ht0, htn, _, _, hmaps, _, hderiv⟩ :=
    hφ.exists_monotone_ball_subdivision γ hγ
  exact ⟨⟨n, t, ht_mono, ht0, htn, fun k ↦ ball (c k) (r k), fun _ ↦ isOpen_ball, hmaps, g, hderiv⟩⟩

/-- The continuous path integral of a covector field `φ : E → E →L[ℝ] F` along `γ : Path a b`,
computed by summing potential increments over any open potential subdivision of `γ` and returning
`0` if no such subdivision exists. -/
noncomputable def localPotentialIntegral (φ : E → E →L[ℝ] F) {a b : E} (γ : Path a b) : F :=
  open Classical in
  if h : Nonempty (PotentialSubdivision φ γ) then h.some.sum else 0

/-- Evaluates `localPotentialIntegral φ γ` on any monotone partition of `I` whose subintervals map
into open sets carrying potentials for `φ`. -/
theorem localPotentialIntegral_eq_sum_sub {a b : E} {γ : Path a b} {n : ℕ} {t : ℕ → I}
    (ht_mono : Monotone t) (ht0 : t 0 = 0) (htn : t n = 1)
    {u : Fin n → Set E} (hu : ∀ k, IsOpen (u k))
    (hγ : ∀ k : Fin n, MapsTo γ (Icc (t k) (t (k + 1))) (u k))
    {g : Fin n → E → F} (hg : ∀ k : Fin n, ∀ x ∈ u k, HasFDerivAt (g k) (φ x) x) :
    localPotentialIntegral φ γ = ∑ k : Fin n, (g k (γ (t (k + 1))) - g k (γ (t k))) := by
  let S : PotentialSubdivision φ γ := ⟨n, t, ht_mono, ht0, htn, u, hu, hγ, g, hg⟩
  have hne : Nonempty (PotentialSubdivision φ γ) := ⟨S⟩
  simp only [localPotentialIntegral, hne, ↓reduceDIte]
  exact hne.some.sum_eq S

/-- Fundamental theorem of calculus for `localPotentialIntegral`: if `g` differentiates to `φ` on an
open set `u` containing the image of a continuous path `γ : Path a b`, then the path integral equals
`g b - g a`. -/
theorem localPotentialIntegral_of_hasFDerivAt {u : Set E} (hu : IsOpen u)
    {a b : E} {γ : Path a b} (hγ : ∀ t, γ t ∈ u)
    {g : E → F} (hg : ∀ x ∈ u, HasFDerivAt g (φ x) x) :
    localPotentialIntegral φ γ = g b - g a := by
  let t : ℕ → I := fun k ↦ if k = 0 then 0 else 1
  have ht_mono : Monotone t := by
    intro i j hij
    dsimp [t]
    split_ifs with hi hj hj
    · exact le_rfl
    · exact unitInterval.nonneg 1
    · omega
    · exact le_rfl
  rw [localPotentialIntegral_eq_sum_sub ht_mono rfl (by simp [t])
    (u := fun _ : Fin 1 ↦ u) (fun _ ↦ hu) (fun _ x _ ↦ hγ x)
    (g := fun _ ↦ g) (fun _ ↦ hg)]
  simp [t]

/-- The path integral along a constant path is zero. -/
@[simp]
theorem localPotentialIntegral_refl (φ : E → E →L[ℝ] F) (a : E) :
    localPotentialIntegral φ (Path.refl a) = 0 := by
  classical
  by_cases h : Nonempty (PotentialSubdivision φ (Path.refl a))
  · obtain ⟨S⟩ := h
    rw [localPotentialIntegral_eq_sum_sub S.ht_mono S.ht0 S.htn S.hu S.hγ S.hg]
    simp
  · simp [localPotentialIntegral, h]

/-- Endpoint casting of a path does not change `localPotentialIntegral`. -/
@[simp]
theorem localPotentialIntegral_cast (φ : E → E →L[ℝ] F) {a b a' b' : E} (γ : Path a b)
    (ha : a' = a) (hb : b' = b) :
    localPotentialIntegral φ (γ.cast ha hb) = localPotentialIntegral φ γ := by
  subst ha hb
  rfl

/-- Reversing a path negates `localPotentialIntegral`. -/
@[simp]
theorem localPotentialIntegral_symm (φ : E → E →L[ℝ] F) {a b : E} (γ : Path a b) :
    localPotentialIntegral φ γ.symm = -localPotentialIntegral φ γ := by
  classical
  let rev {x y : E} {p : Path x y} (S : PotentialSubdivision φ p) :
      PotentialSubdivision φ p.symm :=
    { n := S.n
      t := fun k ↦ if k ≤ S.n then σ (S.t (S.n - k)) else 1
      ht_mono := by
        intro i j hij
        by_cases hj : j ≤ S.n
        · have hi : i ≤ S.n := hij.trans hj
          simp only [hi, hj, ↓reduceIte, ← Subtype.coe_le_coe, unitInterval.coe_symm_eq]
          linarith [Subtype.coe_le_coe.mpr (S.ht_mono (Nat.sub_le_sub_left hij S.n))]
        · simp only [hj, ↓reduceIte]
          exact unitInterval.le_one _
      ht0 := by simp [S.htn]
      htn := by simp [S.ht0]
      u := fun k ↦ S.u k.rev
      hu := fun k ↦ S.hu k.rev
      hγ := by
        intro k x ⟨hx1, hx2⟩
        have hk1 : (k : ℕ) + 1 ≤ S.n := k.2
        have hk0 : (k : ℕ) ≤ S.n := Nat.le_of_succ_le hk1
        simp only [hk0, hk1, ↓reduceIte] at hx1 hx2
        change p (σ x) ∈ S.u k.rev
        refine S.hγ k.rev ⟨?_, ?_⟩
        · have hrev : (k.rev : ℕ) = S.n - ((k : ℕ) + 1) := by simp [Fin.rev]
          rw [hrev]
          exact unitInterval.le_symm_comm.mp hx2
        · have hrev1 : (k.rev : ℕ) + 1 = S.n - (k : ℕ) := by
            simp [Fin.rev]; omega
          rw [hrev1]
          exact unitInterval.symm_le_comm.mp hx1
      g := fun k ↦ S.g k.rev
      hg := fun k ↦ S.hg k.rev }
  by_cases h : Nonempty (PotentialSubdivision φ γ)
  · obtain ⟨S⟩ := h
    let S' := rev S
    rw [localPotentialIntegral_eq_sum_sub S.ht_mono S.ht0 S.htn S.hu S.hγ S.hg,
      localPotentialIntegral_eq_sum_sub S'.ht_mono S'.ht0 S'.htn S'.hu S'.hγ S'.hg]
    dsimp [S', rev]
    rw [← Finset.sum_neg_distrib, ← Equiv.sum_comp Fin.revPerm]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    simp only [Fin.revPerm_apply, Fin.rev_rev]
    have hk1 : (k.rev : ℕ) + 1 ≤ S.n := k.rev.2
    have hk0 : (k.rev : ℕ) ≤ S.n := Nat.le_of_succ_le hk1
    have hsub1 : S.n - ((k.rev : ℕ) + 1) = (k : ℕ) := by simp [Fin.rev]; omega
    have hsub0 : S.n - (k.rev : ℕ) = (k : ℕ) + 1 := by simp [Fin.rev]; omega
    simp only [hk0, hk1, ↓reduceIte, hsub1, hsub0, Path.symm_apply, Function.comp_apply,
      unitInterval.symm_symm, neg_sub]
  · have h' : ¬Nonempty (PotentialSubdivision φ γ.symm) := by
      rintro ⟨S⟩
      have hsymm : γ.symm.symm = γ := Path.symm_symm γ
      exact h ⟨hsymm ▸ rev S⟩
    simp [localPotentialIntegral, h, h']

/-- The zero covector field integrates to zero along every path. -/
@[simp]
theorem localPotentialIntegral_zero {a b : E} (γ : Path a b) :
    localPotentialIntegral (0 : E → E →L[ℝ] F) γ = 0 := by
  have := localPotentialIntegral_of_hasFDerivAt (φ := (0 : E → E →L[ℝ] F)) (γ := γ) isOpen_univ
    (fun _ ↦ mem_univ _) (g := fun _ ↦ (0 : F)) (fun x _ ↦ hasFDerivAt_const (0 : F) x)
  simpa using this

/-- Function-literal form of `localPotentialIntegral_zero`. -/
@[simp]
theorem localPotentialIntegral_fun_zero {a b : E} (γ : Path a b) :
    localPotentialIntegral (fun _ : E ↦ (0 : E →L[ℝ] F)) γ = 0 :=
  localPotentialIntegral_zero γ

/-- Integrating a constant covector field `L` along any continuous path yields `L (b - a)`. -/
@[simp]
theorem localPotentialIntegral_const (L : E →L[ℝ] F) {a b : E} (γ : Path a b) :
    localPotentialIntegral (fun _ ↦ L) γ = L (b - a) := by
  rw [localPotentialIntegral_of_hasFDerivAt isOpen_univ (fun _ ↦ mem_univ _)
    (fun _ _ ↦ L.hasFDerivAt), L.map_sub]

/-- Negating the covector field negates `localPotentialIntegral`. -/
@[simp]
theorem localPotentialIntegral_neg (φ : E → E →L[ℝ] F) {a b : E} (γ : Path a b) :
    localPotentialIntegral (-φ) γ = -localPotentialIntegral φ γ := by
  classical
  let negSub {ψ : E → E →L[ℝ] F} (S : PotentialSubdivision ψ γ) :
      PotentialSubdivision (-ψ) γ :=
    { S with
      g := fun k ↦ -S.g k
      hg := fun k x hx ↦ (S.hg k x hx).neg }
  by_cases h : Nonempty (PotentialSubdivision φ γ)
  · obtain ⟨S⟩ := h
    let S' := negSub S
    rw [localPotentialIntegral_eq_sum_sub S.ht_mono S.ht0 S.htn S.hu S.hγ S.hg,
      localPotentialIntegral_eq_sum_sub S'.ht_mono S'.ht0 S'.htn S'.hu S'.hγ S'.hg,
      ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    simp only [S', negSub, Pi.neg_apply]
    abel
  · have h' : ¬Nonempty (PotentialSubdivision (-φ) γ) := fun ⟨S⟩ ↦
      h ⟨by simpa [neg_neg] using negSub S⟩
    simp [localPotentialIntegral, h, h']

/-- Function-literal form of `localPotentialIntegral_neg`. -/
@[simp]
theorem localPotentialIntegral_fun_neg (φ : E → E →L[ℝ] F) {a b : E} (γ : Path a b) :
    localPotentialIntegral (fun x ↦ -φ x) γ = -localPotentialIntegral φ γ :=
  localPotentialIntegral_neg φ γ

/-- Real scalar multiplication commutes with `localPotentialIntegral`. -/
@[simp]
theorem localPotentialIntegral_smul (c : ℝ) (φ : E → E →L[ℝ] F) {a b : E} (γ : Path a b) :
    localPotentialIntegral (c • φ) γ = c • localPotentialIntegral φ γ := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  classical
  let smulSub (d : ℝ) {ψ : E → E →L[ℝ] F} (S : PotentialSubdivision ψ γ) :
      PotentialSubdivision (d • ψ) γ :=
    { S with
      g := fun k ↦ d • S.g k
      hg := fun k x hx ↦ (S.hg k x hx).const_smul d }
  by_cases h : Nonempty (PotentialSubdivision φ γ)
  · obtain ⟨S⟩ := h
    let S' := smulSub c S
    rw [localPotentialIntegral_eq_sum_sub S.ht_mono S.ht0 S.htn S.hu S.hγ S.hg,
      localPotentialIntegral_eq_sum_sub S'.ht_mono S'.ht0 S'.htn S'.hu S'.hγ S'.hg]
    simp [S', smulSub, Finset.smul_sum, smul_sub]
  · have h' : ¬Nonempty (PotentialSubdivision (c • φ) γ) := fun ⟨S⟩ ↦
      h ⟨by simpa [smul_smul, inv_mul_cancel₀ hc] using smulSub c⁻¹ S⟩
    simp [localPotentialIntegral, h, h']

/-- Function-literal form of `localPotentialIntegral_smul`. -/
@[simp]
theorem localPotentialIntegral_fun_smul (c : ℝ) (φ : E → E →L[ℝ] F) {a b : E} (γ : Path a b) :
    localPotentialIntegral (fun x ↦ c • φ x) γ = c • localPotentialIntegral φ γ :=
  localPotentialIntegral_smul c φ γ

/-- Two covector fields that agree on an open set containing `γ` have the same
`localPotentialIntegral`. -/
theorem localPotentialIntegral_congr_of_isOpen {u : Set E} (hu : IsOpen u)
    {a b : E} {γ : Path a b} (hγ : ∀ t, γ t ∈ u) (h : EqOn φ ψ u) :
    localPotentialIntegral φ γ = localPotentialIntegral ψ γ := by
  classical
  let tr {ω₁ ω₂ : E → E →L[ℝ] F} (heq : EqOn ω₁ ω₂ u) (S : PotentialSubdivision ω₁ γ) :
      PotentialSubdivision ω₂ γ :=
    { S with
      u := fun k ↦ S.u k ∩ u
      hu := fun k ↦ (S.hu k).inter hu
      hγ := fun k x hx ↦ ⟨S.hγ k hx, hγ x⟩
      hg := fun k x hx ↦ heq hx.2 ▸ S.hg k x hx.1 }
  by_cases hne : Nonempty (PotentialSubdivision φ γ)
  · obtain ⟨S⟩ := hne
    let S' := tr h S
    rw [localPotentialIntegral_eq_sum_sub S.ht_mono S.ht0 S.htn S.hu S.hγ S.hg,
      localPotentialIntegral_eq_sum_sub S'.ht_mono S'.ht0 S'.htn S'.hu S'.hγ S'.hg]
  · have hne' : ¬Nonempty (PotentialSubdivision ψ γ) := fun ⟨S⟩ ↦ hne ⟨tr h.symm S⟩
    simp [localPotentialIntegral, hne, hne']

/-- Additivity of `localPotentialIntegral` in the covector field on a `HasLocalPotentials`
domain. -/
theorem HasLocalPotentials.localPotentialIntegral_add
    (hφ : HasLocalPotentials s φ) (hψ : HasLocalPotentials s ψ)
    {a b : E} (γ : Path a b) (hγ : ∀ t, γ t ∈ s) :
    localPotentialIntegral (φ + ψ) γ =
      localPotentialIntegral φ γ + localPotentialIntegral ψ γ := by
  classical
  choose r₁ hr₁pos _ g₁ _ hg₁ using fun p : s ↦ hasLocalPotentials_iff.mp hφ p.1 p.2
  choose r₂ hr₂pos _ g₂ _ hg₂ using fun p : s ↦ hasLocalPotentials_iff.mp hψ p.1 p.2
  let r (p : s) : ℝ := min (r₁ p) (r₂ p)
  have hrpos (p : s) : 0 < r p := lt_min (hr₁pos p) (hr₂pos p)
  obtain ⟨t, ht0, ht_mono, ⟨n, htn⟩, hsub⟩ :=
    exists_monotone_Icc_subset_open_cover_unitInterval
      (c := fun p : s ↦ γ ⁻¹' ball p.1 (r p))
      (fun p ↦ isOpen_ball.preimage γ.continuous)
      (fun x _ ↦ mem_iUnion.mpr ⟨⟨γ x, hγ x⟩, mem_ball_self (hrpos ⟨γ x, hγ x⟩)⟩)
  choose idx hidx using fun k : Fin n ↦ hsub k
  have hmaps₁ (k : Fin n) : MapsTo γ (Icc (t k) (t (k + 1))) (ball (idx k).1 (r₁ (idx k))) :=
    fun x hx ↦ ball_subset_ball (min_le_left _ _) (hidx k hx)
  have hmaps₂ (k : Fin n) : MapsTo γ (Icc (t k) (t (k + 1))) (ball (idx k).1 (r₂ (idx k))) :=
    fun x hx ↦ ball_subset_ball (min_le_right _ _) (hidx k hx)
  have hmaps (k : Fin n) : MapsTo γ (Icc (t k) (t (k + 1))) (ball (idx k).1 (r (idx k))) :=
    fun x hx ↦ hidx k hx
  rw [localPotentialIntegral_eq_sum_sub (φ := φ + ψ) ht_mono ht0 (htn n le_rfl)
        (u := fun k ↦ ball (idx k).1 (r (idx k))) (fun _ ↦ isOpen_ball) hmaps
        (g := fun k ↦ g₁ (idx k) + g₂ (idx k))
        (fun k y hy ↦ (hg₁ (idx k) y (ball_subset_ball (min_le_left _ _) hy)).add
          (hg₂ (idx k) y (ball_subset_ball (min_le_right _ _) hy))),
      localPotentialIntegral_eq_sum_sub ht_mono ht0 (htn n le_rfl)
        (u := fun k ↦ ball (idx k).1 (r₁ (idx k))) (fun _ ↦ isOpen_ball) hmaps₁
        (g := fun k ↦ g₁ (idx k)) (fun k ↦ hg₁ (idx k)),
      localPotentialIntegral_eq_sum_sub ht_mono ht0 (htn n le_rfl)
        (u := fun k ↦ ball (idx k).1 (r₂ (idx k))) (fun _ ↦ isOpen_ball) hmaps₂
        (g := fun k ↦ g₂ (idx k)) (fun k ↦ hg₂ (idx k)),
      ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  simp only [Pi.add_apply]
  abel

/-- Subtraction of covector fields in `localPotentialIntegral` on a `HasLocalPotentials` domain. -/
theorem HasLocalPotentials.localPotentialIntegral_sub
    (hφ : HasLocalPotentials s φ) (hψ : HasLocalPotentials s ψ)
    {a b : E} (γ : Path a b) (hγ : ∀ t, γ t ∈ s) :
    localPotentialIntegral (φ - ψ) γ =
      localPotentialIntegral φ γ - localPotentialIntegral ψ γ := by
  rw [sub_eq_add_neg, hφ.localPotentialIntegral_add hψ.neg γ hγ, localPotentialIntegral_neg,
    sub_eq_add_neg]

/-- Path concatenation adds `localPotentialIntegral` values on a `HasLocalPotentials` domain. -/
theorem HasLocalPotentials.localPotentialIntegral_trans (hφ : HasLocalPotentials s φ)
    {a b c : E} (γ₁ : Path a b) (γ₂ : Path b c)
    (hγ₁ : ∀ t, γ₁ t ∈ s) (hγ₂ : ∀ t, γ₂ t ∈ s) :
    localPotentialIntegral φ (γ₁.trans γ₂) =
      localPotentialIntegral φ γ₁ + localPotentialIntegral φ γ₂ := by
  obtain ⟨S₁⟩ := hφ.nonempty_potentialSubdivision γ₁ hγ₁
  obtain ⟨S₂⟩ := hφ.nonempty_potentialSubdivision γ₂ hγ₂
  let halfLeft (x : I) : I := ⟨(x : ℝ) / 2,
    ⟨by linarith [unitInterval.nonneg x], by linarith [unitInterval.le_one x]⟩⟩
  let halfRight (x : I) : I := ⟨((x : ℝ) + 1) / 2,
    ⟨by linarith [unitInterval.nonneg x], by linarith [unitInterval.le_one x]⟩⟩
  have hmonoL : Monotone halfLeft := fun x y hxy ↦ by
    change (x : ℝ) / 2 ≤ (y : ℝ) / 2; linarith [Subtype.coe_le_coe.mpr hxy]
  have hmonoR : Monotone halfRight := fun x y hxy ↦ by
    change ((x : ℝ) + 1) / 2 ≤ ((y : ℝ) + 1) / 2; linarith [Subtype.coe_le_coe.mpr hxy]
  let t (k : ℕ) : I :=
    if k ≤ S₁.n then halfLeft (S₁.t k) else halfRight (S₂.t (k - S₁.n))
  have ht_mono : Monotone t := by
    intro i j hij
    dsimp [t]
    split_ifs with hi hj hj
    · exact hmonoL (S₁.ht_mono hij)
    · calc halfLeft (S₁.t i) ≤ halfLeft (S₁.t S₁.n) := hmonoL (S₁.ht_mono hi)
        _ = halfRight (S₂.t 0) := by ext; simp [halfLeft, halfRight, S₁.htn, S₂.ht0]
        _ ≤ halfRight (S₂.t (j - S₁.n)) := hmonoR (S₂.ht_mono (Nat.zero_le _))
    · omega
    · exact hmonoR (S₂.ht_mono (Nat.sub_le_sub_right hij S₁.n))
  have ht0 : t 0 = 0 := by ext; simp [t, halfLeft, S₁.ht0]
  have htn : t (S₁.n + S₂.n) = 1 := by
    by_cases h₂0 : S₂.n = 0
    · have h01 : (0 : I) = 1 := S₂.ht0.symm.trans (h₂0 ▸ S₂.htn)
      exact absurd h01 zero_ne_one
    · have hnot : ¬S₁.n + S₂.n ≤ S₁.n := by omega
      ext; simp [t, hnot, halfRight, S₂.htn]
  let u (k : Fin (S₁.n + S₂.n)) : Set E :=
    Fin.addCases S₁.u S₂.u k
  let g (k : Fin (S₁.n + S₂.n)) : E → F :=
    Fin.addCases S₁.g S₂.g k
  have hu (k : Fin (S₁.n + S₂.n)) : IsOpen (u k) := by
    refine Fin.addCases (fun i ↦ ?_) (fun j ↦ ?_) k
    · simpa [u] using S₁.hu i
    · simpa [u] using S₂.hu j
  have hg (k : Fin (S₁.n + S₂.n)) : ∀ x ∈ u k, HasFDerivAt (g k) (φ x) x := by
    refine Fin.addCases (fun i ↦ ?_) (fun j ↦ ?_) k
    · simpa [u, g] using S₁.hg i
    · simpa [u, g] using S₂.hg j
  have htransL (x : I) : (γ₁.trans γ₂) (halfLeft x) = γ₁ x := by
    rw [Path.trans_apply]
    split_ifs with hle
    · congr 1; ext; change 2 * ((x : ℝ) / 2) = x; ring
    · exfalso
      change ¬(x : ℝ) / 2 ≤ 1 / 2 at hle
      linarith [unitInterval.le_one x]
  have htransR (x : I) : (γ₁.trans γ₂) (halfRight x) = γ₂ x := by
    rw [Path.trans_apply]
    split_ifs with hle
    · have hx0 : (x : ℝ) = 0 := by
        change ((x : ℝ) + 1) / 2 ≤ 1 / 2 at hle
        linarith [unitInterval.nonneg x]
      have hx_zero : x = 0 := Subtype.ext hx0
      subst hx_zero
      convert γ₁.target.trans γ₂.source.symm using 2
      ext; change 2 * (((0 : ℝ) + 1) / 2) = 1; ring
    · congr 1; ext; change 2 * (((x : ℝ) + 1) / 2) - 1 = x; ring
  have hmaps (k : Fin (S₁.n + S₂.n)) :
      MapsTo (γ₁.trans γ₂) (Icc (t k) (t (k + 1))) (u k) := by
    refine Fin.addCases (fun i x ⟨hx1, hx2⟩ ↦ ?_) (fun j x ⟨hx1, hx2⟩ ↦ ?_) k
    · have hi1 : (i : ℕ) + 1 ≤ S₁.n := i.2
      have hi0 : (i : ℕ) ≤ S₁.n := Nat.le_of_succ_le hi1
      change t (i : ℕ) ≤ x at hx1
      change x ≤ t ((i : ℕ) + 1) at hx2
      simp only [t, hi0, hi1, ↓reduceIte] at hx1 hx2
      have hx1' : (S₁.t i : ℝ) / 2 ≤ x := hx1
      have hx2' : (x : ℝ) ≤ (S₁.t ((i : ℕ) + 1) : ℝ) / 2 := hx2
      have hx_le_half : (x : ℝ) ≤ 1 / 2 := by
        linarith [unitInterval.le_one (S₁.t ((i : ℕ) + 1))]
      let y : I := ⟨2 * (x : ℝ), ⟨by linarith [unitInterval.nonneg x], by linarith⟩⟩
      have hxy : halfLeft y = x := by ext; change (2 * (x : ℝ)) / 2 = x; ring
      rw [← hxy, htransL]
      simpa [u] using S₁.hγ i
        ⟨Subtype.coe_le_coe.mp (by change (S₁.t i : ℝ) ≤ 2 * (x : ℝ); linarith),
         Subtype.coe_le_coe.mp (by change 2 * (x : ℝ) ≤ S₁.t ((i : ℕ) + 1); linarith)⟩
    · have hj_left : t (S₁.n + j) = halfRight (S₂.t j) := by
        dsimp [t]
        split_ifs with hle
        · have hj0 : (j : ℕ) = 0 := by omega
          ext; simp [hj0, halfLeft, halfRight, S₁.htn, S₂.ht0]
        · simp
      have hj_right : t (S₁.n + (j : ℕ) + 1) = halfRight (S₂.t ((j : ℕ) + 1)) := by
        have hnot : ¬S₁.n + (j : ℕ) + 1 ≤ S₁.n := by omega
        have hsub : S₁.n + (j : ℕ) + 1 - S₁.n = (j : ℕ) + 1 := by omega
        simp [t, hnot, hsub]
      change t (S₁.n + j) ≤ x at hx1
      change x ≤ t (S₁.n + (j : ℕ) + 1) at hx2
      rw [hj_left] at hx1
      rw [hj_right] at hx2
      have hx1' : ((S₂.t j : ℝ) + 1) / 2 ≤ x := hx1
      have hx2' : (x : ℝ) ≤ ((S₂.t ((j : ℕ) + 1) : ℝ) + 1) / 2 := hx2
      have hx_ge_half : (1 : ℝ) / 2 ≤ x := by
        linarith [unitInterval.nonneg (S₂.t j)]
      let y : I := ⟨2 * (x : ℝ) - 1, ⟨by linarith, by linarith [unitInterval.le_one x]⟩⟩
      have hxy : halfRight y = x := by ext; change (2 * (x : ℝ) - 1 + 1) / 2 = x; ring
      rw [← hxy, htransR]
      simpa [u] using S₂.hγ j
        ⟨Subtype.coe_le_coe.mp (by change (S₂.t j : ℝ) ≤ 2 * (x : ℝ) - 1; linarith),
         Subtype.coe_le_coe.mp (by change 2 * (x : ℝ) - 1 ≤ S₂.t ((j : ℕ) + 1); linarith)⟩
  rw [localPotentialIntegral_eq_sum_sub ht_mono ht0 htn hu hmaps hg,
    localPotentialIntegral_eq_sum_sub S₁.ht_mono S₁.ht0 S₁.htn S₁.hu S₁.hγ S₁.hg,
    localPotentialIntegral_eq_sum_sub S₂.ht_mono S₂.ht0 S₂.htn S₂.hu S₂.hγ S₂.hg,
    Fin.sum_univ_add]
  congr 1
  · refine Finset.sum_congr rfl fun i _ ↦ ?_
    have hi1 : (i : ℕ) + 1 ≤ S₁.n := i.2
    have hi0 : (i : ℕ) ≤ S₁.n := Nat.le_of_succ_le hi1
    simp only [Fin.val_castAdd, g, Fin.addCases_left, t, hi0, hi1, ↓reduceIte, htransL]
  · refine Finset.sum_congr rfl fun j _ ↦ ?_
    have hj_left : t (S₁.n + j) = halfRight (S₂.t j) := by
      dsimp [t]
      split_ifs with hle
      · have hj0 : (j : ℕ) = 0 := by omega
        ext; simp [hj0, halfLeft, halfRight, S₁.htn, S₂.ht0]
      · simp
    have hj_right : t (S₁.n + (j : ℕ) + 1) = halfRight (S₂.t ((j : ℕ) + 1)) := by
      have hnot : ¬S₁.n + (j : ℕ) + 1 ≤ S₁.n := by omega
      have hsub : S₁.n + (j : ℕ) + 1 - S₁.n = (j : ℕ) + 1 := by omega
      simp [t, hnot, hsub]
    simp only [Fin.val_natAdd, g, Fin.addCases_right]
    rw [hj_right, hj_left, htransR, htransR]

/-- Change of variables / pullback formula for `localPotentialIntegral` along a `C¹` map `f` of
open domains, stated for any path `γ'` pointwise equal to `f ∘ γ` so that `f` need not be continuous
outside `u`. -/
theorem HasLocalPotentials.localPotentialIntegral_pullback {u : Set G} {f : G → E}
    (hφ : HasLocalPotentials s φ) (hu : IsOpen u) (hf : ContDiffOn ℝ 1 f u)
    (hfs : MapsTo f u s) {a b : G} (γ : Path a b) (hγ : ∀ t, γ t ∈ u)
    {γ' : Path (f a) (f b)} (hγ' : ∀ t, γ' t = f (γ t)) :
    localPotentialIntegral (fun x ↦ (φ (f x)).comp (fderiv ℝ f x)) γ =
      localPotentialIntegral φ γ' := by
  have hγ's : ∀ t, γ' t ∈ s := fun t ↦ hγ' t ▸ hfs (hγ t)
  obtain ⟨S⟩ := hφ.nonempty_potentialSubdivision γ' hγ's
  choose w hw_open hw_eq using fun k : Fin S.n ↦
    continuousOn_iff'.mp hf.continuousOn (S.u k) (S.hu k)
  have hmaps_w (k : Fin S.n) : MapsTo γ (Icc (S.t k) (S.t (k + 1))) (w k ∩ u) := by
    intro x hx
    rw [← hw_eq k]
    exact ⟨by simpa [← hγ' x] using S.hγ k hx, hγ x⟩
  have hderiv_w (k : Fin S.n) :
      ∀ x ∈ w k ∩ u, HasFDerivAt (S.g k ∘ f) ((φ (f x)).comp (fderiv ℝ f x)) x := by
    intro x hx
    rw [← hw_eq k] at hx
    exact (S.hg k (f x) hx.1).comp x
      ((hf.differentiableOn one_ne_zero x hx.2).differentiableAt (hu.mem_nhds hx.2)).hasFDerivAt
  rw [localPotentialIntegral_eq_sum_sub S.ht_mono S.ht0 S.htn
        (u := fun k ↦ w k ∩ u) (fun k ↦ (hw_open k).inter hu) hmaps_w
        (g := fun k ↦ S.g k ∘ f) hderiv_w,
      localPotentialIntegral_eq_sum_sub S.ht_mono S.ht0 S.htn S.hu S.hγ S.hg]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  simp [Function.comp_apply, hγ']

/-- Pullback formula for `localPotentialIntegral` along a globally `C¹` map using `Path.map`. -/
theorem HasLocalPotentials.localPotentialIntegral_map {f : G → E}
    (hφ : HasLocalPotentials s φ) (hf : ContDiff ℝ 1 f)
    {a b : G} (γ : Path a b) (hγ : ∀ t, f (γ t) ∈ s) :
    localPotentialIntegral (fun x ↦ (φ (f x)).comp (fderiv ℝ f x)) γ =
      localPotentialIntegral φ (γ.map hf.continuous) := by
  let u : Set G := f ⁻¹' s
  have hu : IsOpen u := hφ.isOpen.preimage hf.continuous
  exact hφ.localPotentialIntegral_pullback hu hf.contDiffOn (mapsTo_preimage f s) γ hγ (fun _ ↦ rfl)

/-- Boundary relation for `localPotentialIntegral` on a continuous free homotopy square
`H : (γ₀ : C(I, E)).Homotopy γ₁` in `s`: the sum along the bottom and right edges equals the sum
along the left and top edges. -/
theorem HasLocalPotentials.localPotentialIntegral_add_eq_of_homotopy
    (hφ : HasLocalPotentials s φ) {a₀ b₀ a₁ b₁ : E} {γ₀ : Path a₀ b₀} {γ₁ : Path a₁ b₁}
    (H : (γ₀ : C(I, E)).Homotopy γ₁) (hH : ∀ p, H p ∈ s) :
    localPotentialIntegral φ γ₀ + localPotentialIntegral φ (H.evalAt 1) =
      localPotentialIntegral φ (H.evalAt 0) + localPotentialIntegral φ γ₁ := by
  classical
  choose R hRpos _ G _ hGderiv using fun q : s ↦ hasLocalPotentials_iff.mp hφ q.1 q.2
  obtain ⟨t, ht0, ht_mono, ⟨n, htn⟩, hsub⟩ :=
    exists_monotone_Icc_subset_open_cover_unitInterval_prod_self
      (c := fun q : s ↦ H ⁻¹' ball q.1 (R q))
      (fun q ↦ isOpen_ball.preimage H.continuous)
      (fun p _ ↦ mem_iUnion.mpr ⟨⟨H p, hH p⟩, mem_ball_self (hRpos ⟨H p, hH p⟩)⟩)
  have htn_eq : t n = 1 := htn n le_rfl
  choose idx hidx using fun i j : Fin n ↦ hsub i j
  let B (i j : Fin n) : Set E := ball (idx i j).1 (R (idx i j))
  let g (i j : Fin n) : E → F := G (idx i j)
  -- Pick a non-degenerate index witness: `0 ≠ 1` in `I`, so `n` cannot be `0`.
  have hn_pos : 0 < n := by
    by_contra h0
    have hn0 : n = 0 := Nat.eq_zero_of_not_pos h0
    subst hn0
    exact zero_ne_one (ht0.symm.trans htn_eq)
  let zeroFin : Fin n := ⟨0, hn_pos⟩
  let lastFin : Fin n := ⟨n - 1, Nat.sub_lt hn_pos zero_lt_one⟩
  have hlast_succ : (lastFin : ℕ) + 1 = n := Nat.sub_add_cancel hn_pos
  have h0_mem : (0 : I) ∈ Icc (t zeroFin) (t ((zeroFin : ℕ) + 1)) := by
    refine ⟨?_, ?_⟩
    · change t 0 ≤ 0; rw [ht0]
    · exact Subtype.coe_le_coe.mp (unitInterval.nonneg _)
  have h1_mem : (1 : I) ∈ Icc (t lastFin) (t ((lastFin : ℕ) + 1)) := by
    rw [hlast_succ, htn_eq]
    exact ⟨unitInterval.le_one _, le_rfl⟩
  -- Evaluate the four boundary path integrals on the partition `t`.
  have hγ₀_eq : localPotentialIntegral φ γ₀ =
      ∑ j : Fin n, (g zeroFin j (H (0, t (j + 1))) - g zeroFin j (H (0, t j))) := by
    have hmaps (j : Fin n) : MapsTo γ₀ (Icc (t j) (t (j + 1))) (B zeroFin j) := by
      intro y hy
      have := hidx zeroFin j (mk_mem_prod h0_mem hy)
      simpa [B] using this
    rw [localPotentialIntegral_eq_sum_sub ht_mono ht0 htn_eq (fun _ ↦ isOpen_ball) hmaps
      (fun j ↦ hGderiv (idx zeroFin j))]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    simp [g]
  have hγ₁_eq : localPotentialIntegral φ γ₁ =
      ∑ j : Fin n, (g lastFin j (H (1, t (j + 1))) - g lastFin j (H (1, t j))) := by
    have hmaps (j : Fin n) : MapsTo γ₁ (Icc (t j) (t (j + 1))) (B lastFin j) := by
      intro y hy
      have := hidx lastFin j (mk_mem_prod h1_mem hy)
      simpa [B] using this
    rw [localPotentialIntegral_eq_sum_sub ht_mono ht0 htn_eq (fun _ ↦ isOpen_ball) hmaps
      (fun j ↦ hGderiv (idx lastFin j))]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    simp [g]
  have hleft_eq : localPotentialIntegral φ (H.evalAt 0) =
      ∑ i : Fin n, (g i zeroFin (H (t (i + 1), 0)) - g i zeroFin (H (t i, 0))) := by
    have hmaps (i : Fin n) : MapsTo (H.evalAt 0) (Icc (t i) (t (i + 1))) (B i zeroFin) :=
      fun _ hx ↦ hidx i zeroFin (mk_mem_prod hx h0_mem)
    exact localPotentialIntegral_eq_sum_sub ht_mono ht0 htn_eq (fun _ ↦ isOpen_ball) hmaps
      (fun i ↦ hGderiv (idx i zeroFin))
  have hright_eq : localPotentialIntegral φ (H.evalAt 1) =
      ∑ i : Fin n, (g i lastFin (H (t (i + 1), 1)) - g i lastFin (H (t i, 1))) := by
    have hmaps (i : Fin n) : MapsTo (H.evalAt 1) (Icc (t i) (t (i + 1))) (B i lastFin) :=
      fun _ hx ↦ hidx i lastFin (mk_mem_prod hx h1_mem)
    exact localPotentialIntegral_eq_sum_sub ht_mono ht0 htn_eq (fun _ ↦ isOpen_ball) hmaps
      (fun i ↦ hGderiv (idx i lastFin))
  -- Preconnectedness helper for horizontal and vertical grid edges.
  have hIcc_preconn (a b : I) : IsPreconnected (Icc a b) := by
    have heq : Subtype.val '' (Icc a b : Set I) = Icc (a : ℝ) (b : ℝ) := by
      ext x
      constructor
      · rintro ⟨y, ⟨hy1, hy2⟩, rfl⟩; exact ⟨hy1, hy2⟩
      · rintro ⟨hx1, hx2⟩
        exact ⟨⟨x, (unitInterval.nonneg a).trans hx1, hx2.trans (unitInterval.le_one b)⟩,
          ⟨hx1, hx2⟩, rfl⟩
    exact Topology.IsInducing.subtypeVal.isPreconnected_image.mp (heq ▸ isPreconnected_Icc)
  -- Shared horizontal interior edge between row `i` and row `i'` when `(i : ℕ) + 1 = i'`.
  have hhoriz (i i' : Fin n) (hi : (i : ℕ) + 1 = i') (j : Fin n) :
      g i j (H (t (i + 1), t (j + 1))) - g i j (H (t (i + 1), t j)) =
        g i' j (H (t i', t (j + 1))) - g i' j (H (t i', t j)) := by
    have hj_le : t j ≤ t (j + 1) := ht_mono (Nat.le_succ _)
    let edge : Set E := (fun y : I ↦ H (t (i + 1), y)) '' Icc (t j) (t (j + 1))
    have hedge_pre : IsPreconnected edge :=
      (hIcc_preconn _ _).image _
        (H.continuous.comp (continuous_const.prodMk continuous_id)).continuousOn
    have hsub_i : edge ⊆ B i j := by
      rintro _ ⟨y, hy, rfl⟩
      exact hidx i j ⟨⟨ht_mono (Nat.le_succ _), le_rfl⟩, hy⟩
    have hsub_i' : edge ⊆ B i' j := by
      rintro _ ⟨y, hy, rfl⟩
      rw [hi]
      exact hidx i' j ⟨⟨le_rfl, ht_mono (Nat.le_succ _)⟩, hy⟩
    have heq := sub_eq_sub_of_hasFDerivAt_of_isPreconnected isOpen_ball isOpen_ball hedge_pre
      hsub_i hsub_i' (hGderiv (idx i j)) (hGderiv (idx i' j))
      (mem_image_of_mem (fun y : I ↦ H (t (i + 1), y)) ⟨le_rfl, hj_le⟩)
      (mem_image_of_mem (fun y : I ↦ H (t (i + 1), y)) ⟨hj_le, le_rfl⟩)
    simpa [hi] using heq
  -- Shared vertical interior edge between column `j` and column `j'` when `(j : ℕ) + 1 = j'`.
  have hvert (i : Fin n) (j j' : Fin n) (hj : (j : ℕ) + 1 = j') :
      g i j (H (t (i + 1), t (j + 1))) - g i j (H (t i, t (j + 1))) =
        g i j' (H (t (i + 1), t j')) - g i j' (H (t i, t j')) := by
    have hi_le : t i ≤ t (i + 1) := ht_mono (Nat.le_succ _)
    let edge : Set E := (fun x : I ↦ H (x, t (j + 1))) '' Icc (t i) (t (i + 1))
    have hedge_pre : IsPreconnected edge :=
      (hIcc_preconn _ _).image _
        (H.continuous.comp (continuous_id.prodMk continuous_const)).continuousOn
    have hsub_j : edge ⊆ B i j := by
      rintro _ ⟨x, hx, rfl⟩
      exact hidx i j ⟨hx, ⟨ht_mono (Nat.le_succ _), le_rfl⟩⟩
    have hsub_j' : edge ⊆ B i j' := by
      rintro _ ⟨x, hx, rfl⟩
      rw [hj]
      exact hidx i j' ⟨hx, ⟨le_rfl, ht_mono (Nat.le_succ _)⟩⟩
    have heq := sub_eq_sub_of_hasFDerivAt_of_isPreconnected isOpen_ball isOpen_ball hedge_pre
      hsub_j hsub_j' (hGderiv (idx i j)) (hGderiv (idx i j'))
      (mem_image_of_mem (fun x : I ↦ H (x, t (j + 1))) ⟨le_rfl, hi_le⟩)
      (mem_image_of_mem (fun x : I ↦ H (x, t (j + 1))) ⟨hi_le, le_rfl⟩)
    simpa [hj] using heq
  -- Define canonical horizontal and vertical edge increments indexed by `0 ≤ k ≤ n`.
  let H_edge (k : ℕ) (j : Fin n) : F :=
    if hk : k < n then g ⟨k, hk⟩ j (H (t k, t (j + 1))) - g ⟨k, hk⟩ j (H (t k, t j))
    else g lastFin j (H (t k, t (j + 1))) - g lastFin j (H (t k, t j))
  let V_edge (i : Fin n) (k : ℕ) : F :=
    if hk : k < n then g i ⟨k, hk⟩ (H (t (i + 1), t k)) - g i ⟨k, hk⟩ (H (t i, t k))
    else g i lastFin (H (t (i + 1), t k)) - g i lastFin (H (t i, t k))
  have hH_succ (i : Fin n) (j : Fin n) :
      H_edge (i + 1) j = g i j (H (t (i + 1), t (j + 1))) - g i j (H (t (i + 1), t j)) := by
    dsimp [H_edge]
    split_ifs with hk
    · exact (hhoriz i ⟨i + 1, hk⟩ rfl j).symm
    · have hi_last : i = lastFin := by ext; simp [lastFin]; omega
      subst hi_last; rfl
  have hV_succ (i : Fin n) (j : Fin n) :
      V_edge i (j + 1) = g i j (H (t (i + 1), t (j + 1))) - g i j (H (t i, t (j + 1))) := by
    dsimp [V_edge]
    split_ifs with hk
    · exact (hvert i j ⟨j + 1, hk⟩ rfl).symm
    · have hj_last : j = lastFin := by ext; simp [lastFin]; omega
      subst hj_last; rfl
  have hcell_zero (i j : Fin n) :
      (H_edge (i + 1) j - H_edge i j) = (V_edge i (j + 1) - V_edge i j) := by
    have hH_curr : H_edge i j = g i j (H (t i, t (j + 1))) - g i j (H (t i, t j)) := by
      simp [H_edge, i.2]
    have hV_curr : V_edge i j = g i j (H (t (i + 1), t j)) - g i j (H (t i, t j)) := by
      simp [V_edge, j.2]
    rw [hH_succ, hH_curr, hV_succ, hV_curr]
    abel
  have hsum_H :
      (∑ j : Fin n, (H_edge n j - H_edge 0 j)) =
        localPotentialIntegral φ γ₁ - localPotentialIntegral φ γ₀ := by
    rw [hγ₁_eq, hγ₀_eq, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    simp [H_edge, hn_pos, zeroFin, htn_eq, ht0]
  have hsum_V :
      (∑ i : Fin n, (V_edge i n - V_edge i 0)) =
        localPotentialIntegral φ (H.evalAt 1) - localPotentialIntegral φ (H.evalAt 0) := by
    rw [hright_eq, hleft_eq, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    simp [V_edge, hn_pos, zeroFin, htn_eq, ht0]
  have hdouble :
      (∑ j : Fin n, (H_edge n j - H_edge 0 j)) =
        ∑ i : Fin n, (V_edge i n - V_edge i 0) := by
    calc
      ∑ j : Fin n, (H_edge n j - H_edge 0 j)
        = ∑ j : Fin n, ∑ i : Fin n, (H_edge (i + 1) j - H_edge i j) := by
            refine Finset.sum_congr rfl fun j _ ↦ (sum_fin_sub (fun i ↦ H_edge i j)).symm
      _ = ∑ i : Fin n, ∑ j : Fin n, (H_edge (i + 1) j - H_edge i j) := Finset.sum_comm
      _ = ∑ i : Fin n, ∑ j : Fin n, (V_edge i (j + 1) - V_edge i j) := by
            refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ hcell_zero i j
      _ = ∑ i : Fin n, (V_edge i n - V_edge i 0) := by
            refine Finset.sum_congr rfl fun i _ ↦ sum_fin_sub (fun j ↦ V_edge i j)
  calc
    localPotentialIntegral φ γ₀ + localPotentialIntegral φ (H.evalAt 1)
      = localPotentialIntegral φ γ₀ +
          (localPotentialIntegral φ (H.evalAt 1) - localPotentialIntegral φ (H.evalAt 0)) +
          localPotentialIntegral φ (H.evalAt 0) := by abel
    _ = localPotentialIntegral φ γ₀ +
          (localPotentialIntegral φ γ₁ - localPotentialIntegral φ γ₀) +
          localPotentialIntegral φ (H.evalAt 0) := by rw [← hsum_V, ← hdouble, hsum_H]
    _ = localPotentialIntegral φ (H.evalAt 0) + localPotentialIntegral φ γ₁ := by abel

/-- Homotopy invariance of `localPotentialIntegral` relative to endpoints: two paths connected by a
`Path.Homotopy` in `s` have the same `localPotentialIntegral`. -/
theorem HasLocalPotentials.localPotentialIntegral_eq_of_homotopy
    (hφ : HasLocalPotentials s φ) {a b : E} {γ₀ γ₁ : Path a b}
    (F : Path.Homotopy γ₀ γ₁) (hF : ∀ p, F p ∈ s) :
    localPotentialIntegral φ γ₀ = localPotentialIntegral φ γ₁ := by
  have hrel := hφ.localPotentialIntegral_add_eq_of_homotopy F.toHomotopy hF
  have heval0 : F.toHomotopy.evalAt 0 = (Path.refl a).cast γ₀.source γ₁.source := by
    ext t; exact F.source t
  have heval1 : F.toHomotopy.evalAt 1 = (Path.refl b).cast γ₀.target γ₁.target := by
    ext t; exact F.target t
  simpa [heval0, heval1] using hrel

/-- Two homotopic paths in the subtype `s` push forward to paths in `E` with the same
`localPotentialIntegral`. -/
theorem HasLocalPotentials.localPotentialIntegral_eq_of_homotopic
    (hφ : HasLocalPotentials s φ) {x y : s} {p₀ p₁ : Path x y}
    (hp : Path.Homotopic p₀ p₁) :
    localPotentialIntegral φ (p₀.map continuous_subtype_val) =
      localPotentialIntegral φ (p₁.map continuous_subtype_val) := by
  obtain ⟨F⟩ := hp
  let F' : Path.Homotopy (p₀.map continuous_subtype_val) (p₁.map continuous_subtype_val) :=
    F.map ⟨Subtype.val, continuous_subtype_val⟩
  exact hφ.localPotentialIntegral_eq_of_homotopy F' fun p ↦ (F p).2

/-- Endpoint-preserving continuous reparametrization of a path in `s` preserves
`localPotentialIntegral`. -/
theorem HasLocalPotentials.localPotentialIntegral_reparam
    (hφ : HasLocalPotentials s φ) {a b : E} (γ : Path a b) (hγ : ∀ t, γ t ∈ s)
    (f : I → I) (hf : Continuous f) (hf₀ : f 0 = 0) (hf₁ : f 1 = 1) :
    localPotentialIntegral φ (γ.reparam f hf hf₀ hf₁) = localPotentialIntegral φ γ :=
  (hφ.localPotentialIntegral_eq_of_homotopy (Path.Homotopy.reparam γ f hf hf₀ hf₁)
    fun _ ↦ hγ _).symm

end TauCeti
