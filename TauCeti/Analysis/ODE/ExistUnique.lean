/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Zhiyuan Zhang, Leheng Chen, The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.ODE.ExistUnique
public import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Topology.Order.IntermediateValue
import TauCeti.Analysis.ODE.Gronwall.TwoSided

/-!
# ODE uniqueness on relative neighborhoods and subsets

Two solutions of a locally Lipschitz vector field with a common value agree near that time
within an order-connected parameter set. Derivatives are taken within the parameter set,
so the initial time may be a closed endpoint. No completeness of the phase space is needed.
A C¹ vector field supplies the local Lipschitz hypothesis; equality then extends throughout
any preconnected real parameter set.

For an autonomous field `X` that is locally Lipschitz only on a subset `S` containing two
trajectories (without an ambient neighborhood Lipschitz bound), compactness of `[a, c]` yields a
single Lipschitz constant along their joint image, giving forward uniqueness on `[a, b]` and
`[a, b)`. Two autonomous integral curves on half-open intervals can also be concatenated at a
matching time.

## Main results

* `TauCeti.ODE_solution_unique_of_eventually_nhdsWithin`: local uniqueness with a uniform
  state-space Lipschitz constant on a neighborhood of the common phase.
* `ContDiffAt.ode_eventuallyEq_nhdsWithin`: C¹ local uniqueness.
* `IsPreconnected.ode_eqOn`: locally Lipschitz uniqueness on a preconnected parameter set.
* `IsPreconnected.ode_eqOn_of_contDiffAt`: the C¹ specialization.
* `LocallyLipschitzOn.eqOn_Icc_of_hasDerivWithinAt_Ici`,
  `LocallyLipschitzOn.eqOn_Ico_of_hasDerivWithinAt_Ico`: forward uniqueness on `[a, b]` and
  `[a, b)` for autonomous fields locally Lipschitz on a subset `S`.
* `TauCeti.hasDerivWithinAt_ite_Ico`: concatenation of an integral curve on `[a, b₁)` with a
  translated integral curve on `[0, b₂)` into an integral curve on `[a, s + b₂)`.

## References

* `Mathlib.Analysis.ODE.ExistUnique` for local Lipschitz uniqueness.
* J. Morgan and G. Tian, *Ricci Flow and the Poincaré Conjecture*, Lemmas 6.8 and 6.10:
  closed-endpoint ODE uniqueness is an analytic input to reduced-geodesic and variation
  uniqueness there.
* Public formalizations: [lean-eval-submissions](https://github.com/frenzymath/lean-eval-submissions)
  and [PoincareConjecture](https://github.com/frenzymath/PoincareConjecture).
-/

public section

open Filter Topology
open scoped NNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {V : ℝ × E → E} {I : Set ℝ} {f g : ℝ → E} {t0 : ℝ}

/-- Local uniqueness within an order-connected parameter set, with derivatives within that
set. The Lipschitz bound is uniform in time but only compares states in each time slice. -/
theorem TauCeti.ODE_solution_unique_of_eventually_nhdsWithin {K : ℝ≥0} {s : Set (ℝ × E)}
    (hs : s ∈ 𝓝 (t0, f t0))
    (hv : ∀ t, LipschitzOnWith K (fun x ↦ V (t, x)) {x | (t, x) ∈ s})
    (hI : Set.OrdConnected I) (ht0 : t0 ∈ I) (heq : f t0 = g t0)
    (hf : ∀ᶠ t in 𝓝[I] t0, HasDerivWithinAt f (V (t, f t)) I t)
    (hg : ∀ᶠ t in 𝓝[I] t0, HasDerivWithinAt g (V (t, g t)) I t) :
    f =ᶠ[𝓝[I] t0] g := by
  have hfc := (hf.self_of_nhdsWithin ht0).continuousWithinAt
  have hgc := (hg.self_of_nhdsWithin ht0).continuousWithinAt
  have hfQ : ∀ᶠ t in 𝓝[I] t0, (t, f t) ∈ s :=
    (continuousWithinAt_id.prodMk hfc).preimage_mem_nhdsWithin hs
  have hgQ : ∀ᶠ t in 𝓝[I] t0, (t, g t) ∈ s := by
    apply (continuousWithinAt_id.prodMk hgc).preimage_mem_nhdsWithin
    simpa only [heq, Function.id_def] using hs
  obtain ⟨ε, hε, hdata⟩ := Metric.mem_nhdsWithin_iff.mp (hf.and (hg.and (hfQ.and hgQ)))
  filter_upwards [nhdsWithin_le_nhds (Metric.ball_mem_nhds t0 hε),
    self_mem_nhdsWithin] with t ht htI
  have hsub : Set.uIcc t0 t ⊆ Metric.ball t0 ε ∩ I :=
    ((convex_ball t0 ε).ordConnected.inter hI).uIcc_subset
      ⟨Metric.mem_ball_self hε, ht0⟩ ⟨ht, htI⟩
  have hd := fun r (hr : r ∈ Set.uIcc t0 t) ↦ hdata (hsub hr)
  have hderiv : ∀ r ∈ Set.uIcc t0 t,
      HasDerivWithinAt (fun u ↦ f u - g u) (V (r, f r) - V (r, g r)) (Set.uIcc t0 t) r :=
    fun r hr ↦ ((hd r hr).1.sub (hd r hr).2.1).mono fun _ hx ↦ (hsub hx).2
  have hbound : ∀ r ∈ Set.uIcc t0 t,
      ‖V (r, f r) - V (r, g r)‖ ≤ K * ‖f r - g r‖ + 0 := by
    intro r hr
    simpa only [dist_eq_norm, add_zero] using
      (hv r).dist_le_mul _ (hd r hr).2.2.1 _ (hd r hr).2.2.2
  have hnorm := TauCeti.norm_le_gronwallBound_of_norm_derivWithin_le
    Set.left_mem_uIcc hderiv (δ := 0) (by simp only [heq, sub_self, norm_zero, le_refl])
    hbound t Set.right_mem_uIcc
  simpa only [gronwallBound_ε0_δ0, norm_le_zero_iff, sub_eq_zero] using hnorm

/-- Solutions of a C¹ vector field with the same value have the same relative germ,
including at a closed endpoint of the parameter set. Only smoothness at the common phase
is required. -/
theorem ContDiffAt.ode_eventuallyEq_nhdsWithin
    (hV : ContDiffAt ℝ 1 V (t0, f t0)) (hI : Set.OrdConnected I)
    (ht0 : t0 ∈ I) (heq : f t0 = g t0)
    (hf : ∀ᶠ t in 𝓝[I] t0, HasDerivWithinAt f (V (t, f t)) I t)
    (hg : ∀ᶠ t in 𝓝[I] t0, HasDerivWithinAt g (V (t, g t)) I t) :
    f =ᶠ[𝓝[I] t0] g := by
  obtain ⟨K, s, hs, hL⟩ := hV.exists_lipschitzOnWith
  have hLip : ∀ t, LipschitzOnWith K (fun x ↦ V (t, x)) {x | (t, x) ∈ s} := by
    intro t x hx y hy
    simpa only [Prod.edist_eq, edist_self, zero_max] using hL hx hy
  exact TauCeti.ODE_solution_unique_of_eventually_nhdsWithin hs hLip hI ht0 heq hf hg

/-- Two solutions agree throughout a preconnected parameter set if they agree once and
the field has a uniform state-space Lipschitz bound near each phase of the first solution.
The neighborhood and Lipschitz constant may depend on the phase. -/
theorem IsPreconnected.ode_eqOn (hI : IsPreconnected I)
    (hV : ∀ t ∈ I, ∃ (K : ℝ≥0) (s : Set (ℝ × E)), s ∈ 𝓝 (t, f t) ∧
      ∀ r, LipschitzOnWith K (fun x ↦ V (r, x)) {x | (r, x) ∈ s})
    (ht0 : t0 ∈ I) (heq : f t0 = g t0)
    (hf : ∀ t ∈ I, HasDerivWithinAt f (V (t, f t)) I t)
    (hg : ∀ t ∈ I, HasDerivWithinAt g (V (t, g t)) I t) : Set.EqOn f g I := by
  have hfc : ContinuousOn f I := fun t ht ↦ (hf t ht).continuousWithinAt
  have hgc : ContinuousOn g I := fun t ht ↦ (hg t ht).continuousWithinAt
  let : PreconnectedSpace I := isPreconnected_iff_preconnectedSpace.mp hI
  let A : Set I := {t | f t = g t}
  have hclosed : IsClosed A := isClosed_eq hfc.domRestrict hgc.domRestrict
  have hopen : IsOpen A := by
    apply isOpen_iff_mem_nhds.mpr
    intro t ht
    obtain ⟨K, s, hs, hLip⟩ := hV t t.property
    have hlocal := TauCeti.ODE_solution_unique_of_eventually_nhdsWithin hs hLip hI.ordConnected
      t.property ht (eventually_nhdsWithin_of_forall hf) (eventually_nhdsWithin_of_forall hg)
    exact (eventually_nhds_subtype_iff I t (fun r ↦ f r = g r)).mpr hlocal
  have hAll : A = Set.univ := IsClopen.eq_univ ⟨hclosed, hopen⟩ ⟨⟨t0, ht0⟩, heq⟩
  intro t ht
  have hm : (⟨t, ht⟩ : I) ∈ A := by rw [hAll]; trivial
  exact hm

/-- Two solutions of a vector field that is C¹ along the first solution agree on a
preconnected parameter set if they have one common value, even at a closed endpoint. -/
theorem IsPreconnected.ode_eqOn_of_contDiffAt (hI : IsPreconnected I)
    (hV : ∀ t ∈ I, ContDiffAt ℝ 1 V (t, f t))
    (ht0 : t0 ∈ I) (heq : f t0 = g t0)
    (hf : ∀ t ∈ I, HasDerivWithinAt f (V (t, f t)) I t)
    (hg : ∀ t ∈ I, HasDerivWithinAt g (V (t, g t)) I t) : Set.EqOn f g I := by
  apply hI.ode_eqOn (fun t ht ↦ ?_) ht0 heq hf hg
  obtain ⟨K, s, hs, hL⟩ := (hV t ht).exists_lipschitzOnWith
  refine ⟨K, s, hs, fun r x hx y hy ↦ ?_⟩
  simpa only [Prod.edist_eq, edist_self, zero_max] using hL hx hy

namespace LocallyLipschitzOn

open ODE Set

/-- **Forward uniqueness on `[a, b]`.** If `X` is locally Lipschitz on `S`, any two continuous
curves on `[a, b]` mapping `[a, b)` into `S` with right derivative `X (γ t)` on `[a, b)` and the
same value at `a` agree on `[a, b]`. -/
theorem eqOn_Icc_of_hasDerivWithinAt_Ici {S : Set E} {X : E → E} (hX : LocallyLipschitzOn S X)
    {a b : ℝ}
    (hf : ContinuousOn f (Icc a b))
    (hf' : ∀ t ∈ Ico a b, HasDerivWithinAt f (X (f t)) (Ici t) t)
    (hf_mem : MapsTo f (Ico a b) S)
    (hg : ContinuousOn g (Icc a b))
    (hg' : ∀ t ∈ Ico a b, HasDerivWithinAt g (X (g t)) (Ici t) t)
    (hg_mem : MapsTo g (Ico a b) S)
    (ha : f a = g a) :
    EqOn f g (Icc a b) := by
  have hIco : EqOn f g (Ico a b) := fun c hc ↦ by
    have hsub : Icc a c ⊆ Ico a b := fun t ht ↦ ⟨ht.1, ht.2.trans_lt hc.2⟩
    let Kset := f '' Icc a c ∪ g '' Icc a c
    have hKcomp : IsCompact Kset :=
      (isCompact_Icc.image_of_continuousOn (hf.mono (hsub.trans Ico_subset_Icc_self))).union
        (isCompact_Icc.image_of_continuousOn (hg.mono (hsub.trans Ico_subset_Icc_self)))
    have hKsub : Kset ⊆ S := union_subset (image_subset_iff.mpr fun t ht ↦ hf_mem (hsub ht))
      (image_subset_iff.mpr fun t ht ↦ hg_mem (hsub ht))
    obtain ⟨K, hKLip⟩ := (hX.mono hKsub).exists_lipschitzOnWith_of_compact hKcomp
    exact ODE_solution_unique_of_mem_Icc_right (v := fun _ ↦ X) (s := fun _ ↦ Kset)
      (fun _ _ ↦ hKLip) (hf.mono (hsub.trans Ico_subset_Icc_self))
      (fun t ht ↦ hf' t (hsub (Ico_subset_Icc_self ht)))
      (fun t ht ↦ Or.inl (mem_image_of_mem f (Ico_subset_Icc_self ht)))
      (hg.mono (hsub.trans Ico_subset_Icc_self))
      (fun t ht ↦ hg' t (hsub (Ico_subset_Icc_self ht)))
      (fun t ht ↦ Or.inr (mem_image_of_mem g (Ico_subset_Icc_self ht))) ha ⟨hc.1, le_rfl⟩
  rcases lt_or_ge a b with hab | hba
  · exact hIco.of_subset_closure hf hg Ico_subset_Icc_self (closure_Ico hab.ne ▸ Subset.rfl)
  · intro t ht
    obtain rfl : a = b := le_antisymm (ht.1.trans ht.2) hba
    simpa [le_antisymm ht.1 ht.2] using ha

/-- **Forward uniqueness on `[a, b)`.** Two curves on `[a, b)` mapping into `S`, solving
`γ' = X ∘ γ` within `[a, b)` for a locally Lipschitz field `X` on `S`, and agreeing at `a` agree on
`[a, b)`. -/
theorem eqOn_Ico_of_hasDerivWithinAt_Ico {S : Set E} {X : E → E} (hX : LocallyLipschitzOn S X)
    {a b : ℝ}
    (hf' : ∀ t ∈ Ico a b, HasDerivWithinAt f (X (f t)) (Ico a b) t)
    (hf_mem : MapsTo f (Ico a b) S)
    (hg' : ∀ t ∈ Ico a b, HasDerivWithinAt g (X (g t)) (Ico a b) t)
    (hg_mem : MapsTo g (Ico a b) S)
    (ha : f a = g a) :
    EqOn f g (Ico a b) := fun c hc ↦ by
  have hsub : Icc a c ⊆ Ico a b := fun t ht ↦ ⟨ht.1, ht.2.trans_lt hc.2⟩
  have hIci {γ : ℝ → E} (h : ∀ t ∈ Ico a b, HasDerivWithinAt γ (X (γ t)) (Ico a b) t) :
      ∀ t ∈ Ico a c, HasDerivWithinAt γ (X (γ t)) (Ici t) t := fun t ht ↦
    (h t (hsub (Ico_subset_Icc_self ht))).mono_of_mem_nhdsWithin <| mem_nhdsWithin.mpr
      ⟨Iio b, isOpen_Iio, ht.2.trans hc.2, fun _ hs ↦ ⟨ht.1.trans hs.2, hs.1⟩⟩
  exact hX.eqOn_Icc_of_hasDerivWithinAt_Ici
    (fun t ht ↦ ((hf' t (hsub ht)).continuousWithinAt).mono hsub)
    (hIci hf') (fun t ht ↦ hf_mem (hsub (Ico_subset_Icc_self ht)))
    (fun t ht ↦ ((hg' t (hsub ht)).continuousWithinAt).mono hsub)
    (hIci hg') (fun t ht ↦ hg_mem (hsub (Ico_subset_Icc_self ht))) ha ⟨hc.1, le_rfl⟩

end LocallyLipschitzOn

open Set in
/-- Concatenating an integral curve `γ₁` of `X` on `[a, b₁)` (`a ≤ s < b₁`) with an integral
curve `γ₂` of `X` on `[0, b₂)` (`0 < b₂`) starting at `γ₂ 0 = γ₁ s` yields an integral curve of
`X` on `[a, s + b₂)`. -/
theorem TauCeti.hasDerivWithinAt_ite_Ico (X : E → E) {γ₁ γ₂ : ℝ → E} {a s b₁ b₂ u : ℝ}
    (has : a ≤ s) (hsb₁ : s < b₁) (hb₂ : 0 < b₂) (h0₂ : γ₂ 0 = γ₁ s)
    (hγ₁' : ∀ t ∈ Ico a b₁, HasDerivWithinAt γ₁ (X (γ₁ t)) (Ico a b₁) t)
    (hγ₂' : ∀ t ∈ Ico 0 b₂, HasDerivWithinAt γ₂ (X (γ₂ t)) (Ico 0 b₂) t)
    (hu : u ∈ Ico a (s + b₂)) :
    HasDerivWithinAt (fun r ↦ if r ≤ s then γ₁ r else γ₂ (r - s))
      (X ((fun r ↦ if r ≤ s then γ₁ r else γ₂ (r - s)) u)) (Ico a (s + b₂)) u := by
  set γ : ℝ → E := fun r ↦ if r ≤ s then γ₁ r else γ₂ (r - s)
  rcases lt_trichotomy u s with hus | rfl | hsu
  · have hγu : γ u = γ₁ u := ite_eq_left hus.le
    have hd := (hγ₁' u ⟨hu.1, hus.trans hsb₁⟩).mono_of_mem_nhdsWithin (s := Ico a (s + b₂))
      (mem_nhdsWithin.mpr ⟨Iio s, isOpen_Iio, hus, fun _ hr ↦ ⟨hr.2.1, hr.1.trans hsb₁⟩⟩)
    exact (hγu ▸ hd).congr_of_eventuallyEq
      (Filter.mem_of_superset (nhdsWithin_le_nhds (Iio_mem_nhds hus))
        fun _ hr ↦ ite_eq_left (mem_Iio.mp hr).le) hγu
  · have hγs : γ u = γ₁ u := ite_eq_left le_rfl
    have hleft : HasDerivWithinAt γ (X (γ u)) (Icc a u) u :=
      (hγs ▸ (hγ₁' u ⟨has, hsb₁⟩).mono (s := Icc a u)
        (fun _ hr ↦ ⟨hr.1, hr.2.trans_lt hsb₁⟩)).congr (fun _ hr ↦ ite_eq_left hr.2) hγs
    have hright : HasDerivWithinAt γ (X (γ u)) (Ico u (u + b₂)) u := by
      have hd₂ := HasDerivWithinAt.scomp_of_eq (s := Ico u (u + b₂)) u
        (hγ₂' 0 ⟨le_rfl, hb₂⟩) ((hasDerivAt_id u).sub_const u).hasDerivWithinAt
        (fun _ hr ↦ ⟨sub_nonneg.mpr hr.1, sub_lt_iff_lt_add'.mpr hr.2⟩) (sub_self u).symm
      simp only [Function.comp_def, id_eq, h0₂, one_smul, ← hγs] at hd₂
      refine hd₂.congr (fun r hr ↦ ?_) (by simp [γ, h0₂])
      rcases hr.1.eq_or_lt with rfl | hsr
      · simp [γ, h0₂]
      · exact ite_eq_right (not_le_of_gt hsr)
    have hboth : HasDerivWithinAt γ (X (γ u)) (Icc a u ∪ Ico u (u + b₂)) u :=
      hleft.union hright
    rwa [Icc_union_Ico_eq_Ico has (lt_add_of_pos_right u hb₂)] at hboth
  · have hγu : γ u = γ₂ (u - s) := ite_eq_right (not_le_of_gt hsu)
    have hd₂ := ((hγ₂' (u - s) ⟨by linarith, by linarith [hu.2]⟩).hasDerivAt
      (Ico_mem_nhds (by linarith) (by linarith [hu.2]))).comp_sub_const u s
    exact (hγu ▸ hd₂.hasDerivWithinAt).congr_of_eventuallyEq
      (Filter.mem_of_superset (nhdsWithin_le_nhds (Ioi_mem_nhds hsu))
        fun _ hr ↦ ite_eq_right (not_le_of_gt (mem_Ioi.mp hr))) hγu
