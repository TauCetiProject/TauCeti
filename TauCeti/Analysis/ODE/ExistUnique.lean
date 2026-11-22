/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Zhiyuan Zhang, Leheng Chen, The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.ODE.ExistUnique
public import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Topology.Order.IntermediateValue
import TauCeti.Analysis.ODE.Gronwall.Interior

/-!
# ODE uniqueness on relative neighborhoods and subsets

Two solutions of a locally Lipschitz vector field with a common value agree near that time
within an order-connected parameter set. Derivatives are taken within the parameter set,
so the initial time may be a closed endpoint. No completeness of the phase space is needed.
A C¹ vector field supplies the local Lipschitz hypothesis; equality then extends throughout
any preconnected real parameter set. On a closed interval, continuity up to the endpoints and
an interior derivative with a state-space Lipschitz bound likewise yield uniqueness from any
interior or boundary reference point.

For an autonomous field `X` that is locally Lipschitz only on a subset `S` containing two
trajectories (without an ambient neighborhood Lipschitz bound), compactness of `[a, c]` yields a
single Lipschitz constant along their joint image, giving forward uniqueness on `[a, b]` and
`[a, b)`.

## Main results

* `TauCeti.ODE_solution_unique_of_eventually_nhdsWithin`: local uniqueness with a uniform
  state-space Lipschitz constant on a neighborhood of the common phase.
* `ContDiffAt.ode_eventuallyEq_nhdsWithin`: C¹ local uniqueness.
* `IsPreconnected.ode_eqOn`: locally Lipschitz uniqueness on a preconnected parameter set.
* `IsPreconnected.ode_eqOn_of_contDiffAt`: the C¹ specialization.
* `LocallyLipschitzOn.eqOn_Icc_of_hasDerivAt_Ioo`,
  `LocallyLipschitzOn.eqOn_Ico_of_hasDerivAt_Ioo`: forward uniqueness on `[a, b]` and
  `[a, b)` for autonomous fields locally Lipschitz on a subset `S`.
* `ODE.eqOn_Icc_of_lipschitzOnWith` and `ODE.eqOn_Icc_of_lipschitzWith`: closed-interval
  uniqueness from interior derivatives and a common value at any `c ∈ [a, b]`.

## References

* `Mathlib.Analysis.ODE.ExistUnique` for local Lipschitz uniqueness.
* `TauCeti.Analysis.ODE.Gronwall.Interior` for closed-interval Grönwall bounds from interior
  derivatives.
* J. Morgan and G. Tian, *Ricci Flow and the Poincaré Conjecture*, Lemmas 6.8 and 6.10:
  closed-endpoint ODE uniqueness is an analytic input to reduced-geodesic and variation
  uniqueness there.
* Public formalizations: [lean-eval-submissions](https://github.com/frenzymath/lean-eval-submissions)
  and [PoincareConjecture](https://github.com/frenzymath/PoincareConjecture).
-/

public section

open Filter Topology
open scoped NNReal

section

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

end

namespace ODE

open Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Two curves continuous on `[a, b]`, remaining inside `s t` and solving `γ' t = v t (γ t)` at
interior points `t ∈ (a, b)` where `v t` is `K`-Lipschitz on `s t`, agree throughout `[a, b]`
whenever they agree at an interior or boundary point `c ∈ [a, b]`. -/
theorem eqOn_Icc_of_lipschitzOnWith {a b c : ℝ} {v : ℝ → E → E} {s : ℝ → Set E} {K : ℝ≥0}
    {f g : ℝ → E} (hv : ∀ t ∈ Ioo a b, LipschitzOnWith K (v t) (s t)) (hc : c ∈ Icc a b)
    (hf : ContinuousOn f (Icc a b)) (hf' : ∀ t ∈ Ioo a b, HasDerivAt f (v t (f t)) t)
    (hfs : ∀ t ∈ Ioo a b, f t ∈ s t)
    (hg : ContinuousOn g (Icc a b)) (hg' : ∀ t ∈ Ioo a b, HasDerivAt g (v t (g t)) t)
    (hgs : ∀ t ∈ Ioo a b, g t ∈ s t) (hfc : f c = g c) :
    EqOn f g (Icc a b) := fun t ht ↦ by
  have hle := TauCeti.norm_le_gronwallBound_of_norm_deriv_le (f := fun u ↦ f u - g u)
    (f' := fun u ↦ v u (f u) - v u (g u)) (δ := 0) (K := K) (ε := 0) hc (hf.sub hg)
    (fun u hu ↦ (hf' u hu).sub (hg' u hu)) (by simp [hfc])
    (fun u hu ↦ by
      simpa only [add_zero, dist_eq_norm] using
        (hv u hu).dist_le_mul (f u) (hfs u hu) (g u) (hgs u hu))
    t ht
  rw [gronwallBound_ε0_δ0] at hle
  exact sub_eq_zero.1 (norm_le_zero_iff.1 hle)

/-- Two curves continuous on `[a, b]` that solve `γ' t = v t (γ t)` on `(a, b)` for a
state-Lipschitz field `v` and agree at an interior or boundary point `c ∈ [a, b]` agree throughout
`[a, b]`. -/
theorem eqOn_Icc_of_lipschitzWith {a b c : ℝ} {v : ℝ → E → E} {K : ℝ≥0} {f g : ℝ → E}
    (hv : ∀ t ∈ Ioo a b, LipschitzWith K (v t)) (hc : c ∈ Icc a b)
    (hf : ContinuousOn f (Icc a b)) (hf' : ∀ t ∈ Ioo a b, HasDerivAt f (v t (f t)) t)
    (hg : ContinuousOn g (Icc a b)) (hg' : ∀ t ∈ Ioo a b, HasDerivAt g (v t (g t)) t)
    (hfc : f c = g c) :
    EqOn f g (Icc a b) :=
  eqOn_Icc_of_lipschitzOnWith (s := fun _ ↦ univ) (fun t ht ↦ (hv t ht).lipschitzOnWith) hc
    hf hf' (fun _ _ ↦ trivial) hg hg' (fun _ _ ↦ trivial) hfc

end ODE

namespace LocallyLipschitzOn

open ODE Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f g : ℝ → E}

/-- **Forward uniqueness on `[a, b]`.** If `X` is locally Lipschitz on `S`, any two continuous
curves on `[a, b]` mapping `[a, b)` into `S` with derivative `X (γ t)` on `(a, b)` and the same
value at `a` agree on `[a, b]`. -/
theorem eqOn_Icc_of_hasDerivAt_Ioo {S : Set E} {X : E → E} (hX : LocallyLipschitzOn S X)
    {a b : ℝ}
    (hf : ContinuousOn f (Icc a b))
    (hf' : ∀ t ∈ Ioo a b, HasDerivAt f (X (f t)) t)
    (hf_mem : MapsTo f (Ico a b) S)
    (hg : ContinuousOn g (Icc a b))
    (hg' : ∀ t ∈ Ioo a b, HasDerivAt g (X (g t)) t)
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
    exact eqOn_Icc_of_lipschitzOnWith (v := fun _ ↦ X) (s := fun _ ↦ Kset)
      (fun _ _ ↦ hKLip) (left_mem_Icc.mpr hc.1)
      (hf.mono (hsub.trans Ico_subset_Icc_self))
      (fun t ht ↦ hf' t ⟨ht.1, ht.2.trans hc.2⟩)
      (fun _ ht ↦ Or.inl (mem_image_of_mem f (Ioo_subset_Icc_self ht)))
      (hg.mono (hsub.trans Ico_subset_Icc_self))
      (fun t ht ↦ hg' t ⟨ht.1, ht.2.trans hc.2⟩)
      (fun _ ht ↦ Or.inr (mem_image_of_mem g (Ioo_subset_Icc_self ht))) ha ⟨hc.1, le_rfl⟩
  rcases lt_or_ge a b with hab | hba
  · exact hIco.of_subset_closure hf hg Ico_subset_Icc_self (closure_Ico hab.ne ▸ Subset.rfl)
  · intro t ht
    obtain rfl : a = b := le_antisymm (ht.1.trans ht.2) hba
    simpa [le_antisymm ht.1 ht.2] using ha

/-- **Forward uniqueness on `[a, b)`.** Two curves continuous on `[a, b)` mapping into `S`, solving
`γ' = X ∘ γ` on `(a, b)` for a locally Lipschitz field `X` on `S`, and agreeing at `a` agree on
`[a, b)`. -/
theorem eqOn_Ico_of_hasDerivAt_Ioo {S : Set E} {X : E → E} (hX : LocallyLipschitzOn S X)
    {a b : ℝ}
    (hf : ContinuousOn f (Ico a b))
    (hf' : ∀ t ∈ Ioo a b, HasDerivAt f (X (f t)) t)
    (hf_mem : MapsTo f (Ico a b) S)
    (hg : ContinuousOn g (Ico a b))
    (hg' : ∀ t ∈ Ioo a b, HasDerivAt g (X (g t)) t)
    (hg_mem : MapsTo g (Ico a b) S)
    (ha : f a = g a) :
    EqOn f g (Ico a b) := fun c hc ↦ by
  have hsub : Icc a c ⊆ Ico a b := fun t ht ↦ ⟨ht.1, ht.2.trans_lt hc.2⟩
  exact hX.eqOn_Icc_of_hasDerivAt_Ioo
    (hf.mono hsub)
    (fun t ht ↦ hf' t ⟨ht.1, ht.2.trans hc.2⟩)
    (fun t ht ↦ hf_mem (hsub (Ico_subset_Icc_self ht)))
    (hg.mono hsub)
    (fun t ht ↦ hg' t ⟨ht.1, ht.2.trans hc.2⟩)
    (fun t ht ↦ hg_mem (hsub (Ico_subset_Icc_self ht))) ha ⟨hc.1, le_rfl⟩

end LocallyLipschitzOn
