/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.EReal.Basic
public import Mathlib.Topology.Order.Compact
public import Mathlib.Topology.Semicontinuity.Basic
public import Mathlib.Topology.Sequences
import Mathlib.Tactic.Linarith

/-!
# Sequential lower semicontinuity

`TauCeti.SeqLowerSemicontinuousOn f s` expresses lower semicontinuity of `f : X → β` along
convergent sequences in a subset `s`: whenever `u n ∈ s` converges to `x ∈ s` and `b < f x`,
eventually `b < f (u n)`. Like `LowerSemicontinuousOn`, it is stated for an arbitrary preorder `β`
without assuming completeness or an order topology on `β`.

In a linear order, sequential lower semicontinuity on `s` is equivalent to sequential closedness of
every sublevel `{x : s | f x ≤ b}` in the subspace topology of `s`
(`TauCeti.seqLowerSemicontinuousOn_iff_isSeqClosed_sublevel`), and hence agrees with topological
`LowerSemicontinuousOn f s` whenever `s` is a sequential space
(`TauCeti.seqLowerSemicontinuousOn_iff_lowerSemicontinuousOn`). In a complete linear order it is
equivalent to `f x ≤ liminf (f ∘ u) atTop` along every convergent sequence in `s`, and for
real-valued functions to `(f x : EReal) ≤ liminf (fun n ↦ (f (u n) : EReal)) atTop`
(`TauCeti.seqLowerSemicontinuousOn_iff_coe_ereal_le_liminf`). When `f '' s` is bounded below and
closed intervals in `β` are sequentially compact (for instance `β = ℝ`), it is also equivalent to
the finite-limit inequality `Tendsto (f ∘ u) atTop (𝓝 r) → f x ≤ r`; without `BddBelow (f '' s)`,
`f(0) = 0` and `f(1/(n + 1)) = -(n + 1)` on `{0} ∪ {1/(n + 1)} ⊆ ℝ` satisfies the finite-limit
condition vacuously at `0` while failing sequential lower semicontinuity.
-/

public section

open Filter Set Topology

namespace TauCeti

/-- `f` is sequentially lower semicontinuous on `s` if along every sequence in `s` converging to a
point `x ∈ s`, every strict lower bound on `f x` holds eventually along the sequence. -/
def SeqLowerSemicontinuousOn {X β : Type*} [TopologicalSpace X] [Preorder β]
    (f : X → β) (s : Set X) : Prop :=
  ∀ ⦃u : ℕ → X⦄ ⦃x : X⦄, (∀ n, u n ∈ s) → x ∈ s →
    Tendsto u atTop (𝓝 x) → ∀ b < f x, ∀ᶠ n in atTop, b < f (u n)

/-- `f` is sequentially lower semicontinuous if along every convergent sequence `u → x`, every
strict lower bound on `f x` holds eventually along the sequence. -/
def SeqLowerSemicontinuous {X β : Type*} [TopologicalSpace X] [Preorder β]
    (f : X → β) : Prop :=
  ∀ ⦃u : ℕ → X⦄ ⦃x : X⦄, Tendsto u atTop (𝓝 x) → ∀ b < f x, ∀ᶠ n in atTop, b < f (u n)

section Preorder

variable {X Y β : Type*} [TopologicalSpace X] [TopologicalSpace Y] [Preorder β]
  {f g : X → β} {s t : Set X}

/-- Unfolding characterization of `SeqLowerSemicontinuousOn`. -/
theorem seqLowerSemicontinuousOn_iff :
    SeqLowerSemicontinuousOn f s ↔
      ∀ ⦃u : ℕ → X⦄ ⦃x : X⦄, (∀ n, u n ∈ s) → x ∈ s →
        Tendsto u atTop (𝓝 x) → ∀ b < f x, ∀ᶠ n in atTop, b < f (u n) :=
  Iff.rfl

/-- Unfolding characterization of `SeqLowerSemicontinuous`. -/
theorem seqLowerSemicontinuous_iff :
    SeqLowerSemicontinuous f ↔
      ∀ ⦃u : ℕ → X⦄ ⦃x : X⦄, Tendsto u atTop (𝓝 x) → ∀ b < f x, ∀ᶠ n in atTop, b < f (u n) :=
  Iff.rfl

/-- Sequential lower semicontinuity on `univ` is global sequential lower semicontinuity. -/
@[simp] theorem seqLowerSemicontinuousOn_univ_iff :
    SeqLowerSemicontinuousOn f univ ↔ SeqLowerSemicontinuous f :=
  ⟨fun hf _ _ hlim b hb ↦ hf (fun _ ↦ mem_univ _) (mem_univ _) hlim b hb,
    fun hf _ _ _ _ hlim b hb ↦ hf hlim b hb⟩

/-- Every function is sequentially lower semicontinuous on the empty set. -/
@[simp] theorem seqLowerSemicontinuousOn_empty : SeqLowerSemicontinuousOn f ∅ :=
  fun _ _ _ hx ↦ hx.elim

/-- Every constant function is sequentially lower semicontinuous. -/
@[simp] theorem seqLowerSemicontinuous_const (c : β) : SeqLowerSemicontinuous (fun _ : X ↦ c) :=
  fun _ _ _ _ hb ↦ .of_forall fun _ ↦ hb

/-- Every constant function is sequentially lower semicontinuous on any set. -/
@[simp] theorem seqLowerSemicontinuousOn_const (c : β) :
    SeqLowerSemicontinuousOn (fun _ : X ↦ c) s :=
  fun _ _ _ _ _ _ hb ↦ .of_forall fun _ ↦ hb

/-- Sequential lower semicontinuity on `s` depends only on the values of `f` on `s`. -/
theorem seqLowerSemicontinuousOn_congr (h : EqOn f g s) :
    SeqLowerSemicontinuousOn f s ↔ SeqLowerSemicontinuousOn g s := by
  refine ⟨fun hf u x hu hx hlim b hb ↦ ?_, fun hg u x hu hx hlim b hb ↦ ?_⟩
  · exact (hf hu hx hlim b (hb.trans_eq (h hx).symm)).mono fun n hn ↦ hn.trans_eq (h (hu n))
  · exact (hg hu hx hlim b (hb.trans_eq (h hx))).mono fun n hn ↦ hn.trans_eq (h (hu n)).symm

namespace SeqLowerSemicontinuous

/-- A sequentially lower semicontinuous function is sequentially lower semicontinuous on any set. -/
theorem seqLowerSemicontinuousOn (hf : SeqLowerSemicontinuous f) (s : Set X) :
    SeqLowerSemicontinuousOn f s :=
  fun _ _ _ _ hlim b hb ↦ hf hlim b hb

/-- Composition of a sequentially lower semicontinuous function with a sequentially continuous
map is sequentially lower semicontinuous. -/
theorem comp_seqContinuous (hf : SeqLowerSemicontinuous f) {h : Y → X} (hh : SeqContinuous h) :
    SeqLowerSemicontinuous (f ∘ h) :=
  fun _ _ hlim b hb ↦ hf (hh hlim) b hb

end SeqLowerSemicontinuous

namespace SeqLowerSemicontinuousOn

/-- Sequential lower semicontinuity is inherited by subsets. -/
theorem mono (hf : SeqLowerSemicontinuousOn f s) (hts : t ⊆ s) :
    SeqLowerSemicontinuousOn f t :=
  fun _ _ hu hx hlim b hb ↦ hf (fun n ↦ hts (hu n)) (hts hx) hlim b hb

/-- Precomposition with a continuous-on map mapping `t'` into `s` preserves sequential lower
semicontinuity. -/
theorem comp_continuousOn (hf : SeqLowerSemicontinuousOn f s) {h : Y → X} {t' : Set Y}
    (hh : ContinuousOn h t') (hmap : MapsTo h t' s) :
    SeqLowerSemicontinuousOn (f ∘ h) t' := by
  intro u y hu hy hlim b hb
  have huy : Tendsto u atTop (𝓝[t'] y) := tendsto_nhdsWithin_iff.mpr ⟨hlim, .of_forall hu⟩
  exact hf (fun n ↦ hmap (hu n)) (hmap hy) ((hh y hy).tendsto.comp huy) b hb

end SeqLowerSemicontinuousOn

end Preorder

end TauCeti

section Bridges

variable {X β : Type*} [TopologicalSpace X]

/-- Topological lower semicontinuity on `s` implies sequential lower semicontinuity on `s`. -/
theorem LowerSemicontinuousOn.seqLowerSemicontinuousOn [Preorder β] {f : X → β} {s : Set X}
    (hf : LowerSemicontinuousOn f s) : TauCeti.SeqLowerSemicontinuousOn f s :=
  fun _ x hu hx hlim b hb ↦
    (tendsto_nhdsWithin_iff.mpr ⟨hlim, .of_forall hu⟩).eventually (hf x hx b hb)

/-- Topological lower semicontinuity implies sequential lower semicontinuity. -/
theorem LowerSemicontinuous.seqLowerSemicontinuous [Preorder β] {f : X → β}
    (hf : LowerSemicontinuous f) : TauCeti.SeqLowerSemicontinuous f :=
  fun _ x hlim b hb ↦ hlim.eventually (hf x b hb)

/-- A sequentially continuous function into a linearly ordered space with closed `Iic` intervals is
sequentially lower semicontinuous. -/
theorem SeqContinuous.seqLowerSemicontinuous [LinearOrder β] [TopologicalSpace β]
    [ClosedIicTopology β] {f : X → β} (hf : SeqContinuous f) :
    TauCeti.SeqLowerSemicontinuous f :=
  fun _ _ hlim _ hb ↦ (hf hlim).eventually (eventually_gt_nhds hb)

end Bridges

namespace TauCeti

section LinearOrder

variable {X β : Type*} [TopologicalSpace X] [LinearOrder β] {f g : X → β} {s : Set X}

/-- Sequential lower semicontinuity on `s` is equivalent to sequential closedness in the subspace
`s` of every sublevel `{x : s | f x ≤ b}`. -/
theorem seqLowerSemicontinuousOn_iff_isSeqClosed_sublevel :
    SeqLowerSemicontinuousOn f s ↔ ∀ b : β, IsSeqClosed {x : s | f x ≤ b} := by
  constructor
  · intro hf b u x hu hlim
    by_contra hnot
    have hlt : b < f x := not_le.mp hnot
    have hev := hf (fun n ↦ (u n).2) x.2 ((continuous_subtype_val.tendsto x).comp hlim) b hlt
    obtain ⟨n, hn⟩ := hev.exists
    exact hn.not_ge (hu n)
  · intro hsub u x hu hx hlim b hb
    by_contra hnot
    have hfreq : ∃ᶠ n in atTop, f (u n) ≤ b := by
      simpa only [not_eventually, not_lt] using hnot
    obtain ⟨φ, hφ_mono, hφ_le⟩ := extraction_of_frequently_atTop hfreq
    have hlim' : Tendsto (fun n ↦ (⟨u (φ n), hu (φ n)⟩ : s)) atTop (𝓝 ⟨x, hx⟩) :=
      tendsto_subtype_rng.mpr (hlim.comp hφ_mono.tendsto_atTop)
    exact hb.not_ge (hsub b hφ_le hlim')

/-- On a sequentially closed set `s`, sequential lower semicontinuity on `s` is equivalent to
sequential closedness of every relative sublevel `{x ∈ s | f x ≤ b}`. -/
theorem _root_.IsSeqClosed.seqLowerSemicontinuousOn_iff (hs : IsSeqClosed s) :
    SeqLowerSemicontinuousOn f s ↔ ∀ b : β, IsSeqClosed {x ∈ s | f x ≤ b} := by
  rw [seqLowerSemicontinuousOn_iff_isSeqClosed_sublevel]
  refine forall_congr' fun b ↦ ⟨fun hb u x hu hlim ↦ ?_, fun hb u x hu hlim ↦ ?_⟩
  · have hxs : x ∈ s := hs (fun n ↦ (hu n).1) hlim
    exact ⟨hxs, hb (x := fun n ↦ ⟨u n, (hu n).1⟩) (p := ⟨x, hxs⟩)
      (fun n ↦ (hu n).2) (tendsto_subtype_rng.mpr hlim)⟩
  · exact (hb (fun n ↦ ⟨(u n).2, hu n⟩) ((continuous_subtype_val.tendsto x).comp hlim)).2

/-- On a sequentially closed set, every relative sublevel of a sequentially lower semicontinuous
function is sequentially closed. -/
theorem SeqLowerSemicontinuousOn.isSeqClosed_sublevel (hf : SeqLowerSemicontinuousOn f s)
    (hs : IsSeqClosed s) (b : β) : IsSeqClosed {x ∈ s | f x ≤ b} :=
  (hs.seqLowerSemicontinuousOn_iff.mp hf) b

/-- Global sequential lower semicontinuity is equivalent to sequential closedness of every sublevel
`f ⁻¹' Iic b`. -/
theorem seqLowerSemicontinuous_iff_isSeqClosed_preimage :
    SeqLowerSemicontinuous f ↔ ∀ b : β, IsSeqClosed (f ⁻¹' Iic b) := by
  rw [← seqLowerSemicontinuousOn_univ_iff, isClosed_univ.isSeqClosed.seqLowerSemicontinuousOn_iff]
  simp only [mem_univ, true_and]
  rfl

/-- When the subspace `s` is a sequential space, sequential lower semicontinuity on `s` is
equivalent to topological lower semicontinuity on `s`. -/
theorem seqLowerSemicontinuousOn_iff_lowerSemicontinuousOn [SequentialSpace s] :
    SeqLowerSemicontinuousOn f s ↔ LowerSemicontinuousOn f s := by
  rw [seqLowerSemicontinuousOn_iff_isSeqClosed_sublevel, ← lowerSemicontinuous_restrict_iff,
    lowerSemicontinuous_iff_isClosed_preimage]
  exact forall_congr' fun _ ↦ isSeqClosed_iff_isClosed

/-- On a sequential space, sequential lower semicontinuity is equivalent to topological lower
semicontinuity. -/
theorem seqLowerSemicontinuous_iff_lowerSemicontinuous [SequentialSpace X] :
    SeqLowerSemicontinuous f ↔ LowerSemicontinuous f := by
  rw [seqLowerSemicontinuous_iff_isSeqClosed_preimage, lowerSemicontinuous_iff_isClosed_preimage]
  exact forall_congr' fun _ ↦ isSeqClosed_iff_isClosed

/-- Pointwise maximum of two sequentially lower semicontinuous functions on `s`. -/
theorem SeqLowerSemicontinuousOn.sup (hf : SeqLowerSemicontinuousOn f s)
    (hg : SeqLowerSemicontinuousOn g s) :
    SeqLowerSemicontinuousOn (fun x ↦ f x ⊔ g x) s := by
  intro u x hu hx hlim b hb
  rcases lt_sup_iff.mp hb with hbf | hbg
  · exact (hf hu hx hlim b hbf).mono fun n hn ↦ lt_sup_of_lt_left hn
  · exact (hg hu hx hlim b hbg).mono fun n hn ↦ lt_sup_of_lt_right hn

end LinearOrder

section CompleteLinearOrder

variable {X β : Type*} [TopologicalSpace X] [CompleteLinearOrder β] {f : X → β} {s : Set X}

/-- In a complete linear order, sequential lower semicontinuity on `s` is equivalent to the lower
limit inequality `f x ≤ liminf (f ∘ u) atTop` along every convergent sequence in `s`. -/
theorem seqLowerSemicontinuousOn_iff_le_liminf :
    SeqLowerSemicontinuousOn f s ↔
      ∀ ⦃u : ℕ → X⦄ ⦃x : X⦄, (∀ n, u n ∈ s) → x ∈ s →
        Tendsto u atTop (𝓝 x) → f x ≤ liminf (f ∘ u) atTop := by
  constructor
  · intro hf u x hu hx hlim
    by_contra! hlt
    obtain ⟨z, hz, y, hy, hdisj⟩ := hlt.exists_disjoint_Iio_Ioi
    exact hz.not_ge <| le_liminf_of_le (by isBoundedDefault) <|
      (hf hu hx hlim y hy).mono fun n hn ↦ le_of_not_gt fun hlt' ↦ (hdisj _ hlt' _ hn).false
  · exact fun hf u x hu hx hlim b hb ↦ eventually_lt_of_lt_liminf (hb.trans_le (hf hu hx hlim))

/-- Lower limit inequality along a convergent sequence in `s` for a sequentially lower
semicontinuous function valued in a complete linear order. -/
theorem SeqLowerSemicontinuousOn.le_liminf (hf : SeqLowerSemicontinuousOn f s) {u : ℕ → X}
    {x : X} (hu : ∀ n, u n ∈ s) (hx : x ∈ s) (hlim : Tendsto u atTop (𝓝 x)) :
    f x ≤ liminf (f ∘ u) atTop :=
  seqLowerSemicontinuousOn_iff_le_liminf.mp hf hu hx hlim

/-- Pointwise supremum of sequentially lower semicontinuous functions into a complete linear
order. -/
theorem seqLowerSemicontinuousOn_iSup {ι : Sort*} {F : ι → X → β}
    (hF : ∀ i, SeqLowerSemicontinuousOn (F i) s) :
    SeqLowerSemicontinuousOn (fun x ↦ ⨆ i, F i x) s := by
  intro u x hu hx hlim b hb
  obtain ⟨i, hi⟩ := lt_iSup_iff.mp hb
  exact (hF i hu hx hlim b hi).mono fun n hn ↦ hn.trans_le (le_iSup (fun j ↦ F j (u n)) i)

end CompleteLinearOrder

section FiniteLimits

variable {X β : Type*} [TopologicalSpace X] [LinearOrder β] [TopologicalSpace β]
  [ClosedIciTopology β] {f : X → β} {s : Set X}

/-- If `f` is sequentially lower semicontinuous on `s`, `u n ∈ s` converges to `x ∈ s`, and
`f (u n)` converges to `r`, then `f x ≤ r`. -/
theorem SeqLowerSemicontinuousOn.le_of_tendsto (hf : SeqLowerSemicontinuousOn f s) {u : ℕ → X}
    {x : X} {r : β} (hu : ∀ n, u n ∈ s) (hx : x ∈ s) (hux : Tendsto u atTop (𝓝 x))
    (hfu : Tendsto (fun n ↦ f (u n)) atTop (𝓝 r)) : f x ≤ r := by
  by_contra! hlt
  by_cases hgap : ∃ b, r < b ∧ b < f x
  · obtain ⟨b, hrb, hbf⟩ := hgap
    obtain ⟨n, hn₁, hn₂⟩ := ((hf hu hx hux b hbf).and (hfu.eventually_lt_const hrb)).exists
    exact hn₁.not_gt hn₂
  · push Not at hgap
    have hle : ∀ᶠ n in atTop, f x ≤ f (u n) := (hf hu hx hux r hlt).mono fun _ hn ↦ hgap _ hn
    exact hlt.not_ge (ge_of_tendsto hfu hle)

/-- When `f '' s` is bounded below and closed intervals in `β` are sequentially compact, sequential
lower semicontinuity on `s` is equivalent to the finite-limit inequality
`Tendsto (fun n ↦ f (u n)) atTop (𝓝 r) → f x ≤ r`. -/
theorem seqLowerSemicontinuousOn_iff_le_of_tendsto_of_bddBelow [CompactIccSpace β]
    [FirstCountableTopology β] (hbdd : BddBelow (f '' s)) :
    SeqLowerSemicontinuousOn f s ↔
      ∀ ⦃u : ℕ → X⦄ ⦃x : X⦄ ⦃r : β⦄, (∀ n, u n ∈ s) → x ∈ s →
        Tendsto u atTop (𝓝 x) → Tendsto (fun n ↦ f (u n)) atTop (𝓝 r) → f x ≤ r := by
  refine ⟨fun hf u x r hu hx hux hfu ↦ hf.le_of_tendsto hu hx hux hfu, fun hfin ↦ ?_⟩
  obtain ⟨a, ha⟩ := hbdd
  intro u x hu hx hux b hb
  by_contra hnot
  have hfreq : ∃ᶠ n in atTop, f (u n) ≤ b := by
    simpa only [not_eventually, not_lt] using hnot
  obtain ⟨φ, hφ_mono, hφ_le⟩ := extraction_of_frequently_atTop hfreq
  have hmem (n : ℕ) : f (u (φ n)) ∈ Icc a b :=
    ⟨ha (mem_image_of_mem f (hu (φ n))), hφ_le n⟩
  obtain ⟨r, hr, ψ, hψ_mono, hlim⟩ := isCompact_Icc.isSeqCompact hmem
  exact hb.not_ge <| (hfin (fun n ↦ hu (φ (ψ n))) hx
    (hux.comp (hφ_mono.comp hψ_mono).tendsto_atTop) hlim).trans hr.2

end FiniteLimits

section Real

variable {X : Type*} [TopologicalSpace X] {f g : X → ℝ} {s : Set X}

/-- Coercing a real-valued function to `EReal` does not change sequential lower semicontinuity on
`s`. -/
@[simp] theorem seqLowerSemicontinuousOn_coe_ereal_iff :
    SeqLowerSemicontinuousOn (fun x ↦ (f x : EReal)) s ↔ SeqLowerSemicontinuousOn f s := by
  constructor
  · intro hf u x hu hx hlim b hb
    simpa only [EReal.coe_lt_coe_iff] using hf hu hx hlim (b : EReal) (EReal.coe_lt_coe_iff.mpr hb)
  · intro hf u x hu hx hlim b hb
    induction b using EReal.rec with
    | bot => exact .of_forall fun n ↦ EReal.bot_lt_coe (f (u n))
    | coe r =>
      simpa only [EReal.coe_lt_coe_iff] using hf hu hx hlim r (EReal.coe_lt_coe_iff.mp hb)
    | top => exact (not_top_lt hb).elim

/-- For a real-valued function `f`, sequential lower semicontinuity on `s` is equivalent to the
`EReal` lower-limit inequality `(f x : EReal) ≤ liminf (fun n ↦ (f (u n) : EReal)) atTop` along
every convergent sequence in `s`. -/
theorem seqLowerSemicontinuousOn_iff_coe_ereal_le_liminf :
    SeqLowerSemicontinuousOn f s ↔
      ∀ ⦃u : ℕ → X⦄ ⦃x : X⦄, (∀ n, u n ∈ s) → x ∈ s →
        Tendsto u atTop (𝓝 x) → (f x : EReal) ≤ liminf (fun n ↦ (f (u n) : EReal)) atTop := by
  rw [← seqLowerSemicontinuousOn_coe_ereal_iff, seqLowerSemicontinuousOn_iff_le_liminf]
  rfl

/-- Sum of two real-valued sequentially lower semicontinuous functions on `s`. -/
theorem SeqLowerSemicontinuousOn.add (hf : SeqLowerSemicontinuousOn f s)
    (hg : SeqLowerSemicontinuousOn g s) :
    SeqLowerSemicontinuousOn (fun x ↦ f x + g x) s := by
  intro u x hu hx hlim b hb
  let δ := (f x + g x - b) / 2
  have hδ : 0 < δ := by dsimp [δ]; linarith
  refine ((hf hu hx hlim (f x - δ) (by linarith)).and
    (hg hu hx hlim (g x - δ) (by linarith))).mono fun n ⟨hn₁, hn₂⟩ ↦ ?_
  dsimp [δ] at hn₁ hn₂
  linarith

/-- Nonnegative scalar multiple of a real-valued sequentially lower semicontinuous function on
`s`. -/
theorem SeqLowerSemicontinuousOn.const_mul (hf : SeqLowerSemicontinuousOn f s) {c : ℝ}
    (hc : 0 ≤ c) :
    SeqLowerSemicontinuousOn (fun x ↦ c * f x) s := by
  rcases hc.eq_or_lt with rfl | hc_pos
  · simpa only [zero_mul] using seqLowerSemicontinuousOn_const 0
  · intro u x hu hx hlim b hb
    exact (hf hu hx hlim (b / c) ((div_lt_iff₀ hc_pos).mpr (by linarith))).mono fun n hn ↦ by
      have := (div_lt_iff₀ hc_pos).mp hn
      linarith

end Real

end TauCeti
