/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.CWModel
import TauCeti.Geometry.Manifold.Morse.LocalDiffeomorph

/-!
# Relative CW models of regular cobordisms

Let `f` be a Morse function on a boundaryless manifold `M`, and let `a ≤ b` be regular values of
`f` with compact band `W = f⁻¹[a, b]`. Then `W` is a cobordism from its incoming boundary
`f⁻¹(a)` to its outgoing boundary `f⁻¹(b)`. This file builds its CW models relative to either
boundary.

Relative to the incoming boundary, `W` is homotopy equivalent to `f⁻¹(a)` with one `λ`-cell
attached for each critical point of index `λ` in `W`, arranged as a CW complex relative to a copy
of `f⁻¹(a)`, by a homotopy equivalence which is the inclusion on `f⁻¹(a)`
(`TauCeti.IsMorse.exists_relCWComplex_homotopyEquiv_band`). Relative to the outgoing boundary the
same holds with the cells indexed by the critical points of `-f`, so that a critical point of
index `λ` of `f` gives a cell of the complementary dimension `dim M - λ`
(`TauCeti.IsMorse.exists_relCWComplex_homotopyEquiv_upperBand`). These are the CW forms of the
Morse inequalities for the band pairs `(f⁻¹[a, b], f⁻¹(a))` and `(f⁻¹[a, b], f⁻¹(b))` in
`TauCeti.Geometry.Manifold.Morse.Inequalities`.

The incoming model is the relative CW model of the sublevels of `f` on the open submanifold
`V = {a < f}` (`TauCeti.IsMorse.exists_relCWComplex_extension_homotopyEquiv_sublevel`), started
from `f⁻¹(a)` itself. Since `a` is a regular value, the band `f⁻¹[a, s]` is a collar without
critical points for some `s > a`, along which a flow `φ` moves `f` at unit speed
(`TauCeti.exists_flow_apply_eq_sub`). Pushing the level `f⁻¹(a)` up into `V` along `φ` identifies
it, up to homotopy, with the sublevel `{x ∈ V | f x ≤ s}`, and pushing the bottom of the collar
back down identifies `{x ∈ V | f x ≤ b} = f⁻¹(a, b]` with `W`. The two pushes are chosen to
cancel on `f⁻¹(a)`, so the resulting homotopy equivalence is exactly the inclusion there.

## Main results

* `TauCeti.IsMorse.exists_relCWComplex_homotopyEquiv_band`: **the relative CW model of a regular
  cobordism.** `f⁻¹[a, b]` is homotopy equivalent, relative to `f⁻¹(a)`, to a CW complex relative
  to a copy of `f⁻¹(a)` with one `m`-cell for each critical point of index `m` in the band.
* `TauCeti.IsMorse.exists_relCWComplex_homotopyEquiv_upperBand`: the relative CW model of
  `f⁻¹[a, b]` relative to its outgoing boundary `f⁻¹(b)`, with one `m`-cell for each critical
  point of index `dim M - m` in the band.

## References

* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  Theorem 3.5 and its proof.
* J. Milnor, *Lectures on the h-cobordism theorem*, Princeton University Press, 1965, Theorem 3.4,
  for the collar of a regular level.
* R. L. Cohen, K. Iga and P. Norbury, *Topics in Morse Theory*, lecture notes, 2006, Theorem 5.7.
-/

public section

noncomputable section

open Set Topology Topology.RelCWComplex
open scoped Manifold ContDiff ContinuousMap

universe u

namespace TauCeti

variable {E H : Type*} {M : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [FiniteDimensional ℝ E]
  [I.Boundaryless] [IsManifold I ∞ M] [T2Space M] {f : M → ℝ}

omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M] [T2Space M] in
/-- Two maps into a space `Z` embedded in `M` which send each `y` to the flow line of `p y` at the
times `τ₀ y` and `τ₁ y` are homotopic, provided the flow line stays in `Z` at the times in
between. -/
private theorem homotopic_of_flow {Y Z : Type*} [TopologicalSpace Y] [TopologicalSpace Z]
    (φ : Flow ℝ M) {ι : Z → M} (hι : IsEmbedding ι) {F₀ F₁ : C(Y, Z)} {p : Y → M}
    (hp : Continuous p) {τ₀ τ₁ : Y → ℝ} (hτ₀ : Continuous τ₀) (hτ₁ : Continuous τ₁)
    (hF₀ : ∀ y, ι (F₀ y) = φ (τ₀ y) (p y)) (hF₁ : ∀ y, ι (F₁ y) = φ (τ₁ y) (p y))
    (hZ : ∀ y, ∀ t ∈ Icc (0 : ℝ) 1, φ ((1 - t) * τ₀ y + t * τ₁ y) (p y) ∈ range ι) :
    F₀.Homotopic F₁ := by
  choose G hG using fun q : unitInterval × Y ↦ hZ q.2 q.1 q.1.2
  refine ⟨⟨⟨G, ?_⟩, fun y ↦ ?_, fun y ↦ ?_⟩⟩
  · rw [hι.continuous_iff, Function.comp_def]
    simp_rw [hG]
    exact φ.continuous (by fun_prop) (hp.comp continuous_snd)
  · exact hι.injective ((hG (0, y)).trans (by simp [hF₀]))
  · exact hι.injective ((hG (1, y)).trans (by simp [hF₁]))

omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M] [T2Space M] in
/-- **The collar of a regular level as a sublevel of the open superlevel.** Let `φ` be a flow
moving `f` at unit speed through a collar `f⁻¹[a, s]`, `a < s`, and let `V` be the open set
`{a < f}`. Pushing the level `f⁻¹(a)` up to the middle `(a + s) / 2` of the collar is a homotopy
equivalence onto the sublevel `f⁻¹(a, s]` of `V`, whose inverse flows each point down to
`f⁻¹(a)`. -/
private theorem exists_homotopyEquiv_level_sublevel (hfc : Continuous f) (φ : Flow ℝ M)
    {a s : ℝ} (has : a < s)
    (hφ : ∀ y t, f y ∈ Icc a s → f y - t ∈ Icc a s → f (φ t y) = f y - t)
    (V : TopologicalSpace.Opens M) (hV : ∀ x, x ∈ V ↔ a < f x) :
    ∃ h₀ : f ⁻¹' {a} ≃ₕ {y : V | (f ∘ Subtype.val) y ≤ s},
      ∀ x, ((h₀ x : V) : M) = φ (a - (a + s) / 2) x := by
  set m := (a + s) / 2 with hm
  have hup (x : f ⁻¹' {a}) : f (φ (a - m) x) = m := by
    have hx : f x = a := x.2
    rw [hφ _ _ ⟨hx.ge, by linarith⟩ ⟨by linarith, by linarith⟩, hx]
    ring
  let p₀ : C({y : V | (f ∘ Subtype.val) y ≤ s}, M) := ⟨fun y ↦ ((y : V) : M), by fun_prop⟩
  have hp₀ (y : {y : V | (f ∘ Subtype.val) y ≤ s}) : a < f (p₀ y) ∧ f (p₀ y) ≤ s :=
    ⟨(hV _).1 (y : V).2, y.2⟩
  have hdown (y : {y : V | (f ∘ Subtype.val) y ≤ s}) : f (φ (f (p₀ y) - a) (p₀ y)) = a := by
    rw [hφ _ _ ⟨(hp₀ y).1.le, (hp₀ y).2⟩ ⟨by linarith, by linarith [has, (hp₀ y).2]⟩]
    ring
  let up : C(f ⁻¹' {a}, {y : V | (f ∘ Subtype.val) y ≤ s}) :=
    ⟨fun x ↦ ⟨⟨φ (a - m) x, (hV _).2 (by rw [hup]; linarith)⟩,
      show f _ ≤ s by rw [hup]; linarith⟩, by fun_prop⟩
  let down : C({y : V | (f ∘ Subtype.val) y ≤ s}, f ⁻¹' {a}) :=
    ⟨fun y ↦ ⟨φ (f (p₀ y) - a) (p₀ y), hdown y⟩, by fun_prop⟩
  refine ⟨⟨up, down, ?_, ?_⟩, fun x ↦ rfl⟩
  · -- Flowing up and back down is the identity of `f⁻¹(a)`.
    refine homotopic_of_flow φ IsEmbedding.subtypeVal continuous_subtype_val continuous_const
      continuous_const (τ₀ := fun _ ↦ 0) (τ₁ := fun _ ↦ 0) (fun x ↦ ?_) (fun x ↦ by simp)
      fun x t _ ↦ ⟨x, by simp⟩
    simp only [ContinuousMap.comp_apply, ContinuousMap.coe_mk, up, down, p₀, Flow.map_zero_apply]
    rw [hup, ← Flow.map_add, show m - a + (a - m) = 0 by ring, Flow.map_zero_apply]
  · -- Flowing down and back up moves `f⁻¹(a, s]` to the level `m` along its flow lines.
    refine homotopic_of_flow φ (IsEmbedding.subtypeVal.comp IsEmbedding.subtypeVal)
      p₀.continuous (by fun_prop) continuous_const (τ₀ := fun y ↦ f (p₀ y) - m)
      (τ₁ := fun _ ↦ 0) (fun y ↦ ?_) (fun y ↦ by simp [p₀]) fun y t ht ↦ ?_
    · simp only [Function.comp_apply, ContinuousMap.comp_apply, ContinuousMap.coe_mk, up, down]
      rw [← Flow.map_add]
      congr 1
      ring
    obtain ⟨hya, hys⟩ := hp₀ y
    simp only [mul_zero, add_zero]
    have hf' : f (φ ((1 - t) * (f (p₀ y) - m)) (p₀ y)) =
        f (p₀ y) - (1 - t) * (f (p₀ y) - m) :=
      hφ _ _ ⟨hya.le, hys⟩ ⟨by nlinarith [ht.1, ht.2], by nlinarith [ht.1, ht.2]⟩
    refine ⟨⟨⟨_, (hV _).2 ?_⟩, show f _ ≤ s from ?_⟩, rfl⟩ <;>
      rw [hf'] <;> nlinarith [ht.1, ht.2]

omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M] [T2Space M] in
/-- **Removing the bottom level of a band.** Let `φ` be a flow moving `f` at unit speed through a
collar `f⁻¹[a, s]`, `a < s ≤ b`, and let `V` be the open set `{a < f}`. Then the sublevel
`f⁻¹(a, b]` of `V` is homotopy equivalent to the band `f⁻¹[a, b]` by a map which pushes the bottom
of the collar down along `φ`, carrying the middle level `(a + s) / 2` to `f⁻¹(a)`. -/
private theorem exists_homotopyEquiv_sublevel_band (hfc : Continuous f) (φ : Flow ℝ M)
    {a s b : ℝ} (has : a < s) (hsb : s ≤ b)
    (hφ : ∀ y t, f y ∈ Icc a s → f y - t ∈ Icc a s → f (φ t y) = f y - t)
    (V : TopologicalSpace.Opens M) (hV : ∀ x, x ∈ V ↔ a < f x) :
    ∃ k : {y : V | (f ∘ Subtype.val) y ≤ b} ≃ₕ f ⁻¹' Icc a b,
      ∀ y : {y : V | (f ∘ Subtype.val) y ≤ b}, f (y : V) = (a + s) / 2 →
        (k y : M) = φ ((a + s) / 2 - a) (y : V) := by
  let p₁ : C({y : V | (f ∘ Subtype.val) y ≤ b}, M) := ⟨fun y ↦ ((y : V) : M), by fun_prop⟩
  have hp₁ (y : {y : V | (f ∘ Subtype.val) y ≤ b}) : a < f (p₁ y) ∧ f (p₁ y) ≤ b :=
    ⟨(hV _).1 (y : V).2, y.2⟩
  -- The point `y` is pushed down for the time `σ y`, which carries the middle level of the collar
  -- to `a`, and back up for the time `θ y`.
  let σ : M → ℝ := fun y ↦ max 0 (min (f y - a) (s - f y))
  have hσc : Continuous σ := by fun_prop
  let θ : M → ℝ := fun y ↦ max 0 (s - f y) / 2
  have hθc : Continuous θ := by fun_prop
  -- Flowing for any time between `0` and `σ y` keeps a point `y` of the band in the band.
  have hσ (y : M) (hya : a ≤ f y) (hyb : f y ≤ b) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      f (φ (t * σ y) y) = f y - t * σ y ∧ a ≤ f y - t * σ y ∧ f y - t * σ y ≤ b := by
    rcases le_or_gt (f y) s with hys | hys
    · have h0 : 0 ≤ min (f y - a) (s - f y) := le_min (by linarith) (by linarith)
      have hσy : σ y = min (f y - a) (s - f y) := max_eq_right h0
      have h1 : σ y ≤ f y - a := hσy ▸ min_le_left _ _
      have h2 : 0 ≤ σ y := hσy ▸ h0
      exact ⟨hφ _ _ ⟨hya, hys⟩ ⟨by nlinarith [ht.1, ht.2], by nlinarith [ht.1, ht.2]⟩,
        by nlinarith [ht.1, ht.2], by nlinarith [ht.1, ht.2]⟩
    · have hσy : σ y = 0 := max_eq_left ((min_le_right _ _).trans (by linarith))
      rw [hσy, mul_zero, Flow.map_zero_apply, sub_zero]
      exact ⟨rfl, hya, hyb⟩
  -- Flowing back for any time between `0` and `θ y` keeps a point `y` of the band in the band,
  -- and for the time `θ y` it lifts `y` strictly above `a`.
  have hθ (y : M) (hya : a ≤ f y) (hyb : f y ≤ b) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      f (φ (-(t * θ y)) y) = f y + t * θ y ∧ f y ≤ f y + t * θ y ∧ f y + t * θ y ≤ b ∧
        a < f y + θ y := by
    rcases le_or_gt (f y) s with hys | hys
    · have hθy : θ y = (s - f y) / 2 := by
        simp only [θ, max_eq_right (by linarith : 0 ≤ s - f y)]
      have h := hφ y (-(t * θ y)) ⟨hya, hys⟩
        ⟨by rw [hθy]; nlinarith [ht.1, ht.2], by rw [hθy]; nlinarith [ht.1, ht.2]⟩
      refine ⟨by rw [h]; ring, ?_, ?_, ?_⟩ <;> rw [hθy] <;> nlinarith [ht.1, ht.2]
    · have hθy : θ y = 0 := by simp only [θ, max_eq_left (by linarith : s - f y ≤ 0), zero_div]
      rw [hθy, mul_zero, neg_zero, Flow.map_zero_apply, add_zero]
      exact ⟨rfl, le_rfl, hyb, has.trans hys⟩
  let k : C({y : V | (f ∘ Subtype.val) y ≤ b}, f ⁻¹' Icc a b) :=
    ⟨fun y ↦ ⟨φ (σ (p₁ y)) (p₁ y), by
      obtain ⟨h₁, h₂, h₃⟩ := hσ _ (hp₁ y).1.le (hp₁ y).2 1 ⟨zero_le_one, le_rfl⟩
      rw [one_mul] at h₁ h₂ h₃
      exact ⟨h₁ ▸ h₂, h₁ ▸ h₃⟩⟩, by fun_prop⟩
  let incl : C({y : V | (f ∘ Subtype.val) y ≤ b}, f ⁻¹' Icc a b) :=
    ⟨fun y ↦ ⟨p₁ y, (hp₁ y).1.le, (hp₁ y).2⟩, by fun_prop⟩
  let ρ : C(f ⁻¹' Icc a b, {y : V | (f ∘ Subtype.val) y ≤ b}) :=
    ⟨fun y ↦ ⟨⟨φ (-(1 * θ y)) y, (hV _).2 <| by
        obtain ⟨h₁, -, -, h₄⟩ := hθ _ y.2.1 y.2.2 1 ⟨zero_le_one, le_rfl⟩
        rw [h₁, one_mul]
        exact h₄⟩, show f _ ≤ b by
        obtain ⟨h₁, -, h₃, -⟩ := hθ _ y.2.1 y.2.2 1 ⟨zero_le_one, le_rfl⟩
        rw [h₁]
        exact h₃⟩, by fun_prop⟩
  -- `k` is homotopic to the inclusion, which has the homotopy inverse `ρ`.
  have hk : k.Homotopic incl := homotopic_of_flow φ IsEmbedding.subtypeVal p₁.continuous
    (hσc.comp p₁.continuous) continuous_const (τ₀ := fun y ↦ σ (p₁ y)) (τ₁ := fun _ ↦ 0)
    (fun y ↦ rfl) (fun y ↦ by simp [incl])
    fun y t ht ↦ by
      obtain ⟨h₁, h₂, h₃⟩ := hσ _ (hp₁ y).1.le (hp₁ y).2 (1 - t)
        ⟨by linarith [ht.2], by linarith [ht.1]⟩
      simp only [mul_zero, add_zero]
      exact ⟨⟨_, h₁ ▸ h₂, h₁ ▸ h₃⟩, rfl⟩
  have hρ₁ : (incl.comp ρ).Homotopic (ContinuousMap.id _) := homotopic_of_flow φ
    IsEmbedding.subtypeVal continuous_subtype_val (by fun_prop) continuous_const
    (τ₀ := fun y ↦ -(1 * θ y)) (τ₁ := fun _ ↦ 0) (fun y ↦ rfl) (fun y ↦ by simp)
    fun y t ht ↦ by
      obtain ⟨h₁, h₂, h₃, -⟩ := hθ _ y.2.1 y.2.2 (1 - t) ⟨by linarith [ht.2], by linarith [ht.1]⟩
      rw [mul_zero, add_zero, show (1 - t) * -(1 * θ y) = -((1 - t) * θ y) by ring]
      exact ⟨⟨_, show a ≤ f _ by rw [h₁]; linarith [y.2.1], show f _ ≤ b by rw [h₁]; exact h₃⟩,
        rfl⟩
  have hρ₂ : (ρ.comp incl).Homotopic (ContinuousMap.id _) := homotopic_of_flow φ
    (IsEmbedding.subtypeVal.comp IsEmbedding.subtypeVal) p₁.continuous
    (by fun_prop) continuous_const (τ₀ := fun y ↦ -(1 * θ (p₁ y))) (τ₁ := fun _ ↦ 0)
    (fun y ↦ rfl) (fun y ↦ by simp [p₁])
    fun y t ht ↦ by
      obtain ⟨h₁, h₂, h₃, -⟩ := hθ _ (hp₁ y).1.le (hp₁ y).2 (1 - t)
        ⟨by linarith [ht.2], by linarith [ht.1]⟩
      rw [mul_zero, add_zero, show (1 - t) * -(1 * θ (p₁ y)) = -((1 - t) * θ (p₁ y)) by ring]
      exact ⟨⟨⟨_, (hV _).2 (by rw [h₁]; linarith [(hp₁ y).1])⟩,
        show f _ ≤ b by rw [h₁]; exact h₃⟩, rfl⟩
  refine ⟨⟨k, ρ, ((ContinuousMap.Homotopic.refl ρ).comp hk).trans hρ₂,
    (hk.comp (ContinuousMap.Homotopic.refl ρ)).trans hρ₁⟩, fun y hy ↦ ?_⟩
  -- At the middle level of the collar `σ` is the distance to `a`.
  change φ (σ (p₁ y)) (p₁ y) = _
  have hy' : f (p₁ y) = (a + s) / 2 := hy
  simp only [σ, hy']
  rw [show s - (a + s) / 2 = (a + s) / 2 - a by ring, min_self, max_eq_right (by linarith)]
  rfl

/-- **The relative CW model of a regular cobordism.** Let `f` be a Morse function and `a ≤ b`
regular values of `f` with compact band `f⁻¹[a, b]`. Then the band is homotopy equivalent to a CW
complex `X` relative to a copy of its incoming boundary `f⁻¹(a)`, with one `m`-cell for each
critical point of index `m` with value in `(a, b]`: there are a closed embedding
`j : f⁻¹(a) → X`, a relative CW structure on `X` with base the image of `j`, and a homotopy
equivalence `h : X ≃ₕ f⁻¹[a, b]` such that `h ∘ j` is the inclusion `f⁻¹(a) ⊆ f⁻¹[a, b]`. -/
theorem IsMorse.exists_relCWComplex_homotopyEquiv_band (hf : IsMorse I f) {a b : ℝ}
    (hab : a ≤ b) (hcompact : IsCompact (f ⁻¹' Icc a b)) (ha : IsRegularValue I 𝓘(ℝ) f a)
    (hb : IsRegularValue I 𝓘(ℝ) f b) :
    ∃ (X : Type u) (_ : TopologicalSpace X) (_ : T2Space X) (j : C(f ⁻¹' {a}, X))
      (_ : RelCWComplex (univ : Set X) (range j)) (h : X ≃ₕ f ⁻¹' Icc a b),
      IsClosedEmbedding j ∧ (∀ x, (h (j x) : M) = x) ∧
      Nonempty (∀ m, cell (univ : Set X) m ≃
        ↥{x ∈ criticalPoints I f ∩ f ⁻¹' Ioc a b | manifoldMorseIndex I f x = m}) := by
  have hfc : Continuous f := hf.contMDiff.continuous
  rcases hab.eq_or_lt with rfl | hab'
  · -- A band of width zero is its level, a CW complex relative to itself with no cells.
    let := relCWComplexSelf (univ : Set (f ⁻¹' {a})) isClosed_univ
    have (m : ℕ) : IsEmpty ↥{x ∈ criticalPoints I f ∩ f ⁻¹' Ioc a a |
        manifoldMorseIndex I f x = m} :=
      ⟨fun x ↦ (lt_irrefl a) (x.2.1.2.1.trans_le x.2.1.2.2)⟩
    refine ⟨f ⁻¹' {a}, _, inferInstance, .id _, ?_⟩
    rw [ContinuousMap.coe_id, range_id]
    exact ⟨‹_›, (Homeomorph.setCongr (by rw [Icc_self])).toHomotopyEquiv, .id,
      fun x ↦ rfl, ⟨fun m ↦ Equiv.equivOfIsEmpty _ _⟩⟩
  -- A collar `f⁻¹[a, s]` above `a` without critical points, with a flow `φ` moving `f` at unit
  -- speed through it.
  obtain ⟨s, ⟨has, hsb⟩, hcrit⟩ :=
    exists_mem_Ioc_forall_notMem_criticalPoints (hf.contMDiff.of_le (by simp)) hab' hcompact ha
  obtain ⟨φ, -, hanti, hlt, hφf⟩ := exists_flow_apply_eq_sub hf.contMDiff
    (hcompact.of_isClosed_subset (isClosed_Icc.preimage hfc)
      (preimage_mono (Icc_subset_Icc_right hsb)))
    fun x hxa hxs h0 ↦ hcrit x (mem_criticalPoints_iff_mfderiv_eq_zero.2 h0) ⟨hxa, hxs⟩
  have hφ (y : M) (t : ℝ) (hy : f y ∈ Icc a s) (ht : f y - t ∈ Icc a s) :
      f (φ t y) = f y - t :=
    φ.apply_eq_sub_of_mem_Icc hfc (fun x ↦ (hanti x).antitoneOn _) hφf
      (fun x t hx ht ↦ (hlt x t hx.ge (hx.trans_le has.le) ht).trans_eq hx) hy ht
  -- On the open submanifold `V = {a < f}` the sublevels of `f` are `f⁻¹(a, t]`.
  let V : TopologicalSpace.Opens M := ⟨{x | a < f x}, isOpen_lt continuous_const hfc⟩
  have hV (x : M) : x ∈ V ↔ a < f x := Iff.rfl
  have hfV : IsMorse I (f ∘ Subtype.val : V → ℝ) :=
    hf.comp_isLocalDiffeomorph isLocalDiffeomorph_subtype_val
  have hKV : IsCompact ((f ∘ Subtype.val : V → ℝ) ⁻¹' Icc s b) := by
    have hsub : f ⁻¹' Icc s b ⊆ range (Subtype.val : V → M) :=
      fun x hx ↦ ⟨⟨x, (hV x).2 (has.trans_le hx.1)⟩, rfl⟩
    rw [Subtype.isCompact_iff, preimage_comp, image_preimage_eq_of_subset hsub]
    exact hcompact.of_isClosed_subset (isClosed_Icc.preimage hfc)
      (preimage_mono (Icc_subset_Icc_left has.le))
  have hs : IsRegularValue I 𝓘(ℝ) f s := isRegularValue_iff_notMem_image_criticalPoints.2
    fun ⟨x, hx, hxs⟩ ↦ hcrit x hx ⟨hxs.symm ▸ has.le, hxs.le⟩
  -- The relative CW model of `f⁻¹(a, b]` over `f⁻¹(a, s]`, started from `f⁻¹(a)` itself, followed
  -- by the identification of `f⁻¹(a, b]` with the band.
  obtain ⟨h₀, hh₀⟩ := exists_homotopyEquiv_level_sublevel hfc φ has hφ V hV
  obtain ⟨k, hk⟩ := exists_homotopyEquiv_sublevel_band hfc φ has hsb hφ V hV
  let := relCWComplexSelf (univ : Set (f ⁻¹' {a})) isClosed_univ
  obtain ⟨X, _, _, ι, D', _, h', hD', hι, hh, e, -⟩ :=
    hfV.exists_relCWComplex_extension_homotopyEquiv_sublevel hsb hKV (hs.restrict V)
      (hb.restrict V) (f ⁻¹' {a}) univ h₀
  rw [image_univ] at hD'
  subst hD'
  -- The critical points of `f` on `V` with values in `(s, b]` are those of `f` in `(a, b]`.
  have hidx (y : V) (hy : (y : M) ∈ criticalPoints I f) :
      manifoldMorseIndex I (f ∘ Subtype.val) y = manifoldMorseIndex I f y :=
    (isLocalDiffeomorph_subtype_val (I := I) (n := ∞) y).manifoldMorseIndex_comp (by simp)
      (hf.contMDiff.contMDiffAt.of_le (by simp)) hy
  let c (i : ℕ) : ↥{y ∈ criticalPoints I (f ∘ Subtype.val : V → ℝ) ∩
        (f ∘ Subtype.val) ⁻¹' Ioc s b | manifoldMorseIndex I (f ∘ Subtype.val) y = i} ≃
      ↥{x ∈ criticalPoints I f ∩ f ⁻¹' Ioc a b | manifoldMorseIndex I f x = i} :=
    { toFun y := ⟨y.1, ⟨mem_criticalPoints_comp_subtypeVal.1 y.2.1.1,
        has.trans y.2.1.2.1, y.2.1.2.2⟩,
        (hidx _ (mem_criticalPoints_comp_subtypeVal.1 y.2.1.1)).symm.trans y.2.2⟩
      invFun x := ⟨⟨x.1, x.2.1.2.1⟩, ⟨mem_criticalPoints_comp_subtypeVal.2 x.2.1.1,
        lt_of_not_ge fun h ↦ hcrit x x.2.1.1 ⟨x.2.1.2.1.le, h⟩, x.2.1.2.2⟩,
        (hidx ⟨x.1, x.2.1.2.1⟩ x.2.1.1).trans x.2.2⟩
      left_inv y := rfl
      right_inv x := rfl }
  refine ⟨X, _, ‹_›, ι, ‹_›, h'.trans k, hι, fun x ↦ ?_,
    ⟨fun i ↦ (e i).trans ((Equiv.emptySum _ _).trans (c i))⟩⟩
  -- On the level `f⁻¹(a)` the push up and the push down cancel.
  have hx : ((h' (ι x) : V) : M) = φ (a - (a + s) / 2) x := (congrArg Subtype.val (hh x)).trans
    (hh₀ x)
  have hxa : f x = a := x.2
  have hm : f ((h' (ι x) : V) : M) = (a + s) / 2 := by
    rw [hx, hφ _ _ ⟨hxa.ge, by linarith⟩ ⟨by linarith, by linarith⟩, hxa]
    ring
  rw [ContinuousMap.HomotopyEquiv.trans_apply, hk _ hm, hx, ← Flow.map_add,
    show (a + s) / 2 - a + (a - (a + s) / 2) = 0 by ring, Flow.map_zero_apply]

/-- **The relative CW model of a regular cobordism relative to its outgoing boundary.** Let `f` be
a Morse function on a manifold of dimension `n`, and `a ≤ b` regular values of `f` with compact
band `f⁻¹[a, b]`. Then the band is homotopy equivalent to a CW complex `X` relative to a copy of
its outgoing boundary `f⁻¹(b)`, with one `m`-cell for each critical point of index `n - m` with
value in `[a, b)`: there are a closed embedding `j : f⁻¹(b) → X`, a relative CW structure on `X`
with base the image of `j`, and a homotopy equivalence `h : X ≃ₕ f⁻¹[a, b]` such that `h ∘ j` is
the inclusion `f⁻¹(b) ⊆ f⁻¹[a, b]`. This is the model of the same band for `-f`, relative to its
incoming boundary `(-f)⁻¹(-b) = f⁻¹(b)`. -/
theorem IsMorse.exists_relCWComplex_homotopyEquiv_upperBand (hf : IsMorse I f) {a b : ℝ}
    (hab : a ≤ b) (hcompact : IsCompact (f ⁻¹' Icc a b)) (ha : IsRegularValue I 𝓘(ℝ) f a)
    (hb : IsRegularValue I 𝓘(ℝ) f b) :
    ∃ (X : Type u) (_ : TopologicalSpace X) (_ : T2Space X) (j : C(f ⁻¹' {b}, X))
      (_ : RelCWComplex (univ : Set X) (range j)) (h : X ≃ₕ f ⁻¹' Icc a b),
      IsClosedEmbedding j ∧ (∀ x, (h (j x) : M) = x) ∧
      Nonempty (∀ m, cell (univ : Set X) m ≃ ↥{x ∈ criticalPoints I f ∩ f ⁻¹' Ico a b |
        manifoldMorseIndex I f x + m = Module.finrank ℝ E}) := by
  obtain ⟨X, _, _, j, C, h, hj, hh, ⟨e⟩⟩ := hf.neg.exists_relCWComplex_homotopyEquiv_band
    (neg_le_neg hab) (by rwa [preimage_neg_Icc_neg]) (isRegularValue_neg_iff.2 (by rwa [neg_neg]))
    (isRegularValue_neg_iff.2 (by rwa [neg_neg]))
  -- The outgoing boundary of the band is the incoming boundary of the band of `-f`.
  have hL : f ⁻¹' {b} = (-f) ⁻¹' {-b} := by
    ext
    simp
  let j' : C(f ⁻¹' {b}, X) := j.comp ⟨_, (Homeomorph.setCongr hL).continuous⟩
  have hr : range j = range j' := ((Homeomorph.setCongr hL).surjective.range_comp j).symm
  generalize hD : range j = D at C e
  obtain rfl : D = range j' := hD.symm.trans hr
  exact ⟨X, _, ‹_›, j', C,
    h.trans (Homeomorph.setCongr (preimage_neg_Icc_neg f a b)).toHomotopyEquiv,
    hj.comp (Homeomorph.setCongr hL).isClosedEmbedding, fun x ↦ hh _,
    ⟨fun m ↦ (e m).trans (Set.equivOfEq (hf.setOf_neg_band_eq a b m))⟩⟩

end TauCeti
