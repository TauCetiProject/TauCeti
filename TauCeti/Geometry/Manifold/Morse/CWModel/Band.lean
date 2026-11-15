/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.CWModel
import TauCeti.Dynamics.Flow.Homotopy
import TauCeti.Geometry.Manifold.Morse.LocalDiffeomorph
import TauCeti.Topology.Homotopy.DeformationRetract

/-!
# Relative CW models of regular cobordisms

Let `f` be a Morse function on a boundaryless manifold `M`, and let `a ≤ b` be regular values with
compact band `W = f⁻¹[a, b]`. Then `W` is a compact cobordism from the level `f⁻¹(a)` to the level
`f⁻¹(b)`, and it is homotopy equivalent to its incoming boundary with one `λ`-cell attached for
each critical point of index `λ` in the band
(`TauCeti.IsMorse.exists_relCWComplex_homotopyEquiv_band`): there are a finite CW complex `X`
relative to a closed copy of `f⁻¹(a)`, with one `λ`-cell for each critical point of index `λ` with
value in `(a, b]`, and a homotopy equivalence `X ≃ₕ W` which is the inclusion on `f⁻¹(a)`. Read
from the other end, `W` is the band of `-f` between `-b` and `-a`, whose critical points of index
`λ` are those of `f` of index `dim M - λ`. So `W` is also homotopy equivalent to its outgoing
boundary `f⁻¹(b)` with one `(dim M - λ)`-cell attached for each critical point of index `λ` with
value in `[a, b)` (`TauCeti.IsMorse.exists_relCWComplex_homotopyEquiv_upperBand`).

This is the band version of the relative CW model of a sublevel pair
(`TauCeti.IsMorse.exists_relCWComplex_homotopyEquiv_sublevel`), in which `M_b = {f ≤ b}` is built
from `M_a = {f ≤ a}`. Here the base is the level `f⁻¹(a)` itself, which is not a sublevel of `f`.
It becomes one after removing `{f ≤ a}`: on the open submanifold `U = {f > a}` the sublevel
`{x ∈ U | f x ≤ c}` is a collar `f⁻¹(a, c]` when `f⁻¹[a, c]` holds no critical point. Flowing at
unit speed between the levels of the collar `f⁻¹[a, c]` identifies `f⁻¹(a)` with the collar
`f⁻¹(a, c]` up to homotopy, by lifting the level to the middle level `m = (a + c) / 2`, and
identifies `U_b = f⁻¹(a, b]` with `W`, by a map which moves the levels in `(a, m]` down to `a` and
fixes the band above `c`. The relative CW model of `U_b` over `U_c` then gives the model of `W`
over `f⁻¹(a)`, with the cells of the critical points with value in `(c, b]`, which are all those
with value in `(a, b]`.

## Main results

* `TauCeti.IsMorse.exists_relCWComplex_homotopyEquiv_band`: **the relative CW model of a regular
  cobordism**, relative to its incoming boundary `f⁻¹(a)`.
* `TauCeti.IsMorse.exists_relCWComplex_homotopyEquiv_upperBand`: the relative CW model of a
  regular cobordism relative to its outgoing boundary `f⁻¹(b)`, with cells of complementary
  dimension.

## References

* J. Milnor, *Lectures on the h-cobordism theorem*, Princeton University Press, 1965, §3.
* R. L. Cohen, K. Iga and P. Norbury, *Topics in Morse Theory*, lecture notes, 2006,
  Theorem 5.7.
-/

public section

noncomputable section

open Set Topology Topology.RelCWComplex TopologicalSpace
open scoped Manifold ContDiff ContinuousMap

universe u

namespace TauCeti

variable {E H : Type*} {M : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [FiniteDimensional ℝ E]
  [I.Boundaryless] [IsManifold I ∞ M] [T2Space M] {f : M → ℝ}

/-- **Moving between the levels of a collar.** If the band `f⁻¹[a, c]` is compact and has no
critical points, there is a flow `φ` which carries each point `x` with `f x ≥ a` to the level
`s` in the time `f x - s`, for every `s ∈ [a, c]` when `f x ≤ c`, and trivially for `s = f x`. -/
private theorem exists_flow_apply_sub_eq (hf : ContMDiff I 𝓘(ℝ) ∞ f) {a c : ℝ}
    (hcompact : IsCompact (f ⁻¹' Icc a c))
    (hreg : ∀ x, a ≤ f x → f x ≤ c → mfderiv I 𝓘(ℝ) f x ≠ 0) :
    ∃ φ : Flow ℝ M, ∀ x s, a ≤ f x → (f x ≤ c → a ≤ s ∧ s ≤ c) → (c < f x → s = f x) →
      f (φ (f x - s) x) = s := by
  obtain ⟨φ, -, hanti, hlt, hφf⟩ := exists_flow_apply_eq_sub hf hcompact hreg
  refine ⟨φ, fun x s hxa hs hsx ↦ ?_⟩
  rcases le_or_gt (f x) c with hxc | hcx
  swap
  · rw [hsx hcx, sub_self, Flow.map_zero_apply]
  obtain ⟨has, hsc⟩ := hs hxc
  have hac : a ≤ c := hxa.trans hxc
  -- Flow down to the level `a`, then back up to the level `s`.
  have hy : f (φ (f x - a) x) = a := by
    rw [hφf x _ (by linarith) (by linarith) hxc]
    ring
  have h := φ.apply_neg_eq_add_of_apply_eq_sub hf.continuous (fun x ↦ (hanti x).antitoneOn _) hφf
    (fun x t hx ht ↦ (hlt x t hx.ge (hx.trans_le hac) ht).trans_eq hx) hy (t := s - a)
    (by linarith) (by linarith)
  have ht : -(s - a) + (f x - a) = f x - s := by ring
  rwa [← Flow.map_add, ht, add_sub_cancel] at h

omit [T2Space M] in
/-- **Moving back to the original level.** Let `φ` move the points of the collar `f⁻¹[a, c]`
between its levels at unit speed, as in `exists_flow_apply_sub_eq`, and let `J ⊆ [a, ∞)` be an
interval. Let `ℓ` map `J` into itself, mapping the levels of `J` in `[a, c]` into `[a, c]` and
fixing the levels above `c`. Then moving each point `x` of `f⁻¹ J` along `φ` to the level
`ℓ (f x)` is homotopic to the identity: at time `t` move it to the level
`t ℓ (f x) + (1 - t) f x`. -/
private theorem homotopic_id_of_apply_sub_eq (hf : Continuous f) {a c : ℝ} (φ : Flow ℝ M)
    (hφ : ∀ x s, a ≤ f x → (f x ≤ c → a ≤ s ∧ s ≤ c) → (c < f x → s = f x) →
      f (φ (f x - s) x) = s)
    {J : Set ℝ} (hJ : Convex ℝ J) (hJa : ∀ v ∈ J, a ≤ v) {ℓ : ℝ → ℝ} (hℓ : Continuous ℓ)
    (hℓJ : ∀ v ∈ J, ℓ v ∈ J) (hℓc : ∀ v ∈ J, v ≤ c → ℓ v ∈ Icc a c)
    (hℓ' : ∀ v ∈ J, c < v → ℓ v = v) (F : C(f ⁻¹' J, f ⁻¹' J))
    (hF : ∀ x, (F x : M) = φ (f x - ℓ (f x)) x) :
    F.Homotopic (ContinuousMap.id _) := by
  refine φ.homotopic_id_of_apply_mem (τ := fun x ↦ f x - ℓ (f x)) (by fun_prop)
    (fun x t ht₀ ht₁ ↦ ?_) F hF
  have hxa := hJa _ x.2
  have hlev (hxc : f x ≤ c) : t * ℓ (f x) + (1 - t) * f x ∈ Icc a c := by
    simpa using convex_Icc a c (hℓc _ x.2 hxc) (mem_Icc.2 ⟨hxa, hxc⟩) ht₀ (sub_nonneg.2 ht₁)
      (by ring)
  have h := hφ x (t * ℓ (f x) + (1 - t) * f x) hxa hlev fun hcx ↦ by rw [hℓ' _ x.2 hcx]; ring
  rw [show f x - (t * ℓ (f x) + (1 - t) * f x) = t * (f x - ℓ (f x)) by ring] at h
  rw [mem_preimage, h]
  simpa using hJ (hℓJ _ x.2) x.2 ht₀ (sub_nonneg.2 ht₁) (by ring)

omit [T2Space M] in
/-- **A level is a model of the collar above it.** Let `φ` move the points of the collar
`f⁻¹[a, c]` between its levels at unit speed, as in `exists_flow_apply_sub_eq`. Lifting the level
`f⁻¹(a)` to the middle level `m = (a + c) / 2` along `φ` is a homotopy equivalence
`f⁻¹(a) ≃ₕ f⁻¹(a, c]`, and flowing back down from the level `m` recovers the starting point. -/
private theorem exists_homotopyEquiv_level_collar (hf : Continuous f) {a c : ℝ} (hac : a < c)
    (φ : Flow ℝ M) (hφ : ∀ x s, a ≤ f x → (f x ≤ c → a ≤ s ∧ s ≤ c) → (c < f x → s = f x) →
      f (φ (f x - s) x) = s) :
    ∃ h : f ⁻¹' {a} ≃ₕ f ⁻¹' Ioc a c,
      ∀ y, f (h y) = (a + c) / 2 ∧ φ (f (h y) - a) (h y) = y := by
  set m := (a + c) / 2 with hm
  have ham : a < m := by linarith
  have hmc : m < c := by linarith
  have hσ (y : f ⁻¹' {a}) : f (φ (a - m) y) = m := by
    have hy : f y = a := y.2
    have h := hφ y m hy.ge (fun _ ↦ ⟨ham.le, hmc.le⟩) fun h ↦ (hac.not_gt (hy ▸ h)).elim
    rwa [hy] at h
  have hρ (x : f ⁻¹' Ioc a c) : f (φ (f x - a) x) = a :=
    hφ x a x.2.1.le (fun _ ↦ ⟨le_rfl, hac.le⟩) fun h ↦ (h.not_ge x.2.2).elim
  have hσmem (y : f ⁻¹' {a}) : φ (a - m) y ∈ f ⁻¹' Ioc a c := by
    rw [mem_preimage, hσ]
    exact mem_Ioc.2 ⟨ham, hmc.le⟩
  let σ : C(f ⁻¹' {a}, f ⁻¹' Ioc a c) :=
    ⟨fun y ↦ ⟨φ (a - m) y, hσmem y⟩,
      (φ.continuous continuous_const continuous_subtype_val).subtype_mk hσmem⟩
  let ρ : C(f ⁻¹' Ioc a c, f ⁻¹' {a}) :=
    ⟨fun x ↦ ⟨φ (f x - a) x, hρ x⟩, (φ.continuous ((hf.comp continuous_subtype_val).sub
      continuous_const) continuous_subtype_val).subtype_mk hρ⟩
  have hρσ (y : f ⁻¹' {a}) : φ (f (φ (a - m) y) - a) (φ (a - m) y) = y := by
    rw [hσ, ← Flow.map_add, sub_add_sub_cancel, sub_self, Flow.map_zero_apply]
  -- `σ ∘ ρ` moves each point of `f⁻¹(a, c]` to the level `m`.
  have hσρ : (σ.comp ρ).Homotopic (ContinuousMap.id _) := by
    refine homotopic_id_of_apply_sub_eq hf φ hφ (convex_Ioc a c) (fun v hv ↦ hv.1.le)
      continuous_const (fun _ _ ↦ mem_Ioc.2 ⟨ham, hmc.le⟩) (fun _ _ _ ↦ mem_Icc.2 ⟨ham.le, hmc.le⟩)
      (fun v hv hcv ↦ (hcv.not_ge hv.2).elim) _ fun x ↦ ?_
    simp only [ContinuousMap.comp_apply, ContinuousMap.coe_mk, σ, ρ]
    rw [← Flow.map_add, sub_add_sub_cancel']
  refine ⟨.ofDeformationRetraction σ ρ (fun y ↦ Subtype.ext (hρσ y)) hσρ, fun y ↦ ?_⟩
  rw [ContinuousMap.HomotopyEquiv.ofDeformationRetraction_apply]
  exact ⟨hσ y, hρσ y⟩

/-- Two reparametrizations of the levels of a collar `[a, c]`, both fixing the levels above `c`:
`ψ` lowers the levels in `[a, (a + c) / 2]` to `a`, and `μ` raises the levels in `[a, c]` into
`(a, c]`. -/
private theorem exists_collar_levels {a c : ℝ} (hac : a < c) :
    ∃ ψ μ : ℝ → ℝ, Continuous ψ ∧ Continuous μ ∧ (∀ v, a ≤ v → a ≤ ψ v ∧ ψ v ≤ v) ∧
      (∀ v, c < v → ψ v = v) ∧ ψ ((a + c) / 2) = a ∧
      (∀ v, a ≤ v → v ≤ μ v ∧ a < μ v ∧ (v ≤ c → μ v ≤ c)) ∧ (∀ v, μ v ≤ max v c) ∧
      (∀ v, c < v → μ v = v) := by
  refine ⟨fun v ↦ max a (min v (2 * v - c)), fun v ↦ max v ((v + c) / 2), by fun_prop,
    by fun_prop, fun v hav ↦ ⟨le_max_left _ _, max_le hav (min_le_left _ _)⟩, fun v hcv ↦ ?_, ?_,
    fun v hav ↦ ⟨le_max_left _ _, lt_max_of_lt_right (by linarith),
      fun hvc ↦ max_le hvc (by linarith)⟩,
    fun v ↦ max_le (le_max_left _ _) (by linarith [le_max_left v c, le_max_right v c]),
    fun v hcv ↦ max_eq_left (by linarith)⟩
  · beta_reduce
    rw [min_eq_left (by linarith), max_eq_right (by linarith)]
  · beta_reduce
    rw [show 2 * ((a + c) / 2) - c = a by ring, min_eq_right (by linarith), max_self]

omit [T2Space M] in
/-- **The band is a model of the band above its lower level.** Let `φ` move the points of the
collar `f⁻¹[a, c]` between its levels at unit speed, as in `exists_flow_apply_sub_eq`, with
`c ≤ b`. Then `f⁻¹(a, b] ≃ₕ f⁻¹[a, b]` by a homotopy equivalence which fixes `f⁻¹(c, b]` and
moves the points of the middle level `f⁻¹(m)`, `m = (a + c) / 2`, down to the level `a` along
`φ`. -/
private theorem exists_homotopyEquiv_band_collar (hf : Continuous f) {a b c : ℝ} (hac : a < c)
    (hcb : c ≤ b) (φ : Flow ℝ M) (hφ : ∀ x s, a ≤ f x → (f x ≤ c → a ≤ s ∧ s ≤ c) →
      (c < f x → s = f x) → f (φ (f x - s) x) = s) :
    ∃ h : f ⁻¹' Ioc a b ≃ₕ f ⁻¹' Icc a b,
      ∀ x : f ⁻¹' Ioc a b, f x = (a + c) / 2 → (h x : M) = φ (f x - a) x := by
  obtain ⟨ψ, μ, hψc, hμc, hψ, hψ', hψm, hμ, hμle, hμ'⟩ := exists_collar_levels hac
  have hdrop (x : f ⁻¹' Ioc a b) : f (φ (f x - ψ (f x)) x) = ψ (f x) :=
    hφ x _ x.2.1.le (fun h ↦ ⟨(hψ _ x.2.1.le).1, (hψ _ x.2.1.le).2.trans h⟩) (hψ' _)
  have hlift (x : f ⁻¹' Icc a b) : f (φ (f x - μ (f x)) x) = μ (f x) :=
    hφ x _ x.2.1 (fun h ↦ ⟨(hμ _ x.2.1).2.1.le, (hμ _ x.2.1).2.2 h⟩) (hμ' _)
  have hdropmem (x : f ⁻¹' Ioc a b) : φ (f x - ψ (f x)) x ∈ f ⁻¹' Icc a b := by
    rw [mem_preimage, hdrop]
    exact mem_Icc.2 ⟨(hψ _ x.2.1.le).1, (hψ _ x.2.1.le).2.trans x.2.2⟩
  have hliftmem (x : f ⁻¹' Icc a b) : φ (f x - μ (f x)) x ∈ f ⁻¹' Ioc a b := by
    rw [mem_preimage, hlift]
    exact mem_Ioc.2 ⟨(hμ _ x.2.1).2.1, (hμle _).trans (max_le x.2.2 hcb)⟩
  let drop : C(f ⁻¹' Ioc a b, f ⁻¹' Icc a b) :=
    ⟨fun x ↦ ⟨φ (f x - ψ (f x)) x, hdropmem x⟩,
      (φ.continuous (by fun_prop) continuous_subtype_val).subtype_mk hdropmem⟩
  let lift : C(f ⁻¹' Icc a b, f ⁻¹' Ioc a b) :=
    ⟨fun x ↦ ⟨φ (f x - μ (f x)) x, hliftmem x⟩,
      (φ.continuous (by fun_prop) continuous_subtype_val).subtype_mk hliftmem⟩
  refine ⟨⟨drop, lift, ?_, ?_⟩, fun x hx ↦ ?_⟩
  · -- `lift ∘ drop` moves each point to the level `μ (ψ (f x))`.
    refine homotopic_id_of_apply_sub_eq hf φ hφ (convex_Ioc a b) (fun v hv ↦ hv.1.le)
      (by fun_prop) (fun v hv ↦ mem_Ioc.2 ⟨(hμ _ (hψ v hv.1.le).1).2.1,
        (hμle _).trans (max_le ((hψ v hv.1.le).2.trans hv.2) hcb)⟩)
      (fun v hv hvc ↦ mem_Icc.2 ⟨(hμ _ (hψ v hv.1.le).1).2.1.le,
        (hμ _ (hψ v hv.1.le).1).2.2 ((hψ v hv.1.le).2.trans hvc)⟩)
      (fun v _ hcv ↦ by rw [hψ' _ hcv, hμ' _ hcv]) _ fun x ↦ ?_
    simp only [ContinuousMap.comp_apply, ContinuousMap.coe_mk, drop, lift]
    rw [hdrop, ← Flow.map_add, sub_add_sub_cancel']
  · -- `drop ∘ lift` moves each point to the level `ψ (μ (f x))`.
    refine homotopic_id_of_apply_sub_eq hf φ hφ (convex_Icc a b) (fun v hv ↦ hv.1)
      (by fun_prop) (fun v hv ↦ mem_Icc.2 ⟨(hψ _ (hμ v hv.1).2.1.le).1,
        (hψ _ (hμ v hv.1).2.1.le).2.trans ((hμle _).trans (max_le hv.2 hcb))⟩)
      (fun v hv hvc ↦ mem_Icc.2 ⟨(hψ _ (hμ v hv.1).2.1.le).1,
        (hψ _ (hμ v hv.1).2.1.le).2.trans ((hμ v hv.1).2.2 hvc)⟩)
      (fun v _ hcv ↦ by rw [hμ' _ hcv, hψ' _ hcv]) _ fun x ↦ ?_
    simp only [ContinuousMap.comp_apply, ContinuousMap.coe_mk, drop, lift]
    rw [hlift, ← Flow.map_add, sub_add_sub_cancel']
  · simp only [ContinuousMap.coe_mk, drop, hx, hψm]

omit [FiniteDimensional ℝ E] [T2Space M] in
/-- On the open submanifold `U = {f > a}`, the critical points of the restriction of `f` with
value in `(c, b]` are the critical points of `f` with value in `(a, b]`, with the same indices,
when the collar `f⁻¹[a, c]` holds no critical point. -/
private theorem IsMorse.nonempty_equiv_criticalPoints_comp_subtypeVal (hf : IsMorse I f)
    {a b c : ℝ} (hac : a < c) (hreg : ∀ x, a ≤ f x → f x ≤ c → mfderiv I 𝓘(ℝ) f x ≠ 0)
    {U : Opens M} (hU : ∀ x, x ∈ U ↔ a < f x) (m : ℕ) :
    Nonempty (↥{x ∈ criticalPoints I (f ∘ Subtype.val : U → ℝ) ∩ (f ∘ Subtype.val) ⁻¹' Ioc c b |
        manifoldMorseIndex I (f ∘ Subtype.val : U → ℝ) x = m} ≃
      ↥{x ∈ criticalPoints I f ∩ f ⁻¹' Ioc a b | manifoldMorseIndex I f x = m}) := by
  have hidx (x : U) (hx : (x : M) ∈ criticalPoints I f) :
      manifoldMorseIndex I (f ∘ Subtype.val) x = manifoldMorseIndex I f x :=
    (isLocalDiffeomorph_subtype_val (n := ∞) x).manifoldMorseIndex_comp (by simp)
      (hf.contMDiff.contMDiffAt.of_le (by simp)) hx
  exact ⟨{ toFun x := ⟨x.1, ⟨mem_criticalPoints_comp_subtypeVal.1 x.2.1.1,
              hac.trans x.2.1.2.1, x.2.1.2.2⟩,
            (hidx x.1 (mem_criticalPoints_comp_subtypeVal.1 x.2.1.1)).symm.trans x.2.2⟩
           invFun x := ⟨⟨x.1, (hU x).2 x.2.1.2.1⟩, ⟨mem_criticalPoints_comp_subtypeVal.2 x.2.1.1,
              lt_of_not_ge fun h ↦ hreg x x.2.1.2.1.le h
                (mem_criticalPoints_iff_mfderiv_eq_zero.1 x.2.1.1), x.2.1.2.2⟩,
            (hidx _ x.2.1.1).trans x.2.2⟩
           left_inv _ := rfl
           right_inv _ := rfl }⟩

/-- The relative CW model of a band `f⁻¹[a, b]` of positive width over its lower level, without the
finiteness of the model. The level `f⁻¹(a)` models the sublevel `f⁻¹(a, c]` of the open
submanifold `{f > a}` above a collar `f⁻¹[a, c]` without critical points, the relative CW model of
this submanifold extends it to a model of `f⁻¹(a, b]`, and `f⁻¹(a, b]` is a model of
`f⁻¹[a, b]`. -/
private theorem IsMorse.exists_relCWComplex_homotopyEquiv_band_of_lt (hf : IsMorse I f)
    {a b : ℝ} (hab : a < b) (hcompact : IsCompact (f ⁻¹' Icc a b))
    (ha : IsRegularValue I 𝓘(ℝ) f a) (hb : IsRegularValue I 𝓘(ℝ) f b) :
    ∃ (X : Type u) (_ : TopologicalSpace X) (_ : T2Space X) (j : C(f ⁻¹' {a}, X))
      (_ : RelCWComplex (univ : Set X) (range j)) (h : X ≃ₕ f ⁻¹' Icc a b),
      IsClosedEmbedding j ∧ (∀ x, (h (j x) : M) = x) ∧ Nonempty (∀ m, cell (univ : Set X) m ≃
        ↥{x ∈ criticalPoints I f ∩ f ⁻¹' Ioc a b | manifoldMorseIndex I f x = m}) := by
  have hfc : Continuous f := hf.contMDiff.continuous
  -- A collar `f⁻¹[a, c]` without critical points, and a flow moving between its levels.
  obtain ⟨c, ⟨hac, hcb⟩, hcollar, hreg⟩ :=
    exists_mem_Ioc_isCompact_forall_mfderiv_ne_zero (hf.contMDiff.of_le (by simp)) hab hcompact ha
  obtain ⟨φ, hφ⟩ := exists_flow_apply_sub_eq hf.contMDiff hcollar hreg
  -- On the open submanifold `U = {f > a}`, the restriction `g` of `f` is a Morse function whose
  -- sublevels `{g ≤ t}` are the sets `f⁻¹(a, t]`.
  let U : Opens M := ⟨f ⁻¹' Ioi a, isOpen_Ioi.preimage hfc⟩
  let g : U → ℝ := f ∘ Subtype.val
  have hg : IsMorse I g := hf.comp_isLocalDiffeomorph isLocalDiffeomorph_subtype_val
  let e (t : ℝ) : {x : U | g x ≤ t} ≃ₜ f ⁻¹' Ioc a t :=
    { toFun x := ⟨x.1.1, x.1.2, x.2⟩
      invFun y := ⟨⟨y.1, y.2.1⟩, y.2.2⟩
      left_inv _ := rfl
      right_inv _ := rfl
      continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
      continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _ }
  have hc : IsRegularValue I 𝓘(ℝ) f c := isRegularValue_iff_notMem_image_criticalPoints.2
    fun ⟨x, hx, hxc⟩ ↦ hreg x (by linarith) hxc.le (mem_criticalPoints_iff_mfderiv_eq_zero.1 hx)
  have hgcompact : IsCompact (g ⁻¹' Icc c b) := by
    refine IsInducing.subtypeVal.isCompact_comp_preimage_Icc (fun x hx ↦ ?_)
      (hcompact.of_isClosed_subset (isClosed_Icc.preimage hfc)
        (preimage_mono (Icc_subset_Icc_left hac.le)))
    have hxU : ¬ a < f x := fun h ↦ hx ⟨⟨x, h⟩, rfl⟩
    linarith
  -- The level `f⁻¹(a)` models the sublevel `{g ≤ c}`; extend this model across `f⁻¹[c, b]`.
  obtain ⟨h₁, hh₁⟩ := exists_homotopyEquiv_level_collar hfc hac φ hφ
  let := relCWComplexSelf (univ : Set (f ⁻¹' {a})) isClosed_univ
  obtain ⟨X, _, _, j, D, _, h', hD, hj, -, hh', e', -⟩ :=
    hg.exists_relCWComplex_extension_homotopyEquiv_sublevel hcb hgcompact (hc.restrict U)
      (hb.restrict U) (f ⁻¹' {a}) univ (h₁.trans (e c).symm.toHomotopyEquiv)
  rw [image_univ] at hD
  subst hD
  -- The model of `{g ≤ b} = f⁻¹(a, b]` is one of `f⁻¹[a, b]`, still the inclusion on `f⁻¹(a)`.
  obtain ⟨h₂, hh₂⟩ := exists_homotopyEquiv_band_collar hfc hac hcb φ hφ
  refine ⟨X, _, ‹_›, j, ‹_›, (h'.trans (e b).toHomotopyEquiv).trans h₂, hj, fun y ↦ ?_,
    ⟨fun m ↦ (e' m).trans ((Equiv.emptySum _ _).trans
      (hf.nonempty_equiv_criticalPoints_comp_subtypeVal hac hreg (fun _ ↦ Iff.rfl) m).some)⟩⟩
  have hy : ((e b (h' (j y)) : f ⁻¹' Ioc a b) : M) = h₁ y := congrArg Subtype.val (hh' y)
  rw [ContinuousMap.HomotopyEquiv.trans_apply, ContinuousMap.HomotopyEquiv.trans_apply,
    Homeomorph.coe_toHomotopyEquiv, hh₂ _ (hy ▸ (hh₁ y).1), hy, (hh₁ y).2]

/-- **The relative CW model of a regular cobordism** (Milnor, *Lectures on the h-cobordism
theorem*, §3). Let `f` be a Morse function and `a ≤ b` regular values of `f` with compact band
`W = f⁻¹[a, b]`. Then `W` is homotopy equivalent to its incoming boundary `f⁻¹(a)` with one `m`-cell
attached for each critical point of index `m` with value in `(a, b]`: there are a closed embedding
`j : f⁻¹(a) → X`, a finite CW structure on `X` relative to the image of `j` whose `m`-cells
correspond to these critical points, and a homotopy equivalence `h : X ≃ₕ W` such that `h ∘ j` is
the inclusion `f⁻¹(a) ⊆ W`. -/
theorem IsMorse.exists_relCWComplex_homotopyEquiv_band (hf : IsMorse I f) {a b : ℝ} (hab : a ≤ b)
    (hcompact : IsCompact (f ⁻¹' Icc a b)) (ha : IsRegularValue I 𝓘(ℝ) f a)
    (hb : IsRegularValue I 𝓘(ℝ) f b) :
    ∃ (X : Type u) (_ : TopologicalSpace X) (_ : T2Space X) (j : C(f ⁻¹' {a}, X))
      (_ : RelCWComplex (univ : Set X) (range j)) (h : X ≃ₕ f ⁻¹' Icc a b),
      IsClosedEmbedding j ∧ RelCWComplex.Finite (univ : Set X) ∧ (∀ x, (h (j x) : M) = x) ∧
      Nonempty (∀ m, cell (univ : Set X) m ≃
        ↥{x ∈ criticalPoints I f ∩ f ⁻¹' Ioc a b | manifoldMorseIndex I f x = m}) := by
  -- Only finitely many critical points lie in the compact band, so a model with one cell for each
  -- of them is finite.
  have hS : (criticalPoints I f ∩ f ⁻¹' Ioc a b).Finite :=
    (hf.finite_criticalPoints_inter hcompact).subset
      (inter_subset_inter_right _ (preimage_mono Ioc_subset_Icc_self))
  have := finite_sigma_criticalPoints_inter hS
  suffices ∃ (X : Type u) (_ : TopologicalSpace X) (_ : T2Space X) (j : C(f ⁻¹' {a}, X))
      (_ : RelCWComplex (univ : Set X) (range j)) (h : X ≃ₕ f ⁻¹' Icc a b),
      IsClosedEmbedding j ∧ (∀ x, (h (j x) : M) = x) ∧ Nonempty (∀ m, cell (univ : Set X) m ≃
        ↥{x ∈ criticalPoints I f ∩ f ⁻¹' Ioc a b | manifoldMorseIndex I f x = m}) by
    obtain ⟨X, _, _, j, _, h, hj, hh, ⟨e⟩⟩ := this
    exact ⟨X, _, ‹_›, j, ‹_›, h, hj,
      RelCWComplex.finite_of_finite_cells (.of_equiv _ (Equiv.sigmaCongrRight e).symm), hh, ⟨e⟩⟩
  rcases hab.eq_or_lt with rfl | hlt
  · -- A band of width zero is its level, with no cells.
    obtain ⟨_, hcell⟩ : ∃ _ : RelCWComplex (univ : Set (f ⁻¹' {a}))
        (range (ContinuousMap.id (f ⁻¹' {a}))), ∀ m, IsEmpty (cell (univ : Set (f ⁻¹' {a})) m) := by
      rw [ContinuousMap.coe_id, range_id]
      exact ⟨relCWComplexSelf univ isClosed_univ, isEmpty_cell_relCWComplexSelf isClosed_univ⟩
    have (m : ℕ) : IsEmpty ↥{x ∈ criticalPoints I f ∩ f ⁻¹' Ioc a a |
        manifoldMorseIndex I f x = m} := ⟨fun x ↦ by simpa using x.2.1.2⟩
    exact ⟨f ⁻¹' {a}, _, inferInstance, .id _, ‹_›,
      (Homeomorph.setCongr (by rw [Icc_self])).toHomotopyEquiv, .id, fun x ↦ rfl,
      ⟨fun m ↦ Equiv.equivOfIsEmpty _ _⟩⟩
  exact hf.exists_relCWComplex_homotopyEquiv_band_of_lt hlt hcompact ha hb

/-- **The relative CW model of a regular cobordism, from its outgoing boundary.** Let `f` be a
Morse function on a manifold of dimension `n`, and `a ≤ b` regular values of `f` with compact band
`W = f⁻¹[a, b]`. Then `W` is homotopy equivalent to its outgoing boundary `f⁻¹(b)` with one
`(n - λ)`-cell attached for each critical point of index `λ` with value in `[a, b)`: there are a
closed embedding `j : f⁻¹(b) → X`, a finite CW structure on `X` relative to the image of `j` whose
`m`-cells correspond to the critical points with value in `[a, b)` and index `n - m`, and a
homotopy equivalence `h : X ≃ₕ W` such that `h ∘ j` is the inclusion `f⁻¹(b) ⊆ W`. -/
theorem IsMorse.exists_relCWComplex_homotopyEquiv_upperBand (hf : IsMorse I f) {a b : ℝ}
    (hab : a ≤ b) (hcompact : IsCompact (f ⁻¹' Icc a b)) (ha : IsRegularValue I 𝓘(ℝ) f a)
    (hb : IsRegularValue I 𝓘(ℝ) f b) :
    ∃ (X : Type u) (_ : TopologicalSpace X) (_ : T2Space X) (j : C(f ⁻¹' {b}, X))
      (_ : RelCWComplex (univ : Set X) (range j)) (h : X ≃ₕ f ⁻¹' Icc a b),
      IsClosedEmbedding j ∧ RelCWComplex.Finite (univ : Set X) ∧ (∀ x, (h (j x) : M) = x) ∧
      Nonempty (∀ m, cell (univ : Set X) m ≃ ↥{x ∈ criticalPoints I f ∩ f ⁻¹' Ico a b |
        manifoldMorseIndex I f x + m = Module.finrank ℝ E}) := by
  -- This is the model of the band `(-f)⁻¹[-b, -a]` relative to its lower level `(-f)⁻¹(-b)`.
  have h := hf.neg.exists_relCWComplex_homotopyEquiv_band (neg_le_neg hab)
    (by rwa [preimage_neg_Icc_neg]) (isRegularValue_neg_iff.2 (by rwa [neg_neg]))
    (isRegularValue_neg_iff.2 (by rwa [neg_neg]))
  have hlevel : (-f) ⁻¹' {-b} = f ⁻¹' {b} := by
    ext x
    simp
  rw [preimage_neg_Icc_neg, hlevel] at h
  obtain ⟨X, _, _, j, _, h, hj, hfin, hh, ⟨e⟩⟩ := h
  exact ⟨X, _, ‹_›, j, ‹_›, h, hj, hfin, hh,
    ⟨fun m ↦ (e m).trans (Set.equivOfEq (hf.setOf_neg_band_eq a b m))⟩⟩

end TauCeti
