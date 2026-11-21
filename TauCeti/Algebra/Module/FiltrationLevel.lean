/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Submodule.Map
public import Mathlib.Data.EReal.Operations
public import Mathlib.Topology.DiscreteSubset
public import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

/-!
# The filtration level of an element of a filtered module

Let `V : ℝ → Submodule R M` be a family of submodules of `M`, typically an increasing filtration
by sublevels of a real-valued function such as an action functional. The **filtration level** of
`x : M` is

`ℓ(x) = inf {a | x ∈ V a} ∈ [-∞, +∞]`

(`TauCeti.filtrationLevel`), with the convention that `ℓ(x) = +∞` when `x` lies in no `V a`. When
`V a` is the image in the homology of a complex of the homology of its action sublevel `{𝒜 ≤ a}`,
the filtration level of a homology class `σ` is the **spectral invariant** `ρ(σ)` of Viterbo,
Schwarz and Oh, the smallest action level at which `σ` appears.

This file develops the properties of filtration levels that hold for every filtered module, and
which are the algebraic part of the properties of spectral invariants.

* **Valuation.** For every family, `ℓ(0) = -∞`, `ℓ(r • x) ≤ ℓ(x)` and `ℓ(-x) = ℓ(x)`. For an
  increasing filtration, `ℓ(x + y) ≤ max ℓ(x) ℓ(y)`, with equality `ℓ(x + y) = ℓ(x)` when
  `ℓ(y) < ℓ(x)`.
* **Filtered maps.** If a linear map `f` sends `V a` into `W (a + δ)` for every `a`, then
  `ℓ_W(f x) ≤ ℓ_V(x) + δ` (`TauCeti.filtrationLevel_map_le_add`). For continuation maps of Floer
  complexes, whose action shift is bounded by a Hofer-type norm of the change of Hamiltonian,
  this gives the Lipschitz continuity of spectral invariants; maps with `δ = 0`, such as monotone
  continuation maps, do not increase the filtration level.
* **Spectrality.** Suppose that the filtration changes only at the points of a closed set `S`:
  `V b ≤ V a` whenever `a ≤ b` and `[a, b]` does not meet `S`. Then every finite filtration level
  belongs to `S` (`TauCeti.filtrationLevel_mem_of_isClosed`). For a Floer complex `S` is the action
  spectrum, so the spectral invariant of a nonzero class is the action of a periodic orbit. If
  moreover `S` is closed and discrete, and `V b ≤ V a` already when `(a, b]` does not meet `S`, as
  for the sublevels `{𝒜 ≤ a}`, then the infimum defining a finite level is attained
  (`TauCeti.mem_of_filtrationLevel_eq`).

## Main definitions

* `TauCeti.filtrationLevel V x`: the infimum of the indices `a` with `x ∈ V a`, in `EReal`.

## Main results

* `TauCeti.filtrationLevel_add_le`, `TauCeti.filtrationLevel_add_eq_of_lt`: the
  non-Archimedean triangle inequality and its equality case.
* `TauCeti.filtrationLevel_map_le_add`: filtered maps with shift `δ` raise levels by at most `δ`.
* `TauCeti.filtrationLevel_mem_of_isClosed`, `TauCeti.exists_mem_filtrationLevel_eq`:
  spectrality.
* `TauCeti.mem_of_filtrationLevel_eq`: a finite level is attained for a closed discrete spectrum.

## References

* M. Usher, *Spectral numbers in Floer theories*, Compositio Math. 144 (2008), 1581–1592.
* M. Schwarz, *On the action spectrum for closed symplectically aspherical manifolds*,
  Pacific J. Math. 193 (2000), 419–461.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §5.1.
-/

public section

open Filter Set Topology

namespace TauCeti

section Semiring

variable {R M N : Type*} [Semiring R] [AddCommMonoid M] [AddCommMonoid N] [Module R M]
  [Module R N] {V : ℝ → Submodule R M} {W : ℝ → Submodule R N} {x : M} {a : ℝ}

/-- The **filtration level** of `x` for a real-indexed family of submodules `V`: the infimum, in
`EReal`, of the indices `a` with `x ∈ V a`. It is `⊤` when `x` lies in no `V a`. For the images in
homology of the action sublevels of a Floer complex, this is the spectral invariant of a class. -/
noncomputable def filtrationLevel (V : ℝ → Submodule R M) (x : M) : EReal :=
  ⨅ (a : ℝ) (_ : x ∈ V a), (a : EReal)

theorem filtrationLevel_le (h : x ∈ V a) : filtrationLevel V x ≤ a :=
  iInf₂_le a h

theorem le_filtrationLevel_iff {c : EReal} :
    c ≤ filtrationLevel V x ↔ ∀ a, x ∈ V a → c ≤ a :=
  le_iInf₂_iff

theorem filtrationLevel_lt_iff {c : EReal} :
    filtrationLevel V x < c ↔ ∃ a, x ∈ V a ∧ (a : EReal) < c := by
  simp [filtrationLevel, iInf_lt_iff]

@[simp]
theorem filtrationLevel_eq_top_iff : filtrationLevel V x = ⊤ ↔ ∀ a, x ∉ V a := by
  simp [filtrationLevel]

theorem filtrationLevel_lt_top_iff : filtrationLevel V x < ⊤ ↔ ∃ a, x ∈ V a := by
  simp [filtrationLevel_lt_iff]

theorem filtrationLevel_eq_bot_of_forall_mem (h : ∀ a, x ∈ V a) : filtrationLevel V x = ⊥ :=
  (EReal.eq_bot_iff_forall_lt _).mpr fun a ↦
    (filtrationLevel_le (h (a - 1))).trans_lt (EReal.coe_lt_coe_iff.mpr (sub_one_lt a))

@[simp]
theorem filtrationLevel_zero : filtrationLevel V 0 = ⊥ :=
  filtrationLevel_eq_bot_of_forall_mem fun a ↦ (V a).zero_mem

theorem filtrationLevel_le_of_eq_top (h : V a = ⊤) : filtrationLevel V x ≤ a :=
  filtrationLevel_le (h ▸ Submodule.mem_top)

theorem filtrationLevel_smul_le (r : R) (x : M) :
    filtrationLevel V (r • x) ≤ filtrationLevel V x :=
  le_filtrationLevel_iff.mpr fun _ ha ↦ filtrationLevel_le ((V _).smul_mem r ha)

/-- If a linear map sends `V a` into `W (a + δ)` for every `a`, it raises filtration levels by at
most `δ`. -/
theorem filtrationLevel_map_le_add (f : M →ₗ[R] N) (δ : ℝ)
    (hf : ∀ a, (V a).map f ≤ W (a + δ)) (x : M) :
    filtrationLevel W (f x) ≤ filtrationLevel V x + δ := by
  refine EReal.le_of_forall_lt_iff_le.mp fun z hz ↦ ?_
  have hz' : filtrationLevel V x < ((z - δ : ℝ) : EReal) := by
    rw [EReal.coe_sub, EReal.lt_sub_iff_add_lt (Or.inl (EReal.coe_ne_bot δ))
      (Or.inl (EReal.coe_ne_top δ))]
    exact hz
  obtain ⟨a, hxa, ha⟩ := filtrationLevel_lt_iff.mp hz'
  refine (filtrationLevel_le (hf a (Submodule.mem_map_of_mem hxa))).trans ?_
  rw [EReal.coe_le_coe_iff]
  linarith [EReal.coe_lt_coe_iff.mp ha]

/-- A linear map sending `V a` into `W a` for every `a` does not increase filtration levels. -/
theorem filtrationLevel_map_le (f : M →ₗ[R] N) (hf : ∀ a, (V a).map f ≤ W a) (x : M) :
    filtrationLevel W (f x) ≤ filtrationLevel V x := by
  simpa using filtrationLevel_map_le_add f 0 (by simpa using hf) x

/-- **Spectrality.** If the filtration only changes at the points of a closed set `S`, in the
sense that `V b ≤ V a` whenever `a ≤ b` and `[a, b]` does not meet `S`, then every finite
filtration level lies in `S`. -/
theorem filtrationLevel_mem_of_isClosed {S : Set ℝ} (hS : IsClosed S)
    (hVS : ∀ a b, a ≤ b → Disjoint S (Icc a b) → V b ≤ V a) {r : ℝ}
    (hr : filtrationLevel V x = r) : r ∈ S := by
  by_contra hrS
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hS.isOpen_compl r hrS
  obtain ⟨b, hxb, hb⟩ := filtrationLevel_lt_iff.mp
    (hr.trans_lt (EReal.coe_lt_coe_iff.mpr (lt_add_of_pos_right r (half_pos hε))))
  have hb' := EReal.coe_lt_coe_iff.mp hb
  have hrb : r ≤ b := EReal.coe_le_coe_iff.mp (hr ▸ filtrationLevel_le hxb)
  have hdisj : Disjoint S (Icc (r - ε / 2) b) := by
    refine Set.disjoint_left.mpr fun t htS ht ↦ hball ?_ htS
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    constructor <;> linarith [ht.1, ht.2]
  have hle := filtrationLevel_le (hVS _ _ (by linarith) hdisj hxb)
  rw [hr, EReal.coe_le_coe_iff] at hle
  linarith

/-- If the filtration only changes at the points of a closed discrete set `S`, in the sense that
`V b ≤ V a` whenever `a ≤ b` and `(a, b]` does not meet `S`, as for the sublevel sets of a
function with values in `S`, then a finite filtration level is attained. -/
theorem mem_of_filtrationLevel_eq {S : Set ℝ} (hS : Sᶜ ∈ codiscrete ℝ)
    (hVS : ∀ a b, a ≤ b → Disjoint S (Ioc a b) → V b ≤ V a) {r : ℝ}
    (hr : filtrationLevel V x = r) : x ∈ V r := by
  obtain ⟨ε, hε, hball⟩ :=
    Metric.mem_nhdsWithin_iff.mp (mem_codiscrete_iff_forall_mem_nhdsNE.mp hS r)
  obtain ⟨b, hxb, hb⟩ := filtrationLevel_lt_iff.mp
    (hr.trans_lt (EReal.coe_lt_coe_iff.mpr (lt_add_of_pos_right r hε)))
  have hb' := EReal.coe_lt_coe_iff.mp hb
  have hrb : r ≤ b := EReal.coe_le_coe_iff.mp (hr ▸ filtrationLevel_le hxb)
  refine hVS r b hrb (Set.disjoint_left.mpr fun t htS ht ↦ hball ⟨?_, ht.1.ne'⟩ htS) hxb
  rw [Metric.mem_ball, Real.dist_eq, abs_lt]
  constructor <;> linarith [ht.1, ht.2]

variable (hV : Monotone V)
include hV

theorem mem_of_filtrationLevel_lt (h : filtrationLevel V x < a) : x ∈ V a := by
  obtain ⟨b, hxb, hb⟩ := filtrationLevel_lt_iff.mp h
  exact hV (EReal.coe_lt_coe_iff.mp hb).le hxb

theorem filtrationLevel_eq_bot_iff : filtrationLevel V x = ⊥ ↔ ∀ a, x ∈ V a :=
  ⟨fun h a ↦ mem_of_filtrationLevel_lt hV (h ▸ EReal.bot_lt_coe a),
    filtrationLevel_eq_bot_of_forall_mem⟩

/-- The non-Archimedean triangle inequality for filtration levels. -/
theorem filtrationLevel_add_le (x y : M) :
    filtrationLevel V (x + y) ≤ max (filtrationLevel V x) (filtrationLevel V y) := by
  refine EReal.le_of_forall_lt_iff_le.mp fun z hz ↦ filtrationLevel_le ?_
  rw [max_lt_iff] at hz
  exact (V z).add_mem (mem_of_filtrationLevel_lt hV hz.1) (mem_of_filtrationLevel_lt hV hz.2)

/-- A nonzero element lies above every index whose submodule is zero. -/
theorem le_filtrationLevel_of_eq_bot (h : V a = ⊥) (hx : x ≠ 0) :
    (a : EReal) ≤ filtrationLevel V x := by
  refine le_filtrationLevel_iff.mpr fun b hb ↦ EReal.coe_le_coe_iff.mpr ?_
  by_contra! hba
  exact hx ((Submodule.mem_bot R).mp (h ▸ hV hba.le hb))

/-- **Spectrality** for a nonzero element of a filtration which vanishes at some index and
contains the element at another: its filtration level is a real number in `S`. -/
theorem exists_mem_filtrationLevel_eq {S : Set ℝ} (hS : IsClosed S)
    (hVS : ∀ a b, a ≤ b → Disjoint S (Icc a b) → V b ≤ V a) {a b : ℝ} (ha : V a = ⊥)
    (hxb : x ∈ V b) (hx : x ≠ 0) : ∃ s ∈ S, filtrationLevel V x = s := by
  have htop : filtrationLevel V x ≠ ⊤ :=
    ((filtrationLevel_le hxb).trans_lt (EReal.coe_lt_top b)).ne
  have hbot : filtrationLevel V x ≠ ⊥ :=
    ((EReal.bot_lt_coe a).trans_le (le_filtrationLevel_of_eq_bot hV ha hx)).ne'
  exact ⟨_, filtrationLevel_mem_of_isClosed hS hVS (EReal.coe_toReal htop hbot).symm,
    (EReal.coe_toReal htop hbot).symm⟩

end Semiring

section Ring

variable {R M : Type*} [Ring R] [AddCommGroup M] [Module R M] {V : ℝ → Submodule R M}

@[simp]
theorem filtrationLevel_neg (x : M) : filtrationLevel V (-x) = filtrationLevel V x := by
  simp [filtrationLevel]

variable (hV : Monotone V)
include hV

theorem filtrationLevel_sub_le (x y : M) :
    filtrationLevel V (x - y) ≤ max (filtrationLevel V x) (filtrationLevel V y) := by
  simpa [sub_eq_add_neg] using filtrationLevel_add_le hV x (-y)

/-- The equality case of the non-Archimedean triangle inequality: adding an element of strictly
smaller level does not change the filtration level. -/
theorem filtrationLevel_add_eq_of_lt {x y : M} (h : filtrationLevel V y < filtrationLevel V x) :
    filtrationLevel V (x + y) = filtrationLevel V x := by
  refine le_antisymm ((filtrationLevel_add_le hV x y).trans (max_le le_rfl h.le)) ?_
  have hx := filtrationLevel_sub_le hV (x + y) y
  rw [add_sub_cancel_right] at hx
  rcases le_max_iff.mp hx with h' | h'
  · exact h'
  · exact absurd h' h.not_ge

end Ring

end TauCeti
