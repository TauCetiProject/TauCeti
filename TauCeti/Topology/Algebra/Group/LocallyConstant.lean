/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Topology.Algebra.OpenSubgroup
public import TauCeti.Topology.LocallyConstant.Compact

/-!
# Locally constant functions on topological groups

An additive homomorphism from a group with separately continuous addition whose kernel is open
is locally constant, even when its codomain is only an `AddZeroClass`. Open kernels are preserved
by taking integer multiples of additive homomorphisms into an additive commutative group.

A locally constant function `f : G → A` on a topological group is constant near each point, but
the neighbourhood on which it is constant depends on the point. On a *compact* group the
dependence disappears: there is a single open subgroup `V` with `f (x * v) = f x` for **every**
`x : G` and every `v : V`. This file records that subgroup,
`TauCeti.rightTranslationStabilizer f`, and its openness,
`TauCeti.isOpen_rightTranslationStabilizer`.

Uniform local constancy is what makes the coinduced module of locally constant equivariant maps a
*discrete* `G`-module, its right-translation stabilizers being open.

The uniformity statement itself needs only a compact *set* `K ⊆ G` and continuous multiplication:
`IsLocallyConstant.exists_isOpen_forall_mem_mul_right_eq` is that statement, uniform in the point
`x ∈ K`, for the family `x ↦ f (x * σ p)`. The parameter map `σ` needs continuity only at the
chosen point; no associativity, identity or inverse is needed.

`IsLocallyConstant.exists_isOpen_forall_mul_right_eq` specializes to a compact space.
`IsLocallyConstant.exists_isOpen_translate₂` and `IsLocallyConstant.exists_isOpen_translate₃` give
uniformity for the families `(y, y * g)` and `(y, y * g, y * g * h)` used in cochain constructions.
-/

public section

namespace AddMonoidHom

variable {G A : Type*} [AddGroup G] [TopologicalSpace G] [SeparatelyContinuousAdd G]

/-- An additive homomorphism with open kernel is locally constant. -/
theorem isLocallyConstant_of_isOpen_ker [AddZeroClass A] (χ : G →+ A)
    (hχ : IsOpen (χ.ker : Set G)) : IsLocallyConstant (χ : G → A) := by
  refine (IsLocallyConstant.iff_eventually_eq _).2 fun x ↦ ?_
  -- Near `x`, the difference `-x + y` lies in the open kernel.
  have hopen : IsOpen ((fun y : G ↦ -x + y) ⁻¹' (χ.ker : Set G)) :=
    hχ.preimage (continuous_id.const_add (-x))
  filter_upwards [hopen.mem_nhds (by simp)] with y hy
  exact χ.eq_iff.mpr hy

/-- The kernel of an integer multiple of an additive homomorphism with open kernel is open. -/
theorem isOpen_ker_zsmul [AddCommGroup A] (χ : G →+ A)
    (hχ : IsOpen (χ.ker : Set G)) (k : ℤ) :
    IsOpen ((k • χ).ker : Set G) :=
  AddSubgroup.isOpen_mono (fun x hx ↦ by simp_all) hχ

end AddMonoidHom

namespace IsLocallyConstant

variable {G : Type*} [Mul G] [TopologicalSpace G] [ContinuousMul G] {A : Type*}

/-- For a locally constant `f` on a space with continuous multiplication and a compact set `K`,
a family of right translations `σ : P → G` continuous at `p₀` leaves `x ↦ f (x * σ p)` unchanged
on a neighbourhood of `p₀`, uniformly in `x ∈ K`. Only `K` must be compact; no group structure
or continuity of `σ` away from `p₀` is needed. -/
theorem exists_isOpen_forall_mem_mul_right_eq
    {f : G → A} (hf : IsLocallyConstant f) {K : Set G} (hK : IsCompact K) {P : Type*}
    [TopologicalSpace P] {σ : P → G} (p₀ : P) (hσ : ContinuousAt σ p₀) :
    ∃ V : Set P, IsOpen V ∧ p₀ ∈ V ∧ ∀ p ∈ V, ∀ x ∈ K, f (x * σ p) = f (x * σ p₀) := by
  -- The compact-family lemma applied to `(x, g) ↦ f (x * g)` gives a uniform neighbourhood.
  obtain ⟨V, hVopen, hVσ, hV⟩ :=
    (hf.comp_continuous continuous_mul).exists_isOpen_forall_mem_eq hK (σ p₀)
  -- Continuity at `p₀` pulls this neighbourhood back to the parameter space.
  obtain ⟨W, hWV, hWopen, hWp₀⟩ :=
    mem_nhds_iff.mp (hσ.preimage_mem_nhds (hVopen.mem_nhds hVσ))
  exact ⟨W, hWopen, hWp₀, fun p hp x hx ↦ hV (σ p) (hWV hp) x hx⟩

/-- On a compact space with continuous multiplication, a family of right translations continuous
at `p₀` leaves a locally constant `f` unchanged near `p₀`, uniformly in the translated point. -/
theorem exists_isOpen_forall_mul_right_eq [CompactSpace G]
    {f : G → A} (hf : IsLocallyConstant f) {P : Type*} [TopologicalSpace P] {σ : P → G}
    (p₀ : P) (hσ : ContinuousAt σ p₀) :
    ∃ V : Set P, IsOpen V ∧ p₀ ∈ V ∧ ∀ p ∈ V, ∀ x : G, f (x * σ p) = f (x * σ p₀) := by
  simpa using exists_isOpen_forall_mem_mul_right_eq hf isCompact_univ p₀ hσ

/-- A locally constant function `N : G × G → A`, evaluated along `(y, y * g)`, is locally
constant in `g`, uniformly in `y`, on a compact space with continuous multiplication. -/
theorem exists_isOpen_translate₂ [CompactSpace G]
    {N : G × G → A} (hN : IsLocallyConstant N) (g₀ : G) :
    ∃ V : Set G, IsOpen V ∧ g₀ ∈ V ∧ ∀ g ∈ V, ∀ y : G, N (y, y * g) = N (y, y * g₀) := by
  simpa using (hN.comp_continuous
    (continuous_fst.prodMk (continuous_fst.mul continuous_snd))).exists_isOpen_forall_mem_eq
    isCompact_univ g₀

/-- A locally constant function `Q : G × G × G → A`, evaluated along
`(y, y * g, y * g * h)`, is locally constant in `(g, h)`, uniformly in `y`, on a compact space
with continuous multiplication. -/
theorem exists_isOpen_translate₃ [CompactSpace G]
    {Q : G × G × G → A} (hQ : IsLocallyConstant Q) (q₀ : G × G) :
    ∃ V : Set (G × G), IsOpen V ∧ q₀ ∈ V ∧
      ∀ q ∈ V, ∀ y : G, Q (y, y * q.1, y * q.1 * q.2) = Q (y, y * q₀.1, y * q₀.1 * q₀.2) := by
  simpa using (hQ.comp_continuous (continuous_fst.prodMk
    ((continuous_fst.mul (continuous_fst.comp continuous_snd)).prodMk
      ((continuous_fst.mul (continuous_fst.comp continuous_snd)).mul
        (continuous_snd.comp continuous_snd))))).exists_isOpen_forall_mem_eq isCompact_univ q₀

end IsLocallyConstant

namespace TauCeti

variable {G : Type*} [Group G] {A : Type*}

/-- The **right-translation stabilizer** of `f : G → A`: the subgroup of those `g` with
`f (x * g) = f x` for every `x : G`. For a locally constant `f` on a compact group it is open
(`TauCeti.isOpen_rightTranslationStabilizer`), which is the sense in which `f` is *uniformly*
locally constant. -/
def rightTranslationStabilizer (f : G → A) : Subgroup G where
  carrier := {g | ∀ x : G, f (x * g) = f x}
  one_mem' x := by rw [mul_one]
  mul_mem' {g g'} hg hg' x := by rw [← mul_assoc, hg' (x * g), hg x]
  inv_mem' {g} hg x := by rw [← hg (x * g⁻¹), inv_mul_cancel_right]

@[simp]
theorem mem_rightTranslationStabilizer {f : G → A} {g : G} :
    g ∈ rightTranslationStabilizer f ↔ ∀ x : G, f (x * g) = f x := Iff.rfl

/-- A locally constant function on a compact topological group is *uniformly* locally constant:
its right-translation stabilizer is an open subgroup, so a single open neighbourhood of `1` makes
`f (x * g) = f x` hold for every `x` simultaneously. -/
theorem isOpen_rightTranslationStabilizer [TopologicalSpace G] [ContinuousMul G]
    [CompactSpace G] {f : G → A} (hf : IsLocallyConstant f) :
    IsOpen (rightTranslationStabilizer f : Set G) := by
  -- Uniform local constancy near `1` gives a neighbourhood inside the stabilizer subgroup.
  obtain ⟨V, hVopen, hV1, hV⟩ :=
    hf.exists_isOpen_forall_mul_right_eq (1 : G) continuous_id.continuousAt
  refine Subgroup.isOpen_of_mem_nhds _ (Filter.mem_of_superset (hVopen.mem_nhds hV1)
    fun g hg x => ?_)
  simpa using hV g hg x

end TauCeti
