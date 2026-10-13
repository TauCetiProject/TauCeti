/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.Topology.Algebra.OpenSubgroup
public import TauCeti.Algebra.Module.Submodule.Pointwise
public import TauCeti.Topology.Algebra.TopologicallyNilpotent

/-!
# Subrings of a topological ring

This file records facts about a subring `R` of a topological ring `B` without auxiliary ideal or
adic data: the underlying set of `Subring.topologicalClosure` is the closure of the underlying
set of `R`, and the integral closure of `R` in `B` is open as soon as `R` is, for which only
separate continuity of addition is needed.

The first is the `Subring` case of the family `Subsemigroup.coe_topologicalClosure`,
`Submonoid.coe_topologicalClosure`, `Subsemiring.topologicalClosure_coe`; Mathlib stops short of
`Subring`, so the equation is only available as a definitional unfolding, which is what this file
supplies as a rewrite. The second is the observation that the integral closure contains `R` and
that an additive subgroup containing an open one is open.

Powers of a topologically nilpotent scalar absorb elements of the ambient ring into any open
subring. For submodules over that subring, they absorb the ambient span element by element,
and a single exponent absorbs a finitely generated submodule. These facts compare the
power-scaled filtrations of finite spanning lattices; they need only separately continuous
multiplication on the ambient ring. Scalar absorption is supplied by
`exists_mul_pow_mem_of_isTopologicallyNilpotent`.

## Main results

* `Subring.topologicalClosure_coe`: `↑S.topologicalClosure = closure ↑S`.
* `isOpen_integralClosure_toSubring`: the integral closure of an open subring is open.
* `Subring.exists_pow_smul_mem`: a power carries an element of the ambient span into a
  submodule over the open subring.
* `Subring.exists_pow_smul_le` and `Subring.exists_pow_smul_le_pow_smul`: the uniform and
  cofinality forms for finitely generated submodules.
* `Subring.exists_pow_smul_le_pow_smul_of_isUnit`: powers of a topologically nilpotent scalar
  are cofinal in the filtration defined by powers of a unit.

## References

* [Wedhorn, *Adic Spaces*][wedhorn_adic], Definition 7.14, where the integral closure of an open
  subring is taken and its openness is used without comment; Proposition 6.18 and Remark 6.19
  for the application of absorption to module topologies.
-/

public section

namespace Subring

variable {R : Type*} [Ring R] [TopologicalSpace R] [IsSemitopologicalRing R]

/-- The closure of a subring, as a set, is the closure of its underlying set: that set is how
`Subring.topologicalClosure` is defined. Mathlib has the `Subsemigroup`, `Submonoid` and
`Subsemiring` forms of this equation but not the `Subring` one. -/
@[simp]
theorem topologicalClosure_coe (S : Subring R) :
    (S.topologicalClosure : Set R) = _root_.closure (S : Set R) := (rfl)

end Subring

variable {B : Type*} [CommRing B] [TopologicalSpace B] [SeparatelyContinuousAdd B]

/-- The integral closure of an open subring `R` of `B` is open: it contains `R` itself, as the
image of `algebraMap`, and an additive subgroup containing an open one is open. Only separate
continuity of addition on `B` is used, not the full additive topological group structure. -/
theorem isOpen_integralClosure_toSubring {R : Subring B} (hR : IsOpen (R : Set B)) :
    IsOpen ((integralClosure R B).toSubring : Set B) :=
  AddSubgroup.isOpen_mono (H₁ := R.toAddSubgroup)
    (H₂ := (integralClosure R B).toSubring.toAddSubgroup)
    (fun x hx ↦ (integralClosure R B).algebraMap_mem ⟨x, hx⟩) hR

namespace Subring

open scoped Topology Pointwise

variable {A : Type*} [CommRing A] [TopologicalSpace A] [SeparatelyContinuousMul A]
  {M : Type*} [AddCommMonoid M] [Module A M]

/-- A power of a topologically nilpotent scalar `s ∈ S` carries any element of the `A`-span
of `M₀` into `M₀`. No spanning hypothesis on the whole module is needed. -/
theorem exists_pow_smul_mem (S : Subring A) (hS : IsOpen (S : Set A)) {s : A}
    (hs : IsTopologicallyNilpotent s)
    (hs0 : s ∈ S) (M₀ : Submodule S M) {m : M}
    (hm : m ∈ Submodule.span A (M₀ : Set M)) :
    ∃ k : ℕ, s ^ k • m ∈ M₀ := by
  induction hm using Submodule.span_induction with
  | mem x hx => exact ⟨0, by simpa using hx⟩
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ ihx ihy =>
      obtain ⟨kx, hkx⟩ := ihx; obtain ⟨ky, hky⟩ := ihy
      refine ⟨max kx ky, ?_⟩
      have hx' : s ^ (max kx ky) • x ∈ M₀ := by
        have he : max kx ky = (max kx ky - kx) + kx := by omega
        rw [he]; exact M₀.pow_add_smul_mem hs0 _ _ _ hkx
      have hy' : s ^ (max kx ky) • y ∈ M₀ := by
        have he : max kx ky = (max kx ky - ky) + ky := by omega
        rw [he]; exact M₀.pow_add_smul_mem hs0 _ _ _ hky
      rw [smul_add]; exact M₀.add_mem hx' hy'
  | smul c x _ ih =>
      obtain ⟨k, hk⟩ := ih
      obtain ⟨i, hi⟩ := exists_mul_pow_mem_of_isTopologicallyNilpotent hs hS c
      rw [mul_comm] at hi
      refine ⟨i + k, ?_⟩
      have he : s ^ (i + k) • (c • x) = (⟨s ^ i * c, hi⟩ : S) • (s ^ k • x) := by
        rw [smul_smul, Subring.smul_def, ← smul_assoc, smul_eq_mul]
        congr 1
        push_cast
        rw [pow_add]; ring
      rw [he]; exact M₀.smul_mem _ hk

/-- A power of `s` carries a finitely generated `S`-submodule into `M₀` uniformly.

A *single* exponent serves all of `M₁` at once. That uniformity is exactly what finite generation
buys: without it `exists_pow_smul_mem` still gives an exponent for each element separately, but
those exponents need not be bounded, and no power of `s` need carry the whole submodule.

`M₀` is not required to span `M`; only `M₁` need lie in its span. -/
theorem exists_pow_smul_le (S : Subring A) (hS : IsOpen (S : Set A)) {s : A}
    (hs : IsTopologicallyNilpotent s)
    (hs0 : s ∈ S) (M₀ M₁ : Submodule S M)
    (hspan : (M₁ : Set M) ⊆ Submodule.span A (M₀ : Set M)) (hfg : M₁.FG) :
    ∃ k : ℕ, (⟨s, hs0⟩ : S) ^ k • M₁ ≤ M₀ := by
  obtain ⟨G, hG⟩ := hfg
  have hGmem : ∀ g ∈ (G : Set M), g ∈ Submodule.span A (M₀ : Set M) := fun g hg ↦
    hspan (hG ▸ Submodule.subset_span hg)
  choose! f hf using fun g hg ↦ S.exists_pow_smul_mem hS hs hs0 M₀ (hGmem g hg)
  refine ⟨G.sup f, ?_⟩
  rw [← hG, Submodule.smul_span, Submodule.span_le]
  rintro _ ⟨g, hg, rfl⟩
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le (Finset.le_sup (f := f) hg)
  simpa only [SetLike.mem_coe, Subring.smul_def, SubmonoidClass.coe_pow, hd, Nat.add_comm] using
    M₀.pow_add_smul_mem hs0 d (f g) g (hf g hg)

/-- Every member of the power-scaled family built from `M₀` contains a member built from a
finitely generated `M₁` lying in the `A`-span of `M₀`.

Applying this in both directions compares the two filtrations when both submodules are
finitely generated and each lies in the ambient span of the other. -/
theorem exists_pow_smul_le_pow_smul (S : Subring A) (hS : IsOpen (S : Set A)) {s : A}
    (hs : IsTopologicallyNilpotent s) (hs0 : s ∈ S)
    (M₀ M₁ : Submodule S M) (hspan : (M₁ : Set M) ⊆ Submodule.span A (M₀ : Set M))
    (hfg : M₁.FG) (n : ℕ) : ∃ k : ℕ, (⟨s, hs0⟩ : S) ^ k • M₁
      ≤ (⟨s, hs0⟩ : S) ^ n • M₀ := by
  obtain ⟨k, hk⟩ := S.exists_pow_smul_le hS hs hs0 M₀ M₁ hspan hfg
  refine ⟨n + k, ?_⟩
  have hsplit : (⟨s, hs0⟩ : S) ^ (n + k) • M₁
      = (⟨s, hs0⟩ : S) ^ n • ((⟨s, hs0⟩ : S) ^ k • M₁) := by
    rw [pow_add, mul_smul]
  rw [hsplit]
  exact smul_mono_right ((⟨s, hs0⟩ : S) ^ n) hk

/-- The powers of a topologically nilpotent scalar `t` are cofinal in the filtration of `M₀`
by powers of a unit `s`: for every `sⁿ • M₀`, some `tᵏ • M₀` is contained in it.

No finite-generation or spanning hypothesis on `M₀` is needed. -/
theorem exists_pow_smul_le_pow_smul_of_isUnit (S : Subring A) (hS : IsOpen (S : Set A))
    {s t : A} (hs : IsUnit s) (ht : IsTopologicallyNilpotent t)
    (hs0 : s ∈ S) (ht0 : t ∈ S)
    (M₀ : Submodule S M) (n : ℕ) :
    ∃ k : ℕ, (⟨t, ht0⟩ : S) ^ k • M₀
      ≤ (⟨s, hs0⟩ : S) ^ n • M₀ := by
  obtain ⟨u, rfl⟩ := hs
  obtain ⟨k, hk⟩ := exists_mul_pow_mem_of_isTopologicallyNilpotent ht hS ((↑u⁻¹ : A) ^ n)
  rw [mul_comm] at hk
  refine ⟨k, fun x hx ↦ ?_⟩
  obtain ⟨y, hy, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hx
  apply (Submodule.mem_smul_pointwise_iff_exists _ _ _).mpr
  refine ⟨(⟨t ^ k * (↑u⁻¹ : A) ^ n, hk⟩ : S) • y,
    M₀.smul_mem _ hy, ?_⟩
  rw [smul_smul]
  congr 1
  ext
  simp [mul_left_comm, ← mul_pow]

end Subring
