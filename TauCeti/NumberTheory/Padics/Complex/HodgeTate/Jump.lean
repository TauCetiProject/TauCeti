/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.NumberTheory.Cyclotomic.CyclotomicCharacter
public import Mathlib.RepresentationTheory.Basic
public import TauCeti.NumberTheory.Padics.Complex.GaloisAction

import Mathlib.LinearAlgebra.Dimension.Constructions
import TauCeti.LinearAlgebra.LinearIndependent.Restrict
import TauCeti.NumberTheory.Padics.Complex.FixedPoints
import TauCeti.NumberTheory.Padics.Complex.TateTwist

/-!
# Hodge–Tate maps and Hodge–Tate jumps

Let `Γ` be a monoid with a homomorphism `j : Γ → G_{ℚ_p} = Gal(PadicAlgCl p / ℚ_p)`, and let `ρ`
be a representation of `Γ` on a module `T` over a commutative semiring `R`. A property holds for `g`
*near `1`* if it holds for all `g` with `j g` in some neighbourhood of `1`, that is, along the
filter `Filter.comap j (𝓝 1)`. Write `χ` for the cyclotomic character.

For a ring map `γ : R → ℂ_p` and `u ∈ ℤ`, the *Hodge–Tate maps of weight `u` at `γ`* are the
`γ`-semilinear maps `f : T → ℂ_p` such that for every `x ∈ T`,
`f (ρ g x) = χ(j g) ^ (-u) · (j g) (f x)` for `g` near `1` (the neighbourhood may depend on `x`).
They form a `PadicAlgCl p`-subspace `PadicComplex.hodgeTateMaps j ρ γ u`, since algebraic elements
of `ℂ_p` are fixed near `1`. Its dimension is the *Hodge–Tate jump*
`PadicComplex.hodgeTateJump j ρ γ u` (`0` if the dimension is infinite), and a multiset `J` of
integers *is the multiset of jumps* (`PadicComplex.HasHodgeTateJumps`) if each `u` has
multiplicity `hodgeTateJump j ρ γ u` in `J`. With this convention `ℤ_p(1)` has the single jump
`-1`.

The main theorem compares the scalars `ℂ_p` and `PadicAlgCl p`. If the image of `j` is a
neighbourhood of `1` (for a group `Γ`, if it is open), a Hodge–Tate map of weight `u` lying in
the `ℂ_p`-span of Hodge–Tate maps `f i` of weights `k i` lies in the `PadicAlgCl p`-span of those
`f i` with `k i = u`. Writing it in a `ℂ_p`-independent
subfamily, each coefficient `c` satisfies `χ(σ) ^ (-u) σ(c) = χ(σ) ^ (-k i) c` for `σ` near `1`:
the independent family stays independent on finitely many points
(`LinearIndependent.exists_finset_linearIndependent_restrict`), at which a single neighbourhood
of `1` serves. Tate's theorem near `1`
(`PadicComplex.eq_zero_of_eventually_cyclotomicCharacter_zpow_mul_smul_eq`) kills `c` when
`k i ≠ u`, and the Ax–Sen–Tate theorem (`PadicComplex.mem_range_coe_iff_eventually_smul_eq`) makes
`c` algebraic when `k i = u`. Consequently a `ℂ_p`-basis of the semilinear maps consisting of
Hodge–Tate maps of weights `k i` computes the jumps: they form the multiset of the `k i`.

## Main definitions

* `PadicComplex.hodgeTateMaps j ρ γ u`: the Hodge–Tate maps of weight `u` at `γ`.
* `PadicComplex.hodgeTateJump j ρ γ u`: their dimension over `PadicAlgCl p`.
* `PadicComplex.HasHodgeTateJumps j ρ γ J`: `J` is the multiset of Hodge–Tate jumps at `γ`.

## Main results

* `PadicComplex.mem_span_image_of_mem_hodgeTateMaps`: a Hodge–Tate map of weight `u` in the
  `ℂ_p`-span of Hodge–Tate maps lies in the `PadicAlgCl p`-span of those of weight `u`.
* `PadicComplex.disjoint_hodgeTateMaps`: Hodge–Tate maps of different weights meet only in `0`.
* `PadicComplex.hasHodgeTateJumps_of_basis`: a `ℂ_p`-basis of Hodge–Tate maps computes the jumps.

## References

* J.-M. Fontaine, *Représentations p-adiques semi-stables*, Astérisque 223 (1994).
* O. Brinon and B. Conrad, *CMI summer school notes on p-adic Hodge theory* (2009), §2.

The definitions and the argument follow `New.Period.hodgeTateMaps`, `New.Period.jump`,
`New.Period.HasJumps` (`src/Lib/PadicHodge/Crystalline/Basic.lean`) and
`New.Period.hodgeTateMaps.mem_span_same_weight`, `New.Period.hasJumps_of_basis`
(`src/Lib/PadicHodge/Crystalline/HodgeTateForms.lean`) of grh-lean
(https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic, PBC).
-/

public section

open Topology Filter Module

namespace PadicComplex

variable {p : ℕ} [Fact p.Prime] {Γ R T : Type*} [Monoid Γ] [CommSemiring R] [AddCommMonoid T]
  [Module R T] (j : Γ →* (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)) (ρ : Representation R Γ T)
  (γ : R →+* ℂ_[p])

/-- The *Hodge–Tate maps of weight `u` at `γ`*: the `γ`-semilinear maps `f : T → ℂ_p` such that for
every `x ∈ T`, `f (ρ g x) = χ(j g) ^ (-u) · (j g) (f x)` for all `g` near `1`, that is, for `g`
with `j g` in a neighbourhood of `1` that may depend on `x`. They form a subspace over
`PadicAlgCl p`, since algebraic elements of `ℂ_p` are fixed near `1`. -/
noncomputable def hodgeTateMaps (u : ℤ) : Submodule (PadicAlgCl p) (T →ₛₗ[γ] ℂ_[p]) where
  carrier := {f | ∀ x, ∀ᶠ g in comap j (𝓝 1), f (ρ g x) =
    algebraMap ℚ_[p] ℂ_[p]
      (((cyclotomicCharacter (PadicAlgCl p) p (j g).toRingEquiv ^ (-u) : ℤ_[p]ˣ) : ℤ_[p]) :
        ℚ_[p]) * j g • f x}
  zero_mem' _ := by simp
  add_mem' hf hf' x := by
    filter_upwards [hf x, hf' x] with g h h'
    simp [h, h', mul_add]
  smul_mem' a f hf x := by
    filter_upwards [hf x, (mem_range_coe_iff_eventually_smul_eq.1 ⟨a, rfl⟩).comap j] with g h ha
    simp only [LinearMap.smul_apply, Algebra.smul_def, smul_mul', h]
    rw [UniformSpace.Completion.algebraMap_def, Algebra.algebraMap_self_apply, ha, mul_left_comm]

variable {j ρ γ} in
@[simp]
theorem mem_hodgeTateMaps {u : ℤ} {f : T →ₛₗ[γ] ℂ_[p]} :
    f ∈ hodgeTateMaps j ρ γ u ↔ ∀ x, ∀ᶠ g in comap j (𝓝 1), f (ρ g x) =
      algebraMap ℚ_[p] ℂ_[p]
        (((cyclotomicCharacter (PadicAlgCl p) p (j g).toRingEquiv ^ (-u) : ℤ_[p]ˣ) : ℤ_[p]) :
          ℚ_[p]) * j g • f x :=
  Iff.rfl

/-- The *Hodge–Tate jump* of weight `u` at `γ`: the dimension over `PadicAlgCl p` of the space of
Hodge–Tate maps of weight `u` at `γ`, and `0` if it is infinite. -/
noncomputable def hodgeTateJump (u : ℤ) : ℕ :=
  finrank (PadicAlgCl p) (hodgeTateMaps j ρ γ u)

theorem hodgeTateJump_def (u : ℤ) :
    hodgeTateJump j ρ γ u = finrank (PadicAlgCl p) (hodgeTateMaps j ρ γ u) :=
  (rfl)

/-- A multiset `J` of integers *is the multiset of Hodge–Tate jumps at `γ`* if every `u` has
multiplicity `hodgeTateJump j ρ γ u` in `J`. -/
def HasHodgeTateJumps (J : Multiset ℤ) : Prop :=
  ∀ u, hodgeTateJump j ρ γ u = J.count u

theorem hasHodgeTateJumps_iff (J : Multiset ℤ) :
    HasHodgeTateJumps j ρ γ J ↔ ∀ u, hodgeTateJump j ρ γ u = J.count u :=
  (Iff.rfl)

variable {j ρ γ}

/-- The multiset of Hodge–Tate jumps at `γ` is unique when it exists. -/
theorem HasHodgeTateJumps.eq {J J' : Multiset ℤ} (h : HasHodgeTateJumps j ρ γ J)
    (h' : HasHodgeTateJumps j ρ γ J') : J = J' :=
  Multiset.ext.2 fun u ↦ (h u).symm.trans (h' u)

/-- The coefficients of a Hodge–Tate map of weight `u` in a `ℂ_p`-independent finite family of
Hodge–Tate maps of weights `k i`: a nonzero coefficient has `k i = u` and is algebraic. -/
private theorem weight_eq_and_mem_range_of_linearIndependent (hj : Set.range j ∈ 𝓝 1)
    {ι : Type*} [Fintype ι] {k : ι → ℤ} {f : ι → T →ₛₗ[γ] ℂ_[p]}
    (hli : LinearIndependent ℂ_[p] f) (hf : ∀ i, f i ∈ hodgeTateMaps j ρ γ (k i)) {u : ℤ}
    {c : ι → ℂ_[p]} (hc : ∑ i, c i • f i ∈ hodgeTateMaps j ρ γ u) {i : ι} (hci : c i ≠ 0) :
    k i = u ∧ c i ∈ Set.range ((↑) : PadicAlgCl p → ℂ_[p]) := by
  set χ : ℤ → (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) → ℂ_[p] := fun n σ ↦ algebraMap ℚ_[p] ℂ_[p]
    (((cyclotomicCharacter (PadicAlgCl p) p σ.toRingEquiv ^ n : ℤ_[p]ˣ) : ℤ_[p]) : ℚ_[p])
    with hχ
  -- The maps `f i`, as functions on `T`, stay independent on a finite set `s` of points.
  let L : (T →ₛₗ[γ] ℂ_[p]) →ₗ[ℂ_[p]] T → ℂ_[p] :=
    { toFun := (⇑), map_add' := fun _ _ ↦ rfl, map_smul' := fun _ _ ↦ rfl }
  obtain ⟨s, hs⟩ := (hli.map' L (LinearMap.ker_eq_bot.2 DFunLike.coe_injective)
    ).exists_finset_linearIndependent_restrict
  -- At the points of `s`, a single neighbourhood of `1` carries all the twisted relations.
  have hev : ∀ᶠ g in comap j (𝓝 1), ∀ x ∈ s, (∑ i, c i • f i) (ρ g x) =
      χ (-u) (j g) * j g • (∑ i, c i • f i) x ∧ ∀ i, f i (ρ g x) = χ (-k i) (j g) * j g • f i x :=
    s.eventually_all.2 fun x _ ↦ (hc x).and (eventually_all.2 fun i ↦ hf i x)
  have hkey : ∀ᶠ g in comap j (𝓝 1), χ (-u) (j g) * j g • c i = χ (-k i) (j g) * c i := by
    filter_upwards [hev] with g hg
    set σ := j g
    -- Comparing the two expressions for `(∑ i, c i • f i) (ρ g x)` and applying `σ⁻¹` gives a
    -- relation among the `f i` on `s`, whose coefficients therefore vanish.
    have hrel : ∀ x ∈ s,
        ∑ i, σ⁻¹ • (χ (-u) σ * σ • c i - χ (-k i) σ * c i) * f i x = 0 := fun x hx ↦ by
      obtain ⟨h₁, h₂⟩ := hg x hx
      simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, h₂,
        Finset.smul_sum, smul_mul'] at h₁
      rw [← smul_eq_zero_iff_eq σ, Finset.smul_sum]
      simp only [smul_mul', smul_inv_smul]
      calc _ = χ (-u) σ * ∑ i, σ • c i * σ • f i x - ∑ i, c i * (χ (-k i) σ * σ • f i x) := by
            simp only [sub_mul, Finset.sum_sub_distrib, Finset.mul_sum]
            congr 1 <;> exact Finset.sum_congr rfl fun i _ ↦ by ring
        _ = 0 := by rw [h₁]; ring
    have := Fintype.linearIndependent_iff.1 hs _ (funext fun x : s ↦ by
      simpa [L, Finset.sum_apply] using hrel x x.property) i
    rwa [smul_eq_zero_iff_eq, sub_eq_zero] at this
  have hkey' : ∀ᶠ σ in 𝓝 (1 : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p),
      χ (-u) σ * σ • c i = χ (-k i) σ * c i := by
    rw [← map_comap_of_mem hj]
    exact hkey
  by_cases hki : k i = u
  · refine ⟨hki, mem_range_coe_iff_eventually_smul_eq.2 ?_⟩
    filter_upwards [hkey'] with σ hσ
    rw [hki] at hσ
    exact mul_left_cancel₀ (by simp [hχ]) hσ
  · exact absurd (eq_zero_of_eventually_cyclotomicCharacter_zpow_mul_smul_eq
      (fun h ↦ hki (neg_inj.1 h).symm) hkey') hci

/-- Let the image of `j` be a neighbourhood of `1`. If a Hodge–Tate map `φ` of weight `u` lies in
the `ℂ_p`-span of Hodge–Tate maps `f i` of weights `k i`, then it lies in the `PadicAlgCl p`-span of
those `f i` with `k i = u`. -/
theorem mem_span_image_of_mem_hodgeTateMaps (hj : Set.range j ∈ 𝓝 1) {ι : Type*} {k : ι → ℤ}
    {f : ι → T →ₛₗ[γ] ℂ_[p]} (hf : ∀ i, f i ∈ hodgeTateMaps j ρ γ (k i)) {u : ℤ}
    {φ : T →ₛₗ[γ] ℂ_[p]} (hφ : φ ∈ hodgeTateMaps j ρ γ u)
    (hspan : φ ∈ Submodule.span ℂ_[p] (Set.range f)) :
    φ ∈ Submodule.span (PadicAlgCl p) (f '' {i | k i = u}) := by
  -- Write `φ` in a `ℂ_p`-independent subfamily `f ∘ a`, over the finite support of `c`.
  obtain ⟨κ, a, -, hspan_eq, hli⟩ := exists_linearIndependent' ℂ_[p] f
  rw [← hspan_eq, Finsupp.mem_span_range_iff_exists_finsupp] at hspan
  obtain ⟨c, rfl⟩ := hspan
  have hsum : (c.sum fun l b ↦ b • (f ∘ a) l) = ∑ l : c.support, c l • f (a l) := by
    rw [Finsupp.sum, ← Finset.sum_coe_sort]
    simp only [Function.comp_apply]
  rw [hsum] at hφ ⊢
  refine Submodule.sum_mem _ fun l _ ↦ ?_
  obtain ⟨hk, d, hd⟩ := weight_eq_and_mem_range_of_linearIndependent hj
    (hli.comp _ Subtype.val_injective) (fun l ↦ hf (a l)) hφ
    (Finsupp.mem_support_iff.1 l.property)
  rw [← hd, ← Algebra.algebraMap_self_apply d, ← UniformSpace.Completion.algebraMap_def,
    algebraMap_smul]
  exact Submodule.smul_mem _ d (Submodule.subset_span ⟨a l, hk, rfl⟩)

/-- Let the image of `j` be a neighbourhood of `1`. Hodge–Tate maps of different weights meet only
in `0`. -/
theorem disjoint_hodgeTateMaps (hj : Set.range j ∈ 𝓝 1) {u v : ℤ} (huv : u ≠ v) :
    Disjoint (hodgeTateMaps j ρ γ u) (hodgeTateMaps j ρ γ v) := by
  refine Submodule.disjoint_def.2 fun φ hu hv ↦ ?_
  have := mem_span_image_of_mem_hodgeTateMaps hj (f := fun _ : Unit ↦ φ) (k := fun _ ↦ v)
    (fun _ ↦ hv) hu (Submodule.subset_span ⟨(), rfl⟩)
  simpa [Ne.symm huv] using this

/-- Let the image of `j` be a neighbourhood of `1`. If a `ℂ_p`-basis `b` of the `γ`-semilinear maps
`T → ℂ_p` consists of Hodge–Tate maps, `b i` of weight `k i`, then the Hodge–Tate maps of weight `u`
are spanned over `PadicAlgCl p` by the `b i` with `k i = u`. -/
theorem hodgeTateMaps_eq_span_of_basis (hj : Set.range j ∈ 𝓝 1) {ι : Type*}
    (b : Basis ι ℂ_[p] (T →ₛₗ[γ] ℂ_[p])) {k : ι → ℤ}
    (hb : ∀ i, b i ∈ hodgeTateMaps j ρ γ (k i)) (u : ℤ) :
    hodgeTateMaps j ρ γ u = Submodule.span (PadicAlgCl p) (b '' {i | k i = u}) := by
  refine le_antisymm (fun φ hφ ↦ mem_span_image_of_mem_hodgeTateMaps hj hb hφ ?_) ?_
  · rw [b.span_eq]
    exact Submodule.mem_top
  · rw [Submodule.span_le]
    rintro _ ⟨i, hi, rfl⟩
    exact hi ▸ hb i

/-- Let the image of `j` be a neighbourhood of `1`. If a finite `ℂ_p`-basis `b` of the
`γ`-semilinear maps `T → ℂ_p` consists of Hodge–Tate maps, `b i` of weight `k i`, then the
Hodge–Tate jump of weight `u` is the number of `i` with `k i = u`. -/
theorem hodgeTateJump_eq_card_of_basis (hj : Set.range j ∈ 𝓝 1) {ι : Type*} [Fintype ι]
    (b : Basis ι ℂ_[p] (T →ₛₗ[γ] ℂ_[p])) {k : ι → ℤ}
    (hb : ∀ i, b i ∈ hodgeTateMaps j ρ γ (k i)) (u : ℤ) :
    hodgeTateJump j ρ γ u = (Finset.univ.filter fun i ↦ k i = u).card := by
  have hli : LinearIndependent (PadicAlgCl p) fun i : {i | k i = u} ↦ b i :=
    (b.linearIndependent.restrict_scalars' (PadicAlgCl p)).comp _ Subtype.val_injective
  rw [hodgeTateJump_def, hodgeTateMaps_eq_span_of_basis hj b hb, Set.image_eq_range,
    finrank_span_eq_card hli]
  simp [Fintype.card_subtype]

/-- Let the image of `j` be a neighbourhood of `1`. If a finite `ℂ_p`-basis `b` of the
`γ`-semilinear maps `T → ℂ_p` consists of Hodge–Tate maps, `b i` of weight `k i`, then the weights
`k i` form the multiset of Hodge–Tate jumps at `γ`. -/
theorem hasHodgeTateJumps_of_basis (hj : Set.range j ∈ 𝓝 1) {ι : Type*} [Fintype ι]
    (b : Basis ι ℂ_[p] (T →ₛₗ[γ] ℂ_[p])) {k : ι → ℤ}
    (hb : ∀ i, b i ∈ hodgeTateMaps j ρ γ (k i)) :
    HasHodgeTateJumps j ρ γ (Finset.univ.val.map k) := fun u ↦ by
  rw [hodgeTateJump_eq_card_of_basis hj b hb, Multiset.count_map, Finset.card_def,
    Finset.filter_val]
  simp_rw [eq_comm]

end PadicComplex
