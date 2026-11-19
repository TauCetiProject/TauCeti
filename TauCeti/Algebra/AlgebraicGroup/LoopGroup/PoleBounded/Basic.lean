/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.FunctorOfPoints
public import TauCeti.RingTheory.LaurentSeries.Lattice

/-!
# Pole-bounded formal loops

Let `H` be a Hopf algebra over a commutative ring `k`, so that for every commutative `k`-algebra
`R` the convolution group `G(R⸨X⸩) = WithConv (H →ₐ[k] R⸨X⸩)` is the group of formal loops of
`G = Spec H` with coefficients in `R`. Here `R⸨X⸩` carries the coefficientwise `k`-algebra
structure `HahnSeries.instAlgebra`, under which `algebraMap k R⸨X⸩` is
`HahnSeries.C ∘ algebraMap k R`; instance search would otherwise find the structure routed
through `R⟦X⟧`, which agrees with it only propositionally. Files using these declarations
select it with `attribute [local instance 1100] HahnSeries.instAlgebra`.

Fix a family `x : ι → H`, for instance a finite family of algebra generators. A loop `g` is
**pole-bounded of level `N`** for `x` when `g` and its inverse `g⁻¹ = g ∘ S` send every `x i`
into the lattice `X^(-N) R⟦X⟧`. For a finite generating family these are the pieces `LG_(≤N)(R)`
of the ind-affine presentation of the loop group; for an infinite family the pieces need not
exhaust the loop group. Both bounds are needed: for `𝔾ₘ` with the generator `T`, the
loop `X^M` sends `T` into `R⟦X⟧` for every `M ≥ 0`, while its inverse has a pole of order `M`.

This file proves the properties of the pieces that do not depend on a representing algebra:

* the pieces increase with `N` and are stable under inversion;
* they are stable under coefficient maps `R → S`;
* the piece of level `0` consists of the positive loops `G(R⟦X⟧)`, when `x` generates `H`;
* for a finite family, every loop lies in some piece;
* if `x` generates `H`, each piece for `x` is contained in a piece for any finite family `y`, of
  a level depending only on the families, not on `R`; so the pieces of two finite generating
  families are cofinal in each other.

## Main definitions

* `TauCeti.HopfAlgebra.poleBoundedLoops k x R N`: the loops `g` with `g (x i)` and `g⁻¹ (x i)`
  in `X^(-N) R⟦X⟧` for every `i`.

## Main results

* `TauCeti.HopfAlgebra.mem_poleBoundedLoops_iff_antipode`: the bound on `g⁻¹` is a bound on the
  values of `g` at the antipodes `S (x i)`.
* `TauCeti.HopfAlgebra.poleBoundedLoops_mono`, `inv_mem_poleBoundedLoops_iff`.
* `TauCeti.HopfAlgebra.mem_poleBoundedLoops_of_map`: stability under coefficient maps.
* `TauCeti.HopfAlgebra.exists_forall_apply_mem_lattice`: bounds on generators give bounds on
  every element, uniformly in the coefficient algebra.
* `TauCeti.HopfAlgebra.poleBoundedLoops_zero`: `LG_(≤0)(R)` is the image of `G(R⟦X⟧)`.
* `TauCeti.HopfAlgebra.iUnion_poleBoundedLoops`: for a finite family, `LG(R)` is the union of
  the `LG_(≤N)(R)`.
* `TauCeti.HopfAlgebra.exists_poleBoundedLoops_subset`: the pieces for a generating family lie
  in pieces for any finite family, so the pieces of two finite generating families are cofinal
  in each other.

## References

* E. Frenkel, *Langlands correspondence for loop groups*, Cambridge Univ. Press (2007), §1.3.1.
-/

public section

open HahnSeries WithConv TauCeti.LaurentSeries
open HopfAlgebraStruct (antipode)
open scoped LaurentSeries PowerSeries

namespace TauCeti

namespace HopfAlgebra

attribute [local instance 1100] HahnSeries.instAlgebra

universe u v w

variable {k : Type u} {H : Type v} [Semiring H] {ι : Type*} (x : ι → H)

section Bounds

variable [CommSemiring k] [Algebra k H]

/-- Pole bounds on a generating family propagate to every element, uniformly in the
coefficient algebra: for each `h : H` there is `d` such that every `k`-algebra map
`g : H → R⸨X⸩` sending all `x i` into `X^(-N) R⟦X⟧` sends `h` into `X^(-N d) R⟦X⟧`. For `N = 0`
this says that `g` then takes values in `R⟦X⟧`. -/
theorem exists_forall_apply_mem_lattice (hx : Algebra.adjoin k (Set.range x) = ⊤) (N : ℕ)
    (h : H) : ∃ d : ℕ, ∀ (R : Type w) [Semiring R] [Algebra k R] (g : H →ₐ[k] R⸨X⸩),
      (∀ i, g (x i) ∈ lattice R R (-N)) → g h ∈ lattice R R (-(N * d : ℕ)) := by
  have hh : h ∈ Algebra.adjoin k (Set.range x) := hx ▸ Algebra.mem_top
  induction hh using Algebra.adjoin_induction with
  | mem h hh =>
    obtain ⟨i, rfl⟩ := hh
    exact ⟨1, fun R _ _ g hg ↦ by simpa using hg i⟩
  | algebraMap c =>
    refine ⟨0, fun R _ _ g _ ↦ ?_⟩
    rw [AlgHom.commutes, HahnSeries.algebraMap_apply, mul_zero, Nat.cast_zero, neg_zero]
    exact single_mem_lattice le_rfl _
  | add a b _ _ ha hb =>
    obtain ⟨d, hd⟩ := ha
    obtain ⟨e, he⟩ := hb
    refine ⟨max d e, fun R _ _ g hg ↦ ?_⟩
    have hd' : N * d ≤ N * max d e := Nat.mul_le_mul_left _ (le_max_left _ _)
    have he' : N * e ≤ N * max d e := Nat.mul_le_mul_left _ (le_max_right _ _)
    rw [map_add]
    exact add_mem (lattice_antitone (by omega) (hd R g hg))
      (lattice_antitone (by omega) (he R g hg))
  | mul a b _ _ ha hb =>
    obtain ⟨d, hd⟩ := ha
    obtain ⟨e, he⟩ := hb
    refine ⟨d + e, fun R _ _ g hg ↦ ?_⟩
    rw [map_mul, Nat.mul_add, Nat.cast_add, neg_add]
    exact mul_mem_lattice (hd R g hg) (he R g hg)

end Bounds

variable [CommRing k] [_root_.HopfAlgebra k H]

section Pieces

variable (k) (R : Type w) [CommRing R] [Algebra k R]

/-- The pole-bounded loops of level `N` for a family `x : ι → H`: the points
`g : H →ₐ[k] R⸨X⸩` such that `g` and its convolution inverse `g⁻¹` send every `x i` into the
lattice `X^(-N) R⟦X⟧`. For a finite generating family these are the `R`-points of the piece
`LG_(≤N)` of the loop group. -/
def poleBoundedLoops (N : ℕ) : Set (WithConv (H →ₐ[k] R⸨X⸩)) :=
  {g | ∀ i, g.ofConv (x i) ∈ lattice R R (-N) ∧ g⁻¹.ofConv (x i) ∈ lattice R R (-N)}

variable {k x R}

/-- A loop is pole-bounded of level `N` when it and its inverse send every `x i` into
`X^(-N) R⟦X⟧`. -/
theorem mem_poleBoundedLoops_iff {N : ℕ} {g : WithConv (H →ₐ[k] R⸨X⸩)} :
    g ∈ poleBoundedLoops k x R N ↔ ∀ i, g.ofConv (x i) ∈ lattice R R (-N) ∧
      g⁻¹.ofConv (x i) ∈ lattice R R (-N) :=
  Iff.rfl

/-- A loop is pole-bounded of level `N` when it sends every `x i` and every `S (x i)` into
`X^(-N) R⟦X⟧`, where `S` is the antipode. -/
theorem mem_poleBoundedLoops_iff_antipode {N : ℕ} {g : WithConv (H →ₐ[k] R⸨X⸩)} :
    g ∈ poleBoundedLoops k x R N ↔ ∀ i, g.ofConv (x i) ∈ lattice R R (-N) ∧
      g.ofConv (antipode k (x i)) ∈ lattice R R (-N) := by
  simp only [mem_poleBoundedLoops_iff, WithConv.algHom_inv_apply]

/-- The pieces are stable under inversion. -/
@[simp]
theorem inv_mem_poleBoundedLoops_iff {N : ℕ} {g : WithConv (H →ₐ[k] R⸨X⸩)} :
    g⁻¹ ∈ poleBoundedLoops k x R N ↔ g ∈ poleBoundedLoops k x R N := by
  simp only [mem_poleBoundedLoops_iff, inv_inv, and_comm]

variable (k x R) in
/-- The pieces increase with the level. -/
theorem poleBoundedLoops_mono : Monotone (poleBoundedLoops k x R) := by
  intro N M hNM g hg i
  have hle : lattice R R (-N) ≤ lattice R R (-M) := lattice_antitone (by omega)
  exact ⟨hle (hg i).1, hle (hg i).2⟩

/-- The pieces are stable under coefficient maps: if `g'` is obtained from `g` by applying a
`k`-algebra map `φ : R → S` to every coefficient, and `g` is pole-bounded of level `N`, so is
`g'`. -/
theorem mem_poleBoundedLoops_of_map {S : Type*} [CommRing S] [Algebra k S] (φ : R →ₐ[k] S)
    {N : ℕ} {g : WithConv (H →ₐ[k] R⸨X⸩)} {g' : WithConv (H →ₐ[k] S⸨X⸩)}
    (hg' : ∀ h, g'.ofConv h = (g.ofConv h).map φ) (hg : g ∈ poleBoundedLoops k x R N) :
    g' ∈ poleBoundedLoops k x S N := by
  have hmap {f : R⸨X⸩} (hf : f ∈ lattice R R (-N)) : f.map φ ∈ lattice S S (-N) :=
    mem_lattice_iff.2 fun n hn ↦ by rw [map_coeff, mem_lattice_iff.1 hf n hn, map_zero]
  rw [mem_poleBoundedLoops_iff_antipode] at hg ⊢
  exact fun i ↦ ⟨hg' (x i) ▸ hmap (hg i).1, hg' _ ▸ hmap (hg i).2⟩

end Pieces

section Generated

variable (R : Type w) [CommRing R] [Algebra k R]

/-- For a generating family, the pole-bounded loops of level `0` are the positive loops: the
image of `G(R⟦X⟧)` in `G(R⸨X⸩)`. -/
theorem poleBoundedLoops_zero (hx : Algebra.adjoin k (Set.range x) = ⊤) :
    poleBoundedLoops k x R 0 =
      Set.range (AlgHom.mapValue (H := H) (HahnSeries.ofPowerSeriesAlg ℤ k :
        PowerSeries R →ₐ[k] R⸨X⸩)) := by
  ext g
  rw [← MonoidHom.coe_mrange, SetLike.mem_coe,
    AlgHom.mem_mrange_mapValue_iff HahnSeries.ofPowerSeries_injective]
  have hrange {f : R⸨X⸩} : f ∈ (HahnSeries.ofPowerSeriesAlg ℤ k :
      PowerSeries R →ₐ[k] R⸨X⸩).range ↔ f ∈ lattice R R 0 := by
    rw [mem_lattice_zero_iff, AlgHom.mem_range]
    rfl
  simp only [hrange, mem_poleBoundedLoops_iff_antipode, Nat.cast_zero, neg_zero]
  refine ⟨fun hg h ↦ ?_, fun hg i ↦ ⟨hg _, hg _⟩⟩
  obtain ⟨d, hd⟩ := exists_forall_apply_mem_lattice x hx 0 h
  simpa using hd R g.ofConv fun i ↦ by simpa using (hg i).1

/-- For a finite family, every loop is pole-bounded of some level: `LG(R)` is the union of the
pieces `LG_(≤N)(R)`. No generation hypothesis is needed. -/
theorem iUnion_poleBoundedLoops [Finite ι] : ⋃ N, poleBoundedLoops k x R N = Set.univ := by
  refine Set.eq_univ_of_forall fun g ↦ Set.mem_iUnion.2 ?_
  -- Every Laurent series lies in the lattice of its order, hence in that of level `-(-ord).toNat`.
  have hmem (f : R⸨X⸩) : f ∈ lattice R R (-((-f.order).toNat : ℕ)) :=
    lattice_antitone (a := -((-f.order).toNat : ℕ)) (b := f.order) (by omega)
      (mem_lattice_iff.2 fun _ hn ↦ coeff_eq_zero_of_lt_order hn)
  obtain ⟨N, hN⟩ := (Set.finite_range fun i ↦
    max (-(g.ofConv (x i)).order).toNat (-(g⁻¹.ofConv (x i)).order).toNat).bddAbove
  refine ⟨N, fun i ↦ ⟨?_, ?_⟩⟩ <;>
  · refine lattice_antitone ?_ (hmem _)
    have := hN ⟨i, rfl⟩
    simp only [max_le_iff] at this
    omega

/-- If `x` generates `H` and `y` is a finite family, each piece of level `N` for `x` lies in a
piece for `y`, of a level `M` depending only on `x`, `y` and `N`, not on the coefficient algebra.
Applied in both directions, the pieces of two finite generating families are cofinal in each
other. -/
theorem exists_poleBoundedLoops_subset (hx : Algebra.adjoin k (Set.range x) = ⊤) {κ : Type*}
    [Finite κ] (y : κ → H) (N : ℕ) :
    ∃ M : ℕ, ∀ (R : Type w) [CommRing R] [Algebra k R],
      poleBoundedLoops k x R N ⊆ poleBoundedLoops k y R M := by
  choose d hd using exists_forall_apply_mem_lattice.{u, v, w} x hx N
  obtain ⟨D, hD⟩ := (Set.finite_range fun j ↦ max (d (y j)) (d (antipode k (y j)))).bddAbove
  refine ⟨N * D, fun R _ _ g hg ↦ mem_poleBoundedLoops_iff_antipode.2 fun j ↦ ?_⟩
  have hgx : ∀ i, g.ofConv (x i) ∈ lattice R R (-N) := fun i ↦ (mem_poleBoundedLoops_iff.1 hg i).1
  have hDj := hD ⟨j, rfl⟩
  simp only [max_le_iff] at hDj
  have hle {e : ℕ} (he : e ≤ D) : lattice R R (-(N * e : ℕ)) ≤ lattice R R (-(N * D : ℕ)) :=
    lattice_antitone (by have := Nat.mul_le_mul_left N he; omega)
  exact ⟨hle hDj.1 (hd _ R g.ofConv hgx), hle hDj.2 (hd _ R g.ofConv hgx)⟩

end Generated

end HopfAlgebra

end TauCeti
