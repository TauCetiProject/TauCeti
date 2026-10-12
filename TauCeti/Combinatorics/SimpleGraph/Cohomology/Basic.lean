/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Dart
public import Mathlib.GroupTheory.QuotientGroup.Defs

/-!
# The first cohomology of a simple graph

A simple graph is a one-dimensional cell complex, with its vertices as `0`-cells and its edges as
`1`-cells. With coefficients in a commutative group `A`, written multiplicatively, a `1`-cochain
is therefore a function on the darts (oriented edges) which is inverted by reversing a dart, the
coboundary of a function `φ` on the vertices is the `1`-cochain `d ↦ φ d.snd / φ d.fst`, and,
since there are no `2`-cells, every `1`-cochain is a cocycle. The first cohomology `H¹(G, A)` is
the group of `1`-cochains modulo coboundaries.

This is the group in which Couture's classification of skew-zigzag algebras takes its values, with
`A = kˣ` the units of the coefficient ring.

## Main definitions

* `SimpleGraph.oneCochains`: the group of `A`-valued `1`-cochains of a simple graph.
* `SimpleGraph.coboundary`: the coboundary of a function on the vertices.
* `SimpleGraph.FirstCohomology`: the first cohomology group `H¹(G, A)`.
* `SimpleGraph.FirstCohomology.mk`: the cohomology class of a `1`-cochain.
* `SimpleGraph.FirstCohomology.lift`: the universal property of first cohomology.

## Main results

* `SimpleGraph.FirstCohomology.mk_surjective`: every cohomology class is the class of a cochain.
* `SimpleGraph.FirstCohomology.mk_eq_one_iff`: a cochain has trivial class exactly when it is a
  coboundary.
* `SimpleGraph.FirstCohomology.mk_eq_mk_iff`: two cochains have the same class exactly when they
  differ by a coboundary.

## References

C. Couture, *Skew-Zigzag Algebras*, Section 4, https://arxiv.org/abs/1509.08405, for the first
cohomology of a graph with coefficients in the units of a field.
-/

public section

namespace SimpleGraph

variable {V : Type*} (G : SimpleGraph V) (A : Type*) [CommGroup A]

/-- The group of `A`-valued **`1`-cochains** of a simple graph: the functions on its darts which
are inverted by reversing a dart. -/
def oneCochains : Subgroup (G.Dart → A) where
  carrier := {σ | ∀ d : G.Dart, σ d.symm = (σ d)⁻¹}
  mul_mem' {σ τ} (hσ : ∀ d : G.Dart, σ d.symm = (σ d)⁻¹) (hτ : ∀ d : G.Dart, τ d.symm = (τ d)⁻¹)
      d := by
    simp only [Pi.mul_apply, hσ d, hτ d, mul_inv]
  one_mem' d := by simp
  inv_mem' {σ} (hσ : ∀ d : G.Dart, σ d.symm = (σ d)⁻¹) d := by
    simp only [Pi.inv_apply, hσ d]

variable {G A}

/-- A function on the darts is a `1`-cochain exactly when reversing a dart inverts its value. -/
theorem mem_oneCochains_iff {σ : G.Dart → A} :
    σ ∈ G.oneCochains A ↔ ∀ d : G.Dart, σ d.symm = (σ d)⁻¹ := Iff.rfl

/-- The value of a `1`-cochain on a reversed dart is the inverse of its value on the dart. -/
@[simp]
theorem oneCochains_apply_symm (σ : G.oneCochains A) (d : G.Dart) :
    (σ : G.Dart → A) d.symm = ((σ : G.Dart → A) d)⁻¹ :=
  σ.property d

variable (G A)

/-- The **coboundary** of a function `φ` on the vertices of a simple graph: the `1`-cochain whose
value on a dart is the value of `φ` at its target divided by the value at its source. -/
def coboundary : (V → A) →* G.oneCochains A where
  toFun φ := ⟨fun d ↦ φ d.snd / φ d.fst, fun d ↦ by simp [Dart.symm, inv_div]⟩
  map_one' := by
    ext d
    simp
  map_mul' φ ψ := by
    ext d
    simp [mul_div_mul_comm]

variable {G A}

/-- The value of a coboundary on a dart is the quotient of the values at its target and source. -/
@[simp]
theorem coboundary_apply (φ : V → A) (d : G.Dart) :
    (G.coboundary A φ : G.Dart → A) d = φ d.snd / φ d.fst := (rfl)

variable (G A)

/-- The **first cohomology** `H¹(G, A)` of a simple graph with coefficients in a commutative
group: its `1`-cochains modulo the coboundaries of functions on its vertices. -/
def FirstCohomology : Type _ :=
  G.oneCochains A ⧸ (G.coboundary A).range

namespace FirstCohomology

instance : CommGroup (G.FirstCohomology A) :=
  inferInstanceAs (CommGroup (G.oneCochains A ⧸ (G.coboundary A).range))

/-- The **cohomology class** of a `1`-cochain. -/
def mk : G.oneCochains A →* G.FirstCohomology A :=
  QuotientGroup.mk' _

variable {G A}

/-- Every cohomology class is the class of a `1`-cochain. -/
theorem mk_surjective : Function.Surjective (mk G A) :=
  QuotientGroup.mk'_surjective _

variable {M : Type*} [Monoid M]

/-- **Universal property of first cohomology.** A homomorphism from `1`-cochains which is trivial
on coboundaries descends to a homomorphism from `H¹(G, A)`. -/
def lift (f : G.oneCochains A →* M) (h : (G.coboundary A).range ≤ f.ker) :
    G.FirstCohomology A →* M :=
  QuotientGroup.lift _ f h

/-- The descended homomorphism agrees with the original homomorphism on cohomology classes. -/
@[simp]
theorem lift_mk (f : G.oneCochains A →* M) (h : (G.coboundary A).range ≤ f.ker)
    (c : G.oneCochains A) : lift f h (mk G A c) = f c :=
  QuotientGroup.lift_mk' _ h c

/-- The lift is the unique homomorphism from `H¹(G, A)` agreeing with the original homomorphism
on cohomology classes. -/
theorem lift_unique (f : G.oneCochains A →* M) (h : (G.coboundary A).range ≤ f.ker)
    (g : G.FirstCohomology A →* M) (hg : ∀ c, g (mk G A c) = f c) : g = lift f h :=
  MonoidHom.ext fun x ↦ by
    obtain ⟨c, rfl⟩ := mk_surjective x
    exact (hg c).trans (lift_mk f h c).symm

/-- **A `1`-cochain has trivial cohomology class exactly when it is a coboundary.** -/
theorem mk_eq_one_iff {σ : G.oneCochains A} : mk G A σ = 1 ↔ ∃ φ : V → A, G.coboundary A φ = σ :=
  (QuotientGroup.eq_one_iff σ).trans (G.coboundary A).mem_range

/-- The cohomology class of a coboundary is trivial. -/
@[simp]
theorem mk_coboundary (φ : V → A) : mk G A (G.coboundary A φ) = 1 :=
  mk_eq_one_iff.mpr ⟨φ, rfl⟩

/-- **Two `1`-cochains have the same cohomology class exactly when they differ by a
coboundary.** -/
theorem mk_eq_mk_iff {σ τ : G.oneCochains A} :
    mk G A σ = mk G A τ ↔ ∃ φ : V → A, τ = σ * G.coboundary A φ := by
  rw [eq_comm, ← div_eq_one, ← map_div, mk_eq_one_iff]
  exact exists_congr fun φ ↦ by rw [eq_div_iff_mul_eq', eq_comm, mul_comm]

/-- The kernel of the cohomology class map consists of the coboundaries. -/
@[simp]
theorem ker_mk : (mk G A).ker = (G.coboundary A).range :=
  QuotientGroup.ker_mk' _

/-- An equivalence of one-cochain groups preserving coboundaries induces an equivalence of
first cohomology groups. -/
def congr {W : Type*} {H : SimpleGraph W} (e : G.oneCochains A ≃* H.oneCochains A)
    (he : (G.coboundary A).range.map e = (H.coboundary A).range) :
    G.FirstCohomology A ≃* H.FirstCohomology A :=
  QuotientGroup.congr _ _ e he

/-- The induced equivalence sends the class of a cochain to the class of its image. -/
@[simp]
theorem congr_mk {W : Type*} {H : SimpleGraph W} (e : G.oneCochains A ≃* H.oneCochains A)
    (he : (G.coboundary A).range.map e = (H.coboundary A).range)
    (σ : G.oneCochains A) :
    congr e he (mk G A σ) = mk H A (e σ) :=
  QuotientGroup.congr_mk' _ _ e he σ

end FirstCohomology

end SimpleGraph
