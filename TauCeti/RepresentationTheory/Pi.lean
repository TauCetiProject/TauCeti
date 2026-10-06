/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Invariants
public import Mathlib.RepresentationTheory.Rep.Basic
public import TauCeti.RepresentationTheory.Coinvariants

/-!
# Products of representations

Mathlib forms the direct sum `Representation.directSum` and the binary product
`Representation.prod` of representations, but not the product of an arbitrary family. This file
defines it: for representations `ρ i` of a monoid `G` on modules `V i`, the representation
`Representation.pi ρ` acts on `∀ i, V i` factor by factor. The index type is arbitrary. Infinite
products are the case of interest, as in the unit part `∏_v ∏_{w ∣ v} 𝒪_wˣ` of the `S`-ideles of
a Galois extension of number fields, which is a product of representations of the Galois group
indexed by the places `v` outside `S`.

The invariants, the norm and, for a finite monoid, the coinvariant kernel of the product are
computed factor by factor. The last of these uses the finiteness of `G`: an element of the
coinvariant kernel is a sum `∑ g, (ρ g (y g) - y g)` with one term for each `g`, and such sums can
be chosen in every factor at once.

## Main definitions

* `Representation.pi ρ`: the product of a family of representations.
* `Rep.pi M`: the product of a family of objects of `Rep k G`.

## Main results

* `Representation.mem_invariants_pi_iff`: an element of the product is invariant exactly when
  every component is.
* `Representation.norm_pi_apply`: the norm of the product acts factor by factor.
* `Representation.mem_ker_norm_pi_iff`: an element of the product has norm zero exactly when
  every component does.
* `Representation.mem_coinvariantsKer_pi_iff`: for a finite monoid, an element of the product lies
  in the coinvariant kernel exactly when every component does.
-/

public section

namespace Representation

section Semiring

variable {k G ι : Type*} [CommSemiring k] [Monoid G] {V : ι → Type*}
  [∀ i, AddCommMonoid (V i)] [∀ i, Module k (V i)] (ρ : ∀ i, Representation k G (V i))

/-- The product of a family of representations `ρ i` on `V i`: the representation of `G` on
`∀ i, V i` acting on each component by `ρ i`. -/
noncomputable def pi : Representation k G (∀ i, V i) where
  toFun g := LinearMap.piMap fun i ↦ ρ i g
  map_one' := by ext; simp
  map_mul' g h := by ext; simp

@[simp]
theorem pi_apply (g : G) (x : ∀ i, V i) (i : ι) : pi ρ g x i = ρ i g (x i) := (rfl)

end Semiring

section Ring

variable {k G ι : Type*} [CommRing k] {V : ι → Type*} [∀ i, AddCommGroup (V i)]
  [∀ i, Module k (V i)]

/-- An element of a product of representations is invariant exactly when each of its components
is. -/
theorem mem_invariants_pi_iff [Group G] (ρ : ∀ i, Representation k G (V i)) {x : ∀ i, V i} :
    x ∈ (pi ρ).invariants ↔ ∀ i, x i ∈ (ρ i).invariants := by
  simp only [mem_invariants, funext_iff, pi_apply]
  exact forall_comm

/-- The norm of a product of representations of a finite group acts factor by factor. -/
@[simp]
theorem norm_pi_apply [Group G] [Fintype G] (ρ : ∀ i, Representation k G (V i)) (x : ∀ i, V i)
    (i : ι) : (pi ρ).norm x i = (ρ i).norm (x i) := by
  simp [Representation.norm, Finset.sum_apply]

/-- An element of a product of representations of a finite group has norm zero exactly when each
of its components does. -/
theorem mem_ker_norm_pi_iff [Group G] [Fintype G] (ρ : ∀ i, Representation k G (V i))
    {x : ∀ i, V i} : x ∈ LinearMap.ker (pi ρ).norm ↔ ∀ i, x i ∈ LinearMap.ker (ρ i).norm := by
  simp only [LinearMap.mem_ker, funext_iff, norm_pi_apply, Pi.zero_apply]

/-- For a finite monoid, an element of a product of representations lies in the coinvariant
kernel exactly when each of its components does. -/
@[simp]
theorem mem_coinvariantsKer_pi_iff [Monoid G] [Finite G] (ρ : ∀ i, Representation k G (V i))
    {x : ∀ i, V i} : x ∈ Coinvariants.ker (pi ρ) ↔ ∀ i, x i ∈ Coinvariants.ker (ρ i) := by
  have := Fintype.ofFinite G
  simp only [mem_coinvariantsKer_iff_exists_sum]
  constructor
  · rintro ⟨y, rfl⟩ i
    exact ⟨fun g ↦ y g i, by simp [Finset.sum_apply]⟩
  · intro h
    choose y hy using h
    exact ⟨fun g i ↦ y i g, funext fun i ↦ by simpa [Finset.sum_apply] using hy i⟩

end Ring

end Representation

namespace Rep

universe w

variable {k G : Type*} [CommRing k] [Monoid G] {ι : Type w} (M : ι → Rep.{w} k G)

/-- The product of a family of representations, as an object of `Rep k G`. -/
noncomputable abbrev pi : Rep.{w} k G := Rep.of (Representation.pi fun i ↦ (M i).ρ)

end Rep
