/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Invariants
public import Mathlib.RepresentationTheory.Rep.Basic
public import TauCeti.RepresentationTheory.Coinvariants
import TauCeti.Algebra.Exact.Pi
import TauCeti.RepresentationTheory.Rep.TensorShortExact

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
* `Rep.piLift f`: the morphism into `Rep.pi M` with prescribed components `f i : A ⟶ M i`.
* `Rep.piProj M i`: the projection of `Rep.pi M` onto `M i`.
* `Rep.piMap f`: the product of a family of morphisms `f i : M i ⟶ N i`.
* `Rep.resPiIso M f`: restriction along `f` commutes with products.

## Main results

* `Representation.mem_invariants_pi_iff`: an element of the product is invariant exactly when
  every component is.
* `Representation.norm_pi_apply`: the norm of the product acts factor by factor.
* `Representation.mem_ker_norm_pi_iff`: an element of the product has norm zero exactly when
  every component does.
* `Representation.mem_coinvariantsKer_pi_iff`: for a finite monoid, an element of the product lies
  in the coinvariant kernel exactly when every component does.
* `Rep.shortExact_pi`: a product of short exact sequences of representations is short exact.
-/

public section

namespace Representation

section Semiring

variable {k G ι : Type*} [Semiring k] {V : ι → Type*}
  [∀ i, AddCommMonoid (V i)] [∀ i, Module k (V i)]

section Monoid

variable [Monoid G] (ρ : ∀ i, Representation k G (V i))

/-- The product of a family of representations `ρ i` on `V i`: the representation of `G` on
`∀ i, V i` acting on each component by `ρ i`. -/
noncomputable def pi : Representation k G (∀ i, V i) where
  toFun g := LinearMap.piMap fun i ↦ ρ i g
  map_one' := by ext; simp
  map_mul' g h := by ext; simp

@[simp]
theorem pi_apply (g : G) (x : ∀ i, V i) (i : ι) : pi ρ g x i = ρ i g (x i) := (rfl)

end Monoid

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

open CategoryTheory

universe w

section Semiring

variable {k G : Type*} [Semiring k] [Monoid G] {ι : Type w} (M : ι → Rep.{w} k G)

/-- The product of a family of representations, as an object of `Rep k G`. -/
noncomputable abbrev pi : Rep.{w} k G := Rep.of (Representation.pi fun i ↦ (M i).ρ)

variable {M}

/-- **The universal property of the product**: the morphism into `Rep.pi M` whose components are
the morphisms `f i : A ⟶ M i`. -/
noncomputable def piLift {A : Rep.{w} k G} (f : ∀ i, A ⟶ M i) : A ⟶ pi M :=
  ofHom (LinearMap.intertwiningMap_of_isIntertwiningMap _ _
    (LinearMap.pi fun i ↦ (f i).hom.toLinearMap) fun g x ↦ funext fun i ↦ hom_comm_apply (f i) g x)

/-- The components of `Rep.piLift f` are the morphisms `f i`. -/
@[simp]
theorem piLift_hom_apply {A : Rep.{w} k G} (f : ∀ i, A ⟶ M i) (x : A) (i : ι) :
    (piLift f).hom x i = (f i).hom x :=
  (rfl)

variable (M) in
/-- The projection of `Rep.pi M` onto the factor `M i`. -/
noncomputable def piProj (i : ι) : pi M ⟶ M i :=
  ofHom (LinearMap.intertwiningMap_of_isIntertwiningMap _ _ (LinearMap.proj i) fun _ _ ↦ rfl)

/-- `Rep.piProj M i` takes the `i`-th component. -/
@[simp]
theorem piProj_hom_apply (i : ι) (x : pi M) : (piProj M i).hom x = x i :=
  (rfl)

/-- The `i`-th component of `Rep.piLift f` is `f i`. -/
@[reassoc (attr := simp)]
theorem piLift_piProj {A : Rep.{w} k G} (f : ∀ i, A ⟶ M i) (i : ι) :
    piLift f ≫ piProj M i = f i :=
  (rfl)

/-- The product of a family of morphisms `f i : M i ⟶ N i`, acting factor by factor. -/
noncomputable def piMap {N : ι → Rep.{w} k G} (f : ∀ i, M i ⟶ N i) : pi M ⟶ pi N :=
  piLift fun i ↦ piProj M i ≫ f i

/-- `Rep.piMap f` applies `f i` to the `i`-th component. -/
@[simp]
theorem piMap_hom_apply {N : ι → Rep.{w} k G} (f : ∀ i, M i ⟶ N i) (x : pi M) (i : ι) :
    (piMap f).hom x i = (f i).hom (x i) :=
  (rfl)

/-- The `i`-th component of `Rep.piMap f` is `f i` on the `i`-th factor. -/
@[reassoc (attr := simp)]
theorem piMap_piProj {N : ι → Rep.{w} k G} (f : ∀ i, M i ⟶ N i) (i : ι) :
    piMap f ≫ piProj N i = piProj M i ≫ f i :=
  (rfl)

variable (M) in
/-- **Restriction commutes with products**: the restriction of `Rep.pi M` along `f : H →* G` is
the product of the restrictions, by the identity of the underlying module. -/
noncomputable def resPiIso {H : Type*} [Monoid H] (f : H →* G) :
    res f (pi M) ≅ pi fun i ↦ res f (M i) :=
  mkIso (.mk (LinearEquiv.refl k _) fun _ ↦ rfl)

/-- `Rep.resPiIso` is the identity on underlying elements. -/
@[simp]
theorem resPiIso_hom_hom_apply {H : Type*} [Monoid H] (f : H →* G) (x : pi M) :
    (resPiIso M f).hom.hom x = x :=
  (rfl)

end Semiring

section Ring

variable {k G : Type*} [Ring k] [Monoid G] {ι : Type w}

/-- **A product of short exact sequences of representations is short exact**: injectivity,
surjectivity and exactness of linear maps are all checked factor by factor. -/
theorem shortExact_pi (S : ι → ShortComplex (Rep.{w} k G)) (hS : ∀ i, (S i).ShortExact) :
    (ShortComplex.mk (piMap fun i ↦ (S i).f) (piMap fun i ↦ (S i).g)
      (by ext x i; exact congr($((S i).zero).hom (x i)))).ShortExact := by
  have hf (i : ι) := (Rep.mono_iff_injective _).1 (hS i).mono_f
  have hg (i : ι) := (Rep.epi_iff_surjective _).1 (hS i).epi_g
  have hfg (i : ι) := (exact_iff_function_exact _).1 (hS i).exact
  exact .mk' ((exact_iff_function_exact _).2 (Function.Exact.piMap hfg))
    ((Rep.mono_iff_injective _).2 (Function.Injective.piMap hf))
    ((Rep.epi_iff_surjective _).2 (Function.Surjective.piMap hg))

end Ring

end Rep
