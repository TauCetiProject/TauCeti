/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.Filter.Cofinite
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.Topology.Maps.Basic
public import TauCeti.NumberTheory.NumberField.AbsoluteGaloisGroup.Decomposition

/-!
# The filter of most Frobenii

Let `F` be a field, `G_F = Field.absoluteGaloisGroup F` with its Krull topology, and `O` the
integral closure of `𝓞 F` in `F^alg = AlgebraicClosure F`. A **Frobenius datum** over `F`
(`TauCeti.GaloisRep.FrobeniusDatum F`) is a triple `(w, Q, s)` of a finite place `w` of `F` whose
residue field has prime order `q_w`, a maximal ideal `Q` of `O` over `w`, and a geometric Frobenius
`s ∈ G_F` at `Q`, that is, `s⁻¹` is an arithmetic Frobenius at `Q`
(`TauCeti.GaloisRep.IsArithFrobAtIntegralPrime`); its norm is `q_w`. The maximal ideals of `O`
are the finite places of `F^alg` (`TauCeti.GaloisRep.finitePlaceEquivMaximalIdeal`).

A set `X` of Frobenius data *contains most Frobenii* if every nonempty open `V ⊆ G_F` contains a
nonempty open `O` such that, for all but finitely many places `w`, `X` contains every Frobenius
datum `(w, Q, s)` with `s ∈ O`. These sets form the filter `TauCeti.GaloisRep.mostFrobenii F`, a
replacement for "a set of places of density one".

The filter is first built for any type `D` of data with maps `place : D → P` to a type of places and
`frob : D → G` to a topological space (`TauCeti.GaloisRep.mostFrobeniiOf`), where its filter
properties, the passage from cofinitely many places
(`TauCeti.GaloisRep.tendsto_place_mostFrobeniiOf`) and the transport along an open embedding
(`TauCeti.GaloisRep.eventually_mostFrobeniiOf_of_isOpenEmbedding`) are proved; the number-field
statements specialise these.

Nothing here shows that the filter is proper: without Chebotarev's density theorem it may be `⊥`,
for instance when there are no Frobenius data at all. Density of the Frobenius elements of a member,
and properness of `mostFrobeniiAt F g`, are not proved in this file.

## Main definitions

* `TauCeti.GaloisRep.mostFrobeniiOf place frob`: the filter of most Frobenii for data `D` with
  `place : D → P` and `frob : D → G`.
* `TauCeti.GaloisRep.FrobeniusDatum F`: the Frobenius data `(w, Q, s)` over `F`.
* `TauCeti.GaloisRep.mostFrobenii F`: the filter of most Frobenii on Frobenius data over `F`.
* `TauCeti.GaloisRep.mostFrobeniiAt F g`: most Frobenii at `g ∈ G_F`, the meet of
  `mostFrobenii F` with `s → g`.

## Main results

* `TauCeti.GaloisRep.mem_mostFrobenii_iff`: membership in `mostFrobenii F`, unfolded.
* `TauCeti.GaloisRep.mostFrobeniiAt_le_mostFrobenii`,
  `TauCeti.GaloisRep.tendsto_frob_mostFrobeniiAt`: most Frobenii at `g` is finer than most
  Frobenii, and along it the Frobenius element tends to `g`.
* `TauCeti.GaloisRep.eventually_mostFrobenii`: a property of all but finitely many finite places
  of `F` holds at the place of most Frobenius data.
* `TauCeti.GaloisRep.eventually_mostFrobenii_of_isOpenEmbedding`: for an open embedding
  `φ : G_E → G_F` and a map `π` of finite places, if `p` holds for most Frobenius data over `E`,
  then for most Frobenius data `y` over `F`, `p` holds for every datum `x` over `E` with
  `π (place x) = place y` and `φ (frob x) = frob y`.

## References

* The statements follow the formal proof in the folder `grh` of
  https://github.com/lsernau/grh-lean at commit 72fead102f663d5c7a407964a13dc0cf9d977207,
  `Lib/GaloisRep/Main/Defs` (`New.FrobeniusDatum`, `New.mostFrobenii`, `New.mostFrobeniiAt`,
  `New.eventually_mostFrobenii`, `New.eventually_mostFrobenii_of_isOpenEmbedding`).
-/

public section

noncomputable section

open Filter Topology NumberField IsDedekindDomain

namespace TauCeti.GaloisRep

/-! ### The filter of most Frobenii for abstract data -/

section Abstract

variable {D P G : Type*} [TopologicalSpace G]

/-- The **filter of most Frobenii** for data `D` with a place `place d ∈ P` and a Frobenius
element `frob d ∈ G`: a set `X ⊆ D` belongs to it if every nonempty open `V ⊆ G` contains a nonempty
open `O` such that, for all but finitely many `q ∈ P`, `X` contains every datum `d` with
`place d = q` and `frob d ∈ O` (`TauCeti.GaloisRep.mem_mostFrobeniiOf`). -/
def mostFrobeniiOf (place : D → P) (frob : D → G) : Filter D where
  sets := {X | ∀ V : Set G, IsOpen V → V.Nonempty → ∃ O ⊆ V, IsOpen O ∧ O.Nonempty ∧
    ∀ᶠ q in cofinite, ∀ d, place d = q → frob d ∈ O → d ∈ X}
  univ_sets V hV hne := ⟨V, subset_rfl, hV, hne, .of_forall fun _ _ _ _ ↦ trivial⟩
  sets_of_superset hX hXY V hV hne := (hX V hV hne).imp fun _ ⟨hOV, hO, hOne, hev⟩ ↦
    ⟨hOV, hO, hOne, hev.mono fun _ h d hd hdO ↦ hXY (h d hd hdO)⟩
  inter_sets hX hY V hV hne := by
    -- shrink `V` to `O₁` for `X`, then `O₁` to `O₂` for `Y`
    obtain ⟨O₁, h₁V, h₁, h₁ne, hev₁⟩ := hX V hV hne
    obtain ⟨O₂, h₂₁, h₂, h₂ne, hev₂⟩ := hY O₁ h₁ h₁ne
    exact ⟨O₂, h₂₁.trans h₁V, h₂, h₂ne, (hev₁.and hev₂).mono fun _ h d hd hdO ↦
      ⟨h.1 d hd (h₂₁ hdO), h.2 d hd hdO⟩⟩

variable {place : D → P} {frob : D → G}

/-- Membership in the filter of most Frobenii, unfolded. -/
theorem mem_mostFrobeniiOf {X : Set D} :
    X ∈ mostFrobeniiOf place frob ↔ ∀ V : Set G, IsOpen V → V.Nonempty →
      ∃ O ⊆ V, IsOpen O ∧ O.Nonempty ∧ ∀ᶠ q in cofinite, ∀ d, place d = q → frob d ∈ O → d ∈ X :=
  Iff.rfl

/-- If all but finitely many places have a property, then so does the place of most data: `place`
tends to the cofinite filter along the filter of most Frobenii. -/
theorem tendsto_place_mostFrobeniiOf : Tendsto place (mostFrobeniiOf place frob) cofinite :=
  fun S hS ↦ mem_mostFrobeniiOf.2 fun V hV hne ↦ ⟨V, subset_rfl, hV, hne,
    Filter.mem_of_superset hS fun q hq d hd _ ↦ by rwa [Set.mem_preimage, hd]⟩

/-- **Transport along an open embedding.** Let `φ : G → G'` be an open embedding and `π : P → P'`
any map. If `p` holds for most data `x` of `D`, then for most data `y` of `D'`, `p` holds for every
`x` with `π (place x) = place' y` and `φ (frob x) = frob' y`. -/
theorem eventually_mostFrobeniiOf_of_isOpenEmbedding {D' P' G' : Type*} [TopologicalSpace G']
    {place' : D' → P'} {frob' : D' → G'} {φ : G → G'} (hφ : Topology.IsOpenEmbedding φ)
    (π : P → P') {p : D → Prop} (hp : ∀ᶠ x in mostFrobeniiOf place frob, p x) :
    ∀ᶠ y in mostFrobeniiOf place' frob',
      ∀ x, π (place x) = place' y → φ (frob x) = frob' y → p x := by
  rw [Filter.Eventually, mem_mostFrobeniiOf] at hp ⊢
  intro V hV hne
  by_cases h : (φ ⁻¹' V).Nonempty
  · -- pull `V` back to `G`, shrink it there, and push the result forward
    obtain ⟨O, hOV, hO, hOne, hev⟩ := hp _ (hV.preimage hφ.continuous) h
    refine ⟨φ '' O, Set.image_subset_iff.2 hOV, hφ.isOpenMap _ hO, hOne.image φ, ?_⟩
    rw [eventually_cofinite] at hev ⊢
    refine (hev.image π).subset fun q hq ↦ ?_
    simp only [Set.mem_ofPred_eq, not_forall] at hq
    obtain ⟨y, rfl, ⟨g, hgO, hgy⟩, x, hx, hφx, hpx⟩ := hq
    refine ⟨place x, ?_, hx⟩
    simp only [Set.mem_ofPred_eq, not_forall]
    exact ⟨x, rfl, hφ.injective (hφx.trans hgy.symm) ▸ hgO, hpx⟩
  · -- no `frob' y ∈ V` is in the image of `φ`, so `V` itself works
    refine ⟨V, subset_rfl, hV, hne, .of_forall fun _ y _ hy x _ hx ↦ (h ⟨frob x, ?_⟩).elim⟩
    rwa [Set.mem_preimage, hx]

end Abstract

/-! ### Frobenius data over a field -/

variable (F : Type*) [Field F]

/-- A **Frobenius datum** over `F`: a finite place `w` of `F` whose residue field has prime order
`q_w`, a maximal ideal `Q` of the integral closure `O` of `𝓞 F` in `F^alg` lying over `w` (a finite
place of `F^alg` above `w`), and a geometric Frobenius `s ∈ G_F` at `Q` of norm `q_w`, that is, an
element whose inverse is an arithmetic Frobenius at `Q`. -/
@[ext]
structure FrobeniusDatum where
  /-- The finite place `w` of `F`. -/
  place : HeightOneSpectrum (𝓞 F)
  /-- The residue field of `w` has prime order `q_w`. -/
  prime_natCard : (Nat.card (𝓞 F ⧸ place.asIdeal)).Prime
  /-- The maximal ideal `Q` of `O` above `w`. -/
  primeAbove : Ideal (integralClosure (𝓞 F) (AlgebraicClosure F))
  /-- `Q` is a maximal ideal of `O`. -/
  isMaximal_primeAbove : primeAbove.IsMaximal
  /-- `Q` lies over `w`. -/
  under_primeAbove : primeAbove.under (𝓞 F) = place.asIdeal
  /-- The geometric Frobenius `s` at `Q`. -/
  frob : Field.absoluteGaloisGroup F
  /-- `s⁻¹` is an arithmetic Frobenius at `Q`; its norm is the order of `𝓞 F ⧸ w`, which is
  `q_w` by `under_primeAbove`. -/
  isArithFrobAtIntegralPrime_inv_frob : IsArithFrobAtIntegralPrime frob⁻¹ primeAbove

attribute [instance] FrobeniusDatum.isMaximal_primeAbove

/-- The **filter of most Frobenii** on Frobenius data over `F`: a set `X` of Frobenius data belongs
to it if every nonempty open `V ⊆ G_F` contains a nonempty open `O` such that, for all but finitely
many finite places `w` of `F`, `X` contains every Frobenius datum `(w, Q, s)` with `s ∈ O`
(`TauCeti.GaloisRep.mem_mostFrobenii_iff`). -/
def mostFrobenii : Filter (FrobeniusDatum F) :=
  mostFrobeniiOf FrobeniusDatum.place FrobeniusDatum.frob

/-- **Most Frobenii at `g ∈ G_F`**: the meet of the filter of most Frobenii with the condition that
the Frobenius element `s` of the datum tends to `g`. -/
def mostFrobeniiAt (g : Field.absoluteGaloisGroup F) : Filter (FrobeniusDatum F) :=
  mostFrobenii F ⊓ comap FrobeniusDatum.frob (𝓝 g)

variable {F}

/-- `mostFrobenii F` is the filter of most Frobenii for the place and Frobenius element of a
Frobenius datum. -/
theorem mostFrobenii_def :
    mostFrobenii F = mostFrobeniiOf FrobeniusDatum.place FrobeniusDatum.frob := by
  rw [mostFrobenii]

/-- Most Frobenii at `g` is the meet of most Frobenii with `s → g`. -/
theorem mostFrobeniiAt_def (g : Field.absoluteGaloisGroup F) :
    mostFrobeniiAt F g = mostFrobenii F ⊓ comap FrobeniusDatum.frob (𝓝 g) := by
  rw [mostFrobeniiAt]

/-- Most Frobenii at `g` is finer than most Frobenii. -/
theorem mostFrobeniiAt_le_mostFrobenii (g : Field.absoluteGaloisGroup F) :
    mostFrobeniiAt F g ≤ mostFrobenii F := by
  rw [mostFrobeniiAt_def]
  exact inf_le_left

/-- Along most Frobenii at `g`, the Frobenius element `s` of the datum tends to `g`. -/
theorem tendsto_frob_mostFrobeniiAt (g : Field.absoluteGaloisGroup F) :
    Tendsto FrobeniusDatum.frob (mostFrobeniiAt F g) (𝓝 g) := by
  rw [mostFrobeniiAt_def]
  exact tendsto_comap.mono_left inf_le_right

/-- A set `X` of Frobenius data contains most Frobenii if and only if every nonempty open
`V ⊆ G_F` contains a nonempty open `O` such that, for all but finitely many finite places `w`,
every Frobenius datum at `w` with Frobenius element in `O` lies in `X`. -/
theorem mem_mostFrobenii_iff {X : Set (FrobeniusDatum F)} :
    X ∈ mostFrobenii F ↔ ∀ V : Set (Field.absoluteGaloisGroup F), IsOpen V → V.Nonempty →
      ∃ O ⊆ V, IsOpen O ∧ O.Nonempty ∧
        ∀ᶠ w in cofinite, ∀ x : FrobeniusDatum F, x.place = w → x.frob ∈ O → x ∈ X :=
  Iff.rfl

/-- If all but finitely many finite places of `F` have a property, then so does the place of most
Frobenius data over `F`. -/
theorem eventually_mostFrobenii {R : HeightOneSpectrum (𝓞 F) → Prop}
    (h : ∀ᶠ w in cofinite, R w) : ∀ᶠ x in mostFrobenii F, R x.place :=
  tendsto_place_mostFrobeniiOf.eventually h

/-- **Transport of most Frobenii along an open embedding.** Let `φ : G_E → G_F` be an open
embedding and `π` a map from the finite places of `E` to those of `F`. If `p` holds for most
Frobenius data over `E`, then for most Frobenius data `y` over `F`, `p` holds for every Frobenius
datum `x` over `E` with `π (place x) = place y` and `φ (frob x) = frob y`. -/
theorem eventually_mostFrobenii_of_isOpenEmbedding {E : Type*} [Field E]
    {φ : Field.absoluteGaloisGroup E → Field.absoluteGaloisGroup F}
    (hφ : Topology.IsOpenEmbedding φ) (π : HeightOneSpectrum (𝓞 E) → HeightOneSpectrum (𝓞 F))
    {p : FrobeniusDatum E → Prop} (hp : ∀ᶠ x in mostFrobenii E, p x) :
    ∀ᶠ y in mostFrobenii F, ∀ x : FrobeniusDatum E, π x.place = y.place → φ x.frob = y.frob → p x :=
  eventually_mostFrobeniiOf_of_isOpenEmbedding hφ π hp

end TauCeti.GaloisRep
