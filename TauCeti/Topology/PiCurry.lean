/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Currying and regrouping a tuple, topologically

A family of spaces indexed by a sigma type has the same sections as the curried family: the
equivalence `Equiv.piCurry` is a homeomorphism for the product topologies. Composing it with a
bijection between the sigma index and another index presents a tuple as a family of tuples.

Mathlib has `Homeomorph.piCurry` for a *product* index `X × Y`; the sigma-indexed version below is
what a varying family of index types needs.

Similarly, a family indexed by `Option ι` splits off its `none` component: the equivalence
`Equiv.piOptionEquivProd` is a homeomorphism. For cubes this identifies `I^(Option N)` with
`I × I^N`, a cube with one distinguished extra direction.

## Main declarations

* `TauCeti.piCurryHomeomorph`: `Equiv.piCurry` as a homeomorphism.
* `TauCeti.piSigmaHomeomorph`: reindex a curried dependent family along an equivalence from its
  sigma index.
* `TauCeti.piSigmaConstHomeomorph`: along an explicit equivalence from a sigma index, a
  homeomorphism between a family of tuples and a tuple in a fixed space.
* `TauCeti.piOptionEquivProdHomeomorph`: `Equiv.piOptionEquivProd` as a homeomorphism.
-/

public section

namespace TauCeti

/-- **Currying a sigma-indexed family of spaces**, as a homeomorphism. -/
def piCurryHomeomorph {ι : Type*} {κ : ι → Type*} (Y : ∀ i, κ i → Type*)
    [∀ i j, TopologicalSpace (Y i j)] : (∀ p : Σ i, κ i, Y p.1 p.2) ≃ₜ (∀ i j, Y i j) where
  toEquiv := Equiv.piCurry Y
  continuous_toFun :=
    continuous_pi fun i => continuous_pi fun j => continuous_apply (⟨i, j⟩ : Σ i, κ i)
  continuous_invFun := continuous_pi fun p => (continuous_apply p.2).comp (continuous_apply p.1)

@[simp]
theorem piCurryHomeomorph_apply {ι : Type*} {κ : ι → Type*} (Y : ∀ i, κ i → Type*)
    [∀ i j, TopologicalSpace (Y i j)] (f : ∀ p : Σ i, κ i, Y p.1 p.2) (i : ι) (j : κ i) :
    piCurryHomeomorph Y f i j = f ⟨i, j⟩ :=
  (rfl)

@[simp]
theorem piCurryHomeomorph_symm_apply {ι : Type*} {κ : ι → Type*} (Y : ∀ i, κ i → Type*)
    [∀ i j, TopologicalSpace (Y i j)] (f : ∀ i j, Y i j) (p : Σ i, κ i) :
    (piCurryHomeomorph Y).symm f p = f p.1 p.2 :=
  (rfl)

/-- **Regrouping a dependent family.** Curry a family indexed by a sigma type, then reindex its
uncurried form along an explicit equivalence. -/
def piSigmaHomeomorph {ι : Type*} {κ : ι → Type*} (Z : ι → Type*)
    [∀ i, TopologicalSpace (Z i)] {ι' : Type*} (e : (Σ i, κ i) ≃ ι') :
    (∀ i, κ i → Z i) ≃ₜ (∀ j : ι', Z (e.symm j).1) :=
  (piCurryHomeomorph fun (i : ι) (_ : κ i) => Z i).symm.trans
    (Homeomorph.piCongrLeft (Y := fun k : (Σ i, κ i) => Z k.1) e.symm).symm

@[simp]
theorem piSigmaHomeomorph_apply {ι : Type*} {κ : ι → Type*} (Z : ι → Type*)
    [∀ i, TopologicalSpace (Z i)] {ι' : Type*} (e : (Σ i, κ i) ≃ ι')
    (f : ∀ i, κ i → Z i) (j : ι') :
    piSigmaHomeomorph Z e f j = f (e.symm j).1 (e.symm j).2 :=
  (rfl)

/-- **Regrouping a tuple in a fixed space.** An explicit bijection from a sigma type to another
index type identifies a family of tuples of points of `Y` with one tuple of points of `Y`. -/
def piSigmaConstHomeomorph (Y : Type*) [TopologicalSpace Y] {ι : Type*} {κ : ι → Type*}
    {ι' : Type*} (e : (Σ i, κ i) ≃ ι') : (∀ i, κ i → Y) ≃ₜ (ι' → Y) :=
  piSigmaHomeomorph (fun _ : ι => Y) e

@[simp]
theorem piSigmaConstHomeomorph_apply (Y : Type*) [TopologicalSpace Y] {ι : Type*}
    {κ : ι → Type*} {ι' : Type*} (e : (Σ i, κ i) ≃ ι') (f : ∀ i, κ i → Y) (j : ι') :
    piSigmaConstHomeomorph Y e f j = f (e.symm j).1 (e.symm j).2 :=
  (rfl)

@[simp]
theorem piSigmaConstHomeomorph_symm_apply (Y : Type*) [TopologicalSpace Y] {ι : Type*}
    {κ : ι → Type*} {ι' : Type*} (e : (Σ i, κ i) ≃ ι') (f : ι' → Y) (i : ι)
    (j : κ i) : (piSigmaConstHomeomorph Y e).symm f i j = f (e ⟨i, j⟩) := by
  have h : (piSigmaConstHomeomorph Y e).symm f = fun i j => f (e ⟨i, j⟩) := by
    rw [Homeomorph.symm_apply_eq]
    funext k
    rw [piSigmaConstHomeomorph_apply]
    exact congrArg f (e.apply_symm_apply k).symm
  exact congrFun (congrFun h i) j

/-- **Splitting off the `none` component.** A family indexed by `Option ι` is its `none`
component together with the family of its `some` components: `Equiv.piOptionEquivProd` as a
homeomorphism. -/
def piOptionEquivProdHomeomorph {ι : Type*} (Y : Option ι → Type*)
    [∀ i, TopologicalSpace (Y i)] : (∀ i, Y i) ≃ₜ Y none × ∀ i : ι, Y (some i) where
  toEquiv := Equiv.piOptionEquivProd
  continuous_toFun :=
    (continuous_apply none).prodMk (continuous_pi fun i => continuous_apply (some i))
  continuous_invFun := continuous_pi fun o => by
    cases o with
    | none => exact continuous_fst
    | some i =>
      exact ((continuous_apply i).comp continuous_snd :
        Continuous fun x : Y none × ∀ i : ι, Y (some i) => x.2 i)

@[simp]
theorem piOptionEquivProdHomeomorph_apply {ι : Type*} (Y : Option ι → Type*)
    [∀ i, TopologicalSpace (Y i)] (f : ∀ i, Y i) :
    piOptionEquivProdHomeomorph Y f = (f none, fun i => f (some i)) :=
  (rfl)

@[simp]
theorem piOptionEquivProdHomeomorph_symm_apply_none {ι : Type*} (Y : Option ι → Type*)
    [∀ i, TopologicalSpace (Y i)] (x : Y none × ∀ i : ι, Y (some i)) :
    (piOptionEquivProdHomeomorph Y).symm x none = x.1 :=
  (rfl)

@[simp]
theorem piOptionEquivProdHomeomorph_symm_apply_some {ι : Type*} (Y : Option ι → Type*)
    [∀ i, TopologicalSpace (Y i)] (x : Y none × ∀ i : ι, Y (some i)) (i : ι) :
    (piOptionEquivProdHomeomorph Y).symm x (some i) = x.2 i :=
  (rfl)

end TauCeti
