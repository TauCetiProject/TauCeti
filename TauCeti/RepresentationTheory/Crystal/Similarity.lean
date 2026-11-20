/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Crystal.Component
public import TauCeti.RepresentationTheory.Crystal.Word
import Mathlib.Tactic.Linarith
import TauCeti.Data.Option.Basic

/-!
# Similarity morphisms of normal crystals

In Kashiwara's theory of similarity of crystal bases and Littelmann's stretching of piecewise-linear
paths, multiplying a highest weight by a positive integer `n` embeds the crystal `B(λ)` into
`B(n λ)` via a map `S_n` that scales weights and string lengths by `n` and intertwines each simple
root operator `e_i`, `f_i` with the `n`-fold iterate `e_i^n`, `f_i^n`.

This file defines `TauCeti.NormalCrystal.SimilarityHom n c d` for arbitrary normal crystals over a
root datum `(P, b)`: a map `B → B'` scaling weights and raising-string lengths `ε_i` by `n` and
satisfying `d.eIter i n (ψ x) = (c.e i x).map ψ`. Note that `ε_i`-scaling is not redundant for
`n > 1`: `e_i^n` alone leaves `ε_i (ψ x) mod n` unconstrained on highest elements. Conversely, once
`wt` and `ε_i` scale by `n` and `e_i^n` intertwines `e_i`, scaling of `φ_i` and intertwining of
`f_i` with `f_i^n` follow automatically (`TauCeti.NormalCrystal.SimilarityHom.φ_apply`,
`TauCeti.NormalCrystal.SimilarityHom.fIter_self`).

## Main definitions

* `TauCeti.NormalCrystal.SimilarityHom`: a similarity morphism of scale factor `n` between normal
  crystals, with identity at `n = 1`, multiplicative composition, duality, equivalence with
  `TauCeti.NormalCrystal.StrictHom` at `n = 1`, and restriction to connected components.

## Main results

* `TauCeti.NormalCrystal.SimilarityHom.φ_apply`, `TauCeti.NormalCrystal.SimilarityHom.fIter_self`:
  scaling of `φ_i` and intertwining of `f_i` with `f_i^n` follow from the raising axioms.
* `TauCeti.NormalCrystal.SimilarityHom.eWord_flatMap_replicate`,
  `TauCeti.NormalCrystal.SimilarityHom.fWord_flatMap_replicate`: words act through `n`-fold
  letterwise replication.
* `TauCeti.NormalCrystal.SimilarityHom.forall_e_apply_eq_none_iff`: similarity morphisms preserve
  and reflect highest-weight elements.
* `TauCeti.NormalCrystal.SimilarityHom.reachable`: similarity morphisms preserve reachability in
  the crystal graph, hence act on connected components
  (`TauCeti.NormalCrystal.SimilarityHom.mapConnectedComponent`) and restrict to similarity
  morphisms between components (`TauCeti.NormalCrystal.SimilarityHom.componentHom`).

## References

* M. Kashiwara, *Similarity of crystal bases*, Duke Math. J. 84 (1996), 251--277, §§2–3.
* P. Littelmann, *Paths and root operators in representation theory*, Ann. of Math. 142 (1995),
  499--525, §5.
-/

public section

namespace TauCeti.NormalCrystal

universe u v w x₁ x₂ x₃

variable {ι : Type u} {X : Type v} {Y : Type w} [AddCommGroup X] [AddCommGroup Y]
  {P : RootDatum ι X Y} {b : P.Base} {B : Type x₁} {B' : Type x₂} {B'' : Type x₃}

/-! ### Similarity morphisms -/

/-- A **similarity morphism** of scale factor `n` between normal crystals (`S_n` in Kashiwara's
theory of crystal similarity): a map `B → B'` multiplying weights and raising-string lengths `ε i`
by `n` and intertwining each raising operator `e i` with `eIter i n`.

It then also multiplies lowering-string lengths `φ i` by `n` and intertwines `f i` with `fIter i n`
(`TauCeti.NormalCrystal.SimilarityHom.φ_apply`,
`TauCeti.NormalCrystal.SimilarityHom.fIter_self`). -/
structure SimilarityHom (n : ℕ) (c : NormalCrystal P b B) (d : NormalCrystal P b B') where
  /-- The underlying map of crystal elements. -/
  toFun : B → B'
  /-- A similarity morphism of factor `n` multiplies weights by `n`. -/
  wt_toFun (x : B) : d.wt (toFun x) = n • c.wt x
  /-- A similarity morphism of factor `n` multiplies raising-string lengths by `n`. -/
  ε_toFun (i : b.support) (x : B) : d.ε i (toFun x) = n * c.ε i x
  /-- A similarity morphism of factor `n` intertwines `e i` with `eIter i n`. -/
  eIter_toFun (i : b.support) (x : B) : d.eIter i n (toFun x) = (c.e i x).map toFun

namespace SimilarityHom

variable {m n : ℕ} {c : NormalCrystal P b B} {d : NormalCrystal P b B'}
  {d' : NormalCrystal P b B''}

instance : FunLike (SimilarityHom n c d) B B' where
  coe := toFun
  coe_injective ψ χ h := by cases ψ; cases χ; congr

@[simp]
theorem toFun_eq_coe (ψ : SimilarityHom n c d) : ψ.toFun = ψ := (rfl)

@[simp]
theorem coe_mk (g : B → B') (hwt hε he) : ⇑(⟨g, hwt, hε, he⟩ : SimilarityHom n c d) = g := (rfl)

@[ext]
theorem ext {ψ χ : SimilarityHom n c d} (h : ∀ x, ψ x = χ x) : ψ = χ :=
  DFunLike.ext _ _ h

@[simp]
theorem wt_apply (ψ : SimilarityHom n c d) (x : B) : d.wt (ψ x) = n • c.wt x := ψ.wt_toFun x

@[simp]
theorem ε_apply (ψ : SimilarityHom n c d) (i : b.support) (x : B) :
    d.ε i (ψ x) = n * c.ε i x :=
  ψ.ε_toFun i x

@[simp]
theorem eIter_self (ψ : SimilarityHom n c d) (i : b.support) (x : B) :
    d.eIter i n (ψ x) = (c.e i x).map ψ :=
  ψ.eIter_toFun i x

/-- Whenever both `b.support` and `B` are inhabited, the scale factor `n` of a similarity morphism
is strictly positive: the top of the `i`-string above `x` is annihilated by `e i`, whereas
`eIter i 0` is `some`. -/
theorem pos (ψ : SimilarityHom n c d) (i : b.support) (x : B) : 0 < n := by
  obtain ⟨z, hz⟩ := Option.isSome_iff_exists.mp (c.isSome_eIter_iff.mpr (le_refl (c.ε i x)))
  have hεz : c.ε i z = 0 := by
    have := c.ε_of_eIter_eq_some hz
    omega
  have hez : c.e i z = none := c.ε_eq_zero_iff.mp hεz
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have h0 := ψ.eIter_self i z
    rw [d.eIter_zero, hez, Option.map_none] at h0
    cases h0
  · exact hn

/-- A similarity morphism of factor `n` multiplies the lowering-string lengths `φ i` by `n`. -/
@[simp]
theorem φ_apply (ψ : SimilarityHom n c d) (i : b.support) (x : B) :
    d.φ i (ψ x) = n * c.φ i x := by
  have hd := d.φ_sub_ε i (ψ x)
  rw [ψ.wt_apply, ψ.ε_apply, map_nsmul, LinearMap.smul_apply, nsmul_eq_mul,
    ← c.φ_sub_ε i x] at hd
  have hint : (d.φ i (ψ x) : ℤ) = ((n * c.φ i x : ℕ) : ℤ) := by
    push_cast at hd ⊢
    linarith
  exact_mod_cast hint

/-- A similarity morphism of factor `n` intertwines `f i` with `fIter i n`. -/
@[simp]
theorem fIter_self (ψ : SimilarityHom n c d) (i : b.support) (x : B) :
    d.fIter i n (ψ x) = (c.f i x).map ψ := by
  have hn : 0 < n := ψ.pos i x
  cases h : c.f i x with
  | none =>
    rw [Option.map_none, d.fIter_eq_none_iff, ψ.φ_apply, c.φ_eq_zero_iff.mpr h, mul_zero]
    exact hn
  | some y =>
    rw [Option.map_some, d.fIter_eq_some_iff, ψ.eIter_self, c.f_eq_some_iff.mp h, Option.map_some]

/-- A similarity morphism of factor `n` intertwines `eIter i k` with `eIter i (n * k)`. -/
@[simp]
theorem eIter_mul (ψ : SimilarityHom n c d) (i : b.support) (k : ℕ) (x : B) :
    d.eIter i (n * k) (ψ x) = (c.eIter i k x).map ψ := by
  induction k generalizing x with
  | zero => simp
  | succ k ih =>
    rw [Nat.mul_succ, Nat.add_comm, d.eIter_add, ψ.eIter_self, c.eIter_succ]
    cases c.e i x <;> simp [ih]

/-- A similarity morphism of factor `n` intertwines `fIter i k` with `fIter i (n * k)`. -/
@[simp]
theorem fIter_mul (ψ : SimilarityHom n c d) (i : b.support) (k : ℕ) (x : B) :
    d.fIter i (n * k) (ψ x) = (c.fIter i k x).map ψ := by
  induction k generalizing x with
  | zero => simp
  | succ k ih =>
    rw [Nat.mul_succ, Nat.add_comm, d.fIter_add, ψ.fIter_self, c.fIter_succ]
    cases c.f i x <;> simp [ih]

/-- Raising along a word commutes with a similarity morphism upon repeating each letter `n`
times. -/
@[simp]
theorem eWord_flatMap_replicate (ψ : SimilarityHom n c d) (w : List b.support) (x : B) :
    d.eWord (w.flatMap fun j ↦ List.replicate n j) (ψ x) = (c.eWord w x).map ψ := by
  induction w generalizing x with
  | nil => simp
  | cons j w ih =>
    rw [List.flatMap_cons, eWord_append, eWord_replicate, eIter_self, eWord_cons]
    cases c.e j x <;> simp [ih]

/-- Lowering along a word commutes with a similarity morphism upon repeating each letter `n`
times. -/
@[simp]
theorem fWord_flatMap_replicate (ψ : SimilarityHom n c d) (w : List b.support) (x : B) :
    d.fWord (w.flatMap fun j ↦ List.replicate n j) (ψ x) = (c.fWord w x).map ψ := by
  induction w generalizing x with
  | nil => simp
  | cons j w ih =>
    rw [List.flatMap_cons, fWord_append, fWord_replicate, fIter_self, fWord_cons]
    cases c.f j x <;> simp [ih]

/-- Similarity morphisms preserve and reflect vanishing of each raising operator `e i`. -/
@[simp]
theorem e_apply_eq_none_iff (ψ : SimilarityHom n c d) (i : b.support) (x : B) :
    d.e i (ψ x) = none ↔ c.e i x = none := by
  rw [← d.ε_eq_zero_iff, ← c.ε_eq_zero_iff, ψ.ε_apply, mul_eq_zero,
    or_iff_right (ψ.pos i x).ne']

/-- Similarity morphisms preserve and reflect vanishing of each lowering operator `f i`. -/
@[simp]
theorem f_apply_eq_none_iff (ψ : SimilarityHom n c d) (i : b.support) (x : B) :
    d.f i (ψ x) = none ↔ c.f i x = none := by
  rw [← d.φ_eq_zero_iff, ← c.φ_eq_zero_iff, ψ.φ_apply, mul_eq_zero,
    or_iff_right (ψ.pos i x).ne']

/-- Similarity morphisms preserve and reflect highest-weight elements. -/
theorem forall_e_apply_eq_none_iff (ψ : SimilarityHom n c d) {x : B} :
    (∀ j, d.e j (ψ x) = none) ↔ ∀ j, c.e j x = none :=
  forall_congr' fun j ↦ ψ.e_apply_eq_none_iff j x

/-- Similarity morphisms preserve and reflect lowest-weight elements. -/
theorem forall_f_apply_eq_none_iff (ψ : SimilarityHom n c d) {x : B} :
    (∀ j, d.f j (ψ x) = none) ↔ ∀ j, c.f j x = none :=
  forall_congr' fun j ↦ ψ.f_apply_eq_none_iff j x

/-- Adjacent crystal elements map to elements reachable from one another in `d.graph`. -/
theorem reachable_of_adj (ψ : SimilarityHom n c d) {x y : B} (h : c.graph.Adj x y) :
    d.graph.Reachable (ψ x) (ψ y) := by
  obtain ⟨j, h | h⟩ := c.graph_adj_iff.mp h
  · exact d.reachable_of_eIter_eq_some (by rw [ψ.eIter_self, h, Option.map_some])
  · exact (d.reachable_of_eIter_eq_some (by rw [ψ.eIter_self, h, Option.map_some])).symm

/-- Similarity morphisms preserve reachability in the crystal graph. -/
theorem reachable (ψ : SimilarityHom n c d) {x y : B} (h : c.graph.Reachable x y) :
    d.graph.Reachable (ψ x) (ψ y) := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at h
  induction h with
  | refl => exact SimpleGraph.Reachable.refl _
  | tail _ hadj ih => exact ih.trans (ψ.reachable_of_adj hadj)

/-! ### Equivalence with strict morphisms at `n = 1`, composition, duality, and components -/

/-- A similarity morphism of scale factor `1` is a strict crystal morphism. -/
def toStrictHom (ψ : SimilarityHom 1 c d) : StrictHom c d where
  toFun := ψ
  wt_toFun x := by simp
  e_toFun j x := by simpa only [eIter_one] using ψ.eIter_self j x

@[simp]
theorem coe_toStrictHom (ψ : SimilarityHom 1 c d) : ⇑ψ.toStrictHom = ψ := (rfl)

/-- View a strict crystal morphism as a similarity morphism of scale factor `1`. -/
def ofStrictHom (ψ : StrictHom c d) : SimilarityHom 1 c d where
  toFun := ψ
  wt_toFun x := by simp
  ε_toFun j x := by simp
  eIter_toFun j x := by simp

@[simp]
theorem coe_ofStrictHom (ψ : StrictHom c d) : ⇑(ofStrictHom ψ) = ψ := (rfl)

/-- Similarity morphisms of scale factor `1` are in canonical bijection with strict morphisms. -/
def equivStrictHom : SimilarityHom 1 c d ≃ StrictHom c d where
  toFun := toStrictHom
  invFun := ofStrictHom
  left_inv _ := ext fun _ ↦ rfl
  right_inv _ := StrictHom.ext fun _ ↦ rfl

@[simp]
theorem equivStrictHom_apply (ψ : SimilarityHom 1 c d) (x : B) :
    equivStrictHom ψ x = ψ x := (rfl)

@[simp]
theorem equivStrictHom_symm_apply (ψ : StrictHom c d) (x : B) :
    equivStrictHom.symm ψ x = ψ x := (rfl)

variable (c) in
/-- The identity similarity morphism (scale factor `1`). -/
def id : SimilarityHom 1 c c := ofStrictHom (StrictHom.id c)

@[simp]
theorem id_apply (x : B) : SimilarityHom.id c x = x := by simp [id]

/-- Composition of similarity morphisms multiplies their scale factors. -/
def comp (χ : SimilarityHom m d d') (ψ : SimilarityHom n c d) :
    SimilarityHom (m * n) c d' where
  toFun x := χ (ψ x)
  wt_toFun x := by simp [mul_nsmul']
  ε_toFun j x := by simp [mul_assoc]
  eIter_toFun j x := by simp [Option.map_map, Function.comp_def]

@[simp]
theorem comp_apply (χ : SimilarityHom m d d') (ψ : SimilarityHom n c d) (x : B) :
    χ.comp ψ x = χ (ψ x) := (rfl)

/-- A similarity morphism induces a similarity morphism of the same scale factor between the dual
crystals. -/
def dual (ψ : SimilarityHom n c d) : SimilarityHom n c.dual d.dual where
  toFun := ψ
  wt_toFun x := by simp
  ε_toFun j x := by simp
  eIter_toFun j x := by simp

@[simp]
theorem dual_apply (ψ : SimilarityHom n c d) (x : B) : ψ.dual x = ψ x := (rfl)

/-- The map on connected components of the crystal graph induced by a similarity morphism. -/
def mapConnectedComponent (ψ : SimilarityHom n c d) (C : c.graph.ConnectedComponent) :
    d.graph.ConnectedComponent :=
  C.lift (fun x ↦ d.graph.connectedComponentMk (ψ x)) fun _ _ p _ ↦
    SimpleGraph.ConnectedComponent.sound (ψ.reachable p.reachable)

@[simp]
theorem mapConnectedComponent_mk (ψ : SimilarityHom n c d) (x : B) :
    ψ.mapConnectedComponent (c.graph.connectedComponentMk x) =
      d.graph.connectedComponentMk (ψ x) := (rfl)

theorem apply_mem_mapConnectedComponent (ψ : SimilarityHom n c d)
    {C : c.graph.ConnectedComponent} {y : B} (hy : y ∈ C) :
    ψ y ∈ ψ.mapConnectedComponent C := by
  have hy' : c.graph.connectedComponentMk y = C :=
    (SimpleGraph.ConnectedComponent.mem_supp_iff C y).mp hy
  rw [← hy', mapConnectedComponent_mk]
  exact SimpleGraph.ConnectedComponent.connectedComponentMk_mem

/-- A similarity morphism restricts to a similarity morphism from any connected component `C` of
`c.graph` to its image component `ψ.mapConnectedComponent C` in `d.graph`. -/
def componentHom (ψ : SimilarityHom n c d) (C : c.graph.ConnectedComponent) :
    SimilarityHom n (c.component C) (d.component (ψ.mapConnectedComponent C)) where
  toFun y := ⟨ψ y.val, ψ.apply_mem_mapConnectedComponent y.property⟩
  wt_toFun y := by simp
  ε_toFun j y := by simp
  eIter_toFun j y := Option.unattach_inj.mp <| by
    rw [Option.unattach_map, ← Option.map_unattach_eq_map_val (g := ψ)]
    simp

@[simp]
theorem componentHom_apply (ψ : SimilarityHom n c d) (C : c.graph.ConnectedComponent) (y : C) :
    (ψ.componentHom C y).val = ψ y.val := (rfl)

theorem componentHom_injective {ψ : SimilarityHom n c d} (hψ : Function.Injective ψ)
    (C : c.graph.ConnectedComponent) : Function.Injective (ψ.componentHom C) :=
  fun _ _ h ↦ Subtype.ext <| hψ <| congrArg Subtype.val h

end SimilarityHom

end TauCeti.NormalCrystal
