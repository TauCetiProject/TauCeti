/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude, Codex
-/
module

public import TauCeti.LinearAlgebra.Graded.History.Basic
public import Mathlib.RingTheory.Finiteness.Defs

/-!
# Finite expansion into homogeneous histories

Only finitely many histories along a fixed path contribute to a given input, even
when the grading sets are infinite. Their sum recovers the composite of the arrow maps.
A finite support uniform on an input range gives an identity of linear maps, also
after final homogeneous projection or any linear output map. Finite generation of
the input range supplies such a uniform support. Selected sums are independent of
the chosen uniform support, so later incidence conditions may select histories.

Adapted from `yuma-mizuno-lean/Mei`, commit
`bac6f02d25746bc1c2ec808601d4e9284911c475` (Apache 2.0),
`Mei/LinearAlgebra/GradedModule/History/Path.lean`.
-/

public noncomputable section

open TauCeti

namespace Quiver.Path

variable {Q : Type*} [Quiver Q] {a : Q}
  {R : Type*} [Semiring R]
  {M : Q → Type*} [∀ q, AddCommMonoid (M q)] [∀ q, Module R (M q)]
  (T : ∀ {b c : Q}, (b ⟶ c) → M b →ₗ[R] M c)
  {ι : Q → Type*} [∀ q, DecidableEq (ι q)]
  (ℳ : ∀ q, ι q → Submodule R (M q)) [∀ q, DirectSum.Decomposition (ℳ q)]

section Finite

/-- Only finitely many degree histories have nonzero whole decorations for a fixed input.
Neither the degree types nor the homogeneous supports need be finite. -/
theorem finite_support_homogeneousHistory :
    ∀ {b : Q} (p : Path a b) (x : M a),
      (Function.support fun d : p.Degrees ι => p.homogeneousHistory T ℳ d x).Finite
  | _, nil, _ => Set.toFinite _
  | _, cons p e, x => by
    classical
    have hS := finite_support_homogeneousHistory p x
    apply (Finset.finite_toSet (hS.toFinset.biUnion fun d =>
      (DirectSum.decompose (ℳ _) (T e (p.homogeneousHistory T ℳ d x))).support.image
        fun i => ((d, i) : (p.cons e).Degrees ι))).subset
    rintro ⟨d, i⟩ hd
    have hd' : (p.cons e).homogeneousHistory T ℳ ((d, i) : (p.cons e).Degrees ι) x ≠ 0 := hd
    refine Finset.mem_biUnion.mpr ⟨d, (Set.Finite.mem_toFinset _).mpr
      (homogeneousHistory_ne_zero_of_cons T ℳ p e d i hd'), Finset.mem_image.mpr
        ⟨i, DFinsupp.mem_support_iff.mpr fun h => hd' ?_, rfl⟩⟩
    rw [homogeneousHistory_cons_apply, h]
    rfl

/-- The finite set of degree histories whose final whole decoration is nonzero. -/
def historySupport {b : Q} (p : Path a b) (x : M a) : Finset (p.Degrees ι) :=
  (finite_support_homogeneousHistory T ℳ p x).toFinset

/-- Membership retains precisely the histories with nonzero decoration. -/
@[simp]
theorem mem_historySupport {b : Q} (p : Path a b) (x : M a) (d : p.Degrees ι) :
    d ∈ p.historySupport T ℳ x ↔ p.homogeneousHistory T ℳ d x ≠ 0 :=
  Set.Finite.mem_toFinset _

/-- Zero input has no contributing histories. -/
@[simp]
theorem historySupport_zero {b : Q} (p : Path a b) : p.historySupport T ℳ 0 = ∅ := by
  ext d
  simp

open Classical in
/-- Extend each contributing history by exactly the nonzero output components of the
next arrow. -/
theorem historySupport_cons {b c : Q} (p : Path a b) (e : b ⟶ c) (x : M a) :
    (p.cons e).historySupport T ℳ x =
      (p.historySupport T ℳ x).biUnion fun d =>
        (DirectSum.decompose (ℳ c) (T e (p.homogeneousHistory T ℳ d x))).support.image
          fun i => ((d, i) : (p.cons e).Degrees ι) := by
  ext ⟨d, i⟩
  rw [mem_historySupport, Finset.mem_biUnion]
  constructor
  · intro h
    refine ⟨d, (mem_historySupport ..).mpr (homogeneousHistory_ne_zero_of_cons T ℳ p e d i h),
      Finset.mem_image.mpr ⟨i, DFinsupp.mem_support_iff.mpr fun hz => h ?_, rfl⟩⟩
    rw [homogeneousHistory_cons_apply, hz]
    rfl
  · rintro ⟨d', _, hy⟩
    obtain ⟨i', hi, he⟩ := Finset.mem_image.mp hy
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
    rw [homogeneousHistory_cons_apply]
    exact fun hz => DFinsupp.mem_support_iff.mp hi (Subtype.val_injective hz)

open Classical in
private theorem historySupport_cons_disjoint {b c : Q} (p : Path a b) (e : b ⟶ c)
    (x : M a) :
    Set.PairwiseDisjoint (↑(p.historySupport T ℳ x) : Set (p.Degrees ι)) fun d =>
      (DirectSum.decompose (ℳ c) (T e (p.homogeneousHistory T ℳ d x))).support.image
        fun i => ((d, i) : (p.cons e).Degrees ι) := by
  intro d _ d' _ hdd'
  refine Finset.disjoint_left.mpr fun y hy hy' => ?_
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hy
  obtain ⟨i', _, he⟩ := Finset.mem_image.mp hy'
  exact hdd' (congrArg Prod.fst he).symm

open Classical in
/-- The empty path contributes its single empty history exactly for nonzero input. -/
@[simp]
theorem historySupport_nil (x : M a) :
    (nil : Path a a).historySupport T ℳ x = if x = 0 then ∅ else {PUnit.unit} := by
  apply Finset.ext
  intro d
  rw [mem_historySupport, homogeneousHistory_nil, LinearMap.id_apply]
  split_ifs with h <;> simp [h]

/-- Summing exactly the nonzero histories recovers the composite along the path. -/
@[simp]
theorem sum_homogeneousHistory :
    ∀ {b : Q} (p : Path a b) (x : M a),
      ∑ d ∈ p.historySupport T ℳ x, p.homogeneousHistory T ℳ d x = p.composeLinear T x
  | _, nil, x => by
    classical
    by_cases hx : x = 0 <;> simp [hx]
  | _, cons p e, x => by
    classical
    rw [historySupport_cons, Finset.sum_biUnion (historySupport_cons_disjoint T ℳ p e x)]
    trans ∑ d ∈ p.historySupport T ℳ x, T e (p.homogeneousHistory T ℳ d x)
    · refine Finset.sum_congr rfl fun d _ => ?_
      rw [Finset.sum_image fun i _ j _ h => congrArg Prod.snd h]
      simp only [homogeneousHistory_cons_apply]
      exact DirectSum.sum_support_decompose (ℳ _) _
    · simp only [← map_sum, sum_homogeneousHistory p x, composeLinear_cons,
        LinearMap.comp_apply]

open Classical in
/-- Selecting histories by their last degree gives that component of the composite. -/
theorem sum_homogeneousHistory_cons_terminal {b c : Q} (p : Path a b) (e : b ⟶ c)
    (η : ι c) (x : M a) :
    ∑ d ∈ ((p.cons e).historySupport T ℳ x).filter (fun d => d.2 = η),
      (p.cons e).homogeneousHistory T ℳ d x =
        homogeneousComponent (ℳ c) η ((p.cons e).composeLinear T x) := by
  rw [← sum_homogeneousHistory T ℳ (p.cons e) x, map_sum, Finset.sum_filter]
  refine Finset.sum_congr rfl fun d _ => ?_
  obtain ⟨d, i⟩ := d
  by_cases h : i = η
  · subst η
    simp only [↓reduceIte]
    exact (homogeneousComponent_apply_of_mem (ℳ c)
      (homogeneousHistory_cons_mem T ℳ p e d i x)).symm
  · simp only [h, ↓reduceIte]
    exact (homogeneousComponent_apply_of_mem_ne (ℳ c)
      (homogeneousHistory_cons_mem T ℳ p e d i x) h).symm

end Finite

section Uniform

variable {E : Type*} [AddCommMonoid E] [Module R E] {b : Q} (p : Path a b)
  (f : E →ₗ[R] M a)

/-- A uniform support of history maps contains the pointwise support of every input. -/
theorem historySupport_subset_of_comp_eq_zero (S : Finset (p.Degrees ι))
    (hS : ∀ d ∉ S, (p.homogeneousHistory T ℳ d).comp f = 0) (y : E) :
    p.historySupport T ℳ (f y) ⊆ S := by
  intro d hd
  by_contra h
  exact (mem_historySupport T ℳ p (f y) d).mp hd (LinearMap.congr_fun (hS d h) y)

/-- Uniform finite contributing support on the input range gives the expansion as an
identity of linear maps. -/
theorem sum_homogeneousHistory_comp_eq (S : Finset (p.Degrees ι))
    (hS : ∀ d ∉ S, (p.homogeneousHistory T ℳ d).comp f = 0) :
    ∑ d ∈ S, (p.homogeneousHistory T ℳ d).comp f = (p.composeLinear T).comp f := by
  ext y
  simp only [LinearMap.sum_apply, LinearMap.comp_apply]
  rw [← sum_homogeneousHistory T ℳ p (f y)]
  exact (Finset.sum_subset (historySupport_subset_of_comp_eq_zero T ℳ p f S hS y)
    fun d _ hd => by simpa using hd).symm

/-- A linear output map commutes with the uniformly supported history expansion.
The support bound is imposed before the output map. -/
theorem sum_comp_homogeneousHistory_comp_eq {O : Type*} [AddCommMonoid O] [Module R O]
    (g : M b →ₗ[R] O) (S : Finset (p.Degrees ι))
    (hS : ∀ d ∉ S, (p.homogeneousHistory T ℳ d).comp f = 0) :
    ∑ d ∈ S, g.comp ((p.homogeneousHistory T ℳ d).comp f) =
      g.comp ((p.composeLinear T).comp f) := by
  rw [← sum_homogeneousHistory_comp_eq T ℳ p f S hS]
  ext y
  simp

open Classical in
/-- Within a uniformly supported expansion along a nonempty path, selecting the
histories with last degree `η` isolates the final `η`-component of the composite.
The ambient gradings and the intermediate degree types need not be finite. -/
theorem sum_homogeneousHistory_cons_terminal_comp_eq {b c : Q} (p : Path a b)
    (e : b ⟶ c) (η : ι c) (S : Finset ((p.cons e).Degrees ι))
    (hS : ∀ d ∉ S, ((p.cons e).homogeneousHistory T ℳ d).comp f = 0) :
    ∑ d ∈ S.filter (fun d => d.2 = η),
      ((p.cons e).homogeneousHistory T ℳ d).comp f =
        ((homogeneousComponent (ℳ c) η).comp ((p.cons e).composeLinear T)).comp f := by
  rw [Finset.sum_filter]
  calc
    _ = ∑ d ∈ S, (homogeneousComponent (ℳ c) η).comp
        (((p.cons e).homogeneousHistory T ℳ d).comp f) := by
      refine Finset.sum_congr rfl fun d _ => ?_
      obtain ⟨d, i⟩ := d
      by_cases hi : i = η
      · subst η
        simp only [↓reduceIte]
        rw [← LinearMap.comp_assoc, homogeneousComponent_comp_homogeneousHistory_cons]
      · simp only [hi, ↓reduceIte]
        rw [← LinearMap.comp_assoc,
          homogeneousComponent_comp_homogeneousHistory_cons_of_ne T ℳ p e d i η hi,
          LinearMap.zero_comp]
    _ = _ := by
      simpa only [LinearMap.comp_assoc] using
        sum_comp_homogeneousHistory_comp_eq T ℳ (p.cons e) f
          (homogeneousComponent (ℳ c) η) S hS

/-- A finite generating set of inputs gives a uniform finite history support on its span. -/
theorem exists_uniform_historySupport_of_fg (P : Submodule R (M a)) (hP : P.FG) :
    ∃ S : Finset (p.Degrees ι), ∀ d ∉ S, ∀ y ∈ P, p.homogeneousHistory T ℳ d y = 0 := by
  classical
  obtain ⟨s, hs⟩ := hP
  refine ⟨s.biUnion (p.historySupport T ℳ), fun d hd y hy => ?_⟩
  have hker : P ≤ LinearMap.ker (p.homogeneousHistory T ℳ d) := by
    rw [← hs]
    refine Submodule.span_le.mpr fun z hz => LinearMap.mem_ker.mpr ?_
    by_contra hne
    exact hd (Finset.mem_biUnion.mpr ⟨z, hz, (mem_historySupport T ℳ p z d).mpr hne⟩)
  exact hker hy

/-- Finite generation of the input range ensures a uniform finite history support. -/
theorem exists_uniform_historySupport (hf : (LinearMap.range f).FG) :
    ∃ S : Finset (p.Degrees ι), ∀ d ∉ S, (p.homogeneousHistory T ℳ d).comp f = 0 := by
  obtain ⟨S, hS⟩ := exists_uniform_historySupport_of_fg T ℳ p _ hf
  exact ⟨S, fun d hd => LinearMap.ext fun y => hS d hd (f y) (LinearMap.mem_range_self f y)⟩

open Classical in
/-- Selecting histories in a uniform support gives the same value as selecting in the
pointwise nonzero support. -/
theorem sum_ite_homogeneousHistory_comp_apply (S : Finset (p.Degrees ι))
    (hS : ∀ d ∉ S, (p.homogeneousHistory T ℳ d).comp f = 0) (P : p.Degrees ι → Prop)
    (y : E) :
    (∑ d ∈ S, if P d then (p.homogeneousHistory T ℳ d).comp f else 0) y =
      ∑ d ∈ p.historySupport T ℳ (f y),
        if P d then p.homogeneousHistory T ℳ d (f y) else 0 := by
  trans ∑ d ∈ S, if P d then p.homogeneousHistory T ℳ d (f y) else 0
  · simp only [LinearMap.sum_apply]
    exact Finset.sum_congr rfl fun d _ => by split_ifs <;> rfl
  exact (Finset.sum_subset (historySupport_subset_of_comp_eq_zero T ℳ p f S hS y)
    fun d _ hd => by
      have hz : p.homogeneousHistory T ℳ d (f y) = 0 := by simpa using hd
      simp [hz]).symm

open Classical in
/-- Selected linear-map sums agree over any two uniform supports. -/
theorem sum_ite_homogeneousHistory_comp_eq (S S' : Finset (p.Degrees ι))
    (hS : ∀ d ∉ S, (p.homogeneousHistory T ℳ d).comp f = 0)
    (hS' : ∀ d ∉ S', (p.homogeneousHistory T ℳ d).comp f = 0) (P : p.Degrees ι → Prop) :
    (∑ d ∈ S, if P d then (p.homogeneousHistory T ℳ d).comp f else 0) =
      ∑ d ∈ S', if P d then (p.homogeneousHistory T ℳ d).comp f else 0 := by
  ext y
  rw [sum_ite_homogeneousHistory_comp_apply T ℳ p f S hS,
    sum_ite_homogeneousHistory_comp_apply T ℳ p f S' hS']

end Uniform

end Quiver.Path
