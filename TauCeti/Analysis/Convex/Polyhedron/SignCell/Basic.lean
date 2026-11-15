/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Analysis.Convex.Polyhedron.Basic
public import Mathlib.Analysis.Convex.Topology
public import Mathlib.Analysis.Convex.Extreme
public import Mathlib.Basic.Sign.Defs
public import Mathlib.Geometry.Convex.Cone.Pointed
import Mathlib.Tactic.Linarith

/-!
# Sign cells of affine arrangements

An affine family partitions the ambient space by the signs of its values.
The closure of a nonempty sign cell is obtained by weakening its strict
inequalities, while retaining its equality rows. Nonemptiness is essential:
an inconsistent strict system can have a nonempty weakened system.
For linear rows, every weak sign cell is a pointed cone, possibly with lineality.

Adapted from `Mei/Geometry/Convex/Polyhedron/SignCell.lean` in
[yuma-mizuno-lean/Mei](https://github.com/yuma-mizuno-lean/Mei), commit
`a79c57178cc83666fc244ca6e6eeaa722e9b8bc7` (Apache 2.0).
-/

public section

namespace TauCeti.Convex

variable {V ι : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]

/-- The locus realizing an assigned sign for each affine row. -/
def signCell (g : ι → (V →ᴬ[ℝ] ℝ)) (σ : ι → SignType) : Set V :=
  {x | ∀ j, SignType.sign (g j x) = σ j}

/-- Membership in a sign cell means realizing every prescribed affine sign. -/
@[simp] theorem mem_signCell {g : ι → (V →ᴬ[ℝ] ℝ)} {σ : ι → SignType} {x : V} :
    x ∈ signCell g σ ↔ ∀ j, SignType.sign (g j x) = σ j := (Iff.rfl)

/-- The weak sign conditions, with equality rows retained exactly. -/
def weakSignCell (g : ι → (V →ᴬ[ℝ] ℝ)) (σ : ι → SignType) : Set V :=
  {x | ∀ j, match σ j with
    | .zero => g j x = 0
    | .neg => g j x ≤ 0
    | .pos => 0 ≤ g j x}

/-- Membership in a weak sign cell means satisfying every weak row condition. -/
@[simp] theorem mem_weakSignCell {g : ι → (V →ᴬ[ℝ] ℝ)} {σ : ι → SignType} {x : V} :
    x ∈ weakSignCell g σ ↔ ∀ j,
      (σ j = .zero → g j x = 0) ∧ (σ j = .neg → g j x ≤ 0) ∧
        (σ j = .pos → 0 ≤ g j x) := by
  apply forall_congr'
  intro j
  cases σ j <;> simp

/-- The affine inequalities presenting a weak sign cell. Equality rows are
doubled, while the other rows are signed to be nonpositive. -/
def weakSignCellRows (g : ι → (V →ᴬ[ℝ] ℝ)) (σ : ι → SignType) :
    ι × Bool → (V →ᴬ[ℝ] ℝ) := fun p => match σ p.1 with
  | .zero => if p.2 then g p.1 else -g p.1
  | .neg => g p.1
  | .pos => -g p.1

/-- The signed row is the original affine map or its negative, according to the sign. -/
theorem weakSignCellRows_eq (g : ι → (V →ᴬ[ℝ] ℝ)) (σ : ι → SignType) (p : ι × Bool) :
    weakSignCellRows g σ p = match σ p.1 with
      | .zero => if p.2 then g p.1 else -g p.1
      | .neg => g p.1
      | .pos => -g p.1 := by rfl

/-- Signing and doubling do not change the zero locus of an original row. -/
@[simp]
theorem weakSignCellRows_eq_zero_iff {g : ι → (V →ᴬ[ℝ] ℝ)} {σ : ι → SignType}
    {j : ι} {b : Bool} {x : V} :
    weakSignCellRows g σ (j, b) x = 0 ↔ g j x = 0 := by
  cases h : σ j <;> cases b <;> simp [weakSignCellRows, h]

/-- The doubled signed rows present exactly the original weak sign cell. -/
theorem mem_weakSignCell_iff_rows {g : ι → (V →ᴬ[ℝ] ℝ)} {σ : ι → SignType} {x : V} :
    x ∈ weakSignCell g σ ↔ ∀ p, weakSignCellRows g σ p x ≤ 0 := by
  rw [mem_weakSignCell]
  constructor
  · intro hx ⟨j, b⟩
    have := hx j
    cases h : σ j <;> cases b <;> simp_all [weakSignCellRows]
  · intro hx j
    have h₁ := hx (j, true)
    have h₂ := hx (j, false)
    cases h : σ j with
    | zero =>
      simp only [weakSignCellRows, h, Bool.false_eq_true, ↓reduceIte,
        ContinuousAffineMap.neg_apply, neg_nonpos] at h₁ h₂
      simpa using le_antisymm h₁ h₂
    | neg => simpa [weakSignCellRows, h] using h₁
    | pos => simpa [weakSignCellRows, h] using h₁

/-- The weak cell agrees as a carrier with the finite-inequality presentation. -/
theorem weakSignCell_eq_setOf_rows (g : ι → (V →ᴬ[ℝ] ℝ)) (σ : ι → SignType) :
    weakSignCell g σ = {x | ∀ p, weakSignCellRows g σ p x ≤ 0} := by
  ext x
  exact mem_weakSignCell_iff_rows

/-- Strict sign conditions imply their weak versions. -/
theorem signCell_subset_weakSignCell (g : ι → (V →ᴬ[ℝ] ℝ)) (σ : ι → SignType) :
    signCell g σ ⊆ weakSignCell g σ := by
  intro x hx j
  have hj := hx j
  cases h : σ j with
  | zero => exact sign_eq_zero_iff.mp (by simpa [h] using hj)
  | neg => exact (sign_eq_neg_one_iff.mp (by simpa [h] using hj)).le
  | pos => exact (sign_eq_one_iff.mp (by simpa [h] using hj)).le

/-- The weak sign cell is closed, including for an infinite family. -/
theorem isClosed_weakSignCell (g : ι → (V →ᴬ[ℝ] ℝ)) (σ : ι → SignType) :
    IsClosed (weakSignCell g σ) := by
  have he : weakSignCell g σ = ⋂ j, {x : V | match σ j with
      | .zero => g j x = 0 | .neg => g j x ≤ 0 | .pos => 0 ≤ g j x} := by
    ext x
    simp [weakSignCell]
  rw [he]
  apply isClosed_iInter
  intro j
  cases σ j
  · exact isClosed_eq (g j).continuous continuous_const
  · exact isClosed_le (g j).continuous continuous_const
  · exact isClosed_le continuous_const (g j).continuous

/-- Every affine row has a constant weak sign on a subset of a weak sign cell. -/
theorem nonneg_or_nonpos_of_subset_weakSignCell
    {g : ι → (V →ᴬ[ℝ] ℝ)} {σ : ι → SignType} {S : Set V}
    (hS : S ⊆ weakSignCell g σ) (j : ι) :
    (∀ x ∈ S, 0 ≤ g j x) ∨ ∀ x ∈ S, g j x ≤ 0 := by
  cases hs : σ j with
  | zero => exact Or.inr fun x hx => ((mem_weakSignCell.mp (hS hx) j).1 hs).le
  | neg => exact Or.inr fun x hx => (mem_weakSignCell.mp (hS hx) j).2.1 hs
  | pos => exact Or.inl fun x hx => (mem_weakSignCell.mp (hS hx) j).2.2 hs

/-- Moving from a weak solution towards a strict solution makes every prescribed
nonzero sign strict while retaining all equality rows. -/
theorem openSegment_subset_signCell {g : ι → (V →ᴬ[ℝ] ℝ)} {σ : ι → SignType}
    {x p : V} (hx : x ∈ weakSignCell g σ) (hp : p ∈ signCell g σ) :
    openSegment ℝ x p ⊆ signCell g σ := by
  rintro y ⟨a, b, ha, hb, hab, rfl⟩ j
  have he : g j (a • x + b • p) = a * g j x + b * g j p :=
    Convex.combo_affine_apply (f := (g j).toAffineMap) hab
  have hxj := hx j
  have hpj := hp j
  rw [he]
  cases h : σ j with
  | zero =>
    have hpx : g j p = 0 := sign_eq_zero_iff.mp (by simpa [h] using hpj)
    simp only [h] at hxj
    simp [hxj, hpx]
  | neg =>
    apply sign_eq_neg_one_iff.mpr
    have hpp : g j p < 0 := sign_eq_neg_one_iff.mp (by simpa [h] using hpj)
    simp only [h] at hxj
    exact add_neg_of_nonpos_of_neg (mul_nonpos_of_nonneg_of_nonpos ha.le hxj)
      (mul_neg_of_pos_of_neg hb hpp)
  | pos =>
    apply sign_eq_one_iff.mpr
    have hpp : 0 < g j p := sign_eq_one_iff.mp (by simpa [h] using hpj)
    simp only [h] at hxj
    exact add_pos_of_nonneg_of_pos (mul_nonneg ha.le hxj) (mul_pos hb hpp)

/-- For a nonempty sign cell, closure is exactly the weakened system. -/
theorem closure_signCell [ContinuousAdd V] [ContinuousSMul ℝ V]
    {g : ι → (V →ᴬ[ℝ] ℝ)} {σ : ι → SignType}
    (hne : (signCell g σ).Nonempty) : closure (signCell g σ) = weakSignCell g σ := by
  apply Set.Subset.antisymm
  · exact closure_minimal (signCell_subset_weakSignCell g σ) (isClosed_weakSignCell g σ)
  · obtain ⟨p, hp⟩ := hne
    intro x hx
    exact closure_mono (openSegment_subset_signCell hx hp)
      (segment_subset_closure_openSegment (left_mem_segment ℝ x p))

/-- Every point belongs to the cell recording its actual affine signs. -/
theorem mem_signCell_sign (g : ι → (V →ᴬ[ℝ] ℝ)) (x : V) :
    x ∈ signCell g (fun j => SignType.sign (g j x)) := fun _ => rfl

/-- A point cannot belong to two cells with distinct sign assignments. -/
theorem signCell_disjoint {g : ι → (V →ᴬ[ℝ] ℝ)} {σ τ : ι → SignType} (h : σ ≠ τ) :
    Disjoint (signCell g σ) (signCell g τ) := by
  rw [Set.disjoint_left]
  intro x hx hy
  exact h (funext fun j => (hx j).symm.trans (hy j))

/-- Sign cells cover the entire ambient space. -/
theorem iUnion_signCell (g : ι → (V →ᴬ[ℝ] ℝ)) : ⋃ σ, signCell g σ = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  exact Set.mem_iUnion.mpr ⟨_, mem_signCell_sign g x⟩

/-- Each strict sign cell is convex, for an arbitrary family of affine rows. -/
theorem convex_signCell (g : ι → (V →ᴬ[ℝ] ℝ)) (σ : ι → SignType) :
    _root_.Convex ℝ (signCell g σ) := by
  have he : signCell g σ = ⋂ j, {x : V | SignType.sign (g j x) = σ j} := by
    ext x
    simp [signCell]
  rw [he]
  apply convex_iInter
  intro j
  cases σ j with
  | zero =>
    have he : {x : V | SignType.sign (g j x) = .zero} = (g j) ⁻¹' {0} := by
      ext x
      simp
    rw [he]
    exact _root_.Convex.affine_preimage (g j).toAffineMap (convex_singleton 0)
  | neg =>
    have he : {x : V | SignType.sign (g j x) = .neg} = (g j) ⁻¹' Set.Iio 0 := by
      ext x
      simp [sign_eq_neg_one_iff]
    rw [he]
    exact _root_.Convex.affine_preimage (g j).toAffineMap (convex_Iio 0)
  | pos =>
    have he : {x : V | SignType.sign (g j x) = .pos} = (g j) ⁻¹' Set.Ioi 0 := by
      ext x
      simp [sign_eq_one_iff]
    rw [he]
    exact _root_.Convex.affine_preimage (g j).toAffineMap (convex_Ioi 0)

/-- Weak sign cells are convex, including for infinite families and empty strict cells. -/
theorem convex_weakSignCell (g : ι → (V →ᴬ[ℝ] ℝ)) (σ : ι → SignType) :
    _root_.Convex ℝ (weakSignCell g σ) := by
  intro x hx y hy a b ha hb hab j
  have he : g j (a • x + b • y) = a * g j x + b * g j y :=
    Convex.combo_affine_apply (f := (g j).toAffineMap) hab
  have hxj := hx j
  have hyj := hy j
  rw [he]
  cases h : σ j with
  | zero =>
    simp only [h] at hxj hyj
    simp [hxj, hyj]
  | neg =>
    simp only [h] at hxj hyj
    exact add_nonpos (mul_nonpos_of_nonneg_of_nonpos ha hxj)
      (mul_nonpos_of_nonneg_of_nonpos hb hyj)
  | pos =>
    simp only [h] at hxj hyj
    exact add_nonneg (mul_nonneg ha hxj) (mul_nonneg hb hyj)

/-- For linear rows, a weak sign cell is a pointed cone. Lineality is allowed. -/
def weakSignCellCone (g : ι → (V →L[ℝ] ℝ)) (σ : ι → SignType) : PointedCone ℝ V where
  carrier := weakSignCell (fun j => (g j).toContinuousAffineMap) σ
  zero_mem' j := by cases σ j <;> simp
  add_mem' {x y} hx hy j := by
    have hxj := hx j
    have hyj := hy j
    cases h : σ j <;> simp only [h, ContinuousLinearMap.coe_toContinuousAffineMap,
      map_add] at hxj hyj ⊢
    exacts [by simp [hxj, hyj], add_nonpos hxj hyj, add_nonneg hxj hyj]
  smul_mem' c x hx j := by
    have hxj := hx j
    cases h : σ j <;> simp only [h, ContinuousLinearMap.coe_toContinuousAffineMap,
      ← Nonneg.coe_smul, map_smul, smul_eq_mul] at hxj ⊢
    exacts [by simp [hxj], mul_nonpos_of_nonneg_of_nonpos c.property hxj,
      mul_nonneg c.property hxj]

/-- The carrier of the cone of linear rows is the weak sign cell. -/
@[simp]
theorem coe_weakSignCellCone (g : ι → (V →L[ℝ] ℝ)) (σ : ι → SignType) :
    (weakSignCellCone g σ : Set V) = weakSignCell (fun j => (g j).toContinuousAffineMap) σ :=
  (rfl)

/-- A sign assignment specializes another by replacing some of its signs with zero. -/
def SignSpecializes (τ σ : ι → SignType) : Prop := ∀ j, τ j = 0 ∨ τ j = σ j

/-- A specialization replaces each sign with zero or retains it. -/
theorem signSpecializes_iff {τ σ : ι → SignType} :
    SignSpecializes τ σ ↔ ∀ j, τ j = 0 ∨ τ j = σ j := (Iff.rfl)

/-- Each sign assignment specializes itself. -/
@[refl] theorem SignSpecializes.refl {σ : ι → SignType} : SignSpecializes σ σ :=
  fun _ => Or.inr rfl

/-- Specializing twice is again a specialization. -/
@[trans] theorem SignSpecializes.trans {ρ τ σ : ι → SignType}
    (hρτ : SignSpecializes ρ τ) (hτσ : SignSpecializes τ σ) : SignSpecializes ρ σ := by
  intro j
  rcases hρτ j with hz | ht
  · exact Or.inl hz
  · rcases hτσ j with hz | hs
    · exact Or.inl (ht.trans hz)
    · exact Or.inr (ht.trans hs)

/-- Weak sign conditions say exactly that the actual signs specialize the prescribed signs. -/
theorem mem_weakSignCell_iff_specializes {g : ι → (V →ᴬ[ℝ] ℝ)} {σ : ι → SignType}
    {x : V} : x ∈ weakSignCell g σ ↔ SignSpecializes (fun j => SignType.sign (g j x)) σ := by
  apply forall_congr'
  intro j
  cases σ j with
  | zero => simp [sign_eq_zero_iff]
  | neg =>
    simp only [SignType.neg_eq_neg_one, sign_eq_zero_iff, sign_eq_neg_one_iff]
    exact le_iff_eq_or_lt
  | pos =>
    simp only [SignType.pos_eq_one, sign_eq_zero_iff, sign_eq_one_iff]
    exact le_iff_eq_or_lt'

/-- A weak sign cell is the disjoint union of the strict cells obtained by zero specialization. -/
theorem weakSignCell_eq_iUnion_signCell (g : ι → (V →ᴬ[ℝ] ℝ)) (σ : ι → SignType) :
    weakSignCell g σ = ⋃ τ : {τ // SignSpecializes τ σ}, signCell g τ.val := by
  ext x
  constructor
  · intro hx
    exact Set.mem_iUnion.mpr
      ⟨⟨fun j => SignType.sign (g j x), mem_weakSignCell_iff_specializes.mp hx⟩,
        mem_signCell_sign g x⟩
  · intro hx
    obtain ⟨τ, hxτ⟩ := Set.mem_iUnion.mp hx
    apply mem_weakSignCell_iff_specializes.mpr
    intro j
    simpa only [hxτ j] using τ.property j

/-- Replacing more signs by zero restricts the corresponding weak sign cell. -/
theorem weakSignCell_subset_of_specializes {g : ι → (V →ᴬ[ℝ] ℝ)} {σ τ : ι → SignType}
    (h : SignSpecializes τ σ) : weakSignCell g τ ⊆ weakSignCell g σ := by
  intro x hx
  exact mem_weakSignCell_iff_specializes.mpr
    ((mem_weakSignCell_iff_specializes.mp hx).trans h)

/-- Finitely many affine rows give polyhedral weak sign cells; equality rows are
encoded by two opposite affine inequalities. -/
theorem isConvexPolyhedron_weakSignCell [Finite ι] (g : ι → (V →ᴬ[ℝ] ℝ))
    (σ : ι → SignType) : TauCeti.IsConvexPolyhedron (weakSignCell g σ) := by
  rw [weakSignCell_eq_setOf_rows]
  exact TauCeti.isConvexPolyhedron_setOf_forall (weakSignCellRows g σ)

/-- The closures of all cells of a finite arrangement are convex polyhedra. -/
theorem isConvexPolyhedron_closure_signCell [ContinuousAdd V] [ContinuousSMul ℝ V]
    [Finite ι] {g : ι → (V →ᴬ[ℝ] ℝ)}
    {σ : ι → SignType} :
    TauCeti.IsConvexPolyhedron (closure (signCell g σ)) := by
  by_cases hne : (signCell g σ).Nonempty
  · rw [closure_signCell hne]
    exact isConvexPolyhedron_weakSignCell g σ
  · rw [Set.not_nonempty_iff_eq_empty.mp hne, closure_empty]
    simpa [not_le.mpr (zero_lt_one : (0 : ℝ) < 1)] using
      (TauCeti.isConvexPolyhedron_setOf_le (ContinuousAffineMap.const ℝ V (1 : ℝ)))

/-- The sign-cell partition has pairwise disjoint cells. -/
theorem pairwiseDisjoint_signCell (g : ι → (V →ᴬ[ℝ] ℝ)) :
    Set.PairwiseDisjoint (Set.univ : Set (ι → SignType)) (signCell g) := by
  intro σ _ τ _ h
  exact signCell_disjoint h

/-- A zero-specialized weak sign cell is an extreme subset of the original weak
cell. The specialized cell is allowed to be empty. -/
theorem isExtreme_weakSignCell_of_specializes {g : ι → (V →ᴬ[ℝ] ℝ)}
    {σ τ : ι → SignType} (h : SignSpecializes τ σ) :
    IsExtreme ℝ (weakSignCell g σ) (weakSignCell g τ) := by
  refine ⟨weakSignCell_subset_of_specializes h, ?_⟩
  intro x hx y hy z hz hzxy
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := hzxy
  intro j
  rcases h j with hj | hj
  · rw [hj]
    have hzj := hz j
    simp only [hj] at hzj
    have he : a * g j x + b * g j y = 0 := by
      have hcombo : g j (a • x + b • y) = a * g j x + b * g j y :=
        Convex.combo_affine_apply (f := (g j).toAffineMap) hab
      rwa [hcombo] at hzj
    have hxj := hx j
    have hyj := hy j
    cases hs : σ j with
    | zero => simpa only [hs] using hxj
    | neg =>
      simp only [hs] at hxj hyj
      have hax := mul_nonpos_of_nonneg_of_nonpos ha.le hxj
      have hby := mul_nonpos_of_nonneg_of_nonpos hb.le hyj
      have haz : a * g j x = 0 := by linarith
      exact (mul_eq_zero.mp haz).resolve_left ha.ne'
    | pos =>
      simp only [hs] at hxj hyj
      have hax := mul_nonneg ha.le hxj
      have hby := mul_nonneg hb.le hyj
      exact (mul_eq_zero.mp ((add_eq_zero_iff_of_nonneg hax hby).mp he).1).resolve_left ha.ne'
  · simpa only [hj] using hx j

/-- The common zero specialization keeps exactly the signs on which two assignments agree. -/
def commonSignPattern (σ τ : ι → SignType) : ι → SignType :=
  fun j => if σ j = τ j then σ j else 0

/-- The common pattern retains a row's sign exactly when both assignments agree. -/
@[simp] theorem commonSignPattern_apply (σ τ : ι → SignType) (j : ι) :
    commonSignPattern σ τ j = if σ j = τ j then σ j else 0 := (rfl)

/-- The common pattern specializes the first assignment. -/
theorem commonSignPattern_specializes_left (σ τ : ι → SignType) :
    SignSpecializes (commonSignPattern σ τ) σ := by
  intro j
  by_cases h : σ j = τ j <;> simp [h]

/-- The common pattern specializes the second assignment. -/
theorem commonSignPattern_specializes_right (σ τ : ι → SignType) :
    SignSpecializes (commonSignPattern σ τ) τ := by
  intro j
  by_cases h : σ j = τ j <;> simp [h]

/-- Specializing the common pattern is equivalent to specializing both assignments. -/
@[simp] theorem signSpecializes_commonSignPattern_iff {ρ σ τ : ι → SignType} :
    SignSpecializes ρ (commonSignPattern σ τ) ↔
      SignSpecializes ρ σ ∧ SignSpecializes ρ τ := by
  constructor
  · intro h
    exact ⟨h.trans (commonSignPattern_specializes_left σ τ),
      h.trans (commonSignPattern_specializes_right σ τ)⟩
  · rintro ⟨hσ, hτ⟩ j
    rcases hσ j with hz | hs
    · exact Or.inl hz
    · rcases hτ j with hz | ht
      · exact Or.inl hz
      · rw [commonSignPattern_apply, ite_eq_left (hs.symm.trans ht)]
        exact Or.inr hs

/-- Intersecting two weak sign cells forces every disagreement row to zero. -/
theorem weakSignCell_inter (g : ι → (V →ᴬ[ℝ] ℝ)) (σ τ : ι → SignType) :
    weakSignCell g σ ∩ weakSignCell g τ = weakSignCell g (commonSignPattern σ τ) := by
  ext x
  simp only [Set.mem_inter_iff, mem_weakSignCell_iff_specializes,
    signSpecializes_commonSignPattern_iff]

/-- Every intersection of weak sign cells is an extreme subset of the first cell,
including when the intersection is empty. -/
theorem isExtreme_weakSignCell_inter (g : ι → (V →ᴬ[ℝ] ℝ)) (σ τ : ι → SignType) :
    IsExtreme ℝ (weakSignCell g σ) (weakSignCell g σ ∩ weakSignCell g τ) := by
  rw [weakSignCell_inter]
  exact isExtreme_weakSignCell_of_specializes (commonSignPattern_specializes_left σ τ)

/-- The closure of a realized sign cell consists precisely of its strict zero-specializations. -/
theorem closure_signCell_eq_iUnion [ContinuousAdd V] [ContinuousSMul ℝ V]
    {g : ι → (V →ᴬ[ℝ] ℝ)} {σ : ι → SignType}
    (hne : (signCell g σ).Nonempty) :
    closure (signCell g σ) = ⋃ τ : {τ // SignSpecializes τ σ}, signCell g τ.val := by
  rw [closure_signCell hne, weakSignCell_eq_iUnion_signCell]

/-- Intersections of closures of sign cells are extreme subsets of each
closure. The intersection may be empty; interchange assignments for the symmetric statement. -/
theorem isExtreme_closure_signCell_inter [ContinuousAdd V] [ContinuousSMul ℝ V]
    {g : ι → (V →ᴬ[ℝ] ℝ)} {σ τ : ι → SignType} :
    IsExtreme ℝ (closure (signCell g σ))
      (closure (signCell g σ) ∩ closure (signCell g τ)) := by
  by_cases hσ : (signCell g σ).Nonempty
  · by_cases hτ : (signCell g τ).Nonempty
    · rw [closure_signCell hσ, closure_signCell hτ]
      exact isExtreme_weakSignCell_inter g σ τ
    · rw [Set.not_nonempty_iff_eq_empty.mp hτ, closure_empty, Set.inter_empty]
      refine ⟨Set.empty_subset _, ?_⟩
      simp
  · rw [Set.not_nonempty_iff_eq_empty.mp hσ, closure_empty, Set.empty_inter]

/-- Closed sign-cell supports cover the ambient space. Empty labels contribute nothing. -/
theorem iUnion_closure_signCell (g : ι → (V →ᴬ[ℝ] ℝ)) :
    ⋃ σ, closure (signCell g σ) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  exact Set.mem_iUnion.mpr ⟨_, subset_closure (mem_signCell_sign g x)⟩

/-- Combining affine families refines their strict cells by intersection. -/
theorem signCell_sum {κ : Type*} (g : ι → (V →ᴬ[ℝ] ℝ)) (h : κ → (V →ᴬ[ℝ] ℝ))
    (σ : ι → SignType) (τ : κ → SignType) :
    signCell (Sum.elim g h) (Sum.elim σ τ) = signCell g σ ∩ signCell h τ := by
  ext x
  simp [signCell, Sum.forall]

/-- Combining affine families refines their weak cells by intersection. -/
theorem weakSignCell_sum {κ : Type*} (g : ι → (V →ᴬ[ℝ] ℝ)) (h : κ → (V →ᴬ[ℝ] ℝ))
    (σ : ι → SignType) (τ : κ → SignType) :
    weakSignCell (Sum.elim g h) (Sum.elim σ τ) = weakSignCell g σ ∩ weakSignCell h τ := by
  ext x
  simp [weakSignCell, Sum.forall]

/-- The actual closed supports of the realized sign cells of an affine family. -/
def realizedSignCellClosures (g : ι → (V →ᴬ[ℝ] ℝ)) : Set (Set V) :=
  {P | ∃ σ, (signCell g σ).Nonempty ∧ P = closure (signCell g σ)}

/-- Membership means being the closure of a realized strict sign cell. -/
@[simp]
theorem mem_realizedSignCellClosures {g : ι → (V →ᴬ[ℝ] ℝ)} {P : Set V} :
    P ∈ realizedSignCellClosures g ↔
      ∃ σ, (signCell g σ).Nonempty ∧ P = closure (signCell g σ) := by
  simp only [realizedSignCellClosures, Set.mem_ofPred_eq]

/-- A member of the realized closure family has nonempty carrier. -/
theorem nonempty_of_mem_realizedSignCellClosures {g : ι → (V →ᴬ[ℝ] ℝ)} {P : Set V}
    (hP : P ∈ realizedSignCellClosures g) : P.Nonempty := by
  obtain ⟨σ, ⟨p, hp⟩, rfl⟩ := hP
  exact ⟨p, subset_closure hp⟩

/-- A finite arrangement has only finitely many realized closed sign-cell supports. -/
theorem finite_realizedSignCellClosures [Finite ι] (g : ι → (V →ᴬ[ℝ] ℝ)) :
    (realizedSignCellClosures g).Finite :=
  (Set.finite_range (fun σ => closure (signCell g σ))).subset fun _ ⟨σ, _, heq⟩ => ⟨σ, heq.symm⟩

/-- The realized closed sign cells cover the ambient space. -/
theorem sUnion_realizedSignCellClosures (g : ι → (V →ᴬ[ℝ] ℝ)) :
    ⋃₀ realizedSignCellClosures g = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  let σ := fun j => SignType.sign (g j x)
  have hx : x ∈ signCell g σ := mem_signCell_sign g x
  exact Set.mem_sUnion.mpr ⟨closure (signCell g σ), ⟨σ, ⟨x, hx⟩, rfl⟩, subset_closure hx⟩

/-- Every member of a finite realized closure family is a convex polyhedron. -/
theorem isConvexPolyhedron_of_mem_realizedSignCellClosures
    [ContinuousAdd V] [ContinuousSMul ℝ V] [Finite ι]
    {g : ι → (V →ᴬ[ℝ] ℝ)} {P : Set V} (hP : P ∈ realizedSignCellClosures g) :
    TauCeti.IsConvexPolyhedron P := by
  obtain ⟨σ, _, rfl⟩ := hP
  exact isConvexPolyhedron_closure_signCell

/-- Intersections of realized closed cells are extreme subsets of each cell;
the intersection is allowed to be empty. -/
theorem isExtreme_inter_of_mem_realizedSignCellClosures
    [ContinuousAdd V] [ContinuousSMul ℝ V]
    {g : ι → (V →ᴬ[ℝ] ℝ)} {P Q : Set V}
    (hP : P ∈ realizedSignCellClosures g) (hQ : Q ∈ realizedSignCellClosures g) :
    IsExtreme ℝ P (P ∩ Q) := by
  obtain ⟨σ, _, rfl⟩ := hP
  obtain ⟨τ, _, rfl⟩ := hQ
  exact isExtreme_closure_signCell_inter

end TauCeti.Convex
