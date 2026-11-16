/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Coherent
public import TauCeti.Topology.Homotopy.DeformationRetract
public import TauCeti.Topology.Homotopy.Extension.MappingCylinder
public import TauCeti.Topology.Homotopy.Extension.Pushout
public import TauCeti.Topology.Homotopy.MappingTelescope.Basic

/-!
# The stage filtration of the mapping telescope

The mapping telescope `TauCeti.MappingTelescope f` of `f : ∀ n, C(X n, X (n + 1))` carries a
canonical increasing filtration by closed subspaces `TauCeti.MappingTelescope.stage f n`: the
`n`-th stage consists of the cylinders `0, …, n - 1` together with the bottom face `X n` of the
`n`-th cylinder.

* `stage f 0` is the image of `incl f 0`, and `stage f (n + 1)` is the pushout in `TopCat` obtained
  from `stage f n` by attaching `MappingCylinder (f n)` along `X n`
  (`TauCeti.MappingTelescope.stage_succ`,
  `TauCeti.MappingTelescope.stage_inter_range_fromMappingCylinder`, and
  `TauCeti.MappingTelescope.isPushout_stage_succ`).
* The stages are closed (`TauCeti.MappingTelescope.isClosed_stage`), cover the telescope
  (`TauCeti.MappingTelescope.iUnion_stage`), and determine its topology coherently
  (`TauCeti.MappingTelescope.isCoherentWith_range_stage`), and every compact subset of the telescope
  lands in a finite stage (`TauCeti.MappingTelescope.exists_subset_stage_of_isCompact`).
* Collapsing the cylinders `0, …, n - 1` forward along the bonding maps gives a strong deformation
  retraction of `stage f n` onto the image of `X n`, exhibiting `inclStage f n : C(X n, stage f n)`
  as a homotopy equivalence `TauCeti.MappingTelescope.stageHomotopyEquiv f n : X n ≃ₕ stage f n`
  with retraction `TauCeti.MappingTelescope.stageProj f n` commuting strictly with the stage
  inclusions (`TauCeti.MappingTelescope.stageProj_inclusion`).
* Each inclusion `stage f n ⊆ stage f (n + 1)` has the homotopy extension property
  (`TauCeti.MappingTelescope.hasHomotopyExtensionProperty_stage`), deduced via
  `CategoryTheory.IsPushout.hasHomotopyExtensionProperty_range_inr` from
  `TauCeti.MappingCylinder.hasHomotopyExtensionProperty_range_incl`. Consequently every stage is a
  closed cofibration in every other stage and in the whole telescope
  (`TauCeti.MappingTelescope.hasHomotopyExtensionProperty_preimage_stage`,
  `TauCeti.MappingTelescope.hasHomotopyExtensionProperty_stage_univ`), and a well-pointed initial
  space `(X 0, x₀)` makes `(MappingTelescope f, incl f 0 x₀)` well-pointed
  (`TauCeti.MappingTelescope.hasHomotopyExtensionProperty_singleton_incl_zero`).

## References

* J. Milnor, *On axiomatic homology theory*, Pacific J. Math. 12 (1962), 337–341.
* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.F and Appendix, Proposition A.11.
* T. tom Dieck, *Algebraic Topology*, EMS Textbooks in Mathematics, 2008, Chapter 5.
-/

public section

noncomputable section

namespace TauCeti

open Set Topology ContinuousMap unitInterval

universe u

variable {X : ℕ → Type u} [∀ n, TopologicalSpace (X n)]

namespace MappingTelescope

variable {f : ∀ n, C(X n, X (n + 1))}

section Filtration

/-- The `n`-th finite stage of the mapping telescope: the union of the cylinders `0, …, n - 1`
together with the bottom face `Set.range (incl f n)` of the `n`-th cylinder. -/
def stage (f : ∀ n, C(X n, X (n + 1))) (n : ℕ) : Set (MappingTelescope f) :=
  Set.range (incl f n) ∪ ⋃ k < n, Set.range (mkCyl f k)

@[simp]
theorem stage_zero : stage f 0 = Set.range (incl f 0) := by
  simp [stage]

/-- A cylinder point `mkCyl f m (s, x)` belongs to `stage f n` if and only if `m < n`, or `m = n`
and `s = 0`. -/
@[simp]
theorem mkCyl_mem_stage_iff {m n : ℕ} {s : I} {x : X m} :
    mkCyl f m (s, x) ∈ stage f n ↔ m < n ∨ (m = n ∧ s = 0) := by
  simp only [stage, mem_union, mem_range, mem_iUnion, exists_prop]
  constructor
  · rintro (⟨y, hy⟩ | ⟨k, hkn, q, hq⟩)
    · rw [incl_apply, mkCyl_eq_mkCyl_iff] at hy
      rcases hy with ⟨hnm, h0s, -⟩ | ⟨_, h01, -⟩ | ⟨_, h01, -⟩ | ⟨hmn, -, _, -⟩
      · exact Or.inr ⟨hnm.symm, h0s.symm⟩
      · exact absurd h01 zero_ne_one
      · exact absurd h01 zero_ne_one
      · exact Or.inl (by omega)
    · obtain ⟨qt, qx⟩ := q
      rw [mkCyl_eq_mkCyl_iff] at hq
      rcases hq with ⟨hkm, -⟩ | ⟨hkm, -⟩ | ⟨hk1m, -, hs0, -⟩ | ⟨hm1k, -⟩
      · exact Or.inl (by omega)
      · exact Or.inl (by omega)
      · rcases Nat.lt_or_eq_of_le (by omega : m ≤ n) with hlt | rfl
        · exact Or.inl hlt
        · exact Or.inr ⟨rfl, hs0⟩
      · exact Or.inl (by omega)
  · rintro (hmn | ⟨rfl, rfl⟩)
    · exact Or.inr ⟨m, hmn, (s, x), rfl⟩
    · exact Or.inl ⟨x, incl_apply m x⟩

theorem incl_mem_stage_iff {m n : ℕ} {x : X m} :
    incl f m x ∈ stage f n ↔ m ≤ n := by
  rw [incl_apply, mkCyl_mem_stage_iff]
  exact ⟨by rintro (h | ⟨rfl, -⟩); exacts [h.le, le_rfl],
    fun h => h.lt_or_eq.imp id fun h' => ⟨h', rfl⟩⟩

theorem stage_mono : Monotone (stage f) := by
  intro m n hmn z
  induction z using ind with
  | cyl k q =>
    obtain ⟨s, x⟩ := q
    simp only [mkCyl_mem_stage_iff]
    rintro (hk | ⟨rfl, rfl⟩)
    · exact Or.inl (lt_of_lt_of_le hk hmn)
    · exact hmn.lt_or_eq.imp id fun h => ⟨h, rfl⟩

/-- `stage f (n + 1)` is obtained from `stage f n` by attaching `MappingCylinder (f n)`. -/
theorem stage_succ (n : ℕ) :
    stage f (n + 1) = stage f n ∪ Set.range (fromMappingCylinder f n) := by
  ext z
  induction z using ind with
  | cyl k q =>
    obtain ⟨s, x⟩ := q
    rw [mem_union, range_fromMappingCylinder, mem_union]
    constructor
    · intro hz
      rcases mkCyl_mem_stage_iff.1 hz with hk | ⟨rfl, rfl⟩
      · rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hk) with hlt | rfl
        · exact Or.inl (mkCyl_mem_stage_iff.2 (Or.inl hlt))
        · exact Or.inr (Or.inl ⟨(s, x), rfl⟩)
      · exact Or.inr (Or.inr ⟨x, incl_apply (n + 1) x⟩)
    · rintro (hz | ⟨p, hp⟩ | ⟨y, hy⟩)
      · exact stage_mono n.le_succ hz
      · rw [← hp]
        exact mkCyl_mem_stage_iff.2 (Or.inl n.lt_succ_self)
      · rw [← hy]
        exact incl_mem_stage_iff.2 le_rfl

/-- `stage f n` meets the attached `MappingCylinder (f n)` along `Set.range (incl f n)`. -/
theorem stage_inter_range_fromMappingCylinder (n : ℕ) :
    stage f n ∩ Set.range (fromMappingCylinder f n) = Set.range (incl f n) := by
  ext z
  simp only [mem_inter_iff, mem_range]
  constructor
  · rintro ⟨hz, w, rfl⟩
    induction w using MappingCylinder.ind with
    | cyl q =>
      obtain ⟨qs, qx⟩ := q
      rw [fromMappingCylinder_mkCyl, mkCyl_mem_stage_iff] at hz
      rcases hz with hlt | ⟨_, rfl⟩
      · omega
      · exact ⟨qx, by simp⟩
    | base y =>
      rw [fromMappingCylinder_mkBase, incl_mem_stage_iff] at hz
      omega
  · rintro ⟨x, rfl⟩
    exact ⟨incl_mem_stage_iff.2 le_rfl, MappingCylinder.incl (f n) x, fromMappingCylinder_incl n x⟩

/-- The canonical homotopy `inclHomotopyOfLE f h` for `m ≤ n` stays inside `stage f n`. -/
theorem inclHomotopyOfLE_mem_stage {m n : ℕ} (h : m ≤ n) (t : I) (x : X m) :
    inclHomotopyOfLE f h (t, x) ∈ stage f n := by
  induction n, h using Nat.le_induction generalizing t with
  | base =>
    rw [inclHomotopyOfLE_refl]
    simp
  | succ k hmk ih =>
    rw [inclHomotopyOfLE_step hmk, ContinuousMap.Homotopy.cast_apply,
      ContinuousMap.Homotopy.trans_apply]
    split_ifs
    · exact stage_mono k.le_succ (ih _)
    · simp only [ContinuousMap.Homotopy.compContinuousMap_apply, inclHomotopy_apply]
      exact mkCyl_mem_stage_iff.2 (Or.inl k.lt_succ_self)

/-- **Every stage `stage f n` is a closed subspace of the mapping telescope.** -/
theorem isClosed_stage (n : ℕ) : IsClosed (stage f n) := by
  refine isClosed_iff.2 fun m => ?_
  rcases lt_trichotomy m n with hlt | rfl | hgt
  · convert isClosed_univ using 1
    ext ⟨s, x⟩
    simp [mkCyl_mem_stage_iff, hlt]
  · convert (isClosed_singleton (x := (0 : I))).preimage continuous_fst using 1
    ext ⟨s, x⟩
    simp [mkCyl_mem_stage_iff]
  · convert isClosed_empty using 1
    ext ⟨s, x⟩
    simp only [mem_preimage, mkCyl_mem_stage_iff, mem_empty_iff_false, iff_false]
    omega

/-- The stages exhaust the mapping telescope. -/
theorem iUnion_stage : ⋃ n, stage f n = Set.univ := by
  ext z
  simp only [mem_iUnion, mem_univ, iff_true]
  induction z using ind with
  | cyl m q =>
    obtain ⟨s, x⟩ := q
    exact ⟨m + 1, mkCyl_mem_stage_iff.2 (Or.inl m.lt_succ_self)⟩

/-- **The mapping telescope carries the topology coherent with its finite stages.** -/
theorem isCoherentWith_range_stage : Topology.IsCoherentWith (Set.range (stage f)) := by
  refine .of_isClosed fun t ht => isClosed_iff.2 fun m => ?_
  let c : C(I × X m, stage f (m + 1)) :=
    ⟨fun p => ⟨mkCyl f m p, mkCyl_mem_stage_iff.2 (Or.inl m.lt_succ_self)⟩,
      (mkCyl f m).continuous.subtype_mk _⟩
  exact (ht (stage f (m + 1)) (mem_range_self (m + 1))).preimage c.continuous

/-- Any cofinal sequence of stages covers the mapping telescope. -/
theorem iUnion_stage_comp {φ : ℕ → ℕ} (hcof : ∀ m, ∃ n, m ≤ φ n) :
    ⋃ n, stage f (φ n) = Set.univ := by
  ext z
  simp only [mem_iUnion, mem_univ, iff_true]
  obtain ⟨m, hm⟩ := mem_iUnion.1 (iUnion_stage (f := f) ▸ mem_univ z)
  obtain ⟨n, hmn⟩ := hcof m
  exact ⟨n, stage_mono hmn hm⟩

/-- Any cofinal sequence of stages determines the topology of the mapping telescope coherently. -/
theorem isCoherentWith_range_stage_comp {φ : ℕ → ℕ} (hcof : ∀ m, ∃ n, m ≤ φ n) :
    Topology.IsCoherentWith (Set.range fun n => stage f (φ n)) := by
  refine .of_isClosed fun t ht => isCoherentWith_range_stage.isClosed_iff.2 <|
    forall_mem_range.2 fun m => ?_
  obtain ⟨n, hmn⟩ := hcof m
  let inc : C(stage f m, stage f (φ n)) :=
    ⟨Set.inclusion (stage_mono hmn), continuous_inclusion _⟩
  exact (ht (stage f (φ n)) (mem_range_self n)).preimage inc.continuous

/-- Every point of height strictly less than `n` lies in `stage f n`. -/
theorem mem_stage_of_height_lt {z : MappingTelescope f} {n : ℕ} (h : height f z < n) :
    z ∈ stage f n := by
  induction z using ind_ne_one with
  | cyl m s x _ =>
    rw [height_mkCyl] at h
    have hm : (m : ℝ) < n := lt_of_le_of_lt (le_add_of_nonneg_right s.2.1) h
    exact mkCyl_mem_stage_iff.2 (Or.inl (Nat.cast_lt.1 hm))

/-- Every compact subset of `MappingTelescope f` lies in a finite stage. -/
theorem exists_subset_stage_of_isCompact {K : Set (MappingTelescope f)} (hK : IsCompact K) :
    ∃ n, K ⊆ stage f n := by
  obtain ⟨B, hB⟩ := (hK.image (height f).continuous).bddAbove
  obtain ⟨n, hn⟩ := exists_nat_gt B
  exact ⟨n, fun z hz => mem_stage_of_height_lt (lt_of_le_of_lt (hB ⟨z, hz, rfl⟩) hn)⟩

end Filtration

section StageHomotopyEquiv

/-- The inclusion of `X n` into the `n`-th stage `stage f n`. -/
def inclStage (f : ∀ n, C(X n, X (n + 1))) (n : ℕ) : C(X n, stage f n) :=
  ⟨fun x => ⟨incl f n x, incl_mem_stage_iff.2 le_rfl⟩, (incl f n).continuous.subtype_mk _⟩

@[simp]
lemma inclStage_coe (n : ℕ) (x : X n) : (inclStage f n x : MappingTelescope f) = incl f n x :=
  (rfl)

/-- Inclusion of the shifted mapping telescope `MappingTelescope (fun n => f (n + 1))` into
`MappingTelescope f` by shifting cylinder indices by `1`. -/
def tailIncl (f : ∀ n, C(X n, X (n + 1))) :
    C(MappingTelescope (fun n => f (n + 1)), MappingTelescope f) :=
  lift (X := fun k => X (k + 1)) (f := fun k => f (k + 1))
    (fun n => mkCyl f (n + 1)) fun n x => mkCyl_one (n + 1) x

@[simp]
lemma tailIncl_mkCyl (n : ℕ) (p : I × X (n + 1)) :
    tailIncl f (mkCyl (X := fun k => X (k + 1)) (fun k => f (k + 1)) n p) = mkCyl f (n + 1) p :=
  lift_mkCyl (X := fun k => X (k + 1)) (f := fun k => f (k + 1)) _ n p

lemma tailIncl_incl (n : ℕ) (x : X (n + 1)) :
    tailIncl f (incl (X := fun k => X (k + 1)) (fun k => f (k + 1)) n x) = incl f (n + 1) x := by
  rw [incl_apply, tailIncl_mkCyl, incl_apply]

@[simp]
lemma tailIncl_comp_incl (n : ℕ) :
    (tailIncl f).comp (incl (X := fun k => X (k + 1)) (fun k => f (k + 1)) n) =
      incl f (n + 1) :=
  ContinuousMap.ext (tailIncl_incl n)

/-- Retraction of `MappingTelescope f` onto the shifted telescope
`MappingTelescope (fun n => f (n + 1))` collapsing cylinder `0` onto `incl _ 0 ∘ f 0`. -/
def tailRetract (f : ∀ n, C(X n, X (n + 1))) :
    C(MappingTelescope f, MappingTelescope (X := fun k => X (k + 1)) (fun n => f (n + 1))) :=
  lift
    (fun n => Nat.casesOn n
      ((incl (X := fun k => X (k + 1)) (fun k => f (k + 1)) 0).comp
        ((f 0).comp ⟨Prod.snd, continuous_snd⟩))
      (fun m => mkCyl (X := fun k => X (k + 1)) (fun k => f (k + 1)) m))
    fun n x => by
      cases n with
      | zero => simp [incl_apply]
      | succ m => exact mkCyl_one (X := fun k => X (k + 1)) (f := fun k => f (k + 1)) m x

@[simp]
lemma tailRetract_mkCyl_zero (p : I × X 0) :
    tailRetract f (mkCyl f 0 p) =
      incl (X := fun k => X (k + 1)) (fun k => f (k + 1)) 0 (f 0 p.2) :=
  lift_mkCyl _ 0 p

@[simp]
lemma tailRetract_mkCyl_succ (m : ℕ) (p : I × X (m + 1)) :
    tailRetract f (mkCyl f (m + 1) p) =
      mkCyl (X := fun k => X (k + 1)) (fun k => f (k + 1)) m p :=
  lift_mkCyl _ (m + 1) p

@[simp]
lemma tailRetract_tailIncl (z : MappingTelescope (X := fun k => X (k + 1)) (fun k => f (k + 1))) :
    tailRetract f (tailIncl f z) = z := by
  induction z using ind with
  | cyl m p => simp

private def tailDeformMap (f : ∀ n, C(X n, X (n + 1))) (t : I) :
    C(MappingTelescope f, MappingTelescope f) :=
  lift
    (fun n => Nat.casesOn n
      ((mkCyl f 0).comp ⟨fun p : I × X 0 => (p.1 ⊔ t, p.2),
        (continuous_fst.sup continuous_const).prodMk continuous_snd⟩)
      (fun m => mkCyl f (m + 1)))
    fun n x => by
      cases n with
      | zero =>
        have ht : t ≤ 1 := t.2.2
        dsimp
        rw [max_eq_left ht, mkCyl_one]
      | succ m => exact mkCyl_one (m + 1) x

private lemma tailDeformMap_mkCyl_zero (t : I) (p : I × X 0) :
    tailDeformMap f t (mkCyl f 0 p) = mkCyl f 0 (p.1 ⊔ t, p.2) :=
  lift_mkCyl _ 0 p

private lemma tailDeformMap_mkCyl_succ (t : I) (m : ℕ) (p : I × X (m + 1)) :
    tailDeformMap f t (mkCyl f (m + 1) p) = mkCyl f (m + 1) p :=
  lift_mkCyl _ (m + 1) p

/-- Strong deformation of `MappingTelescope f` onto `Set.range (tailIncl f)`, sliding the `0`-th
cylinder upward via `(s, x) ↦ (s ⊔ t, x)` while keeping all higher cylinders stationary. -/
private def tailDeform (f : ∀ n, C(X n, X (n + 1))) :
    C(I × MappingTelescope f, MappingTelescope f) where
  toFun q := tailDeformMap f q.1 q.2
  continuous_toFun := by
    rw [continuous_prod_iff]
    intro n
    cases n with
    | zero =>
      simp only [tailDeformMap_mkCyl_zero]
      exact (mkCyl f 0).continuous.comp
        (((continuous_fst.comp continuous_snd).sup continuous_fst).prodMk
          (continuous_snd.comp continuous_snd))
    | succ m =>
      simp only [tailDeformMap_mkCyl_succ]
      exact (mkCyl f (m + 1)).continuous.comp continuous_snd

private lemma tailDeform_apply (t : I) (z : MappingTelescope f) :
    tailDeform f (t, z) = tailDeformMap f t z :=
  (rfl)

private lemma tailDeform_zero (z : MappingTelescope f) : tailDeform f (0, z) = z := by
  induction z using ind with
  | cyl n p =>
    rw [tailDeform_apply]
    cases n with
    | zero =>
      obtain ⟨s, x⟩ := p
      have hs : (0 : I) ≤ s := s.2.1
      rw [tailDeformMap_mkCyl_zero]
      dsimp only
      rw [max_eq_left hs]
    | succ m =>
      exact tailDeformMap_mkCyl_succ 0 m p

private lemma tailDeform_one (z : MappingTelescope f) :
    tailDeform f (1, z) = tailIncl f (tailRetract f z) := by
  induction z using ind with
  | cyl n p =>
    rw [tailDeform_apply]
    cases n with
    | zero =>
      obtain ⟨s, x⟩ := p
      have hs : s ≤ 1 := s.2.2
      rw [tailDeformMap_mkCyl_zero]
      dsimp only
      rw [max_eq_right hs, mkCyl_one, tailRetract_mkCyl_zero, tailIncl_incl, incl_apply]
    | succ m =>
      rw [tailDeformMap_mkCyl_succ, tailRetract_mkCyl_succ, tailIncl_mkCyl]

private lemma tailDeform_tailIncl (t : I)
    (w : MappingTelescope (X := fun k => X (k + 1)) (fun k => f (k + 1))) :
    tailDeform f (t, tailIncl f w) = tailIncl f w := by
  induction w using ind with
  | cyl m p =>
    rw [tailDeform_apply, tailIncl_mkCyl, tailDeformMap_mkCyl_succ]

private lemma tailDeform_mem_stage (n : ℕ) (t : I) {z : MappingTelescope f}
    (hz : z ∈ stage f (n + 1)) : tailDeform f (t, z) ∈ stage f (n + 1) := by
  induction z using ind with
  | cyl k p =>
    rw [tailDeform_apply]
    cases k with
    | zero =>
      obtain ⟨s, x⟩ := p
      rw [tailDeformMap_mkCyl_zero]
      exact mkCyl_mem_stage_iff.2 (Or.inl (Nat.zero_lt_succ n))
    | succ m =>
      rwa [tailDeformMap_mkCyl_succ]

private lemma mapsTo_tailIncl_stage (n : ℕ) :
    MapsTo (tailIncl f) (stage (X := fun k => X (k + 1)) (fun k => f (k + 1)) n)
      (stage f (n + 1)) := by
  intro w hw
  induction w using ind with
  | cyl m p =>
    obtain ⟨s, x⟩ := p
    rw [tailIncl_mkCyl, mkCyl_mem_stage_iff]
    rcases mkCyl_mem_stage_iff.1 hw with hlt | ⟨rfl, rfl⟩
    · exact Or.inl (Nat.succ_lt_succ hlt)
    · exact Or.inr ⟨rfl, rfl⟩

private lemma mapsTo_tailRetract_stage (n : ℕ) :
    MapsTo (tailRetract f) (stage f (n + 1))
      (stage (X := fun k => X (k + 1)) (fun k => f (k + 1)) n) := by
  intro z hz
  induction z using ind with
  | cyl k p =>
    obtain ⟨s, x⟩ := p
    cases k with
    | zero =>
      rw [tailRetract_mkCyl_zero]
      exact incl_mem_stage_iff.2 (Nat.zero_le n)
    | succ m =>
      rw [tailRetract_mkCyl_succ, mkCyl_mem_stage_iff]
      rcases mkCyl_mem_stage_iff.1 hz with hlt | ⟨h, rfl⟩
      · exact Or.inl (Nat.lt_of_succ_lt_succ hlt)
      · exact Or.inr ⟨by omega, rfl⟩

/-- The retraction of `stage f n` onto `X n` obtained by collapsing the cylinders `0, …, n - 1`
forward along the bonding maps `f`. -/
def stageProj {X : ℕ → Type u} [∀ n, TopologicalSpace (X n)]
    (f : ∀ n, C(X n, X (n + 1))) : ∀ n : ℕ, C(stage f n, X n)
  | 0 =>
    ⟨fun z => (inclHomeomorph f 0).symm ⟨z.1, stage_zero (f := f) ▸ z.2⟩,
      (inclHomeomorph f 0).symm.continuous.comp (continuous_subtype_val.subtype_mk _)⟩
  | n + 1 =>
    (stageProj (X := fun k => X (k + 1)) (fun k => f (k + 1)) n).comp
      ⟨(mapsTo_tailRetract_stage n).restrict _ _ _, (tailRetract f).continuous.restrict _⟩

private lemma stageProj_zero_apply (z : stage f 0) :
    stageProj f 0 z = (inclHomeomorph f 0).symm ⟨z.1, stage_zero (f := f) ▸ z.2⟩ := (rfl)

private lemma stageProj_succ_apply (n : ℕ) (z : stage f (n + 1)) :
    stageProj f (n + 1) z =
      stageProj (X := fun k => X (k + 1)) (fun k => f (k + 1)) n
        ⟨tailRetract f z.1, mapsTo_tailRetract_stage n z.2⟩ :=
  (rfl)

@[simp]
theorem stageProj_inclStage (n : ℕ) (x : X n) :
    stageProj f n (inclStage f n x) = x := by
  induction n generalizing X with
  | zero =>
    rw [stageProj_zero_apply]
    have heq : (⟨(inclStage f 0 x).1, stage_zero (f := f) ▸ (inclStage f 0 x).2⟩ :
        Set.range (incl f 0)) = inclHomeomorph f 0 x := by
      ext
      simp
    rw [heq, Homeomorph.symm_apply_apply]
  | succ n ih =>
    rw [stageProj_succ_apply]
    have heq : (⟨tailRetract f (inclStage f (n + 1) x).1,
        mapsTo_tailRetract_stage n (inclStage f (n + 1) x).2⟩ :
        stage (X := fun k => X (k + 1)) (fun k => f (k + 1)) n) =
        inclStage (X := fun k => X (k + 1)) (fun k => f (k + 1)) n x := by
      ext
      simp [incl_apply]
    rw [heq]
    exact ih (X := fun k => X (k + 1)) (f := fun k => f (k + 1)) x

private lemma bondOfLE_shift {m n : ℕ} (h : m ≤ n) :
    bondOfLE (X := fun k => X (k + 1)) (fun k => f (k + 1)) h =
      bondOfLE f (Nat.succ_le_succ h) := by
  induction n, h using Nat.le_induction with
  | base => simp
  | succ k hmk ih =>
    rw [bondOfLE_step hmk, bondOfLE_step (Nat.succ_le_succ hmk), ih]

private lemma stageProj_mkCyl_of_lt {k n : ℕ} (hk : k < n) (s : I) (x : X k)
    {hz : mkCyl f k (s, x) ∈ stage f n} :
    stageProj f n ⟨mkCyl f k (s, x), hz⟩ = bondOfLE f hk.le x := by
  induction n generalizing X k s with
  | zero => omega
  | succ n ih =>
    rw [stageProj_succ_apply]
    cases k with
    | zero =>
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · have heq : (⟨tailRetract f (mkCyl f 0 (s, x)), mapsTo_tailRetract_stage 0 hz⟩ :
            stage (X := fun m => X (m + 1)) (fun m => f (m + 1)) 0) =
            inclStage (X := fun m => X (m + 1)) (fun m => f (m + 1)) 0 (f 0 x) := by
          ext
          simp
        rw [heq, stageProj_inclStage, bondOfLE_succ]
      · have heq : (⟨tailRetract f (mkCyl f 0 (s, x)), mapsTo_tailRetract_stage n hz⟩ :
            stage (X := fun m => X (m + 1)) (fun m => f (m + 1)) n) =
            ⟨mkCyl (X := fun m => X (m + 1)) (fun m => f (m + 1)) 0 (0, f 0 x),
              mkCyl_mem_stage_iff.2 (Or.inl hn)⟩ := by
          ext
          simp [incl_apply]
        rw [heq, ih (X := fun m => X (m + 1)) (f := fun m => f (m + 1)) hn 0 (f 0 x),
          bondOfLE_shift]
        have hcomp := bondOfLE_apply_bondOfLE (f := f) (Nat.le_succ 0)
          (Nat.succ_le_succ hn.le) x
        rwa [bondOfLE_succ] at hcomp
    | succ m =>
      have hmn : m < n := Nat.lt_of_succ_lt_succ hk
      have heq : (⟨tailRetract f (mkCyl f (m + 1) (s, x)), mapsTo_tailRetract_stage n hz⟩ :
          stage (X := fun j => X (j + 1)) (fun j => f (j + 1)) n) =
          ⟨mkCyl (X := fun j => X (j + 1)) (fun j => f (j + 1)) m (s, x),
            mkCyl_mem_stage_iff.2 (Or.inl hmn)⟩ := by
        ext
        simp
      rw [heq, ih (X := fun j => X (j + 1)) (f := fun j => f (j + 1)) hmn s x, bondOfLE_shift]

/-- On any cylinder `k ≤ n` meeting `stage f n`, `stageProj f n` evaluates to the composite bonding
map `bondOfLE f`. -/
@[simp]
theorem stageProj_mkCyl {k n : ℕ} (h : k ≤ n) (s : I) (x : X k)
    {hz : mkCyl f k (s, x) ∈ stage f n} :
    stageProj f n ⟨mkCyl f k (s, x), hz⟩ = bondOfLE f h x := by
  rcases h.lt_or_eq with hk | rfl
  · exact stageProj_mkCyl_of_lt hk s x
  · rcases mkCyl_mem_stage_iff.1 hz with hk | ⟨-, rfl⟩
    · omega
    · have heq : (⟨mkCyl f k (0, x), hz⟩ : stage f k) = inclStage f k x := by
        ext
        simp [incl_apply]
      rw [heq, stageProj_inclStage, bondOfLE_refl, ContinuousMap.id_apply]

/-- **Naturality of stage retractions.** Restricting `stageProj f (n + 1)` to `stage f n` equals
`f n` composed with `stageProj f n`. -/
theorem stageProj_inclusion (n : ℕ) (z : stage f n) :
    stageProj f (n + 1) (Set.inclusion (stage_mono n.le_succ) z) = f n (stageProj f n z) := by
  obtain ⟨z, hz⟩ := z
  induction z using ind with
  | cyl k p =>
    obtain ⟨s, x⟩ := p
    have hk : k ≤ n := (mkCyl_mem_stage_iff.1 hz).elim le_of_lt fun h => h.1.le
    rw [stageProj_mkCyl (Nat.le_succ_of_le hk), stageProj_mkCyl hk, bondOfLE_step hk,
      ContinuousMap.comp_apply]

/-- **Each `stage f n` strong-deformation retracts onto `Set.range (inclStage f n)`.** -/
theorem homotopicRel_id_stage (n : ℕ) :
    (ContinuousMap.id (stage f n)).HomotopicRel
      ((inclStage f n).comp (stageProj f n)) (Set.range (inclStage f n)) := by
  induction n generalizing X with
  | zero =>
    have hid : (inclStage f 0).comp (stageProj f 0) = ContinuousMap.id (stage f 0) := by
      ext ⟨z, hz⟩
      simp only [ContinuousMap.comp_apply, ContinuousMap.id_apply, inclStage_coe,
        stageProj_zero_apply]
      exact (inclHomeomorph_apply_coe 0 _).symm.trans
        (congrArg Subtype.val ((inclHomeomorph f 0).apply_symm_apply ⟨z, stage_zero (f := f) ▸ hz⟩))
    rw [hid]
    exact ContinuousMap.HomotopicRel.refl _
  | succ n ih =>
    let i : C(stage (X := fun k => X (k + 1)) (fun k => f (k + 1)) n, stage f (n + 1)) :=
      ⟨(mapsTo_tailIncl_stage n).restrict _ _ _, (tailIncl f).continuous.restrict _⟩
    let r : C(stage f (n + 1), stage (X := fun k => X (k + 1)) (fun k => f (k + 1)) n) :=
      ⟨(mapsTo_tailRetract_stage n).restrict _ _ _, (tailRetract f).continuous.restrict _⟩
    have hri : Function.LeftInverse r i := fun w => Subtype.ext (tailRetract_tailIncl w.1)
    have hH : (ContinuousMap.id (stage f (n + 1))).HomotopicRel (i.comp r) (Set.range i) :=
      ⟨{ toFun q := ⟨tailDeform f (q.1, q.2.1), tailDeform_mem_stage n q.1 q.2.2⟩
         continuous_toFun := by
           refine Continuous.subtype_mk ?_ _
           exact (tailDeform f).continuous.comp
             (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
         map_zero_left z := Subtype.ext (tailDeform_zero z.1)
         map_one_left z := Subtype.ext (tailDeform_one z.1)
         prop' := by
           rintro t _ ⟨w, rfl⟩
           exact Subtype.ext (tailDeform_tailIncl t w.1) }⟩
    have hij : i.comp (inclStage (X := fun k => X (k + 1)) (fun k => f (k + 1)) n) =
        inclStage f (n + 1) := by
      ext x
      exact tailIncl_incl n x
    have hsr : (stageProj (X := fun k => X (k + 1)) (fun k => f (k + 1)) n).comp r =
        stageProj f (n + 1) := rfl
    simpa only [hij, hsr] using
      hH.comp_retractions (ih (X := fun k => X (k + 1)) (f := fun k => f (k + 1))) hri

/-- **Every finite stage `stage f n` is homotopy equivalent to `X n`.** -/
def stageHomotopyEquiv (f : ∀ n, C(X n, X (n + 1))) (n : ℕ) : X n ≃ₕ stage f n :=
  ContinuousMap.HomotopyEquiv.ofDeformationRetraction (inclStage f n) (stageProj f n)
    (stageProj_inclStage n) ⟨(homotopicRel_id_stage n).symm.some.toHomotopy⟩

@[simp]
theorem stageHomotopyEquiv_toFun (n : ℕ) :
    (stageHomotopyEquiv f n).toFun = inclStage f n :=
  ContinuousMap.HomotopyEquiv.ofDeformationRetraction_toFun _ _ _ _

@[simp]
theorem stageHomotopyEquiv_invFun (n : ℕ) :
    (stageHomotopyEquiv f n).invFun = stageProj f n :=
  ContinuousMap.HomotopyEquiv.ofDeformationRetraction_invFun _ _ _ _

theorem stageHomotopyEquiv_apply_coe (n : ℕ) (x : X n) :
    (stageHomotopyEquiv f n x : MappingTelescope f) = incl f n x := by
  rw [stageHomotopyEquiv_toFun, inclStage_coe]

@[simp]
theorem stageHomotopyEquiv_symm_apply (n : ℕ) (z : stage f n) :
    (stageHomotopyEquiv f n).symm z = stageProj f n z :=
  ContinuousMap.HomotopyEquiv.ofDeformationRetraction_symm_apply _ _ _ _ z

/-- `tailIncl f` is a homotopy equivalence from the shifted telescope to `MappingTelescope f`. -/
def tailHomotopyEquiv (f : ∀ n, C(X n, X (n + 1))) :
    MappingTelescope (X := fun k => X (k + 1)) (fun n => f (n + 1)) ≃ₕ MappingTelescope f :=
  ContinuousMap.HomotopyEquiv.ofDeformationRetraction (tailIncl f) (tailRetract f)
    tailRetract_tailIncl
    ⟨({ toContinuousMap := tailDeform f
        map_zero_left := tailDeform_zero
        map_one_left := tailDeform_one } :
      (ContinuousMap.id (MappingTelescope f)).Homotopy ((tailIncl f).comp (tailRetract f))).symm⟩

@[simp]
theorem tailHomotopyEquiv_toFun : (tailHomotopyEquiv f).toFun = tailIncl f :=
  ContinuousMap.HomotopyEquiv.ofDeformationRetraction_toFun _ _ _ _

@[simp]
theorem tailHomotopyEquiv_invFun : (tailHomotopyEquiv f).invFun = tailRetract f :=
  ContinuousMap.HomotopyEquiv.ofDeformationRetraction_invFun _ _ _ _

end StageHomotopyEquiv

section HomotopyExtension

open CategoryTheory Limits

/-- The embedding of `MappingCylinder (f n)` into `stage f (n + 1)`. -/
def fromMappingCylinderStage (f : ∀ n, C(X n, X (n + 1))) (n : ℕ) :
    C(MappingCylinder (f n), stage f (n + 1)) :=
  ⟨fun w => ⟨fromMappingCylinder f n w,
      (Set.ext_iff.1 (stage_succ (f := f) n) _).2 (Or.inr (mem_range_self w))⟩,
    (fromMappingCylinder f n).continuous.subtype_mk _⟩

@[simp]
lemma fromMappingCylinderStage_coe (n : ℕ) (w : MappingCylinder (f n)) :
    (fromMappingCylinderStage f n w : MappingTelescope f) = fromMappingCylinder f n w :=
  (rfl)

/-- `fromMappingCylinderStage f n` is a closed embedding into `stage f (n + 1)`. -/
theorem isClosedEmbedding_fromMappingCylinderStage (n : ℕ) :
    IsClosedEmbedding (fromMappingCylinderStage f n) := by
  refine ⟨.of_comp (fromMappingCylinderStage f n).continuous continuous_subtype_val
    (isClosedEmbedding_fromMappingCylinder n).isEmbedding, ?_⟩
  have hrange : Set.range (fromMappingCylinderStage f n) =
      ((↑) ⁻¹' Set.range (fromMappingCylinder f n) : Set (stage f (n + 1))) := by
    ext z
    exact ⟨by rintro ⟨w, rfl⟩; exact mem_range_self w,
      by rintro ⟨w, hw⟩; exact ⟨w, Subtype.ext hw⟩⟩
  rw [hrange]
  exact (isClosedEmbedding_fromMappingCylinder n).isClosed_range.preimage continuous_subtype_val

/-- **Pushout presentation of successor stages.** In `TopCat`, `stage f (n + 1)` is the pushout of
`MappingCylinder (f n)` and `stage f n` along `X n`. -/
theorem isPushout_stage_succ (n : ℕ) :
    IsPushout (TopCat.ofHom (MappingCylinder.incl (f n))) (TopCat.ofHom (inclStage f n))
      (TopCat.ofHom (fromMappingCylinderStage f n))
      (TopCat.ofHom ⟨Set.inclusion (stage_mono n.le_succ), continuous_inclusion _⟩) := by
  let inl : TopCat.of (MappingCylinder (f n)) ⟶ TopCat.of (stage f (n + 1)) :=
    TopCat.ofHom (fromMappingCylinderStage f n)
  let inr : TopCat.of (stage f n) ⟶ TopCat.of (stage f (n + 1)) :=
    TopCat.ofHom ⟨Set.inclusion (stage_mono n.le_succ), continuous_inclusion _⟩
  have hinr : IsClosedEmbedding inr :=
    ⟨Topology.IsEmbedding.inclusion (stage_mono n.le_succ), by
      have hr : Set.range inr = Set.range (Set.inclusion (stage_mono n.le_succ)) := rfl
      rw [hr, Set.range_inclusion]
      exact (isClosed_stage n).preimage continuous_subtype_val⟩
  have hcover : Set.range inr ∪ ⋃ _ : Unit, Set.range inl = Set.univ := by
    ext z
    simp only [mem_union, mem_iUnion, exists_const, mem_univ, iff_true]
    rcases (Set.ext_iff.1 (stage_succ (f := f) n) z.1).1 z.2 with hz | ⟨w, hw⟩
    · exact Or.inl ⟨⟨z.1, hz⟩, rfl⟩
    · exact Or.inr ⟨w, Subtype.ext hw⟩
  have w : TopCat.ofHom (MappingCylinder.incl (f n)) ≫ inl =
      TopCat.ofHom (inclStage f n) ≫ inr := by
    ext x
    exact fromMappingCylinder_incl n x
  let glue (s : PushoutCocone (TopCat.ofHom (MappingCylinder.incl (f n)))
      (TopCat.ofHom (inclStage f n))) :=
    TopCat.exists_glue_of_isClosedEmbedding (ι := Unit) (B := fun _ => _) hinr
      (fun _ => isClosedEmbedding_fromMappingCylinderStage n) hcover
      (fun k l hkl => (hkl (Subsingleton.elim k l)).elim) s.inr (fun _ => s.inl)
      fun _ u v huv => by
        have huv' : (u : MappingTelescope f) = fromMappingCylinder f n v :=
          congrArg (Subtype.val : stage f (n + 1) → MappingTelescope f) huv
        have hv : fromMappingCylinder f n v ∈ stage f n ∩ Set.range (fromMappingCylinder f n) :=
          ⟨by rw [← huv']; exact u.2, mem_range_self v⟩
        rw [stage_inter_range_fromMappingCylinder] at hv
        obtain ⟨x, hx⟩ := hv
        obtain rfl : MappingCylinder.incl (f n) x = v :=
          (fromMappingCylinder_injective n) ((fromMappingCylinder_incl n x).trans hx)
        obtain rfl : inclStage f n x = u := Subtype.ext (hx.trans huv'.symm)
        exact (ConcreteCategory.congr_hom s.condition x).symm
  refine IsPushout.of_isColimit' ⟨w⟩ (PushoutCocone.IsColimit.mk w (fun s => (glue s).choose)
    (fun s => (glue s).choose_spec.2 ()) (fun s => (glue s).choose_spec.1)
    fun s m hm_inl hm_inr => ?_)
  ext z
  rcases (Set.ext_iff.1 hcover z).2 (mem_univ z) with ⟨u, rfl⟩ | h
  · exact (ConcreteCategory.congr_hom hm_inr u).trans
      (ConcreteCategory.congr_hom (glue s).choose_spec.1 u).symm
  · obtain ⟨_, v, rfl⟩ := mem_iUnion.1 h
    exact (ConcreteCategory.congr_hom hm_inl v).trans
      (ConcreteCategory.congr_hom ((glue s).choose_spec.2 ()) v).symm

/-- **Every stage has the homotopy extension property in the next stage.** -/
theorem hasHomotopyExtensionProperty_stage (n : ℕ) :
    HasHomotopyExtensionProperty ((↑) ⁻¹' stage f n : Set (stage f (n + 1))) := by
  have hrange : ((↑) ⁻¹' stage f n : Set (stage f (n + 1))) =
      Set.range (TopCat.ofHom ⟨Set.inclusion (stage_mono n.le_succ), continuous_inclusion _⟩) :=
    (Set.range_inclusion (stage_mono n.le_succ)).symm
  rw [hrange]
  exact (isPushout_stage_succ n).hasHomotopyExtensionProperty_range_inr
    (MappingCylinder.isClosedEmbedding_incl (f := f n)).isEmbedding
    (MappingCylinder.hasHomotopyExtensionProperty_range_incl (f := f n))

/-- **For any `m` and `n`, the preimage of `stage f m` in `stage f n` has the homotopy extension
property.** For `m ≤ n` it is an iterated closed cofibration of stages; for `n ≤ m` it is
`Set.univ`. -/
theorem hasHomotopyExtensionProperty_preimage_stage (m n : ℕ) :
    HasHomotopyExtensionProperty ((↑) ⁻¹' stage f m : Set (stage f n)) := by
  rcases le_total m n with h | h
  · induction n, h using Nat.le_induction with
    | base =>
      have huniv : ((↑) ⁻¹' stage f m : Set (stage f m)) = Set.univ :=
        Set.ext fun z => ⟨fun _ => trivial, fun _ => z.2⟩
      rw [huniv]
      exact isClopen_univ.hasHomotopyExtensionProperty
    | succ k hmk ih =>
      have himg := ih.image_of_isEmbedding (Topology.IsEmbedding.inclusion (stage_mono k.le_succ))
        (by rw [Set.range_inclusion]; exact hasHomotopyExtensionProperty_stage k)
      convert himg using 1
      ext z
      simp only [mem_preimage, mem_image]
      exact ⟨fun hz => ⟨⟨z.1, stage_mono hmk hz⟩, hz, rfl⟩,
        by rintro ⟨w, hw, rfl⟩; exact hw⟩
  · have huniv : ((↑) ⁻¹' stage f m : Set (stage f n)) = Set.univ :=
      Set.ext fun z => ⟨fun _ => trivial, fun _ => stage_mono h z.2⟩
    rw [huniv]
    exact isClopen_univ.hasHomotopyExtensionProperty

/-- **Every stage `stage f n` has the homotopy extension property in `MappingTelescope f`.** -/
theorem hasHomotopyExtensionProperty_stage_univ (n : ℕ) :
    HasHomotopyExtensionProperty (stage f n) := by
  rw [hasHomotopyExtensionProperty_iff]
  intro Y _ g H hgH
  let S (k : ℕ) : Set (MappingTelescope f) := stage f (n + k)
  have hS_mono : Monotone S := fun i j hij => stage_mono (Nat.add_le_add_left hij n)
  have hS_cof (m : ℕ) : ∃ k, m ≤ n + k := ⟨m, Nat.le_add_left m n⟩
  have hS_univ : ⋃ k, S k = Set.univ := iUnion_stage_comp hS_cof
  have hS_coh : Topology.IsCoherentWith (Set.range S) := isCoherentWith_range_stage_comp hS_cof
  let P (k : ℕ) : Type u := { G : C(I × S k, Y) // ∀ x : S k, G (0, x) = g x }
  have step (k : ℕ) (p : P k) : ∃ p' : P (k + 1),
      ∀ (t : I) (x : S k), p'.1 (t, Set.inclusion (hS_mono k.le_succ) x) = p.1 (t, x) := by
    let j : C(I × ↥((↑) ⁻¹' S k : Set (S (k + 1))), I × S k) :=
      ⟨fun q => (q.1, ⟨q.2.1.1, q.2.2⟩), by fun_prop⟩
    obtain ⟨G', hG'0, hG'ext⟩ :=
      (hasHomotopyExtensionProperty_stage (f := f) (n + k)).exists_extension
        (g.restrict (S (k + 1))) (p.1.comp j) fun a => p.2 ⟨a.1.1, a.2⟩
    exact ⟨⟨G', hG'0⟩, fun t x => hG'ext t ⟨Set.inclusion (hS_mono k.le_succ) x, x.2⟩⟩
  choose next hnext using step
  let seq : ∀ k, P k := fun k => Nat.rec ⟨H, hgH⟩ next k
  have hseq_compat {i j : ℕ} (hij : i ≤ j) (t : I) (x : S i) :
      (seq j).1 (t, Set.inclusion (hS_mono hij) x) = (seq i).1 (t, x) := by
    induction j, hij using Nat.le_induction with
    | base => rfl
    | succ k hik ih => exact (hnext k (seq k) t (Set.inclusion (hS_mono hik) x)).trans ih
  have hIS_univ : ⋃ k, (Set.univ : Set I) ×ˢ S k = Set.univ := by
    simp [← prod_iUnion, hS_univ]
  let φ (k : ℕ) : C(↥((Set.univ : Set I) ×ˢ S k), Y) :=
    (seq k).1.comp ⟨fun q => (q.1.1, ⟨q.1.2, q.2.2⟩), by fun_prop⟩
  let G : C(I × MappingTelescope f, Y) :=
    ContinuousMap.liftCoherent (fun k => (Set.univ : Set I) ×ˢ S k) φ
      (fun i j q hi hj =>
        (hseq_compat (le_max_left i j) q.1 ⟨q.2, hi.2⟩).symm.trans
          (hseq_compat (le_max_right i j) q.1 ⟨q.2, hj.2⟩))
      (hS_coh.univ_prod hS_univ) hIS_univ
  have hG (k : ℕ) (t : I) (x : S k) : G (t, x) = (seq k).1 (t, x) :=
    ContinuousMap.liftCoherent_coe (S := fun k => (Set.univ : Set I) ×ˢ S k)
      ⟨(t, x.1), mem_univ t, x.2⟩
  refine ⟨G, fun z => ?_, fun t a => hG 0 t a⟩
  obtain ⟨k, hk⟩ := mem_iUnion.1 (hS_univ ▸ mem_univ z)
  exact (hG k 0 ⟨z, hk⟩).trans ((seq k).2 ⟨z, hk⟩)

/-- **Well-pointedness of the mapping telescope.** If `{x₀}` has the homotopy extension property in
`X 0`, then `{incl f 0 x₀}` has the homotopy extension property in `MappingTelescope f`. -/
theorem hasHomotopyExtensionProperty_singleton_incl_zero {x₀ : X 0}
    (hx₀ : HasHomotopyExtensionProperty ({x₀} : Set (X 0))) :
    HasHomotopyExtensionProperty ({incl f 0 x₀} : Set (MappingTelescope f)) := by
  have h0 : HasHomotopyExtensionProperty (inclHomeomorph f 0 '' ({x₀} : Set (X 0))) :=
    hx₀.image (inclHomeomorph f 0)
  have hstage : HasHomotopyExtensionProperty (Set.range (Subtype.val :
      Set.range (incl f 0) → MappingTelescope f)) := by
    rw [Subtype.range_coe, ← stage_zero]
    exact hasHomotopyExtensionProperty_stage_univ 0
  convert h0.image_of_isEmbedding Topology.IsEmbedding.subtypeVal hstage using 1
  ext z
  simp

end HomotopyExtension

end MappingTelescope

end TauCeti
