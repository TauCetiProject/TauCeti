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
  closed cofibration in every later stage and in the whole telescope, while its preimage in any
  earlier stage is the whole earlier stage
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
  refine ⟨?_, ?_⟩
  · rintro (⟨y, hy⟩ | ⟨k, hkn, ⟨qt, qx⟩, hq⟩)
    · rw [incl_apply, mkCyl_eq_mkCyl_iff] at hy
      rcases hy with ⟨hnm, h0s, -⟩ | ⟨_, h01, -⟩ | ⟨_, h01, -⟩ | ⟨hmn, -⟩
      exacts [Or.inr ⟨hnm.symm, h0s.symm⟩, absurd h01 zero_ne_one, absurd h01 zero_ne_one,
        Or.inl (by omega)]
    · rw [mkCyl_eq_mkCyl_iff] at hq
      rcases hq with ⟨hkm, -⟩ | ⟨hkm, -⟩ | ⟨hk1m, -, hs0, -⟩ | ⟨hm1k, -⟩
      exacts [Or.inl (by omega), Or.inl (by omega),
        (Nat.lt_or_eq_of_le (by omega : m ≤ n)).imp id fun h => ⟨h, hs0⟩, Or.inl (by omega)]
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
    refine ⟨fun hz => ?_, ?_⟩
    · rcases mkCyl_mem_stage_iff.1 hz with hk | ⟨rfl, rfl⟩
      · rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hk) with hlt | rfl
        · exact Or.inl (mkCyl_mem_stage_iff.2 (Or.inl hlt))
        · exact Or.inr (Or.inl ⟨(s, x), rfl⟩)
      · exact Or.inr (Or.inr ⟨x, incl_apply (n + 1) x⟩)
    · rintro (hz | ⟨p, hp⟩ | ⟨y, hy⟩)
      · exact stage_mono n.le_succ hz
      · exact hp ▸ mkCyl_mem_stage_iff.2 (Or.inl n.lt_succ_self)
      · exact hy ▸ incl_mem_stage_iff.2 le_rfl

/-- `stage f n` meets the attached `MappingCylinder (f n)` along `Set.range (incl f n)`. -/
theorem stage_inter_range_fromMappingCylinder (n : ℕ) :
    stage f n ∩ Set.range (fromMappingCylinder f n) = Set.range (incl f n) := by
  ext z
  simp only [mem_inter_iff, mem_range]
  refine ⟨?_, fun ⟨x, hx⟩ => ?_⟩
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
  · subst hx
    exact ⟨incl_mem_stage_iff.2 le_rfl, MappingCylinder.incl (f n) x, fromMappingCylinder_incl n x⟩

/-- The canonical homotopy `inclHomotopyOfLE f h` for `m ≤ n` stays inside `stage f n`. -/
theorem inclHomotopyOfLE_mem_stage {m n : ℕ} (h : m ≤ n) (t : I) (x : X m) :
    inclHomotopyOfLE f h (t, x) ∈ stage f n := by
  induction n, h using Nat.le_induction generalizing t with
  | base => simp
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
  | cyl m q => exact ⟨m + 1, mkCyl_mem_stage_iff.2 (Or.inl m.lt_succ_self)⟩

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
  exact (ht (stage f (φ n)) (mem_range_self n)).preimage (continuous_inclusion (stage_mono hmn))

/-- Every point of height strictly less than `n` lies in `stage f n`. -/
theorem mem_stage_of_height_lt {z : MappingTelescope f} {n : ℕ} (h : height f z < n) :
    z ∈ stage f n := by
  induction z using ind_ne_one with
  | cyl m s x _ =>
    rw [height_mkCyl] at h
    have hm : (m : ℝ) < n := lt_of_le_of_lt (le_add_of_nonneg_right s.property.1) h
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
        dsimp
        rw [max_eq_left (show t ≤ 1 from t.property.2), mkCyl_one]
      | succ m => exact mkCyl_one (m + 1) x

@[simp]
private lemma tailDeformMap_mkCyl_zero (t : I) (p : I × X 0) :
    tailDeformMap f t (mkCyl f 0 p) = mkCyl f 0 (p.1 ⊔ t, p.2) :=
  lift_mkCyl _ 0 p

@[simp]
private lemma tailDeformMap_mkCyl_succ (t : I) (m : ℕ) (p : I × X (m + 1)) :
    tailDeformMap f t (mkCyl f (m + 1) p) = mkCyl f (m + 1) p :=
  lift_mkCyl _ (m + 1) p

/-- Strong deformation of `MappingTelescope f` onto `Set.range (tailIncl f)`, sliding the `0`-th
cylinder upward via `(s, x) ↦ (s ⊔ t, x)` while keeping all higher cylinders stationary. -/
private def tailDeform (f : ∀ n, C(X n, X (n + 1))) :
    (ContinuousMap.id (MappingTelescope f)).Homotopy ((tailIncl f).comp (tailRetract f)) where
  toFun q := tailDeformMap f q.1 q.2
  continuous_toFun := continuous_prod_iff.2 fun n => by
    cases n with
    | zero =>
      simp only [tailDeformMap_mkCyl_zero]
      exact (mkCyl f 0).continuous.comp
        (((continuous_fst.comp continuous_snd).sup continuous_fst).prodMk
          (continuous_snd.comp continuous_snd))
    | succ m =>
      simp only [tailDeformMap_mkCyl_succ]
      exact (mkCyl f (m + 1)).continuous.comp continuous_snd
  map_zero_left z := by
    induction z using ind with
    | cyl n p =>
      cases n with
      | zero =>
        simp only [tailDeformMap_mkCyl_zero, ContinuousMap.id_apply]
        exact congrArg (mkCyl f 0 ⟨·, p.2⟩) (max_eq_left (show (0 : I) ≤ p.1 from p.1.property.1))
      | succ m => simp
  map_one_left z := by
    induction z using ind with
    | cyl n p =>
      cases n with
      | zero =>
        simp only [tailDeformMap_mkCyl_zero, ContinuousMap.comp_apply,
          max_eq_right (show p.1 ≤ 1 from p.1.property.2), mkCyl_one, tailRetract_mkCyl_zero,
          incl_apply, tailIncl_mkCyl]
      | succ m => simp

private lemma tailDeform_tailIncl (t : I)
    (w : MappingTelescope (X := fun k => X (k + 1)) (fun k => f (k + 1))) :
    tailDeform f (t, tailIncl f w) = tailIncl f w := by
  induction w using ind with
  | cyl m p =>
    rw [tailIncl_mkCyl]
    exact tailDeformMap_mkCyl_succ t m p

private lemma tailDeform_mem_stage (n : ℕ) (t : I) {z : MappingTelescope f}
    (hz : z ∈ stage f (n + 1)) : tailDeform f (t, z) ∈ stage f (n + 1) := by
  induction z using ind with
  | cyl k p =>
    cases k with
    | zero =>
      change tailDeformMap f t (mkCyl f 0 p) ∈ stage f (n + 1)
      rw [tailDeformMap_mkCyl_zero]
      exact mkCyl_mem_stage_iff.2 (Or.inl (Nat.zero_lt_succ n))
    | succ m =>
      change tailDeformMap f t (mkCyl f (m + 1) p) ∈ stage f (n + 1)
      rwa [tailDeformMap_mkCyl_succ]

private lemma mapsTo_tailIncl_stage (n : ℕ) :
    MapsTo (tailIncl f) (stage (X := fun k => X (k + 1)) (fun k => f (k + 1)) n)
      (stage f (n + 1)) := by
  intro w hw
  induction w using ind with
  | cyl m p =>
    obtain ⟨s, x⟩ := p
    rw [tailIncl_mkCyl, mkCyl_mem_stage_iff]
    exact (mkCyl_mem_stage_iff.1 hw).imp Nat.succ_lt_succ fun h => ⟨congrArg (· + 1) h.1, h.2⟩

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
      exact (mkCyl_mem_stage_iff.1 hz).imp Nat.lt_of_succ_lt_succ fun h => ⟨by omega, h.2⟩

/-- The retraction of `stage f n` onto `X n` obtained by collapsing the cylinders `0, …, n - 1`
forward along the bonding maps `f`. -/
def stageProj {X : ℕ → Type u} [∀ n, TopologicalSpace (X n)]
    (f : ∀ n, C(X n, X (n + 1))) : ∀ n : ℕ, C(stage f n, X n)
  | 0 =>
    ⟨fun z => (inclHomeomorph f 0).symm ⟨z.val, stage_zero (f := f) ▸ z.property⟩,
      (inclHomeomorph f 0).symm.continuous.comp (continuous_subtypeVal.subtype_mk _)⟩
  | n + 1 =>
    (stageProj (X := fun k => X (k + 1)) (fun k => f (k + 1)) n).comp
      ⟨(mapsTo_tailRetract_stage n).restrict _ _ _, (tailRetract f).continuous.restrict _⟩

@[simp]
theorem stageProj_inclStage (n : ℕ) (x : X n) :
    stageProj f n (inclStage f n x) = x := by
  induction n generalizing X with
  | zero =>
    refine (congrArg (inclHomeomorph f 0).symm ?_).trans ((inclHomeomorph f 0).symm_apply_apply x)
    exact Subtype.ext (by simp)
  | succ n ih =>
    refine (congrArg (stageProj (X := fun k => X (k + 1)) (fun k => f (k + 1)) n) ?_).trans
      (ih (X := fun k => X (k + 1)) (f := fun k => f (k + 1)) x)
    exact Subtype.ext (by simp [incl_apply])

/-- On any cylinder `k ≤ n` meeting `stage f n`, `stageProj f n` evaluates to the composite bonding
map `bondOfLE f`. -/
@[simp]
theorem stageProj_mkCyl {k n : ℕ} (h : k ≤ n) (s : I) (x : X k)
    {hz : mkCyl f k (s, x) ∈ stage f n} :
    stageProj f n ⟨mkCyl f k (s, x), hz⟩ = bondOfLE f h x := by
  induction n generalizing X k s with
  | zero =>
    obtain rfl : k = 0 := Nat.eq_zero_of_le_zero h
    rcases mkCyl_mem_stage_iff.1 hz with hk | ⟨-, rfl⟩
    · omega
    · rw [show (⟨mkCyl f 0 (0, x), hz⟩ : stage f 0) = inclStage f 0 x from
        Subtype.ext (by simp [incl_apply]), stageProj_inclStage, bondOfLE_refl,
        ContinuousMap.id_apply]
  | succ n ih =>
    change stageProj (X := fun m => X (m + 1)) (fun m => f (m + 1)) n
      ⟨tailRetract f (mkCyl f k (s, x)), mapsTo_tailRetract_stage n hz⟩ = bondOfLE f h x
    cases k with
    | zero =>
      have h0 : mkCyl (X := fun m => X (m + 1)) (fun m => f (m + 1)) 0 (0, f 0 x) ∈
          stage (X := fun m => X (m + 1)) (fun m => f (m + 1)) n := by
        rw [← incl_apply]
        exact incl_mem_stage_iff.2 (Nat.zero_le n)
      have heq : (⟨tailRetract f (mkCyl f 0 (s, x)), mapsTo_tailRetract_stage n hz⟩ :
          stage (X := fun m => X (m + 1)) (fun m => f (m + 1)) n) =
          ⟨mkCyl (X := fun m => X (m + 1)) (fun m => f (m + 1)) 0 (0, f 0 x), h0⟩ :=
        Subtype.ext (by simp [incl_apply])
      rw [heq, ih (X := fun m => X (m + 1)) (f := fun m => f (m + 1)) (Nat.zero_le n) 0 (f 0 x)]
      have hcomp := bondOfLE_apply_bondOfLE (f := f) (Nat.le_succ 0)
        (Nat.succ_le_succ (Nat.zero_le n)) x
      rwa [bondOfLE_succ] at hcomp
    | succ m =>
      have hmn : m ≤ n := Nat.le_of_succ_le_succ h
      have heq : (⟨tailRetract f (mkCyl f (m + 1) (s, x)), mapsTo_tailRetract_stage n hz⟩ :
          stage (X := fun j => X (j + 1)) (fun j => f (j + 1)) n) =
          ⟨mkCyl (X := fun j => X (j + 1)) (fun j => f (j + 1)) m (s, x),
            by simpa [tailRetract_mkCyl_succ] using mapsTo_tailRetract_stage n hz⟩ :=
        Subtype.ext (by simp)
      rw [heq]
      exact ih (X := fun j => X (j + 1)) (f := fun j => f (j + 1)) hmn s x

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
      exact (inclHomeomorph_apply_coe 0 _).symm.trans
        (congrArg Subtype.val ((inclHomeomorph f 0).apply_symm_apply ⟨z, stage_zero (f := f) ▸ hz⟩))
    rw [hid]
    exact ContinuousMap.HomotopicRel.refl _
  | succ n ih =>
    let i : C(stage (X := fun k => X (k + 1)) (fun k => f (k + 1)) n, stage f (n + 1)) :=
      ⟨(mapsTo_tailIncl_stage n).restrict _ _ _, (tailIncl f).continuous.restrict _⟩
    let r : C(stage f (n + 1), stage (X := fun k => X (k + 1)) (fun k => f (k + 1)) n) :=
      ⟨(mapsTo_tailRetract_stage n).restrict _ _ _, (tailRetract f).continuous.restrict _⟩
    have hri : Function.LeftInverse r i := fun w => Subtype.ext (tailRetract_tailIncl w.val)
    have hH : (ContinuousMap.id (stage f (n + 1))).HomotopicRel (i.comp r) (Set.range i) :=
      ⟨{ toFun q := ⟨tailDeform f (q.1, q.2.val), tailDeform_mem_stage n q.1 q.2.property⟩
         continuous_toFun := ((tailDeform f).continuous.comp
           (continuous_fst.prodMk (continuous_subtypeVal.comp continuous_snd))).subtype_mk _
         map_zero_left z := Subtype.ext ((tailDeform f).apply_zero z.val)
         map_one_left z := Subtype.ext ((tailDeform f).apply_one z.val)
         prop' := by rintro t _ ⟨w, rfl⟩; exact Subtype.ext (tailDeform_tailIncl t w.val) }⟩
    have hij : i.comp (inclStage (X := fun k => X (k + 1)) (fun k => f (k + 1)) n) =
        inclStage f (n + 1) := ContinuousMap.ext fun x => Subtype.ext (tailIncl_incl n x)
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
    tailRetract_tailIncl ⟨(tailDeform f).symm⟩

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
  refine ⟨.of_comp (fromMappingCylinderStage f n).continuous continuous_subtypeVal
    (isClosedEmbedding_fromMappingCylinder n).isEmbedding, ?_⟩
  have hrange : Set.range (fromMappingCylinderStage f n) =
      ((↑) ⁻¹' Set.range (fromMappingCylinder f n) : Set (stage f (n + 1))) :=
    Set.ext fun z => ⟨by rintro ⟨w, rfl⟩; exact mem_range_self w,
      fun ⟨w, hw⟩ => ⟨w, Subtype.ext hw⟩⟩
  rw [hrange]
  exact (isClosedEmbedding_fromMappingCylinder n).isClosed_range.preimage continuous_subtypeVal

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
      change IsClosed (Set.range (Set.inclusion (stage_mono n.le_succ)))
      rw [Set.range_inclusion]
      exact (isClosed_stage n).preimage continuous_subtypeVal⟩
  have hcover : Set.range inr ∪ ⋃ _ : Unit, Set.range inl = Set.univ := by
    ext z
    simp only [mem_union, mem_iUnion, exists_const, mem_univ, iff_true]
    exact ((Set.ext_iff.1 (stage_succ (f := f) n) z.val).1 z.property).imp
      (fun hz => ⟨⟨z.val, hz⟩, rfl⟩) fun ⟨w, hw⟩ => ⟨w, Subtype.ext hw⟩
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
          ⟨huv' ▸ u.property, mem_range_self v⟩
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
      rw [show ((↑) ⁻¹' stage f m : Set (stage f m)) = Set.univ from
        Set.ext fun z => ⟨fun _ => trivial, fun _ => z.property⟩]
      exact isClopen_univ.hasHomotopyExtensionProperty
    | succ k hmk ih =>
      convert ih.image_of_isEmbedding (Topology.IsEmbedding.inclusion (stage_mono k.le_succ))
        (by rw [Set.range_inclusion]; exact hasHomotopyExtensionProperty_stage k) using 1
      ext z
      simp only [mem_preimage, mem_image]
      exact ⟨fun hz => ⟨⟨z.val, stage_mono hmk hz⟩, hz, rfl⟩,
        by rintro ⟨w, hw, rfl⟩; exact hw⟩
  · rw [show ((↑) ⁻¹' stage f m : Set (stage f n)) = Set.univ from
      Set.ext fun z => ⟨fun _ => trivial, fun _ => stage_mono h z.property⟩]
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
      ∀ (t : I) (x : S k), p'.val (t, Set.inclusion (hS_mono k.le_succ) x) = p.val (t, x) := by
    let j : C(I × ↥((↑) ⁻¹' S k : Set (S (k + 1))), I × S k) :=
      ⟨fun q => (q.1, ⟨q.2.val.val, q.2.property⟩), by fun_prop⟩
    obtain ⟨G', hG'0, hG'ext⟩ :=
      (hasHomotopyExtensionProperty_stage (f := f) (n + k)).exists_extension
        (g.restrict (S (k + 1))) (p.val.comp j) fun a => p.property ⟨a.val.val, a.property⟩
    exact ⟨⟨G', hG'0⟩, fun t x => hG'ext t ⟨Set.inclusion (hS_mono k.le_succ) x, x.property⟩⟩
  choose next hnext using step
  let seq : ∀ k, P k := fun k => Nat.rec ⟨H, hgH⟩ next k
  have hseq_compat {i j : ℕ} (hij : i ≤ j) (t : I) (x : S i) :
      (seq j).val (t, Set.inclusion (hS_mono hij) x) = (seq i).val (t, x) := by
    induction j, hij using Nat.le_induction with
    | base => rfl
    | succ k hik ih => exact (hnext k (seq k) t (Set.inclusion (hS_mono hik) x)).trans ih
  have hIS_univ : ⋃ k, (Set.univ : Set I) ×ˢ S k = Set.univ := by
    simp [← prod_iUnion, hS_univ]
  let φ (k : ℕ) : C(↥((Set.univ : Set I) ×ˢ S k), Y) :=
    (seq k).val.comp ⟨fun q => (q.val.1, ⟨q.val.2, q.property.2⟩), by fun_prop⟩
  let G : C(I × MappingTelescope f, Y) :=
    ContinuousMap.liftCoherent (fun k => (Set.univ : Set I) ×ˢ S k) φ
      (fun i j q hi hj =>
        (hseq_compat (le_max_left i j) q.1 ⟨q.2, hi.2⟩).symm.trans
          (hseq_compat (le_max_right i j) q.1 ⟨q.2, hj.2⟩))
      (hS_coh.univ_prod hS_univ) hIS_univ
  have hG (k : ℕ) (t : I) (x : S k) : G (t, x) = (seq k).val (t, x) :=
    ContinuousMap.liftCoherent_coe (S := fun k => (Set.univ : Set I) ×ˢ S k)
      ⟨(t, x.val), mem_univ t, x.property⟩
  refine ⟨G, fun z => ?_, fun t a => hG 0 t a⟩
  obtain ⟨k, hk⟩ := mem_iUnion.1 (hS_univ ▸ mem_univ z)
  exact (hG k 0 ⟨z, hk⟩).trans ((seq k).property ⟨z, hk⟩)

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
