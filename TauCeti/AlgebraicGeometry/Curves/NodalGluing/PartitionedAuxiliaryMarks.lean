/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.NodalGluing.AuxiliaryMarks
public import Mathlib.CategoryTheory.Groupoid.Subgroupoid

/-!
# Marked nodal curves with partitioned auxiliary marks

Let the auxiliary marks of a marked nodal curve (labelled by `R`, see
`TauCeti.AlgebraicGeometry.Curves.NodalGluing.AuxiliaryMarks`) be coloured by a function
`κ : R → Cl`, so that the auxiliary labels are partitioned into the colour classes
`Λ_c = κ ⁻¹' {c}`, empty classes being allowed.  An arrow `(π, f)` with unordered auxiliary marks
*preserves the colours* when `κ (π j) = κ j` for every auxiliary label `j`: its permutation lies
in `∏_c S(Λ_c)`, and it may permute the marks within each colour class but never moves a mark to
another class.  For instance, two distinguished unordered auxiliary sets `R₁` and `R₂` use the
permutations `S(R₁) × S(R₂)` of `R₁ ⊕ R₂`, not all of `S(R₁ ⊕ R₂)`, which could interchange their
roles (`AuxiliaryIso.preservesColors_isLeft_iff`).

The colour-preserving arrows form a wide subgroupoid of the groupoid of curves with unordered
auxiliary marks: it has all the objects but in general not all the arrows between them.  Its
inclusion is faithful on actual arrows, as for every subgroupoid (`Subgroupoid.hom.faithful`).
The automorphisms preserving the colours form a subgroup of the automorphism group, between the
ordered automorphisms and all of it, and it acts on each colour class.

A single colour class recovers the groupoid with unordered auxiliary marks, and singleton colour
classes recover the ordered isomorphisms, those fixing every mark.  Relabelling the colours
bijectively does not change the subgroupoid, and merging colour classes only enlarges it.

## Main definitions

* `NodalGluing.AuxiliaryIso.PreservesColors κ e`: the arrow `e` preserves the colouring `κ`.
* `NodalGluing.AuxiliaryMarkedCurve.partitionedAuxiliaryIsomorphismGroupoid κ`: the wide
  subgroupoid of the colour-preserving arrows (`isWide_partitionedAuxiliaryIsomorphismGroupoid`).
* `NodalGluing.AuxiliaryAut.partitioned I n m κ`: the subgroup of colour-preserving automorphisms,
  with its action `AuxiliaryAut.blockPerm` on the colour classes, whose kernel is the subgroup of
  ordered automorphisms (`AuxiliaryAut.ker_blockPerm`).

## Main results

* `AuxiliaryMarkedCurve.partitionedAuxiliaryIsomorphismGroupoid_eq_top`,
  `mem_partitionedAuxiliaryIsomorphismGroupoid_iff_perm_eq_one`: one colour class gives every
  arrow, and singleton colour classes give the arrows fixing every mark.
* `AuxiliaryMarkedCurve.partitionedAuxiliaryIsomorphismGroupoid_comp_of_injective`,
  `partitionedAuxiliaryIsomorphismGroupoid_le_comp`: relabelling and merging colour classes.
* `AuxiliaryIso.PreservesColors.perm_image_preimage`,
  `AuxiliaryIso.PreservesColors.image_image_point_inr_preimage`: a colour-preserving arrow maps
  each union of colour classes onto itself, and so carries the auxiliary marks of those colours
  onto the auxiliary marks of the same colours.  For an arbitrary arrow, the marks labelled by a
  set `S` go to those labelled by its image under the permutation
  (`AuxiliaryIso.image_image_point_inr`).
* `AuxiliaryIso.preservesColors_isLeft_iff`: the two-colour case `S(R₁) × S(R₂)`.

## References

* Joel W. Robbin and Dietmar A. Salamon, *A construction of the Deligne–Mumford orbifold*,
  J. Eur. Math. Soc. 8 (2006), 611–699, for marked nodal Riemann surfaces and their isomorphisms
  (Definition 3.2).
-/

public noncomputable section

open Set CategoryTheory
open scoped Manifold ContDiff

namespace TauCeti

namespace NodalGluing

universe u v w

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H} {n : ℕ∞ω}
  {ι Flag : Type*} {X : ι → Type*} [∀ i, TopologicalSpace (X i)] [∀ i, ChartedSpace H (X i)]
  {ι' Flag' : Type*} {X' : ι' → Type*} [∀ i, TopologicalSpace (X' i)]
  [∀ i, ChartedSpace H (X' i)]
  {ι'' Flag'' : Type*} {X'' : ι'' → Type*} [∀ i, TopologicalSpace (X'' i)]
  [∀ i, ChartedSpace H (X'' i)]
  {d : FlagPairData ι Flag X} {d' : FlagPairData ι' Flag' X'} {d'' : FlagPairData ι'' Flag'' X''}
  {N R Cl Cl' : Type*}

/-! ### Colour-preserving arrows -/

namespace AuxiliaryIso

variable {m : Marking d (N ⊕ R)} {m' : Marking d' (N ⊕ R)} {m'' : Marking d'' (N ⊕ R)}

/-- **A colour-preserving arrow.**  For a colouring `κ : R → Cl` of the auxiliary labels, the
arrow `e` preserves the colours when its permutation carries each auxiliary label to a label of
the same colour, that is, when it permutes each colour class `κ ⁻¹' {c}`. -/
def PreservesColors (κ : R → Cl) (e : AuxiliaryIso I n m m') : Prop :=
  ∀ j, κ (e.perm j) = κ j

variable {κ : R → Cl}

theorem preservesColors_iff (e : AuxiliaryIso I n m m') :
    e.PreservesColors κ ↔ ∀ j, κ (e.perm j) = κ j :=
  Iff.rfl

/-- An arrow preserves the colours exactly when its permutation is constant on colours. -/
theorem preservesColors_iff_comp_eq (e : AuxiliaryIso I n m m') :
    e.PreservesColors κ ↔ κ ∘ e.perm = κ :=
  funext_iff.symm

variable (I n m κ) in
/-- The identity arrow preserves the colours. -/
@[simp] theorem preservesColors_refl : (AuxiliaryIso.refl I n m).PreservesColors κ :=
  fun _ ↦ by rw [perm_refl, Equiv.refl_apply]

/-- The inverse of a colour-preserving arrow preserves the colours. -/
theorem PreservesColors.symm {e : AuxiliaryIso I n m m'} (h : e.PreservesColors κ) :
    e.symm.PreservesColors κ := fun j ↦ by
  rw [perm_symm, ← h (e.perm.symm j), Equiv.apply_symm_apply]

/-- The inverse of an arrow preserves the colours exactly when the arrow does. -/
@[simp] theorem preservesColors_symm_iff {e : AuxiliaryIso I n m m'} :
    e.symm.PreservesColors κ ↔ e.PreservesColors κ :=
  ⟨fun h ↦ e.symm_symm ▸ h.symm, PreservesColors.symm⟩

/-- A composite of colour-preserving arrows preserves the colours. -/
theorem PreservesColors.trans {e : AuxiliaryIso I n m m'} {e' : AuxiliaryIso I n m' m''}
    (h : e.PreservesColors κ) (h' : e'.PreservesColors κ) : (e.trans e').PreservesColors κ :=
  fun j ↦ by rw [perm_trans, Equiv.trans_apply, h', h]

/-- **Merging colour classes.**  An arrow preserving a colouring `κ` preserves every coarser
colouring `σ ∘ κ`. -/
theorem PreservesColors.comp {e : AuxiliaryIso I n m m'} (h : e.PreservesColors κ)
    (σ : Cl → Cl') : e.PreservesColors (σ ∘ κ) :=
  fun j ↦ congrArg σ (h j)

/-- **Relabelling the colours.**  For an injective relabelling `σ` of the colours, an arrow
preserves `σ ∘ κ` exactly when it preserves `κ`. -/
theorem preservesColors_comp_iff {σ : Cl → Cl'} (hσ : Function.Injective σ)
    (e : AuxiliaryIso I n m m') : e.PreservesColors (σ ∘ κ) ↔ e.PreservesColors κ :=
  ⟨fun h j ↦ hσ (h j), fun h ↦ h.comp σ⟩

/-- **One colour class.**  If there is at most one colour, every arrow preserves the colours. -/
theorem preservesColors_of_subsingleton [Subsingleton Cl] (e : AuxiliaryIso I n m m') :
    e.PreservesColors κ :=
  fun _ ↦ Subsingleton.elim _ _

/-- **Singleton colour classes.**  For an injective colouring, an arrow preserves the colours
exactly when its permutation of the auxiliary labels is trivial. -/
theorem preservesColors_iff_perm_eq_one (hκ : Function.Injective κ)
    (e : AuxiliaryIso I n m m') : e.PreservesColors κ ↔ e.perm = 1 :=
  ⟨fun h ↦ Equiv.ext fun j ↦ hκ (h j), fun h j ↦ by rw [h, Equiv.Perm.one_apply]⟩

/-- A colour-preserving arrow maps each union of colour classes onto itself. -/
theorem PreservesColors.perm_image_preimage {e : AuxiliaryIso I n m m'}
    (h : e.PreservesColors κ) (T : Set Cl) : e.perm '' (κ ⁻¹' T) = κ ⁻¹' T := by
  ext j
  refine ⟨?_, fun hj ↦ ⟨e.perm.symm j, ?_, e.perm.apply_symm_apply j⟩⟩
  · rintro ⟨k, hk, rfl⟩
    rwa [mem_preimage, h k]
  · rwa [mem_preimage, ← h (e.perm.symm j), Equiv.apply_symm_apply]

/-- **Colour classes are transported.**  A colour-preserving arrow carries the auxiliary marks of
any union of colour classes exactly onto the auxiliary marks of the same colours. -/
theorem PreservesColors.image_image_point_inr_preimage {e : AuxiliaryIso I n m m'}
    (h : e.PreservesColors κ) (T : Set Cl) :
    e '' ((fun j ↦ m.point (.inr j)) '' (κ ⁻¹' T)) =
      (fun j ↦ m'.point (.inr j)) '' (κ ⁻¹' T) := by
  rw [image_image_point_inr, h.perm_image_preimage]

/-- **Two colour classes.**  For auxiliary labels `R₁ ⊕ R₂` coloured by their summand, an arrow
preserves the colours exactly when its permutation lies in `S(R₁) × S(R₂)`, embedded in
`S(R₁ ⊕ R₂)` by `Equiv.Perm.sumCongrHom`. -/
theorem preservesColors_isLeft_iff {R₁ R₂ : Type*} {m : Marking d (N ⊕ (R₁ ⊕ R₂))}
    {m' : Marking d' (N ⊕ (R₁ ⊕ R₂))} (e : AuxiliaryIso I n m m') :
    e.PreservesColors Sum.isLeft ↔ e.perm ∈ (Equiv.Perm.sumCongrHom R₁ R₂).range := by
  constructor
  · intro h
    have hl (x : R₁ ⊕ R₂) : (e.perm x).isLeft ↔ x.isLeft := by rw [h x]
    have hr (x : R₁ ⊕ R₂) : (e.perm x).isRight ↔ x.isRight := by
      rw [← Sum.not_isLeft, ← Sum.not_isLeft, h x]
    refine ⟨(Equiv.sumIsLeft.permCongr (e.perm.subtypePerm hl),
      Equiv.sumIsRight.permCongr (e.perm.subtypePerm hr)), Equiv.ext ?_⟩
    rintro (a | b)
    · obtain ⟨a', ha'⟩ := Sum.isLeft_iff.mp ((hl (.inl a)).mpr rfl)
      simp [ha']
    · obtain ⟨b', hb'⟩ := Sum.isRight_iff.mp ((hr (.inr b)).mpr rfl)
      simp [hb']
  · rintro ⟨⟨σ₁, σ₂⟩, hσ⟩ (a | b) <;> simp [← hσ]

end AuxiliaryIso

/-! ### The partitioned groupoid -/

namespace AuxiliaryMarkedCurve

variable (I n N) in
/-- **The groupoid of curves with partitioned auxiliary marks.**  For a colouring `κ : R → Cl` of
the auxiliary labels, this is the subgroupoid of the groupoid of curves with unordered auxiliary
marks consisting of the colour-preserving arrows `(π, f)`, those whose permutation `π` lies in
`∏_c S(κ ⁻¹' {c})`.  It is wide (`isWide_partitionedAuxiliaryIsomorphismGroupoid`): it has the
same objects, but in general fewer arrows between them. -/
def partitionedAuxiliaryIsomorphismGroupoid (κ : R → Cl) :
    Subgroupoid (AuxiliaryMarkedCurve.{u, v, w} I n N R) where
  arrows _ _ := {e | AuxiliaryIso.PreservesColors κ e}
  inv h := AuxiliaryIso.PreservesColors.symm h
  mul h _ h' := AuxiliaryIso.PreservesColors.trans h h'

variable {κ : R → Cl} {C C' : AuxiliaryMarkedCurve.{u, v, w} I n N R}

/-- An arrow lies in the partitioned groupoid exactly when it preserves the colours. -/
@[simp] theorem mem_partitionedAuxiliaryIsomorphismGroupoid_iff (e : C ⟶ C') :
    e ∈ (partitionedAuxiliaryIsomorphismGroupoid I n N κ).arrows C C' ↔
      AuxiliaryIso.PreservesColors κ (m := C.marking) (m' := C'.marking) e :=
  Iff.rfl

variable (κ) in
/-- The partitioned groupoid is a wide subgroupoid: it contains the identity of every curve. -/
theorem isWide_partitionedAuxiliaryIsomorphismGroupoid :
    (partitionedAuxiliaryIsomorphismGroupoid.{u, v, w} I n N κ).IsWide :=
  ⟨fun C ↦ AuxiliaryIso.preservesColors_refl I n C.marking κ⟩

variable (κ) in
/-- **Merging colour classes** enlarges the partitioned groupoid. -/
theorem partitionedAuxiliaryIsomorphismGroupoid_le_comp (σ : Cl → Cl') :
    partitionedAuxiliaryIsomorphismGroupoid.{u, v, w} I n N κ ≤
      partitionedAuxiliaryIsomorphismGroupoid I n N (σ ∘ κ) :=
  (Subgroupoid.le_iff _ _).mpr fun {_ _} _ h ↦ AuxiliaryIso.PreservesColors.comp h σ

/-- **Relabelling the colours** injectively does not change the partitioned groupoid. -/
theorem partitionedAuxiliaryIsomorphismGroupoid_comp_of_injective {σ : Cl → Cl'}
    (hσ : Function.Injective σ) :
    partitionedAuxiliaryIsomorphismGroupoid.{u, v, w} I n N (σ ∘ κ) =
      partitionedAuxiliaryIsomorphismGroupoid I n N κ :=
  le_antisymm ((Subgroupoid.le_iff _ _).mpr fun {_ _} e ↦
    (AuxiliaryIso.preservesColors_comp_iff hσ e).mp)
    (partitionedAuxiliaryIsomorphismGroupoid_le_comp κ σ)

/-- **One colour class** recovers the groupoid of curves with unordered auxiliary marks: every
arrow preserves the colours. -/
theorem partitionedAuxiliaryIsomorphismGroupoid_eq_top [Subsingleton Cl] :
    partitionedAuxiliaryIsomorphismGroupoid.{u, v, w} I n N κ = ⊤ :=
  eq_top_iff.mpr <| (Subgroupoid.le_iff _ _).mpr fun {_ _} e _ ↦
    AuxiliaryIso.preservesColors_of_subsingleton e

/-- **Singleton colour classes** recover the ordered isomorphisms: for an injective colouring, the
arrows of the partitioned groupoid are those with trivial permutation, which fix every
distinguished and every auxiliary label. -/
theorem mem_partitionedAuxiliaryIsomorphismGroupoid_iff_perm_eq_one (hκ : Function.Injective κ)
    (e : C ⟶ C') :
    e ∈ (partitionedAuxiliaryIsomorphismGroupoid I n N κ).arrows C C' ↔
      AuxiliaryIso.perm (m := C.marking) (m' := C'.marking) e = 1 :=
  AuxiliaryIso.preservesColors_iff_perm_eq_one hκ e

end AuxiliaryMarkedCurve

/-! ### Colour-preserving automorphisms -/

namespace AuxiliaryAut

variable {m : Marking d (N ⊕ R)}

variable (I n m) in
/-- **The colour-preserving automorphisms** of a curve with auxiliary marks coloured by
`κ : R → Cl`: the automorphisms whose permutation of the auxiliary labels preserves every colour
class. -/
def partitioned (κ : R → Cl) : Subgroup (AuxiliaryAut I n m) where
  carrier := {e | e.PreservesColors κ}
  one_mem' := AuxiliaryIso.preservesColors_refl I n m κ
  mul_mem' h h' := AuxiliaryIso.PreservesColors.trans h' h
  inv_mem' h := AuxiliaryIso.PreservesColors.symm h

variable {κ : R → Cl}

/-- An automorphism is colour-preserving exactly when its permutation preserves the colours. -/
@[simp] theorem mem_partitioned_iff (e : AuxiliaryAut I n m) :
    e ∈ partitioned I n m κ ↔ e.PreservesColors κ :=
  Iff.rfl

variable (κ) in
/-- Every ordered automorphism preserves the colours. -/
theorem ordered_le_partitioned : ordered I n m ≤ partitioned I n m κ := fun e he j ↦ by
  rw [(mem_ordered_iff e).mp he, Equiv.Perm.one_apply]

variable (κ) in
/-- **Merging colour classes** enlarges the colour-preserving automorphisms. -/
theorem partitioned_le_comp (σ : Cl → Cl') : partitioned I n m κ ≤ partitioned I n m (σ ∘ κ) :=
  fun _ h ↦ AuxiliaryIso.PreservesColors.comp h σ

/-- **Relabelling the colours** injectively does not change the colour-preserving
automorphisms. -/
theorem partitioned_comp_of_injective {σ : Cl → Cl'} (hσ : Function.Injective σ) :
    partitioned I n m (σ ∘ κ) = partitioned I n m κ :=
  Subgroup.ext fun e ↦ AuxiliaryIso.preservesColors_comp_iff hσ e

/-- **One colour class**: every automorphism preserves the colours. -/
theorem partitioned_eq_top [Subsingleton Cl] : partitioned I n m κ = ⊤ :=
  eq_top_iff.mpr fun e _ ↦ AuxiliaryIso.preservesColors_of_subsingleton e

/-- **Singleton colour classes**: for an injective colouring, the colour-preserving automorphisms
are the ordered automorphisms. -/
theorem partitioned_eq_ordered (hκ : Function.Injective κ) :
    partitioned I n m κ = ordered I n m :=
  Subgroup.ext fun e ↦ (AuxiliaryIso.preservesColors_iff_perm_eq_one hκ e).trans
    (mem_ordered_iff e).symm

/-- **The action on the colour classes.**  A colour-preserving automorphism permutes each colour
class `κ ⁻¹' {c}`; this is its image in `∏_c S(κ ⁻¹' {c})`. -/
def blockPerm : partitioned I n m κ →* ∀ c, Equiv.Perm {j // κ j = c} where
  toFun e c := e.1.perm.subtypePerm fun j ↦ by rw [e.2 j]
  map_one' := funext fun _ ↦ Equiv.ext fun _ ↦ Subtype.ext <| by
    simp [OneMemClass.coe_one, one_def]
  map_mul' _ _ := funext fun _ ↦ Equiv.ext fun _ ↦ Subtype.ext <| by
    simp [Subgroup.coe_mul, mul_def, -Equiv.Perm.subtypePerm_mul]

/-- The action of a colour-preserving automorphism on a colour class is its permutation. -/
@[simp] theorem coe_blockPerm_apply (e : partitioned I n m κ) (c : Cl) (j : {j // κ j = c}) :
    (blockPerm e c j : R) = e.1.perm j :=
  (rfl)

/-- A colour-preserving automorphism acts trivially on every colour class exactly when it is
ordered: the kernel of the action on the colour classes is the subgroup of ordered
automorphisms. -/
theorem ker_blockPerm :
    (blockPerm : partitioned I n m κ →* _).ker =
      (ordered I n m).subgroupOf (partitioned I n m κ) := by
  ext e
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, mem_ordered_iff, funext_iff]
  refine ⟨fun h ↦ Equiv.ext fun j ↦ ?_, fun h c ↦ Equiv.ext fun j ↦ ?_⟩
  · simpa using congrArg Subtype.val (Equiv.ext_iff.mp (h (κ j)) ⟨j, rfl⟩)
  · exact Subtype.ext (by simp [h])

end AuxiliaryAut

end NodalGluing

end TauCeti
