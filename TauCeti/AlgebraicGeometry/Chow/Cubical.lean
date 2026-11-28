/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AffineSpace.Cubical
public import TauCeti.AlgebraicGeometry.Chow.OpenRestriction
public import TauCeti.AlgebraicGeometry.Chow.ClosedImmersion
public import TauCeti.AlgebraicGeometry.Chow.TopDimension
import TauCeti.AlgebraicGeometry.Morphisms.LocallyQuasiFinite
import TauCeti.AlgebraicGeometry.Morphisms.Smooth.RelativeDimension

/-!
# Face-admissible cycles on algebraic cubes

The dimension-graded raw group of cubical cycles in degree `n` is the subgroup of
`AlgebraicCycle` on the relative affine `n`-space over `X` generated, for quasi-compact `X`,
by the integral closed subsets of dimension `j + n` that meet the faces properly.
On an equidimensional variety of dimension `d`, codimension `p` corresponds to `j = d - p`.

We test the dimension of each integral support on every iterated face. In a face with `m`
coordinates left, every point of the intersection must have dimension at most `j + m`.
In particular, a negative bound requires the intersection to be empty. The coordinates
of the two endpoints in the affine model are zero and one.

In degree zero the group identifies with ordinary cycles on the base. Open restriction
of cycles preserves this grading over a field and commutes with composition.

The construction uses the dimension grading of `Chow.cyclesOfDimension` and the face
inclusions `AlgebraicGeometry.AffineSpace.cubeFace`. The incidence convention is that of
Burgos Gil and Feliu, [*Higher arithmetic Chow groups*](https://arxiv.org/abs/0907.5169), §2.1.
-/

public section

noncomputable section

open AlgebraicGeometry CategoryTheory Order
open AlgebraicGeometry.AffineSpace

universe u

namespace TauCeti.AlgebraicGeometry.Chow

variable {X U V : Scheme.{u}} {j : ℤ} {n : ℕ}

/-- A support is admissible in dimension grading `j` if it has dimension at most `j + n`
on the whole cube and satisfies the corresponding bound on every iterated face. For a
closed subset its dimension bound can be tested on the heights of its points. -/
def IsAdmissibleCubeSupport (X : Scheme.{u}) (j : ℤ) :
    (n : ℕ) → Set 𝔸(ULift.{u} (Fin n); X) → Prop
  | 0, Z => ∀ y ∈ Z, ∃ b : ℕ, height y ≤ b ∧ (b : ℤ) ≤ j
  | n + 1, Z =>
    (∀ y ∈ Z, ∃ b : ℕ, height y ≤ b ∧ (b : ℤ) ≤ j + (n + 1 : ℕ)) ∧
      ∀ (i : Fin (n + 1)) (ε : Bool),
        IsAdmissibleCubeSupport X j n (cubeFace X i (if ε then 1 else 0) ⁻¹' Z)

/-- At degree zero only the dimension bound remains. -/
lemma isAdmissibleCubeSupport_zero_iff {Z : Set 𝔸(ULift.{u} (Fin 0); X)} :
    IsAdmissibleCubeSupport X j 0 Z ↔ ∀ y ∈ Z, ∃ b : ℕ, height y ≤ b ∧ (b : ℤ) ≤ j :=
  Iff.rfl

/-- Admissibility is tested on the ambient cube and recursively on both faces in each
coordinate. -/
lemma isAdmissibleCubeSupport_succ_iff {Z : Set 𝔸(ULift.{u} (Fin (n + 1)); X)} :
    IsAdmissibleCubeSupport X j (n + 1) Z ↔
      (∀ y ∈ Z, ∃ b : ℕ, height y ≤ b ∧ (b : ℤ) ≤ j + (n + 1 : ℕ)) ∧
        ∀ (i : Fin (n + 1)) (ε : Bool),
          IsAdmissibleCubeSupport X j n (cubeFace X i (if ε then 1 else 0) ⁻¹' Z) :=
  Iff.rfl

/-- A subset of an admissible support satisfies the same incidence bounds. -/
lemma IsAdmissibleCubeSupport.mono {Z W : Set 𝔸(ULift.{u} (Fin n); X)}
    (hW : IsAdmissibleCubeSupport X j n W) (h : Z ⊆ W) : IsAdmissibleCubeSupport X j n Z := by
  induction n with
  | zero => exact fun y hy ↦ hW y (h hy)
  | succ n ih =>
    exact ⟨fun y hy ↦ hW.1 y (h hy), fun i ε ↦ ih (hW.2 i ε) (Set.preimage_mono h)⟩

/-- The empty subset is an admissible support in every dimension grading. -/
@[simp]
lemma isAdmissibleCubeSupport_empty (X : Scheme.{u}) (j : ℤ) (n : ℕ) :
    IsAdmissibleCubeSupport X j n ∅ := by
  induction n with
  | zero => simp [isAdmissibleCubeSupport_zero_iff]
  | succ n ih => simp [isAdmissibleCubeSupport_succ_iff, ih]

/-- A union is admissible exactly when each of its two supports is admissible. -/
@[simp]
lemma isAdmissibleCubeSupport_union {Z W : Set 𝔸(ULift.{u} (Fin n); X)} :
    IsAdmissibleCubeSupport X j n (Z ∪ W) ↔
      IsAdmissibleCubeSupport X j n Z ∧ IsAdmissibleCubeSupport X j n W := by
  refine ⟨fun h ↦ ⟨h.mono Set.subset_union_left, h.mono Set.subset_union_right⟩, ?_⟩
  rintro ⟨hZ, hW⟩
  induction n with
  | zero => exact fun y hy ↦ hy.elim (hZ y) (hW y)
  | succ n ih =>
    exact ⟨fun y hy ↦ hy.elim (hZ.1 y) (hW.1 y), fun i ε ↦ ih (hZ.2 i ε) (hW.2 i ε)⟩

/-- The dimension bound on the ambient cube, including cube degree zero. -/
lemma IsAdmissibleCubeSupport.exists_height_le {Z : Set 𝔸(ULift.{u} (Fin n); X)}
    (hZ : IsAdmissibleCubeSupport X j n Z) {y} (hy : y ∈ Z) :
    ∃ b : ℕ, height y ≤ b ∧ (b : ℤ) ≤ j + n := by
  cases n with
  | zero => simpa using hZ y hy
  | succ n => exact hZ.1 y hy

/-- A negative dimension bound on a face forces its entire support to be empty. -/
lemma isAdmissibleCubeSupport_iff_of_neg {Z : Set 𝔸(ULift.{u} (Fin n); X)} (h : j + n < 0) :
    IsAdmissibleCubeSupport X j n Z ↔ Z = ∅ := by
  refine ⟨fun hZ ↦ Set.eq_empty_iff_forall_notMem.mpr fun y hy ↦ ?_, ?_⟩
  · obtain ⟨b, _, hb⟩ := hZ.exists_height_le hy
    omega
  · rintro rfl
    exact isAdmissibleCubeSupport_empty _ _ _

/-- If the base has dimension at most `d`, the whole cube is admissible in grading `d` since
the dimension of every face is bounded by `d` plus its number of free coordinates. -/
lemma isAdmissibleCubeSupport_univ_of_dim_le [IsLocallyNoetherian X] {d : ℕ}
    (hX : topologicalKrullDim X ≤ d) (n : ℕ) :
    IsAdmissibleCubeSupport X d n Set.univ := by
  have bound (m : ℕ) (y : 𝔸(ULift.{u} (Fin m); X)) : height y ≤ d + m := by
    let f := 𝔸(ULift.{u} (Fin m); X) ↘ X
    have : IsLocallyNoetherian 𝔸(ULift.{u} (Fin m); X) := LocallyOfFiniteType.isLocallyNoetherian f
    exact_mod_cast (height_le_topologicalKrullDim y).trans
      ((topologicalKrullDim_le_add_of_relativeDimensionLE (d := m) f).trans (add_le_add hX le_rfl))
  induction n with
  | zero =>
    exact fun y _ ↦ ⟨d, by simpa using bound 0 y, le_rfl⟩
  | succ n ih =>
    exact ⟨fun y _ ↦ ⟨d + (n + 1), by exact_mod_cast bound (n + 1) y, by omega⟩,
      fun _ _ ↦ ih.mono (Set.subset_univ _)⟩

/-- Generic points indexing the integral generators of the raw cubical cycle group. Their
closures have dimension exactly `j + n` and meet all faces in the prescribed dimension. -/
def admissibleCubePoints (X : Scheme.{u}) (j : ℤ) (n : ℕ) : Set 𝔸(ULift.{u} (Fin n); X) :=
  pointsOfDimension _ (j + n) ∩ {x | IsAdmissibleCubeSupport X j n (closure {x})}

/-- Membership requires the prescribed ambient dimension and admissibility of the closure. -/
lemma mem_admissibleCubePoints_iff {x : 𝔸(ULift.{u} (Fin n); X)} :
    x ∈ admissibleCubePoints X j n ↔
      x ∈ pointsOfDimension _ (j + n) ∧ IsAdmissibleCubeSupport X j n (closure {x}) :=
  Iff.rfl

/-- A closed point, graded as a zero-dimensional cycle on a positive-dimensional cube,
is admissible exactly when it lies off both faces in every coordinate. -/
lemma mem_admissibleCubePoints_iff_of_isClosed {x : 𝔸(ULift.{u} (Fin (n + 1)); X)}
    (hx : IsClosed ({x} : Set _)) (hj : j + (n + 1 : ℕ) = 0) :
    x ∈ admissibleCubePoints X j (n + 1) ↔
      ∀ (i : Fin (n + 1)) (ε : Bool), x ∉ Set.range (cubeFace X i (if ε then 1 else 0)) := by
  have hd : x ∈ pointsOfDimension _ (j + (n + 1 : ℕ)) :=
    mem_pointsOfDimension.mpr ⟨0, by simpa using Scheme.height_of_isClosed hx, by omega⟩
  have hface : j + n < 0 := by omega
  simp only [Nat.cast_add, Nat.cast_one] at hj
  rw [mem_admissibleCubePoints_iff, and_iff_right hd, hx.closure_eq,
    isAdmissibleCubeSupport_succ_iff]
  simp [hj, height_eq_zero.mp (Scheme.height_of_isClosed hx),
    isAdmissibleCubeSupport_iff_of_neg hface, Set.preimage_singleton_eq_empty]

/-- The raw dimension-`j` cubical cycles in degree `n`, as a subgroup of native integral
algebraic cycles. Their coefficients may be nonzero only at admissible generic points. -/
def cubicalCycles (X : Scheme.{u}) (j : ℤ) (n : ℕ) :
    AddSubgroup (AlgebraicCycle 𝔸(ULift.{u} (Fin n); X) ℤ) :=
  Function.locallyFinsuppWithin.supported ℤ Set.univ (admissibleCubePoints X j n)

@[simp]
lemma mem_cubicalCycles_iff {α : AlgebraicCycle 𝔸(ULift.{u} (Fin n); X) ℤ} :
    α ∈ cubicalCycles X j n ↔ α.support ⊆ admissibleCubePoints X j n :=
  Iff.rfl

/-- A raw cubical cycle is an ordinary cycle of dimension `j + n` on the cube. -/
lemma cubicalCycles_le_cyclesOfDimension :
    cubicalCycles X j n ≤ cyclesOfDimension _ (j + n) :=
  fun _ h ↦ mem_cyclesOfDimension_iff.mpr fun _ hx ↦
    (mem_admissibleCubePoints_iff.mp (mem_cubicalCycles_iff.mp h hx)).1

/-- The cycle with a single coefficient is admissible exactly when its coefficient vanishes
or its generic point is admissible. -/
lemma single_mem_cubicalCycles_iff [DecidableEq 𝔸(ULift.{u} (Fin n); X)]
    {x : 𝔸(ULift.{u} (Fin n); X)} {r : ℤ} :
    Function.locallyFinsuppWithin.single x r ∈ cubicalCycles X j n ↔
      r = 0 ∨ x ∈ admissibleCubePoints X j n := by
  by_cases hr : r = 0
  · simp [hr]
  · simp [mem_cubicalCycles_iff, Function.locallyFinsuppWithin.support,
      Pi.support_single_of_ne hr, hr]

/-- Two cubical cycles agree if their coefficients agree at the admissible generic points. -/
@[ext]
lemma cubicalCycles_ext {α β : cubicalCycles X j n}
    (h : ∀ x : admissibleCubePoints X j n, α.val x.val = β.val x.val) : α = β := by
  refine Subtype.ext (Function.locallyFinsuppWithin.ext fun x ↦ ?_)
  by_cases hx : x ∈ admissibleCubePoints X j n
  · exact h ⟨x, hx⟩
  · have hz (γ : cubicalCycles X j n) : γ.val x = 0 :=
      Function.notMem_support.mp fun hy ↦ hx (mem_cubicalCycles_iff.mp γ.property hy)
    exact (hz α).trans (hz β).symm

/-- Over a quasi-compact base the raw cubical cycles are freely generated by the admissible
integral supports. The coordinates of the equivalence are the native cycle coefficients. -/
def cubicalCyclesEquivFinsupp (X : Scheme.{u}) [CompactSpace X] (j : ℤ) (n : ℕ) :
    cubicalCycles X j n ≃ₗ[ℤ] (admissibleCubePoints X j n →₀ ℤ) := by
  let : CompactSpace 𝔸(ULift.{u} (Fin n); X) :=
    QuasiCompact.compactSpace_of_compactSpace (𝔸(ULift.{u} (Fin n); X) ↘ X)
  let e := cyclesOfDimensionEquivFinsupp 𝔸(ULift.{u} (Fin n); X) (j + n)
  let ι : admissibleCubePoints X j n ↪ pointsOfDimension 𝔸(ULift.{u} (Fin n); X) (j + n) :=
    ⟨Set.inclusion (fun _ hx ↦ (mem_admissibleCubePoints_iff.mp hx).1), Set.inclusion_injective _⟩
  -- Restrict the ordinary cycle coordinates to the admissible generic points.
  let coeff := (Finsupp.comapDomain.addMonoidHom (M := ℤ) ι.injective).comp
    (e.toAddMonoidHom.comp (AddSubgroup.inclusion cubicalCycles_le_cyclesOfDimension))
  have coeff_apply (α : cubicalCycles X j n) (x : admissibleCubePoints X j n) :
      coeff α x = α.val x.val := by
    exact cyclesOfDimensionEquivFinsupp_apply _ _ _ (ι x)
  refine (AddEquiv.ofBijective coeff ⟨?_, ?_⟩).toIntLinearEquiv
  · exact fun α β h ↦ cubicalCycles_ext fun x ↦
      (coeff_apply α x).symm.trans ((DFunLike.congr_fun h x).trans (coeff_apply β x))
  · intro v
    -- Extend by zero in the ordinary coordinates, then read off the support.
    let γ := e.symm (v.embDomain ι)
    have hγ : (γ : AlgebraicCycle _ ℤ) ∈ cubicalCycles X j n := by
      refine mem_cubicalCycles_iff.mpr fun x hx ↦ ?_
      let y : pointsOfDimension _ (j + n) := ⟨x, mem_cyclesOfDimension_iff.mp γ.property hx⟩
      have hy : v.embDomain ι y ≠ 0 := by
        rwa [← cyclesOfDimensionEquivFinsupp_symm_apply]
      obtain ⟨z, hz⟩ := (Finsupp.mem_range_embDomain_iff ι _).mp ⟨v, rfl⟩
        (Finsupp.mem_support_iff.mpr hy)
      have he : z.val = x := congrArg Subtype.val hz
      exact he ▸ z.property
    refine ⟨⟨γ.val, hγ⟩, Finsupp.ext fun x ↦ ?_⟩
    rw [coeff_apply]
    exact (cyclesOfDimensionEquivFinsupp_symm_apply _ _ _ (ι x)).trans
      (Finsupp.embDomain_apply_self ι v x)

/-- The coordinates of a raw cubical cycle in the free group of admissible generators. -/
@[simp]
lemma cubicalCyclesEquivFinsupp_apply [CompactSpace X] (α : cubicalCycles X j n)
    (x : admissibleCubePoints X j n) :
    cubicalCyclesEquivFinsupp X j n α x = α.val x.val := by
  let : CompactSpace 𝔸(ULift.{u} (Fin n); X) :=
    QuasiCompact.compactSpace_of_compactSpace (𝔸(ULift.{u} (Fin n); X) ↘ X)
  exact cyclesOfDimensionEquivFinsupp_apply _ _ _ _

/-- Reconstructing a raw cycle from its integer coefficients recovers each prescribed value. -/
@[simp]
lemma cubicalCyclesEquivFinsupp_symm_apply [CompactSpace X] (v : admissibleCubePoints X j n →₀ ℤ)
    (x : admissibleCubePoints X j n) :
    ((cubicalCyclesEquivFinsupp X j n).symm v).val x.val = v x := by
  rw [← cubicalCyclesEquivFinsupp_apply, LinearEquiv.apply_symm_apply]

/-- In degree zero there is no proper-face condition on a generator. -/
@[simp]
lemma admissibleCubePoints_zero (X : Scheme.{u}) (j : ℤ) :
    admissibleCubePoints X j 0 = pointsOfDimension _ j := by
  ext x
  rw [mem_admissibleCubePoints_iff, Nat.cast_zero, add_zero]
  refine and_iff_left_of_imp fun hx y hy ↦ ?_
  obtain ⟨b, hb, rfl⟩ := mem_pointsOfDimension.mp hx
  exact ⟨b, (height_mono (Scheme.le_iff_specializes.mpr (specializes_iff_mem_closure.mpr hy))).trans
    hb.le, le_rfl⟩

/-- The degree-zero subgroup is the ordinary cycle subgroup on the zero-dimensional cube. -/
@[simp]
lemma cubicalCycles_zero (X : Scheme.{u}) (j : ℤ) :
    cubicalCycles X j 0 = cyclesOfDimension _ j := by
  ext
  simp

/-- If the required ambient dimension is negative there are no generators. -/
lemma cubicalCycles_eq_bot_of_neg (h : j + n < 0) : cubicalCycles X j n = ⊥ := by
  exact le_bot_iff.mp ((cubicalCycles_le_cyclesOfDimension (X := X)).trans_eq
    (cyclesOfDimension_eq_bot_of_neg _ h))

/-- In top dimension every ordinary cycle on the cube meets its faces properly. -/
lemma cubicalCycles_eq_cyclesOfDimension_of_dim_le [IsLocallyNoetherian X] {d : ℕ}
    (hX : topologicalKrullDim X ≤ d) (n : ℕ) :
    cubicalCycles X d n = cyclesOfDimension _ ((d : ℤ) + n) := by
  refine le_antisymm cubicalCycles_le_cyclesOfDimension fun α hα ↦ mem_cubicalCycles_iff.mpr ?_
  exact fun x hx ↦ mem_admissibleCubePoints_iff.mpr ⟨mem_cyclesOfDimension_iff.mp hα hx,
    (isAdmissibleCubeSupport_univ_of_dim_le hX n).mono (Set.subset_univ _)⟩

/-- Negative codimension gives the zero group in every cube degree. A dimension grading
strictly above the dimension of the base has no generators. -/
lemma cubicalCycles_eq_bot_of_dim_lt [IsLocallyNoetherian X] {d : ℕ}
    (hX : topologicalKrullDim X ≤ d) (hj : (d : ℤ) < j) (n : ℕ) :
    cubicalCycles X j n = ⊥ := by
  refine le_bot_iff.mp fun α hα ↦ AddSubgroup.mem_bot.mpr ?_
  ext x
  apply Function.notMem_support.mp
  intro hx
  obtain ⟨b, hb, hbj⟩ := mem_pointsOfDimension.mp
    (mem_admissibleCubePoints_iff.mp (mem_cubicalCycles_iff.mp hα hx)).1
  obtain ⟨c, hc, hcd⟩ := (isAdmissibleCubeSupport_univ_of_dim_le hX n).exists_height_le
    (Set.mem_univ x)
  rw [hb] at hc
  norm_cast at hc
  omega

/-- In cube degree zero the structure isomorphism identifies the raw cubical cycles with
ordinary cycles on the base, in the same dimension grading. -/
def cubicalCyclesZeroEquiv (X : Scheme.{u}) (j : ℤ) :
    cubicalCycles X j 0 ≃+ cyclesOfDimension X j :=
  (AddEquiv.addSubgroupCongr (cubicalCycles_zero X j)).trans <|
    AddEquiv.ofBijective (cyclesPushforward (𝔸(ULift.{u} (Fin 0); X) ↘ X))
      ⟨cyclesPushforward_injective, fun α ↦ mem_range_cyclesPushforward_iff.mpr (by
        rw [(𝔸(ULift.{u} (Fin 0); X) ↘ X).surjective.range_eq]
        exact Set.subset_univ _)⟩

/-- The degree-zero identification transports each coefficient to its image on the base. -/
@[simp]
lemma cubicalCyclesZeroEquiv_apply (α : cubicalCycles X j 0) (y : 𝔸(ULift.{u} (Fin 0); X)) :
    (cubicalCyclesZeroEquiv X j α : AlgebraicCycle X ℤ) ((𝔸(ULift.{u} (Fin 0); X) ↘ X) y) =
      (α : AlgebraicCycle _ ℤ) y :=
  cyclesPushforward_apply _ _

/-- Inverse images under locally quasi-finite changes of base preserve the dimension bounds
on the whole cube and on each iterated face. -/
lemma IsAdmissibleCubeSupport.preimage {Z : Set 𝔸(ULift.{u} (Fin n); X)}
    (hZ : IsAdmissibleCubeSupport X j n Z) (f : U ⟶ X) [LocallyQuasiFinite f] :
    IsAdmissibleCubeSupport U j n (AffineSpace.map _ f ⁻¹' Z) := by
  have hdim (m : ℕ) (y : 𝔸(ULift.{u} (Fin m); U)) :
      height y ≤ height (AffineSpace.map _ f y) := by
    let : LocallyQuasiFinite (AffineSpace.map (ULift.{u} (Fin m)) f) :=
      MorphismProperty.of_isPullback (isPullback_map f).flip inferInstance
    exact height_le_height_apply_of_strictMono _ (Scheme.Hom.strictMono _) _
  induction n with
  | zero =>
    intro y hy
    obtain ⟨b, hb, hj⟩ := hZ _ hy
    exact ⟨b, (hdim 0 y).trans hb, hj⟩
  | succ n ih =>
    refine ⟨fun y hy ↦ ?_, fun i ε ↦ ?_⟩
    · obtain ⟨b, hb, hj⟩ := hZ.1 _ hy
      exact ⟨b, (hdim _ y).trans hb, hj⟩
    · have h := ih (hZ.2 i ε)
      have w := map_cubeFace i (if ε then 1 else 0) f
      have he : f.appTop (if ε then 1 else 0) = (if ε then 1 else 0) := by cases ε <;> simp
      rw [he] at w
      apply h.mono
      intro y hy
      simpa only [Set.mem_preimage, ← Scheme.Hom.comp_apply, w] using hy

section Restriction

variable (k : Type u) [Field k] [X.Over (Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]

include k in
/-- Open restriction preserves admissibility of a generic point in the same dimension grading. -/
lemma mem_admissibleCubePoints_of_map_mem (f : U ⟶ X) [IsOpenImmersion f]
    {x : 𝔸(ULift.{u} (Fin n); U)} (hx : AffineSpace.map _ f x ∈ admissibleCubePoints X j n) :
    x ∈ admissibleCubePoints U j n := by
  let g := AffineSpace.map (ULift.{u} (Fin n)) f
  let : IsOpenImmersion g := MorphismProperty.of_isPullback (isPullback_map f).flip inferInstance
  let : LocallyOfFiniteType (𝔸(ULift.{u} (Fin n); X) ↘ Spec (.of k)) :=
    inferInstanceAs (LocallyOfFiniteType ((𝔸(ULift.{u} (Fin n); X) ↘ X) ≫ X ↘ Spec (.of k)))
  obtain ⟨hx, hZ⟩ := mem_admissibleCubePoints_iff.mp hx
  refine mem_admissibleCubePoints_iff.mpr ⟨?_, (hZ.preimage f).mono ?_⟩
  · rw [mem_pointsOfDimension] at hx ⊢
    rwa [← height_apply_of_isOpenImmersion k g x]
  · exact (Set.mapsTo_singleton.mpr (Set.mem_singleton _)).closure g.continuous

/-- Restriction of raw cubical cycles to an open subscheme. -/
def cubicalCyclesRestrict (f : U ⟶ X) [IsOpenImmersion f] (j : ℤ) (n : ℕ) :
    cubicalCycles X j n →+ cubicalCycles U j n := by
  let g := AffineSpace.map (ULift.{u} (Fin n)) f
  letI : IsOpenImmersion g := MorphismProperty.of_isPullback (isPullback_map f).flip inferInstance
  letI : LocallyOfFiniteType (𝔸(ULift.{u} (Fin n); X) ↘ Spec (.of k)) :=
    inferInstanceAs (LocallyOfFiniteType ((𝔸(ULift.{u} (Fin n); X) ↘ X) ≫ X ↘ Spec (.of k)))
  let res := (cyclesRestrict k g (n := j + n)).comp (AddSubgroup.inclusion
    (cubicalCycles_le_cyclesOfDimension (X := X)))
  refine (((cyclesOfDimension _ (j + n)).subtype).comp res).codRestrict _ fun α ↦ ?_
  refine mem_cubicalCycles_iff.mpr fun y hy ↦ mem_admissibleCubePoints_of_map_mem k f ?_
  apply mem_cubicalCycles_iff.mp α.property
  exact (Function.mem_support.mp hy) ∘ fun h ↦ (cyclesRestrict_apply g _ y).trans h

/-- Open restriction reads the original coefficient at the image point of the cube. -/
@[simp]
lemma cubicalCyclesRestrict_apply (f : U ⟶ X) [IsOpenImmersion f] (α : cubicalCycles X j n)
    (x : 𝔸(ULift.{u} (Fin n); U)) :
    (cubicalCyclesRestrict k f j n α : AlgebraicCycle _ ℤ) x =
      (α : AlgebraicCycle _ ℤ) (AffineSpace.map _ f x) := by
  simp [cubicalCyclesRestrict, cyclesRestrict_apply]

/-- Restriction to the identity open immersion fixes a cubical cycle. -/
@[simp]
lemma cubicalCyclesRestrict_id :
    cubicalCyclesRestrict k (𝟙 X) j n = AddMonoidHom.id _ := by
  ext α x
  simp

/-- Restricting successively is restriction along the composite open immersion. -/
lemma cubicalCyclesRestrict_comp [U.Over (Spec (.of k))] [LocallyOfFiniteType (U ↘ Spec (.of k))]
    (g : V ⟶ U) (f : U ⟶ X) [IsOpenImmersion f] [IsOpenImmersion g] :
    cubicalCyclesRestrict k (g ≫ f) j n =
      (cubicalCyclesRestrict k g j n).comp (cubicalCyclesRestrict k f j n) := by
  ext α x
  simp

end Restriction

end TauCeti.AlgebraicGeometry.Chow
