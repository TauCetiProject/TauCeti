/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Topology.Algebra.Module.Equiv.Pi
public import Mathlib.Topology.Algebra.Module.Equiv.Prod
public import TauCeti.Topology.PiCurry
import Mathlib.Algebra.Order.Group.Pointwise.Interval
import Mathlib.Order.Interval.Set.Pi

/-!
# Continuous linear regrouping of coordinate families

`ContinuousLinearEquiv.piOptionEquivProd` splits a dependent family indexed by `Option ι`
into its `none` coordinate and its `some` coordinates, and
`ContinuousLinearEquiv.piProdEquivPiOption` reassembles a family on `ι` paired with a
distinguished coordinate into a family on `Option ι`. Both supply product coordinates
for linear charts, with no finiteness or norm assumptions.

The construction combines `LinearEquiv.piOptionEquivProd` with
`TauCeti.piOptionEquivProdHomeomorph`.

For Mathlib's `ContinuousLinearEquiv.piCongrLeft` and `ContinuousLinearEquiv.sumPiEquivProdPi`,
`@[simp]` lemmas evaluate the equivalences and their inverses and record reflexivity of
`piCongrLeft`, and `ContinuousLinearEquiv.piProdEquivPiSumUnique` identifies `(σ → M) × M` with
`σ ⊕ τ → M` for any unique index type `τ`.
`ContinuousLinearEquiv.negCoord` negates a single coordinate of a dependent product while leaving
the remaining coordinates fixed; `TauCeti.image_single_add_negCoord_univ_pi`,
`TauCeti.image_single_add_negCoord_Icc`, and `TauCeti.image_single_add_negCoord_pi_Ioo` record
its action on product sets and unit cubes, and `TauCeti.image_add_piCongrRight_smulLeft_Icc`
identifies the image of the unit cube under positive coordinatewise scaling.

`TauCeti.piSigmaConstContinuousLinearEquiv` regroups a family of tuples along a bijection of its
sigma index. Its underlying homeomorphism is `TauCeti.piSigmaConstHomeomorph`, which is linear
coordinatewise, so coordinate calculations can use both the homeomorphism and the linear API.

Over an empty index type, `ContinuousLinearMap.piMap T` is a continuous linear equivalence
between zero spaces (`ContinuousLinearMap.piMap_eq_of_isEmpty`), and
`ContinuousLinearMap.piCongrLeft_symm_comp_piMap` reindexes a product operator along an
equivalence of index types.
-/

public section

namespace ContinuousLinearEquiv

variable (R : Type*) [Semiring R]

section OptionPi

variable {ι : Type*} {M : Option ι → Type*}
  [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)] [∀ i, TopologicalSpace (M i)]

/-- Split a family indexed by `Option ι` into its distinguished coordinate and the rest. -/
def piOptionEquivProd : ((i : Option ι) → M i) ≃L[R] M none × ((i : ι) → M (some i)) :=
  { toLinearEquiv := LinearEquiv.piOptionEquivProd R
    continuous_toFun := (TauCeti.piOptionEquivProdHomeomorph M).continuous.congr
      (fun x => TauCeti.piOptionEquivProdHomeomorph_apply M x)
    continuous_invFun := (TauCeti.piOptionEquivProdHomeomorph M).symm.continuous.congr
      (fun q => by
        funext i
        cases i <;> simp only [TauCeti.piOptionEquivProdHomeomorph_symm_apply_none,
          TauCeti.piOptionEquivProdHomeomorph_symm_apply_some] <;> rfl) }

/-- The split coordinates are the `none` value followed by the `some` values. -/
@[simp] theorem piOptionEquivProd_apply (x : (i : Option ι) → M i) :
    piOptionEquivProd R x = (x none, fun i => x (some i)) := (rfl)

/-- Reassemble an optional coordinate family from its distinguished value and the rest. -/
@[simp] theorem piOptionEquivProd_symm_apply (q : M none × ((i : ι) → M (some i))) :
    (piOptionEquivProd R).symm q = (fun i => match i with
      | none => q.1
      | some j => q.2 j) := by
  funext i
  cases i <;> rfl

/-- Identify a family indexed by `ι` paired with a distinguished coordinate as a family indexed by
`Option ι`, placing the distinguished coordinate at `none`. -/
def piProdEquivPiOption :
    (((i : ι) → M (some i)) × M none) ≃L[R] ((i : Option ι) → M i) :=
  (prodComm R ((i : ι) → M (some i)) (M none)).trans (piOptionEquivProd R).symm

/-- Applying `piProdEquivPiOption` places the distinguished coordinate at `none` and the remaining
coordinates at `some i`. -/
@[simp] theorem piProdEquivPiOption_apply (q : ((i : ι) → M (some i)) × M none) :
    piProdEquivPiOption R q = (fun i => match i with
      | none => q.2
      | some j => q.1 j) := by
  funext i
  cases i <;> rfl

/-- The inverse of `piProdEquivPiOption` extracts the `some` coordinates and the `none`
coordinate. -/
@[simp] theorem piProdEquivPiOption_symm_apply (x : (i : Option ι) → M i) :
    (piProdEquivPiOption R).symm x = (fun i => x (some i), x none) := (rfl)

end OptionPi

section PiCongrLeft

variable {ι ι' : Type*} (φ : ι → Type*) [∀ i, AddCommMonoid (φ i)] [∀ i, Module R (φ i)]
  [∀ i, TopologicalSpace (φ i)]

/-- Reindexing along the identity equivalence gives the identity continuous linear equivalence. -/
@[simp] theorem piCongrLeft_refl :
    piCongrLeft R φ (.refl ι) = .refl R ((i : ι) → φ i) := (rfl)

/-- The inverse of `ContinuousLinearEquiv.piCongrLeft` precomposes with the index equivalence. -/
@[simp] theorem piCongrLeft_symm_apply (e : ι' ≃ ι) (g : (i : ι) → φ i) (i' : ι') :
    (piCongrLeft R φ e).symm g i' = g (e i') := (rfl)

/-- Evaluating `ContinuousLinearEquiv.piCongrLeft` at an image index `e i'` returns the `i'`th
coordinate. -/
@[simp] theorem piCongrLeft_apply_apply (e : ι' ≃ ι) (f : (i' : ι') → φ (e i')) (i' : ι') :
    piCongrLeft R φ e f (e i') = f i' :=
  Equiv.piCongrLeft_apply_apply φ e f i'

end PiCongrLeft

section PiCongrLeftConst

variable {ι ι' : Type*} (N : Type*) [AddCommMonoid N] [Module R N] [TopologicalSpace N]

/-- On a non-dependent family, `ContinuousLinearEquiv.piCongrLeft` precomposes with `e.symm`. -/
@[simp] theorem piCongrLeft_const_apply (e : ι' ≃ ι) (f : ι' → N) (i : ι) :
    piCongrLeft R (fun _ : ι ↦ N) e f i = f (e.symm i) := by
  obtain ⟨i', rfl⟩ := e.surjective i; simp

end PiCongrLeftConst

section SumPi

variable {S T : Type*} {A : S ⊕ T → Type*} [∀ st, AddCommMonoid (A st)] [∀ st, Module R (A st)]
  [∀ st, TopologicalSpace (A st)]

/-- Mathlib's `ContinuousLinearEquiv.sumPiEquivProdPi` restricts a family on `S ⊕ T` to `S` and
to `T`. -/
@[simp] theorem sumPiEquivProdPi_apply (x : (st : S ⊕ T) → A st) :
    sumPiEquivProdPi R S T A x = (fun s => x (.inl s), fun t => x (.inr t)) := (rfl)

/-- The inverse of `ContinuousLinearEquiv.sumPiEquivProdPi` glues a family on `S` and a family on
`T` into a family on `S ⊕ T`. -/
@[simp] theorem sumPiEquivProdPi_symm_apply
    (p : ((s : S) → A (.inl s)) × ((t : T) → A (.inr t))) :
    (sumPiEquivProdPi R S T A).symm p = Sum.rec p.1 p.2 := (rfl)

/-- Identify a family indexed by `σ` paired with a single value in `N` as a family indexed by
`σ ⊕ τ` for any unique index type `τ`. -/
def piProdEquivPiSumUnique (σ τ N : Type*) [Unique τ]
    [AddCommMonoid N] [Module R N] [TopologicalSpace N] :
    ((σ → N) × N) ≃L[R] (σ ⊕ τ → N) :=
  ((ContinuousLinearEquiv.refl R (σ → N)).prodCongr (funUnique τ R N).symm).trans
    (sumPiEquivProdPi R σ τ (fun _ ↦ N)).symm

/-- Applying `piProdEquivPiSumUnique` combines the `σ`-indexed family with the constant value on
`τ` via `Sum.elim`. -/
@[simp] theorem piProdEquivPiSumUnique_apply {σ τ N : Type*} [Unique τ]
    [AddCommMonoid N] [Module R N] [TopologicalSpace N] (q : (σ → N) × N) :
    piProdEquivPiSumUnique R σ τ N q = Sum.elim q.1 (fun _ ↦ q.2) := by
  funext x
  cases x <;> rfl

/-- The inverse of `piProdEquivPiSumUnique` restricts to `σ` and evaluates at `Sum.inr default`. -/
@[simp] theorem piProdEquivPiSumUnique_symm_apply {σ τ N : Type*} [Unique τ]
    [AddCommMonoid N] [Module R N] [TopologicalSpace N] (p : σ ⊕ τ → N) :
    (piProdEquivPiSumUnique R σ τ N).symm p = (p ∘ Sum.inl, p (.inr default)) :=
  (rfl)

end SumPi

section NegCoord

variable {R} {ι : Type*} [DecidableEq ι] {N P : ι → Type*}
  [∀ i, TopologicalSpace (N i)] [∀ i, AddCommMonoid (N i)] [∀ i, Module R (N i)]
  [∀ i, TopologicalSpace (P i)] [∀ i, AddCommMonoid (P i)] [∀ i, Module R (P i)]

/-- A coordinatewise continuous linear equivalence sends a one-point family to the one-point family
of its image in that coordinate. -/
@[simp]
theorem piCongrRight_single (e : ∀ i, N i ≃L[R] P i) (i : ι) (x : N i) :
    piCongrRight e (Pi.single i x) = Pi.single i (e i x) := by
  funext j
  rw [piCongrRight_apply]
  exact Pi.apply_single (fun i ↦ e i) (fun _ ↦ map_zero _) i x j

variable (R) {Q : ι → Type*} [∀ i, TopologicalSpace (Q i)] [∀ i, AddCommGroup (Q i)]
  [∀ i, Module R (Q i)] [∀ i, ContinuousNeg (Q i)]

/-- Negate the `k`-th coordinate of a dependent product while leaving all other coordinates
unchanged, as a continuous linear equivalence. -/
def negCoord (k : ι) : ((i : ι) → Q i) ≃L[R] (i : ι) → Q i :=
  piCongrRight (Function.update (fun i ↦ ContinuousLinearEquiv.refl R (Q i)) k (neg R))

variable {R}

theorem negCoord_def (k : ι) :
    negCoord R (Q := Q) k =
      piCongrRight (Function.update (fun i ↦ ContinuousLinearEquiv.refl R (Q i)) k (neg R)) :=
  (rfl)

/-- `negCoord` updates the `k`-th coordinate by its negation. -/
theorem negCoord_eq_update (k : ι) (x : (i : ι) → Q i) :
    negCoord R k x = Function.update x k (-x k) := by
  ext i
  by_cases h : i = k
  · subst h
    simp [negCoord]
  · simp [negCoord, h]

@[simp]
theorem negCoord_apply_same (k : ι) (x : (i : ι) → Q i) :
    negCoord R k x k = -x k := by
  simp [negCoord]

@[simp]
theorem negCoord_apply_of_ne {k i : ι} (h : i ≠ k) (x : (i : ι) → Q i) :
    negCoord R k x i = x i := by
  simp [negCoord, h]

@[simp]
theorem symm_negCoord (k : ι) :
    (negCoord R (Q := Q) k).symm = negCoord R k := by
  ext x i
  by_cases h : i = k
  · subst h
    simp [negCoord]
  · simp [negCoord, h]

@[simp]
theorem negCoord_negCoord (k : ι) (x : (i : ι) → Q i) :
    negCoord R k (negCoord R k x) = x := by
  ext i
  by_cases h : i = k
  · subst h
    simp
  · simp [h]

@[simp]
theorem negCoord_trans_negCoord (k : ι) :
    (negCoord R (Q := Q) k).trans (negCoord R k) = .refl R ((i : ι) → Q i) := by
  ext x i
  simp

@[simp]
theorem negCoord_comp_negCoord (k : ι) :
    (negCoord R (Q := Q) k : ((i : ι) → Q i) → (i : ι) → Q i) ∘
        (negCoord R k : ((i : ι) → Q i) → (i : ι) → Q i) = id := by
  ext x
  simp

@[simp]
theorem negCoord_single_same (k : ι) (v : Q k) :
    negCoord R (Q := Q) k (Pi.single k v) = Pi.single k (-v) := by
  simp [negCoord]

@[simp]
theorem negCoord_single_of_ne {k i : ι} (h : i ≠ k) (v : Q i) :
    negCoord R (Q := Q) k (Pi.single i v) = Pi.single i v := by
  simp [negCoord, h]

end NegCoord

end ContinuousLinearEquiv

namespace ContinuousLinearMap

variable {R : Type*} [Semiring R]

section IsEmpty

variable {ι : Type*} [IsEmpty ι] {E F : ι → Type*}
variable [∀ i, AddCommMonoid (E i)] [∀ i, TopologicalSpace (E i)] [∀ i, Module R (E i)]
variable [∀ i, AddCommMonoid (F i)] [∀ i, TopologicalSpace (F i)] [∀ i, Module R (F i)]

/-- Over an empty index type the product operator is the unique map between zero spaces, which
is a continuous linear equivalence. -/
theorem piMap_eq_of_isEmpty (T : ∀ i, E i →L[R] F i) :
    piMap T = ((ContinuousLinearEquiv.piCongrRight fun i ↦ isEmptyElim i :
      (∀ i, E i) ≃L[R] ∀ i, F i) : (∀ i, E i) →L[R] ∀ i, F i) := by
  ext x i
  exact isEmptyElim i

end IsEmpty

section Reindex

variable {ι ι' : Type*} {E F : ι → Type*}
variable [∀ i, AddCommMonoid (E i)] [∀ i, TopologicalSpace (E i)] [∀ i, Module R (E i)]
variable [∀ i, AddCommMonoid (F i)] [∀ i, TopologicalSpace (F i)] [∀ i, Module R (F i)]

/-- Reindexing a product operator along `e : ι' ≃ ι` gives the product of the reindexed family. -/
theorem piCongrLeft_symm_comp_piMap (e : ι' ≃ ι) (T : ∀ i, E i →L[R] F i) :
    ((ContinuousLinearEquiv.piCongrLeft R F e).symm : (∀ i, F i) →L[R] ∀ i', F (e i')) ∘L
        piMap T =
      piMap (fun i' ↦ T (e i')) ∘L
        ((ContinuousLinearEquiv.piCongrLeft R E e).symm : (∀ i, E i) →L[R] ∀ i', E (e i')) :=
  -- the inverse of `piCongrLeft` reads the coordinate `i'` of a vector at `e i'` by definition
  (rfl)

end Reindex

end ContinuousLinearMap

namespace TauCeti

/-- Reflecting the `k`-th coordinate by `t ↦ c - t`, namely `u ↦ Pi.single k c + negCoord R k u`,
maps a product set `Set.univ.pi s` to the product set with `s k` replaced by `(c - ·) '' s k`. -/
theorem image_single_add_negCoord_univ_pi {R : Type*} [Semiring R] {ι : Type*} [DecidableEq ι]
    {Q : ι → Type*} [∀ i, TopologicalSpace (Q i)] [∀ i, AddCommGroup (Q i)]
    [∀ i, Module R (Q i)] [∀ i, ContinuousNeg (Q i)] (k : ι) (c : Q k) (s : ∀ i, Set (Q i)) :
    (fun u : (i : ι) → Q i ↦ Pi.single k c + ContinuousLinearEquiv.negCoord R k u) ''
        Set.univ.pi s =
      Set.univ.pi (Function.update s k ((fun t ↦ c - t) '' s k)) := by
  have hmap : (fun u : (i : ι) → Q i ↦ Pi.single k c + ContinuousLinearEquiv.negCoord R k u) =
      Pi.map (Function.update (fun i ↦ (id : Q i → Q i)) k (fun t ↦ c - t)) := by
    ext u i
    rcases eq_or_ne i k with rfl | hik <;> simp [sub_eq_add_neg, *]
  rw [hmap, Set.piMap_image_univ_pi]
  refine Set.pi_congr rfl fun i _ ↦ ?_
  rcases eq_or_ne i k with rfl | hik <;> simp [*]

/-- Reflecting the `k`-th coordinate by `t ↦ 1 - t` maps the closed unit cube `Set.Icc 0 1` in
`ι → R` onto itself over any ordered ring `R`. -/
theorem image_single_add_negCoord_Icc {R : Type*} [Ring R] [PartialOrder R]
    [IsOrderedAddMonoid R] [TopologicalSpace R] [ContinuousNeg R] {ι : Type*} [DecidableEq ι]
    (k : ι) :
    (fun u : ι → R ↦ Pi.single k 1 + ContinuousLinearEquiv.negCoord R k u) ''
        Set.Icc 0 1 = Set.Icc 0 1 := by
  rw [← Set.pi_univ_Icc, image_single_add_negCoord_univ_pi]
  simp

/-- Reflecting the `k`-th coordinate by `t ↦ 1 - t` maps the open unit cube
`Set.univ.pi fun _ ↦ Set.Ioo 0 1` in `ι → R` onto itself over any ordered ring `R`. -/
theorem image_single_add_negCoord_pi_Ioo {R : Type*} [Ring R] [PartialOrder R]
    [IsOrderedAddMonoid R] [TopologicalSpace R] [ContinuousNeg R] {ι : Type*} [DecidableEq ι]
    (k : ι) :
    (fun u : ι → R ↦ Pi.single k 1 + ContinuousLinearEquiv.negCoord R k u) ''
        Set.univ.pi (fun _ ↦ Set.Ioo 0 1) =
      Set.univ.pi (fun _ ↦ Set.Ioo 0 1) := by
  rw [image_single_add_negCoord_univ_pi]
  simp

/-- Positive coordinatewise scaling from `a` by `b - a` maps the unit cube `Set.Icc 0 1` in
`ι → K` onto the closed box `Set.Icc a b` over any ordered field `K`. -/
theorem image_add_piCongrRight_smulLeft_Icc {K : Type*} [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] [TopologicalSpace K] [ContinuousConstSMul K K]
    {ι : Type*} {a b : ι → K} (hab : ∀ i, a i < b i) :
    (fun u : ι → K ↦ a +
      ContinuousLinearEquiv.piCongrRight (fun i ↦
        (ContinuousLinearEquiv.smulLeft
          (Units.mk0 (b i - a i) (sub_ne_zero.mpr (hab i).ne')) : K ≃L[K] K)) u) ''
        Set.Icc 0 1 = Set.Icc a b := by
  have hmap : (fun u : ι → K ↦ a +
      ContinuousLinearEquiv.piCongrRight (fun i ↦
        (ContinuousLinearEquiv.smulLeft
          (Units.mk0 (b i - a i) (sub_ne_zero.mpr (hab i).ne')) : K ≃L[K] K)) u) =
      Pi.map fun i t ↦ (b i - a i) * t + a i := by
    ext u i
    simp [add_comm]
  rw [hmap, ← Set.pi_univ_Icc, Set.piMap_image_univ_pi, ← Set.pi_univ_Icc]
  refine Set.pi_congr rfl fun i _ ↦ ?_
  simp [Set.image_affine_Icc' (sub_pos.mpr (hab i))]

/-- Regrouping a family of tuples along a bijection of the sigma index, as a continuous linear
equivalence. The underlying homeomorphism is `TauCeti.piSigmaConstHomeomorph`. -/
def piSigmaConstContinuousLinearEquiv (R : Type*) [Semiring R] (E : Type*)
    [TopologicalSpace E] [AddCommMonoid E] [Module R E]
    {ι : Type*} {κ : ι → Type*} {ι' : Type*} (e : (Σ i, κ i) ≃ ι') :
    (∀ i, κ i → E) ≃L[R] (ι' → E) where
  __ := piSigmaConstHomeomorph E e
  map_add' x y := by
    funext j
    simp
  map_smul' c x := by
    funext j
    simp

/-- The continuous linear regrouping has the existing regrouping homeomorphism as its function. -/
@[simp]
theorem coe_piSigmaConstContinuousLinearEquiv (R : Type*) [Semiring R] (E : Type*)
    [TopologicalSpace E] [AddCommMonoid E] [Module R E]
    {ι : Type*} {κ : ι → Type*} {ι' : Type*} (e : (Σ i, κ i) ≃ ι') :
    (piSigmaConstContinuousLinearEquiv R E e : (∀ i, κ i → E) → (ι' → E)) =
      piSigmaConstHomeomorph E e :=
  (rfl)

/-- The inverse continuous linear regrouping has the inverse regrouping homeomorphism as its
function. -/
@[simp]
theorem coe_piSigmaConstContinuousLinearEquiv_symm (R : Type*) [Semiring R] (E : Type*)
    [TopologicalSpace E] [AddCommMonoid E] [Module R E]
    {ι : Type*} {κ : ι → Type*} {ι' : Type*} (e : (Σ i, κ i) ≃ ι') :
    ((piSigmaConstContinuousLinearEquiv R E e).symm : (ι' → E) → ∀ i, κ i → E) =
      (piSigmaConstHomeomorph E e).symm :=
  (rfl)

end TauCeti
