/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Steinberg.Basic
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.GroupTheory.NoncommPiCoprod

/-!
# Row and column root subgroups of the Steinberg group

Fix an associative unital ring `R`, a finite index type `ι` and an index `t : ι`. The Steinberg
generators `x_{it}(a)` with `i ≠ t` pairwise commute, and so do the generators `x_{ti}(a)`. Hence
every vector `v : {i // i ≠ t} → R` determines the **column element**
`colHom t v = ∏_{i ≠ t} x_{it}(v i)` and the **row element** `rowHom t v = ∏_{i ≠ t} x_{ti}(v i)`
of `St_ι(R)`, independently of the order of the factors, and both are homomorphisms from the
additive group of vectors.

Their images in `GL ι R` are the unipotent matrices `1 + ∑_{i ≠ t} single i t (v i)` and
`1 + ∑_{i ≠ t} single t i (v i)`, from which every coordinate of `v` can be read off. So both
homomorphisms are injective, already after composing with `St_ι(R) →* GL ι R`, and for `ι = Fin n`
they remain injective after mapping to the stable Steinberg group `St(R)`. A generator `x_{ab}(c)`
with `a, b ≠ t` normalizes both subgroups: conjugation by it adds `c * v b` to the column
coordinate `v a`, and adds `-(v a * c)` to the row coordinate `v b`. These faithful normalized
root subgroups are the device behind Kervaire's and Steinberg's proof that the kernel of
`St(R) →* E(R)` is central.

No commutativity of `R` is assumed; the order of the products `c * v b` and `v a * c` matters.

## Main definitions

* `TauCeti.IndexedSteinbergGroup.colHom`: the column homomorphism
  `Multiplicative ({i // i ≠ t} → R) →* St_ι(R)`, `v ↦ ∏_{i ≠ t} x_{it}(v i)`.
* `TauCeti.IndexedSteinbergGroup.rowHom`: the row homomorphism
  `Multiplicative ({i // i ≠ t} → R) →* St_ι(R)`, `v ↦ ∏_{i ≠ t} x_{ti}(v i)`.

## Main results

* `TauCeti.IndexedSteinbergGroup.colHom_ofAdd_single`,
  `TauCeti.IndexedSteinbergGroup.rowHom_ofAdd_single`: on a basis vector they are the Steinberg
  generators.
* `TauCeti.IndexedSteinbergGroup.coe_toGL_colHom`, `TauCeti.IndexedSteinbergGroup.coe_toGL_rowHom`:
  the matrix images.
* `TauCeti.IndexedSteinbergGroup.toGL_comp_colHom_injective`,
  `TauCeti.IndexedSteinbergGroup.colHom_injective`,
  `TauCeti.SteinbergGroup.ofFin_comp_colHom_injective`, and their row versions: faithfulness in
  `GL ι R`, in `St_ι(R)` and in the stable group `St(R)`.
* `TauCeti.IndexedSteinbergGroup.x_mem_range_colHom`,
  `TauCeti.IndexedSteinbergGroup.x_mem_range_rowHom`: the generators lie in the root subgroups.
* `TauCeti.IndexedSteinbergGroup.x_mul_colHom_mul_inv`,
  `TauCeti.IndexedSteinbergGroup.x_mul_rowHom_mul_inv`: conjugation by `x_{ab}(c)` with
  `a, b ≠ t`.
* `TauCeti.IndexedSteinbergGroup.x_mem_normalizer_range_colHom`,
  `TauCeti.IndexedSteinbergGroup.x_mem_normalizer_range_rowHom`: hence `x_{ab}(c)` normalizes both
  root subgroups.
* `TauCeti.IndexedSteinbergGroup.map_colHom`, `TauCeti.IndexedSteinbergGroup.mapIndex_colHom`,
  `TauCeti.IndexedSteinbergGroup.transposeOp_colHom`, and their row versions: compatibility with
  ring homomorphisms, with index embeddings (which extend vectors by zero), and with the
  opposite-ring inverse-transpose isomorphism.

## References

* J. Milnor, *Introduction to Algebraic K-Theory*, Annals of Mathematics Studies 72 (1971), §5,
  proof of Theorem 5.1.
* C. A. Weibel, *The K-book: An Introduction to Algebraic K-Theory*, Graduate Studies in
  Mathematics 145 (2013), Chapter III, Exercise 5.2 and the proof of Theorem 5.2.1.
-/

public section

noncomputable section

open Matrix

namespace TauCeti

namespace IndexedSteinbergGroup

variable {ι κ R S : Type*} [Ring R] [Ring S]

section Hom

private theorem pairwise_commute_xHom_col (t : ι) :
    Pairwise fun i j : {i // i ≠ t} ↦ ∀ a b : Multiplicative R,
      Commute (xHom i.2 a) (xHom j.2 b) :=
  fun i j _ a b ↦ by
    rw [xHom_apply, xHom_apply]
    exact commute_x i.2 j.2 j.2.symm i.2.symm a.toAdd b.toAdd

private theorem pairwise_commute_xHom_row (t : ι) :
    Pairwise fun i j : {i // i ≠ t} ↦ ∀ a b : Multiplicative R,
      Commute (xHom i.2.symm a) (xHom j.2.symm b) :=
  fun i j _ a b ↦ by
    rw [xHom_apply, xHom_apply]
    exact commute_x i.2.symm j.2.symm i.2 j.2 a.toAdd b.toAdd

private theorem funMultiplicative_ofAdd_single {α : Type*} [DecidableEq α] (i : α) (r : R) :
    MulEquiv.funMultiplicative α R (Multiplicative.ofAdd (Pi.single i r)) =
      Pi.mulSingle i (Multiplicative.ofAdd r) :=
  funext fun j ↦ (Pi.mulSingle_multiplicativeOfAdd_eq (M := fun _ ↦ R) i r j).symm

variable [Fintype ι] [DecidableEq ι] (t : ι)

/-- The **column root homomorphism** `v ↦ ∏_{i ≠ t} x_{it}(v i)` from the additive group of
vectors indexed by `{i // i ≠ t}` to the Steinberg group; its factors commute, so no order is
involved. -/
def colHom : Multiplicative ({i // i ≠ t} → R) →* IndexedSteinbergGroup ι R :=
  (MonoidHom.noncommPiCoprod (fun i ↦ xHom i.2) (pairwise_commute_xHom_col t)).comp
    (MulEquiv.funMultiplicative {i // i ≠ t} R).toMonoidHom

/-- The **row root homomorphism** `v ↦ ∏_{i ≠ t} x_{ti}(v i)` from the additive group of vectors
indexed by `{i // i ≠ t}` to the Steinberg group; its factors commute, so no order is involved. -/
def rowHom : Multiplicative ({i // i ≠ t} → R) →* IndexedSteinbergGroup ι R :=
  (MonoidHom.noncommPiCoprod (fun i ↦ xHom i.2.symm) (pairwise_commute_xHom_row t)).comp
    (MulEquiv.funMultiplicative {i // i ≠ t} R).toMonoidHom

variable {t}

/-- On the basis vector supported at `i` with value `r`, the column homomorphism is the Steinberg
generator `x_{it}(r)`. -/
@[simp]
theorem colHom_ofAdd_single (i : {i // i ≠ t}) (r : R) :
    colHom t (Multiplicative.ofAdd (Pi.single i r)) = x i.2 r := by
  rw [colHom, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, funMultiplicative_ofAdd_single,
    MonoidHom.noncommPiCoprod_mulSingle, xHom_apply, toAdd_ofAdd]

/-- On the basis vector supported at `i` with value `r`, the row homomorphism is the Steinberg
generator `x_{ti}(r)`. -/
@[simp]
theorem rowHom_ofAdd_single (i : {i // i ≠ t}) (r : R) :
    rowHom t (Multiplicative.ofAdd (Pi.single i r)) = x i.2.symm r := by
  rw [rowHom, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, funMultiplicative_ofAdd_single,
    MonoidHom.noncommPiCoprod_mulSingle, xHom_apply, toAdd_ofAdd]

/-- Each generator `x_{it}(r)` with `i ≠ t` lies in the column root subgroup at `t`. -/
theorem x_mem_range_colHom (i : {i // i ≠ t}) (r : R) : x i.2 r ∈ (colHom t).range :=
  ⟨Multiplicative.ofAdd (Pi.single i r), colHom_ofAdd_single i r⟩

/-- Each generator `x_{ti}(r)` with `i ≠ t` lies in the row root subgroup at `t`. -/
theorem x_mem_range_rowHom (i : {i // i ≠ t}) (r : R) : x i.2.symm r ∈ (rowHom t).range :=
  ⟨Multiplicative.ofAdd (Pi.single i r), rowHom_ofAdd_single i r⟩

/-! ### Matrix images and faithfulness -/

/-- The image of the column element `colHom t v` in `GL ι R` is the unipotent matrix
`1 + ∑_{i ≠ t} single i t (v i)`, whose `t`-th column carries the coordinates of `v`. -/
@[simp]
theorem coe_toGL_colHom (v : {i // i ≠ t} → R) :
    (toGL (colHom t (Multiplicative.ofAdd v)) : Matrix ι ι R) =
      1 + ∑ i : {i // i ≠ t}, single (i : ι) t (v i) := by
  induction v using Pi.single_induction with
  | zero => simp
  | add v w hv hw =>
    have hvw : (∑ i : {i // i ≠ t}, single (i : ι) t (v i)) *
        ∑ j : {i // i ≠ t}, single (j : ι) t (w j) = 0 := by
      rw [Finset.sum_mul_sum]
      exact Finset.sum_eq_zero fun i _ ↦ Finset.sum_eq_zero fun j _ ↦ by simp [j.2.symm]
    simp only [ofAdd_add, map_mul, Units.val_mul, hv, hw, Pi.add_apply, single_add,
      Finset.sum_add_distrib, add_mul, mul_add, one_mul, mul_one, hvw]
    abel
  | single i r =>
    rw [colHom_ofAdd_single, toGL_x, coe_transvectionUnit_eq_one_add_single,
      Finset.sum_eq_single i (fun j _ hj ↦ by simp [hj]) (by simp)]
    simp

/-- The image of the row element `rowHom t v` in `GL ι R` is the unipotent matrix
`1 + ∑_{i ≠ t} single t i (v i)`, whose `t`-th row carries the coordinates of `v`. -/
@[simp]
theorem coe_toGL_rowHom (v : {i // i ≠ t} → R) :
    (toGL (rowHom t (Multiplicative.ofAdd v)) : Matrix ι ι R) =
      1 + ∑ i : {i // i ≠ t}, single t (i : ι) (v i) := by
  induction v using Pi.single_induction with
  | zero => simp
  | add v w hv hw =>
    have hvw : (∑ i : {i // i ≠ t}, single t (i : ι) (v i)) *
        ∑ j : {i // i ≠ t}, single t (j : ι) (w j) = 0 := by
      rw [Finset.sum_mul_sum]
      exact Finset.sum_eq_zero fun i _ ↦ Finset.sum_eq_zero fun j _ ↦ by simp [i.2]
    simp only [ofAdd_add, map_mul, Units.val_mul, hv, hw, Pi.add_apply, single_add,
      Finset.sum_add_distrib, add_mul, mul_add, one_mul, mul_one, hvw]
    abel
  | single i r =>
    rw [rowHom_ofAdd_single, toGL_x, coe_transvectionUnit_eq_one_add_single,
      Finset.sum_eq_single i (fun j _ hj ↦ by simp [hj]) (by simp)]
    simp

variable (t)

/-- The column root subgroup maps faithfully to `GL ι R`: the entry in position `(i, t)` of the
image of `colHom t v` is `v i`. -/
theorem toGL_comp_colHom_injective :
    Function.Injective (toGL.comp (colHom (ι := ι) (R := R) t)) := by
  intro v w h
  obtain ⟨v, rfl⟩ := Multiplicative.ofAdd.surjective v
  obtain ⟨w, rfl⟩ := Multiplicative.ofAdd.surjective w
  refine congrArg Multiplicative.ofAdd (funext fun i ↦ ?_)
  have hi := congrArg (fun g : GL ι R ↦ (g : Matrix ι ι R) i t) h
  simpa [coe_toGL_colHom, sum_apply, single_apply,
    one_apply_ne i.2, Subtype.coe_inj] using hi

/-- The row root subgroup maps faithfully to `GL ι R`: the entry in position `(t, i)` of the image
of `rowHom t v` is `v i`. -/
theorem toGL_comp_rowHom_injective :
    Function.Injective (toGL.comp (rowHom (ι := ι) (R := R) t)) := by
  intro v w h
  obtain ⟨v, rfl⟩ := Multiplicative.ofAdd.surjective v
  obtain ⟨w, rfl⟩ := Multiplicative.ofAdd.surjective w
  refine congrArg Multiplicative.ofAdd (funext fun i ↦ ?_)
  have hi := congrArg (fun g : GL ι R ↦ (g : Matrix ι ι R) t i) h
  simpa [coe_toGL_rowHom, sum_apply, single_apply,
    one_apply_ne i.2.symm, Subtype.coe_inj] using hi

/-- The column homomorphism is injective. -/
theorem colHom_injective : Function.Injective (colHom (ι := ι) (R := R) t) :=
  fun _ _ h ↦ toGL_comp_colHom_injective t (congrArg toGL h)

/-- The row homomorphism is injective. -/
theorem rowHom_injective : Function.Injective (rowHom (ι := ι) (R := R) t) :=
  fun _ _ h ↦ toGL_comp_rowHom_injective t (congrArg toGL h)

variable {t}

/-! ### Conjugation by Steinberg generators away from `t` -/

/-- Conjugating a column element by `x_{ab}(c)`, for distinct `a, b` both different from `t`,
adds `c * v b` to the coordinate `v a`. -/
theorem x_mul_colHom_mul_inv {a b : ι} (hab : a ≠ b) (hat : a ≠ t) (hbt : b ≠ t) (c : R)
    (v : {i // i ≠ t} → R) :
    x hab c * colHom t (Multiplicative.ofAdd v) * (x hab c)⁻¹ =
      colHom t (Multiplicative.ofAdd (v + Pi.single ⟨a, hat⟩ (c * v ⟨b, hbt⟩))) := by
  induction v using Pi.single_induction with
  | zero => simp [← x_add]
  | add v w hv hw =>
    have hconj : x hab c * colHom t (Multiplicative.ofAdd (v + w)) * (x hab c)⁻¹ =
        (x hab c * colHom t (Multiplicative.ofAdd v) * (x hab c)⁻¹) *
          (x hab c * colHom t (Multiplicative.ofAdd w) * (x hab c)⁻¹) := by
      rw [ofAdd_add, map_mul]
      group
    rw [hconj, hv, hw, ← map_mul, ← ofAdd_add, Pi.add_apply, mul_add, Pi.single_add]
    abel_nf
  | single i r =>
    by_cases hib : i = ⟨b, hbt⟩
    · subst hib
      simp only [colHom_ofAdd_single, x_mul_x_mul_inv hab hbt hat, Pi.single_eq_same, ofAdd_add,
        map_mul]
      exact (commute_x hat hbt hbt.symm hat.symm _ _).eq
    · have hib' : (b : ι) ≠ i := fun h ↦ hib (Subtype.ext h.symm)
      simp [(commute_x hab i.2 hib' hat.symm c r).eq, Pi.single_eq_of_ne (Ne.symm hib), mul_assoc,
        ← x_add]

/-- Conjugating a row element by `x_{ab}(c)`, for distinct `a, b` both different from `t`,
adds `-(v a * c)` to the coordinate `v b`. -/
theorem x_mul_rowHom_mul_inv {a b : ι} (hab : a ≠ b) (hat : a ≠ t) (hbt : b ≠ t) (c : R)
    (v : {i // i ≠ t} → R) :
    x hab c * rowHom t (Multiplicative.ofAdd v) * (x hab c)⁻¹ =
      rowHom t (Multiplicative.ofAdd (v + Pi.single ⟨b, hbt⟩ (-(v ⟨a, hat⟩ * c)))) := by
  induction v using Pi.single_induction with
  | zero => simp [← x_add]
  | add v w hv hw =>
    have hconj : x hab c * rowHom t (Multiplicative.ofAdd (v + w)) * (x hab c)⁻¹ =
        (x hab c * rowHom t (Multiplicative.ofAdd v) * (x hab c)⁻¹) *
          (x hab c * rowHom t (Multiplicative.ofAdd w) * (x hab c)⁻¹) := by
      rw [ofAdd_add, map_mul]
      group
    rw [hconj, hv, hw, ← map_mul, ← ofAdd_add, Pi.add_apply, add_mul, neg_add, Pi.single_add]
    abel_nf
  | single i r =>
    by_cases hia : i = ⟨a, hat⟩
    · subst hia
      simp only [rowHom_ofAdd_single, x_mul_x_mul_inv_reverse hab hat.symm hbt.symm,
        Pi.single_eq_same, ofAdd_add, map_mul]
      exact (commute_x hbt.symm hat.symm hbt hat _ _).eq
    · have hia' : (i : ι) ≠ a := fun h ↦ hia (Subtype.ext h)
      simp [(commute_x hab i.2.symm hbt hia' c r).eq, Pi.single_eq_of_ne (Ne.symm hia), mul_assoc,
        ← x_add]

/-- A generator `x_{ab}(c)`, for distinct `a, b` both different from `t`, normalizes the column
root subgroup at `t`. -/
theorem x_mem_normalizer_range_colHom {a b : ι} (hab : a ≠ b) (hat : a ≠ t) (hbt : b ≠ t)
    (c : R) :
    x hab c ∈
      Subgroup.normalizer ((colHom (R := R) t).range : Set (IndexedSteinbergGroup ι R)) := by
  have hconj : ∀ (c : R) (y : IndexedSteinbergGroup ι R), y ∈ (colHom t).range →
      x hab c * y * (x hab c)⁻¹ ∈ (colHom t).range := by
    rintro c _ ⟨v, rfl⟩
    exact ⟨_, (x_mul_colHom_mul_inv hab hat hbt c v.toAdd).symm⟩
  refine Subgroup.mem_normalizer_iff.mpr fun y ↦ ⟨hconj c y, fun hy ↦ ?_⟩
  simpa [← x_inv, mul_assoc] using hconj (-c) _ hy

/-- A generator `x_{ab}(c)`, for distinct `a, b` both different from `t`, normalizes the row root
subgroup at `t`. -/
theorem x_mem_normalizer_range_rowHom {a b : ι} (hab : a ≠ b) (hat : a ≠ t) (hbt : b ≠ t)
    (c : R) :
    x hab c ∈
      Subgroup.normalizer ((rowHom (R := R) t).range : Set (IndexedSteinbergGroup ι R)) := by
  have hconj : ∀ (c : R) (y : IndexedSteinbergGroup ι R), y ∈ (rowHom t).range →
      x hab c * y * (x hab c)⁻¹ ∈ (rowHom t).range := by
    rintro c _ ⟨v, rfl⟩
    exact ⟨_, (x_mul_rowHom_mul_inv hab hat hbt c v.toAdd).symm⟩
  refine Subgroup.mem_normalizer_iff.mpr fun y ↦ ⟨hconj c y, fun hy ↦ ?_⟩
  simpa [← x_inv, mul_assoc] using hconj (-c) _ hy

/-! ### Functoriality -/

/-- A ring homomorphism acts on column elements entrywise. -/
@[simp]
theorem map_colHom (f : R →+* S) (v : {i // i ≠ t} → R) :
    map f (colHom t (Multiplicative.ofAdd v)) =
      colHom t (Multiplicative.ofAdd fun i ↦ f (v i)) := by
  induction v using Pi.single_induction with
  | zero =>
    simp only [ofAdd_zero, map_one, Pi.zero_apply, map_zero]
    exact (map_one _).symm
  | add v w hv hw =>
    rw [ofAdd_add, map_mul, map_mul, hv, hw, ← map_mul, ← ofAdd_add]
    congr 2
    funext i
    exact (map_add f _ _).symm
  | single i r =>
    rw [colHom_ofAdd_single, map_x, ← colHom_ofAdd_single]
    congr
    funext j
    exact (Pi.apply_single (fun _ ↦ f) (fun _ ↦ map_zero f) i r j).symm

/-- A ring homomorphism acts on row elements entrywise. -/
@[simp]
theorem map_rowHom (f : R →+* S) (v : {i // i ≠ t} → R) :
    map f (rowHom t (Multiplicative.ofAdd v)) =
      rowHom t (Multiplicative.ofAdd fun i ↦ f (v i)) := by
  induction v using Pi.single_induction with
  | zero =>
    simp only [ofAdd_zero, map_one, Pi.zero_apply, map_zero]
    exact (map_one _).symm
  | add v w hv hw =>
    rw [ofAdd_add, map_mul, map_mul, hv, hw, ← map_mul, ← ofAdd_add]
    congr 2
    funext i
    exact (map_add f _ _).symm
  | single i r =>
    rw [rowHom_ofAdd_single, map_x, ← rowHom_ofAdd_single]
    congr
    funext j
    exact (Pi.apply_single (fun _ ↦ f) (fun _ ↦ map_zero f) i r j).symm

/-- The opposite-ring inverse-transpose isomorphism turns a column element into the row element
of the negated vector in `Rᵐᵒᵖ`. -/
@[simp]
theorem transposeOp_colHom (v : {i // i ≠ t} → R) :
    transposeOp (colHom t (Multiplicative.ofAdd v)) =
      rowHom t (Multiplicative.ofAdd fun i ↦ MulOpposite.op (-v i)) := by
  induction v using Pi.single_induction with
  | zero =>
    simp only [ofAdd_zero, map_one, Pi.zero_apply, neg_zero, MulOpposite.op_zero]
    exact (map_one _).symm
  | add v w hv hw =>
    rw [ofAdd_add, map_mul, map_mul, hv, hw, ← map_mul, ← ofAdd_add]
    congr 2
    funext i
    rw [Pi.add_apply, Pi.add_apply, neg_add, MulOpposite.op_add]
  | single i r =>
    rw [colHom_ofAdd_single, transposeOp_x, ← rowHom_ofAdd_single]
    congr
    funext j
    exact (Pi.apply_single (fun _ s ↦ MulOpposite.op (-s)) (fun _ ↦ by simp) i r j).symm

/-- The opposite-ring inverse-transpose isomorphism turns a row element into the column element
of the negated vector in `Rᵐᵒᵖ`. -/
@[simp]
theorem transposeOp_rowHom (v : {i // i ≠ t} → R) :
    transposeOp (rowHom t (Multiplicative.ofAdd v)) =
      colHom t (Multiplicative.ofAdd fun i ↦ MulOpposite.op (-v i)) := by
  induction v using Pi.single_induction with
  | zero =>
    simp only [ofAdd_zero, map_one, Pi.zero_apply, neg_zero, MulOpposite.op_zero]
    exact (map_one _).symm
  | add v w hv hw =>
    rw [ofAdd_add, map_mul, map_mul, hv, hw, ← map_mul, ← ofAdd_add]
    congr 2
    funext i
    rw [Pi.add_apply, Pi.add_apply, neg_add, MulOpposite.op_add]
  | single i r =>
    rw [rowHom_ofAdd_single, transposeOp_x, ← colHom_ofAdd_single]
    congr
    funext j
    exact (Pi.apply_single (fun _ s ↦ MulOpposite.op (-s)) (fun _ ↦ by simp) i r j).symm

variable [Fintype κ] [DecidableEq κ]

/-- Along an embedding `e : ι ↪ κ` of index types, a column element at `t` maps to the column
element at `e t` of the vector extended by zero. -/
@[simp]
theorem mapIndex_colHom (e : ι ↪ κ) (v : {i // i ≠ t} → R) :
    mapIndex e (colHom t (Multiplicative.ofAdd v)) =
      colHom (e t) (Multiplicative.ofAdd (Function.extend
        (Subtype.map (p := (· ≠ t)) (q := (· ≠ e t)) e fun _ ↦ e.injective.ne) v 0)) := by
  have he := Subtype.map_injective (p := (· ≠ t)) (q := (· ≠ e t)) (fun _ ↦ e.injective.ne)
    e.injective
  induction v using Pi.single_induction with
  | zero => simp
  | add v w hv hw =>
    rw [ofAdd_add, map_mul, map_mul, hv, hw, ← map_mul, ← ofAdd_add, ← Function.extend_add,
      add_zero]
  | single i r =>
    rw [colHom_ofAdd_single, mapIndex_x, he.extend_single, colHom_ofAdd_single]
    simp only [Subtype.map_coe]

/-- Along an embedding `e : ι ↪ κ` of index types, a row element at `t` maps to the row element at
`e t` of the vector extended by zero. -/
@[simp]
theorem mapIndex_rowHom (e : ι ↪ κ) (v : {i // i ≠ t} → R) :
    mapIndex e (rowHom t (Multiplicative.ofAdd v)) =
      rowHom (e t) (Multiplicative.ofAdd (Function.extend
        (Subtype.map (p := (· ≠ t)) (q := (· ≠ e t)) e fun _ ↦ e.injective.ne) v 0)) := by
  have he := Subtype.map_injective (p := (· ≠ t)) (q := (· ≠ e t)) (fun _ ↦ e.injective.ne)
    e.injective
  induction v using Pi.single_induction with
  | zero => simp
  | add v w hv hw =>
    rw [ofAdd_add, map_mul, map_mul, hv, hw, ← map_mul, ← ofAdd_add, ← Function.extend_add,
      add_zero]
  | single i r =>
    rw [rowHom_ofAdd_single, mapIndex_x, he.extend_single, rowHom_ofAdd_single]
    simp only [Subtype.map_coe]

end Hom

end IndexedSteinbergGroup

namespace SteinbergGroup

variable {R : Type*} [Ring R]

open IndexedSteinbergGroup

/-- The column root subgroup of `Stₙ(R)` maps faithfully to the stable Steinberg group `St(R)`. -/
theorem ofFin_comp_colHom_injective {n : ℕ} (t : Fin n) :
    Function.Injective ((ofFin R n).comp (colHom t)) := by
  intro v w h
  apply toGL_comp_colHom_injective t
  apply StableGeneralLinearGroup.of_injective n
  simpa using congrArg (toStableGL R) h

/-- The row root subgroup of `Stₙ(R)` maps faithfully to the stable Steinberg group `St(R)`. -/
theorem ofFin_comp_rowHom_injective {n : ℕ} (t : Fin n) :
    Function.Injective ((ofFin R n).comp (rowHom t)) := by
  intro v w h
  apply toGL_comp_rowHom_injective t
  apply StableGeneralLinearGroup.of_injective n
  simpa using congrArg (toStableGL R) h

end SteinbergGroup

end TauCeti
