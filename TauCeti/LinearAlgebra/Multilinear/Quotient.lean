/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Multilinear.Basic
public import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Multilinear maps on quotient modules

A multilinear map on finitely many modules descends to their quotients if it vanishes
whenever one argument belongs to the submodule being divided out. `MultilinearMap.liftQ`
constructs the descended map, characterized by evaluation on quotient classes.
This permits tensor constructions with different quotient modules in different slots.
-/

public section

namespace MultilinearMap

variable {R ι : Type*} [Ring R] [Finite ι]
  {M : ι → Type*} [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
  {P : Type*} [AddCommMonoid P] [Module R P]

/-- A multilinear map killing a submodule in each slot takes the same value on tuples
representing the same quotient classes. -/
theorem apply_eq_of_mkQ_eq (f : MultilinearMap R M P) (N : ∀ i, Submodule R (M i))
    (hf : ∀ [DecidableEq ι] (m : ∀ i, M i) (i : ι) (x : M i),
      x ∈ N i → f (Function.update m i x) = 0)
    {a b : ∀ i, M i} (h : ∀ i, (N i).mkQ (a i) = (N i).mkQ (b i)) : f a = f b := by
  classical
  let := Fintype.ofFinite ι
  have hab (i : ι) : a i - b i ∈ N i := (Submodule.Quotient.eq _).mp (h i)
  have heq : a = (a - b) + b := by simp
  rw [heq, f.map_add_univ, Finset.sum_eq_single ∅]
  · simp
  · intro s _ hs
    obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.mpr hs
    have hi' : (s.piecewise (a - b) b) i = a i - b i :=
      Finset.piecewise_eq_of_mem s (a - b) b hi
    simpa only [← hi', Function.update_eq_self] using
      hf (s.piecewise (a - b) b) i (a i - b i) (hab i)
  · simp

/-- Descend a multilinear map to a family of quotient modules. The hypothesis requires
vanishing when any one coordinate belongs to its prescribed submodule. -/
noncomputable def liftQ (f : MultilinearMap R M P) (N : ∀ i, Submodule R (M i))
    (hf : ∀ [DecidableEq ι] (m : ∀ i, M i) (i : ι) (x : M i),
      x ∈ N i → f (Function.update m i x) = 0) :
    MultilinearMap R (fun i ↦ M i ⧸ N i) P where
  toFun m := f (fun i ↦ (m i).out)
  map_update_add' m i x y := by
    classical
    have h (z : M i ⧸ N i) :
        f (fun j ↦ (Function.update m i z j).out) =
          f (Function.update (fun j ↦ (m j).out) i z.out) := by
      apply f.apply_eq_of_mkQ_eq N hf
      intro j
      by_cases hj : j = i
      · subst j; simp [Submodule.Quotient.mk_out]
      · simp [Function.update_of_ne hj]
    rw [h]
    have hxy : f (Function.update (fun j ↦ (m j).out) i (x + y).out) =
        f (Function.update (fun j ↦ (m j).out) i (x.out + y.out)) := by
      apply f.apply_eq_of_mkQ_eq N hf
      intro j
      by_cases hj : j = i
      · subst j; simp [Submodule.Quotient.mk_out]
      · simp [Function.update_of_ne hj]
    rw [hxy, f.map_update_add, h, h]
  map_update_smul' m i c x := by
    classical
    have h : f (fun j ↦ (Function.update m i (c • x) j).out) =
        f (Function.update (fun j ↦ (m j).out) i (c • x.out)) := by
      apply f.apply_eq_of_mkQ_eq N hf
      intro j
      by_cases hj : j = i
      · subst j; simp [Submodule.Quotient.mk_out]
      · simp [Function.update_of_ne hj]
    rw [h, f.map_update_smul]
    congr 1
    apply f.apply_eq_of_mkQ_eq N hf
    intro j
    by_cases hj : j = i
    · subst j; simp [Submodule.Quotient.mk_out]
    · simp [Function.update_of_ne hj]

/-- Evaluation of the descended multilinear map on quotient classes. -/
@[simp]
theorem liftQ_apply (f : MultilinearMap R M P) (N : ∀ i, Submodule R (M i))
    (hf : ∀ [DecidableEq ι] (m : ∀ i, M i) (i : ι) (x : M i),
      x ∈ N i → f (Function.update m i x) = 0) (m : ∀ i, M i) :
    f.liftQ N hf (fun i ↦ Submodule.Quotient.mk (m i)) = f m := by
  dsimp only [liftQ]
  apply f.apply_eq_of_mkQ_eq N hf
  intro i
  exact Submodule.Quotient.mk_out _

/-- A descended multilinear map is uniquely determined by evaluation on quotient classes. -/
theorem liftQ_unique (f : MultilinearMap R M P) (N : ∀ i, Submodule R (M i))
    (hf : ∀ [DecidableEq ι] (m : ∀ i, M i) (i : ι) (x : M i),
      x ∈ N i → f (Function.update m i x) = 0)
    (g : MultilinearMap R (fun i ↦ M i ⧸ N i) P)
    (hg : g.compLinearMap (fun i ↦ (N i).mkQ) = f) : g = f.liftQ N hf := by
  apply compLinearMap_injective (fun i ↦ (N i).mkQ) (fun i ↦ (N i).mkQ_surjective)
  ext m
  simpa only [compLinearMap_apply, Submodule.mkQ_apply, liftQ_apply] using
    congrArg (fun h ↦ h m) hg

end MultilinearMap
