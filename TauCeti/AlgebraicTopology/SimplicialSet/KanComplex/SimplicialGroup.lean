/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.KanComplex
public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.Algebra.Category.ModuleCat.Basic

/-!
# Simplicial groups are Kan complexes

A simplicial set whose sets of simplices are groups, with all simplicial operators group
homomorphisms, is a Kan complex (`SSet.kanComplex_of_group`, Moore's theorem). Hence the
underlying simplicial set of a simplicial group, of a simplicial abelian group and of a
simplicial module is a Kan complex.

This is what makes the combinatorial homotopy theory of simplicial groups available, and it is
the Kan property of the mapping spaces of simplicial categories built from simplicial abelian
groups, such as the Dold–Kan images of connective chain complexes.

## Proof

By `SSet.KanComplex.iff`, a horn `Λ[n + 1, i] ⟶ X` is a compatible family of `n`-simplices
`y j`, one for each face `j ≠ i`. The filler is built by correcting faces one at a time. Below
`i`, from the bottom up: if `w` already has the faces `y j` for `j < r`, then
`w * σ r ((d r w)⁻¹ * y r)` also has the face `y r`, since the correction is the degeneracy of a
simplex whose faces below `r` are trivial by compatibility. Above `i`, from the top down: if
`w` has the faces `y j` for `j < i` and `j > r`, then `w * σ (r - 1) ((d r w)⁻¹ * y r)` also has
the face `y r`, by the same argument.

## Main results

* `SSet.kanComplex_of_group`, `SSet.kanComplex_of_addGroup`: Moore's theorem for simplicial
  sets with group and with additive group structures.
* `CategoryTheory.SimplicialObject.kanComplex_comp_forget_grpCat`,
  `CategoryTheory.SimplicialObject.kanComplex_comp_forget_addCommGrpCat` and
  `CategoryTheory.SimplicialObject.kanComplex_comp_forget_moduleCat`: the underlying simplicial
  sets of simplicial groups, simplicial abelian groups and simplicial modules are Kan complexes.

## References

* J. C. Moore, *Homotopie des complexes monoïdaux, I*, Séminaire Henri Cartan 7 (1954–1955).
* J. P. May, *Simplicial Objects in Algebraic Topology*, Theorem 17.1.
* P. G. Goerss and J. F. Jardine, *Simplicial Homotopy Theory*, Lemma I.3.4.
-/

public section

universe u

open CategoryTheory Simplicial

namespace SSet

/-! ### Simplicial identities with indices given by their values

These restate Mathlib's simplicial identities with the indices given by their values, so that
the inductive steps below can name indices such as `j - 1` directly. -/

section Identities

variable {X : SSet.{u}} {n : ℕ}

private lemma δ_σ_of_lt (a : Fin (n + 3)) (b : Fin (n + 2)) (a' : Fin (n + 2)) (b' : Fin (n + 1))
    (hab : a.val < b.val) (ha' : a'.val = a.val) (hb' : b'.val + 1 = b.val) (x : X _⦋n + 1⦌) :
    X.δ a (X.σ b x) = X.σ b' (X.δ a' x) := by
  obtain rfl : a = a'.castSucc := Fin.ext ha'.symm
  obtain rfl : b = b'.succ := Fin.ext (by simpa using hb'.symm)
  exact δ_comp_σ_of_le_apply (by rw [Fin.le_def]; simp at hab ⊢; omega) x

private lemma δ_σ_of_gt (a : Fin (n + 3)) (b : Fin (n + 2)) (a' : Fin (n + 2)) (b' : Fin (n + 1))
    (hab : b.val + 1 < a.val) (ha' : a'.val + 1 = a.val) (hb' : b'.val = b.val) (x : X _⦋n + 1⦌) :
    X.δ a (X.σ b x) = X.σ b' (X.δ a' x) := by
  obtain rfl : a = a'.succ := Fin.ext (by simpa using ha'.symm)
  obtain rfl : b = b'.castSucc := Fin.ext hb'.symm
  exact δ_comp_σ_of_gt_apply (by rw [Fin.lt_def]; simp at hab ⊢; omega) x

private lemma δ_δ_of_lt (a b : Fin (n + 3)) (a' b' : Fin (n + 2)) (hab : a.val < b.val)
    (ha' : a'.val = a.val) (hb' : b'.val + 1 = b.val) (x : X _⦋n + 2⦌) :
    X.δ a' (X.δ b x) = X.δ b' (X.δ a x) := by
  obtain rfl : a = a'.castSucc := Fin.ext ha'.symm
  obtain rfl : b = b'.succ := Fin.ext (by simpa using hb'.symm)
  exact δ_comp_δ_apply (by rw [Fin.le_def]; simp at hab ⊢; omega) x

end Identities

section Group

variable {X : SSet.{u}} [∀ n, Group (X.obj n)]
  (hX : ∀ ⦃m n : SimplexCategoryᵒᵖ⦄ (f : m ⟶ n) (x y : X.obj m),
    X.map f (x * y) = X.map f x * X.map f y)

include hX

private lemma δ_mul {n : ℕ} (j : Fin (n + 2)) (x y : X _⦋n + 1⦌) :
    X.δ j (x * y) = X.δ j x * X.δ j y :=
  hX _ x y

private lemma δ_inv {n : ℕ} (j : Fin (n + 2)) (x : X _⦋n + 1⦌) : X.δ j x⁻¹ = (X.δ j x)⁻¹ :=
  map_inv (MonoidHom.mk' (fun x => X.δ j x) (δ_mul hX j)) x

private lemma σ_one {n : ℕ} (j : Fin (n + 1)) : X.σ j (1 : X _⦋n⦌) = 1 :=
  map_one (MonoidHom.mk' (fun x => X.σ j x) (hX _))

/-- Multiplying `w` by the degeneracy `σ b ((δ k w)⁻¹ * v)` does not change its `a`-th face,
when `δ a` turns `σ b` into `σ b'` after the face `δ a'`, and `δ k w` and `v` have the same
`a'`-th face. -/
private lemma δ_mul_σ_inv_mul {n : ℕ} {a k : Fin (n + 3)} {b a' : Fin (n + 2)} {b' : Fin (n + 1)}
    (hσ : ∀ x : X _⦋n + 1⦌, X.δ a (X.σ b x) = X.σ b' (X.δ a' x)) {w : X _⦋n + 2⦌}
    {v : X _⦋n + 1⦌} (hv : X.δ a' (X.δ k w) = X.δ a' v) :
    X.δ a (w * X.σ b ((X.δ k w)⁻¹ * v)) = X.δ a w := by
  simp [δ_mul hX, δ_inv hX, hσ, hv, σ_one hX]

variable {m : ℕ} {i : Fin (m + 3)} {y : ∀ j : Fin (m + 3), j ≠ i → X _⦋m + 1⦌}
  (hy : ∀ (j k : Fin (m + 3)) (hj : j ≠ i) (hk : k ≠ i) (p q : Fin (m + 2)), j.val < k.val →
    p.val + 1 = k.val → q.val = j.val → X.δ p (y j hj) = X.δ q (y k hk))

include hy

/-- Correcting the face `b.castSucc < i` by multiplying with a degenerate simplex keeps the faces
below it. -/
private lemma exists_lower_step (b : Fin (m + 2)) (hbi : b.castSucc ≠ i)
    (w : X _⦋m + 2⦌) (hw : ∀ (j : Fin (m + 3)) (hj : j ≠ i), j.val < b.val → X.δ j w = y j hj) :
    ∃ w' : X _⦋m + 2⦌, ∀ (j : Fin (m + 3)) (hj : j ≠ i), j.val ≤ b.val → X.δ j w' = y j hj := by
  refine ⟨w * X.σ b ((X.δ b.castSucc w)⁻¹ * y b.castSucc hbi), fun j hj hjb => ?_⟩
  rcases lt_or_eq_of_le hjb with hjb | hjb
  · -- Below `b`, the correction is the degeneracy of a simplex with trivial `j`-th face.
    have hb₁ : b.val - 1 + 1 < m + 2 := by omega
    rw [δ_mul_σ_inv_mul hX
      (δ_σ_of_lt j b ⟨j.val, by omega⟩ ⟨b.val - 1, by omega⟩ hjb rfl (by simp; omega)) ?_,
      hw j hj hjb]
    rw [δ_δ_of_lt j b.castSucc ⟨j.val, by omega⟩ ⟨b.val - 1, by omega⟩ hjb rfl (by simp; omega),
      hw j hj hjb]
    exact hy j b.castSucc hj hbi ⟨b.val - 1, by omega⟩ ⟨j.val, by omega⟩ hjb (by simp; omega) rfl
  · obtain rfl : j = b.castSucc := Fin.ext hjb
    rw [δ_mul hX, δ_comp_σ_self_apply, mul_inv_cancel_left]

/-- Correcting the face `b.succ > i` by multiplying with a degenerate simplex keeps the faces
below `i` and above `b.succ`. -/
private lemma exists_upper_step (b : Fin (m + 2)) (hbi : b.succ ≠ i) (hb : i.val ≤ b.val)
    (w : X _⦋m + 2⦌) (hlow : ∀ (j : Fin (m + 3)) (hj : j ≠ i), j.val < i.val → X.δ j w = y j hj)
    (hup : ∀ (j : Fin (m + 3)) (hj : j ≠ i), b.val + 1 < j.val → X.δ j w = y j hj) :
    ∃ w' : X _⦋m + 2⦌, (∀ (j : Fin (m + 3)) (hj : j ≠ i), j.val < i.val → X.δ j w' = y j hj) ∧
      ∀ (j : Fin (m + 3)) (hj : j ≠ i), b.val < j.val → X.δ j w' = y j hj := by
  refine ⟨w * X.σ b ((X.δ b.succ w)⁻¹ * y b.succ hbi), fun j hj hji => ?_, fun j hj hbj => ?_⟩
  · -- Below `i`, the correction is the degeneracy of a simplex with trivial `j`-th face.
    have hjb : j.val < b.val := by omega
    rw [δ_mul_σ_inv_mul hX
      (δ_σ_of_lt j b ⟨j.val, by omega⟩ ⟨b.val - 1, by omega⟩ hjb rfl (by simp; omega)) ?_,
      hlow j hj hji]
    rw [δ_δ_of_lt j b.succ ⟨j.val, by omega⟩ b (by simp; omega) rfl (by simp), hlow j hj hji]
    exact hy j b.succ hj hbi b ⟨j.val, by omega⟩ (by simp; omega) (by simp) rfl
  · rcases lt_or_eq_of_le (Nat.succ_le_of_lt hbj) with hbj | hbj
    · -- Above `b.succ`, the correction is the degeneracy of a simplex with trivial face.
      rw [δ_mul_σ_inv_mul hX
        (δ_σ_of_gt j b ⟨j.val - 1, by omega⟩ ⟨b.val, by omega⟩ hbj (by simp; omega) rfl) ?_,
        hup j hj hbj]
      rw [← δ_δ_of_lt b.succ j ⟨b.val + 1, by omega⟩ ⟨j.val - 1, by omega⟩ (by simpa using hbj)
        (by simp) (by simp; omega), hup j hj hbj]
      exact (hy b.succ j hbi hj ⟨j.val - 1, by omega⟩ ⟨b.val + 1, by omega⟩
        (by simpa using hbj) (by simp; omega) (by simp)).symm
    · obtain rfl : j = b.succ := Fin.ext (by simpa using hbj.symm)
      rw [δ_mul hX, δ_comp_σ_succ_apply, mul_inv_cancel_left]

/-- **Horn filling in a simplicial group**: a compatible family of `m + 1`-simplices on the faces
`j ≠ i` of an `(m + 2)`-simplex is the family of faces of an `(m + 2)`-simplex. -/
private lemma exists_δ_eq_of_group : ∃ w : X _⦋m + 2⦌, ∀ (j : Fin (m + 3)) (hj : j ≠ i),
    X.δ j w = y j hj := by
  -- First correct the faces below `i`, from the bottom up.
  have hlow : ∀ r ≤ i.val, ∃ w : X _⦋m + 2⦌, ∀ (j : Fin (m + 3)) (hj : j ≠ i), j.val < r →
      X.δ j w = y j hj := by
    intro r
    induction r with
    | zero => exact fun _ => ⟨1, fun j _ hj => absurd hj (Nat.not_lt_zero _)⟩
    | succ r ih =>
      intro hr
      obtain ⟨w, hw⟩ := ih (by omega)
      obtain ⟨w', hw'⟩ := exists_lower_step hX hy ⟨r, by omega⟩
        (Fin.ne_of_val_ne (by simp; omega)) w hw
      exact ⟨w', fun j hj hjr => hw' j hj (by simp; omega)⟩
  -- Then correct the faces above `i`, from the top down.
  have hup : ∀ t ≤ m + 2 - i.val, ∃ w : X _⦋m + 2⦌,
      (∀ (j : Fin (m + 3)) (hj : j ≠ i), j.val < i.val → X.δ j w = y j hj) ∧
      ∀ (j : Fin (m + 3)) (hj : j ≠ i), m + 2 - t < j.val → X.δ j w = y j hj := by
    intro t
    induction t with
    | zero =>
      intro _
      obtain ⟨w, hw⟩ := hlow i.val le_rfl
      exact ⟨w, hw, fun j _ hj => absurd hj (by omega)⟩
    | succ t ih =>
      intro ht
      obtain ⟨w, hw, hw'⟩ := ih (by omega)
      obtain ⟨w', hw₁, hw₂⟩ := exists_upper_step hX hy ⟨m + 1 - t, by omega⟩
        (Fin.ne_of_val_ne (by simp; omega)) (by simp; omega) w hw
        (fun j hj hjt => hw' j hj (by simp at hjt; omega))
      exact ⟨w', hw₁, fun j hj hjt => hw₂ j hj (by simp; omega)⟩
  obtain ⟨w, hw, hw'⟩ := hup (m + 2 - i.val) le_rfl
  refine ⟨w, fun j hj => ?_⟩
  rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hj) with h | h
  · exact hw j hj h
  · exact hw' j hj (by omega)

omit hy in
/-- **Moore's theorem**: a simplicial set whose sets of simplices are groups, with simplicial
operators group homomorphisms, is a Kan complex. -/
theorem kanComplex_of_group : X.KanComplex := by
  rw [KanComplex.iff]
  intro n i f hf
  suffices h : ∃ x : X _⦋n + 1⦌, ∀ (j : Fin (n + 2)) (hj : j ≠ i), X.δ j x = yonedaEquiv (f j hj) by
    obtain ⟨x, hx⟩ := h
    refine ⟨yonedaEquiv.symm x, fun j hj => ?_⟩
    rw [stdSimplex.δ_comp_yonedaEquiv_symm, hx, Equiv.symm_apply_apply]
  cases n with
  | zero =>
    -- A one-dimensional horn is a single vertex, filled by its degenerate edge.
    obtain rfl | rfl := Fin.exists_fin_two.mp ⟨i, rfl⟩
    · refine ⟨X.σ 0 (yonedaEquiv (f 1 (by decide))), fun j hj => ?_⟩
      obtain rfl | rfl := Fin.exists_fin_two.mp ⟨j, rfl⟩
      · exact absurd rfl hj
      · exact δ_comp_σ_succ_apply 0 _
    · refine ⟨X.σ 0 (yonedaEquiv (f 0 (by decide))), fun j hj => ?_⟩
      obtain rfl | rfl := Fin.exists_fin_two.mp ⟨j, rfl⟩
      · exact δ_comp_σ_self_apply 0 _
      · exact absurd rfl hj
  | succ m =>
    refine exists_δ_eq_of_group hX (fun j k hj hk p q hjk hp hq => ?_)
    obtain rfl : p = k.pred (Fin.ne_zero_of_lt (Fin.lt_def.mpr hjk)) :=
      Fin.ext (by simp; omega)
    obtain rfl : q = j.castPred (Fin.ne_last_of_lt (Fin.lt_def.mpr hjk)) := Fin.ext (by simpa)
    have := congrArg yonedaEquiv (hf.δ_pred_comp j k hj hk (Fin.lt_def.mpr hjk))
    rwa [stdSimplex.yonedaEquiv_δ_comp, stdSimplex.yonedaEquiv_δ_comp] at this

end Group

/-- **Moore's theorem** for additive groups: a simplicial set whose sets of simplices are additive
groups, with simplicial operators additive, is a Kan complex. -/
theorem kanComplex_of_addGroup {X : SSet.{u}} [∀ n, AddGroup (X.obj n)]
    (hX : ∀ ⦃m n : SimplexCategoryᵒᵖ⦄ (f : m ⟶ n) (x y : X.obj m),
      X.map f (x + y) = X.map f x + X.map f y) :
    X.KanComplex :=
  letI : ∀ n, Group (X.obj n) := fun n => (inferInstance : Group (Multiplicative (X.obj n)))
  kanComplex_of_group fun _ _ f x y => hX f x y

end SSet

namespace CategoryTheory.SimplicialObject

/-- The underlying simplicial set of a simplicial group is a Kan complex. -/
instance kanComplex_comp_forget_grpCat (G : SimplicialObject GrpCat.{u}) :
    SSet.KanComplex (G ⋙ forget GrpCat) :=
  letI (n : SimplexCategoryᵒᵖ) : Group ((G ⋙ forget GrpCat).obj n) :=
    inferInstanceAs (Group (G.obj n))
  SSet.kanComplex_of_group (X := G ⋙ forget GrpCat) fun _ _ f x y => map_mul (G.map f).hom x y

/-- The underlying simplicial set of a simplicial abelian group is a Kan complex. -/
instance kanComplex_comp_forget_addCommGrpCat (G : SimplicialObject AddCommGrpCat.{u}) :
    SSet.KanComplex (G ⋙ forget AddCommGrpCat) :=
  letI (n : SimplexCategoryᵒᵖ) : AddGroup ((G ⋙ forget AddCommGrpCat).obj n) :=
    inferInstanceAs (AddGroup (G.obj n))
  SSet.kanComplex_of_addGroup (X := G ⋙ forget AddCommGrpCat) fun _ _ f x y =>
    map_add (G.map f).hom x y

/-- The underlying simplicial set of a simplicial module is a Kan complex. -/
instance kanComplex_comp_forget_moduleCat {R : Type*} [Ring R]
    (G : SimplicialObject (ModuleCat.{u} R)) : SSet.KanComplex (G ⋙ forget (ModuleCat R)) :=
  letI (n : SimplexCategoryᵒᵖ) : AddGroup ((G ⋙ forget (ModuleCat R)).obj n) :=
    inferInstanceAs (AddGroup (G.obj n))
  SSet.kanComplex_of_addGroup (X := G ⋙ forget (ModuleCat R)) fun _ _ f x y =>
    map_add (G.map f).hom x y

end CategoryTheory.SimplicialObject
