/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.GroupWithZero.Action
public import Mathlib.Algebra.BigOperators.NatAntidiagonal
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import TauCeti.Algebra.Homology.TotalComplex
public import TauCeti.AlgebraicTopology.SimplexCategory.Subinterval

/-!
# The diagonal and the Alexander–Whitney map of a bisimplicial object

A bisimplicial object in `C` is a simplicial object `X` in `SimplicialObject C`; its `(p, q)`
term is `(X _⦋p⦌) _⦋q⦌`.  It has two chain-level shadows.

* The **diagonal** `CategoryTheory.SimplicialObject.diag`, the simplicial object
  `⦋n⦌ ↦ (X _⦋n⦌) _⦋n⦌`, on which a map of `SimplexCategory` acts in both directions at once.
  (This is unrelated to `CategoryTheory.SimplicialObject.diagonal`, the long-edge map of a single
  simplicial object.)
* The **double complex** `CategoryTheory.SimplicialObject.doubleComplex`, obtained by taking the
  alternating face map complex in the outer direction and then in the inner one.  Its total
  complex for `ComplexShape.down ℕ` has the differential `d₁ + (-1)^p d₂` on the term of bidegree
  `(p, q)`, with `d₁` the outer and `d₂` the inner alternating face map differential.

The **Alexander–Whitney map** `CategoryTheory.SimplicialObject.diagAlexanderWhitney` is the
morphism of chain complexes from the alternating face map complex of the diagonal to this total
complex which in degree `n` is the sum over `p + q = n` of the maps
`(X _⦋n⦌) _⦋n⦌ ⟶ (X _⦋p⦌) _⦋q⦌` given by the front `p`-face `0, …, p` in the outer direction and
the back `q`-face `p, …, n` in the inner direction.  It is natural in `X`.

For two simplicial objects `A` and `B` of a monoidal category, the bisimplicial object
`(p, q) ↦ A _⦋p⦌ ⊗ B _⦋q⦌` has the degreewise tensor product as its diagonal and the tensor
product of the alternating face map complexes as its total complex; the components of this map
are then those of the classical Alexander–Whitney map
`CategoryTheory.SimplicialObject.alexanderWhitney`.

The generalized Eilenberg–Zilber theorem of Dold and Puppe says that the Alexander–Whitney
map is a chain homotopy equivalence, with homotopy inverse the shuffle map.  This comparison of
the chains on the diagonal with the total complex is what identifies the cohomology of the
diagonal of a bisimplicial set, such as the levelwise singular complex of a simplicial space,
with the abutment of the spectral sequence of its double complex.

## Main definitions and results

* `CategoryTheory.SimplicialObject.diag`: the diagonal of a bisimplicial object, as a functor.
* `CategoryTheory.SimplicialObject.doubleComplex`: the double complex of a bisimplicial object, as
  a functor, with its differentials described by
  `CategoryTheory.SimplicialObject.doubleComplex_obj_d_f` and
  `CategoryTheory.SimplicialObject.doubleComplex_obj_X_d`.
* `CategoryTheory.SimplicialObject.diagAlexanderWhitney`: the Alexander–Whitney chain map, with
  components `CategoryTheory.SimplicialObject.diagAlexanderWhitney_f` and naturality
  `CategoryTheory.SimplicialObject.diagAlexanderWhitney_naturality`.

## References

* A. Dold and D. Puppe, *Homologie nicht-additiver Funktoren. Anwendungen*, Ann. Inst. Fourier 11
  (1961).
* P. G. Goerss and J. F. Jardine, *Simplicial homotopy theory*, Section IV.2.
-/

public section

noncomputable section

open CategoryTheory Limits Opposite AlgebraicTopology

open scoped Simplicial

universe v u

namespace CategoryTheory.SimplicialObject

variable (C : Type u) [Category.{v} C]

/-- The diagonal `⦋n⦌ ↦ (X _⦋n⦌) _⦋n⦌` of a bisimplicial object `X`, on which a map of
`SimplexCategory` acts in both directions at once. -/
@[expose, simps]
def diag : SimplicialObject (SimplicialObject C) ⥤ SimplicialObject C where
  obj X :=
    { obj n := (X.obj n).obj n
      map f := (X.map f).app _ ≫ (X.obj _).map f
      map_id n := by simp
      map_comp f g := by simp [NatTrans.naturality_assoc] }
  map φ :=
    { app n := (φ.app n).app n
      naturality n m f := by
        dsimp
        rw [Category.assoc, NatTrans.naturality, ← Category.assoc, ← NatTrans.comp_app,
          φ.naturality, NatTrans.comp_app, Category.assoc] }

variable {C}

/-- The faces of the diagonal are the faces in the two directions at once. -/
@[simp]
lemma diag_obj_δ (X : SimplicialObject (SimplicialObject C)) {n : ℕ} (i : Fin (n + 2)) :
    ((diag C).obj X).δ i = (X.δ i).app (op ⦋n + 1⦌) ≫ (X _⦋n⦌).δ i :=
  (rfl)

variable (X : SimplicialObject (SimplicialObject C))

/-- The map `(X _⦋n⦌) _⦋m⦌ ⟶ (X _⦋p⦌) _⦋q⦌` induced by `f` in the outer and `g` in the inner
direction. -/
private def bimap {n m p q : ℕ} (f : ⦋p⦌ ⟶ ⦋n⦌) (g : ⦋q⦌ ⟶ ⦋m⦌) :
    (X _⦋n⦌) _⦋m⦌ ⟶ (X _⦋p⦌) _⦋q⦌ :=
  (X.map f.op).app _ ≫ (X _⦋p⦌).map g.op

@[reassoc]
private lemma bimap_comp {n m p q p' q' : ℕ} (f : ⦋p⦌ ⟶ ⦋n⦌) (g : ⦋q⦌ ⟶ ⦋m⦌)
    (f' : ⦋p'⦌ ⟶ ⦋p⦌) (g' : ⦋q'⦌ ⟶ ⦋q⦌) :
    bimap X f g ≫ bimap X f' g' = bimap X (f' ≫ f) (g' ≫ g) := by
  simp only [bimap, Category.assoc, ← NatTrans.naturality_assoc, op_comp, Functor.map_comp,
    NatTrans.comp_app]

private lemma δ_app_eq_bimap {p : ℕ} (i : Fin (p + 2)) (q : ℕ) :
    (X.δ i).app (op ⦋q⦌) = bimap X (SimplexCategory.δ i) (𝟙 ⦋q⦌) := by
  simp [bimap, SimplicialObject.δ]

private lemma δ_eq_bimap (p : ℕ) {q : ℕ} (j : Fin (q + 2)) :
    (X _⦋p⦌).δ j = bimap X (𝟙 ⦋p⦌) (SimplexCategory.δ j) := by
  simp [bimap, SimplicialObject.δ]

/-- The map induced in both directions by a morphism of bisimplicial objects commutes with the
maps induced by maps of `SimplexCategory`. -/
@[reassoc]
private lemma app_app_comp_bimap {X Y : SimplicialObject (SimplicialObject C)} (φ : X ⟶ Y)
    {n m p q : ℕ} (f : ⦋p⦌ ⟶ ⦋n⦌) (g : ⦋q⦌ ⟶ ⦋m⦌) :
    (φ.app (op ⦋n⦌)).app (op ⦋m⦌) ≫ bimap Y f g =
      bimap X f g ≫ (φ.app (op ⦋p⦌)).app (op ⦋q⦌) := by
  rw [bimap, bimap, ← NatTrans.comp_app_assoc, ← φ.naturality, NatTrans.comp_app_assoc,
    ← NatTrans.naturality, Category.assoc]

variable (C) [Preadditive C]

/-- The double complex of a bisimplicial object `X`: the alternating face map complex in the
outer direction, of the alternating face map complexes in the inner direction.  Its term of
bidegree `(p, q)` is `(X _⦋p⦌) _⦋q⦌`. -/
@[expose]
def doubleComplex :
    SimplicialObject (SimplicialObject C) ⥤
      HomologicalComplex₂ C (ComplexShape.down ℕ) (ComplexShape.down ℕ) :=
  alternatingFaceMapComplex (SimplicialObject C) ⋙
    (alternatingFaceMapComplex C).mapHomologicalComplex _

variable {C}

@[simp]
lemma doubleComplex_obj_X_X (p q : ℕ) : (((doubleComplex C).obj X).X p).X q = (X _⦋p⦌) _⦋q⦌ :=
  (rfl)

/-- The outer differential of the double complex is the alternating sum of the outer faces. -/
@[simp]
lemma doubleComplex_obj_d_f (p q : ℕ) :
    (((doubleComplex C).obj X).d (p + 1) p).f q =
      ∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) • (X.δ i).app (op ⦋q⦌) := by
  simp only [doubleComplex, Functor.comp_obj, Functor.mapHomologicalComplex_obj_d,
    alternatingFaceMapComplex_obj_d, AlternatingFaceMapComplex.objD, Functor.map_sum]
  rw [← HomologicalComplex.Hom.fAddMonoidHom_apply, map_sum]
  exact Finset.sum_congr rfl fun i _ ↦ rfl

/-- The inner differential of the double complex is the alternating sum of the inner faces. -/
@[simp]
lemma doubleComplex_obj_X_d (p q : ℕ) :
    (((doubleComplex C).obj X).X p).d (q + 1) q =
      ∑ j : Fin (q + 2), (-1 : ℤ) ^ (j : ℕ) • (X _⦋p⦌).δ j := by
  simp [doubleComplex]

@[simp]
lemma doubleComplex_map_f_f {X Y : SimplicialObject (SimplicialObject C)} (φ : X ⟶ Y)
    (p q : ℕ) :
    (((doubleComplex C).map φ).f p).f q = (φ.app (op ⦋p⦌)).app (op ⦋q⦌) :=
  (rfl)

variable [HasFiniteCoproducts C]

/-- The inclusion of the term `(X _⦋p⦌) _⦋q⦌` into the total complex of the double complex. -/
private def ιTot (p q n : ℕ) (h : p + q = n) :
    (X _⦋p⦌) _⦋q⦌ ⟶ (((doubleComplex C).obj X).total (ComplexShape.down ℕ)).X n :=
  ((doubleComplex C).obj X).ιTotal (ComplexShape.down ℕ) p q n h

/-- The outer part of the total differential on a term of positive outer degree. -/
private lemma ιTot_D₁ (r s n : ℕ) (h : r + 1 + s = n + 1) :
    ιTot X (r + 1) s (n + 1) h ≫ ((doubleComplex C).obj X).D₁ (ComplexShape.down ℕ) (n + 1) n =
      ∑ i : Fin (r + 2), (-1 : ℤ) ^ (i : ℕ) •
        ((X.δ i).app (op ⦋s⦌) ≫ ιTot X r s n (by omega)) := by
  have h₁ := ((doubleComplex C).obj X).ι_D₁ (ComplexShape.down ℕ) (n + 1) n (r + 1) s h
  rw [HomologicalComplex₂.d₁_eq _ _ (ComplexShape.down_mk (r + 1) r rfl) _ _
    (by simp; omega), doubleComplex_obj_d_f] at h₁
  simp only [ComplexShape.ε₁_def, one_smul] at h₁
  -- the alternating sum is typed by the terms of `X`, the inclusion by those of the double
  -- complex, so the sum is distributed by a term rather than by `simp`
  exact h₁.trans ((Preadditive.sum_comp _ _ _).trans
    (Finset.sum_congr rfl fun i _ ↦ Preadditive.zsmul_comp _ _ _))

/-- The outer part of the total differential vanishes on a term of outer degree zero. -/
private lemma ιTot_D₁_zero (n : ℕ) :
    ιTot X 0 (n + 1) (n + 1) (by omega) ≫
      ((doubleComplex C).obj X).D₁ (ComplexShape.down ℕ) (n + 1) n = 0 :=
  (((doubleComplex C).obj X).ι_D₁ _ _ _ _ _ _).trans
    (HomologicalComplex₂.d₁_eq_zero _ _ _ _ _ (by simp))

/-- The inner part of the total differential on a term of positive inner degree, with the sign
`(-1)^r` of the outer degree `r`. -/
private lemma ιTot_D₂ (r s n : ℕ) (h : r + (s + 1) = n + 1) :
    ιTot X r (s + 1) (n + 1) h ≫ ((doubleComplex C).obj X).D₂ (ComplexShape.down ℕ) (n + 1) n =
      (-1 : ℤ) ^ r • ∑ j : Fin (s + 2), (-1 : ℤ) ^ (j : ℕ) •
        ((X _⦋r⦌).δ j ≫ ιTot X r s n (by omega)) := by
  have h₁ := ((doubleComplex C).obj X).ι_D₂ (ComplexShape.down ℕ) (n + 1) n r (s + 1) h
  rw [HomologicalComplex₂.d₂_eq _ _ _ (ComplexShape.down_mk (s + 1) s rfl) _
    (by simp; omega), doubleComplex_obj_X_d] at h₁
  simp only [ComplexShape.ε₂_def, ComplexShape.ε_down_ℕ, Units.smul_def, Units.val_pow_eq_pow_val,
    Units.val_neg, Units.val_one] at h₁
  -- the alternating sum is typed by the terms of `X`, the inclusion by those of the double
  -- complex, so the sum is distributed by a term rather than by `simp`
  exact h₁.trans (congrArg _ ((Preadditive.sum_comp _ _ _).trans
    (Finset.sum_congr rfl fun j _ ↦ Preadditive.zsmul_comp _ _ _)))

/-- The inner part of the total differential vanishes on a term of inner degree zero. -/
private lemma ιTot_D₂_zero (n : ℕ) :
    ιTot X (n + 1) 0 (n + 1) (by omega) ≫
      ((doubleComplex C).obj X).D₂ (ComplexShape.down ℕ) (n + 1) n = 0 :=
  (((doubleComplex C).obj X).ι_D₂ _ _ _ _ _ _).trans
    (HomologicalComplex₂.d₂_eq_zero _ _ _ _ _ (by simp))

/-- The summand of the Alexander–Whitney map in degree `n` and bidegree `(p, q)`: the front
`p`-face in the outer direction and the back `q`-face in the inner direction, or zero if
`p + q ≠ n`. -/
private def alexanderWhitneyTerm (n p q : ℕ) :
    (X _⦋n⦌) _⦋n⦌ ⟶ (((doubleComplex C).obj X).total (ComplexShape.down ℕ)).X n :=
  if h : p + q = n then
    bimap X (SimplexCategory.subinterval (n := n) 0 p (by omega))
        (SimplexCategory.subinterval (n := n) p q (by omega)) ≫ ιTot X p q n h
  else 0

private lemma alexanderWhitneyTerm_of_eq (n p q : ℕ) (h : p + q = n) :
    alexanderWhitneyTerm X n p q =
      bimap X (SimplexCategory.subinterval (n := n) 0 p (by omega))
          (SimplexCategory.subinterval (n := n) p q (by omega)) ≫ ιTot X p q n h := by
  simp only [alexanderWhitneyTerm, h, ↓reduceDIte]

/-- The boundary of the Alexander–Whitney map in the bidegree `(r, s)`: the part of `d ∘ AW` that
lands in bidegree `(r, s)` is `AW ∘ d`.  The last outer face of the front `(r + 1)`-face cancels
against the zeroth inner face of the back `(s + 1)`-face; every other face of a front or back face
is the front or back face of a face of the simplex. -/
private lemma alexanderWhitneyTerm_D (n r s : ℕ) (h : r + s = n) :
    alexanderWhitneyTerm X (n + 1) (r + 1) s ≫
        ((doubleComplex C).obj X).D₁ (ComplexShape.down ℕ) (n + 1) n +
      alexanderWhitneyTerm X (n + 1) r (s + 1) ≫
        ((doubleComplex C).obj X).D₂ (ComplexShape.down ℕ) (n + 1) n =
      ∑ k : Fin (n + 2), (-1 : ℤ) ^ (k : ℕ) •
        (bimap X (SimplexCategory.δ k) (SimplexCategory.δ k) ≫ alexanderWhitneyTerm X n r s) := by
  rw [alexanderWhitneyTerm_of_eq _ _ _ _ (by omega), alexanderWhitneyTerm_of_eq _ _ _ _ (by omega),
    alexanderWhitneyTerm_of_eq _ _ _ _ h, Category.assoc, Category.assoc, ιTot_D₁, ιTot_D₂]
  simp only [δ_app_eq_bimap, δ_eq_bimap, Preadditive.comp_sum, Preadditive.comp_zsmul,
    bimap_comp_assoc, Category.id_comp]
  have hrs : r + 1 + (s + 1) = n + 2 := by omega
  conv_rhs => rw [← Fin.sum_congr' _ hrs, Fin.sum_univ_add]
  rw [Fin.sum_univ_castSucc (n := r + 1), Fin.sum_univ_succ (n := s + 1)]
  simp only [SimplexCategory.δ_last_comp_subinterval_zero, SimplexCategory.δ_zero_comp_subinterval]
  rw [smul_add, Finset.smul_sum, add_add_add_comm]
  -- the two sums match termwise, and the two remaining terms cancel
  have key {M : Type _} [AddCommGroup M] {P P' a b Q Q' : M} (h₁ : P = P') (h₂ : Q = Q')
      (h₃ : a + b = 0) : P + b + (a + Q) = P' + Q' := by
    have hadd : P + b + (a + Q) = P + Q + (a + b) := by abel
    rw [← h₁, ← h₂, hadd, h₃, add_zero]
  refine key ?_ ?_ ?_
  · refine Finset.sum_congr rfl fun i _ ↦ ?_
    have := i.isLt
    rw [SimplexCategory.δ_comp_subinterval_zero i.castSucc
        (Fin.cast (by omega) (Fin.castAdd (s + 1) i)) (by simp),
      SimplexCategory.subinterval_comp_δ_of_le (j := r) _ (by simp; omega)]
    simp
  · refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [SimplexCategory.δ_succ_comp_subinterval j (Fin.cast (by omega) (Fin.natAdd (r + 1) j))
        (by simp),
      SimplexCategory.subinterval_zero_comp_δ_of_lt (p := r) _ (by simp; omega), smul_smul]
    congr 1
    simp [pow_add]
  · rw [smul_smul, ← add_smul]
    simp [pow_succ]

/-- The degree-`n` component of the Alexander–Whitney map. -/
private def alexanderWhitneyX (n : ℕ) :
    (X _⦋n⦌) _⦋n⦌ ⟶ (((doubleComplex C).obj X).total (ComplexShape.down ℕ)).X n :=
  ∑ pq ∈ Finset.antidiagonal n, alexanderWhitneyTerm X n pq.1 pq.2

/-- The Alexander–Whitney map commutes with the differentials, stated with the faces of the
diagonal written as maps between the terms of `X`. -/
private lemma alexanderWhitneyX_comm (n : ℕ) :
    alexanderWhitneyX X (n + 1) ≫
        (((doubleComplex C).obj X).total (ComplexShape.down ℕ)).d (n + 1) n =
      (∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) •
        bimap X (SimplexCategory.δ i) (SimplexCategory.δ i)) ≫ alexanderWhitneyX X n := by
  rw [HomologicalComplex₂.total_d]
  simp only [alexanderWhitneyX, Preadditive.sum_comp, Preadditive.comp_add,
    Preadditive.zsmul_comp, Preadditive.comp_sum]
  rw [Finset.Nat.sum_antidiagonal_succ, Finset.Nat.sum_antidiagonal_succ',
    alexanderWhitneyTerm_of_eq _ _ 0 (n + 1) (by omega),
    alexanderWhitneyTerm_of_eq _ _ (n + 1) 0 (by omega), Category.assoc, Category.assoc,
    ιTot_D₁_zero, ιTot_D₂_zero, comp_zero, comp_zero, zero_add, zero_add,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun pq hpq ↦ ?_
  exact alexanderWhitneyTerm_D X n pq.1 pq.2 (Finset.mem_antidiagonal.mp hpq)

/-- **The Alexander–Whitney map** of a bisimplicial object `X`, from the alternating face map
complex of its diagonal to the total complex of its double complex.  In degree `n` it is the sum
over `p + q = n` of the front `p`-face in the outer direction followed by the back `q`-face in the
inner direction (`CategoryTheory.SimplicialObject.diagAlexanderWhitney_f`). -/
def diagAlexanderWhitney :
    (alternatingFaceMapComplex C).obj ((diag C).obj X) ⟶
      ((doubleComplex C).obj X).total (ComplexShape.down ℕ) where
  f := alexanderWhitneyX X
  comm' := by
    rintro _ n rfl
    refine (alexanderWhitneyX_comm X n).trans ?_
    rw [alternatingFaceMapComplex_obj_d, AlternatingFaceMapComplex.objD]
    -- the faces of the diagonal are by definition the maps induced in both directions at once
    rfl

/-- The degree-`n` component of the Alexander–Whitney map: the sum over `p ≤ n` of the front
`p`-face in the outer direction followed by the back `(n - p)`-face in the inner direction. -/
-- The sum is typed as a morphism out of `(X _⦋n⦌) _⦋n⦌` rather than out of the degree-`n` term of
-- the alternating face map complex of the diagonal, which is the same object only up to
-- unfolding, so that composites with the summands can be rewritten.
@[simp]
lemma diagAlexanderWhitney_f (n : ℕ) :
    (diagAlexanderWhitney X).f n =
      (∑ p : Fin (n + 1),
        (X.map (SimplexCategory.subinterval (n := n) 0 p (by omega)).op).app (op ⦋n⦌) ≫
          (X _⦋p⦌).map (SimplexCategory.subinterval (n := n) p (n - p) (by omega)).op ≫
            ((doubleComplex C).obj X).ιTotal (ComplexShape.down ℕ) p (n - p) n (by simp; omega) :
        (X _⦋n⦌) _⦋n⦌ ⟶ _) := by
  refine (Finset.Nat.sum_antidiagonal_eq_sum_range_succ (alexanderWhitneyTerm X n) n).trans ?_
  rw [Finset.sum_range]
  refine Finset.sum_congr rfl fun p _ ↦ ?_
  rw [alexanderWhitneyTerm_of_eq X n p (n - p) (by omega)]
  -- `bimap` and `ιTot` unfold to the maps in the statement
  unfold bimap ιTot
  exact Category.assoc _ _ _

variable {X} in
/-- The naturality of the Alexander–Whitney map in degree `n`, stated with the component of `φ` on
the diagonal written as a map between the terms of `X` and `Y`. -/
private lemma app_app_comp_alexanderWhitneyX {Y : SimplicialObject (SimplicialObject C)}
    (φ : X ⟶ Y) (n : ℕ) :
    (φ.app (op ⦋n⦌)).app (op ⦋n⦌) ≫ alexanderWhitneyX Y n =
      alexanderWhitneyX X n ≫
        (HomologicalComplex₂.total.map ((doubleComplex C).map φ) (ComplexShape.down ℕ)).f n := by
  simp only [alexanderWhitneyX, Preadditive.comp_sum, Preadditive.sum_comp]
  refine Finset.sum_congr rfl fun pq hpq ↦ ?_
  rw [alexanderWhitneyTerm_of_eq _ _ _ _ (Finset.mem_antidiagonal.mp hpq),
    alexanderWhitneyTerm_of_eq _ _ _ _ (Finset.mem_antidiagonal.mp hpq), Category.assoc]
  -- `ιTot` is the inclusion `HomologicalComplex₂.ιTotal`, retyped by the terms of `X`
  exact (app_app_comp_bimap_assoc φ _ _ _).trans (congrArg (bimap X _ _ ≫ ·)
    (HomologicalComplex₂.ιTotal_map _ _ ((doubleComplex C).map φ) _ _ _ _ _).symm)

variable {X} in
/-- The Alexander–Whitney map is natural in the bisimplicial object. -/
@[reassoc]
lemma diagAlexanderWhitney_naturality {Y : SimplicialObject (SimplicialObject C)} (φ : X ⟶ Y) :
    (alternatingFaceMapComplex C).map ((diag C).map φ) ≫ diagAlexanderWhitney Y =
      diagAlexanderWhitney X ≫
        HomologicalComplex₂.total.map ((doubleComplex C).map φ) (ComplexShape.down ℕ) := by
  ext n : 1
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f]
  exact app_app_comp_alexanderWhitneyX φ n

end CategoryTheory.SimplicialObject
