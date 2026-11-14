/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.SymplecticGroup
public import TauCeti.Combinatorics.Brauer.Generation
-- Non-public: `Finset.orderIsoOfFin` enumerates the lower ends of a diagram in order so that
-- `BrauerDiagram.symplecticActionMatrix` is computable, while diagram and loop-count associativity,
-- double-update sums, and `TauCeti.LinearAlgebra.SymplecticGroup` supply the loop-rule identities.
import Mathlib.Algebra.Star.BigOperators
import Mathlib.Data.Finset.Sort
import TauCeti.Combinatorics.Brauer.Associativity
import TauCeti.Combinatorics.Brauer.WeightedAssociativity
import TauCeti.Data.Fintype.BigOperators
import TauCeti.LinearAlgebra.SymplecticGroup

/-!
# The symplectic matrix of a Brauer diagram

Equip `(ι ⊕ ι) → R` with its standard alternating bilinear form, represented by `Matrix.J ι R`,
whose inverse copairing is the bivector of `-Matrix.J ι R`. A Brauer diagram `D` on `k` strands
determines a matrix `TauCeti.BrauerDiagram.symplecticActionMatrix` indexed by the labellings
`Fin k → ι ⊕ ι` of its bottom and top boundaries:

* each cap of `D` evaluates `Matrix.J ι R` at its two bottom labels;
* each cup of `D` evaluates `Matrix.J ι R` at its two top labels (with a sign supplied by the
  boundary permutation, matching the copairing `-Matrix.J ι R`);
* each through strand of `D` evaluates the Kronecker delta between its bottom and top labels, with
  sign `+1` when oriented bottom-to-top and `-1` when oriented top-to-bottom.

Because these oriented arc kernels (`TauCeti.BrauerDiagram.symplecticArcWeight`) are skew-symmetric
under reversing an arc, multiplying their product over the `k` arcs by the sign of the arc
parametrization measured against `Equiv.boolProdEquivSum (Fin k)` produces an entry independent of
how the `k` arcs and their endpoints are ordered
(`TauCeti.BrauerDiagram.symplecticActionMatrix_apply_of_isArcParam`).

The main theorem of this file is **the loop rule**
(`TauCeti.BrauerDiagram.symplecticActionMatrix_mul`): stacking `D₁` above `D₂` multiplies their
symplectic matrices up to the scalar `(-(2 * |ι|)) ^ c`, where `c` is the number of closed middle
loops (`TauCeti.middleLoopCount D₁ D₂`), each closed loop contracting `J` against `-J` to
`-tr (J * Jᵀ) = -(2 * |ι|)`.

## Main definitions

* `TauCeti.BrauerDiagram.symplecticArcWeight`: the skew-symmetric kernel assigned to an oriented
  arc of a Brauer diagram.
* `TauCeti.BrauerDiagram.IsArcParam`: an equivalence `Bool × Fin k ≃ Fin k ⊕ Fin k` pairing each
  `(false, r)` with its partner `(true, r)` in `D`.
* `TauCeti.BrauerDiagram.symplecticActionMatrix`: the matrix of a Brauer diagram acting on the
  `k`-th tensor power of `(ι ⊕ ι) → R` in the monomial basis.

## Main results

* `TauCeti.BrauerDiagram.symplecticActionMatrix_apply_of_isArcParam`: any arc parametrization of `D`
  computes the entries of `D.symplecticActionMatrix R ι`.
* `TauCeti.BrauerDiagram.symplecticActionMatrix_permToBrauer` and
  `TauCeti.BrauerDiagram.symplecticActionMatrix_capCup`: the explicit entries on permutation
  diagrams and on cap-cup diagrams.
* `TauCeti.BrauerDiagram.symplecticActionMatrix_relabel`: relabelling the bottom and top boundaries
  reindexes the matrix entries and multiplies by the product of the two permutation signs.
* `TauCeti.BrauerDiagram.symplecticActionMatrix_mul`: **the loop rule**,
  `M(D₁) * M(D₂) = (-(2 * |ι|)) ^ c • M(D₁ ∘ D₂)`.
* `TauCeti.BrauerDiagram.transpose_symplecticActionMatrix` and
  `TauCeti.BrauerDiagram.conjTranspose_symplecticActionMatrix`: the transpose and conjugate
  transpose of the matrix of `D` equal the matrix of the reflected diagram `D.flip`.

## References

* [R. Brauer, *On algebras which are connected with the semisimple continuous groups*][brauer1937],
  Annals of Mathematics 38 (1937), 857-872.
* R. Dipper, S. Doty and J. Hu, *Brauer algebras, symplectic Schur algebras and Schur–Weyl
  duality*, Trans. Amer. Math. Soc. 360 (2008), 189-213, §1.
* R. Goodman and N. R. Wallach, *Symmetry, Representations, and Invariants*, Springer GTM 255
  (2009), §10.1.
-/

public section

open scoped Matrix

namespace TauCeti

universe u

namespace BrauerDiagram

variable (R : Type u) [CommRing R] (ι : Type*) [DecidableEq ι] {k : ℕ}

/-! ### Oriented arc kernels -/

/-- **The skew-symmetric kernel of an oriented arc** `(x, y)` of a Brauer diagram on `k` strands,
evaluated at the boundary labels `a, b : ι ⊕ ι`: caps and cups evaluate `Matrix.J ι R a b`, while
bottom-to-top and top-to-bottom through strands evaluate the Kronecker delta with opposite signs so
that reversing an arc always negates its weight (`TauCeti.BrauerDiagram.symplecticArcWeight_swap`).
-/
def symplecticArcWeight : (Fin k ⊕ Fin k) → (ι ⊕ ι) → (Fin k ⊕ Fin k) → (ι ⊕ ι) → R
  | Sum.inl _, a, Sum.inl _, b => Matrix.J ι R a b
  | Sum.inr _, a, Sum.inr _, b => Matrix.J ι R a b
  | Sum.inl _, a, Sum.inr _, b => if a = b then 1 else 0
  | Sum.inr _, a, Sum.inl _, b => if a = b then -1 else 0

@[simp]
theorem symplecticArcWeight_inl_inl (i j : Fin k) (a b : ι ⊕ ι) :
    symplecticArcWeight R ι (Sum.inl i) a (Sum.inl j) b = Matrix.J ι R a b :=
  (rfl)

@[simp]
theorem symplecticArcWeight_inr_inr (i j : Fin k) (a b : ι ⊕ ι) :
    symplecticArcWeight R ι (Sum.inr i) a (Sum.inr j) b = Matrix.J ι R a b :=
  (rfl)

@[simp]
theorem symplecticArcWeight_inl_inr (i j : Fin k) (a b : ι ⊕ ι) :
    symplecticArcWeight R ι (Sum.inl i) a (Sum.inr j) b = if a = b then 1 else 0 :=
  (rfl)

@[simp]
theorem symplecticArcWeight_inr_inl (i j : Fin k) (a b : ι ⊕ ι) :
    symplecticArcWeight R ι (Sum.inr i) a (Sum.inl j) b = if a = b then -1 else 0 :=
  (rfl)

/-- **Reversing an oriented arc negates its kernel.** -/
theorem symplecticArcWeight_swap (x : Fin k ⊕ Fin k) (a : ι ⊕ ι) (y : Fin k ⊕ Fin k)
    (b : ι ⊕ ι) :
    symplecticArcWeight R ι y b x a = -symplecticArcWeight R ι x a y b := by
  rcases x with _ | _ <;> rcases y with _ | _
  · exact Matrix.J_apply_swap ι R a b
  · simp only [symplecticArcWeight_inl_inr, symplecticArcWeight_inr_inl, eq_comm]
    split_ifs <;> simp
  · simp only [symplecticArcWeight_inl_inr, symplecticArcWeight_inr_inl, eq_comm]
    split_ifs <;> simp
  · exact Matrix.J_apply_swap ι R a b

/-- Under horizontal reflection `Sum.swap`, the oriented arc kernel picks up `-1` on caps and cups
and `+1` on through strands. -/
private theorem symplecticArcWeight_sumSwap {D : BrauerDiagram k} {x : Fin k ⊕ Fin k}
    (a b : ι ⊕ ι) :
    symplecticArcWeight R ι (D.val x).swap b x.swap a =
      (if D.IsThrough x then (1 : R) else -1) * symplecticArcWeight R ι x a (D.val x) b := by
  rcases x with i | i <;> rcases hx : D.val _ with j | j
  · simp [isThrough_def, hx, Matrix.J_apply_swap ι R a b]
  · simp only [isThrough_def, hx, Sum.swap_inl, Sum.swap_inr, Sum.isLeft_inl, Sum.isLeft_inr,
      symplecticArcWeight_inl_inr]
    split_ifs <;> simp_all
  · simp only [isThrough_def, hx, Sum.swap_inl, Sum.swap_inr, Sum.isLeft_inl, Sum.isLeft_inr,
      symplecticArcWeight_inr_inl]
    split_ifs <;> simp_all
  · simp [isThrough_def, hx, Matrix.J_apply_swap ι R a b]

/-- Every entry of `symplecticArcWeight` is an integer cast, so every `StarRing` fixes it. -/
private theorem star_symplecticArcWeight [StarRing R] (x : Fin k ⊕ Fin k) (a : ι ⊕ ι)
    (y : Fin k ⊕ Fin k) (b : ι ⊕ ι) :
    star (symplecticArcWeight R ι x a y b) = symplecticArcWeight R ι x a y b := by
  have hJ (c d : ι ⊕ ι) : star (Matrix.J ι R c d) = Matrix.J ι R c d := by
    rw [← Matrix.map_J ι (Int.castRingHom R), Matrix.map_apply, eq_intCast, star_intCast]
  rcases x with _ | _ <;> rcases y with _ | _
  · exact hJ a b
  · simp only [symplecticArcWeight_inl_inr]; split_ifs <;> simp
  · simp only [symplecticArcWeight_inr_inl]; split_ifs <;> simp
  · exact hJ a b

/-- Contracting two arcs ending at `Sum.inr a` and `Sum.inr b` against `Matrix.J` produces the
single arc weight between their other endpoints `p` and `q`. -/
private theorem sum_symplecticArcWeight_mul_J [Fintype ι] (p q : Fin k ⊕ Fin k) (lp lq : ι ⊕ ι)
    (a b : Fin k) :
    (∑ x : ι ⊕ ι, ∑ y : ι ⊕ ι,
      symplecticArcWeight R ι p lp (Sum.inr a) x * Matrix.J ι R x y *
        symplecticArcWeight R ι q lq (Sum.inr b) y) =
      symplecticArcWeight R ι p lp q lq := by
  rcases p with _ | _ <;> rcases q with _ | _
  · simp
  · simp only [symplecticArcWeight_inl_inr, symplecticArcWeight_inr_inr]
    have hrow (y : ι ⊕ ι) :
        (∑ x : ι ⊕ ι, (if lp = x then (1 : R) else 0) * Matrix.J ι R x y * Matrix.J ι R lq y) =
          Matrix.J ι R lp y * Matrix.J ι R lq y := by
      simp
    rw [Finset.sum_comm]
    simp only [hrow]
    have hJ : Matrix.J ι R * (Matrix.J ι R)ᵀ = 1 := by
      rw [Matrix.J_transpose]; exact Matrix.J_mul_neg_J ι R
    simpa only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply] using
      congrFun (congrFun hJ lp) lq
  · simp only [symplecticArcWeight_inr_inr, symplecticArcWeight_inl_inr,
      symplecticArcWeight_inr_inl]
    have hinner (x : ι ⊕ ι) :
        (∑ y : ι ⊕ ι, Matrix.J ι R lp x * Matrix.J ι R x y * if lq = y then (1 : R) else 0) =
          Matrix.J ι R lp x * Matrix.J ι R x lq := by
      simp
    simp only [hinner]
    have hsq := congrFun (congrFun (Matrix.J_squared ι R) lp) lq
    simp only [Matrix.mul_apply, Matrix.neg_apply, Matrix.one_apply] at hsq
    rw [hsq]
    split_ifs <;> simp
  · simp only [symplecticArcWeight_inr_inr]
    have hid : Matrix.J ι R * Matrix.J ι R * (Matrix.J ι R)ᵀ = Matrix.J ι R := by
      rw [Matrix.J_squared, Matrix.J_transpose, Matrix.neg_mul, Matrix.one_mul, neg_neg]
    have h := congrFun (congrFun hid lp) lq
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul] at h
    rw [← h, Finset.sum_comm]

/-! ### Arc parametrizations and sign invariance -/

variable {R ι}

/-- **An arc parametrization of a Brauer diagram `D`**: an equivalence
`φ : Bool × Fin k ≃ Fin k ⊕ Fin k` sending `(false, r)` and `(true, r)` to the two endpoints of the
`r`-th arc of `D` for every `r : Fin k`. -/
def IsArcParam (D : BrauerDiagram k) (φ : Bool × Fin k ≃ Fin k ⊕ Fin k) : Prop :=
  ∀ r : Fin k, D.val (φ (false, r)) = φ (true, r)

/-- `D.IsArcParam φ` means that `D` matches `φ (false, r)` with `φ (true, r)` for every `r`. -/
theorem isArcParam_def (D : BrauerDiagram k) (φ : Bool × Fin k ≃ Fin k ⊕ Fin k) :
    D.IsArcParam φ ↔ ∀ r : Fin k, D.val (φ (false, r)) = φ (true, r) :=
  Iff.rfl

private theorem IsArcParam.val_apply {D : BrauerDiagram k} {φ : Bool × Fin k ≃ Fin k ⊕ Fin k}
    (hφ : D.IsArcParam φ) (b : Bool) (r : Fin k) :
    D.val (φ (b, r)) = φ (!b, r) := by
  cases b
  · exact hφ r
  · simp [← hφ r]

private theorem IsArcParam.symm_val_apply {D : BrauerDiagram k} {φ : Bool × Fin k ≃ Fin k ⊕ Fin k}
    (hφ : D.IsArcParam φ) (x : Fin k ⊕ Fin k) :
    φ.symm (D.val x) = (!(φ.symm x).1, (φ.symm x).2) := by
  rcases hx : φ.symm x with ⟨b, r⟩
  have hx' : x = φ (b, r) := by simpa [hx] using (φ.apply_symm_apply x).symm
  rw [hx', hφ.val_apply, φ.symm_apply_apply]

private theorem IsArcParam.congr {D : BrauerDiagram k} {φ : Bool × Fin k ≃ Fin k ⊕ Fin k}
    (hφ : D.IsArcParam φ) (σ : Equiv.Perm (Fin k ⊕ Fin k)) :
    IsArcParam (PerfectMatching.congr σ D) (φ.trans σ) := fun r => by
  simp [hφ r]

private theorem IsArcParam.flipEndpoints {D : BrauerDiagram k} {φ : Bool × Fin k ≃ Fin k ⊕ Fin k}
    (hφ : D.IsArcParam φ) (P : Fin k → Prop) [DecidablePred P] :
    D.IsArcParam ((Equiv.prodCongrLeft fun r =>
      if P r then Equiv.swap false true else 1).trans φ) := fun r => by
  by_cases hP : P r <;> simp [hP, hφ.val_apply]

/-- The lower ends of `D`, read in `Fin (k + k)` so that `Finset.orderIsoOfFin` enumerates them
computably. -/
private def lowerEndFinset (D : BrauerDiagram k) : Finset (Fin (k + k)) :=
  Finset.univ.filter fun i => D.IsLowerEnd (finSumFinEquiv.symm i)

private theorem card_lowerEndFinset (D : BrauerDiagram k) :
    (lowerEndFinset D).card = k := by
  rw [lowerEndFinset, ← Fintype.card_subtype]
  refine (Fintype.card_congr ?_).trans D.card_isLowerEnd
  exact
    { toFun := fun i => ⟨finSumFinEquiv.symm i.1, i.2⟩
      invFun := fun x => ⟨finSumFinEquiv x.1, by simpa using x.2⟩
      left_inv := fun i => Subtype.ext (by simp)
      right_inv := fun x => Subtype.ext (by simp) }

/-- The canonical computable enumeration of the `k` lower ends of `D`. -/
private def lowerEndEquiv (D : BrauerDiagram k) : Fin k ≃ {x // D.IsLowerEnd x} :=
  ((lowerEndFinset D).orderIsoOfFin (card_lowerEndFinset D)).toEquiv.trans
    { toFun := fun i => ⟨finSumFinEquiv.symm i.1, (Finset.mem_filter.mp i.2).2⟩
      invFun := fun x =>
        ⟨finSumFinEquiv x.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa using x.2⟩⟩
      left_inv := fun i => Subtype.ext (by simp)
      right_inv := fun x => Subtype.ext (by simp) }

/-- The canonical computable arc parametrization of `D`, pairing each lower end with its partner. -/
private def arcParam (D : BrauerDiagram k) : Bool × Fin k ≃ Fin k ⊕ Fin k where
  toFun
    | (false, r) => (D.lowerEndEquiv r).1
    | (true, r) => D.val (D.lowerEndEquiv r).1
  invFun x :=
    if hx : D.IsLowerEnd x then
      (false, D.lowerEndEquiv.symm ⟨x, hx⟩)
    else
      (true, D.lowerEndEquiv.symm ⟨D.val x, D.isLowerEnd_val_of_not_isLowerEnd hx⟩)
  left_inv := by
    rintro ⟨_ | _, r⟩
    · simp [(D.lowerEndEquiv r).2]
    · simp [D.not_isLowerEnd_val (D.lowerEndEquiv r).2, D.apply_apply]
  right_inv x := by
    by_cases hx : D.IsLowerEnd x <;> simp [hx, D.apply_apply]

private theorem isArcParam_arcParam (D : BrauerDiagram k) : D.IsArcParam D.arcParam :=
  fun _ => rfl

/-- **Every Brauer diagram admits an arc parametrization.** -/
theorem exists_isArcParam (D : BrauerDiagram k) :
    ∃ φ : Bool × Fin k ≃ Fin k ⊕ Fin k, D.IsArcParam φ :=
  ⟨D.arcParam, D.isArcParam_arcParam⟩

variable (R ι)

/-- The signed product of arc kernels associated to an arc parametrization `φ` and a boundary
labelling `ℓ : Fin k ⊕ Fin k → ι ⊕ ι`, with sign measured against `Equiv.boolProdEquivSum (Fin k)`.
-/
private def arcParamTerm (φ : Bool × Fin k ≃ Fin k ⊕ Fin k) (ℓ : Fin k ⊕ Fin k → ι ⊕ ι) : R :=
  ((Equiv.Perm.sign ((Equiv.boolProdEquivSum (Fin k)).symm.trans φ) : ℤ) : R) *
    ∏ r : Fin k, symplecticArcWeight R ι (φ (false, r)) (ℓ (φ (false, r)))
      (φ (true, r)) (ℓ (φ (true, r)))

/-- Permuting the `k` arcs induces the same permutation on both `Bool` copies, which is even, and
reindexes the product over `Fin k`. -/
private theorem arcParamTerm_reindex (φ : Bool × Fin k ≃ Fin k ⊕ Fin k)
    (α : Equiv.Perm (Fin k)) (ℓ : Fin k ⊕ Fin k → ι ⊕ ι) :
    arcParamTerm R ι ((Equiv.prodCongrRight fun _ : Bool => α).trans φ) ℓ =
      arcParamTerm R ι φ ℓ := by
  have hbool : Equiv.Perm.sign (Equiv.prodCongrRight fun _ : Bool => α) = 1 := by
    rw [Equiv.Perm.sign_prodCongrRight, Fintype.prod_bool, Int.units_mul_self]
  have hsign :
      Equiv.Perm.sign
          ((Equiv.boolProdEquivSum (Fin k)).symm.trans
            ((Equiv.prodCongrRight fun _ : Bool => α).trans φ)) =
        Equiv.Perm.sign ((Equiv.boolProdEquivSum (Fin k)).symm.trans φ) := by
    rw [Equiv.Perm.sign_trans_trans, hbool, one_mul]
  rw [arcParamTerm, arcParamTerm, hsign]
  exact congrArg _ (Fintype.prod_equiv α _ _ fun _ => rfl)

/-- Reversing the endpoints of selected arcs negates both the permutation sign and each reversed arc
kernel, leaving the signed product unchanged. -/
private theorem arcParamTerm_flipEndpoints (φ : Bool × Fin k ≃ Fin k ⊕ Fin k)
    (P : Fin k → Prop) [DecidablePred P] (ℓ : Fin k ⊕ Fin k → ι ⊕ ι) :
    arcParamTerm R ι
        ((Equiv.prodCongrLeft fun r => if P r then Equiv.swap false true else 1).trans φ) ℓ =
      arcParamTerm R ι φ ℓ := by
  let flipPerm : Fin k → Equiv.Perm Bool := fun r => if P r then Equiv.swap false true else 1
  let castUnit : ℤˣ →* R := (Int.castRingHom R).toMonoidHom.comp (Units.coeHom ℤ)
  have hsign_flip :
      ((Equiv.Perm.sign (Equiv.prodCongrLeft flipPerm) : ℤ) : R) =
        ∏ r : Fin k, if P r then (-1 : R) else 1 := by
    rw [Equiv.Perm.sign_prodCongrLeft]
    refine (map_prod castUnit (fun r => Equiv.Perm.sign (flipPerm r)) Finset.univ).trans ?_
    refine Finset.prod_congr rfl fun r _ => ?_
    by_cases hP : P r <;> simp [castUnit, flipPerm, hP]
  have hsq : (∏ r : Fin k, if P r then (-1 : R) else 1) *
      (∏ r : Fin k, if P r then (-1 : R) else 1) = 1 := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_eq_one fun r _ => ?_
    by_cases hP : P r <;> simp [hP]
  have hfactor (r : Fin k) :
      symplecticArcWeight R ι (((Equiv.prodCongrLeft flipPerm).trans φ) (false, r))
          (ℓ (((Equiv.prodCongrLeft flipPerm).trans φ) (false, r)))
          (((Equiv.prodCongrLeft flipPerm).trans φ) (true, r))
          (ℓ (((Equiv.prodCongrLeft flipPerm).trans φ) (true, r))) =
        (if P r then (-1 : R) else 1) *
          symplecticArcWeight R ι (φ (false, r)) (ℓ (φ (false, r)))
            (φ (true, r)) (ℓ (φ (true, r))) := by
    by_cases hP : P r
    · simp only [Equiv.trans_apply, Equiv.prodCongrLeft_apply, flipPerm, hP, ↓reduceIte,
        Equiv.swap_apply_left, Equiv.swap_apply_right, neg_one_mul]
      exact symplecticArcWeight_swap R ι _ _ _ _
    · simp [flipPerm, hP]
  rw [arcParamTerm, arcParamTerm, Equiv.Perm.sign_trans_trans, Units.val_mul, Int.cast_mul,
    hsign_flip, Finset.prod_congr rfl fun r _ => hfactor r, Finset.prod_mul_distrib]
  set Q := ∏ r : Fin k, if P r then (-1 : R) else 1
  set S := ((Equiv.Perm.sign ((Equiv.boolProdEquivSum (Fin k)).symm.trans φ) : ℤ) : R)
  set W := ∏ r : Fin k, symplecticArcWeight R ι (φ (false, r)) (ℓ (φ (false, r)))
    (φ (true, r)) (ℓ (φ (true, r)))
  calc Q * S * (Q * W) = (Q * Q) * (S * W) := by ring
    _ = S * W := by rw [hsq, one_mul]

/-- **Independence of the arc parametrization.** Any two arc parametrizations of `D` differ by
permuting the `k` arcs and flipping endpoints within individual arcs, so they produce the same
signed product. -/
private theorem arcParamTerm_eq_of_isArcParam {D : BrauerDiagram k}
    {φ₁ φ₂ : Bool × Fin k ≃ Fin k ⊕ Fin k} (h₁ : D.IsArcParam φ₁) (h₂ : D.IsArcParam φ₂)
    (ℓ : Fin k ⊕ Fin k → ι ⊕ ι) :
    arcParamTerm R ι φ₁ ℓ = arcParamTerm R ι φ₂ ℓ := by
  let τ : Equiv.Perm (Bool × Fin k) := φ₂.trans φ₁.symm
  let β : Fin k → Bool := fun r => (τ (false, r)).1
  let α : Fin k → Fin k := fun r => (τ (false, r)).2
  have hτ (b : Bool) (r : Fin k) : τ (b, r) = (Bool.xor (β r) b, α r) := by
    cases b
    · simp [β, α]
    · simp only [τ, Equiv.trans_apply, ← h₂ r, h₁.symm_val_apply]
      rfl
  have hα_inj : Function.Injective α := fun r₁ r₂ h => by
    have h_eq : τ (Bool.xor (β r₂) (β r₁), r₂) = τ (false, r₁) := by
      rw [hτ, hτ, h]
      rcases β r₁ <;> rcases β r₂ <;> rfl
    exact (Prod.mk.inj (τ.injective h_eq)).2.symm
  let αPerm : Equiv.Perm (Fin k) := Equiv.ofBijective α (Finite.injective_iff_bijective.mp hα_inj)
  let flipPerm : Fin k → Equiv.Perm Bool := fun r => if β r then Equiv.swap false true else 1
  have hφ₂ : φ₂ = (Equiv.prodCongrLeft flipPerm).trans
      ((Equiv.prodCongrRight fun _ : Bool => αPerm).trans φ₁) := by
    ext ⟨b, r⟩
    have happ : φ₂ (b, r) = φ₁ (τ (b, r)) := by simp [τ]
    rw [happ, hτ]
    rcases hβ : β r <;> cases b <;> simp [αPerm, flipPerm, hβ]
  rw [hφ₂, arcParamTerm_flipEndpoints, arcParamTerm_reindex]

/-! ### The symplectic matrix and its entries on generators -/

/-- **The matrix of a Brauer diagram** acting on the `k`-th tensor power of `(ι ⊕ ι) → R` with its
standard alternating form `Matrix.J ι R`, in the monomial basis indexed by the labellings
`Fin k → ι ⊕ ι` of the strands. -/
def symplecticActionMatrix (D : BrauerDiagram k) :
    Matrix (Fin k → ι ⊕ ι) (Fin k → ι ⊕ ι) R :=
  Matrix.of fun v u => arcParamTerm R ι D.arcParam (Sum.elim u v)

/-- **Any arc parametrization computes the entries of `symplecticActionMatrix`.** -/
theorem symplecticActionMatrix_apply_of_isArcParam {D : BrauerDiagram k}
    {φ : Bool × Fin k ≃ Fin k ⊕ Fin k} (hφ : D.IsArcParam φ) (v u : Fin k → ι ⊕ ι) :
    D.symplecticActionMatrix R ι v u =
      ((Equiv.Perm.sign ((Equiv.boolProdEquivSum (Fin k)).symm.trans φ) : ℤ) : R) *
        ∏ r : Fin k, symplecticArcWeight R ι (φ (false, r)) (Sum.elim u v (φ (false, r)))
          (φ (true, r)) (Sum.elim u v (φ (true, r))) :=
  arcParamTerm_eq_of_isArcParam R ι D.isArcParam_arcParam hφ (Sum.elim u v)

/-- **The matrix of a permutation diagram**: `permToBrauer σ` has entry `sign σ` when `u = v ∘ σ`,
and `0` otherwise. -/
theorem symplecticActionMatrix_permToBrauer (σ : Equiv.Perm (Fin k))
    (v u : Fin k → ι ⊕ ι) :
    (permToBrauer σ).symplecticActionMatrix R ι v u =
      if u = v ∘ σ then ((Equiv.Perm.sign σ : ℤ) : R) else 0 := by
  let φ : Bool × Fin k ≃ Fin k ⊕ Fin k :=
    (Equiv.boolProdEquivSum (Fin k)).trans (Equiv.Perm.sumCongr 1 σ)
  have hφ : (permToBrauer σ).IsArcParam φ := fun r => by simp [φ]
  rw [symplecticActionMatrix_apply_of_isArcParam R ι hφ]
  have hperm : (Equiv.boolProdEquivSum (Fin k)).symm.trans φ = Equiv.Perm.sumCongr 1 σ := by
    ext x; simp only [φ, Equiv.trans_apply, Equiv.apply_symm_apply]
  rw [hperm, Equiv.Perm.sign_sumCongr, map_one, one_mul]
  have hprod : (∏ r : Fin k, symplecticArcWeight R ι (φ (false, r)) (Sum.elim u v (φ (false, r)))
      (φ (true, r)) (Sum.elim u v (φ (true, r)))) = if u = v ∘ σ then 1 else 0 := by
    simp only [φ, Equiv.trans_apply, Equiv.boolProdEquivSum_apply, ↓reduceIte,
      Bool.false_eq_true, Equiv.Perm.sumCongr_apply, Sum.map_inl, Equiv.Perm.one_apply,
      Sum.map_inr, Sum.elim_inl, Sum.elim_inr, symplecticArcWeight_inl_inr]
    rw [Fintype.prod_boole]
    split_ifs <;> simp_all [funext_iff]
  rw [hprod, mul_ite, mul_one, mul_zero]

/-- The identity diagram has the identity matrix. -/
@[simp]
theorem symplecticActionMatrix_permToBrauer_one :
    (permToBrauer 1).symplecticActionMatrix R ι =
      (1 : Matrix (Fin k → ι ⊕ ι) (Fin k → ι ⊕ ι) R) := by
  ext v u
  rw [symplecticActionMatrix_permToBrauer, map_one, Units.val_one, Int.cast_one, Matrix.one_apply]
  exact if_congr eq_comm rfl rfl

/-- **The matrix of a cap-cup diagram**: on two distinct strands `a ≠ b`, the `(v, u)` entry is
`-(J (u a) (u b) * J (v a) (v b))` when `v` agrees with `u` away from `a` and `b`, and `0`
otherwise, matching `TauCeti.piTensorProduct_repr_symplecticCupCapAt_piTensorProduct`. -/
theorem symplecticActionMatrix_capCup {a b : Fin k} (hab : a ≠ b) (v u : Fin k → ι ⊕ ι) :
    (capCup a b).symplecticActionMatrix R ι v u =
      if ∀ t, t ≠ a → t ≠ b → v t = u t then
        -(Matrix.J ι R (u a) (u b) * Matrix.J ι R (v a) (v b))
      else 0 := by
  let σ : Equiv.Perm (Fin k ⊕ Fin k) := Equiv.swap (Sum.inr a) (Sum.inl b)
  let φ : Bool × Fin k ≃ Fin k ⊕ Fin k := (Equiv.boolProdEquivSum (Fin k)).trans σ
  have hφ : (capCup a b).IsArcParam φ := fun r => by
    simp only [φ, σ, Equiv.trans_apply, Equiv.boolProdEquivSum_apply, ↓reduceIte,
      Bool.false_eq_true]
    rcases eq_or_ne r a with rfl | hra
    · rw [Equiv.swap_apply_of_ne_of_ne Sum.inl_ne_inr (Sum.inl_injective.ne hab),
        Equiv.swap_apply_left, capCup_val_inl_left hab]
    rcases eq_or_ne r b with rfl | hrb
    · rw [Equiv.swap_apply_right,
        Equiv.swap_apply_of_ne_of_ne (Sum.inr_injective.ne hab.symm) Sum.inr_ne_inl,
        capCup_val_inr_left hab]
    · rw [Equiv.swap_apply_of_ne_of_ne Sum.inl_ne_inr (Sum.inl_injective.ne hrb),
        Equiv.swap_apply_of_ne_of_ne (Sum.inr_injective.ne hra) Sum.inr_ne_inl,
        capCup_val_inl_of_ne hra hrb]
  rw [symplecticActionMatrix_apply_of_isArcParam R ι hφ]
  have hperm : (Equiv.boolProdEquivSum (Fin k)).symm.trans φ = σ := by
    ext x; simp only [φ, Equiv.trans_apply, Equiv.apply_symm_apply]
  have hsign : ((Equiv.Perm.sign σ : ℤ) : R) = -1 := by
    rw [Equiv.Perm.sign_swap Sum.inr_ne_inl]; simp
  rw [hperm, hsign, neg_one_mul, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ a),
    ← Finset.mul_prod_erase (Finset.univ.erase a) _
      (Finset.mem_erase.mpr ⟨hab.symm, Finset.mem_univ b⟩)]
  have ha_term : symplecticArcWeight R ι (φ (false, a)) (Sum.elim u v (φ (false, a)))
      (φ (true, a)) (Sum.elim u v (φ (true, a))) = Matrix.J ι R (u a) (u b) := by
    simp only [φ, σ, Equiv.trans_apply, Equiv.boolProdEquivSum_apply, ↓reduceIte,
      Bool.false_eq_true, Equiv.swap_apply_of_ne_of_ne Sum.inl_ne_inr (Sum.inl_injective.ne hab),
      Equiv.swap_apply_left, Sum.elim_inl, symplecticArcWeight_inl_inl]
  have hb_term : symplecticArcWeight R ι (φ (false, b)) (Sum.elim u v (φ (false, b)))
      (φ (true, b)) (Sum.elim u v (φ (true, b))) = Matrix.J ι R (v a) (v b) := by
    simp only [φ, σ, Equiv.trans_apply, Equiv.boolProdEquivSum_apply, ↓reduceIte,
      Bool.false_eq_true, Equiv.swap_apply_right,
      Equiv.swap_apply_of_ne_of_ne (Sum.inr_injective.ne hab.symm) Sum.inr_ne_inl,
      Sum.elim_inr, symplecticArcWeight_inr_inr]
  have hrest : (∏ r ∈ (Finset.univ.erase a).erase b,
      symplecticArcWeight R ι (φ (false, r)) (Sum.elim u v (φ (false, r)))
        (φ (true, r)) (Sum.elim u v (φ (true, r)))) =
      if ∀ t, t ≠ a → t ≠ b → v t = u t then 1 else 0 := by
    have hcongr : ∀ r ∈ (Finset.univ.erase a).erase b,
        symplecticArcWeight R ι (φ (false, r)) (Sum.elim u v (φ (false, r)))
          (φ (true, r)) (Sum.elim u v (φ (true, r))) = if v r = u r then 1 else 0 := by
      intro r hr
      have hrb : r ≠ b := (Finset.mem_erase.mp hr).1
      have hra : r ≠ a := (Finset.mem_erase.mp (Finset.mem_erase.mp hr).2).1
      simp only [φ, σ, Equiv.trans_apply, Equiv.boolProdEquivSum_apply, ↓reduceIte,
        Bool.false_eq_true, Equiv.swap_apply_of_ne_of_ne Sum.inl_ne_inr (Sum.inl_injective.ne hrb),
        Equiv.swap_apply_of_ne_of_ne (Sum.inr_injective.ne hra) Sum.inr_ne_inl,
        Sum.elim_inl, Sum.elim_inr, symplecticArcWeight_inl_inr]
      exact if_congr eq_comm rfl rfl
    rw [Finset.prod_congr rfl hcongr, Finset.prod_boole]
    split_ifs <;> simp_all
  rw [ha_term, hb_term, hrest]
  split_ifs <;> ring

/-- **Relabelling a diagram** reindexes its symplectic matrix entries along the two boundary
permutations and multiplies by the product of their signs. -/
theorem symplecticActionMatrix_relabel (D : BrauerDiagram k) (σ τ : Equiv.Perm (Fin k))
    (v u : Fin k → ι ⊕ ι) :
    (D.relabel σ τ).symplecticActionMatrix R ι v u =
      ((Equiv.Perm.sign σ * Equiv.Perm.sign τ : ℤˣ) : R) *
        D.symplecticActionMatrix R ι (v ∘ τ) (u ∘ σ) := by
  let φ' : Bool × Fin k ≃ Fin k ⊕ Fin k := D.arcParam.trans (Equiv.Perm.sumCongr σ τ)
  have hφ' : (D.relabel σ τ).IsArcParam φ' := by
    rw [relabel_def]
    exact D.isArcParam_arcParam.congr (Equiv.Perm.sumCongr σ τ)
  rw [symplecticActionMatrix_apply_of_isArcParam R ι D.isArcParam_arcParam,
    symplecticActionMatrix_apply_of_isArcParam R ι hφ']
  have hperm : (Equiv.boolProdEquivSum (Fin k)).symm.trans φ' =
      ((Equiv.boolProdEquivSum (Fin k)).symm.trans D.arcParam).trans
        (Equiv.Perm.sumCongr σ τ) := rfl
  have hsign : ((Equiv.Perm.sign ((Equiv.boolProdEquivSum (Fin k)).symm.trans φ') : ℤ) : R) =
      ((Equiv.Perm.sign σ * Equiv.Perm.sign τ : ℤˣ) : R) *
        ((Equiv.Perm.sign ((Equiv.boolProdEquivSum (Fin k)).symm.trans D.arcParam) : ℤ) : R) := by
    rw [hperm, Equiv.Perm.sign_trans, Equiv.Perm.sign_sumCongr, Units.val_mul, Int.cast_mul]
  have hweight (x y : Fin k ⊕ Fin k) :
      symplecticArcWeight R ι (Equiv.Perm.sumCongr σ τ x)
          (Sum.elim u v (Equiv.Perm.sumCongr σ τ x))
          (Equiv.Perm.sumCongr σ τ y) (Sum.elim u v (Equiv.Perm.sumCongr σ τ y)) =
        symplecticArcWeight R ι x (Sum.elim (u ∘ σ) (v ∘ τ) x) y
          (Sum.elim (u ∘ σ) (v ∘ τ) y) := by
    rcases x with _ | _ <;> rcases y with _ | _ <;> simp
  rw [hsign, mul_assoc]
  exact congrArg _ (congrArg _ (Finset.prod_congr rfl fun _ _ => hweight _ _))

/-! ### The loop rule for diagram multiplication -/

/-- Stacking a permutation diagram above `D` multiplies its symplectic matrix on the left. -/
private theorem symplecticActionMatrix_permToBrauer_mul [Fintype ι] (σ : Equiv.Perm (Fin k))
    (D : BrauerDiagram k) :
    (permToBrauer σ).symplecticActionMatrix R ι * D.symplecticActionMatrix R ι =
      (composeDiagram (permToBrauer σ) D).symplecticActionMatrix R ι := by
  ext v u
  rw [Matrix.mul_apply, composeDiagram_permToBrauer_left, symplecticActionMatrix_relabel]
  simp [symplecticActionMatrix_permToBrauer]

/-- When `D` cups `a` to `b`, some arc parametrization of `D` sends `(false, r₀)` to `Sum.inr a`
and `(true, r₀)` to `Sum.inr b`. -/
private theorem exists_isArcParam_of_cup {D : BrauerDiagram k} {a b : Fin k}
    (hcup : D.val (Sum.inr a) = Sum.inr b) :
    ∃ (φ : Bool × Fin k ≃ Fin k ⊕ Fin k) (r₀ : Fin k),
      D.IsArcParam φ ∧ φ (false, r₀) = Sum.inr a ∧ φ (true, r₀) = Sum.inr b := by
  let r₀ : Fin k := (D.arcParam.symm (Sum.inr a)).2
  let φ : Bool × Fin k ≃ Fin k ⊕ Fin k :=
    (Equiv.prodCongrLeft fun r =>
      if r = r₀ ∧ (D.arcParam.symm (Sum.inr a)).1 then Equiv.swap false true else 1).trans
        D.arcParam
  have hφ : D.IsArcParam φ := D.isArcParam_arcParam.flipEndpoints _
  have hφ_false : φ (false, r₀) = Sum.inr a := by
    rcases hs : D.arcParam.symm (Sum.inr a) with ⟨_ | _, r⟩ <;>
      simpa [φ, r₀, hs] using D.arcParam.apply_symm_apply (Sum.inr a)
  exact ⟨φ, r₀, hφ, hφ_false, by rw [← hφ r₀, hφ_false, hcup]⟩

/-- When `D` does not cup `a` to `b` (`a ≠ b`), some arc parametrization of `D` orients the two
distinct arcs meeting `Sum.inr a` and `Sum.inr b` so that `Sum.inr a` and `Sum.inr b` are their
`(true, ·)` endpoints. -/
private theorem exists_isArcParam_of_ne_cup {D : BrauerDiagram k} {a b : Fin k} (hab : a ≠ b)
    (hcup : D.val (Sum.inr a) ≠ Sum.inr b) :
    ∃ (φ : Bool × Fin k ≃ Fin k ⊕ Fin k) (r₁ r₂ : Fin k),
      D.IsArcParam φ ∧ r₁ ≠ r₂ ∧
        φ (false, r₁) = D.val (Sum.inr a) ∧ φ (true, r₁) = Sum.inr a ∧
        φ (false, r₂) = D.val (Sum.inr b) ∧ φ (true, r₂) = Sum.inr b := by
  let φ : Bool × Fin k ≃ Fin k ⊕ Fin k :=
    (Equiv.prodCongrLeft fun r =>
      if D.arcParam (false, r) = Sum.inr a ∨ D.arcParam (false, r) = Sum.inr b then
        Equiv.swap false true
      else 1).trans D.arcParam
  have hφ : D.IsArcParam φ := D.isArcParam_arcParam.flipEndpoints _
  have htrue {c : Fin k} (hc : c = a ∨ c = b) : φ (true, (φ.symm (Sum.inr c)).2) = Sum.inr c := by
    rcases hs : φ.symm (Sum.inr c) with ⟨_ | _, r⟩
    · have hf : φ (false, r) = Sum.inr c := by simpa [hs] using φ.apply_symm_apply (Sum.inr c)
      by_cases hcond : D.arcParam (false, r) = Sum.inr a ∨ D.arcParam (false, r) = Sum.inr b
      · have hd : D.val (D.arcParam (false, r)) = Sum.inr c := by
          simpa [φ, hcond, ← D.isArcParam_arcParam r] using hf
        rcases hcond with h1 | h1 <;> rw [h1] at hd <;> rcases hc with rfl | rfl
        · exact absurd hd (D.apply_ne _)
        · exact absurd hd hcup
        · exact absurd (D.apply_eq_of_apply_eq hd) hcup
        · exact absurd hd (D.apply_ne _)
      · have hf' : D.arcParam (false, r) = Sum.inr c := by simpa [φ, hcond] using hf
        exact absurd (hc.imp (fun h => hf'.trans (congrArg Sum.inr h))
          (fun h => hf'.trans (congrArg Sum.inr h))) hcond
    · simpa [hs] using φ.apply_symm_apply (Sum.inr c)
  let r₁ : Fin k := (φ.symm (Sum.inr a)).2
  let r₂ : Fin k := (φ.symm (Sum.inr b)).2
  have ht₁ : φ (true, r₁) = Sum.inr a := htrue (Or.inl rfl)
  have ht₂ : φ (true, r₂) = Sum.inr b := htrue (Or.inr rfl)
  have hr₁₂ : r₁ ≠ r₂ := fun h => Sum.inr_injective.ne hab (by rw [← ht₁, h, ht₂])
  exact ⟨φ, r₁, r₂, hφ, hr₁₂, by simpa [← ht₁] using (hφ.val_apply true r₁).symm, ht₁,
    by simpa [← ht₂] using (hφ.val_apply true r₂).symm, ht₂⟩

/-- Updating `v` at `a` and `b` leaves `Sum.elim u v` unchanged at every boundary point other than
`Sum.inr a` and `Sum.inr b`. -/
private theorem sumElim_update_update_of_ne {α : Type*} {a b : Fin k} {z : Fin k ⊕ Fin k}
    (hza : z ≠ Sum.inr a) (hzb : z ≠ Sum.inr b) (u v : Fin k → α) (x y : α) :
    Sum.elim u (Function.update (Function.update v a x) b y) z = Sum.elim u v z := by
  rcases z with _ | j
  · rfl
  · simp only [Sum.elim_inr]
    rw [Function.update_of_ne (fun h => hzb (congrArg Sum.inr h)),
      Function.update_of_ne (fun h => hza (congrArg Sum.inr h))]

/-- The closed-loop case of `symplecticActionMatrix_capCup_mul`, when `D` already cups `a` to `b`.
-/
private theorem symplecticActionMatrix_capCup_mul_of_cup [Fintype ι] {a b : Fin k} (hab : a ≠ b)
    {D : BrauerDiagram k} (hcup : D.val (Sum.inr a) = Sum.inr b) (v u : Fin k → ι ⊕ ι) :
    (∑ x : ι ⊕ ι, ∑ y : ι ⊕ ι,
        -(Matrix.J ι R x y * Matrix.J ι R (v a) (v b)) *
          D.symplecticActionMatrix R ι (Function.update (Function.update v a x) b y) u) =
      (-(2 * Fintype.card ι : R)) * D.symplecticActionMatrix R ι v u := by
  obtain ⟨φ, r₀, hφ, hφ_false, hφ_true⟩ := exists_isArcParam_of_cup hcup
  set S := ((Equiv.Perm.sign ((Equiv.boolProdEquivSum (Fin k)).symm.trans φ) : ℤ) : R)
  set P := ∏ r ∈ Finset.univ.erase r₀,
    symplecticArcWeight R ι (φ (false, r)) (Sum.elim u v (φ (false, r)))
      (φ (true, r)) (Sum.elim u v (φ (true, r)))
  have hterm (x y : ι ⊕ ι) :
      D.symplecticActionMatrix R ι (Function.update (Function.update v a x) b y) u =
        S * (Matrix.J ι R x y * P) := by
    rw [symplecticActionMatrix_apply_of_isArcParam R ι hφ,
      ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ r₀)]
    congr 2
    · simp [hφ_false, hφ_true, Function.update_of_ne hab]
    · refine Finset.prod_congr rfl fun r hr => ?_
      have hr₀ : r ≠ r₀ := (Finset.mem_erase.mp hr).1
      have hne (c : Bool) : φ (c, r) ≠ Sum.inr a ∧ φ (c, r) ≠ Sum.inr b :=
        ⟨fun h => hr₀ (Prod.mk.inj (φ.injective (h.trans hφ_false.symm))).2,
          fun h => hr₀ (Prod.mk.inj (φ.injective (h.trans hφ_true.symm))).2⟩
      rw [sumElim_update_update_of_ne (hne false).1 (hne false).2,
        sumElim_update_update_of_ne (hne true).1 (hne true).2]
  have htarget : D.symplecticActionMatrix R ι v u = S * (Matrix.J ι R (v a) (v b) * P) := by
    rw [symplecticActionMatrix_apply_of_isArcParam R ι hφ,
      ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ r₀), hφ_false, hφ_true]
    simp [S, P]
  have hrewrite (x y : ι ⊕ ι) :
      -(Matrix.J ι R x y * Matrix.J ι R (v a) (v b)) * (S * (Matrix.J ι R x y * P)) =
        Matrix.J ι R x y * Matrix.J ι R x y * (-(S * (Matrix.J ι R (v a) (v b) * P))) := by
    ring
  simp only [hterm, hrewrite, ← Finset.sum_mul, Matrix.sum_sum_J_mul_J, htarget]
  ring

/-- The loop-free case of `symplecticActionMatrix_capCup_mul`, when `D` does not cup `a` to `b`. -/
private theorem symplecticActionMatrix_capCup_mul_of_ne_cup [Fintype ι] {a b : Fin k} (hab : a ≠ b)
    {D : BrauerDiagram k} (hcup : D.val (Sum.inr a) ≠ Sum.inr b) (v u : Fin k → ι ⊕ ι) :
    (∑ x : ι ⊕ ι, ∑ y : ι ⊕ ι,
        -(Matrix.J ι R x y * Matrix.J ι R (v a) (v b)) *
          D.symplecticActionMatrix R ι (Function.update (Function.update v a x) b y) u) =
      symplecticActionMatrix R ι (D.reconnect (Sum.inr a) (Sum.inr b)) v u := by
  obtain ⟨φ, r₁, r₂, hφ, hr₁₂, hφ_false₁, hφ_true₁, hφ_false₂, hφ_true₂⟩ :=
    exists_isArcParam_of_ne_cup hab hcup
  set p := D.val (Sum.inr a)
  set q := D.val (Sum.inr b) with hq_def
  have hpa : p ≠ Sum.inr a := D.apply_ne (Sum.inr a)
  have hqb : q ≠ Sum.inr b := D.apply_ne (Sum.inr b)
  have hqa : q ≠ Sum.inr a := fun h => hcup (D.apply_eq_of_apply_eq (hq_def.symm.trans h))
  have hrest_ne {r : Fin k} (hr₁ : r ≠ r₁) (hr₂ : r ≠ r₂) (c : Bool) :
      φ (c, r) ≠ p ∧ φ (c, r) ≠ Sum.inr a ∧ φ (c, r) ≠ q ∧ φ (c, r) ≠ Sum.inr b :=
    ⟨fun h => hr₁ (Prod.mk.inj (φ.injective (h.trans hφ_false₁.symm))).2,
      fun h => hr₁ (Prod.mk.inj (φ.injective (h.trans hφ_true₁.symm))).2,
      fun h => hr₂ (Prod.mk.inj (φ.injective (h.trans hφ_false₂.symm))).2,
      fun h => hr₂ (Prod.mk.inj (φ.injective (h.trans hφ_true₂.symm))).2⟩
  set S := ((Equiv.Perm.sign ((Equiv.boolProdEquivSum (Fin k)).symm.trans φ) : ℤ) : R)
  set P := ∏ r ∈ (Finset.univ.erase r₁).erase r₂,
    symplecticArcWeight R ι (φ (false, r)) (Sum.elim u v (φ (false, r)))
      (φ (true, r)) (Sum.elim u v (φ (true, r)))
  have hterm (x y : ι ⊕ ι) :
      D.symplecticActionMatrix R ι (Function.update (Function.update v a x) b y) u =
        S * (symplecticArcWeight R ι p (Sum.elim u v p) (Sum.inr a) x *
          (symplecticArcWeight R ι q (Sum.elim u v q) (Sum.inr b) y * P)) := by
    rw [symplecticActionMatrix_apply_of_isArcParam R ι hφ,
      ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ r₁),
      ← Finset.mul_prod_erase (Finset.univ.erase r₁) _
        (Finset.mem_erase.mpr ⟨hr₁₂.symm, Finset.mem_univ r₂⟩)]
    refine congrArg (S * ·) (congrArg₂ (· * ·) ?_ (congrArg₂ (· * ·) ?_ ?_))
    · rw [hφ_false₁, hφ_true₁, sumElim_update_update_of_ne hpa hcup]
      simp [Function.update_of_ne hab]
    · rw [hφ_false₂, hφ_true₂, sumElim_update_update_of_ne hqa hqb]
      simp
    · refine Finset.prod_congr rfl fun r hr => ?_
      have hr₂' : r ≠ r₂ := (Finset.mem_erase.mp hr).1
      have hr₁' : r ≠ r₁ := (Finset.mem_erase.mp (Finset.mem_erase.mp hr).2).1
      rw [sumElim_update_update_of_ne (hrest_ne hr₁' hr₂' false).2.1
          (hrest_ne hr₁' hr₂' false).2.2.2,
        sumElim_update_update_of_ne (hrest_ne hr₁' hr₂' true).2.1
          (hrest_ne hr₁' hr₂' true).2.2.2]
  let σ : Equiv.Perm (Fin k ⊕ Fin k) := Equiv.swap p (Sum.inr b)
  have hφ' : IsArcParam (D.reconnect (Sum.inr a) (Sum.inr b)) (φ.trans σ) := fun r => by
    rw [PerfectMatching.reconnect_val]
    simp [σ, p, hφ r]
  have htarget :
      symplecticActionMatrix R ι (D.reconnect (Sum.inr a) (Sum.inr b)) v u =
        -S * (-Matrix.J ι R (v a) (v b) *
          (-symplecticArcWeight R ι p (Sum.elim u v p) q (Sum.elim u v q) * P)) := by
    rw [symplecticActionMatrix_apply_of_isArcParam R ι hφ',
      ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ r₁),
      ← Finset.mul_prod_erase (Finset.univ.erase r₁) _
        (Finset.mem_erase.mpr ⟨hr₁₂.symm, Finset.mem_univ r₂⟩)]
    have hsign' :
        ((Equiv.Perm.sign ((Equiv.boolProdEquivSum (Fin k)).symm.trans (φ.trans σ)) : ℤ) : R) =
          -S := by
      have hperm : (Equiv.boolProdEquivSum (Fin k)).symm.trans (φ.trans σ) =
          ((Equiv.boolProdEquivSum (Fin k)).symm.trans φ).trans σ := rfl
      rw [hperm, Equiv.Perm.sign_trans, Equiv.Perm.sign_swap hcup]
      simp [S]
    have hpq : q ≠ p := fun h => hab (Sum.inr_injective (D.val.injective h.symm))
    rw [hsign']
    refine congrArg (-S * ·) (congrArg₂ (· * ·) ?_ (congrArg₂ (· * ·) ?_ ?_))
    · simp only [Equiv.trans_apply, σ, hφ_false₁, hφ_true₁, Equiv.swap_apply_left,
        Equiv.swap_apply_of_ne_of_ne hpa.symm (Sum.inr_injective.ne hab), Sum.elim_inr,
        symplecticArcWeight_inr_inr]
      exact Matrix.J_apply_swap ι R (v a) (v b)
    · simp only [Equiv.trans_apply, σ, hφ_false₂, hφ_true₂, Equiv.swap_apply_of_ne_of_ne hpq hqb,
        Equiv.swap_apply_right]
      exact symplecticArcWeight_swap R ι _ _ _ _
    · refine Finset.prod_congr rfl fun r hr => ?_
      have hr₂' : r ≠ r₂ := (Finset.mem_erase.mp hr).1
      have hr₁' : r ≠ r₁ := (Finset.mem_erase.mp (Finset.mem_erase.mp hr).2).1
      simp [σ, Equiv.swap_apply_of_ne_of_ne (hrest_ne hr₁' hr₂' false).1
        (hrest_ne hr₁' hr₂' false).2.2.2,
        Equiv.swap_apply_of_ne_of_ne (hrest_ne hr₁' hr₂' true).1
          (hrest_ne hr₁' hr₂' true).2.2.2]
  have hfactor (x y : ι ⊕ ι) :
      -(Matrix.J ι R x y * Matrix.J ι R (v a) (v b)) *
          (S * (symplecticArcWeight R ι p (Sum.elim u v p) (Sum.inr a) x *
            (symplecticArcWeight R ι q (Sum.elim u v q) (Sum.inr b) y * P))) =
        (symplecticArcWeight R ι p (Sum.elim u v p) (Sum.inr a) x * Matrix.J ι R x y *
            symplecticArcWeight R ι q (Sum.elim u v q) (Sum.inr b) y) *
          (-(S * Matrix.J ι R (v a) (v b) * P)) := by
    ring
  simp only [hterm, htarget, hfactor, ← Finset.sum_mul, sum_symplecticArcWeight_mul_J]
  ring

/-- Stacking `capCup a b` (`a ≠ b`) above `D` obeys the symplectic loop rule. -/
private theorem symplecticActionMatrix_capCup_mul [Fintype ι] {a b : Fin k} (hab : a ≠ b)
    (D : BrauerDiagram k) :
    (capCup a b).symplecticActionMatrix R ι * D.symplecticActionMatrix R ι =
      (-(2 * Fintype.card ι : R)) ^ middleLoopCount (capCup a b) D •
        (composeDiagram (capCup a b) D).symplecticActionMatrix R ι := by
  ext v u
  rw [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul, composeDiagram_capCup_left,
    middleLoopCount_capCup_left hab]
  have hcond (m : Fin k → ι ⊕ ι) :
      (∀ t, t ≠ a → t ≠ b → v t = m t) ↔
        m = Function.update (Function.update v a (m a)) b (m b) := by
    simp only [Function.eq_update_iff, true_and]
    refine ⟨fun h t htb => ?_, fun h t hta htb => ((h t htb).trans (by simp [hta])).symm⟩
    rcases eq_or_ne t a with rfl | hta
    · simp
    · simp [hta, (h t hta htb).symm]
  simp only [symplecticActionMatrix_capCup R ι hab, ite_mul, zero_mul, hcond]
  refine (Fintype.sum_ite_eq_update_update (M := R) v hab _).trans ?_
  simp only [Function.update_of_ne hab, Function.update_self]
  split_ifs with hcup
  · have hrec : D.reconnect (Sum.inr a) (Sum.inr b) = D :=
      hcup ▸ PerfectMatching.reconnect_partner D (Sum.inr a)
    rw [pow_one, hrec]
    exact symplecticActionMatrix_capCup_mul_of_cup R ι hab hcup v u
  · rw [pow_zero, one_mul]
    exact symplecticActionMatrix_capCup_mul_of_ne_cup R ι hab hcup v u

/-- **The loop rule for the symplectic matrices of Brauer diagrams.** Multiplying the matrices of
`D₁` and `D₂` gives the matrix of `composeDiagram D₁ D₂` scaled by `(-(2 * |ι|)) ^ c`, where `c` is
the number of closed loops formed in the middle boundary. -/
theorem symplecticActionMatrix_mul [Fintype ι] (D₁ D₂ : BrauerDiagram k) :
    D₁.symplecticActionMatrix R ι * D₂.symplecticActionMatrix R ι =
      (-(2 * Fintype.card ι : R)) ^ middleLoopCount D₁ D₂ •
        (composeDiagram D₁ D₂).symplecticActionMatrix R ι := by
  induction D₁ using BrauerDiagram.capCup_induction_on generalizing D₂ with
  | permToBrauer σ =>
    rw [symplecticActionMatrix_permToBrauer_mul, middleLoopCount_permToBrauer_left, pow_zero,
      one_smul]
  | capCup_compose a b X hab hloop ih =>
    have hX : (composeDiagram (capCup a b) X).symplecticActionMatrix R ι =
        (capCup a b).symplecticActionMatrix R ι * X.symplecticActionMatrix R ι := by
      rw [symplecticActionMatrix_capCup_mul R ι hab X, hloop, pow_zero, one_smul]
    have hassoc := middleLoopCount_add_middleLoopCount_composeDiagram (capCup a b) X D₂
    rw [hloop, zero_add] at hassoc
    rw [hX, Matrix.mul_assoc, ih D₂, Algebra.mul_smul_comm,
      symplecticActionMatrix_capCup_mul R ι hab (composeDiagram X D₂), composeDiagram_assoc,
      smul_smul, ← pow_add, ← hassoc]

/-! ### Reflection, transpose, and conjugate transpose -/

/-- The number of non-through arcs of `D` equals `D.bottomCap.card` (twice the number of caps). -/
private theorem card_filter_not_isThrough_arcParam (D : BrauerDiagram k) :
    (Finset.univ.filter fun r : Fin k => ¬D.IsThrough (D.arcParam (false, r))).card =
      D.bottomCap.card := by
  let S : Finset (Bool × Fin k) := Finset.univ.filter fun p => ¬D.IsThrough (D.arcParam p)
  have hS₁ : S.card =
      2 * (Finset.univ.filter fun r : Fin k => ¬D.IsThrough (D.arcParam (false, r))).card := by
    have hiff (b : Bool) (r : Fin k) :
        ¬D.IsThrough (D.arcParam (b, r)) ↔ ¬D.IsThrough (D.arcParam (false, r)) := by
      cases b
      · exact Iff.rfl
      · rw [← D.isArcParam_arcParam r, D.isThrough_val]
    have hprod : S = (Finset.univ : Finset Bool) ×ˢ
        (Finset.univ.filter fun r : Fin k => ¬D.IsThrough (D.arcParam (false, r))) := by
      ext ⟨b, r⟩
      simp [S, hiff b r]
    rw [hprod, Finset.card_product]
    simp
  have hS₂ : S.card = 2 * D.bottomCap.card := by
    have himg : S.map D.arcParam.toEmbedding = D.bottomCap.disjSum D.topCup := by
      ext (i | j) <;> simp [S, D.isCap_inl_iff, D.isCup_inr_iff]
    rw [← Finset.card_map D.arcParam.toEmbedding, himg, Finset.card_disjSum,
      ← D.card_bottomCap_eq_card_topCup, two_mul]
  omega

/-- **Reflecting a diagram transposes its symplectic matrix**: horizontal reflection swaps inputs
with outputs, picking up `-1` on each cap and each cup, and a Brauer diagram has an even number of
non-through arcs so their signs cancel. -/
@[simp]
theorem transpose_symplecticActionMatrix (D : BrauerDiagram k) :
    (D.symplecticActionMatrix R ι)ᵀ = D.flip.symplecticActionMatrix R ι := by
  ext v u
  rw [Matrix.transpose_apply]
  let φ_flip : Bool × Fin k ≃ Fin k ⊕ Fin k :=
    (Equiv.prodCongr (Equiv.swap false true) (Equiv.refl (Fin k))).trans
      (D.arcParam.trans (Equiv.sumComm (Fin k) (Fin k)))
  have hφ_flip : D.flip.IsArcParam φ_flip := fun r => by
    simp [φ_flip, flip_val_swap, D.isArcParam_arcParam.val_apply]
  rw [symplecticActionMatrix_apply_of_isArcParam R ι D.isArcParam_arcParam u v,
    symplecticActionMatrix_apply_of_isArcParam R ι hφ_flip v u]
  have hconj :
      (Equiv.boolProdEquivSum (Fin k)).symm.trans φ_flip =
        (Equiv.sumComm (Fin k) (Fin k)).permCongr
          ((Equiv.boolProdEquivSum (Fin k)).symm.trans D.arcParam) := by
    ext x
    rcases x with r | r <;> simp [φ_flip]
  rw [hconj, Equiv.Perm.sign_permCongr]
  congr 1
  have hswap_elim (z : Fin k ⊕ Fin k) : Sum.elim u v z.swap = Sum.elim v u z := by
    rcases z with _ | _ <;> rfl
  have hterm (r : Fin k) :
      symplecticArcWeight R ι (φ_flip (false, r)) (Sum.elim u v (φ_flip (false, r)))
          (φ_flip (true, r)) (Sum.elim u v (φ_flip (true, r))) =
        (if D.IsThrough (D.arcParam (false, r)) then (1 : R) else -1) *
          symplecticArcWeight R ι (D.arcParam (false, r)) (Sum.elim v u (D.arcParam (false, r)))
            (D.arcParam (true, r)) (Sum.elim v u (D.arcParam (true, r))) := by
    have hf : φ_flip (false, r) = (D.val (D.arcParam (false, r))).swap := by
      simp [φ_flip, ← D.isArcParam_arcParam r]
    have ht : φ_flip (true, r) = (D.arcParam (false, r)).swap := by simp [φ_flip]
    rw [hf, ht, hswap_elim, hswap_elim, symplecticArcWeight_sumSwap, D.isArcParam_arcParam r]
  rw [Finset.prod_congr rfl fun r _ => hterm r, Finset.prod_mul_distrib, Finset.prod_ite,
    Finset.prod_const_one, one_mul, Finset.prod_const, card_filter_not_isThrough_arcParam,
    D.even_card_bottomCap.neg_one_pow, one_mul]

/-- Every entry of `TauCeti.BrauerDiagram.symplecticActionMatrix` is an integer cast, which every
star structure fixes, so its conjugate transpose equals its transpose, the matrix of the reflected
diagram. -/
@[simp]
theorem conjTranspose_symplecticActionMatrix [StarRing R] (D : BrauerDiagram k) :
    (D.symplecticActionMatrix R ι)ᴴ = D.flip.symplecticActionMatrix R ι := by
  rw [← transpose_symplecticActionMatrix]
  ext v u
  rw [Matrix.conjTranspose_apply, Matrix.transpose_apply,
    symplecticActionMatrix_apply_of_isArcParam R ι D.isArcParam_arcParam, star_mul', star_intCast,
    star_prod, Finset.prod_congr rfl fun _ _ => star_symplecticArcWeight R ι _ _ _ _, mul_comm]

end BrauerDiagram

end TauCeti
