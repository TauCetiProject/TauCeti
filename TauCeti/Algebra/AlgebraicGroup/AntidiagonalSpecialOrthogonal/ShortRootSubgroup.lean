/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.AntidiagonalSpecialOrthogonal.DiagonalTorus
public import TauCeti.Algebra.AlgebraicGroup.AntidiagonalSpecialOrthogonal.RootSubgroup
public import TauCeti.Algebra.AlgebraicGroup.SplitTorus.Weight
public import TauCeti.Algebra.Ring.Invertible
public import TauCeti.LinearAlgebra.Matrix.Exponential.CubeZero

/-!
# Short root subgroups of `SO_l^J` for odd `l`

Let `l` be odd, `m` the middle index (`m = l - 1 - m`), and `i ≠ m` another index, with mirror
image `i' = l - 1 - i`. The nilpotent matrix `N = E_im - E_{m i'}` (`rootNilpotent i m`) satisfies
`N² = -E_{i i'}` and `N³ = 0`, and `N J_l` is antisymmetric. Over a ring containing `½`, put

```text
x_i(a) = 1 + a N + ½ a² N² = 1 + a(E_im - E_{m i'}) - ½ a² E_{i i'}.
```

This is the exponential of `a N` (`TauCeti.RingTheory.Nilpotent.Exp.CubeZero`), so
`x_i(a + b) = x_i(a) x_i(b)`, it preserves `J_l`, and it has determinant one; `a ↦ x_i(a)` is a
homomorphism `𝔾ₐ → SO_l^J`, promoted here to a closed immersion of affine group schemes over every
ring containing `½`. For `l = 3` and `i = 0` it is the matrix
with rows `(1, a, -a²/2)`, `(0, 1, -a)`, `(0, 0, 1)`; its entry `-a²/2` is why `2` must be
invertible. For `i < m` it is the root subgroup of the short root `ε_i` of the diagonal torus, and
conjugation by `d = diag(d_k)` with `d_{k'} = d_k⁻¹` and `d_m = 1` scales its parameter by `d_i`.

The construction of the group-scheme morphism follows `TauCeti.AntidiagonalSpecialOrthogonal`'s
long root subgroups (`TauCeti.Algebra.AlgebraicGroup.AntidiagonalSpecialOrthogonal.RootSubgroup`).

## Main declarations

* `TauCeti.AntidiagonalSpecialOrthogonal.ShortRootIndex`: a pair `(i, m)` as above.
* `TauCeti.AntidiagonalSpecialOrthogonal.shortRootMatrix`: the matrix `x_i(a)`, with
  `shortRootMatrix_mul_formMatrix_mul_transpose`, `det_shortRootMatrix`, `shortRootMatrix_add`
  and `shortRootMatrix_apply_i_rev`.
* `TauCeti.AntidiagonalSpecialOrthogonal.diagonal_mul_shortRootMatrix_mul_diagonal_inv` and
  `TauCeti.AntidiagonalSpecialOrthogonal.diagonalTorusPoints_mul_shortRootSubgroupPoints_mul_inv`:
  the diagonal torus acts on `x_i` through the weight `w_i` of the `i`-th diagonal entry.
* `TauCeti.AntidiagonalSpecialOrthogonal.shortRootSubgroupCoordinateMap` and
  `TauCeti.AntidiagonalSpecialOrthogonal.shortRootSubgroup`: the coordinate morphism and the
  closed immersion `𝔾ₐ → SO_l^J`, with `pointsMulEquiv_shortRootSubgroupPoints` on points.

## References

* J. E. Humphreys, *Linear Algebraic Groups* (1975), §26.3, for the root subgroups of the
  orthogonal groups in the antidiagonal model.
-/

public section

open AlgebraicGeometry CategoryTheory Matrix WithConv

namespace TauCeti.AntidiagonalSpecialOrthogonal

universe u v w

/-! ### The matrices -/

/-- **An index pair for a short root subgroup of `SO_l^J`**: the middle index `m = l - 1 - m` of
odd `l` and another index `i ≠ m`. -/
structure ShortRootIndex (l : ℕ) where
  /-- The index of the short root. -/
  i : Fin l
  /-- The middle index. -/
  m : Fin l
  rev_m : Fin.rev m = m
  ne : i ≠ m

namespace ShortRootIndex

variable {l : ℕ} (s : ShortRootIndex l)

/-- The index `i` is not its own mirror image: only the middle index is. -/
theorem i_ne_rev : s.i ≠ Fin.rev s.i := by
  intro h
  have h1 := congrArg Fin.val h
  have h2 := congrArg Fin.val s.rev_m
  rw [Fin.val_rev] at h1 h2
  exact s.ne (Fin.ext (by omega))

/-- The mirror image of `i` is not the middle index. -/
theorem rev_ne_m : Fin.rev s.i ≠ s.m := fun h =>
  s.ne (by rw [← Fin.rev_rev s.i, h, s.rev_m])

end ShortRootIndex

section Matrices

variable {A : Type w} [CommRing A] {l : ℕ} (s : ShortRootIndex l)

/-- `N = E_im - E_{m i'}` for the middle index `m`. -/
theorem rootNilpotent_shortRoot :
    rootNilpotent (A := A) s.i s.m = single s.i s.m 1 - single s.m (Fin.rev s.i) 1 := by
  rw [rootNilpotent_def, s.rev_m]

/-- `N² = -E_{i i'}`. -/
theorem rootNilpotent_shortRoot_mul_self :
    rootNilpotent (A := A) s.i s.m * rootNilpotent s.i s.m = -single s.i (Fin.rev s.i) 1 := by
  rw [rootNilpotent_shortRoot, sub_mul, mul_sub, mul_sub,
    single_mul_single_of_ne _ _ _ _ s.ne.symm, single_mul_single_same,
    single_mul_single_of_ne _ _ _ _ s.rev_ne_m, single_mul_single_of_ne _ _ _ _ s.i_ne_rev.symm]
  simp

/-- `N³ = 0`. -/
theorem rootNilpotent_shortRoot_mul_self_mul_self :
    rootNilpotent (A := A) s.i s.m * rootNilpotent s.i s.m * rootNilpotent s.i s.m = 0 := by
  rw [rootNilpotent_shortRoot_mul_self, rootNilpotent_shortRoot, neg_mul, mul_sub,
    single_mul_single_of_ne _ _ _ _ s.rev_ne_m, single_mul_single_of_ne _ _ _ _ s.i_ne_rev.symm]
  simp

/-- **The short root matrix** `x_i(a) = 1 + a N + h a² N²`, where `h` plays the role of `½`. -/
def shortRootMatrix (h a : A) : Matrix (Fin l) (Fin l) A :=
  1 + a • rootNilpotent s.i s.m + (h * a * a) • (rootNilpotent s.i s.m * rootNilpotent s.i s.m)

/-- The short root matrix is `1 + a N + h a² N²`. -/
theorem shortRootMatrix_def (h a : A) :
    shortRootMatrix s h a =
      1 + a • rootNilpotent s.i s.m +
        (h * a * a) • (rootNilpotent s.i s.m * rootNilpotent s.i s.m) :=
  (rfl)

/-- The short root matrix is `1 + a(E_im - E_{m i'}) - h a² E_{i i'}`. -/
theorem shortRootMatrix_eq (h a : A) :
    shortRootMatrix s h a =
      1 + a • (single s.i s.m 1 - single s.m (Fin.rev s.i) 1) -
        (h * a * a) • single s.i (Fin.rev s.i) 1 := by
  rw [shortRootMatrix_def, rootNilpotent_shortRoot_mul_self, rootNilpotent_shortRoot, smul_neg,
    ← sub_eq_add_neg]

/-- `x_i(0) = 1`. -/
@[simp]
theorem shortRootMatrix_zero (h : A) : shortRootMatrix s h 0 = 1 := by
  simp [shortRootMatrix_def]

/-- **`x_i(a + b) = x_i(a) x_i(b)`** when `2h = 1`. -/
theorem shortRootMatrix_add {h : A} (hh : 2 * h = 1) (a b : A) :
    shortRootMatrix s h (a + b) = shortRootMatrix s h a * shortRootMatrix s h b :=
  one_add_smul_add_smul_mul_self_add hh (rootNilpotent_shortRoot_mul_self_mul_self s) a b

/-- **`x_i(a)` preserves `J_l`** when `2h = 1`: `x_i(a) J_l x_i(a)ᵀ = J_l`. -/
theorem shortRootMatrix_mul_formMatrix_mul_transpose {h : A} (hh : 2 * h = 1) (a : A) :
    shortRootMatrix s h a * formMatrix A l * (shortRootMatrix s h a)ᵀ = formMatrix A l :=
  one_add_smul_add_smul_mul_self_mul_mul_transpose _ hh
    (rootNilpotent_shortRoot_mul_self_mul_self s) (formMatrix_mul_transpose_rootNilpotent s.i s.m) a

/-- `x_i(a)` is the product of the transvections `1 + a E_im`, `1 - a E_{m i'}` and
`1 + (a² - h a²) E_{i i'}`. -/
theorem shortRootMatrix_eq_transvection_mul (h a : A) :
    shortRootMatrix s h a =
      transvection s.i s.m a * transvection s.m (Fin.rev s.i) (-a) *
        transvection s.i (Fin.rev s.i) (a * a - h * a * a) := by
  rw [shortRootMatrix_eq]
  simp only [transvection, add_mul, mul_add, Matrix.one_mul, Matrix.mul_one,
    single_mul_single_same, single_mul_single_of_ne _ _ _ _ s.ne.symm,
    single_mul_single_of_ne _ _ _ _ s.i_ne_rev.symm, add_zero]
  refine Matrix.ext fun p q => ?_
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, single_apply, smul_eq_mul]
  split_ifs <;> ring

/-- **`x_i(a)` has determinant one.** -/
@[simp]
theorem det_shortRootMatrix (h a : A) : (shortRootMatrix s h a).det = 1 := by
  rw [shortRootMatrix_eq_transvection_mul, det_mul, det_mul, det_transvection_of_ne _ _ s.ne,
    det_transvection_of_ne _ _ fun h => s.rev_ne_m h.symm,
    det_transvection_of_ne _ _ s.i_ne_rev, mul_one, mul_one]

/-- The entry of `x_i(a)` at `(i, m)` is `a`. -/
@[simp]
theorem shortRootMatrix_apply_i_m (h a : A) : shortRootMatrix s h a s.i s.m = a := by
  rw [shortRootMatrix_eq]
  simp [Matrix.one_apply_ne s.ne, s.ne.symm, s.rev_ne_m]

/-- **The entry of `x_i(a)` at `(i, i')` is `-h a²`**, that is `-a²/2`. -/
@[simp]
theorem shortRootMatrix_apply_i_rev (h a : A) :
    shortRootMatrix s h a s.i (Fin.rev s.i) = -(h * a * a) := by
  rw [shortRootMatrix_eq]
  simp [Matrix.one_apply_ne s.i_ne_rev, s.ne.symm, s.rev_ne_m.symm]

/-- Mapping a short root matrix entrywise along a ring homomorphism maps `h` and `a`. -/
theorem map_shortRootMatrix {B : Type v} [CommRing B] (f : A →+* B) (h a : A) :
    (shortRootMatrix s h a).map f = shortRootMatrix s (f h) (f a) := by
  refine Matrix.ext fun p q => ?_
  simp [shortRootMatrix_eq, Matrix.one_apply, Matrix.single_apply, apply_ite f]

/-- **Conjugating a short root matrix by a diagonal matrix of the torus shape.** If
`d_{k'} = d_k⁻¹` for every `k` and `d_m = 1`, then `d x_i(a) d⁻¹ = x_i(d_i a)`. -/
theorem diagonal_mul_shortRootMatrix_mul_diagonal_inv (d : Fin l → Aˣ)
    (hd : ∀ k, d (Fin.rev k) = (d k)⁻¹) (hm : d s.m = 1) (h a : A) :
    diagonal (fun k ↦ (d k : A)) * shortRootMatrix s h a *
        diagonal (fun k ↦ (((d k)⁻¹ : Aˣ) : A)) =
      shortRootMatrix s h ((d s.i : A) * a) := by
  have hi' : ((d (Fin.rev s.i))⁻¹ : Aˣ) = d s.i := by rw [hd, inv_inv]
  have h1 := s.ne
  have h2 := s.i_ne_rev
  have h3 := s.rev_ne_m
  have h1' := s.ne.symm
  have h3' := s.rev_ne_m.symm
  refine Matrix.ext fun p q => ?_
  rw [mul_diagonal, diagonal_mul, shortRootMatrix_eq, shortRootMatrix_eq]
  by_cases hpq : p = q
  · subst hpq
    have h4 : ¬(s.i = p ∧ s.m = p) := fun h => h1 (h.1.trans h.2.symm)
    have h5 : ¬(s.m = p ∧ Fin.rev s.i = p) := fun h => h3 (h.2.trans h.1.symm)
    have h6 : ¬(s.i = p ∧ Fin.rev s.i = p) := fun h => h2 (h.1.trans h.2.symm)
    simp [h4, h5, h6]
  by_cases him : p = s.i ∧ q = s.m
  · obtain ⟨rfl, rfl⟩ := him
    simp [h1, h1', h3, hm]
  by_cases hmi : p = s.m ∧ q = Fin.rev s.i
  · obtain ⟨rfl, rfl⟩ := hmi
    simp [h1, h3', hi', hm]
    ring
  by_cases hii : p = s.i ∧ q = Fin.rev s.i
  · obtain ⟨rfl, rfl⟩ := hii
    simp [h1', h2, h3', hi']
    ring
  have h4 : ¬(s.i = p ∧ s.m = q) := fun h => him ⟨h.1.symm, h.2.symm⟩
  have h5 : ¬(s.m = p ∧ Fin.rev s.i = q) := fun h => hmi ⟨h.1.symm, h.2.symm⟩
  have h6 : ¬(s.i = p ∧ Fin.rev s.i = q) := fun h => hii ⟨h.1.symm, h.2.symm⟩
  simp [Matrix.one_apply_ne hpq, h4, h5, h6]

end Matrices

/-! ### The homomorphism on points -/

section Points

variable {l : ℕ} (s : ShortRootIndex l) {A : Type w} [CommRing A] {h : A} (hh : 2 * h = 1)

/-- The short root subgroup `a ↦ x_i(a)` as a homomorphism into `GL_l(A)`, given `h` with
`2h = 1`. -/
def shortRootHom : Multiplicative A →* GL (Fin l) A where
  toFun a :=
    ⟨shortRootMatrix s h a.toAdd, shortRootMatrix s h (-a.toAdd),
      by rw [← shortRootMatrix_add s hh, add_neg_cancel, shortRootMatrix_zero],
      by rw [← shortRootMatrix_add s hh, neg_add_cancel, shortRootMatrix_zero]⟩
  map_one' := Units.ext (shortRootMatrix_zero s h)
  map_mul' a b := Units.ext (shortRootMatrix_add s hh a.toAdd b.toAdd)

/-- The matrix of `shortRootHom` at `a` is the short root matrix `x_i(a)`. -/
@[simp]
theorem coe_shortRootHom (a : Multiplicative A) :
    (shortRootHom s hh a : Matrix (Fin l) (Fin l) A) = shortRootMatrix s h a.toAdd :=
  (rfl)

/-- The short root subgroup lands in the points of `SO_l^J`. -/
theorem shortRootHom_mem_pointsSubgroup (a : Multiplicative A) :
    shortRootHom s hh a ∈ pointsSubgroup l A :=
  (mem_pointsSubgroup_iff _).mpr
    ⟨det_shortRootMatrix s h _, shortRootMatrix_mul_formMatrix_mul_transpose s hh _⟩

/-- **The short root subgroup on points**, `a ↦ x_i(a)`, as a homomorphism into the points of
`SO_l^J`. -/
def shortRootPoints : Multiplicative A →* pointsSubgroup l A :=
  (shortRootHom s hh).codRestrict _ (shortRootHom_mem_pointsSubgroup s hh)

/-- The underlying invertible matrix of `shortRootPoints` at `a` is `shortRootHom` at `a`. -/
@[simp]
theorem coe_shortRootPoints (a : Multiplicative A) :
    ((shortRootPoints s hh a : pointsSubgroup l A) : GL (Fin l) A) = shortRootHom s hh a :=
  (rfl)

/-- The short root subgroup on points is natural in the value ring. -/
theorem pointsSubgroupMap_shortRootPoints {B : Type v} [CommRing B] (f : A →+* B)
    (a : Multiplicative A) :
    pointsSubgroupMap f (shortRootPoints s hh a) =
      shortRootPoints s (h := f h) (by rw [← map_ofNat f 2, ← map_mul, hh, map_one])
        (Multiplicative.ofAdd (f a.toAdd)) := by
  apply Subtype.ext
  apply Units.ext
  rw [coe_pointsSubgroupMap, coe_shortRootPoints, coe_shortRootPoints]
  ext p q
  rw [Matrix.GeneralLinearGroup.map_apply, coe_shortRootHom, coe_shortRootHom, toAdd_ofAdd,
    ← map_shortRootMatrix, Matrix.map_apply]

end Points

/-! ### Hopf points and the group-scheme morphism -/

section HopfPoints

variable {R : Type u} [CommRing R] [Invertible (2 : R)] {l : ℕ} (s : ShortRootIndex l)
variable {A : Type w} [CommRing A] [Algebra R A]
variable {B : Type v} [CommRing B] [Algebra R B]

/-- The short root subgroup on Hopf points: an `A`-point of `𝔾ₐ` goes to the `A`-point of
`SO_l^J` given by its short root matrix, with `h = ½`. -/
noncomputable def shortRootSubgroupPoints :
    WithConv (AdditiveGroup.coordinateHopfAlgebra R →ₐ[R] A) →*
      WithConv (coordinateHopfAlgebra R l →ₐ[R] A) :=
  (pointsMulEquiv R l (A := A)).symm.toMonoidHom.comp
    ((shortRootPoints s (two_mul_map_invOf_two (algebraMap R A))).comp
      (AdditiveGroup.gaPointsMulEquiv (R := R) (A := A)).toMonoidHom)

/-- Under the point equivalence of `SO_l^J`, a short root point is the short root matrix of its
additive parameter. -/
@[simp↓]
theorem pointsMulEquiv_shortRootSubgroupPoints
    (q : WithConv (AdditiveGroup.coordinateHopfAlgebra R →ₐ[R] A)) :
    pointsMulEquiv R l (A := A) (shortRootSubgroupPoints s q) =
      shortRootPoints s (two_mul_map_invOf_two (algebraMap R A))
        (AdditiveGroup.gaPointsMulEquiv (R := R) (A := A) q) := by
  rw [shortRootSubgroupPoints, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.apply_symm_apply, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]

/-- The short root subgroup on Hopf points is natural in the value algebra. -/
theorem mapValue_shortRootSubgroupPoints (φ : A →ₐ[R] B)
    (q : WithConv (AdditiveGroup.coordinateHopfAlgebra R →ₐ[R] A)) :
    AlgHom.mapValue (H := coordinateHopfAlgebra R l) φ (shortRootSubgroupPoints s q) =
      shortRootSubgroupPoints s
        (AlgHom.mapValue (H := AdditiveGroup.coordinateHopfAlgebra R) φ q) := by
  apply (pointsMulEquiv R l (A := B)).injective
  rw [pointsMulEquiv_mapValue, pointsMulEquiv_shortRootSubgroupPoints,
    pointsMulEquiv_shortRootSubgroupPoints, pointsSubgroupMap_shortRootPoints]
  apply Subtype.ext
  apply Units.ext
  rw [coe_shortRootPoints, coe_shortRootPoints, coe_shortRootHom, coe_shortRootHom, toAdd_ofAdd,
    AdditiveGroup.toAdd_gaPointsMulEquiv_mapValue, AlgHom.coe_toRingHom, AlgHom.commutes]

/-- The natural transformation of group-valued points given by the short root subgroup. -/
noncomputable def shortRootSubgroupPointsMap :
    HopfAlgebra.pointsFunctor (R := R) (H := AdditiveGroup.coordinateHopfAlgebra R) ⟶
      HopfAlgebra.pointsFunctor (R := R) (H := coordinateHopfAlgebra R l) where
  app A := GrpCat.ofHom (shortRootSubgroupPoints (A := A) s)
  naturality _ _ φ := by
    ext q
    exact (mapValue_shortRootSubgroupPoints s φ.hom q).symm

/-- A component of the natural short root points map is the short root point homomorphism. -/
@[simp]
theorem shortRootSubgroupPointsMap_app (A : CommAlgCat.{w} R) :
    (shortRootSubgroupPointsMap (R := R) s).app A = GrpCat.ofHom (shortRootSubgroupPoints s) :=
  (rfl)

end HopfPoints

section Scheme

variable {R : Type u} [CommRing R] [Invertible (2 : R)] {l : ℕ} (s : ShortRootIndex l)

/-- **The coordinate morphism `O(SO_l^J) → O(𝔾ₐ)` of the short root subgroup**, recovered from
its natural action on points. -/
noncomputable def shortRootSubgroupCoordinateMap :
    coordinateHopfAlgebra R l ⟶ AdditiveGroup.coordinateHopfAlgebra R :=
  CommHopfAlgCat.homOfPointsMap (shortRootSubgroupPointsMap.{u, u} (R := R) s)

/-- Over any value-algebra universe, the short root coordinate morphism induces the short root
point homomorphism. -/
@[simp↓]
theorem mapPointsFunctor_shortRootSubgroupCoordinateMap_app (A : CommAlgCat.{w} R)
    (q : HopfAlgebra.points (R := R) (H := AdditiveGroup.coordinateHopfAlgebra R) A) :
    (CommHopfAlgCat.Hom.mapPointsFunctor (shortRootSubgroupCoordinateMap (R := R) s)).app A q =
      shortRootSubgroupPoints s q := by
  rw [shortRootSubgroupCoordinateMap, CommHopfAlgCat.mapPointsFunctor_homOfPointsMap_app,
    shortRootSubgroupPointsMap_app]
  refine (mapValue_shortRootSubgroupPoints s q.ofConv _).trans ?_
  rw [AlgHom.mapValue_apply, ofConv_toConv, AlgHom.comp_id, toConv_ofConv]

/-- **The short root subgroup `x_i : 𝔾ₐ → SO_l^J`**, as a morphism of affine group schemes over
a base ring containing `½`. -/
noncomputable def shortRootSubgroup : AdditiveGroup.groupScheme R ⟶ groupScheme R l :=
  eqToHom (AdditiveGroup.groupScheme_def R) ≫
    (hopfSpec (CommRingCat.of R)).map (shortRootSubgroupCoordinateMap s).op ≫
    eqToHom (groupScheme_def R l).symm

/-- The short root subgroup is relative spectrum applied contravariantly to its coordinate
morphism. -/
theorem shortRootSubgroup_def :
    shortRootSubgroup (R := R) s =
      eqToHom (AdditiveGroup.groupScheme_def R) ≫
        (hopfSpec (CommRingCat.of R)).map (shortRootSubgroupCoordinateMap s).op ≫
        eqToHom (groupScheme_def R l).symm :=
  (rfl)

/-- **The generic point of the short root subgroup**: restricting functions from `GL_l` to
`SO_l^J` and then to the short root subgroup sends the generic matrix to the short root matrix of
the coordinate of `𝔾ₐ`. -/
theorem pointToGeneralLinear_coordinateMap_comp_shortRootSubgroupCoordinateMap :
    ((GeneralLinear.pointToGeneralLinear l
        (toConv (coordinateMap R l ≫ shortRootSubgroupCoordinateMap s).hom.toAlgHom) :
        GL (Fin l) (AdditiveGroup.coordinateHopfAlgebra R)) :
      Matrix (Fin l) (Fin l) (AdditiveGroup.coordinateHopfAlgebra R)) =
      shortRootMatrix s (algebraMap R _ ⅟2) (SymmetricAlgebra.ι R R 1) := by
  let q₀ : WithConv (AdditiveGroup.coordinateHopfAlgebra R →ₐ[R]
      AdditiveGroup.coordinateHopfAlgebra R) := toConv (AlgHom.id R _)
  have happ := mapPointsFunctor_shortRootSubgroupCoordinateMap_app s
    (CommAlgCat.of R (AdditiveGroup.coordinateHopfAlgebra R)) q₀
  rw [CommHopfAlgCat.Hom.mapPointsFunctor_app_apply, AlgHom.id_comp] at happ
  have hpt : GeneralLinear.pointToGeneralLinear l
      (toConv (coordinateMap R l ≫ shortRootSubgroupCoordinateMap s).hom.toAlgHom) =
      (pointsMulEquiv R l (A := AdditiveGroup.coordinateHopfAlgebra R)
        (shortRootSubgroupPoints s q₀) : GL (Fin l) _) := by
    rw [← pointsMulEquiv_coe, ← happ, CommHopfAlgCat.quotientPointsHom_apply,
      ← GeneralLinear.pointsMulEquiv_apply, coordinateMap_def, CommHopfAlgCat.hom_comp,
      BialgHom.comp_toAlgHom, WithConv.ofConv_toConv]
  rw [hpt, pointsMulEquiv_shortRootSubgroupPoints, coe_shortRootPoints, coe_shortRootHom]
  simp [q₀]

/-- The short root coordinate morphism sends the coordinate at `(a, b)` to the `(a, b)` entry of
the short root matrix of the coordinate of `𝔾ₐ`. -/
@[simp↓]
theorem shortRootSubgroupCoordinateMap_coordinateMap_genericMatrix (a b : Fin l) :
    (shortRootSubgroupCoordinateMap s).hom
        ((coordinateMap R l).hom (GeneralLinear.genericMatrix R l a b)) =
      shortRootMatrix s (algebraMap R _ ⅟2) (SymmetricAlgebra.ι R R 1) a b := by
  rw [← pointToGeneralLinear_coordinateMap_comp_shortRootSubgroupCoordinateMap,
    GeneralLinear.pointToGeneralLinear_apply, GeneralLinear.genericMatrix_apply,
    WithConv.ofConv_toConv, CommHopfAlgCat.hom_comp, BialgHom.comp_toAlgHom, AlgHom.comp_apply,
    BialgHom.coe_toAlgHom, BialgHom.coe_toAlgHom]

/-- The short root coordinate morphism is surjective: the entry at `(i, m)` restricts to the
coordinate of `𝔾ₐ`. -/
theorem shortRootSubgroupCoordinateMap_surjective :
    Function.Surjective (shortRootSubgroupCoordinateMap (R := R) s).hom := by
  apply (shortRootSubgroupCoordinateMap (R := R) s).hom.toAlgHom.surjective_of_ι_one_mem_range
  exact ⟨_, (shortRootSubgroupCoordinateMap_coordinateMap_genericMatrix s s.i s.m).trans
    (shortRootMatrix_apply_i_m s _ _)⟩

/-- **The short root subgroup is a closed subgroup scheme of `SO_l^J`.** -/
instance isClosedImmersion_shortRootSubgroup :
    IsClosedImmersion (shortRootSubgroup (R := R) s).hom.hom.left := by
  rw [shortRootSubgroup_def]
  exact (CommHopfAlgCat.isClosedImmersion_eqToHom_comp_hopfSpec_map_comp_eqToHom_iff
    (AdditiveGroup.groupScheme_def R) (groupScheme_def R l) _).mpr
    (shortRootSubgroupCoordinateMap_surjective s)

end Scheme

/-! ### The action of the diagonal torus -/

section Torus

variable {R : Type u} [CommRing R] [Invertible (2 : R)] {l : ℕ} (s : ShortRootIndex l)
variable {A : Type v} [CommRing A] [Algebra R A]

/-- The middle diagonal entry of the diagonal torus has weight `0`. -/
theorem diagonalTorusWeight_m : diagonalTorusWeight.{u} l s.m = 0 := by
  have h := congrArg Fin.val s.rev_m
  rw [Fin.val_rev] at h
  apply diagonalTorusWeight_eq_zero
  · omega
  · rw [s.rev_m]
    omega

/-- **The diagonal torus of `SO_l^J` acts on the short root subgroup `x_i` through the weight
`w_i`** of the `i`-th diagonal entry: conjugation by a point `t` of the diagonal torus scales the
parameter by the value at `t` of `w_i`, which is `ε_i` for `i < l / 2`. -/
theorem diagonalTorusPoints_mul_shortRootSubgroupPoints_mul_inv
    (t : WithConv (MonoidAlgebra R (Multiplicative (ULift.{u} (Fin (l / 2)) →₀ ℤ)) →ₐ[R] A))
    (c : WithConv (AdditiveGroup.coordinateHopfAlgebra R →ₐ[R] A)) :
    diagonalTorusPoints R l A t * shortRootSubgroupPoints s c *
        (diagonalTorusPoints R l A t)⁻¹ =
      shortRootSubgroupPoints s
        ((AdditiveGroup.gaPointsMulEquiv (R := R) (A := A)).symm <|
          Multiplicative.ofAdd
            (((DiagonalizableGroup.charOfPoint t.ofConv
                (SplitTorus.weightCharacter (diagonalTorusWeight.{u} l s.i)) : Aˣ) : A) *
              Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv c))) := by
  apply (pointsMulEquiv R l (A := A)).injective
  rw [map_mul, map_mul, map_inv, pointsMulEquiv_shortRootSubgroupPoints,
    pointsMulEquiv_shortRootSubgroupPoints, MulEquiv.apply_symm_apply,
    SplitTorus.charOfPoint_weightCharacter]
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, pointsMulEquiv_diagonalTorusPoints,
    coe_shortRootPoints, coe_shortRootPoints]
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, ← map_inv, diagGL_coe, diagGL_coe, coe_shortRootHom,
    coe_shortRootHom, toAdd_ofAdd]
  exact diagonal_mul_shortRootMatrix_mul_diagonal_inv s _
    (fun k => by rw [diagonalTorusWeight_rev, torusCharacter_neg])
    (by rw [diagonalTorusWeight_m, torusCharacter_zero]) _ _

end Torus

end TauCeti.AntidiagonalSpecialOrthogonal
