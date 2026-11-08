/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Matrix.Composition
public import Mathlib.RingTheory.Norm.Defs
public import TauCeti.Algebra.Homology.ReidemeisterTorsion.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import TauCeti.Algebra.Homology.ModuleCat.Finrank
import TauCeti.LinearAlgebra.Basis.Semilinear
import TauCeti.LinearAlgebra.Basis.SmulTower

/-!
# The torsion of the restriction of scalars of a based complex

Let `L` be a finite extension of a field `F`, with an ordered `F`-basis `β a`, `a : Fin m`, and let
`C` be a `ℤ`-graded chain complex of `L`-vector spaces with an ordered basis `c i` of each
`C.X i`. Viewed as `F`-vector spaces, the terms of `C` have the bases `β a • c i k`
(`Module.Basis.smulTower'`), ordered first by `k` and then by `a` (`finProdFinEquiv`). In these
bases the matrix of a differential is the block matrix obtained from its matrix over `L` by
replacing each entry `x` by the matrix `Algebra.leftMulMatrix β x` of multiplication by `x`
(`LinearMap.toMatrix_restrictScalars`).

This file proves that the torsion of the resulting based complex over `F` is the norm of the
torsion of `C` (`HomologicalComplex.norm_reidemeisterTorsion`): if `D` is a complex of
`F`-vector spaces with bases `e i` in which the matrices of the differentials are these block
matrices, then

`τ(D, e) = N_{L/F} (τ(C, c))`,

with no sign. This holds for every complex: `D` is acyclic exactly when `C` is
(`HomologicalComplex.acyclic_iff_of_toMatrix_eq_leftMulMatrix`), and both sides vanish otherwise.
To compare the brackets, the boundaries of `D` are given the bases
`β a • bⱼ k` built from bases `bⱼ` of the boundaries of `C`, and the lifts `β a • sⱼ k` built
from lifts `sⱼ`; the bracket of `D` in each degree is then the determinant of a family of the
form `β a • v k` in the basis `β a • c i k`, which is the norm of the determinant of `v` in the
basis `c i` (`Module.Basis.det_smulTower'`). Listing the vectors `β a • v k` with `k` as the
outer index keeps the boundary vectors before the lifts, so no reordering sign appears.

Torsions of finite covers are compared with norms of torsions in this way: over the Novikov
series on `H`, restricting scalars to a finite-index subgroup `K` in the basis of coset monomials
produces differentials of the same block form, and the theorem here is the corresponding statement
over fields.

## Main results

* `HomologicalComplex.norm_reidemeisterTorsion`: the torsion of the restriction of scalars of a
  based complex along a finite field extension is the norm of its torsion.

## References

* M. Hutchings, *Reidemeister torsion in generalized Morse theory*, Forum Math. 14 (2002),
  Section 3 (norms of torsion under finite cyclic covers, Proposition 3.6).
* V. Turaev, *Introduction to combinatorial torsions*, Birkhäuser 2001, Chapter I.
-/

public section

noncomputable section

open CategoryTheory Module
open scoped ModuleCat.Algebra

namespace HomologicalComplex

variable {F L : Type*} [Field F] [Field L] [Algebra F L] {m : ℕ} (β : Basis (Fin m) F L)
  {C : ChainComplex (ModuleCat L) ℤ} {n : ℤ → ℕ} (c : ∀ i, Basis (Fin (n i)) L (C.X i))

/-- The `F`-basis `β a • c i k` of `C.X i`, indexed by `Fin (n i * m)`. -/
private def towerBasis (i : ℤ) : Basis (Fin (n i * m)) F (C.X i) :=
  (β.smulTower' (c i)).reindex finProdFinEquiv

/-- The matrix of a differential of `C`, viewed over `F`, in the tower bases. -/
private theorem toMatrix_towerBasis (i j : ℤ) :
    LinearMap.toMatrix (towerBasis β c i) (towerBasis β c j)
        ((C.d i j).hom.restrictScalars F) =
      Matrix.reindex finProdFinEquiv finProdFinEquiv (Matrix.comp _ _ _ _ F
        ((LinearMap.toMatrix (c i) (c j) (C.d i j).hom).map (Algebra.leftMulMatrix β))) := by
  rw [← LinearMap.toMatrix_restrictScalars]
  ext k l
  simp [LinearMap.toMatrix_apply, towerBasis]

variable {β c} {D : ChainComplex (ModuleCat F) ℤ} {e : ∀ i, Basis (Fin (n i * m)) F (D.X i)}
  (hd : ∀ i, LinearMap.toMatrix (e (i + 1)) (e i) (D.d (i + 1) i).hom =
    Matrix.reindex finProdFinEquiv finProdFinEquiv (Matrix.comp _ _ _ _ F
      ((LinearMap.toMatrix (c (i + 1)) (c i) (C.d (i + 1) i).hom).map (Algebra.leftMulMatrix β))))

variable (β c e) in
/-- The `F`-linear isomorphism `C.X i → D.X i` sending the tower basis to the basis `e i`. -/
private def towerEquiv (i : ℤ) : C.X i ≃ₗ[F] D.X i :=
  (towerBasis β c i).equiv (e i) (Equiv.refl _)

private theorem semilinearMap_towerBasis (i : ℤ) :
    ((towerBasis β c i).semilinearMap (RingHom.id F) (e i) : C.X i →ₗ[F] D.X i) =
      (towerEquiv β c e i).toLinearMap :=
  (towerBasis β c i).ext fun k ↦ by simp [towerEquiv]

include hd in
/-- The isomorphisms `towerEquiv` commute with the differentials. -/
private theorem d_towerEquiv (j : ℤ) (x : C.X (j + 1)) :
    (D.d (j + 1) j).hom (towerEquiv β c e (j + 1) x) =
      towerEquiv β c e j ((C.d (j + 1) j).hom x) := by
  have h := Basis.semilinearMap_comp_apply_of_toMatrix_eq (σ := RingHom.id F)
    (f := (C.d (j + 1) j).hom.restrictScalars F) (g := (D.d (j + 1) j).hom)
    (b := towerBasis β c (j + 1)) (b' := e (j + 1)) (c := towerBasis β c j) (c' := e j)
    (by rw [hd, toMatrix_towerBasis, RingHom.coe_id, Matrix.map_id]) x
  simpa [semilinearMap_towerBasis] using h

variable (β c e) in
/-- The vectors `β a • u k` of `C.X i`, transported to `D.X i` and indexed by `Fin (p * m)`. -/
private def towerVec (i : ℤ) {p : ℕ} (u : Fin p → C.X i) (x : Fin (p * m)) : D.X i :=
  towerEquiv β c e i (β (finProdFinEquiv.symm x).2 • u (finProdFinEquiv.symm x).1)

include hd in
private theorem d_towerVec (j : ℤ) {p : ℕ} (u : Fin p → C.X (j + 1)) (x : Fin (p * m)) :
    (D.d (j + 1) j).hom (towerVec β c e (j + 1) u x) =
      towerVec β c e j (fun k ↦ (C.d (j + 1) j).hom (u k)) x := by
  rw [towerVec, d_towerEquiv hd, towerVec, map_smul]

include hd in
/-- The transported lifts are lifts of the transported boundary vectors. -/
private theorem d_towerVec_chosenBoundaryLift (j : ℤ) (x) :
    (D.d (j + 1) j).hom (towerVec β c e (j + 1) (chosenBoundaryLift C c j) x) =
      towerVec β c e j (fun k ↦ (chosenBoundaryBasis C c j k : C.X j)) x := by
  rw [d_towerVec hd]
  simp_rw [chosenBoundaryLift_spec]

include hd in
private theorem towerVec_mem_range (j : ℤ) (x) :
    towerVec β c e j (fun k ↦ (chosenBoundaryBasis C c j k : C.X j)) x ∈
      LinearMap.range (D.d (j + 1) j).hom :=
  ⟨_, d_towerVec_chosenBoundaryLift hd j x⟩

private theorem linearIndependent_towerVec (j : ℤ) :
    LinearIndependent F (towerVec β c e j fun k ↦ (chosenBoundaryBasis C c j k : C.X j)) := by
  have hb := (β.smulTower' (chosenBoundaryBasis C c j)).linearIndependent.map'
    ((LinearMap.range (C.d (j + 1) j).hom).subtype.restrictScalars F)
    (LinearMap.ker_eq_bot.2 Subtype.val_injective)
  have := (hb.comp _ finProdFinEquiv.symm.injective).map' (towerEquiv β c e j).toLinearMap
    (LinearEquiv.ker _)
  convert this using 1
  ext x
  simp [towerVec, Basis.smulTower'_apply]

include hd in
/-- The basis of the boundaries of `D` in degree `j` made of the transported vectors
`β a • b k`, for the chosen basis `b` of the boundaries of `C`. -/
private def towerBoundaryBasis (j : ℤ) :
    Basis (Fin (finrank L (LinearMap.range (C.d (j + 1) j).hom) * m)) F
      (LinearMap.range (D.d (j + 1) j).hom) :=
  have : Module.Finite F (D.X j) := .of_basis (e j)
  basisOfLinearIndependentOfCardEqFinrank' (fun x ↦ ⟨_, towerVec_mem_range hd j x⟩)
    (LinearIndependent.of_comp (LinearMap.range (D.d (j + 1) j).hom).subtype
      (linearIndependent_towerVec j))
    (by rw [Fintype.card_fin, finrank_range_d_eq_mul_of_toMatrix_eq_leftMulMatrix β (hd j)])

private theorem coe_towerBoundaryBasis (j : ℤ) (x) :
    (towerBoundaryBasis hd j x : D.X j) =
      towerVec β c e j (fun k ↦ (chosenBoundaryBasis C c j k : C.X j)) x := by
  simp [towerBoundaryBasis]

/-- Appending two families of transported vectors, in the order of `finProdFinEquiv`. -/
private theorem append_towerVec (j : ℤ) {p q N : ℕ} (hN : N = p + q) (hNm : N * m = p * m + q * m)
    (u : Fin p → C.X j) (w : Fin q → C.X j) (k : Fin N) (a : Fin m) :
    Fin.append (towerVec β c e j u) (towerVec β c e j w)
        (Fin.cast hNm (finProdFinEquiv (k, a))) =
      towerEquiv β c e j (β a • Fin.append u w (Fin.cast hN k)) := by
  subst hN
  induction k using Fin.addCases with
  | left k =>
    have : Fin.cast hNm (finProdFinEquiv (Fin.castAdd q k, a)) =
        Fin.castAdd (q * m) (finProdFinEquiv (k, a)) := Fin.ext (by simp)
    simp [this, towerVec]
  | right k =>
    have : Fin.cast hNm (finProdFinEquiv (Fin.natAdd p k, a)) =
        Fin.natAdd (p * m) (finProdFinEquiv (k, a)) := Fin.ext (by simp; ring)
    simp [this, towerVec]

include hd in
/-- The bracket of `D` for the transported boundary bases and lifts is the norm of the bracket of
`C` for the chosen boundary bases and lifts. -/
private theorem torsionBracket_towerBoundaryBasis {j : ℤ} (h : C.ExactAt (j + 1))
    (hD : D.ExactAt (j + 1)) :
    torsionBracket e hD (towerBoundaryBasis hd (j + 1)) (towerBoundaryBasis hd j)
        (towerVec β c e (j + 1) (chosenBoundaryLift C c j))
        (fun x ↦ by rw [d_towerVec_chosenBoundaryLift hd, coe_towerBoundaryBasis]) =
      Algebra.norm F (torsionBracket c h (chosenBoundaryBasis C c (j + 1))
        (chosenBoundaryBasis C c j) (chosenBoundaryLift C c j)
        (chosenBoundaryLift_spec C c j)) := by
  have hn := eq_add_of_exactAt c h (chosenBoundaryBasis C c (j + 1)) (chosenBoundaryBasis C c j)
  have hnm : n (j + 1) * m = finrank L (LinearMap.range (C.d (j + 1 + 1) (j + 1)).hom) * m +
      finrank L (LinearMap.range (C.d (j + 1) j).hom) * m := by rw [hn, add_mul]
  set V := Fin.append (fun k ↦ (chosenBoundaryBasis C c (j + 1) k : C.X (j + 1)))
    (chosenBoundaryLift C c j) ∘ Fin.cast hn
  have hfam : Fin.append (fun x ↦ (towerBoundaryBasis hd (j + 1) x : D.X (j + 1)))
      (towerVec β c e (j + 1) (chosenBoundaryLift C c j)) ∘ Fin.cast hnm =
      (towerBasis β c (j + 1)).semilinearMap (RingHom.id F) (e (j + 1)) ∘
        fun x ↦ β (finProdFinEquiv.symm x).2 • V (finProdFinEquiv.symm x).1 := by
    funext x
    obtain ⟨⟨k, a⟩, rfl⟩ := finProdFinEquiv.surjective x
    have hb : (fun x ↦ (towerBoundaryBasis hd (j + 1) x : D.X (j + 1))) =
        towerVec β c e (j + 1) fun k ↦ (chosenBoundaryBasis C c (j + 1) k : C.X (j + 1)) :=
      funext (coe_towerBoundaryBasis hd (j + 1))
    simp only [Function.comp_apply, hb, append_towerVec (j + 1) hn hnm,
      semilinearMap_towerBasis, LinearEquiv.coe_coe, Equiv.symm_apply_apply, V]
  rw [torsionBracket_eq_det_append e _ _ _ _ _ hnm, torsionBracket_eq_det_append c _ _ _ _ _ hn,
    hfam, Basis.det_comp_semilinearMap, RingHom.id_apply, towerBasis, Basis.det_reindex,
    ← Basis.det_smulTower' β]
  congr 1
  funext x
  simp only [Function.comp_apply, Equiv.symm_apply_apply, V]

include hd in
/-- **Restriction of scalars of the torsion.** Let `L` be a field extension of `F` with an ordered
basis `β a`, `a : Fin m`, and let `D` be a complex of vector spaces over `F` with bases `e i` in
which the matrix of each differential is obtained from the matrix of the corresponding differential
of `C` in the bases `c i` by replacing each entry `x` with the matrix of multiplication by `x` in
the basis `β`, the indices `(k, a)` being ordered by `finProdFinEquiv`; that is, `(D, e)` is the
restriction of scalars of `(C, c)` to `F`, based by the vectors `β a • c i k`. Then the torsion of
`D` is the norm of the torsion of `C`. This holds for every complex: `D` is acyclic exactly when
`C` is, and both torsions are `0` otherwise. -/
theorem norm_reidemeisterTorsion :
    Algebra.norm F (C.reidemeisterTorsion c) = D.reidemeisterTorsion e := by
  symm
  have : Module.Finite F L := .of_basis β
  have hm : m ≠ 0 := (Fin.pos_iff_nonempty.2 β.index_nonempty).ne'
  have hnD : {i | n i * m ≠ 0} = {i | n i ≠ 0} := by
    ext i
    simp [hm]
  by_cases hn : {i | n i ≠ 0}.Finite
  swap
  · rw [reidemeisterTorsion_of_not_finite _ _ hn,
      reidemeisterTorsion_of_not_finite _ _ (hnD ▸ hn), Algebra.norm_zero]
  have hDC : D.Acyclic ↔ C.Acyclic := acyclic_iff_of_toMatrix_eq_leftMulMatrix β fun i j hij ↦ by
    obtain rfl : j + 1 = i := hij
    exact hd j
  by_cases h : C.Acyclic
  swap
  · rw [reidemeisterTorsion_of_not_acyclic C c h,
      reidemeisterTorsion_of_not_acyclic D e (mt hDC.1 h), Algebra.norm_zero]
  have hD := hDC.2 h
  -- The norm as a homomorphism of monoids with zero, to commute with integer powers.
  let N : L →*₀ F := { Algebra.norm F with map_zero' := Algebra.norm_zero }
  rw [reidemeisterTorsion_eq_finprod hn h (chosenBoundaryBasis C c) (chosenBoundaryLift C c)
      (chosenBoundaryLift_spec C c),
    reidemeisterTorsion_eq_finprod (hnD ▸ hn) hD (towerBoundaryBasis hd)
      (fun j ↦ towerVec β c e (j + 1) (chosenBoundaryLift C c j))
      (fun j x ↦ by rw [d_towerVec_chosenBoundaryLift hd, coe_towerBoundaryBasis])]
  refine Eq.trans (finprod_congr fun j ↦ ?_) (MonoidHom.map_finprod (N : L →* F)
    (hasFiniteMulSupport_torsionBracket hn h _ _ (chosenBoundaryLift_spec C c))).symm
  rw [torsionBracket_towerBoundaryBasis hd (h (j + 1)) (hD (j + 1))]
  exact (map_zpow₀ N _ _).symm

end HomologicalComplex
