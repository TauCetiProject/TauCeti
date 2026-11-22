/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.Norm.Defs
public import Mathlib.RingTheory.Trace.Defs
public import TauCeti.NumberTheory.Padics.Coleman.Basic
public import TauCeti.RingTheory.Norm.Units

import Mathlib.RingTheory.Norm.Basic
import Mathlib.RingTheory.NormTrace
import Mathlib.RingTheory.Trace.Basic
import TauCeti.RingTheory.AdicCompletion.Principal
import TauCeti.RingTheory.Polynomial.Resultant.AdjoinRoot

/-!
# Coleman's norm and trace operators on power series

For a prime `p` and `(p)`-adically complete commutative ring `O`, Frobenius substitution
`Φ = TauCeti.Coleman.frobeniusHom p O` equips `O⟦X⟧` with the `@[instance_reducible]`
`O⟦X⟧`-algebra `TauCeti.Coleman.scalarAlgebra p O` (avoiding a clash with `Algebra.id O⟦X⟧`). By
`Coleman.Basic`, `O⟦X⟧` is free of rank `p` (for `[Nontrivial O]`) with basis `{(1 + X) ^ i}`
(`TauCeti.Coleman.basis p O`) and isomorphic to `AdjoinRoot (X ^ p - C (1 + X))` via
`TauCeti.Coleman.adjoinRootEquiv p O`. Mathlib's `Algebra.norm` and `Algebra.trace` yield
Coleman's norm `N` and trace `τ`, with matrix, first-order, Kummer, and functoriality formulas.

## Main definitions and results

* `TauCeti.Coleman.scalarAlgebra`, `TauCeti.Coleman.basis`, `TauCeti.Coleman.adjoinRootEquiv`,
  `TauCeti.Coleman.module_free_scalarAlgebra`, `TauCeti.Coleman.module_finite_scalarAlgebra`,
  `TauCeti.Coleman.finrank_scalarAlgebra`: Frobenius algebra, rank-`p` basis, and `AdjoinRoot`.
* `TauCeti.Coleman.norm`, `TauCeti.Coleman.normUnits`, `TauCeti.Coleman.trace`,
  `TauCeti.Coleman.leftMulMatrix`: Coleman's norm, unit norm, trace, and multiplication matrix.
* `TauCeti.Coleman.norm_eq_det_leftMulMatrix`, `TauCeti.Coleman.trace_eq_trace_leftMulMatrix`,
  `TauCeti.Coleman.trace_eq_p_mul_coord_zero`, `TauCeti.Coleman.norm_one_add_frobeniusHom_mul`,
  `TauCeti.Coleman.norm_frobeniusHom_sub_one_add_X`, `TauCeti.Coleman.norm_one_add_X`,
  `TauCeti.Coleman.norm_X`, `TauCeti.Coleman.map_norm`, `TauCeti.Coleman.map_trace`: matrix,
  trace, first-order, Kummer, and functoriality formulas.

## References

* R. F. Coleman, *Division Values in Local Fields*, Invent. Math. 53 (1979), §§II, IV (Thm. 4,
  Lemma 6, Thm. 11).
* J. Coates and R. Sujatha, *Cyclotomic Fields and Zeta Values*, Springer (2006), §2.2
  (Prop. 2.2.3).
* R. Sharifi, *Iwasawa Theory*, §5.4 (Prop. 5.4.3, Def. 5.4.4, Lemma 5.4.14).
* J. Rodrigues Jacinto and C. Williams, *An introduction to p-adic L-functions* (2025), Ch. 10.
* C. Birkbeck et al., `CBirkbeck/padic-L-functions` (`Coleman/NormOperator.lean`, commit
  `45307015169791f1316f23a459c8e92ed5961c54`), whose Frobenius scalar-algebra and
  multiplication-matrix determinant route is generalized here to arbitrary `(p)`-adically complete
  rings `O`.
-/

public noncomputable section

open PowerSeries

namespace TauCeti.Coleman

section Definitions

variable (p : ℕ) (O : Type*) [CommRing O]

/-- The `O⟦X⟧`-algebra structure on `O⟦X⟧` via `Φ : f ↦ f((1 + X) ^ p - 1)`. Marked
`@[instance_reducible]` rather than `instance` to avoid clashing with `Algebra.id O⟦X⟧`. -/
@[instance_reducible]
def scalarAlgebra : Algebra O⟦X⟧ O⟦X⟧ := (frobeniusHom p O).toRingHom.toAlgebra

/-- `scalarAlgebra p O` is the algebra structure induced by `(frobeniusHom p O).toRingHom`. -/
theorem scalarAlgebra_eq : scalarAlgebra p O = (frobeniusHom p O).toRingHom.toAlgebra := (rfl)

/-- The structure map of `scalarAlgebra p O` is `(frobeniusHom p O).toRingHom`. -/
theorem scalarAlgebra_algebraMap :
    @algebraMap O⟦X⟧ O⟦X⟧ _ _ (scalarAlgebra p O) = (frobeniusHom p O).toRingHom := (rfl)

/-- Pointwise, the structure map of `scalarAlgebra p O` is `frobeniusHom p O`. -/
@[simp]
theorem scalarAlgebra_algebraMap_apply {p : ℕ} {O : Type*} [CommRing O] (c : O⟦X⟧) :
    @algebraMap O⟦X⟧ O⟦X⟧ _ _ (scalarAlgebra p O) c = frobeniusHom p O c := (rfl)

/-- Scalar multiplication under `scalarAlgebra p O` is multiplication by `frobeniusHom p O c`. -/
@[simp]
theorem scalarAlgebra_smul_def {p : ℕ} {O : Type*} [CommRing O] (c f : O⟦X⟧) :
    @HSMul.hSMul O⟦X⟧ O⟦X⟧ O⟦X⟧ (@instHSMul _ _ (scalarAlgebra p O).toSMul) c f =
      frobeniusHom p O c * f := (rfl)

/-- Internal type synonym for `O⟦X⟧` with `scalarAlgebra p O`, avoiding module diamonds. -/
private def OverFrobenius (_p : ℕ) (O : Type*) := O⟦X⟧

private instance : CommRing (OverFrobenius p O) := inferInstanceAs (CommRing O⟦X⟧)

private def overFrobeniusRingEquiv : OverFrobenius p O ≃+* O⟦X⟧ := RingEquiv.refl _

private instance : Algebra O⟦X⟧ (OverFrobenius p O) :=
  ((overFrobeniusRingEquiv p O).symm.toRingHom.comp (frobeniusHom p O).toRingHom).toAlgebra

private theorem overFrobeniusRingEquiv_algebraMap (c : O⟦X⟧) :
    overFrobeniusRingEquiv p O (algebraMap O⟦X⟧ (OverFrobenius p O) c) = frobeniusHom p O c := rfl

private theorem overFrobeniusRingEquiv_smul (c : O⟦X⟧) (x : OverFrobenius p O) :
    overFrobeniusRingEquiv p O (c • x) = frobeniusHom p O c * overFrobeniusRingEquiv p O x := rfl

private theorem overFrobenius_smul_eq (a f : O⟦X⟧) :
    (overFrobeniusRingEquiv p O).symm (frobeniusHom p O a * f) =
      a • (overFrobeniusRingEquiv p O).symm f := rfl

private theorem overFrobenius_algebraMap_eq (a : O⟦X⟧) :
    (overFrobeniusRingEquiv p O).symm (frobeniusHom p O a) =
      algebraMap O⟦X⟧ (OverFrobenius p O) a := rfl

end Definitions

section InternalBasis

variable {p : ℕ} [Fact p.Prime] {O : Type*} [CommRing O] [IsAdicComplete (Ideal.span {(p : O)}) O]

private def overFrobeniusBasis (p : ℕ) [Fact p.Prime] (O : Type*) [CommRing O]
    [IsAdicComplete (Ideal.span {(p : O)}) O] : Module.Basis (Fin p) O⟦X⟧ (OverFrobenius p O) :=
  Module.Basis.ofEquivFun
    { toFun x := coordEquiv p O (overFrobeniusRingEquiv p O x)
      invFun a := (overFrobeniusRingEquiv p O).symm ((coordEquiv p O).symm a)
      left_inv _ := by simp only [LinearEquiv.symm_apply_apply, RingEquiv.symm_apply_apply]
      right_inv _ := by simp only [RingEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
      map_add' _ _ := by simp only [map_add]
      map_smul' _ _ := funext fun _ ↦ by
        simp only [overFrobeniusRingEquiv_smul, coordEquiv_apply, coord_frobeniusHom_mul,
          RingHom.id_apply, Pi.smul_apply, smul_eq_mul] }

private theorem overFrobeniusBasis_apply (i : Fin p) :
    overFrobeniusRingEquiv p O (overFrobeniusBasis p O i) = (1 + X : O⟦X⟧) ^ (i : ℕ) := by
  simp only [overFrobeniusBasis, Module.Basis.coe_ofEquivFun, LinearEquiv.coe_symm_mk,
    RingEquiv.apply_symm_apply, coordEquiv_symm_apply]
  rw [Finset.sum_eq_single i (fun j _ hji ↦ by simp [hji.symm]) (by simp)]; simp

private theorem overFrobeniusBasis_repr_apply (x : OverFrobenius p O) (i : Fin p) :
    (overFrobeniusBasis p O).repr x i = coord p O i (overFrobeniusRingEquiv p O x) := by
  simp [overFrobeniusBasis]

private def overFrobeniusAdjoinRootHom :
    AdjoinRoot (Polynomial.X ^ p - Polynomial.C (1 + X : O⟦X⟧)) →ₐ[O⟦X⟧] OverFrobenius p O :=
  AdjoinRoot.liftAlgHom (Polynomial.X ^ p - Polynomial.C (1 + X : O⟦X⟧))
    (Algebra.ofId O⟦X⟧ (OverFrobenius p O))
    ((overFrobeniusRingEquiv p O).symm (1 + X)) <| (overFrobeniusRingEquiv p O).injective <| by
      simp [overFrobeniusRingEquiv_algebraMap]

private theorem overFrobeniusAdjoinRootHom_bijective [Nontrivial O] :
    Function.Bijective (overFrobeniusAdjoinRootHom (p := p) (O := O)) := by
  let hp := Polynomial.monic_X_pow_sub_C (1 + X : O⟦X⟧) (Fact.out : p.Prime).ne_zero
  let pb := AdjoinRoot.powerBasis' hp
  let e := pb.basis.equiv (overFrobeniusBasis p O)
    (finCongr ((AdjoinRoot.powerBasis'_dim hp).trans (Polynomial.natDegree_X_pow_sub_C _)))
  have hEq : (overFrobeniusAdjoinRootHom (p := p) (O := O)).toLinearMap = e.toLinearMap :=
    pb.basis.ext fun i ↦ (overFrobeniusRingEquiv p O).injective <| by
      rw [AlgHom.toLinearMap_apply, LinearEquiv.coe_toLinearMap, Module.Basis.equiv_apply,
        overFrobeniusBasis_apply, pb.basis_eq_pow, AdjoinRoot.powerBasis'_gen, map_pow,
        overFrobeniusAdjoinRootHom, AdjoinRoot.liftAlgHom_root, map_pow,
        (overFrobeniusRingEquiv p O).apply_symm_apply, finCongr_apply, Fin.val_cast]
  exact (congrArg DFunLike.coe hEq).symm ▸ e.bijective

private def overFrobeniusAdjoinRootEquiv [Nontrivial O] :
    AdjoinRoot (Polynomial.X ^ p - Polynomial.C (1 + X : O⟦X⟧)) ≃ₐ[O⟦X⟧] OverFrobenius p O :=
  AlgEquiv.ofBijective (overFrobeniusAdjoinRootHom (p := p) (O := O))
    overFrobeniusAdjoinRootHom_bijective

private theorem overFrobeniusAdjoinRootEquiv_root [Nontrivial O] :
    overFrobeniusAdjoinRootEquiv (p := p) (O := O)
        (AdjoinRoot.root (Polynomial.X ^ p - Polynomial.C (1 + X : O⟦X⟧))) =
      (overFrobeniusRingEquiv p O).symm (1 + X) := by
  rw [overFrobeniusAdjoinRootEquiv, AlgEquiv.ofBijective_apply, overFrobeniusAdjoinRootHom,
    AdjoinRoot.liftAlgHom_root]

private def overFrobeniusToScalarAlgEquiv :
    @AlgEquiv O⟦X⟧ (OverFrobenius p O) O⟦X⟧ _ _ _ _ (scalarAlgebra p O) :=
  @AlgEquiv.mk O⟦X⟧ (OverFrobenius p O) O⟦X⟧ _ _ _ _ (scalarAlgebra p O)
    (overFrobeniusRingEquiv p O).toEquiv (overFrobeniusRingEquiv p O).map_mul'
    (overFrobeniusRingEquiv p O).map_add' (fun _ ↦ rfl)

end InternalBasis

section Operators

variable (p : ℕ) [Fact p.Prime] (O : Type*) [CommRing O] [IsAdicComplete (Ideal.span {(p : O)}) O]

/-- The `O`-algebra map `O⟦X⟧ →ₐ[O] Matrix (Fin p) (Fin p) O⟦X⟧` of left multiplication in
`basis p O`: entry `(i, j)` is `c_{i - j}(f)` (`j ≤ i`) and `c_{p + i - j}(f) * (1 + X)`
(`i < j`). -/
def leftMulMatrix : O⟦X⟧ →ₐ[O] Matrix (Fin p) (Fin p) O⟦X⟧ where
  toFun f := Algebra.leftMulMatrix (overFrobeniusBasis p O) ((overFrobeniusRingEquiv p O).symm f)
  map_one' := by rw [map_one, map_one]
  map_mul' _ _ := by rw [map_mul, map_mul]
  map_zero' := by rw [map_zero, map_zero]
  map_add' _ _ := by rw [map_add, map_add]
  commutes' _ := by
    rw [PowerSeries.algebraMap_eq, ← frobeniusHom_C (p := p), overFrobenius_algebraMap_eq,
      AlgHom.commutes]
    ext i j; simp [Matrix.algebraMap_eq_diagonal, Pi.algebraMap_def, PowerSeries.algebraMap_eq]

/-- Coleman's multiplicative norm `N : O⟦X⟧ →* O⟦X⟧`, defined as the determinant of
`leftMulMatrix p O` in the rank-`p` basis `basis p O` (agreeing with `Algebra.norm` for
`scalarAlgebra p O`). Requiring prime `p` and `(p)`-adic completeness ensures the finite basis
without non-finite-free fallbacks. -/
def norm : O⟦X⟧ →* O⟦X⟧ :=
  Matrix.detMonoidHom.comp (leftMulMatrix p O).toMonoidHom

/-- Coleman's norm restricted to units, `O⟦X⟧ˣ →* O⟦X⟧ˣ`, under the supported finite-free prime
and `(p)`-adic-completeness hypotheses of `Coleman.norm`. -/
def normUnits : O⟦X⟧ˣ →* O⟦X⟧ˣ :=
  Units.map (norm p O)

/-- Coleman's trace `τ : O⟦X⟧ →ₗ[O] O⟦X⟧`, defined as the trace of `leftMulMatrix p O` in the
rank-`p` basis `basis p O` (agreeing with `Algebra.trace` for `scalarAlgebra p O`). Requiring prime
`p` and `(p)`-adic completeness ensures the finite basis without non-finite-free fallbacks. -/
def trace : O⟦X⟧ →ₗ[O] O⟦X⟧ where
  toFun f := Matrix.trace (leftMulMatrix p O f)
  map_add' _ _ := by rw [map_add, Matrix.trace_add]
  map_smul' _ _ := by rw [map_smul, Matrix.trace_smul, RingHom.id_apply]

/-- The Coleman `O⟦X⟧`-basis `{(1 + X) ^ i : i < p}` of `O⟦X⟧` under `scalarAlgebra p O`. -/
def basis : @Module.Basis (Fin p) O⟦X⟧ O⟦X⟧ _ _ (scalarAlgebra p O).toModule :=
  @Module.Basis.map _ _ _ _ _ _ _ _ (scalarAlgebra p O).toModule (overFrobeniusBasis p O)
    (@AlgEquiv.toLinearEquiv _ _ _ _ _ _ _ (scalarAlgebra p O) overFrobeniusToScalarAlgEquiv)

/-- For nontrivial `O`, `AdjoinRoot (X ^ p - C (1 + X)) ≃ₐ[O⟦X⟧] O⟦X⟧` under `scalarAlgebra p O`,
sending `AdjoinRoot.root` to `1 + X`. -/
def adjoinRootEquiv [Nontrivial O] :
    @AlgEquiv O⟦X⟧ (AdjoinRoot (Polynomial.X ^ p - Polynomial.C (1 + X : O⟦X⟧))) O⟦X⟧ _ _ _ _
      (scalarAlgebra p O) :=
  @AlgEquiv.trans _ _ _ _ _ _ _ _ _ _ (scalarAlgebra p O)
    overFrobeniusAdjoinRootEquiv overFrobeniusToScalarAlgEquiv

private theorem leftMulMatrix_def (f : O⟦X⟧) :
    leftMulMatrix p O f =
      Algebra.leftMulMatrix (overFrobeniusBasis p O) ((overFrobeniusRingEquiv p O).symm f) := rfl

private theorem trace_def (f : O⟦X⟧) :
    trace p O f = Algebra.trace O⟦X⟧ (OverFrobenius p O) ((overFrobeniusRingEquiv p O).symm f) :=
  (Algebra.trace_eq_matrix_trace (overFrobeniusBasis p O)
    ((overFrobeniusRingEquiv p O).symm f)).symm

private theorem norm_eq_overFrobenius_norm (f : O⟦X⟧) :
    norm p O f = Algebra.norm O⟦X⟧ ((overFrobeniusRingEquiv p O).symm f) :=
  (Algebra.norm_eq_matrix_det (overFrobeniusBasis p O)
    ((overFrobeniusRingEquiv p O).symm f)).symm

/-- `Coleman.norm p O` equals Mathlib's `Algebra.norm` for `scalarAlgebra p O`. -/
theorem norm_eq_algebraNorm : norm p O = @Algebra.norm O⟦X⟧ O⟦X⟧ _ _ (scalarAlgebra p O) :=
  MonoidHom.ext fun f ↦ by
    simpa only [norm_eq_overFrobenius_norm, RingEquiv.symm_refl, RingEquiv.refl_apply,
      RingEquiv.apply_symm_apply] using
      @Algebra.norm_eq_of_equiv_equiv O⟦X⟧ (OverFrobenius p O) O⟦X⟧ O⟦X⟧ _ _ _ _ inferInstance
        (scalarAlgebra p O) (RingEquiv.refl _) (overFrobeniusRingEquiv p O)
        (RingHom.ext fun _ ↦ rfl) ((overFrobeniusRingEquiv p O).symm f)

/-- `Coleman.normUnits p O` equals `TauCeti.Algebra.normUnits` for `scalarAlgebra p O`. -/
theorem normUnits_eq_algebraNormUnits :
    normUnits p O = @TauCeti.Algebra.normUnits O⟦X⟧ _ O⟦X⟧ _ (scalarAlgebra p O) :=
  MonoidHom.ext fun f ↦ Units.ext <| by
    rw [normUnits, Units.coe_map, norm_eq_algebraNorm]
    exact (@TauCeti.Algebra.coe_normUnits O⟦X⟧ _ O⟦X⟧ _ (scalarAlgebra p O) f).symm

/-- `Coleman.normUnits p O` is the restriction of `Coleman.norm p O` via `Units.map`. -/
theorem normUnits_eq_unitsMap_norm : normUnits p O = Units.map (norm p O) := (rfl)

variable {p O}

/-- The underlying series of `normUnits p O f` is `norm p O f`. -/
@[simp]
theorem coe_normUnits (f : O⟦X⟧ˣ) :
    (normUnits p O f : O⟦X⟧) = norm p O (f : O⟦X⟧) :=
  Units.coe_map (norm p O) f

/-- Pointwise, `Coleman.trace p O` agrees with Mathlib's `Algebra.trace` for `scalarAlgebra p O`. -/
theorem trace_eq_algebraTrace (f : O⟦X⟧) :
    trace p O f = @Algebra.trace O⟦X⟧ O⟦X⟧ _ _ (scalarAlgebra p O) f := by
  rw [trace_def]
  simpa only [RingEquiv.symm_refl, RingEquiv.refl_apply, RingEquiv.apply_symm_apply] using
    @Algebra.trace_eq_of_equiv_equiv O⟦X⟧ (OverFrobenius p O) O⟦X⟧ O⟦X⟧ _ _ _ _ inferInstance
      (scalarAlgebra p O) (RingEquiv.refl _) (overFrobeniusRingEquiv p O) (RingHom.ext fun _ ↦ rfl)
      ((overFrobeniusRingEquiv p O).symm f)

/-- Coleman's trace is `O⟦X⟧`-linear for `frobeniusHom`: `τ(Φ(a) * f) = a * τ(f)`. -/
@[simp]
theorem trace_frobeniusHom_mul (a f : O⟦X⟧) :
    trace p O (frobeniusHom p O a * f) = a * trace p O f := by
  rw [trace_def, overFrobenius_smul_eq, LinearMap.map_smul, smul_eq_mul, trace_def]

private theorem leftMulMatrix_eq_coord_mul (f : O⟦X⟧) (i j : Fin p) :
    leftMulMatrix p O f i j = coord p O i (f * (1 + X) ^ (j : ℕ)) := by
  rw [leftMulMatrix_def, Algebra.leftMulMatrix_eq_repr_mul, overFrobeniusBasis_repr_apply, map_mul,
    (overFrobeniusRingEquiv p O).apply_symm_apply, overFrobeniusBasis_apply]

/-- The `i`-th element of `basis p O` is `(1 + X) ^ (i : ℕ)`. -/
@[simp]
theorem basis_apply (i : Fin p) : basis p O i = (1 + X : O⟦X⟧) ^ (i : ℕ) :=
  (@Module.Basis.map_apply _ _ _ _ _ _ _ _ (scalarAlgebra p O).toModule ..).trans
    (overFrobeniusBasis_apply i)

/-- The `i`-th coordinate of `f` in `basis p O` is `coord p O i f`. -/
@[simp]
theorem basis_repr_apply (f : O⟦X⟧) (i : Fin p) :
    @Module.Basis.repr (Fin p) O⟦X⟧ O⟦X⟧ _ _ (scalarAlgebra p O).toModule (basis p O) f i =
      coord p O i f := by
  rw [basis, @Module.Basis.map_repr _ _ _ _ _ _ _ _ (scalarAlgebra p O).toModule,
    LinearEquiv.trans_apply, overFrobeniusBasis_repr_apply]; rfl

/-- `adjoinRootEquiv p O` sends the adjoined root to `1 + X`. -/
@[simp]
theorem adjoinRootEquiv_root [Nontrivial O] :
    adjoinRootEquiv p O (AdjoinRoot.root (Polynomial.X ^ p - Polynomial.C (1 + X : O⟦X⟧))) =
      1 + X := by
  rw [adjoinRootEquiv, @AlgEquiv.trans_apply _ _ _ _ _ _ _ _ _ _ (scalarAlgebra p O),
    overFrobeniusAdjoinRootEquiv_root]
  exact (overFrobeniusRingEquiv p O).apply_symm_apply _

/-- `adjoinRootEquiv p O` sends `AdjoinRoot.of _ g` to `frobeniusHom p O g`. -/
@[simp]
theorem adjoinRootEquiv_of [Nontrivial O] (g : O⟦X⟧) :
    adjoinRootEquiv p O (AdjoinRoot.of (Polynomial.X ^ p - Polynomial.C (1 + X : O⟦X⟧)) g) =
      frobeniusHom p O g := by
  rw [← AdjoinRoot.algebraMap_eq,
    @AlgEquiv.commutes _ _ _ _ _ _ _ (scalarAlgebra p O) (adjoinRootEquiv p O) g,
    scalarAlgebra_algebraMap_apply]

/-- `Coleman.leftMulMatrix p O` agrees with `Algebra.leftMulMatrix` for `basis p O`. -/
theorem leftMulMatrix_eq_algebra_leftMulMatrix (f : O⟦X⟧) :
    leftMulMatrix p O f =
      @Algebra.leftMulMatrix O⟦X⟧ O⟦X⟧ _ _ (scalarAlgebra p O) (Fin p) _ _ (basis p O) f :=
  Matrix.ext fun i j ↦ by
    rw [leftMulMatrix_eq_coord_mul,
      @Algebra.leftMulMatrix_eq_repr_mul _ _ _ _ (scalarAlgebra p O) (Fin p) _ _ (basis p O),
      basis_repr_apply, basis_apply]

/-- Left multiplication by `Φ(a)` is represented by the scalar diagonal matrix `a • 1`. -/
@[simp]
theorem leftMulMatrix_frobeniusHom (a : O⟦X⟧) :
    leftMulMatrix p O (frobeniusHom p O a) = Matrix.diagonal fun _ ↦ a := by
  rw [leftMulMatrix_def, overFrobenius_algebraMap_eq, AlgHom.commutes]
  ext i j; simp [Matrix.algebraMap_eq_diagonal, Pi.algebraMap_def]

/-- Explicit formula for the `(i, j)` entry of `leftMulMatrix p O f`. -/
theorem leftMulMatrix_apply (f : O⟦X⟧) (i j : Fin p) :
    leftMulMatrix p O f i j =
      if h : (j : ℕ) ≤ i then coord p O ⟨(i : ℕ) - j, by omega⟩ f
      else coord p O ⟨p + (i : ℕ) - j, by omega⟩ f * (1 + X) := by
  rw [leftMulMatrix_eq_coord_mul]
  conv_lhs => rw [← sum_frobeniusHom_coord (p := p) f, Finset.sum_mul]
  simp only [map_sum, mul_assoc, ← pow_add, coord_frobeniusHom_mul, coord_one_add_X_pow]
  have hmod (r : Fin p) :
      ((r : ℕ) + j) % p = if (r : ℕ) + j < p then (r : ℕ) + j else (r : ℕ) + j - p := by
    split_ifs with h
    · exact Nat.mod_eq_of_lt h
    · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
  let r₀ : Fin p :=
    if h : (j : ℕ) ≤ i then ⟨(i : ℕ) - j, by omega⟩ else ⟨p + (i : ℕ) - j, by omega⟩
  rw [Finset.sum_eq_single r₀ (fun r _ hr ↦ by
    have hne : (i : ℕ) ≠ ((r : ℕ) + j) % p := by
      intro heq; apply hr; ext; rw [hmod] at heq; dsimp [r₀]; split_ifs at heq ⊢ <;> simp <;> omega
    simp [hne]) (by simp)]
  rcases le_or_gt (j : ℕ) i with h | h
  · simp [r₀, h, Nat.sub_add_cancel h, Nat.mod_eq_of_lt i.isLt, Nat.div_eq_of_lt i.isLt]
  · have hadd : p + (i : ℕ) - j + j = p + i := by omega
    simp [r₀, not_le.mpr h, hadd, Nat.add_div_left _ (Fact.out : p.Prime).pos,
      Nat.mod_eq_of_lt i.isLt, Nat.div_eq_of_lt i.isLt]

/-- Under `scalarAlgebra p O`, `O⟦X⟧` is a free `O⟦X⟧`-module. -/
theorem module_free_scalarAlgebra : @Module.Free O⟦X⟧ O⟦X⟧ _ _ (scalarAlgebra p O).toModule :=
  @Module.Free.of_basis _ _ _ _ (scalarAlgebra p O).toModule _ (basis p O)

/-- Under `scalarAlgebra p O`, `O⟦X⟧` is a finite `O⟦X⟧`-module. -/
theorem module_finite_scalarAlgebra : @Module.Finite O⟦X⟧ O⟦X⟧ _ _ (scalarAlgebra p O).toModule :=
  @Module.Finite.of_basis _ _ _ _ _ (scalarAlgebra p O).toModule _ (basis p O)

/-- Under `scalarAlgebra p O`, `O⟦X⟧` has rank `p` over `O⟦X⟧` (for nontrivial `O`). -/
theorem finrank_scalarAlgebra [Nontrivial O] :
    @Module.finrank O⟦X⟧ O⟦X⟧ _ _ (scalarAlgebra p O).toModule = p := by
  rw [@Module.finrank_eq_card_basis _ _ _ _ (scalarAlgebra p O).toModule _ _ _ (basis p O),
    Fintype.card_fin]

/-- Expanding `f * (1 + X) ^ j` in `basis p O` recovers column `j` of `leftMulMatrix p O f`. -/
theorem mul_one_add_X_pow_eq_sum_leftMulMatrix (f : O⟦X⟧) (j : Fin p) :
    f * (1 + X) ^ (j : ℕ) =
      ∑ i : Fin p, frobeniusHom p O (leftMulMatrix p O f i j) * (1 + X) ^ (i : ℕ) := by
  simpa only [leftMulMatrix_eq_coord_mul] using
    (sum_frobeniusHom_coord (p := p) (f * (1 + X) ^ (j : ℕ))).symm

/-- **Determinant formula for Coleman's norm.** `norm p O f = det (leftMulMatrix p O f)`. -/
theorem norm_eq_det_leftMulMatrix (f : O⟦X⟧) : norm p O f = Matrix.det (leftMulMatrix p O f) := by
  rw [norm_eq_overFrobenius_norm, Algebra.norm_eq_matrix_det (overFrobeniusBasis p O)]; rfl

/-- **Matrix-trace formula for Coleman's trace.** `trace p O f = trace (leftMulMatrix p O f)`. -/
theorem trace_eq_trace_leftMulMatrix (f : O⟦X⟧) :
    trace p O f = Matrix.trace (leftMulMatrix p O f) := (rfl)

/-- **Trace formula in the Coleman basis.** `trace p O f` equals `p` times `coord p O 0 f`. -/
theorem trace_eq_p_mul_coord_zero (f : O⟦X⟧) :
    trace p O f = (p : O⟦X⟧) * coord p O ⟨0, (Fact.out : p.Prime).pos⟩ f := by
  rw [trace_eq_trace_leftMulMatrix, Matrix.trace]
  have hdiag (i : Fin p) : leftMulMatrix p O f i i = coord p O ⟨0, (Fact.out : p.Prime).pos⟩ f := by
    simp only [leftMulMatrix_apply, dite_eq_left le_rfl]; congr 1; ext; simp
  simp [Matrix.diag, hdiag]

/-- Coleman's trace of `1` is `p`. -/
@[simp]
theorem trace_one : trace p O 1 = (p : O⟦X⟧) := by rw [trace_eq_p_mul_coord_zero, coord_one]; simp

/-- Coleman's trace on `Φ(a)` is `p * a`. -/
@[simp]
theorem trace_frobeniusHom (a : O⟦X⟧) : trace p O (frobeniusHom p O a) = (p : O⟦X⟧) * a := by
  simpa [mul_comm] using trace_frobeniusHom_mul (p := p) a 1

/-- Coleman's trace on a constant series `C c` is `p * C c`. -/
@[simp]
theorem trace_C (c : O) : trace p O (C c) = (p : O⟦X⟧) * C c := by
  simpa only [frobeniusHom_C] using trace_frobeniusHom (p := p) (C c)

/-- Coleman's trace on `(1 + X) ^ n` is `p * (1 + X) ^ (n / p)` when `p ∣ n`, and `0` otherwise. -/
@[simp]
theorem trace_one_add_X_pow (n : ℕ) :
    trace p O ((1 + X : O⟦X⟧) ^ n) = if p ∣ n then (p : O⟦X⟧) * (1 + X) ^ (n / p) else 0 := by
  simp only [trace_eq_p_mul_coord_zero, coord_one_add_X_pow, eq_comm (a := 0),
    Nat.dvd_iff_mod_eq_zero]
  split_ifs <;> simp

/-- Coleman's trace on `1 + X` is `0`. -/
@[simp]
theorem trace_one_add_X : trace p O (1 + X) = 0 := by
  simpa [Nat.Prime.not_dvd_one (Fact.out : p.Prime)] using trace_one_add_X_pow (p := p) (O := O) 1

/-- Coleman's trace on `X` is `-p`. -/
@[simp]
theorem trace_X : trace p O X = -(p : O⟦X⟧) := by
  have hX : (X : O⟦X⟧) = (1 + X) - 1 := by ring
  rw [hX, map_sub, trace_one_add_X, trace_one, zero_sub]

/-- Coleman's norm of `Φ(a)` is `a ^ p`. -/
@[simp]
theorem norm_frobeniusHom (a : O⟦X⟧) : norm p O (frobeniusHom p O a) = a ^ p := by
  rw [norm_eq_overFrobenius_norm, overFrobenius_algebraMap_eq,
    Algebra.norm_algebraMap_of_basis (overFrobeniusBasis p O), Fintype.card_fin]

/-- Coleman's norm of `0` is `0`. -/
@[simp]
theorem norm_zero : norm p O 0 = 0 := by
  simpa [zero_pow (Fact.out : p.Prime).ne_zero] using norm_frobeniusHom (p := p) (0 : O⟦X⟧)

/-- Coleman's norm of a constant series `C c` is `C (c ^ p)`. -/
@[simp]
theorem norm_C (c : O) : norm p O (C c) = C (c ^ p) := by
  simpa only [frobeniusHom_C, map_pow] using norm_frobeniusHom (p := p) (C c)

/-- **First-order expansion of Coleman's norm near `1`.** For any `a, f ∈ O⟦X⟧`, there exists
`r ∈ O⟦X⟧` such that `N(1 + Φ(a) * f) = 1 + τ(f) * a + r * a ^ 2`. -/
theorem norm_one_add_frobeniusHom_mul (a f : O⟦X⟧) :
    ∃ r : O⟦X⟧, norm p O (1 + frobeniusHom p O a * f) = 1 + trace p O f * a + r * a ^ 2 := by
  have := Module.Free.of_basis (overFrobeniusBasis p O)
  have := Module.Finite.of_basis (overFrobeniusBasis p O)
  obtain ⟨r, hr⟩ := Algebra.norm_one_add_smul a ((overFrobeniusRingEquiv p O).symm f)
  exact ⟨r, by rw [norm_eq_overFrobenius_norm, map_add, map_one, overFrobenius_smul_eq, hr,
    ← trace_def]⟩

/-- **Norm of linear elements `Φ(g) - (1 + X)`.** `N(Φ(g) - (1 + X)) = g ^ p - (1 + X)`. -/
theorem norm_frobeniusHom_sub_one_add_X (g : O⟦X⟧) :
    norm p O (frobeniusHom p O g - (1 + X)) = g ^ p - (1 + X) := by
  nontriviality O
  set P : Polynomial O⟦X⟧ := Polynomial.X ^ p - Polynomial.C (1 + X : O⟦X⟧)
  have harg : overFrobeniusAdjoinRootEquiv (p := p) (O := O) (AdjoinRoot.of P g - AdjoinRoot.root P)
      = (overFrobeniusRingEquiv p O).symm (frobeniusHom p O g - (1 + X)) := by
    rw [map_sub, ← AdjoinRoot.algebraMap_eq, AlgEquiv.commutes, ← overFrobenius_algebraMap_eq,
      overFrobeniusAdjoinRootEquiv_root, map_sub]
  rw [norm_eq_overFrobenius_norm, ← harg,
    Algebra.norm_eq_of_algEquiv (overFrobeniusAdjoinRootEquiv (p := p) (O := O)),
    AdjoinRoot.norm_algebraMap_sub_root
      (Polynomial.monic_X_pow_sub_C (1 + X) (Fact.out : p.Prime).ne_zero) g]
  simp

private theorem norm_eq_neg_one_pow_mul_of_norm_neg {f : O⟦X⟧} (hf : norm p O (-f) = -f) :
    norm p O f = (-1 : O⟦X⟧) ^ (p - 1) * f := by
  have hneg : (-1 : O⟦X⟧) ^ p * norm p O f = -f := by
    have hnegf : C (-1 : O) * f = -f := by simp
    have h := congrArg (norm p O) hnegf
    rw [map_mul, norm_C, map_pow, map_neg, map_one] at h; exact h.trans hf
  have hmul := congrArg (((-1 : O⟦X⟧) ^ p) * ·) hneg
  simp only [← mul_assoc, ← mul_pow, neg_one_mul, neg_neg, one_pow, one_mul] at hmul
  rw [hmul, neg_eq_neg_one_mul f, ← mul_assoc]
  congr 1; conv_lhs => rw [(Nat.sub_add_cancel (Fact.out : p.Prime).pos).symm, pow_succ]
  ring

/-- **Norm of `1 + X`:** `N(1 + X) = (-1) ^ (p - 1) * (1 + X)`. -/
@[simp]
theorem norm_one_add_X : norm p O (1 + X) = (-1 : O⟦X⟧) ^ (p - 1) * (1 + X) :=
  norm_eq_neg_one_pow_mul_of_norm_neg <| by
    simpa [zero_pow (Fact.out : p.Prime).ne_zero] using
      norm_frobeniusHom_sub_one_add_X (p := p) (0 : O⟦X⟧)

/-- **Norm of `X`:** `N(X) = (-1) ^ (p - 1) * X`. -/
@[simp]
theorem norm_X : norm p O X = (-1 : O⟦X⟧) ^ (p - 1) * X :=
  norm_eq_neg_one_pow_mul_of_norm_neg <| by
    simpa using norm_frobeniusHom_sub_one_add_X (p := p) (1 : O⟦X⟧)

/-- Functoriality of Coleman's norm along any homomorphism between `(p)`-adically complete rings. -/
theorem map_norm {O' : Type*} [CommRing O'] [IsAdicComplete (Ideal.span {(p : O')}) O']
    (φ : O →+* O') (f : O⟦X⟧) :
    PowerSeries.map φ (norm p O f) = norm p O' (PowerSeries.map φ f) := by
  rw [norm_eq_det_leftMulMatrix, norm_eq_det_leftMulMatrix, RingHom.map_det]
  congr 1; refine Matrix.ext fun i j ↦ ?_
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, leftMulMatrix_apply]
  split_ifs <;> simp [map_coord]

/-- Functoriality of Coleman's trace along any homomorphism of `(p)`-adically complete rings. -/
theorem map_trace {O' : Type*} [CommRing O'] [IsAdicComplete (Ideal.span {(p : O')}) O']
    (φ : O →+* O') (f : O⟦X⟧) :
    PowerSeries.map φ (trace p O f) = trace p O' (PowerSeries.map φ f) := by
  rw [trace_eq_p_mul_coord_zero, trace_eq_p_mul_coord_zero, map_mul, map_natCast, map_coord]

end Operators

section Examples

example : norm 2 (ZMod 2) (1 + X) = -(1 + X) := by simp

example : norm 3 (ZMod 3) (1 + X) = 1 + X ∧ norm 3 (ZMod 3) X = X ∧
    trace 3 (ZMod 3) (1 + X) = 0 := by simp

example {O : Type*} [CommRing O] [IsAdicComplete (Ideal.span {(2 : O)}) O] :
    norm 2 O (1 + X) = -(1 + X) ∧ norm 2 O X = -X := by simp

example {O : Type*} [CommRing O] [IsAdicComplete (Ideal.span {(3 : O)}) O] :
    norm 3 O (1 + X) = 1 + X ∧ trace 3 O 1 = 3 ∧ norm 3 O (C 2) = C 8 := by
  refine ⟨by simp, by simp, ?_⟩; rw [norm_C]; norm_num

end Examples

end TauCeti.Coleman
