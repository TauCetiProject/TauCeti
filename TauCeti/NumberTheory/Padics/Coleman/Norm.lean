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

Let `p` be a prime and `O` a `(p)`-adically complete commutative ring. The Frobenius substitution
`Φ = TauCeti.Coleman.frobeniusHom p O` equips `O⟦X⟧` with an `O⟦X⟧`-algebra structure
`TauCeti.Coleman.scalarAlgebra p O` (marked `@[instance_reducible]` rather than a global instance,
to avoid clashing with `Algebra.id O⟦X⟧`). By the Coleman basis theorem in
`TauCeti.NumberTheory.Padics.Coleman.Basic`, `O⟦X⟧` is a free `O⟦X⟧`-module under
`scalarAlgebra p O` with explicit basis `TauCeti.Coleman.basis p O` (`1, 1 + X, …,
(1 + X) ^ (p - 1)`), of rank `p` when `[Nontrivial O]`, and when `[Nontrivial O]` is isomorphic as
an `O⟦X⟧`-algebra to `AdjoinRoot (Polynomial.X ^ p - Polynomial.C (1 + X))` via
`TauCeti.Coleman.adjoinRootEquiv p O`.

Mathlib's `Algebra.norm` and `Algebra.trace` for `scalarAlgebra p O` give Coleman's multiplicative
norm operator `N` and linear trace operator `τ` on `O⟦X⟧`. This file develops their explicit matrix
and coordinate formulas, first-order expansion near `1`, Kummer norm evaluation, and functoriality
along coefficient ring homomorphisms, which feed the mod-`p ^ k` norm contraction and
corrected-norm projector in `TauCeti.NumberTheory.Padics.Coleman.Limit` as well as the `ψ` and
root-of-unity sum/product identities in `TauCeti.NumberTheory.Padics.Coleman.Measure`.

## Main definitions

* `TauCeti.Coleman.scalarAlgebra`: the `@[instance_reducible]` `O⟦X⟧`-algebra structure on `O⟦X⟧`
  induced by `frobeniusHom`.
* `TauCeti.Coleman.norm`, `TauCeti.Coleman.normUnits`: Coleman's norm operator on `O⟦X⟧` and its
  restriction to `O⟦X⟧ˣ`.
* `TauCeti.Coleman.trace`: Coleman's trace operator on `O⟦X⟧`.
* `TauCeti.Coleman.basis`: the rank-`p` `Module.Basis (Fin p) O⟦X⟧ O⟦X⟧` for `scalarAlgebra p O`.
* `TauCeti.Coleman.adjoinRootEquiv`: for `[Nontrivial O]`, the `O⟦X⟧`-algebra equivalence between
  `AdjoinRoot (Polynomial.X ^ p - Polynomial.C (1 + X))` and `O⟦X⟧` under `scalarAlgebra p O`.
* `TauCeti.Coleman.leftMulMatrix`: the `O`-algebra homomorphism
  `O⟦X⟧ →ₐ[O] Matrix (Fin p) (Fin p) O⟦X⟧` giving left multiplication in `basis p O`.

## Main results

* `TauCeti.Coleman.module_free_scalarAlgebra`, `TauCeti.Coleman.module_finite_scalarAlgebra`,
  `TauCeti.Coleman.finrank_scalarAlgebra`: `O⟦X⟧` is free and finite for `scalarAlgebra p O`, of
  rank `p` when `[Nontrivial O]`.
* `TauCeti.Coleman.norm_eq_det_leftMulMatrix`, `TauCeti.Coleman.trace_eq_trace_leftMulMatrix`,
  `TauCeti.Coleman.trace_eq_p_mul_coord_zero`: determinant formula for `N` and trace formulas
  `τ(f) = Matrix.trace (leftMulMatrix p O f) = p * c₀(f)`.
* `TauCeti.Coleman.norm_one_add_frobeniusHom_mul`: first-order expansion
  `N(1 + Φ(a) * f) = 1 + τ(f) * a + r * a ^ 2`.
* `TauCeti.Coleman.norm_frobeniusHom_sub_one_add_X`, `TauCeti.Coleman.norm_one_add_X`,
  `TauCeti.Coleman.norm_X`: explicit values `N(Φ(g) - (1 + X)) = g ^ p - (1 + X)`,
  `N(1 + X) = (-1) ^ (p - 1) * (1 + X)`, and `N(X) = (-1) ^ (p - 1) * X`.
* `TauCeti.Coleman.map_norm`, `TauCeti.Coleman.map_trace`: functoriality along coefficient ring
  homomorphisms.

## References

* R. F. Coleman, *Division Values in Local Fields*, Invent. Math. 53 (1979), §§II, IV (Theorem 4,
  Lemma 6, Theorem 11).
* J. Coates and R. Sujatha, *Cyclotomic Fields and Zeta Values*, Springer (2006), §2.2
  (Proposition 2.2.3).
* R. Sharifi, *Iwasawa Theory*, §5.4 (Proposition 5.4.3, Definition 5.4.4, Lemma 5.4.14).
* J. Rodrigues Jacinto and C. Williams, *An introduction to p-adic L-functions* (2025), Chapter 10
  (Lemmas 10.8–10.10).
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

/-- The `O⟦X⟧`-algebra structure on `O⟦X⟧` given by Frobenius substitution
`f ↦ f((1 + X) ^ p - 1)`. Marked `@[instance_reducible]` rather than `instance` so it does not
clash with `Algebra.id O⟦X⟧`. -/
@[instance_reducible]
def scalarAlgebra : Algebra O⟦X⟧ O⟦X⟧ :=
  (frobeniusHom p O).toRingHom.toAlgebra

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

/-- Internal type synonym for `O⟦X⟧` equipped with `scalarAlgebra p O`, avoiding the
`Semiring.toModule` vs `Algebra.toModule` diamond in internal proofs. -/
private def OverFrobenius (_p : ℕ) (O : Type*) := O⟦X⟧

private instance : CommRing (OverFrobenius p O) := inferInstanceAs (CommRing O⟦X⟧)

private def overFrobeniusRingEquiv : OverFrobenius p O ≃+* O⟦X⟧ := RingEquiv.refl _

private instance : Algebra O⟦X⟧ (OverFrobenius p O) :=
  ((overFrobeniusRingEquiv p O).symm.toRingHom.comp (frobeniusHom p O).toRingHom).toAlgebra

private theorem overFrobeniusRingEquiv_algebraMap (c : O⟦X⟧) :
    overFrobeniusRingEquiv p O (algebraMap O⟦X⟧ (OverFrobenius p O) c) = frobeniusHom p O c := rfl

private theorem overFrobeniusRingEquiv_smul (c : O⟦X⟧) (x : OverFrobenius p O) :
    overFrobeniusRingEquiv p O (c • x) = frobeniusHom p O c * overFrobeniusRingEquiv p O x := rfl

private theorem overFrobenius_algebraMap_comp :
    (@algebraMap O⟦X⟧ O⟦X⟧ _ _ (scalarAlgebra p O)).comp (RingEquiv.refl O⟦X⟧ : O⟦X⟧ →+* O⟦X⟧) =
      (overFrobeniusRingEquiv p O : OverFrobenius p O →+* O⟦X⟧).comp
        (algebraMap O⟦X⟧ (OverFrobenius p O)) :=
  RingHom.ext fun _ ↦ rfl

/-- Coleman's multiplicative norm operator `N : O⟦X⟧ →* O⟦X⟧`, defined as `Algebra.norm` for
`scalarAlgebra p O`. -/
def norm : O⟦X⟧ →* O⟦X⟧ :=
  @Algebra.norm O⟦X⟧ O⟦X⟧ _ _ (scalarAlgebra p O)

/-- `Coleman.norm p O` equals Mathlib's `Algebra.norm` for `scalarAlgebra p O`. -/
theorem norm_eq_algebraNorm :
    norm p O = @Algebra.norm O⟦X⟧ O⟦X⟧ _ _ (scalarAlgebra p O) := (rfl)

/-- Pointwise, `Coleman.norm p O` equals Mathlib's `Algebra.norm` for `scalarAlgebra p O`. -/
theorem norm_eq_algebraNorm_apply {p : ℕ} {O : Type*} [CommRing O] (f : O⟦X⟧) :
    norm p O f = @Algebra.norm O⟦X⟧ O⟦X⟧ _ _ (scalarAlgebra p O) f := (rfl)

/-- Coleman's norm restricted to units, `O⟦X⟧ˣ →* O⟦X⟧ˣ`. -/
def normUnits : O⟦X⟧ˣ →* O⟦X⟧ˣ :=
  @TauCeti.Algebra.normUnits O⟦X⟧ _ O⟦X⟧ _ (scalarAlgebra p O)

/-- `Coleman.normUnits p O` equals `TauCeti.Algebra.normUnits` for `scalarAlgebra p O`. -/
theorem normUnits_eq_algebraNormUnits :
    normUnits p O = @TauCeti.Algebra.normUnits O⟦X⟧ _ O⟦X⟧ _ (scalarAlgebra p O) := (rfl)

/-- The underlying series of `normUnits p O f` is `norm p O f`. -/
@[simp]
theorem coe_normUnits {p : ℕ} {O : Type*} [CommRing O] (f : O⟦X⟧ˣ) :
    (normUnits p O f : O⟦X⟧) = norm p O (f : O⟦X⟧) :=
  @TauCeti.Algebra.coe_normUnits O⟦X⟧ _ O⟦X⟧ _ (scalarAlgebra p O) f

/-- `Coleman.normUnits p O` is the restriction of `Coleman.norm p O` via `Units.map`. -/
theorem normUnits_eq_unitsMap_norm :
    normUnits p O = Units.map (norm p O) :=
  MonoidHom.ext fun f ↦ Units.ext (coe_normUnits f)

/-- Coleman's trace operator `τ : O⟦X⟧ →ₗ[O] O⟦X⟧`, agreeing pointwise with `Algebra.trace` for
`scalarAlgebra p O`. -/
def trace : O⟦X⟧ →ₗ[O] O⟦X⟧ where
  toFun f := Algebra.trace O⟦X⟧ (OverFrobenius p O) ((overFrobeniusRingEquiv p O).symm f)
  map_add' f g := by rw [map_add, map_add]
  map_smul' c f := by
    have hsmul : (overFrobeniusRingEquiv p O).symm (c • f) =
        C c • (overFrobeniusRingEquiv p O).symm f := by
      apply (overFrobeniusRingEquiv p O).injective
      rw [(overFrobeniusRingEquiv p O).apply_symm_apply, overFrobeniusRingEquiv_smul,
        frobeniusHom_C, (overFrobeniusRingEquiv p O).apply_symm_apply, PowerSeries.smul_eq_C_mul]
    rw [hsmul, LinearMap.map_smul, RingHom.id_apply, smul_eq_mul, PowerSeries.smul_eq_C_mul]

private theorem trace_eq_overFrobenius_trace (f : O⟦X⟧) :
    trace p O f = Algebra.trace O⟦X⟧ (OverFrobenius p O) ((overFrobeniusRingEquiv p O).symm f) :=
  rfl

/-- Pointwise, `Coleman.trace p O` agrees with Mathlib's `Algebra.trace` for `scalarAlgebra p O`. -/
theorem trace_eq_algebraTrace {p : ℕ} {O : Type*} [CommRing O] (f : O⟦X⟧) :
    trace p O f = @Algebra.trace O⟦X⟧ O⟦X⟧ _ _ (scalarAlgebra p O) f := by
  rw [trace_eq_overFrobenius_trace]
  have h := @Algebra.trace_eq_of_equiv_equiv O⟦X⟧ (OverFrobenius p O) O⟦X⟧ O⟦X⟧ _ _ _ _ _
    (scalarAlgebra p O) (RingEquiv.refl O⟦X⟧) (overFrobeniusRingEquiv p O)
    (overFrobenius_algebraMap_comp p O) ((overFrobeniusRingEquiv p O).symm f)
  simpa only [RingEquiv.symm_refl, RingEquiv.refl_apply, RingEquiv.apply_symm_apply] using h

/-- Coleman's trace is `O⟦X⟧`-linear for `frobeniusHom`: `τ(Φ(a) * f) = a * τ(f)`. -/
@[simp]
theorem trace_frobeniusHom_mul {p : ℕ} {O : Type*} [CommRing O] (a f : O⟦X⟧) :
    trace p O (frobeniusHom p O a * f) = a * trace p O f := by
  have hsmul : (overFrobeniusRingEquiv p O).symm (frobeniusHom p O a * f) =
      a • (overFrobeniusRingEquiv p O).symm f := by
    apply (overFrobeniusRingEquiv p O).injective
    rw [(overFrobeniusRingEquiv p O).apply_symm_apply, overFrobeniusRingEquiv_smul,
      (overFrobeniusRingEquiv p O).apply_symm_apply]
  rw [trace_eq_overFrobenius_trace, hsmul, LinearMap.map_smul, smul_eq_mul,
    trace_eq_overFrobenius_trace]

private theorem norm_eq_overFrobenius_norm (f : O⟦X⟧) :
    norm p O f = Algebra.norm O⟦X⟧ ((overFrobeniusRingEquiv p O).symm f) := by
  have h := @Algebra.norm_eq_of_equiv_equiv O⟦X⟧ (OverFrobenius p O) O⟦X⟧ O⟦X⟧ _ _ _ _ _
    (scalarAlgebra p O) (RingEquiv.refl O⟦X⟧) (overFrobeniusRingEquiv p O)
    (overFrobenius_algebraMap_comp p O) ((overFrobeniusRingEquiv p O).symm f)
  simpa only [norm, RingEquiv.symm_refl, RingEquiv.refl_apply, RingEquiv.apply_symm_apply] using
    h.symm

end Definitions

section InternalBasis

variable {p : ℕ} [Fact p.Prime] {O : Type*} [CommRing O] [IsAdicComplete (Ideal.span {(p : O)}) O]

private def overFrobeniusBasis (p : ℕ) [Fact p.Prime] (O : Type*) [CommRing O]
    [IsAdicComplete (Ideal.span {(p : O)}) O] :
    Module.Basis (Fin p) O⟦X⟧ (OverFrobenius p O) :=
  Module.Basis.ofEquivFun
    { toFun x := coordEquiv p O (overFrobeniusRingEquiv p O x)
      invFun a := (overFrobeniusRingEquiv p O).symm ((coordEquiv p O).symm a)
      left_inv _ := by simp only [LinearEquiv.symm_apply_apply, RingEquiv.symm_apply_apply]
      right_inv _ := by simp only [RingEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
      map_add' _ _ := by simp only [map_add]
      map_smul' c x := by
        funext i
        simp only [overFrobeniusRingEquiv_smul, coordEquiv_apply, coord_frobeniusHom_mul,
          RingHom.id_apply, Pi.smul_apply, smul_eq_mul] }

private theorem overFrobeniusBasis_apply (i : Fin p) :
    overFrobeniusRingEquiv p O (overFrobeniusBasis p O i) = (1 + X : O⟦X⟧) ^ (i : ℕ) := by
  simp only [overFrobeniusBasis, Module.Basis.coe_ofEquivFun, LinearEquiv.coe_symm_mk,
    RingEquiv.apply_symm_apply, coordEquiv_symm_apply]
  rw [Finset.sum_eq_single i (fun j _ hji ↦ by simp [hji.symm]) (by simp)]
  simp

private theorem overFrobeniusBasis_repr_apply (x : OverFrobenius p O) (i : Fin p) :
    (overFrobeniusBasis p O).repr x i = coord p O i (overFrobeniusRingEquiv p O x) := by
  simp [overFrobeniusBasis]

private def overFrobeniusAdjoinRootEquiv [Nontrivial O] :
    AdjoinRoot (Polynomial.X ^ p - Polynomial.C (1 + X : O⟦X⟧)) ≃ₐ[O⟦X⟧] OverFrobenius p O := by
  set P : Polynomial O⟦X⟧ := Polynomial.X ^ p - Polynomial.C (1 + X : O⟦X⟧)
  have hP : P.Monic := Polynomial.monic_X_pow_sub_C (1 + X) (Fact.out : p.Prime).ne_zero
  have hroot : Polynomial.aeval ((overFrobeniusRingEquiv p O).symm (1 + X : O⟦X⟧)) P = 0 := by
    apply (overFrobeniusRingEquiv p O).injective
    simp only [P, map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C, map_zero,
      (overFrobeniusRingEquiv p O).apply_symm_apply, overFrobeniusRingEquiv_algebraMap,
      frobeniusHom_one_add_X, sub_self]
  let φ : AdjoinRoot P →ₐ[O⟦X⟧] OverFrobenius p O :=
    AdjoinRoot.liftAlgHom P (Algebra.ofId O⟦X⟧ (OverFrobenius p O))
      ((overFrobeniusRingEquiv p O).symm (1 + X)) (by simpa [Polynomial.aeval_def] using hroot)
  let pb := AdjoinRoot.powerBasis' hP
  have hdeg : pb.dim = p := Polynomial.natDegree_X_pow_sub_C (1 + X : O⟦X⟧)
  let e := pb.basis.equiv (overFrobeniusBasis p O) (finCongr hdeg)
  have hEq : φ.toLinearMap = e.toLinearMap := pb.basis.ext fun i ↦ by
    apply (overFrobeniusRingEquiv p O).injective
    rw [AlgHom.toLinearMap_apply, LinearEquiv.coe_toLinearMap,
      pb.basis.equiv_apply i (overFrobeniusBasis p O) (finCongr hdeg), pb.basis_eq_pow i, map_pow,
      overFrobeniusBasis_apply, finCongr_apply, Fin.val_cast]
    simp [φ, pb]
  exact AlgEquiv.ofBijective φ ((congrArg DFunLike.coe hEq).symm ▸ e.bijective)

private def overFrobeniusToScalarLinearEquiv :
    @LinearEquiv O⟦X⟧ O⟦X⟧ _ _ (RingHom.id O⟦X⟧) (RingHom.id O⟦X⟧) _ _
      (OverFrobenius p O) O⟦X⟧ _ _ _ (scalarAlgebra p O).toModule :=
  @LinearEquiv.mk O⟦X⟧ O⟦X⟧ _ _ (RingHom.id O⟦X⟧) (RingHom.id O⟦X⟧) _ _
    (OverFrobenius p O) O⟦X⟧ _ _ _ (scalarAlgebra p O).toModule
    (@LinearMap.mk O⟦X⟧ O⟦X⟧ _ _ (RingHom.id O⟦X⟧) (OverFrobenius p O) O⟦X⟧ _ _ _
      (scalarAlgebra p O).toModule (overFrobeniusRingEquiv p O).toAddHom
      (fun c x ↦ overFrobeniusRingEquiv_smul p O c x))
    (overFrobeniusRingEquiv p O).symm
    (overFrobeniusRingEquiv p O).symm_apply_apply
    (overFrobeniusRingEquiv p O).apply_symm_apply

omit [Fact p.Prime] [IsAdicComplete (Ideal.span {(p : O)}) O] in
private theorem overFrobeniusToScalarLinearEquiv_apply (x : OverFrobenius p O) :
    overFrobeniusToScalarLinearEquiv x = overFrobeniusRingEquiv p O x := rfl

omit [Fact p.Prime] [IsAdicComplete (Ideal.span {(p : O)}) O] in
private theorem overFrobeniusToScalarLinearEquiv_symm_apply (f : O⟦X⟧) :
    overFrobeniusToScalarLinearEquiv.symm f = (overFrobeniusRingEquiv p O).symm f := rfl

private def overFrobeniusToScalarAlgEquiv :
    @AlgEquiv O⟦X⟧ (OverFrobenius p O) O⟦X⟧ _ _ _ _ (scalarAlgebra p O) :=
  @AlgEquiv.mk O⟦X⟧ (OverFrobenius p O) O⟦X⟧ _ _ _ _ (scalarAlgebra p O)
    (overFrobeniusRingEquiv p O).toEquiv
    (overFrobeniusRingEquiv p O).map_mul'
    (overFrobeniusRingEquiv p O).map_add'
    (fun _ ↦ rfl)

omit [Fact p.Prime] [IsAdicComplete (Ideal.span {(p : O)}) O] in
private theorem overFrobeniusToScalarAlgEquiv_apply (x : OverFrobenius p O) :
    overFrobeniusToScalarAlgEquiv x = overFrobeniusRingEquiv p O x := rfl

end InternalBasis

section Operators

variable (p : ℕ) [Fact p.Prime] (O : Type*) [CommRing O] [IsAdicComplete (Ideal.span {(p : O)}) O]

/-- The Coleman `O⟦X⟧`-basis `{(1 + X) ^ i : i < p}` of `O⟦X⟧` under `scalarAlgebra p O`. -/
def basis : @Module.Basis (Fin p) O⟦X⟧ O⟦X⟧ _ _ (scalarAlgebra p O).toModule :=
  @Module.Basis.map (Fin p) O⟦X⟧ (OverFrobenius p O) O⟦X⟧ _ _ _ _ (scalarAlgebra p O).toModule
    (overFrobeniusBasis p O) overFrobeniusToScalarLinearEquiv

/-- For nontrivial `O`, the `O⟦X⟧`-algebra equivalence between
`AdjoinRoot (Polynomial.X ^ p - Polynomial.C (1 + X))` and `O⟦X⟧` equipped with `scalarAlgebra p O`,
sending `AdjoinRoot.root` to `1 + X`. -/
def adjoinRootEquiv [Nontrivial O] :
    @AlgEquiv O⟦X⟧ (AdjoinRoot (Polynomial.X ^ p - Polynomial.C (1 + X : O⟦X⟧))) O⟦X⟧ _ _ _ _
      (scalarAlgebra p O) :=
  @AlgEquiv.trans O⟦X⟧ (AdjoinRoot (Polynomial.X ^ p - Polynomial.C (1 + X : O⟦X⟧)))
    (OverFrobenius p O) O⟦X⟧ _ _ _ _ _ _ (scalarAlgebra p O)
    overFrobeniusAdjoinRootEquiv overFrobeniusToScalarAlgEquiv

/-- The `O`-algebra homomorphism `O⟦X⟧ →ₐ[O] Matrix (Fin p) (Fin p) O⟦X⟧` giving left
multiplication in the Coleman basis `basis p O`. Entry `(i, j)` of `leftMulMatrix p O f` is
`c_{i - j}(f)` for `j ≤ i`, and `c_{p + i - j}(f) * (1 + X)` for `i < j`. -/
def leftMulMatrix : O⟦X⟧ →ₐ[O] Matrix (Fin p) (Fin p) O⟦X⟧ where
  toFun f := Algebra.leftMulMatrix (overFrobeniusBasis p O) ((overFrobeniusRingEquiv p O).symm f)
  map_one' := by rw [map_one, map_one]
  map_mul' f g := by rw [map_mul, map_mul]
  map_zero' := by rw [map_zero, map_zero]
  map_add' f g := by rw [map_add, map_add]
  commutes' c := by
    have halg : (overFrobeniusRingEquiv p O).symm (algebraMap O O⟦X⟧ c) =
        algebraMap O⟦X⟧ (OverFrobenius p O) (C c) :=
      (overFrobeniusRingEquiv p O).injective (by
        rw [(overFrobeniusRingEquiv p O).apply_symm_apply, overFrobeniusRingEquiv_algebraMap,
          frobeniusHom_C, PowerSeries.algebraMap_eq])
    rw [halg, AlgHom.commutes]
    ext i j
    simp [Matrix.algebraMap_eq_diagonal, Pi.algebraMap_def, PowerSeries.algebraMap_eq]

variable {p O}

private theorem leftMulMatrix_eq_overFrobenius (f : O⟦X⟧) :
    leftMulMatrix p O f =
      Algebra.leftMulMatrix (overFrobeniusBasis p O) ((overFrobeniusRingEquiv p O).symm f) :=
  rfl

/-- The `i`-th element of `basis p O` is `(1 + X) ^ (i : ℕ)`. -/
@[simp]
theorem basis_apply (i : Fin p) : basis p O i = (1 + X : O⟦X⟧) ^ (i : ℕ) := by
  rw [basis, @Module.Basis.map_apply (Fin p) O⟦X⟧ (OverFrobenius p O) O⟦X⟧ _ _ _ _
    (scalarAlgebra p O).toModule, overFrobeniusToScalarLinearEquiv_apply, overFrobeniusBasis_apply]

/-- The `i`-th coordinate of `f` in `basis p O` is `coord p O i f`. -/
@[simp]
theorem basis_repr_apply (f : O⟦X⟧) (i : Fin p) :
    @Module.Basis.repr (Fin p) O⟦X⟧ O⟦X⟧ _ _ (scalarAlgebra p O).toModule (basis p O) f i =
      coord p O i f := by
  rw [basis, @Module.Basis.map_repr (Fin p) O⟦X⟧ (OverFrobenius p O) O⟦X⟧ _ _ _ _
    (scalarAlgebra p O).toModule, LinearEquiv.trans_apply,
    overFrobeniusToScalarLinearEquiv_symm_apply, overFrobeniusBasis_repr_apply,
    (overFrobeniusRingEquiv p O).apply_symm_apply]

/-- `adjoinRootEquiv p O` sends the adjoined root to `1 + X`. -/
@[simp]
theorem adjoinRootEquiv_root [Nontrivial O] :
    adjoinRootEquiv p O (AdjoinRoot.root (Polynomial.X ^ p - Polynomial.C (1 + X : O⟦X⟧))) =
      1 + X := by
  rw [adjoinRootEquiv, @AlgEquiv.trans_apply O⟦X⟧ _ (OverFrobenius p O) O⟦X⟧ _ _ _ _ _ _
    (scalarAlgebra p O), overFrobeniusToScalarAlgEquiv_apply]
  simp [overFrobeniusAdjoinRootEquiv]

/-- `adjoinRootEquiv p O` sends `AdjoinRoot.of _ g` to `frobeniusHom p O g`. -/
@[simp]
theorem adjoinRootEquiv_of [Nontrivial O] (g : O⟦X⟧) :
    adjoinRootEquiv p O (AdjoinRoot.of (Polynomial.X ^ p - Polynomial.C (1 + X : O⟦X⟧)) g) =
      frobeniusHom p O g := by
  rw [← AdjoinRoot.algebraMap_eq,
    @AlgEquiv.commutes O⟦X⟧ _ O⟦X⟧ _ _ _ _ (scalarAlgebra p O) (adjoinRootEquiv p O) g,
    scalarAlgebra_algebraMap_apply]

/-- `Coleman.leftMulMatrix p O` agrees with Mathlib's `Algebra.leftMulMatrix` for `basis p O` under
`scalarAlgebra p O`. -/
theorem leftMulMatrix_eq_algebra_leftMulMatrix (f : O⟦X⟧) :
    leftMulMatrix p O f =
      @Algebra.leftMulMatrix O⟦X⟧ O⟦X⟧ _ _ (scalarAlgebra p O) (Fin p) _ _ (basis p O) f := by
  refine Matrix.ext fun i j ↦ ?_
  rw [leftMulMatrix_eq_overFrobenius, Algebra.leftMulMatrix_eq_repr_mul,
    @Algebra.leftMulMatrix_eq_repr_mul O⟦X⟧ O⟦X⟧ _ _ (scalarAlgebra p O) (Fin p) _ _ (basis p O),
    basis_repr_apply, basis_apply, overFrobeniusBasis_repr_apply, map_mul,
    (overFrobeniusRingEquiv p O).apply_symm_apply, overFrobeniusBasis_apply]

/-- Left multiplication by `Φ(a)` is represented by the scalar diagonal matrix `a • 1`. -/
@[simp]
theorem leftMulMatrix_frobeniusHom (a : O⟦X⟧) :
    leftMulMatrix p O (frobeniusHom p O a) = Matrix.diagonal fun _ ↦ a := by
  rw [leftMulMatrix_eq_overFrobenius]
  have halg : (overFrobeniusRingEquiv p O).symm (frobeniusHom p O a) =
      algebraMap O⟦X⟧ (OverFrobenius p O) a :=
    (overFrobeniusRingEquiv p O).injective (by simp [overFrobeniusRingEquiv_algebraMap])
  rw [halg, AlgHom.commutes]
  ext i j
  simp [Matrix.algebraMap_eq_diagonal, Pi.algebraMap_def]

/-- Explicit formula for the `(i, j)` entry of `leftMulMatrix p O f`. -/
theorem leftMulMatrix_apply (f : O⟦X⟧) (i j : Fin p) :
    leftMulMatrix p O f i j =
      if h : (j : ℕ) ≤ i then coord p O ⟨(i : ℕ) - j, by omega⟩ f
      else coord p O ⟨p + (i : ℕ) - j, by omega⟩ f * (1 + X) := by
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hcol : f * (1 + X) ^ (j : ℕ) =
      ∑ r : Fin p, frobeniusHom p O (if h : (j : ℕ) ≤ r then coord p O ⟨(r : ℕ) - j, by omega⟩ f
        else coord p O ⟨p + (r : ℕ) - j, by omega⟩ f * (1 + X)) * (1 + X) ^ (r : ℕ) := by
    conv_lhs => rw [← sum_frobeniusHom_coord (p := p) f, Finset.sum_mul]
    rw [← Equiv.sum_comp (Equiv.subRight j)]
    refine Finset.sum_congr rfl fun r _ ↦ ?_
    simp only [Equiv.subRight_apply]
    split_ifs with h
    · have hsub : r - j = ⟨(r : ℕ) - j, by omega⟩ := Fin.ext <| by
        rw [Fin.sub_def]; dsimp only
        have h1 : p - (j : ℕ) + (r : ℕ) = p + ((r : ℕ) - (j : ℕ)) := by omega
        rw [h1, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
      rw [hsub, mul_assoc, ← pow_add]; dsimp only; rw [Nat.sub_add_cancel h]
    · have hsub : r - j = ⟨p + (r : ℕ) - j, by omega⟩ := Fin.ext <| by
        rw [Fin.sub_def]; dsimp only
        have h1 : p - (j : ℕ) + (r : ℕ) = p + (r : ℕ) - (j : ℕ) := by omega
        rw [h1, Nat.mod_eq_of_lt (by omega)]
      rw [hsub, map_mul, frobeniusHom_one_add_X, mul_assoc, mul_assoc, ← pow_add, ← pow_add]
      congr 2; dsimp only; omega
  rw [leftMulMatrix_eq_overFrobenius, Algebra.leftMulMatrix_eq_repr_mul,
    overFrobeniusBasis_repr_apply, map_mul, (overFrobeniusRingEquiv p O).apply_symm_apply,
    overFrobeniusBasis_apply]
  exact coord_unique hcol.symm i

/-- Under `scalarAlgebra p O`, `O⟦X⟧` is a free `O⟦X⟧`-module. -/
theorem module_free_scalarAlgebra :
    @Module.Free O⟦X⟧ O⟦X⟧ _ _ (scalarAlgebra p O).toModule :=
  (@Module.Free.iff_of_equiv O⟦X⟧ O⟦X⟧ (OverFrobenius p O) O⟦X⟧ _ _ _ _ _
    (scalarAlgebra p O).toModule (RingHom.id O⟦X⟧) (RingHom.id O⟦X⟧) _ _
    overFrobeniusToScalarLinearEquiv).mp (Module.Free.of_basis (overFrobeniusBasis p O))

/-- Under `scalarAlgebra p O`, `O⟦X⟧` is a finite `O⟦X⟧`-module. -/
theorem module_finite_scalarAlgebra :
    @Module.Finite O⟦X⟧ O⟦X⟧ _ _ (scalarAlgebra p O).toModule :=
  @Module.Finite.equiv O⟦X⟧ (OverFrobenius p O) O⟦X⟧ _ _ _ _ (scalarAlgebra p O).toModule
    (Module.Finite.of_basis (overFrobeniusBasis p O)) overFrobeniusToScalarLinearEquiv

/-- Under `scalarAlgebra p O`, `O⟦X⟧` has rank `p` over `O⟦X⟧` (for nontrivial `O`). -/
theorem finrank_scalarAlgebra [Nontrivial O] :
    @Module.finrank O⟦X⟧ O⟦X⟧ _ _ (scalarAlgebra p O).toModule = p := by
  have heq := @LinearEquiv.finrank_eq O⟦X⟧ (OverFrobenius p O) O⟦X⟧ _ _ _ _
    (scalarAlgebra p O).toModule overFrobeniusToScalarLinearEquiv
  rw [← heq, Module.finrank_eq_card_basis (overFrobeniusBasis p O), Fintype.card_fin]

/-- Expanding `f * (1 + X) ^ j` in the Coleman basis recovers the `j`-th column of
`leftMulMatrix p O f`. -/
theorem mul_one_add_X_pow_eq_sum_leftMulMatrix (f : O⟦X⟧) (j : Fin p) :
    f * (1 + X) ^ (j : ℕ) =
      ∑ i : Fin p, frobeniusHom p O (leftMulMatrix p O f i j) * (1 + X) ^ (i : ℕ) := by
  have hcol (i : Fin p) : leftMulMatrix p O f i j = coord p O i (f * (1 + X) ^ (j : ℕ)) := by
    rw [leftMulMatrix_eq_overFrobenius, Algebra.leftMulMatrix_eq_repr_mul,
      overFrobeniusBasis_repr_apply, map_mul, (overFrobeniusRingEquiv p O).apply_symm_apply,
      overFrobeniusBasis_apply]
  simpa only [hcol] using (sum_frobeniusHom_coord (p := p) (f * (1 + X) ^ (j : ℕ))).symm

/-- **Determinant formula for Coleman's norm.** `norm p O f` is the determinant of the explicit
left-multiplication matrix `leftMulMatrix p O f`. -/
theorem norm_eq_det_leftMulMatrix (f : O⟦X⟧) :
    norm p O f = Matrix.det (leftMulMatrix p O f) := by
  rw [norm_eq_overFrobenius_norm, Algebra.norm_eq_matrix_det (overFrobeniusBasis p O),
    leftMulMatrix_eq_overFrobenius]

/-- **Matrix-trace formula for Coleman's trace.** `trace p O f` is the trace of
`leftMulMatrix p O f`. -/
theorem trace_eq_trace_leftMulMatrix (f : O⟦X⟧) :
    trace p O f = Matrix.trace (leftMulMatrix p O f) := by
  rw [trace_eq_overFrobenius_trace, Algebra.trace_eq_matrix_trace (overFrobeniusBasis p O),
    leftMulMatrix_eq_overFrobenius]

/-- **Trace formula in the Coleman basis.** `trace p O f` equals `p` times the zeroth Coleman
coordinate of `f`. -/
theorem trace_eq_p_mul_coord_zero (f : O⟦X⟧) :
    trace p O f = (p : O⟦X⟧) * coord p O ⟨0, (Fact.out : p.Prime).pos⟩ f := by
  rw [trace_eq_trace_leftMulMatrix, Matrix.trace]
  have hdiag (i : Fin p) : leftMulMatrix p O f i i = coord p O ⟨0, (Fact.out : p.Prime).pos⟩ f := by
    simp only [leftMulMatrix_apply, dite_eq_left le_rfl]
    congr 1; ext; simp
  simp [Matrix.diag, hdiag]

/-- Coleman's trace of `1` is `p`. -/
@[simp]
theorem trace_one : trace p O 1 = (p : O⟦X⟧) := by
  rw [trace_eq_p_mul_coord_zero, coord_one]; simp

/-- Coleman's trace on `Φ(a)` is `p * a`. -/
@[simp]
theorem trace_frobeniusHom (a : O⟦X⟧) : trace p O (frobeniusHom p O a) = (p : O⟦X⟧) * a := by
  simpa [mul_comm] using trace_frobeniusHom_mul (p := p) a 1

/-- Coleman's trace on a constant series `C c` is `p * C c`. -/
@[simp]
theorem trace_C (c : O) : trace p O (C c) = (p : O⟦X⟧) * C c := by
  conv_lhs => rw [← frobeniusHom_C (p := p) c]
  exact trace_frobeniusHom (C c)

/-- Coleman's trace on `(1 + X) ^ n` is `p * (1 + X) ^ (n / p)` when `p ∣ n`, and `0` otherwise. -/
@[simp]
theorem trace_one_add_X_pow (n : ℕ) :
    trace p O ((1 + X : O⟦X⟧) ^ n) =
      if p ∣ n then (p : O⟦X⟧) * (1 + X) ^ (n / p) else 0 := by
  rw [trace_eq_p_mul_coord_zero, coord_one_add_X_pow]
  have hiff : (0 : ℕ) = n % p ↔ p ∣ n := by rw [eq_comm, Nat.dvd_iff_mod_eq_zero]
  simp only [hiff]; split_ifs <;> simp

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
  rw [norm_eq_overFrobenius_norm]
  have halg : (overFrobeniusRingEquiv p O).symm (frobeniusHom p O a) =
      algebraMap O⟦X⟧ (OverFrobenius p O) a :=
    (overFrobeniusRingEquiv p O).injective (by simp [overFrobeniusRingEquiv_algebraMap])
  rw [halg, Algebra.norm_algebraMap_of_basis (overFrobeniusBasis p O), Fintype.card_fin]

/-- Coleman's norm of `0` is `0`. -/
@[simp]
theorem norm_zero : norm p O 0 = 0 := by
  simpa [zero_pow (Fact.out : p.Prime).ne_zero] using norm_frobeniusHom (p := p) (0 : O⟦X⟧)

/-- Coleman's norm of a constant series `C c` is `C (c ^ p)`. -/
@[simp]
theorem norm_C (c : O) : norm p O (C c) = C (c ^ p) := by
  conv_lhs => rw [← frobeniusHom_C (p := p) c]
  rw [norm_frobeniusHom, map_pow]

/-- **First-order expansion of Coleman's norm near `1`.** For any `a, f ∈ O⟦X⟧`, there exists
`r ∈ O⟦X⟧` such that `N(1 + Φ(a) * f) = 1 + τ(f) * a + r * a ^ 2`. -/
theorem norm_one_add_frobeniusHom_mul (a f : O⟦X⟧) :
    ∃ r : O⟦X⟧, norm p O (1 + frobeniusHom p O a * f) = 1 + trace p O f * a + r * a ^ 2 := by
  have : Module.Free O⟦X⟧ (OverFrobenius p O) := Module.Free.of_basis (overFrobeniusBasis p O)
  have : Module.Finite O⟦X⟧ (OverFrobenius p O) := Module.Finite.of_basis (overFrobeniusBasis p O)
  obtain ⟨r, hr⟩ := Algebra.norm_one_add_smul a ((overFrobeniusRingEquiv p O).symm f)
  refine ⟨r, ?_⟩
  rw [norm_eq_overFrobenius_norm, trace_eq_overFrobenius_trace]
  have harg : (overFrobeniusRingEquiv p O).symm (1 + frobeniusHom p O a * f) =
      1 + a • (overFrobeniusRingEquiv p O).symm f :=
    (overFrobeniusRingEquiv p O).injective (by simp [overFrobeniusRingEquiv_smul])
  rw [harg, hr]

/-- **Norm of linear elements `Φ(g) - (1 + X)`.** For every `g ∈ O⟦X⟧`,
`N(Φ(g) - (1 + X)) = g ^ p - (1 + X)`. -/
theorem norm_frobeniusHom_sub_one_add_X (g : O⟦X⟧) :
    norm p O (frobeniusHom p O g - (1 + X)) = g ^ p - (1 + X) := by
  nontriviality O
  set P : Polynomial O⟦X⟧ := Polynomial.X ^ p - Polynomial.C (1 + X : O⟦X⟧)
  have hP : P.Monic := Polynomial.monic_X_pow_sub_C (1 + X) (Fact.out : p.Prime).ne_zero
  have harg :
      overFrobeniusAdjoinRootEquiv (p := p) (O := O) (AdjoinRoot.of P g - AdjoinRoot.root P) =
        (overFrobeniusRingEquiv p O).symm (frobeniusHom p O g - (1 + X)) := by
    apply (overFrobeniusRingEquiv p O).injective
    rw [map_sub, (overFrobeniusRingEquiv p O).apply_symm_apply, map_sub,
      ← AdjoinRoot.algebraMap_eq, AlgEquiv.commutes, overFrobeniusRingEquiv_algebraMap]
    simp [overFrobeniusAdjoinRootEquiv, P]
  rw [norm_eq_overFrobenius_norm, ← harg,
    Algebra.norm_eq_of_algEquiv (overFrobeniusAdjoinRootEquiv (p := p) (O := O)),
    AdjoinRoot.norm_algebraMap_sub_root hP g]
  simp [P]

/-- Sign-clearing helper: if `N(-f) = -f`, then `N(f) = (-1) ^ (p - 1) * f`. -/
private theorem norm_eq_neg_one_pow_mul_of_norm_neg {f : O⟦X⟧} (hf : norm p O (-f) = -f) :
    norm p O f = (-1 : O⟦X⟧) ^ (p - 1) * f := by
  have hneg : norm p O (-f) = (-1 : O⟦X⟧) ^ p * norm p O f := by
    have hcf : -f = C (-1 : O) * f := by simp
    rw [hcf, map_mul, norm_C, map_pow, map_neg, map_one]
  rw [hneg] at hf
  have hmul := congrArg (fun z : O⟦X⟧ ↦ (-1 : O⟦X⟧) ^ p * z) hf
  simp only [← mul_assoc, ← mul_pow, neg_one_mul, neg_neg, one_pow, one_mul] at hmul
  rw [hmul, neg_eq_neg_one_mul f, ← mul_assoc]
  congr 1
  conv_lhs => rw [(Nat.sub_add_cancel (Fact.out : p.Prime).pos).symm, pow_succ]
  ring

/-- **Norm of `1 + X`.** `N(1 + X) = (-1) ^ (p - 1) * (1 + X)`, which equals `1 + X` for odd `p`
and `-(1 + X)` for `p = 2`. -/
@[simp]
theorem norm_one_add_X : norm p O (1 + X) = (-1 : O⟦X⟧) ^ (p - 1) * (1 + X) := by
  refine norm_eq_neg_one_pow_mul_of_norm_neg ?_
  have h0 := norm_frobeniusHom_sub_one_add_X (p := p) (0 : O⟦X⟧)
  rwa [map_zero, zero_sub, zero_pow (Fact.out : p.Prime).ne_zero, zero_sub] at h0

/-- **Norm of `X`.** `N(X) = (-1) ^ (p - 1) * X`, which equals `X` for odd `p` and `-X` for
`p = 2`. -/
@[simp]
theorem norm_X : norm p O X = (-1 : O⟦X⟧) ^ (p - 1) * X := by
  refine norm_eq_neg_one_pow_mul_of_norm_neg ?_
  have h1 := norm_frobeniusHom_sub_one_add_X (p := p) (1 : O⟦X⟧)
  rwa [map_one, one_pow, sub_add_cancel_left] at h1

/-- Functoriality of Coleman's norm along any coefficient ring homomorphism between `(p)`-adically
complete rings. -/
theorem map_norm {O' : Type*} [CommRing O'] [IsAdicComplete (Ideal.span {(p : O')}) O']
    (φ : O →+* O') (f : O⟦X⟧) :
    PowerSeries.map φ (norm p O f) = norm p O' (PowerSeries.map φ f) := by
  rw [norm_eq_det_leftMulMatrix, norm_eq_det_leftMulMatrix, RingHom.map_det]
  congr 1
  refine Matrix.ext fun i j ↦ ?_
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, leftMulMatrix_apply]
  split_ifs <;> simp [map_coord]

/-- Functoriality of Coleman's trace along any coefficient ring homomorphism between `(p)`-adically
complete rings. -/
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
  refine ⟨by simp, by simp, ?_⟩
  rw [norm_C]; norm_num

end Examples

end TauCeti.Coleman
