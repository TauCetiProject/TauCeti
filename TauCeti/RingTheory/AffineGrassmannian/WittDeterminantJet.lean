/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.RingTheory.Localization.Away.AdjoinRoot
public import TauCeti.RingTheory.Perfect.Colimit
public import TauCeti.RingTheory.WittVector.Truncated.Basic
import Mathlib.RingTheory.WittVector.Domain
import TauCeti.RingTheory.WittVector.Units

/-!
# The finite Witt determinant locus

For `N < h`, the length-`h` Witt matrices whose determinant has its first `N` coordinates
zero and its `N`-th coordinate invertible form an affine scheme of finite presentation over
`𝔽_p`. Its coordinate ring is obtained from the polynomial ring in the matrix-entry
coordinates by quotienting by the lower determinant coordinates and inverting the leading one.
The colimit perfection of this ring gives the corresponding model on perfect test algebras.

Over a perfect ring of characteristic `p`, these equations say exactly that the determinant
of any full Witt lift is `p ^ N` times a unit. This gives the matrix parameter space for the
finite-jet presentation of bounded lattices in the Witt affine Grassmannian.

## References

* X. Zhu, *Affine Grassmannians and the geometric Satake in mixed characteristic*,
  Ann. of Math. 185 (2017), §1.2.4, pp. 418–421.
-/

public section

noncomputable section

open MvPolynomial

namespace TauCeti.WittDeterminantJet

variable {p N h : ℕ} [Fact p.Prime] {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {R S : Type*} [CommRing R] [CommRing S]

/-- A matrix belongs to the determinant locus at depth `h` and order `N` if its lower
determinant coordinates vanish and its `N`-th determinant coordinate is a unit. -/
def IsPoint (hN : N < h) (A : Matrix ι ι (TruncatedWittVector p h R)) : Prop :=
  (∀ i : Fin h, i.val < N → A.det.coeff i = 0) ∧ IsUnit (A.det.coeff ⟨N, hN⟩)

/-- The defining equations of the finite determinant locus. -/
theorem isPoint_iff_det_coeff (hN : N < h) (A : Matrix ι ι (TruncatedWittVector p h R)) :
    IsPoint hN A ↔
      (∀ i : Fin h, i.val < N → A.det.coeff i = 0) ∧ IsUnit (A.det.coeff ⟨N, hN⟩) :=
  Iff.rfl

/-- Applying a coefficient homomorphism preserves the determinant equations and the leading
unit. -/
theorem IsPoint.map {hN : N < h} {A : Matrix ι ι (TruncatedWittVector p h R)}
    (hA : IsPoint hN A) (f : R →+* S) :
    IsPoint hN (A.map (TruncatedWittVector.map h f)) := by
  constructor
  · intro i hi
    simp only [← RingHom.mapMatrix_apply, ← RingHom.map_det,
      TruncatedWittVector.map_coeff, hA.1 i hi, map_zero]
  · rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, TruncatedWittVector.map_coeff]
    exact hA.2.map f

/-- Reducing the jet preserves and reflects membership whenever the new depth still exceeds
the determinant order. -/
theorem isPoint_truncate_iff_of_le {m : ℕ} (hN : N < h) (hh : h ≤ m)
    (A : Matrix ι ι (TruncatedWittVector p m R)) :
    IsPoint hN (A.map (TruncatedWittVector.truncate hh)) ↔ IsPoint (hN.trans_le hh) A := by
  simp only [IsPoint, ← RingHom.mapMatrix_apply, ← RingHom.map_det,
    TruncatedWittVector.coeff_truncate]
  refine and_congr_left' ⟨fun ha i hi ↦ ?_, fun ha i hi ↦ ha _ hi⟩
  exact ha ⟨i.val, hi.trans hN⟩ hi

/-- Right multiplication by a matrix with unit determinant preserves the determinant locus in
characteristic `p`, including over nonperfect test rings. -/
theorem IsPoint.mul_right [CharP R p] {hN : N < h}
    {A B : Matrix ι ι (TruncatedWittVector p h R)} (hA : IsPoint hN A) (hB : IsUnit B.det) :
    IsPoint hN (A * B) := by
  let : NeZero h := ⟨(Nat.zero_lt_of_lt hN).ne'⟩
  let x := A.det.out
  let y := B.det.out
  have htrunc : (A * B).det = WittVector.truncate h (x * y) := by
    rw [Matrix.det_mul, map_mul]
    exact congrArg₂ (· * ·) (TruncatedWittVector.truncateFun_out _).symm
      (TruncatedWittVector.truncateFun_out _).symm
  have hx : x = WittVector.verschiebung^[N] (x.shift N) :=
    WittVector.eq_iterate_verschiebung fun i hi ↦
      (TruncatedWittVector.coeff_out A.det ⟨i, hi.trans hN⟩).trans (hA.1 _ hi)
  have hprod : x * y =
      WittVector.verschiebung^[N] (x.shift N * WittVector.frobenius^[N] y) :=
    (congrArg (· * y) hx).trans (WittVector.iterate_verschiebung_mul_left _ _ _)
  have hy : IsUnit (y.coeff 0) := by
    rw [← Fin.val_zero (n := h), TruncatedWittVector.coeff_out,
      ← TruncatedWittVector.constantCoeff_apply]
    exact hB.map TruncatedWittVector.constantCoeff
  have hlead : (x * y).coeff N = x.coeff N * y.coeff 0 ^ p ^ N := by
    rw [hprod]
    simpa only [zero_add, WittVector.mul_coeff_zero, WittVector.shift_coeff, add_zero,
      WittVector.iterate_frobenius_coeff] using
      WittVector.iterate_verschiebung_coeff (x.shift N * WittVector.frobenius^[N] y) N 0
  rw [isPoint_iff_det_coeff, htrunc]
  constructor
  · intro i hi
    rw [WittVector.coeff_truncate, hprod]
    exact WittVector.iterate_verschiebung_coeff_eq_zero _ hi
  · rw [WittVector.coeff_truncate, hlead]
    have hxUnit : IsUnit (x.coeff N) :=
      (TruncatedWittVector.coeff_out A.det ⟨N, hN⟩).symm ▸ hA.2
    exact hxUnit.mul (hy.pow _)

section CoordinateRing

variable (p h ι)

/-- The length-`h` Witt matrix with an independent coordinate for each entry and Witt index. -/
def universalMatrix :
    Matrix ι ι (TruncatedWittVector p h (MvPolynomial (ι × ι × Fin h) (ZMod p))) :=
  Matrix.of fun i j ↦ TruncatedWittVector.mk p fun k ↦ X (i, j, k)

/-- The polynomial giving one Witt coordinate of the determinant of a length-`h` matrix. -/
def detCoeff (k : Fin h) : MvPolynomial (ι × ι × Fin h) (ZMod p) :=
  (universalMatrix p h ι).det.coeff k

variable {p ι h}

/-- Evaluation of a determinant-coordinate polynomial computes the corresponding Witt
coordinate of the evaluated matrix's determinant. -/
theorem aeval_detCoeff [Algebra (ZMod p) R] (A : Matrix ι ι (TruncatedWittVector p h R))
    (k : Fin h) :
    aeval (fun v : ι × ι × Fin h ↦ (A v.1 v.2.1).coeff v.2.2) (detCoeff p h ι k) =
      A.det.coeff k := by
  let f : MvPolynomial (ι × ι × Fin h) (ZMod p) →ₐ[ZMod p] R :=
    aeval fun v ↦ (A v.1 v.2.1).coeff v.2.2
  have hm : (universalMatrix p h ι).map (TruncatedWittVector.map h f.toRingHom) = A := by
    ext i j k
    simp [universalMatrix, f]
  calc
    f (detCoeff p h ι k) =
        ((TruncatedWittVector.map h f.toRingHom) (universalMatrix p h ι).det).coeff k :=
      (TruncatedWittVector.map_coeff h f.toRingHom (universalMatrix p h ι).det k).symm
    _ = A.det.coeff k := by rw [RingHom.map_det, RingHom.mapMatrix_apply, hm]

variable (p ι)

/-- The ideal generated by the determinant coordinates strictly below `N`. -/
def lowerIdeal (hN : N < h) : Ideal (MvPolynomial (ι × ι × Fin h) (ZMod p)) :=
  Ideal.span (Set.range fun k : Fin N ↦ detCoeff p h ι (Fin.castLE hN.le k))

/-- The coordinate algebra of the determinant locus. It imposes the `N` vanishing coefficients
and inverts the `N`-th determinant coefficient. -/
abbrev CoordinateRing (hN : N < h) :=
  Localization.Away (Ideal.Quotient.mk (lowerIdeal p ι hN) (detCoeff p h ι ⟨N, hN⟩))

instance (hN : N < h) : Algebra.FinitePresentation (ZMod p) (CoordinateRing p ι hN) := by
  let : Algebra.FinitePresentation (ZMod p)
      (MvPolynomial (ι × ι × Fin h) (ZMod p) ⧸ lowerIdeal p ι hN) :=
    Algebra.FinitePresentation.quotient (Submodule.fg_span (Set.finite_range _))
  infer_instance

variable (hN : N < h)

/-- The quotient and localization map from the ring of matrix-entry coordinates. -/
def coordinateMap :
    MvPolynomial (ι × ι × Fin h) (ZMod p) →ₐ[ZMod p] CoordinateRing p ι hN :=
  (Algebra.algHom (ZMod p) _ _).comp (Ideal.Quotient.mkₐ (ZMod p) (lowerIdeal p ι hN))

@[simp]
theorem coordinateMap_detCoeff_eq_zero (k : Fin h) (hk : k.val < N) :
    coordinateMap p ι hN (detCoeff p h ι k) = 0 := by
  have hz : detCoeff p h ι k ∈ lowerIdeal p ι hN :=
    Ideal.subset_span ⟨⟨k, hk⟩, rfl⟩
  simp [coordinateMap, Ideal.Quotient.eq_zero_iff_mem.mpr hz]

@[simp]
theorem isUnit_coordinateMap_detCoeff :
    IsUnit (coordinateMap p ι hN (detCoeff p h ι ⟨N, hN⟩)) :=
  IsLocalization.Away.algebraMap_isUnit
    (Ideal.Quotient.mk (lowerIdeal p ι hN) (detCoeff p h ι ⟨N, hN⟩))

variable {p ι}

/-- The Witt matrix over a test ring determined by evaluation on the coordinate algebra. -/
def matrixOfHom [Algebra (ZMod p) R] (f : CoordinateRing p ι hN →ₐ[ZMod p] R) :
    Matrix ι ι (TruncatedWittVector p h R) :=
  (universalMatrix p h ι).map
    (TruncatedWittVector.map h (f.comp (coordinateMap p ι hN)).toRingHom)

@[simp]
theorem coeff_matrixOfHom [Algebra (ZMod p) R] (f : CoordinateRing p ι hN →ₐ[ZMod p] R)
    (i j : ι) (k : Fin h) :
    (matrixOfHom hN f i j).coeff k = f (coordinateMap p ι hN (X (i, j, k))) := by
  simp [matrixOfHom, universalMatrix]

theorem isPoint_matrixOfHom [Algebra (ZMod p) R] (f : CoordinateRing p ι hN →ₐ[ZMod p] R) :
    IsPoint hN (matrixOfHom hN f) := by
  have heval (k : Fin h) : (matrixOfHom hN f).det.coeff k =
      f (coordinateMap p ι hN (detCoeff p h ι k)) := by
    simp [matrixOfHom, ← RingHom.mapMatrix_apply, ← RingHom.map_det, detCoeff]
  exact ⟨fun k hk ↦ by rw [heval, coordinateMap_detCoeff_eq_zero _ _ _ _ hk, map_zero],
    by rw [heval]; exact (isUnit_coordinateMap_detCoeff p ι hN).map f⟩

private def matrixEval [Algebra (ZMod p) R] (A : Matrix ι ι (TruncatedWittVector p h R)) :
    MvPolynomial (ι × ι × Fin h) (ZMod p) →ₐ[ZMod p] R :=
  aeval fun v ↦ (A v.1 v.2.1).coeff v.2.2

/-- Evaluate polynomials at a matrix on the determinant locus, then descend to the quotient by
the vanishing coordinates. -/
private def evalQuotient [Algebra (ZMod p) R]
    {A : Matrix ι ι (TruncatedWittVector p h R)} (hA : IsPoint hN A) :
    (MvPolynomial (ι × ι × Fin h) (ZMod p) ⧸ lowerIdeal p ι hN) →ₐ[ZMod p] R :=
  Ideal.Quotient.liftₐ _ (matrixEval A) (by
    intro x hx
    refine (Ideal.span_le.mpr ?_ : lowerIdeal p ι hN ≤ RingHom.ker _) hx
    rintro _ ⟨k, rfl⟩
    exact RingHom.mem_ker.mpr ((aeval_detCoeff A _).trans (hA.1 _ k.is_lt)))

private theorem evalQuotient_mk [Algebra (ZMod p) R]
    {A : Matrix ι ι (TruncatedWittVector p h R)} (hA : IsPoint hN A)
    (x : MvPolynomial (ι × ι × Fin h) (ZMod p)) :
    evalQuotient hN hA (Ideal.Quotient.mk (lowerIdeal p ι hN) x) =
      aeval (fun v : ι × ι × Fin h ↦ (A v.1 v.2.1).coeff v.2.2) x := by
  have hc : (evalQuotient hN hA).comp (Ideal.Quotient.mkₐ (ZMod p) (lowerIdeal p ι hN)) =
      matrixEval A :=
    Ideal.Quotient.liftₐ_comp (lowerIdeal p ι hN) (matrixEval A) _
  exact AlgHom.congr_fun hc x

/-- Evaluation at a matrix on the locus extends uniquely to its coordinate algebra. -/
def homOfMatrix [Algebra (ZMod p) R]
    {A : Matrix ι ι (TruncatedWittVector p h R)} (hA : IsPoint hN A) :
    CoordinateRing p ι hN →ₐ[ZMod p] R :=
  IsLocalization.Away.liftAlgHom
    (Ideal.Quotient.mk (lowerIdeal p ι hN) (detCoeff p h ι ⟨N, hN⟩))
    (f := evalQuotient hN hA)
    (by
      rw [evalQuotient_mk, aeval_detCoeff]
      exact hA.2)

@[simp]
theorem homOfMatrix_coordinateMap [Algebra (ZMod p) R]
    {A : Matrix ι ι (TruncatedWittVector p h R)} (hA : IsPoint hN A)
    (x : MvPolynomial (ι × ι × Fin h) (ZMod p)) :
    homOfMatrix hN hA (coordinateMap p ι hN x) =
      aeval (fun v : ι × ι × Fin h ↦ (A v.1 v.2.1).coeff v.2.2) x := by
  simp only [homOfMatrix, coordinateMap, AlgHom.comp_apply, Algebra.algHom,
    IsScalarTower.coe_toAlgHom', Ideal.Quotient.mkₐ_eq_mk,
    IsLocalization.Away.liftAlgHom_apply, IsLocalization.Away.lift_eq]
  exact evalQuotient_mk hN hA x

@[simp]
theorem matrixOfHom_homOfMatrix [Algebra (ZMod p) R]
    {A : Matrix ι ι (TruncatedWittVector p h R)} (hA : IsPoint hN A) :
    matrixOfHom hN (homOfMatrix hN hA) = A := by
  ext i j k
  simp

/-- The values on the Witt coordinates of the matrix determine a map from the coordinate ring. -/
theorem hom_ext [Algebra (ZMod p) R] {f g : CoordinateRing p ι hN →ₐ[ZMod p] R}
    (heq : matrixOfHom hN f = matrixOfHom hN g) : f = g := by
  apply IsLocalization.algHom_ext
    (Submonoid.powers (Ideal.Quotient.mk (lowerIdeal p ι hN) (detCoeff p h ι ⟨N, hN⟩)))
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  rintro ⟨i, j, k⟩
  simpa [coordinateMap, Algebra.algHom] using congrArg (fun A ↦ (A i j).coeff k) heq

/-- The finite-jet determinant locus is corepresented by its coordinate algebra. -/
def homEquiv [Algebra (ZMod p) R] :
    (CoordinateRing p ι hN →ₐ[ZMod p] R) ≃
      {A : Matrix ι ι (TruncatedWittVector p h R) // IsPoint hN A} where
  toFun f := ⟨matrixOfHom hN f, isPoint_matrixOfHom hN f⟩
  invFun A := homOfMatrix hN A.property
  left_inv f := hom_ext hN (matrixOfHom_homOfMatrix hN (isPoint_matrixOfHom hN f))
  right_inv A := Subtype.ext (matrixOfHom_homOfMatrix hN A.property)

@[simp]
theorem homEquiv_apply_val [Algebra (ZMod p) R] (f : CoordinateRing p ι hN →ₐ[ZMod p] R) :
    (homEquiv hN f).val = matrixOfHom hN f :=
  (rfl)

/-- The corepresenting equivalence sends postcomposition to coefficient change of matrices. -/
theorem homEquiv_natural [Algebra (ZMod p) R] [Algebra (ZMod p) S]
    (g : R →ₐ[ZMod p] S) (f : CoordinateRing p ι hN →ₐ[ZMod p] R) :
    (homEquiv hN (g.comp f)).val =
      (homEquiv hN f).val.map (TruncatedWittVector.map h g.toRingHom) := by
  ext i j k
  simp

end CoordinateRing

section Perfection

variable (p ι) (hN : N < h)

/-- The prime `p` vanishes in the finite determinant model. -/
theorem natCast_eq_zero : (p : CoordinateRing p ι hN) = 0 := by
  rw [← map_natCast (algebraMap (ZMod p) (CoordinateRing p ι hN)),
    CharP.cast_eq_zero, map_zero]

/-- The coordinate ring of the perfected finite-jet determinant locus. -/
abbrev PerfectCoordinateRing :=
  ColimitPerfection (CoordinateRing p ι hN) p (natCast_eq_zero p ι hN)

instance : Algebra (ZMod p) (PerfectCoordinateRing p ι hN) :=
  ((ColimitPerfection.of _ p (natCast_eq_zero p ι hN)).comp
    (algebraMap (ZMod p) (CoordinateRing p ι hN))).toAlgebra

/-- The map from the finite model to its coordinate-ring perfection. -/
def toPerfect : CoordinateRing p ι hN →ₐ[ZMod p] PerfectCoordinateRing p ι hN where
  toRingHom := ColimitPerfection.of _ p (natCast_eq_zero p ι hN)
  commutes' _ := rfl

variable {p ι}

/-- The affine perfection of the finite model represents determinant jets on perfect test
algebras. -/
def perfectHomEquiv [Algebra (ZMod p) R] [PerfectRing R p] :
    (PerfectCoordinateRing p ι hN →ₐ[ZMod p] R) ≃
      {A : Matrix ι ι (TruncatedWittVector p h R) // IsPoint hN A} :=
  (Equiv.ofBijective (fun f ↦ f.comp (toPerfect p ι hN)) (by
    constructor
    · intro f g e
      apply AlgHom.toRingHom_injective
      exact ColimitPerfection.hom_ext (congrArg AlgHom.toRingHom e)
    · intro f
      let g := ColimitPerfection.lift (natCast_eq_zero p ι hN) f.toRingHom
      let gAlg : PerfectCoordinateRing p ι hN →ₐ[ZMod p] R :=
        { toRingHom := g
          commutes' := fun c ↦ RingHom.congr_fun
            (Subsingleton.elim (g.comp (algebraMap (ZMod p) _)) (algebraMap (ZMod p) R)) c }
      refine ⟨gAlg, AlgHom.ext fun x ↦ ?_⟩
      exact ColimitPerfection.lift_of f.toRingHom x)).trans (homEquiv hN)

@[simp]
theorem perfectHomEquiv_apply [Algebra (ZMod p) R] [PerfectRing R p]
    (f : PerfectCoordinateRing p ι hN →ₐ[ZMod p] R) :
    perfectHomEquiv hN f = homEquiv hN (f.comp (toPerfect p ι hN)) :=
  (rfl)

/-- The perfect model's point equivalence commutes with coefficient change. -/
theorem perfectHomEquiv_natural [Algebra (ZMod p) R] [PerfectRing R p]
    [Algebra (ZMod p) S] [PerfectRing S p] (g : R →ₐ[ZMod p] S)
    (f : PerfectCoordinateRing p ι hN →ₐ[ZMod p] R) :
    (perfectHomEquiv hN (g.comp f)).val =
      (perfectHomEquiv hN f).val.map (TruncatedWittVector.map h g.toRingHom) := by
  rw [perfectHomEquiv_apply, perfectHomEquiv_apply, AlgHom.comp_assoc]
  exact homEquiv_natural hN g (f.comp (toPerfect p ι hN))

end Perfection

section Perfect

variable [CharP R p] [PerfectRing R p]

/-- A length-`h` jet of a full Witt matrix is on the determinant locus precisely when the
determinant of the full matrix is `p ^ N` times a unit. -/
theorem isPoint_truncate_iff (hN : N < h) (A : Matrix ι ι (WittVector p R)) :
    IsPoint hN (A.map (WittVector.truncate h)) ↔
      ∃ u : (WittVector p R)ˣ, A.det = ↑u * (p : WittVector p R) ^ N := by
  simp only [IsPoint, ← RingHom.mapMatrix_apply, ← RingHom.map_det, WittVector.coeff_truncate]
  have coeff_mul_pow (u : WittVector p R) : (u * (p : WittVector p R) ^ N).coeff N =
      u.coeff 0 ^ p ^ N := by
    simpa using (WittVector.mul_pow_charP_coeff_succ u (m := 0) (n := N))
  constructor
  · rintro ⟨hlo, hunit⟩
    have hdvd : (p : WittVector p R) ^ N ∣ A.det := by
      rw [← Ideal.mem_span_singleton, WittVector.mem_span_p_pow_iff_le_coeff_eq_zero]
      exact fun j hj ↦ hlo ⟨j, hj.trans hN⟩ hj
    obtain ⟨u, hu⟩ := hdvd
    have hu₀ : IsUnit (u.coeff 0) := by
      rw [hu, mul_comm ((p : WittVector p R) ^ N) u, coeff_mul_pow] at hunit
      exact (isUnit_pow_iff (pow_ne_zero _ (Fact.out : p.Prime).ne_zero)).mp hunit
    exact ⟨(WittVector.isUnit_iff_isUnit_coeff_zero.mpr hu₀).unit,
      by simpa [mul_comm] using hu⟩
  · rintro ⟨u, hu⟩
    refine ⟨fun i hi ↦ by rw [hu, WittVector.mul_pow_charP_coeff_zero _ hi], ?_⟩
    rw [hu, coeff_mul_pow]
    exact ((WittVector.isUnit_iff_isUnit_coeff_zero.mp u.isUnit).pow _)

/-- Zero-padding each matrix entry gives a full lift of a determinant jet with determinant
`p ^ N` times a unit. -/
theorem exists_unit_det_out {hN : N < h} {A : Matrix ι ι (TruncatedWittVector p h R)}
    (hA : IsPoint hN A) :
    ∃ u : (WittVector p R)ˣ,
      (A.map TruncatedWittVector.out).det = ↑u * (p : WittVector p R) ^ N := by
  apply (isPoint_truncate_iff hN _).mp
  have heq : (A.map TruncatedWittVector.out).map (WittVector.truncate h) = A := by
    ext i j k
    simp
  rwa [heq]

/-- On a perfect base the determinant equations are equivalent to a unit times `p ^ N`
in the truncated Witt ring itself. -/
theorem isPoint_iff (hN : N < h) (A : Matrix ι ι (TruncatedWittVector p h R)) :
    IsPoint hN A ↔
      ∃ u : (TruncatedWittVector p h R)ˣ, A.det = ↑u * (p : TruncatedWittVector p h R) ^ N := by
  let trunc : WittVector p R →+* TruncatedWittVector p h R := WittVector.truncate h
  constructor
  · intro hA
    obtain ⟨u, hu⟩ := exists_unit_det_out hA
    have hm : trunc.mapMatrix (A.map TruncatedWittVector.out) = A := by
      ext i j k
      simp [trunc, RingHom.mapMatrix_apply]
    refine ⟨Units.map trunc u, ?_⟩
    simpa only [RingHom.map_det, hm, map_mul, map_pow, map_natCast, Units.coe_map,
      MonoidHom.coe_ofClass] using congrArg trunc hu
  · rintro ⟨u, hu⟩
    have hzero : 0 < h := Nat.zero_lt_of_lt hN
    let : NeZero h := ⟨hzero.ne'⟩
    let v := (u : TruncatedWittVector p h R).out
    have hv : IsUnit (v.coeff 0) := by
      rw [← Fin.val_zero (n := h), TruncatedWittVector.coeff_out,
        ← TruncatedWittVector.constantCoeff_apply]
      exact u.isUnit.map TruncatedWittVector.constantCoeff
    have hvtrunc : trunc v = u := TruncatedWittVector.truncateFun_out _
    have hdet : A.det = trunc (v * (p : WittVector p R) ^ N) := by
      rwa [map_mul, map_pow, hvtrunc, map_natCast]
    constructor
    · intro i hi
      rw [hdet]
      exact WittVector.mul_pow_charP_coeff_zero v hi
    · have hc : (v * (p : WittVector p R) ^ N).coeff N = v.coeff 0 ^ p ^ N := by
        simpa only [zero_add] using (WittVector.mul_pow_charP_coeff_succ v (m := 0) (n := N))
      rw [hdet]
      simpa only [trunc, WittVector.coeff_truncate, hc] using hv.pow (p ^ N)

end Perfect

end TauCeti.WittDeterminantJet
