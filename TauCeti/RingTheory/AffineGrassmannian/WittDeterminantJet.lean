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
theorem isPoint_map_truncate_iff {m : ℕ} (hN : N < h) (hh : h ≤ m)
    (A : Matrix ι ι (TruncatedWittVector p m R)) :
    IsPoint hN (A.map (TruncatedWittVector.truncate hh)) ↔ IsPoint (hN.trans_le hh) A := by
  simp only [IsPoint, ← RingHom.mapMatrix_apply, ← RingHom.map_det,
    TruncatedWittVector.coeff_truncate]
  refine and_congr_left' ⟨fun ha i hi ↦ ?_, fun ha i hi ↦ ha _ hi⟩
  exact ha ⟨i.val, hi.trans hN⟩ hi

/-- Right multiplication by a matrix with unit determinant preserves the determinant locus. -/
theorem IsPoint.mul_right {hN : N < h}
    {A B : Matrix ι ι (TruncatedWittVector p h R)} (hA : IsPoint hN A) (hB : IsUnit B.det) :
    IsPoint hN (A * B) := by
  obtain ⟨b, hb⟩ := hB.exists_right_inv
  rw [isPoint_iff_det_coeff, Matrix.det_mul]
  have hAu := A.det.mul_coeff_eq_zero_of_lt B.det hA.1
  refine ⟨hAu, isUnit_of_dvd_unit ?_ hA.2⟩
  -- Multiplying back by the inverse shows the new leading coefficient divides the original.
  have hdiv := (A.det * B.det).coeff_dvd_mul_coeff b hN hAu
  rwa [mul_assoc, hb, mul_one] at hdiv

section CoordinateRing

variable (p h ι)

/-- The length-`h` Witt matrix with an independent coordinate for each entry and Witt index. -/
def universalMatrix :
    Matrix ι ι (TruncatedWittVector p h (MvPolynomial (ι × ι × Fin h) (ZMod p))) :=
  Matrix.of fun i j ↦ TruncatedWittVector.mk p fun k ↦ X (i, j, k)

omit [Fintype ι] [DecidableEq ι] in
@[simp]
theorem coeff_universalMatrix (i j : ι) (k : Fin h) :
    (universalMatrix p h ι i j).coeff k = X (i, j, k) := by
  simp [universalMatrix]

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
    simp [f]
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
  simp [matrixOfHom]

theorem isPoint_matrixOfHom [Algebra (ZMod p) R] (f : CoordinateRing p ι hN →ₐ[ZMod p] R) :
    IsPoint hN (matrixOfHom hN f) := by
  have heval (k : Fin h) : (matrixOfHom hN f).det.coeff k =
      f (coordinateMap p ι hN (detCoeff p h ι k)) := by
    simp [matrixOfHom, ← RingHom.mapMatrix_apply, ← RingHom.map_det, detCoeff]
  exact ⟨fun k hk ↦ by rw [heval, coordinateMap_detCoeff_eq_zero _ _ _ _ hk, map_zero],
    by rw [heval]; exact (isUnit_coordinateMap_detCoeff p ι hN).map f⟩

private theorem aeval_eq_zero_of_mem_lowerIdeal [Algebra (ZMod p) R]
    {A : Matrix ι ι (TruncatedWittVector p h R)} (hA : IsPoint hN A)
    (x : MvPolynomial (ι × ι × Fin h) (ZMod p)) (hx : x ∈ lowerIdeal p ι hN) :
    aeval (fun v : ι × ι × Fin h ↦ (A v.1 v.2.1).coeff v.2.2) x = 0 := by
  refine (Ideal.span_le.mpr ?_ : lowerIdeal p ι hN ≤ RingHom.ker _) hx
  rintro _ ⟨k, rfl⟩
  exact RingHom.mem_ker.mpr ((aeval_detCoeff A _).trans (hA.1 _ k.is_lt))

/-- Evaluate polynomials at a matrix on the determinant locus, then descend to the quotient by
the vanishing coordinates. -/
private def evalQuotient [Algebra (ZMod p) R]
    {A : Matrix ι ι (TruncatedWittVector p h R)} (hA : IsPoint hN A) :
    (MvPolynomial (ι × ι × Fin h) (ZMod p) ⧸ lowerIdeal p ι hN) →ₐ[ZMod p] R :=
  Ideal.Quotient.liftₐ _ _ (aeval_eq_zero_of_mem_lowerIdeal hN hA)

/-- Evaluation at a matrix on the locus extends uniquely to its coordinate algebra. -/
def homOfMatrix [Algebra (ZMod p) R]
    {A : Matrix ι ι (TruncatedWittVector p h R)} (hA : IsPoint hN A) :
    CoordinateRing p ι hN →ₐ[ZMod p] R :=
  IsLocalization.Away.liftAlgHom
    (Ideal.Quotient.mk (lowerIdeal p ι hN) (detCoeff p h ι ⟨N, hN⟩))
    (f := evalQuotient hN hA)
    (by
      have heval := Ideal.Quotient.liftₐ_comp _ _ (aeval_eq_zero_of_mem_lowerIdeal hN hA)
      have hk := (AlgHom.congr_fun heval (detCoeff p h ι ⟨N, hN⟩)).trans (aeval_detCoeff A _)
      exact hk.symm ▸ hA.2)

@[simp]
theorem homOfMatrix_coordinateMap [Algebra (ZMod p) R]
    {A : Matrix ι ι (TruncatedWittVector p h R)} (hA : IsPoint hN A)
    (x : MvPolynomial (ι × ι × Fin h) (ZMod p)) :
    homOfMatrix hN hA (coordinateMap p ι hN x) =
      aeval (fun v : ι × ι × Fin h ↦ (A v.1 v.2.1).coeff v.2.2) x := by
  simp only [homOfMatrix, coordinateMap, AlgHom.comp_apply, Algebra.algHom,
    IsScalarTower.coe_toAlgHom']
  calc
    _ = evalQuotient hN hA (Ideal.Quotient.mkₐ (ZMod p) (lowerIdeal p ι hN) x) :=
      (IsLocalization.Away.liftAlgHom_apply _ _ _).trans (IsLocalization.Away.lift_eq _ _ _)
    _ = _ := AlgHom.congr_fun
      (Ideal.Quotient.liftₐ_comp _ _ (aeval_eq_zero_of_mem_lowerIdeal hN hA)) x

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

@[simp]
theorem homEquiv_symm_apply [Algebra (ZMod p) R]
    (A : {A : Matrix ι ι (TruncatedWittVector p h R) // IsPoint hN A}) :
    (homEquiv hN).symm A = homOfMatrix hN A.property :=
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

@[simp]
theorem toPerfect_apply (x : CoordinateRing p ι hN) :
    toPerfect p ι hN x = ColimitPerfection.of _ p (natCast_eq_zero p ι hN) x :=
  (rfl)

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

@[simp]
theorem perfectHomEquiv_symm_comp_toPerfect [Algebra (ZMod p) R] [PerfectRing R p]
    (A : {A : Matrix ι ι (TruncatedWittVector p h R) // IsPoint hN A}) :
    ((perfectHomEquiv hN).symm A).comp (toPerfect p ι hN) = homOfMatrix hN A.property := by
  apply (homEquiv hN).injective
  rw [← perfectHomEquiv_apply, Equiv.apply_symm_apply, ← homEquiv_symm_apply,
    Equiv.apply_symm_apply]

/-- The perfect model's point equivalence commutes with coefficient change. -/
theorem perfectHomEquiv_natural [Algebra (ZMod p) R] [PerfectRing R p]
    [Algebra (ZMod p) S] [PerfectRing S p] (g : R →ₐ[ZMod p] S)
    (f : PerfectCoordinateRing p ι hN →ₐ[ZMod p] R) :
    (perfectHomEquiv hN (g.comp f)).val =
      (perfectHomEquiv hN f).val.map (TruncatedWittVector.map h g.toRingHom) := by
  rw [perfectHomEquiv_apply, perfectHomEquiv_apply, AlgHom.comp_assoc]
  exact homEquiv_natural hN g (f.comp (toPerfect p ι hN))

end Perfection

section CharP

variable [CharP R p]

private theorem isPoint_of_det_eq_truncate_mul_pow (hN : N < h)
    {A : Matrix ι ι (TruncatedWittVector p h R)} {v : WittVector p R}
    (hdet : A.det = WittVector.truncate h (v * (p : WittVector p R) ^ N))
    (hv : IsUnit (v.coeff 0)) : IsPoint hN A := by
  have hlead : (v * (p : WittVector p R) ^ N).coeff N = v.coeff 0 ^ p ^ N := by
    simpa only [zero_add] using WittVector.mul_pow_charP_coeff_succ v (m := 0) (n := N)
  rw [isPoint_iff_det_coeff, hdet]
  simp only [WittVector.coeff_truncate, hlead,
    isUnit_pow_iff (pow_ne_zero _ (Fact.out : p.Prime).ne_zero)]
  exact ⟨fun _ hi ↦ WittVector.mul_pow_charP_coeff_zero v hi, hv⟩

/-- A full Witt matrix with determinant a unit times `p ^ N` gives a point at every depth
greater than `N`. -/
theorem IsPoint.map_truncate_of_det_eq_unit_mul_pow {hN : N < h}
    {A : Matrix ι ι (WittVector p R)} {u : (WittVector p R)ˣ}
    (hdet : A.det = ↑u * (p : WittVector p R) ^ N) :
    IsPoint hN (A.map (WittVector.truncate h)) := by
  apply isPoint_of_det_eq_truncate_mul_pow hN (v := ↑u) ?_
  · exact WittVector.isUnit_iff_isUnit_coeff_zero.mp u.isUnit
  · rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, hdet]

/-- A truncated Witt matrix with determinant a unit times `p ^ N` lies on the determinant
locus. -/
theorem IsPoint.of_det_eq_unit_mul_pow {hN : N < h}
    {A : Matrix ι ι (TruncatedWittVector p h R)} {u : (TruncatedWittVector p h R)ˣ}
    (hdet : A.det = ↑u * (p : TruncatedWittVector p h R) ^ N) :
    IsPoint hN A := by
  let : NeZero h := ⟨(Nat.zero_lt_of_lt hN).ne'⟩
  let v := (u : TruncatedWittVector p h R).out
  have hv : WittVector.truncate h v = ↑u := TruncatedWittVector.truncateFun_out _
  have hdet' : A.det = WittVector.truncate h (v * (p : WittVector p R) ^ N) := by
    simpa only [map_mul, map_pow, hv, map_natCast] using hdet
  apply isPoint_of_det_eq_truncate_mul_pow hN hdet'
  rw [← TruncatedWittVector.constantCoeff_wittVector_truncate (n := h), hv]
  exact u.isUnit.map TruncatedWittVector.constantCoeff

end CharP

section Perfect

variable [CharP R p] [PerfectRing R p]

/-- A length-`h` jet of a full Witt matrix is on the determinant locus precisely when the
determinant of the full matrix is `p ^ N` times a unit. -/
theorem isPoint_map_truncate_iff_exists_unit_mul_pow (hN : N < h)
    (A : Matrix ι ι (WittVector p R)) :
    IsPoint hN (A.map (WittVector.truncate h)) ↔
      ∃ u : (WittVector p R)ˣ, A.det = ↑u * (p : WittVector p R) ^ N := by
  constructor
  · intro hA
    rw [isPoint_iff_det_coeff] at hA
    simp only [← RingHom.mapMatrix_apply, ← RingHom.map_det, WittVector.coeff_truncate] at hA
    obtain ⟨u, hu⟩ := WittVector.associated_p_pow_iff.mpr
      ⟨fun j hj ↦ hA.1 ⟨j, hj.trans hN⟩ hj, hA.2⟩
    exact ⟨u, by simpa [mul_comm] using hu.symm⟩
  · rintro ⟨u, hu⟩
    exact IsPoint.map_truncate_of_det_eq_unit_mul_pow (u := u) hu

/-- Zero-padding each matrix entry gives a full lift of a determinant jet with determinant
`p ^ N` times a unit. -/
theorem exists_det_map_out_eq_unit_mul_pow {hN : N < h}
    {A : Matrix ι ι (TruncatedWittVector p h R)} (hA : IsPoint hN A) :
    ∃ u : (WittVector p R)ˣ,
      (A.map TruncatedWittVector.out).det = ↑u * (p : WittVector p R) ^ N := by
  apply (isPoint_map_truncate_iff_exists_unit_mul_pow hN _).mp
  rwa [Matrix.map_wittVector_truncate_map_out]

/-- On a perfect base the determinant equations are equivalent to a unit times `p ^ N`
in the truncated Witt ring itself. -/
theorem isPoint_iff_exists_unit_mul_pow (hN : N < h) (A : Matrix ι ι (TruncatedWittVector p h R)) :
    IsPoint hN A ↔
      ∃ u : (TruncatedWittVector p h R)ˣ, A.det = ↑u * (p : TruncatedWittVector p h R) ^ N := by
  constructor
  · intro hA
    obtain ⟨u, hu⟩ := exists_det_map_out_eq_unit_mul_pow hA
    let trunc : WittVector p R →+* TruncatedWittVector p h R := WittVector.truncate h
    refine ⟨Units.map trunc u, ?_⟩
    simpa only [RingHom.map_det, RingHom.mapMatrix_apply, trunc,
      Matrix.map_wittVector_truncate_map_out, map_mul, map_pow, map_natCast,
      Units.coe_map, MonoidHom.coe_ofClass] using
      congrArg trunc hu
  · rintro ⟨u, hu⟩
    exact IsPoint.of_det_eq_unit_mul_pow (u := u) hu

end Perfect

end TauCeti.WittDeterminantJet
