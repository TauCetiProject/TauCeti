/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Functoriality
public import TauCeti.LinearAlgebra.CliffordAlgebra.Reversal.Basic
import TauCeti.LinearAlgebra.QuadraticForm.Prod

/-!
# Even Clifford algebras of scalar multiples

Multiplying a quadratic form by a unit does not change its even Clifford algebra up to
isomorphism. The equivalence sends a pair of generating vectors to the corresponding pair
multiplied by the inverse scalar. This allows a represented unit to be normalized to `-1`
before applying the dimension-shift equivalence for Clifford algebras. Scaling preserves
reversal, and dimension reduction turns reversal into Clifford conjugation.

The construction uses the universal property of the even subalgebra, following Mathlib's
`CliffordAlgebra.evenToNeg` and `CliffordAlgebra.evenEquivEvenNeg` for negation.

## References

* T. Y. Lam, *Introduction to Quadratic Forms over Fields*, Chapter V, §2.
-/

public section

namespace TauCeti.CliffordAlgebra

open _root_.CliffordAlgebra

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

-- The equality parameter allows the inverse map to land in `even Q` without a cast.
private def evenMapScale (Q P : QuadraticForm R M) (a : Rˣ) (h : P = (a : R) • Q) :
    even Q →ₐ[R] even P :=
  even.lift Q
    { bilin := (↑a⁻¹ : R) • (even.ι P).bilin
      contract := fun m => by
        simp only [LinearMap.smul_apply, EvenHom.contract, h, smul_apply]
        rw [smul_eq_mul, map_mul, Algebra.smul_def, ← mul_assoc, ← map_mul]
        simp
      contract_mid := fun m n p => by
        simp only [LinearMap.smul_apply, smul_mul_smul_comm, EvenHom.contract_mid,
          h, smul_apply, smul_eq_mul, smul_smul]
        congr 1
        simp [mul_assoc, mul_left_comm, mul_comm] }

private theorem evenMapScale_ι (Q P : QuadraticForm R M) (a : Rˣ)
    (h : P = (a : R) • Q) (m n : M) :
    evenMapScale Q P a h ((even.ι Q).bilin m n) =
      (↑a⁻¹ : R) • (even.ι P).bilin m n :=
  even.lift_ι Q _ m n

private theorem evenMapScale_comp (Q P : QuadraticForm R M) (a : Rˣ)
    (h : P = (a : R) • Q) (h' : Q = (↑a⁻¹ : R) • P) :
    (evenMapScale P Q a⁻¹ h').comp (evenMapScale Q P a h) = AlgHom.id R _ := by
  ext m n : 4
  simp [evenMapScale_ι, smul_smul]

/-- Scaling a quadratic form by a unit preserves its even Clifford algebra. On products of
two generating vectors the equivalence multiplies by the inverse unit. -/
def evenEquivEvenSMul (Q : QuadraticForm R M) (a : Rˣ) :
    even Q ≃ₐ[R] even ((a : R) • Q) :=
  let h : Q = (↑a⁻¹ : R) • ((a : R) • Q) := by simp [smul_smul]
  AlgEquiv.ofAlgHom (evenMapScale Q _ a rfl) (evenMapScale _ Q a⁻¹ h)
    (evenMapScale_comp _ Q a⁻¹ h (by simp)) (evenMapScale_comp Q _ a rfl h)

/-- The scaling equivalence multiplies each bilinear generator by the inverse scalar. -/
@[simp]
theorem evenEquivEvenSMul_ι (Q : QuadraticForm R M) (a : Rˣ) (m n : M) :
    evenEquivEvenSMul Q a ((even.ι Q).bilin m n) =
      (↑a⁻¹ : R) • (even.ι ((a : R) • Q)).bilin m n :=
  evenMapScale_ι Q _ a rfl m n

/-- The inverse scaling equivalence multiplies a bilinear generator by the scalar. -/
@[simp]
theorem evenEquivEvenSMul_symm_ι (Q : QuadraticForm R M) (a : Rˣ) (m n : M) :
    (evenEquivEvenSMul Q a).symm ((even.ι ((a : R) • Q)).bilin m n) =
      (a : R) • (even.ι Q).bilin m n := by
  simp [evenEquivEvenSMul, evenMapScale_ι]

/-- The even-algebra scaling equivalence preserves Clifford reversal. -/
theorem evenEquivEvenSMul_reverseEven (Q : QuadraticForm R M) (a : Rˣ) (x : even Q) :
    evenEquivEvenSMul Q a (reverseEven Q x) =
      reverseEven ((a : R) • Q) (evenEquivEvenSMul Q a x) := by
  rcases x with ⟨x, hx⟩
  -- Even induction separates the ambient Clifford element from its membership proof;
  -- repackaging each branch exposes the subalgebra arithmetic used by the reversal API.
  induction x, hx using even_induction with
  | algebraMap r =>
      change evenEquivEvenSMul Q a (reverseEven Q (algebraMap R (even Q) r)) =
        reverseEven _ (evenEquivEvenSMul Q a (algebraMap R (even Q) r))
      simp
  | add x y hx hy ihx ihy =>
      change evenEquivEvenSMul Q a (reverseEven Q (⟨x, hx⟩ + ⟨y, hy⟩)) =
        reverseEven _ (evenEquivEvenSMul Q a (⟨x, hx⟩ + ⟨y, hy⟩))
      simp only [map_add, ihx, ihy]
  | ι_mul_ι_mul m n x hx ih =>
      let z : even Q := ⟨x, hx⟩
      change evenEquivEvenSMul Q a (reverseEven Q z) =
        reverseEven _ (evenEquivEvenSMul Q a z) at ih
      change evenEquivEvenSMul Q a (reverseEven Q ((even.ι Q).bilin m n * z)) =
        reverseEven _ (evenEquivEvenSMul Q a ((even.ι Q).bilin m n * z))
      simp only [reverseEven_mul, map_mul, ih, reverseEven_ι,
        evenEquivEvenSMul_ι, map_smul]

-- Normalizing the last coefficient to `-1` gives exactly Mathlib's augmented form.
private def normalizeLast (Q : QuadraticForm R M) (a : Rˣ) :
    ((↑(-a⁻¹) : R) • (Q.prod ((a : R) • QuadraticMap.sq))).IsometryEquiv
      (EquivEven.Q' ((↑(-a⁻¹) : R) • Q)) where
  toLinearEquiv := LinearEquiv.refl R _
  map_app' x := congrArg (fun P : QuadraticForm R (M × R) => P x)
    (by simp [QuadraticMap.smul_prod, EquivEven.Q', smul_smul])

private theorem normalizeLast_apply (Q : QuadraticForm R M) (a : Rˣ) (x : M × R) :
    normalizeLast Q a x = x := (rfl)

/-- The even Clifford algebra of `q ⊥ ⟨a⟩` is the Clifford algebra of `-a⁻¹ • q`.
This reduces the even algebra of a regular space to a Clifford algebra in one lower dimension. -/
noncomputable def evenProdSMulSqEquiv (Q : QuadraticForm R M) (a : Rˣ) :
    even (Q.prod ((a : R) • QuadraticMap.sq)) ≃ₐ[R]
      CliffordAlgebra (-(↑a⁻¹ : R) • Q) :=
  -- The target is the simp-normal form of `↑(-a⁻¹) • Q`: `Units.val_neg` is `rfl`,
  -- so these scalar expressions agree definitionally and the generator simp lemmas apply.
  ((evenEquivEvenSMul _ (-a⁻¹)).trans (evenEquivOfIsometry (normalizeLast Q a))).trans
    (equivEven _).symm

/-- On a pair of generators, the dimension-reduction equivalence is Mathlib's `ofEven`
formula multiplied by `-a`. -/
@[simp]
theorem evenProdSMulSqEquiv_ι (Q : QuadraticForm R M) (a : Rˣ) (x y : M × R) :
    evenProdSMulSqEquiv Q a ((even.ι (Q.prod ((a : R) • QuadraticMap.sq))).bilin x y) =
      -(a : R) •
        ((ι (-(↑a⁻¹ : R) • Q) x.1 + algebraMap R _ x.2) *
          (ι (-(↑a⁻¹ : R) • Q) y.1 - algebraMap R _ y.2)) := by
  rw [evenProdSMulSqEquiv, AlgEquiv.trans_apply, AlgEquiv.trans_apply, evenEquivEvenSMul_ι]
  simp only [map_smul, evenEquivOfIsometry_ι, equivEven_symm_apply, ofEven_ι]
  rw [normalizeLast_apply, normalizeLast_apply]
  simp

/-- The inverse dimension-reduction equivalence sends a vector to the last basis vector
times that vector, multiplied by `-a⁻¹`. -/
@[simp]
theorem evenProdSMulSqEquiv_symm_ι (Q : QuadraticForm R M) (a : Rˣ) (m : M) :
    (evenProdSMulSqEquiv Q a).symm (ι (-(↑a⁻¹ : R) • Q) m) =
      -(↑a⁻¹ : R) •
        (even.ι (Q.prod ((a : R) • QuadraticMap.sq))).bilin (0, 1) (m, 0) := by
  apply (evenProdSMulSqEquiv Q a).injective
  rw [map_smul, evenProdSMulSqEquiv_ι]
  simp [smul_smul]

/-- Dimension reduction sends reversal on the even algebra to Clifford conjugation. -/
theorem evenProdSMulSqEquiv_reverseEven (Q : QuadraticForm R M) (a : Rˣ)
    (x : even (Q.prod ((a : R) • QuadraticMap.sq))) :
    evenProdSMulSqEquiv Q a (reverseEven _ x) = star (evenProdSMulSqEquiv Q a x) := by
  simp only [evenProdSMulSqEquiv, AlgEquiv.trans_apply]
  rw [evenEquivEvenSMul_reverseEven, evenEquivOfIsometry_reverseEven,
    equivEven_symm_reverseEven]

end TauCeti.CliffordAlgebra
