/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

-- `Complex.isAlgClosed`, which `Representation.extendToGL` needs over `ℂ`.
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import TauCeti.RepresentationTheory.ClassicalGroups.Rational
public import TauCeti.RepresentationTheory.ClassicalGroups.SpecialLinear
-- `MvPolynomial.IsHomogeneous.eval_smul`, the scaling of a homogeneous component, and
-- `MvPolynomial.eval_eq_sum_homogeneousComponent_of_eval_smul`, the averaging over roots of unity.
import TauCeti.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.RootsOfUnity.Complex

/-!
# Rational representations of the special linear group

A representation of `SL n ℂ` is **rational** when, in some basis of the carrier, every matrix entry
of `ρ s` is a polynomial in the entries `sᵢⱼ` (`TauCeti.IsRationalSLRep`). On `SL n ℂ` the
determinant is `1`, so this is the restriction of the condition `TauCeti.IsRationalRep` on
`GL n ℂ`, and a rational representation of `GL n ℂ` restricts to a rational representation of
`SL n ℂ` (`TauCeti.IsRationalRep.comp_toGL`).

The point of this file is the converse. If the determinant-one scalar matrices act on `ρ` by
`z ↦ z ^ a`, then `ρ` extends to the representation `Representation.extendToGL` of `GL n ℂ`,
acting on `toGL s * scalar z` by `z ^ a • ρ s`, and that extension is again rational
(`TauCeti.IsRationalSLRep.isRationalRep_extendToGL`). This is not automatic: `z` is an `n`-th root
of `det g`, not a polynomial function of `g`.

## The argument

Let `P` be a polynomial giving a matrix entry of `ρ` on `SL n ℂ`, and `ζ` a primitive `n`-th root of
unity. Multiplying `s` by the scalar matrix `ζ ^ j` multiplies the entry by `ζ ^ (j a)`, while it
multiplies the homogeneous component of degree `d` of `P` by `ζ ^ (j d)`. Averaging over `j` with
the weights `ζ ^ (-j a)` kills every component whose degree is not congruent to `a` modulo `n`, so
the entry is already given by the components of degree `d ≡ a (mod n)`. On such a component, the
substitution `s = z⁻¹ g` produces the factor `z ^ (a - d) = (z ^ n) ^ ((a - d) / n)`, an integral
power of `det g = z ^ n`. So each entry of the extension is a sum of determinant powers times
polynomials in the entries of `g`, a rational function.

## Main definitions

* `TauCeti.IsRationalSLRep`: a representation of `SL n ℂ` is rational in coordinates.

## Main results

* `TauCeti.isRationalSLRep_iff_exists_toMatrix_eq_eval`: rationality can be checked against any
  finite basis.
* `TauCeti.IsRationalRep.comp_toGL`: a rational representation of `GL n ℂ` restricts to a rational
  representation of `SL n ℂ`.
* `TauCeti.IsRationalSLRep.isRationalRep_extendToGL`: **the extension of a rational
  representation of `SL n ℂ` to `GL n ℂ` is rational.**

## References

* W. Fulton and J. Harris, *Representation Theory: A First Course* (1991), Lecture 15.
-/

public section

open Matrix MvPolynomial TauCeti.Matrix.GeneralLinearGroup

namespace TauCeti

variable {n : ℕ} {W : Type*} [AddCommMonoid W] [Module ℂ W]

/-- **A rational representation** of `SL n ℂ`: in some basis of the carrier, every matrix entry of
`ρ s` is a polynomial in the entries of `s`. Since `det s = 1`, no determinant denominator is
needed, and this is the condition `TauCeti.IsRationalRep` read on the special linear group. The
carrier is forced to be finite-dimensional (`TauCeti.IsRationalSLRep.finite`), and the condition
does not depend on the basis: see `TauCeti.isRationalSLRep_iff_exists_toMatrix_eq_eval`. The base
field is `ℂ` for the reason recorded on `TauCeti.IsPolynomialRep`. -/
def IsRationalSLRep (ρ : Representation ℂ (SpecialLinearGroup (Fin n) ℂ) W) : Prop :=
  ∃ (b : Module.Basis (Fin (Module.finrank ℂ W)) ℂ W)
    (P : Fin (Module.finrank ℂ W) → Fin (Module.finrank ℂ W) → MvPolynomial (Fin n × Fin n) ℂ),
    ∀ (s : SpecialLinearGroup (Fin n) ℂ) (i j : Fin (Module.finrank ℂ W)),
      LinearMap.toMatrix b b (ρ s) i j
        = MvPolynomial.eval (fun p => (s : Matrix (Fin n) (Fin n) ℂ) p.1 p.2) (P i j)

/-- The coordinate-entry form of `TauCeti.IsRationalSLRep`, as a lemma. -/
theorem isRationalSLRep_iff (ρ : Representation ℂ (SpecialLinearGroup (Fin n) ℂ) W) :
    IsRationalSLRep ρ ↔ ∃ (b : Module.Basis (Fin (Module.finrank ℂ W)) ℂ W)
      (P : Fin (Module.finrank ℂ W) → Fin (Module.finrank ℂ W) → MvPolynomial (Fin n × Fin n) ℂ),
      ∀ (s : SpecialLinearGroup (Fin n) ℂ) (i j : Fin (Module.finrank ℂ W)),
        LinearMap.toMatrix b b (ρ s) i j
          = MvPolynomial.eval (fun p => (s : Matrix (Fin n) (Fin n) ℂ) p.1 p.2) (P i j) :=
  (Iff.rfl)

/-- The carrier of a rational representation of `SL n ℂ` is finite-dimensional. -/
theorem IsRationalSLRep.finite {ρ : Representation ℂ (SpecialLinearGroup (Fin n) ℂ) W}
    (h : IsRationalSLRep ρ) : Module.Finite ℂ W := by
  obtain ⟨b, -⟩ := h
  exact Module.Finite.of_basis b

/-- **Rationality on `SL n ℂ` is basis independent.** A representation of `SL n ℂ` is rational
exactly when, against *any* chosen finite basis, each matrix entry of `ρ s` is a polynomial in the
entries of `s`. -/
theorem isRationalSLRep_iff_exists_toMatrix_eq_eval
    {ρ : Representation ℂ (SpecialLinearGroup (Fin n) ℂ) W} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℂ W) :
    IsRationalSLRep ρ ↔ ∃ P : ι → ι → MvPolynomial (Fin n × Fin n) ℂ,
      ∀ (s : SpecialLinearGroup (Fin n) ℂ) (i j : ι),
        LinearMap.toMatrix b b (ρ s) i j
          = MvPolynomial.eval (fun p => (s : Matrix (Fin n) (Fin n) ℂ) p.1 p.2) (P i j) := by
  -- The polynomial functions on `SL n ℂ`, as a subalgebra of all functions.
  let A : Subalgebra ℂ (SpecialLinearGroup (Fin n) ℂ → ℂ) :=
    (aeval fun p : Fin n × Fin n => fun s : SpecialLinearGroup (Fin n) ℂ =>
      (s : Matrix (Fin n) (Fin n) ℂ) p.1 p.2).range
  have hA : ∀ f : SpecialLinearGroup (Fin n) ℂ → ℂ, f ∈ A ↔ ∃ P : MvPolynomial (Fin n × Fin n) ℂ,
      ∀ s, f s = eval (fun p => (s : Matrix (Fin n) (Fin n) ℂ) p.1 p.2) P := fun f => by
    have happ : ∀ (P : MvPolynomial (Fin n × Fin n) ℂ) (s : SpecialLinearGroup (Fin n) ℂ),
        (aeval fun p : Fin n × Fin n => fun s : SpecialLinearGroup (Fin n) ℂ =>
          (s : Matrix (Fin n) (Fin n) ℂ) p.1 p.2) P s
          = eval (fun p => (s : Matrix (Fin n) (Fin n) ℂ) p.1 p.2) P := fun P s => by
      simpa [aeval_eq_eval] using comp_aeval_apply
        (fun p : Fin n × Fin n => fun s : SpecialLinearGroup (Fin n) ℂ =>
          (s : Matrix (Fin n) (Fin n) ℂ) p.1 p.2)
        (Pi.evalAlgHom ℂ (fun _ : SpecialLinearGroup (Fin n) ℂ => ℂ) s) P
    constructor
    · rintro ⟨P, rfl⟩
      exact ⟨P, happ P⟩
    · rintro ⟨P, hP⟩
      exact ⟨P, funext fun s => (happ P s).trans (hP s).symm⟩
  constructor
  · rintro ⟨b₀, P, hP⟩
    have h := Representation.toMatrix_mem_of_toMatrix_mem A b₀ b ρ
      (fun p l => (hA _).mpr ⟨P p l, fun s => hP s p l⟩)
    choose Q hQ using fun q : ι × ι => (hA _).mp (h q.1 q.2)
    exact ⟨fun i j => Q (i, j), fun s i j => hQ (i, j) s⟩
  · rintro ⟨P, hP⟩
    let e : ι ≃ Fin (Module.finrank ℂ W) :=
      Fintype.equivFinOfCardEq (Module.finrank_eq_card_basis b).symm
    have h := Representation.toMatrix_mem_of_toMatrix_mem A b (b.reindex e) ρ
      (fun p l => (hA _).mpr ⟨P p l, fun s => hP s p l⟩)
    choose Q hQ using fun q : Fin (Module.finrank ℂ W) × Fin (Module.finrank ℂ W) =>
      (hA _).mp (h q.1 q.2)
    exact ⟨b.reindex e, fun i j => Q (i, j), fun s i j => hQ (i, j) s⟩

/-- **A rational representation of `GL n ℂ` restricts to a rational representation of
`SL n ℂ`**: the determinant denominator is `1` on the special linear group. -/
theorem IsRationalRep.comp_toGL {ρ : Representation ℂ (GL (Fin n) ℂ) W} (h : IsRationalRep ρ) :
    IsRationalSLRep (ρ.comp SpecialLinearGroup.toGL) := by
  obtain ⟨b, P, m, hP⟩ := (isRationalRep_iff ρ).mp h
  refine ⟨b, P, fun s i j => ?_⟩
  simpa using hP (SpecialLinearGroup.toGL s) i j

/-! ### The extension to `GL n ℂ` is rational -/

variable {ρ : Representation ℂ (SpecialLinearGroup (Fin n) ℂ) W} {a : ℤ}
  {ι : Type*} [Fintype ι] [DecidableEq ι] {b : Module.Basis ι ℂ W} {i j : ι}
  {Q : MvPolynomial (Fin n × Fin n) ℂ}

/-- If a matrix entry of `ρ` is the polynomial `Q` on `SL n ℂ`, and the determinant-one scalar
matrices act by `z ↦ z ^ a`, then that entry is already given by the homogeneous components of `Q`
of degree congruent to `a` modulo `n`. -/
private theorem toMatrix_apply_eq_sum_homogeneousComponent [NeZero n]
    (ha : ∀ (s : SpecialLinearGroup (Fin n) ℂ) (z : ℂˣ),
      SpecialLinearGroup.toGL s = _root_.Matrix.GeneralLinearGroup.scalar (Fin n) z →
        ∀ v, ρ s v = ((z ^ a : ℂˣ) : ℂ) • v)
    (hQ : ∀ s : SpecialLinearGroup (Fin n) ℂ, LinearMap.toMatrix b b (ρ s) i j =
      eval (fun p => (s : Matrix (Fin n) (Fin n) ℂ) p.1 p.2) Q)
    (s : SpecialLinearGroup (Fin n) ℂ) :
    LinearMap.toMatrix b b (ρ s) i j =
      ∑ d ∈ (Finset.range (Q.totalDegree + 1)).filter (fun d : ℕ => (n : ℤ) ∣ d - a),
        eval (fun p => (s : Matrix (Fin n) (Fin n) ℂ) p.1 p.2) (homogeneousComponent d Q) := by
  have hζ := Complex.isPrimitiveRoot_exp n (NeZero.ne n)
  set ζ := Complex.exp (2 * Real.pi * Complex.I / n)
  let u : ℂˣ := (hζ.isUnit (NeZero.ne n)).unit
  have hu : IsPrimitiveRoot u n := IsPrimitiveRoot.coe_units_iff.mp hζ
  rw [hQ]
  refine eval_eq_sum_homogeneousComponent_of_eval_smul _ hζ a _ fun k => ?_
  -- The scalar matrix `ζ ^ k` has determinant one.
  let t : SpecialLinearGroup (Fin n) ℂ :=
    ⟨_root_.Matrix.GeneralLinearGroup.scalar (Fin n) (u ^ k), by
      rw [← _root_.Matrix.GeneralLinearGroup.val_det_apply,
        _root_.Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin, ← pow_mul, mul_comm,
        pow_mul, hu.pow_eq_one, one_pow, Units.val_one]⟩
  have ht : SpecialLinearGroup.toGL t = _root_.Matrix.GeneralLinearGroup.scalar (Fin n) (u ^ k) :=
    Units.ext rfl
  have htm : (t : Matrix (Fin n) (Fin n) ℂ) = Matrix.scalar (Fin n) (ζ ^ k) := by
    rw [SpecialLinearGroup.coe_mk, _root_.Matrix.GeneralLinearGroup.coe_scalar,
      Units.val_pow_eq_pow_val, IsUnit.unit_spec]
  have hent : (ζ ^ k) • (fun p : Fin n × Fin n => (s : Matrix (Fin n) (Fin n) ℂ) p.1 p.2) =
      fun p => ((s * t : SpecialLinearGroup (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) p.1 p.2 := by
    funext p
    rw [SpecialLinearGroup.coe_mul, htm, Matrix.scalar_apply, Matrix.mul_diagonal, Pi.smul_apply,
      smul_eq_mul, mul_comm]
  have hact : ρ (s * t) = (ζ ^ k) ^ a • ρ s := by
    ext v
    rw [map_mul, Module.End.mul_apply, ha _ _ ht, map_smul, LinearMap.smul_apply,
      Units.val_zpow_eq_zpow_val, Units.val_pow_eq_pow_val, IsUnit.unit_spec]
  rw [hent, ← hQ, hact, map_smul, Matrix.smul_apply, smul_eq_mul, hQ]

/-- **The matrix entries of the extension.** If a matrix entry of `ρ` is the polynomial `Q` on
`SL n ℂ`, the corresponding entry of `Representation.extendToGL ρ a ha` at `g` is the sum, over the
degrees `d ≡ a (mod n)`, of `det g ^ ((a - d) / n)` times the homogeneous component of degree `d`
of `Q` evaluated at `g`. -/
private theorem toMatrix_extendToGL_apply [NeZero n]
    (ha : ∀ (s : SpecialLinearGroup (Fin n) ℂ) (z : ℂˣ),
      SpecialLinearGroup.toGL s = _root_.Matrix.GeneralLinearGroup.scalar (Fin n) z →
        ∀ v, ρ s v = ((z ^ a : ℂˣ) : ℂ) • v)
    (hQ : ∀ s : SpecialLinearGroup (Fin n) ℂ, LinearMap.toMatrix b b (ρ s) i j =
      eval (fun p => (s : Matrix (Fin n) (Fin n) ℂ) p.1 p.2) Q)
    (g : GL (Fin n) ℂ) :
    LinearMap.toMatrix b b (ρ.extendToGL a ha g) i j =
      ∑ d ∈ (Finset.range (Q.totalDegree + 1)).filter (fun d : ℕ => (n : ℤ) ∣ d - a),
        ((_root_.Matrix.GeneralLinearGroup.det g ^ ((a - d) / n) : ℂˣ) : ℂ) *
          eval (fun p => (g : Matrix (Fin n) (Fin n) ℂ) p.1 p.2) (homogeneousComponent d Q) := by
  obtain ⟨s, z, rfl⟩ := g.exists_toGL_mul_scalar_eq
  rw [Representation.extendToGL_toGL_mul_scalar, map_smul, Matrix.smul_apply, smul_eq_mul,
    toMatrix_apply_eq_sum_homogeneousComponent ha hQ, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  -- The entries of `s` are those of `toGL s * scalar z` divided by `z`.
  have hent : (fun p : Fin n × Fin n => (s : Matrix (Fin n) (Fin n) ℂ) p.1 p.2) =
      ((z : ℂ)⁻¹) • fun p : Fin n × Fin n =>
        ((SpecialLinearGroup.toGL s * _root_.Matrix.GeneralLinearGroup.scalar (Fin n) z :
          GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) p.1 p.2 := by
    funext p
    simp only [Matrix.GeneralLinearGroup.coe_mul, SpecialLinearGroup.coe_GL_coe_matrix,
      Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.mul_diagonal,
      Pi.smul_apply, smul_eq_mul]
    rw [mul_comm ((s : Matrix (Fin n) (Fin n) ℂ) p.1 p.2), ← mul_assoc,
      inv_mul_cancel₀ z.ne_zero, one_mul]
  rw [hent, (homogeneousComponent_isHomogeneous d _).eval_smul, smul_eq_mul, ← mul_assoc]
  congr 1
  -- `z ^ a * z ^ (-d) = (z ^ n) ^ ((a - d) / n)`, and `z ^ n = det (toGL s * scalar z)`.
  have hdvd : (n : ℤ) ∣ a - d := by
    rw [← dvd_neg, neg_sub]
    exact (Finset.mem_filter.mp hd).2
  rw [map_mul, SpecialLinearGroup.coeToGL_det, one_mul,
    _root_.Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin, ← zpow_natCast z n,
    ← zpow_mul, Int.mul_ediv_cancel' hdvd, zpow_sub, Units.val_mul, Units.val_inv_eq_inv_val,
    zpow_natCast, Units.val_pow_eq_pow_val, inv_pow]

/-- **The extension of a rational representation of `SL n ℂ` to `GL n ℂ` is rational.** If the
determinant-one scalar matrices act on a rational `ρ` by `z ↦ z ^ a`, the representation
`Representation.extendToGL ρ a ha` of `GL n ℂ`, acting on `toGL s * scalar z` by `z ^ a • ρ s`, is
rational: its matrix entries are sums of integral powers of `det` times polynomials in the
entries. -/
theorem IsRationalSLRep.isRationalRep_extendToGL (hρ : IsRationalSLRep ρ) (a : ℤ)
    (ha : ∀ (s : SpecialLinearGroup (Fin n) ℂ) (z : ℂˣ),
      SpecialLinearGroup.toGL s = _root_.Matrix.GeneralLinearGroup.scalar (Fin n) z →
        ∀ v, ρ s v = ((z ^ a : ℂˣ) : ℂ) • v) :
    IsRationalRep (ρ.extendToGL a ha) := by
  obtain ⟨b, P, hP⟩ := (isRationalSLRep_iff ρ).mp hρ
  rw [isRationalRep_iff_forall_mem_rationalFunctions b]
  intro i j
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · -- `GL 0 ℂ` is a single point, on which every function is constant.
    have hconst : (fun g : GL (Fin 0) ℂ => LinearMap.toMatrix b b (ρ.extendToGL a ha g) i j) =
        algebraMap ℂ (GL (Fin 0) ℂ → ℂ)
          (LinearMap.toMatrix b b (ρ.extendToGL a ha 1) i j) :=
      funext fun g => by
        rw [Subsingleton.elim g 1, Pi.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
    rw [hconst]
    exact Subalgebra.algebraMap_mem _ _
  have : NeZero n := ⟨hn.ne'⟩
  have hF : (fun g => LinearMap.toMatrix b b (ρ.extendToGL a ha g) i j) =
      ∑ d ∈ (Finset.range ((P i j).totalDegree + 1)).filter (fun d : ℕ => (n : ℤ) ∣ d - a),
        (fun g : GL (Fin n) ℂ =>
          ((_root_.Matrix.GeneralLinearGroup.det g ^ ((a - d) / n) : ℂˣ) : ℂ)) *
        (fun g : GL (Fin n) ℂ => eval (fun p => (g : Matrix (Fin n) (Fin n) ℂ) p.1 p.2)
          (homogeneousComponent d (P i j))) := by
    funext g
    rw [toMatrix_extendToGL_apply ha (hP · i j) g]
    simp only [Finset.sum_apply, Pi.mul_apply]
  rw [hF]
  exact Subalgebra.sum_mem _ fun d _ => Subalgebra.mul_mem _ (det_zpow_mem_rationalFunctions _)
    (polynomialFunctions_le_rationalFunctions (mem_polynomialFunctions.mpr ⟨_, fun _ => rfl⟩))

end TauCeti
