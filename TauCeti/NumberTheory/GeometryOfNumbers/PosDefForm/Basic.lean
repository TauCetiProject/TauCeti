/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.GCDMonoid.Finset
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.Algebra.GCDMonoid.Nat
import TauCeti.LinearAlgebra.Matrix.Divisibility

/-!
# Positive definite real forms and their similarity classes

A *form* of rank `n` is a real symmetric positive definite `n × n` matrix `A`, evaluated on
vectors as `xᵀAx`. Forms are the objects of the extremal theory of lattices (minima, Hermite
invariants, perfect and extreme forms): the Gram matrices of the bases of a positive definite
lattice form one orbit of `GL_n(ℤ)` acting by `A ↦ UᵀAU`, and an invariant of forms that is
constant on these orbits is an isometry invariant of lattices.

This file sets up the carrier `TauCeti.PosDefForm n`, the subtype of Mathlib's `Matrix.PosDef`
(which includes symmetry), with:

* the value `A.eval x = xᵀAx` as a `QuadraticForm` and the pairing `A.pairing x y = xᵀAy` as a
  bilinear form, with positivity and polarization;
* the right action `actGL U A = UᵀAU` of `GL_n(ℤ)`, packaged as a `MulAction` of the opposite
  group, which preserves the determinant and satisfies `(actGL U A).eval x = A.eval (U x)`;
* the positive scaling `smulPos c hc A = c • A`, which commutes with the action;
* similarity, `B = c • UᵀAU` for some `c > 0` and `U ∈ GL_n(ℤ)`, an equivalence relation;
* integral and primitive forms, and the normalization theorem: in positive rank, the similarity
  class of an integral form contains a primitive integral form, unique up to `GL_n(ℤ)`.

In rank zero no form is primitive, since the gcd of the empty family of entries is `0`.

## Main declarations

* `TauCeti.PosDefForm`: positive definite real forms of rank `n`.
* `TauCeti.PosDefForm.actGL`, `TauCeti.PosDefForm.smulPos`, `TauCeti.PosDefForm.Similar`.
* `TauCeti.PosDefForm.det_actGL`: the action preserves the determinant.
* `TauCeti.PosDefForm.similar_equivalence`: similarity is an equivalence relation.
* `TauCeti.PosDefForm.exists_isPrimitiveForm_similar`,
  `TauCeti.PosDefForm.IsPrimitiveForm.exists_actGL_eq_of_similar`: existence and uniqueness of
  the primitive representative of an integral similarity class.

## References

* J. Martinet, *Perfect Lattices in Euclidean Spaces*, Grundlehren 327, Springer, 2003, §1.1
  and §2.1.
* J. H. Conway, N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, 3rd ed., Springer, 1999,
  Ch. 1 §2 and Ch. 2 §2.
-/

public section

open Matrix

namespace TauCeti

/-- A positive definite real form of rank `n`: a real `n × n` matrix satisfying Mathlib's
`Matrix.PosDef`, which includes symmetry. It is evaluated on vectors as `xᵀAx`. -/
abbrev PosDefForm (n : ℕ) : Type := {A : Matrix (Fin n) (Fin n) ℝ // A.PosDef}

namespace PosDefForm

variable {n : ℕ}

/-! ### Evaluation and pairing -/

/-- The pairing `xᵀAy` of a form, as a bilinear form on `ℝⁿ`. -/
noncomputable def pairing (A : PosDefForm n) : LinearMap.BilinForm ℝ (Fin n → ℝ) :=
  Matrix.toLinearMap₂' ℝ A.val

/-- The value `xᵀAx` of a form, as a quadratic form on `ℝⁿ`. -/
noncomputable def eval (A : PosDefForm n) : QuadraticForm ℝ (Fin n → ℝ) :=
  A.val.toQuadraticForm'

theorem pairing_apply (A : PosDefForm n) (x y : Fin n → ℝ) :
    A.pairing x y = x ⬝ᵥ (A.val *ᵥ y) :=
  Matrix.toLinearMap₂'_apply' A.val x y

theorem eval_apply (A : PosDefForm n) (x : Fin n → ℝ) : A.eval x = x ⬝ᵥ (A.val *ᵥ x) := by
  simp [eval, Matrix.toQuadraticForm', Matrix.toLinearMap₂'_apply']

@[simp]
theorem pairing_self (A : PosDefForm n) (x : Fin n → ℝ) : A.pairing x x = A.eval x := by
  rw [pairing_apply, eval_apply]

/-- The pairing of a form is symmetric, because the matrix of a form is symmetric. -/
theorem pairing_comm (A : PosDefForm n) (x y : Fin n → ℝ) : A.pairing x y = A.pairing y x := by
  have h : A.valᵀ = A.val := by simpa using A.prop.isHermitian.eq
  rw [pairing_apply, pairing_apply, dotProduct_comm, dotProduct_mulVec, ← mulVec_transpose, h]

/-- **Polarization.** `(x + y)ᵀA(x + y) = xᵀAx + yᵀAy + 2 xᵀAy`. -/
theorem eval_add (A : PosDefForm n) (x y : Fin n → ℝ) :
    A.eval (x + y) = A.eval x + A.eval y + 2 * A.pairing x y := by
  simp only [← pairing_self, map_add, LinearMap.add_apply, pairing_comm A y x]
  ring

theorem eval_pos (A : PosDefForm n) {x : Fin n → ℝ} (hx : x ≠ 0) : 0 < A.eval x := by
  simpa [eval_apply] using A.prop.dotProduct_mulVec_pos hx

/-- The quadratic form of a form is positive definite. -/
theorem posDef_eval (A : PosDefForm n) : A.eval.PosDef := fun _ hx => A.eval_pos hx

theorem eval_nonneg (A : PosDefForm n) (x : Fin n → ℝ) : 0 ≤ A.eval x :=
  A.posDef_eval.nonneg x

@[simp]
theorem eval_eq_zero_iff (A : PosDefForm n) {x : Fin n → ℝ} : A.eval x = 0 ↔ x = 0 :=
  A.posDef_eval.anisotropic.eq_zero_iff

/-! ### The action of `GL_n(ℤ)` -/

/-- The right action `A ↦ UᵀAU` of `GL_n(ℤ)` on forms; `UᵀAU` is positive definite because `U`
is invertible over `ℝ`. -/
noncomputable def actGL (U : GL (Fin n) ℤ) (A : PosDefForm n) : PosDefForm n :=
  ⟨((U : Matrix (Fin n) (Fin n) ℤ).map ((↑) : ℤ → ℝ))ᵀ * A.val *
      (U : Matrix (Fin n) (Fin n) ℤ).map ((↑) : ℤ → ℝ), by
    have hU : IsUnit ((U : Matrix (Fin n) (Fin n) ℤ).map ((↑) : ℤ → ℝ)) :=
      U.isUnit.map (Int.castRingHom ℝ).mapMatrix
    simpa using A.prop.conjTranspose_mul_mul_same (mulVec_injective_iff_isUnit.mpr hU)⟩

theorem coe_actGL (U : GL (Fin n) ℤ) (A : PosDefForm n) :
    ((actGL U A : PosDefForm n) : Matrix (Fin n) (Fin n) ℝ) =
      ((U : Matrix (Fin n) (Fin n) ℤ).map ((↑) : ℤ → ℝ))ᵀ * A.val *
        (U : Matrix (Fin n) (Fin n) ℤ).map ((↑) : ℤ → ℝ) :=
  (rfl)

/-- `(UᵀAU)[x, y] = A[Ux, Uy]`. -/
@[simp]
theorem pairing_actGL (U : GL (Fin n) ℤ) (A : PosDefForm n) (x y : Fin n → ℝ) :
    (actGL U A).pairing x y =
      A.pairing ((U : Matrix (Fin n) (Fin n) ℤ).map ((↑) : ℤ → ℝ) *ᵥ x)
        ((U : Matrix (Fin n) (Fin n) ℤ).map ((↑) : ℤ → ℝ) *ᵥ y) := by
  simp only [pairing_apply, coe_actGL, ← mulVec_mulVec, dotProduct_mulVec _ (_ᵀ),
    vecMul_transpose]

/-- `(UᵀAU)[x] = A[Ux]`. -/
@[simp]
theorem eval_actGL (U : GL (Fin n) ℤ) (A : PosDefForm n) (x : Fin n → ℝ) :
    (actGL U A).eval x = A.eval ((U : Matrix (Fin n) (Fin n) ℤ).map ((↑) : ℤ → ℝ) *ᵥ x) := by
  rw [← pairing_self, pairing_actGL, pairing_self]

@[simp]
theorem actGL_one (A : PosDefForm n) : actGL 1 A = A :=
  Subtype.ext <| by simp [coe_actGL]

/-- The action is a right action: acting by `U` and then by `V` is acting by `U * V`. -/
theorem actGL_mul (U V : GL (Fin n) ℤ) (A : PosDefForm n) :
    actGL (U * V) A = actGL V (actGL U A) := by
  refine Subtype.ext ?_
  simp only [coe_actGL, Units.val_mul, ← Int.coe_castRingHom, Matrix.map_mul, transpose_mul,
    Matrix.mul_assoc]

/-- `GL_n(ℤ)` acts on the right on forms by `A ↦ UᵀAU`, that is, `MulOpposite.op U • A`
is `actGL U A`. -/
noncomputable instance instMulAction : MulAction (GL (Fin n) ℤ)ᵐᵒᵖ (PosDefForm n) where
  smul U A := actGL U.unop A
  one_smul := actGL_one
  mul_smul U V A := actGL_mul V.unop U.unop A

@[simp]
theorem op_smul_eq_actGL (U : GL (Fin n) ℤ) (A : PosDefForm n) :
    MulOpposite.op U • A = actGL U A :=
  rfl

/-- The action of `GL_n(ℤ)` preserves the determinant, because `det U = ±1`. -/
@[simp]
theorem det_actGL (U : GL (Fin n) ℤ) (A : PosDefForm n) :
    (actGL U A).val.det = A.val.det := by
  have h : IsUnit (U : Matrix (Fin n) (Fin n) ℤ).det :=
    (isUnit_iff_isUnit_det _).mp U.isUnit
  rcases Int.isUnit_iff.mp h with h | h <;>
    simp [coe_actGL, det_mul, ← Int.cast_det, h]

/-! ### Positive scaling -/

/-- The positive scaling `c • A` of a form, `c > 0`. -/
def smulPos (c : ℝ) (hc : 0 < c) (A : PosDefForm n) : PosDefForm n :=
  ⟨c • A.val, A.prop.smul hc⟩

@[simp]
theorem coe_smulPos (c : ℝ) (hc : 0 < c) (A : PosDefForm n) :
    ((smulPos c hc A : PosDefForm n) : Matrix (Fin n) (Fin n) ℝ) = c • A.val :=
  (rfl)

@[simp]
theorem pairing_smulPos (c : ℝ) (hc : 0 < c) (A : PosDefForm n) (x y : Fin n → ℝ) :
    (smulPos c hc A).pairing x y = c * A.pairing x y := by
  simp [pairing_apply, smul_mulVec]

@[simp]
theorem eval_smulPos (c : ℝ) (hc : 0 < c) (A : PosDefForm n) (x : Fin n → ℝ) :
    (smulPos c hc A).eval x = c * A.eval x := by
  rw [← pairing_self, pairing_smulPos, pairing_self]

@[simp]
theorem smulPos_one (A : PosDefForm n) : smulPos 1 one_pos A = A :=
  Subtype.ext <| one_smul ℝ A.val

@[simp]
theorem smulPos_smulPos (c d : ℝ) (hc : 0 < c) (hd : 0 < d) (A : PosDefForm n) :
    smulPos c hc (smulPos d hd A) = smulPos (c * d) (mul_pos hc hd) A :=
  Subtype.ext <| smul_smul c d A.val

/-- The two generators of similarity commute: scaling commutes with the action of `GL_n(ℤ)`. -/
@[simp]
theorem actGL_smulPos (U : GL (Fin n) ℤ) (c : ℝ) (hc : 0 < c) (A : PosDefForm n) :
    actGL U (smulPos c hc A) = smulPos c hc (actGL U A) :=
  Subtype.ext <| by simp [coe_actGL]

/-! ### Similarity -/

/-- Similarity of forms: `B = c • UᵀAU` for some `c > 0` and `U ∈ GL_n(ℤ)`. -/
def Similar (A B : PosDefForm n) : Prop :=
  ∃ (c : ℝ) (hc : 0 < c) (U : GL (Fin n) ℤ), B = smulPos c hc (actGL U A)

theorem similar_def {A B : PosDefForm n} :
    Similar A B ↔ ∃ (c : ℝ) (hc : 0 < c) (U : GL (Fin n) ℤ), B = smulPos c hc (actGL U A) :=
  Iff.rfl

@[refl]
theorem Similar.refl (A : PosDefForm n) : Similar A A :=
  ⟨1, one_pos, 1, by simp⟩

theorem similar_actGL (U : GL (Fin n) ℤ) (A : PosDefForm n) : Similar A (actGL U A) :=
  ⟨1, one_pos, U, by simp⟩

theorem similar_smulPos (c : ℝ) (hc : 0 < c) (A : PosDefForm n) : Similar A (smulPos c hc A) :=
  ⟨c, hc, 1, by simp⟩

@[symm]
theorem Similar.symm {A B : PosDefForm n} (h : Similar A B) : Similar B A := by
  obtain ⟨c, hc, U, rfl⟩ := h
  refine ⟨c⁻¹, inv_pos.mpr hc, U⁻¹, ?_⟩
  rw [actGL_smulPos, ← actGL_mul, mul_inv_cancel, actGL_one, smulPos_smulPos]
  simp [inv_mul_cancel₀ hc.ne']

@[trans]
theorem Similar.trans {A B C : PosDefForm n} (hAB : Similar A B) (hBC : Similar B C) :
    Similar A C := by
  obtain ⟨c, hc, U, rfl⟩ := hAB
  obtain ⟨d, hd, V, rfl⟩ := hBC
  exact ⟨d * c, mul_pos hd hc, U * V, by rw [actGL_smulPos, smulPos_smulPos, actGL_mul]⟩

/-- Similarity is an equivalence relation on forms. -/
theorem similar_equivalence : Equivalence (Similar (n := n)) :=
  ⟨Similar.refl, Similar.symm, Similar.trans⟩

/-! ### Integral and primitive forms -/

/-- A form is *integral* when its entries are integers. -/
def IsIntegralForm (A : PosDefForm n) : Prop :=
  ∃ M : Matrix (Fin n) (Fin n) ℤ, M.map ((↑) : ℤ → ℝ) = A.val

/-- An integral form is the real cast of an integer matrix. -/
theorem isIntegralForm_iff_exists_matrix {A : PosDefForm n} :
    A.IsIntegralForm ↔ ∃ M : Matrix (Fin n) (Fin n) ℤ, M.map (Int.cast : ℤ → ℝ) = A.val :=
  Iff.rfl

/-- A form is *primitive* when it is integral and its entries have gcd `1`. In rank zero the gcd
of the empty family of entries is `0`, so no form of rank zero is primitive. -/
def IsPrimitiveForm (A : PosDefForm n) : Prop :=
  ∃ M : Matrix (Fin n) (Fin n) ℤ, M.map ((↑) : ℤ → ℝ) = A.val ∧
    Finset.univ.gcd (fun p : Fin n × Fin n => M p.fst p.snd) = 1

theorem isPrimitiveForm_iff {A : PosDefForm n} :
    A.IsPrimitiveForm ↔ ∃ M : Matrix (Fin n) (Fin n) ℤ, M.map ((↑) : ℤ → ℝ) = A.val ∧
      Finset.univ.gcd (fun p : Fin n × Fin n => M p.fst p.snd) = 1 :=
  Iff.rfl

theorem isIntegralForm_iff (A : PosDefForm n) :
    A.IsIntegralForm ↔ ∀ i j, ∃ m : ℤ, A.val i j = m := by
  refine ⟨fun ⟨M, hM⟩ i j => ⟨M i j, by simp [← hM]⟩, fun h => ?_⟩
  choose M hM using h
  exact ⟨Matrix.of M, by ext i j; simp [hM]⟩

theorem IsPrimitiveForm.isIntegralForm {A : PosDefForm n} (h : A.IsPrimitiveForm) :
    A.IsIntegralForm :=
  let ⟨M, hM, _⟩ := h
  ⟨M, hM⟩

/-- Primitive forms have positive rank. -/
theorem IsPrimitiveForm.pos_rank {A : PosDefForm n} (h : A.IsPrimitiveForm) : 0 < n := by
  obtain ⟨M, -, hM⟩ := h
  refine Nat.pos_of_ne_zero fun hn => ?_
  subst hn
  simp at hM

/-- The integer matrix of `actGL U A`, for an integral form `A` with integer matrix `M`. -/
private theorem map_transpose_mul_mul (U : GL (Fin n) ℤ) {A : PosDefForm n}
    {M : Matrix (Fin n) (Fin n) ℤ} (hM : M.map ((↑) : ℤ → ℝ) = A.val) :
    ((U : Matrix (Fin n) (Fin n) ℤ)ᵀ * M * U).map ((↑) : ℤ → ℝ) = (actGL U A).val := by
  rw [coe_actGL, ← hM]
  simp only [← Int.coe_castRingHom, Matrix.map_mul, transpose_map]

/-- Primitivity is invariant under the action of `GL_n(ℤ)`. -/
theorem IsPrimitiveForm.actGL {A : PosDefForm n} (h : A.IsPrimitiveForm) (U : GL (Fin n) ℤ) :
    (PosDefForm.actGL U A).IsPrimitiveForm := by
  obtain ⟨M, hM, hM1⟩ := h
  refine ⟨_, map_transpose_mul_mul U hM, ?_⟩
  -- The gcd `d` of the entries of `K = UᵀMU` divides the entries of `M = U⁻ᵀKU⁻¹`, hence
  -- divides `1`.
  have hMK : M = (↑U⁻¹ : Matrix (Fin n) (Fin n) ℤ)ᵀ *
      ((U : Matrix (Fin n) (Fin n) ℤ)ᵀ * M * U) * (↑U⁻¹ : Matrix (Fin n) (Fin n) ℤ) := by
    simp [← Matrix.mul_assoc, ← transpose_mul]
  set K := (U : Matrix (Fin n) (Fin n) ℤ)ᵀ * M * U
  refine Int.eq_one_of_dvd_one (Int.nonneg_of_normalize_eq_self Finset.normalize_gcd) ?_
  rw [← hM1, Finset.dvd_gcd_iff]
  rintro ⟨i, j⟩ -
  rw [hMK]
  exact dvd_mul_mul_apply (fun i j => Finset.gcd_dvd (f := fun p : Fin n × Fin n => K p.fst p.snd)
    (b := (i, j)) (Finset.mem_univ _)) _ _ i j

/-- Integrality is invariant under the action of `GL_n(ℤ)`. -/
theorem IsIntegralForm.actGL {A : PosDefForm n} (h : A.IsIntegralForm) (U : GL (Fin n) ℤ) :
    (PosDefForm.actGL U A).IsIntegralForm := by
  obtain ⟨M, hM⟩ := h
  exact ⟨_, map_transpose_mul_mul U hM⟩

/-- **Existence of the primitive representative.** In positive rank, the similarity class of an
integral form contains a primitive form: divide the form by the gcd of its entries. -/
theorem exists_isPrimitiveForm_similar (hn : 0 < n) {A : PosDefForm n}
    (hA : A.IsIntegralForm) : ∃ P : PosDefForm n, P.IsPrimitiveForm ∧ Similar A P := by
  obtain ⟨M, hM⟩ := hA
  have : Nonempty (Fin n × Fin n) := ⟨(⟨0, hn⟩, ⟨0, hn⟩)⟩
  obtain ⟨M₀, hM₀, hg1⟩ := Finset.extract_gcd (fun p : Fin n × Fin n => M p.fst p.snd)
    Finset.univ_nonempty
  generalize hg : Finset.univ.gcd (fun p : Fin n × Fin n => M p.fst p.snd) = g at hM₀
  -- the gcd `g` is positive: it is nonnegative, and it divides the positive entry `M 0 0`
  have hdiag : (0 : ℝ) < M ⟨0, hn⟩ ⟨0, hn⟩ := by
    simpa [← hM] using A.prop.diag_pos (i := ⟨0, hn⟩)
  have hgpos : (0 : ℝ) < g := by
    have hgne : g ≠ 0 := by
      rintro rfl
      have := hM₀ (⟨0, hn⟩, ⟨0, hn⟩) (Finset.mem_univ _)
      simp only [zero_mul] at this
      simp [this] at hdiag
    exact_mod_cast (hg ▸ Int.nonneg_of_normalize_eq_self Finset.normalize_gcd).lt_of_ne' hgne
  refine ⟨smulPos (g : ℝ)⁻¹ (inv_pos.mpr hgpos) A,
    ⟨Matrix.of fun i j => M₀ (i, j), ?_, hg1⟩, (g : ℝ)⁻¹, inv_pos.mpr hgpos, 1, by simp⟩
  ext i j
  have := hM₀ (i, j) (Finset.mem_univ _)
  simp only at this
  simp [← hM, this, hgpos.ne']

/-- **Uniqueness of the primitive representative.** Two similar primitive forms are
`GL_n(ℤ)`-equivalent: the scaling factor relating them is `1`. -/
theorem IsPrimitiveForm.exists_actGL_eq_of_similar {P Q : PosDefForm n}
    (hP : P.IsPrimitiveForm) (hQ : Q.IsPrimitiveForm) (h : Similar P Q) :
    ∃ U : GL (Fin n) ℤ, Q = PosDefForm.actGL U P := by
  have hn := hP.pos_rank
  obtain ⟨c, hc, U, rfl⟩ := h
  refine ⟨U, ?_⟩
  obtain ⟨M, hM, hM1⟩ := hP.actGL U
  obtain ⟨N, hN, hN1⟩ := hQ
  set i₀ : Fin n := ⟨0, hn⟩
  -- entrywise, `N = c • M` as real matrices
  have hNM : ∀ i j, (N i j : ℝ) = c * M i j := fun i j => by
    have := congrFun (congrFun hN i) j
    simp only [map_apply, coe_smulPos] at this
    rw [this, ← hM]
    simp
  have hb : (0 : ℝ) < M i₀ i₀ := by
    simpa [← hM] using (PosDefForm.actGL U P).prop.diag_pos (i := i₀)
  -- clearing the denominator of `c = N₀₀ / M₀₀` gives `M₀₀ • N = N₀₀ • M` over `ℤ`
  have hint : ∀ i j, M i₀ i₀ * N i j = N i₀ i₀ * M i j := fun i j => by
    have : ((M i₀ i₀ * N i j : ℤ) : ℝ) = ((N i₀ i₀ * M i j : ℤ) : ℝ) := by
      push_cast
      rw [hNM, hNM]
      ring
    exact_mod_cast this
  -- comparing the gcds of the entries of both sides gives `M₀₀ = N₀₀`
  have hgcd := congrArg (fun f : Fin n → Fin n → ℤ =>
    Finset.univ.gcd fun p : Fin n × Fin n => f p.fst p.snd) (funext₂ hint)
  simp only [Finset.gcd_mul_left, hM1, hN1, mul_one] at hgcd
  have hpos : (0 : ℤ) ≤ M i₀ i₀ := by exact_mod_cast hb.le
  have hpos' : (0 : ℤ) ≤ N i₀ i₀ := by
    have hN₀ : (0 : ℝ) ≤ N i₀ i₀ := by
      rw [hNM]
      positivity
    exact_mod_cast hN₀
  rw [Int.normalize_of_nonneg hpos, Int.normalize_of_nonneg hpos'] at hgcd
  have hc1 : c = 1 := by
    have h₀ := hNM i₀ i₀
    rw [← hgcd] at h₀
    exact (mul_eq_right₀ hb.ne').mp h₀.symm
  subst hc1
  simp

end PosDefForm

end TauCeti
