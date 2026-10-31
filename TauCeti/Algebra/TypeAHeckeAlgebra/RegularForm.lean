/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.TypeAHeckeAlgebra.CanonicalTrace
public import TauCeti.Algebra.TypeAHeckeAlgebra.Star
public import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# The positive regular form of the type-A Hecke algebra

For a real nonzero Hecke parameter over `ℝ` or `ℂ`, the canonical trace defines the positive
definite form `⟨x,y⟩ = τ(x* y)`. The PBW basis `T_w` is orthonormal, so the rescaled basis
`g_w = q ^ length w • T_w` has squared length `(q²) ^ length w`. Left and right multiplication
have adjoints given by multiplication on the same side by the involution. In particular both
simple multiplication operators are self-adjoint, and the two actions commute.

`regularInnerProductCore` packages this form as an `InnerProductSpace.Core`, from which Mathlib
constructs its norm and inner product space. It does not install a global norm instance. This
is the regular Hilbert carrier used for orthogonal decompositions of positive-real Hecke
modules. It is distinct from an arbitrary-parameter Markov trace or its positive quotient.

The coordinate pairing is proved over every commutative star ring with star-fixed parameter;
only positivity needs real or complex coefficients.

## References

* M. Geck and G. Pfeiffer, *Characters of Finite Coxeter Groups and Iwahori-Hecke Algebras*,
  OUP (2000), Section 8.1, for the canonical symmetrizing trace.
* A. Mathas, *Iwahori–Hecke algebras and Schur algebras of the symmetric group*,
  University Lecture Series 15, AMS (1999).
-/

public section

namespace TauCeti.TypeAHeckeAlgebra

section StarRing

variable {R : Type*} [CommRing R] [StarRing R] {q : Rˣ} {n : ℕ}
variable [Fact (IsSelfAdjoint (q : R))]
variable {W : Type*} [Group W]
variable (cs : CoxeterSystem (CoxeterMatrix.A (n - 1)) W)

/-- The canonical trace conjugates under the real-parameter involution. -/
@[simp]
theorem canonicalTrace_star (x : TypeAHeckeAlgebra R q n) :
    canonicalTrace cs (star x) = star (canonicalTrace cs x) := by
  classical
  conv_lhs => rw [← (basisTw q cs).linearCombination_repr x]
  conv_rhs => rw [← (basisTw q cs).linearCombination_repr x]
  simp +contextual [Finsupp.linearCombination_apply, Finsupp.sum, star_smul,
    coe_basisTw, canonicalTrace_Tw, apply_ite]

/-- The trace pairing with a PBW vector extracts the conjugate coordinate. -/
theorem canonicalTrace_star_mul_Tw (x : TypeAHeckeAlgebra R q n) (w : W) :
    canonicalTrace cs (star x * Tw q cs w) = star ((basisTw q cs).repr x w) := by
  calc
    canonicalTrace cs (star x * Tw q cs w) =
        star (canonicalTrace cs (Tw q cs w⁻¹ * x)) := by
      rw [← canonicalTrace_star, star_mul, star_Tw, inv_inv]
    _ = star ((basisTw q cs).repr x w) := by rw [canonicalTrace_Tw_inv_mul]

/-- The trace form is the standard Hermitian pairing in PBW coordinates. -/
theorem canonicalTrace_star_mul [Fintype W] (x y : TypeAHeckeAlgebra R q n) :
    canonicalTrace cs (star x * y) =
      ∑ w, star ((basisTw q cs).repr x w) * (basisTw q cs).repr y w := by
  conv_lhs => rw [← (basisTw q cs).sum_repr y]
  simp [Finset.mul_sum, coe_basisTw, canonicalTrace_star_mul_Tw, mul_comm]

/-- The trace form is Hermitian. -/
theorem star_canonicalTrace_star_mul (x y : TypeAHeckeAlgebra R q n) :
    star (canonicalTrace cs (star y * x)) = canonicalTrace cs (star x * y) := by
  rw [← canonicalTrace_star, star_mul, star_star]

/-- The adjoint of left multiplication is left multiplication by the involution. -/
theorem canonicalTrace_star_mul_left (a x y : TypeAHeckeAlgebra R q n) :
    canonicalTrace cs (star (a * x) * y) = canonicalTrace cs (star x * (star a * y)) := by
  simp [star_mul, mul_assoc]

/-- The adjoint of right multiplication is right multiplication by the involution. -/
theorem canonicalTrace_star_mul_right (a x y : TypeAHeckeAlgebra R q n) :
    canonicalTrace cs (star (x * a) * y) = canonicalTrace cs (star x * (y * star a)) := by
  rw [star_mul, mul_assoc, canonicalTrace_mul_comm cs, mul_assoc]

open Classical in
/-- In the `g_w = q ^ length w • T_w` normalization, the diagonal entry of the trace form is
`(q²) ^ length w`, and all off-diagonal entries vanish. -/
theorem canonicalTrace_star_rescaled_Tw_mul_rescaled_Tw (v w : W) :
    canonicalTrace cs (star (((q : R) ^ cs.length v) • Tw q cs v) *
      ((q : R) ^ cs.length w) • Tw q cs w) =
        if v = w then ((q : R) ^ 2) ^ cs.length w else 0 := by
  classical
  rw [star_smul, star_pow, (Fact.out : IsSelfAdjoint (q : R)).star_eq, star_Tw]
  simpa only [cs.length_inv, inv_mul_eq_one] using
    canonicalTrace_rescaled_Tw_mul_rescaled_Tw (q := q) cs v⁻¹ w

end StarRing

section RCLike

variable {𝕜 : Type*} [RCLike 𝕜] {q : 𝕜ˣ} {n : ℕ}
variable [Fact (IsSelfAdjoint (q : 𝕜))]
variable {W : Type*} [Group W]
variable (cs : CoxeterSystem (CoxeterMatrix.A (n - 1)) W)

/-- The real part of the squared trace length is the sum of squared PBW coordinate norms. -/
theorem re_canonicalTrace_star_mul_self [Fintype W] (x : TypeAHeckeAlgebra 𝕜 q n) :
    RCLike.re (canonicalTrace cs (star x * x)) = ∑ w, ‖(basisTw q cs).repr x w‖ ^ 2 := by
  simp [canonicalTrace_star_mul, RCLike.conj_mul]

/-- The canonical trace is positive on squares for every real nonzero parameter. -/
theorem re_canonicalTrace_star_mul_self_nonneg [Finite W] (x : TypeAHeckeAlgebra 𝕜 q n) :
    0 ≤ RCLike.re (canonicalTrace cs (star x * x)) := by
  let := Fintype.ofFinite W
  rw [re_canonicalTrace_star_mul_self]
  exact Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- The canonical trace form is positive definite, including at `q = ±1`. -/
@[simp]
theorem canonicalTrace_star_mul_self_eq_zero_iff [Finite W] (x : TypeAHeckeAlgebra 𝕜 q n) :
    canonicalTrace cs (star x * x) = 0 ↔ x = 0 := by
  classical
  let := Fintype.ofFinite W
  constructor
  · intro hx
    have hs : ∑ w, ‖(basisTw q cs).repr x w‖ ^ 2 = 0 := by
      rw [← re_canonicalTrace_star_mul_self, hx, map_zero]
    have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun w _ => sq_nonneg
      ‖(basisTw q cs).repr x w‖)).mp hs
    apply (basisTw q cs).repr.injective
    ext w
    simpa using hz w (Finset.mem_univ w)
  · rintro rfl
    simp

/-- The positive definite regular inner product `⟨x,y⟩ = τ(x* y)`. This core supplies the
normed and inner product space structures without choosing a global norm instance. -/
@[instance_reducible]
noncomputable def regularInnerProductCore [Finite W] :
    InnerProductSpace.Core 𝕜 (TypeAHeckeAlgebra 𝕜 q n) where
  inner x y := canonicalTrace cs (star x * y)
  conj_inner_symm x y := star_canonicalTrace_star_mul cs x y
  re_inner_nonneg := re_canonicalTrace_star_mul_self_nonneg cs
  add_left x y z := by simp [star_add, add_mul]
  smul_left x y r := by simp [star_smul]
  definite x := (canonicalTrace_star_mul_self_eq_zero_iff cs x).mp

/-- The regular inner product core has the canonical trace form as its inner product. -/
@[simp]
theorem regularInnerProductCore_inner [Finite W] (x y : TypeAHeckeAlgebra 𝕜 q n) :
    (regularInnerProductCore cs).inner x y = canonicalTrace cs (star x * y) := (rfl)

/-- Left multiplication by a simple generator is self-adjoint for the regular inner product. -/
theorem regularInnerProductCore_T_mul [Finite W] (i : Fin (n - 1)) (x y : TypeAHeckeAlgebra 𝕜 q n) :
    (regularInnerProductCore cs).inner (T q i * x) y =
      (regularInnerProductCore cs).inner x (T q i * y) := by
  simp only [regularInnerProductCore_inner, canonicalTrace_star_mul_left, star_T]

/-- Right multiplication by a simple generator is self-adjoint for the regular inner product. -/
theorem regularInnerProductCore_mul_T [Finite W] (i : Fin (n - 1)) (x y : TypeAHeckeAlgebra 𝕜 q n) :
    (regularInnerProductCore cs).inner (x * T q i) y =
      (regularInnerProductCore cs).inner x (y * T q i) := by
  simp only [regularInnerProductCore_inner, canonicalTrace_star_mul_right, star_T]

end RCLike

end TauCeti.TypeAHeckeAlgebra
