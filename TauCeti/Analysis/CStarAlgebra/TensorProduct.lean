/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Spectrum
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Algebra.Star.TensorProduct
public import Mathlib.Analysis.Normed.Unbundled.RingSeminorm
public import TauCeti.Analysis.CStarAlgebra.Completion
public import TauCeti.Analysis.Normed.Ring.Completion

/-!
# The C*-tensor product with respect to a C*-norm

Let `A` and `B` be (possibly non-unital) C*-algebras. A **C*-norm** on the algebraic tensor
product `A ⊗[ℂ] B` (`TauCeti.CStarTensorNorm A B`) is a norm that is submultiplicative,
star-invariant and satisfies the C*-identity `N (x⋆ x) = N x ^ 2`. With such a norm, `A ⊗[ℂ] B`
is a normed star algebra satisfying the C*-identity (`TauCeti.CStarTensorAlgebra N`, a type
synonym of `A ⊗[ℂ] B`). Its completion is the **C*-tensor product** `TauCeti.CStarTensorProduct N`
(written A ⊗_N B in the literature; this file declares no notation for it), a C*-algebra, with
the star homomorphism `TauCeti.CStarTensorProduct.of N : A ⊗[ℂ] B → TauCeti.CStarTensorProduct N`,
which is injective, isometric for `N` and has dense range. A star homomorphism `A ⊗[ℂ] B → C` into
a C*-algebra bounded by `N` extends to `TauCeti.CStarTensorProduct N`
(`TauCeti.CStarTensorProduct.extend`), isometrically if it preserves `N`.

The maximal and minimal tensor products `TauCeti.MaxTensorProduct A B` and
`TauCeti.MinTensorProduct A B` are the cases of the maximal and minimal norms.

## Main declarations

* `TauCeti.CStarTensorNorm A B`: C*-norms on `A ⊗[ℂ] B`.
* `TauCeti.CStarTensorAlgebra N`: `A ⊗[ℂ] B` with the norm `N`, with the star algebra isomorphism
  `TauCeti.CStarTensorAlgebra.equiv N` from `A ⊗[ℂ] B`.
* `TauCeti.CStarTensorProduct N`: its completion, a C*-algebra.
* `TauCeti.CStarTensorProduct.of`, `TauCeti.CStarTensorProduct.norm_of`,
  `TauCeti.CStarTensorProduct.of_injective`, `TauCeti.CStarTensorProduct.denseRange_of`,
  `TauCeti.CStarTensorProduct.starAlgHom_ext`.
* `TauCeti.CStarTensorProduct.extend`: extension of star homomorphisms bounded by `N`.

## References

* B. Blackadar, *Operator Algebras: Theory of C*-Algebras and von Neumann Algebras*,
  II.9.1–II.9.2.
-/

public section

noncomputable section

open UniformSpace TensorProduct

universe u v

namespace TauCeti

variable (A : Type u) (B : Type v) [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]

/-- A **C*-norm** on the algebraic tensor product `A ⊗[ℂ] B`: a norm that is submultiplicative,
star-invariant and satisfies the C*-identity `N (x⋆ x) = N x ^ 2`. Its completion is the
C*-tensor product `TauCeti.CStarTensorProduct N`. -/
structure CStarTensorNorm extends RingNorm (A ⊗[ℂ] B) where
  /-- A C*-norm is absolutely homogeneous. -/
  smul' (c : ℂ) (x : A ⊗[ℂ] B) : toFun (c • x) = ‖c‖ * toFun x
  /-- A C*-norm is star-invariant. -/
  star' (x : A ⊗[ℂ] B) : toFun (star x) = toFun x
  /-- A C*-norm satisfies the C*-identity. -/
  star_mul_self' (x : A ⊗[ℂ] B) : toFun (star x * x) = toFun x ^ 2

namespace CStarTensorNorm

variable {A B}

instance : FunLike (CStarTensorNorm A B) (A ⊗[ℂ] B) ℝ where
  coe N := N.toRingNorm
  coe_injective N N' h := by
    cases N
    cases N'
    congr
    exact DFunLike.coe_injective h

/-- A C*-norm is a ring norm, so the generic `RingNormClass` API applies to it. -/
instance : RingNormClass (CStarTensorNorm A B) (A ⊗[ℂ] B) ℝ where
  map_zero N := map_zero N.toRingNorm
  map_add_le_add N := map_add_le_add N.toRingNorm
  map_mul_le_mul N := map_mul_le_mul N.toRingNorm
  map_neg_eq_map N := map_neg_eq_map N.toRingNorm
  eq_zero_of_map_eq_zero N := eq_zero_of_map_eq_zero N.toRingNorm

/-- The underlying ring norm of a C*-norm has the same values. -/
@[simp]
theorem coe_toRingNorm (N : CStarTensorNorm A B) : ⇑N.toRingNorm = N :=
  (rfl)

/-- Two C*-norms with the same values are equal. -/
@[ext]
theorem ext {N N' : CStarTensorNorm A B} (h : ∀ x, N x = N' x) : N = N' :=
  DFunLike.ext N N' h

/-- A C*-norm is absolutely homogeneous. -/
theorem map_smul_eq_mul (N : CStarTensorNorm A B) (c : ℂ) (x : A ⊗[ℂ] B) :
    N (c • x) = ‖c‖ * N x :=
  N.smul' c x

/-- A C*-norm is star-invariant. -/
@[simp]
theorem map_star (N : CStarTensorNorm A B) (x : A ⊗[ℂ] B) : N (star x) = N x :=
  N.star' x

/-- A C*-norm satisfies the C*-identity. -/
theorem map_star_mul_self (N : CStarTensorNorm A B) (x : A ⊗[ℂ] B) :
    N (star x * x) = N x ^ 2 :=
  N.star_mul_self' x

end CStarTensorNorm

variable {A B}

/-- The algebraic tensor product `A ⊗[ℂ] B` with a C*-norm `N`. Its completion is the C*-tensor
product `TauCeti.CStarTensorProduct N`. Use `TauCeti.CStarTensorAlgebra.equiv N` to pass to and
from `A ⊗[ℂ] B`. -/
@[expose] def CStarTensorAlgebra (_N : CStarTensorNorm A B) : Type (max u v) :=
  A ⊗[ℂ] B

namespace CStarTensorAlgebra

variable (N : CStarTensorNorm A B)

instance : NonUnitalRing (CStarTensorAlgebra N) :=
  inferInstanceAs (NonUnitalRing (A ⊗[ℂ] B))

instance : Module ℂ (CStarTensorAlgebra N) :=
  inferInstanceAs (Module ℂ (A ⊗[ℂ] B))

instance : IsScalarTower ℂ (CStarTensorAlgebra N) (CStarTensorAlgebra N) :=
  inferInstanceAs (IsScalarTower ℂ (A ⊗[ℂ] B) (A ⊗[ℂ] B))

instance : SMulCommClass ℂ (CStarTensorAlgebra N) (CStarTensorAlgebra N) :=
  inferInstanceAs (SMulCommClass ℂ (A ⊗[ℂ] B) (A ⊗[ℂ] B))

instance : StarRing (CStarTensorAlgebra N) :=
  inferInstanceAs (StarRing (A ⊗[ℂ] B))

instance : StarModule ℂ (CStarTensorAlgebra N) :=
  inferInstanceAs (StarModule ℂ (A ⊗[ℂ] B))

/-- Regard an element of `A ⊗[ℂ] B` as an element with the norm `N`: the identity of the
underlying star algebra. -/
def equiv : A ⊗[ℂ] B ≃⋆ₐ[ℂ] CStarTensorAlgebra N where
  __ := Equiv.refl _
  map_mul' _ _ := (rfl)
  map_add' _ _ := (rfl)
  map_smul' _ _ := (rfl)
  map_star' _ := (rfl)

/-- The norm `N` makes `A ⊗[ℂ] B` a normed group. -/
instance : NormedAddCommGroup (CStarTensorAlgebra N) :=
  @AddGroupNorm.toNormedAddCommGroup (CStarTensorAlgebra N) _ N.toAddGroupNorm

variable {N}

/-- The norm of an element of `TauCeti.CStarTensorAlgebra N` is the norm `N` of the underlying
element of `A ⊗[ℂ] B`. -/
theorem norm_def (x : CStarTensorAlgebra N) : ‖x‖ = N ((equiv N).symm x) :=
  (rfl)

@[simp]
theorem norm_equiv (x : A ⊗[ℂ] B) : ‖equiv N x‖ = N x :=
  (rfl)

instance : NormedSpace ℂ (CStarTensorAlgebra N) where
  __ : Module ℂ (CStarTensorAlgebra N) := inferInstance
  norm_smul_le c x := by
    rw [norm_def, norm_def, map_smul]
    exact (N.map_smul_eq_mul c _).le

/-- A C*-norm is submultiplicative, so `TauCeti.CStarTensorAlgebra N` is a normed ring. -/
instance : NonUnitalNormedRing (CStarTensorAlgebra N) where
  __ : NormedAddCommGroup (CStarTensorAlgebra N) := inferInstance
  __ : NonUnitalRing (CStarTensorAlgebra N) := inferInstance
  norm_mul_le x y := by
    rw [norm_def, norm_def, norm_def, map_mul]
    exact map_mul_le_mul N _ _

/-- The star operation is isometric for a C*-norm. -/
instance : NormedStarGroup (CStarTensorAlgebra N) where
  norm_star_le x := by
    rw [norm_def, norm_def, map_star]
    exact (N.map_star _).le

/-- A C*-norm satisfies the C*-identity. -/
instance : CStarRing (CStarTensorAlgebra N) where
  norm_mul_self_le x := by
    rw [norm_def, norm_def, map_mul, map_star, ← sq]
    exact (N.map_star_mul_self _).ge

end CStarTensorAlgebra

open CStarTensorAlgebra

/-- The **C*-tensor product** of C*-algebras `A` and `B` with respect to a C*-norm `N`: the
completion of the algebraic tensor product `A ⊗[ℂ] B` in `N`. It is a C*-algebra, and the
canonical map `TauCeti.CStarTensorProduct.of N` from `A ⊗[ℂ] B` is injective and isometric with
dense range. -/
@[expose] def CStarTensorProduct (N : CStarTensorNorm A B) : Type (max u v) :=
  Completion (CStarTensorAlgebra N)

namespace CStarTensorProduct

open scoped _root_.CStarAlgebra

variable (N : CStarTensorNorm A B)

/-- The completion of `A ⊗[ℂ] B` in a C*-norm is a C*-algebra. -/
instance : NonUnitalCStarAlgebra (Completion (CStarTensorAlgebra N)) where
  toCStarRing := Completion.cstarRing fun x ↦ (CStarRing.norm_star_mul_self (x := x)).ge

/-- The C*-tensor product is a C*-algebra. -/
instance : NonUnitalCStarAlgebra (CStarTensorProduct N) :=
  inferInstanceAs (NonUnitalCStarAlgebra (Completion (CStarTensorAlgebra N)))

/-- The canonical star homomorphism `A ⊗[ℂ] B → CStarTensorProduct N`. -/
def of : A ⊗[ℂ] B →⋆ₙₐ[ℂ] CStarTensorProduct N where
  toFun x := (equiv N x : Completion (CStarTensorAlgebra N))
  map_smul' c x := by
    rw [map_smul]
    exact Completion.coe_smul c _
  map_zero' := by
    rw [map_zero]
    exact Completion.coe_zero
  map_add' x y := by
    rw [map_add]
    exact Completion.coe_add _ _
  map_mul' x y := by
    rw [map_mul]
    exact Completion.coe_mul' _ _
  map_star' x := by
    rw [map_star]
    exact Completion.coe_star _

variable {N}

/-- The image of `x` under the completion map of `TauCeti.CStarTensorAlgebra N` is `of N x`. -/
@[simp]
theorem coe_equiv_eq_of (x : A ⊗[ℂ] B) :
    ((equiv N x : Completion (CStarTensorAlgebra N)) : CStarTensorProduct N) = of N x :=
  (rfl)

/-- The norm of the image of `x` in `CStarTensorProduct N` is `N x`. -/
@[simp]
theorem norm_of (x : A ⊗[ℂ] B) : ‖of N x‖ = N x :=
  Completion.norm_coe (equiv N x)

/-- The canonical map `A ⊗[ℂ] B → CStarTensorProduct N` is injective. -/
theorem of_injective : Function.Injective (of N) :=
  (injective_iff_map_eq_zero (of N)).2 fun x hx ↦
    eq_zero_of_map_eq_zero N ((norm_of x).symm.trans (by rw [hx, norm_zero]))

/-- `A ⊗[ℂ] B` is dense in `CStarTensorProduct N`. -/
theorem denseRange_of : DenseRange (of N) :=
  Completion.denseRange_coe.comp (equiv N).surjective.denseRange (Completion.continuous_coe _)

/-- To prove a closed property of every element of `CStarTensorProduct N`, it suffices to prove
it on `A ⊗[ℂ] B`. -/
@[elab_as_elim]
theorem induction_on {p : CStarTensorProduct N → Prop} (x : CStarTensorProduct N)
    (hp : IsClosed {x | p x}) (ih : ∀ x, p (of N x)) : p x :=
  Completion.induction_on (p := p) x hp fun y ↦ by
    have h := ih ((equiv N).symm y)
    rwa [← coe_equiv_eq_of, StarAlgEquiv.apply_symm_apply] at h

/-- Star homomorphisms from `CStarTensorProduct N` into a C*-algebra are determined by their
values on the elementary tensors `a ⊗ b`. -/
@[ext]
theorem starAlgHom_ext {C : Type*} [NonUnitalCStarAlgebra C]
    {φ ψ : CStarTensorProduct N →⋆ₙₐ[ℂ] C} (h : ∀ a b, φ (of N (a ⊗ₜ b)) = ψ (of N (a ⊗ₜ b))) :
    φ = ψ := by
  refine NonUnitalStarAlgHom.ext fun x ↦ induction_on x (isClosed_eq (map_continuous φ)
    (map_continuous ψ)) fun x ↦ ?_
  induction x using TensorProduct.inductionOn with
  | tmul a b => exact h a b
  | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]

/-- A star homomorphism `A ⊗[ℂ] B → C` into a C*-algebra that is bounded by `N` extends to
`CStarTensorProduct N`. -/
def extend {C : Type*} [NonUnitalCStarAlgebra C] (f : A ⊗[ℂ] B →⋆ₙₐ[ℂ] C)
    (hf : ∀ x, ‖f x‖ ≤ N x) : CStarTensorProduct N →⋆ₙₐ[ℂ] C :=
  (f.comp (equiv N).symm.toNonUnitalStarAlgHom).fromCompletion <|
    AddMonoidHomClass.continuous_of_bound _ 1 fun x ↦ by
      simpa [norm_def] using hf ((equiv N).symm x)

/-- On `A ⊗[ℂ] B`, the extension of `f` is `f`. -/
@[simp]
theorem extend_of {C : Type*} [NonUnitalCStarAlgebra C] (f : A ⊗[ℂ] B →⋆ₙₐ[ℂ] C)
    (hf : ∀ x, ‖f x‖ ≤ N x) (x : A ⊗[ℂ] B) : extend f hf (of N x) = f x := by
  rw [← coe_equiv_eq_of]
  -- `extend f hf` is by definition the extension from the completion of `CStarTensorAlgebra N`.
  exact (NonUnitalStarAlgHom.fromCompletion_apply_coe _ _ (equiv N x)).trans (by simp)

/-- If `f` preserves `N`, its extension to `CStarTensorProduct N` is isometric. -/
theorem norm_extend {C : Type*} [NonUnitalCStarAlgebra C] (f : A ⊗[ℂ] B →⋆ₙₐ[ℂ] C)
    (hf : ∀ x, ‖f x‖ = N x) (u : CStarTensorProduct N) :
    ‖extend f (fun x ↦ (hf x).le) u‖ = ‖u‖ :=
  induction_on u (isClosed_eq (continuous_norm.comp (map_continuous _)) continuous_norm)
    fun x ↦ by rw [extend_of, norm_of, hf]

end CStarTensorProduct

end TauCeti
