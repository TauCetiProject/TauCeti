/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Spectrum
public import TauCeti.Analysis.CStarAlgebra.MaxTensor.Norm
public import TauCeti.Analysis.CStarAlgebra.Completion
public import TauCeti.Analysis.Normed.Ring.Completion

/-!
# The maximal C*-tensor product

Let `A` and `B` be (possibly non-unital) C*-algebras. The algebraic tensor product
`A ⊗[ℂ] B` with the maximal C*-norm `TauCeti.maxTensorNorm` is a normed star algebra satisfying
the C*-identity (`TauCeti.MaxTensorAlgebra A B`, a type synonym of `A ⊗[ℂ] B`). Its completion is
the **maximal tensor product** `TauCeti.MaxTensorProduct A B` (written A ⊗max B in the
literature; this file declares no notation for it), a C*-algebra, with the star homomorphism
`TauCeti.MaxTensorProduct.of : A ⊗[ℂ] B → TauCeti.MaxTensorProduct A B`, which is injective,
isometric for the maximal norm and has dense range.

**Universal property.** Commuting star homomorphisms `φ : A → C` and `ψ : B → C` into a
C*-algebra `C` in the universe `max u v` integrate to a star homomorphism `a ⊗ b ↦ φ a * ψ b` on
`A ⊗[ℂ] B` bounded by the maximal norm (`TauCeti.norm_liftNonUnitalStarAlgHom_le_maxTensorNorm`),
which extends uniquely to `TauCeti.MaxTensorProduct A B` (`TauCeti.MaxTensorProduct.lift`, with
`TauCeti.MaxTensorProduct.lift_of_tmul` and the uniqueness
`TauCeti.MaxTensorProduct.starAlgHom_ext`).
In particular every commuting pair of representations of `A` and `B` integrates to a
representation of `TauCeti.MaxTensorProduct A B`
(`TauCeti.CommutingRepresentationPair.maxTensorHom`).

## Main declarations

* `TauCeti.MaxTensorAlgebra A B`: `A ⊗[ℂ] B` with the maximal norm.
* `TauCeti.MaxTensorProduct A B`: its completion, a C*-algebra.
* `TauCeti.MaxTensorProduct.of`, `TauCeti.MaxTensorProduct.norm_of`,
  `TauCeti.MaxTensorProduct.of_injective`, `TauCeti.MaxTensorProduct.denseRange_of`.
* `TauCeti.MaxTensorProduct.lift`: the universal property.

## References

* B. Blackadar, *Operator Algebras: Theory of C*-Algebras and von Neumann Algebras*,
  II.9.2.1–II.9.2.3.
-/

public section

noncomputable section

open UniformSpace TensorProduct

universe u v

namespace TauCeti

variable (A : Type u) (B : Type v) [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]

/-- The algebraic tensor product `A ⊗[ℂ] B` with the maximal C*-norm `TauCeti.maxTensorNorm`.
Its completion is the maximal tensor product `TauCeti.MaxTensorProduct A B`. Use
`TauCeti.MaxTensorAlgebra.toMax` and `TauCeti.MaxTensorAlgebra.ofMax` to pass to and from
`A ⊗[ℂ] B`. -/
@[expose] def MaxTensorAlgebra : Type (max u v) :=
  A ⊗[ℂ] B

namespace MaxTensorAlgebra

variable {A B}

/-- Regard an element of `A ⊗[ℂ] B` as an element with the maximal norm. -/
def toMax : A ⊗[ℂ] B ≃ MaxTensorAlgebra A B :=
  Equiv.refl _

/-- The element of `A ⊗[ℂ] B` underlying an element with the maximal norm. -/
def ofMax : MaxTensorAlgebra A B ≃ A ⊗[ℂ] B :=
  Equiv.refl _

@[simp]
theorem toMax_symm : (toMax (A := A) (B := B)).symm = ofMax :=
  (rfl)

@[simp]
theorem ofMax_symm : (ofMax (A := A) (B := B)).symm = toMax :=
  (rfl)

@[simp]
theorem ofMax_toMax (x : A ⊗[ℂ] B) : ofMax (toMax x) = x :=
  (rfl)

@[simp]
theorem toMax_ofMax (x : MaxTensorAlgebra A B) : toMax (ofMax x) = x :=
  (rfl)

instance : NonUnitalRing (MaxTensorAlgebra A B) :=
  inferInstanceAs (NonUnitalRing (A ⊗[ℂ] B))

instance : Module ℂ (MaxTensorAlgebra A B) :=
  inferInstanceAs (Module ℂ (A ⊗[ℂ] B))

instance : IsScalarTower ℂ (MaxTensorAlgebra A B) (MaxTensorAlgebra A B) :=
  inferInstanceAs (IsScalarTower ℂ (A ⊗[ℂ] B) (A ⊗[ℂ] B))

instance : SMulCommClass ℂ (MaxTensorAlgebra A B) (MaxTensorAlgebra A B) :=
  inferInstanceAs (SMulCommClass ℂ (A ⊗[ℂ] B) (A ⊗[ℂ] B))

instance : StarRing (MaxTensorAlgebra A B) :=
  inferInstanceAs (StarRing (A ⊗[ℂ] B))

instance : StarModule ℂ (MaxTensorAlgebra A B) :=
  inferInstanceAs (StarModule ℂ (A ⊗[ℂ] B))

@[simp]
theorem toMax_zero : toMax (0 : A ⊗[ℂ] B) = 0 :=
  (rfl)

@[simp]
theorem toMax_add (x y : A ⊗[ℂ] B) : toMax (x + y) = toMax x + toMax y :=
  (rfl)

@[simp]
theorem toMax_neg (x : A ⊗[ℂ] B) : toMax (-x) = -toMax x :=
  (rfl)

@[simp]
theorem toMax_sub (x y : A ⊗[ℂ] B) : toMax (x - y) = toMax x - toMax y :=
  (rfl)

@[simp]
theorem toMax_mul (x y : A ⊗[ℂ] B) : toMax (x * y) = toMax x * toMax y :=
  (rfl)

@[simp]
theorem toMax_smul (c : ℂ) (x : A ⊗[ℂ] B) : toMax (c • x) = c • toMax x :=
  (rfl)

@[simp]
theorem toMax_star (x : A ⊗[ℂ] B) : toMax (star x) = star (toMax x) :=
  (rfl)

@[simp]
theorem ofMax_zero : ofMax (0 : MaxTensorAlgebra A B) = 0 :=
  (rfl)

@[simp]
theorem ofMax_add (x y : MaxTensorAlgebra A B) : ofMax (x + y) = ofMax x + ofMax y :=
  (rfl)

@[simp]
theorem ofMax_neg (x : MaxTensorAlgebra A B) : ofMax (-x) = -ofMax x :=
  (rfl)

@[simp]
theorem ofMax_sub (x y : MaxTensorAlgebra A B) : ofMax (x - y) = ofMax x - ofMax y :=
  (rfl)

@[simp]
theorem ofMax_smul (c : ℂ) (x : MaxTensorAlgebra A B) : ofMax (c • x) = c • ofMax x :=
  (rfl)

@[simp]
theorem ofMax_mul (x y : MaxTensorAlgebra A B) : ofMax (x * y) = ofMax x * ofMax y :=
  (rfl)

@[simp]
theorem ofMax_star (x : MaxTensorAlgebra A B) : ofMax (star x) = star (ofMax x) :=
  (rfl)

variable (A B) in
/-- `TauCeti.MaxTensorAlgebra.toMax` as an isomorphism of star algebras. -/
def toMaxStarAlgEquiv : A ⊗[ℂ] B ≃⋆ₐ[ℂ] MaxTensorAlgebra A B where
  __ := toMax
  map_mul' _ _ := (rfl)
  map_add' _ _ := (rfl)
  map_smul' _ _ := (rfl)
  map_star' _ := (rfl)

@[simp]
theorem toMaxStarAlgEquiv_apply (x : A ⊗[ℂ] B) : toMaxStarAlgEquiv A B x = toMax x :=
  (rfl)

@[simp]
theorem toMaxStarAlgEquiv_symm_apply (x : MaxTensorAlgebra A B) :
    (toMaxStarAlgEquiv A B).symm x = ofMax x :=
  (rfl)

variable (A B) in
/-- The maximal norm as an additive group norm on `A ⊗[ℂ] B`. -/
def maxTensorAddGroupNorm : AddGroupNorm (A ⊗[ℂ] B) where
  toFun := maxTensorNorm A B
  map_zero' := maxTensorNorm_zero
  add_le' := maxTensorNorm_add_le
  neg' := maxTensorNorm_neg
  eq_zero_of_map_eq_zero' _ := maxTensorNorm_eq_zero_iff.1

/-- The maximal norm makes `A ⊗[ℂ] B` a normed group. -/
instance : NormedAddCommGroup (MaxTensorAlgebra A B) :=
  @AddGroupNorm.toNormedAddCommGroup (MaxTensorAlgebra A B) _ (maxTensorAddGroupNorm A B)

/-- The norm of an element of `TauCeti.MaxTensorAlgebra A B` is the maximal norm of the underlying
element of `A ⊗[ℂ] B`. -/
theorem norm_def (x : MaxTensorAlgebra A B) : ‖x‖ = maxTensorNorm A B (ofMax x) :=
  (rfl)

@[simp]
theorem norm_toMax (x : A ⊗[ℂ] B) : ‖toMax x‖ = maxTensorNorm A B x :=
  (rfl)

instance : NormedSpace ℂ (MaxTensorAlgebra A B) where
  __ : Module ℂ (MaxTensorAlgebra A B) := inferInstance
  norm_smul_le c x := by
    rw [norm_def, norm_def, ofMax_smul]
    exact (maxTensorNorm_smul c (ofMax x)).le

/-- The maximal norm is submultiplicative, so `TauCeti.MaxTensorAlgebra A B` is a normed ring. -/
instance : NonUnitalNormedRing (MaxTensorAlgebra A B) where
  __ : NormedAddCommGroup (MaxTensorAlgebra A B) := inferInstance
  __ : NonUnitalRing (MaxTensorAlgebra A B) := inferInstance
  norm_mul_le x y := by
    rw [norm_def, norm_def, norm_def, ofMax_mul]
    exact maxTensorNorm_mul_le (ofMax x) (ofMax y)

/-- The star operation is isometric for the maximal norm. -/
instance : NormedStarGroup (MaxTensorAlgebra A B) where
  norm_star_le x := by
    rw [norm_def, norm_def, ofMax_star]
    exact (maxTensorNorm_star (ofMax x)).le

/-- The maximal norm satisfies the C*-identity. -/
instance : CStarRing (MaxTensorAlgebra A B) where
  norm_mul_self_le x := by
    rw [norm_def, norm_def, ← sq, ← maxTensorNorm_star_mul_self]
    exact le_rfl

end MaxTensorAlgebra

open MaxTensorAlgebra

/-- The **maximal tensor product** of C*-algebras `A` and `B`: the completion of the
algebraic tensor product `A ⊗[ℂ] B` in the maximal C*-norm. It is a C*-algebra, and the
canonical map `TauCeti.MaxTensorProduct.of` from `A ⊗[ℂ] B` is injective and isometric with
dense range. -/
@[expose] def MaxTensorProduct : Type (max u v) :=
  Completion (MaxTensorAlgebra A B)

namespace MaxTensorProduct

/-- The completion of `A ⊗[ℂ] B` in the maximal norm is a C*-algebra. -/
instance : NonUnitalCStarAlgebra (Completion (MaxTensorAlgebra A B)) where
  toCStarRing := Completion.cstarRing fun x ↦ (CStarRing.norm_star_mul_self (x := x)).ge

/-- The maximal tensor product is a C*-algebra. -/
instance : NonUnitalCStarAlgebra (MaxTensorProduct A B) :=
  inferInstanceAs (NonUnitalCStarAlgebra (Completion (MaxTensorAlgebra A B)))

/-- The canonical star homomorphism `A ⊗[ℂ] B → MaxTensorProduct A B`. -/
def of : A ⊗[ℂ] B →⋆ₙₐ[ℂ] MaxTensorProduct A B :=
  (Completion.coeNonUnitalStarAlgHom ℂ).comp (toMaxStarAlgEquiv A B).toNonUnitalStarAlgHom

variable {A B}

/-- The image of `x` under the completion map of `TauCeti.MaxTensorAlgebra A B` is `of A B x`. -/
@[simp]
theorem coe_toMax_eq_of (x : A ⊗[ℂ] B) :
    ((toMax x : Completion (MaxTensorAlgebra A B)) : MaxTensorProduct A B) = of A B x :=
  (congrFun (Completion.coe_coeNonUnitalStarAlgHom ℂ) (toMax x)).symm

/-- The norm of the image of `x` in `MaxTensorProduct A B` is its maximal norm. -/
@[simp]
theorem norm_of (x : A ⊗[ℂ] B) : ‖of A B x‖ = maxTensorNorm A B x := by
  rw [← coe_toMax_eq_of]
  exact Completion.norm_coe (toMax x)

/-- `‖a ⊗ b‖ = ‖a‖ ‖b‖` in `MaxTensorProduct A B`. -/
theorem norm_of_tmul (a : A) (b : B) : ‖of A B (a ⊗ₜ b)‖ = ‖a‖ * ‖b‖ := by
  rw [norm_of, maxTensorNorm_tmul]

/-- The canonical map `A ⊗[ℂ] B → MaxTensorProduct A B` is injective. -/
theorem of_injective : Function.Injective (of A B) :=
  (injective_iff_map_eq_zero (of A B)).2 fun x hx ↦
    maxTensorNorm_eq_zero_iff.1 (by rw [← norm_of, hx, norm_zero])

/-- `A ⊗[ℂ] B` is dense in `MaxTensorProduct A B`. -/
theorem denseRange_of : DenseRange (of A B) := by
  rw [show ⇑(of A B) =
      fun x ↦ ((toMax x : Completion (MaxTensorAlgebra A B)) : MaxTensorProduct A B) from
    funext fun x ↦ (coe_toMax_eq_of x).symm]
  exact Completion.denseRange_coe.comp toMax.surjective.denseRange (Completion.continuous_coe _)

/-- To prove a closed property of every element of `MaxTensorProduct A B`, it suffices to prove
it on `A ⊗[ℂ] B`. -/
@[elab_as_elim]
theorem induction_on {p : MaxTensorProduct A B → Prop} (x : MaxTensorProduct A B)
    (hp : IsClosed {x | p x}) (ih : ∀ x, p (of A B x)) : p x :=
  Completion.induction_on (p := p) x hp fun y ↦ by
    have h := ih (ofMax y)
    rwa [← coe_toMax_eq_of, toMax_ofMax] at h

open scoped _root_.CStarAlgebra in
/-- Star homomorphisms from `MaxTensorProduct A B` into a C*-algebra are determined by their
values on the elementary tensors `a ⊗ b`. -/
@[ext]
theorem starAlgHom_ext {C : Type*} [NonUnitalCStarAlgebra C]
    {φ ψ : MaxTensorProduct A B →⋆ₙₐ[ℂ] C} (h : ∀ a b, φ (of A B (a ⊗ₜ b)) = ψ (of A B (a ⊗ₜ b))) :
    φ = ψ := by
  refine NonUnitalStarAlgHom.ext fun x ↦ induction_on x (isClosed_eq (map_continuous φ)
    (map_continuous ψ)) fun x ↦ ?_
  induction x using TensorProduct.inductionOn with
  | tmul a b => exact h a b
  | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]

variable {C : Type (max u v)} [NonUnitalCStarAlgebra C] (φ : A →⋆ₙₐ[ℂ] C) (ψ : B →⋆ₙₐ[ℂ] C)
  (h : ∀ a b, Commute (φ a) (ψ b))

/-- **The universal property of `MaxTensorProduct A B`.** Commuting star homomorphisms
`φ : A → C` and `ψ : B → C` into a C*-algebra `C` in the universe `max u v` extend to the star
homomorphism `MaxTensorProduct A B → C` sending `a ⊗ b` to `φ a * ψ b`
(`TauCeti.MaxTensorProduct.lift_of_tmul`); it is unique by
`TauCeti.MaxTensorProduct.starAlgHom_ext`. -/
def lift : MaxTensorProduct A B →⋆ₙₐ[ℂ] C :=
  ((Algebra.TensorProduct.liftNonUnitalStarAlgHom φ ψ h).comp
    (toMaxStarAlgEquiv A B).symm.toNonUnitalStarAlgHom).fromCompletion <|
    AddMonoidHomClass.continuous_of_bound _ 1 fun x ↦ by
      simpa [norm_def] using norm_liftNonUnitalStarAlgHom_le_maxTensorNorm φ ψ h (ofMax x)

/-- On `A ⊗[ℂ] B`, the extension is the integrated form `a ⊗ b ↦ φ a * ψ b`. -/
@[simp]
theorem lift_of (x : A ⊗[ℂ] B) :
    lift φ ψ h (of A B x) = Algebra.TensorProduct.liftNonUnitalStarAlgHom φ ψ h x := by
  rw [← coe_toMax_eq_of]
  -- `lift φ ψ h` is by definition the extension from the completion of `MaxTensorAlgebra A B`.
  exact (NonUnitalStarAlgHom.fromCompletion_apply_coe _ _ (toMax x)).trans (by simp)

/-- The extension sends `a ⊗ b` to `φ a * ψ b`. -/
theorem lift_of_tmul (a : A) (b : B) : lift φ ψ h (of A B (a ⊗ₜ b)) = φ a * ψ b := by
  rw [lift_of, Algebra.TensorProduct.liftNonUnitalStarAlgHom_tmul]

/-- Composing the extension with the canonical map recovers the integrated form. -/
@[simp]
theorem lift_comp_of :
    (lift φ ψ h).comp (of A B) = Algebra.TensorProduct.liftNonUnitalStarAlgHom φ ψ h :=
  NonUnitalStarAlgHom.ext (lift_of φ ψ h)

end MaxTensorProduct

namespace CommutingRepresentationPair

open MaxTensorProduct

variable {A B}

/-- The representation of `MaxTensorProduct A B` integrating a commuting pair of representations
of `A` and `B`, `a ⊗ b ↦ π a * ρ b`. -/
def maxTensorHom (p : CommutingRepresentationPair A B) :
    MaxTensorProduct A B →⋆ₙₐ[ℂ] (p.H →L[ℂ] p.H) :=
  lift p.left p.right p.commute

/-- On `A ⊗[ℂ] B`, the representation of `MaxTensorProduct A B` is the integrated form of the
pair. -/
@[simp]
theorem maxTensorHom_of (p : CommutingRepresentationPair A B) (x : A ⊗[ℂ] B) :
    p.maxTensorHom (of A B x) = p.tensorHom x := by
  rw [maxTensorHom, lift_of, tensorHom_def]

end CommutingRepresentationPair

end TauCeti
