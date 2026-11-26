/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.MinTensorNorm
public import TauCeti.Analysis.CStarAlgebra.MaxTensor.Product
public import TauCeti.Analysis.CStarAlgebra.Completion
public import TauCeti.Analysis.Normed.Ring.Completion
import TauCeti.Analysis.CStarAlgebra.Quotient

/-!
# The minimal C*-tensor product

Let `A` and `B` be (possibly non-unital) C*-algebras. The algebraic tensor product
`A ⊗[ℂ] B` with the minimal C*-norm `TauCeti.minTensorNorm` is a normed star algebra satisfying
the C*-identity (`TauCeti.MinTensorAlgebra A B`, a type synonym of `A ⊗[ℂ] B`). Its completion is
the **minimal tensor product** `TauCeti.MinTensorProduct A B` (written A ⊗min B in the
literature; this file declares no notation for it), a C*-algebra, with the star homomorphism
`TauCeti.MinTensorProduct.of : A ⊗[ℂ] B → TauCeti.MinTensorProduct A B`, which is injective,
isometric for the minimal norm and has dense range.

**Spatial realization.** Representations `π : A → B(E)` and `ρ : B → B(F)` give the spatial
tensor homomorphism `a ⊗ b ↦ π a ⊗ ρ b` into `B(E ⊗₂ F)`, which is bounded by the minimal norm
and so extends to `TauCeti.MinTensorProduct.spatialTensorHom π ρ`. For faithful `π` and `ρ` it is
isometric (`TauCeti.MinTensorProduct.norm_spatialTensorHom`), by representation independence of
the spatial norm (`TauCeti.minTensorNorm_eq_norm_spatialTensorHom`). For closed concrete operator
algebras `A ⊆ B(E)` and `B ⊆ B(F)`, the minimal tensor product is isomorphic to the spatial
tensor product `NonUnitalStarSubalgebra.minTensor A B`, the closure of the image of `A ⊗[ℂ] B` in
`B(E ⊗₂ F)` (`NonUnitalStarSubalgebra.minTensorProductEquiv`).

**Functoriality.** Star homomorphisms `φ : A → A'` and `ψ : B → B'` give the star homomorphism
`TauCeti.MinTensorProduct.map φ ψ` extending `φ ⊗ ψ`, which is isometric, hence injective, when
`φ` and `ψ` are injective (`TauCeti.MinTensorProduct.norm_map`,
`TauCeti.MinTensorProduct.map_injective`).

**Comparison with the maximal tensor product.** Since `‖·‖_min ≤ ‖·‖_max`, the identity of
`A ⊗[ℂ] B` extends to the canonical star homomorphism
`TauCeti.MaxTensorProduct.toMin : TauCeti.MaxTensorProduct A B → TauCeti.MinTensorProduct A B`,
which is surjective (`TauCeti.MaxTensorProduct.toMin_surjective`): its range is closed, as for
every star homomorphism of C*-algebras, and dense.

## Main declarations

* `TauCeti.MinTensorAlgebra A B`: `A ⊗[ℂ] B` with the minimal norm.
* `TauCeti.MinTensorProduct A B`: its completion, a C*-algebra.
* `TauCeti.MinTensorProduct.of`, `TauCeti.MinTensorProduct.norm_of`,
  `TauCeti.MinTensorProduct.of_injective`, `TauCeti.MinTensorProduct.denseRange_of`.
* `TauCeti.MinTensorProduct.spatialTensorHom`: the spatial realization, isometric for faithful
  representations.
* `NonUnitalStarSubalgebra.minTensorProductEquiv`: `A ⊗min B ≃ A ⊗_min B` for closed concrete
  operator algebras.
* `TauCeti.MinTensorProduct.map`: functoriality.
* `TauCeti.MaxTensorProduct.toMin`: the canonical surjection `A ⊗max B → A ⊗min B`.

## References

* B. Blackadar, *Operator Algebras: Theory of C*-Algebras and von Neumann Algebras*,
  II.9.2.1–II.9.2.6.
* M. Takesaki, *Theory of Operator Algebras I*, Chapter IV, §4.
-/

public section

noncomputable section

open UniformSpace TensorProduct

universe u v

namespace TauCeti

variable (A : Type u) (B : Type v) [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]

/-- The algebraic tensor product `A ⊗[ℂ] B` with the minimal C*-norm `TauCeti.minTensorNorm`.
Its completion is the minimal tensor product `TauCeti.MinTensorProduct A B`. Use
`TauCeti.MinTensorAlgebra.toMin` and `TauCeti.MinTensorAlgebra.ofMin` to pass to and from
`A ⊗[ℂ] B`. -/
@[expose] def MinTensorAlgebra : Type (max u v) :=
  A ⊗[ℂ] B

namespace MinTensorAlgebra

variable {A B}

/-- Regard an element of `A ⊗[ℂ] B` as an element with the minimal norm. -/
def toMin : A ⊗[ℂ] B ≃ MinTensorAlgebra A B :=
  Equiv.refl _

/-- The element of `A ⊗[ℂ] B` underlying an element with the minimal norm. -/
def ofMin : MinTensorAlgebra A B ≃ A ⊗[ℂ] B :=
  Equiv.refl _

@[simp]
theorem toMin_symm : (toMin (A := A) (B := B)).symm = ofMin :=
  (rfl)

@[simp]
theorem ofMin_symm : (ofMin (A := A) (B := B)).symm = toMin :=
  (rfl)

@[simp]
theorem ofMin_toMin (x : A ⊗[ℂ] B) : ofMin (toMin x) = x :=
  (rfl)

@[simp]
theorem toMin_ofMin (x : MinTensorAlgebra A B) : toMin (ofMin x) = x :=
  (rfl)

instance : NonUnitalRing (MinTensorAlgebra A B) :=
  inferInstanceAs (NonUnitalRing (A ⊗[ℂ] B))

instance : Module ℂ (MinTensorAlgebra A B) :=
  inferInstanceAs (Module ℂ (A ⊗[ℂ] B))

instance : IsScalarTower ℂ (MinTensorAlgebra A B) (MinTensorAlgebra A B) :=
  inferInstanceAs (IsScalarTower ℂ (A ⊗[ℂ] B) (A ⊗[ℂ] B))

instance : SMulCommClass ℂ (MinTensorAlgebra A B) (MinTensorAlgebra A B) :=
  inferInstanceAs (SMulCommClass ℂ (A ⊗[ℂ] B) (A ⊗[ℂ] B))

instance : StarRing (MinTensorAlgebra A B) :=
  inferInstanceAs (StarRing (A ⊗[ℂ] B))

instance : StarModule ℂ (MinTensorAlgebra A B) :=
  inferInstanceAs (StarModule ℂ (A ⊗[ℂ] B))

@[simp]
theorem ofMin_zero : ofMin (0 : MinTensorAlgebra A B) = 0 :=
  (rfl)

@[simp]
theorem ofMin_add (x y : MinTensorAlgebra A B) : ofMin (x + y) = ofMin x + ofMin y :=
  (rfl)

@[simp]
theorem ofMin_neg (x : MinTensorAlgebra A B) : ofMin (-x) = -ofMin x :=
  (rfl)

@[simp]
theorem ofMin_sub (x y : MinTensorAlgebra A B) : ofMin (x - y) = ofMin x - ofMin y :=
  (rfl)

@[simp]
theorem ofMin_smul (c : ℂ) (x : MinTensorAlgebra A B) : ofMin (c • x) = c • ofMin x :=
  (rfl)

@[simp]
theorem ofMin_mul (x y : MinTensorAlgebra A B) : ofMin (x * y) = ofMin x * ofMin y :=
  (rfl)

@[simp]
theorem ofMin_star (x : MinTensorAlgebra A B) : ofMin (star x) = star (ofMin x) :=
  (rfl)

variable (A B) in
/-- `TauCeti.MinTensorAlgebra.toMin` as an isomorphism of star algebras. -/
def toMinStarAlgEquiv : A ⊗[ℂ] B ≃⋆ₐ[ℂ] MinTensorAlgebra A B where
  __ := toMin
  map_mul' _ _ := (rfl)
  map_add' _ _ := (rfl)
  map_smul' _ _ := (rfl)
  map_star' _ := (rfl)

@[simp]
theorem toMinStarAlgEquiv_apply (x : A ⊗[ℂ] B) : toMinStarAlgEquiv A B x = toMin x :=
  (rfl)

@[simp]
theorem toMinStarAlgEquiv_symm_apply (x : MinTensorAlgebra A B) :
    (toMinStarAlgEquiv A B).symm x = ofMin x :=
  (rfl)

variable (A B) in
/-- The minimal norm as an additive group norm on `A ⊗[ℂ] B`. -/
def minTensorAddGroupNorm : AddGroupNorm (A ⊗[ℂ] B) where
  toFun := minTensorNorm A B
  map_zero' := minTensorNorm_zero
  add_le' := minTensorNorm_add_le
  neg' := minTensorNorm_neg
  eq_zero_of_map_eq_zero' _ := minTensorNorm_eq_zero_iff.1

/-- The minimal norm makes `A ⊗[ℂ] B` a normed group. -/
instance : NormedAddCommGroup (MinTensorAlgebra A B) :=
  @AddGroupNorm.toNormedAddCommGroup (MinTensorAlgebra A B) _ (minTensorAddGroupNorm A B)

/-- The norm of an element of `TauCeti.MinTensorAlgebra A B` is the minimal norm of the underlying
element of `A ⊗[ℂ] B`. -/
theorem norm_def (x : MinTensorAlgebra A B) : ‖x‖ = minTensorNorm A B (ofMin x) :=
  (rfl)

@[simp]
theorem norm_toMin (x : A ⊗[ℂ] B) : ‖toMin x‖ = minTensorNorm A B x :=
  (rfl)

instance : NormedSpace ℂ (MinTensorAlgebra A B) where
  __ : Module ℂ (MinTensorAlgebra A B) := inferInstance
  norm_smul_le c x := by
    rw [norm_def, norm_def, ofMin_smul]
    exact (minTensorNorm_smul c (ofMin x)).le

/-- The minimal norm is submultiplicative, so `TauCeti.MinTensorAlgebra A B` is a normed ring. -/
instance : NonUnitalNormedRing (MinTensorAlgebra A B) where
  __ : NormedAddCommGroup (MinTensorAlgebra A B) := inferInstance
  __ : NonUnitalRing (MinTensorAlgebra A B) := inferInstance
  norm_mul_le x y := by
    rw [norm_def, norm_def, norm_def, ofMin_mul]
    exact minTensorNorm_mul_le (ofMin x) (ofMin y)

/-- The star operation is isometric for the minimal norm. -/
instance : NormedStarGroup (MinTensorAlgebra A B) where
  norm_star_le x := by
    rw [norm_def, norm_def, ofMin_star]
    exact (minTensorNorm_star (ofMin x)).le

/-- The minimal norm satisfies the C*-identity. -/
instance : CStarRing (MinTensorAlgebra A B) where
  norm_mul_self_le x := by
    rw [norm_def, norm_def, ← sq, ← minTensorNorm_star_mul_self]
    exact le_rfl

end MinTensorAlgebra

open MinTensorAlgebra

/-- The **minimal tensor product** of C*-algebras `A` and `B`: the completion of the
algebraic tensor product `A ⊗[ℂ] B` in the minimal C*-norm. It is a C*-algebra, and the
canonical map `TauCeti.MinTensorProduct.of` from `A ⊗[ℂ] B` is injective and isometric with
dense range. -/
@[expose] def MinTensorProduct : Type (max u v) :=
  Completion (MinTensorAlgebra A B)

namespace MinTensorProduct

open scoped _root_.CStarAlgebra

/-- The completion of `A ⊗[ℂ] B` in the minimal norm is a C*-algebra. -/
instance : NonUnitalCStarAlgebra (Completion (MinTensorAlgebra A B)) where
  toCStarRing := Completion.cstarRing fun x ↦ (CStarRing.norm_star_mul_self (x := x)).ge

/-- The minimal tensor product is a C*-algebra. -/
instance : NonUnitalCStarAlgebra (MinTensorProduct A B) :=
  inferInstanceAs (NonUnitalCStarAlgebra (Completion (MinTensorAlgebra A B)))

/-- The canonical star homomorphism `A ⊗[ℂ] B → MinTensorProduct A B`. -/
def of : A ⊗[ℂ] B →⋆ₙₐ[ℂ] MinTensorProduct A B where
  toFun x := (toMinStarAlgEquiv A B x : Completion (MinTensorAlgebra A B))
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

variable {A B}

/-- The image of `x` under the completion map of `TauCeti.MinTensorAlgebra A B` is `of A B x`. -/
@[simp]
theorem coe_toMin_eq_of (x : A ⊗[ℂ] B) :
    ((toMin x : Completion (MinTensorAlgebra A B)) : MinTensorProduct A B) = of A B x :=
  (rfl)

/-- The norm of the image of `x` in `MinTensorProduct A B` is its minimal norm. -/
@[simp]
theorem norm_of (x : A ⊗[ℂ] B) : ‖of A B x‖ = minTensorNorm A B x :=
  Completion.norm_coe (toMin x)

/-- `‖a ⊗ b‖ = ‖a‖ ‖b‖` in `MinTensorProduct A B`. -/
theorem norm_of_tmul (a : A) (b : B) : ‖of A B (a ⊗ₜ b)‖ = ‖a‖ * ‖b‖ := by
  rw [norm_of, minTensorNorm_tmul]

/-- The canonical map `A ⊗[ℂ] B → MinTensorProduct A B` is injective. -/
theorem of_injective : Function.Injective (of A B) :=
  (injective_iff_map_eq_zero (of A B)).2 fun x hx ↦
    minTensorNorm_eq_zero_iff.1 (by rw [← norm_of, hx, norm_zero])

/-- `A ⊗[ℂ] B` is dense in `MinTensorProduct A B`. -/
theorem denseRange_of : DenseRange (of A B) :=
  Completion.denseRange_coe.comp toMin.surjective.denseRange (Completion.continuous_coe _)

/-- To prove a closed property of every element of `MinTensorProduct A B`, it suffices to prove
it on `A ⊗[ℂ] B`. -/
@[elab_as_elim]
theorem induction_on {p : MinTensorProduct A B → Prop} (x : MinTensorProduct A B)
    (hp : IsClosed {x | p x}) (ih : ∀ x, p (of A B x)) : p x :=
  Completion.induction_on (p := p) x hp fun y ↦ by
    have h := ih (ofMin y)
    rwa [← coe_toMin_eq_of, toMin_ofMin] at h

/-- Star homomorphisms from `MinTensorProduct A B` into a C*-algebra are determined by their
values on the elementary tensors `a ⊗ b`. -/
@[ext]
theorem starAlgHom_ext {C : Type*} [NonUnitalCStarAlgebra C]
    {φ ψ : MinTensorProduct A B →⋆ₙₐ[ℂ] C} (h : ∀ a b, φ (of A B (a ⊗ₜ b)) = ψ (of A B (a ⊗ₜ b))) :
    φ = ψ := by
  refine NonUnitalStarAlgHom.ext fun x ↦ induction_on x (isClosed_eq (map_continuous φ)
    (map_continuous ψ)) fun x ↦ ?_
  induction x using TensorProduct.inductionOn with
  | tmul a b => exact h a b
  | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]

/-- A star homomorphism `A ⊗[ℂ] B → C` into a C*-algebra that is bounded by the minimal norm
extends to `MinTensorProduct A B`. -/
def extend {C : Type*} [NonUnitalCStarAlgebra C] (f : A ⊗[ℂ] B →⋆ₙₐ[ℂ] C)
    (hf : ∀ x, ‖f x‖ ≤ minTensorNorm A B x) : MinTensorProduct A B →⋆ₙₐ[ℂ] C :=
  (f.comp (toMinStarAlgEquiv A B).symm.toNonUnitalStarAlgHom).fromCompletion <|
    AddMonoidHomClass.continuous_of_bound _ 1 fun x ↦ by
      simpa [norm_def] using hf (ofMin x)

@[simp]
theorem extend_of {C : Type*} [NonUnitalCStarAlgebra C] (f : A ⊗[ℂ] B →⋆ₙₐ[ℂ] C)
    (hf : ∀ x, ‖f x‖ ≤ minTensorNorm A B x) (x : A ⊗[ℂ] B) : extend f hf (of A B x) = f x := by
  rw [← coe_toMin_eq_of]
  exact (NonUnitalStarAlgHom.fromCompletion_apply_coe _ _ (toMin x)).trans (by simp)

/-- If `f` preserves the minimal norm, its extension to `MinTensorProduct A B` is isometric. -/
theorem norm_extend {C : Type*} [NonUnitalCStarAlgebra C] (f : A ⊗[ℂ] B →⋆ₙₐ[ℂ] C)
    (hf : ∀ x, ‖f x‖ = minTensorNorm A B x) (u : MinTensorProduct A B) :
    ‖extend f (fun x ↦ (hf x).le) u‖ = ‖u‖ :=
  induction_on u (isClosed_eq (continuous_norm.comp (map_continuous _)) continuous_norm)
    fun x ↦ by rw [extend_of, norm_of, hf]

/-! ### The spatial realization -/

section Spatial

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- The **spatial realization** of `MinTensorProduct A B` by representations `π : A → B(E)` and
`ρ : B → B(F)`: the extension of the spatial tensor homomorphism `a ⊗ b ↦ π a ⊗ ρ b` into
`B(E ⊗₂ F)`. It is isometric when `π` and `ρ` are faithful
(`TauCeti.MinTensorProduct.norm_spatialTensorHom`). -/
def spatialTensorHom (π : A →⋆ₙₐ[ℂ] (E →L[ℂ] E)) (ρ : B →⋆ₙₐ[ℂ] (F →L[ℂ] F)) :
    MinTensorProduct A B →⋆ₙₐ[ℂ] (Completion (E ⊗[ℂ] F) →L[ℂ] Completion (E ⊗[ℂ] F)) :=
  extend (π.spatialTensorHom ρ) (norm_spatialTensorHom_le_minTensorNorm π ρ)

@[simp]
theorem spatialTensorHom_of (π : A →⋆ₙₐ[ℂ] (E →L[ℂ] E)) (ρ : B →⋆ₙₐ[ℂ] (F →L[ℂ] F))
    (x : A ⊗[ℂ] B) : spatialTensorHom π ρ (of A B x) = π.spatialTensorHom ρ x :=
  extend_of _ _ x

/-- For faithful representations the spatial realization of `MinTensorProduct A B` is
isometric. -/
theorem norm_spatialTensorHom {π : A →⋆ₙₐ[ℂ] (E →L[ℂ] E)} {ρ : B →⋆ₙₐ[ℂ] (F →L[ℂ] F)}
    (hπ : Function.Injective π) (hρ : Function.Injective ρ) (u : MinTensorProduct A B) :
    ‖spatialTensorHom π ρ u‖ = ‖u‖ :=
  norm_extend _ (fun x ↦ (minTensorNorm_eq_norm_spatialTensorHom hπ hρ x).symm) u

/-- For faithful representations the spatial realization of `MinTensorProduct A B` is
injective. -/
theorem spatialTensorHom_injective {π : A →⋆ₙₐ[ℂ] (E →L[ℂ] E)} {ρ : B →⋆ₙₐ[ℂ] (F →L[ℂ] F)}
    (hπ : Function.Injective π) (hρ : Function.Injective ρ) :
    Function.Injective (spatialTensorHom π ρ) :=
  (injective_iff_map_eq_zero _).2 fun u hu ↦
    norm_eq_zero.1 (by rw [← norm_spatialTensorHom hπ hρ u, hu]; simp)

end Spatial

/-! ### Functoriality -/

section Map

variable {A' B' A'' B'' : Type*} [NonUnitalCStarAlgebra A'] [NonUnitalCStarAlgebra B']
  [NonUnitalCStarAlgebra A''] [NonUnitalCStarAlgebra B'']

open Algebra.TensorProduct (mapNonUnitalStarAlgHom mapNonUnitalStarAlgHom_tmul)

/-- **Functoriality of the minimal tensor product**: star homomorphisms `φ : A → A'` and
`ψ : B → B'` extend `φ ⊗ ψ` to a star homomorphism
`MinTensorProduct A B → MinTensorProduct A' B'`. -/
def map (φ : A →⋆ₙₐ[ℂ] A') (ψ : B →⋆ₙₐ[ℂ] B') :
    MinTensorProduct A B →⋆ₙₐ[ℂ] MinTensorProduct A' B' :=
  extend ((of A' B').comp (mapNonUnitalStarAlgHom φ ψ)) fun x ↦ by
    rw [NonUnitalStarAlgHom.comp_apply, norm_of]
    exact minTensorNorm_mapNonUnitalStarAlgHom_le φ ψ x

@[simp]
theorem map_of (φ : A →⋆ₙₐ[ℂ] A') (ψ : B →⋆ₙₐ[ℂ] B') (x : A ⊗[ℂ] B) :
    map φ ψ (of A B x) = of A' B' (mapNonUnitalStarAlgHom φ ψ x) :=
  extend_of _ _ x

theorem map_of_tmul (φ : A →⋆ₙₐ[ℂ] A') (ψ : B →⋆ₙₐ[ℂ] B') (a : A) (b : B) :
    map φ ψ (of A B (a ⊗ₜ b)) = of A' B' (φ a ⊗ₜ ψ b) := by
  rw [map_of, mapNonUnitalStarAlgHom_tmul]

/-- For injective `φ` and `ψ`, `map φ ψ` is isometric. -/
theorem norm_map {φ : A →⋆ₙₐ[ℂ] A'} {ψ : B →⋆ₙₐ[ℂ] B'} (hφ : Function.Injective φ)
    (hψ : Function.Injective ψ) (u : MinTensorProduct A B) : ‖map φ ψ u‖ = ‖u‖ :=
  norm_extend _ (fun x ↦ by
    rw [NonUnitalStarAlgHom.comp_apply, norm_of, minTensorNorm_mapNonUnitalStarAlgHom hφ hψ]) u

/-- **The minimal tensor product preserves injectivity**: for injective `φ` and `ψ`, `map φ ψ` is
injective. -/
theorem map_injective {φ : A →⋆ₙₐ[ℂ] A'} {ψ : B →⋆ₙₐ[ℂ] B'} (hφ : Function.Injective φ)
    (hψ : Function.Injective ψ) : Function.Injective (map φ ψ) :=
  (AddMonoidHomClass.isometry_of_norm _ (norm_map hφ hψ)).injective

@[simp]
theorem map_id :
    map (NonUnitalStarAlgHom.id ℂ A) (NonUnitalStarAlgHom.id ℂ B) =
      NonUnitalStarAlgHom.id ℂ (MinTensorProduct A B) :=
  starAlgHom_ext fun a b ↦ by simp

theorem map_comp (φ' : A' →⋆ₙₐ[ℂ] A'') (ψ' : B' →⋆ₙₐ[ℂ] B'') (φ : A →⋆ₙₐ[ℂ] A')
    (ψ : B →⋆ₙₐ[ℂ] B') : map (φ'.comp φ) (ψ'.comp ψ) = (map φ' ψ').comp (map φ ψ) :=
  starAlgHom_ext fun a b ↦ by simp

end Map

end MinTensorProduct

/-! ### The canonical surjection from the maximal tensor product -/

namespace MaxTensorProduct

variable {A B}

/-- The canonical star homomorphism `MaxTensorProduct A B → MinTensorProduct A B`, extending the
identity of `A ⊗[ℂ] B`; it is bounded because `‖·‖_min ≤ ‖·‖_max`. -/
def toMin : MaxTensorProduct A B →⋆ₙₐ[ℂ] MinTensorProduct A B :=
  ((MinTensorProduct.of A B).comp
    (MaxTensorAlgebra.toMaxStarAlgEquiv A B).symm.toNonUnitalStarAlgHom).fromCompletion <|
    AddMonoidHomClass.continuous_of_bound _ 1 fun x ↦ by
      simpa [MaxTensorAlgebra.norm_def] using
        minTensorNorm_le_maxTensorNorm (MaxTensorAlgebra.ofMax x)

@[simp]
theorem toMin_of (x : A ⊗[ℂ] B) : toMin (of A B x) = MinTensorProduct.of A B x := by
  rw [← coe_toMax_eq_of]
  exact (NonUnitalStarAlgHom.fromCompletion_apply_coe _ _ (MaxTensorAlgebra.toMax x)).trans
    (by simp)

/-- **The canonical map `A ⊗max B → A ⊗min B` is surjective.** -/
theorem toMin_surjective : Function.Surjective (toMin (A := A) (B := B)) := by
  refine NonUnitalStarAlgHom.surjective_of_denseRange ?_
  refine (MinTensorProduct.denseRange_of (A := A) (B := B)).mono ?_
  rintro _ ⟨x, rfl⟩
  exact ⟨of A B x, toMin_of x⟩

end MaxTensorProduct

end TauCeti

/-! ### Closed concrete operator algebras -/

namespace NonUnitalStarSubalgebra

open TauCeti

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  (A : NonUnitalStarSubalgebra ℂ (E →L[ℂ] E)) (B : NonUnitalStarSubalgebra ℂ (F →L[ℂ] F))

/-- The spatial tensor product is closed, so it is a C*-algebra. -/
instance instIsClosedMinTensor :
    IsClosed (minTensor A B : Set (Completion (E ⊗[ℂ] F) →L[ℂ] Completion (E ⊗[ℂ] F))) :=
  isClosed_minTensor A B

variable [IsClosed (A : Set (E →L[ℂ] E))] [IsClosed (B : Set (F →L[ℂ] F))]

/-- For closed concrete operator algebras, the norm of `x` in the spatial tensor product
`A ⊗_min B` is its minimal norm. -/
theorem norm_toMinTensor_eq_minTensorNorm (x : A ⊗[ℂ] B) :
    ‖toMinTensor A B x‖ = minTensorNorm A B x := by
  rw [norm_toMinTensor, minTensorNorm_eq_spatialNorm]

/-- The star homomorphism `MinTensorProduct A B → A ⊗_min B` extending the identity of
`A ⊗[ℂ] B`, for closed concrete operator algebras. -/
def minTensorProductToMinTensor : MinTensorProduct A B →⋆ₙₐ[ℂ] minTensor A B :=
  MinTensorProduct.extend (toMinTensor A B) fun x ↦ (norm_toMinTensor_eq_minTensorNorm A B x).le

@[simp]
theorem minTensorProductToMinTensor_of (x : A ⊗[ℂ] B) :
    minTensorProductToMinTensor A B (MinTensorProduct.of A B x) = toMinTensor A B x :=
  MinTensorProduct.extend_of _ _ x

/-- The map `MinTensorProduct A B → A ⊗_min B` is isometric. -/
theorem norm_minTensorProductToMinTensor (u : MinTensorProduct A B) :
    ‖minTensorProductToMinTensor A B u‖ = ‖u‖ :=
  MinTensorProduct.norm_extend _ (norm_toMinTensor_eq_minTensorNorm A B) u

theorem bijective_minTensorProductToMinTensor :
    Function.Bijective (minTensorProductToMinTensor A B) := by
  refine ⟨(AddMonoidHomClass.isometry_of_norm _
      (norm_minTensorProductToMinTensor A B)).injective,
    NonUnitalStarAlgHom.surjective_of_denseRange ?_⟩
  refine (denseRange_toMinTensor A B).mono ?_
  rintro _ ⟨x, rfl⟩
  exact ⟨MinTensorProduct.of A B x, minTensorProductToMinTensor_of A B x⟩

/-- For closed concrete operator algebras `A ⊆ B(E)` and `B ⊆ B(F)`, the minimal tensor product
`A ⊗min B` is isomorphic to the spatial tensor product `A ⊗_min B ⊆ B(E ⊗₂ F)`, compatibly with
the maps from `A ⊗[ℂ] B`. -/
def minTensorProductEquiv : MinTensorProduct A B ≃⋆ₐ[ℂ] minTensor A B :=
  StarAlgEquiv.ofBijective (minTensorProductToMinTensor A B)
    (bijective_minTensorProductToMinTensor A B)

@[simp]
theorem minTensorProductEquiv_of (x : A ⊗[ℂ] B) :
    minTensorProductEquiv A B (MinTensorProduct.of A B x) = toMinTensor A B x :=
  minTensorProductToMinTensor_of A B x

end NonUnitalStarSubalgebra
