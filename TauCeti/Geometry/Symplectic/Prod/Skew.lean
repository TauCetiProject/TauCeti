/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Prod.Basic
public import TauCeti.Geometry.Symplectic.SymplecticTransport
public import TauCeti.Geometry.Symplectic.Transport

/-!
# Skew products of almost complex structures and symplectic forms

Let `A : V →ₗ[ℝ] W` be a linear map, and let `e_A : V × W ≃ₗ[ℝ] V × W` be the shear
`(v, w) ↦ (v, w + A v)` (`LinearEquiv.skewProd`). Transporting the direct-sum structure
`J₁ ⊕ J₂` and the direct-sum form `ω₁ ⊕ ω₂` of `TauCeti.Geometry.Symplectic.Prod.Basic` along
`e_A` gives the *skew products*

* `J_A(v, w) = (J₁ v, J₂ (w - A v) + A (J₁ v))`, and
* `ω_A((v, w), (v', w')) = ω₁(v, v') + ω₂(w - A v, w' - A v')`.

Since `e_A` is a linear equivalence, a skew product of tame (respectively compatible) pairs is
again tame (respectively compatible). The first projection is complex linear from `J_A` to `J₁`,
and the inclusion of the second factor is complex linear from `J₂` to `J_A`: the vertical
subspace `{0} × W` is `J_A`-complex with the structure `J₂`, so every affine fibre `{v} × W` has
tangent spaces carrying `J₂`.

This is the pointwise linear algebra of Gromov's graph construction. For a map `L : V →ₗ[ℝ] W`,
the graph map `v ↦ (v, L v)` is complex linear from `J₁` to `J_A` exactly when `L - A` is complex
linear from `J₁` to `J₂` (`TauCeti.AlmostComplexStructure.isComplexLinearMap_id_prod_skewProd_iff`).
For `A` the Hamiltonian vector field one-form of an inhomogeneous Cauchy–Riemann equation, this
turns its solutions into holomorphic graphs.

## Main declarations

* `TauCeti.AlmostComplexStructure.skewProd`: the skew product `J_A` of `J₁` and `J₂` along `A`.
* `TauCeti.SymplecticForm.skewProd`: the skew product `ω_A` of `ω₁` and `ω₂` along `A`.
* `TauCeti.AlmostComplexStructure.isComplexLinearMap_skewProd_iff`: a linear map `f` into `V × W`
  is complex linear for `J_A` exactly when its first component and `f.2 - A ∘ f.1` are.
* `TauCeti.SymplecticForm.skewProd_tames`, `TauCeti.SymplecticForm.skewProd_compatible`: skew
  products of tame (compatible) pairs are tame (compatible).

## References

* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, Section 8.1, where
  this construction appears on the product of a Riemann surface with a symplectic manifold.
-/

public section

namespace TauCeti

variable {U V W : Type*}
variable [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]

namespace AlmostComplexStructure

/-- The skew product of almost complex structures `J₁` on `V` and `J₂` on `W` along a linear map
`A : V →ₗ[ℝ] W`: the direct sum `J₁ ⊕ J₂` transported along the shear `(v, w) ↦ (v, w + A v)`.
It sends `(v, w)` to `(J₁ v, J₂ (w - A v) + A (J₁ v))`. -/
def skewProd (J₁ : AlmostComplexStructure V) (J₂ : AlmostComplexStructure W) (A : V →ₗ[ℝ] W) :
    AlmostComplexStructure (V × W) :=
  (J₁.prod J₂).transport ((LinearEquiv.refl ℝ V).skewProd (LinearEquiv.refl ℝ W) A)

@[simp]
lemma skewProd_apply (J₁ : AlmostComplexStructure V) (J₂ : AlmostComplexStructure W)
    (A : V →ₗ[ℝ] W) (p : V × W) :
    J₁.skewProd J₂ A p = (J₁ p.1, J₂ (p.2 - A p.1) + A (J₁ p.1)) := by
  simp [skewProd, LinearEquiv.skewProd_apply, LinearEquiv.skewProd_symm_apply]

/-- Along the zero map the skew product is the direct sum. -/
@[simp]
lemma skewProd_zero (J₁ : AlmostComplexStructure V) (J₂ : AlmostComplexStructure W) :
    J₁.skewProd J₂ 0 = J₁.prod J₂ :=
  ext fun p ↦ by simp

/-- **Complex linearity into a skew product.** A linear map `f : U →ₗ[ℝ] V × W` is complex
linear from `J` to the skew product `J₁.skewProd J₂ A` exactly when its first component is
complex linear from `J` to `J₁` and `f.2 - A ∘ f.1` is complex linear from `J` to `J₂`. -/
lemma isComplexLinearMap_skewProd_iff {J : AlmostComplexStructure U}
    {J₁ : AlmostComplexStructure V} {J₂ : AlmostComplexStructure W} {A : V →ₗ[ℝ] W}
    {f : U →ₗ[ℝ] V × W} :
    IsComplexLinearMap J (J₁.skewProd J₂ A) f ↔
      IsComplexLinearMap J J₁ (LinearMap.fst ℝ V W ∘ₗ f) ∧
        IsComplexLinearMap J J₂ (LinearMap.snd ℝ V W ∘ₗ f - A ∘ₗ LinearMap.fst ℝ V W ∘ₗ f) := by
  simp only [isComplexLinearMap_iff_apply, skewProd_apply, Prod.ext_iff, LinearMap.sub_apply,
    LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_fst, LinearMap.coe_snd]
  constructor
  · intro h
    exact ⟨fun u ↦ (h u).1, fun u ↦ by rw [(h u).2, (h u).1, add_sub_cancel_right]⟩
  · intro h u
    exact ⟨h.1 u, by rw [← h.2 u, h.1 u, sub_add_cancel]⟩

/-- **Graphs in a skew product.** The graph map `v ↦ (v, L v)` of a linear map `L` is complex
linear from `J₁` to `J₁.skewProd J₂ A` exactly when `L - A` is complex linear from `J₁` to
`J₂`. -/
lemma isComplexLinearMap_id_prod_skewProd_iff {J₁ : AlmostComplexStructure V}
    {J₂ : AlmostComplexStructure W} {A L : V →ₗ[ℝ] W} :
    IsComplexLinearMap J₁ (J₁.skewProd J₂ A) (LinearMap.id.prod L) ↔
      IsComplexLinearMap J₁ J₂ (L - A) := by
  rw [isComplexLinearMap_skewProd_iff, LinearMap.fst_prod, LinearMap.snd_prod,
    LinearMap.comp_id]
  exact and_iff_right (isComplexLinearMap_id J₁)

/-- The first projection is complex linear out of a skew product. -/
@[simp]
lemma isComplexLinearMap_skewProd_fst (J₁ : AlmostComplexStructure V)
    (J₂ : AlmostComplexStructure W) (A : V →ₗ[ℝ] W) :
    IsComplexLinearMap (J₁.skewProd J₂ A) J₁ (LinearMap.fst ℝ V W) := by
  rw [isComplexLinearMap_iff_apply]
  intro p
  simp

/-- The inclusion of the second factor is complex linear into a skew product: the vertical
subspace `{0} × W` is a complex subspace on which the skew product restricts to `J₂`, so every
affine fibre `{v} × W` has tangent spaces carrying `J₂`. -/
@[simp]
lemma isComplexLinearMap_skewProd_inr (J₁ : AlmostComplexStructure V)
    (J₂ : AlmostComplexStructure W) (A : V →ₗ[ℝ] W) :
    IsComplexLinearMap J₂ (J₁.skewProd J₂ A) (LinearMap.inr ℝ V W) := by
  rw [isComplexLinearMap_iff_apply]
  intro w
  simp

end AlmostComplexStructure

namespace SymplecticForm

/-- The skew product of symplectic forms `ω₁` on `V` and `ω₂` on `W` along a linear map
`A : V →ₗ[ℝ] W`: the direct sum `ω₁ ⊕ ω₂` transported along the shear `(v, w) ↦ (v, w + A v)`.
Its value on `(v, w)` and `(v', w')` is `ω₁(v, v') + ω₂(w - A v, w' - A v')`. -/
noncomputable def skewProd (ω₁ : SymplecticForm V) (ω₂ : SymplecticForm W) (A : V →ₗ[ℝ] W) :
    SymplecticForm (V × W) :=
  (ω₁.prod ω₂).transport ((LinearEquiv.refl ℝ V).skewProd (LinearEquiv.refl ℝ W) A)

@[simp]
lemma skewProd_apply (ω₁ : SymplecticForm V) (ω₂ : SymplecticForm W) (A : V →ₗ[ℝ] W)
    (p q : V × W) :
    ω₁.skewProd ω₂ A p q = ω₁ p.1 q.1 + ω₂ (p.2 - A p.1) (q.2 - A q.1) := by
  simp [skewProd, LinearEquiv.skewProd_symm_apply]

/-- Along the zero map the skew product is the direct sum. -/
@[simp]
lemma skewProd_zero (ω₁ : SymplecticForm V) (ω₂ : SymplecticForm W) :
    ω₁.skewProd ω₂ 0 = ω₁.prod ω₂ :=
  toBilinForm_injective <| LinearMap.ext₂ fun p q ↦ by simp

variable {ω₁ : SymplecticForm V} {ω₂ : SymplecticForm W}
  {J₁ : AlmostComplexStructure V} {J₂ : AlmostComplexStructure W}

/-- A skew product of tame pairs is tame. -/
lemma skewProd_tames (h₁ : ω₁.Tames J₁) (h₂ : ω₂.Tames J₂) (A : V →ₗ[ℝ] W) :
    (ω₁.skewProd ω₂ A).Tames (J₁.skewProd J₂ A) :=
  (prod_tames h₁ h₂).transport _

/-- A skew product of compatible pairs is compatible. -/
lemma skewProd_compatible (h₁ : ω₁.Compatible J₁) (h₂ : ω₂.Compatible J₂) (A : V →ₗ[ℝ] W) :
    (ω₁.skewProd ω₂ A).Compatible (J₁.skewProd J₂ A) :=
  (prod_compatible h₁ h₂).transport _

end SymplecticForm

end TauCeti
