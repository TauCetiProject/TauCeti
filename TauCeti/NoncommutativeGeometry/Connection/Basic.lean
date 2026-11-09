/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Torsor.Defs
public import TauCeti.Algebra.Lie.Derivation.Basic

/-!
# Connections along derivations

Let `A` be an algebra and `δ` a derivation of `A`. A *connection along `δ`* on a right `A`-module
`E` is an additive map `∇ : E → E` satisfying the Leibniz rule

`∇ (ξ a) = (∇ ξ) a + ξ δ(a)`.

This is Connes' notion of a connection on a module over a noncommutative algebra equipped with an
action of a Lie algebra by derivations, taken one derivation at a time: on the smooth
noncommutative torus with its two basic derivations `δ₁` and `δ₂`, a connection is a pair
`(∇₁, ∇₂)` of connections along `δ₁` and `δ₂`. Right modules are encoded as modules over the
opposite algebra `Aᵐᵒᵖ`, and `ξ a` is written `ξ <• a`.

The connections along `δ` form an affine space over the `A`-linear endomorphisms of `E`: the
difference of two connections is `A`-linear, and adding an `A`-linear endomorphism to a connection
gives a connection. When `δ₁` and `δ₂` commute, the curvature `∇₁ ∇₂ - ∇₂ ∇₁` of connections along
them is `A`-linear. The `A`-linear automorphisms of `E` act on connections by gauge
transformations `∇ ↦ u ∇ u⁻¹`, and conjugate the curvature.

## Main definitions

* `TauCeti.DerivationConnection δ E`: the connections along `δ` on the right `A`-module `E`.
* `TauCeti.DerivationConnection.instAddTorsor`: connections along `δ`, when there is one, form an
  affine space over `E →ₗ[Aᵐᵒᵖ] E`.
* `TauCeti.DerivationConnection.instBracket`: the commutator `⁅∇, α⁆ = ∇ α - α ∇` of a connection
  with an `A`-linear endomorphism, itself `A`-linear.
* `TauCeti.DerivationConnection.curvature`: the curvature `∇₁ ∇₂ - ∇₂ ∇₁` of connections along
  commuting derivations, as an `A`-linear endomorphism.
* `TauCeti.DerivationConnection.instMulAction`: the action `u • ∇ = u ∇ u⁻¹` of the gauge group
  `E ≃ₗ[Aᵐᵒᵖ] E`.

## Main results

* `TauCeti.DerivationConnection.leibniz`: the Leibniz rule.
* `TauCeti.DerivationConnection.curvature_vadd`: the change of curvature under a change of
  connection, `F(∇₁ + α, ∇₂ + β) = F(∇₁, ∇₂) + ⁅∇₁, β⁆ - ⁅∇₂, α⁆ + ⁅α, β⁆`.
* `TauCeti.DerivationConnection.curvature_smul_apply`: gauge transformations conjugate the
  curvature.

## References

* A. Connes, *C\*-algèbres et géométrie différentielle*, C. R. Acad. Sci. Paris Sér. A-B 290
  (1980), A599–A604.
* A. Connes, *Noncommutative Geometry*, Academic Press, 1994, Chapter III, §2.β and §3.
-/

public section

open scoped RightActions

namespace TauCeti

variable {k A : Type*} [CommRing k] [Ring A] [Algebra k A]

/-- A **connection along a derivation** `δ` of `A` on a right `A`-module `E`: an additive map
`∇ : E → E` satisfying the Leibniz rule `∇ (ξ a) = (∇ ξ) a + ξ δ(a)`. The right action of `A` on
`E` is a module structure over the opposite algebra `Aᵐᵒᵖ`. -/
structure DerivationConnection (δ : derivationLieAlgebra k A) (E : Type*) [AddCommGroup E]
    [Module Aᵐᵒᵖ E] where
  /-- The underlying additive map of a connection. -/
  toAddMonoidHom : E →+ E
  /-- The Leibniz rule `∇ (ξ a) = (∇ ξ) a + ξ δ(a)`. -/
  leibniz' (ξ : E) (a : A) :
    toAddMonoidHom (ξ <• a) = toAddMonoidHom ξ <• a + ξ <• (δ : Module.End k A) a

namespace DerivationConnection

variable {E : Type*} [AddCommGroup E] [Module Aᵐᵒᵖ E] {δ δ₁ δ₂ : derivationLieAlgebra k A}

instance : FunLike (DerivationConnection δ E) E E where
  coe D := D.toAddMonoidHom
  coe_injective D D' h := by
    cases D
    cases D'
    congr
    exact DFunLike.coe_injective h

instance : AddMonoidHomClass (DerivationConnection δ E) E E where
  map_add D := D.toAddMonoidHom.map_add
  map_zero D := D.toAddMonoidHom.map_zero

@[ext]
theorem ext {D D' : DerivationConnection δ E} (h : ∀ ξ, D ξ = D' ξ) : D = D' :=
  DFunLike.ext _ _ h

@[simp]
theorem coe_toAddMonoidHom (D : DerivationConnection δ E) : ⇑D.toAddMonoidHom = D :=
  (rfl)

@[simp]
theorem coe_mk (f : E →+ E) (h) : ⇑(⟨f, h⟩ : DerivationConnection δ E) = f :=
  (rfl)

/-- **The Leibniz rule** of a connection: `∇ (ξ a) = (∇ ξ) a + ξ δ(a)`. -/
@[simp]
theorem leibniz (D : DerivationConnection δ E) (ξ : E) (a : A) :
    D (ξ <• a) = D ξ <• a + ξ <• (δ : Module.End k A) a :=
  D.leibniz' ξ a

/-! ### The affine structure -/

/-- Adding an `A`-linear endomorphism to a connection gives a connection. -/
instance : VAdd (E →ₗ[Aᵐᵒᵖ] E) (DerivationConnection δ E) where
  vadd α D :=
    { toAddMonoidHom := α.toAddMonoidHom + D.toAddMonoidHom
      leibniz' ξ a := by
        simp only [AddMonoidHom.add_apply, LinearMap.toAddMonoidHom_coe, LinearMap.map_smul,
          coe_toAddMonoidHom, leibniz, smul_add]
        abel }

@[simp]
theorem vadd_apply (α : E →ₗ[Aᵐᵒᵖ] E) (D : DerivationConnection δ E) (ξ : E) :
    (α +ᵥ D) ξ = α ξ + D ξ :=
  (rfl)

instance : AddAction (E →ₗ[Aᵐᵒᵖ] E) (DerivationConnection δ E) where
  zero_vadd D := ext fun ξ ↦ by simp
  add_vadd α β D := ext fun ξ ↦ by simp [add_assoc]

/-- The difference of two connections along the same derivation is `A`-linear. -/
instance : VSub (E →ₗ[Aᵐᵒᵖ] E) (DerivationConnection δ E) where
  vsub D D' :=
    { toFun ξ := D ξ - D' ξ
      map_add' ξ η := by simp only [map_add]; abel
      map_smul' a ξ := by
        induction a using MulOpposite.rec' with | _ a
        simp only [leibniz, RingHom.id_apply]
        rw [smul_sub]
        abel }

@[simp]
theorem vsub_apply (D D' : DerivationConnection δ E) (ξ : E) : (D -ᵥ D') ξ = D ξ - D' ξ :=
  (rfl)

/-- **Connections form an affine space.** When a connection along `δ` exists, the connections along
`δ` form an affine space over the `A`-linear endomorphisms of `E`. -/
instance instAddTorsor [Nonempty (DerivationConnection δ E)] :
    AddTorsor (E →ₗ[Aᵐᵒᵖ] E) (DerivationConnection δ E) where
  vsub_vadd' D D' := ext fun ξ ↦ by simp
  vadd_vsub' α D := LinearMap.ext fun ξ ↦ by simp

/-! ### Commutators with endomorphisms -/

/-- The commutator `⁅∇, α⁆ = ∇ α - α ∇` of a connection with an `A`-linear endomorphism is
`A`-linear: the two Leibniz terms `α ξ δ(a)` cancel. -/
instance instBracket : Bracket (DerivationConnection δ E) (E →ₗ[Aᵐᵒᵖ] E) where
  bracket D α :=
    { toFun ξ := D (α ξ) - α (D ξ)
      map_add' ξ η := by simp only [map_add]; abel
      map_smul' a ξ := by
        induction a using MulOpposite.rec' with | _ a
        simp only [LinearMap.map_smul, leibniz, map_add, RingHom.id_apply]
        rw [smul_sub]
        abel }

@[simp]
theorem lie_apply (D : DerivationConnection δ E) (α : E →ₗ[Aᵐᵒᵖ] E) (ξ : E) :
    ⁅D, α⁆ ξ = D (α ξ) - α (D ξ) :=
  (rfl)

/-! ### Curvature -/

/-- The **curvature** `∇₁ ∇₂ - ∇₂ ∇₁` of connections `∇₁` and `∇₂` along commuting derivations
`δ₁` and `δ₂`. It is `A`-linear because the Leibniz terms cancel when `δ₁ δ₂ = δ₂ δ₁`. -/
def curvature (D₁ : DerivationConnection δ₁ E) (D₂ : DerivationConnection δ₂ E)
    (h : Commute (δ₁ : Module.End k A) δ₂) : E →ₗ[Aᵐᵒᵖ] E where
  toFun ξ := D₁ (D₂ ξ) - D₂ (D₁ ξ)
  map_add' ξ η := by simp only [map_add]; abel
  map_smul' a ξ := by
    induction a using MulOpposite.rec' with | _ a
    have h' : (δ₁ : Module.End k A) ((δ₂ : Module.End k A) a) =
        (δ₂ : Module.End k A) ((δ₁ : Module.End k A) a) :=
      LinearMap.congr_fun h.eq a
    simp only [leibniz, map_add, RingHom.id_apply, h']
    rw [smul_sub]
    abel

@[simp]
theorem curvature_apply (D₁ : DerivationConnection δ₁ E) (D₂ : DerivationConnection δ₂ E)
    (h : Commute (δ₁ : Module.End k A) δ₂) (ξ : E) :
    D₁.curvature D₂ h ξ = D₁ (D₂ ξ) - D₂ (D₁ ξ) :=
  (rfl)

/-- **Change of connection.** Adding `A`-linear endomorphisms `α` and `β` to connections `∇₁` and
`∇₂` changes the curvature by `⁅∇₁, β⁆ - ⁅∇₂, α⁆ + ⁅α, β⁆`. -/
theorem curvature_vadd (D₁ : DerivationConnection δ₁ E) (D₂ : DerivationConnection δ₂ E)
    (h : Commute (δ₁ : Module.End k A) δ₂) (α β : E →ₗ[Aᵐᵒᵖ] E) :
    (α +ᵥ D₁).curvature (β +ᵥ D₂) h = D₁.curvature D₂ h + ⁅D₁, β⁆ - ⁅D₂, α⁆ + ⁅α, β⁆ := by
  ext ξ
  simp only [curvature_apply, vadd_apply, map_add, LinearMap.add_apply, LinearMap.sub_apply,
    lie_apply, Ring.lie_def, mul_apply_eq_comp]
  abel

/-! ### Gauge transformations -/

/-- The gauge group `E ≃ₗ[Aᵐᵒᵖ] E` acts on connections by `u • ∇ = u ∇ u⁻¹`. -/
instance instMulAction : MulAction (E ≃ₗ[Aᵐᵒᵖ] E) (DerivationConnection δ E) where
  smul u D :=
    { toAddMonoidHom :=
        { toFun ξ := u (D (u.symm ξ))
          map_zero' := by simp
          map_add' ξ η := by simp }
      leibniz' ξ a := by simp [leibniz] }
  one_smul D := ext fun ξ ↦ rfl
  mul_smul u v D := ext fun ξ ↦ rfl

@[simp]
theorem smul_apply (u : E ≃ₗ[Aᵐᵒᵖ] E) (D : DerivationConnection δ E) (ξ : E) :
    (u • D) ξ = u (D (u.symm ξ)) :=
  (rfl)

/-- **Gauge transformations conjugate the curvature**: the curvature of `(u ∇₁ u⁻¹, u ∇₂ u⁻¹)` is
`u F u⁻¹`, where `F` is the curvature of `(∇₁, ∇₂)`. -/
theorem curvature_smul_apply (D₁ : DerivationConnection δ₁ E) (D₂ : DerivationConnection δ₂ E)
    (h : Commute (δ₁ : Module.End k A) δ₂) (u : E ≃ₗ[Aᵐᵒᵖ] E) (ξ : E) :
    (u • D₁).curvature (u • D₂) h ξ = u (D₁.curvature D₂ h (u.symm ξ)) := by
  simp

end DerivationConnection

end TauCeti
