/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Spectrum
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import TauCeti.Dynamics.Flow.Basic

/-!
# Continuous actions on C⋆-algebras

A `CStarAction G A` is a homomorphism into the complex star-algebra automorphisms of `A`
whose orbits are norm-continuous. The algebra need not have an identity. Automorphisms are
isometric, hence each one is a continuous complex linear map, and point-norm continuity implies
joint continuity of evaluation. This is the continuity needed when an action is applied to a
coefficient-valued convolution integrand.

Each automorphism of an action commutes with Bochner integrals.

Actions can be pulled back along continuous group homomorphisms and transported along
star-algebra equivalences. The latter construction expresses conjugacy of dynamical systems.
Membership in a subset invariant in the sense of Mathlib's `IsInvariant` is unchanged by the
action.

The conventions follow Dana Williams, *Crossed Products of C*-Algebras*, Chapter 2.
The joint-continuity argument uses Mathlib's `StarAlgEquiv.isometry` and
`continuous_prod_of_continuous_lipschitzWith'`.
-/

public section

namespace TauCeti

variable (G A : Type*) [Group G] [TopologicalSpace G] [NonUnitalCStarAlgebra A]

/-- A point-norm continuous action on a possibly nonunital complex C⋆-algebra. -/
structure CStarAction where
  /-- The homomorphism into star-algebra automorphisms. -/
  toMonoidHom : G →* (A ≃⋆ₐ[ℂ] A)
  /-- Continuity of every orbit in the norm topology. -/
  continuous_orbit : ∀ a : A, Continuous fun g => toMonoidHom g a

namespace CStarAction

variable {G A}

instance : FunLike (CStarAction G A) G (A ≃⋆ₐ[ℂ] A) where
  coe α := α.toMonoidHom
  coe_injective α β h := by
    have : α.toMonoidHom = β.toMonoidHom := MonoidHom.ext (congrFun h)
    cases α
    cases β
    congr

/-- Actions are determined by their values on group elements and coefficients. -/
@[ext]
theorem ext {α β : CStarAction G A} (h : ∀ g a, α g a = β g a) : α = β :=
  DFunLike.ext _ _ fun g => StarAlgEquiv.ext (h g)

@[simp]
theorem toMonoidHom_apply (α : CStarAction G A) (g : G) : α.toMonoidHom g = α g :=
  (rfl)

@[simp]
theorem one_apply (α : CStarAction G A) (a : A) : α 1 a = a := by
  simp [← toMonoidHom_apply]

/-- The group product acts by composition, with the right factor acting first. -/
theorem mul_apply (α : CStarAction G A) (g h : G) (a : A) :
    α (g * h) a = α g (α h a) := by
  simp [← toMonoidHom_apply]

@[simp]
theorem inv_apply_apply (α : CStarAction G A) (g : G) (a : A) :
    α g⁻¹ (α g a) = a := by
  rw [← mul_apply]
  simp

@[simp]
theorem apply_inv_apply (α : CStarAction G A) (g : G) (a : A) :
    α g (α g⁻¹ a) = a := by
  rw [← mul_apply]
  simp

/-- The automorphism by which a group element acts, as a continuous complex linear map. -/
def toContinuousLinearMap (α : CStarAction G A) (g : G) : A →L[ℂ] A where
  toFun := α g
  map_add' := map_add _
  map_smul' := map_smul _
  cont := (StarAlgEquiv.isometry (α g)).continuous

@[simp]
theorem toContinuousLinearMap_apply (α : CStarAction G A) (g : G) (a : A) :
    α.toContinuousLinearMap g a = α g a :=
  (rfl)

/-- Each automorphism of a C⋆-action commutes with Bochner integrals. No integrability is needed,
since the automorphism is a linear isometry. -/
theorem integral_comp_comm (α : CStarAction G A) {X : Type*} [MeasurableSpace X]
    (ν : MeasureTheory.Measure X) (g : G) (F : X → A) :
    ∫ x, α g (F x) ∂ν = α g (∫ x, F x ∂ν) :=
  LinearIsometry.integral_comp_comm ⟨(α g : A →ₗ[ℂ] A), StarAlgEquiv.norm_map (α g)⟩ F

/-- Membership in an invariant subset is unchanged by the action. -/
@[simp]
theorem _root_.IsInvariant.cstarAction_apply_mem_iff {α : CStarAction G A} {s : Set A}
    (hs : IsInvariant (fun g a ↦ α g a) s) (g : G) (a : A) : α g a ∈ s ↔ a ∈ s :=
  hs.apply_mem_iff (fun g a ↦ α.inv_apply_apply g a) g a

/-- Point-norm continuity implies joint continuity of the action. -/
@[fun_prop]
theorem continuous (α : CStarAction G A) : Continuous fun p : G × A => α p.1 p.2 :=
  continuous_prod_of_continuous_lipschitzWith' _ 1
    (fun g => (StarAlgEquiv.isometry (α g)).lipschitzWith) α.continuous_orbit

/-- Apply an action to two continuously varying arguments. -/
@[fun_prop]
theorem continuous_apply (α : CStarAction G A) {X : Type*} [TopologicalSpace X]
    {g : X → G} {a : X → A} (hg : Continuous g) (ha : Continuous a) :
    Continuous fun x => α (g x) (a x) :=
  α.continuous.comp (hg.prodMk ha)

/-- The inverse of an automorphism of the action is the action of the inverse element. -/
@[simp]
theorem symm_apply (α : CStarAction G A) (g : G) (a : A) : (α g).symm a = α g⁻¹ a :=
  (α g).symm_apply_eq.mpr (α.apply_inv_apply g a).symm

/-- Orbits through inverses are continuous. Continuity of inversion in `G` is not needed, since
`‖α g⁻¹ a - α h⁻¹ a‖ = ‖α h b - α g b‖` for `b = α h⁻¹ a`. -/
theorem continuous_inv_apply (α : CStarAction G A) (a : A) : Continuous fun g => α g⁻¹ a := by
  refine continuous_iff_continuousAt.2 fun h => ?_
  have hdist (g : G) : dist (α g⁻¹ a) (α h⁻¹ a) = dist (α g (α h⁻¹ a)) a := by
    rw [← (StarAlgEquiv.isometry (α g)).dist_eq, apply_inv_apply, dist_comm]
  have hlim : Filter.Tendsto (fun g => α g (α h⁻¹ a)) (nhds h) (nhds a) := by
    simpa using (α.continuous_orbit (α h⁻¹ a)).tendsto h
  rw [tendsto_iff_dist_tendsto_zero] at hlim
  rw [ContinuousAt, tendsto_iff_dist_tendsto_zero]
  simpa only [hdist] using hlim

/-- The trivial action, including on the zero algebra. -/
def trivial : CStarAction G A where
  toMonoidHom := 1
  continuous_orbit _ := by simpa using continuous_const

@[simp]
theorem trivial_apply (g : G) (a : A) : trivial (G := G) (A := A) g a = a :=
  (rfl)

variable {H K : Type*} [Group H] [TopologicalSpace H] [Group K] [TopologicalSpace K]

/-- Pull back an action along a continuous homomorphism, in particular a subgroup inclusion. -/
def comp (α : CStarAction G A) (φ : ContinuousMonoidHom H G) : CStarAction H A where
  toMonoidHom := α.toMonoidHom.comp φ.toMonoidHom
  continuous_orbit a := (α.continuous_orbit a).comp φ.continuous

@[simp]
theorem comp_apply (α : CStarAction G A) (φ : ContinuousMonoidHom H G) (h : H) (a : A) :
    α.comp φ h a = α (φ h) a :=
  (rfl)

@[simp]
theorem comp_id (α : CStarAction G A) : α.comp (ContinuousMonoidHom.id G) = α := by
  ext
  simp

@[simp]
theorem comp_comp (α : CStarAction G A) (φ : ContinuousMonoidHom H G)
    (ψ : ContinuousMonoidHom K H) : (α.comp φ).comp ψ = α.comp (φ.comp ψ) := by
  ext
  simp

variable {B C : Type*} [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra C]

/-- Transport an action through a star-algebra equivalence: `g` acts by `e ∘ α g ∘ e⁻¹`. -/
def conjugate (α : CStarAction G A) (e : A ≃⋆ₐ[ℂ] B) : CStarAction G B where
  toMonoidHom :=
    { toFun g := e.symm.trans ((α g).trans e)
      map_one' := by
        ext
        simp
      map_mul' g h := by
        ext
        simp [mul_apply] }
  continuous_orbit b :=
    (StarAlgEquiv.isometry e).continuous.comp (α.continuous_orbit (e.symm b))

@[simp]
theorem conjugate_apply (α : CStarAction G A) (e : A ≃⋆ₐ[ℂ] B) (g : G) (b : B) :
    α.conjugate e g b = e (α g (e.symm b)) :=
  (rfl)

@[simp]
theorem conjugate_refl (α : CStarAction G A) : α.conjugate (.refl ℂ A) = α := by
  ext
  simp

/-- Successive conjugacies equal conjugacy along the composite equivalence. -/
-- Keep this as an explicit rewrite so inverse conjugacies remain visible to simplification.
theorem conjugate_conjugate (α : CStarAction G A) (e : A ≃⋆ₐ[ℂ] B) (f : B ≃⋆ₐ[ℂ] C) :
    (α.conjugate e).conjugate f = α.conjugate (e.trans f) := by
  ext
  simp

/-- Transporting an action back along the inverse equivalence recovers it. -/
@[simp]
theorem conjugate_symm (α : CStarAction G A) (e : A ≃⋆ₐ[ℂ] B) :
    (α.conjugate e).conjugate e.symm = α := by
  ext
  simp

/-- Pullback in the group and conjugacy in the algebra commute. -/
theorem conjugate_comp (α : CStarAction G A) (e : A ≃⋆ₐ[ℂ] B)
    (φ : ContinuousMonoidHom H G) : (α.conjugate e).comp φ = (α.comp φ).conjugate e := by
  ext
  simp

end CStarAction

end TauCeti
