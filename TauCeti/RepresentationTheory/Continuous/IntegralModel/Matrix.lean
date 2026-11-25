/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.Lattice
public import TauCeti.GroupTheory.GroupAction.Stabilizer.Basic
public import TauCeti.RepresentationTheory.Continuous.IntegralModel.Basic
public import TauCeti.Topology.Algebra.Group.Units

/-!
# The matrix form of an integral model

Let `ρ` be a jointly continuous representation (`TauCeti.ContinuousRep`) of a topological group
`Γ` on a module `V` over a ring `E`, and let `Λ` be an integral model of `ρ` over `O`
(`TauCeti.GaloisLattice.IntegralModel`): a `Γ`-stable full `O`-lattice in `V`. Every `ρ g` then
lies in the stabilizer of `Λ` in `V ≃ₗ[E] V` (`TauCeti.GaloisLattice.IntegralModel.toStabilizer`),
and an `O`-basis `b` of `Λ` of size `n` identifies this stabilizer with `GL_n(O)`
(`Module.Basis.stabilizerMulEquivGL`). The composite is the matrix form
`TauCeti.GaloisLattice.IntegralModel.toGL Λ b : Γ →* GL ι O` of `ρ`: the matrix of `ρ g` in the
basis `b`, which is also a basis of `V` over `E`, has entries in `O`, as has its inverse.

When `O` is a topological ring and `Λ` carries its `O`-module topology, the matrix form is
continuous (`TauCeti.GaloisLattice.IntegralModel.continuous_toGL`). This applies to the
valuation ring `𝒪[E]` of a field with a valuative topology, where the subspace topology on a
lattice is its module topology. Over a nonarchimedean local field `E`, where `𝒪[E]` is a
discrete valuation ring and integral models exist for compact groups, a jointly continuous
representation of a compact group on a finite-dimensional `E`-vector space is therefore, in a
suitable basis of `V`, a continuous homomorphism `Γ → GL_n(𝒪[E])`
(`TauCeti.ContinuousRep.exists_basis_continuousMonoidHom_GL`).

## Main definitions

* `TauCeti.GaloisLattice.IntegralModel.toStabilizer`: `Γ` acts through the stabilizer of `Λ`.
* `TauCeti.GaloisLattice.IntegralModel.toGL`: the matrix form `Γ →* GL ι O` in a basis of `Λ`.

## Main results

* `TauCeti.GaloisLattice.IntegralModel.coe_toGL_apply`: the matrix form is the matrix of the
  restricted action on `Λ`.
* `TauCeti.GaloisLattice.IntegralModel.map_toGL_apply`: its image in `GL ι E` is the matrix of
  `ρ g` in the extended basis of `V`.
* `TauCeti.GaloisLattice.IntegralModel.continuous_toGL`: the matrix form is continuous.
* `TauCeti.ContinuousRep.exists_basis_continuousMonoidHom_GL`: over a nonarchimedean local field,
  a representation of a compact group is a continuous homomorphism to `GL_n(𝒪[E])` in some basis.

## References

* H. Darmon, F. Diamond and R. Taylor, *Fermat's Last Theorem*, §2.1, paragraph after
  Proposition 2.6.
* G. Böckle, M. Harris, C. Khare and J. A. Thorne, *\hat{G}-local systems on smooth
  projective curves are potentially automorphic*, Theorem 4.8(ii).
-/

public section

open Module Submodule
open scoped Pointwise

namespace TauCeti.GaloisLattice.IntegralModel

variable {Γ : Type*} [Group Γ] [TopologicalSpace Γ] {O : Type*} [CommRing O]
  {E : Type*} [CommRing E] [Algebra O E] {V : Type*} [AddCommGroup V] [Module E V] [Module O V]
  [IsScalarTower O E V] [TopologicalSpace V] {ρ : ContinuousRep Γ E V}

/-- **The action of `Γ` through the stabilizer of an integral model.** Each `ρ g`, as a linear
automorphism of `V`, maps the lattice of `Λ` onto itself. -/
def toStabilizer (Λ : IntegralModel O ρ) :
    Γ →* MulAction.stabilizer (V ≃ₗ[E] V) (Λ.lattice : Set V) :=
  ((LinearMap.GeneralLinearGroup.generalLinearEquiv E V).toMonoidHom.comp
    ρ.toRepresentation.asGroupHom).codRestrict _ fun g =>
      TauCeti.mem_stabilizer_set_iff_mapsTo.mpr
        ⟨fun x hx => Λ.stable g x hx, fun x hx => by
          simpa [← map_inv, LinearEquiv.smul_def, Representation.asGroupHom_apply] using
            Λ.stable g⁻¹ x hx⟩

@[simp]
theorem coe_toStabilizer_apply (Λ : IntegralModel O ρ) (g : Γ) (x : V) :
    (Λ.toStabilizer g : V ≃ₗ[E] V) x = ρ g x :=
  (rfl)

/-- Restricting `ρ g` from the stabilizer to a free lattice gives the restricted action. -/
@[simp]
theorem stabilizerMulEquiv_toStabilizer (Λ : IntegralModel O ρ) [Module.Free O Λ.lattice]
    (g : Γ) :
    (Λ.lattice.stabilizerMulEquiv E (Λ.toStabilizer g) : Λ.lattice →ₗ[O] Λ.lattice) =
      Λ.toContinuousRep g :=
  LinearMap.ext fun _ => Subtype.ext (by simp)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The matrix form of an integral model.** In an `O`-basis `b` of the lattice of `Λ`, `ρ` is
a homomorphism `Γ →* GL ι O`, sending `g` to the matrix of `ρ g` restricted to the lattice. -/
noncomputable def toGL (Λ : IntegralModel O ρ) (b : Basis ι O Λ.lattice) : Γ →* GL ι O :=
  (b.stabilizerMulEquivGL E).toMonoidHom.comp Λ.toStabilizer

/-- The matrix form sends `g` to the matrix in `b` of the action of `g` on the lattice. -/
@[simp]
theorem coe_toGL_apply (Λ : IntegralModel O ρ) (b : Basis ι O Λ.lattice) (g : Γ) :
    (Λ.toGL b g : Matrix ι ι O) = LinearMap.toMatrix b b (Λ.toContinuousRep g) := by
  have := Module.Free.of_basis b
  simp [toGL]

/-- The entries of the matrix form, read in `E`, are those of the matrix of `ρ g` in the
extended basis of `V`. -/
theorem map_toGL_apply (Λ : IntegralModel O ρ) (b : Basis ι O Λ.lattice) (g : Γ) :
    (Λ.toGL b g : Matrix ι ι O).map (algebraMap O E) =
      LinearMap.toMatrix (b.extendOfIsFullLattice E) (b.extendOfIsFullLattice E) (ρ g) := by
  rw [toGL, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, Basis.map_stabilizerMulEquivGL_apply]
  exact congrArg (LinearMap.toMatrix _ _) (LinearMap.ext (coe_toStabilizer_apply Λ g))

/-- **The matrix form of an integral model is continuous.** If `O` is a topological ring and the
lattice of `Λ` carries its `O`-module topology, as it does over the valuation ring of a field with
a valuative topology, then `g ↦ Λ.toGL b g` is continuous. -/
theorem continuous_toGL [ContinuousInv Γ] [TopologicalSpace O] [IsTopologicalSemiring O]
    (Λ : IntegralModel O ρ) [IsModuleTopology O Λ.lattice] (b : Basis ι O Λ.lattice) :
    Continuous (Λ.toGL b) :=
  (MonoidHom.continuous_iff_continuous_val _).2 <| by
    simpa only [coe_toGL_apply] using Λ.toContinuousRep.continuous_toMatrix b

end TauCeti.GaloisLattice.IntegralModel

namespace TauCeti.ContinuousRep

open ValuativeRel

variable {Γ : Type*} [Group Γ] [TopologicalSpace Γ] [ContinuousInv Γ] [CompactSpace Γ]
  {E V : Type*} [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [AddCommGroup V] [Module E V] [Module 𝒪[E] V] [IsScalarTower 𝒪[E] E V]
  [TopologicalSpace V] [IsModuleTopology E V] [FiniteDimensional E V]

/-- **The matrix form of the stable-lattice theorem.** A jointly continuous representation `ρ` of
a compact group `Γ` on a finite-dimensional vector space `V` over a nonarchimedean local field
`E` is, in a suitable basis of `V`, a continuous homomorphism `Γ → GL_n(𝒪[E])` with
`n = dim V`: the matrix of every `ρ g` has entries in `𝒪[E]`. The basis is a basis of a stable
lattice. -/
theorem exists_basis_continuousMonoidHom_GL (ρ : ContinuousRep Γ E V) :
    ∃ (c : Basis (Fin (finrank E V)) E V) (φ : Γ →ₜ* GL (Fin (finrank E V)) 𝒪[E]),
      ∀ g, (φ g : Matrix _ _ 𝒪[E]).map (algebraMap 𝒪[E] E) = LinearMap.toMatrix c c (ρ g) := by
  obtain ⟨Λ⟩ : Nonempty (GaloisLattice.IntegralModel 𝒪[E] ρ) := inferInstance
  have := IsLattice.free E Λ.lattice
  let b := Module.finBasisOfFinrankEq 𝒪[E] Λ.lattice
    (IsFullLattice.finrank_eq (K := E) (M := Λ.lattice))
  exact ⟨b.extendOfIsFullLattice E, ⟨Λ.toGL b, Λ.continuous_toGL b⟩, Λ.map_toGL_apply b⟩

end TauCeti.ContinuousRep
