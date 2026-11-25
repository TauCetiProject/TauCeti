/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Contractible
public import TauCeti.AlgebraicTopology.Singular.Torus.Lattice
public import TauCeti.Geometry.Lie.Exponential.CommutativeGroup.Basic
public import TauCeti.Topology.Algebra.Module.Quotient

/-!
# The first homology of a connected commutative Lie group

Let `G` be a connected commutative real Lie group with Lie algebra `𝔤`, and let
`Λ = ker (exp : 𝔤 → G)`, the kernel of `TauCeti.lieExpAddMonoidHom`; when `G` is compact, `Λ` is a
full lattice in `𝔤` (`TauCeti.isZLattice_ker_lieExpAddMonoidHom`). This file identifies the first
integral singular homology of `G` with `Λ`.

The exponential identifies the orbit space `AddAction.orbitRel.Quotient Λ 𝔤` of translation by
`Λ`, the standard model of `𝔤 / Λ` on which `AddSubgroup.orbitRelQuotientFirstHomologyEquiv`
computes first homology, with `G` (`TauCeti.lieExpOrbitRelQuotientHomeomorph`). It is the
composite of `Submodule.orbitRelQuotientContinuousAddEquiv`, which compares the orbit space with
the additive quotient `𝔤 ⧸ Λ`, and the first isomorphism theorem
`TauCeti.lieExpQuotientKerContinuousAddEquiv : 𝔤 ⧸ Λ ≃ₜ+ G`. Transporting first homology along it
gives `TauCeti.lieExpFirstHomologyEquiv : H₁(G; ℤ) ≃ₗ[ℤ] Λ`.

The class of a loop `γ` in `G` goes to `Γ 1 - Γ 0` for any continuous lift `Γ` of `γ` through the
exponential (`TauCeti.lieExpFirstHomologyEquiv_loopClass`). The identification is natural: a
continuous map `ψ : G → G'` and a continuous additive map `f : 𝔤 → 𝔤'` with
`ψ (exp X) = exp (f X)` act on first homology and on the lattices in the same way
(`TauCeti.lieExpFirstHomologyEquiv_singularHomologyMap_of_lieExp`). In particular the `n`-th power
map of `G` acts on `H₁(G; ℤ) ≃ Λ` as multiplication by `n`
(`TauCeti.lieExpFirstHomologyEquiv_singularHomologyMap_pow`).

This is the homology part of the lattice uniformization of compact connected commutative complex
Lie groups in the roadmap AbelianSchemesAndArithmeticModuli, §A5.1; it needs only the underlying
real Lie group. Singular chains with integer coefficients are defined on spaces in the lowest
universe, so the model spaces and `G` are types in `Type`.

## Main declarations

* `TauCeti.lieExpOrbitRelQuotientHomeomorph`: the homeomorphism `𝔤 / Λ ≃ₜ G`, `[X] ↦ exp X`.
* `TauCeti.lieExpFirstHomologyEquiv`: the isomorphism `H₁(G; ℤ) ≃ₗ[ℤ] Λ`.
* `TauCeti.lieExpFirstHomologyEquiv_loopClass`: the period displacement of a lifted loop.
* `TauCeti.lieExpFirstHomologyEquiv_singularHomologyMap_of_lieExp`: naturality.
* `TauCeti.lieExpFirstHomologyEquiv_singularHomologyMap_pow`: power maps act by multiplication.
-/

public section

noncomputable section

namespace TauCeti

open TauCeti.HurewiczOne
open scoped ContDiff Manifold

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [FiniteDimensional ℝ E] [LieGroup I ∞ G] [T2Space G] [BoundarylessManifold I G]
  [IsMulCommutative G] [PreconnectedSpace G]

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

/-- The exponential, read on the orbit space of translation by its kernel. -/
def lieExpOrbitRelQuotientMap :
    AddAction.orbitRel.Quotient (lieExpAddMonoidHom (I := I) (G := G)).ker
      (LeftInvariantDerivation I G) → G :=
  Quotient.lift (lieExp (I := I)) fun X Y h ↦ by
    obtain ⟨k, rfl⟩ := AddAction.orbitRel_apply.1 h
    change lieExp ((k : LeftInvariantDerivation I G) + Y) = lieExp Y
    rw [lieExp_add, mem_ker_lieExpAddMonoidHom.1 k.property, one_mul]

omit [PreconnectedSpace G] in
theorem lieExpOrbitRelQuotientMap_mk (X : LeftInvariantDerivation I G) :
    lieExpOrbitRelQuotientMap (I := I) (G := G)
        (_root_.Quotient.mk (AddAction.orbitRel (lieExpAddMonoidHom (I := I) (G := G)).ker _) X) =
      lieExp (I := I) X :=
  (rfl)

theorem lieExpOrbitRelQuotientMap_bijective :
    Function.Bijective (lieExpOrbitRelQuotientMap (I := I) (G := G)) := by
  refine ⟨fun x y hxy ↦ ?_, fun g ↦ ?_⟩
  · induction x using Quotient.inductionOn with | h X => ?_
    induction y using Quotient.inductionOn with | h Y => ?_
    rw [lieExpOrbitRelQuotientMap_mk, lieExpOrbitRelQuotientMap_mk] at hxy
    refine Quotient.sound (AddAction.orbitRel_apply.2 ⟨⟨X - Y, ?_⟩, sub_add_cancel X Y⟩)
    rw [mem_ker_lieExpAddMonoidHom, sub_eq_add_neg, lieExp_add, lieExp_neg, hxy, mul_inv_cancel]
  · obtain ⟨X, rfl⟩ := lieExp_surjective_of_preconnectedSpace (I := I) (G := G) g
    exact ⟨_, lieExpOrbitRelQuotientMap_mk X⟩

/-- **A connected commutative Lie group is the orbit space of its Lie algebra under translation by
the kernel of the exponential.** It sends the orbit of `X` to `exp X`
(`TauCeti.lieExpOrbitRelQuotientHomeomorph_mk`): the exponential is a continuous open surjection
whose fibres are the orbits of its kernel. -/
def lieExpOrbitRelQuotientHomeomorph :
    AddAction.orbitRel.Quotient (lieExpAddMonoidHom (I := I) (G := G)).ker
      (LeftInvariantDerivation I G) ≃ₜ G :=
  (Equiv.ofBijective _ lieExpOrbitRelQuotientMap_bijective).toHomeomorphOfContinuousOpen
    (AddAction.isOpenQuotientMap_quotientMk.isQuotientMap.continuous_iff.2
      (contMDiff_lieExp (I := I) (G := G)).continuous)
    (fun U hU ↦ by
      have : lieExpOrbitRelQuotientMap (I := I) (G := G) '' U =
          lieExp (I := I) '' (_root_.Quotient.mk _ ⁻¹' U) := by
        ext g
        constructor
        · rintro ⟨x, hx, rfl⟩
          induction x using Quotient.inductionOn with | h X => exact ⟨X, hx, rfl⟩
        · rintro ⟨X, hX, rfl⟩
          exact ⟨_, hX, rfl⟩
      exact this ▸ isOpenMap_lieExp (I := I) (G := G) _
        (hU.preimage AddAction.isOpenQuotientMap_quotientMk.continuous))

/-- `TauCeti.lieExpOrbitRelQuotientHomeomorph` sends the orbit of `X` to `exp X`. -/
@[simp]
theorem lieExpOrbitRelQuotientHomeomorph_mk (X : LeftInvariantDerivation I G) :
    lieExpOrbitRelQuotientHomeomorph (I := I) (G := G)
        (_root_.Quotient.mk (AddAction.orbitRel (lieExpAddMonoidHom (I := I) (G := G)).ker _) X) =
      lieExp (I := I) X :=
  (rfl)

/-- The inverse of `TauCeti.lieExpOrbitRelQuotientHomeomorph` sends `exp X` to the orbit of
`X`. -/
@[simp]
theorem lieExpOrbitRelQuotientHomeomorph_symm_lieExp (X : LeftInvariantDerivation I G) :
    (lieExpOrbitRelQuotientHomeomorph (I := I) (G := G)).symm (lieExp (I := I) X) =
      _root_.Quotient.mk (AddAction.orbitRel (lieExpAddMonoidHom (I := I) (G := G)).ker _) X := by
  rw [Homeomorph.symm_apply_eq, lieExpOrbitRelQuotientHomeomorph_mk]

/-- **The first homology of a connected commutative Lie group is the kernel of its exponential.**
First singular homology with integer coefficients is transported along
`TauCeti.lieExpOrbitRelQuotientHomeomorph` to the orbit space of translation by the kernel, where
`AddSubgroup.orbitRelQuotientFirstHomologyEquiv` identifies it with the kernel. -/
def lieExpFirstHomologyEquiv :
    ((singularChains ℤ).obj (TopCat.of G)).homology 1 ≃ₗ[ℤ]
      (lieExpAddMonoidHom (I := I) (G := G)).ker :=
  (LinearEquiv.ofLinearMap
      (ContinuousMap.singularHomologyMap ℤ 1
        ((lieExpOrbitRelQuotientHomeomorph (I := I) (G := G)).symm : C(_, _)))
      (ContinuousMap.singularHomologyMap ℤ 1
        (lieExpOrbitRelQuotientHomeomorph (I := I) (G := G) : C(_, _)))
      (by
        rw [← ContinuousMap.singularHomologyMap_comp', Homeomorph.symm_comp_toContinuousMap,
          ContinuousMap.singularHomologyMap_id'])
      (by
        rw [← ContinuousMap.singularHomologyMap_comp', Homeomorph.toContinuousMap_comp_symm,
          ContinuousMap.singularHomologyMap_id'])) ≪≫ₗ
    (lieExpAddMonoidHom (I := I) (G := G)).ker.orbitRelQuotientFirstHomologyEquiv

/-- On a class carried from the orbit space by `TauCeti.lieExpOrbitRelQuotientHomeomorph`,
`TauCeti.lieExpFirstHomologyEquiv` is `AddSubgroup.orbitRelQuotientFirstHomologyEquiv`. -/
@[simp]
theorem lieExpFirstHomologyEquiv_singularHomologyMap
    (c : ((singularChains ℤ).obj (TopCat.of (AddAction.orbitRel.Quotient
      (lieExpAddMonoidHom (I := I) (G := G)).ker (LeftInvariantDerivation I G)))).homology 1) :
    lieExpFirstHomologyEquiv (I := I) (G := G)
        (ContinuousMap.singularHomologyMap ℤ 1
          (lieExpOrbitRelQuotientHomeomorph (I := I) (G := G) : C(_, _)) c) =
      (lieExpAddMonoidHom (I := I) (G := G)).ker.orbitRelQuotientFirstHomologyEquiv c := by
  rw [lieExpFirstHomologyEquiv, LinearEquiv.trans_apply, LinearEquiv.coe_ofLinearMap,
    ← ContinuousMap.singularHomologyMap_comp, Homeomorph.symm_comp_toContinuousMap,
    ContinuousMap.singularHomologyMap_id]

/-- **Period displacement.** The homology class of a loop `γ` in `G` corresponds to `Γ 1 - Γ 0`,
for any continuous lift `Γ` of `γ` through the exponential. -/
theorem lieExpFirstHomologyEquiv_loopClass {g : G} (γ : Path g g)
    (Γ : C(unitInterval, LeftInvariantDerivation I G)) (hΓ : ∀ t, lieExp (I := I) (Γ t) = γ t) :
    (lieExpFirstHomologyEquiv (I := I) (G := G)
        (H₁AddEquivHomology ℤ (TopCat.of G) (loopClass ℤ (X := TopCat.of G) γ)) :
          LeftInvariantDerivation I G) = Γ 1 - Γ 0 := by
  rw [lieExpFirstHomologyEquiv, LinearEquiv.trans_apply, LinearEquiv.coe_ofLinearMap,
    ContinuousMap.singularHomologyMap_loopClass]
  refine AddSubgroup.orbitRelQuotientFirstHomologyEquiv_loopClass _ _ Γ (funext fun t ↦ ?_)
  simp [← hΓ t]

/-- **Naturality.** Let `ψ : G → G'` be a continuous map and `f : 𝔤 → 𝔤'` a continuous additive
map of Lie algebras with `ψ (exp X) = exp (f X)`. On first homology, `ψ` acts as `f` on the kernels
of the exponentials. -/
theorem lieExpFirstHomologyEquiv_singularHomologyMap_of_lieExp
    {E' : Type} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    {H' : Type} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
    {G' : Type} [TopologicalSpace G'] [ChartedSpace H' G'] [Group G']
    [FiniteDimensional ℝ E'] [LieGroup I' ∞ G'] [T2Space G'] [BoundarylessManifold I' G']
    [IsMulCommutative G'] [PreconnectedSpace G']
    (ψ : C(G, G')) (f : LeftInvariantDerivation I G →+ LeftInvariantDerivation I' G')
    (hf : Continuous f) (hψ : ∀ X, ψ (lieExp (I := I) X) = lieExp (I := I') (f X))
    (c : ((singularChains ℤ).obj (TopCat.of G)).homology 1) :
    (lieExpFirstHomologyEquiv (I := I') (G := G') (ContinuousMap.singularHomologyMap ℤ 1 ψ c) :
        LeftInvariantDerivation I' G') =
      f (lieExpFirstHomologyEquiv (I := I) (G := G) c) := by
  let e : C(_, G) := ⟨_, (lieExpOrbitRelQuotientHomeomorph (I := I) (G := G)).continuous⟩
  let e' : C(_, G') := ⟨_, (lieExpOrbitRelQuotientHomeomorph (I := I') (G := G')).continuous⟩
  -- Read `ψ` on the orbit spaces, where it is induced by `f`.
  let φ : C(_, _) :=
    (⟨_, (lieExpOrbitRelQuotientHomeomorph (I := I') (G := G')).symm.continuous⟩ : C(G', _)).comp
      (ψ.comp e)
  have hφ : ∀ v, φ (_root_.Quotient.mk _ v) =
      _root_.Quotient.mk (AddAction.orbitRel (lieExpAddMonoidHom (I := I') (G := G')).ker _)
        (f v) := fun v ↦ by
    simp [φ, e, hψ]
  obtain ⟨c, rfl⟩ : ∃ c', ContinuousMap.singularHomologyMap ℤ 1 e c' = c :=
    ⟨ContinuousMap.singularHomologyMap ℤ 1
      ⟨_, (lieExpOrbitRelQuotientHomeomorph (I := I) (G := G)).symm.continuous⟩ c, by
      rw [← ContinuousMap.singularHomologyMap_comp, Homeomorph.toContinuousMap_comp_symm,
        ContinuousMap.singularHomologyMap_id]⟩
  have hcomp : ψ.comp e = e'.comp φ := by
    ext x
    simp [φ, e, e']
  rw [← ContinuousMap.singularHomologyMap_comp, hcomp, ContinuousMap.singularHomologyMap_comp,
    lieExpFirstHomologyEquiv_singularHomologyMap, lieExpFirstHomologyEquiv_singularHomologyMap]
  exact AddSubgroup.orbitRelQuotientFirstHomologyEquiv_singularHomologyMap _ _ f hf φ hφ c

/-- **Power maps act by multiplication.** The `n`-th power map of `G` acts on first homology,
read in the kernel of the exponential through `TauCeti.lieExpFirstHomologyEquiv`, as
multiplication by `n`. -/
theorem lieExpFirstHomologyEquiv_singularHomologyMap_pow (n : ℕ)
    (c : ((singularChains ℤ).obj (TopCat.of G)).homology 1) :
    lieExpFirstHomologyEquiv (I := I) (G := G)
        (ContinuousMap.singularHomologyMap ℤ 1 ⟨(· ^ n), by
          have := topologicalGroup_of_lieGroup I ∞ (G := G)
          exact continuous_pow n⟩ c) =
      n • lieExpFirstHomologyEquiv (I := I) (G := G) c := by
  apply Subtype.ext
  rw [lieExpFirstHomologyEquiv_singularHomologyMap_of_lieExp (I' := I) _
    (nsmulAddMonoidHom n) (continuous_const_smul n) (fun X ↦ ?_) c]
  · rfl
  · rw [ContinuousMap.coe_mk, nsmulAddMonoidHom_apply, ← toMul_ofMul (lieExp (I := I) (n • X)),
      ← lieExpAddMonoidHom_apply, map_nsmul, lieExpAddMonoidHom_apply, toMul_nsmul, toMul_ofMul]

end TauCeti
