/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Contractible
public import TauCeti.AlgebraicTopology.Singular.Homotopy.Invariance
public import TauCeti.AlgebraicTopology.Singular.Torus.Lattice
public import TauCeti.Geometry.Lie.Exponential.CommutativeGroup.Basic
public import TauCeti.Topology.Algebra.GroupAction.Quotient

/-!
# The first homology of a connected commutative Lie group

Let `G` be a connected commutative real Lie group with Lie algebra `𝔤`, and let
`Λ = ker (exp : 𝔤 → G)`, the kernel of `TauCeti.lieExpAddMonoidHom`; when `G` is compact, `Λ` is a
full lattice in `𝔤` (`TauCeti.isZLattice_ker_lieExpAddMonoidHom`). This file identifies the first
integral singular homology of `G` with `Λ`.

The exponential is a continuous open surjection whose fibres are the orbits of translation by
`Λ`, so it induces a homeomorphism `TauCeti.lieExpOrbitRelQuotientHomeomorph` from the orbit space
`AddAction.orbitRel.Quotient Λ 𝔤` onto `G`, sending the orbit of `X` to `exp X`. That orbit space
is the standard model of `𝔤 / Λ` on which `AddSubgroup.orbitRelQuotientFirstHomologyEquiv` computes
first homology. Transporting first homology along the homeomorphism gives
`TauCeti.lieExpFirstHomologyEquiv : H₁(G; ℤ) ≃ₗ[ℤ] Λ`.

The class of a loop `γ` in `G` goes to `Γ 1 - Γ 0` for any continuous lift `Γ` of `γ` through the
exponential (`TauCeti.lieExpFirstHomologyEquiv_loopClass`). The identification is natural: a
continuous map `ψ : G → G'` and a continuous additive map `f : 𝔤 → 𝔤'` with
`ψ (exp X) = exp (f X)` act on first homology and on the lattices in the same way
(`TauCeti.lieExpFirstHomologyEquiv_singularHomologyMap_of_lieExp`). In particular the `n`-th power
map of `G` acts on `H₁(G; ℤ) ≃ Λ` as multiplication by `n`
(`TauCeti.lieExpFirstHomologyEquiv_singularHomologyMap_pow`).

This is the homology half of the lattice uniformization of compact connected commutative complex
Lie groups; it needs only the underlying real Lie group. Singular chains with integer coefficients
are defined on spaces in the lowest universe, so the model spaces and `G` are types in `Type`.

## Main declarations

* `TauCeti.lieExpOrbitRelQuotientHomeomorph`: the homeomorphism `𝔤 / Λ ≃ₜ G`, `[X] ↦ exp X`.
* `TauCeti.lieExpFirstHomologyEquiv`: the isomorphism `H₁(G; ℤ) ≃ₗ[ℤ] Λ`.
* `TauCeti.lieExpFirstHomologyEquiv_loopClass`: the period displacement of a lifted loop.
* `TauCeti.lieExpFirstHomologyEquiv_singularHomologyMap_of_lieExp`: naturality.
* `TauCeti.lieExpFirstHomologyEquiv_singularHomologyMap_pow`: power maps act by multiplication.

## References

* Stanford VIGRE notes, *Complex theory of abelian varieties* (2004), Theorem 1.8 and § 1.2,
  pp. 2–4, <https://math.stanford.edu/~conrad/vigregroup/vigre04/abvaran.pdf>: a connected
  compact commutative complex Lie group is `𝔤 / Λ` through its exponential, with `Λ = H₁`.
* Christina Birkenhake and Herbert Lange, *Complex Abelian Varieties*, second edition,
  Grundlehren der mathematischen Wissenschaften 302, Springer, 2004, Chapter 1, Section 1.1.
* T. Bröcker and T. tom Dieck, *Representations of Compact Lie Groups*, Springer GTM 98 (1985),
  Chapter I, § 3 (The Exponential Map).
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

omit [PreconnectedSpace G] in
/-- Two derivations have the same exponential exactly when they differ by an element of the kernel
of the exponential. -/
private theorem lieExp_eq_lieExp_iff_mem_orbit (X Y : LeftInvariantDerivation I G) :
    lieExp (I := I) X = lieExp Y ↔
      X ∈ AddAction.orbit (lieExpAddMonoidHom (I := I) (G := G)).ker Y := by
  rw [AddAction.mem_orbit_iff]
  constructor
  · intro h
    refine ⟨⟨X - Y, ?_⟩, by rw [AddSubgroup.vadd_def, vadd_eq_add, sub_add_cancel]⟩
    rw [mem_ker_lieExpAddMonoidHom, sub_eq_add_neg, lieExp_add, lieExp_neg, h, mul_inv_cancel]
  · rintro ⟨k, rfl⟩
    rw [AddSubgroup.vadd_def, vadd_eq_add, lieExp_add, mem_ker_lieExpAddMonoidHom.1 k.property,
      one_mul]

/-- **A connected commutative Lie group is the orbit space of its Lie algebra under translation by
the kernel of the exponential.** It sends the orbit of `X` to `exp X`
(`TauCeti.lieExpOrbitRelQuotientHomeomorph_mk`): the exponential is a continuous open surjection
whose fibres are the orbits of its kernel. -/
def lieExpOrbitRelQuotientHomeomorph :
    AddAction.orbitRel.Quotient (lieExpAddMonoidHom (I := I) (G := G)).ker
      (LeftInvariantDerivation I G) ≃ₜ G :=
  ((isOpenMap_lieExp (I := I) (G := G)).isQuotientMap
      (contMDiff_lieExp (I := I) (G := G)).continuous
      lieExp_surjective_of_preconnectedSpace).addOrbitRelQuotientHomeomorph
    lieExp_eq_lieExp_iff_mem_orbit

/-- `TauCeti.lieExpOrbitRelQuotientHomeomorph` sends the orbit of `X` to `exp X`. -/
@[simp]
theorem lieExpOrbitRelQuotientHomeomorph_mk (X : LeftInvariantDerivation I G) :
    lieExpOrbitRelQuotientHomeomorph (I := I) (G := G)
        (_root_.Quotient.mk (AddAction.orbitRel (lieExpAddMonoidHom (I := I) (G := G)).ker _) X) =
      lieExp (I := I) X :=
  Topology.IsQuotientMap.addOrbitRelQuotientHomeomorph_mk _ _ X

/-- The inverse of `TauCeti.lieExpOrbitRelQuotientHomeomorph` sends `exp X` to the orbit of
`X`. -/
@[simp]
theorem lieExpOrbitRelQuotientHomeomorph_symm_lieExp (X : LeftInvariantDerivation I G) :
    (lieExpOrbitRelQuotientHomeomorph (I := I) (G := G)).symm (lieExp (I := I) X) =
      _root_.Quotient.mk (AddAction.orbitRel (lieExpAddMonoidHom (I := I) (G := G)).ker _) X :=
  Topology.IsQuotientMap.addOrbitRelQuotientHomeomorph_symm_apply _ _ X

/-- **The first homology of a connected commutative Lie group is the kernel of its exponential.**
First singular homology with integer coefficients is transported along
`TauCeti.lieExpOrbitRelQuotientHomeomorph` to the orbit space of translation by the kernel, where
`AddSubgroup.orbitRelQuotientFirstHomologyEquiv` identifies it with the kernel. -/
def lieExpFirstHomologyEquiv :
    ((singularChains ℤ).obj (TopCat.of G)).homology 1 ≃ₗ[ℤ]
      (lieExpAddMonoidHom (I := I) (G := G)).ker :=
  -- The homology groups are written as `(singularChains ℤ).obj X).homology 1` rather than through
  -- `singularHomologyFunctor`, as in `AddSubgroup.orbitRelQuotientFirstHomologyEquiv`, so that
  -- `LinearEquiv.trans_apply` unfolds the composite.
  LinearEquiv.trans
    (M₁ := ((singularChains ℤ).obj (TopCat.of G)).homology 1)
    (M₂ := ((singularChains ℤ).obj (TopCat.of (AddAction.orbitRel.Quotient
      (lieExpAddMonoidHom (I := I) (G := G)).ker (LeftInvariantDerivation I G)))).homology 1)
    ((lieExpOrbitRelQuotientHomeomorph (I := I) (G := G)).toHomotopyEquiv.singularHomologyIso
      (ModuleCat.of ℤ ℤ) 1).symm.toLinearEquiv
    (lieExpAddMonoidHom (I := I) (G := G)).ker.orbitRelQuotientFirstHomologyEquiv

/-- `TauCeti.lieExpFirstHomologyEquiv` moves a class to the orbit space along the inverse of
`TauCeti.lieExpOrbitRelQuotientHomeomorph` and applies
`AddSubgroup.orbitRelQuotientFirstHomologyEquiv` there. -/
theorem lieExpFirstHomologyEquiv_apply (c : ((singularChains ℤ).obj (TopCat.of G)).homology 1) :
    lieExpFirstHomologyEquiv (I := I) (G := G) c =
      (lieExpAddMonoidHom (I := I) (G := G)).ker.orbitRelQuotientFirstHomologyEquiv
        (ContinuousMap.singularHomologyMap ℤ 1
          ((lieExpOrbitRelQuotientHomeomorph (I := I) (G := G)).symm : C(_, _)) c) := by
  rw [lieExpFirstHomologyEquiv]
  -- The composite is typed at `((singularChains ℤ).obj X).homology 1` while `singularHomologyIso`
  -- is typed at `singularHomologyFunctor`, so `rw` cannot match the lemmas about the composite and
  -- the iso; they are chained by `Eq.trans` instead.
  refine (LinearEquiv.trans_apply c).trans
    (congrArg _ ((CategoryTheory.Iso.toLinearEquiv_apply _ c).trans ?_))
  rw [CategoryTheory.Iso.symm_hom, ContinuousMap.HomotopyEquiv.singularHomologyIso_inv]
  -- The homotopy inverse `invFun` of `e.toHomotopyEquiv` is the continuous map `e.symm`.
  exact LinearMap.congr_fun
    (ContinuousMap.singularHomologyMap_eq_singularHomologyFunctor_map ℤ 1 _).symm c

/-- The inverse of `TauCeti.lieExpFirstHomologyEquiv` sends `λ` to the class that
`AddSubgroup.orbitRelQuotientFirstHomologyEquiv` attaches to `λ` on the orbit space, carried to `G`
by `TauCeti.lieExpOrbitRelQuotientHomeomorph`. -/
theorem lieExpFirstHomologyEquiv_symm_apply (l : (lieExpAddMonoidHom (I := I) (G := G)).ker) :
    (lieExpFirstHomologyEquiv (I := I) (G := G)).symm l =
      ContinuousMap.singularHomologyMap ℤ 1
        (lieExpOrbitRelQuotientHomeomorph (I := I) (G := G) : C(_, _))
        ((lieExpAddMonoidHom (I := I) (G := G)).ker.orbitRelQuotientFirstHomologyEquiv.symm l) := by
  rw [lieExpFirstHomologyEquiv]
  -- As in `TauCeti.lieExpFirstHomologyEquiv_apply`, the lemmas are chained by `Eq.trans`; the
  -- inverse of `i.symm.toLinearEquiv` is `i.toLinearEquiv`
  -- (`CategoryTheory.Iso.toLinearEquiv_symm`).
  refine (LinearEquiv.symm_trans_apply l).trans
    ((CategoryTheory.Iso.toLinearEquiv_apply _ _).trans ?_)
  rw [ContinuousMap.HomotopyEquiv.singularHomologyIso_hom]
  -- The forward map `toFun` of `e.toHomotopyEquiv` is the continuous map `e`.
  exact LinearMap.congr_fun
    (ContinuousMap.singularHomologyMap_eq_singularHomologyFunctor_map ℤ 1 _).symm _

/-- On a class carried from the orbit space by `TauCeti.lieExpOrbitRelQuotientHomeomorph`,
`TauCeti.lieExpFirstHomologyEquiv` is `AddSubgroup.orbitRelQuotientFirstHomologyEquiv`. -/
@[simp]
theorem lieExpFirstHomologyEquiv_singularHomologyMap_lieExpOrbitRelQuotientHomeomorph
    (c : ((singularChains ℤ).obj (TopCat.of (AddAction.orbitRel.Quotient
      (lieExpAddMonoidHom (I := I) (G := G)).ker (LeftInvariantDerivation I G)))).homology 1) :
    lieExpFirstHomologyEquiv (I := I) (G := G)
        (ContinuousMap.singularHomologyMap ℤ 1
          (lieExpOrbitRelQuotientHomeomorph (I := I) (G := G) : C(_, _)) c) =
      (lieExpAddMonoidHom (I := I) (G := G)).ker.orbitRelQuotientFirstHomologyEquiv c := by
  rw [lieExpFirstHomologyEquiv_apply, ← ContinuousMap.singularHomologyMap_comp,
    Homeomorph.symm_comp_toContinuousMap, ContinuousMap.singularHomologyMap_id]

/-- **Period displacement.** The homology class of a loop `γ` in `G` corresponds to `Γ 1 - Γ 0`,
for any continuous lift `Γ` of `γ` through the exponential. -/
theorem lieExpFirstHomologyEquiv_loopClass {g : G} (γ : Path g g)
    (Γ : C(unitInterval, LeftInvariantDerivation I G)) (hΓ : ∀ t, lieExp (I := I) (Γ t) = γ t) :
    (lieExpFirstHomologyEquiv (I := I) (G := G)
        (H₁AddEquivHomology ℤ (TopCat.of G) (loopClass ℤ (X := TopCat.of G) γ)) :
          LeftInvariantDerivation I G) = Γ 1 - Γ 0 := by
  rw [lieExpFirstHomologyEquiv_apply, ContinuousMap.singularHomologyMap_loopClass]
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
  -- The homeomorphisms with the orbit spaces, as continuous maps. Their types are written out
  -- because the coercion from a homeomorphism does not elaborate against an unknown domain.
  let e : C(AddAction.orbitRel.Quotient (lieExpAddMonoidHom (I := I) (G := G)).ker
      (LeftInvariantDerivation I G), G) := lieExpOrbitRelQuotientHomeomorph (I := I) (G := G)
  let e' : C(AddAction.orbitRel.Quotient (lieExpAddMonoidHom (I := I') (G := G')).ker
      (LeftInvariantDerivation I' G'), G') := lieExpOrbitRelQuotientHomeomorph (I := I') (G := G')
  -- Read `ψ` on the orbit spaces, where it is induced by `f`.
  let φ : C(_, _) :=
    ((lieExpOrbitRelQuotientHomeomorph (I := I') (G := G')).symm :
      C(G', AddAction.orbitRel.Quotient (lieExpAddMonoidHom (I := I') (G := G')).ker
        (LeftInvariantDerivation I' G'))).comp (ψ.comp e)
  have hφ : ∀ v, φ (_root_.Quotient.mk _ v) =
      _root_.Quotient.mk (AddAction.orbitRel (lieExpAddMonoidHom (I := I') (G := G')).ker _)
        (f v) := fun v ↦ by
    simp [φ, e, hψ]
  -- Every class comes from the orbit space, by `TauCeti.lieExpFirstHomologyEquiv_symm_apply`.
  obtain ⟨c, rfl⟩ : ∃ c', ContinuousMap.singularHomologyMap ℤ 1 e c' = c :=
    ⟨_, by rw [← lieExpFirstHomologyEquiv_symm_apply, LinearEquiv.symm_apply_apply]⟩
  have hcomp : ψ.comp e = e'.comp φ := by
    ext x
    simp [φ, e, e']
  rw [← ContinuousMap.singularHomologyMap_comp, hcomp, ContinuousMap.singularHomologyMap_comp,
    lieExpFirstHomologyEquiv_singularHomologyMap_lieExpOrbitRelQuotientHomeomorph,
    lieExpFirstHomologyEquiv_singularHomologyMap_lieExpOrbitRelQuotientHomeomorph]
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
  · simp
  · rw [ContinuousMap.coe_mk, nsmulAddMonoidHom_apply, lieExp_nsmul]

end TauCeti
