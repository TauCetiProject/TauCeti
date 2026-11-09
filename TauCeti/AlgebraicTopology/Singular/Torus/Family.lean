/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Contractible
public import Mathlib.Topology.Homotopy.Lifting
public import TauCeti.Algebra.Module.ZLattice.Family.AffineAction
public import TauCeti.Algebra.Module.ZLattice.Family.Fiber
public import TauCeti.AlgebraicTopology.Singular.Homotopy.Invariance
public import TauCeti.AlgebraicTopology.Singular.Torus.Lattice

/-!
# The canonical marking of the fibres of a family of tori

Let `P : Y → (Λ →ₗ[ℤ] E)` be a period family: each `P y` is injective with discrete range, and
each period `y ↦ P y l` is continuous. The fibre over `y` of the standard orbit quotient
`(Y × E)/Λ → Y` is the torus `T_y = E / LinearMap.range (P y)`
(`TauCeti.torusFamilyFiberHomeomorph`). This file constructs the canonical **marking**

`H₁(T_y; ℤ) ≃ₗ[ℤ] Λ`

of each fibre (`TauCeti.torusFamilyMarking`) and proves that these markings are compatible with
one another as `y` varies.

The marking is computed by lifting loops: a loop `γ` in the fibre over `y`, written
`γ t = [y, Γ t]` for a continuous `Γ : I → E`, has period displacement `Γ 1 - Γ 0 ∈ range (P y)`,
and its class is sent to the unique `l : Λ` with `P y l = Γ 1 - Γ 0`
(`TauCeti.torusFamilyMarking_loopClass`). Under the identification of the fibre with
`E / LinearMap.range (P y)` the marking is the identification `H₁(E / L; ℤ) ≃ L` of
`AddSubgroup.orbitRelQuotientFirstHomologyEquiv` followed by `P y⁻¹`
(`TauCeti.torusFamilyMarking_singularHomologyMap`). No basis of `Λ` is chosen.

For a continuous family of full lattices over a locally compact Hausdorff base, the markings at
different points agree on loops which are freely homotopic in the total space
(`TauCeti.torusFamilyMarking_loopClass_eq_of_homotopy`). In particular, carrying a loop along a
path in the base, through loops in the fibres, does not change its marking: the globally marked
family has trivial monodromy. The proof lifts the homotopy through the orbit projection
`Y × E → (Y × E)/Λ`, a covering map because the period action is free and properly
discontinuous, with Mathlib's homotopy lifting `IsCoveringMap.liftHomotopy`, and compares the two
edges of the lift by uniqueness of lifts, `IsCoveringMap.eq_of_comp_eq`.

The markings are natural in maps of fibres induced by affine maps of `E`: a continuous map from
the fibre over `y` to the fibre over `y'` sending `[y, v]` to `[y', A v + β]`, for a continuous
additive `A`, acts on periods by `A`, whatever the translation `β`
(`TauCeti.torusFamilyMarking_singularHomologyMap_of_affine`). For an action of a monoid `Γ` on
`Y` lifted to the family by affine maps `[y, v] ↦ R g y v +ᵥ b g y`
(`TauCeti.torusFamilyAffineMap`) with periods equivariant for `ρ : Representation ℤ Γ Λ`, the
markings are therefore equivariant: `g` acts on them by `ρ g`
(`TauCeti.torusFamilyMarking_singularHomologyMap_affineMap`). Combined with trivial monodromy
of the globally marked family, this computes the monodromy of the family over the quotient
base: a loop over `y₀` carried by a free homotopy in the total space to a loop over `y₁`, and
identified back with the fibre over `y₀ = g • y₁` by the action of `g`, has its marking
transformed by `ρ g` (`TauCeti.torusFamilyMarking_singularHomologyMap_loopClass_of_homotopy`).
For a group action and a free homotopy ending at a loop over `h • y₀`, this transport is `ρ h⁻¹`.

Singular chains with integer coefficients are defined on spaces in the lowest universe, so `Y`
and `E` are types in `Type`.

## Main declarations

* `TauCeti.torusFamilyMarking`: the marking `H₁(T_y; ℤ) ≃ₗ[ℤ] Λ` of the fibre over `y`.
* `TauCeti.torusFamilyMarking_loopClass`: the marking of a loop is its period displacement.
* `TauCeti.torusFamilyMarking_singularHomologyMap`: compatibility with the identification of the
  fibre with `E / LinearMap.range (P y)`.
* `TauCeti.torusFamilyMarking_loopClass_eq_of_homotopy`: freely homotopic loops in two fibres
  have the same marking.
* `TauCeti.torusFamilyMarking_singularHomologyMap_of_affine`: naturality of the marking in maps
  of fibres induced by affine maps of `E`.
* `TauCeti.torusFamilyMarking_singularHomologyMap_affineMap`: equivariance of the marking under
  an affine action, which acts on it through `ρ`.
* `TauCeti.torusFamilyMarking_singularHomologyMap_loopClass_of_homotopy`: the monodromy of an
  affine action on the marking.

## References

* Christina Birkenhake and Herbert Lange, *Complex Abelian Varieties*, second edition,
  Grundlehren der mathematischen Wissenschaften 302, Springer, 2004, Chapter 1, Section 1.1 and
  Chapter 8 (families of complex tori given by period matrices).
* A. Hatcher, *Algebraic Topology*, Proposition 1.30 (homotopy lifting) and Proposition 1.34
  (uniqueness of lifts).
-/

public section

noncomputable section

open Function unitInterval TauCeti.HurewiczOne

namespace TauCeti

section Marking

variable {Y E : Type} [TopologicalSpace Y] [AddCommGroup E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [SimplyConnectedSpace E] {Λ : Type*} [AddCommGroup Λ]
  (P : Y → Λ →ₗ[ℤ] E) [∀ y, DiscreteTopology (LinearMap.range (P y))]
  (hcont : ∀ l, Continuous fun y ↦ P y l) (hinj : ∀ y, Injective (P y)) (y : Y)

/-- The **canonical marking** of the fibre over `y` of a period family: the identification
`H₁(T_y; ℤ) ≃ₗ[ℤ] Λ` of the first integral homology of the torus `T_y` over `y` with the lattice
`Λ`. It identifies the fibre with `E / LinearMap.range (P y)`, applies
`AddSubgroup.orbitRelQuotientFirstHomologyEquiv`, and pulls the period back along the injective
map `P y`. The class of a loop goes to its period displacement
(`TauCeti.torusFamilyMarking_loopClass`). -/
def torusFamilyMarking :
    letI := periodAddAction P
    ((singularChains ℤ).obj (TopCat.of
      {z : AddAction.orbitRel.Quotient Λ (Y × E) | torusFamilyProjection P z = y})).homology 1
      ≃ₗ[ℤ] Λ :=
  letI := periodAddAction P
  -- The homology groups are written as `(singularChains ℤ).obj X).homology 1` rather than through
  -- `singularHomologyFunctor`, as in `AddSubgroup.orbitRelQuotientFirstHomologyEquiv`, so that
  -- `LinearEquiv.trans_apply` unfolds the composite.
  (LinearEquiv.trans
    (M₁ := ((singularChains ℤ).obj (TopCat.of
      {z : AddAction.orbitRel.Quotient Λ (Y × E) | torusFamilyProjection P z = y})).homology 1)
    (M₂ := ((singularChains ℤ).obj (TopCat.of (AddAction.orbitRel.Quotient
      (LinearMap.range (P y)).toAddSubgroup E))).homology 1)
    ((torusFamilyFiberHomeomorph P y hcont).toHomotopyEquiv.singularHomologyIso
      (ModuleCat.of ℤ ℤ) 1).symm.toLinearEquiv
    (LinearMap.range (P y)).toAddSubgroup.orbitRelQuotientFirstHomologyEquiv) ≪≫ₗ
    (LinearEquiv.ofInjective (P y) (hinj y)).symm

/-- The canonical marking moves a class to `E / LinearMap.range (P y)` along the inverse fibre
homeomorphism, identifies it with a period there, and takes the corresponding element of `Λ`. -/
theorem torusFamilyMarking_apply
    (c : letI := periodAddAction P
      ((singularChains ℤ).obj (TopCat.of
        {z : AddAction.orbitRel.Quotient Λ (Y × E) | torusFamilyProjection P z = y})).homology 1) :
    torusFamilyMarking P hcont hinj y c =
      (LinearEquiv.ofInjective (P y) (hinj y)).symm
        ((LinearMap.range (P y)).toAddSubgroup.orbitRelQuotientFirstHomologyEquiv
          (ContinuousMap.singularHomologyMap ℤ 1
            ((torusFamilyFiberHomeomorph P y hcont).symm : C(_, _)) c)) := by
  rw [torusFamilyMarking, LinearEquiv.trans_apply]
  refine congrArg _ ((LinearEquiv.trans_apply c).trans (congrArg _ ?_))
  exact congrArg (fun f ↦ ModuleCat.Hom.hom f c)
    ((torusFamilyFiberHomeomorph P y hcont).toHomotopyEquiv.singularHomologyIso_inv
      (ModuleCat.of ℤ ℤ) 1)

/-- The inverse of the canonical marking sends `l` to the class corresponding to the period
`P y l`, carried into the fibre by the fibre homeomorphism. -/
theorem torusFamilyMarking_symm_apply (l : Λ) :
    (torusFamilyMarking P hcont hinj y).symm l =
      ContinuousMap.singularHomologyMap ℤ 1 (torusFamilyFiberHomeomorph P y hcont : C(_, _))
        ((LinearMap.range (P y)).toAddSubgroup.orbitRelQuotientFirstHomologyEquiv.symm
          (LinearEquiv.ofInjective (P y) (hinj y) l)) := by
  rw [torusFamilyMarking, LinearEquiv.symm_trans_apply, LinearEquiv.symm_symm]
  refine (LinearEquiv.symm_trans_apply _).trans ?_
  exact congrArg (fun f ↦ ModuleCat.Hom.hom f _)
    ((torusFamilyFiberHomeomorph P y hcont).toHomotopyEquiv.singularHomologyIso_hom
      (ModuleCat.of ℤ ℤ) 1)

/-- The period of the marking of a class is the period attached to it on
`E / LinearMap.range (P y)`. -/
private theorem period_torusFamilyMarking
    (c : letI := periodAddAction P
      ((singularChains ℤ).obj (TopCat.of
        {z : AddAction.orbitRel.Quotient Λ (Y × E) | torusFamilyProjection P z = y})).homology 1) :
    P y (torusFamilyMarking P hcont hinj y c) =
      (LinearMap.range (P y)).toAddSubgroup.orbitRelQuotientFirstHomologyEquiv
        (ContinuousMap.singularHomologyMap ℤ 1
          ((torusFamilyFiberHomeomorph P y hcont).symm : C(_, _)) c) := by
  rw [torusFamilyMarking_apply, ← LinearEquiv.ofInjective_apply (h := hinj y),
    LinearEquiv.apply_symm_apply]

/-- **Compatibility with the fibre identification.** Transported to the fibre over `y` by
`TauCeti.torusFamilyFiberHomeomorph`, a class of `H₁(E / LinearMap.range (P y); ℤ)` is marked by
the element of `Λ` whose period is the one given by
`AddSubgroup.orbitRelQuotientFirstHomologyEquiv`. -/
@[simp]
theorem torusFamilyMarking_singularHomologyMap
    (c : ((singularChains ℤ).obj (TopCat.of
      (AddAction.orbitRel.Quotient (LinearMap.range (P y)) E))).homology 1) :
    P y (torusFamilyMarking P hcont hinj y (ContinuousMap.singularHomologyMap ℤ 1
      (torusFamilyFiberHomeomorph P y hcont : C(_, _)) c)) =
      ((LinearMap.range (P y)).toAddSubgroup.orbitRelQuotientFirstHomologyEquiv c : E) := by
  let _ := periodAddAction P
  rw [period_torusFamilyMarking, ← ContinuousMap.singularHomologyMap_comp]
  simp only [ContinuousMap.singularHomologyMap, Homeomorph.symm_comp_toContinuousMap,
    TopCat.ofHom_id, CategoryTheory.Functor.map_id]
  rw [HomologicalComplex.homologyMap_id, ModuleCat.hom_id, LinearMap.id_apply]

/-- **Period displacement.** Let `γ` be a loop in the fibre over `y`, written `γ t = [y, Γ t]`
for a continuous `Γ : I → E`. Its class is marked by the element of `Λ` whose period at `y` is
the displacement `Γ 1 - Γ 0`. -/
theorem torusFamilyMarking_loopClass
    {z : letI := periodAddAction P
      {z : AddAction.orbitRel.Quotient Λ (Y × E) | torusFamilyProjection P z = y}}
    (γ : Path z z) (Γ : C(I, E))
    (hΓ : letI := periodAddAction P
      ∀ t, (γ t : AddAction.orbitRel.Quotient Λ (Y × E)) = Quotient.mk _ (y, Γ t)) :
    P y (torusFamilyMarking P hcont hinj y (H₁AddEquivHomology _ (loopClass γ))) =
      Γ 1 - Γ 0 := by
  let _ := periodAddAction P
  rw [period_torusFamilyMarking, ContinuousMap.singularHomologyMap_loopClass]
  refine AddSubgroup.orbitRelQuotientFirstHomologyEquiv_loopClass _ _ Γ (funext fun t ↦ ?_)
  simp only [Function.comp_apply, Path.map_coe, ContinuousMap.coe_ofClass]
  rw [eq_comm, Homeomorph.symm_apply_eq]
  ext
  rw [hΓ]
  -- The orbit space of `(LinearMap.range (P y)).toAddSubgroup` used by the homology equivalence
  -- is definitionally that of the submodule `LinearMap.range (P y)` used by the fibre map.
  exact (congrArg Subtype.val (torusFamilyFiberHomeomorph_mk P y hcont (Γ t))).symm

end Marking

section Naturality

variable {Y E : Type} [TopologicalSpace Y] [AddCommGroup E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [SimplyConnectedSpace E] {Λ : Type*} [AddCommGroup Λ]
  (P : Y → Λ →ₗ[ℤ] E) [∀ y, DiscreteTopology (LinearMap.range (P y))]
  (hcont : ∀ l, Continuous fun y ↦ P y l) (hinj : ∀ y, Injective (P y))

include hcont in
/-- Every first homology class of the fibre over `y` is the class of a loop `t ↦ [y, Γ t]` for a
continuous `Γ : I → E`: by the Hurewicz theorem it is the class of a loop in
`E / LinearMap.range (P y)`, which lifts to `E` through the orbit projection, a covering map. -/
private theorem exists_loopClass_eq (y : Y)
    (c : letI := periodAddAction P
      ((singularChains ℤ).obj (TopCat.of
        {z : AddAction.orbitRel.Quotient Λ (Y × E) | torusFamilyProjection P z = y})).homology 1) :
    letI := periodAddAction P
    ∃ (z : {z : AddAction.orbitRel.Quotient Λ (Y × E) | torusFamilyProjection P z = y})
      (γ : Path z z) (Γ : C(I, E)),
      (∀ t, (γ t : AddAction.orbitRel.Quotient Λ (Y × E)) = Quotient.mk _ (y, Γ t)) ∧
        H₁AddEquivHomology _ (loopClass γ) = c := by
  let _ := periodAddAction P
  let L := (LinearMap.range (P y)).toAddSubgroup
  -- The orbit space of `L` is definitionally that of the submodule `LinearMap.range (P y)`.
  let h : AddAction.orbitRel.Quotient L E ≃ₜ
      {z : AddAction.orbitRel.Quotient Λ (Y × E) | torusFamilyProjection P z = y} :=
    torusFamilyFiberHomeomorph P y hcont
  let x : AddAction.orbitRel.Quotient L E := Quotient.mk _ 0
  obtain ⟨a, ha⟩ := (hurewiczHomologyAddEquiv (X := TopCat.of (AddAction.orbitRel.Quotient L E))
    x).surjective (ContinuousMap.singularHomologyMap ℤ 1 (h.symm : C(_, _)) c)
  obtain ⟨a, rfl⟩ := Additive.ofMul.surjective a
  -- `Abelianization G` is the quotient of `G` by its commutator subgroup and `Abelianization.of`
  -- is `QuotientGroup.mk'`; Mathlib states no surjectivity lemma for `Abelianization.of` itself.
  obtain ⟨a, rfl⟩ : ∃ a', Abelianization.of a' = a := QuotientGroup.mk'_surjective _ a
  obtain ⟨a, rfl⟩ : ∃ p, FundamentalGroup.fromPath p = a := ⟨a.toPath, rfl⟩
  induction a using Path.Homotopic.Quotient.ind with | mk γ =>
  rw [hurewiczHomologyAddEquiv_ofMul_of_mk] at ha
  have cov := L.isAddQuotientCoveringMap_quotientMk.isCoveringMap
  let Γ := cov.liftPath γ.toContinuousMap 0 γ.source
  refine ⟨h x, γ.map h.continuous, Γ, fun t ↦ ?_, ?_⟩
  · have hΓt : (Quotient.mk _ (Γ t) : AddAction.orbitRel.Quotient L E) = γ t :=
      congr_fun (cov.liftPath_lifts γ.toContinuousMap 0 γ.source) t
    rw [Path.map_coe, Function.comp_apply, ← hΓt]
    exact congrArg Subtype.val (torusFamilyFiberHomeomorph_mk P y hcont (Γ t))
  · have hc : ContinuousMap.singularHomologyMap ℤ 1
        (h : C(_, {z : AddAction.orbitRel.Quotient Λ (Y × E) | torusFamilyProjection P z = y}))
        (ContinuousMap.singularHomologyMap ℤ 1 (h.symm : C(_, AddAction.orbitRel.Quotient L E))
          c) = c := by
      rw [← ContinuousMap.singularHomologyMap_comp, Homeomorph.toContinuousMap_comp_symm,
        ContinuousMap.singularHomologyMap_id]
    rw [← hc, ← ha]
    exact (ContinuousMap.singularHomologyMap_loopClass (.ofClass h) γ).symm

/-- **Naturality of the canonical marking under affine maps of fibres.** Let `φ` be a continuous
map from the fibre over `y` to the fibre over `y'` induced by an affine map of `E`, so that `φ`
sends `[y, v]` to `[y', A v + β]` for a continuous additive map `A : E →+ E` and a vector `β : E`.
Then `φ` acts on markings through `A`: the period at `y'` of the marking of `φ_* c` is the image
under `A` of the period at `y` of the marking of `c`. The translation part `β` does not
contribute. -/
theorem torusFamilyMarking_singularHomologyMap_of_affine {y y' : Y}
    (φ : letI := periodAddAction P
      C({z : AddAction.orbitRel.Quotient Λ (Y × E) | torusFamilyProjection P z = y},
        {z : AddAction.orbitRel.Quotient Λ (Y × E) | torusFamilyProjection P z = y'}))
    (A : E →+ E) (hA : Continuous A) (β : E)
    (hφ : letI := periodAddAction P
      ∀ (x : {z : AddAction.orbitRel.Quotient Λ (Y × E) | torusFamilyProjection P z = y}) (v : E),
        (x : AddAction.orbitRel.Quotient Λ (Y × E)) = Quotient.mk _ (y, v) →
        (φ x : AddAction.orbitRel.Quotient Λ (Y × E)) = Quotient.mk _ (y', A v + β))
    (c : letI := periodAddAction P
      ((singularChains ℤ).obj (TopCat.of
        {z : AddAction.orbitRel.Quotient Λ (Y × E) | torusFamilyProjection P z = y})).homology 1) :
    P y' (torusFamilyMarking P hcont hinj y' (ContinuousMap.singularHomologyMap ℤ 1 φ c)) =
      A (P y (torusFamilyMarking P hcont hinj y c)) := by
  obtain ⟨z, γ, Γ, hΓ, rfl⟩ := exists_loopClass_eq P hcont y c
  let Γ' : C(I, E) := ⟨fun t ↦ A (Γ t) + β, (hA.comp Γ.continuous).add continuous_const⟩
  rw [ContinuousMap.singularHomologyMap_loopClass,
    torusFamilyMarking_loopClass P hcont hinj y γ Γ hΓ,
    torusFamilyMarking_loopClass P hcont hinj y' _ Γ' fun t ↦ hφ _ _ (hΓ t)]
  simp only [Γ', ContinuousMap.coe_mk, map_sub]
  abel

variable {Γ : Type*} [Monoid Γ] [MulAction Γ Y] (R : Γ → Y → E →+ E)
  (ρ : Representation ℤ Γ Λ) (hP : ∀ (g : Γ) (y : Y) (l : Λ), P (g • y) (ρ g l) = R g y (P y l))
  (b : Γ → Y → letI := periodAddAction P; AddAction.orbitRel.Quotient Λ (Y × E))
  (hb : ∀ (g : Γ) (y : Y), torusFamilyProjection P (b g y) = g • y)

/-- **Equivariance of the canonical marking.** Let `g` act on the family of tori by the affine map
`[y, v] ↦ R g y v +ᵥ b g y` (`TauCeti.torusFamilyAffineMap`), with `R g y` continuous, and let
`φ` be its restriction to a continuous map from the fibre over `y` to the fibre over `y'` (so that
`y' = g • y`). Then `φ` acts on markings by `ρ g`: the marking of `φ_* c` at `y'` is `ρ g` applied
to the marking of `c` at `y`. -/
theorem torusFamilyMarking_singularHomologyMap_affineMap {g : Γ} {y y' : Y}
    (φ : letI := periodAddAction P
      C({z : AddAction.orbitRel.Quotient Λ (Y × E) | torusFamilyProjection P z = y},
        {z : AddAction.orbitRel.Quotient Λ (Y × E) | torusFamilyProjection P z = y'}))
    (hφ : letI := periodAddAction P
      ∀ x : {z : AddAction.orbitRel.Quotient Λ (Y × E) | torusFamilyProjection P z = y},
        (φ x : AddAction.orbitRel.Quotient Λ (Y × E)) = torusFamilyAffineMap R P ρ hP b hb g x)
    (hR : Continuous (R g y))
    (c : letI := periodAddAction P
      ((singularChains ℤ).obj (TopCat.of
        {z : AddAction.orbitRel.Quotient Λ (Y × E) | torusFamilyProjection P z = y})).homology 1) :
    torusFamilyMarking P hcont hinj y' (ContinuousMap.singularHomologyMap ℤ 1 φ c) =
      ρ g (torusFamilyMarking P hcont hinj y c) := by
  let _ := periodAddAction P
  -- The target fibre is the fibre over `g • y`, as `φ` sends `[y, 0]` there.
  have hy' : y' = g • y := by
    have : torusFamilyProjection P
        (φ ⟨Quotient.mk _ (y, 0), torusFamilyProjection_mk P (y, 0)⟩ : _) = y' := (φ _).2
    rwa [hφ, torusFamilyProjection_affineMap, torusFamilyProjection_mk, eq_comm] at this
  subst hy'
  obtain ⟨⟨y₁, β⟩, hβ⟩ := Quotient.exists_rep (b g y)
  obtain rfl : y₁ = g • y := by simpa [hb] using congrArg (torusFamilyProjection P) hβ
  refine hinj (g • y) ?_
  rw [torusFamilyMarking_singularHomologyMap_of_affine P hcont hinj φ (R g y) hR β
    (fun x v hx ↦ by rw [hφ, hx, torusFamilyAffineMap_mk_of_eq R P ρ hP b hb hβ.symm]), hP]

end Naturality

section Monodromy

variable {Y E : Type} [TopologicalSpace Y] [LocallyCompactSpace Y] [T2Space Y]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {Λ : Type*} [AddCommGroup Λ] [Module.Free ℤ Λ] [Module.Finite ℤ Λ]
  (P : Y → Λ →ₗ[ℤ] E) [∀ y, DiscreteTopology (LinearMap.range (P y))]
  [∀ y, IsZLattice ℝ (LinearMap.range (P y))]
  (hcont : ∀ l, Continuous fun y ↦ P y l) (hinj : ∀ y, Injective (P y))

/-- **Trivial monodromy of the canonical marking.** Let `γ₀` and `γ₁` be loops in the fibres over
`y₀` and `y₁`, and let `H : I × I → (Y × E)/Λ` be a free homotopy between them in the total
space: `H (·, 0) = γ₀`, `H (·, 1) = γ₁`, and each `H (·, s)` is a loop. Then `γ₀` and `γ₁` have
the same marking. The intermediate loops `H (·, s)` need not lie in single fibres; when they do,
this says that carrying a loop along a path in the base does not change its marking. -/
theorem torusFamilyMarking_loopClass_eq_of_homotopy {y₀ y₁ : Y}
    {z₀ : letI := periodAddAction P
      {z : AddAction.orbitRel.Quotient Λ (Y × E) | torusFamilyProjection P z = y₀}}
    {z₁ : letI := periodAddAction P
      {z : AddAction.orbitRel.Quotient Λ (Y × E) | torusFamilyProjection P z = y₁}}
    (γ₀ : Path z₀ z₀) (γ₁ : Path z₁ z₁)
    (H : letI := periodAddAction P; C(I × I, AddAction.orbitRel.Quotient Λ (Y × E)))
    (hH : ∀ s, H (0, s) = H (1, s)) (h₀ : ∀ t, (γ₀ t : _) = H (t, 0))
    (h₁ : ∀ t, (γ₁ t : _) = H (t, 1)) :
    torusFamilyMarking P hcont hinj y₀ (H₁AddEquivHomology _ (loopClass γ₀)) =
      torusFamilyMarking P hcont hinj y₁ (H₁AddEquivHomology _ (loopClass γ₁)) := by
  let _ := periodAddAction P
  have _ := continuousConstVAdd_periodAddAction P hcont
  have _ := properlyDiscontinuousVAdd_periodAddAction P hcont hinj
  have _ := isCancelVAdd_periodAddAction P hinj
  have cov : IsCoveringMap (Quotient.mk (AddAction.orbitRel Λ (Y × E))) :=
    isAddQuotientCoveringMap_quotientMk_of_properlyDiscontinuousVAdd.isCoveringMap
  -- Lift the path `s ↦ H (0, s)` of base points of the loops, then the whole family of loops.
  let c : C(I, AddAction.orbitRel.Quotient Λ (Y × E)) :=
    H.comp ((ContinuousMap.const I 0).prodMk (ContinuousMap.id I))
  obtain ⟨p₀, hp₀⟩ := Quotient.exists_rep (c 0)
  let c' := cov.liftPath c p₀ hp₀.symm
  have hc' : ∀ s, H (0, s) = Quotient.mk _ (c' s) := fun s ↦
    (congr_fun (cov.liftPath_lifts c p₀ hp₀.symm) s).symm
  let H' := cov.liftHomotopy H c' hc'
  have hH' : ∀ t s, Quotient.mk _ (H' (t, s)) = H (t, s) := fun t s ↦
    congr_fun (cov.liftHomotopy_lifts H c' hc') (t, s)
  -- The lifts of the loops `γ₀` and `γ₁` lie over `y₀` and `y₁`.
  have hy : ∀ {y : Y} {z} (γ : Path z z) (s : I),
      (∀ t, ((γ t : {z : AddAction.orbitRel.Quotient Λ (Y × E) | torusFamilyProjection P z = y}) :
        AddAction.orbitRel.Quotient Λ (Y × E)) = H (t, s)) → ∀ t, (H' (t, s)).1 = y := by
    intro y z γ s hγ t
    rw [← torusFamilyProjection_mk P, hH', ← hγ]
    exact (γ t).2
  let Γ : I → C(I, E) := fun s ↦
    ContinuousMap.snd.comp (H'.comp ((ContinuousMap.id I).prodMk (ContinuousMap.const I s)))
  have hΓ : ∀ {y : Y} {z} (γ : Path z z) (s : I),
      (∀ t, ((γ t : {z : AddAction.orbitRel.Quotient Λ (Y × E) | torusFamilyProjection P z = y}) :
        AddAction.orbitRel.Quotient Λ (Y × E)) = H (t, s)) →
      ∀ t, (γ t : AddAction.orbitRel.Quotient Λ (Y × E)) = Quotient.mk _ (y, Γ s t) := by
    intro y z γ s hγ t
    -- `Γ s t` is the second coordinate of `H' (t, s)`.
    rw [hγ, ← hH', ← hy γ s hγ t]
    rfl
  have hΓ₀ := torusFamilyMarking_loopClass P hcont hinj y₀ γ₀ (Γ 0) (hΓ γ₀ 0 h₀)
  have hΓ₁ := torusFamilyMarking_loopClass P hcont hinj y₁ γ₁ (Γ 1) (hΓ γ₁ 1 h₁)
  set l := torusFamilyMarking P hcont hinj y₀ (H₁AddEquivHomology _ (loopClass γ₀))
  -- By uniqueness of lifts of `s ↦ H (0, s) = H (1, s)`, translating the start points of the
  -- lifted loops by `l` gives their end points, since this holds at `s = 0`.
  have key : (fun s ↦ H' (1, s)) = fun s ↦ l +ᵥ H' (0, s) := by
    refine cov.eq_of_comp_eq (H'.continuous.comp (Continuous.prodMk_right 1))
      ((continuous_const_vadd l).comp (H'.continuous.comp (Continuous.prodMk_right 0)))
      (funext fun s ↦ ?_) 0 ?_
    · simp only [Function.comp_apply]
      rw [hH', Quotient.sound (AddAction.mem_orbit (H' (0, s)) l), hH', hH]
    · refine Prod.ext ?_ ?_ <;> simp only [periodAddAction_vadd, hy γ₀ 0 h₀ 1, hy γ₀ 0 h₀ 0, hΓ₀]
      exact (add_sub_cancel _ _).symm
  refine hinj y₁ ?_
  rw [hΓ₁]
  have h := congrArg Prod.snd (congr_fun key 1)
  simp only [periodAddAction_vadd, hy γ₁ 1 h₁ 0] at h
  exact eq_sub_of_add_eq' h.symm

variable {Γ : Type*} [Monoid Γ] [MulAction Γ Y] (R : Γ → Y → E →+ E)
  (ρ : Representation ℤ Γ Λ) (hP : ∀ (g : Γ) (y : Y) (l : Λ), P (g • y) (ρ g l) = R g y (P y l))
  (b : Γ → Y → letI := periodAddAction P; AddAction.orbitRel.Quotient Λ (Y × E))
  (hb : ∀ (g : Γ) (y : Y), torusFamilyProjection P (b g y) = g • y)

/-- **Monodromy of an affine action.** Let a loop `γ₀` in the fibre over `y₀` be carried by a free
homotopy `H` in the total space to a loop `γ₁` in the fibre over `y₁`, and identify the fibre over
`y₁` back with the fibre over `y₀` by the affine map of `g` (`TauCeti.torusFamilyAffineMap`), so
that `g • y₁ = y₀`, through its restriction `φ`. Then the transported loop `φ ∘ γ₁` is marked by
`ρ g` applied to the marking of `γ₀`.

For a group `Γ` and a loop over `y₀` carried by a free homotopy to a loop over `h • y₀`, the
inverse action `g = h⁻¹` identifies the end fibre with the starting one, so the transport on the
marking is `ρ h⁻¹`; equivalently, a loop carried by a free homotopy to a loop over `g⁻¹ • y₀` and
then moved by the action of `g` has monodromy `ρ g`. -/
theorem torusFamilyMarking_singularHomologyMap_loopClass_of_homotopy {g : Γ} {y₀ y₁ : Y}
    {z₀ : letI := periodAddAction P
      {z : AddAction.orbitRel.Quotient Λ (Y × E) | torusFamilyProjection P z = y₀}}
    {z₁ : letI := periodAddAction P
      {z : AddAction.orbitRel.Quotient Λ (Y × E) | torusFamilyProjection P z = y₁}}
    (γ₀ : Path z₀ z₀) (γ₁ : Path z₁ z₁)
    (H : letI := periodAddAction P; C(I × I, AddAction.orbitRel.Quotient Λ (Y × E)))
    (hH : ∀ s, H (0, s) = H (1, s)) (h₀ : ∀ t, (γ₀ t : _) = H (t, 0))
    (h₁ : ∀ t, (γ₁ t : _) = H (t, 1))
    (φ : letI := periodAddAction P
      C({z : AddAction.orbitRel.Quotient Λ (Y × E) | torusFamilyProjection P z = y₁},
        {z : AddAction.orbitRel.Quotient Λ (Y × E) | torusFamilyProjection P z = y₀}))
    (hφ : letI := periodAddAction P
      ∀ x : {z : AddAction.orbitRel.Quotient Λ (Y × E) | torusFamilyProjection P z = y₁},
        (φ x : AddAction.orbitRel.Quotient Λ (Y × E)) = torusFamilyAffineMap R P ρ hP b hb g x)
    (hR : Continuous (R g y₁)) :
    torusFamilyMarking P hcont hinj y₀
        (ContinuousMap.singularHomologyMap ℤ 1 φ (H₁AddEquivHomology _ (loopClass γ₁))) =
      ρ g (torusFamilyMarking P hcont hinj y₀ (H₁AddEquivHomology _ (loopClass γ₀))) := by
  rw [torusFamilyMarking_singularHomologyMap_affineMap P hcont hinj R ρ hP b hb φ hφ hR,
    torusFamilyMarking_loopClass_eq_of_homotopy P hcont hinj γ₀ γ₁ H hH h₀ h₁]

end Monodromy

end TauCeti
