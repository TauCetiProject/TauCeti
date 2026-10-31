/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Contractible
public import Mathlib.Topology.Homotopy.Lifting
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

Singular chains with integer coefficients are defined on spaces in the lowest universe, so `Y`
and `E` are types in `Type`.

## Main declarations

* `TauCeti.torusFamilyMarking`: the marking `H₁(T_y; ℤ) ≃ₗ[ℤ] Λ` of the fibre over `y`.
* `TauCeti.torusFamilyMarking_loopClass`: the marking of a loop is its period displacement.
* `TauCeti.torusFamilyMarking_singularHomologyMap`: compatibility with the identification of the
  fibre with `E / LinearMap.range (P y)`.
* `TauCeti.torusFamilyMarking_loopClass_eq_of_homotopy`: freely homotopic loops in two fibres
  have the same marking.

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
  rw [period_torusFamilyMarking, ContinuousMap.singularHomologyMap,
    homologyMap_H₁AddEquivHomology_loopClass]
  refine AddSubgroup.orbitRelQuotientFirstHomologyEquiv_loopClass _ _ Γ (funext fun t ↦ ?_)
  simp only [Function.comp_apply, Path.map_coe, TopCat.hom_ofHom, ContinuousMap.coe_ofClass]
  rw [eq_comm, Homeomorph.symm_apply_eq]
  ext
  rw [hΓ]
  -- The orbit space of `(LinearMap.range (P y)).toAddSubgroup` used by the homology equivalence
  -- is definitionally that of the submodule `LinearMap.range (P y)` used by the fibre map.
  exact (congrArg Subtype.val (torusFamilyFiberHomeomorph_mk P y hcont (Γ t))).symm

end Marking

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

end Monodromy

end TauCeti
