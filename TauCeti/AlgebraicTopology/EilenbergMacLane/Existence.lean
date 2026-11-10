/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cellular.CellAttachment
public import TauCeti.AlgebraicTopology.EilenbergMacLane.Degree
public import TauCeti.AlgebraicTopology.Homotopy.CellAttachment
public import TauCeti.AlgebraicTopology.Homotopy.Hurewicz.Absolute
public import TauCeti.AlgebraicTopology.Homotopy.Hurewicz.DiskBoundary
public import TauCeti.AlgebraicTopology.Homotopy.KillHomotopyGroups
import TauCeti.AlgebraicTopology.Singular.Contractible

/-!
# Eilenberg--Mac Lane spaces `K(A, n)` from a presentation

For every abelian group `A` and every `n ≥ 2` there is a Hausdorff Eilenberg--Mac Lane space of type
`K(A, n)` (`TauCeti.exists_isEilenbergMacLaneSpace`). It is built from a presentation of `A` by
cells, following Hatcher:

1. Attach one `n`-cell to a point for each element of `A`, along the constant map. The result `W`
   is a wedge of `n`-spheres. It is `(n - 1)`-connected, so by the Hurewicz theorem
   `πₙ(W) ≅ Hₙ(W; ℤ)`, and `Hₙ(W; ℤ)` is free on the cells
   (`TauCeti.nonempty_singularHomology_cellAttachment_iso_sigma`). Sending the cell of `a` to `a`
   gives a surjection `ψ : Hₙ(W; ℤ) → A`.
2. Attach an `(n + 1)`-cell along every map `g : Sⁿ → W` whose class `g_*[Sⁿ]` lies in the kernel of
   `ψ`. The result `Y` is still `(n - 1)`-connected. By
   `TauCeti.ker_singularHomologyMap_cellAttachmentIncl`, the kernel of `Hₙ(W) → Hₙ(Y)` is spanned by
   the classes of the attaching spheres. Every class of `Hₙ(W)` is a Hurewicz class, hence up to
   sign the class of the attaching sphere of a generalized loop
   (`GenLoop.exists_singularHomologyMap_diskBoundaryMap_eq_units_smul_hurewicz`), so this kernel is
   exactly the kernel of `ψ`. Hence `πₙ(Y) ≅ Hₙ(Y; ℤ) ≅ Hₙ(W; ℤ) ⧸ ker ψ ≅ A`.
3. Kill the homotopy groups of `Y` above dimension `n` by attaching cells of dimension at least
   `n + 2` (`TauCeti.isEilenbergMacLaneSpace_killHomotopyGroups`).

The construction uses the Hurewicz theorem with integer coefficients, which is stated for spaces in
the lowest universe, so `A` is a type in `Type`.

## Main results

* `TauCeti.exists_isEilenbergMacLaneSpace`: every abelian group `A` has a Hausdorff `K(A, n)` for
  every `n ≥ 2`.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 2.2, Example 2.40 (Moore spaces from a presentation), and Section 4.2, Theorem 4.32
  (the Hurewicz theorem) and the construction of Eilenberg--Mac Lane spaces preceding
  Proposition 4.30.
-/

public section

noncomputable section

open CategoryTheory Limits AlgebraicTopology
open scoped Topology

namespace TauCeti

namespace EilenbergMacLane

variable (A : Type) (n : ℕ)

/-- The constant attaching maps of the cells of the wedge of spheres. -/
private abbrev wedgeAttach : A → (TopCat.diskBoundary.{0} (n + 2) ⟶ TopCat.of PUnit.{1}) :=
  fun _ ↦ TopCat.ofHom (ContinuousMap.const _ PUnit.unit)

/-- The wedge of `(n + 2)`-spheres indexed by the elements of `A`: one `(n + 2)`-cell attached to
a point for each element, along the constant map. -/
private abbrev wedge : TopCat.{0} := cellAttachment (wedgeAttach A n)

/-- The base point of the wedge. -/
private abbrev wedgeBase : wedge A n := cellAttachmentIncl (wedgeAttach A n) PUnit.unit

/-- The wedge of `(n + 2)`-spheres is `(n + 1)`-connected. -/
private lemma subsingleton_homotopyGroup_wedge (k : ℕ) (hk : k < n + 2) :
    Subsingleton (π_ k (wedge A n) (wedgeBase A n)) :=
  (surjective_homotopyGroupMap_cellAttachmentIncl (N := Fin k) (wedgeAttach A n)
    (by simpa using Nat.le_of_lt_succ hk) PUnit.unit).subsingleton

/-- Integral singular homology in degree `k`, as a functor. -/
private abbrev H (k : ℕ) : TopCat.{0} ⥤ ModuleCat.{0} ℤ :=
  (singularHomologyFunctor (ModuleCat.{0} ℤ) k).obj (ModuleCat.of ℤ ℤ)

/-- The generator `[Sⁿ⁺²]` of the integral homology of the sphere `TopCat.diskBoundary (n + 3)`. -/
private abbrev sphereClass : (H (n + 2)).obj (TopCat.diskBoundary.{0} (n + 3)) :=
  (reducedSingularHomologyι (ModuleCat.of ℤ ℤ) (n + 2)).app (TopCat.diskBoundary.{0} (n + 3))
    ((reducedSingularHomologyTopCatSphereIso (ModuleCat.of ℤ ℤ) (n + 2)).inv 1)

variable [AddCommGroup A]

/-- A surjection `Hₙ₊₂(W; ℤ) → A` from the homology of the wedge, sending the cell of `a` to `a`
for some identification of `Hₙ₊₂(W; ℤ)` with the free abelian group on the cells. -/
private lemma exists_surjective_wedge :
    ∃ ψ : (H (n + 2)).obj (wedge A n) →ₗ[ℤ] A, Function.Surjective ψ := by
  obtain ⟨e⟩ := nonempty_singularHomology_cellAttachment_iso_sigma (wedgeAttach A n) ℤ
    (isZero_singularHomologyFunctor_of_contractibleSpace (ModuleCat.of ℤ ℤ) (TopCat.of PUnit.{1})
      (by omega))
    (isZero_singularHomologyFunctor_of_contractibleSpace (ModuleCat.of ℤ ℤ) (TopCat.of PUnit.{1})
      (by omega))
  let d : (∐ fun _ : A ↦ ModuleCat.of ℤ ℤ) ⟶ ModuleCat.of ℤ A :=
    Sigma.desc fun a ↦ ModuleCat.ofHom (LinearMap.toSpanSingleton ℤ A a)
  refine ⟨(e.hom ≫ d).hom, fun a ↦ ⟨e.inv (Sigma.ι (fun _ : A ↦ ModuleCat.of ℤ ℤ) a 1), ?_⟩⟩
  rw [ModuleCat.comp_apply, Iso.inv_hom_id_apply]
  exact (ConcreteCategory.congr_hom
    (Sigma.ι_comp_desc (fun a ↦ ModuleCat.ofHom (LinearMap.toSpanSingleton ℤ A a)) a) 1).trans
      (one_smul ℤ a)

/-- The maps `Sⁿ⁺² → W` into the wedge whose class lies in the kernel of `ψ`. -/
private abbrev Relation (ψ : (H (n + 2)).obj (wedge A n) →ₗ[ℤ] A) : Type :=
  {g : TopCat.diskBoundary.{0} (n + 3) ⟶ wedge A n // ψ ((H (n + 2)).map g (sphereClass n)) = 0}

/-- The relations, as attaching maps. -/
private abbrev relationAttach (ψ : (H (n + 2)).obj (wedge A n) →ₗ[ℤ] A) (r : Relation A n ψ) :
    TopCat.diskBoundary.{0} (n + 3) ⟶ wedge A n :=
  r.1

/-- The wedge with an `(n + 3)`-cell attached along every map in the kernel of `ψ`. -/
private abbrev presentation (ψ : (H (n + 2)).obj (wedge A n) →ₗ[ℤ] A) : TopCat.{0} :=
  cellAttachment (relationAttach A n ψ)

/-- The base point of the presentation complex. -/
private abbrev presentationBase (ψ : (H (n + 2)).obj (wedge A n) →ₗ[ℤ] A) : presentation A n ψ :=
  cellAttachmentIncl (relationAttach A n ψ) (wedgeBase A n)

/-- The presentation complex is `(n + 1)`-connected. -/
private lemma subsingleton_homotopyGroup_presentation
    (ψ : (H (n + 2)).obj (wedge A n) →ₗ[ℤ] A) (k : ℕ) (hk : k < n + 2) :
    Subsingleton (π_ k (presentation A n ψ) (presentationBase A n ψ)) :=
  have := subsingleton_homotopyGroup_wedge A n k hk
  (bijective_homotopyGroupMap_cellAttachmentIncl (N := Fin k) (relationAttach A n ψ)
    (by simpa using hk) (wedgeBase A n)).2.subsingleton

/-- Attaching the relation cells kills exactly the kernel of `ψ` in `Hₙ₊₂`. -/
private lemma ker_presentation (ψ : (H (n + 2)).obj (wedge A n) →ₗ[ℤ] A) :
    LinearMap.ker ((H (n + 2)).map (cellAttachmentIncl (relationAttach A n ψ))).hom =
      LinearMap.ker ψ := by
  rw [ker_singularHomologyMap_cellAttachmentIncl]
  refine le_antisymm (Submodule.span_le.2 ?_) fun h hh ↦ ?_
  · rintro _ ⟨r, rfl⟩
    exact r.2
  -- Every class of `Hₙ₊₂(W)` is the Hurewicz class of a generalized loop, so up to sign the class
  -- of its attaching sphere, which lies in the kernel of `ψ` with the class.
  obtain ⟨ε, hε⟩ :=
    GenLoop.exists_singularHomologyMap_diskBoundaryMap_eq_units_smul_hurewicz (n + 1)
  obtain ⟨a, rfl⟩ :=
    (HomotopyGroup.hurewiczAddEquiv (subsingleton_homotopyGroup_wedge A n)).surjective h
  induction a using Additive.rec with | ofMul a => ?_
  induction a using Quotient.inductionOn with | h p => ?_
  have hp : (H (n + 2)).map (GenLoop.diskBoundaryMap p) (sphereClass n) =
      (ε : ℤ) • HomotopyGroup.hurewiczAddEquiv (subsingleton_homotopyGroup_wedge A n)
        (Additive.ofMul ⟦p⟧) := by
    rw [HomotopyGroup.hurewiczAddEquiv_apply, HomotopyGroup.hurewiczHom_apply]
    -- `Additive.ofMul ⟦p⟧` is presented through `Quotient` rather than `HomotopyGroup`, so the
    -- generated motive of `rw` is ill-typed and `erw` is needed.
    erw [toMul_ofMul, HomotopyGroup.hurewicz_mk]
    exact hε (wedge A n) _ p
  have hr : ψ ((H (n + 2)).map (GenLoop.diskBoundaryMap p) (sphereClass n)) = 0 := by
    rw [hp, map_zsmul, LinearMap.mem_ker.1 hh, smul_zero]
  have hmem := (Submodule.span ℤ (Set.range fun r : Relation A n ψ ↦
    (H (n + 2)).map (relationAttach A n ψ r) (sphereClass n))).toAddSubgroup.zsmul_mem
    (Submodule.subset_span ⟨⟨GenLoop.diskBoundaryMap p, hr⟩, rfl⟩) ((ε⁻¹ : ℤˣ) : ℤ)
  dsimp only [relationAttach] at hmem
  rw [hp] at hmem
  simpa only [smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul,
    Submodule.mem_toAddSubgroup] using hmem

/-- **The presentation complex has `πₙ₊₂ ≅ A`.** -/
private lemma nonempty_homotopyGroup_presentation_mulEquiv
    (ψ : (H (n + 2)).obj (wedge A n) →ₗ[ℤ] A)
    (hψ : Function.Surjective ψ) :
    Nonempty (π_ (n + 2) (presentation A n ψ) (presentationBase A n ψ) ≃* Multiplicative A) := by
  let f := (H (n + 2)).map (cellAttachmentIncl (relationAttach A n ψ))
  -- `Hₙ₊₂(Y) ≅ Hₙ₊₂(W) ⧸ ker f = Hₙ₊₂(W) ⧸ ker ψ ≅ A`.
  let e : (H (n + 2)).obj (presentation A n ψ) ≃ₗ[ℤ] A :=
    (f.hom.quotKerEquivOfSurjective
      (surjective_singularHomologyMap_cellAttachmentIncl (relationAttach A n ψ) ℤ)).symm.trans
      ((Submodule.quotEquivOfEq _ _ (ker_presentation A n ψ)).trans
        (ψ.quotKerEquivOfSurjective hψ))
  exact ⟨AddEquiv.toMultiplicative
    ((HomotopyGroup.hurewiczAddEquiv (subsingleton_homotopyGroup_presentation A n ψ)).trans
      e.toAddEquiv)⟩

end EilenbergMacLane

open EilenbergMacLane in
/-- **Every abelian group has a `K(A, n)` for `n ≥ 2`.** For an abelian group `A` and `n ≥ 2`, there
is a Hausdorff based space whose homotopy groups vanish outside dimension `n` and whose `n`-th
homotopy group is isomorphic to `A`. It is obtained from a presentation of `A` by cells: a wedge of
`n`-spheres, `(n + 1)`-cells killing the relations, and cells of dimension at least `n + 2`
killing the higher homotopy groups. -/
theorem exists_isEilenbergMacLaneSpace (A : Type) [AddCommGroup A] (n : ℕ) :
    ∃ (X : Type) (_ : TopologicalSpace X) (x : X), T2Space X ∧
      IsEilenbergMacLaneSpace (Multiplicative A) (n + 2) X x := by
  obtain ⟨ψ, hψ⟩ := exists_surjective_wedge A n
  have : PathConnectedSpace (presentation A n ψ) :=
    (pathConnectedSpace_iff_subsingleton_homotopyGroup_zero (presentationBase A n ψ)).2
      (subsingleton_homotopyGroup_presentation A n ψ 0 (by omega))
  obtain ⟨e⟩ := nonempty_homotopyGroup_presentation_mulEquiv A n ψ hψ
  exact ⟨_, inferInstance, _, inferInstance,
    (isEilenbergMacLaneSpace_killHomotopyGroups (n + 2) (presentation A n ψ)
      (presentationBase A n ψ) fun k _ hk ↦
        subsingleton_homotopyGroup_presentation A n ψ k hk).of_mulEquiv e⟩

end TauCeti
