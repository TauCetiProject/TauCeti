/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Basic
public import TauCeti.RingTheory.RootsOfUnity.Basic
public import TauCeti.RingTheory.RootsOfUnity.TateModule

/-!
# The profinite limit of the groups of roots of unity

For nonzero natural numbers prime to `p`, ordered by divisibility, the maps `μ_m(R) → μ_n(R)`
send `ζ` to `ζ ^ (m / n)`. Over a domain these are finite groups. Mathlib's functor
`forget₂ FiniteGrp ProfiniteGrp` gives each level the discrete topology independently
of any topology on `R` or its units.

The resulting diagram in `ProfiniteGrp` has the existing Tate module
`TauCeti.PrimeToPTateModule p R` as its limit. The limit cone and its universal property
identify the concrete group of compatible families with the categorical inverse limit.
For `p = 1` this is the full roots-of-unity tower acting on ramified Laurent extensions
by Kummer theory.
-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace TauCeti.PrimeToPTateModule

/-- Nonzero orders prime to `p`, ordered by divisibility. -/
@[ext]
structure Index (p : ℕ) where
  /-- The nonzero order, coprime to `p`, of a finite level. -/
  order : {m : ℕ // m ≠ 0 ∧ m.Coprime p}

namespace Index

variable {p : ℕ}

instance : PartialOrder (Index p) where
  le n m := (n.order : ℕ) ∣ m.order
  le_refl n := dvd_refl _
  le_trans _ _ _ := dvd_trans
  le_antisymm _ _ hnm hmn := Index.ext (Subtype.ext (Nat.dvd_antisymm hnm hmn))

/-- Comparison of level indices is divisibility of their orders. -/
@[simp]
theorem le_iff_dvd {n m : Index p} : n ≤ m ↔ (n.order : ℕ) ∣ m.order := Iff.rfl

instance (n : Index p) : NeZero (n.order : ℕ) := ⟨n.order.2.1⟩

end Index

variable (p : ℕ) (R : Type*) [CommRing R] [IsDomain R]

/-- The inverse system of finite groups of roots of unity of order prime to `p`. -/
-- Expose the object assignment: morphism types depend on the actual finite-level carriers.
@[expose]
def finiteRootsOfUnityDiagram : (Index p)ᵒᵖ ⥤ FiniteGrp where
  obj n := FiniteGrp.of (rootsOfUnity n.unop.order R)
  map f := FiniteGrp.ofHom (rootsOfUnityPowOfDvd f.unop.le)
  map_id n := by
    rw [rootsOfUnityPowOfDvd_refl]
    -- FiniteGrp.ofHom wraps MonoidHom.id as the categorical identity by definition.
    rfl
  map_comp {n m l} f g := by
    rw [← rootsOfUnityPowOfDvd_comp g.unop.le f.unop.le]
    -- FiniteGrp.ofHom preserves composition by definition of the GrpCat hom wrapper.
    rfl

/-- The inverse system of finite discrete root groups, with orders prime to `p`. -/
-- Expose the finite-level carriers supplied by Mathlib's discrete-topology functor.
@[expose]
def rootsOfUnityDiagram : (Index p)ᵒᵖ ⥤ ProfiniteGrp :=
  finiteRootsOfUnityDiagram p R ⋙ forget₂ FiniteGrp ProfiniteGrp

/-- The object at `n` is the discrete group of `n`-th roots of unity. -/
@[simp]
theorem rootsOfUnityDiagram_obj (n : (Index p)ᵒᵖ) :
    (rootsOfUnityDiagram p R).obj n =
      ProfiniteGrp.ofFiniteGrp (FiniteGrp.of (rootsOfUnity n.unop.order R)) := (rfl)

/-- Each diagram level has the bottom topology supplied by `ProfiniteGrp.ofFiniteGrp`. -/
instance (n : (Index p)ᵒᵖ) : DiscreteTopology ((rootsOfUnityDiagram p R).obj n) :=
  ⟨rfl⟩

/-- The arrows of the diagram are the power transitions. -/
@[simp]
theorem rootsOfUnityDiagram_map_hom {n m : (Index p)ᵒᵖ} (f : n ⟶ m) :
    MonoidHom.ofClass ((rootsOfUnityDiagram p R).map f).hom =
      rootsOfUnityPowOfDvd (M := R) f.unop.le := (rfl)

/-- On underlying units the diagram maps are the usual power maps. -/
@[simp]
theorem rootsOfUnityDiagram_map_apply {n m : (Index p)ᵒᵖ} (f : n ⟶ m)
    (ζ : (rootsOfUnityDiagram p R).obj n) :
    (((rootsOfUnityDiagram p R).map f).hom ζ : rootsOfUnity m.unop.order R).val =
      (ζ : rootsOfUnity n.unop.order R).val ^ ((n.unop.order : ℕ) / m.unop.order) :=
  coe_rootsOfUnityPowOfDvd_apply f.unop.le ζ

/-- The compatible projections from the Tate module form a cone in profinite groups. -/
-- Expose the vertex so its projections have the existing Tate module as their source.
@[expose]
def rootsOfUnityCone : Cone (rootsOfUnityDiagram p R) where
  pt := ProfiniteGrp.of (PrimeToPTateModule p R)
  π :=
    { app := fun n ↦ by
        exact ConcreteCategory.ofHom
          ({ toMonoidHom := proj n.unop.order
             continuous_toFun := IsLocallyConstant.continuous
               (Y := (rootsOfUnityDiagram p R).obj n) (isLocallyConstant_proj n.unop.order) } :
            PrimeToPTateModule p R →ₜ* (rootsOfUnityDiagram p R).obj n)
      naturality := fun {n m} f ↦ by
        apply ProfiniteGrp.hom_ext
        apply ContinuousMonoidHom.ext
        intro ζ
        apply Subtype.ext
        simp only [Functor.const_obj_map, ProfiniteGrp.comp_apply,
          ConcreteCategory.hom_ofHom, rootsOfUnityDiagram_map_apply]
        exact (proj_pow_div ζ f.unop.le).symm }

/-- The cone has the existing Tate module as its vertex. -/
@[simp]
theorem rootsOfUnityCone_pt :
    (rootsOfUnityCone p R).pt = ProfiniteGrp.of (PrimeToPTateModule p R) := (rfl)

/-- The cone maps are the Tate-module projections to the discrete levels. -/
@[simp]
theorem rootsOfUnityCone_π_app_hom (n : (Index p)ᵒᵖ) :
    MonoidHom.ofClass ((rootsOfUnityCone p R).π.app n).hom =
      proj (E := R) n.unop.order := (rfl)

/-- Applying a cone leg evaluates the corresponding Tate-module component. -/
@[simp]
theorem rootsOfUnityCone_π_app_apply (n : (Index p)ᵒᵖ) (x : (rootsOfUnityCone p R).pt) :
    (ProfiniteGrp.Hom.hom (M := (rootsOfUnityCone p R).pt)
      ((rootsOfUnityCone p R).π.app n)) x = proj n.unop.order x := (rfl)

private def coneLiftHom (s : Cone (rootsOfUnityDiagram p R)) :
    s.pt →* PrimeToPTateModule p R :=
  lift (fun m ↦ (s.π.app (Opposite.op ⟨m⟩)).hom.toMonoidHom)
    (fun m n x h ↦ by
      have hw := congrArg (fun f ↦ f.hom x)
        (s.w (homOfLE (x := (⟨n⟩ : Index p)) (y := ⟨m⟩) h).op)
      have hv := congrArg (fun ζ : rootsOfUnity n R ↦ ζ.val) hw
      simp only [ProfiniteGrp.comp_apply, rootsOfUnityDiagram_map_apply] at hv
      exact hv)

private theorem proj_coneLiftHom (s : Cone (rootsOfUnityDiagram p R))
    (m : {m : ℕ // m ≠ 0 ∧ m.Coprime p}) (x : s.pt) :
    proj m (coneLiftHom p R s x) = (s.π.app (Opposite.op ⟨m⟩)).hom x :=
  proj_lift _ _ m x

private def coneLift (s : Cone (rootsOfUnityDiagram p R)) :
    s.pt ⟶ (rootsOfUnityCone p R).pt :=
  ConcreteCategory.ofHom
    ({ coneLiftHom p R s with
      continuous_toFun := continuous_iff.mpr fun m ↦ by
        have hc := (IsLocallyConstant.iff_continuous _).mpr
          (s.π.app (Opposite.op ⟨m⟩)).hom.continuous
        -- Specify the predicate being transported across the projection equality.
        exact (congrArg IsLocallyConstant
          (funext (proj_coneLiftHom p R s m))).mpr hc } : s.pt →ₜ* PrimeToPTateModule p R)

private theorem coneLift_apply (s : Cone (rootsOfUnityDiagram p R)) (x : s.pt) :
    (coneLift p R s).hom x = coneLiftHom p R s x := rfl

/-- The prime-to-`p` Tate module is the inverse limit of the finite discrete groups of roots
of unity of order prime to `p` in `ProfiniteGrp`: every compatible family of continuous
homomorphisms factors uniquely through its projections. -/
def rootsOfUnityConeIsLimit : IsLimit (rootsOfUnityCone p R) where
  lift s := coneLift p R s
  fac s n := by
    apply ProfiniteGrp.hom_ext
    apply ContinuousMonoidHom.ext
    intro x
    rw [ProfiniteGrp.comp_apply, rootsOfUnityCone_π_app_apply, coneLift_apply]
    exact proj_coneLiftHom p R s n.unop.order x
  uniq s f hf := by
    have hF : f.hom.toMonoidHom = coneLiftHom p R s := by
      apply lift_unique
      intro m
      apply MonoidHom.ext
      intro x
      have h := congrArg (fun g ↦ (ProfiniteGrp.Hom.hom g) x) (hf (Opposite.op ⟨m⟩))
      rw [ProfiniteGrp.comp_apply, rootsOfUnityCone_π_app_apply] at h
      exact h
    apply ProfiniteGrp.hom_ext
    apply ContinuousMonoidHom.ext
    intro x
    exact (DFunLike.congr_fun hF x).trans (coneLift_apply p R s x).symm

end TauCeti.PrimeToPTateModule
