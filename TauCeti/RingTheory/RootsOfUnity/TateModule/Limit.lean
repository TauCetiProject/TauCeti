/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Basic
public import TauCeti.RingTheory.LaurentSeries.RamificationIndex
import TauCeti.RingTheory.RootsOfUnity.Basic
public import TauCeti.RingTheory.RootsOfUnity.TateModule

/-!
# The profinite limit of the groups of roots of unity

For positive integers ordered by divisibility, the maps `μ_m(R) → μ_n(R)` send `ζ` to
`ζ ^ (m / n)`. Over a domain these are finite groups. We give each level a fresh carrier
`DiscreteRootsOfUnity n R`, so its discrete topology is independent of any topology on `R`
or its units.

The resulting diagram in `ProfiniteGrp` has the existing Tate module
`TauCeti.PrimeToPTateModule 1 R` as its limit. The limit cone and its universal property
identify the concrete group of compatible families with the categorical inverse limit.
This is the roots-of-unity tower acting on ramified Laurent extensions by Kummer theory.
-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace TauCeti

/-- The `n`-th roots of unity on a fresh carrier with the discrete topology. -/
def DiscreteRootsOfUnity (n : ℕ+) (R : Type*) [CommMonoid R] : Type _ := rootsOfUnity n R

namespace DiscreteRootsOfUnity

variable {R : Type*} [CommMonoid R] {n m l : ℕ+}

instance : CommGroup (DiscreteRootsOfUnity n R) :=
  inferInstanceAs (CommGroup (rootsOfUnity n R))

/-- Forgetting the discrete carrier is a group equivalence. -/
def equivRootsOfUnity : DiscreteRootsOfUnity n R ≃* rootsOfUnity n R := .refl _

/-- Discrete roots of unity are determined by their underlying units. -/
@[ext]
theorem ext {ζ ξ : DiscreteRootsOfUnity n R}
    (h : (equivRootsOfUnity ζ : Rˣ) = equivRootsOfUnity ξ) : ζ = ξ :=
  equivRootsOfUnity.injective (Subtype.ext h)

instance : TopologicalSpace (DiscreteRootsOfUnity n R) := ⊥

instance : DiscreteTopology (DiscreteRootsOfUnity n R) := ⟨rfl⟩

instance [Finite (rootsOfUnity n R)] : Finite (DiscreteRootsOfUnity n R) :=
  Finite.of_equiv _ equivRootsOfUnity.symm.toEquiv

/-- The transition from level `m` to level `n`, for `n ∣ m`, raises to `m / n`. -/
def transition (h : n ∣ m) : DiscreteRootsOfUnity m R →ₜ* DiscreteRootsOfUnity n R where
  toMonoidHom := equivRootsOfUnity.symm.toMonoidHom.comp
    ((rootsOfUnityPowOfDvd (PNat.dvd_iff.mp h)).comp equivRootsOfUnity.toMonoidHom)
  continuous_toFun := continuous_of_discreteTopology

/-- On units the transition is the usual power map. -/
@[simp]
theorem coe_transition (h : n ∣ m) (ζ : DiscreteRootsOfUnity m R) :
    (equivRootsOfUnity (transition h ζ) : Rˣ) =
      (equivRootsOfUnity ζ : Rˣ) ^ ((m : ℕ) / n) :=
  coe_rootsOfUnityPowOfDvd_apply (PNat.dvd_iff.mp h) (equivRootsOfUnity ζ)

@[simp]
theorem transition_refl (ζ : DiscreteRootsOfUnity n R) : transition (dvd_refl n) ζ = ζ := by
  apply DiscreteRootsOfUnity.ext
  simp

/-- The power transitions compose along divisibility. -/
@[simp]
theorem transition_transition (hnm : n ∣ m) (hml : m ∣ l) (ζ : DiscreteRootsOfUnity l R) :
    transition hnm (transition hml ζ) = transition (hnm.trans hml) ζ := by
  apply DiscreteRootsOfUnity.ext
  simp only [coe_transition, ← pow_mul, Nat.div_mul_div (PNat.dvd_iff.mp hml)
    (PNat.dvd_iff.mp hnm)]

end DiscreteRootsOfUnity

namespace PrimeToPTateModule

section Projections

variable {R : Type*} [CommMonoid R]

/-- The projection of the Tate module to a discrete root group. -/
def discreteProj (n : ℕ+) : PrimeToPTateModule 1 R →ₜ* DiscreteRootsOfUnity n R where
  toMonoidHom := DiscreteRootsOfUnity.equivRootsOfUnity.symm.toMonoidHom.comp
    (proj ⟨n, n.ne_zero, Nat.coprime_one_right _⟩)
  continuous_toFun :=
    ((isLocallyConstant_proj ⟨n, n.ne_zero, Nat.coprime_one_right _⟩).comp
      DiscreteRootsOfUnity.equivRootsOfUnity.symm).continuous

/-- Forgetting the discrete carrier recovers the original Tate-module projection. -/
@[simp]
theorem equivRootsOfUnity_discreteProj (n : ℕ+) (ζ : PrimeToPTateModule 1 R) :
    DiscreteRootsOfUnity.equivRootsOfUnity (discreteProj n ζ) =
      proj ⟨n, n.ne_zero, Nat.coprime_one_right _⟩ ζ := (rfl)

/-- Tate-module projections are compatible with the discrete power transitions. -/
@[simp]
theorem transition_discreteProj {n m : ℕ+} (h : n ∣ m) (ζ : PrimeToPTateModule 1 R) :
    DiscreteRootsOfUnity.transition h (discreteProj m ζ) = discreteProj n ζ := by
  apply DiscreteRootsOfUnity.ext
  simp only [DiscreteRootsOfUnity.coe_transition, equivRootsOfUnity_discreteProj]
  exact proj_pow_div ζ
    (m := ⟨m, m.ne_zero, Nat.coprime_one_right _⟩)
    (n := ⟨n, n.ne_zero, Nat.coprime_one_right _⟩) (PNat.dvd_iff.mp h)

end Projections

variable (R : Type*) [CommRing R] [IsDomain R]

/-- The inverse system of finite discrete groups of roots of unity, indexed by positive
integers under divisibility. -/
-- Expose the object assignment: morphism types depend on the actual finite-level carriers.
@[expose]
def rootsOfUnityDiagram : RamificationIndexᵒᵖ ⥤ ProfiniteGrp where
  obj n := ProfiniteGrp.of (DiscreteRootsOfUnity n.unop.toPNat R)
  map f := ProfiniteGrp.ofHom (DiscreteRootsOfUnity.transition f.unop.le)
  map_id n := by
    apply ConcreteCategory.hom_ext
    intro ζ
    exact DiscreteRootsOfUnity.transition_refl ζ
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    intro ζ
    exact (DiscreteRootsOfUnity.transition_transition g.unop.le f.unop.le ζ).symm

/-- The object at `n` is the discrete group of `n`-th roots of unity. -/
@[simp]
theorem rootsOfUnityDiagram_obj (n : RamificationIndexᵒᵖ) :
    (rootsOfUnityDiagram R).obj n = ProfiniteGrp.of (DiscreteRootsOfUnity n.unop.toPNat R) :=
  (rfl)

/-- The arrows of the diagram are the power transitions. -/
@[simp]
theorem rootsOfUnityDiagram_map_hom {n m : RamificationIndexᵒᵖ} (f : n ⟶ m) :
    ((rootsOfUnityDiagram R).map f).hom = DiscreteRootsOfUnity.transition f.unop.le := (rfl)

/-- The compatible projections from the Tate module form a cone in profinite groups. -/
-- Expose the vertex so its projections have the existing Tate module as their source.
@[expose]
def rootsOfUnityCone : Cone (rootsOfUnityDiagram R) where
  pt := ProfiniteGrp.of (PrimeToPTateModule 1 R)
  π :=
    { app := fun n ↦ ProfiniteGrp.ofHom (discreteProj n.unop.toPNat)
      naturality := fun {n m} f ↦ by
        apply ConcreteCategory.hom_ext
        intro ζ
        exact (transition_discreteProj f.unop.le ζ).symm }

/-- The cone has the existing Tate module as its vertex. -/
@[simp]
theorem rootsOfUnityCone_pt :
    (rootsOfUnityCone R).pt = ProfiniteGrp.of (PrimeToPTateModule 1 R) := (rfl)

/-- The cone maps are the discrete projections. -/
@[simp]
theorem rootsOfUnityCone_π_app_hom (n : RamificationIndexᵒᵖ) :
    ((rootsOfUnityCone R).π.app n).hom = discreteProj n.unop.toPNat := (rfl)

private def coneComponent (s : Cone (rootsOfUnityDiagram R)) (n : ℕ+) :
    s.pt →ₜ* DiscreteRootsOfUnity n R :=
  (s.π.app (Opposite.op ⟨n⟩)).hom

private theorem coneComponent_transition (s : Cone (rootsOfUnityDiagram R))
    {n m : ℕ+} (h : n ∣ m) (x : s.pt) :
    DiscreteRootsOfUnity.transition h (coneComponent R s m x) = coneComponent R s n x :=
  ConcreteCategory.congr_hom (s.w (homOfLE (x := (⟨n⟩ : RamificationIndex)) (y := ⟨m⟩) h).op) x

private def coneLiftHom (s : Cone (rootsOfUnityDiagram R)) :
    s.pt →* PrimeToPTateModule 1 R :=
  lift
    (fun m ↦ by
      let n : ℕ+ := ⟨m, Nat.pos_of_ne_zero m.2.1⟩
      exact (DiscreteRootsOfUnity.equivRootsOfUnity (R := R) (n := n)).toMonoidHom.comp
        (coneComponent R s n).toMonoidHom)
    (fun m n x h ↦ by
      let m' : ℕ+ := ⟨m, Nat.pos_of_ne_zero m.2.1⟩
      let n' : ℕ+ := ⟨n, Nat.pos_of_ne_zero n.2.1⟩
      have h' : n' ∣ m' := PNat.dvd_iff.mpr h
      calc
        _ = (DiscreteRootsOfUnity.equivRootsOfUnity
            (DiscreteRootsOfUnity.transition h' (coneComponent R s m' x)) : Rˣ) :=
          (DiscreteRootsOfUnity.coe_transition h' (coneComponent R s m' x)).symm
        _ = _ := congrArg (fun ζ ↦ (DiscreteRootsOfUnity.equivRootsOfUnity ζ : Rˣ))
          (coneComponent_transition R s h' x))

private theorem proj_coneLiftHom (s : Cone (rootsOfUnityDiagram R))
    (m : {m : ℕ // m ≠ 0 ∧ m.Coprime 1}) (x : s.pt) :
    proj m (coneLiftHom R s x) = DiscreteRootsOfUnity.equivRootsOfUnity
      (coneComponent R s ⟨m, Nat.pos_of_ne_zero m.2.1⟩ x) :=
  proj_lift _ _ m x

private def coneLift (s : Cone (rootsOfUnityDiagram R)) :
    s.pt →ₜ* PrimeToPTateModule 1 R :=
  { coneLiftHom R s with
    continuous_toFun := continuous_iff.mpr fun m ↦ by
      let n : ℕ+ := ⟨m, Nat.pos_of_ne_zero m.2.1⟩
      have hc := ((IsLocallyConstant.iff_continuous _).mpr
        (coneComponent R s n).continuous).comp
          (DiscreteRootsOfUnity.equivRootsOfUnity (R := R) (n := n))
      have heq : (fun x ↦ proj m (coneLiftHom R s x)) =
          (fun x ↦ DiscreteRootsOfUnity.equivRootsOfUnity (coneComponent R s n x)) :=
        funext (proj_coneLiftHom R s m)
      exact heq.symm ▸ hc }

private theorem proj_coneLift (s : Cone (rootsOfUnityDiagram R))
    (m : {m : ℕ // m ≠ 0 ∧ m.Coprime 1}) (x : s.pt) :
    proj m (coneLift R s x) = DiscreteRootsOfUnity.equivRootsOfUnity
      (coneComponent R s ⟨m, Nat.pos_of_ne_zero m.2.1⟩ x) :=
  proj_coneLiftHom R s m x

/-- The Tate module is the inverse limit of the finite discrete groups of roots of unity
in `ProfiniteGrp`: every compatible family of continuous homomorphisms factors uniquely
through its projections. -/
def rootsOfUnityConeIsLimit : IsLimit (rootsOfUnityCone R) where
  lift s := ProfiniteGrp.ofHom (coneLift R s)
  fac s n := by
    rcases n with ⟨⟨n⟩⟩
    dsimp only [rootsOfUnityCone, rootsOfUnityDiagram]
    apply ProfiniteGrp.hom_ext
    apply ContinuousMonoidHom.ext
    intro x
    simp only [ProfiniteGrp.hom_comp, ProfiniteGrp.hom_ofHom,
      ContinuousMonoidHom.coe_comp, Function.comp_apply]
    apply DiscreteRootsOfUnity.equivRootsOfUnity.injective
    rw [equivRootsOfUnity_discreteProj]
    exact proj_coneLift R s ⟨n, n.ne_zero, Nat.coprime_one_right _⟩ x
  uniq s f hf := by
    dsimp only [rootsOfUnityCone, rootsOfUnityDiagram] at f hf ⊢
    apply ProfiniteGrp.hom_ext
    apply ContinuousMonoidHom.ext
    intro x
    apply ext
    intro m
    rw [ProfiniteGrp.hom_ofHom, proj_coneLift]
    let n : ℕ+ := ⟨m, Nat.pos_of_ne_zero m.2.1⟩
    have h := congrArg (fun g ↦ (ProfiniteGrp.Hom.hom g) x) (hf (Opposite.op ⟨n⟩))
    simp only [ProfiniteGrp.hom_comp, ProfiniteGrp.hom_ofHom,
      ContinuousMonoidHom.coe_comp, Function.comp_apply] at h
    have h' := congrArg (DiscreteRootsOfUnity.equivRootsOfUnity (R := R) (n := n)) h
    rw [equivRootsOfUnity_discreteProj] at h'
    exact h'

end PrimeToPTateModule

end TauCeti
