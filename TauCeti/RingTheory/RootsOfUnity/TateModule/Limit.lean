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
    apply ConcreteCategory.hom_ext
    intro ζ
    -- Reduce the bundled carrier in the variable type so rewriting sees rootsOfUnity.
    dsimp only [FiniteGrp.of] at ζ
    apply Subtype.ext
    -- FiniteGrp's induced-category morphisms use a different coercion from ofHom_apply.
    -- Identify the underlying homomorphism before applying the power-map API.
    change (rootsOfUnityPowOfDvd (M := R) (dvd_refl (n.unop.order : ℕ))
      (ζ : rootsOfUnity n.unop.order R) : Rˣ) = (ζ : rootsOfUnity n.unop.order R).val
    simp [Nat.div_self (Nat.pos_of_ne_zero n.unop.order.2.1)]
  map_comp {n m l} f g := by
    apply ConcreteCategory.hom_ext
    intro ζ
    -- Reduce the bundled carrier in the variable type so rewriting sees rootsOfUnity.
    dsimp only [FiniteGrp.of] at ζ
    apply Subtype.ext
    -- As above, expose only the induced-category coercions, keeping the power maps opaque.
    change (rootsOfUnityPowOfDvd (M := R) (g.unop.le.trans f.unop.le)
      (ζ : rootsOfUnity n.unop.order R) : Rˣ) =
      (rootsOfUnityPowOfDvd (M := R) g.unop.le
        (rootsOfUnityPowOfDvd (M := R) f.unop.le (ζ : rootsOfUnity n.unop.order R)) : Rˣ)
    rw [coe_rootsOfUnityPowOfDvd_apply, coe_rootsOfUnityPowOfDvd_apply,
      coe_rootsOfUnityPowOfDvd_apply, ← pow_mul, Nat.div_mul_div f.unop.le g.unop.le]

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
        letI : TopologicalSpace (rootsOfUnity n.unop.order R) := ⊥
        letI : DiscreteTopology (rootsOfUnity n.unop.order R) := ⟨rfl⟩
        exact ConcreteCategory.ofHom
          ({ toMonoidHom := proj n.unop.order
             continuous_toFun := (isLocallyConstant_proj n.unop.order).continuous } :
            PrimeToPTateModule p R →ₜ* (rootsOfUnityDiagram p R).obj n)
      naturality := fun {n m} f ↦ by
        apply ProfiniteGrp.hom_ext
        apply ContinuousMonoidHom.ext
        intro ζ
        apply Subtype.ext
        simp only [Functor.const_obj_map, ProfiniteGrp.hom_comp,
          ConcreteCategory.hom_ofHom, ContinuousMonoidHom.coe_comp,
          Function.comp_apply, rootsOfUnityDiagram_map_apply]
        -- The cone legs are literal continuous-hom structures; their application does not
        -- simplify through the finite functor's dependent carrier without this identification.
        change (proj m.unop.order ζ : Rˣ) =
          (proj n.unop.order ζ : Rˣ) ^ ((n.unop.order : ℕ) / m.unop.order)
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

private def coneLiftHom (s : Cone (rootsOfUnityDiagram p R)) :
    s.pt →* PrimeToPTateModule p R :=
  lift (fun m ↦ (s.π.app (Opposite.op ⟨m⟩)).hom.toMonoidHom)
    (fun m n x h ↦ by
      have hw := congrArg (fun f ↦ f.hom x)
        (s.w (homOfLE (x := (⟨n⟩ : Index p)) (y := ⟨m⟩) h).op)
      have hv := congrArg (fun ζ : rootsOfUnity n R ↦ ζ.val) hw
      simp only [ProfiniteGrp.hom_comp, ContinuousMonoidHom.coe_comp,
        Function.comp_apply, rootsOfUnityDiagram_map_apply] at hv
      exact hv)

private theorem proj_coneLiftHom (s : Cone (rootsOfUnityDiagram p R))
    (m : {m : ℕ // m ≠ 0 ∧ m.Coprime p}) (x : s.pt) :
    proj m (coneLiftHom p R s x) = (s.π.app (Opposite.op ⟨m⟩)).hom x :=
  proj_lift _ _ m x

private def coneLift (s : Cone (rootsOfUnityDiagram p R)) :
    s.pt →ₜ* PrimeToPTateModule p R :=
  { coneLiftHom p R s with
    continuous_toFun := continuous_iff.mpr fun m ↦ by
      let : DiscreteTopology ((rootsOfUnityDiagram p R).obj (Opposite.op ⟨m⟩)) := ⟨rfl⟩
      have hc := (IsLocallyConstant.iff_continuous _).mpr
        (s.π.app (Opposite.op ⟨m⟩)).hom.continuous
      have heq := funext (proj_coneLiftHom p R s m)
      exact heq.symm ▸ hc }

/-- The prime-to-`p` Tate module is the inverse limit of the finite discrete groups of roots
of unity of order prime to `p` in `ProfiniteGrp`: every compatible family of continuous
homomorphisms factors uniquely through its projections. -/
def rootsOfUnityConeIsLimit : IsLimit (rootsOfUnityCone p R) where
  lift s := ProfiniteGrp.ofHom (coneLift p R s)
  fac s n := by
    -- The source of the cone leg is a dependent field. Reduce the cone to identify its
    -- carrier and topology with the Tate module before applying homomorphism extensionality.
    dsimp only [rootsOfUnityCone]
    apply ProfiniteGrp.hom_ext
    apply ContinuousMonoidHom.ext
    intro x
    simp only [ProfiniteGrp.hom_comp, ProfiniteGrp.hom_ofHom,
      ContinuousMonoidHom.coe_comp, Function.comp_apply]
    exact proj_coneLiftHom p R s n.unop.order x
  uniq s f hf := by
    -- The codomain in f's type must be the Tate module for its extensionality lemma;
    -- rewriting the leg alone leaves the dependent carrier and topology hidden in f.
    dsimp only [rootsOfUnityCone] at f hf ⊢
    apply ProfiniteGrp.hom_ext
    apply ContinuousMonoidHom.ext
    intro x
    apply ext
    intro m
    rw [ProfiniteGrp.hom_ofHom]
    have h := congrArg (fun g ↦ (ProfiniteGrp.Hom.hom g) x) (hf (Opposite.op ⟨m⟩))
    simp only [ProfiniteGrp.hom_comp, ConcreteCategory.hom_ofHom,
      ContinuousMonoidHom.coe_comp, Function.comp_apply] at h
    exact h.trans (proj_coneLiftHom p R s m x).symm

end TauCeti.PrimeToPTateModule
