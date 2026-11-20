/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Homotopy.Hurewicz.One.Naturality
public import Mathlib.Algebra.Exact.Basic

/-!
# Homomorphisms out of first integral homology

A homomorphism from the fundamental group of a path-connected space to an abelian group
factors uniquely through first integral singular homology. `homologyLift` gives this factor,
with its computation on loop classes. For a continuous map whose fundamental-group image is
the kernel of the original homomorphism, `exact_homologyMap_homologyLift` proves exactness
on first homology. This applies in particular to connected abelian covering spaces.

The construction uses the degree-one Hurewicz isomorphism, following Hatcher,
*Algebraic Topology*, Theorem 2A.1.
-/

public section
noncomputable section

open CategoryTheory

namespace TauCeti.HurewiczOne

variable {H : Type*} [AddCommGroup H]

section Lift

variable {X : Type} [TopologicalSpace X] [PathConnectedSpace X]

/-- The homomorphism on first integral homology induced by an abelian-valued homomorphism
on the fundamental group. -/
def homologyLift (x : X) (φ : FundamentalGroup X x →* Multiplicative H) :
    ((singularChains ℤ).obj (TopCat.of X)).homology 1 →+ H :=
  (MonoidHom.toAdditiveLeft (Group.Abelianization.lift φ)).comp
    (hurewiczHomologyAddEquiv (X := TopCat.of X) x).symm.toAddMonoidHom

/-- The homology lift evaluates the Hurewicz class through the abelianization lift. -/
@[simp↓]
theorem homologyLift_hurewiczHomologyAddEquiv (x : X)
    (φ : FundamentalGroup X x →* Multiplicative H)
    (a : Additive (Group.Abelianization (FundamentalGroup X x))) :
    homologyLift x φ (hurewiczHomologyAddEquiv (X := TopCat.of X) x a) =
      (Group.Abelianization.lift φ a.toMul).toAdd := by
  simp [homologyLift, MonoidHom.coe_toAdditiveLeft]

/-- On a loop class, the homology lift agrees with the original fundamental-group map. -/
@[simp↓]
theorem homologyLift_H₁AddEquivHomology_loopClass {x : X}
    (φ : FundamentalGroup X x →* Multiplicative H) (γ : Path x x) :
    homologyLift x φ (H₁AddEquivHomology (TopCat.of X) (loopClass γ)) =
      (φ (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk γ))).toAdd := by
  rw [← hurewiczHomologyAddEquiv_ofMul_of_mk, homologyLift_hurewiczHomologyAddEquiv]
  simp

/-- A homomorphism on first homology agreeing with `φ` on Hurewicz classes is its unique
homology lift. -/
theorem homologyLift_unique (x : X) (φ : FundamentalGroup X x →* Multiplicative H)
    (ψ : ((singularChains ℤ).obj (TopCat.of X)).homology 1 →+ H)
    (hψ : ∀ g : FundamentalGroup X x,
      ψ (hurewiczHomologyAddEquiv (X := TopCat.of X) x
        (Additive.ofMul (Group.Abelianization.of g))) = (φ g).toAdd) :
    ψ = homologyLift x φ := by
  ext a
  obtain ⟨b, rfl⟩ := (hurewiczHomologyAddEquiv (X := TopCat.of X) x).surjective a
  obtain ⟨g, rfl⟩ := Group.Abelianization.exists_eq_ofMul_of b
  simp [hψ]

/-- A surjective fundamental-group homomorphism induces a surjective homology lift. -/
theorem homologyLift_surjective (x : X) (φ : FundamentalGroup X x →* Multiplicative H)
    (hφ : Function.Surjective φ) : Function.Surjective (homologyLift x φ) := by
  intro h
  obtain ⟨g, hg⟩ := hφ (Multiplicative.ofAdd h)
  refine ⟨hurewiczHomologyAddEquiv (X := TopCat.of X) x
    (Additive.ofMul (Group.Abelianization.of g)), ?_⟩
  simp [hg]

end Lift

variable {X Y : TopCat.{0}} [PathConnectedSpace X]

/-- If the image of a pointed continuous map on fundamental groups is `ker φ`, its homology
map followed by the abelian-valued homology lift of `φ` is exact. Surjectivity of `φ` is not
needed for exactness at first homology. -/
theorem exact_homologyMap_homologyLift [PathConnectedSpace Y]
    (f : X ⟶ Y) {x : X} {y : Y} (h : f x = y)
    (φ : FundamentalGroup Y y →* Multiplicative H)
    (hRange : (FundamentalGroup.mapOfEq f.hom h).range = φ.ker) :
    Function.Exact (HomologicalComplex.homologyMap ((singularChains ℤ).map f) 1).hom
      (homologyLift y φ) := by
  -- The evaluation theorem is stated for raw types. Both rewrites below use `(X := Y)`
  -- to match its `TopCat.of ↑Y` homology carrier with bundled `Y` by definitional equality.
  intro a
  obtain ⟨b, rfl⟩ := (hurewiczHomologyAddEquiv y).surjective a
  obtain ⟨g, rfl⟩ := Group.Abelianization.exists_eq_ofMul_of b
  constructor
  · intro hg
    have hgker : g ∈ φ.ker := by
      rw [homologyLift_hurewiczHomologyAddEquiv (X := Y) y φ] at hg
      simpa using hg
    rw [← hRange] at hgker
    obtain ⟨k, hk⟩ := hgker
    refine ⟨hurewiczHomologyAddEquiv x (Additive.ofMul (Group.Abelianization.of k)), ?_⟩
    rw [homologyMap_hurewiczHomologyAddEquiv_mapOfEq f h]
    simp [hk]
  · rintro ⟨c, hc⟩
    obtain ⟨d, rfl⟩ := (hurewiczHomologyAddEquiv x).surjective c
    obtain ⟨k, rfl⟩ := Group.Abelianization.exists_eq_ofMul_of d
    rw [← hc, homologyMap_hurewiczHomologyAddEquiv_mapOfEq f h]
    have hk : FundamentalGroup.mapOfEq f.hom h k ∈ φ.ker := by
      rw [← hRange]
      exact ⟨k, rfl⟩
    rw [homologyLift_hurewiczHomologyAddEquiv (X := Y) y φ]
    simpa using hk

end TauCeti.HurewiczOne
