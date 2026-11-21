/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.LocalHomology.Orientation.Basic

/-!
# Transport of local orientations

The integral local homology system transports generators along paths. This file restricts its
transport to equivalences between the sets of local orientations, compatible with identities,
composition, path reversal and orientation reversal. They act on the generator fibres of the
existing integral local homology system. Along loops at `x` they form an action of the
fundamental group on the local orientations at `x` (`TauCeti.localOrientationTransportPerm`). In
the dimension of a manifold, transport along a loop either fixes every local orientation or
reverses every local orientation (`TauCeti.localOrientationTransport_eq_self_of_eq_self`,
`TauCeti.localOrientationTransport_eq_neg_of_eq_neg`).

The underlying local homology transport is described through compact convex sets in charts by
`TauCeti.localHomologyRestriction_comp_localHomologyTransport` in
`TauCeti.AlgebraicTopology.Singular.LocalHomology.System`.

The transport is defined in every degree; in the dimension of a manifold its fibres have two
orientations, as described by `TauCeti.isLocalOrientation_iff_eq_or_eq_neg_inv_one` and the chart
computation of local homology.

## References

* A. Hatcher, *Algebraic Topology*, Section 3.3: transport of local orientations through local
  homology over balls.
-/

public section

noncomputable section

open CategoryTheory

universe w

namespace TauCeti

variable (M E : Type w) [TopologicalSpace M] [T2Space M]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [ChartedSpace E M]
  (d : ℕ)

/-- Transport of local orientations along a path class, obtained by restricting the integral
local homology transport to its generators. -/
def localOrientationTransport {x y : FundamentalGroupoid M} (f : x ⟶ y) :
    LocalOrientation M x.as d ≃ LocalOrientation M y.as d :=
  let e := (localHomologySystem (A := ModuleCat.{w} ℤ)
    (ModuleCat.of ℤ (ULift.{w} ℤ)) M E d).mapIso (asIso f)
  e.toLinearEquiv.toEquiv.subtypeEquiv fun z ↦
    ⟨fun hz ↦ hz.map e, fun hz ↦ (e.hom_inv_id_apply z) ▸ hz.map e.symm⟩

/-- On local homology classes, orientation transport is the integral local homology transport. -/
@[simp]
lemma coe_localOrientationTransport {x y : FundamentalGroupoid M} (f : x ⟶ y)
    (z : LocalOrientation M x.as d) :
    (localOrientationTransport M E d f z).val =
      localHomologyTransport (A := ModuleCat.{w} ℤ) (ModuleCat.of ℤ (ULift.{w} ℤ)) M E d f z.val :=
  (rfl)

/-- The inverse equivalence acts on classes by transport along the reversed path. -/
@[simp]
lemma coe_localOrientationTransport_symm {x y : FundamentalGroupoid M} (f : x ⟶ y)
    (z : LocalOrientation M y.as d) :
    ((localOrientationTransport M E d f).symm z).val =
      localHomologyTransport (A := ModuleCat.{w} ℤ) (ModuleCat.of ℤ (ULift.{w} ℤ))
        M E d (inv f) z.val :=
  (rfl)

@[simp]
lemma localOrientationTransport_id (x : FundamentalGroupoid M) :
    localOrientationTransport M E d (𝟙 x) = Equiv.refl _ := by
  apply Equiv.ext
  intro z
  apply Subtype.ext
  simp

/-- Transport along a composite is successive transport along its two paths. -/
@[simp]
lemma localOrientationTransport_comp {x y z : FundamentalGroupoid M} (f : x ⟶ y)
    (g : y ⟶ z) :
    localOrientationTransport M E d (f ≫ g) =
      (localOrientationTransport M E d f).trans (localOrientationTransport M E d g) := by
  apply Equiv.ext
  intro a
  apply Subtype.ext
  simp [localHomologyTransport_comp]

/-- Reversing a path inverts its equivalence of local orientations. -/
@[simp]
lemma localOrientationTransport_inv {x y : FundamentalGroupoid M} (f : x ⟶ y) :
    localOrientationTransport M E d (inv f) = (localOrientationTransport M E d f).symm := by
  ext z
  simp

/-- Transport commutes with reversal of local orientations. -/
@[simp]
lemma localOrientationTransport_neg {x y : FundamentalGroupoid M} (f : x ⟶ y)
    (z : LocalOrientation M x.as d) :
    localOrientationTransport M E d f (-z) = -(localOrientationTransport M E d f z) := by
  apply Subtype.ext
  exact (localHomologyTransport (A := ModuleCat.{w} ℤ) (ModuleCat.of ℤ (ULift.{w} ℤ))
      M E d f).hom.map_neg z.val

/-- Transport of local orientations along loops at `x`: the action of the fundamental group
`π₁(M, x)` on the local orientations at `x`. -/
def localOrientationTransportPerm (x : M) :
    FundamentalGroup M x →* Equiv.Perm (LocalOrientation M x d) where
  toFun γ := localOrientationTransport M E d γ.asHom
  map_one' := by
    rw [End.one_asHom, localOrientationTransport_id, Equiv.Perm.one_def]
  map_mul' γ δ := by
    rw [End.mul_asHom, localOrientationTransport_comp, Equiv.Perm.mul_def]

@[simp]
lemma localOrientationTransportPerm_apply (x : M) (γ : FundamentalGroup M x) :
    localOrientationTransportPerm M E d x γ = localOrientationTransport M E d γ.asHom :=
  (rfl)

variable {M d}

/-- Transport of local orientations along a loop is the identity as soon as it fixes one local
orientation. -/
theorem localOrientationTransport_eq_self_of_eq_self (hd : Module.finrank ℝ E = d) {x : M}
    (γ : FundamentalGroupoid.mk x ⟶ FundamentalGroupoid.mk x) {z₀ : LocalOrientation M x d}
    (h : localOrientationTransport M E d γ z₀ = z₀) (z : LocalOrientation M x d) :
    localOrientationTransport M E d γ z = z := by
  rcases LocalOrientation.eq_or_eq_neg hd z₀ z with rfl | rfl
  · exact h
  · rw [localOrientationTransport_neg, h]

/-- Transport of local orientations along a loop reverses every local orientation as soon as it
reverses one. -/
theorem localOrientationTransport_eq_neg_of_eq_neg (hd : Module.finrank ℝ E = d) {x : M}
    (γ : FundamentalGroupoid.mk x ⟶ FundamentalGroupoid.mk x) {z₀ : LocalOrientation M x d}
    (h : localOrientationTransport M E d γ z₀ = -z₀) (z : LocalOrientation M x d) :
    localOrientationTransport M E d γ z = -z := by
  rcases LocalOrientation.eq_or_eq_neg hd z₀ z with rfl | rfl
  · exact h
  · rw [localOrientationTransport_neg, h]

end TauCeti
