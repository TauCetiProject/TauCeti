/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.BorelCalculus.Unitary
public import TauCeti.Analysis.InnerProductSpace.Modulus
public import TauCeti.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Connected
public import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Invertible

/-!
# Norm-path-connectedness of `GL(H)` and invertible Hilbert-space operators

This file combines the continuous-functional-calculus polar homotopy for units
(`TauCeti.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Connected`) with Putnam–Wintner
unitary Borel logarithms (`TauCeti.Analysis.InnerProductSpace.BorelCalculus.Unitary`) to establish
norm-path-connectedness of the general linear group `(H →L[ℂ] H)ˣ` and rectangular invertible
operator spaces `{A : E →L[ℂ] F // A.IsInvertible}` over `ℂ`, with no separability or
finite-dimensionality assumptions.

## Main declarations

* `Units.borelPolarPathToOne`: the explicit polar-linear path
  `t ↦ exp(i t borelArg g.polarUnitary) ∘L ((1 - t) • 1 + t • |g|)` from `1` to `g` in
  `(H →L[ℂ] H)ˣ`.
* `Units.instPathConnectedSpaceContinuousLinearMap`,
  `ContinuousLinearMap.isPathConnected_isUnit`,
  `ContinuousLinearMap.isPathConnected_isInvertible_endo`: norm-path-connectedness of
  `(H →L[ℂ] H)ˣ` and `{T : H →L[ℂ] H | T.IsInvertible}` in arbitrary Hilbert dimension.
* `ContinuousLinearMap.IsInvertible.borelPolarPath`,
  `ContinuousLinearMap.IsInvertible.joinedIn`,
  `ContinuousLinearMap.isPreconnected_isInvertible`,
  `ContinuousLinearMap.isPathConnected_isInvertible_iff`: explicit norm-continuous paths between any
  two invertible bounded operators `S, T : E →L[ℂ] F` from a complex Hilbert space `E` to a complex
  seminormed space `F`, showing that `{A : E →L[ℂ] F | A.IsInvertible}` is preconnected and is
  path-connected if and only if `Nonempty (E ≃L[ℂ] F)`.

## References

* C. R. Putnam, A. Wintner, *The Orthogonal Group in Hilbert Space*,
  Amer. J. Math. **74** (1952), 52–78.
* R. G. Douglas, *Banach Algebra Techniques in Operator Theory*, 2nd ed., Springer (1998),
  Corollary 4.30.
-/

public section

noncomputable section

open scoped InnerProduct unitInterval

section Complex

section Endo

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace Units

/-- The explicit Putnam–Wintner polar-linear path from `1` to `g` in `(H →L[ℂ] H)ˣ`, given by
`t ↦ exp(i t borelArg g.polarUnitary) ∘L ((1 - t) • 1 + t • |g|)`. -/
def borelPolarPathToOne (g : (H →L[ℂ] H)ˣ) : Path 1 g :=
  g.polarPathToOne (Unitary.borelPathToOne g.polarUnitary)

/-- Evaluating `g.borelPolarPathToOne` at `t` in `H →L[ℂ] H` gives the product of the unitary Borel
exponential path and the straight-line modulus interpolation. -/
@[simp]
theorem val_borelPolarPathToOne_apply (g : (H →L[ℂ] H)ˣ) (t : I) :
    (g.borelPolarPathToOne t : H →L[ℂ] H) =
      NormedSpace.exp (Complex.I • ((t : ℝ) • (Unitary.borelArg g.polarUnitary : H →L[ℂ] H))) *
        ((1 - (t : ℝ)) • (1 : H →L[ℂ] H) + (t : ℝ) • (g : H →L[ℂ] H).modulus) := by
  simp [borelPolarPathToOne, (g : H →L[ℂ] H).modulus_eq_sqrt, ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.mul_def]

/-- **Norm-path-connectedness of `GL(H)`.** For every complex Hilbert space `H` (without any
separability or finite-dimensionality assumption), the group of invertible bounded operators
`(H →L[ℂ] H)ˣ` is path-connected in the operator norm topology. -/
instance instPathConnectedSpaceContinuousLinearMap : PathConnectedSpace (H →L[ℂ] H)ˣ :=
  pathConnectedSpace_of_unitary

/-- The path component of `1` in `(H →L[ℂ] H)ˣ` is the entire general linear group. -/
@[simp]
theorem pathComponent_one_continuousLinearMap_eq_univ :
    pathComponent (1 : (H →L[ℂ] H)ˣ) = Set.univ :=
  Set.eq_univ_of_forall (PathConnectedSpace.joined 1)

end Units

namespace ContinuousLinearMap

/-- The set `{T : H →L[ℂ] H | IsUnit T}` of invertible bounded endomorphisms on a complex Hilbert
space `H` is path-connected in the operator norm topology. -/
theorem isPathConnected_isUnit : IsPathConnected {T : H →L[ℂ] H | IsUnit T} :=
  Units.isPathConnected_isUnit_of_unitary

/-- The set `{T : H →L[ℂ] H | T.IsInvertible}` of invertible bounded endomorphisms on a complex
Hilbert space `H` is path-connected in the operator norm topology. -/
theorem isPathConnected_isInvertible_endo : IsPathConnected {T : H →L[ℂ] H | T.IsInvertible} := by
  convert isPathConnected_isUnit (H := H) using 1
  ext T
  exact isInvertible_iff_isUnit

end ContinuousLinearMap

end Endo

section Rectangular

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [SeminormedAddCommGroup F] [NormedSpace ℂ F]

namespace ContinuousLinearMap

/-- Explicit operator-norm continuous path in `{A : E →L[ℂ] F // A.IsInvertible}` joining any two
invertible bounded operators `S, T : E →L[ℂ] F` from a complex Hilbert space `E` to a complex
seminormed space `F`, obtained by transporting `Units.borelPolarPathToOne` for the unit
`S.inverse ∘L T : (E →L[ℂ] E)ˣ` along left composition with `S`. -/
def IsInvertible.borelPolarPath {S T : E →L[ℂ] F}
    (hS : S.IsInvertible) (hT : T.IsInvertible) :
    Path (⟨S, hS⟩ : {A : E →L[ℂ] F // A.IsInvertible}) ⟨T, hT⟩ where
  toFun t :=
    let u : (E →L[ℂ] E)ˣ := (isInvertible_iff_isUnit.1 (hS.inverse.comp hT)).unit
    ⟨S ∘L (u.borelPolarPathToOne t : E →L[ℂ] E),
      hS.comp (isInvertible_iff_isUnit.2 (u.borelPolarPathToOne t).isUnit)⟩
  continuous_toFun := by
    let u : (E →L[ℂ] E)ˣ := (isInvertible_iff_isUnit.1 (hS.inverse.comp hT)).unit
    exact Continuous.subtype_mk
      (continuous_const.clm_comp (Units.continuous_val.comp u.borelPolarPathToOne.continuous)) _
  source' := Subtype.ext <| by
    simp only [Path.source, Units.val_one, one_def, comp_id]
  target' := Subtype.ext <| by
    have hu : (((isInvertible_iff_isUnit.1 (hS.inverse.comp hT)).unit : (E →L[ℂ] E)ˣ) :
        E →L[ℂ] E) = S.inverse ∘L T := IsUnit.unit_spec _
    simp only [Path.target, hu, ← comp_assoc, hS.self_comp_inverse, id_comp]

/-- Evaluating `hS.borelPolarPath hT` at `t` gives `S` composed with `borelPolarPathToOne` for the
transition unit `S.inverse ∘L T`. -/
@[simp]
theorem IsInvertible.coe_borelPolarPath_apply {S T : E →L[ℂ] F}
    (hS : S.IsInvertible) (hT : T.IsInvertible) (t : I) :
    (hS.borelPolarPath hT t : E →L[ℂ] F) =
      S ∘L (((isInvertible_iff_isUnit.1 (hS.inverse.comp hT)).unit).borelPolarPathToOne t :
        E →L[ℂ] E) :=
  (rfl)

/-- Any two invertible bounded operators `S, T : E →L[ℂ] F` from a complex Hilbert space `E` to a
complex seminormed space `F` are joined by an operator-norm continuous path within
`{A : E →L[ℂ] F | A.IsInvertible}`. -/
theorem IsInvertible.joinedIn {S T : E →L[ℂ] F}
    (hS : S.IsInvertible) (hT : T.IsInvertible) :
    JoinedIn {A : E →L[ℂ] F | A.IsInvertible} S T :=
  (joinedIn_iff_joined hS hT).2 ⟨hS.borelPolarPath hT⟩

/-- For a complex Hilbert space `E` and a complex seminormed space `F`, the set
`{A : E →L[ℂ] F | A.IsInvertible}` of invertible bounded operators is preconnected in the operator
norm topology (it is either empty or path-connected). -/
theorem isPreconnected_isInvertible : IsPreconnected {A : E →L[ℂ] F | A.IsInvertible} := by
  rcases Set.eq_empty_or_nonempty {A : E →L[ℂ] F | A.IsInvertible} with h | h
  · exact h ▸ isPreconnected_empty
  · exact (isPathConnected_iff.2 ⟨h, fun _ hS _ hT ↦ hS.joinedIn hT⟩).isConnected.isPreconnected

/-- The subtype `{A : E →L[ℂ] F // A.IsInvertible}` of invertible bounded operators from a complex
Hilbert space `E` to a complex seminormed space `F` is preconnected in the operator norm topology.
-/
instance instPreconnectedSpaceSubtypeIsInvertible :
    PreconnectedSpace {A : E →L[ℂ] F // A.IsInvertible} :=
  isPreconnected_iff_preconnectedSpace.1 isPreconnected_isInvertible

/-- When `E` and `F` are continuously linearly equivalent (with `E` a complex Hilbert space), the
space `{A : E →L[ℂ] F // A.IsInvertible}` of invertible bounded operators is norm-path-connected. -/
instance instPathConnectedSpaceSubtypeIsInvertible [h : Nonempty (E ≃L[ℂ] F)] :
    PathConnectedSpace {A : E →L[ℂ] F // A.IsInvertible} where
  nonempty := let ⟨e⟩ := h; ⟨⟨e, isInvertible_equiv⟩⟩
  joined S T := ⟨S.property.borelPolarPath T.property⟩

/-- For a complex Hilbert space `E` and a complex seminormed space `F`,
`{A : E →L[ℂ] F | A.IsInvertible}` is path-connected if and only if `E` and `F` are continuously
linearly equivalent. -/
theorem isPathConnected_isInvertible_iff :
    IsPathConnected {A : E →L[ℂ] F | A.IsInvertible} ↔ Nonempty (E ≃L[ℂ] F) :=
  ⟨fun ⟨_, ⟨e, _⟩, _⟩ ↦ ⟨e⟩, fun ⟨e⟩ ↦
    isPathConnected_iff.2 ⟨⟨e, isInvertible_equiv⟩, fun _ hS _ hT ↦ hS.joinedIn hT⟩⟩

end ContinuousLinearMap

end Rectangular

end Complex
