/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Cohomology.Support.BasicOpen

/-!
# Example: `H¹_Z(𝔸¹, 𝒪) = R[t, t⁻¹] / R[t]` for `Z` the origin

On the affine line `𝔸¹_R = Spec R[t]` over a commutative ring `R`, let `Z = V(t)` be the origin,
the complement of the basic open `D(t)`. Since `𝔸¹_R` is affine, `H¹(𝔸¹_R, 𝒪) = 0`, so the long
exact sequence of supports identifies `H¹_Z(𝔸¹_R, 𝒪)` with the cokernel of the restriction
`Γ(𝔸¹_R, 𝒪) → Γ(D(t), 𝒪)`, that is, of `R[t] → R[t, t⁻¹]`
(`TauCeti.AlgebraicGeometry.SupportDegreeOneExample.cohomologyWithSupportOneAddEquiv`).
-/

public section

open AlgebraicGeometry Polynomial

universe u

noncomputable section

namespace TauCeti.AlgebraicGeometry.SupportDegreeOneExample

variable (R : Type u) [CommRing R]

/-- The affine line `𝔸¹_R = Spec R[t]`. -/
abbrev affineLine : Scheme.{u} := Spec (.of R[X])

/-- The coordinate `t` of `𝔸¹_R`, as a global function. -/
abbrev coordinate : Γ(affineLine R, ⊤) := (Scheme.ΓSpecIso (.of R[X])).inv X

/-- **`H¹_Z(𝔸¹_R, 𝒪) = R[t, t⁻¹] / R[t]` for `Z` the origin.** On the affine line over a
commutative ring `R`, the first cohomology of the structure sheaf with supports in the origin
`V(t)` is the quotient of the Laurent polynomials `R[t, t⁻¹]` by the polynomials `R[t]`. -/
abbrev cohomologyWithSupportOneAddEquiv :
    (Scheme.Modules.unit (affineLine R)).cohomologyWithSupport
        ((affineLine R).basicOpen (coordinate R)).compl ⊤ 1 ≃+
      Localization.Away (X : R[X]) ⧸
        (algebraMap R[X] (Localization.Away (X : R[X]))).toAddMonoidHom.range :=
  Scheme.Modules.cohomologyWithSupportOneComplBasicOpenSpecUnitAddEquiv X _

end TauCeti.AlgebraicGeometry.SupportDegreeOneExample

end
