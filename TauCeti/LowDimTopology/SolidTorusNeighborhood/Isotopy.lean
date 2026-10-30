/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Circle
public import TauCeti.LowDimTopology.SolidTorusNeighborhood.Basic
public import TauCeti.Topology.Homotopy.AmbientIsotopyConj
public import TauCeti.Topology.Homotopy.Isotopy.Radial

/-!
# Isotopies of the boundary torus extend over the solid torus

A homeomorphism of the boundary torus `S¹ × S¹` of the solid torus `V = D² × S¹` which is the final
homeomorphism of an ambient isotopy extends to a homeomorphism of `V`: the isotopy is run along the
radial coordinate of the disc factor, in the collar `1 / 2 ≤ ‖w‖ ≤ 1`, and the extension is the
identity on the core solid torus `‖w‖ ≤ 1 / 2` (`TauCeti.AmbientIsotopy.solidTorusHomeomorph`).
This is the case `D × Z = D² × S¹` of `TauCeti.AmbientIsotopy.closedBallProdHomeomorph`, read
through the identification `Circle ≃ₜ sphere (0 : ℂ) 1`.

Consequently the torus homeomorphisms extending over `V` are closed under composition with
homeomorphisms isotopic to the identity
(`TauCeti.SolidTorus.exists_homeomorph_boundaryInclusion_comp_final`). This is the isotopy step
of the classical proof that a Dehn filling depends only on its slope (Rolfsen, *Knots and Links*,
Section 9F): two fillings of a knot exterior whose gluings `g`, `g'` differ by a torus
homeomorphism `g'⁻¹ ∘ g` extending over the filling solid torus are homeomorphic, by the identity
on the exterior and that extension on the solid torus, so a gluing may be replaced by any gluing
isotopic to it. Here the isotopy is absorbed into a collar inside the filling solid torus, so no
collar of the exterior is needed.

## Main definitions

* `TauCeti.AmbientIsotopy.solidTorusHomeomorph`: the homeomorphism of the solid torus extending
  the final homeomorphism of an ambient isotopy of its boundary torus.

## Main results

* `TauCeti.AmbientIsotopy.solidTorusHomeomorph_boundaryInclusion`: on the boundary torus it is the
  final homeomorphism of the isotopy.
* `TauCeti.AmbientIsotopy.solidTorusHomeomorph_of_norm_le`: it is the identity on the core
  `‖w‖ ≤ 1 / 2`.
* `TauCeti.SolidTorus.exists_homeomorph_boundaryInclusion_comp_final`: if a homeomorphism `h` of
  the boundary torus extends over the solid torus, so does `h ∘ Φ₁` for every ambient isotopy `Φ`
  of the torus.

## References

* D. Rolfsen, *Knots and Links*, Publish or Perish (1976), Section 9F (the result of a Dehn
  filling depends only on the isotopy class of the gluing).
-/

public section

noncomputable section

namespace TauCeti

open Metric Set

namespace AmbientIsotopy

variable (Φ : AmbientIsotopy (Circle × Circle))

/-- The **extension of an ambient isotopy of the boundary torus over the solid torus**
`V = D² × S¹`: the isotopy `Φ` of `S¹ × S¹` is run along the radial coordinate `‖w‖ ∈ [1 / 2, 1]`
of the disc factor. It is the identity on the core `‖w‖ ≤ 1 / 2`
(`solidTorusHomeomorph_of_norm_le`) and the final homeomorphism of `Φ` on the boundary torus
(`solidTorusHomeomorph_boundaryInclusion`). -/
def solidTorusHomeomorph : SolidTorus ≃ₜ SolidTorus :=
  (Φ.transport
    (Circle.homeomorphSphere.prodCongr (Homeomorph.refl Circle))).closedBallProdHomeomorph

/-- The boundary inclusion of the solid torus, read through `Circle ≃ₜ sphere (0 : ℂ) 1`, is the
inclusion of the unit sphere into the closed unit ball. -/
private theorem boundaryInclusion_eq (q : Circle × Circle) :
    SolidTorus.boundaryInclusion q =
      (inclusion sphere_subset_closedBall
          ((Circle.homeomorphSphere.prodCongr (Homeomorph.refl Circle)) q).1,
        ((Circle.homeomorphSphere.prodCongr (Homeomorph.refl Circle)) q).2) :=
  Prod.ext (Subtype.ext (by simp [Circle.coe_homeomorphSphere_apply])) (by simp)

/-- On the boundary torus the extension of `Φ` is the final homeomorphism of `Φ`. -/
@[simp]
theorem solidTorusHomeomorph_boundaryInclusion (q : Circle × Circle) :
    Φ.solidTorusHomeomorph (SolidTorus.boundaryInclusion q) =
      SolidTorus.boundaryInclusion (Φ.final q) := by
  rw [boundaryInclusion_eq, boundaryInclusion_eq, solidTorusHomeomorph,
    closedBallProdHomeomorph_inclusion, final_transport, Homeomorph.symm_apply_apply]

/-- The extension of `Φ` over the solid torus is the identity on the core `‖w‖ ≤ 1 / 2`. -/
theorem solidTorusHomeomorph_of_norm_le {p : SolidTorus} (hp : ‖(p.1 : ℂ)‖ ≤ 1 / 2) :
    Φ.solidTorusHomeomorph p = p :=
  closedBallProdHomeomorph_of_norm_le _ hp

end AmbientIsotopy

/-- **Isotopies are absorbed by the solid torus.** If a homeomorphism `h` of the boundary torus
extends to a homeomorphism `ψ` of the solid torus, then so does `h ∘ Φ₁` for every ambient isotopy
`Φ` of the torus: so whether a torus homeomorphism extends over the solid torus only depends on it
up to isotopy. -/
theorem SolidTorus.exists_homeomorph_boundaryInclusion_comp_final
    {h : Circle × Circle → Circle × Circle} (ψ : SolidTorus ≃ₜ SolidTorus)
    (hψ : ∀ q, ψ (SolidTorus.boundaryInclusion q) = SolidTorus.boundaryInclusion (h q))
    (Φ : AmbientIsotopy (Circle × Circle)) :
    ∃ ψ' : SolidTorus ≃ₜ SolidTorus,
      ∀ q, ψ' (SolidTorus.boundaryInclusion q) = SolidTorus.boundaryInclusion (h (Φ.final q)) :=
  ⟨Φ.solidTorusHomeomorph.trans ψ, fun q => by
    rw [Homeomorph.trans_apply, AmbientIsotopy.solidTorusHomeomorph_boundaryInclusion, hψ]⟩

end TauCeti
