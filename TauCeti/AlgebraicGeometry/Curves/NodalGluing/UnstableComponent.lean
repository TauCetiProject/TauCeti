/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.NodalGluing.ComponentAut
public import TauCeti.Geometry.Diffeomorphism.RelativeCongr
public import TauCeti.Geometry.Manifold.Instances.OnePoint.FixingSubgroup

/-!
# Unstable rational and elliptic components

A marked nodal curve is presented by its normalization components `X i`, its flag pairs and its
marks. A component with infinitely many diffeomorphisms fixing its special points (every flag
point and every mark lying on it, `Marking.specialPoints`) makes the ordered automorphism group
infinite (`AuxiliaryAut.infinite_ordered_of_infinite_fixingSubgroup`, in
`TauCeti.AlgebraicGeometry.Curves.NodalGluing.ComponentAut`). This happens for a component
diffeomorphic to the projective line carrying at most two special points, where the Möbius
dilations fixing those points give infinitely many
(`AuxiliaryAut.infinite_ordered_of_encard_specialPoints_le_two`). Contrapositively, when the
ordered automorphism group is finite, every component diffeomorphic to the projective line carries
at least three special points (`AuxiliaryAut.two_lt_encard_specialPoints`). Over `ℂ` this says that
in a marked nodal curve with finitely many automorphisms fixing every label, every component
biholomorphic to the Riemann sphere satisfies the stability condition `2 g_i - 2 + n_i > 0`.
Applying this to every genus-zero component requires identifying such a component with the
Riemann sphere, which is not done here.

Likewise a component without special points that is diffeomorphic to an infinite additive group
acting on itself by `C^n` translations, such as a complex torus `E / L` of positive dimension
(`Submodule.instInfiniteOrbitRelQuotient`), has infinitely many diffeomorphisms, namely the
translations, so the marked curve has infinitely many automorphisms fixing every label
(`AuxiliaryAut.infinite_ordered_of_specialPoints_eq_empty`). Contrapositively, when the ordered
automorphism group is finite, every component diffeomorphic to such a group carries a special point
(`AuxiliaryAut.nonempty_specialPoints`). Over `ℂ` this is the stability condition
`2 g_i - 2 + n_i > 0` for a component biholomorphic to a complex torus `ℂ / Λ`, of genus one.

## Main results

* `NodalGluing.AuxiliaryAut.infinite_ordered_of_encard_specialPoints_le_two`: a component
  diffeomorphic to the projective line with at most two special points gives infinitely many
  ordered automorphisms.
* `NodalGluing.AuxiliaryAut.two_lt_encard_specialPoints`: if the ordered automorphism group is
  finite, every component diffeomorphic to the projective line has at least three special points.
* `NodalGluing.AuxiliaryAut.infinite_ordered_of_specialPoints_eq_empty`: a component without
  special points diffeomorphic to an infinite group with `C^n` translations, such as a complex
  torus, gives infinitely many ordered automorphisms.
* `NodalGluing.AuxiliaryAut.nonempty_specialPoints`: if the ordered automorphism group is finite,
  every such component carries a special point.

## References

* Joel W. Robbin and Dietmar A. Salamon, *A construction of the Deligne–Mumford orbifold*,
  J. Eur. Math. Soc. 8 (2006), 611–699, §3, for stable marked nodal curves and the finiteness of
  their automorphism groups.
* Enrico Arbarello, Maurizio Cornalba, Phillip A. Griffiths, *Geometry of Algebraic Curves,
  Volume II*, Chapter X, §3, for stability of pointed nodal curves.
-/

public section

open Set
open scoped Manifold ContDiff

namespace TauCeti

namespace NodalGluing

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H} {n : ℕ∞ω}
  {ι Flag : Type*} {X : ι → Type*} [∀ i, TopologicalSpace (X i)] [∀ i, ChartedSpace H (X i)]
  {d : FlagPairData ι Flag X} {N R : Type*} {m : Marking d (N ⊕ R)}

namespace AuxiliaryAut

/-- **An unstable rational component.** If the component `i` is diffeomorphic to the projective
line `OnePoint 𝕜` and carries at most two special points, the marked curve has infinitely many
automorphisms fixing every label: Möbius transformations fixing those points act on the
component. -/
theorem infinite_ordered_of_encard_specialPoints_le_two [ProperSpace 𝕜] (i : ι)
    (e : X i ≃ₘ^n⟮I, 𝓘(𝕜)⟯ OnePoint 𝕜) (h : (m.specialPoints i).encard ≤ 2) :
    Infinite (ordered I n m) :=
  have := e.infinite_fixingSubgroup_of_encard_le_two h
  infinite_ordered_of_infinite_fixingSubgroup i

/-- **Projective-line components of a curve with finite automorphism group are stable.** If
the marked curve has finitely many automorphisms fixing every label, every component diffeomorphic
to the projective line carries at least three special points. -/
theorem two_lt_encard_specialPoints [ProperSpace 𝕜] [Finite (ordered I n m)] (i : ι)
    (e : X i ≃ₘ^n⟮I, 𝓘(𝕜)⟯ OnePoint 𝕜) : 2 < (m.specialPoints i).encard :=
  lt_of_not_ge fun h ↦ not_finite_iff_infinite.mpr
    (infinite_ordered_of_encard_specialPoints_le_two i e h) ‹_›

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {H' : Type*} [TopologicalSpace H']
  {I' : ModelWithCorners 𝕜 E' H'} {G : Type*} [AddGroup G] [TopologicalSpace G] [ChartedSpace H' G]
  [ContMDiffConstVAdd I' n G G] [Infinite G]

/-- **An unstable elliptic component.** If the component `i` carries no special points and is
diffeomorphic to an infinite additive group `G` whose translations are `C^n`, such as a complex
torus `E / L` of positive dimension, the marked curve has infinitely many automorphisms fixing
every label: the translations of `G` act on the component. -/
theorem infinite_ordered_of_specialPoints_eq_empty (i : ι) (e : X i ≃ₘ^n⟮I, I'⟯ G)
    (h : m.specialPoints i = ∅) : Infinite (ordered I n m) := by
  have : Infinite (Diffeomorph.fixingSubgroup (I := I) (n := n) (m.specialPoints i)) :=
    h ▸ e.infinite_fixingSubgroup_empty
  exact infinite_ordered_of_infinite_fixingSubgroup i

/-- **Elliptic components of a curve with finite automorphism group are stable.** If the marked
curve has finitely many automorphisms fixing every label, every component diffeomorphic to an
infinite additive group with `C^n` translations, such as a complex torus `E / L` of positive
dimension, carries a special point. -/
theorem nonempty_specialPoints [Finite (ordered I n m)] (i : ι) (e : X i ≃ₘ^n⟮I, I'⟯ G) :
    (m.specialPoints i).Nonempty :=
  nonempty_iff_ne_empty.mpr fun h ↦ not_finite_iff_infinite.mpr
    (infinite_ordered_of_specialPoints_eq_empty i e h) ‹_›

end AuxiliaryAut

end NodalGluing

end TauCeti
