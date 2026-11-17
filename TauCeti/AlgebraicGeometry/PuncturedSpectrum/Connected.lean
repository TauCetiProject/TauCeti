/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.PuncturedSpectrum
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.RingTheory.Depth.Basic
import Mathlib.AlgebraicGeometry.Properties
import TauCeti.AlgebraicGeometry.PuncturedSpectrum.Sections

/-!
# Connectedness of the punctured spectrum

If `R` is a Noetherian local ring of depth at least two, then its punctured spectrum
`U = Spec R ∖ {𝔪}` is connected (`TauCeti.IsLocalRing.connectedSpace_puncturedSpectrum`). It is
nonempty since `R` has positive Krull dimension
(`TauCeti.IsLocalRing.nonempty_puncturedSpectrum_iff`).

Connectedness comes from the algebraic Hartogs principle: in depth at least two, restriction
`R = Γ(Spec R, 𝒪) → Γ(U, 𝒪)` is bijective. A decomposition of `U` into two disjoint nonempty open
subsets `V` and `W` would make `Γ(U, 𝒪) ≅ Γ(V, 𝒪) × Γ(W, 𝒪)` a product of two nonzero rings, which
is not local.

Depth one does not suffice: two planes in affine four-space meeting in a single point have a
local ring of depth one at that point, and its punctured spectrum is the disjoint union of the two
punctured planes.

Connectedness of `U` is what makes finite étale covers of `U` behave like those of a connected
scheme, for instance when restricting them to the punctured spectrum of a hypersurface section,
as in Stacks, Lemma 58.19.7 (0BLJ).

## Main results

* `TauCeti.IsLocalRing.connectedSpace_puncturedSpectrum`: the punctured spectrum of a Noetherian
  local ring of depth at least two is connected.

## References

* [Stacks Project, Lemma 31.5.11](https://stacks.math.columbia.edu/tag/0E9I), extension of
  sections across a closed subset of depth at least two.
* R. Hartshorne, *Complete intersections and connectedness*, Amer. J. Math. 84 (1962),
  Proposition 2.1.
-/

public section

open CategoryTheory Limits Opposite AlgebraicGeometry

universe u

namespace TauCeti.IsLocalRing

variable (R : Type u) [CommRing R] [IsLocalRing R]

/-- **The punctured spectrum is connected in depth at least two.** For a Noetherian local ring
`R` of depth at least two, the complement of the closed point of `Spec R` is connected. -/
theorem connectedSpace_puncturedSpectrum [IsNoetherianRing R]
    (hdepth : 2 ≤ _root_.IsLocalRing.depth (ModuleCat.of R R)) :
    ConnectedSpace (puncturedSpectrum R).toScheme := by
  let U := puncturedSpectrum R
  let X := U.toScheme
  have : Nonempty X := (nonempty_puncturedSpectrum_iff R).mpr
    (dense_compl_singleton_closedPoint_iff.mp
      (dense_compl_singleton_closedPoint_of_one_le_depth (one_le_two.trans hdepth)))
  -- By the Hartogs principle, `R → Γ(U, 𝒪)` is a ring isomorphism.
  have hbij := TauCeti.AlgebraicGeometry.Spec.presheaf_map_leTop_bijective_of_flat (B := R) hdepth
    U fun p hp ↦ (mem_puncturedSpectrum_iff R p).mpr fun h ↦ hp (by
      simp [h, Ideal.under_def, Ideal.comap_id, _root_.IsLocalRing.closedPoint])
  let eR : R ≃+* Γ(X, ⊤) :=
    ((Scheme.ΓSpecIso (.of R)).symm.commRingCatIsoToRingEquiv.trans
      (RingEquiv.ofBijective _ hbij)).trans U.topIso.symm.commRingCatIsoToRingEquiv
  refine connectedSpace_iff_clopen.mpr ⟨inferInstance, fun s hs ↦ ?_⟩
  by_contra! hne
  let V : X.Opens := ⟨s, hs.isOpen⟩
  let W : X.Opens := ⟨sᶜ, hs.isClosed.isOpen_compl⟩
  have : Nonempty V := hne.1.to_subtype
  have : Nonempty W := (Set.nonempty_compl.mpr hne.2).to_subtype
  have hVW : V ⊓ W = ⊥ := by ext; simp [V, W]
  have hsup : V ⊔ W = ⊤ := by ext; simp [V, W]
  -- `Γ(U, 𝒪)` is the product of the nonzero rings `Γ(V, 𝒪)` and `Γ(W, 𝒪)`.
  let e : Γ(X, ⊤) ≃+* Γ(X, V) × Γ(X, W) :=
    (X.presheaf.mapIso (eqToIso hsup).op ≪≫
      (X.sheaf.isProductOfDisjoint V W hVW).conePointUniqueUpToIso
        (CommRingCat.prodFanIsLimit _ _)).commRingCatIsoToRingEquiv
  let φ := eR.trans e
  have hadd : φ.symm (1, 0) + φ.symm (0, 1) = 1 := by
    rw [← map_add, Prod.mk_add_mk, add_zero, zero_add, ← Prod.one_eq_mk, map_one]
  rcases _root_.IsLocalRing.isUnit_or_isUnit_of_add_one hadd with h | h
  · have := (Prod.isUnit_iff.mp (by simpa using h.map φ)).2
    exact not_isUnit_zero this
  · have := (Prod.isUnit_iff.mp (by simpa using h.map φ)).1
    exact not_isUnit_zero this

end TauCeti.IsLocalRing
