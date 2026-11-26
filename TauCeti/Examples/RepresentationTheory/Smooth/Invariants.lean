/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Smooth.Invariants
public import Mathlib.Topology.Instances.ZMod

/-!
# Examples of invariants of smooth representations

For the trivial representation every subgroup acts trivially, so `V^U = V`.

Taking invariants is not right exact without invertibility of the order of the group. For the
discrete group `G = ℤ/p` and `A = 𝔽_p`, the augmentation `𝔽_p[G] → 𝔽_p`, `[g] ↦ 1`, is an
epimorphism of smooth representations, but its restriction to `G`-invariants is not surjective:
a `G`-invariant of `𝔽_p[G]` has constant coefficients, so its augmentation is `p` times a
coefficient, which is zero.
-/

public section

open CategoryTheory Representation

namespace TauCeti

/-- For the trivial representation, `V^U = V` for every subgroup `U`. -/
example {A G V : Type*} [CommRing A] [Group G] [AddCommGroup V] [Module A V] (U : Subgroup G) :
    invariants ((trivial A G V).comp U.subtype) = ⊤ := by
  ext v
  simp [mem_invariants]

/-- **Invariants are not right exact.** For `G = ℤ/p` (discrete) and `A = 𝔽_p`, the augmentation
`𝔽_p[G] → 𝔽_p` is an epimorphism of smooth representations whose map on `G`-invariants is not
surjective. -/
example (p : ℕ) [Fact p.Prime] :
    let G := Multiplicative (ZMod p)
    let ε : (⟨Rep.leftRegular (ZMod p) G, inferInstance⟩ : SmoothRep (ZMod p) G) ⟶
        ⟨Rep.trivial (ZMod p) G (ZMod p), inferInstance⟩ :=
      ObjectProperty.homMk (Rep.leftRegularHom _ (1 : ZMod p))
    Epi ε ∧
      ¬Function.Surjective ((SmoothRep.invariantsFunctor (ZMod p) (⊤ : Subgroup G)).map ε).hom := by
  intro G ε
  refine ⟨(SmoothRep.epi_iff_surjective ε).2 fun r ↦ ⟨.single 1 r, by simp [ε]⟩, fun h ↦ ?_⟩
  obtain ⟨⟨x, hx⟩, hx1⟩ := h ⟨(1 : ZMod p), fun _ ↦ rfl⟩
  have hconst (g : G) : x.coeff g = x.coeff 1 := by
    simpa [Representation.coeff_ofMulAction, Subgroup.smul_def] using
      (congrArg (·.coeff g) (hx ⟨g, trivial⟩)).symm
  have h1 : ε.hom.hom x = 1 :=
    (SmoothRep.coe_invariantsFunctor_map_hom_apply _ ε ⟨x, hx⟩).symm.trans
      (congrArg Subtype.val hx1)
  have hsum : ε.hom.hom x = ∑ g : G, x.coeff g := by
    simp [ε, Rep.leftRegularHom, Finsupp.sum_fintype]
  simp only [hsum, hconst, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h1
  simp [G, Fintype.card_multiplicative] at h1

end TauCeti
