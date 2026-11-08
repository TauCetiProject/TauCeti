/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.ValuationSpectrum.Amalgamation
public import TauCeti.AlgebraicGeometry.AdicSpace.ValuationSpectrum.Pi
public import TauCeti.RingTheory.Etale.Torsor.GaloisMap

/-!
# Fibres of the valuation spectrum of a finite étale torsor

Let `B` be a finite étale `G`-torsor over `A` (`TauCeti.Algebra.IsFiniteEtaleTorsor G A B`). The
group `G` acts on `Spv B` by transport of structure, `(g • y)(b) = y(g⁻¹ • b)`, that is
`g • y = comap (g⁻¹ • ·) y`. This file shows that the fibres of `Spv B → Spv A` are exactly the
`G`-orbits
(`TauCeti.ValuationSpectrum.comap_algebraMap_eq_comap_algebraMap_iff_of_isFiniteEtaleTorsor`).
No topology is involved, and the valuations may have arbitrary rank.

Points in one orbit have the same image because `G` fixes `A`. Conversely, let `y` and `y'` be
points of `Spv B` with the same image in `Spv A`. They amalgamate to a point `v` of
`Spv (B ⊗[A] B)` (`TauCeti.ValuationSpectrum.exists_amalgamation`). The Galois isomorphism
`B ⊗[A] B ≅ ∏_{g ∈ G} B`, `b ⊗ b' ↦ (b * g • b')_g`, turns `v` into a point of the valuation
spectrum of a finite product, which is pulled back from a single factor `g`
(`TauCeti.ValuationSpectrum.exists_comap_evalRingHom_eq`). Along that factor `b ⊗ 1 ↦ b` and
`1 ⊗ b' ↦ g • b'`, so `y' = comap (g • ·) y`.

This is the valuation-theoretic content of the description of the adic spectrum of a finite étale
torsor over a Tate ring as a quotient by `G`.

## References

* P. Scholze, *Étale cohomology of diamonds*, proof of Proposition 15.4.
* R. Huber, *A generalization of formal schemes and rigid analytic varieties*, Math. Z. 217
  (1994), proof of Lemma 3.9(i), for the amalgamation of valuations.
-/

public section

open TensorProduct Algebra.TensorProduct

namespace TauCeti.ValuationSpectrum

variable {G A B : Type*} [Group G] [Finite G] [CommRing A] [CommRing B] [Algebra A B]
  [MulSemiringAction G B] [SMulCommClass G A B]

/-- **The fibres of `Spv B → Spv A` for a finite étale torsor are the `G`-orbits.** If `B` is a
finite étale `G`-torsor over `A`, two points `y` and `y'` of `Spv B` have the same image in
`Spv A` exactly when `y' = g • y` for some `g ∈ G`, where `(g • y)(b) = y(g⁻¹ • b)`. -/
theorem comap_algebraMap_eq_comap_algebraMap_iff_of_isFiniteEtaleTorsor
    [Algebra.IsFiniteEtaleTorsor G A B] {y y' : Spv B} :
    comap (algebraMap A B) y = comap (algebraMap A B) y' ↔
      ∃ g : G, y' = comap (MulSemiringAction.toRingHom G B g⁻¹) y := by
  refine ⟨fun h ↦ ?_, fun ⟨g, hg⟩ ↦ by rw [hg, comap_algebraMap_comap_toRingHom]⟩
  obtain ⟨v, hvy, hvy'⟩ := exists_amalgamation y y' h
  -- transport the amalgam to `∏_{g ∈ G} B`, where it lives on a single factor `g`
  let Φ := Algebra.IsFiniteEtaleTorsor.galoisMap G A B
  obtain ⟨g, w, hw⟩ := exists_comap_evalRingHom_eq (R := fun _ : G ↦ B)
    (comap (Φ.symm : (G → B) →+* B ⊗[A] B) v)
  let ψ : B ⊗[A] B →+* B := (Pi.evalRingHom (fun _ : G ↦ B) g).comp Φ
  have hΦ : (Φ.symm : (G → B) →+* B ⊗[A] B).comp Φ = RingHom.id _ :=
    RingHom.ext Φ.symm_apply_apply
  have hv : v = comap ψ w := by
    rw [← comap_comap, hw, comap_comap, hΦ, comap_id, id]
  -- along that factor, `b ⊗ 1 ↦ b` and `1 ⊗ b' ↦ g • b'`
  have hψl : ψ.comp includeLeftRingHom = RingHom.id B :=
    RingHom.ext fun b ↦ by simp [ψ, Φ]
  have hψr : ψ.comp (includeRight (R := A) (A := B)).toRingHom =
      MulSemiringAction.toRingHom G B g :=
    RingHom.ext fun b ↦ by simp [ψ, Φ]
  have hy : y = w := by
    rw [← hvy, hv, comap_comap, hψl, comap_id, id]
  have hy' : y' = comap (MulSemiringAction.toRingHom G B g) w := by
    rw [← hvy', hv, comap_comap, hψr]
  exact ⟨g⁻¹, by rw [inv_inv, hy', hy]⟩

end TauCeti.ValuationSpectrum
