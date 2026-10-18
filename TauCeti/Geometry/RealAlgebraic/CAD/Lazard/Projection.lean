/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.RealAlgebraic.CAD.Lazard.Basic
public import TauCeti.Geometry.RealAlgebraic.Projection.Lazard.Lifting

/-!
# Lifting a CAD adapted to the Lazard projection

A CAD of the base into analytic submanifolds lifts to a sign-invariant CAD for a finite
polynomial family when the family's Lazard projection is valuation-invariant on every base
cell. The lifted cells remain analytic submanifolds, and their projections are exactly the
original base cells. No well-orientedness, nonnullification or preservation of fiber degrees
is required.

The distinguished variable in a CAD is coordinate zero, whereas Lazard evaluation places it
last. The valuation conclusion therefore first renames each input by the inverse rotation and
evaluates at `Fin.snoc (Fin.tail x) (x 0)`. The sign conclusion concerns the original input at
`x`. Lazard valuation is not asserted to be invariant under coordinate permutations.

This is a one-level projection-and-lifting theorem: its input is a CAD on which the base
projection already has constant Lazard valuation in its specified coordinate order.

## References

* S. McCallum, A. Parusiński, L. Paunescu, *Validity proof of Lazard's method for CAD
  construction*, Journal of Symbolic Computation 92 (2019), 52–69, Section 5.3.
-/

public section

open MvPolynomial Set

namespace TauCeti

variable {n : ℕ} [NormalizedGCDMonoid (MvPolynomial (Fin n) ℝ)]
  {F : Finset (MvPolynomial (Fin (n + 1)) ℝ)}
  {B : Finset (Polynomial (MvPolynomial (Fin n) ℝ))}

/-- **CAD lifting from the Lazard projection.** An analytic CAD of the base on whose cells the
Lazard projection of an irreducible basis is valuation-invariant lifts to an analytic,
sign-invariant CAD for the original family, with precisely the given base CAD as projection.
The lifted cells also have constant Lazard valuation when the distinguished coordinate is read
last. Ordinary fibers may be nullified, including over positive-dimensional base cells. -/
theorem IsCAD.exists_isCAD_lazardValuation_eq_of_lazardProjection
    {𝓓 : Set (Set (Fin n → ℝ))} (h𝓓 : IsCAD n 𝓓)
    (hB : (F.map (finSuccEquiv ℝ n).toEquiv.toEmbedding).IsIrreducibleBasis B)
    (hanalytic : ∀ C ∈ 𝓓, ∃ d, IsAnalyticSubmanifold d C)
    (hproj : ∀ q ∈ (F.map (finSuccEquiv ℝ n).toEquiv.toEmbedding).lazardProjection B,
      ∀ C ∈ 𝓓, ∀ x ∈ C, ∀ y ∈ C, q.lazardValuation x = q.lazardValuation y) :
    ∃ 𝓒, IsCAD (n + 1) 𝓒 ∧ image Fin.tail '' 𝓒 = 𝓓 ∧
      (∀ E ∈ 𝓒, ∃ d, IsAnalyticSubmanifold d E) ∧
      (∀ f ∈ F, ∀ E ∈ 𝓒, ∀ x ∈ E, ∀ y ∈ E,
        f.lazardValuationReindex (finRotate (n + 1)).symm x =
          f.lazardValuationReindex (finRotate (n + 1)).symm y) ∧
      ∀ f ∈ F, ∀ E ∈ 𝓒, SignInvariant (fun x ↦ eval x f) E := by
  classical
  let A := F.map (finSuccEquiv ℝ n).toEquiv.toEmbedding
  let G : A → MvPolynomial (Fin (n + 1)) ℝ := fun b ↦
    rename finSuccEquivLast.symm ((optionEquivLeft ℝ (Fin n)).symm b.1)
  -- The family lifting theorem reads the distinguished variable last. Rotation recovers
  -- the original polynomial in the ambient coordinate-zero convention.
  have hG (b : A) : rename (finRotate (n + 1)) (G b) = (finSuccEquiv ℝ n).symm b.1 := by
    apply (finSuccEquiv ℝ n).injective
    rw [finSuccEquiv_rename_finRotate]
    simp only [G, rename_rename, Equiv.self_comp_symm, rename_id_apply,
      AlgEquiv.apply_symm_apply]
  have hD (C : Set (Fin n → ℝ)) (hC : C ∈ 𝓓) : Nonempty (LazardDelineation G C) := by
    obtain ⟨d, hd⟩ := hanalytic C hC
    exact nonempty_lazardDelineation_of_lazardProjection hB hd
      (h𝓓.isConnected hC).isPreconnected (fun q hq ↦ hproj q hq C hC)
  obtain ⟨𝓒, h𝓒, htail, ha, hv, hs⟩ :=
    h𝓓.exists_isCAD_lazardValuation_eq_of_lazardDelineation hanalytic hD
  have hmem (f : F) : finSuccEquiv ℝ n f.1 ∈ A := Finset.mem_map.2 ⟨f, f.2, rfl⟩
  refine ⟨𝓒, h𝓒, htail, ha, fun f hf ↦ ?_, fun f hf E hE ↦ ?_⟩
  · simpa only [hG, AlgEquiv.symm_apply_apply] using
      hv ⟨finSuccEquiv ℝ n f, hmem ⟨f, hf⟩⟩
  · simpa only [hG, AlgEquiv.symm_apply_apply] using
      hs ⟨finSuccEquiv ℝ n f, hmem ⟨f, hf⟩⟩ E hE

end TauCeti
