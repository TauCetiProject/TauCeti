/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Formation.Lifting
public import TauCeti.NumberTheory.ClassFieldTheory.Global.LiftIndependence
public import TauCeti.NumberTheory.ClassFieldTheory.Global.PrescribedInvariant

/-!
# Lifting idele-class cohomology to the ideles after a refinement

Let `K` be a number field and `L/F` a finite Galois layer inside `Kˢ`, of degree `n`. A class of
`H²(Gal(L/F), C_L)` lifts to `H²(Gal(L/F), I_L)` only when its obstruction in `H³(Gal(L/F), Lˣ)`
vanishes (`range_ideleToClassH2`), and this fails for the biquadratic field `ℚ(√13, √17)`. This file
shows that the obstruction is killed by inflation to a suitable refinement `L'/F` of the layer,
one refinement serving every class, granted the following global inputs:

* the local invariants of every class of `Br K` sum to zero;
* an idele-layer class whose local invariants sum to zero dies in idele-class cohomology;
* `H¹` of every layer of the idele classes vanishes;
* `#H²(Gal(L/F), C_L)` divides `n`, the second fundamental inequality in cohomological form.

The refinement is the one carrying an idele-layer class whose local invariants sum to `1/n`
(`exists_refinement_ideleSumLocalInv_eq`), the sum of the local invariants multiplies by the
relative degree under restriction (`ideleSumLocalInv_res`), and the first input makes it vanish on
the kernel of `H²(Gal(L/F), I_L) → H²(Gal(L/F), C_L)`, which consists of the images of
`H²(Gal(L/F), Lˣ)` (`ker_ideleToClassH2`, `ideleSumLocalInv_multiplicativeToIdeleH2`). The
formation-level argument is `NormalLayer.exists_refinement_forall_exists_map_eq_cohomologyInfl`.

## Main statements

* `TauCeti.ClassFieldTheory.exists_refinement_mem_range_ideleToClassH2_of_natCard_H2_dvd`: after
  inflation to one refinement of the layer, every class of `H²(Gal(L/F), C_L)` lifts to the
  ideles.

## References

* J. S. Milne, *Class Field Theory*, v4.03, Chapter VIII, §4 (proof of Theorem 4.7).
* J. Tate, *Global class field theory*, in J. W. S. Cassels and A. Fröhlich (eds.),
  *Algebraic Number Theory*, Chapter VII, §11.
-/

public section

namespace TauCeti.ClassFieldTheory

variable {K : Type} [Field K] [NumberField K]

/-- **Every idele-class class lifts to the ideles after inflation to one refinement**, granted the
global inputs of the invariant of idele classes. Let `L/F` be a layer of degree `n`. Suppose that
the local invariants of every global Brauer class sum to zero, that an idele-layer class whose local
invariants sum to zero dies in idele-class cohomology, that `H¹` of every layer of the idele classes
vanishes, and that `#H²(Gal(L/F), C_L)` divides `n`. Then some refinement `L'/F` of the layer has
the property that the inflation of every class of `H²(Gal(L/F), C_L)` to `H²(Gal(L'/F), C_{L'})`
comes from `H²(Gal(L'/F), I_{L'})`. -/
theorem exists_refinement_mem_range_ideleToClassH2_of_natCard_H2_dvd
    (L : NormalLayer (AbsoluteGaloisGroup K))
    (hsum : ∀ x : Br K, sumLocalInv K (brLocalization K x) = 0)
    (hσ₀ : ∀ (M : NormalLayer (AbsoluteGaloisGroup K)) (y : M.H (ideleFormation K) 2),
      ideleSumLocalInv K M y = 0 → ideleToClassH2 K M y = 0)
    (h1 : ∀ M : NormalLayer (AbsoluteGaloisGroup K), Subsingleton (M.H (globalFormation K) 1))
    (h2 : Nat.card (L.H (globalFormation K) 2) ∣ L.degree) :
    ∃ (L' : NormalLayer (AbsoluteGaloisGroup K)) (T : LayerRefinement L L'),
      ∀ x : L.H (globalFormation K) 2,
        T.cohomologyInfl (globalFormation K) 2 x ∈ (ideleToClassH2 K L').range := by
  -- The sum of the local invariants vanishes on the classes killed by the idele-class map, which
  -- come from the multiplicative group.
  have hker (M : NormalLayer (AbsoluteGaloisGroup K)) (y : M.H (ideleFormation K) 2)
      (hy : groupCohomology.map (MonoidHom.id M.Gal) (M.repMap (ideleClassHom K)) 2 y = 0) :
      ideleSumLocalInv K M y = 0 := by
    rw [← ideleToClassH2_apply, ← AddMonoidHom.mem_ker, ker_ideleToClassH2] at hy
    obtain ⟨z, rfl⟩ := hy
    rw [ideleSumLocalInv_multiplicativeToIdeleH2, hsum]
  obtain ⟨L', T, h⟩ := NormalLayer.exists_refinement_forall_exists_map_eq_cohomologyInfl
    (ideleClassHom K) (ideleSumLocalInv K) (ideleSumLocalInv_res K) hker
    (fun M y hy ↦ (ideleToClassH2_apply K M y).symm.trans (hσ₀ M y hy)) h1 h2
    (exists_refinement_ideleSumLocalInv_eq L)
  refine ⟨L', T, fun x ↦ ?_⟩
  obtain ⟨y, hy⟩ := h x
  exact ⟨y, (ideleToClassH2_apply K L' y).trans hy⟩

end TauCeti.ClassFieldTheory
