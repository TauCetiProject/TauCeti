/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.Cup.TrivialFp.Basic
public import TauCeti.RepresentationTheory.Homological.ContCohomology.TrivialFp.Explicit

/-!
# The homogeneous cocycle of a character and its cup products

A continuous character `χ : G → 𝔽_p` of a topological group `G` is a homogeneous one-cocycle
`(g₀, g₁) ↦ χ (g₀⁻¹ g₁)` with trivial `𝔽_p` coefficients (`TauCeti.characterCocycle`), and its
class is the class attached to `χ` by the identification
`TauCeti.cohomFpLinearEquivContinuousZModDual` of `H¹(G, 𝔽_p)` with the continuous `𝔽_p`-dual of
`G` (`TauCeti.cohomFpLinearEquivContinuousZModDual_symm_apply`). This gives every class of
`H¹(G, 𝔽_p)` an explicit representative on Mathlib's homogeneous cochains, on which the cup product
`H¹ × H¹ → H²` of `TauCeti.cupFp` is computed by the Alexander–Whitney formula
`(χ ⌣ ψ) g₀ g₁ g₂ = χ (g₀⁻¹ g₁) ψ (g₁⁻¹ g₂)`.

The one consequence drawn here is a **symmetry test for the vanishing of a cup product**: the
coboundary of an invariant one-cochain `w`, evaluated at `(1, x, xy)`, is
`w 1 y - w 1 (xy) + w 1 x`, which is unchanged by exchanging `x` and `y` when they commute. So if
`a ⌣ b = 0` in `H²(G, 𝔽_p)` for classes `a, b` of `H¹(G, 𝔽_p)` with characters `χ, ψ`, then
`χ(x) ψ(y) = χ(y) ψ(x)` for all commuting `x, y ∈ G` (`TauCeti.mul_eq_mul_of_cupFp_eq_zero`).
Contrapositively, two characters that are not proportional on a pair of commuting elements have a
nonzero cup product; this is how the cup product of an abelian pro-`p` group such as `ℤ_p × ℤ_p` is
shown to be nondegenerate.

## Main definitions

* `TauCeti.characterCochain`, `TauCeti.characterCocycle`: the homogeneous one-cocycle
  `(g₀, g₁) ↦ χ (g₀⁻¹ g₁)` of a continuous character `χ`.

## Main results

* `TauCeti.cohomFpLinearEquivContinuousZModDual_symm_apply`: the class attached to a character is
  the class of its homogeneous cocycle.
* `TauCeti.cohomFpLinearEquivContinuousZModDual_cohomFpMap`: pullback of degree-one classes is
  precomposition of their characters.
* `TauCeti.mul_eq_mul_of_cupFp_eq_zero`: if `a ⌣ b = 0` then the characters `χ, ψ` of `a, b`
  satisfy `χ(x) ψ(y) = χ(y) ψ(x)` for commuting `x` and `y`.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., I §1.4.
* J.-P. Serre, *Galois Cohomology*, Springer (1997), Chapter I, §4.5.
-/

public section

namespace TauCeti

open CategoryTheory _root_.ContinuousCohomology TopRep

universe u

variable (p : ℕ) {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-! ### Homogeneous cochains with trivial coefficients -/

/-- A homogeneous one-cochain with trivial coefficients is determined by its values at `(1, g)`:
`a g₀ g₁ = a 1 (g₀⁻¹ g₁)`. -/
theorem homogeneousCochains_trivialFp_one_apply_eq (a : (homogeneousCochains (trivialFp p G)).X 1)
    (g₀ g₁ : G) : a.val g₀ g₁ = a.val 1 (g₀⁻¹ * g₁) := by
  have h := congrArg (fun F : C(G, C(G, (trivialFp p G).V)) ↦ F g₀ g₁) (a.property g₀)
  simpa only [ContRepresentation.coind₁_apply_apply, trivialFp_ρ_apply_apply, inv_mul_cancel]
    using h.symm

/-! ### The cocycle of a character -/

/-- The homogeneous one-cochain `(g₀, g₁) ↦ χ (g₀⁻¹ g₁)` of a continuous character `χ : G → 𝔽_p`,
with trivial `𝔽_p` coefficients. -/
noncomputable def characterCochain (χ : continuousZModDual p G) :
    (homogeneousCochains (trivialFp p G)).X 1 :=
  ⟨ContinuousMap.curry ⟨fun q : G × G ↦
      (trivialFpEquiv p G).symm (Multiplicative.toAdd (Additive.toMul χ (q.1⁻¹ * q.2))),
      continuous_of_discreteTopology.comp (continuous_toAdd.comp
        ((Additive.toMul χ).continuous.comp (continuous_fst.inv.mul continuous_snd)))⟩,
    fun g ↦ by
      ext h k
      simp only [ContRepresentation.coind₁_apply_apply, trivialFp_ρ_apply_apply,
        ContinuousMap.curry_apply, ContinuousMap.coe_mk]
      rw [mul_inv_rev, inv_inv, mul_assoc, mul_inv_cancel_left]⟩

/-- The value of the cochain of `χ` at `(g₀, g₁)` is `χ (g₀⁻¹ g₁)`, lifted to the coefficients. -/
-- Not a `simp` lemma: the carrier of the homogeneous cochains is the iterated function space
-- `C(G, C(G, X.V))` only after unfolding the coinduction, which `simp` does not do when matching
-- the left-hand side; use it with `rw`.
theorem characterCochain_apply (χ : continuousZModDual p G) (g₀ g₁ : G) :
    (characterCochain p χ).val g₀ g₁ =
      (trivialFpEquiv p G).symm (Multiplicative.toAdd (Additive.toMul χ (g₀⁻¹ * g₁))) :=
  (rfl)

/-- The cochain of a character is a cocycle. -/
theorem d_characterCochain (χ : continuousZModDual p G) :
    ((homogeneousCochains (trivialFp p G)).d 1 (1 + 1)).hom (characterCochain p χ) = 0 := by
  apply Subtype.ext
  ext g₀ g₁ g₂
  rw [homogeneousCochains.d_one_apply, characterCochain_apply, characterCochain_apply,
    characterCochain_apply, ← map_sub, ← map_sub, Submodule.coe_zero, ContinuousMap.zero_apply,
    ContinuousMap.zero_apply, ContinuousMap.zero_apply, ← map_zero (trivialFpEquiv p G).symm]
  congr 1
  have h : Additive.toMul χ (g₀⁻¹ * g₂) =
      Additive.toMul χ (g₀⁻¹ * g₁) * Additive.toMul χ (g₁⁻¹ * g₂) := by
    rw [← map_mul, mul_assoc, mul_inv_cancel_left]
  rw [h, toAdd_mul]
  abel

/-- The homogeneous one-cocycle `(g₀, g₁) ↦ χ (g₀⁻¹ g₁)` of a continuous character `χ : G → 𝔽_p`. -/
noncomputable def characterCocycle (χ : continuousZModDual p G) : cocycles (trivialFp p G) 1 :=
  (homogeneousCochains (trivialFp p G)).cyclesMkOfEq (characterCochain p χ) (1 + 1)
    (CochainComplex.next ℕ 1) (d_characterCochain p χ)

/-- The underlying cochain of the cocycle of `χ` is `characterCochain p χ`. -/
-- Not a `simp` lemma: `simp` rewrites the ambient object
-- `(homogeneousCochains (trivialFp p G)).X 1` on the left-hand side through
-- `CategoryTheory.Functor.mapHomologicalComplex_obj_X`, so the statement is not in `simp`-normal
-- form; use it with `rw` or `simp only`.
theorem iCycles_characterCocycle (χ : continuousZModDual p G) :
    (homogeneousCochains (trivialFp p G)).iCycles 1 (characterCocycle p χ) =
      characterCochain p χ :=
  HomologicalComplex.iCycles_cyclesMkOfEq _ _ _ _ _

/-! ### The class of a character -/

/-- The character attached to the class of the homogeneous cocycle of `χ` is `χ`. -/
@[simp]
theorem cohomFpLinearEquivContinuousZModDual_π_characterCocycle (χ : continuousZModDual p G) :
    cohomFpLinearEquivContinuousZModDual p G (π (trivialFp p G) 1 (characterCocycle p χ)) = χ := by
  apply Additive.toMul.injective
  ext g
  apply Multiplicative.toAdd.injective
  rw [cohomFpLinearEquivContinuousZModDual_π_apply, iCycles_characterCocycle,
    characterCochain_apply, inv_one, one_mul, LinearEquiv.apply_symm_apply]

/-- **The class of a character** is the class of its homogeneous cocycle `(g₀, g₁) ↦ χ (g₀⁻¹ g₁)`:
the inverse of `TauCeti.cohomFpLinearEquivContinuousZModDual`, computed on Mathlib's homogeneous
cochains, which is the form a cup-product computation consumes. -/
-- Not a `simp` lemma: the inverse identification is the intended normal form of the class of a
-- character, and this lemma unfolds it to a representative.
theorem cohomFpLinearEquivContinuousZModDual_symm_apply (χ : continuousZModDual p G) :
    (cohomFpLinearEquivContinuousZModDual p G).symm χ =
      π (trivialFp p G) 1 (characterCocycle p χ) :=
  (cohomFpLinearEquivContinuousZModDual p G).symm_apply_eq.2
    (cohomFpLinearEquivContinuousZModDual_π_characterCocycle p χ).symm

variable {H : Type u} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

/-- The identification of degree-one cohomology with continuous characters is natural in the
group: pullback of cohomology classes corresponds to precomposition of characters. -/
theorem cohomFpLinearEquivContinuousZModDual_cohomFpMap (f : H →ₜ* G)
    (x : cohomFp p G 1) :
    cohomFpLinearEquivContinuousZModDual p H (cohomFpMap p f 1 x) =
      f.continuousZModDualMap (cohomFpLinearEquivContinuousZModDual p G x) := by
  let χ := cohomFpLinearEquivContinuousZModDual p G x
  apply (cohomFpLinearEquivContinuousZModDual p H).symm.injective
  rw [LinearEquiv.symm_apply_apply]
  calc
    cohomFpMap p f 1 x =
        cohomFpMap p f 1 ((cohomFpLinearEquivContinuousZModDual p G).symm χ) := by
      simp only [χ, LinearEquiv.symm_apply_apply]
    _ = cohomFpMap p f 1 (π (trivialFp p G) 1 (characterCocycle p χ)) := by
      rw [cohomFpLinearEquivContinuousZModDual_symm_apply]
    _ = π (trivialFp p H) 1
        (_root_.ContinuousCohomology.cocyclesMap f
          (eqToHom (res_trivialFp_hom p f)) 1 (characterCocycle p χ)) := by
      rw [cohomFpMap_def, ContinuousCohomology.map_π_apply]
    _ = π (trivialFp p H) 1 (characterCocycle p (f.continuousZModDualMap χ)) := by
      congr 1
      apply (TopRep.homogeneousCochains (trivialFp p H)).iCycles_injective 1
      let f' : (trivialFp p G).V →+ (trivialFp p H).V :=
        ((trivialFpEquiv p H).symm.toLinearMap ∘ₗ
          (trivialFpEquiv p G).toLinearMap).toAddMonoidHom
      have hf (m : (trivialFp p G).V) :
          (eqToHom (res_trivialFp_hom p f)).hom m = f' m :=
        (trivialFpEquiv p H).injective <| by
          simpa [f'] using trivialFpEquiv_eqToHom_res_trivialFp_hom p f m
      have hf'_symm_apply (z : ZMod p) :
          f' ((trivialFpEquiv p G).symm z) = (trivialFpEquiv p H).symm z := by
        apply (trivialFpEquiv p H).injective
        simp [f']
      apply Subtype.ext
      ext h₀ h₁
      refine (ContinuousCohomology.iCycles_cocyclesMap_one_apply f
        (eqToHom (res_trivialFp_hom p f)) (characterCocycle p χ) f' hf h₀ h₁).trans ?_
      rw [iCycles_characterCocycle, iCycles_characterCocycle,
        characterCochain_apply, characterCochain_apply, hf'_symm_apply]
      apply (trivialFpEquiv p H).injective
      rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
      rw [ContinuousMonoidHom.toMul_continuousZModDualMap_apply]
      rw [map_mul f, map_inv f]
    _ = (cohomFpLinearEquivContinuousZModDual p H).symm
        (f.continuousZModDualMap χ) :=
      (cohomFpLinearEquivContinuousZModDual_symm_apply p _).symm

/-! ### The symmetry test for the cup product -/

/-- **A vanishing cup product forces a symmetry on commuting elements.** Let `χ` and `ψ` be the
characters of the classes `a` and `b` of `H¹(G, 𝔽_p)`. If `a ⌣ b = 0` in `H²(G, 𝔽_p)`, then
`χ(x) ψ(y) = χ(y) ψ(x)` for every pair of commuting elements `x, y` of `G`. Indeed the cup product
is then the coboundary of an invariant one-cochain `w`, whose value at `(1, x, xy)` is
`w 1 y - w 1 (xy) + w 1 x`, which is symmetric in `x` and `y` when `xy = yx`. -/
theorem mul_eq_mul_of_cupFp_eq_zero {a b : cohomFp p G 1} (h : cupFp p G a b = 0) {x y : G}
    (hxy : Commute x y) :
    Multiplicative.toAdd (Additive.toMul (cohomFpLinearEquivContinuousZModDual p G a) x) *
        Multiplicative.toAdd (Additive.toMul (cohomFpLinearEquivContinuousZModDual p G b) y) =
      Multiplicative.toAdd (Additive.toMul (cohomFpLinearEquivContinuousZModDual p G a) y) *
        Multiplicative.toAdd (Additive.toMul (cohomFpLinearEquivContinuousZModDual p G b) x) := by
  -- `a` and `b` are the classes of the homogeneous cocycles of their characters.
  rw [← (cohomFpLinearEquivContinuousZModDual p G).symm_apply_apply a,
    ← (cohomFpLinearEquivContinuousZModDual p G).symm_apply_apply b,
    cohomFpLinearEquivContinuousZModDual_symm_apply,
    cohomFpLinearEquivContinuousZModDual_symm_apply, cupFp_π] at h
  obtain ⟨w, hw⟩ := ((homogeneousCochains (trivialFp p G)).homologyπ_eq_zero_iff 2 (m := 1)
    (CochainComplex.prev_nat_succ 1)).1 h
  -- The coboundary of `w` is the cup product of the two cocycles, as homogeneous two-cochains.
  have hw' := congrArg ((homogeneousCochains (trivialFp p G)).iCycles (1 + 1)) hw
  rw [HomologicalComplex.iCycles_toCycles_apply, TopPairing.iCycles_cupCocycles,
    iCycles_characterCocycle, iCycles_characterCocycle] at hw'
  -- Evaluate at `(1, x, x * y)` and at `(1, y, y * x)`.
  have h₁ := ContinuousMap.congr_fun (ContinuousMap.congr_fun (ContinuousMap.congr_fun
    (congrArg Subtype.val hw') 1) x) (x * y)
  have h₂ := ContinuousMap.congr_fun (ContinuousMap.congr_fun (ContinuousMap.congr_fun
    (congrArg Subtype.val hw') 1) y) (y * x)
  -- The evaluation lemmas are stated on the carriers `C(G, C(G, C(G, X.V)))` of the resolution,
  -- which are the carriers of the homogeneous cochains only after unfolding the coinduction; `rw`
  -- unfolds that much, `simp` does not.
  rw [homogeneousCochains.d_one_apply, TopPairing.cupCochain_one_one_apply, characterCochain_apply,
    characterCochain_apply] at h₁ h₂
  simp only [fpPairing_bil_apply, LinearEquiv.apply_symm_apply, inv_one, one_mul,
    inv_mul_cancel_left] at h₁ h₂
  apply (trivialFpEquiv p G).symm.injective
  rw [← h₁, ← h₂, homogeneousCochains_trivialFp_one_apply_eq p w x (x * y),
    homogeneousCochains_trivialFp_one_apply_eq p w y (y * x), inv_mul_cancel_left,
    inv_mul_cancel_left, hxy.eq]
  abel

end TauCeti
