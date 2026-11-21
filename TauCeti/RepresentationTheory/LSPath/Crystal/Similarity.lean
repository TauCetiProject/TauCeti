/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.LSPath.Similarity

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# Dilation similarity on normal crystals of piecewise-linear paths

Fix a root datum `P : RootDatum ι X Y` with a base `b : P.Base`, an injective additive realization
`f : X →+ V` in a vector space over a linearly ordered field `𝕜`, and height forms
`F : b.support → Module.Dual 𝕜 V` agreeing with the simple coroots on `f(X)`.

Building on `TauCeti.PLPath.dilationSimilarityHom` from
`TauCeti.RepresentationTheory.LSPath.Similarity`, this file supplies the specialization to
Littelmann's ambient integral-path crystal `normalCrystal hf hF`
(`TauCeti.PLPath.dilationToNormalCrystalSimilarityHom`), compatibility with `embedHom`,
`inclusionHom`, multiplicative composition, and `reverseIso` on duals.

Conversely, integrality of a dilated path does **not** descend to the original path for any
magnification `1 < n`, even when the original path already has zero endpoint
(`π.endpoint = 0 ∈ f(X)`): for any isolated simple node `i` (in particular on every rank-one root
datum), the excursion `-(1 / (2n)) α_i` followed by `(1 / (2n)) α_i` dilates at `n` to the
integral path `simpleRootBent 𝕜 f i` while itself having non-integral minimum height `-1 / n`
(`TauCeti.PLPath.exists_isIntegralPath_map_natCast_smul_and_not_isIntegralPath_of_isolated`,
`TauCeti.PLPath.exists_isIntegralPath_map_natCast_smul_and_not_isIntegralPath`). Thus
crystal-admissibility of the unstretched source set is genuinely needed in the crystal similarity
construction.

## Main definitions

* `TauCeti.PLPath.dilationToNormalCrystalSimilarityHom`: specialization of
  `TauCeti.PLPath.dilationSimilarityHom` with target `normalCrystal hf hF`.

## Main results

* `TauCeti.PLPath.dilationToNormalCrystalSimilarityHom_injective`: injectivity of dilation into
  `normalCrystal hf hF`.
* `TauCeti.PLPath.dilationSimilarityHom_compStrictHom_inclusionHom`,
  `TauCeti.PLPath.inclusionHom_compSimilarityHom_dilationSimilarityHom`,
  `TauCeti.PLPath.dilationToNormalCrystalSimilarityHom_compStrictHom_inclusionHom`,
  `TauCeti.PLPath.embedHom_compSimilarityHom_dilationSimilarityHom`,
  `TauCeti.PLPath.toStrictHom_dilationSimilarityHom_one`,
  `TauCeti.PLPath.toStrictHom_dilationToNormalCrystalSimilarityHom_one`,
  `TauCeti.PLPath.dilationSimilarityHom_comp`,
  `TauCeti.PLPath.reverseIso_dilationToNormalCrystalSimilarityHom_dual_apply`: compatibility with
  `inclusionHom` and `embedHom`, reduction at `n = 1` to `inclusionHom` and `embedHom`,
  multiplicative composition, and agreement on underlying paths with `reverseIso` on dualized
  dilation.
* `TauCeti.PLPath.exists_isIntegralPath_map_natCast_smul_and_not_isIntegralPath_of_isolated`,
  `TauCeti.PLPath.exists_isIntegralPath_map_natCast_smul_and_not_isIntegralPath`: for every
  `1 < n`, integrality of the `n`-dilation of `π` and `π.endpoint = 0` do not imply integrality of
  `π`.

## References

* P. Littelmann, *Paths and root operators in representation theory*, Ann. of Math. 142 (1995),
  §5.
* M. Kashiwara, *Similarity of crystal bases*, Contemp. Math. 194, Amer. Math. Soc. (1996),
  177–186.
-/

public section

namespace TauCeti.PLPath

open Module Set

variable {ι X Y 𝕜 V : Type*} [AddCommGroup X] [AddCommGroup Y]
  {P : RootDatum ι X Y} {b : P.Base}
  [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [AddCommGroup V] [Module 𝕜 V]
  {f : X →+ V} {F : b.support → Dual 𝕜 V}

/-! ### Dilation similarity morphisms into `normalCrystal` and structural compatibility -/

section DilationHom

/-- Specialization of `dilationSimilarityHom` landing in Littelmann's ambient integral-path
crystal `normalCrystal hf hF`. -/
noncomputable def dilationToNormalCrystalSimilarityHom (hf : Function.Injective f)
    (hF : ∀ (i : b.support) (x : X), F i (f x) = (P.coroot' i x : 𝕜))
    {S : Set (PLPath 𝕜 V)} (hS : IsCrystalSet b f F S) {n : ℕ} (hn : 0 < n)
    (hmap : ∀ ⦃π⦄, π ∈ S → IsIntegralPath b f F (π.map ((n : 𝕜) • LinearMap.id))) :
    NormalCrystal.SimilarityHom n (normalCrystalOn hf hF hS) (normalCrystal hf hF) :=
  dilationSimilarityHom hf hF hS isCrystalSet_setOf_isIntegralPath hn hmap

@[simp]
theorem dilationToNormalCrystalSimilarityHom_apply (hf : Function.Injective f)
    (hF : ∀ (i : b.support) (x : X), F i (f x) = (P.coroot' i x : 𝕜))
    {S : Set (PLPath 𝕜 V)} (hS : IsCrystalSet b f F S) {n : ℕ} (hn : 0 < n)
    (hmap : ∀ ⦃π⦄, π ∈ S → IsIntegralPath b f F (π.map ((n : 𝕜) • LinearMap.id))) (x : S) :
    (dilationToNormalCrystalSimilarityHom hf hF hS hn hmap x).val =
      x.val.map ((n : 𝕜) • LinearMap.id) :=
  dilationSimilarityHom_apply hf hF hS isCrystalSet_setOf_isIntegralPath hn hmap x

/-- Every positive-integer dilation similarity morphism into `normalCrystal hf hF` is injective. -/
theorem dilationToNormalCrystalSimilarityHom_injective (hf : Function.Injective f)
    (hF : ∀ (i : b.support) (x : X), F i (f x) = (P.coroot' i x : 𝕜))
    {S : Set (PLPath 𝕜 V)} (hS : IsCrystalSet b f F S) {n : ℕ} (hn : 0 < n)
    (hmap : ∀ ⦃π⦄, π ∈ S → IsIntegralPath b f F (π.map ((n : 𝕜) • LinearMap.id))) :
    Function.Injective (dilationToNormalCrystalSimilarityHom hf hF hS hn hmap) :=
  dilationSimilarityHom_injective hf hF hS isCrystalSet_setOf_isIntegralPath hn hmap

/-- Precomposing `dilationSimilarityHom` with `inclusionHom` restricts the source set. -/
theorem dilationSimilarityHom_compStrictHom_inclusionHom (hf : Function.Injective f)
    (hF : ∀ (i : b.support) (x : X), F i (f x) = (P.coroot' i x : 𝕜))
    {S T U : Set (PLPath 𝕜 V)} (hS : IsCrystalSet b f F S) (hT : IsCrystalSet b f F T)
    (hU : IsCrystalSet b f F U) (hST : S ⊆ T) {n : ℕ} (hn : 0 < n)
    (hTU : ∀ ⦃π⦄, π ∈ T → π.map ((n : 𝕜) • LinearMap.id) ∈ U) :
    (dilationSimilarityHom hf hF hT hU hn hTU).compStrictHom
        (inclusionHom (hf := hf) (hF := hF) hS hT hST) =
      dilationSimilarityHom hf hF hS hU hn (fun _ hπ ↦ hTU (hST hπ)) :=
  NormalCrystal.SimilarityHom.ext fun _ ↦ Subtype.ext (by simp)

/-- Postcomposing `dilationSimilarityHom` with `inclusionHom` enlarges the target set. -/
theorem inclusionHom_compSimilarityHom_dilationSimilarityHom (hf : Function.Injective f)
    (hF : ∀ (i : b.support) (x : X), F i (f x) = (P.coroot' i x : 𝕜))
    {S T U : Set (PLPath 𝕜 V)} (hS : IsCrystalSet b f F S) (hT : IsCrystalSet b f F T)
    (hU : IsCrystalSet b f F U) (hTU : T ⊆ U) {n : ℕ} (hn : 0 < n)
    (hST : ∀ ⦃π⦄, π ∈ S → π.map ((n : 𝕜) • LinearMap.id) ∈ T) :
    (inclusionHom (hf := hf) (hF := hF) hT hU hTU).compSimilarityHom
        (dilationSimilarityHom hf hF hS hT hn hST) =
      dilationSimilarityHom hf hF hS hU hn (fun _ hπ ↦ hTU (hST hπ)) :=
  NormalCrystal.SimilarityHom.ext fun _ ↦ Subtype.ext (by simp)

/-- Precomposing `dilationToNormalCrystalSimilarityHom` with `inclusionHom` restricts the source
set. -/
theorem dilationToNormalCrystalSimilarityHom_compStrictHom_inclusionHom (hf : Function.Injective f)
    (hF : ∀ (i : b.support) (x : X), F i (f x) = (P.coroot' i x : 𝕜))
    {S T : Set (PLPath 𝕜 V)} (hS : IsCrystalSet b f F S) (hT : IsCrystalSet b f F T)
    (hST : S ⊆ T) {n : ℕ} (hn : 0 < n)
    (hmap : ∀ ⦃π⦄, π ∈ T → IsIntegralPath b f F (π.map ((n : 𝕜) • LinearMap.id))) :
    (dilationToNormalCrystalSimilarityHom hf hF hT hn hmap).compStrictHom
        (inclusionHom (hf := hf) (hF := hF) hS hT hST) =
      dilationToNormalCrystalSimilarityHom hf hF hS hn (fun _ hπ ↦ hmap (hST hπ)) :=
  dilationSimilarityHom_compStrictHom_inclusionHom hf hF hS hT
    isCrystalSet_setOf_isIntegralPath hST hn hmap

/-- Postcomposing `dilationSimilarityHom` with `embedHom` gives
`dilationToNormalCrystalSimilarityHom`. -/
theorem embedHom_compSimilarityHom_dilationSimilarityHom (hf : Function.Injective f)
    (hF : ∀ (i : b.support) (x : X), F i (f x) = (P.coroot' i x : 𝕜))
    {S T : Set (PLPath 𝕜 V)} (hS : IsCrystalSet b f F S) (hT : IsCrystalSet b f F T)
    {n : ℕ} (hn : 0 < n)
    (hmap : ∀ ⦃π⦄, π ∈ S → π.map ((n : 𝕜) • LinearMap.id) ∈ T) :
    (embedHom (hf := hf) (hF := hF) hT).compSimilarityHom
        (dilationSimilarityHom hf hF hS hT hn hmap) =
      dilationToNormalCrystalSimilarityHom hf hF hS hn
        (fun _ hπ ↦ hT.subset_isIntegralPath (hmap hπ)) :=
  NormalCrystal.SimilarityHom.ext fun _ ↦ Subtype.ext (by simp)

/-- At magnification `n = 1`, `dilationSimilarityHom` recovers `inclusionHom`. -/
@[simp]
theorem toStrictHom_dilationSimilarityHom_one (hf : Function.Injective f)
    (hF : ∀ (i : b.support) (x : X), F i (f x) = (P.coroot' i x : 𝕜))
    {S T : Set (PLPath 𝕜 V)} (hS : IsCrystalSet b f F S) (hT : IsCrystalSet b f F T)
    (hn : 0 < 1) (hmap : ∀ ⦃π⦄, π ∈ S → π.map (((1 : ℕ) : 𝕜) • LinearMap.id) ∈ T) :
    (dilationSimilarityHom hf hF hS hT hn hmap).toStrictHom =
      inclusionHom hS hT (subset_def.mpr fun _ hπ ↦ by simpa using hmap hπ) :=
  NormalCrystal.StrictHom.ext fun _ ↦ Subtype.ext (by simp)

/-- At magnification `n = 1`, `dilationToNormalCrystalSimilarityHom` recovers `embedHom`. -/
@[simp]
theorem toStrictHom_dilationToNormalCrystalSimilarityHom_one (hf : Function.Injective f)
    (hF : ∀ (i : b.support) (x : X), F i (f x) = (P.coroot' i x : 𝕜))
    {S : Set (PLPath 𝕜 V)} (hS : IsCrystalSet b f F S) (hn : 0 < 1)
    (hmap : ∀ ⦃π⦄, π ∈ S → IsIntegralPath b f F (π.map (((1 : ℕ) : 𝕜) • LinearMap.id))) :
    (dilationToNormalCrystalSimilarityHom hf hF hS hn hmap).toStrictHom =
      embedHom hS :=
  NormalCrystal.StrictHom.ext fun _ ↦ Subtype.ext (by simp)

/-- Composing a magnification-`m` dilation with a magnification-`n` dilation equals the
magnification-`(m * n)` dilation. -/
theorem dilationSimilarityHom_comp (hf : Function.Injective f)
    (hF : ∀ (i : b.support) (x : X), F i (f x) = (P.coroot' i x : 𝕜))
    {S T U : Set (PLPath 𝕜 V)} (hS : IsCrystalSet b f F S) (hT : IsCrystalSet b f F T)
    (hU : IsCrystalSet b f F U) {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (hST : ∀ ⦃π⦄, π ∈ S → π.map ((n : 𝕜) • LinearMap.id) ∈ T)
    (hTU : ∀ ⦃π⦄, π ∈ T → π.map ((m : 𝕜) • LinearMap.id) ∈ U) :
    (dilationSimilarityHom hf hF hT hU hm hTU).comp
        (dilationSimilarityHom hf hF hS hT hn hST) =
      dilationSimilarityHom hf hF hS hU (Nat.mul_pos hm hn)
        (fun _ hπ ↦ by
          simpa [map_map, LinearMap.comp_smul, smul_smul, Nat.cast_mul, mul_comm] using
            hTU (hST hπ)) :=
  NormalCrystal.SimilarityHom.ext fun _ ↦ Subtype.ext
    (by simp [map_map, LinearMap.comp_smul, smul_smul, Nat.cast_mul, mul_comm])

/-- Applying `reverseIso` to the dual of `dilationToNormalCrystalSimilarityHom` agrees on
underlying paths with dilating the reversed path. -/
theorem reverseIso_dilationToNormalCrystalSimilarityHom_dual_apply (hf : Function.Injective f)
    (hF : ∀ (i : b.support) (x : X), F i (f x) = (P.coroot' i x : 𝕜))
    {S : Set (PLPath 𝕜 V)} (hS : IsCrystalSet b f F S) {n : ℕ} (hn : 0 < n)
    (hmap : ∀ ⦃π⦄, π ∈ S → IsIntegralPath b f F (π.map ((n : 𝕜) • LinearMap.id))) (x : S) :
    (reverseIso hf hF ((dilationToNormalCrystalSimilarityHom hf hF hS hn hmap).dual x)).val =
      x.val.reverse.map ((n : 𝕜) • LinearMap.id) := by
  simp [map_reverse]

end DilationHom

/-! ### Integrality does not descend along positive-integer dilation -/

section Counterexample

/-- **Integrality of `n • π` and `π.endpoint = 0` do not imply integrality of `π` for any `1 < n`**:
for an isolated simple node `i`, the excursion `-(1 / (2n)) α_i` followed by `(1 / (2n)) α_i` has
zero endpoint and dilates by `n` to the integral path `simpleRootBent 𝕜 f i`, yet has minimum
`i`-coroot height `-1 / n ∉ ℤ`. -/
theorem exists_isIntegralPath_map_natCast_smul_and_not_isIntegralPath_of_isolated
    (hF : ∀ (i : b.support) (x : X), F i (f x) = (P.coroot' i x : 𝕜)) (i : b.support)
    (hi : ∀ j : b.support, j ≠ i → P.pairing i.val j.val = 0) {n : ℕ} (hn : 1 < n) :
    ∃ π : PLPath 𝕜 V, π.endpoint = 0 ∧
      IsIntegralPath b f F (π.map ((n : 𝕜) • LinearMap.id)) ∧
      ¬ IsIntegralPath b f F π := by
  let u := (2 * (n : 𝕜))⁻¹ • f (P.root i)
  let π : PLPath 𝕜 V := straight 𝕜 (-u) * straight 𝕜 u
  have hn1 : (1 : 𝕜) < n := Nat.one_lt_cast.mpr hn
  have hn0 : (n : 𝕜) ≠ 0 := by linarith
  have hnu : (n : 𝕜) • u = (2 : 𝕜)⁻¹ • f (P.root i) := by
    simp only [u, smul_smul]
    congr 1
    field_simp
  have hdil : π.map ((n : 𝕜) • LinearMap.id) = simpleRootBent 𝕜 f i := by
    simp [π, simpleRootBent_def, hnu]
  have hint_bent : IsIntegralPath b f F (simpleRootBent 𝕜 f i) :=
    (isCrystalSet_simpleRootString hF i hi).subset_isIntegralPath (Or.inr (Or.inl rfl))
  have hFu : F i u = (n : 𝕜)⁻¹ := by
    simp only [u, map_smul, smul_eq_mul, apply_root_eq_two hF i]
    field_simp
  exact ⟨π, by simp [π], hdil ▸ hint_bent,
    not_isIntegralPath_straight_neg_mul_straight i
      (hFu ▸ inv_pos.mpr (by linarith)) (hFu ▸ inv_lt_one_of_one_lt₀ hn1)⟩

/-- Over any rank-one root datum (`Nonempty b.support` and `Subsingleton b.support`) and for any
`1 < n`, there exists a zero-endpoint path `π` whose `n`-dilation is an integral path while `π`
itself is not. -/
theorem exists_isIntegralPath_map_natCast_smul_and_not_isIntegralPath
    [Nonempty b.support] [Subsingleton b.support]
    (hF : ∀ (i : b.support) (x : X), F i (f x) = (P.coroot' i x : 𝕜)) {n : ℕ} (hn : 1 < n) :
    ∃ π : PLPath 𝕜 V, π.endpoint = 0 ∧
      IsIntegralPath b f F (π.map ((n : 𝕜) • LinearMap.id)) ∧
      ¬ IsIntegralPath b f F π := by
  obtain ⟨i⟩ := ‹Nonempty b.support›
  exact exists_isIntegralPath_map_natCast_smul_and_not_isIntegralPath_of_isolated hF i
    (fun j hj ↦ absurd (Subsingleton.elim j i) hj) hn

end Counterexample

end TauCeti.PLPath
