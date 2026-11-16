/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Crystal.Similarity
public import TauCeti.RepresentationTheory.LSPath.Crystal.Operations

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import TauCeti.RepresentationTheory.LSPath.CappedReflection

/-!
# Dilation similarity on normal crystals of piecewise-linear paths

Fix a root datum `P : RootDatum ι X Y` with a base `b : P.Base`, an injective additive realization
`f : X →+ V` in a vector space over a linearly ordered field `𝕜`, and height forms
`F : b.support → Module.Dual 𝕜 V` agreeing with the simple coroots on `f(X)`.

Whenever `0 < n` and positive-integer dilation `π ↦ π.map ((n : 𝕜) • LinearMap.id)` sends a
crystal-admissible set `S` into a crystal-admissible set `T`, the path-level similarity identity
`PLPath.raiseIter_map_natCast_smul` assembles dilation into a magnification-`n` crystal similarity
morphism `TauCeti.PLPath.dilationOnSimilarityHom` from `normalCrystalOn hf hF hS` to
`normalCrystalOn hf hF hT` (and into `normalCrystal hf hF` when dilated paths in `S` are integral,
via `TauCeti.PLPath.dilationToNormalCrystalSimilarityHom`). At magnification `n = 1`, these
morphisms recover `inclusionHom` (`TauCeti.PLPath.toStrictHom_dilationOnSimilarityHom_one`) and
`embedHom` (`TauCeti.PLPath.toStrictHom_dilationToNormalCrystalSimilarityHom_one`); postcomposing
`dilationOnSimilarityHom` with `embedHom` yields `dilationToNormalCrystalSimilarityHom`
(`TauCeti.PLPath.embedHom_compSimilarityHom_dilationOnSimilarityHom`); dilation morphisms compose
multiplicatively across magnification factors (`TauCeti.PLPath.dilationOnSimilarityHom_comp`); and
`reverseIso` applied to the dual of `dilationToNormalCrystalSimilarityHom` agrees on underlying
paths with dilation of the reversed path
(`TauCeti.PLPath.reverseIso_dilationToNormalCrystalSimilarityHom_dual_apply`).

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

* `TauCeti.PLPath.dilationOnSimilarityHom`: magnification-`n` similarity morphism induced by
  positive-integer path dilation between `normalCrystalOn` crystals.
* `TauCeti.PLPath.dilationToNormalCrystalSimilarityHom`: specialization with target
  `normalCrystal hf hF`.

## Main results

* `TauCeti.PLPath.dilationOnSimilarityHom_injective`: dilation similarity morphisms on path
  crystals are always injective (since scalar multiplication by `(n : 𝕜) ≠ 0` is a linear
  automorphism of `V`, hence induces a bijection on `PLPath 𝕜 V`).
* `TauCeti.PLPath.embedHom_compSimilarityHom_dilationOnSimilarityHom`,
  `TauCeti.PLPath.toStrictHom_dilationOnSimilarityHom_one`,
  `TauCeti.PLPath.toStrictHom_dilationToNormalCrystalSimilarityHom_one`,
  `TauCeti.PLPath.dilationOnSimilarityHom_comp`,
  `TauCeti.PLPath.reverseIso_dilationToNormalCrystalSimilarityHom_dual_apply`: factorization
  through `embedHom`, reduction at `n = 1` to `inclusionHom` and `embedHom`, multiplicative
  composition, and agreement on underlying paths with `reverseIso` on dualized dilation.
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

/-! ### Dilation similarity morphisms between path crystals -/

section DilationHom

/-- **Path dilation realizes crystal similarity**: for `0 < n`, whenever positive-integer dilation
`π ↦ π.map ((n : 𝕜) • LinearMap.id)` maps a crystal-admissible set `S` into a crystal-admissible
set `T`, it induces a magnification-`n` similarity morphism between their `normalCrystalOn`
crystals. -/
noncomputable def dilationOnSimilarityHom (hf : Function.Injective f)
    (hF : ∀ (i : b.support) (x : X), F i (f x) = (P.coroot' i x : 𝕜))
    {S T : Set (PLPath 𝕜 V)} (hS : IsCrystalSet b f F S) (hT : IsCrystalSet b f F T)
    {n : ℕ} (hn : 0 < n)
    (hmap : ∀ ⦃π⦄, π ∈ S → π.map ((n : 𝕜) • LinearMap.id) ∈ T) :
    NormalCrystal.SimilarityHom
      (normalCrystalOn hf hF hS) (normalCrystalOn hf hF hT) n where
  toFun x := ⟨x.1.map ((n : 𝕜) • LinearMap.id), hmap x.2⟩
  wt_toFun x := hf (by
    rw [apply_normalCrystalOn_wt, endpoint_map, LinearMap.smul_apply, LinearMap.id_apply,
      map_nsmul, apply_normalCrystalOn_wt, Nat.cast_smul_eq_nsmul])
  ε_toFun i x := by
    rw [normalCrystalOn_ε_eq_iff, minHeight_map_smul (Nat.cast_nonneg n), Nat.cast_mul,
      cast_normalCrystalOn_ε]
    ring
  eIter_toFun i x := by
    rw [normalCrystalOn_eIter_eq_map_iff, raiseIter_map_natCast_smul (apply_root_eq_two hF i) hn,
      ← unattach_normalCrystalOn_e (hf := hf) (hF := hF) (hS := hS) i x, Option.unattach,
      Option.map_map]
    rfl

@[simp]
theorem dilationOnSimilarityHom_apply (hf : Function.Injective f)
    (hF : ∀ (i : b.support) (x : X), F i (f x) = (P.coroot' i x : 𝕜))
    {S T : Set (PLPath 𝕜 V)} (hS : IsCrystalSet b f F S) (hT : IsCrystalSet b f F T)
    {n : ℕ} (hn : 0 < n)
    (hmap : ∀ ⦃π⦄, π ∈ S → π.map ((n : 𝕜) • LinearMap.id) ∈ T) (x : S) :
    (dilationOnSimilarityHom hf hF hS hT hn hmap x).1 = x.1.map ((n : 𝕜) • LinearMap.id) :=
  (rfl)

/-- Every positive-integer dilation similarity morphism on path crystals is injective, since
rescaling by `(n : 𝕜)⁻¹` recovers the underlying path. -/
theorem dilationOnSimilarityHom_injective (hf : Function.Injective f)
    (hF : ∀ (i : b.support) (x : X), F i (f x) = (P.coroot' i x : 𝕜))
    {S T : Set (PLPath 𝕜 V)} (hS : IsCrystalSet b f F S) (hT : IsCrystalSet b f F T)
    {n : ℕ} (hn : 0 < n)
    (hmap : ∀ ⦃π⦄, π ∈ S → π.map ((n : 𝕜) • LinearMap.id) ∈ T) :
    Function.Injective (dilationOnSimilarityHom hf hF hS hT hn hmap) := by
  have hn0 : (n : 𝕜) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  intro x y hxy
  apply Subtype.ext
  have hval := congrArg (fun z : T ↦ z.1.map ((n : 𝕜)⁻¹ • LinearMap.id)) hxy
  simpa [map_map, LinearMap.comp_smul, smul_smul, mul_inv_cancel₀ hn0] using hval

/-- Specialization of `dilationOnSimilarityHom` landing in Littelmann's ambient integral-path
crystal `normalCrystal hf hF`. -/
noncomputable def dilationToNormalCrystalSimilarityHom (hf : Function.Injective f)
    (hF : ∀ (i : b.support) (x : X), F i (f x) = (P.coroot' i x : 𝕜))
    {S : Set (PLPath 𝕜 V)} (hS : IsCrystalSet b f F S) {n : ℕ} (hn : 0 < n)
    (hmap : ∀ ⦃π⦄, π ∈ S → IsIntegralPath b f F (π.map ((n : 𝕜) • LinearMap.id))) :
    NormalCrystal.SimilarityHom (normalCrystalOn hf hF hS) (normalCrystal hf hF) n :=
  dilationOnSimilarityHom hf hF hS isCrystalSet_setOf_isIntegralPath hn hmap

@[simp]
theorem dilationToNormalCrystalSimilarityHom_apply (hf : Function.Injective f)
    (hF : ∀ (i : b.support) (x : X), F i (f x) = (P.coroot' i x : 𝕜))
    {S : Set (PLPath 𝕜 V)} (hS : IsCrystalSet b f F S) {n : ℕ} (hn : 0 < n)
    (hmap : ∀ ⦃π⦄, π ∈ S → IsIntegralPath b f F (π.map ((n : 𝕜) • LinearMap.id))) (x : S) :
    (dilationToNormalCrystalSimilarityHom hf hF hS hn hmap x).1 =
      x.1.map ((n : 𝕜) • LinearMap.id) :=
  (rfl)

/-- Every positive-integer dilation similarity morphism into `normalCrystal hf hF` is injective. -/
theorem dilationToNormalCrystalSimilarityHom_injective (hf : Function.Injective f)
    (hF : ∀ (i : b.support) (x : X), F i (f x) = (P.coroot' i x : 𝕜))
    {S : Set (PLPath 𝕜 V)} (hS : IsCrystalSet b f F S) {n : ℕ} (hn : 0 < n)
    (hmap : ∀ ⦃π⦄, π ∈ S → IsIntegralPath b f F (π.map ((n : 𝕜) • LinearMap.id))) :
    Function.Injective (dilationToNormalCrystalSimilarityHom hf hF hS hn hmap) :=
  dilationOnSimilarityHom_injective hf hF hS isCrystalSet_setOf_isIntegralPath hn hmap

/-- Postcomposing `dilationOnSimilarityHom` with `embedHom` gives
`dilationToNormalCrystalSimilarityHom`. -/
theorem embedHom_compSimilarityHom_dilationOnSimilarityHom (hf : Function.Injective f)
    (hF : ∀ (i : b.support) (x : X), F i (f x) = (P.coroot' i x : 𝕜))
    {S T : Set (PLPath 𝕜 V)} (hS : IsCrystalSet b f F S) (hT : IsCrystalSet b f F T)
    {n : ℕ} (hn : 0 < n)
    (hmap : ∀ ⦃π⦄, π ∈ S → π.map ((n : 𝕜) • LinearMap.id) ∈ T) :
    (embedHom (hf := hf) (hF := hF) hT).compSimilarityHom
        (dilationOnSimilarityHom hf hF hS hT hn hmap) =
      dilationToNormalCrystalSimilarityHom hf hF hS hn
        (fun _ hπ ↦ hT.subset_isIntegralPath (hmap hπ)) :=
  NormalCrystal.SimilarityHom.ext fun _ ↦ Subtype.ext (by simp)

/-- At magnification `n = 1`, `dilationOnSimilarityHom` recovers `inclusionHom`. -/
@[simp]
theorem toStrictHom_dilationOnSimilarityHom_one (hf : Function.Injective f)
    (hF : ∀ (i : b.support) (x : X), F i (f x) = (P.coroot' i x : 𝕜))
    {S T : Set (PLPath 𝕜 V)} (hS : IsCrystalSet b f F S) (hT : IsCrystalSet b f F T)
    (hn : 0 < 1) (hmap : ∀ ⦃π⦄, π ∈ S → π.map (((1 : ℕ) : 𝕜) • LinearMap.id) ∈ T) :
    (dilationOnSimilarityHom hf hF hS hT hn hmap).toStrictHom =
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
theorem dilationOnSimilarityHom_comp (hf : Function.Injective f)
    (hF : ∀ (i : b.support) (x : X), F i (f x) = (P.coroot' i x : 𝕜))
    {S T U : Set (PLPath 𝕜 V)} (hS : IsCrystalSet b f F S) (hT : IsCrystalSet b f F T)
    (hU : IsCrystalSet b f F U) {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (hST : ∀ ⦃π⦄, π ∈ S → π.map ((n : 𝕜) • LinearMap.id) ∈ T)
    (hTU : ∀ ⦃π⦄, π ∈ T → π.map ((m : 𝕜) • LinearMap.id) ∈ U) :
    (dilationOnSimilarityHom hf hF hT hU hm hTU).comp
        (dilationOnSimilarityHom hf hF hS hT hn hST) =
      dilationOnSimilarityHom hf hF hS hU (Nat.mul_pos hm hn)
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
    (reverseIso hf hF ((dilationToNormalCrystalSimilarityHom hf hF hS hn hmap).dual x)).1 =
      x.1.reverse.map ((n : 𝕜) • LinearMap.id) := by
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
    (hi : ∀ j : b.support, j ≠ i → P.pairing i.1 j.1 = 0) {n : ℕ} (hn : 1 < n) :
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
