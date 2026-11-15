/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Crystal.Similarity
public import TauCeti.RepresentationTheory.LSPath.Crystal.Operations
public import TauCeti.RepresentationTheory.LSPath.Similarity

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

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
via `TauCeti.PLPath.dilationToNormalCrystalSimilarityHom`). Dilation similarity is functorial with
respect to inclusions, multiplicatively composes across magnification factors, and commutes with
path reversal (`reverseIso`).

Conversely, integrality of a dilated path does **not** descend to the original path, even when the
original path already has zero endpoint (`π.endpoint = 0 ∈ f(X)`): for any isolated simple node `i`
(in particular on every rank-one root datum), the excursion `-(1/4) α_i` followed by `(1/4) α_i`
dilates at `n = 2` to the integral path `simpleRootBent 𝕜 f i` while itself having non-integral
minimum height `-1/2` (`TauCeti.PLPath.exists_isIntegralPath_two_smul_and_not_isIntegralPath`).
Thus crystal-admissibility of the unstretched source set is genuinely needed in the crystal
similarity construction.

## Main definitions

* `TauCeti.PLPath.dilationOnSimilarityHom`: magnification-`n` similarity morphism induced by
  positive-integer path dilation between `normalCrystalOn` crystals.
* `TauCeti.PLPath.dilationToNormalCrystalSimilarityHom`: specialization with target
  `normalCrystal hf hF`.

## Main results

* `TauCeti.PLPath.dilationOnSimilarityHom_injective`: dilation similarity morphisms on path
  crystals are always injective (since scalar multiplication by `(n : 𝕜) ≠ 0` is a linear
  automorphism on `PLPath 𝕜 V`).
* `TauCeti.PLPath.dilationOnSimilarityHom_one`, `TauCeti.PLPath.dilationOnSimilarityHom_comp`,
  `TauCeti.PLPath.reverseIso_comp_dilationToNormalCrystalSimilarityHom`: compatibility with
  inclusions, iterated dilation, and crystal duality.
* `TauCeti.PLPath.exists_isIntegralPath_two_smul_and_not_isIntegralPath_of_isolated`,
  `TauCeti.PLPath.exists_isIntegralPath_two_smul_and_not_isIntegralPath`: integrality of `2 • π`
  and `π.endpoint = 0` do not imply integrality of `π`.

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

section IterCriteria

variable {hf : Function.Injective f}
  {hF : ∀ (i : b.support) (x : X), F i (f x) = (P.coroot' i x : 𝕜)}
  {S : Set (PLPath 𝕜 V)} {hS : IsCrystalSet b f F S}

/-- Equality of `eIter` in `normalCrystalOn` reduces to equality of `raiseIter` on underlying
paths. -/
theorem normalCrystalOn_eIter_eq_iff {i : b.support} {n : ℕ} {π : S} {o : Option S} :
    (normalCrystalOn hf hF hS).eIter i n π = o ↔
      raiseIter (F i) (f (P.root i)) n π.1 = o.unattach := by
  rw [← unattach_normalCrystalOn_eIter (hf := hf) (hF := hF) (hS := hS)]
  cases (normalCrystalOn hf hF hS).eIter i n π <;> cases o <;> simp [Subtype.ext_iff]

/-- Equality of `fIter` in `normalCrystalOn` reduces to equality of `lowerIter` on underlying
paths. -/
theorem normalCrystalOn_fIter_eq_iff {i : b.support} {n : ℕ} {π : S} {o : Option S} :
    (normalCrystalOn hf hF hS).fIter i n π = o ↔
      lowerIter (F i) (f (P.root i)) n π.1 = o.unattach := by
  rw [← unattach_normalCrystalOn_fIter (hf := hf) (hF := hF) (hS := hS)]
  cases (normalCrystalOn hf hF hS).fIter i n π <;> cases o <;> simp [Subtype.ext_iff]

/-- Equality of `eIter` with `o.map g` in `normalCrystalOn` reduces to `raiseIter` on underlying
paths. -/
theorem normalCrystalOn_eIter_eq_map_iff {B : Type*} {i : b.support} {n : ℕ} {π : S}
    {o : Option B} {g : B → S} :
    (normalCrystalOn hf hF hS).eIter i n π = o.map g ↔
      raiseIter (F i) (f (P.root i)) n π.1 = o.map (fun x ↦ (g x).1) := by
  rw [normalCrystalOn_eIter_eq_iff, Option.unattach, Option.map_map, Function.comp_def]

/-- Equality of `fIter` with `o.map g` in `normalCrystalOn` reduces to `lowerIter` on underlying
paths. -/
theorem normalCrystalOn_fIter_eq_map_iff {B : Type*} {i : b.support} {n : ℕ} {π : S}
    {o : Option B} {g : B → S} :
    (normalCrystalOn hf hF hS).fIter i n π = o.map g ↔
      lowerIter (F i) (f (P.root i)) n π.1 = o.map (fun x ↦ (g x).1) := by
  rw [normalCrystalOn_fIter_eq_iff, Option.unattach, Option.map_map, Function.comp_def]

end IterCriteria

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
theorem dilationOnSimilarityHom_one (hf : Function.Injective f)
    (hF : ∀ (i : b.support) (x : X), F i (f x) = (P.coroot' i x : 𝕜))
    {S T : Set (PLPath 𝕜 V)} (hS : IsCrystalSet b f F S) (hT : IsCrystalSet b f F T)
    (hST : S ⊆ T) :
    (dilationOnSimilarityHom hf hF hS hT Nat.one_pos
      (fun _ hπ ↦ by simpa using hST hπ)).toStrictHom =
      inclusionHom hS hT hST :=
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

/-- Path reversal intertwines dualized dilation similarity with dilation on reversed paths. -/
theorem reverseIso_comp_dilationToNormalCrystalSimilarityHom (hf : Function.Injective f)
    (hF : ∀ (i : b.support) (x : X), F i (f x) = (P.coroot' i x : 𝕜))
    {S : Set (PLPath 𝕜 V)} (hS : IsCrystalSet b f F S) {n : ℕ} (hn : 0 < n)
    (hmap : ∀ ⦃π⦄, π ∈ S → IsIntegralPath b f F (π.map ((n : 𝕜) • LinearMap.id))) (x : S) :
    (reverseIso hf hF ((dilationToNormalCrystalSimilarityHom hf hF hS hn hmap).dual x)).1 =
      x.1.reverse.map ((n : 𝕜) • LinearMap.id) := by
  simp [map_reverse]

end DilationHom

/-! ### Integrality does not descend along positive-integer dilation -/

section Counterexample

/-- **Integrality of `2 • π` and `π.endpoint = 0` do not imply integrality of `π`**: for an
isolated simple node `i`, the excursion `-(1/4) α_i` followed by `(1/4) α_i` has zero endpoint and
dilates by `2` to the integral path `simpleRootBent 𝕜 f i`, yet has minimum `i`-coroot height
`-1/2 ∉ ℤ`. -/
theorem exists_isIntegralPath_two_smul_and_not_isIntegralPath_of_isolated
    (hF : ∀ (i : b.support) (x : X), F i (f x) = (P.coroot' i x : 𝕜)) (i : b.support)
    (hi : ∀ j : b.support, j ≠ i → P.pairing i.1 j.1 = 0) :
    ∃ π : PLPath 𝕜 V, π.endpoint = 0 ∧
      IsIntegralPath b f F (π.map ((2 : 𝕜) • LinearMap.id)) ∧
      ¬ IsIntegralPath b f F π := by
  let u := (4 : 𝕜)⁻¹ • f (P.root i)
  let π : PLPath 𝕜 V := straight 𝕜 (-u) * straight 𝕜 u
  have h2u : (2 : 𝕜) • u = (2 : 𝕜)⁻¹ • f (P.root i) := by
    simp only [u, smul_smul]
    norm_num
  have hdil : π.map ((2 : 𝕜) • LinearMap.id) = simpleRootBent 𝕜 f i := by
    simp [π, simpleRootBent_def, h2u]
  have hint_bent : IsIntegralPath b f F (simpleRootBent 𝕜 f i) :=
    (isCrystalSet_simpleRootString hF i hi).subset_isIntegralPath (Or.inr (Or.inl rfl))
  refine ⟨π, by simp [π], hdil ▸ hint_bent, fun hπ ↦ ?_⟩
  obtain ⟨z, hz⟩ := hπ.exists_minHeight_eq_intCast i
  have hmin : π.minHeight (F i) = -(2 : 𝕜)⁻¹ := by
    rw [minHeight_straight_neg_mul_straight]
    simp only [u, map_smul, smul_eq_mul, apply_root_eq_two hF i]
    norm_num
  rw [hmin] at hz
  have h2z : ((2 * z : ℤ) : 𝕜) = -1 := by
    push_cast
    linarith
  have : (2 * z : ℤ) = -1 := by exact_mod_cast h2z
  omega

/-- Over any rank-one root datum (`Nonempty b.support` and `Subsingleton b.support`), there exists
a zero-endpoint path `π` whose `2`-dilation is an integral path while `π` itself is not. -/
theorem exists_isIntegralPath_two_smul_and_not_isIntegralPath
    [Nonempty b.support] [Subsingleton b.support]
    (hF : ∀ (i : b.support) (x : X), F i (f x) = (P.coroot' i x : 𝕜)) :
    ∃ π : PLPath 𝕜 V, π.endpoint = 0 ∧
      IsIntegralPath b f F (π.map ((2 : 𝕜) • LinearMap.id)) ∧
      ¬ IsIntegralPath b f F π := by
  obtain ⟨i⟩ := ‹Nonempty b.support›
  exact exists_isIntegralPath_two_smul_and_not_isIntegralPath_of_isolated hF i
    fun j hj ↦ absurd (Subsingleton.elim j i) hj

end Counterexample

end TauCeti.PLPath
