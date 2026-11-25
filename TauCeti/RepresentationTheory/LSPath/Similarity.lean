/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Crystal.Similarity
public import TauCeti.RepresentationTheory.LSPath.CappedReflection
public import TauCeti.RepresentationTheory.LSPath.Crystal.Normal
public import TauCeti.RepresentationTheory.LSPath.Crystal.Operations
public import TauCeti.RepresentationTheory.LSPath.RationalChain
import TauCeti.Data.Option.Basic
import TauCeti.LinearAlgebra.Dual.BaseChange
import TauCeti.LinearAlgebra.RootSystem.Reduced
import TauCeti.RepresentationTheory.LSPath.Realization.Faithful

/-!
# Littelmann's path similarity under positive-scalar dilation and stretching

Fix a vector `x : V` and a linear form `f : Dual 𝕜 V` with `f x = 2`. Combining the single
capped-reflection formula for `lowerIter f x n` (`TauCeti.PLPath.lowerIter_eq_ite_cappedReflection`)
with positive scalar equivariance of capped reflection (`TauCeti.PLPath.cappedReflection_map_smul`)
yields Littelmann's general **positive-scalar path similarity theorem**
(`TauCeti.PLPath.lowerIter_map_smul`, `TauCeti.PLPath.raiseIter_map_smul`): for every `0 < a`
and `m, n : ℕ` satisfying `(m : 𝕜) = a * n`, `m`-fold lowering or raising on the `a`-dilated path
equals the `a`-dilation of `n`-fold lowering or raising on the original path (with no integrality
assumption on the path). Specializing to `(a, m, n) = (n, n, 1)` recovers positive-integer
dilation (`TauCeti.PLPath.lowerIter_map_natCast_smul`, `TauCeti.PLPath.raiseIter_map_natCast_smul`),
and specializing to `(a, m, n) = ((n : 𝕜)⁻¹, 1, n)` gives fractional `(n : 𝕜)⁻¹`-contraction.

Because nonzero scalar dilation acts injectively on `PLPath 𝕜 V`
(`TauCeti.PLPath.map_smul_id_injective`), whenever `(m : 𝕜) = a * n` for `0 < a`, dilation by `a`
both preserves and reflects defined iterated root operators and replicated root-operator words,
matching `m` steps (or `m` copies per letter) after dilation with `n` steps (or `n` copies per
letter) before dilation (`TauCeti.PLPath.lowerIter_map_smul_eq_some_iff`,
`TauCeti.PLPath.lowerWord_flatMap_replicate_map_smul_eq_some_iff`). On crystal-admissible
sets of paths and connected path components, positive-integer dilation assembles into injective
similarity morphisms of normal crystals (`TauCeti.PLPath.dilationSimilarityHom`,
`TauCeti.PLPath.componentDilationSimilarityHom`), and in particular embeds every integral
straight-path component `B(π_λ)` into `B(π_{n λ})`
(`TauCeti.PLPath.straightComponentDilationSimilarityHom`,
`TauCeti.PLPath.simpleRootStringDilationSimilarityHom`).

Specializing to Lakshmibai–Seshadri paths connects `LSPath.stretch` and the denominator-clearing
construction `LSPath.ofBruhatChain` with iterated root operators and `n`-replicated words, and
packages stretching as a similarity morphism `LSPath.stretchSimilarityHom : B(λ) → B(n • λ)` whose
rigidity and injectivity follow from highest-weight generation of `B(λ)`
(`LSPath.eq_of_similarityHom_apply_straight_eq`, `LSPath.similarityHom_injective`).

## Main definitions

* `TauCeti.PLPath.dilationSimilarityHom`: positive-integer dilation as a
  `TauCeti.NormalCrystal.SimilarityHom` between normal crystals on crystal-admissible path sets.
* `TauCeti.PLPath.componentDilationSimilarityHom`,
  `TauCeti.PLPath.straightComponentDilationSimilarityHom`,
  `TauCeti.PLPath.simpleRootStringDilationSimilarityHom`: Kashiwara–Littelmann similarity embeddings
  on connected path components, integral straight-path components `B(π_λ) ↪ B(π_{n λ})`, and
  isolated simple-root strings.
* `TauCeti.LSPath.stretchSimilarityHom`: positive-integer stretching as a scale-factor-`n`
  similarity morphism `B(λ) → B(n • λ)`.

## Main results

* `TauCeti.PLPath.lowerIter_map_smul`, `TauCeti.PLPath.raiseIter_map_smul`: Littelmann's
  positive-scalar path similarity theorem for `(m : 𝕜) = a * n` on arbitrary piecewise-linear
  paths (covering both positive-integer dilation `(a, m, n) = (n, n, 1)` and fractional
  contraction `(a, m, n) = ((n : 𝕜)⁻¹, 1, n)`), with positive-integer corollaries
  `TauCeti.PLPath.lowerIter_map_natCast_smul` and `TauCeti.PLPath.raiseIter_map_natCast_smul`.
* `TauCeti.PLPath.lowerWord_flatMap_replicate_map_smul`,
  `TauCeti.PLPath.raiseWord_flatMap_replicate_map_smul`,
  `TauCeti.PLPath.lowerWord_flatMap_replicate_map_smul_eq_some_iff`,
  `TauCeti.PLPath.raiseWord_flatMap_replicate_map_smul_eq_some_iff`,
  `TauCeti.PLPath.lowerWord_flatMap_replicate_map_natCast_smul`,
  `TauCeti.PLPath.raiseWord_flatMap_replicate_map_natCast_smul`,
  `TauCeti.PLPath.lowerWord_flatMap_replicate_map_natCast_smul_eq_some_iff`,
  `TauCeti.PLPath.raiseWord_flatMap_replicate_map_natCast_smul_eq_some_iff`: when `(m : 𝕜) = a * n`
  for `0 < a`, dilation by `a` intertwines (and preserves/reflects definedness of) lowering and
  raising along `m`-replicated words after dilation and `n`-replicated words before dilation
  (specializing to `n` copies vs. `1` copy at `a = n`, and `1` copy vs. `n` copies at
  `a = (n : 𝕜)⁻¹`).
* `TauCeti.PLPath.reflTransGen_rootStep_map_natCast_smul`,
  `TauCeti.PLPath.IsIntegralPath.map_natCast_smul_of_reflTransGen_rootStep`: dilation by
  any `n : ℕ` preserves finite sequences of simple-root steps and transports integrality
  along root-step walks.
* `TauCeti.LSPath.lowerIter_toPLPath_stretch`,
  `TauCeti.LSPath.lowerIter_toPLPath_ofBruhatChain`,
  `TauCeti.LSPath.lowerWord_flatMap_replicate_toPLPath_ofBruhatChain_eq_some_iff`: root-operator
  similarity for stretched LS paths and cleared rational Bruhat-chain paths.
* `TauCeti.LSPath.eq_of_similarityHom_apply_straight_eq`,
  `TauCeti.LSPath.similarityHom_injective`: rigidity and automatic injectivity of similarity
  morphisms out of `B(λ)`.

## References

* P. Littelmann, *Paths and root operators in representation theory*, Ann. of Math. 142 (1995),
  499--525, §§1–2, 5.
* M. Kashiwara, *Similarity of crystal bases*, in Lie algebras and their representations (Seoul,
  1995), Contemp. Math. 194, Amer. Math. Soc. (1996), 177–186, §3.
* D. Bump and A. Schilling, *Crystal bases: representations and combinatorics*, World Scientific
  (2017), §14.1 (crystal similarity morphisms and automatic injectivity/rigidity).
-/

public section

namespace TauCeti.PLPath

open _root_.Module Relation

/-! ### Littelmann's path similarity theorem -/

section DilationSimilarity

variable {ι 𝕜 V : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [AddCommGroup V] [Module 𝕜 V] {f : Dual 𝕜 V} {x : V}

/-- **Dilation similarity for iterated lowering** (Littelmann): for `f x = 2`, `0 < a`, and
`(m : 𝕜) = a * n`, `m`-fold lowering on the `a`-dilated path equals the `a`-dilation of `n`-fold
lowering on the original path. No integrality of the path is needed. Specializing to
`(a, m, n) = ((n : 𝕜)⁻¹, 1, n)` yields fractional `(n : 𝕜)⁻¹`-contraction (Littelmann,
Lemma 2.1(d)). -/
theorem lowerIter_map_smul (hx : f x = 2) {a : 𝕜} (ha : 0 < a) {m n : ℕ}
    (hmn : (m : 𝕜) = a * n) (p : PLPath 𝕜 V) :
    lowerIter f x m (p.map (a • LinearMap.id)) =
      (lowerIter f x n p).map (·.map (a • LinearMap.id)) := by
  have hcond :
      ((m : 𝕜) ≤
          f (p.map (a • LinearMap.id)).endpoint - (p.map (a • LinearMap.id)).minHeight f) ↔
        (n : 𝕜) ≤ f p.endpoint - p.minHeight f := by
    simp only [endpoint_map, LinearMap.smul_apply, LinearMap.id_apply, map_smul, smul_eq_mul,
      minHeight_map_smul ha.le, ← mul_sub, hmn, mul_le_mul_iff_right₀ ha]
  rw [lowerIter_eq_ite_cappedReflection hx, lowerIter_eq_ite_cappedReflection hx,
    if_congr hcond rfl rfl]
  split_ifs with hn
  · simp [minHeight_map_smul ha.le, hmn, ← mul_add, cappedReflection_map_smul ha]
  · rfl

/-- **Dilation similarity for iterated raising** (Littelmann): for `f x = 2`, `0 < a`, and
`(m : 𝕜) = a * n`, `m`-fold raising on the `a`-dilated path equals the `a`-dilation of `n`-fold
raising on the original path. Specializing to `(a, m, n) = ((n : 𝕜)⁻¹, 1, n)` yields fractional
`(n : 𝕜)⁻¹`-contraction. -/
theorem raiseIter_map_smul (hx : f x = 2) {a : 𝕜} (ha : 0 < a) {m n : ℕ}
    (hmn : (m : 𝕜) = a * n) (p : PLPath 𝕜 V) :
    raiseIter f x m (p.map (a • LinearMap.id)) =
      (raiseIter f x n p).map (·.map (a • LinearMap.id)) := by
  rw [raiseIter_eq_map_lowerIter_reverse, raiseIter_eq_map_lowerIter_reverse, ← map_reverse,
    lowerIter_map_smul hx ha hmn]
  simp only [Option.map_map, Function.comp_def, map_reverse]

/-- Positive-scalar dilation preserves and reflects iterated lowering via `(m : 𝕜) = a * n`. -/
theorem lowerIter_map_smul_eq_some_iff (hx : f x = 2) {a : 𝕜} (ha : 0 < a) {m n : ℕ}
    (hmn : (m : 𝕜) = a * n) {p q : PLPath 𝕜 V} :
    lowerIter f x m (p.map (a • LinearMap.id)) = some (q.map (a • LinearMap.id)) ↔
      lowerIter f x n p = some q := by
  rw [lowerIter_map_smul hx ha hmn, Option.map_eq_some_iff]
  simp [(map_smul_id_injective (V := V) ha.ne').eq_iff]

/-- Positive-scalar dilation preserves and reflects iterated raising via `(m : 𝕜) = a * n`. -/
theorem raiseIter_map_smul_eq_some_iff (hx : f x = 2) {a : 𝕜} (ha : 0 < a) {m n : ℕ}
    (hmn : (m : 𝕜) = a * n) {p q : PLPath 𝕜 V} :
    raiseIter f x m (p.map (a • LinearMap.id)) = some (q.map (a • LinearMap.id)) ↔
      raiseIter f x n p = some q := by
  rw [raiseIter_map_smul hx ha hmn, Option.map_eq_some_iff]
  simp [(map_smul_id_injective (V := V) ha.ne').eq_iff]

/-- **Littelmann's path similarity theorem (lowering)**: for `f x = 2` and any positive integer `n`,
dilating a piecewise-linear path `p` by `n` intertwines `lower f x` with the `n`-fold iterate
`lowerIter f x n`. No integrality assumption on `p` is required. -/
theorem lowerIter_map_natCast_smul (hx : f x = 2) {n : ℕ} (hn : 0 < n) (p : PLPath 𝕜 V) :
    lowerIter f x n (p.map ((n : 𝕜) • LinearMap.id)) =
      (lower f x p).map (·.map ((n : 𝕜) • LinearMap.id)) := by
  simpa using lowerIter_map_smul hx (Nat.cast_pos.mpr hn) (m := n) (n := 1) (by simp) p

/-- **Littelmann's path similarity theorem (raising)**: for `f x = 2` and any positive integer `n`,
dilating a piecewise-linear path `p` by `n` intertwines `raise f x` with the `n`-fold iterate
`raiseIter f x n`. -/
theorem raiseIter_map_natCast_smul (hx : f x = 2) {n : ℕ} (hn : 0 < n) (p : PLPath 𝕜 V) :
    raiseIter f x n (p.map ((n : 𝕜) • LinearMap.id)) =
      (raise f x p).map (·.map ((n : 𝕜) • LinearMap.id)) := by
  simpa using raiseIter_map_smul hx (Nat.cast_pos.mpr hn) (m := n) (n := 1) (by simp) p

/-- Dilation by `n > 0` intertwines `lowerIter f x k` with `lowerIter f x (n * k)`. -/
theorem lowerIter_mul_map_natCast_smul (hx : f x = 2) {n : ℕ} (hn : 0 < n) (k : ℕ)
    (p : PLPath 𝕜 V) :
    lowerIter f x (n * k) (p.map ((n : 𝕜) • LinearMap.id)) =
      (lowerIter f x k p).map (·.map ((n : 𝕜) • LinearMap.id)) :=
  lowerIter_map_smul hx (Nat.cast_pos.mpr hn) (m := n * k) (n := k) (by push_cast; ring) p

/-- Dilation by `n > 0` intertwines `raiseIter f x k` with `raiseIter f x (n * k)`. -/
theorem raiseIter_mul_map_natCast_smul (hx : f x = 2) {n : ℕ} (hn : 0 < n) (k : ℕ)
    (p : PLPath 𝕜 V) :
    raiseIter f x (n * k) (p.map ((n : 𝕜) • LinearMap.id)) =
      (raiseIter f x k p).map (·.map ((n : 𝕜) • LinearMap.id)) :=
  raiseIter_map_smul hx (Nat.cast_pos.mpr hn) (m := n * k) (n := k) (by push_cast; ring) p

/-- Positive-integer dilation preserves and reflects single-step lowering via `lowerIter f x n`. -/
theorem lowerIter_map_natCast_smul_eq_some_iff (hx : f x = 2) {n : ℕ} (hn : 0 < n)
    {p q : PLPath 𝕜 V} :
    lowerIter f x n (p.map ((n : 𝕜) • LinearMap.id)) =
        some (q.map ((n : 𝕜) • LinearMap.id)) ↔
      lower f x p = some q := by
  simpa using lowerIter_map_smul_eq_some_iff hx (Nat.cast_pos.mpr hn)
    (m := n) (n := 1) (by simp) (p := p) (q := q)

/-- Positive-integer dilation preserves and reflects single-step raising via `raiseIter f x n`. -/
theorem raiseIter_map_natCast_smul_eq_some_iff (hx : f x = 2) {n : ℕ} (hn : 0 < n)
    {p q : PLPath 𝕜 V} :
    raiseIter f x n (p.map ((n : 𝕜) • LinearMap.id)) =
        some (q.map ((n : 𝕜) • LinearMap.id)) ↔
      raise f x p = some q := by
  simpa using raiseIter_map_smul_eq_some_iff hx (Nat.cast_pos.mpr hn)
    (m := n) (n := 1) (by simp) (p := p) (q := q)

/-- **Dilation similarity for lowering words**: for `F i (x i) = 2` on every letter `i ∈ w`,
`0 < a`, and `(m : 𝕜) = a * n`, lowering along `w.flatMap fun i ↦ List.replicate m i` on the
`a`-dilated path equals the `a`-dilation of lowering along
`w.flatMap fun i ↦ List.replicate n i` on the original path. Specializing to
`(a, m, n) = ((n : 𝕜)⁻¹, 1, n)` contracts `n`-replicated lowering on `π` to lowering along `w`
on `(n : 𝕜)⁻¹ • π`. -/
theorem lowerWord_flatMap_replicate_map_smul {F : ι → Dual 𝕜 V} {x : ι → V}
    (w : List ι) (hx : ∀ i ∈ w, F i (x i) = 2) {a : 𝕜} (ha : 0 < a) {m n : ℕ}
    (hmn : (m : 𝕜) = a * n) (π : PLPath 𝕜 V) :
    lowerWord F x (w.flatMap fun i ↦ List.replicate m i) (π.map (a • LinearMap.id)) =
      (lowerWord F x (w.flatMap fun i ↦ List.replicate n i) π).map
        (·.map (a • LinearMap.id)) := by
  induction w generalizing π with
  | nil => simp
  | cons i w ih =>
    rw [List.flatMap_cons, lowerWord_append, lowerWord_replicate,
      lowerIter_map_smul (hx i List.mem_cons_self) ha hmn, List.flatMap_cons,
      lowerWord_append, lowerWord_replicate]
    cases lowerIter (F i) (x i) n π <;>
      simp [ih fun j hj ↦ hx j (List.mem_cons_of_mem i hj)]

/-- **Dilation similarity for raising words**: for `F i (x i) = 2` on every letter `i ∈ w`,
`0 < a`, and `(m : 𝕜) = a * n`, raising along `w.flatMap fun i ↦ List.replicate m i` on the
`a`-dilated path equals the `a`-dilation of raising along
`w.flatMap fun i ↦ List.replicate n i` on the original path. Specializing to
`(a, m, n) = ((n : 𝕜)⁻¹, 1, n)` contracts `n`-replicated raising on `π` to raising along `w` on
`(n : 𝕜)⁻¹ • π`. -/
theorem raiseWord_flatMap_replicate_map_smul {F : ι → Dual 𝕜 V} {x : ι → V}
    (w : List ι) (hx : ∀ i ∈ w, F i (x i) = 2) {a : 𝕜} (ha : 0 < a) {m n : ℕ}
    (hmn : (m : 𝕜) = a * n) (π : PLPath 𝕜 V) :
    raiseWord F x (w.flatMap fun i ↦ List.replicate m i) (π.map (a • LinearMap.id)) =
      (raiseWord F x (w.flatMap fun i ↦ List.replicate n i) π).map
        (·.map (a • LinearMap.id)) := by
  rw [raiseWord_eq_map_lowerWord_reverse, raiseWord_eq_map_lowerWord_reverse, ← map_reverse,
    lowerWord_flatMap_replicate_map_smul w hx ha hmn]
  simp only [Option.map_map, Function.comp_def, map_reverse]

/-- Lowering along a word commutes with positive-integer dilation upon repeating each letter `n`
times. -/
theorem lowerWord_flatMap_replicate_map_natCast_smul {F : ι → Dual 𝕜 V} {x : ι → V}
    (w : List ι) (hx : ∀ i ∈ w, F i (x i) = 2) {n : ℕ} (hn : 0 < n) (p : PLPath 𝕜 V) :
    lowerWord F x (w.flatMap fun i ↦ List.replicate n i) (p.map ((n : 𝕜) • LinearMap.id)) =
      (lowerWord F x w p).map (·.map ((n : 𝕜) • LinearMap.id)) := by
  simpa [List.flatMap_singleton] using
    lowerWord_flatMap_replicate_map_smul w hx (Nat.cast_pos.mpr hn) (m := n) (n := 1) (by simp) p

/-- Raising along a word commutes with positive-integer dilation upon repeating each letter `n`
times. -/
theorem raiseWord_flatMap_replicate_map_natCast_smul {F : ι → Dual 𝕜 V} {x : ι → V}
    (w : List ι) (hx : ∀ i ∈ w, F i (x i) = 2) {n : ℕ} (hn : 0 < n) (p : PLPath 𝕜 V) :
    raiseWord F x (w.flatMap fun i ↦ List.replicate n i) (p.map ((n : 𝕜) • LinearMap.id)) =
      (raiseWord F x w p).map (·.map ((n : 𝕜) • LinearMap.id)) := by
  simpa [List.flatMap_singleton] using
    raiseWord_flatMap_replicate_map_smul w hx (Nat.cast_pos.mpr hn) (m := n) (n := 1) (by simp) p

/-- Positive-scalar dilation preserves and reflects lowering along replicated words via
`(m : 𝕜) = a * n`. -/
theorem lowerWord_flatMap_replicate_map_smul_eq_some_iff {F : ι → Dual 𝕜 V} {x : ι → V}
    (w : List ι) (hx : ∀ i ∈ w, F i (x i) = 2) {a : 𝕜} (ha : 0 < a) {m n : ℕ}
    (hmn : (m : 𝕜) = a * n) {π ρ : PLPath 𝕜 V} :
    lowerWord F x (w.flatMap fun i ↦ List.replicate m i) (π.map (a • LinearMap.id)) =
        some (ρ.map (a • LinearMap.id)) ↔
      lowerWord F x (w.flatMap fun i ↦ List.replicate n i) π = some ρ := by
  rw [lowerWord_flatMap_replicate_map_smul w hx ha hmn, Option.map_eq_some_iff]
  simp [(map_smul_id_injective (V := V) ha.ne').eq_iff]

/-- Positive-scalar dilation preserves and reflects raising along replicated words via
`(m : 𝕜) = a * n`. -/
theorem raiseWord_flatMap_replicate_map_smul_eq_some_iff {F : ι → Dual 𝕜 V} {x : ι → V}
    (w : List ι) (hx : ∀ i ∈ w, F i (x i) = 2) {a : 𝕜} (ha : 0 < a) {m n : ℕ}
    (hmn : (m : 𝕜) = a * n) {π ρ : PLPath 𝕜 V} :
    raiseWord F x (w.flatMap fun i ↦ List.replicate m i) (π.map (a • LinearMap.id)) =
        some (ρ.map (a • LinearMap.id)) ↔
      raiseWord F x (w.flatMap fun i ↦ List.replicate n i) π = some ρ := by
  rw [raiseWord_flatMap_replicate_map_smul w hx ha hmn, Option.map_eq_some_iff]
  simp [(map_smul_id_injective (V := V) ha.ne').eq_iff]

/-- Dilation by `n > 0` preserves and reflects lowering along any word via `n`-fold letter
replication. -/
theorem lowerWord_flatMap_replicate_map_natCast_smul_eq_some_iff {F : ι → Dual 𝕜 V} {x : ι → V}
    (w : List ι) (hx : ∀ i ∈ w, F i (x i) = 2) {n : ℕ} (hn : 0 < n) {p q : PLPath 𝕜 V} :
    lowerWord F x (w.flatMap fun i ↦ List.replicate n i) (p.map ((n : 𝕜) • LinearMap.id)) =
        some (q.map ((n : 𝕜) • LinearMap.id)) ↔
      lowerWord F x w p = some q := by
  simpa [List.flatMap_singleton] using
    lowerWord_flatMap_replicate_map_smul_eq_some_iff w hx (Nat.cast_pos.mpr hn)
      (m := n) (n := 1) (by simp) (π := p) (ρ := q)

/-- Dilation by `n > 0` preserves and reflects raising along any word via `n`-fold letter
replication. -/
theorem raiseWord_flatMap_replicate_map_natCast_smul_eq_some_iff {F : ι → Dual 𝕜 V} {x : ι → V}
    (w : List ι) (hx : ∀ i ∈ w, F i (x i) = 2) {n : ℕ} (hn : 0 < n) {p q : PLPath 𝕜 V} :
    raiseWord F x (w.flatMap fun i ↦ List.replicate n i) (p.map ((n : 𝕜) • LinearMap.id)) =
        some (q.map ((n : 𝕜) • LinearMap.id)) ↔
      raiseWord F x w p = some q := by
  simpa [List.flatMap_singleton] using
    raiseWord_flatMap_replicate_map_smul_eq_some_iff w hx (Nat.cast_pos.mpr hn)
      (m := n) (n := 1) (by simp) (π := p) (ρ := q)

end DilationSimilarity

/-! ### Root-step walks and path-crystal similarity morphisms -/

section CrystalSimilarity

variable {ι X Y 𝕜 V : Type*} [AddCommGroup X] [AddCommGroup Y]
  {P : RootDatum ι X Y} {b : P.Base}
  [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [AddCommGroup V] [Module 𝕜 V]
  {f : X →+ V} {F : b.support → Dual 𝕜 V}

/-- Dilation by any natural number `n` (including `n = 0`, which sends both paths to `1`) preserves
finite sequences of simple-root raising and lowering steps. -/
theorem reflTransGen_rootStep_map_natCast_smul
    (hx : ∀ i : b.support, F i (f (P.root i)) = 2) (n : ℕ) {π π' : PLPath 𝕜 V}
    (h : ReflTransGen (RootStep b f F) π π') :
    ReflTransGen (RootStep b f F) (π.map ((n : 𝕜) • LinearMap.id))
      (π'.map ((n : 𝕜) • LinearMap.id)) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [Nat.cast_zero, zero_smul, map_zero_linearMap]
    exact .refl
  induction h with
  | refl => exact .refl
  | tail _ hstep ih =>
    obtain ⟨i, hstep | hstep⟩ := rootStep_iff.mp hstep
    · exact ih.trans <| reflTransGen_rootStep_of_raiseIter_eq_some <| by
        rw [raiseIter_map_natCast_smul (hx i) hn, hstep, Option.map_some]
    · exact ih.trans <| reflTransGen_rootStep_of_lowerIter_eq_some <| by
        rw [lowerIter_map_natCast_smul (hx i) hn, hstep, Option.map_some]

private theorem normalCrystalOn_wt_of_val_eq_map_natCast_smul {S T : Set (PLPath 𝕜 V)}
    (hf : Function.Injective f)
    (hF : ∀ (i : b.support) (x : X), F i (f x) = (P.coroot' i x : 𝕜))
    (hS : IsCrystalSet b f F S) (hT : IsCrystalSet b f F T)
    {n : ℕ} {π : S} {π' : T} (hπ' : π'.val = π.val.map ((n : 𝕜) • LinearMap.id)) :
    (normalCrystalOn hf hF hT).wt π' = n • (normalCrystalOn hf hF hS).wt π :=
  hf <| by
    rw [apply_normalCrystalOn_wt, hπ', map_nsmul, apply_normalCrystalOn_wt, endpoint_map,
      LinearMap.smul_apply, LinearMap.id_apply, Nat.cast_smul_eq_nsmul]

private theorem normalCrystalOn_ε_of_val_eq_map_natCast_smul {S T : Set (PLPath 𝕜 V)}
    (hf : Function.Injective f)
    (hF : ∀ (i : b.support) (x : X), F i (f x) = (P.coroot' i x : 𝕜))
    (hS : IsCrystalSet b f F S) (hT : IsCrystalSet b f F T)
    (i : b.support) {n : ℕ} {π : S} {π' : T}
    (hπ' : π'.val = π.val.map ((n : 𝕜) • LinearMap.id)) :
    (normalCrystalOn hf hF hT).ε i π' = n * (normalCrystalOn hf hF hS).ε i π :=
  Nat.cast_injective (R := 𝕜) <| by
    rw [cast_normalCrystalOn_ε, hπ', Nat.cast_mul, cast_normalCrystalOn_ε,
      minHeight_map_smul (Nat.cast_nonneg n), mul_neg]

private theorem unattach_normalCrystalOn_eIter_of_val_eq_map_natCast_smul {S T : Set (PLPath 𝕜 V)}
    (hf : Function.Injective f)
    (hF : ∀ (i : b.support) (x : X), F i (f x) = (P.coroot' i x : 𝕜))
    (hS : IsCrystalSet b f F S) (hT : IsCrystalSet b f F T)
    (i : b.support) {n : ℕ} (hn : 0 < n) {π : S} {π' : T}
    (hπ' : π'.val = π.val.map ((n : 𝕜) • LinearMap.id)) :
    ((normalCrystalOn hf hF hT).eIter i n π').unattach =
      (((normalCrystalOn hf hF hS).e i π).unattach).map (·.map ((n : 𝕜) • LinearMap.id)) := by
  rw [unattach_normalCrystalOn_eIter, hπ', unattach_normalCrystalOn_e,
    raiseIter_map_natCast_smul (apply_root_eq_two hF i) hn]

/-- Positive-integer dilation between crystal-admissible sets of paths assembles into a similarity
morphism of normal crystals. -/
noncomputable def dilationSimilarityHom {S T : Set (PLPath 𝕜 V)} (hf : Function.Injective f)
    (hF : ∀ (i : b.support) (x : X), F i (f x) = (P.coroot' i x : 𝕜))
    (hS : IsCrystalSet b f F S) (hT : IsCrystalSet b f F T)
    {n : ℕ} (hn : 0 < n) (hST : ∀ ⦃π⦄, π ∈ S → π.map ((n : 𝕜) • LinearMap.id) ∈ T) :
    NormalCrystal.SimilarityHom n (normalCrystalOn hf hF hS) (normalCrystalOn hf hF hT) where
  toFun π := ⟨π.val.map ((n : 𝕜) • LinearMap.id), hST π.property⟩
  wt_toFun _ := normalCrystalOn_wt_of_val_eq_map_natCast_smul hf hF hS hT rfl
  ε_toFun i _ := normalCrystalOn_ε_of_val_eq_map_natCast_smul hf hF hS hT i rfl
  eIter_toFun i _ := Option.unattach_inj.mp <| by
    simpa only [Option.unattach_map, Option.map_unattach_eq_map_val] using
      unattach_normalCrystalOn_eIter_of_val_eq_map_natCast_smul hf hF hS hT i hn rfl

@[simp]
theorem dilationSimilarityHom_apply {S T : Set (PLPath 𝕜 V)} (hf : Function.Injective f)
    (hF : ∀ (i : b.support) (x : X), F i (f x) = (P.coroot' i x : 𝕜))
    (hS : IsCrystalSet b f F S) (hT : IsCrystalSet b f F T)
    {n : ℕ} (hn : 0 < n) (hST : ∀ ⦃π⦄, π ∈ S → π.map ((n : 𝕜) • LinearMap.id) ∈ T) (π : S) :
    (dilationSimilarityHom hf hF hS hT hn hST π).val = π.val.map ((n : 𝕜) • LinearMap.id) := (rfl)

/-- Positive-integer dilation of crystal-admissible path sets is injective. -/
theorem dilationSimilarityHom_injective {S T : Set (PLPath 𝕜 V)} (hf : Function.Injective f)
    (hF : ∀ (i : b.support) (x : X), F i (f x) = (P.coroot' i x : 𝕜))
    (hS : IsCrystalSet b f F S) (hT : IsCrystalSet b f F T)
    {n : ℕ} (hn : 0 < n) (hST : ∀ ⦃π⦄, π ∈ S → π.map ((n : 𝕜) • LinearMap.id) ∈ T) :
    Function.Injective (dilationSimilarityHom hf hF hS hT hn hST) := fun _ _ h ↦
  Subtype.ext <| map_smul_id_injective (Nat.cast_pos.mpr hn).ne' <| congrArg Subtype.val h

/-- If the `n`-dilation of `π₀` is an integral path, then the `n`-dilation of every path reachable
from `π₀` by simple-root steps is also an integral path. -/
theorem IsIntegralPath.map_natCast_smul_of_reflTransGen_rootStep
    (hF : ∀ (i : b.support) (x : X), F i (f x) = (P.coroot' i x : 𝕜))
    {n : ℕ} {π₀ π : PLPath 𝕜 V}
    (h₀ : IsIntegralPath b f F (π₀.map ((n : 𝕜) • LinearMap.id)))
    (hwalk : ReflTransGen (RootStep b f F) π₀ π) :
    IsIntegralPath b f F (π.map ((n : 𝕜) • LinearMap.id)) :=
  h₀.of_reflTransGen_rootStep
    (reflTransGen_rootStep_map_natCast_smul (apply_root_eq_two hF) n hwalk)

private theorem reflTransGen_rootStep_of_mem_connectedComponentMk_map_natCast_smul
    (hf : Function.Injective f)
    (hF : ∀ (i : b.support) (x : X), F i (f x) = (P.coroot' i x : 𝕜))
    {n : ℕ} {x x' y : {π : PLPath 𝕜 V | IsIntegralPath b f F π}}
    (hx' : x.val.map ((n : 𝕜) • LinearMap.id) = x'.val)
    (hy : y ∈ (normalCrystal hf hF).graph.connectedComponentMk x) :
    ReflTransGen (RootStep b f F) x'.val (y.val.map ((n : 𝕜) • LinearMap.id)) :=
  hx' ▸ reflTransGen_rootStep_map_natCast_smul (apply_root_eq_two hF) n
    ((mem_supp_connectedComponentMk_normalCrystalOn_iff x y).mp hy)

/-- **Component similarity morphism on integral-path components**: whenever the `n`-dilation of an
integral path `x` equals an integral path `x'` (`n > 0`), positive-integer dilation embeds the
connected path crystal component `normalCrystalComponent hf hF x` into
`normalCrystalComponent hf hF x'` as an injective similarity morphism of scale factor `n`. -/
noncomputable def componentDilationSimilarityHom (hf : Function.Injective f)
    (hF : ∀ (i : b.support) (x : X), F i (f x) = (P.coroot' i x : 𝕜))
    {x x' : {π : PLPath 𝕜 V | IsIntegralPath b f F π}} {n : ℕ} (hn : 0 < n)
    (hx' : x.val.map ((n : 𝕜) • LinearMap.id) = x'.val) :
    NormalCrystal.SimilarityHom n
      (normalCrystalComponent hf hF x) (normalCrystalComponent hf hF x') where
  toFun y :=
    have hwalk := reflTransGen_rootStep_of_mem_connectedComponentMk_map_natCast_smul hf hF hx'
        y.property
    ⟨⟨y.val.val.map ((n : 𝕜) • LinearMap.id), x'.property.of_reflTransGen_rootStep hwalk⟩,
      (mem_supp_connectedComponentMk_normalCrystalOn_iff x' _).mpr hwalk⟩
  wt_toFun _ := by
    rw [NormalCrystal.component_wt, NormalCrystal.component_wt]
    exact normalCrystalOn_wt_of_val_eq_map_natCast_smul hf hF _ _ rfl
  ε_toFun i _ := by
    rw [NormalCrystal.component_ε, NormalCrystal.component_ε]
    exact normalCrystalOn_ε_of_val_eq_map_natCast_smul hf hF _ _ i rfl
  eIter_toFun i y := Option.unattach_inj.mp <| Option.unattach_inj.mp <| by
    rw [NormalCrystal.unattach_component_eIter,
      unattach_normalCrystalOn_eIter_of_val_eq_map_natCast_smul hf hF
        isCrystalSet_setOf_isIntegralPath _ i hn (π := y.val) rfl,
      ← NormalCrystal.unattach_component_e]
    simp only [Option.unattach_map, Option.map_unattach_eq_map_val]

@[simp]
theorem componentDilationSimilarityHom_apply (hf : Function.Injective f)
    (hF : ∀ (i : b.support) (x : X), F i (f x) = (P.coroot' i x : 𝕜))
    {x x' : {π : PLPath 𝕜 V | IsIntegralPath b f F π}} {n : ℕ} (hn : 0 < n)
    (hx' : x.val.map ((n : 𝕜) • LinearMap.id) = x'.val)
    (y : (normalCrystal hf hF).graph.connectedComponentMk x) :
    (componentDilationSimilarityHom hf hF hn hx' y).val.val = y.val.val.map ((n : 𝕜) • LinearMap.id)
        :=
  (rfl)

theorem componentDilationSimilarityHom_injective (hf : Function.Injective f)
    (hF : ∀ (i : b.support) (x : X), F i (f x) = (P.coroot' i x : 𝕜))
    {x x' : {π : PLPath 𝕜 V | IsIntegralPath b f F π}} {n : ℕ} (hn : 0 < n)
    (hx' : x.val.map ((n : 𝕜) • LinearMap.id) = x'.val) :
    Function.Injective (componentDilationSimilarityHom hf hF hn hx') :=
  fun _ _ h ↦ Subtype.ext <| Subtype.ext <|
    map_smul_id_injective (Nat.cast_pos.mpr hn).ne' <|
      congrArg (fun z ↦ z.val.val) h

/-- **Kashiwara–Littelmann similarity embedding `B(π_λ) ↪ B(π_{n λ})`** on straight-path crystal
components: for every integral straight path `straight 𝕜 (f lam)` and every `n > 0`, dilating paths
by `n` gives an injective similarity morphism of scale factor `n` from the connected component of
`straight 𝕜 (f lam)` to that of `straight 𝕜 (f (n • lam))`. -/
noncomputable def straightComponentDilationSimilarityHom (hf : Function.Injective f)
    (hF : ∀ (i : b.support) (x : X), F i (f x) = (P.coroot' i x : 𝕜))
    {lam : X} (hlam : IsIntegralPath b f F (straight 𝕜 (f lam))) {n : ℕ} (hn : 0 < n) :
    NormalCrystal.SimilarityHom n
      (normalCrystalComponent hf hF ⟨straight 𝕜 (f lam), hlam⟩)
      (normalCrystalComponent hf hF ⟨straight 𝕜 (f (n • lam)), hlam.straight_nsmul hF n⟩) :=
  componentDilationSimilarityHom hf hF hn <| by
    dsimp only
    rw [map_straight, LinearMap.smul_apply, LinearMap.id_apply, map_nsmul, Nat.cast_smul_eq_nsmul]

@[simp]
theorem straightComponentDilationSimilarityHom_apply (hf : Function.Injective f)
    (hF : ∀ (i : b.support) (x : X), F i (f x) = (P.coroot' i x : 𝕜))
    {lam : X} (hlam : IsIntegralPath b f F (straight 𝕜 (f lam))) {n : ℕ} (hn : 0 < n)
    (y : (normalCrystal hf hF).graph.connectedComponentMk ⟨straight 𝕜 (f lam), hlam⟩) :
    (straightComponentDilationSimilarityHom hf hF hlam hn y).val.val =
      y.val.val.map ((n : 𝕜) • LinearMap.id) :=
  (rfl)

theorem straightComponentDilationSimilarityHom_injective (hf : Function.Injective f)
    (hF : ∀ (i : b.support) (x : X), F i (f x) = (P.coroot' i x : 𝕜))
    {lam : X} (hlam : IsIntegralPath b f F (straight 𝕜 (f lam))) {n : ℕ} (hn : 0 < n) :
    Function.Injective (straightComponentDilationSimilarityHom hf hF hlam hn) :=
  componentDilationSimilarityHom_injective hf hF hn _

/-- Unconditional similarity embedding of scale factor `n > 0` on the connected path crystal
component of `straight 𝕜 (f (P.root i))` for any isolated simple node `i` (in particular on any
rank-one root datum), sending the length-`2` simple-root string into a string of length `2 n`. -/
noncomputable def simpleRootStringDilationSimilarityHom (hf : Function.Injective f)
    (hF : ∀ (i : b.support) (x : X), F i (f x) = (P.coroot' i x : 𝕜))
    (i : b.support) (hi : ∀ j : b.support, j ≠ i → P.pairing i.val j.val = 0)
    {n : ℕ} (hn : 0 < n) :
    NormalCrystal.SimilarityHom n
      (normalCrystalComponent hf hF
        ⟨straight 𝕜 (f (P.root i)), isIntegralPath_straight_root hF i hi⟩)
      (normalCrystalComponent hf hF
        ⟨straight 𝕜 (f (n • P.root i)),
          (isIntegralPath_straight_root hF i hi).straight_nsmul hF n⟩) :=
  straightComponentDilationSimilarityHom hf hF (isIntegralPath_straight_root hF i hi) hn

@[simp]
theorem simpleRootStringDilationSimilarityHom_apply (hf : Function.Injective f)
    (hF : ∀ (i : b.support) (x : X), F i (f x) = (P.coroot' i x : 𝕜))
    (i : b.support) (hi : ∀ j : b.support, j ≠ i → P.pairing i.val j.val = 0)
    {n : ℕ} (hn : 0 < n)
    (y : (normalCrystal hf hF).graph.connectedComponentMk
      ⟨straight 𝕜 (f (P.root i)), isIntegralPath_straight_root hF i hi⟩) :
    (simpleRootStringDilationSimilarityHom hf hF i hi hn y).val.val =
      y.val.val.map ((n : 𝕜) • LinearMap.id) :=
  (rfl)

theorem simpleRootStringDilationSimilarityHom_injective (hf : Function.Injective f)
    (hF : ∀ (i : b.support) (x : X), F i (f x) = (P.coroot' i x : 𝕜))
    (i : b.support) (hi : ∀ j : b.support, j ≠ i → P.pairing i.val j.val = 0)
    {n : ℕ} (hn : 0 < n) :
    Function.Injective (simpleRootStringDilationSimilarityHom hf hF i hi hn) :=
  straightComponentDilationSimilarityHom_injective hf hF
    (isIntegralPath_straight_root hF i hi) hn

end CrystalSimilarity

end TauCeti.PLPath

/-! ### Stretching similarity for Lakshmibai–Seshadri and cleared Bruhat-chain paths -/

namespace TauCeti.LSPath

open RootPairing

variable {ι M N 𝕜 V : Type*} [AddCommGroup M] [AddCommGroup N]
  {P : RootPairing ι ℤ M N} {b : P.Base} [Finite ι] [P.IsReduced]
  {lam μ : M} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [AddCommGroup V] [Module 𝕜 V]

section Stretch

variable (𝕜) (f : M →+ V)

/-- Stretching an LS path by `n > 0` multiplies its minimum height under any linear form by `n`. -/
@[simp]
theorem minHeight_toPLPath_stretch (π : LSPath P b lam) (n : ℕ) (hn : 0 < n)
    (F : Module.Dual 𝕜 V) :
    ((π.stretch n hn).toPLPath 𝕜 f).minHeight F = (n : 𝕜) * (π.toPLPath 𝕜 f).minHeight F := by
  rw [toPLPath_stretch, PLPath.minHeight_map_smul (Nat.cast_nonneg n)]

/-- Applying `lowerIter F x n` to a stretched LS path dilates the result of `lower F x` on the
original LS path. -/
theorem lowerIter_toPLPath_stretch {F : Module.Dual 𝕜 V} {x : V} (hx : F x = 2)
    (π : LSPath P b lam) {n : ℕ} (hn : 0 < n) :
    PLPath.lowerIter F x n ((π.stretch n hn).toPLPath 𝕜 f) =
      (PLPath.lower F x (π.toPLPath 𝕜 f)).map (·.map ((n : 𝕜) • LinearMap.id)) := by
  rw [toPLPath_stretch, PLPath.lowerIter_map_natCast_smul hx hn]

/-- Applying `raiseIter F x n` to a stretched LS path dilates the result of `raise F x` on the
original LS path. -/
theorem raiseIter_toPLPath_stretch {F : Module.Dual 𝕜 V} {x : V} (hx : F x = 2)
    (π : LSPath P b lam) {n : ℕ} (hn : 0 < n) :
    PLPath.raiseIter F x n ((π.stretch n hn).toPLPath 𝕜 f) =
      (PLPath.raise F x (π.toPLPath 𝕜 f)).map (·.map ((n : 𝕜) • LinearMap.id)) := by
  rw [toPLPath_stretch, PLPath.raiseIter_map_natCast_smul hx hn]

/-- `n`-fold lowering links the realizations of two stretched LS paths if and only if single-step
lowering links the realizations of the unstretched paths. -/
theorem lowerIter_toPLPath_stretch_eq_some_iff {F : Module.Dual 𝕜 V} {x : V} (hx : F x = 2)
    (π : LSPath P b lam) (ρ : LSPath P b μ) {n : ℕ} (hn : 0 < n) :
    PLPath.lowerIter F x n ((π.stretch n hn).toPLPath 𝕜 f) =
        some ((ρ.stretch n hn).toPLPath 𝕜 f) ↔
      PLPath.lower F x (π.toPLPath 𝕜 f) = some (ρ.toPLPath 𝕜 f) := by
  rw [toPLPath_stretch, toPLPath_stretch, PLPath.lowerIter_map_natCast_smul_eq_some_iff hx hn]

/-- `n`-fold raising links the realizations of two stretched LS paths if and only if single-step
raising links the realizations of the unstretched paths. -/
theorem raiseIter_toPLPath_stretch_eq_some_iff {F : Module.Dual 𝕜 V} {x : V} (hx : F x = 2)
    (π : LSPath P b lam) (ρ : LSPath P b μ) {n : ℕ} (hn : 0 < n) :
    PLPath.raiseIter F x n ((π.stretch n hn).toPLPath 𝕜 f) =
        some ((ρ.stretch n hn).toPLPath 𝕜 f) ↔
      PLPath.raise F x (π.toPLPath 𝕜 f) = some (ρ.toPLPath 𝕜 f) := by
  rw [toPLPath_stretch, toPLPath_stretch, PLPath.raiseIter_map_natCast_smul_eq_some_iff hx hn]

/-- Lowering a stretched LS path along an `n`-replicated word dilates lowering the original LS path
along the un-replicated word. -/
theorem lowerWord_flatMap_replicate_toPLPath_stretch {α : Type*}
    {F : α → Module.Dual 𝕜 V} {x : α → V} (w : List α) (hx : ∀ i ∈ w, F i (x i) = 2)
    (π : LSPath P b lam) {n : ℕ} (hn : 0 < n) :
    PLPath.lowerWord F x (w.flatMap fun i ↦ List.replicate n i)
        ((π.stretch n hn).toPLPath 𝕜 f) =
      (PLPath.lowerWord F x w (π.toPLPath 𝕜 f)).map (·.map ((n : 𝕜) • LinearMap.id)) := by
  rw [toPLPath_stretch, PLPath.lowerWord_flatMap_replicate_map_natCast_smul w hx hn]

/-- Raising a stretched LS path along an `n`-replicated word dilates raising the original LS path
along the un-replicated word. -/
theorem raiseWord_flatMap_replicate_toPLPath_stretch {α : Type*}
    {F : α → Module.Dual 𝕜 V} {x : α → V} (w : List α) (hx : ∀ i ∈ w, F i (x i) = 2)
    (π : LSPath P b lam) {n : ℕ} (hn : 0 < n) :
    PLPath.raiseWord F x (w.flatMap fun i ↦ List.replicate n i)
        ((π.stretch n hn).toPLPath 𝕜 f) =
      (PLPath.raiseWord F x w (π.toPLPath 𝕜 f)).map (·.map ((n : 𝕜) • LinearMap.id)) := by
  rw [toPLPath_stretch, PLPath.raiseWord_flatMap_replicate_map_natCast_smul w hx hn]

/-- Lowering along an `n`-replicated word links two stretched LS paths if and only if lowering along
the original word links the unstretched paths. -/
theorem lowerWord_flatMap_replicate_toPLPath_stretch_eq_some_iff {α : Type*}
    {F : α → Module.Dual 𝕜 V} {x : α → V} (w : List α) (hx : ∀ i ∈ w, F i (x i) = 2)
    (π : LSPath P b lam) (ρ : LSPath P b μ) {n : ℕ} (hn : 0 < n) :
    PLPath.lowerWord F x (w.flatMap fun i ↦ List.replicate n i)
        ((π.stretch n hn).toPLPath 𝕜 f) = some ((ρ.stretch n hn).toPLPath 𝕜 f) ↔
      PLPath.lowerWord F x w (π.toPLPath 𝕜 f) = some (ρ.toPLPath 𝕜 f) := by
  rw [toPLPath_stretch, toPLPath_stretch,
    PLPath.lowerWord_flatMap_replicate_map_natCast_smul_eq_some_iff w hx hn]

/-- Raising along an `n`-replicated word links two stretched LS paths if and only if raising along
the original word links the unstretched paths. -/
theorem raiseWord_flatMap_replicate_toPLPath_stretch_eq_some_iff {α : Type*}
    {F : α → Module.Dual 𝕜 V} {x : α → V} (w : List α) (hx : ∀ i ∈ w, F i (x i) = 2)
    (π : LSPath P b lam) (ρ : LSPath P b μ) {n : ℕ} (hn : 0 < n) :
    PLPath.raiseWord F x (w.flatMap fun i ↦ List.replicate n i)
        ((π.stretch n hn).toPLPath 𝕜 f) = some ((ρ.stretch n hn).toPLPath 𝕜 f) ↔
      PLPath.raiseWord F x w (π.toPLPath 𝕜 f) = some (ρ.toPLPath 𝕜 f) := by
  rw [toPLPath_stretch, toPLPath_stretch,
    PLPath.raiseWord_flatMap_replicate_map_natCast_smul_eq_some_iff w hx hn]

end Stretch

section RationalChain

variable {l : ℕ}
  (dir : Fin (l + 1) →
    {w // (weylCoxeterSystem P b).IsMinimalCosetRep (P.wallIndices b lam) w})
  (hdir : ∀ j : Fin l,
    (weylCoxeterSystem P b).BruhatLE (dir j.succ).val (dir j.castSucc).val)
  (hne : ∀ j : Fin l, dir j.succ ≠ dir j.castSucc)
  (time : Fin (l + 2) → ℚ) (hzero : time 0 = 0) (hlast : time (Fin.last _) = 1)
  (htime : StrictMono time) (n : ℕ) (hn : 0 < n)
  (hden : ∀ j : Fin l, (time j.castSucc.succ).den ∣ n)
  (𝕜) (f : M →+ V)

/-- Applying `lowerIter F x n` to the LS path `ofBruhatChain` obtained by clearing break
denominators dilates single-step lowering on the original rational Bruhat-chain path. -/
theorem lowerIter_toPLPath_ofBruhatChain {F : Module.Dual 𝕜 V} {x : V} (hx : F x = 2) :
    PLPath.lowerIter F x n
        ((ofBruhatChain dir hdir hne time hzero hlast htime n hn hden).toPLPath 𝕜 f) =
      (PLPath.lower F x (PLPath.ofSegments 𝕜 (List.ofFn fun j : Fin (l + 1) ↦
        ((time j.succ - time j.castSucc : ℚ) : 𝕜) • f ((dir j).val • lam)))).map
          (·.map ((n : 𝕜) • LinearMap.id)) := by
  rw [toPLPath_ofBruhatChain, PLPath.lowerIter_map_natCast_smul hx hn]

/-- Applying `raiseIter F x n` to `ofBruhatChain` dilates single-step raising on the original
rational Bruhat-chain path. -/
theorem raiseIter_toPLPath_ofBruhatChain {F : Module.Dual 𝕜 V} {x : V} (hx : F x = 2) :
    PLPath.raiseIter F x n
        ((ofBruhatChain dir hdir hne time hzero hlast htime n hn hden).toPLPath 𝕜 f) =
      (PLPath.raise F x (PLPath.ofSegments 𝕜 (List.ofFn fun j : Fin (l + 1) ↦
        ((time j.succ - time j.castSucc : ℚ) : 𝕜) • f ((dir j).val • lam)))).map
          (·.map ((n : 𝕜) • LinearMap.id)) := by
  rw [toPLPath_ofBruhatChain, PLPath.raiseIter_map_natCast_smul hx hn]

/-- The denominator-cleared LS path `ofBruhatChain` is obtained from `straight (n • lam)` by
lowering along an `n`-replicated word if and only if the original rational Bruhat-chain path is
obtained from `PLPath.straight 𝕜 (f lam)` by lowering along the un-replicated word. -/
theorem lowerWord_flatMap_replicate_toPLPath_ofBruhatChain_eq_some_iff {α : Type*}
    {F : α → Module.Dual 𝕜 V} {x : α → V} (w : List α) (hx : ∀ i ∈ w, F i (x i) = 2) :
    PLPath.lowerWord F x (w.flatMap fun i ↦ List.replicate n i)
        ((straight (n • lam) : LSPath P b (n • lam)).toPLPath 𝕜 f) =
      some ((ofBruhatChain dir hdir hne time hzero hlast htime n hn hden).toPLPath 𝕜 f) ↔
    PLPath.lowerWord F x w (PLPath.straight 𝕜 (f lam)) =
      some (PLPath.ofSegments 𝕜 (List.ofFn fun j : Fin (l + 1) ↦
        ((time j.succ - time j.castSucc : ℚ) : 𝕜) • f ((dir j).val • lam))) := by
  rw [toPLPath_straight_nsmul, toPLPath_ofBruhatChain,
    PLPath.lowerWord_flatMap_replicate_map_natCast_smul_eq_some_iff w hx hn]

/-- Dual raising criterion for `ofBruhatChain`: raising `ofBruhatChain` along an `n`-replicated
word reaches `straight (n • lam)` if and only if raising the original rational Bruhat-chain path
along the un-replicated word reaches `PLPath.straight 𝕜 (f lam)`. -/
theorem raiseWord_flatMap_replicate_toPLPath_ofBruhatChain_eq_some_iff {α : Type*}
    {F : α → Module.Dual 𝕜 V} {x : α → V} (w : List α) (hx : ∀ i ∈ w, F i (x i) = 2) :
    PLPath.raiseWord F x (w.flatMap fun i ↦ List.replicate n i)
        ((ofBruhatChain dir hdir hne time hzero hlast htime n hn hden).toPLPath 𝕜 f) =
      some ((straight (n • lam) : LSPath P b (n • lam)).toPLPath 𝕜 f) ↔
    PLPath.raiseWord F x w (PLPath.ofSegments 𝕜 (List.ofFn fun j : Fin (l + 1) ↦
        ((time j.succ - time j.castSucc : ℚ) : 𝕜) • f ((dir j).val • lam))) =
      some (PLPath.straight 𝕜 (f lam)) := by
  rw [toPLPath_straight_nsmul, toPLPath_ofBruhatChain,
    PLPath.raiseWord_flatMap_replicate_map_natCast_smul_eq_some_iff w hx hn]

end RationalChain

end TauCeti.LSPath

section CrystalComparison

open scoped TensorProduct

namespace TauCeti.LSPath

open RootPairing

variable {ι X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
  {P : RootDatum ι X Y} {b : P.Base} [Finite ι] [P.IsReduced] {lam : X}

/-- **Kashiwara–Littelmann similarity morphism `B(λ) → B(n • λ)`** on the normal crystal of
Lakshmibai–Seshadri paths, induced by `LSPath.stretch`. -/
noncomputable def stretchSimilarityHom (hlam : lam ∈ dominantChamber P b) {n : ℕ} (hn : 0 < n) :
    NormalCrystal.SimilarityHom n (crystal hlam)
      (crystal (nsmul_mem_dominantChamber P b n hlam)) where
  toFun π := π.stretch n hn
  wt_toFun π := by
    simp only [crystal_wt]
    exact (weight_eq_iff_endpoint_toRatPLPath (π.stretch n hn)).mpr <| by
      rw [toRatPLPath_def, endpoint_toPLPath_stretch, ← toRatPLPath_def, endpoint_toRatPLPath,
        Nat.cast_smul_eq_nsmul, map_nsmul]
  ε_toFun i π := by
    have hF : ∀ x, Module.Dual.baseChange ℚ (P.coroot' i)
        ((TensorProduct.mk ℤ ℚ X 1).toAddMonoidHom x) = (P.coroot' i x : ℚ) :=
      Module.Dual.baseChange_apply_toAddMonoidHom_mk_one (P.coroot' i)
    rw [← Nat.cast_inj (R := ℚ), Nat.cast_mul, ← neg_inj,
      ← minHeight_toPLPath_eq_neg_crystal_ε (nsmul_mem_dominantChamber P b n hlam)
        (TensorProduct.mk ℤ ℚ X 1).toAddMonoidHom i (Module.Dual.baseChange ℚ (P.coroot' i)) hF,
      minHeight_toPLPath_stretch,
      minHeight_toPLPath_eq_neg_crystal_ε hlam (TensorProduct.mk ℤ ℚ X 1).toAddMonoidHom i
        (Module.Dual.baseChange ℚ (P.coroot' i)) hF]
    ring
  eIter_toFun i π := by
    have hF : ∀ x, Module.Dual.baseChange ℚ (P.coroot' i)
        ((TensorProduct.mk ℤ ℚ X 1).toAddMonoidHom x) = (P.coroot' i x : ℚ) :=
      Module.Dual.baseChange_apply_toAddMonoidHom_mk_one (P.coroot' i)
    have hroot : Module.Dual.baseChange ℚ (P.coroot' i)
        ((TensorProduct.mk ℤ ℚ X 1).toAddMonoidHom (P.root i)) = (2 : ℚ) := by
      rw [hF, P.root_coroot'_eq_pairing, P.pairing_same, Int.cast_ofNat]
    apply Option.map_injective (toRatPLPath_injective (nsmul_mem_dominantChamber P b n hlam))
    rw [toRatPLPath_eq,
      ← raiseIter_toPLPath (nsmul_mem_dominantChamber P b n hlam)
        (TensorProduct.mk ℤ ℚ X 1).toAddMonoidHom i (Module.Dual.baseChange ℚ (P.coroot' i)) hF,
      toPLPath_stretch, PLPath.raiseIter_map_natCast_smul hroot hn,
      raise_toPLPath hlam (TensorProduct.mk ℤ ℚ X 1).toAddMonoidHom i
        (Module.Dual.baseChange ℚ (P.coroot' i)) hF,
      Option.map_map, Option.map_map]
    refine congrArg (Option.map · _) (funext fun ρ ↦ ?_)
    simp [toPLPath_stretch]

@[simp]
theorem stretchSimilarityHom_apply (hlam : lam ∈ dominantChamber P b) {n : ℕ} (hn : 0 < n)
    (π : LSPath P b lam) :
    stretchSimilarityHom hlam hn π = π.stretch n hn := (rfl)

/-- Rigidity of similarity morphisms out of `B(λ)`: any two scale-factor-`n` similarity morphisms
out of `crystal hlam` agreeing on the straight path are equal. -/
theorem eq_of_similarityHom_apply_straight_eq {B' : Type*} {d : NormalCrystal P b B'} {n : ℕ}
    (hlam : lam ∈ dominantChamber P b)
    {ψ₁ ψ₂ : NormalCrystal.SimilarityHom n (crystal hlam) d}
    (hstraight : ψ₁ (straight lam) = ψ₂ (straight lam)) :
    ψ₁ = ψ₂ :=
  NormalCrystal.SimilarityHom.eq_of_apply_eq_of_forall_exists_fWord_eq_some hstraight
    (exists_fWord_straight_eq_some hlam)

/-- Automatic injectivity of similarity morphisms out of `B(λ)` (in particular of
`LSPath.stretchSimilarityHom`). -/
theorem similarityHom_injective {B' : Type*} {d : NormalCrystal P b B'} {n : ℕ}
    (hlam : lam ∈ dominantChamber P b)
    (ψ : NormalCrystal.SimilarityHom n (crystal hlam) d) :
    Function.Injective ψ :=
  ψ.injective_of_forall_exists_fWord_eq_some (exists_fWord_straight_eq_some hlam)

end TauCeti.LSPath

end CrystalComparison
