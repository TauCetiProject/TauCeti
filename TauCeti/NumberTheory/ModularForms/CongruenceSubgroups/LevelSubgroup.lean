/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

-- `CongruenceSubgroup.Gamma0`, `Gamma1` and `Gamma` occur in the statements below.
public import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
-- `ZMod.unitsMap` occurs in the statements below.
public import Mathlib.Data.ZMod.Units
-- `TauCeti.GL2Borel`, `TauCeti.GL2Gamma1` and `TauCeti.GL2Gamma1Mu` occur in the statements
-- below.
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Borel
-- The split and nonsplit Cartan subgroups and their normalizers occur in the statements below.
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.SplitCartan
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.NonSplitCartan
-- `Subgroup.projectiveIndex` occurs in the statements below.
public import TauCeti.NumberTheory.ModularForms.ArithmeticSubgroups
-- The indices of `Γ₀(N)` and `Γ₁(N)` in `SL(2, ℤ)`, and strong approximation for `SL₂`.
import TauCeti.NumberTheory.ModularForms.CongruenceSubgroups.Basic
-- `Matrix.GeneralLinearGroup.map_neg`: reduction commutes with negation.
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Map
-- The field structure of `ZMod 13`, used to evaluate the Cartan degrees at `ℓ = 13`.
import Mathlib.Algebra.Field.ZMod

/-!
# Level subgroups of `GL₂(ℤ / N)`

A level of a modular curve is a subgroup `H` of `GL₂(ℤ / N)`: a level-`H` structure on an
elliptic curve `E` is an `H`-orbit of ordered bases `(P, Q)` of `E[N]`, on which a matrix acts on
the right by `(P, Q) • !![a, b; c, d] = (a P + c Q, b P + d Q)`. The standard levels are the
following subgroups, whose preimages in `SL(2, ℤ)` are the congruence subgroups:

* the trivial subgroup, for `Γ(N)` (full level);
* `TauCeti.GL2Gamma1 (ZMod N) = {a = 1, c = 0}`, the stabiliser of `P`, for `Γ₁(N)`;
* `TauCeti.GL2Borel (ZMod N) = {c = 0}`, the stabiliser of the line through `P`, for `Γ₀(N)`;
* `TauCeti.GL2Gamma1Mu (ZMod N) = {c = 0, d = 1}`, whose structures are the embeddings
  `μ_N ↪ E[N]` (the convention of Calegari and Geraghty), for `Γ₁(N)` again.

This file checks these against Mathlib's congruence subgroups: the preimage of each under the
reduction `SL(2, ℤ) → GL₂(ℤ / N)` is `Γ(N)`, `Γ₁(N)`, `Γ₀(N)` and `Γ₁(N)` respectively. The
reduction has image `SL₂(ℤ / N)` (strong approximation), so for a level `H` whose determinant is
surjective onto `(ℤ / N)ˣ` the index of `H` in `GL₂(ℤ / N)` is the index of its preimage in
`SL(2, ℤ)`. Hence `[GL₂(ℤ / N) : B] = [SL(2, ℤ) : Γ₀(N)] = N ∏_{p ∣ N} (1 + 1/p)` and
`[GL₂(ℤ / N) : Γ₁] = [GL₂(ℤ / N) : Γ₁^μ] = [SL(2, ℤ) : Γ₁(N)]`.

The degree of the modular curve `X_H` over the `j`-line is the projective index
`[GL₂(ℤ / N) : ±H]` (`Subgroup.projectiveIndex`), not the index: the two agree for `Γ₀`, which
contains `-1`, while for `Γ₁` and `N ≥ 3` the index is twice the projective index. For a prime
`p` this gives the degrees `p + 1` of `X₀(p)` and `(p² - 1) / 2` of `X₁(p)` for `p ≥ 3`. For a
prime `ℓ`, the Cartan levels `TauCeti.diagonalTorus`, `TauCeti.GL2SplitCartanNormalizer`,
`TauCeti.GL2NonSplitCartan` and `TauCeti.GL2NonSplitCartanNormalizer` all contain `-1`, and give
the degrees `ℓ (ℓ + 1)`, `ℓ (ℓ + 1) / 2`, `ℓ (ℓ - 1)` and `ℓ (ℓ - 1) / 2`: `91` and `78` for the
two normalizers at `ℓ = 13`.

The index, the projective index and the determinant image of a level are unchanged by
conjugation in `GL₂(ℤ / N)`: by `Subgroup.index_smul`, `Subgroup.projectiveIndex_pointwise_smul`
and `Subgroup.map_det_pointwise_smul` respectively.

A level at modulus `n` is also a level at every multiple `m` of `n`, through its preimage under
the reduction `GL₂(ℤ / m) → GL₂(ℤ / n)`. This reduction is surjective for `m ≠ 0`
(`TauCeti.GL2.map_castHom_surjective`), so the preimage has the same index
(Mathlib's `Subgroup.index_comap_of_surjective`) and the same projective index. Its determinant
image is the full preimage of that of `H` under `(ℤ / m)ˣ → (ℤ / n)ˣ`
(`TauCeti.GL2.map_det_comap_map_castHom`); these are subgroups at different moduli and are not
equal in general.

## Main results

* `TauCeti.range_mapGL_zmod`: the reduction `SL(2, ℤ) → GL₂(ℤ / N)` has image `SL₂(ℤ / N)`.
* `TauCeti.index_comap_mapGL_zmod`: a level whose determinant is surjective has the same index as
  its preimage in `SL(2, ℤ)`.
* `TauCeti.comap_mapGL_GL2Borel`, `TauCeti.comap_mapGL_GL2Gamma1`, `TauCeti.ker_mapGL_zmod`: the
  preimages of the standard levels are `Γ₀(N)`, `Γ₁(N)` and `Γ(N)`.
* `TauCeti.comap_mapGL_GL2Gamma1Mu`: the preimage of `Γ₁^μ` is also `Γ₁(N)`.
* `TauCeti.index_GL2Borel_zmod`, `TauCeti.index_GL2Gamma1_zmod`, `TauCeti.index_GL2Gamma1Mu_zmod`:
  their indices.
* `TauCeti.projectiveIndex_GL2Borel_zmod_prime`, `TauCeti.two_mul_projectiveIndex_GL2Gamma1_zmod`,
  `TauCeti.two_mul_projectiveIndex_GL2Gamma1Mu_zmod`: their projective indices.
* `TauCeti.projectiveIndex_diagonalTorus_two`,
  `TauCeti.two_mul_projectiveIndex_GL2SplitCartanNormalizer`,
  `TauCeti.projectiveIndex_GL2NonSplitCartan`,
  `TauCeti.two_mul_projectiveIndex_GL2NonSplitCartanNormalizer`: the projective indices of the
  Cartan levels over a finite field, and
  `TauCeti.projectiveIndex_GL2SplitCartanNormalizer_zmod_thirteen`,
  `TauCeti.projectiveIndex_GL2NonSplitCartanNormalizer_zmod_thirteen`: the values `91` and `78`.
* `TauCeti.GL2.map_castHom_surjective`: the reduction `GL₂(ℤ / m) → GL₂(ℤ / n)` is surjective for
  `n ∣ m` and `m ≠ 0`.
* `TauCeti.GL2.projectiveIndex_comap_map_castHom`, `TauCeti.GL2.map_det_comap_map_castHom`: the
  projective index and the determinant image of a level pulled back to a multiple modulus.

## References

* K. Česnavičius, *A modular description of `X₀(n)`*, Algebra Number Theory 11 (2017), §4.1.
* D. Zywina, *On the possible images of the mod `ℓ` representations associated to elliptic curves
  over `ℚ`*, arXiv:1508.07660, §3.2.
* F. Diamond and J. Shurman, *A First Course in Modular Forms*, GTM 228, §1.2 and §3.1.
* F. Calegari and D. Geraghty, *Modularity lifting beyond the Taylor–Wiles method*, Invent. Math.
  211 (2018), arXiv:1207.4224, for the `Γ₁^μ` level structures `μ_N ↪ E[N]`.
-/

public section

open Matrix Matrix.SpecialLinearGroup CongruenceSubgroup

open scoped MatrixGroups

namespace TauCeti

section Reduction

variable (N : ℕ)

/-- **The image of `SL(2, ℤ)` in `GL₂(ℤ / N)` is `SL₂(ℤ / N)`**: the matrices of determinant `1`.
This is strong approximation for `SL₂`, `Matrix.SpecialLinearGroup.map_intCast_zmod_surjective`. -/
theorem range_mapGL_zmod :
    (mapGL (ZMod N) : SL(2, ℤ) →* GL (Fin 2) (ZMod N)).range = GeneralLinearGroup.det.ker := by
  rw [mapGL, MonoidHom.range_comp, MonoidHom.range_eq_top_of_surjective _ (by
    simpa only [algebraMap_int_eq] using map_intCast_zmod_surjective (d := N)),
    ← MonoidHom.range_eq_map, range_toGL_eq_ker_det]

variable {N}

/-- **A level with surjective determinant has the index of its preimage in `SL(2, ℤ)`.** If
`det : H → (ℤ / N)ˣ` is surjective, then `H` meets every coset of `SL₂(ℤ / N)`, so its index in
`GL₂(ℤ / N)` is its relative index in `SL₂(ℤ / N)`, the image of `SL(2, ℤ)`. -/
theorem index_comap_mapGL_zmod {H : Subgroup (GL (Fin 2) (ZMod N))}
    (hH : H.map GeneralLinearGroup.det = ⊤) :
    (H.comap (mapGL (R := ℤ) (ZMod N))).index = H.index := by
  have hsup : H ⊔ (GeneralLinearGroup.det : GL (Fin 2) (ZMod N) →* _).ker = ⊤ := by
    rw [← Subgroup.comap_map_eq, hH, Subgroup.comap_top]
  rw [Subgroup.index_comap, range_mapGL_zmod,
    ← Subgroup.relIndex_sup_of_le_normalizer Subgroup.le_normalizer_of_normal, hsup,
    Subgroup.relIndex_top_right]

variable (N)

/-- The preimage in `SL(2, ℤ)` of the upper-triangular matrices modulo `N` is `Γ₀(N)`. -/
@[simp]
theorem comap_mapGL_GL2Borel : (GL2Borel (ZMod N)).comap (mapGL (ZMod N)) = Gamma0 N := by
  ext γ
  simp [Gamma0_mem]

/-- The preimage in `SL(2, ℤ)` of `TauCeti.GL2Gamma1 (ZMod N)` is `Γ₁(N)`. In `SL(2, ℤ)` the two
conditions `a ≡ 1` and `c ≡ 0` force the third condition `d ≡ 1` of `Γ₁(N)` through the
determinant. -/
@[simp]
theorem comap_mapGL_GL2Gamma1 : (GL2Gamma1 (ZMod N)).comap (mapGL (ZMod N)) = Gamma1 N := by
  ext γ
  simp only [Subgroup.mem_comap, GL2Gamma1.mem_iff, mapGL_coe_matrix, algebraMap_int_eq,
    map_apply_coe, Matrix.map_apply, Int.coe_castRingHom, Gamma1_mem]
  refine ⟨fun ⟨h₀, h₁⟩ ↦ ⟨h₀, ?_, h₁⟩, fun ⟨h₀, _, h₁⟩ ↦ ⟨h₀, h₁⟩⟩
  have hdet : ((γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 : ℤ) : ZMod N) = 1 := by
    rw [← det_fin_two, γ.det_coe, Int.cast_one]
  push_cast at hdet
  simpa [h₀, h₁] using hdet

/-- The kernel of the reduction `SL(2, ℤ) → GL₂(ℤ / N)`, the preimage of the trivial level, is
`Γ(N)`. -/
@[simp]
theorem ker_mapGL_zmod : (mapGL (R := ℤ) (n := Fin 2) (ZMod N)).ker = Gamma N := by
  ext γ
  simp only [MonoidHom.mem_ker, Gamma_mem, Units.ext_iff, Units.val_one,
    mapGL_coe_matrix, ← Matrix.ext_iff, Fin.forall_fin_two, algebraMap_int_eq, one_apply_eq,
    one_apply_ne zero_ne_one, one_apply_ne one_ne_zero]
  tauto

/-- **`[GL₂(ℤ / N) : B] = [SL(2, ℤ) : Γ₀(N)]`**, which is `N ∏_{p ∣ N} (1 + 1/p)` by
`CongruenceSubgroup.Gamma0_index_mul_prod_primeFactors`. -/
theorem index_GL2Borel_zmod : (GL2Borel (ZMod N)).index = (Gamma0 N).index := by
  rw [← comap_mapGL_GL2Borel, index_comap_mapGL_zmod GL2Borel.map_det]

/-- **`[GL₂(ℤ / N) : Γ₁] = [SL(2, ℤ) : Γ₁(N)]`**, which is `φ(N) [SL(2, ℤ) : Γ₀(N)]` by
`CongruenceSubgroup.Gamma1_index`. -/
theorem index_GL2Gamma1_zmod : (GL2Gamma1 (ZMod N)).index = (Gamma1 N).index := by
  rw [← comap_mapGL_GL2Gamma1, index_comap_mapGL_zmod GL2Gamma1.map_det]

/-- **The degree of `X₀(N)` over the `j`-line**: as `-1` is upper triangular, the projective index
of the upper-triangular level is its index `[SL(2, ℤ) : Γ₀(N)]`. -/
theorem projectiveIndex_GL2Borel_zmod :
    (GL2Borel (ZMod N)).projectiveIndex = (Gamma0 N).index := by
  rw [Subgroup.projectiveIndex_eq_index GL2Borel.neg_one_mem, index_GL2Borel_zmod]

/-- **The degree of `X₀(p)` over the `j`-line is `p + 1`.** -/
theorem projectiveIndex_GL2Borel_zmod_prime {p : ℕ} (hp : p.Prime) :
    (GL2Borel (ZMod p)).projectiveIndex = p + 1 := by
  rw [projectiveIndex_GL2Borel_zmod, Gamma0_prime_index p hp]

/-- **The degree of `X₁(N)` over the `j`-line, for `N ≥ 3`**: there `-1 ∉ Γ₁`, so the index
`[SL(2, ℤ) : Γ₁(N)]` is twice the projective index. -/
theorem two_mul_projectiveIndex_GL2Gamma1_zmod (hN : 3 ≤ N) :
    2 * (GL2Gamma1 (ZMod N)).projectiveIndex = (Gamma1 N).index := by
  have : Fact (2 < N) := ⟨hN⟩
  rw [Subgroup.two_mul_projectiveIndex (GL2Gamma1.neg_one_mem_iff.not.mpr ZMod.neg_one_ne_one),
    index_GL2Gamma1_zmod]

/-- **The degree of `X₁(p)` over the `j`-line is `(p² - 1) / 2`** for an odd prime `p`. -/
theorem two_mul_projectiveIndex_GL2Gamma1_zmod_prime {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    2 * (GL2Gamma1 (ZMod p)).projectiveIndex = (p - 1) * (p + 1) := by
  have : Fact p.Prime := ⟨hp⟩
  rw [two_mul_projectiveIndex_GL2Gamma1_zmod p (by have := hp.two_le; omega), Gamma1_index,
    Gamma0_prime_index p hp, Nat.card_eq_fintype_card, ZMod.card_units_eq_totient,
    Nat.totient_prime hp]

/-- The preimage in `SL(2, ℤ)` of `TauCeti.GL2Gamma1Mu (ZMod N)` is `Γ₁(N)`. In `SL(2, ℤ)` the two
conditions `c ≡ 0` and `d ≡ 1` force the third condition `a ≡ 1` of `Γ₁(N)` through the
determinant. -/
@[simp]
theorem comap_mapGL_GL2Gamma1Mu : (GL2Gamma1Mu (ZMod N)).comap (mapGL (ZMod N)) = Gamma1 N := by
  ext γ
  simp only [Subgroup.mem_comap, GL2Gamma1Mu.mem_iff, mapGL_coe_matrix, algebraMap_int_eq,
    map_apply_coe, Matrix.map_apply, Int.coe_castRingHom, Gamma1_mem]
  refine ⟨fun ⟨h₁, h₀⟩ ↦ ⟨?_, h₁, h₀⟩, fun ⟨_, h₁, h₀⟩ ↦ ⟨h₁, h₀⟩⟩
  have hdet : ((γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 : ℤ) : ZMod N) = 1 := by
    rw [← det_fin_two, γ.det_coe, Int.cast_one]
  push_cast at hdet
  simpa [h₀, h₁] using hdet

/-- **`[GL₂(ℤ / N) : Γ₁^μ] = [SL(2, ℤ) : Γ₁(N)]`**. -/
theorem index_GL2Gamma1Mu_zmod : (GL2Gamma1Mu (ZMod N)).index = (Gamma1 N).index := by
  rw [← comap_mapGL_GL2Gamma1Mu, index_comap_mapGL_zmod GL2Gamma1Mu.map_det]

/-- **The degree of the `Γ₁^μ(N)` curve over the `j`-line, for `N ≥ 3`**: as for `Γ₁`, there
`-1 ∉ Γ₁^μ`, so the index `[SL(2, ℤ) : Γ₁(N)]` is twice the projective index. -/
theorem two_mul_projectiveIndex_GL2Gamma1Mu_zmod (hN : 3 ≤ N) :
    2 * (GL2Gamma1Mu (ZMod N)).projectiveIndex = (Gamma1 N).index := by
  have : Fact (2 < N) := ⟨hN⟩
  rw [Subgroup.two_mul_projectiveIndex (GL2Gamma1Mu.neg_one_mem_iff.not.mpr ZMod.neg_one_ne_one),
    index_GL2Gamma1Mu_zmod]

end Reduction

section Cartan

variable {F : Type*} [Field F] [Finite F]

/-- **The degree of `X_s(ℓ)` over the `j`-line**: the split Cartan level, the diagonal torus, over
a field with `q` elements has projective index `q (q + 1)`. -/
theorem projectiveIndex_diagonalTorus_two :
    (diagonalTorus F 2).projectiveIndex = Nat.card F * (Nat.card F + 1) := by
  rw [Subgroup.projectiveIndex_eq_index neg_one_mem_diagonalTorus, index_diagonalTorus_two]

/-- **The degree of `X_s⁺(ℓ)` over the `j`-line is `ℓ (ℓ + 1) / 2`**: twice the projective index
of the monomial level over a field with `q` elements is `q (q + 1)`. -/
theorem two_mul_projectiveIndex_GL2SplitCartanNormalizer :
    2 * (GL2SplitCartanNormalizer F).projectiveIndex = Nat.card F * (Nat.card F + 1) := by
  rw [Subgroup.projectiveIndex_eq_index GL2SplitCartanNormalizer.neg_one_mem,
    GL2SplitCartanNormalizer.two_mul_index]

variable {t n : F}

/-- **The degree of `X_ns(ℓ)` over the `j`-line**: the nonsplit Cartan level over a field with `q`
elements has projective index `q (q - 1)`. -/
theorem projectiveIndex_GL2NonSplitCartan (hirr : ∀ x : F, x ^ 2 ≠ t * x + n) :
    (GL2NonSplitCartan t n).projectiveIndex = Nat.card F * (Nat.card F - 1) := by
  rw [Subgroup.projectiveIndex_eq_index GL2NonSplitCartan.neg_one_mem,
    GL2NonSplitCartan.index_eq hirr]

/-- **The degree of `X_ns⁺(ℓ)` over the `j`-line is `ℓ (ℓ - 1) / 2`**: twice the projective
index of the nonsplit Cartan normalizer over a field with `q` elements is `q (q - 1)`. -/
theorem two_mul_projectiveIndex_GL2NonSplitCartanNormalizer (hirr : ∀ x : F, x ^ 2 ≠ t * x + n) :
    2 * (GL2NonSplitCartanNormalizer t n).projectiveIndex = Nat.card F * (Nat.card F - 1) := by
  rw [Subgroup.projectiveIndex_eq_index
      (GL2NonSplitCartan.le_normalizer (t := t) (n := n) GL2NonSplitCartan.neg_one_mem),
    GL2NonSplitCartanNormalizer.two_mul_index hirr]

/-- **The degree of `X_s⁺(13)` over the `j`-line is `91`.** -/
theorem projectiveIndex_GL2SplitCartanNormalizer_zmod_thirteen :
    (GL2SplitCartanNormalizer (ZMod 13)).projectiveIndex = 91 := by
  have : Fact (Nat.Prime 13) := ⟨by decide⟩
  have h := two_mul_projectiveIndex_GL2SplitCartanNormalizer (F := ZMod 13)
  rw [Nat.card_zmod] at h
  omega

/-- **The degree of `X_ns⁺(13)` over the `j`-line is `78`**, for the nonsplit Cartan subgroup
`{!![a, 2 b; b, a]}`: `2` is not a square modulo `13`. -/
theorem projectiveIndex_GL2NonSplitCartanNormalizer_zmod_thirteen :
    (GL2NonSplitCartanNormalizer (0 : ZMod 13) 2).projectiveIndex = 78 := by
  have hirr : ∀ x : ZMod 13, x ^ 2 ≠ 0 * x + 2 := by decide
  have : Fact (Nat.Prime 13) := ⟨by decide⟩
  have h := two_mul_projectiveIndex_GL2NonSplitCartanNormalizer (F := ZMod 13) hirr
  rw [Nat.card_zmod] at h
  omega

end Cartan

namespace GL2

section ChangeOfLevel

variable {m n : ℕ} (h : n ∣ m)

/-- **Lifting with a prescribed determinant.** An element `g` of `GL₂(ℤ / n)` lifts to an element
of `GL₂(ℤ / m)` with any prescribed determinant `u` reducing to `det g`. Write `g` as an element of
`SL₂(ℤ / n)` times `!![det g, 0; 0, 1]`; the first factor lifts through `SL(2, ℤ)` by strong
approximation, and the second lifts to `!![u, 0; 0, 1]`. -/
theorem exists_map_castHom_eq_and_det_eq (g : GL (Fin 2) (ZMod n)) {u : (ZMod m)ˣ}
    (hu : ZMod.unitsMap h u = GeneralLinearGroup.det g) :
    ∃ g' : GL (Fin 2) (ZMod m),
      GeneralLinearGroup.map (ZMod.castHom h (ZMod n)) g' = g ∧ GeneralLinearGroup.det g' = u := by
  set f := GeneralLinearGroup.map (n := Fin 2) (ZMod.castHom h (ZMod n))
  have hD (v : (ZMod m)ˣ) : f (GL2Borel.mk v 1 0) = GL2Borel.mk (ZMod.unitsMap h v) 1 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [f, GeneralLinearGroup.map_apply, ZMod.unitsMap_def, -ZMod.castHom_apply]
  -- The determinant-one factor `s = g * !![det g, 0; 0, 1]⁻¹` lifts through `SL(2, ℤ)`.
  set s := g * (GL2Borel.mk (GeneralLinearGroup.det g) 1 0)⁻¹ with hs
  have hs1 : s ∈ (GeneralLinearGroup.det : GL (Fin 2) (ZMod n) →* _).ker := by
    simp [hs]
  obtain ⟨γ, hγ⟩ := (range_mapGL_zmod n).ge hs1
  have hγ' : f (mapGL (ZMod m) γ) = s := by
    rw [← hγ]
    ext i j
    simp [f, GeneralLinearGroup.map_apply, -ZMod.castHom_apply]
  refine ⟨mapGL (ZMod m) γ * GL2Borel.mk u 1 0, ?_, by simp⟩
  rw [map_mul, hD, hu, hγ', hs, inv_mul_cancel_right]

/-- **The reduction `GL₂(ℤ / m) → GL₂(ℤ / n)` is surjective** for `n ∣ m` and `m ≠ 0`. For
`m = 0` it is the reduction from `GL₂(ℤ)`, whose determinants are only `±1`. -/
theorem map_castHom_surjective [NeZero m] :
    Function.Surjective (GeneralLinearGroup.map (n := Fin 2) (ZMod.castHom h (ZMod n))) := by
  intro g
  obtain ⟨u, hu⟩ := ZMod.unitsMap_surjective h (GeneralLinearGroup.det g)
  obtain ⟨g', hg', -⟩ := exists_map_castHom_eq_and_det_eq h g hu
  exact ⟨g', hg'⟩

/-- **Change of level preserves the projective index**: the preimage in `GL₂(ℤ / m)` of a level
`H` of `GL₂(ℤ / n)` has the projective index of `H`, for `n ∣ m` and `m ≠ 0`. The same holds for
the index, by `Subgroup.index_comap_of_surjective` and `TauCeti.GL2.map_castHom_surjective`. -/
theorem projectiveIndex_comap_map_castHom [NeZero m] (H : Subgroup (GL (Fin 2) (ZMod n))) :
    (H.comap (GeneralLinearGroup.map (ZMod.castHom h (ZMod n)))).projectiveIndex =
      H.projectiveIndex :=
  H.projectiveIndex_comap_of_surjective (GeneralLinearGroup.map_neg _) (map_castHom_surjective h)

/-- **The determinant image under change of level**: the determinants of the preimage in
`GL₂(ℤ / m)` of a level `H` of `GL₂(ℤ / n)` are the units modulo `m` that reduce into
`det(H)`. This holds for `m = 0` as well. -/
theorem map_det_comap_map_castHom (H : Subgroup (GL (Fin 2) (ZMod n))) :
    (H.comap (GeneralLinearGroup.map (ZMod.castHom h (ZMod n)))).map GeneralLinearGroup.det =
      (H.map GeneralLinearGroup.det).comap (ZMod.unitsMap h) := by
  ext u
  simp only [Subgroup.mem_map, Subgroup.mem_comap]
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact ⟨_, hg, by rw [GeneralLinearGroup.map_det, ZMod.unitsMap_def]⟩
  · rintro ⟨g, hg, hgu⟩
    obtain ⟨g', hg', hdet⟩ := exists_map_castHom_eq_and_det_eq h g hgu.symm
    exact ⟨g', hg' ▸ hg, hdet⟩

end ChangeOfLevel

end GL2

end TauCeti
