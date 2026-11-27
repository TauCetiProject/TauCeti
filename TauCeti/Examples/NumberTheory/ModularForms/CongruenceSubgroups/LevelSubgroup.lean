/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.CongruenceSubgroups.LevelSubgroup
import TauCeti.NumberTheory.ModularForms.CongruenceSubgroups.Basic

/-!
# Checks for levels: `Γ₁(5)`, `Γ₁^μ(5)` and change of modulus

The coarse degree of `X_H` over the `j`-line is the projective index, not the index: for the
levels `Γ₁ = TauCeti.GL2Gamma1 (ZMod 5)` and `Γ₁^μ = TauCeti.GL2Mirabolic (ZMod 5)` the index is
`24` but the projective index is `12`, because `-1` lies in neither.

* `[GL₂(ℤ / 5) : Γ₁] = 24` and `[GL₂(ℤ / 5) : ±Γ₁] = 12`.
* `[GL₂(ℤ / 5) : Γ₁^μ] = 24` and `[GL₂(ℤ / 5) : ±Γ₁^μ] = 12`.

The invariants of levels under change of modulus:

* At modulus `1` every level is all of `GL₂(ℤ / 1)`, with index and projective index `1` and
  trivial determinant image.
* Pulling the level one back to modulus `5` gives all of `GL₂(𝔽₅)`, whose determinant image is
  all of `𝔽₅ˣ`, which is nontrivial: the determinant images of a level and of its pullback live
  at different moduli and are not equal.
* The determinant is surjective onto `(ℤ / N)ˣ` on `Γ₀(N)` and `Γ₁(N)`, and trivial on `Γ(N)`.
-/

public section

open CongruenceSubgroup Matrix

namespace TauCeti.Examples.LevelSubgroup

/-- `[SL(2, ℤ) : Γ₁(5)] = φ(5) (5 + 1) = 24`. -/
theorem index_gamma1_five : (Gamma1 5).index = 24 := by
  rw [Gamma1_prime_index 5 Nat.prime_five]

/-- The level `Γ₁(5)` has index `24`. -/
theorem index_GL2Gamma1_five : (GL2Gamma1 (ZMod 5)).index = 24 := by
  rw [index_GL2Gamma1_zmod, index_gamma1_five]

/-- The level `Γ₁(5)` has projective index `12`, half its index. -/
theorem projectiveIndex_GL2Gamma1_five : (GL2Gamma1 (ZMod 5)).projectiveIndex = 12 := by
  have := two_mul_projectiveIndex_GL2Gamma1_zmod 5 (by norm_num)
  rw [index_gamma1_five] at this
  omega

/-- The level `Γ₁^μ(5)` has index `24`. -/
theorem index_GL2Mirabolic_five : (GL2Mirabolic (ZMod 5)).index = 24 := by
  rw [index_GL2Mirabolic_zmod, index_gamma1_five]

/-- The level `Γ₁^μ(5)` has projective index `12`, half its index. -/
theorem projectiveIndex_GL2Mirabolic_five : (GL2Mirabolic (ZMod 5)).projectiveIndex = 12 := by
  have := two_mul_projectiveIndex_GL2Mirabolic_zmod 5 (by norm_num)
  rw [index_gamma1_five] at this
  omega

/-- At modulus `1` every level is all of `GL₂(ℤ / 1)`. -/
theorem eq_top_zmod_one (H : Subgroup (GL (Fin 2) (ZMod 1))) : H = ⊤ :=
  Subsingleton.elim _ _

/-- At modulus `1` every level has index `1`. -/
theorem index_zmod_one (H : Subgroup (GL (Fin 2) (ZMod 1))) : H.index = 1 := by
  rw [eq_top_zmod_one H, Subgroup.index_top]

/-- At modulus `1` every level has projective index `1`. -/
theorem projectiveIndex_zmod_one (H : Subgroup (GL (Fin 2) (ZMod 1))) :
    H.projectiveIndex = 1 := by
  rw [Subgroup.projectiveIndex_def, eq_top_zmod_one H.adjoinNegOne, Subgroup.index_top]

/-- At modulus `1` every level has trivial determinant image. -/
theorem map_det_zmod_one (H : Subgroup (GL (Fin 2) (ZMod 1))) :
    H.map GeneralLinearGroup.det = ⊥ :=
  Subsingleton.elim _ _

/-- **Pulling level one back to modulus `5`** gives all of `GL₂(𝔽₅)`. -/
theorem comap_top_one_five :
    (⊤ : Subgroup (GL (Fin 2) (ZMod 1))).comap
      (GeneralLinearGroup.map (ZMod.castHom (one_dvd 5) (ZMod 1))) = ⊤ :=
  Subgroup.comap_top _

/-- The determinant image of the pullback of level one to modulus `5` is all of `𝔽₅ˣ`. -/
theorem map_det_comap_top_one_five :
    ((⊤ : Subgroup (GL (Fin 2) (ZMod 1))).comap
      (GeneralLinearGroup.map (ZMod.castHom (one_dvd 5) (ZMod 1)))).map
        GeneralLinearGroup.det = ⊤ := by
  rw [GL2.map_det_comap_map_castHom, map_det_zmod_one, eq_top_iff]
  intro u _
  rw [Subgroup.mem_comap, Subgroup.mem_bot]
  exact Subsingleton.elim _ _

/-- The determinant image at modulus `5` is nontrivial, unlike that at modulus `1`. -/
theorem map_det_comap_top_one_five_ne_bot :
    ((⊤ : Subgroup (GL (Fin 2) (ZMod 1))).comap
      (GeneralLinearGroup.map (ZMod.castHom (one_dvd 5) (ZMod 1)))).map
        GeneralLinearGroup.det ≠ ⊥ := by
  rw [map_det_comap_top_one_five]
  intro h
  have h1 : (-1 : (ZMod 5)ˣ) ∈ (⊥ : Subgroup (ZMod 5)ˣ) := h ▸ Subgroup.mem_top _
  exact absurd (Subgroup.mem_bot.1 h1) (by decide)

/-- The determinant maps `Γ₀(N)` onto `(ℤ / N)ˣ`. -/
theorem map_det_GL2Borel (N : ℕ) :
    (GL2Borel (ZMod N)).map GeneralLinearGroup.det = ⊤ :=
  GL2Borel.map_det

/-- The determinant maps `Γ₁(N)` onto `(ℤ / N)ˣ`. -/
theorem map_det_GL2Gamma1 (N : ℕ) :
    (GL2Gamma1 (ZMod N)).map GeneralLinearGroup.det = ⊤ :=
  GL2Gamma1.map_det

/-- The determinant is trivial on the full level `Γ(N)`, the trivial subgroup. -/
theorem map_det_bot (N : ℕ) :
    (⊥ : Subgroup (GL (Fin 2) (ZMod N))).map GeneralLinearGroup.det = ⊥ :=
  Subgroup.map_bot _

end TauCeti.Examples.LevelSubgroup
