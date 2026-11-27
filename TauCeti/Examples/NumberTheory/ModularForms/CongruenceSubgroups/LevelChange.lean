/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.CongruenceSubgroups.LevelSubgroup

/-!
# Checks for the invariants of levels and change of level

* At modulus `1` every level is all of `GL₂(ℤ / 1)`, with index and projective index `1` and
  trivial determinant image.
* Pulling the level one back to modulus `5` gives all of `GL₂(𝔽₅)`, whose determinant image is
  all of `𝔽₅ˣ`, which is nontrivial: the determinant images of a level and of its pullback live
  at different moduli and are not equal.
* The determinant is surjective onto `(ℤ / N)ˣ` on `Γ₀(N)` and `Γ₁(N)`, and trivial on `Γ(N)`.
-/

public section

open Matrix

namespace TauCeti.Examples.LevelChange

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

end TauCeti.Examples.LevelChange
