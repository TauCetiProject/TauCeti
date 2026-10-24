/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Circle
public import TauCeti.Analysis.Normed.Lp.ProdLp.Sphere
public import TauCeti.LowDimTopology.Heegaard.Splitting

/-!
# The genus-one Heegaard splitting of the `3`-sphere

The unit sphere `S³ = {(z, w) | ‖z‖ ^ 2 + ‖w‖ ^ 2 = 1}` of `ℂ²` is the union of the two solid tori
`‖z‖ ≤ ‖w‖` and `‖w‖ ≤ ‖z‖`, which meet along the Clifford torus `‖z‖ = ‖w‖`. The first is a copy
of `D² × S¹` through `(z, w) ↦ (z / ‖w‖, w / ‖w‖)` and the second a copy of `S¹ × D²`. This is the
standard genus-one Heegaard splitting of `S³` (`TauCeti.cliffordHeegaardSplitting`), the model from
which lens spaces are obtained by regluing the two solid tori along a different torus
homeomorphism.

Here `ℂ²` is the `L²` product `WithLp 2 (ℂ × ℂ)`, so that its unit sphere is the round
`3`-sphere. Transporting along a homeomorphism of unit spheres gives a genus-one Heegaard splitting
of the unit sphere of every four-dimensional real normed space
(`TauCeti.exists_heegaardSplitting_genus_eq_one`). The Heegaard genus of the `3`-sphere is still
zero (`TauCeti.heegaardGenus_sphere`): a splitting of genus one need not be of minimal genus.

## Main definitions

* `TauCeti.cliffordHeegaardSplitting`: the splitting of the unit sphere of `ℂ²` into the solid tori
  `‖z‖ ≤ ‖w‖` and `‖w‖ ≤ ‖z‖`.

## Main results

* `TauCeti.cliffordHeegaardSplitting_left_inter_right`: the two solid tori meet along the Clifford
  torus `‖z‖ = ‖w‖`.
* `TauCeti.exists_heegaardSplitting_genus_eq_one`: the unit sphere of a four-dimensional real
  normed space has a Heegaard splitting of genus one.

## References

* M. Scharlemann, *Heegaard splittings of compact 3-manifolds*, in *Handbook of Geometric
  Topology*, North-Holland (2002), Section 2.
* D. Rolfsen, *Knots and Links*, Publish or Perish (1976), Chapter 9 (the decomposition of `S³`
  into two solid tori, and lens spaces).
-/

public section

noncomputable section

open Metric Set

namespace TauCeti

/-- The solid torus `‖z‖ ≤ ‖w‖` in the unit sphere of `ℂ²` is a genus-one handlebody. -/
private theorem nonempty_homeomorph_setOf_norm_fst_le_norm_snd_handlebody_one :
    Nonempty ({x : sphere (0 : WithLp 2 (ℂ × ℂ)) 1 | ‖(x : WithLp 2 (ℂ × ℂ)).fst‖ ≤
      ‖(x : WithLp 2 (ℂ × ℂ)).snd‖} ≃ₜ handlebody 1) :=
  nonempty_homeomorph_handlebody_one.map fun e ↦
    (sphereProdFstLeHomeomorph ℂ ℂ).trans <|
      ((Homeomorph.refl _).prodCongr Circle.homeomorphSphere.symm).trans e.symm

/-- The solid torus `‖w‖ ≤ ‖z‖` in the unit sphere of `ℂ²` is a genus-one handlebody. -/
private theorem nonempty_homeomorph_setOf_norm_snd_le_norm_fst_handlebody_one :
    Nonempty ({x : sphere (0 : WithLp 2 (ℂ × ℂ)) 1 | ‖(x : WithLp 2 (ℂ × ℂ)).snd‖ ≤
      ‖(x : WithLp 2 (ℂ × ℂ)).fst‖} ≃ₜ handlebody 1) :=
  nonempty_homeomorph_handlebody_one.map fun e ↦
    (sphereProdSndLeHomeomorph ℂ ℂ).trans <| (Homeomorph.prodComm _ _).trans <|
      ((Homeomorph.refl _).prodCongr Circle.homeomorphSphere.symm).trans e.symm

/-- The genus-one Heegaard splitting of the unit sphere of `ℂ²` into the solid tori `‖z‖ ≤ ‖w‖`
and `‖w‖ ≤ ‖z‖`, meeting along the Clifford torus `‖z‖ = ‖w‖`. -/
def cliffordHeegaardSplitting : HeegaardSplitting (sphere (0 : WithLp 2 (ℂ × ℂ)) 1) where
  genus := 1
  left := {x | ‖(x : WithLp 2 (ℂ × ℂ)).fst‖ ≤ ‖(x : WithLp 2 (ℂ × ℂ)).snd‖}
  right := {x | ‖(x : WithLp 2 (ℂ × ℂ)).snd‖ ≤ ‖(x : WithLp 2 (ℂ × ℂ)).fst‖}
  union_eq_univ := by
    ext x
    simp [le_total]
  inter_eq_frontier_left := by
    rw [frontier_setOf_norm_fst_le_norm_snd]
    ext x
    simp [le_antisymm_iff]
  inter_eq_frontier_right := by
    rw [frontier_setOf_norm_snd_le_norm_fst]
    ext x
    simp [le_antisymm_iff]
  nonempty_homeomorph_left := nonempty_homeomorph_setOf_norm_fst_le_norm_snd_handlebody_one
  nonempty_homeomorph_right := nonempty_homeomorph_setOf_norm_snd_le_norm_fst_handlebody_one

@[simp] theorem cliffordHeegaardSplitting_genus : cliffordHeegaardSplitting.genus = 1 := (rfl)

@[simp]
theorem cliffordHeegaardSplitting_left :
    cliffordHeegaardSplitting.left =
      {x : sphere (0 : WithLp 2 (ℂ × ℂ)) 1 |
        ‖(x : WithLp 2 (ℂ × ℂ)).fst‖ ≤ ‖(x : WithLp 2 (ℂ × ℂ)).snd‖} :=
  (rfl)

@[simp]
theorem cliffordHeegaardSplitting_right :
    cliffordHeegaardSplitting.right =
      {x : sphere (0 : WithLp 2 (ℂ × ℂ)) 1 |
        ‖(x : WithLp 2 (ℂ × ℂ)).snd‖ ≤ ‖(x : WithLp 2 (ℂ × ℂ)).fst‖} :=
  (rfl)

/-- The two solid tori of `TauCeti.cliffordHeegaardSplitting` meet along the Clifford torus
`‖z‖ = ‖w‖`. -/
theorem cliffordHeegaardSplitting_left_inter_right :
    cliffordHeegaardSplitting.left ∩ cliffordHeegaardSplitting.right =
      {x : sphere (0 : WithLp 2 (ℂ × ℂ)) 1 |
        ‖(x : WithLp 2 (ℂ × ℂ)).fst‖ = ‖(x : WithLp 2 (ℂ × ℂ)).snd‖} := by
  rw [cliffordHeegaardSplitting.inter_eq_frontier_left, cliffordHeegaardSplitting_left,
    frontier_setOf_norm_fst_le_norm_snd]

/-- **The `3`-sphere has a Heegaard splitting of genus one.** The unit sphere of any
four-dimensional real normed space has a Heegaard splitting of genus one, transported from the
splitting of the unit sphere of `ℂ²` into two solid tori. -/
theorem exists_heegaardSplitting_genus_eq_one {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (hE : Module.finrank ℝ E = 4) :
    ∃ s : HeegaardSplitting (sphere (0 : E) 1), s.genus = 1 := by
  have : FiniteDimensional ℝ E := .of_finrank_eq_succ hE
  have h : Module.finrank ℝ (WithLp 2 (ℂ × ℂ)) = Module.finrank ℝ E := by
    rw [(WithLp.linearEquiv 2 ℝ (ℂ × ℂ)).finrank_eq, Module.finrank_prod,
      Complex.finrank_real_complex, hE]
  exact ⟨cliffordHeegaardSplitting.transHomeomorph (sphereHomeomorphOfFinrankEq h), by simp⟩

end TauCeti
