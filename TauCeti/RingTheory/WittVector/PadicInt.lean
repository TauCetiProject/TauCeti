/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.WittVector.Compare
public import Mathlib.RingTheory.WittVector.Frobenius
public import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology

/-!
# The map `ℤ_p → 𝕎 R` for a ring `R` of characteristic `p`

Mathlib identifies the `p`-adic integers with the Witt vectors of `𝔽_p`
(`WittVector.fromPadicInt : ℤ_[p] →+* 𝕎 (ZMod p)`). For a ring `R` of characteristic `p`, the
unique ring homomorphism `ZMod p → R` induces `𝕎 (ZMod p) → 𝕎 R`, and composing gives the
structure map `ℤ_[p] → 𝕎 R` (`TauCeti.WittVector.padicIntHom`). For `R = 𝒪_F` this is the
structure map `ℤ_p → A_inf`, the ring map underlying the projection of `Spa(A_inf, A_inf)`, and of
the period domain of the Fargues–Fontaine curve inside it, to `Spa(ℤ_p, ℤ_p)`.

The map is natural in `R`, so the Witt-vector Frobenius, which in characteristic `p` is the map
induced by the Frobenius of `R`, fixes it: Frobenius is a map over `ℤ_p`. It sends `p` to `p`, so
it is continuous for every adic topology on `𝕎 R` defined by an ideal containing `p`, such as the
`(p, [ϖ])`-adic topology of `A_inf`.

## Main definitions

* `TauCeti.WittVector.padicIntHom`: the ring homomorphism `ℤ_[p] → 𝕎 R`.

## Main results

* `TauCeti.WittVector.padicIntHom_zmod`: for `R = ZMod p` it is `WittVector.fromPadicInt`.
* `TauCeti.WittVector.map_comp_padicIntHom`: it is natural in `R`.
* `TauCeti.WittVector.frobenius_comp_padicIntHom`: Frobenius fixes it.
* `TauCeti.WittVector.continuous_padicIntHom`: it is continuous for every `J`-adic topology on
  `𝕎 R` with `p ∈ J`.
-/

public section

namespace TauCeti.WittVector

open _root_.WittVector

variable (p : ℕ) [Fact p.Prime] (R : Type*) [CommRing R] [CharP R p]

local notation "𝕎" => _root_.WittVector p

/-- **The structure map `ℤ_p → 𝕎 R`** of the Witt vectors of a ring `R` of characteristic `p`:
Mathlib's identification `ℤ_[p] ≅ 𝕎 (ZMod p)` followed by the map of Witt vectors induced by the
unique ring homomorphism `ZMod p → R`. -/
noncomputable def padicIntHom : ℤ_[p] →+* 𝕎 R :=
  (map (ZMod.castHom (dvd_refl p) R)).comp (fromPadicInt p)

/-- The Witt-vector coefficients of the image of a `p`-adic integer are the images in `R` of its
coefficients in `𝕎 (ZMod p)`. -/
theorem coeff_padicIntHom (x : ℤ_[p]) (n : ℕ) :
    (padicIntHom p R x).coeff n = ZMod.castHom (dvd_refl p) R ((fromPadicInt p x).coeff n) := by
  simp [padicIntHom, map_coeff]

/-- For `R = ZMod p` the structure map is Mathlib's `WittVector.fromPadicInt`. -/
theorem padicIntHom_zmod : padicIntHom p (ZMod p) = fromPadicInt p := by
  ext x n
  simp [coeff_padicIntHom]

variable {R} in
/-- **Naturality**: the map of Witt vectors induced by a ring homomorphism `R → S` of rings of
characteristic `p` carries the structure map of `𝕎 R` to that of `𝕎 S`. -/
@[simp]
theorem map_comp_padicIntHom {S : Type*} [CommRing S] [CharP S p] (f : R →+* S) :
    (map f).comp (padicIntHom p R) = padicIntHom p S := by
  ext x n
  rw [RingHom.comp_apply, map_coeff, coeff_padicIntHom, coeff_padicIntHom, ← RingHom.comp_apply,
    RingHom.ext_zmod (f.comp _) (ZMod.castHom (dvd_refl p) S)]

/-- **Frobenius is a map over `ℤ_p`**: the Witt-vector Frobenius of `𝕎 R`, which is induced by the
Frobenius of `R`, fixes the structure map `ℤ_[p] → 𝕎 R`. -/
@[simp]
theorem frobenius_comp_padicIntHom : frobenius.comp (padicIntHom p R) = padicIntHom p R := by
  rw [frobenius_eq_map_frobenius, map_comp_padicIntHom]

/-- **The structure map `ℤ_[p] → 𝕎 R` is continuous** for the `J`-adic topology on `𝕎 R`, for every
ideal `J` containing `p`: it carries `pⁿ ℤ_[p]` into `pⁿ 𝕎 R ⊆ Jⁿ`. This applies to the
`(p, [ϖ])`-adic topology of `A_inf`. -/
theorem continuous_padicIntHom [TopologicalSpace (𝕎 R)] {J : Ideal (𝕎 R)} (hJ : IsAdic J)
    (hp : (p : 𝕎 R) ∈ J) : Continuous (padicIntHom p R) := by
  have : IsTopologicalRing (𝕎 R) := hJ ▸ J.nonarchimedean.toIsTopologicalRing
  refine continuous_of_continuousAt_zero _ fun s hs ↦ ?_
  rw [map_zero] at hs
  obtain ⟨n, hn⟩ := (isAdic_iff.mp hJ).2 s hs
  have hball : Metric.closedBall (0 : ℤ_[p]) ((p : ℝ) ^ (-(n : ℤ))) ∈ nhds 0 :=
    Metric.closedBall_mem_nhds _ (zpow_pos (Nat.cast_pos.mpr (Fact.out : p.Prime).pos) _)
  refine Filter.mem_map.mpr <| Filter.mem_of_superset hball fun x hx ↦ hn ?_
  rw [Metric.mem_closedBall, dist_zero_right, PadicInt.norm_le_pow_iff_mem_span_pow,
    Ideal.mem_span_singleton] at hx
  obtain ⟨y, rfl⟩ := hx
  rw [SetLike.mem_coe, map_mul, map_pow, map_natCast]
  exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hp n)

end TauCeti.WittVector
