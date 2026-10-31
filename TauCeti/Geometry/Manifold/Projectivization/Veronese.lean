/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.SmoothEmbedding
public import TauCeti.Geometry.Manifold.Immersion.Differential
public import TauCeti.Geometry.Manifold.Projectivization.Map
public import TauCeti.Topology.Algebra.Projectivization.Veronese

/-!
# The Veronese map is a closed analytic embedding

The Veronese map `Projectivization.veronese 𝕜 d` sends `[v]` to the point of
`ℙ 𝕜 (Fin (veroneseDim (m + 1) d) → 𝕜)` whose homogeneous coordinates are the monomials of degree
`d` in `v`. The manifold structure of projective space is defined on `ℙ 𝕜 (Fin (n + 1) → 𝕜)`, so
the Veronese map is read through an injective linear map `f` from its space of homogeneous
coordinates to `Fin (n + 1) → 𝕜`, such as a reindexing of the monomials by a linear equivalence
when `veroneseDim (m + 1) d = n + 1`, or its composite with a linear inclusion into a larger
projective space. The resulting map `Projectivization.map f hf ∘ Projectivization.veronese 𝕜 d`
is given in homogeneous coordinates by the polynomial map `f ∘ veroneseMonomials d`, so it is
analytic (`Projectivization.contMDiff_map_comp_veronese`); over `ℂ` it is holomorphic.

For positive degree `e + 1` it is moreover an immersion. On the affine open where the `i`-th
homogeneous coordinate is nonzero, the coordinates `y_(e e_i + e_j)` of the image of `[v]` are the
coordinates of `v i ^ e • v` (`TauCeti.veroneseLocalInverse_veroneseMonomials`). Composed with a
linear left inverse of `f`, they define an analytic map on an open neighbourhood of the image which
is a left inverse of the Veronese map near `[v]`, so its differential is injective
(`Projectivization.isImmersion_map_comp_veronese`). Since projective space is compact and the
Veronese map of positive degree is injective, it is a closed embedding, and hence a closed analytic
embedding (`Projectivization.isSmoothEmbedding_map_comp_veronese`,
`Projectivization.isClosedEmbedding_map_comp_veronese`).

## Main results

* `TauCeti.contDiff_veroneseMonomials`: the vector of monomials of degree `d` is a `C^r` function
  of the vector, for every `r`.
* `Projectivization.contMDiff_map_comp_veronese`: the Veronese map, read through an injective
  linear map, is `C^r` for every `r`, including the analytic order `ω`.
* `Projectivization.isImmersion_map_comp_veronese`: for positive degree it is an immersion.
* `Projectivization.isClosedEmbedding_map_comp_veronese` and
  `Projectivization.isSmoothEmbedding_map_comp_veronese`: for positive degree it is a closed
  embedding and a `C^r` embedding, over `ℝ` or `ℂ`.

## References

* J. Harris, *Algebraic Geometry: A First Course*, Graduate Texts in Mathematics 133, Springer,
  1992, Lecture 2, Example 2.4.
* P. Griffiths and J. Harris, *Principles of Algebraic Geometry*, Chapter 0, §1.
-/

public section

open Set Function Topology Manifold
open scoped ContDiff Manifold LinearAlgebra.Projectivization

namespace TauCeti

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {N : ℕ}

/-- The vector of monomials of degree `d` of `v` is a `C^r` function of `v`, for every `r`. -/
theorem contDiff_veroneseMonomials (d : ℕ) {r : ℕ∞ω} :
    ContDiff 𝕜 r (veroneseMonomials (N := N) (K := 𝕜) d) :=
  contDiff_pi.2 fun k ↦ by
    simp only [veroneseMonomials_apply]
    exact contDiff_prod fun i _ ↦ (contDiff_pi.1 contDiff_id i).pow _

end TauCeti

namespace Projectivization

open TauCeti

section NontriviallyNormedField

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {m n d : ℕ}

/-- The Veronese map, read through an injective linear map `f` from its space of homogeneous
coordinates to `Fin (n + 1) → 𝕜`, is `C^r` for every `r`; for `r = ω` it is analytic. Over `ℂ`
it is holomorphic. -/
theorem contMDiff_map_comp_veronese
    (f : (Fin (veroneseDim (m + 1) d) → 𝕜) →ₗ[𝕜] Fin (n + 1) → 𝕜) (hf : Injective f)
    (r : ℕ∞ω) : ContMDiff 𝓘(𝕜, Fin m → 𝕜) 𝓘(𝕜, Fin n → 𝕜) r (map f hf ∘ veronese 𝕜 d) :=
  contMDiff_of_contDiffOn (F := f ∘ veroneseMonomials d)
    ((⟨f, LinearMap.continuous_on_pi f⟩ : (Fin (veroneseDim (m + 1) d) → 𝕜) →L[𝕜]
      Fin (n + 1) → 𝕜).contDiff.comp (contDiff_veroneseMonomials d)).contDiffOn
    (fun _ hv ↦ (map_ne_zero_iff f hf).2 (veroneseMonomials_ne_zero d hv))
    fun _ _ ↦ by simp [map_mk]

end NontriviallyNormedField

section RCLike

variable {𝕜 : Type*} [RCLike 𝕜] {m n d : ℕ}

/-- **The Veronese map is an immersion.** For positive degree, the Veronese map read through an
injective linear map `f` is a `C^r` immersion for every `r ≥ 1`. Near a point where the `i`-th
homogeneous coordinate is nonzero, it has the analytic left inverse
`[w] ↦ [veroneseLocalInverse 𝕜 (d - 1) i (g w)]`, for a linear left inverse `g` of `f`. -/
theorem isImmersion_map_comp_veronese (hd : d ≠ 0)
    (f : (Fin (veroneseDim (m + 1) d) → 𝕜) →ₗ[𝕜] Fin (n + 1) → 𝕜) (hf : Injective f)
    {r : ℕ∞ω} (hr : 1 ≤ r) :
    IsImmersion 𝓘(𝕜, Fin m → 𝕜) 𝓘(𝕜, Fin n → 𝕜) r (map f hf ∘ veronese 𝕜 d) := by
  obtain ⟨e, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hd
  have hr0 : r ≠ 0 := by rintro rfl; simp at hr
  rw [isImmersion_iff_forall_isImmersionAt]
  intro x
  obtain ⟨i, hi⟩ := exists_mem_affineOpen x
  obtain ⟨g, hg⟩ := f.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.2 hf)
  -- The local inverse in homogeneous coordinates, and the open set where it does not vanish.
  let G := veroneseLocalInverse 𝕜 e i ∘ₗ g
  have hGf (v : Fin (m + 1) → 𝕜) : G (f (veroneseMonomials (e + 1) v)) = v i ^ e • v := by
    rw [← veroneseLocalInverse_veroneseMonomials, LinearMap.comp_apply, ← LinearMap.comp_apply g,
      hg, LinearMap.id_apply]
  have hGrep (w : Fin (n + 1) → 𝕜) (hw : w ≠ 0) : ∃ a : 𝕜ˣ, G (mk 𝕜 w hw).rep = a • G w := by
    obtain ⟨a, ha⟩ := exists_smul_eq_mk_rep 𝕜 w hw
    exact ⟨a, by rw [← ha, Units.smul_def, map_smul, Units.smul_def]⟩
  let s : Set (ℙ 𝕜 (Fin (n + 1) → 𝕜)) := {y | G y.rep ≠ 0}
  have hmem (w : Fin (n + 1) → 𝕜) (hw : w ≠ 0) : mk 𝕜 w hw ∈ s ↔ G w ≠ 0 := by
    obtain ⟨a, ha⟩ := hGrep w hw
    simp only [s, mem_ofPred_eq, ha, smul_ne_zero_iff_ne]
  have hs : IsOpen s := by
    rw [← isQuotientMap_mk'.isOpen_preimage]
    convert isOpen_ne_fun ((LinearMap.continuous_on_pi G).comp continuous_subtype_val)
      (continuous_const (y := (0 : Fin (m + 1) → 𝕜))) using 1
    ext v
    simp [mk'_eq_mk, hmem]
  let ginv : ℙ 𝕜 (Fin (n + 1) → 𝕜) → ℙ 𝕜 (Fin (m + 1) → 𝕜) := fun y ↦
    if h : G y.rep ≠ 0 then mk 𝕜 (G y.rep) h else x
  have hginv (w : Fin (n + 1) → 𝕜) (hw : w ≠ 0) (h : G w ≠ 0) :
      ginv (mk 𝕜 w hw) = mk 𝕜 (G w) h := by
    have h' : G (mk 𝕜 w hw).rep ≠ 0 := (hmem w hw).2 h
    obtain ⟨a, ha⟩ := hGrep w hw
    simp only [ginv, ne_eq, h', not_false_eq_true, ↓reduceDIte]
    exact (mk_eq_mk_iff' 𝕜 _ _ _ _).2 ⟨a, by rw [ha, Units.smul_def]⟩
  have hginvs : ContMDiffOn 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, Fin m → 𝕜) r ginv s :=
    contMDiffOn_of_contDiffOn hs
      (⟨G, LinearMap.continuous_on_pi G⟩ : (Fin (n + 1) → 𝕜) →L[𝕜]
        Fin (m + 1) → 𝕜).contDiff.contDiffOn
      (fun w hw h ↦ (hmem w hw).1 h) fun w hw h ↦ hginv w hw _
  -- On the affine open at `i`, the image lies in `s` and `ginv` inverts the Veronese map.
  have hloc (y) (hy : y ∈ affineOpen i) :
      (map f hf ∘ veronese 𝕜 (e + 1)) y ∈ s ∧ ginv ((map f hf ∘ veronese 𝕜 (e + 1)) y) = y := by
    induction y using ind with | h v hv => ?_
    rw [mk_mem_affineOpen_iff] at hy
    have hne : G (f (veroneseMonomials (e + 1) v)) ≠ 0 := by
      rw [hGf]
      exact smul_ne_zero (pow_ne_zero e hy) hv
    simp only [comp_apply, veronese_mk, map_mk]
    refine ⟨(hmem _ _).2 hne, ?_⟩
    rw [hginv _ _ hne]
    exact (mk_eq_mk_iff' 𝕜 _ _ _ _).2 ⟨v i ^ e, (hGf v).symm⟩
  have hh := contMDiff_map_comp_veronese (𝕜 := 𝕜) (m := m) (d := e + 1) f hf r
  exact (hh.contMDiffOn (s := univ)).isImmersionAt_of_comp_eventuallyEq_id isOpen_univ
    (mem_univ x) hr (((hginvs _ (hloc x hi).1).contMDiffAt
      (hs.mem_nhds (hloc x hi).1)).mdifferentiableAt hr0)
    (Filter.eventuallyEq_of_mem ((isOpen_affineOpen i).mem_nhds hi) fun y hy ↦ (hloc y hy).2)

/-- For positive degree, the Veronese map read through an injective linear map is a closed
embedding: projective space is compact and the map is continuous and injective. -/
theorem isClosedEmbedding_map_comp_veronese (hd : d ≠ 0)
    (f : (Fin (veroneseDim (m + 1) d) → 𝕜) →ₗ[𝕜] Fin (n + 1) → 𝕜) (hf : Injective f) :
    IsClosedEmbedding (map f hf ∘ veronese 𝕜 d) :=
  (contMDiff_map_comp_veronese f hf 0).continuous.isClosedEmbedding
    ((map_injective f hf).comp (veronese_injective hd))

/-- **The Veronese map is a closed analytic embedding.** For positive degree, the Veronese map read
through an injective linear map is a `C^r` embedding for every `r ≥ 1`, including the analytic
order `ω`; its image is closed by `Projectivization.isClosedEmbedding_map_comp_veronese`. Over `ℂ`
it is a holomorphic embedding. -/
theorem isSmoothEmbedding_map_comp_veronese (hd : d ≠ 0)
    (f : (Fin (veroneseDim (m + 1) d) → 𝕜) →ₗ[𝕜] Fin (n + 1) → 𝕜) (hf : Injective f)
    {r : ℕ∞ω} (hr : 1 ≤ r) :
    IsSmoothEmbedding 𝓘(𝕜, Fin m → 𝕜) 𝓘(𝕜, Fin n → 𝕜) r (map f hf ∘ veronese 𝕜 d) :=
  ⟨isImmersion_map_comp_veronese hd f hf hr,
    (isClosedEmbedding_map_comp_veronese hd f hf).isEmbedding⟩

end RCLike

end Projectivization
