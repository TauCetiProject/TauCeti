/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Diffeomorphism.Diffeotopy.Basic
public import TauCeti.Geometry.Manifold.Instances.Icc
public import TauCeti.Geometry.Manifold.Instances.MappingTorus.Map

/-!
# Mapping tori of isotopic diffeomorphisms

Let `φ, ψ : M ≃ₘ^n⟮I, I⟯ M` be diffeomorphisms with smooth mapping tori `Y_φ` and `Y_ψ`
(`TauCeti.SmoothMappingTorus`), let `Φ` be a diffeotopy of `M` (`TauCeti.Diffeotopy`), with time
slices `Φ_s`, and let `ψ ∘ Φ₁ = φ`. Then `φ` and `ψ` are isotopic, and their mapping tori are
diffeomorphic over the circle (`TauCeti.SmoothMappingTorus.congrDiffeotopy`). The diffeomorphism
is `[t, x] ↦ [t, g t x]`, induced (`TauCeti.SmoothMappingTorus.congrFamily`) by the family

`g t = ψ ^ (-⌊t⌋) ∘ Φ_(c (t - ⌊t⌋)) ∘ φ ^ ⌊t⌋`

(`TauCeti.SmoothMappingTorus.diffeotopyFamily`), where `c` is the collared smooth transition
`TauCeti.collaredSmoothTransitionUnit`, equal to `0` up to time `1 / 4` and to `1` from time
`3 / 4` on. The equivariance `ψ ∘ g (t + 1) = g t ∘ φ` holds by construction. The family is
jointly smooth because near an integer time `k` both of its pieces equal `ψ ^ (-k) ∘ φ ^ k`, which
is where `ψ ∘ Φ₁ = φ` enters. On the fibre over `0` the diffeomorphism is the identity
`[0, x] ↦ [0, x]`, and over `t ∈ [0, 1]` it moves the fibre by `Φ_(c t)`. Unlike the maps induced
by conjugacies, it need not intertwine the suspension flows.

This is how a perturbation of the monodromy within its isotopy class, for instance the composite
`ψ = φ ∘ Φ₁⁻¹` with the final map of a Hamiltonian isotopy, is transported to a diffeomorphism of
the suspensions.

## Main definitions

* `TauCeti.SmoothMappingTorus.diffeotopyFamily φ ψ Φ`: the equivariant family built from a
  diffeotopy `Φ`.
* `TauCeti.SmoothMappingTorus.congrDiffeotopy Φ hΦ hn`: the diffeomorphism `Y_φ ≃ Y_ψ` over the
  circle induced by a diffeotopy `Φ` with `ψ ∘ Φ₁ = φ`.

## Main results

* `TauCeti.SmoothMappingTorus.contMDiff_diffeotopyFamily`: the family built from a diffeotopy `Φ`
  with `ψ ∘ Φ₁ = φ` is jointly `C^n` for `n ≤ ∞`.
* `TauCeti.SmoothMappingTorus.congrDiffeotopy_mk_of_mem_Icc`,
  `TauCeti.SmoothMappingTorus.congrDiffeotopy_mk_zero`: the diffeomorphism induced by a diffeotopy
  is `[t, x] ↦ [t, Φ_(c t) x]` for `t ∈ [0, 1]`, and the identity on the fibre over `0`.
* `TauCeti.SmoothMappingTorus.congrDiffeotopy_symm`: its inverse is induced by the inverse
  diffeotopy.

## References

* Morris W. Hirsch, *Differential Topology*, Graduate Texts in Mathematics 33, Springer, 1976,
  Chapter 8 (isotopy).
* Allen Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Section 2.2 (mapping
  tori).
-/

public noncomputable section

open Set Filter Topology
open scoped Manifold ContDiff

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {n : ℕ∞ω}

namespace SmoothMappingTorus

/-- The equivariant family `t ↦ ψ ^ (-⌊t⌋) ∘ Φ_(c (t - ⌊t⌋)) ∘ φ ^ ⌊t⌋` built from a diffeotopy
`Φ`, where `c` is the collared smooth transition `TauCeti.collaredSmoothTransitionUnit`. It
satisfies `ψ ∘ g (t + 1) = g t ∘ φ`
(`TauCeti.SmoothMappingTorus.apply_diffeotopyFamily_add_one`). When `ψ ∘ Φ₁ = φ` it equals
`Φ_(c t)` for `t ∈ [0, 1]` (`TauCeti.SmoothMappingTorus.diffeotopyFamily_of_mem_Icc`), and when
moreover `n ≤ ∞` it is jointly `C^n` (`TauCeti.SmoothMappingTorus.contMDiff_diffeotopyFamily`). -/
def diffeotopyFamily (φ ψ : M ≃ₘ^n⟮I, I⟯ M) (Φ : Diffeotopy I n M) (t : ℝ) :
    M ≃ₘ^n⟮I, I⟯ M :=
  ψ ^ (-⌊t⌋) * Φ.timeSlice (collaredSmoothTransitionUnit (Int.fract t)) * φ ^ ⌊t⌋

variable {φ ψ : M ≃ₘ^n⟮I, I⟯ M} {Φ : Diffeotopy I n M}

/-- The family built from a diffeotopy at time `t`, evaluated at `x`. -/
theorem diffeotopyFamily_apply (t : ℝ) (x : M) :
    diffeotopyFamily φ ψ Φ t x =
      (ψ ^ (-⌊t⌋)) (Φ (collaredSmoothTransitionUnit (Int.fract t), (φ ^ ⌊t⌋) x)) := by
  rw [diffeotopyFamily, Diffeomorph.mul_apply, Diffeomorph.mul_apply, Diffeotopy.timeSlice_apply]

/-- The family built from a diffeotopy satisfies the equivariance `ψ ∘ g (t + 1) = g t ∘ φ`. -/
theorem apply_diffeotopyFamily_add_one (t : ℝ) (x : M) :
    ψ (diffeotopyFamily φ ψ Φ (t + 1) x) = diffeotopyFamily φ ψ Φ t (φ x) := by
  have h : ψ * diffeotopyFamily φ ψ Φ (t + 1) = diffeotopyFamily φ ψ Φ t * φ := by
    simp only [diffeotopyFamily, Int.floor_add_one, Int.fract_add_one]
    group
  exact DFunLike.congr_fun h x

/-- The inverses of the family built from `Φ` form the family built from the inverse diffeotopy,
with the roles of `φ` and `ψ` exchanged. -/
theorem diffeotopyFamily_symm (t : ℝ) :
    (diffeotopyFamily φ ψ Φ t).symm = diffeotopyFamily ψ φ Φ.symm t := by
  rw [← Diffeomorph.inv_def, diffeotopyFamily, diffeotopyFamily, Diffeotopy.timeSlice_symm,
    ← Diffeomorph.inv_def]
  group

/-- If `ψ ∘ Φ₁ = φ`, then the final time slice `Φ₁` is `ψ⁻¹ ∘ φ`. -/
private theorem timeSlice_one_eq_inv_mul (hΦ : ψ * Φ.final = φ) : Φ.timeSlice 1 = ψ⁻¹ * φ := by
  rw [← Diffeotopy.final_def, ← hΦ, inv_mul_cancel_left]

/-- Near the integer time `k`, on the open interval `(k - 1/4, k + 1)`, the family built from a
diffeotopy `Φ` with `ψ ∘ Φ₁ = φ` is `ψ ^ (-k) ∘ Φ_(c (t - k)) ∘ φ ^ k`: on `(k - 1/4, k]` both
expressions equal `ψ ^ (-k) ∘ φ ^ k`. -/
private theorem diffeotopyFamily_eq_of_mem_Ioo (hΦ : ψ * Φ.final = φ) (k : ℤ) {t : ℝ}
    (ht : t ∈ Ioo ((k : ℝ) - 1 / 4) (k + 1)) :
    diffeotopyFamily φ ψ Φ t =
      ψ ^ (-k) * Φ.timeSlice (collaredSmoothTransitionUnit (t - k)) * φ ^ k := by
  rcases lt_or_ge t k with htk | htk
  · -- On `(k - 1/4, k)` the collar of the previous interval is at its final time.
    have hfl : ⌊t⌋ = k - 1 :=
      Int.floor_eq_iff.2 ⟨by push_cast; linarith [ht.1], by push_cast; linarith⟩
    have hfr : collaredSmoothTransitionUnit (Int.fract t) = 1 :=
      collaredSmoothTransitionUnit_eq_one_of_ge (by
        rw [← Int.self_sub_floor, hfl]; push_cast; linarith [ht.1])
    rw [diffeotopyFamily, hfr, hfl, collaredSmoothTransitionUnit_eq_zero_of_le (by linarith),
      Diffeotopy.timeSlice_zero, ← Diffeomorph.one_def, timeSlice_one_eq_inv_mul hΦ]
    group
  · have hfl : ⌊t⌋ = k := Int.floor_eq_iff.2 ⟨htk, ht.2⟩
    rw [diffeotopyFamily, ← Int.self_sub_floor, hfl]

/-- On the time interval `[0, 1]`, the family built from a diffeotopy `Φ` with `ψ ∘ Φ₁ = φ` is
`Φ_(c t)`. -/
theorem diffeotopyFamily_of_mem_Icc (hΦ : ψ * Φ.final = φ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    diffeotopyFamily φ ψ Φ t = Φ.timeSlice (collaredSmoothTransitionUnit t) := by
  rcases eq_or_lt_of_le ht.2 with rfl | ht1
  · -- At the time `1`, the family is the final diffeomorphism `ψ⁻¹ ∘ φ = Φ₁`.
    rw [diffeotopyFamily_eq_of_mem_Ioo hΦ 1 ⟨by norm_num, by norm_num⟩, Int.cast_one, sub_self,
      collaredSmoothTransitionUnit_eq_zero_of_le (by norm_num),
      collaredSmoothTransitionUnit_eq_one_of_ge (by norm_num), Diffeotopy.timeSlice_zero,
      ← Diffeomorph.one_def, timeSlice_one_eq_inv_mul hΦ]
    group
  · simpa using diffeotopyFamily_eq_of_mem_Ioo hΦ 0 ⟨by linarith [ht.1], by simpa using ht1⟩

/-- The family built from a diffeotopy `Φ` with `ψ ∘ Φ₁ = φ` is jointly `C^n` in `(t, x)` for
`n ≤ ∞`. Near each integer time it agrees with a single smooth expression, because the collared
transition is constant near the ends of the unit interval. -/
theorem contMDiff_diffeotopyFamily (hΦ : ψ * Φ.final = φ) (hn : n ≤ ∞) :
    ContMDiff (𝓘(ℝ).prod I) I n fun p : ℝ × M ↦ diffeotopyFamily φ ψ Φ p.1 p.2 := by
  intro p
  set k := ⌊p.1⌋
  -- The expression `ψ ^ (-k) ∘ Φ_(c (t - k)) ∘ φ ^ k` is smooth on all of `ℝ × M`.
  have hG : ContMDiff (𝓘(ℝ).prod I) I n fun q : ℝ × M ↦
      (ψ ^ (-k)) (Φ (collaredSmoothTransitionUnit (q.1 - k), (φ ^ k) q.2)) :=
    (ψ ^ (-k)).contMDiff.comp <| Φ.contMDiff.comp <|
      ((contMDiff_collaredSmoothTransitionUnit hn).comp
        ((contDiff_id.sub contDiff_const).contMDiff.comp contMDiff_fst)).prodMk
        ((φ ^ k).contMDiff.comp contMDiff_snd)
  have hmem : Ioo ((k : ℝ) - 1 / 4) (k + 1) ×ˢ (univ : Set M) ∈ 𝓝 p :=
    prod_mem_nhds (Ioo_mem_nhds (by linarith [Int.floor_le p.1]) (Int.lt_floor_add_one p.1))
      univ_mem
  exact (hG p).congr_of_eventuallyEq <| eventually_of_mem hmem fun q hq ↦
    by simp only [diffeotopyFamily_eq_of_mem_Ioo hΦ k hq.1, Diffeomorph.mul_apply,
      Diffeotopy.timeSlice_apply]

variable [T2Space M] [LocallyCompactSpace M] [IsManifold I n M]

/-- The diffeomorphism `[t, x] ↦ [t, g t x]` of mapping tori induced by a diffeotopy `Φ` of `M`
with `ψ ∘ Φ₁ = φ`, where `g` is the equivariant family
`TauCeti.SmoothMappingTorus.diffeotopyFamily φ ψ Φ`. So isotopic monodromies have diffeomorphic
mapping tori, by a diffeomorphism over the circle which is the identity on the fibre over `0`
(`TauCeti.SmoothMappingTorus.congrDiffeotopy_mk_zero`). -/
def congrDiffeotopy (Φ : Diffeotopy I n M) (hΦ : ψ * Φ.final = φ) (hn : n ≤ ∞) :
    SmoothMappingTorus φ ≃ₘ^n⟮𝓘(ℝ).prod I, 𝓘(ℝ).prod I⟯ SmoothMappingTorus ψ :=
  congrFamily (diffeotopyFamily φ ψ Φ) (contMDiff_diffeotopyFamily hΦ hn)
    (by simpa only [diffeotopyFamily_symm] using
      contMDiff_diffeotopyFamily (Φ.mul_final_symm_eq_of_mul_final_eq hΦ) hn)
    apply_diffeotopyFamily_add_one

/-- The diffeomorphism induced by a diffeotopy sends `[t, x]` to `[t, g t x]`, where `g` is the
equivariant family built from the diffeotopy. -/
@[simp]
theorem congrDiffeotopy_mk (hΦ : ψ * Φ.final = φ) (hn : n ≤ ∞) (t : ℝ) (x : M) :
    congrDiffeotopy Φ hΦ hn (mk φ t x) = mk ψ t (diffeotopyFamily φ ψ Φ t x) := by
  rw [congrDiffeotopy, coe_congrFamily, mapFamily_mk]

/-- For `t ∈ [0, 1]`, the diffeomorphism induced by a diffeotopy `Φ` sends `[t, x]` to
`[t, Φ_(c t) x]`, where `c` is the collared smooth transition. -/
theorem congrDiffeotopy_mk_of_mem_Icc (hΦ : ψ * Φ.final = φ) (hn : n ≤ ∞) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) (x : M) :
    congrDiffeotopy Φ hΦ hn (mk φ t x) = mk ψ t (Φ (collaredSmoothTransitionUnit t, x)) := by
  rw [congrDiffeotopy_mk, diffeotopyFamily_of_mem_Icc hΦ ht, Diffeotopy.timeSlice_apply]

/-- The diffeomorphism induced by a diffeotopy is the identity on the fibre over `0`. -/
theorem congrDiffeotopy_mk_zero (hΦ : ψ * Φ.final = φ) (hn : n ≤ ∞) (x : M) :
    congrDiffeotopy Φ hΦ hn (mk φ 0 x) = mk ψ 0 x := by
  rw [congrDiffeotopy_mk_of_mem_Icc hΦ hn ⟨le_rfl, zero_le_one⟩,
    collaredSmoothTransitionUnit_eq_zero_of_le (by norm_num), Diffeotopy.apply_zero]

/-- The diffeomorphism induced by a diffeotopy lies over the circle. -/
@[simp]
theorem proj_congrDiffeotopy (hΦ : ψ * Φ.final = φ) (hn : n ≤ ∞) (z : SmoothMappingTorus φ) :
    proj ψ (congrDiffeotopy Φ hΦ hn z) = proj φ z := by
  rw [congrDiffeotopy, coe_congrFamily, proj_mapFamily]

/-- The inverse of the diffeomorphism induced by a diffeotopy `Φ` is induced by the inverse
diffeotopy. -/
@[simp]
theorem congrDiffeotopy_symm (hΦ : ψ * Φ.final = φ) (hn : n ≤ ∞) :
    (congrDiffeotopy Φ hΦ hn).symm =
      congrDiffeotopy Φ.symm (Φ.mul_final_symm_eq_of_mul_final_eq hΦ) hn := by
  ext z
  obtain ⟨⟨t, x⟩, rfl⟩ := uncurry_mk_surjective ψ z
  simp [congrDiffeotopy, diffeotopyFamily_symm]

end SmoothMappingTorus

end TauCeti
