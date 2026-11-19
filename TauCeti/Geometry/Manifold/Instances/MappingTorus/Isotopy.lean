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

Let `φ : M ≃ₘ^n⟮I, I⟯ M` and `ψ : N ≃ₘ^n⟮J, J⟯ N` be diffeomorphisms with smooth mapping tori
`Y_φ` and `Y_ψ` (`TauCeti.SmoothMappingTorus`). A time-dependent family of maps `g t : M → N`
satisfying the equivariance

`ψ ∘ g (t + 1) = g t ∘ φ`

induces the map `[t, x] ↦ [t, g t x]` of mapping tori
(`TauCeti.SmoothMappingTorus.mapFamily`). It lies over the circle, and it is `C^n` when
`(t, x) ↦ g t x` is. For a constant family the equivariance says that `g` intertwines `φ` and `ψ`,
and the induced map is `TauCeti.SmoothMappingTorus.map`. A family of diffeomorphisms whose
inverses are also jointly `C^n` induces a diffeomorphism `Y_φ ≃ Y_ψ`
(`TauCeti.SmoothMappingTorus.congrFamily`). Unlike the maps induced by conjugacies, these maps
need not intertwine the suspension flows.

The main application is to isotopic monodromies. Let `Φ` be a diffeotopy of `M`
(`TauCeti.Diffeotopy`), with time slices `Φ_s`, and let `ψ ∘ Φ₁ = φ`. Then `φ` and `ψ` are
isotopic, and their mapping tori are diffeomorphic over the circle
(`TauCeti.SmoothMappingTorus.congrDiffeotopy`). The family realizing the diffeomorphism is

`g t = ψ ^ (-⌊t⌋) ∘ Φ_(c (t - ⌊t⌋)) ∘ φ ^ ⌊t⌋`

(`TauCeti.SmoothMappingTorus.diffeotopyFamily`), where `c` is the collared smooth transition
`TauCeti.collaredSmoothTransitionUnit`, equal to `0` up to time `1 / 4` and to `1` from time
`3 / 4` on. The equivariance holds by construction. The family is jointly smooth because near an
integer time `k` both of its pieces equal `ψ ^ (-k) ∘ φ ^ k`, which is where `ψ ∘ Φ₁ = φ` enters.
On the fibre over `0` the diffeomorphism is the identity `[0, x] ↦ [0, x]`, and over `t ∈ [0, 1]`
it moves the fibre by `Φ_(c t)`.

This is how a perturbation of the monodromy within its isotopy class, for instance the composite
`ψ = φ ∘ Φ₁⁻¹` with the final map of a Hamiltonian isotopy, is transported to a diffeomorphism of
the suspensions.

## Main definitions

* `TauCeti.SmoothMappingTorus.mapFamily φ ψ g h`: the map `[t, x] ↦ [t, g t x]` induced by an
  equivariant family `g`.
* `TauCeti.SmoothMappingTorus.congrFamily e he he' h`: the diffeomorphism induced by an equivariant
  jointly smooth family of diffeomorphisms `e`.
* `TauCeti.SmoothMappingTorus.diffeotopyFamily φ ψ Φ`: the equivariant family built from a
  diffeotopy `Φ`.
* `TauCeti.SmoothMappingTorus.congrDiffeotopy Φ hΦ hn`: the diffeomorphism `Y_φ ≃ Y_ψ` over the
  circle induced by a diffeotopy `Φ` with `ψ ∘ Φ₁ = φ`.

## Main results

* `TauCeti.SmoothMappingTorus.mapFamily_mk`, `TauCeti.SmoothMappingTorus.proj_mapFamily`: the
  induced map sends `[t, x]` to `[t, g t x]` and lies over the circle.
* `TauCeti.SmoothMappingTorus.mapFamily_const`: constant families induce the maps of
  `TauCeti.SmoothMappingTorus.map`.
* `TauCeti.SmoothMappingTorus.mapFamily_mapFamily`: composition of families.
* `TauCeti.SmoothMappingTorus.contMDiff_mapFamily`: the induced map is `C^n` when the family is.
* `TauCeti.SmoothMappingTorus.contMDiff_diffeotopyFamily`: the family built from a diffeotopy is
  jointly `C^n`.
* `TauCeti.SmoothMappingTorus.congrDiffeotopy_mk_of_mem_Icc`,
  `TauCeti.SmoothMappingTorus.congrDiffeotopy_mk_zero`: the diffeomorphism induced by a diffeotopy
  is `[t, x] ↦ [t, Φ_(c t) x]` for `t ∈ [0, 1]`, and the identity on the fibre over `0`.

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
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] {H' : Type*} [TopologicalSpace H']
  {J : ModelWithCorners ℝ E' H'} {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
  {E'' : Type*} [NormedAddCommGroup E''] [NormedSpace ℝ E''] {H'' : Type*}
  [TopologicalSpace H''] {K : ModelWithCorners ℝ E'' H''} {P : Type*} [TopologicalSpace P]
  [ChartedSpace H'' P] {n : ℕ∞ω}

namespace SmoothMappingTorus

open Cover Function

/-! ### Maps induced by equivariant families -/

section MapFamily

variable (φ : M ≃ₘ^n⟮I, I⟯ M) (ψ : N ≃ₘ^n⟮J, J⟯ N) (g : ℝ → M → N)
  (h : ∀ t x, ψ (g (t + 1) x) = g t (φ x))

include h in
/-- The equivariance `ψ ∘ g (t + 1) = g t ∘ φ` extends to all integer shifts:
`ψ ^ k ∘ g (t + k) = g t ∘ φ ^ k`. -/
private theorem zpow_apply_add_intCast (k : ℤ) (t : ℝ) (x : M) :
    (ψ ^ k) (g (t + k) x) = g t ((φ ^ k) x) := by
  induction k using Int.induction_on generalizing t x with
  | zero => simp
  | succ k ih =>
    push_cast at ih ⊢
    rw [zpow_add_one, zpow_add_one, Diffeomorph.mul_apply, Diffeomorph.mul_apply, ← add_assoc,
      h, ih]
  | pred k ih =>
    push_cast at ih ⊢
    -- Write `x = φ (φ⁻¹ x)` and move one step of the equivariance to the time `t - k - 1`.
    have hk := h (t + (-(k : ℝ) - 1)) (φ.symm x)
    rw [φ.apply_symm_apply, show t + (-(k : ℝ) - 1) + 1 = t + -(k : ℝ) by ring] at hk
    rw [← hk, ← Diffeomorph.mul_apply, ← zpow_add_one, sub_add_cancel, ih, zpow_sub_one,
      Diffeomorph.mul_apply, Diffeomorph.inv_apply]

/-- The map `[t, x] ↦ [t, g t x]` of mapping tori induced by a family of maps `g t : M → N`
satisfying the equivariance `ψ ∘ g (t + 1) = g t ∘ φ`. It is well defined because the
equivariance extends to all integer shifts of time. For a constant family it is the map
`TauCeti.SmoothMappingTorus.map` (`TauCeti.SmoothMappingTorus.mapFamily_const`). -/
def mapFamily : SmoothMappingTorus φ → SmoothMappingTorus ψ :=
  MulAction.orbitRelQuotientLift
    (fun z ↦ mk ψ ((ofProd φ).symm z).1 (g ((ofProd φ).symm z).1 ((ofProd φ).symm z).2))
    fun k z ↦ by
      rw [ofProd_symm_smul, mk_add_intCast, zpow_apply_add_intCast φ ψ g h,
        ← Diffeomorph.mul_apply, ← zpow_add, add_neg_cancel, zpow_zero, Diffeomorph.one_apply]

/-- The induced map sends `[t, x]` to `[t, g t x]`. -/
@[simp]
theorem mapFamily_mk (t : ℝ) (x : M) : mapFamily φ ψ g h (mk φ t x) = mk ψ t (g t x) := by
  rw [mapFamily, mk_def φ, MulAction.orbitRelQuotientLift_mk, Equiv.symm_apply_apply]

/-- On `ℝ × M`, the induced map is `(t, x) ↦ (t, g t x)` followed by the quotient map of `Y_ψ`. -/
theorem mapFamily_comp_uncurry_mk :
    mapFamily φ ψ g h ∘ uncurry (mk φ) = uncurry (mk ψ) ∘ fun p : ℝ × M ↦ (p.1, g p.1 p.2) :=
  funext fun p ↦ mapFamily_mk φ ψ g h p.1 p.2

/-- The induced map lies over the circle. -/
@[simp]
theorem proj_mapFamily (z : SmoothMappingTorus φ) : proj ψ (mapFamily φ ψ g h z) = proj φ z := by
  obtain ⟨⟨t, x⟩, rfl⟩ := uncurry_mk_surjective φ z
  simp

/-- The induced map lies over the circle, as an equality of functions. -/
theorem proj_comp_mapFamily : proj ψ ∘ mapFamily φ ψ g h = proj φ :=
  funext (proj_mapFamily φ ψ g h)

/-- A constant family induces the map of `TauCeti.SmoothMappingTorus.map`: for a constant family
the equivariance says that `g` intertwines `φ` and `ψ`. -/
theorem mapFamily_const (g : M → N) (h : Semiconj g φ ψ) :
    mapFamily φ ψ (fun _ ↦ g) (fun _ x ↦ (h x).symm) = map φ ψ g h := by
  funext z
  obtain ⟨⟨t, x⟩, rfl⟩ := uncurry_mk_surjective φ z
  simp

/-- Maps induced by equivariant families respect composition of the families. -/
@[simp]
theorem mapFamily_mapFamily (χ : P ≃ₘ^n⟮K, K⟯ P) (g' : ℝ → N → P)
    (h' : ∀ t y, χ (g' (t + 1) y) = g' t (ψ y)) (z : SmoothMappingTorus φ) :
    mapFamily ψ χ g' h' (mapFamily φ ψ g h z) =
      mapFamily φ χ (fun t ↦ g' t ∘ g t) (fun t x ↦ by simp only [comp_apply, h', h]) z := by
  obtain ⟨⟨t, x⟩, rfl⟩ := uncurry_mk_surjective φ z
  simp

/-- The induced map is continuous when `(t, x) ↦ g t x` is. -/
theorem continuous_mapFamily (hg : Continuous fun p : ℝ × M ↦ g p.1 p.2) :
    Continuous (mapFamily φ ψ g h) :=
  continuous_orbitRelQuotientLift_iff.2 <| (continuous_uncurry_mk ψ).comp
    ((continuous_ofProd_symm φ).fst.prodMk (hg.comp (continuous_ofProd_symm φ)))

/-- The induced map is `C^n` when `(t, x) ↦ g t x` is. -/
theorem contMDiff_mapFamily [T2Space M] [LocallyCompactSpace M] [IsManifold I n M] [T2Space N]
    [LocallyCompactSpace N] [IsManifold J n N]
    (hg : ContMDiff (𝓘(ℝ).prod I) J n fun p : ℝ × M ↦ g p.1 p.2) :
    ContMDiff (𝓘(ℝ).prod I) (𝓘(ℝ).prod J) n (mapFamily φ ψ g h) := by
  rw [← (isLocalDiffeomorph_uncurry_mk φ).contMDiff_comp_iff (uncurry_mk_surjective φ) le_rfl,
    mapFamily_comp_uncurry_mk]
  exact (contMDiff_uncurry_mk ψ).comp (contMDiff_fst.prodMk hg)

end MapFamily

/-! ### Diffeomorphisms induced by equivariant families of diffeomorphisms -/

section CongrFamily

variable {φ : M ≃ₘ^n⟮I, I⟯ M} {ψ : N ≃ₘ^n⟮J, J⟯ N}

/-- The inverses of a family of diffeomorphisms satisfying the equivariance
`ψ ∘ e (t + 1) = e t ∘ φ` satisfy the equivariance `φ ∘ (e (t + 1))⁻¹ = (e t)⁻¹ ∘ ψ` in the
opposite direction. -/
theorem apply_symm_add_one {e : ℝ → M ≃ₘ^n⟮I, J⟯ N}
    (h : ∀ t x, ψ (e (t + 1) x) = e t (φ x)) (t : ℝ) (y : N) :
    φ ((e (t + 1)).symm y) = (e t).symm (ψ y) := by
  have h' := congrArg (e t).symm (h t ((e (t + 1)).symm y))
  rwa [Diffeomorph.apply_symm_apply, Diffeomorph.symm_apply_apply, eq_comm] at h'

variable [T2Space M] [LocallyCompactSpace M] [IsManifold I n M] [T2Space N]
  [LocallyCompactSpace N] [IsManifold J n N]

/-- The diffeomorphism `[t, x] ↦ [t, e t x]` of mapping tori induced by a family of
diffeomorphisms `e t : M ≃ N` satisfying the equivariance `ψ ∘ e (t + 1) = e t ∘ φ`, provided
`(t, x) ↦ e t x` and `(t, y) ↦ (e t)⁻¹ y` are `C^n`. Its inverse is induced by the inverse family
(`TauCeti.SmoothMappingTorus.coe_congrFamily_symm`). -/
def congrFamily (e : ℝ → M ≃ₘ^n⟮I, J⟯ N)
    (he : ContMDiff (𝓘(ℝ).prod I) J n fun p : ℝ × M ↦ e p.1 p.2)
    (he' : ContMDiff (𝓘(ℝ).prod J) I n fun p : ℝ × N ↦ (e p.1).symm p.2)
    (h : ∀ t x, ψ (e (t + 1) x) = e t (φ x)) :
    SmoothMappingTorus φ ≃ₘ^n⟮𝓘(ℝ).prod I, 𝓘(ℝ).prod J⟯ SmoothMappingTorus ψ where
  toFun := mapFamily φ ψ (fun t ↦ e t) h
  invFun := mapFamily ψ φ (fun t ↦ (e t).symm) (apply_symm_add_one h)
  left_inv z := by
    obtain ⟨⟨t, x⟩, rfl⟩ := uncurry_mk_surjective φ z
    simp
  right_inv z := by
    obtain ⟨⟨t, y⟩, rfl⟩ := uncurry_mk_surjective ψ z
    simp
  contMDiff_toFun := contMDiff_mapFamily φ ψ (fun t ↦ e t) h he
  contMDiff_invFun := contMDiff_mapFamily ψ φ (fun t ↦ (e t).symm) (apply_symm_add_one h) he'

variable (e : ℝ → M ≃ₘ^n⟮I, J⟯ N)
  (he : ContMDiff (𝓘(ℝ).prod I) J n fun p : ℝ × M ↦ e p.1 p.2)
  (he' : ContMDiff (𝓘(ℝ).prod J) I n fun p : ℝ × N ↦ (e p.1).symm p.2)
  (h : ∀ t x, ψ (e (t + 1) x) = e t (φ x))

/-- The diffeomorphism induced by an equivariant family is the map induced by the family. -/
@[simp]
theorem coe_congrFamily : ⇑(congrFamily e he he' h) = mapFamily φ ψ (fun t ↦ e t) h :=
  (rfl)

/-- The inverse of the diffeomorphism induced by an equivariant family is the map induced by the
inverse family. -/
@[simp]
theorem coe_congrFamily_symm :
    ⇑(congrFamily e he he' h).symm = mapFamily ψ φ (fun t ↦ (e t).symm) (apply_symm_add_one h) :=
  (rfl)

end CongrFamily

/-! ### Diffeomorphisms induced by diffeotopies -/

section Diffeotopy

/-- The equivariant family `t ↦ ψ ^ (-⌊t⌋) ∘ Φ_(c (t - ⌊t⌋)) ∘ φ ^ ⌊t⌋` built from a diffeotopy
`Φ`, where `c` is the collared smooth transition `TauCeti.collaredSmoothTransitionUnit`. It
satisfies `ψ ∘ g (t + 1) = g t ∘ φ`
(`TauCeti.SmoothMappingTorus.apply_diffeotopyFamily_add_one`), and when `ψ ∘ Φ₁ = φ` it is jointly
`C^n` (`TauCeti.SmoothMappingTorus.contMDiff_diffeotopyFamily`) and equals `Φ_(c t)` for
`t ∈ [0, 1]` (`TauCeti.SmoothMappingTorus.diffeotopyFamily_of_mem_Icc`). -/
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
  simp only [diffeotopyFamily_apply, Int.floor_add_one, Int.fract_add_one]
  rw [← Diffeomorph.mul_apply ψ, ← zpow_one_add, show (1 : ℤ) + -(⌊t⌋ + 1) = -⌊t⌋ by ring,
    zpow_add_one, Diffeomorph.mul_apply]

/-- The inverses of the family built from `Φ` form the family built from the inverse diffeotopy,
with the roles of `φ` and `ψ` exchanged. -/
theorem diffeotopyFamily_symm (t : ℝ) :
    (diffeotopyFamily φ ψ Φ t).symm = diffeotopyFamily ψ φ Φ.symm t := by
  rw [← Diffeomorph.inv_def, diffeotopyFamily, diffeotopyFamily, mul_inv_rev, mul_inv_rev,
    ← zpow_neg, ← zpow_neg, neg_neg, Diffeotopy.timeSlice_symm, ← Diffeomorph.inv_def, mul_assoc]

/-- On the time interval `[0, 1]`, the family built from a diffeotopy `Φ` with `ψ ∘ Φ₁ = φ` is
`Φ_(c t)`. -/
theorem diffeotopyFamily_of_mem_Icc (hΦ : ψ * Φ.final = φ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    diffeotopyFamily φ ψ Φ t = Φ.timeSlice (collaredSmoothTransitionUnit t) := by
  rcases eq_or_lt_of_le ht.2 with rfl | ht1
  · rw [diffeotopyFamily, Int.floor_one, Int.fract_one,
      collaredSmoothTransitionUnit_eq_zero_of_le (by norm_num),
      collaredSmoothTransitionUnit_eq_one_of_ge (by norm_num), Diffeotopy.timeSlice_zero,
      ← Diffeomorph.one_def, mul_one, zpow_neg_one, zpow_one, ← hΦ, inv_mul_cancel_left,
      Diffeotopy.final_def]
  · have hfl : ⌊t⌋ = 0 := Int.floor_eq_iff.2 ⟨by simpa using ht.1, by simpa using ht1⟩
    rw [diffeotopyFamily, hfl, Int.fract, hfl]
    simp

/-- Near the integer time `k`, on the open interval `(k - 1/4, k + 1)`, the family built from a
diffeotopy `Φ` with `ψ ∘ Φ₁ = φ` is `ψ ^ (-k) ∘ Φ_(c (t - k)) ∘ φ ^ k`: on `(k - 1/4, k)` both
expressions equal `ψ ^ (-k) ∘ φ ^ k`. -/
private theorem diffeotopyFamily_apply_of_mem_Ioo (hΦ : ψ * Φ.final = φ) (k : ℤ) {t : ℝ}
    (ht : t ∈ Ioo ((k : ℝ) - 1 / 4) (k + 1)) (x : M) :
    diffeotopyFamily φ ψ Φ t x =
      (ψ ^ (-k)) (Φ (collaredSmoothTransitionUnit (t - k), (φ ^ k) x)) := by
  rcases lt_or_ge t k with htk | htk
  · -- On `(k - 1/4, k)` the collar of the previous interval is at its final time.
    have hfl : ⌊t⌋ = k - 1 :=
      Int.floor_eq_iff.2 ⟨by push_cast; linarith [ht.1], by push_cast; linarith⟩
    have hfr : collaredSmoothTransitionUnit (Int.fract t) = 1 :=
      collaredSmoothTransitionUnit_eq_one_of_ge (by
        rw [← Int.self_sub_floor, hfl]; push_cast; linarith [ht.1])
    rw [diffeotopyFamily_apply, hfr, hfl, collaredSmoothTransitionUnit_eq_zero_of_le (by linarith),
      Diffeotopy.apply_zero, ← Diffeotopy.final_apply, show -(k - 1) = -k + 1 by ring,
      zpow_add_one, Diffeomorph.mul_apply, ← Diffeomorph.mul_apply ψ, hΦ,
      ← Diffeomorph.mul_apply φ, ← zpow_one_add, add_sub_cancel]
  · have hfl : ⌊t⌋ = k := Int.floor_eq_iff.2 ⟨htk, ht.2⟩
    rw [diffeotopyFamily_apply, ← Int.self_sub_floor, hfl]

/-- The family built from a diffeotopy `Φ` with `ψ ∘ Φ₁ = φ` is jointly `C^n` in `(t, x)`. Near
each integer time it agrees with a single smooth expression, because the collared transition is
constant near the ends of the unit interval. -/
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
    diffeotopyFamily_apply_of_mem_Ioo hΦ k hq.1 q.2

variable [T2Space M] [LocallyCompactSpace M] [IsManifold I n M]

/-- The diffeomorphism `[t, x] ↦ [t, g t x]` of mapping tori induced by a diffeotopy `Φ` of `M`
with `ψ ∘ Φ₁ = φ`, where `g` is the equivariant family
`TauCeti.SmoothMappingTorus.diffeotopyFamily φ ψ Φ`. So isotopic monodromies have diffeomorphic
mapping tori, by a diffeomorphism over the circle which is the identity on the fibre over `0`
(`TauCeti.SmoothMappingTorus.congrDiffeotopy_mk_zero`). -/
def congrDiffeotopy (Φ : Diffeotopy I n M) (hΦ : ψ * Φ.final = φ) (hn : n ≤ ∞) :
    SmoothMappingTorus φ ≃ₘ^n⟮𝓘(ℝ).prod I, 𝓘(ℝ).prod I⟯ SmoothMappingTorus ψ :=
  congrFamily (diffeotopyFamily φ ψ Φ) (contMDiff_diffeotopyFamily hΦ hn)
    (by
      simp_rw [diffeotopyFamily_symm]
      exact contMDiff_diffeotopyFamily (by
        rw [Diffeotopy.final_symm, ← Diffeomorph.inv_def, ← hΦ, mul_inv_cancel_right]) hn)
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

end Diffeotopy

end SmoothMappingTorus

end TauCeti
