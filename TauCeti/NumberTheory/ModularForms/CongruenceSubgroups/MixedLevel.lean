/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.CongruenceSubgroups.LevelSubgroup
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Map

/-!
# The mixed levels `Γ₁(N) ∩ Γ₀(M)`

For `N ∣ M`, the mixed level `Γ₁(N) ∩ Γ₀(M)` is the subgroup of `GL₂(ℤ / M)` of matrices
`!![a, b; c, d]` with `c = 0` and `a ≡ 1 mod N`: the intersection of the upper-triangular level
`TauCeti.GL2Borel (ZMod M)` with the preimage of `TauCeti.GL2Gamma1 (ZMod N)` under the reduction
`GL₂(ℤ / M) → GL₂(ℤ / N)`. Under the right action
`(P, Q) • !![a, b; c, d] = (a P + c Q, b P + d Q)` on ordered bases of `E[M]` it is the stabiliser
of the cyclic subgroup `⟨P⟩` of order `M` together with the point `(M / N) P` of order `N`.

The preimage of the mixed level in `SL(2, ℤ)` is `Γ₁(N) ⊓ Γ₀(M)`. The upper-left entry maps the
upper-triangular level onto `(ℤ / N)ˣ` with kernel the mixed level, so its index in
`GL₂(ℤ / M)` is `φ(N) [SL(2, ℤ) : Γ₀(M)] = φ(N) ψ(M)`. It contains `-1` exactly when `N ≤ 2`, and
its determinant image is all of `(ℤ / M)ˣ`. For `N = M` it is the level `Γ₁(N)`, and for `N = 1`
the level `Γ₀(M)`.

## Main definitions

* `TauCeti.GL2Gamma1Gamma0 h`: the mixed level `Γ₁(N) ∩ Γ₀(M)` in `GL₂(ℤ / M)`, for `h : N ∣ M`.

## Main results

* `TauCeti.GL2Gamma1Gamma0.comap_mapGL`: its preimage in `SL(2, ℤ)` is `Γ₁(N) ⊓ Γ₀(M)`.
* `TauCeti.GL2Gamma1Gamma0.index_eq`: its index is `φ(N) [SL(2, ℤ) : Γ₀(M)]`.
* `TauCeti.GL2Gamma1Gamma0.neg_one_mem_iff`: it contains `-1` exactly when `N ≤ 2`.
* `TauCeti.GL2Gamma1Gamma0.map_det`: its determinant image is all of `(ℤ / M)ˣ`.
* `TauCeti.GL2Gamma1Gamma0.of_dvd_refl` and `TauCeti.GL2Gamma1Gamma0.of_one_dvd`: the cases
  `N = M` and `N = 1`.

## References

* K. Česnavičius, *A modular description of `X₀(n)`*, Algebra Number Theory 11 (2017), §4.1.
-/

public section

open Matrix Matrix.SpecialLinearGroup CongruenceSubgroup

open scoped MatrixGroups

namespace TauCeti

variable {N M : ℕ} (h : N ∣ M)

/-- **The mixed level `Γ₁(N) ∩ Γ₀(M)`** in `GL₂(ℤ / M)`, for `N ∣ M`: the upper-triangular
matrices whose upper-left entry is `1` modulo `N`. -/
def GL2Gamma1Gamma0 : Subgroup (GL (Fin 2) (ZMod M)) :=
  (GL2Gamma1 (ZMod N)).comap (GeneralLinearGroup.map (ZMod.castHom h (ZMod N))) ⊓
    GL2Borel (ZMod M)

namespace GL2Gamma1Gamma0

variable {h}

@[simp]
theorem mem_iff {g : GL (Fin 2) (ZMod M)} :
    g ∈ GL2Gamma1Gamma0 h ↔
      ZMod.castHom h (ZMod N) ((g : Matrix (Fin 2) (Fin 2) (ZMod M)) 0 0) = 1 ∧
        (g : Matrix (Fin 2) (Fin 2) (ZMod M)) 1 0 = 0 := by
  simp only [GL2Gamma1Gamma0, Subgroup.mem_inf, Subgroup.mem_comap, GL2Gamma1.mem_iff,
    GL2Borel.mem_iff, GeneralLinearGroup.map_apply]
  constructor
  · rintro ⟨⟨h₀, -⟩, h₁⟩
    exact ⟨h₀, h₁⟩
  · rintro ⟨h₀, h₁⟩
    exact ⟨⟨h₀, by rw [h₁, map_zero]⟩, h₁⟩

variable (h)

theorem le_GL2Borel : GL2Gamma1Gamma0 h ≤ GL2Borel (ZMod M) :=
  inf_le_right

/-- Reducing `SL(2, ℤ)` modulo `M` and then modulo `N` is reducing modulo `N`. -/
theorem map_castHom_comp_mapGL :
    (GeneralLinearGroup.map (ZMod.castHom h (ZMod N))).comp
        (mapGL (R := ℤ) (n := Fin 2) (ZMod M)) = mapGL (ZMod N) := by
  ext γ i j
  simp [GeneralLinearGroup.map_apply]

/-- **The preimage of the mixed level in `SL(2, ℤ)` is `Γ₁(N) ⊓ Γ₀(M)`.** -/
@[simp]
theorem comap_mapGL : (GL2Gamma1Gamma0 h).comap (mapGL (ZMod M)) = Gamma1 N ⊓ Gamma0 M := by
  rw [GL2Gamma1Gamma0, Subgroup.comap_inf, Subgroup.comap_comap, map_castHom_comp_mapGL,
    comap_mapGL_GL2Gamma1, comap_mapGL_GL2Borel]

/-- The upper-left entry modulo `N` of an upper-triangular matrix, as a homomorphism to
`(ℤ / N)ˣ`; its kernel is the mixed level. -/
noncomputable def upperLeftHom : GL2Borel (ZMod M) →* (ZMod N)ˣ :=
  (ZMod.unitsMap h).comp ((MonoidHom.fst _ _).comp GL2Borel.diag)

theorem ker_upperLeftHom :
    (upperLeftHom h).ker = (GL2Gamma1Gamma0 h).subgroupOf (GL2Borel (ZMod M)) := by
  ext g
  simp only [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, mem_iff, upperLeftHom,
    MonoidHom.comp_apply, MonoidHom.coe_fst, Units.ext_iff, ZMod.unitsMap_val, Units.val_one,
    GL2Borel.diag_fst_val, GL2Borel.apply_one_zero, and_true]
  rfl

theorem upperLeftHom_surjective [NeZero M] : Function.Surjective (upperLeftHom h) :=
  (ZMod.unitsMap_surjective h).comp (Prod.fst_surjective.comp GL2Borel.diag_surjective)

/-- **`[Γ₀(M) : Γ₁(N) ∩ Γ₀(M)] = φ(N)`** in `GL₂(ℤ / M)`. -/
theorem relIndex_GL2Borel [NeZero M] :
    (GL2Gamma1Gamma0 h).relIndex (GL2Borel (ZMod M)) = N.totient := by
  have : NeZero N := ⟨fun hN ↦ NeZero.ne M (Nat.eq_zero_of_zero_dvd (hN ▸ h))⟩
  rw [Subgroup.relIndex, ← ker_upperLeftHom, Subgroup.index_ker,
    MonoidHom.range_eq_top_of_surjective _ (upperLeftHom_surjective h), Subgroup.card_top,
    Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]

/-- **The index of the mixed level is `φ(N) ψ(M)`**, where `ψ(M) = [SL(2, ℤ) : Γ₀(M)]`. -/
theorem index_eq [NeZero M] : (GL2Gamma1Gamma0 h).index = N.totient * (Gamma0 M).index := by
  rw [← Subgroup.relIndex_mul_index (le_GL2Borel h), relIndex_GL2Borel, index_GL2Borel_zmod]

/-- **`-1` lies in the mixed level exactly when `N ≤ 2`.** -/
theorem neg_one_mem_iff [NeZero M] : (-1 : GL (Fin 2) (ZMod M)) ∈ GL2Gamma1Gamma0 h ↔ N ≤ 2 := by
  have hN : N ≠ 0 := fun hN ↦ NeZero.ne M (Nat.eq_zero_of_zero_dvd (hN ▸ h))
  rw [GL2Gamma1Gamma0, Subgroup.mem_inf, Subgroup.mem_comap, GeneralLinearGroup.map_neg, map_one,
    GL2Gamma1.neg_one_mem_iff, and_iff_left GL2Borel.neg_one_mem]
  constructor
  · intro h1
    by_contra! h2
    have : Fact (2 < N) := ⟨h2⟩
    exact ZMod.neg_one_ne_one h1
  · intro h2
    have h1 : 1 ≤ N := Nat.pos_of_ne_zero hN
    interval_cases N <;> decide

/-- **The projective index of the mixed level** is its index for `N ≤ 2`. -/
theorem projectiveIndex_eq_index [NeZero M] (hN : N ≤ 2) :
    (GL2Gamma1Gamma0 h).projectiveIndex = (GL2Gamma1Gamma0 h).index :=
  Subgroup.projectiveIndex_eq_index ((neg_one_mem_iff h).mpr hN)

/-- **The projective index of the mixed level** is half its index for `N ≥ 3`. -/
theorem two_mul_projectiveIndex [NeZero M] (hN : 3 ≤ N) :
    2 * (GL2Gamma1Gamma0 h).projectiveIndex = (GL2Gamma1Gamma0 h).index :=
  Subgroup.two_mul_projectiveIndex ((neg_one_mem_iff h).not.mpr (by omega))

/-- **The determinant maps the mixed level onto `(ℤ / M)ˣ`**: `!![1, 0; 0, u]` has determinant
`u`. -/
theorem map_det : (GL2Gamma1Gamma0 h).map GeneralLinearGroup.det = ⊤ :=
  eq_top_iff.mpr fun u _ ↦
    ⟨GL2Borel.mk 1 u 0, mem_iff.mpr ⟨by simp [-ZMod.castHom_apply], by simp⟩, by simp⟩

/-- For `N = M` the mixed level is `Γ₁(N)`. -/
theorem of_dvd_refl : GL2Gamma1Gamma0 (dvd_refl N) = GL2Gamma1 (ZMod N) := by
  rw [GL2Gamma1Gamma0, ZMod.castHom_self, GeneralLinearGroup.map_id, Subgroup.comap_id,
    inf_eq_left]
  exact GL2Gamma1.le_GL2Borel

/-- For `N = 1` the mixed level is `Γ₀(M)`. -/
theorem of_one_dvd : GL2Gamma1Gamma0 (one_dvd M) = GL2Borel (ZMod M) := by
  rw [GL2Gamma1Gamma0, inf_eq_right]
  intro g _
  simp [Subsingleton.elim _ (1 : ZMod 1)]

end GL2Gamma1Gamma0

end TauCeti
