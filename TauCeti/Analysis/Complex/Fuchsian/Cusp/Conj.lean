/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Fuchsian.Cusp.Horodisc
public import TauCeti.GroupTheory.GroupAction.ConjAct
import Mathlib.Algebra.Group.Subgroup.Actions

/-!
# Cusps of conjugate Fuchsian groups

Let `Γ ≤ PSL(2, ℝ)`, `g ∈ PSL(2, ℝ)`, and let `Γ' = g Γ g⁻¹`, written
`ConjAct.toConjAct g • Γ = Γ'`. Conjugation by `g` carries the parabolic elements of `Γ` fixing a
boundary point `c` to the parabolic elements of `Γ'` fixing `g • c`, so translation by `g` carries
the cusp points and the cusp orbits of `Γ` onto those of `Γ'`.

It also carries normalized cusp data. If `D` has cusp `c`, scaling `σ`, generator `γ` and width
`w`, then `D.conj h` has cusp `g • c`, scaling `σ g⁻¹`, generator `g γ g⁻¹` and the same width
`w`. Since `(σ g⁻¹) • (g • z) = σ • z`, the horodiscs of `D.conj h` are the translates by `g` of
those of `D`, and the q-coordinate of `D.conj h` at `g • z` is the q-coordinate of `D` at `z`.
This is what makes conjugation compatible with the cusp charts of the compactified quotients.

The conjugate is passed as a subgroup `Γ'` together with the equation `ConjAct.toConjAct g • Γ = Γ'`
rather than as the expression `ConjAct.toConjAct g • Γ`: the inverse transport is then the same
construction for `g⁻¹`, and an element of the normalizer of `Γ` acts on the cusps of `Γ` itself.

## Main declarations

* `Subgroup.isCuspPoint_smul_iff_of_conjAct_smul_eq`: `g • c` is a cusp point of `g Γ g⁻¹`
  exactly when `c` is a cusp point of `Γ`.
* `Subgroup.cuspOrbitConjEquiv`: the induced bijection of cusp orbits, with the identity and
  composition laws `Subgroup.cuspOrbitConjEquiv_one` and `Subgroup.cuspOrbitConjEquiv_trans`.
* `Subgroup.CuspDatum.conj`: the transported cusp datum, with
  `Subgroup.CuspDatum.cuspOrbit_conj` and the identity and composition laws
  `Subgroup.CuspDatum.conj_one` and `Subgroup.CuspDatum.conj_conj`.
* `TauCeti.Subgroup.CuspDatum.horodisc_conj` and
  `TauCeti.Subgroup.CuspDatum.coordinate_conj_smul`: transport of horodiscs and of the
  q-coordinate.

## References

* Svetlana Katok, *Fuchsian Groups*, Chicago Lectures in Mathematics, University of Chicago
  Press, 1992, §4.2.
* Fred Diamond and Jerry Shurman, *A First Course in Modular Forms*, Graduate Texts in
  Mathematics 228, Springer, 2005, §2.4.
-/

public noncomputable section

open MulAction UpperHalfPlane
open scoped MatrixGroups Pointwise

namespace Subgroup

open Matrix.ProjectiveSpecialLinearGroup

variable {Γ Γ' : Subgroup PSL(2, ℝ)} {g : PSL(2, ℝ)}

/-- **Cusp points of conjugate groups correspond.** If `Γ' = g Γ g⁻¹`, then `g • c` is a cusp
point of `Γ'` exactly when `c` is a cusp point of `Γ`: conjugation by `g` carries the parabolic
elements of `Γ` fixing `c` to the parabolic elements of `Γ'` fixing `g • c`. -/
theorem isCuspPoint_smul_iff_of_conjAct_smul_eq (h : ConjAct.toConjAct g • Γ = Γ')
    (c : OnePoint ℝ) : Γ'.IsCuspPoint (g • c) ↔ Γ.IsCuspPoint c := by
  subst h
  simp only [isCuspPoint_iff_exists_mem_stabilizer_isParabolic, MulAction.mem_stabilizer_iff,
    Subtype.exists, Subgroup.mk_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
    ← ConjAct.toConjAct_inv, ConjAct.toConjAct_smul, inv_inv]
  refine ⟨fun ⟨k, hk, hkc, hpar⟩ ↦ ⟨g⁻¹ * k * g, hk, ?_, (isParabolic_conj_iff' g k).mpr hpar⟩,
    fun ⟨k, hk, hkc, hpar⟩ ↦ ⟨g * k * g⁻¹, by simpa [mul_assoc] using hk, ?_,
      (isParabolic_conj_iff g k).mpr hpar⟩⟩
  · rw [mul_smul, mul_smul, hkc, inv_smul_smul]
  · rw [mul_smul, mul_smul, inv_smul_smul, hkc]

/-- **The cusp orbits of conjugate groups correspond**: if `Γ' = g Γ g⁻¹`, translation by `g`
sends the cusp orbit of `c` under `Γ` to the cusp orbit of `g • c` under `Γ'`. -/
def cuspOrbitConjEquiv (h : ConjAct.toConjAct g • Γ = Γ') : Γ.CuspOrbit ≃ Γ'.CuspOrbit :=
  Equiv.subtypeEquiv (p := Γ.IsCuspOrbit) (q := Γ'.IsCuspOrbit)
    (Quotient.congr (MulAction.toPerm g) fun c d ↦
      (TauCeti.MulAction.orbitRel_smul_smul_iff_of_conjAct_smul_eq h c d).symm)
    fun C ↦ Quotient.inductionOn' C fun c ↦ (isCuspOrbit_mk_iff c).trans
      ((isCuspPoint_smul_iff_of_conjAct_smul_eq h c).symm.trans (isCuspOrbit_mk_iff _).symm)

@[simp]
theorem cuspOrbitConjEquiv_cuspOrbitMk (h : ConjAct.toConjAct g • Γ = Γ') (c : Γ.cuspPoints) :
    cuspOrbitConjEquiv h (Γ.cuspOrbitMk c) =
      Γ'.cuspOrbitMk ⟨g • (c : OnePoint ℝ), mem_cuspPoints.mpr
        ((isCuspPoint_smul_iff_of_conjAct_smul_eq h c).mpr (mem_cuspPoints.mp c.2))⟩ :=
  Subtype.ext (by simp only [cuspOrbitConjEquiv, Equiv.subtypeEquiv_apply, cuspOrbitMk_val]; rfl)

/-- The inverse of the bijection of cusp orbits induced by `g` is the one induced by `g⁻¹`. -/
@[simp]
theorem cuspOrbitConjEquiv_symm (h : ConjAct.toConjAct g • Γ = Γ') :
    (cuspOrbitConjEquiv h).symm =
      cuspOrbitConjEquiv (by rw [← h, map_inv, inv_smul_smul] :
        ConjAct.toConjAct g⁻¹ • Γ' = Γ) := by
  refine Equiv.ext fun C ↦ ?_
  obtain ⟨c, rfl⟩ := cuspOrbitMk_surjective C
  rw [Equiv.symm_apply_eq, cuspOrbitConjEquiv_cuspOrbitMk, cuspOrbitConjEquiv_cuspOrbitMk]
  simp

/-- Conjugation by `1` induces the identity of the cusp orbits. -/
@[simp]
theorem cuspOrbitConjEquiv_one (h : ConjAct.toConjAct (1 : PSL(2, ℝ)) • Γ = Γ) :
    cuspOrbitConjEquiv h = Equiv.refl _ := by
  refine Equiv.ext fun C ↦ ?_
  obtain ⟨c, rfl⟩ := cuspOrbitMk_surjective C
  rw [cuspOrbitConjEquiv_cuspOrbitMk, Equiv.refl_apply]
  simp

/-- Conjugating by `g` and then by `g'` induces the same bijection of cusp orbits as conjugating
by `g' * g`. -/
@[simp]
theorem cuspOrbitConjEquiv_trans {Γ'' : Subgroup PSL(2, ℝ)} {g' : PSL(2, ℝ)}
    (h : ConjAct.toConjAct g • Γ = Γ') (h' : ConjAct.toConjAct g' • Γ' = Γ'') :
    (cuspOrbitConjEquiv h).trans (cuspOrbitConjEquiv h') =
      cuspOrbitConjEquiv (by rw [map_mul, mul_smul, h, h'] :
        ConjAct.toConjAct (g' * g) • Γ = Γ'') := by
  refine Equiv.ext fun C ↦ ?_
  obtain ⟨c, rfl⟩ := cuspOrbitMk_surjective C
  rw [Equiv.trans_apply, cuspOrbitConjEquiv_cuspOrbitMk, cuspOrbitConjEquiv_cuspOrbitMk,
    cuspOrbitConjEquiv_cuspOrbitMk]
  simp [mul_smul]

/-- **Transport of a normalized cusp datum to a conjugate group.** If `Γ' = g Γ g⁻¹` and `D` is a
cusp datum of `Γ` with cusp `c`, scaling `σ`, generator `γ` and width `w`, then `Γ'` has the cusp
datum with cusp `g • c`, scaling `σ g⁻¹`, generator `g γ g⁻¹` and the same width `w`. -/
def CuspDatum.conj (D : Γ.CuspDatum) (h : ConjAct.toConjAct g • Γ = Γ') : Γ'.CuspDatum where
  cusp := g • D.cusp
  scaling := D.scaling * g⁻¹
  generator := ⟨g * D.generator * g⁻¹, h ▸ by
    simpa [ConjAct.toConjAct_smul] using
      smul_mem_pointwise_smul _ (ConjAct.toConjAct g) Γ D.generator.2⟩
  width := D.width
  width_pos := D.width_pos
  zpowers_generator := by
    subst h
    ext k
    have hk : g⁻¹ * k * g ∈ Γ := by
      have := Subgroup.mem_pointwise_smul_iff_inv_smul_mem.mp k.2
      rwa [← ConjAct.toConjAct_inv, ConjAct.toConjAct_smul, inv_inv] at this
    -- `k` fixes `g • c` exactly when `g⁻¹ k g` fixes `c`, that is, is a power of `γ`
    have key := D.mem_stabilizer_iff (g := ⟨g⁻¹ * k * g, hk⟩)
    rw [MulAction.mem_stabilizer_iff, Subgroup.mk_smul, mul_smul, mul_smul,
      inv_smul_eq_iff] at key
    rw [mem_zpowers_iff, MulAction.mem_stabilizer_iff, Subgroup.smul_def, key]
    refine exists_congr fun n ↦ ?_
    simp only [Subtype.ext_iff, Subgroup.coe_zpow, conj_zpow]
    constructor
    · intro hn
      rw [← hn]
      group
    · intro hn
      rw [hn]
      group
  scaling_mul_generator_mul_inv := by
    simp only [mul_inv_rev, inv_inv]
    rw [← D.scaling_mul_generator_mul_inv]
    group

namespace CuspDatum

variable (D : Γ.CuspDatum) (h : ConjAct.toConjAct g • Γ = Γ')

@[simp]
theorem conj_cusp : (D.conj h).cusp = g • D.cusp :=
  (rfl)

@[simp]
theorem conj_scaling : (D.conj h).scaling = D.scaling * g⁻¹ :=
  (rfl)

@[simp]
theorem conj_width : (D.conj h).width = D.width :=
  (rfl)

@[simp]
theorem coe_conj_generator : ((D.conj h).generator : PSL(2, ℝ)) = g * D.generator * g⁻¹ :=
  (rfl)

/-- The transported cusp datum represents the image of the cusp orbit of `D`. -/
@[simp]
theorem cuspOrbit_conj : (D.conj h).cuspOrbit = cuspOrbitConjEquiv h D.cuspOrbit := by
  have hD : D.cuspOrbit = Γ.cuspOrbitMk ⟨D.cusp, mem_cuspPoints.mpr D.isCuspPoint⟩ :=
    Subtype.ext (by rw [cuspOrbit_val, cuspOrbitMk_val])
  rw [hD, cuspOrbitConjEquiv_cuspOrbitMk]
  exact Subtype.ext (by rw [cuspOrbit_val, cuspOrbitMk_val, conj_cusp])

/-- Transport of a cusp datum by conjugation by `1` is the identity. -/
@[simp]
theorem conj_one (h : ConjAct.toConjAct (1 : PSL(2, ℝ)) • Γ = Γ) : D.conj h = D :=
  CuspDatum.ext (by simp) (by simp)

/-- Transporting a cusp datum by conjugation by `g` and then by `g'` is transporting it by
conjugation by `g' * g`. -/
@[simp]
theorem conj_conj {Γ'' : Subgroup PSL(2, ℝ)} {g' : PSL(2, ℝ)}
    (h' : ConjAct.toConjAct g' • Γ' = Γ'') :
    (D.conj h).conj h' =
      D.conj (by rw [map_mul, mul_smul, h, h'] : ConjAct.toConjAct (g' * g) • Γ = Γ'') :=
  CuspDatum.ext (by simp [mul_smul]) (by simp [mul_assoc])

end CuspDatum

end Subgroup

namespace TauCeti.Subgroup.CuspDatum

variable {Γ Γ' : Subgroup PSL(2, ℝ)} {g : PSL(2, ℝ)} (D : Γ.CuspDatum)
  (h : ConjAct.toConjAct g • Γ = Γ')

/-- The translate by `g` of a point lies in a horodisc of the transported cusp datum exactly when
the point lies in the horodisc of the same height of the original datum. -/
theorem smul_mem_horodisc_conj_iff {A : ℝ} {z : ℍ} :
    g • z ∈ horodisc (D.conj h) A ↔ z ∈ horodisc D A := by
  rw [mem_horodisc, mem_horodisc, _root_.Subgroup.CuspDatum.conj_scaling, mul_smul,
    inv_smul_smul]

/-- The horodiscs of the transported cusp datum are the translates by `g` of the horodiscs of the
original datum. -/
theorem horodisc_conj (A : ℝ) : horodisc (D.conj h) A = g • horodisc D A := by
  ext z
  rw [Set.mem_smul_set_iff_inv_smul_mem, ← smul_mem_horodisc_conj_iff D h, smul_inv_smul]

/-- **The q-coordinate is compatible with conjugation**: the q-coordinate of the transported cusp
datum at `g • z` is the q-coordinate of the original datum at `z`. -/
@[simp]
theorem coordinate_conj_smul (z : ℍ) : coordinate (D.conj h) (g • z) = coordinate D z := by
  rw [coordinate_apply, coordinate_apply, _root_.Subgroup.CuspDatum.conj_scaling,
    _root_.Subgroup.CuspDatum.conj_width, mul_smul, inv_smul_smul]

end TauCeti.Subgroup.CuspDatum
