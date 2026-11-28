/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Transfer
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.UpperTriangular.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Matrix.Transvection

/-!
# Transfer of the line-stabiliser first-entry character on `GL_N(F)`

Let `F` be a field and `N > 0`. The stabiliser `TauCeti.lineStabilizer F N` of the line spanned by
the first basis vector in `GL (Fin N) F` is `blockTriangularGroup F (fun i ↦ min 1 i.val)`. Its
action on that line gives `TauCeti.lineStabilizerFirstEntry : lineStabilizer F N →* Fˣ`, sending
`g` to `g 0 0`. Over a finite field, its transfer (`MonoidHom.transfer`) to `GL (Fin N) F` is
`GeneralLinearGroup.det`.

## Provenance

Adapted from `grh-lean` (`https://github.com/lsernau/grh-lean`, commit
`72fead102f663d5c7a407964a13dc0cf9d977207`), file `src/New/Congruences/FirstOrder/OnePrime.lean`
(`New.Patching.residueLineStabilizer`, `New.Patching.firstEntry`,
`New.Patching.firstEntry_conj_diagGL`, `New.Patching.transfer_firstEntry_diagGL`,
`New.Patching.transfer_firstEntry`, `New.Patching.transfer_comp_firstEntry`).
-/

public section

open Matrix GeneralLinearGroup SpecialLinearGroup

namespace TauCeti

/-- The stabiliser in `GL (Fin N) F` of the line spanned by the first basis vector. -/
def lineStabilizer (F : Type*) [CommRing F] (N : ℕ) : Subgroup (GL (Fin N) F) :=
  blockTriangularGroup F fun i : Fin N ↦ min 1 i.val

/-- A matrix lies in `lineStabilizer F N` if and only if its first column vanishes below the
first entry. -/
theorem mem_lineStabilizer {F : Type*} [CommRing F] {N : ℕ} [NeZero N] {g : GL (Fin N) F} :
    g ∈ lineStabilizer F N ↔ ∀ i ≠ 0, g i 0 = 0 := by
  rw [lineStabilizer, mem_blockTriangularGroup_iff]
  refine ⟨fun hg i hi ↦ hg (by dsimp; have : i.val ≠ 0 := Fin.val_ne_of_ne hi; omega),
    fun hg i j hij ↦ ?_⟩
  dsimp at hij
  have hj : j = 0 := Fin.ext (by simp only [Fin.val_zero]; omega)
  have hi : i ≠ 0 := fun h ↦ by subst h; simp at hij
  subst hj
  exact hg i hi

/-- The first-entry character `g ↦ g 0 0` on `lineStabilizer F N`: the scalar by which `g` acts
on the line of the first basis vector. -/
noncomputable def lineStabilizerFirstEntry (F : Type*) [Field F] (N : ℕ) [NeZero N] :
    lineStabilizer F N →* Fˣ :=
  MonoidHom.toHomUnits
    { toFun g := (g : GL (Fin N) F) 0 0
      map_one' := by simp
      map_mul' g h := by
        change (∑ j : Fin N, (g : GL (Fin N) F) 0 j * (h : GL (Fin N) F) j 0) = _
        exact Fintype.sum_eq_single 0 fun j hj ↦ by
          rw [mem_lineStabilizer.mp h.property j hj, mul_zero] }

/-- If `h⁻¹ * d * h` stabilises the first line and `d = diagGL t`, then its first entry is `t i`
whenever `h i 0 ≠ 0`. -/
theorem lineStabilizerFirstEntry_conj_diagGL {F : Type*} [Field F] {N : ℕ} [NeZero N]
    {t : Fin N → Fˣ} {h d : GL (Fin N) F} (hd : d = diagGL t)
    (h_mem : h⁻¹ * d * h ∈ lineStabilizer F N) {i : Fin N} (hi : h i 0 ≠ 0) :
    lineStabilizerFirstEntry F N ⟨h⁻¹ * d * h, h_mem⟩ = t i := by
  refine Units.ext (mul_left_cancel₀ hi ?_)
  have hmul : (h * (h⁻¹ * d * h)) i 0 = h i 0 * (h⁻¹ * d * h) 0 0 := by
    change (∑ j : Fin N, h i j * (h⁻¹ * d * h) j 0) = _
    exact Fintype.sum_eq_single 0 fun j hj ↦ by rw [mem_lineStabilizer.mp h_mem j hj, mul_zero]
  calc h i 0 * lineStabilizerFirstEntry F N ⟨h⁻¹ * d * h, h_mem⟩
      = (h * (h⁻¹ * d * h)) i 0 := hmul.symm
    _ = (diagGL t * h) i 0 := by rw [mul_assoc, mul_inv_cancel_left, hd]
    _ = h i 0 * t i := by simp [mul_comm]

/-- Over a finite field `F`, the transfer of `lineStabilizerFirstEntry F N` to `GL (Fin N) F`
sends `diagGL (Pi.mulSingle 0 x)` to `x`. -/
theorem transfer_lineStabilizerFirstEntry_diagGL {F : Type*} [Field F] [Finite F] {N : ℕ}
    [NeZero N] (x : Fˣ) :
    (lineStabilizerFirstEntry F N).transfer (diagGL (Pi.mulSingle 0 x)) = x := by
  let H : Subgroup (GL (Fin N) F) := lineStabilizer F N
  set g : GL (Fin N) F := diagGL (Pi.mulSingle 0 x) with hg
  let Ω := Quotient (MulAction.orbitRel (Subgroup.zpowers g) (GL (Fin N) F ⧸ H))
  let _ : Fintype Ω := Fintype.ofFinite Ω
  have g_pow (f : ℕ) : g ^ f = diagGL (Pi.mulSingle 0 (x ^ f)) := by
    rw [hg, ← map_pow, Pi.mulSingle_pow]
  have g_mem : g ∈ H := mem_lineStabilizer.mpr fun i hi ↦ by simp [g, hi]
  let η₀ : GL (Fin N) F ⧸ H := ↑(1 : GL (Fin N) F)
  have eq_iff (η : GL (Fin N) F ⧸ H) : η₀ = η ↔ η.out ∈ H := by
    conv_lhs => rw [← η.out_eq', QuotientGroup.eq, inv_one, one_mul]
  have fixed (k : GL (Fin N) F) (hk : k ∈ H) : k • η₀ = η₀ := by
    simpa [η₀, QuotientGroup.eq] using hk
  rw [MonoidHom.transfer_eq_prod_quotient_orbitRel_zpowers_quot,
    Fintype.prod_eq_single (⟦η₀⟧ : Ω)]
  · have out_eq : η₀ = (⟦η₀⟧ : Ω).out := by
      obtain ⟨k, hk⟩ :=
        Quotient.mk_out (s := MulAction.orbitRel (Subgroup.zpowers g) (GL (Fin N) F ⧸ H)) η₀
      change (k : GL (Fin N) F) • η₀ = (⟦η₀⟧ : Ω).out at hk
      rw [← hk, fixed k (Subgroup.zpowers_le.mpr g_mem k.property)]
    have out_mem : (⟦η₀⟧ : Ω).out.out ∈ H := (eq_iff _).mp out_eq
    have entry_ne : (⟦η₀⟧ : Ω).out.out 0 0 ≠ 0 :=
      (lineStabilizerFirstEntry F N ⟨_, out_mem⟩).ne_zero
    have period : Function.minimalPeriod (g • ·) (⟦η₀⟧ : Ω).out = 1 :=
      Function.minimalPeriod_eq_one_iff_isFixedPt.mpr (by rw [← out_eq]; exact fixed g g_mem)
    rw [lineStabilizerFirstEntry_conj_diagGL (g_pow _) _ entry_ne, period, pow_one,
      Pi.mulSingle_eq_same]
  · intro q hq
    have not_mem : q.out.out ∉ H := fun h ↦ hq (by rw [(eq_iff q.out).mpr h, q.out_eq])
    obtain ⟨i, hi, entry_ne⟩ : ∃ i ≠ 0, q.out.out i 0 ≠ 0 := by
      simpa using mt mem_lineStabilizer.mpr not_mem
    rw [lineStabilizerFirstEntry_conj_diagGL (g_pow _) _ entry_ne, Pi.mulSingle_eq_of_ne hi]

/-- Over a finite field `F`, the transfer of `lineStabilizerFirstEntry F N` to `GL (Fin N) F`
is the determinant `GeneralLinearGroup.det`. -/
theorem transfer_lineStabilizerFirstEntry {F : Type*} [Field F] [Finite F] {N : ℕ} [NeZero N]
    (g : GL (Fin N) F) :
    (lineStabilizerFirstEntry F N).transfer g = GeneralLinearGroup.det g := by
  let _ : Fintype F := Fintype.ofFinite F
  set τ := (lineStabilizerFirstEntry F N).transfer
  have h_trans (t : TransvectionStruct (Fin N) F) : τ (toGL t.toSpecialLinearGroup) = 1 := by
    let ψ : F →+ Additive Fˣ :=
      .mk' (fun c ↦ .ofMul (τ (toGL (transvection t.hij c)))) (by simp [transvection_add])
    have pow_card : τ (toGL t.toSpecialLinearGroup) ^ Fintype.card F = 1 :=
      congrArg Additive.toMul (show Fintype.card F • ψ t.c = 0 by
        rw [← map_nsmul, card_nsmul_eq_zero, map_zero])
    exact Units.ext (by rw [← FiniteField.pow_card (τ (toGL t.toSpecialLinearGroup) : F),
      ← Units.val_pow_eq_pow_val, pow_card])
  have τ_diag : τ.comp diagGL = GeneralLinearGroup.det.comp diagGL := by
    refine MonoidHom.pi_ext fun i x ↦ ?_
    have hsq : (Equiv.swap (0 : Fin N) i).permMatrix F *
        (Equiv.swap (0 : Fin N) i).permMatrix F = 1 := by
      have htr : (Equiv.swap (0 : Fin N) i).trans (Equiv.swap 0 i) = Equiv.refl _ := by
        ext x; simp
      rw [Equiv.Perm.permMatrix, ← PEquiv.toMatrix_trans, ← Equiv.toPEquiv_trans, htr,
        Equiv.toPEquiv_refl, PEquiv.toMatrix_refl]
    let s : GL (Fin N) F := ⟨(Equiv.swap 0 i).permMatrix F, (Equiv.swap 0 i).permMatrix F, hsq, hsq⟩
    have hconj : s * diagGL (Pi.mulSingle 0 x) = diagGL (Pi.mulSingle i x) * s := by
      simpa [Pi.mulSingle_comp_equiv] using
        mul_diagGL_of_coe_eq_permMatrix s (Equiv.swap 0 i) rfl (Pi.mulSingle 0 x)
    have hτi : τ (diagGL (Pi.mulSingle i x)) = x := by
      have h1 : τ (diagGL (Pi.mulSingle i x)) = τ (diagGL (Pi.mulSingle 0 x)) :=
        mul_right_cancel (b := τ s) (by rw [← map_mul, ← hconj, map_mul, mul_comm])
      rw [h1, transfer_lineStabilizerFirstEntry_diagGL]
    exact hτi.trans <| Units.ext (by simp)
  let ⟨g', h, h'⟩ := diagonal_transvection_induction_of_det_ne_zero
    (fun M ↦ ∃ g' : GL (Fin N) F, (g' : Matrix _ _ F) = M ∧ τ g' = GeneralLinearGroup.det g')
    g g.det_ne_zero
    (fun D hD ↦ ⟨diagGL fun i ↦ .mk0 (D i) (by simp_all [Finset.prod_ne_zero_iff]),
      by simp [diagGL_coe], DFunLike.congr_fun τ_diag _⟩)
    (fun t ↦ ⟨toGL t.toSpecialLinearGroup, rfl, by simp [h_trans]⟩)
    (fun _ _ _ _ ⟨g₁, h₁, e₁⟩ ⟨g₂, h₂, e₂⟩ ↦ ⟨g₁ * g₂, by simp [h₁, h₂], by simp [e₁, e₂]⟩)
  simpa [Units.val_inj.mp h] using h'

/-- Over a finite field `F`, for any homomorphism `l : Fˣ →* A` into a commutative group `A`, the
transfer of `l.comp (lineStabilizerFirstEntry F N)` to `GL (Fin N) F` is
`l.comp GeneralLinearGroup.det`. -/
theorem transfer_comp_lineStabilizerFirstEntry {F A : Type*} [Field F] [Finite F] [CommGroup A]
    {N : ℕ} [NeZero N] (l : Fˣ →* A) :
    (l.comp (lineStabilizerFirstEntry F N)).transfer = l.comp GeneralLinearGroup.det := by
  ext g
  rw [MonoidHom.comp_apply, ← transfer_lineStabilizerFirstEntry, MonoidHom.transfer_def _ default,
    MonoidHom.transfer_def _ default]
  simp [Subgroup.leftTransversals.diff, map_prod]

end TauCeti
