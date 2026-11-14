/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.Weyl.LongestElement
public import TauCeti.RepresentationTheory.LSPath.Basic
import TauCeti.LinearAlgebra.RootSystem.Reduced

/-!
# Duality of Lakshmibai–Seshadri paths

For a dominant weight `λ` of a finite reduced root pairing, the contragredient dominant weight is
`λ* = -w₀ λ`, where `w₀` is the longest element of the Weyl group
(`TauCeti.neg_smul_mem_dominantChamber_longestElement_int`). Reversing the directions `(τ₀, …, τ_l)`
of a Lakshmibai–Seshadri path `π` of shape `λ` by right multiplication by `w₀` (followed by taking
minimal coset representatives in `W / W_{λ*}`) and replacing the break times `(a₀, …, a_{l+1})` by
`(1 - a_{l+1}, …, 1 - a₀)` produces a Lakshmibai–Seshadri path `π.dual hlam` of shape `-w₀ λ`.

On realized paths, `π.dual hlam` reverses the distinguished timed presentation
(`TauCeti.LSPath.timed_dual`) and therefore realizes the reversed path `(π.toPLPath 𝕜 f).reverse`
(`TauCeti.LSPath.toPLPath_dual`). Applying duality twice returns `π` up to the identity
`-w₀ (-w₀ λ) = λ` (`TauCeti.LSPath.dual_dual`), packaging duality as an equivalence
`TauCeti.LSPath.dualEquiv : LSPath P b λ ≃ LSPath P b (-w₀ λ)`.

## Main definitions

* `TauCeti.LSPath.dual`: the dual Lakshmibai–Seshadri path of shape `-w₀ λ`.
* `TauCeti.LSPath.dualEquiv`: the duality equivalence `LSPath P b λ ≃ LSPath P b (-w₀ λ)`.

## Main results

* `TauCeti.LSPath.timed_dual` and `TauCeti.LSPath.toPLPath_dual`: **the dual LS path realizes the
  reversed piecewise-linear path `(π.toPLPath 𝕜 f).reverse`.**
* `TauCeti.LSPath.dual_dual`: dualizing twice recovers the original LS path along
  `-w₀ (-w₀ λ) = λ`.

## References

* P. Littelmann, *Paths and root operators in representation theory*, Ann. of Math. 142 (1995),
  §§1–2, 4.
-/

public section

universe u w x

namespace TauCeti.LSPath

open RootPairing

variable {ι : Type u} {M : Type w} {N : Type x} [AddCommGroup M] [AddCommGroup N]
  {P : RootPairing ι ℤ M N} {b : P.Base} [Finite ι] [P.IsReduced]

/-- **The dual Lakshmibai–Seshadri path** of `π` of dominant shape `λ`, of contragredient dominant
shape `-w₀ λ`: its directions are the minimal coset representatives of `τ_{l-j} w₀` in
`W / W_{-w₀ λ}`, and its break times are `1 - a_{l+1-k}`. -/
noncomputable def dual {lam : M} (hlam : lam ∈ dominantChamber P b) (π : LSPath P b lam) :
    LSPath P b (-(longestElement P b • lam)) where
  length := π.length
  dir j :=
    ⟨(weylCoxeterSystem P b).minimalCosetRep
        (P.wallIndices b (-(longestElement P b • lam)))
        ((π.dir j.rev).1 * longestElement P b),
      (weylCoxeterSystem P b).isMinimalCosetRep_minimalCosetRep _ _⟩
  time k := 1 - π.time k.rev
  time_zero := by rw [Fin.rev_zero, π.time_last, sub_self]
  time_last := by rw [Fin.rev_last, π.time_zero, sub_zero]
  strictMono_time _ _ hk := sub_lt_sub_left (π.strictMono_time (Fin.rev_lt_rev.mpr hk)) 1
  dir_succ_ne j hj := by
    have hval := congrArg
      (fun u ↦ (weylCoxeterSystem P b).minimalCosetRep (P.wallIndices b lam)
        (u.1 * longestElement P b)) hj
    dsimp only at hval
    rw [(P.isLongest_longestElement b).minimalCosetRep_mul_minimalCosetRep_mul
        (conj_longestElement_mem_parabolic_wallIndices_int_iff hlam) (π.dir j.succ.rev).2,
      (P.isLongest_longestElement b).minimalCosetRep_mul_minimalCosetRep_mul
        (conj_longestElement_mem_parabolic_wallIndices_int_iff hlam) (π.dir j.castSucc.rev).2]
      at hval
    exact π.dir_succ_ne j (Fin.rev_injective (π.dir_injective (Subtype.ext hval)) ▸ rfl)
  exists_isAChain j := by
    obtain ⟨C, hhead, hlast, hC⟩ := π.exists_isAChain j.rev
    refine ⟨C.reverseMul (P.isLongest_longestElement b)
      (conj_longestElement_mem_parabolic_wallIndices_int_iff hlam), ?_, ?_, ?_⟩
    · refine Subtype.ext ?_
      have hj : j.rev.succ = j.castSucc.rev := by
        ext; simp only [Fin.val_rev, Fin.val_succ, Fin.val_castSucc]; omega
      rw [CoxeterSystem.MinimalCosetRepChain.head_reverseMul, hlast, hj]
    · refine Subtype.ext ?_
      have hj : j.rev.castSucc = j.succ.rev := by
        ext; simp only [Fin.val_rev, Fin.val_succ, Fin.val_castSucc]; omega
      rw [CoxeterSystem.MinimalCosetRepChain.last_reverseMul, hhead, hj]
    · have htime : j.castSucc.succ.rev = j.rev.castSucc.succ := by
        ext; simp [Fin.val_rev]; omega
      rw [htime]
      exact (isAChain_one_sub_reverseMul_iff hlam).mpr hC

@[simp]
theorem length_dual {lam : M} (hlam : lam ∈ dominantChamber P b) (π : LSPath P b lam) :
    (π.dual hlam).length = π.length :=
  (rfl)

@[simp]
theorem coe_dir_dual {lam : M} (hlam : lam ∈ dominantChamber P b) (π : LSPath P b lam)
    (j : Fin ((π.dual hlam).length + 1)) :
    ((π.dual hlam).dir j).1 =
      (weylCoxeterSystem P b).minimalCosetRep
        (P.wallIndices b (-(longestElement P b • lam)))
        ((π.dir (j.rev.cast (by rw [length_dual]))).1 * longestElement P b) :=
  (rfl)

@[simp]
theorem time_dual {lam : M} (hlam : lam ∈ dominantChamber P b) (π : LSPath P b lam)
    (k : Fin ((π.dual hlam).length + 2)) :
    (π.dual hlam).time k = 1 - π.time (k.rev.cast (by rw [length_dual])) :=
  (rfl)

@[simp]
theorem duration_dual {lam : M} (hlam : lam ∈ dominantChamber P b) (π : LSPath P b lam)
    (j : Fin ((π.dual hlam).length + 1)) :
    (π.dual hlam).duration j = π.duration (j.rev.cast (by rw [length_dual])) := by
  have hj : (j : ℕ) < π.length + 1 := by simpa using j.isLt
  have hsucc : (j.succ.rev.cast (by rw [length_dual])) =
      (j.rev.cast (by rw [length_dual])).castSucc := by
    ext; simp only [Fin.val_cast, Fin.val_rev, Fin.val_succ, Fin.val_castSucc, length_dual]; omega
  have hcast : (j.castSucc.rev.cast (by rw [length_dual])) =
      (j.rev.cast (by rw [length_dual])).succ := by
    ext; simp only [Fin.val_cast, Fin.val_rev, Fin.val_succ, Fin.val_castSucc, length_dual]; omega
  rw [duration_def, time_dual, time_dual, hsucc, hcast, duration_def]
  ring

/-- **Dualizing a Lakshmibai–Seshadri path twice recovers it** along `-w₀ (-w₀ λ) = λ`. -/
@[simp]
theorem dual_dual {lam : M} (hlam : lam ∈ dominantChamber P b) (π : LSPath P b lam) :
    ((π.dual hlam).dual (neg_smul_mem_dominantChamber_longestElement_int hlam)) =
      cast (by simp [smul_neg, smul_smul_longestElement]) π := by
  have hlam_eq : lam = -(longestElement P b • -(longestElement P b • lam)) := by
    simp [smul_neg, smul_smul_longestElement]
  set dd := (π.dual hlam).dual (neg_smul_mem_dominantChamber_longestElement_int hlam)
  refine ext ?_ ?_
  · refine List.ext_getElem (by simp [dd]) fun i h₁ h₂ ↦ Subtype.ext ?_
    have hi₁ : i < dd.length + 1 := by rwa [List.length_ofFn] at h₁
    have hi₂ : i < (cast hlam_eq π).length + 1 := by rwa [List.length_ofFn] at h₂
    have hi : i < π.length + 1 := by rwa [length_cast] at hi₂
    simp only [List.getElem_ofFn, dd, coe_dir_dual, coe_dir_cast]
    have hJ : P.wallIndices b (-(longestElement P b • -(longestElement P b • lam))) =
        P.wallIndices b lam := congrArg (P.wallIndices b) hlam_eq.symm
    have hidx : ((((⟨i, hi₁⟩ : Fin (dd.length + 1)).rev.cast
        (by rw [length_dual])).rev.cast (by rw [length_dual])) : Fin (π.length + 1)) =
        (⟨i, hi₂⟩ : Fin ((cast hlam_eq π).length + 1)).cast (by rw [length_cast]) := by
      ext
      simp only [Fin.val_cast, Fin.val_rev, dd, length_dual]
      omega
    exact (congrArg (fun K ↦ (weylCoxeterSystem P b).minimalCosetRep K _) hJ).trans
      (((P.isLongest_longestElement b).minimalCosetRep_mul_minimalCosetRep_mul
        (conj_longestElement_mem_parabolic_wallIndices_int_iff hlam) (π.dir _).2).trans
        (congrArg (fun k ↦ (π.dir k).1) hidx))
  · refine List.ext_getElem (by simp [dd]) fun i h₁ h₂ ↦ ?_
    have hi₂ : i < (cast hlam_eq π).length + 2 := by rwa [List.length_ofFn] at h₂
    have hi : i < π.length + 2 := by rwa [length_cast] at hi₂
    simp only [List.getElem_ofFn, dd, time_dual, time_cast, sub_sub_cancel]
    exact congrArg π.time
      (by ext; simp only [Fin.val_cast, Fin.val_rev, length_dual]; omega)

/-- **Duality as an equivalence** between Lakshmibai–Seshadri paths of shape `λ` and of shape
`-w₀ λ`. -/
noncomputable def dualEquiv {lam : M} (hlam : lam ∈ dominantChamber P b) :
    LSPath P b lam ≃ LSPath P b (-(longestElement P b • lam)) where
  toFun := dual hlam
  invFun ρ :=
    cast (by simp [smul_neg, smul_smul_longestElement])
      (ρ.dual (neg_smul_mem_dominantChamber_longestElement_int hlam))
  left_inv π := by simp
  right_inv ρ := by
    have hcast : ∀ {μ₁ μ₂ : M} (h : μ₁ = μ₂) (hμ₁ : μ₁ ∈ dominantChamber P b)
        (hμ₂ : μ₂ ∈ dominantChamber P b) (σ : LSPath P b μ₁),
        (cast h σ).dual hμ₂ =
          cast (congrArg (fun x ↦ -(longestElement P b • x)) h) (σ.dual hμ₁) := by
      intro μ₁ μ₂ h hμ₁ hμ₂ σ
      subst h
      simp
    have hdom₂ := neg_smul_mem_dominantChamber_longestElement_int
      (neg_smul_mem_dominantChamber_longestElement_int hlam)
    rw [hcast _ hdom₂ hlam, dual_dual, cast_cast]
    exact cast_rfl ρ

@[simp]
theorem dualEquiv_apply {lam : M} (hlam : lam ∈ dominantChamber P b) (π : LSPath P b lam) :
    dualEquiv hlam π = π.dual hlam :=
  (rfl)

section Realization

variable (𝕜 : Type*) {V : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [AddCommGroup V] [Module 𝕜 V] (f : M →+ V)

omit [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
/-- **The distinguished timed presentation of the dual LS path is the timed reversal of that of
`π`.** -/
@[simp]
theorem timed_dual {lam : M} (hlam : lam ∈ dominantChamber P b) (π : LSPath P b lam) :
    (π.dual hlam).timed 𝕜 f = PLPath.reverseTimed (π.timed 𝕜 f) := by
  have := P.flip_isReduced
  rw [timed_def, PLPath.reverseTimed_def, timed_def]
  refine List.ext_getElem (by simp) fun i h₁ h₂ ↦ ?_
  have hi₁ : i < (π.dual hlam).length + 1 := by rwa [List.length_ofFn] at h₁
  have hi : i < π.length + 1 := by rwa [length_dual] at hi₁
  simp only [List.getElem_ofFn, List.getElem_reverse, List.getElem_map, List.length_map,
    List.length_ofFn, coe_dir_dual, duration_dual, minimalCosetRep_mul_longestElement_smul hlam,
    map_neg, smul_neg]
  have hidx : (⟨i, hi₁⟩ : Fin ((π.dual hlam).length + 1)).rev.cast
      (by rw [length_dual]) = ⟨π.length + 1 - 1 - i, by omega⟩ := by
    ext
    simp only [Fin.val_cast, Fin.val_rev, length_dual]
    omega
  rw [hidx]

/-- **The dual Lakshmibai–Seshadri path realizes the reversed piecewise-linear path.** -/
@[simp]
theorem toPLPath_dual {lam : M} (hlam : lam ∈ dominantChamber P b) (π : LSPath P b lam) :
    (π.dual hlam).toPLPath 𝕜 f = (π.toPLPath 𝕜 f).reverse := by
  rw [toPLPath_def, timed_dual, PLPath.ofSegments_map_snd_reverseTimed, ← toPLPath_def]

@[simp]
theorem toPLPath_dualEquiv_symm {lam : M} (hlam : lam ∈ dominantChamber P b)
    (ρ : LSPath P b (-(longestElement P b • lam))) :
    ((dualEquiv hlam).symm ρ).toPLPath 𝕜 f = (ρ.toPLPath 𝕜 f).reverse := by
  rw [← PLPath.reverse_reverse (((dualEquiv hlam).symm ρ).toPLPath 𝕜 f), ← toPLPath_dual 𝕜 f hlam,
    ← dualEquiv_apply, (dualEquiv hlam).apply_symm_apply]

theorem endpoint_toPLPath_dual {lam : M} (hlam : lam ∈ dominantChamber P b) (π : LSPath P b lam) :
    ((π.dual hlam).toPLPath 𝕜 f).endpoint = -(π.toPLPath 𝕜 f).endpoint := by
  rw [toPLPath_dual, PLPath.endpoint_reverse]

end Realization

end TauCeti.LSPath
