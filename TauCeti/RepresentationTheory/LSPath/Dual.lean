/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.Weyl.ReversedChain
public import TauCeti.RepresentationTheory.LSPath.Weight

/-!
# Littelmann's dual Lakshmibai–Seshadri path

For a finite reduced root pairing `P` with base `b` and longest element `w₀`, Littelmann's dual of
an LS path `π = (τ₀, …, τ_l; a₀, …, a_{l+1})` of shape `λ` is the path `π^*` of shape
`-(w₀ • λ)` whose coset sequence is `(τ_l w₀ W_{-w₀ λ}, …, τ₀ w₀ W_{-w₀ λ})` (encoded by their
minimal coset representatives `minimalCosetRep (P.wallIndices b (-(w₀ • λ))) (τ_{l - j} w₀)`) and
whose breaks are `(1 - a_{l+1}, …, 1 - a₀)`. Its distinguished timed presentation is
`PLPath.reverseTimed (π.timed 𝕜 f)` and its path is `(π.toPLPath 𝕜 f).reverse`, with no dominance
assumption on `λ`.

## Main definitions and results

* `TauCeti.LSPath.dual`: Littelmann's duality `LSPath P b λ ≃ LSPath P b (-(w₀ • λ))`.
* `TauCeti.LSPath.timed_dual`, `TauCeti.LSPath.toPLPath_dual`, `TauCeti.LSPath.weight_dual`.
* `TauCeti.LSPath.dual_symm_eq_congr_dual`, `TauCeti.LSPath.congr_dual_dual`.

## References

* P. Littelmann, *A Littlewood–Richardson rule for symmetrizable Kac–Moody algebras*, Invent.
  Math. 116 (1994), 329--346, Lemma 4.3.
* P. Littelmann, *Paths and root operators in representation theory*, Ann. of Math. 142 (1995),
  499--525, Section 4.
-/

public section

universe u w x

namespace TauCeti.LSPath

open RootPairing

variable {ι : Type u} {M : Type w} {N : Type x} [AddCommGroup M] [AddCommGroup N]
  {P : RootPairing ι ℤ M N} {b : P.Base} [Finite ι] [P.IsReduced]

/-! ### Littelmann's dual Lakshmibai–Seshadri path -/

private noncomputable def dualAux {lam : M} (π : LSPath P b lam) :
    LSPath P b (-(longestElement P b • lam)) where
  length := π.length
  dir j := ⟨(weylCoxeterSystem P b).minimalCosetRep (P.wallIndices b (-(longestElement P b • lam)))
      ((π.dir j.rev).val * longestElement P b),
    (weylCoxeterSystem P b).isMinimalCosetRep_minimalCosetRep _ _⟩
  time k := 1 - π.time k.rev
  time_zero := by simp [Fin.rev_zero, π.time_last]
  time_last := by simp [Fin.rev_last, π.time_zero]
  strictMono_time _ _ hk := sub_lt_sub_left (π.strictMono_time (Fin.rev_lt_rev.mpr hk)) 1
  dir_succ_ne j h := by
    have hinv {u : P.weylGroup} :=
      (P.isLongest_longestElement b).minimalCosetRep_mul_minimalCosetRep_mul
        (u := u) (conj_longestElement_mem_parabolic_wallIndices_iff lam)
    have heq : (π.dir j.rev.castSucc).val = (π.dir j.rev.succ).val := by
      rw [← hinv (π.dir j.rev.castSucc).property, ← hinv (π.dir j.rev.succ).property]
      exact congrArg (fun u ↦ (weylCoxeterSystem P b).minimalCosetRep (P.wallIndices b lam)
        (u * longestElement P b))
        (by simpa [Fin.rev_succ, Fin.rev_castSucc] using congrArg (·.val) h)
    exact π.dir_succ_ne j.rev (Subtype.ext heq.symm)
  exists_isAChain j := by
    obtain ⟨C, hhead, hlast, hC⟩ := π.exists_isAChain j.rev
    refine ⟨C.reverseMul (P.isLongest_longestElement b)
      (conj_longestElement_mem_parabolic_wallIndices_iff lam),
      Subtype.ext (by rw [C.head_reverseMul, hlast, Fin.rev_castSucc]),
      Subtype.ext (by rw [C.last_reverseMul, hhead, Fin.rev_succ]), ?_⟩
    rw [Fin.rev_succ, Fin.rev_castSucc, ← Fin.succ_castSucc]
    exact C.isAChain_one_sub_reverseMul_longestElement_iff.mpr hC

private theorem dualAux_congr {lam lam' : M} (h : lam = lam') (π : LSPath P b lam) :
    dualAux (congr h π) =
      congr (congrArg (fun m ↦ -(longestElement P b • m)) h) (dualAux π) := by subst h; simp

private theorem neg_longestElement_smul_neg_longestElement_smul (lam : M) :
    -(longestElement P b • -(longestElement P b • lam)) = lam := by
  simp [smul_neg, smul_smul_longestElement]

private theorem congr_dualAux_dualAux {lam : M} (π : LSPath P b lam) :
    congr (neg_longestElement_smul_neg_longestElement_smul (P := P) (b := b) lam)
        (dualAux (dualAux π)) = π := by
  have hwall : P.wallIndices b (-(longestElement P b • -(longestElement P b • lam))) =
      P.wallIndices b lam :=
    congrArg (P.wallIndices b) (neg_longestElement_smul_neg_longestElement_smul lam)
  symm
  refine ext' (by simp [dualAux]) (fun j ↦ ?_) (fun k ↦ ?_)
  · simp only [dir_congr, dualAux, Fin.rev_rev, hwall]
    exact ((P.isLongest_longestElement b).minimalCosetRep_mul_minimalCosetRep_mul
      (conj_longestElement_mem_parabolic_wallIndices_iff lam) (π.dir j).property).symm
  · have htime (m : Fin ((dualAux (dualAux π)).length + 2)) :
        (dualAux (dualAux π)).time m = π.time m.rev.rev := by
      dsimp only [dualAux]
      exact sub_sub_cancel _ _
    rw [time_congr, htime, Fin.rev_rev]
    exact congrArg π.time (Fin.ext (by simp))

/-- **Littelmann's dual Lakshmibai–Seshadri path** `LSPath P b λ ≃ LSPath P b (-(w₀ • λ))`,
realizing path reversal on `TauCeti.PLPath` (`TauCeti.LSPath.toPLPath_dual`). -/
noncomputable def dual {lam : M} : LSPath P b lam ≃ LSPath P b (-(longestElement P b • lam)) where
  toFun := dualAux
  invFun π' := congr (neg_longestElement_smul_neg_longestElement_smul lam) (dualAux π')
  left_inv := congr_dualAux_dualAux
  right_inv π' := by rw [dualAux_congr]; exact congr_dualAux_dualAux π'

variable {lam : M} (π : LSPath P b lam)

@[simp]
theorem length_dual : (dual π).length = π.length := (rfl)

/-- The `j`-th direction of `π^*` is the minimal coset representative of `τ_{l - j} w₀`. -/
@[simp]
theorem dir_dual (j : Fin ((dual π).length + 1)) :
    ((dual π).dir j).val = (weylCoxeterSystem P b).minimalCosetRep
      (P.wallIndices b (-(longestElement P b • lam)))
      ((π.dir (j.cast (by rw [length_dual])).rev).val * longestElement P b) := (rfl)

/-- The `k`-th break of `π^*` is `1 - a_{l + 1 - k}`. -/
@[simp]
theorem time_dual (k : Fin ((dual π).length + 2)) :
    (dual π).time k = 1 - π.time (k.cast (by rw [length_dual])).rev := (rfl)

/-- The durations of `π^*` are the durations of `π` in reverse order. -/
@[simp]
theorem duration_dual (j : Fin ((dual π).length + 1)) :
    (dual π).duration j = π.duration (j.cast (by rw [length_dual])).rev := by
  rw [duration_def, time_dual, time_dual, duration_def, Fin.cast_succ_eq, Fin.rev_succ,
    Fin.cast_castSucc, Fin.rev_castSucc]
  ring

/-- The inverse of `dual` is `dual` followed by shape transport along `-(w₀ • -(w₀ • λ)) = λ`. -/
theorem dual_symm_eq_congr_dual (π' : LSPath P b (-(longestElement P b • lam))) :
    dual.symm π' = congr (by simp [smul_neg, smul_smul_longestElement]) (dual π') := (rfl)

/-- Applying `dual` twice returns the original LS path up to `-(w₀ • -(w₀ • λ)) = λ`. -/
@[simp]
theorem congr_dual_dual (h : -(longestElement P b • -(longestElement P b • lam)) = lam) :
    congr h (dual (dual π)) = π := congr_dualAux_dualAux π

@[simp]
theorem dual_congr {lam' : M} (h : lam = lam') :
    dual (congr h π) = congr (congrArg (fun m ↦ -(longestElement P b • m)) h) (dual π) :=
  dualAux_congr h π

section Realization

variable (𝕜 : Type*) {V : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [AddCommGroup V] [Module 𝕜 V] (f : M →+ V)

omit [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
/-- **The distinguished timed presentation of `π^*` is the reversal of that of `π`.** -/
@[simp]
theorem timed_dual : (dual π).timed 𝕜 f = PLPath.reverseTimed (π.timed 𝕜 f) := by
  refine List.ext_getElem (by simp [timed_def, PLPath.reverseTimed_def]) fun n h₁ _ ↦ ?_
  simp only [timed_def, PLPath.reverseTimed_def, List.getElem_ofFn, List.getElem_reverse,
    List.length_map, List.length_ofFn, List.getElem_map, duration_dual, dir_dual]
  have hidx : ((⟨n, by simpa only [timed_def, List.length_ofFn] using h₁⟩ :
      Fin ((dual π).length + 1)).cast (by rw [length_dual])).rev =
      ⟨π.length - n, by simp only [timed_def, List.length_ofFn, length_dual] at h₁; omega⟩ :=
    Fin.ext (by simp [Fin.val_rev])
  rw [hidx, minimalCosetRep_mul_longestElement_smul lam, map_neg, smul_neg]
  simp only [Nat.add_sub_cancel]

/-- **The piecewise-linear path of `π^*` is the reversal of the path of `π`.** -/
@[simp]
theorem toPLPath_dual : (dual π).toPLPath 𝕜 f = (π.toPLPath 𝕜 f).reverse := by
  rw [toPLPath_def, timed_dual, PLPath.ofSegments_map_snd_reverseTimed, ← toPLPath_def]

@[simp]
theorem toPLPath_dual_symm (π' : LSPath P b (-(longestElement P b • lam))) :
    (dual.symm π').toPLPath 𝕜 f = (π'.toPLPath 𝕜 f).reverse := by
  rw [dual_symm_eq_congr_dual, toPLPath_congr, toPLPath_dual]

end Realization

/-- The weight of Littelmann's dual path `π^*` is the negative of the weight of `π`. -/
theorem weight_dual (hlam : lam ∈ dominantChamber P b)
    (hlam' : -(longestElement P b • lam) ∈ dominantChamber P b) :
    (dual π).weight hlam' = -π.weight hlam :=
  ((dual π).weight_eq_iff_toRatPLPath_endpoint hlam').mpr (by
    rw [toRatPLPath, toPLPath_dual, PLPath.endpoint_reverse, map_neg, ← toRatPLPath,
      ← apply_weight ℚ (TensorProduct.mk ℤ ℚ M 1).toAddMonoidHom hlam π,
      LinearMap.toAddMonoidHom_coe])

end TauCeti.LSPath
