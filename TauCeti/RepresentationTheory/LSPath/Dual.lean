/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.Weyl.ReversedChain
public import TauCeti.RepresentationTheory.LSPath.Basic

/-!
# Littelmann's dual Lakshmibai–Seshadri path

Let `P` be a finite reduced root datum with base `b`, and write `w₀` for the longest element of its
Weyl group (`TauCeti.longestElement`). For any weight `λ`, Littelmann's dual of an LS path
`π = (τ₀, …, τ_l; a₀, …, a_{l+1})` of shape `λ` is the LS path
`π^* = (τ_l w₀, …, τ₀ w₀; 1 - a_{l+1}, …, 1 - a₀)` of shape `-(w₀ • λ)`, where each coset is
represented by its minimal coset representative. By
`CoxeterSystem.MinimalCosetRepChain.isAChain_one_sub_reverseMul_longestElement_iff` and
`TauCeti.minimalCosetRep_mul_longestElement_smul`, its distinguished timed presentation is
`TauCeti.PLPath.reverseTimed (π.timed 𝕜 f)` and its path is `(π.toPLPath 𝕜 f).reverse`, with no
dominance assumption on `λ`. We also provide shape transport `TauCeti.LSPath.congr` along `λ = λ'`.

## Main definitions and results

* `TauCeti.LSPath.congr` and `TauCeti.LSPath.dual`: shape transport and Littelmann's duality
  `LSPath P b λ ≃ LSPath P b (-(w₀ • λ))`.
* `TauCeti.LSPath.timed_dual` and `TauCeti.LSPath.toPLPath_dual`: compatibility with
  `TauCeti.PLPath.reverseTimed` and `TauCeti.PLPath.reverse`.
* `TauCeti.LSPath.dual_symm_eq_congr_dual` and `TauCeti.LSPath.congr_dual_dual`: involutivity.

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

/-! ### Extensionality and transport along an equality of shapes -/

section Congr

/-- Two Lakshmibai–Seshadri encodings of the same shape are equal once their lengths, directions,
and break times agree pointwise. -/
theorem eq_of_length_dir_time {lam : M} {π π' : LSPath P b lam}
    (hlen : π.length = π'.length)
    (hdir : ∀ j : Fin (π.length + 1), (π.dir j).1 = (π'.dir (j.cast (by rw [hlen]))).1)
    (htime : ∀ k : Fin (π.length + 2), π.time k = π'.time (k.cast (by rw [hlen]))) :
    π = π' := by
  apply LSPath.ext
  · refine List.ext_getElem (by simp [hlen]) fun n h₁ _ ↦ Subtype.ext ?_
    rw [List.getElem_ofFn, List.getElem_ofFn]
    exact hdir ⟨n, by simpa only [List.length_ofFn] using h₁⟩
  · refine List.ext_getElem (by simp [hlen]) fun n h₁ _ ↦ ?_
    rw [List.getElem_ofFn, List.getElem_ofFn]
    exact htime ⟨n, by simpa only [List.length_ofFn] using h₁⟩

/-- Transport of Lakshmibai–Seshadri encodings along an equality of shape weights. -/
def congr {lam lam' : M} (h : lam = lam') : LSPath P b lam ≃ LSPath P b lam' :=
  h ▸ Equiv.refl _

@[simp]
theorem congr_refl (lam : M) :
    (congr (rfl : lam = lam) : LSPath P b lam ≃ LSPath P b lam) = Equiv.refl _ :=
  (rfl)

@[simp]
theorem congr_symm {lam lam' : M} (h : lam = lam') :
    (congr (P := P) (b := b) h).symm = congr h.symm := by subst h; rfl

@[simp]
theorem congr_trans {lam₁ lam₂ lam₃ : M} (h₁ : lam₁ = lam₂) (h₂ : lam₂ = lam₃) :
    (congr (P := P) (b := b) h₁).trans (congr h₂) = congr (h₁.trans h₂) := by subst h₁ h₂; rfl

@[simp]
theorem congr_congr {lam₁ lam₂ lam₃ : M} (h₁ : lam₁ = lam₂) (h₂ : lam₂ = lam₃)
    (π : LSPath P b lam₁) :
    congr h₂ (congr h₁ π) = congr (h₁.trans h₂) π := by subst h₁ h₂; rfl

@[simp]
theorem length_congr {lam lam' : M} (h : lam = lam') (π : LSPath P b lam) :
    (congr h π).length = π.length := by subst h; rfl

@[simp]
theorem dir_congr {lam lam' : M} (h : lam = lam') (π : LSPath P b lam)
    (j : Fin ((congr h π).length + 1)) :
    ((congr h π).dir j).1 = (π.dir (j.cast (by rw [length_congr]))).1 := by subst h; rfl

@[simp]
theorem time_congr {lam lam' : M} (h : lam = lam') (π : LSPath P b lam)
    (k : Fin ((congr h π).length + 2)) :
    (congr h π).time k = π.time (k.cast (by rw [length_congr])) := by subst h; rfl

@[simp]
theorem duration_congr {lam lam' : M} (h : lam = lam') (π : LSPath P b lam)
    (j : Fin ((congr h π).length + 1)) :
    (congr h π).duration j = π.duration (j.cast (by rw [length_congr])) := by subst h; rfl

@[simp]
theorem congr_straight {lam lam' : M} (h : lam = lam') :
    congr (P := P) (b := b) h (straight lam) = straight lam' := by subst h; rfl

section Realization

variable (𝕜 : Type*) {V : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [AddCommGroup V] [Module 𝕜 V] (f : M →+ V)

omit [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
@[simp]
theorem timed_congr {lam lam' : M} (h : lam = lam') (π : LSPath P b lam) :
    (congr h π).timed 𝕜 f = π.timed 𝕜 f := by subst h; rfl

@[simp]
theorem toPLPath_congr {lam lam' : M} (h : lam = lam') (π : LSPath P b lam) :
    (congr h π).toPLPath 𝕜 f = π.toPLPath 𝕜 f := by subst h; rfl

end Realization

end Congr

/-! ### Littelmann's dual Lakshmibai–Seshadri path -/

section Dual

/-- Auxiliary construction of Littelmann's dual LS path of shape `-(w₀ • λ)`. -/
private noncomputable def dualAux {lam : M} (π : LSPath P b lam) :
    LSPath P b (-(longestElement P b • lam)) where
  length := π.length
  dir j :=
    ⟨(weylCoxeterSystem P b).minimalCosetRep
        (P.wallIndices b (-(longestElement P b • lam)))
        ((π.dir j.rev).1 * longestElement P b),
      (weylCoxeterSystem P b).isMinimalCosetRep_minimalCosetRep _ _⟩
  time k := 1 - π.time k.rev
  time_zero := by simp [Fin.rev_zero, π.time_last]
  time_last := by simp [Fin.rev_last, π.time_zero]
  strictMono_time _ _ hk := sub_lt_sub_left (π.strictMono_time (Fin.rev_lt_rev.mpr hk)) 1
  dir_succ_ne j h := by
    have hinv {u : P.weylGroup} :=
      (P.isLongest_longestElement b).minimalCosetRep_mul_minimalCosetRep_mul
        (u := u) (conj_longestElement_mem_parabolic_wallIndices_iff lam)
    have heq : (π.dir j.rev.castSucc).1 = (π.dir j.rev.succ).1 := by
      rw [← hinv (π.dir j.rev.castSucc).2, ← hinv (π.dir j.rev.succ).2]
      exact congrArg (fun u ↦ (weylCoxeterSystem P b).minimalCosetRep (P.wallIndices b lam)
        (u * longestElement P b)) (by simpa [Fin.rev_succ, Fin.rev_castSucc] using congrArg (·.1) h)
    exact π.dir_succ_ne j.rev (Subtype.ext heq.symm)
  exists_isAChain j := by
    obtain ⟨C, hhead, hlast, hC⟩ := π.exists_isAChain j.rev
    refine ⟨C.reverseMul (P.isLongest_longestElement b)
      (conj_longestElement_mem_parabolic_wallIndices_iff lam),
      Subtype.ext (by rw [CoxeterSystem.MinimalCosetRepChain.head_reverseMul, hlast,
        Fin.rev_castSucc]),
      Subtype.ext (by rw [CoxeterSystem.MinimalCosetRepChain.last_reverseMul, hhead,
        Fin.rev_succ]), ?_⟩
    rw [show j.castSucc.succ.rev = j.rev.castSucc.succ from Fin.ext (by simp [Fin.val_rev]; omega)]
    exact C.isAChain_one_sub_reverseMul_longestElement_iff.mpr hC

private theorem dualAux_congr {lam lam' : M} (h : lam = lam') (π : LSPath P b lam) :
    dualAux (congr h π) =
      congr (congrArg (fun m ↦ -(longestElement P b • m)) h) (dualAux π) := by subst h; rfl

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
  refine eq_of_length_dir_time (by simp [dualAux]) (fun j ↦ ?_) (fun k ↦ ?_)
  · simp only [dir_congr, dualAux, Fin.rev_rev, hwall]
    exact (((P.isLongest_longestElement b).minimalCosetRep_mul_minimalCosetRep_mul
      (conj_longestElement_mem_parabolic_wallIndices_iff lam) (π.dir j).2).symm).trans
      (congrArg (fun i ↦ (weylCoxeterSystem P b).minimalCosetRep (P.wallIndices b lam)
        ((weylCoxeterSystem P b).minimalCosetRep (P.wallIndices b (-(longestElement P b • lam)))
          ((π.dir i).1 * longestElement P b) * longestElement P b)) (Fin.ext rfl))
  · simp only [time_congr, dualAux, Fin.rev_rev, sub_sub_cancel]
    exact congrArg π.time (Fin.ext rfl)

/-- **Littelmann's dual Lakshmibai–Seshadri path.** Reversing the directions by `w₀` and replacing
each break `a` by `1 - a` gives an equivalence between Lakshmibai–Seshadri paths of shape `λ` and
Lakshmibai–Seshadri paths of shape `-(w₀ • λ)`, realizing path reversal on `TauCeti.PLPath`
(`TauCeti.LSPath.toPLPath_dual`). -/
noncomputable def dual {lam : M} :
    LSPath P b lam ≃ LSPath P b (-(longestElement P b • lam)) where
  toFun := dualAux
  invFun π' := congr (neg_longestElement_smul_neg_longestElement_smul lam) (dualAux π')
  left_inv := congr_dualAux_dualAux
  right_inv π' := by rw [dualAux_congr]; exact congr_dualAux_dualAux π'

variable {lam : M} (π : LSPath P b lam)

@[simp]
theorem length_dual : (dual π).length = π.length :=
  (rfl)

/-- The `j`-th direction of `π^*` is the minimal coset representative of `τ_{l - j} w₀` in
`W / W_{-(w₀ • λ)}`. -/
@[simp]
theorem dir_dual (j : Fin ((dual π).length + 1)) :
    ((dual π).dir j).1 =
      (weylCoxeterSystem P b).minimalCosetRep
        (P.wallIndices b (-(longestElement P b • lam)))
        ((π.dir (j.cast (by rw [length_dual])).rev).1 * longestElement P b) :=
  (rfl)

/-- The `k`-th break of `π^*` is `1 - a_{l + 1 - k}`. -/
@[simp]
theorem time_dual (k : Fin ((dual π).length + 2)) :
    (dual π).time k = 1 - π.time (k.cast (by rw [length_dual])).rev :=
  (rfl)

/-- The durations of `π^*` are the durations of `π` in reverse order. -/
@[simp]
theorem duration_dual (j : Fin ((dual π).length + 1)) :
    (dual π).duration j = π.duration (j.cast (by rw [length_dual])).rev := by
  have hj : j.val < π.length + 1 := by simpa [length_dual] using j.isLt
  have hsucc :
      (j.succ.cast (congrArg (· + 2) (length_dual π))).rev =
        (j.cast (congrArg (· + 1) (length_dual π))).rev.castSucc :=
    Fin.ext (by simp [Fin.val_rev])
  have hcast :
      (j.castSucc.cast (congrArg (· + 2) (length_dual π))).rev =
        (j.cast (congrArg (· + 1) (length_dual π))).rev.succ :=
    Fin.ext (by simp [Fin.val_rev]; omega)
  rw [duration_def, time_dual, time_dual, hsucc, hcast, duration_def]
  ring

/-- The inverse of `dual` is `dual` followed by shape transport along
`-(w₀ • -(w₀ • λ)) = λ`. -/
theorem dual_symm_eq_congr_dual (π' : LSPath P b (-(longestElement P b • lam))) :
    dual.symm π' =
      congr (by simp [smul_neg, smul_smul_longestElement]) (dual π') :=
  (rfl)

/-- Applying `dual` twice returns the original LS path up to `-(w₀ • -(w₀ • λ)) = λ`. -/
@[simp]
theorem congr_dual_dual
    (h : -(longestElement P b • -(longestElement P b • lam)) = lam) :
    congr h (dual (dual π)) = π :=
  congr_dualAux_dualAux π

@[simp]
theorem dual_congr {lam' : M} (h : lam = lam') :
    dual (congr h π) =
      congr (congrArg (fun m ↦ -(longestElement P b • m)) h) (dual π) :=
  dualAux_congr h π

section Realization

variable (𝕜 : Type*) {V : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [AddCommGroup V] [Module 𝕜 V] (f : M →+ V)

omit [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
/-- **The distinguished timed presentation of `π^*` is the reversal of that of `π`.** Each segment
`d_j • f (τ_j • λ)` is negated and the list is traversed in reverse order. -/
@[simp]
theorem timed_dual :
    (dual π).timed 𝕜 f = PLPath.reverseTimed (π.timed 𝕜 f) := by
  apply List.ext_getElem
  · simp [timed_def, PLPath.reverseTimed_def]
  · intro n h₁ h₂
    simp only [timed_def, PLPath.reverseTimed_def, List.getElem_ofFn, List.getElem_reverse,
      List.length_map, List.length_ofFn, List.getElem_map, duration_dual, dir_dual]
    have hn : n < (dual π).length + 1 := by simpa only [timed_def, List.length_ofFn] using h₁
    have hidx :
        ((⟨n, hn⟩ : Fin ((dual π).length + 1)).cast (by rw [length_dual])).rev =
          ⟨(π.length + 1) - 1 - n, by simp [length_dual] at hn; omega⟩ :=
      Fin.ext (by simp [Fin.val_rev])
    rw [hidx, minimalCosetRep_mul_longestElement_smul lam, map_neg, smul_neg]

/-- **The piecewise-linear path of Littelmann's dual LS path `π^*` is the reversal of the
piecewise-linear path of `π`.** -/
@[simp]
theorem toPLPath_dual :
    (dual π).toPLPath 𝕜 f = (π.toPLPath 𝕜 f).reverse := by
  rw [toPLPath_def, timed_dual, PLPath.ofSegments_map_snd_reverseTimed, ← toPLPath_def]

@[simp]
theorem toPLPath_dual_symm (π' : LSPath P b (-(longestElement P b • lam))) :
    (dual.symm π').toPLPath 𝕜 f = (π'.toPLPath 𝕜 f).reverse := by
  rw [dual_symm_eq_congr_dual, toPLPath_congr, toPLPath_dual]

end Realization

end Dual

end TauCeti.LSPath
