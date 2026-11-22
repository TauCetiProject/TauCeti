/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.TensorProduct.Tower
public import TauCeti.RepresentationTheory.LSPath.Distinguished
import TauCeti.LinearAlgebra.RootSystem.BaseChange.Basic
import TauCeti.LinearAlgebra.RootSystem.Reduced
import TauCeti.LinearAlgebra.RootSystem.Weyl.Orbit.Ray

/-!
# Faithful realization of Lakshmibai–Seshadri encodings

An LS encoding records minimal coset directions and rational breaks. Its timed presentation
recovers both: durations determine the breaks, and velocities determine the minimal coset
representatives for a dominant shape. Consequently an injective realization of the orbit gives
an injective map from encodings to timed presentations.

If distinct realized orbit weights never lie in the same ray, the distinguished-presentation
uniqueness theorem also recovers the timed presentation from the unparametrized path. Thus
`LSPath.toPLPath_injective` identifies encodings with their realized paths, rather than merely
counting presentations. This allows root operators on paths to be transferred to encodings
once their stability is established. Zero and central shapes are included; no regularity of
the dominant shape is required.

This file also defines the canonical rational realization `TauCeti.LSPath.toRatPLPath` in
`ℚ ⊗[ℤ] M`, its pushforward `TauCeti.LSPath.mapSemilinear_toRatPLPath` to arbitrary realizations
(valid for arbitrary shapes), and its injectivity (`TauCeti.LSPath.toRatPLPath_injective`) as well
as injectivity in any injective compatible realization
(`TauCeti.LSPath.toPLPath_injective_of_compatible`) for dominant shapes.

## References

* P. Littelmann, *Paths and root operators in representation theory*, Ann. of Math. 142 (1995),
  §4.
-/

public section

namespace TauCeti.LSPath

open RootPairing

variable {ι M N : Type*} [AddCommGroup M] [AddCommGroup N]
  {P : RootPairing ι ℤ M N} {b : P.Base} [Finite ι] [P.IsReduced]
  {lam : M}

section Timed

variable {𝕜 V : Type*} [Field 𝕜] [CharZero 𝕜] [AddCommGroup V] [Module 𝕜 V] {f : M →+ V}

/-- For a dominant shape, an LS encoding is determined by its timed presentation whenever the
realization separates orbit weights. No ray condition is needed for timed presentations. -/
theorem timed_injective (hlam : lam ∈ dominantChamber P b)
    (hf : Set.InjOn f (Set.range fun w : P.weylGroup ↦ w • lam)) :
    Function.Injective (fun π : LSPath P b lam ↦ π.timed 𝕜 f) := by
  have := P.flip_isReduced
  intro π π' h
  have hlen : π.length = π'.length := by
    have := congrArg List.length h
    simpa only [timed_def, List.length_ofFn, Nat.add_right_cancel_iff] using this
  -- Align the finite index types before recovering durations and velocities entry by entry.
  cases π with
  | mk l dir time hzero hlast hmono hne hchain =>
    cases π' with
    | mk l' dir' time' hzero' hlast' hmono' hne' hchain' =>
      dsimp only at hlen
      subst l'
      simp only [timed_def, duration_def] at h
      have hentry := List.ofFn_injective h
      have hduration (j : Fin (l + 1)) :
          time j.succ - time j.castSucc = time' j.succ - time' j.castSucc := by
        have heq : ((time j.succ - time j.castSucc : ℚ) : 𝕜) =
            ((time' j.succ - time' j.castSucc : ℚ) : 𝕜) :=
          congrArg Prod.fst (congrFun hentry j)
        exact_mod_cast heq
      have htime : time = time' := by
        funext j
        induction j using Fin.induction with
        | zero => exact hzero.trans hzero'.symm
        | succ j ih =>
          have := hduration j
          linarith
      have hdir : dir = dir' := by
        funext j
        have hseg := congrArg Prod.snd (congrFun hentry j)
        have hd : ((time j.succ - time j.castSucc : ℚ) : 𝕜) ≠ 0 := by
          exact Rat.cast_ne_zero.mpr (sub_pos.mpr (hmono j.castSucc_lt_succ)).ne'
        rw [← htime] at hseg
        exact eq_of_isMinimalCosetRep_of_smul_apply_smul_eq hlam hf hd hseg
      subst dir'
      subst time'
      rfl

end Timed

section PLPath

variable {𝕜 V : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [AddCommGroup V] [Module 𝕜 V] {f : M →+ V}

/-- For a dominant shape whose realized orbit has no distinct weights on the same ray, the
unparametrized piecewise-linear path determines the entire LS encoding, including its breaks. -/
theorem toPLPath_injective (hlam : lam ∈ dominantChamber P b)
    (hf : Set.InjOn f (Set.range fun w : P.weylGroup ↦ w • lam))
    (hS : (Set.range fun w : P.weylGroup ↦ f (w • lam)).Pairwise
      fun u v ↦ ¬ SameRay 𝕜 u v) :
    Function.Injective (fun π : LSPath P b lam ↦ π.toPLPath 𝕜 f) := by
  have := P.flip_isReduced
  intro π π' h
  apply timed_injective (𝕜 := 𝕜) hlam hf
  simp only [toPLPath_def] at h
  exact (π.isDistinguished_timed 𝕜 f hlam hf).unique
    (π'.isDistinguished_timed 𝕜 f hlam hf) hS h

/-- Equality of realized LS paths is exactly equality of encodings. -/
@[simp]
theorem toPLPath_inj (hlam : lam ∈ dominantChamber P b)
    (hf : Set.InjOn f (Set.range fun w : P.weylGroup ↦ w • lam))
    (hS : (Set.range fun w : P.weylGroup ↦ f (w • lam)).Pairwise
      fun u v ↦ ¬ SameRay 𝕜 u v) {π π' : LSPath P b lam} :
    π.toPLPath 𝕜 f = π'.toPLPath 𝕜 f ↔ π = π' :=
  (toPLPath_injective hlam hf hS).eq_iff

/-- In any injective compatible realization `(𝕜, V, f, F)`, no two distinct points of a realized
Weyl orbit lie on the same ray: the sum of squares of all coroot pairings is Weyl-invariant. -/
theorem pairwise_not_sameRay_of_compatible {f : M →+ V} (hf : Function.Injective f)
    {F : b.support → Module.Dual 𝕜 V}
    (hF : ∀ (i : b.support) (x : M), F i (f x) = (P.coroot' i x : 𝕜)) (lam : M) :
    (Set.range fun w : P.weylGroup ↦ f (w • lam)).Pairwise fun u v ↦ ¬ SameRay 𝕜 u v := by
  have := P.flip_isReduced
  rintro _ ⟨w₁, rfl⟩ _ ⟨w₂, rfl⟩ hne hray
  have hw_ne_zero (w : P.weylGroup) : f (w • lam) ≠ 0 := by
    intro h0
    have hw0 : w • lam = 0 := hf (h0.trans (map_zero f).symm)
    have hlam0 : lam = 0 := by
      rw [← inv_smul_smul w lam, hw0, smul_zero]
    exact hne (by simp [hlam0])
  obtain ⟨r₁, r₂, hr₁, hr₂, hsmul⟩ := hray.exists_pos (hw_ne_zero w₁) (hw_ne_zero w₂)
  have hsimple (i : b.support) :
      r₁ * (P.coroot' i (w₁ • lam) : 𝕜) = r₂ * (P.coroot' i (w₂ • lam) : 𝕜) := by
    have := congrArg (F i) hsmul
    simpa only [map_smul, smul_eq_mul, hF] using this
  have hpos (j : ι) (hj : j ∈ posRoots P b) :
      r₁ * (P.coroot' j (w₁ • lam) : 𝕜) = r₂ * (P.coroot' j (w₂ • lam) : 𝕜) := by
    obtain ⟨c, -, hsum⟩ := exists_coroot'_eq_sum_nat_of_mem_posRoots P b hj
    simp only [hsum, LinearMap.sum_apply, LinearMap.smul_apply, Nat.cast_smul_eq_nsmul,
      nsmul_eq_mul, Int.cast_sum, Int.cast_mul, Int.cast_natCast, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    rw [← mul_assoc, mul_comm r₁, mul_assoc, hsimple ⟨i, hi⟩, ← mul_assoc, mul_comm _ r₂, mul_assoc]
  have hcoroot (j : ι) :
      r₁ * (P.coroot' j (w₁ • lam) : 𝕜) = r₂ * (P.coroot' j (w₂ • lam) : 𝕜) := by
    let := P.indexNeg
    rcases Base.IsPos.or_neg b j with hj | hj
    · exact hpos j ((mem_posRoots P b j).mpr hj)
    · have h := hpos (-j) ((mem_posRoots P b (-j)).mpr hj)
      simpa only [indexNeg_neg, coroot'_reflectionPerm_self, LinearMap.neg_apply, Int.cast_neg,
        mul_neg, neg_inj] using h
  let := Fintype.ofFinite ι
  have hsq_inv (w : P.weylGroup) :
      ∑ j : ι, (P.coroot' j (w • lam) : 𝕜) ^ 2 = ∑ j : ι, (P.coroot' j lam : 𝕜) ^ 2 := by
    calc ∑ j : ι, (P.coroot' j (w • lam) : 𝕜) ^ 2
        = ∑ j : ι, (P.coroot' (P.weylGroupToPerm w⁻¹ j) lam : 𝕜) ^ 2 := by
          refine Finset.sum_congr rfl fun j _ ↦ ?_
          have hc := P.coroot'_weylGroupToPerm_smul w⁻¹ j (w • lam)
          rw [inv_smul_smul] at hc
          rw [hc]
      _ = ∑ j : ι, (P.coroot' j lam : 𝕜) ^ 2 :=
          Equiv.sum_comp (P.weylGroupToPerm w⁻¹) fun j ↦ (P.coroot' j lam : 𝕜) ^ 2
  have hS : r₁ ^ 2 * ∑ j : ι, (P.coroot' j (w₁ • lam) : 𝕜) ^ 2 =
      r₂ ^ 2 * ∑ j : ι, (P.coroot' j (w₁ • lam) : 𝕜) ^ 2 := by
    calc r₁ ^ 2 * ∑ j : ι, (P.coroot' j (w₁ • lam) : 𝕜) ^ 2
        = ∑ j : ι, (r₁ * (P.coroot' j (w₁ • lam) : 𝕜)) ^ 2 := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun j _ ↦ by ring
      _ = ∑ j : ι, (r₂ * (P.coroot' j (w₂ • lam) : 𝕜)) ^ 2 :=
          Finset.sum_congr rfl fun j _ ↦ congrArg (· ^ 2) (hcoroot j)
      _ = r₂ ^ 2 * ∑ j : ι, (P.coroot' j (w₂ • lam) : 𝕜) ^ 2 := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun j _ ↦ by ring
      _ = r₂ ^ 2 * ∑ j : ι, (P.coroot' j (w₁ • lam) : 𝕜) ^ 2 := by
          rw [hsq_inv w₂, ← hsq_inv w₁]
  by_cases hsum0 : ∑ j : ι, (P.coroot' j (w₁ • lam) : 𝕜) ^ 2 = 0
  · rw [Finset.sum_eq_zero_iff_of_nonneg fun j _ ↦ sq_nonneg _] at hsum0
    have hzero : ∀ i ∈ b.support, P.coroot' i (w₁ • lam) = 0 := fun i _ ↦ by
      have hi := sq_eq_zero_iff.mp (hsum0 i (Finset.mem_univ i))
      exact Int.cast_eq_zero.mp hi
    have hfix : w₁ • lam = lam := by
      have h := smul_eq_self_of_forall_coroot'_eq_zero b hzero w₁⁻¹
      rw [inv_smul_smul] at h
      exact h.symm
    have hfix2 : w₂ • lam = w₁ • lam := by
      rw [hfix]
      have hzero' : ∀ i ∈ b.support, P.coroot' i lam = 0 := fun i hi ↦ hfix ▸ hzero i hi
      exact smul_eq_self_of_forall_coroot'_eq_zero b hzero' w₂
    exact hne (congrArg f hfix2.symm)
  · have hr : r₁ = r₂ := (sq_eq_sq₀ hr₁.le hr₂.le).mp (mul_right_cancel₀ hsum0 hS)
    rw [hr] at hsmul
    exact hne (smul_right_injective V hr₂.ne' hsmul)

/-- In any injective compatible realization `(𝕜, V, f, F)`, the realized piecewise-linear path
determines the LS encoding of a dominant shape without needing an explicit ray-separation
hypothesis. -/
theorem toPLPath_injective_of_compatible (hlam : lam ∈ dominantChamber P b)
    {f : M →+ V} (hf : Function.Injective f) {F : b.support → Module.Dual 𝕜 V}
    (hF : ∀ (i : b.support) (x : M), F i (f x) = (P.coroot' i x : 𝕜)) :
    Function.Injective (fun π : LSPath P b lam ↦ π.toPLPath 𝕜 f) :=
  toPLPath_injective hlam hf.injOn (pairwise_not_sameRay_of_compatible hf hF lam)

end PLPath

section Rational

open scoped TensorProduct

/-- The canonical rational piecewise-linear realization of an LS path in `ℚ ⊗[ℤ] M`. -/
noncomputable abbrev toRatPLPath (π : LSPath P b lam) : PLPath ℚ (ℚ ⊗[ℤ] M) :=
  π.toPLPath ℚ (TensorProduct.mk ℤ ℚ M 1).toAddMonoidHom

/-- Pushing `LSPath.toRatPLPath` forward along the canonical semilinear extension of `f : M →+ V`
yields `π.toPLPath 𝕜 f`. -/
theorem mapSemilinear_toRatPLPath {𝕜 V : Type*} [Field 𝕜] [LinearOrder 𝕜]
    [IsStrictOrderedRing 𝕜] [AddCommGroup V] [Module 𝕜 V] (f : M →+ V) (π : LSPath P b lam) :
    π.toRatPLPath.mapSemilinear (f.liftBaseChangeSemilinear (Rat.castHom 𝕜)) =
      π.toPLPath 𝕜 f := by
  rw [toRatPLPath, mapSemilinear_toPLPath ℚ _ _ (Rat.cast_mono (K := 𝕜)),
    AddMonoidHom.liftBaseChangeSemilinear_comp_mk]

/-- In the canonical rational realization `ℚ ⊗[ℤ] M`, no two distinct points of a Weyl orbit lie
on the same ray. -/
theorem pairwise_not_sameRay_toRatPLPath (P : RootPairing ι ℤ M N) (b : P.Base) [P.IsReduced]
    (lam : M) :
    (Set.range fun w : P.weylGroup ↦
      (TensorProduct.mk ℤ ℚ M 1).toAddMonoidHom (w • lam)).Pairwise
        fun u v ↦ ¬ SameRay ℚ u v := by
  have := P.finite_weylGroup_of_base b
  simpa only [LinearMap.toAddMonoidHom_coe] using
    P.pairwise_not_sameRay_tensorProduct_mk_orbit ℚ lam

/-- The canonical rational realization `LSPath.toRatPLPath` is injective for any dominant shape. -/
theorem toRatPLPath_injective (hlam : lam ∈ dominantChamber P b) :
    Function.Injective (toRatPLPath (P := P) (b := b) (lam := lam)) :=
  toPLPath_injective hlam (P.tensorProduct_mk_injective ℚ).injOn
    (pairwise_not_sameRay_toRatPLPath P b lam)

end Rational

end TauCeti.LSPath
