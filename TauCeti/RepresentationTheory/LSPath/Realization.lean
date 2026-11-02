/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.LSPath.Distinguished

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

## References

* P. Littelmann, *Paths and root operators in representation theory*, Ann. of Math. 142 (1995),
  §4.
-/

public section

namespace TauCeti.LSPath

open RootPairing

variable {ι M N : Type*} [AddCommGroup M] [AddCommGroup N]
  {P : RootPairing ι ℤ M N} {b : P.Base} [Finite ι] [P.IsReduced] [P.flip.IsReduced]
  {lam : M} {𝕜 V : Type*} [Field 𝕜] [AddCommGroup V] [Module 𝕜 V] {f : M →+ V}

section Timed

variable [CharZero 𝕜]

/-- For a dominant shape, an LS encoding is determined by its timed presentation whenever the
realization separates orbit weights. No ray condition is needed for timed presentations. -/
theorem timed_injective (hlam : lam ∈ dominantChamber P b)
    (hf : Set.InjOn f (Set.range fun w : P.weylGroup ↦ w • lam)) :
    Function.Injective (fun π : LSPath P b lam ↦ π.timed 𝕜 f) := by
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
        have hweight : f ((dir j).1 • lam) = f ((dir' j).1 • lam) := by
          rw [← htime] at hseg
          exact (smul_right_injective _ hd) hseg
        exact Subtype.ext (eq_of_isMinimalCosetRep_of_smul_eq hlam (dir j).2 (dir' j).2
          (hf ⟨_, rfl⟩ ⟨_, rfl⟩ hweight))
      subst dir'
      subst time'
      rfl

end Timed

variable [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

/-- For a dominant shape whose realized orbit has no distinct weights on the same ray, the
unparametrized piecewise-linear path determines the entire LS encoding, including its breaks. -/
theorem toPLPath_injective (hlam : lam ∈ dominantChamber P b)
    (hf : Set.InjOn f (Set.range fun w : P.weylGroup ↦ w • lam))
    (hS : (Set.range fun w : P.weylGroup ↦ f (w • lam)).Pairwise
      fun u v ↦ ¬ SameRay 𝕜 u v) :
    Function.Injective (fun π : LSPath P b lam ↦ π.toPLPath 𝕜 f) := by
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

end TauCeti.LSPath
