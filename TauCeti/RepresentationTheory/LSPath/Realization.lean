/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.LSPath.Distinguished
import TauCeti.LinearAlgebra.RootSystem.FundamentalDomain
import TauCeti.LinearAlgebra.RootSystem.Reduced
import TauCeti.LinearAlgebra.RootSystem.Weyl.Orbit.Ray

/-!
# Faithful realization of Lakshmibai–Seshadri encodings

An LS encoding records minimal coset directions and rational breaks. Its timed presentation
recovers both: durations determine the breaks, and velocities determine the minimal coset
representatives for a dominant shape. Consequently an injective realization of the orbit gives
an injective map from encodings to timed presentations.

If distinct realized orbit weights never lie in the same ray, the distinguished-presentation
uniqueness theorem also recovers the timed presentation from the unparametrized path. Whenever
linear forms on the ambient vector space realize the simple coroots, both orbit separation
(`TauCeti.LSPath.injOn_range_smul_of_coroot'`) and ray separation
(`TauCeti.LSPath.pairwise_not_sameRay_range_smul`) hold automatically because the simple
reflections generate the finite Weyl group and each orbit meets the closed dominant chamber in a
single point. Thus `LSPath.toPLPath_injective` and `LSPath.toPLPath_injective_of_coroot'` identify
encodings with their realized paths, even when central weights lie in the kernel of the
realization. Zero and central shapes are included; no regularity of the dominant shape is required.

## References

* P. Littelmann, *Paths and root operators in representation theory*, Ann. of Math. 142 (1995),
  §4.
-/

public section

namespace TauCeti.LSPath

open RootPairing

variable {ι M N : Type*} [AddCommGroup M] [AddCommGroup N]
  {P : RootPairing ι ℤ M N} {b : P.Base} [Finite ι] [P.IsReduced]
  {lam : M} {𝕜 V : Type*} [Field 𝕜] [AddCommGroup V] [Module 𝕜 V] {f : M →+ V}

section Timed

variable [CharZero 𝕜]

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
        have hweight : f ((dir j).1 • lam) = f ((dir' j).1 • lam) := by
          rw [← htime] at hseg
          exact (smul_right_injective _ hd) hseg
        exact Subtype.ext (eq_of_isMinimalCosetRep_of_smul_eq hlam (dir j).2 (dir' j).2
          (hf ⟨_, rfl⟩ ⟨_, rfl⟩ hweight))
      subst dir'
      subst time'
      rfl

/-- Whenever linear forms on `V` agree with the simple coroots on the weight lattice, `f` is
injective on every Weyl orbit `W λ`: the Weyl group acts compatibly on `f '' W λ` through
reflections along those forms, and each orbit meets the closed dominant chamber in a single point,
detected by the simple coroots. -/
theorem injOn_range_smul_of_coroot' {F : b.support → Module.Dual 𝕜 V}
    (hF : ∀ (i : b.support) m, F i (f m) = (P.coroot' i m : 𝕜)) (lam : M) :
    Set.InjOn f (Set.range fun w : P.weylGroup ↦ w • lam) := by
  have := P.flip_isReduced
  have := P.finite_weylGroup_of_base b
  have hsmul : ∀ (w : P.weylGroup) {x y : M}, f x = f y → f (w • x) = f (w • y) := by
    intro w
    obtain ⟨ω, rfl⟩ := (weylCoxeterSystem P b).wordProd_surjective w
    induction ω with
    | nil => simp
    | cons i ω ih =>
      intro x y hxy
      rw [(weylCoxeterSystem P b).wordProd_cons, simple_mul_smul_eq_reflection,
        simple_mul_smul_eq_reflection, P.map_reflection_eq_preReflection _ (hF i),
        P.map_reflection_eq_preReflection _ (hF i), ih hxy]
  rintro _ ⟨w₁, rfl⟩ _ ⟨w₂, rfl⟩ h₁₂
  obtain ⟨w, hw⟩ := exists_mem_dominantChamber_of_finite_weylGroup P b (w₁ • lam)
  have hw' := hsmul w h₁₂
  have hw₂ : w • (w₂ • lam) ∈ dominantChamber P b := by
    rw [mem_dominantChamber] at hw ⊢
    intro i hi
    have hpair : (P.coroot' i (w • (w₁ • lam)) : 𝕜) = (P.coroot' i (w • (w₂ • lam)) : 𝕜) := by
      rw [← hF ⟨i, hi⟩, ← hF ⟨i, hi⟩, hw']
    exact (Int.cast_injective hpair).symm ▸ hw i hi
  have heq : w • (w₁ • lam) = w • (w₂ • lam) :=
    subsingleton_orbit_inter_dominantChamber P b lam
      ⟨⟨w * w₁, mul_smul w w₁ lam⟩, hw⟩ ⟨⟨w * w₂, mul_smul w w₂ lam⟩, hw₂⟩
  simpa using congrArg (w⁻¹ • ·) heq

end Timed

variable [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

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

/-- Whenever linear forms on `V` agree with the simple coroots on the weight lattice, no two
distinct realized orbit weights lie on the same ray: the simple reflections generate the finite
Weyl group and act on `V` by linear reflections along those forms. -/
theorem pairwise_not_sameRay_range_smul {F : b.support → Module.Dual 𝕜 V}
    (hF : ∀ (i : b.support) m, F i (f m) = (P.coroot' i m : 𝕜)) (lam : M) :
    (Set.range fun w : P.weylGroup ↦ f (w • lam)).Pairwise fun u v ↦ ¬ SameRay 𝕜 u v := by
  have := P.finite_weylGroup_of_base b
  have hgen : Subgroup.closure (weylGroup.ofIdx P '' b.support) = ⊤ := by
    convert (weylCoxeterSystem P b).subgroupClosure_range_simple using 2
    ext w
    simp
  have himg : (Set.range fun w : P.weylGroup ↦ f (w • lam)) =
      f '' MulAction.orbit P.weylGroup lam := by
    ext v
    simp [MulAction.mem_orbit_iff]
  rw [himg]
  exact P.pairwise_not_sameRay_image_orbit_weylGroup_of_closure_eq_top hgen hF lam

/-- When linear forms on `V` realize the simple coroots, the unparametrized piecewise-linear path
determines the LS encoding of dominant shape without any separate orbit-injectivity or
ray-separation hypothesis. -/
theorem toPLPath_injective_of_coroot' (hlam : lam ∈ dominantChamber P b)
    {F : b.support → Module.Dual 𝕜 V}
    (hF : ∀ (i : b.support) m, F i (f m) = (P.coroot' i m : 𝕜)) :
    Function.Injective (fun π : LSPath P b lam ↦ π.toPLPath 𝕜 f) :=
  toPLPath_injective hlam (injOn_range_smul_of_coroot' hF lam)
    (pairwise_not_sameRay_range_smul hF lam)

/-- Equality of realized LS paths of dominant shape is equality of encodings whenever linear forms
realize the simple coroots. -/
theorem toPLPath_inj_of_coroot' (hlam : lam ∈ dominantChamber P b)
    {F : b.support → Module.Dual 𝕜 V}
    (hF : ∀ (i : b.support) m, F i (f m) = (P.coroot' i m : 𝕜)) {π π' : LSPath P b lam} :
    π.toPLPath 𝕜 f = π'.toPLPath 𝕜 f ↔ π = π' :=
  (toPLPath_injective_of_coroot' hlam hF).eq_iff

end TauCeti.LSPath
