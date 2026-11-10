/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.Localization.Away.Basic
public import TauCeti.RingTheory.AdicCompletion.Regular
import Mathlib.Tactic.LinearCombination
import Mathlib.Algebra.Module.LocalizedModule.IsLocalization
import TauCeti.Algebra.Module.LocalizedModule.Regular
import TauCeti.RingTheory.AdicCompletion.Exactness
import TauCeti.RingTheory.AdicCompletion.Pi

/-!
# The principal localization–completion square

For a regular element `r` of a commutative ring `R`, the square with corners
`R`, `R[1/r]`, the `(r)`-adic completion `R̂` of `R`, and `R̂[1/r]` is a pullback.
The difference map `R[1/r] × R̂ → R̂[1/r]` is also surjective. Thus it gives the short exact
sequence used before further completion in a second parameter.

Now let `(p, v)` be a weakly regular pair on `R`, with `v` regular. Then `p` is regular on
`R ⧸ vⁿ R` for every `n`, hence on `R̂` and on `R̂[1/v]`. So the cokernel of the short exact
sequence `0 → R → R[1/v] × R̂ → R̂[1/v] → 0` has no `p`-torsion, and the sequence stays short exact
after `p`-adic completion. In other words, the `p`-adic completion of the square is again a
pullback. For `v = v₁` on a chart of the moduli of elliptic curves, its corners are the ordinary
coefficients `(R[1/v₁])^_p`, the supersingular side `(R̂_{v₁})^_p` and their overlap
`(R̂_{v₁}[1/v₁])^_p`.

The results use the native `AdicCompletion` and `Localization.Away` carriers. No Noetherian,
separatedness or completeness hypothesis is imposed on `R`. In particular completion need not
be faithfully flat: localization retains the part invisible to completion.

## Main results

* `AdicCompletion.existsUnique_localization_lift`: the localization–completion square of a
  regular element is cartesian.
* `AdicCompletion.exists_localization_sub_completion`: the difference map onto `R̂[1/r]` is
  surjective.
* `AdicCompletion.isSMulRegular_localization_away`: for a weakly regular pair `(p, v)`, the
  overlap `R̂[1/v]` has no `p`-torsion.
* `AdicCompletion.existsUnique_map_localization_lift`: for a weakly regular pair `(p, v)` with
  `v` regular, the `p`-adic completion of the localization–completion square for `v` is cartesian.

## References

* Douglas–Francis–Henriques–Hill, *Topological Modular Forms*, Chapter 12, §8, for the
  localization/completion square in the comparison of ordinary and supersingular coefficients.
* The Stacks Project, Section 15.91, formal glueing.
-/

public section

namespace AdicCompletion

variable {R : Type*} [CommRing R] {r : R}

/-- The localization–completion square of a regular element is cartesian: compatible elements
of `R[1/r]` and the `(r)`-adic completion come from a unique element of `R`. -/
theorem existsUnique_localization_lift (hr : IsRegular r)
    (a : Localization.Away r) (b : AdicCompletion (Ideal.span {r}) R)
    (hab : Localization.awayMap (algebraMap R (AdicCompletion (Ideal.span {r}) R)) r a =
      algebraMap _ (Localization.Away
        (algebraMap R (AdicCompletion (Ideal.span {r}) R) r)) b) :
    ∃! x : R, algebraMap R (Localization.Away r) x = a ∧
      algebraMap R (AdicCompletion (Ideal.span {r}) R) x = b := by
  let I : Ideal R := Ideal.span {r}
  let C := AdicCompletion I R
  let D := Localization.Away (algebraMap R C r)
  let f := Localization.awayMap (algebraMap R C) r
  have hrC : IsRegular (algebraMap R C r) := hr.adicCompletion
  have hinjC := IsLocalization.injective D
    (Submonoid.powers_le.mpr (isRegular_iff_mem_nonZeroDivisors.mp hrC))
  have hinjR := IsLocalization.injective (Localization.Away r)
    (Submonoid.powers_le.mpr (isRegular_iff_mem_nonZeroDivisors.mp hr))
  obtain ⟨n, c, hc⟩ := IsLocalization.Away.surj r a
  have hcb : algebraMap R C c = algebraMap R C r ^ n * b := by
    apply hinjC
    have hf (y : R) : f (algebraMap R (Localization.Away r) y) =
        algebraMap C D (algebraMap R C y) :=
      IsLocalization.map_eq (Submonoid.powers r).le_comap_map y
    have h := congrArg f hc
    simp only [map_mul, map_pow, hf] at h
    rw [hab] at h
    rw [map_mul, map_pow]
    exact h.symm.trans (mul_comm _ _)
  -- Divisibility of the completed numerator descends through the residue modulo `r^n`.
  have hcI : algebraMap R C c ∈ (I ^ n).map (algebraMap R C) := by
    simp only [I, Ideal.span_singleton_pow, Ideal.map_span, Set.image_singleton,
      Ideal.mem_span_singleton, map_pow]
    exact ⟨b, hcb⟩
  have hcR : c ∈ Ideal.span {r ^ n} := by
    rw [← Ideal.span_singleton_pow]
    exact (algebraMap_mem_map_pow_iff n).mp hcI
  obtain ⟨x, hx⟩ := Ideal.mem_span_singleton.mp hcR
  have ha : algebraMap R (Localization.Away r) x = a := by
    apply (IsLocalization.Away.algebraMap_pow_isUnit r n).mul_left_injective
    simpa only [hx, map_mul, map_pow, mul_comm] using hc.symm
  have hb : algebraMap R C x = b := by
    apply (hrC.pow n).left
    simpa only [hx, map_mul, map_pow] using hcb
  exact ⟨x, ⟨ha, hb⟩, fun y hy ↦ hinjR (hy.1.trans ha.symm)⟩

/-- Every element of the localized completion is a difference of an element from the
localization and an element from the completion. This is the surjectivity at the right end of
the localization–completion short exact sequence, with no regularity hypothesis needed. -/
theorem exists_localization_sub_completion (r : R)
    (z : Localization.Away (algebraMap R (AdicCompletion (Ideal.span {r}) R) r)) :
    ∃ (a : Localization.Away r) (b : AdicCompletion (Ideal.span {r}) R),
      Localization.awayMap (algebraMap R (AdicCompletion (Ideal.span {r}) R)) r a -
        algebraMap _ (Localization.Away
          (algebraMap R (AdicCompletion (Ideal.span {r}) R) r)) b = z := by
  let I : Ideal R := Ideal.span {r}
  let C := AdicCompletion I R
  let D := Localization.Away (algebraMap R C r)
  let f := Localization.awayMap (algebraMap R C) r
  obtain ⟨n, c, hc⟩ := IsLocalization.Away.surj (algebraMap R C r) z
  obtain ⟨x, hx⟩ := exists_sub_algebraMap_mem_map_pow (Submodule.fg_span_singleton r) n c
  simp only [Ideal.span_singleton_pow, Ideal.map_span, Set.image_singleton,
    Ideal.mem_span_singleton, map_pow] at hx
  obtain ⟨b, hb⟩ := hx
  let a : Localization.Away r := IsLocalization.mk' (Localization.Away r) x
    (⟨r ^ n, n, rfl⟩ : Submonoid.powers r)
  have ha : a * algebraMap R (Localization.Away r) r ^ n =
      algebraMap R (Localization.Away r) x := by
    simpa only [map_pow] using IsLocalization.mk'_spec (Localization.Away r) x
      (⟨r ^ n, n, rfl⟩ : Submonoid.powers r)
  refine ⟨a, -b, ?_⟩
  apply (IsLocalization.Away.algebraMap_pow_isUnit (algebraMap R C r) n).mul_left_injective
  have hf (y : R) : f (algebraMap R (Localization.Away r) y) =
      algebraMap C D (algebraMap R C y) :=
    IsLocalization.map_eq (Submonoid.powers r).le_comap_map y
  have hfa := congrArg f ha
  simp only [map_mul, map_pow, hf] at hfa
  have hbD := congrArg (algebraMap C D) hb
  simp only [map_sub, map_mul, map_pow] at hbD
  simp only [map_neg, sub_neg_eq_add]
  linear_combination hfa - hbD - hc

section Completion

open RingTheory.Sequence

variable {p v : R}

/-- For a weakly regular pair `(p, v)`, the localized `(v)`-adic completion `R̂[1/v]` has no
`p`-torsion. Since `R̂[1/v]` is the cokernel of the localization–completion sequence for `v`, this
is the hypothesis under which that sequence stays exact after `p`-adic completion. -/
theorem isSMulRegular_localization_away (h : IsWeaklyRegular R [p, v]) :
    IsSMulRegular (Localization.Away (algebraMap R (AdicCompletion (Ideal.span {v}) R) v)) p := by
  let C := AdicCompletion (Ideal.span {v}) R
  have hC : IsSMulRegular C (algebraMap R C p) :=
    (isSMulRegular_algebraMap_iff C).2 h.isSMulRegular_adicCompletion
  exact (isSMulRegular_algebraMap_iff C).1 <|
    IsLocalizedModule.isSMulRegular (Submonoid.powers (algebraMap R C v))
      (Algebra.linearMap C (Localization.Away (algebraMap R C v))) hC

/-- **The `p`-adically completed localization–completion square is cartesian.** Let `(p, v)` be a
weakly regular pair on `R` with `v` regular. Compatible elements of the `p`-adic completions of
`R[1/v]` and of the `(v)`-adic completion `R̂` come from a unique element of the `p`-adic completion
of `R`. -/
theorem existsUnique_map_localization_lift (h : IsWeaklyRegular R [p, v]) (hv : IsRegular v)
    (a : AdicCompletion (Ideal.span {p}) (Localization.Away v))
    (b : AdicCompletion (Ideal.span {p}) (AdicCompletion (Ideal.span {v}) R))
    (hab : map (Ideal.span {p})
        (Localization.awayMapₐ (Algebra.ofId R (AdicCompletion (Ideal.span {v}) R)) v).toLinearMap
          a =
      map (Ideal.span {p}) (IsScalarTower.toAlgHom R (AdicCompletion (Ideal.span {v}) R)
        (Localization.Away (algebraMap R (AdicCompletion (Ideal.span {v}) R) v))).toLinearMap b) :
    ∃! x : AdicCompletion (Ideal.span {p}) R,
      map (Ideal.span {p}) (Algebra.linearMap R (Localization.Away v)) x = a ∧
        map (Ideal.span {p}) (Algebra.linearMap R (AdicCompletion (Ideal.span {v}) R)) x = b := by
  let I : Ideal R := Ideal.span {p}
  let L := Localization.Away v
  let C := AdicCompletion (Ideal.span {v}) R
  let D := Localization.Away (algebraMap R C v)
  let φ : L →ₗ[R] D := (Localization.awayMapₐ (Algebra.ofId R C) v).toLinearMap
  let ψ : C →ₗ[R] D := (IsScalarTower.toAlgHom R C D).toLinearMap
  let f : R →ₗ[R] L × C := (Algebra.linearMap R L).prod (Algebra.linearMap R C)
  let g : L × C →ₗ[R] D := φ.coprod (-ψ)
  -- The uncompleted sequence `0 → R → R[1/v] × R̂ → R̂[1/v] → 0` is exact.
  have hcomm (x : R) : Localization.awayMap (algebraMap R C) v (algebraMap R L x) =
      algebraMap C D (algebraMap R C x) :=
    IsLocalization.map_eq (Submonoid.powers v).le_comap_map x
  have hf : Function.Injective f := fun x y hxy ↦
    (existsUnique_localization_lift hv _ _ (hcomm x)).unique ⟨rfl, rfl⟩
      ⟨(congrArg Prod.fst hxy).symm, (congrArg Prod.snd hxy).symm⟩
  have hfg : Function.Exact f g := by
    intro y
    constructor
    · intro hy
      obtain ⟨x, hx, -⟩ := existsUnique_localization_lift hv y.1 y.2 (sub_eq_zero.1 hy)
      exact ⟨x, Prod.ext hx.1 hx.2⟩
    · rintro ⟨x, rfl⟩
      exact sub_eq_zero.2 (hcomm x)
  have hg : Function.Surjective g := fun z ↦ by
    obtain ⟨a, b, hab⟩ := exists_localization_sub_completion v z
    exact ⟨(a, b), hab⟩
  -- Since `p` is regular on `R̂[1/v]`, the sequence stays short exact after `p`-adic completion.
  have hD := isSMulRegular_localization_away h
  have hf' := map_span_singleton_injective_of_isSMulRegular hf hfg hD
  have hfg' := map_span_singleton_exact_of_isSMulRegular hfg hg hD
  let y := map I (LinearMap.inl R L C) a + map I (LinearMap.inr R L C) b
  have hy : map I g y = 0 := by
    rw [map_add, map_comp_apply, map_comp_apply, LinearMap.coprod_inl, LinearMap.coprod_inr,
      map_neg, LinearMap.neg_apply, add_neg_eq_zero]
    exact hab
  have hfst : map I (LinearMap.fst R L C) y = a := by
    simp [y, map_comp_apply, map_id]
  have hsnd : map I (LinearMap.snd R L C) y = b := by
    simp [y, map_comp_apply, map_id]
  obtain ⟨x, hx⟩ := (hfg' y).1 hy
  refine ⟨x, ⟨?_, ?_⟩, fun x' hx' ↦ hf' ?_⟩
  · rw [← hfst, ← hx, map_comp_apply, LinearMap.fst_prod]
  · rw [← hsnd, ← hx, map_comp_apply, LinearMap.snd_prod]
  · -- An element of the completed product is determined by its two components.
    rw [hx, ← map_inl_map_fst_add_map_inr_map_snd I (map I f x'), map_comp_apply (f := f),
      map_comp_apply (f := f), LinearMap.fst_prod, LinearMap.snd_prod, hx'.1, hx'.2]

end Completion

end AdicCompletion
