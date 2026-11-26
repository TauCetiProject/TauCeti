/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.Localization.Away.Basic
public import TauCeti.RingTheory.AdicCompletion.Regular
public import TauCeti.RingTheory.AdicCompletion.Iterated
public import TauCeti.RingTheory.Regular.Pair
public import TauCeti.RingTheory.Patching.GlueingPair
import TauCeti.RingTheory.Localization.Away.Basic
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
pullback. Its supersingular corner `(R̂_v)^_p` is the `(p, v)`-adic completion of `R`
(`AdicCompletion.iteratedEquivSup`), so the square may be stated with that corner instead. For
`v = v₁` on a chart of the moduli of elliptic curves, its corners are the ordinary coefficients
`(R[1/v₁])^_p`, the supersingular coefficients `R̂_{(p, v₁)}` and their overlap
`(R̂_{v₁}[1/v₁])^_p`.

For a regular element `r`, the pair `(R → R̂, r)` is a glueing pair (Stacks, Remark 15.92.7), so
the square is the exact square `TauCeti.GlueingPair.exactSquare` of that pair, and the results on
the native carriers below are derived from it.

The results use the native `AdicCompletion` and `Localization.Away` carriers. No Noetherian,
separatedness or completeness hypothesis is imposed on `R`. In particular completion need not
be faithfully flat: localization retains the part invisible to completion.

## Main results

* `IsRegular.glueingPair_adicCompletion`: if `f` is a nonzerodivisor, then `R` and its
  `(f)`-adic completion form a glueing pair.
* `AdicCompletion.existsUnique_localization_lift`: the localization–completion square of a
  regular element is cartesian.
* `AdicCompletion.exists_localization_sub_completion`: the difference map onto `R̂[1/r]` is
  surjective.
* `AdicCompletion.isSMulRegular_localization_away`: for a weakly regular pair `(p, v)`, the
  overlap `R̂[1/v]` has no `p`-torsion.
* `AdicCompletion.existsUnique_map_localization_lift`: for a weakly regular pair `(p, v)` with
  `v` regular, the `p`-adic completion of the localization–completion square for `v` is cartesian.
* `AdicCompletion.existsUnique_map_localization_lift_sup`: the same square with the `(p, v)`-adic
  completion of `R` as its supersingular corner.

## References

* Douglas–Francis–Henriques–Hill, *Topological Modular Forms*, Chapter 12, §8, for the
  localization/completion square in the comparison of ordinary and supersingular coefficients.
* The Stacks Project, Section 15.91, formal glueing.
* [The Stacks Project, Remark 15.92.7](https://stacks.math.columbia.edu/tag/0BNS), the completion
  at a nonzerodivisor as a glueing pair.
-/

public section

namespace AdicCompletion

variable {R : Type*} [CommRing R] {r : R}

/-- If `f` is a nonzerodivisor of `R`, then `R` and its `(f)`-adic completion form a glueing pair
(Stacks, Remark 15.92.7). No noetherian hypothesis is needed: the completion has the same
quotients by the powers of `f`, and `f` stays a nonzerodivisor in it, so neither ring has
`f`-power torsion. -/
theorem _root_.IsRegular.glueingPair_adicCompletion {f : R} (hf : IsRegular f) :
    TauCeti.GlueingPair (AdicCompletion (Ideal.span {f}) R) f := by
  refine TauCeti.glueingPair_iff.mpr ⟨fun n ↦ ?_, ?_⟩
  · convert quotientMap_algebraMap_bijective (Submodule.fg_span_singleton f) n <;>
      simp [Ideal.span_singleton_pow, Ideal.map_span]
  · rw [hf.isSMulRegular.torsion'_powers_eq_bot,
      hf.adicCompletion.isSMulRegular.torsion'_powers_eq_bot, Submodule.bot_coe, Submodule.bot_coe]
    exact Set.bijOn_singleton.mpr (_root_.map_zero _)

/-- The localization–completion square of a regular element is cartesian: compatible elements
of `R[1/r]` and the `(r)`-adic completion come from a unique element of `R`. -/
theorem existsUnique_localization_lift (hr : IsRegular r)
    (a : Localization.Away r) (b : AdicCompletion (Ideal.span {r}) R)
    (hab : Localization.awayMap (algebraMap R (AdicCompletion (Ideal.span {r}) R)) r a =
      algebraMap _ (Localization.Away
        (algebraMap R (AdicCompletion (Ideal.span {r}) R) r)) b) :
    ∃! x : R, algebraMap R (Localization.Away r) x = a ∧
      algebraMap R (AdicCompletion (Ideal.span {r}) R) x = b := by
  let := (Localization.awayMap (algebraMap R (AdicCompletion (Ideal.span {r}) R)) r).toAlgebra
  have := Localization.isScalarTower_awayMap (AdicCompletion (Ideal.span {r}) R) r
  have h := hr.glueingPair_adicCompletion.exactSquare (Localization.Away r)
    (Localization.Away (algebraMap R (AdicCompletion (Ideal.span {r}) R) r))
  obtain ⟨x, hx⟩ := (h.exists_algebraMap_eq_iff b a).mpr hab.symm
  exact ⟨x, ⟨hx.2, hx.1⟩, fun y hy ↦ h.injective (Prod.ext (hy.2.trans hx.1.symm)
    (hy.1.trans hx.2.symm))⟩

/-- Every element of the localized completion is a difference of an element from the
localization and an element from the completion. This is the surjectivity at the right end of
the localization–completion short exact sequence, with no regularity hypothesis needed. -/
theorem exists_localization_sub_completion (r : R)
    (z : Localization.Away (algebraMap R (AdicCompletion (Ideal.span {r}) R) r)) :
    ∃ (a : Localization.Away r) (b : AdicCompletion (Ideal.span {r}) R),
      Localization.awayMap (algebraMap R (AdicCompletion (Ideal.span {r}) R)) r a -
        algebraMap _ (Localization.Away
          (algebraMap R (AdicCompletion (Ideal.span {r}) R) r)) b = z := by
  let := (Localization.awayMap (algebraMap R (AdicCompletion (Ideal.span {r}) R)) r).toAlgebra
  have := Localization.isScalarTower_awayMap (AdicCompletion (Ideal.span {r}) R) r
  obtain ⟨⟨b, a⟩, h⟩ := TauCeti.surjective_sub_of_quotient_surjective (R₂ := Localization.Away r)
    (fun n y ↦ by simpa [Ideal.span_singleton_pow, Ideal.map_span] using
      exists_sub_algebraMap_mem_map_pow (Submodule.fg_span_singleton r) n y) (-z)
  exact ⟨a, b, by rw [← neg_sub, ← neg_neg z]; exact congrArg Neg.neg h⟩

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
  -- The uncompleted sequence `0 → R → R[1/v] × R̂ → R̂[1/v] → 0` is the exact square of the
  -- glueing pair `(R → R̂, v)`, with its factors swapped.
  let := (Localization.awayMap (algebraMap R C) v).toAlgebra
  have := Localization.isScalarTower_awayMap C v
  have hsq := hv.glueingPair_adicCompletion.exactSquare L D
  have hg_apply (y : L × C) : g y = -(algebraMap C D y.2 - algebraMap L D y.1) := by
    rw [neg_sub, sub_eq_add_neg]
    rfl
  have hf : Function.Injective f := fun x y hxy ↦
    hsq.injective (Prod.ext congr(($hxy).2) congr(($hxy).1))
  have hfg : Function.Exact f g := fun y ↦ by
    rw [hg_apply, neg_eq_zero]
    refine (hsq.exact (y.2, y.1)).trans ?_
    exact ⟨fun ⟨x, hx⟩ ↦ ⟨x, Prod.ext congr(($hx).2) congr(($hx).1)⟩,
        fun ⟨x, hx⟩ ↦ ⟨x, Prod.ext congr(($hx).2) congr(($hx).1)⟩⟩
  have hg : Function.Surjective g := fun z ↦ by
    obtain ⟨⟨b, a⟩, hab⟩ := hsq.surjective (-z)
    exact ⟨(a, b), (hg_apply _).trans (neg_eq_iff_eq_neg.mpr hab)⟩
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

/-- **The coefficient pullback square with the `(p, v)`-adic completion.** Let `(p, v)` be a
weakly regular pair on `R` with `v` regular. Compatible elements of the `p`-adic completion of
`R[1/v]` and of the `((p) ⊔ (v))`-adic completion of `R` come from a unique element of the
`p`-adic completion of `R`. The `((p) ⊔ (v))`-adic completion is identified with the `p`-adic
completion of the `(v)`-adic completion by `AdicCompletion.iteratedEquivSup`. -/
theorem existsUnique_map_localization_lift_sup (h : IsWeaklyRegular R [p, v]) (hv : IsRegular v)
    (a : AdicCompletion (Ideal.span {p}) (Localization.Away v))
    (b : AdicCompletion (Ideal.span {p} ⊔ Ideal.span {v}) R)
    (hab : map (Ideal.span {p})
        (Localization.awayMapₐ (Algebra.ofId R (AdicCompletion (Ideal.span {v}) R)) v).toLinearMap
          a =
      map (Ideal.span {p}) (IsScalarTower.toAlgHom R (AdicCompletion (Ideal.span {v}) R)
        (Localization.Away (algebraMap R (AdicCompletion (Ideal.span {v}) R) v))).toLinearMap
          ((iteratedEquivSup R h.isSMulRegular_quotient_pow_smul_top).symm b)) :
    ∃! x : AdicCompletion (Ideal.span {p}) R,
      map (Ideal.span {p}) (Algebra.linearMap R (Localization.Away v)) x = a ∧
        iteratedToSup (Ideal.span {p}) (Ideal.span {v}) R
          (map (Ideal.span {p}) (Algebra.linearMap R (AdicCompletion (Ideal.span {v}) R)) x) =
            b := by
  let e := iteratedEquivSup R h.isSMulRegular_quotient_pow_smul_top
  obtain ⟨x, hx, hxu⟩ := existsUnique_map_localization_lift h hv a (e.symm b) hab
  refine ⟨x, ⟨hx.1, ?_⟩, fun y hy ↦ hxu y ⟨hy.1, ?_⟩⟩
  · rw [← iteratedEquivSup_apply h.isSMulRegular_quotient_pow_smul_top, hx.2,
      e.apply_symm_apply]
  · rw [← hy.2, ← iteratedEquivSup_apply h.isSMulRegular_quotient_pow_smul_top,
      e.symm_apply_apply]

end Completion

end AdicCompletion
