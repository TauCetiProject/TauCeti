/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Bilinear
public import Mathlib.RingTheory.AdicCompletion.Completeness
public import Mathlib.RingTheory.AdicCompletion.Functoriality
import TauCeti.RingTheory.AdicCompletion.Exactness

/-!
# Maps that are bijective on adic completions

Let `I` be an ideal of a commutative ring `R`. An `R`-linear map `f : M →ₗ[R] N` induces a
bijection `AdicCompletion.map I f` of `I`-adic completions exactly when it is onto modulo `I` and
`f x ∈ Iⁿ N` forces `x ∈ Iⁿ M` for every `n` (`AdicCompletion.map_bijective_iff`). For `I = (p)`
these are the conditions that `f` be onto modulo `p` and that `pⁿ ∣ f x` imply `pⁿ ∣ x`. Both
conditions are tested on `M` and `N` themselves, without completing.

Maps that are bijective on completions are invisible to complete targets: along such an `f`,
every linear map to an `I`-adically complete module extends uniquely
(`AdicCompletion.bijective_comp_of_map_bijective`), and along such an algebra map, every algebra
map to an `I`-adically complete algebra extends uniquely
(`AdicCompletion.bijective_algHom_comp_of_map_bijective`). The extension of an algebra map is the
extension of its underlying linear map, which is multiplicative by uniqueness of linear extensions,
applied once in each variable. For `I` finitely generated, the canonical map `M → AdicCompletion I
M` is bijective on completions (`AdicCompletion.map_of_bijective`).

This is the form in which `p`-adic completions are compared with each other: a map of
`p`-torsion-free algebras that is an isomorphism modulo `p`, or the inclusion of an algebra into
its completion, does not change the maps into `p`-adically complete algebras.

## Main results

* `AdicCompletion.map_bijective_iff`: `map I f` is bijective if and only if `f` is onto modulo `I`
  and `f⁻¹ (Iⁿ N) ≤ Iⁿ M` for every `n`.
* `AdicCompletion.bijective_comp_of_map_bijective`: if `map I f` is bijective, then
  `g ↦ g ∘ₗ f` is a bijection from linear maps `N →ₗ[R] P` to linear maps `M →ₗ[R] P`, for every
  `I`-adically complete `P`.
* `AdicCompletion.bijective_algHom_comp_of_map_bijective`: the same for algebra maps along an
  algebra map `κ : A →ₐ[R] B`, into an `I`-adically complete `R`-algebra.
* `AdicCompletion.map_of_bijective`: for `I` finitely generated, `M → AdicCompletion I M` induces a
  bijection of completions.

## References

* [Stacks Project, Tag 0317](https://stacks.math.columbia.edu/tag/0317) (the completion of a
  module and its universal property).
-/

public section

namespace AdicCompletion

variable {R : Type*} [CommRing R] {I : Ideal R}
variable {M N P : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [AddCommGroup P] [Module R P] {f : M →ₗ[R] N}

/-- If `map I f` is onto, then every element of `Iⁿ N` is the image under `map I f` of an element
of `Iⁿ` times the completion of `M`, up to the canonical map `N → AdicCompletion I N`. -/
private theorem exists_mem_pow_smul_top_map_eq_of (hf : Function.Surjective (map I f)) {n : ℕ}
    {y : N} (hy : y ∈ (I ^ n • ⊤ : Submodule R N)) :
    ∃ w ∈ (I ^ n • ⊤ : Submodule R (AdicCompletion I M)), map I f w = of I N y := by
  induction hy using Submodule.smul_induction_on' with
  | smul a ha y _ =>
    obtain ⟨z, hz⟩ := hf (of I N y)
    exact ⟨a • z, Submodule.smul_mem_smul ha Submodule.mem_top, by
      rw [LinearMap.map_smul_of_tower, hz, map_smul]⟩
  | add y₁ _ y₂ _ ih₁ ih₂ =>
    obtain ⟨w₁, hw₁, h₁⟩ := ih₁
    obtain ⟨w₂, hw₂, h₂⟩ := ih₂
    exact ⟨w₁ + w₂, add_mem hw₁ hw₂, by rw [map_add, map_add, h₁, h₂]⟩

/-- **Bijectivity on completions, tested before completing.** The map of `I`-adic completions
induced by `f : M →ₗ[R] N` is bijective if and only if `f` is onto modulo `I` and `f x ∈ Iⁿ N`
implies `x ∈ Iⁿ M` for every `n`. For `I = (p)`: `f` is onto modulo `p`, and `pⁿ ∣ f x` implies
`pⁿ ∣ x`. -/
theorem map_bijective_iff :
    Function.Bijective (map I f) ↔ Function.Surjective ((I • ⊤ : Submodule R N).mkQ ∘ₗ f) ∧
      ∀ n, (I ^ n • ⊤ : Submodule R N).comap f ≤ I ^ n • ⊤ := by
  refine ⟨fun hf ↦ ⟨fun y ↦ ?_, fun n x hx ↦ ?_⟩, fun ⟨h₁, h₂⟩ ↦
    ⟨map_injective_of_comap_pow_smul_top_le (k := 0) h₂, map_surjective_of_mkQ_comp_surjective h₁⟩⟩
  · -- Compare the first coordinates of `of y` and of a preimage under `map I f`.
    obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective _ y
    obtain ⟨z, hz⟩ := hf.2 (of I N y)
    obtain ⟨x, hx⟩ := Submodule.Quotient.mk_surjective _ (z.val 1)
    refine ⟨x, ?_⟩
    have h := congrArg (fun w ↦ w.val 1) hz
    simp only [map_val_apply, ← hx, LinearMap.reduceModIdeal_apply, of_apply,
      Submodule.mkQ_apply, Submodule.Quotient.eq, pow_one] at h
    simpa only [LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.Quotient.eq] using h
  · -- `of x` lies in `Iⁿ` times the completion, so its `n`-th coordinate vanishes.
    obtain ⟨w, hw, hwx⟩ := exists_mem_pow_smul_top_map_eq_of hf.2 hx
    rw [← map_of] at hwx
    obtain rfl := hf.1 hwx
    have := pow_smul_top_le_ker_eval I n hw
    rwa [LinearMap.mem_ker, eval_of, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at this

/-- **Linear maps into a complete module extend uniquely along a map bijective on completions.**
If `f : M →ₗ[R] N` induces a bijection of `I`-adic completions and `P` is `I`-adically complete,
then `g ↦ g ∘ₗ f` is a bijection from linear maps `N →ₗ[R] P` to linear maps `M →ₗ[R] P`. -/
theorem bijective_comp_of_map_bijective (hf : Function.Bijective (map I f)) [IsAdicComplete I P] :
    Function.Bijective fun g : N →ₗ[R] P ↦ g ∘ₗ f := by
  refine ⟨fun g g' h ↦ ?_, fun h ↦ ?_⟩
  · -- `map I g` and `map I g'` agree after the surjection `map I f`, and `P` is Hausdorff.
    have hmap : map I g = map I g' := LinearMap.ext fun z ↦ by
      obtain ⟨w, rfl⟩ := hf.2 z
      rw [← LinearMap.comp_apply, map_comp, ← LinearMap.comp_apply (map I g'), map_comp]
      exact congr($(congrArg (map I) h) w)
    exact LinearMap.ext fun y ↦ of_injective I P (by rw [← map_of, hmap, map_of])
  · -- Complete, invert `map I f`, apply `map I h`, and return to `P`.
    let e := (LinearEquiv.ofBijective (map I f) hf).restrictScalars R
    refine ⟨(ofLinearEquiv I P).symm.toLinearMap ∘ₗ (map I h).restrictScalars R ∘ₗ
      e.symm.toLinearMap ∘ₗ of I N, LinearMap.ext fun x ↦ ?_⟩
    have hx : e.symm (of I N (f x)) = of I M x :=
      e.symm_apply_eq.mpr (map_of I f x).symm
    simp [hx, map_of]

/-- **Algebra maps into a complete algebra extend uniquely along a map bijective on
completions.** Let `κ : A →ₐ[R] B` be an algebra map whose underlying linear map induces a
bijection of `I`-adic completions, and let `C` be an `I`-adically complete `R`-algebra. Then
`g ↦ g.comp κ` is a bijection from algebra maps `B →ₐ[R] C` to algebra maps `A →ₐ[R] C`. -/
theorem bijective_algHom_comp_of_map_bijective {A B C : Type*} [Ring A] [Ring B] [Ring C]
    [Algebra R A] [Algebra R B] [Algebra R C] {κ : A →ₐ[R] B}
    (hκ : Function.Bijective (map I κ.toLinearMap)) [IsAdicComplete I C] :
    Function.Bijective fun g : B →ₐ[R] C ↦ g.comp κ := by
  have hlin := bijective_comp_of_map_bijective (P := C) hκ
  refine ⟨fun g g' h ↦ AlgHom.toLinearMap_injective <| hlin.1 ?_, fun h ↦ ?_⟩
  · simpa only [AlgHom.comp_toLinearMap] using congrArg AlgHom.toLinearMap h
  obtain ⟨g, hg⟩ := hlin.2 h.toLinearMap
  have hgκ (a : A) : g (κ a) = h a := congr($hg a)
  -- The linear extension `g` is multiplicative: both sides of `g (x * y) = g x * g y` are linear
  -- in `y`, and agree on the image of `κ`; first for `x` in the image of `κ`, then for all `x`.
  have hmul₁ (a : A) (y : B) : g (y * κ a) = g y * h a := by
    have : g ∘ₗ LinearMap.mulRight R (κ a) = LinearMap.mulRight R (h a) ∘ₗ g :=
      hlin.1 <| LinearMap.ext fun b ↦ by simp [← map_mul, hgκ]
    exact congr($this y)
  have hmul (x y : B) : g (x * y) = g x * g y := by
    have : g ∘ₗ LinearMap.mulLeft R x = LinearMap.mulLeft R (g x) ∘ₗ g :=
      hlin.1 <| LinearMap.ext fun a ↦ by simp [hmul₁, hgκ]
    exact congr($this y)
  exact ⟨AlgHom.ofLinearMap g (by rw [← map_one κ, hgκ, map_one]) hmul,
    AlgHom.ext fun a ↦ hgκ a⟩

/-- **A module and its completion have the same completion.** For a finitely generated ideal `I`,
the canonical map `M → AdicCompletion I M` induces a bijection of `I`-adic completions. Hence, by
`AdicCompletion.bijective_comp_of_map_bijective`, linear maps from `M` to `I`-adically complete
modules extend uniquely to its completion. -/
theorem map_of_bijective (hI : I.FG) : Function.Bijective (map I (of I M)) := by
  refine map_bijective_iff.mpr ⟨fun z ↦ ?_, fun n x hx ↦ ?_⟩
  · obtain ⟨z, rfl⟩ := Submodule.mkQ_surjective _ z
    obtain ⟨x, hx⟩ := Submodule.Quotient.mk_surjective _ (z.val 1)
    refine ⟨x, ?_⟩
    have hmem : of I M x - z ∈ (I ^ 1 • ⊤ : Submodule R (AdicCompletion I M)) := by
      rw [pow_smul_top_eq_ker_eval hI, LinearMap.mem_ker, map_sub, eval_of, eval_apply, ← hx,
        Submodule.mkQ_apply, sub_self]
    rw [pow_one] at hmem
    simpa only [LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.Quotient.eq] using hmem
  · have := pow_smul_top_le_ker_eval I n hx
    rwa [LinearMap.mem_ker, eval_of, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at this

end AdicCompletion
