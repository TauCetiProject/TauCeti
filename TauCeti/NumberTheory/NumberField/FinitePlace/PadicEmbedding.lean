/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
public import Mathlib.NumberTheory.Ostrowski
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import TauCeti.NumberTheory.NumberField.PlacesOver.Relative
public import TauCeti.RingTheory.DedekindDomain.FiniteAdeleRing.Place

import Mathlib.Topology.Algebra.Module.FiniteDimension
import TauCeti.Algebra.Algebra.Subalgebra.Lattice
import TauCeti.NumberTheory.NumberField.Global.Places.Rat
import TauCeti.NumberTheory.NumberField.PlacesOver.FinitePlace
import TauCeti.NumberTheory.Padics.Basic

/-!
# Embeddings of a number field into a `p`-adic normed field

Let `E` be a number field, `p` a prime and `F` a normed field (or normed division ring) which is a
normed algebra over `ℚ_[p]`, not necessarily complete, such as `ℂ_[p]` or an algebraic closure of
`ℚ_[p]`. The norm of `F` is then ultrametric (Mathlib's `IsUltrametricDist.of_normedAlgebra`), and
a ring homomorphism `σ : E →+* F` is read at a finite place of `E`:

* the integers `x` of `E` with `‖σ x‖ < 1` form a height one prime `σ.padicPrime p` of `𝓞 E`,
  which contains `p`;
* the absolute value `x ↦ ‖σ x‖` is the finite place of that prime normalised on `ℚ`: its power
  by the local degree `e f` of the prime over `p` is the finite place;
* `σ` extends to a continuous ring homomorphism `σ.adicCompletionExtension p` from the completion
  `E_v` of `E` at that prime to `F`, with values in the `ℚ_[p]`-subalgebra `ℚ_[p](σ E)` generated
  by the image of `σ`, and it compares norms as the valuation of `E_v` does;
* composed with the projection of the finite adeles onto `E_v`, it gives a continuous ring
  homomorphism `σ.finiteAdeleRingExtension p : 𝔸ᶠ[E] →+* F` extending `σ`, of norm at most `1` on
  the integral finite adeles, under which two finite adeles have images of equal norm exactly when
  their components at the prime have equal valuations.

The last map is how a finite adele, or the value at it of a character of the finite ideles, is
read at a `p`-adic embedding, for instance in the `p`-adic absolute values of the values of
algebraic Hecke characters.

For `F = ℚ_[p]` the prime of `σ` is the kernel of the reduction of `σ` modulo `p`, which
`RingHom.exists_inertiaDeg_eq_one_of_padic` shows to have residue degree one.

The extension to `E_v` exists although `F` need not be complete: `ℚ_[p](σ E)` is finite
dimensional over the complete field `ℚ_[p]`, hence complete, and `σ` is continuous for the
`v`-adic topology because its norm is a power of the `v`-adic absolute value.

## Main definitions

* `RingHom.padicPrime`: the prime of `𝓞 E` induced by `σ`.
* `RingHom.adicCompletionExtension`: the continuous extension `E_v →+* F` of `σ`.
* `RingHom.finiteAdeleRingExtension`: the continuous extension `𝔸ᶠ[E] →+* F` of `σ`.

## Main results

* `RingHom.finiteDimensional_adjoin_range`, `RingHom.completeSpace_adjoin_range`: the image of a
  number field generates a finite dimensional subalgebra over any field, which is complete over a
  complete field.
* `RingHom.place_liesOver_padic`: on `ℚ`, the absolute value `x ↦ ‖σ x‖` is the `p`-adic one.
* `RingHom.mem_padicPrime_iff`, `RingHom.natCast_mem_padicPrime`: the prime of `σ` consists of
  the integers at which `σ` has norm less than `1`, and it contains `p`.
* `RingHom.place_eq_relativeAbsValue_padicPrime`, `RingHom.norm_pow_localDegree`,
  `RingHom.isEquiv_place_padicPrime`: the absolute value `x ↦ ‖σ x‖` is the local-degree root of
  the finite place of the prime of `σ`, in particular equivalent to it.
* `RingHom.norm_apply_le_norm_apply_iff`: `‖σ x‖ ≤ ‖σ y‖` exactly when the valuation of `x` at
  the prime of `σ` is at most that of `y`.
* `RingHom.continuous_adicCompletionExtension`,
  `RingHom.eq_adicCompletionExtension_of_continuous`: the extension to `E_v` is continuous, and it
  is the only continuous ring homomorphism `E_v →+* F` extending `σ`.
* `RingHom.adicCompletionExtension_mem_adjoin`: its values lie in `ℚ_[p](σ E)`.
* `RingHom.norm_adicCompletionExtension_pow_localDegree`,
  `RingHom.norm_adicCompletionExtension_le_iff`: its norm is the local-degree root of the norm of
  `E_v`, so it compares norms as the valuation of `E_v` does.
* `RingHom.continuous_finiteAdeleRingExtension`,
  `RingHom.eq_finiteAdeleRingExtension_of_continuous`: the extension to the finite adeles is
  continuous, and by strong approximation it is the only continuous ring homomorphism extending
  `σ`.
* `RingHom.norm_finiteAdeleRingExtension_le_one`,
  `RingHom.norm_finiteAdeleRingExtension_eq_iff`: its norm is at most `1` on the integral finite
  adeles, and it detects the valuation at the prime of `σ`.

## References

* J. Neukirch, *Algebraic Number Theory*, Springer, 1999, Chapter II.
* J.-P. Serre, *Local Fields*, Springer, 1979, Chapter II.
* `grh-lean`, https://github.com/lsernau/grh-lean, file
  `src/Lib/ClassField/Places/ValuationSubrings.lean` (declarations `New.placeOfEmb`,
  `New.exists_placeOfEmb_extension`, `New.adeleExtension`, `New.norm_adeleExtension_le_one`,
  `New.norm_adeleExtension_eq_iff`); Apache 2.0, Copyright 2026 Anthropic, PBC. The construction
  follows the method of that formalization: the embedding is uniformly continuous for the prime it
  induces and extends to the completion, with values in a field finite over `ℚ_[p]`.
-/

public section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField

namespace RingHom

variable {E : Type*} [Field E] [NumberField E]

/-! ### The subalgebra generated by the image of a number field -/

/-- The image of a number field `E` in a `K`-algebra `A` generates a finite dimensional
`K`-subalgebra: it is spanned by the images of a `ℚ`-basis of `E`. -/
theorem finiteDimensional_adjoin_range {K A : Type*} [Field K] [Ring A] [Algebra K A]
    (σ : E →+* A) : FiniteDimensional K (Algebra.adjoin K (Set.range σ)) := by
  rcases subsingleton_or_nontrivial A with hA | hA
  · infer_instance
  have : CharZero A := (RingHom.charZero_iff σ.injective).mp inferInstance
  have : CharZero K := (algebraMap K A).charZero
  -- the two maps `ℚ → A`, through `E` and through `K`, agree
  have hq (q : ℚ) : σ q = algebraMap K A q := by
    simpa using DFunLike.congr_fun
      (RingHom.ext_rat (σ.comp (Rat.castHom E)) ((algebraMap K A).comp (Rat.castHom K))) q
  let b := Module.finBasis ℚ E
  have := FiniteDimensional.span_of_finite K (Set.finite_range (σ ∘ b))
  rw [← Subalgebra.finiteDimensional_toSubmodule, ← σ.coe_range, Algebra.adjoin_coe_eq_span]
  refine Submodule.finiteDimensional_of_le (S₂ := Submodule.span K (Set.range (σ ∘ b)))
    (Submodule.span_le.mpr ?_)
  rintro _ ⟨x, rfl⟩
  rw [← b.sum_repr x, map_sum]
  refine Submodule.sum_mem _ fun i _ ↦ ?_
  rw [Rat.smul_def, map_mul, hq, ← Algebra.smul_def]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

/-- The image of a number field `E` in a normed algebra `A` over a complete nontrivially normed
field `𝕜` generates a complete `𝕜`-subalgebra, being finite dimensional. -/
theorem completeSpace_adjoin_range {𝕜 A : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
    [NormedRing A] [NormedAlgebra 𝕜 A] (σ : E →+* A) :
    CompleteSpace (Algebra.adjoin 𝕜 (Set.range σ)) := by
  have := Subalgebra.finiteDimensional_toSubmodule.mpr (σ.finiteDimensional_adjoin_range (K := 𝕜))
  have h := Submodule.isComplete_of_finiteDimensional
    (Subalgebra.toSubmodule (Algebra.adjoin 𝕜 (Set.range σ)))
  rw [Subalgebra.coe_toSubmodule] at h
  exact h.completeSpace_coe

variable {F : Type*} [NormedDivisionRing F] (σ : E →+* F) (p : ℕ) [Fact p.Prime]
  [NormedAlgebra ℚ_[p] F]

/-! ### The prime of an embedding -/

/-- On `ℚ`, the absolute value `x ↦ ‖σ x‖` is the `p`-adic absolute value. -/
instance place_liesOver_padic : (place σ).LiesOver (Rat.AbsoluteValue.padic p) :=
  ⟨AbsoluteValue.ext fun q ↦ by
    rw [AbsoluteValue.under_apply, place_apply, Rat.AbsoluteValue.padic_eq_padicNorm,
      ← Padic.eq_padicNorm, eq_ratCast, map_ratCast, ← map_ratCast (algebraMap ℚ_[p] F),
      norm_algebraMap']⟩

/-- The prime of `ℤ` below `p`, read in `𝓞 ℚ`. -/
private noncomputable abbrev ratPrime : HeightOneSpectrum (𝓞 ℚ) :=
  (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm ⟨p, Fact.out⟩

private theorem place_liesOver_ratPrime : (place σ).LiesOver (FinitePlace.mk (ratPrime p)).val :=
  ⟨(AbsoluteValue.LiesOver.under_eq (place σ) (Rat.AbsoluteValue.padic p)).trans
    (Nat.Primes.finitePlace_mk_val_eq_padic ⟨p, Fact.out⟩).symm⟩

private theorem existsUnique_padicPrime :
    ∃! 𝔓 : HeightOneSpectrum (𝓞 E), 𝔓.asIdeal.LiesOver (ratPrime p).asIdeal ∧ ∀ y, place σ y =
      FinitePlace.mk 𝔓 y ^
        ((𝔓.asIdeal.ramificationIdx (𝓞 ℚ) : ℝ) * 𝔓.asIdeal.inertiaDeg (𝓞 ℚ))⁻¹ :=
  have := place_liesOver_ratPrime σ p
  existsUnique_finitePlace_rpow_inv_eq_of_liesOver

/-- The prime of `𝓞 E` induced by an embedding `σ` of `E` into a normed division ring (such as a
normed field) over `ℚ_[p]`: the integers `x` with `‖σ x‖ < 1` (`RingHom.mem_padicPrime_iff`). It
contains `p`, and `x ↦ ‖σ x‖` is a root of its finite place
(`RingHom.place_eq_relativeAbsValue_padicPrime`). -/
noncomputable def padicPrime : HeightOneSpectrum (𝓞 E) :=
  (existsUnique_padicPrime σ p).exists.choose

private theorem padicPrime_spec : ∀ y, place σ y = FinitePlace.mk (σ.padicPrime p) y ^
    (((σ.padicPrime p).asIdeal.ramificationIdx (𝓞 ℚ) : ℝ) *
      (σ.padicPrime p).asIdeal.inertiaDeg (𝓞 ℚ))⁻¹ :=
  (existsUnique_padicPrime σ p).exists.choose_spec.2

/-- **The absolute value of a `p`-adic embedding.** The absolute value `x ↦ ‖σ x‖` is the finite
place of the prime of `σ`, normalised on `ℚ`: its local-degree root over `ℚ`. -/
theorem place_eq_relativeAbsValue_padicPrime :
    place σ = (FinitePlace.mk (σ.padicPrime p)).relativeAbsValue ℚ := by
  ext y
  simpa only [FinitePlace.relativeAbsValue_apply, FinitePlace.localDegree_def,
    FinitePlace.maximalIdeal_mk, Nat.cast_mul] using padicPrime_spec σ p y

/-- The local-degree power of `‖σ x‖` is the value at `x` of the finite place of the prime of
`σ`. -/
theorem norm_pow_localDegree (x : E) :
    ‖σ x‖ ^ (FinitePlace.mk (σ.padicPrime p)).localDegree ℚ =
      FinitePlace.mk (σ.padicPrime p) x := by
  rw [← place_apply, σ.place_eq_relativeAbsValue_padicPrime p,
    FinitePlace.relativeAbsValue_pow_localDegree]

/-- The absolute value `x ↦ ‖σ x‖` is equivalent to the finite place of the prime of `σ`. -/
theorem isEquiv_place_padicPrime : (place σ).IsEquiv (FinitePlace.mk (σ.padicPrime p)).val := by
  rw [σ.place_eq_relativeAbsValue_padicPrime p]
  exact (FinitePlace.isEquiv_relativeAbsValue _).symm

/-- **The prime of a `p`-adic embedding.** An integer `x` of `E` lies in the prime of `σ` exactly
when `‖σ x‖ < 1`. -/
@[simp]
theorem mem_padicPrime_iff {x : 𝓞 E} : x ∈ (σ.padicPrime p).asIdeal ↔ ‖σ x‖ < 1 := by
  rw [← FinitePlace.norm_lt_one_iff_mem E, ← FinitePlace.mk_apply,
    ← RingOfIntegers.coe_eq_algebraMap, ← σ.norm_pow_localDegree p,
    pow_lt_one_iff_of_nonneg (norm_nonneg _) (FinitePlace.localDegree_pos _).ne']

/-- The prime of `σ` contains `p`. -/
theorem natCast_mem_padicPrime : (p : 𝓞 E) ∈ (σ.padicPrime p).asIdeal := by
  rw [mem_padicPrime_iff, RingOfIntegers.coe_eq_algebraMap, map_natCast, map_natCast,
    TauCeti.norm_natCast_p]
  exact inv_lt_one_of_one_lt₀ (mod_cast (Fact.out : p.Prime).one_lt)

/-! ### The extension to the completion -/

/-- `σ`, read on `E` with the `v`-adic uniform structure of its prime and with values in
`ℚ_[p](σ E)`. -/
private noncomputable def withValAdjoin :
    WithVal ((σ.padicPrime p).valuation E) →+* Algebra.adjoin ℚ_[p] (Set.range σ) :=
  (σ.codRestrict (Algebra.adjoin ℚ_[p] (Set.range σ)) fun x ↦
    Algebra.subset_adjoin (Set.mem_range_self x)).comp (WithVal.equiv _).toRingHom

private theorem continuous_withValAdjoin : Continuous (withValAdjoin σ p) := by
  set v := σ.padicPrime p
  set n := (FinitePlace.mk v).localDegree ℚ
  have hn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (FinitePlace.localDegree_pos _).ne'
  -- the image of `x` in the completion, whose norm is the finite place of `v` at `x`
  let ι : WithVal (v.valuation E) → v.adicCompletion E := fun x ↦ (x.ofVal : v.adicCompletion E)
  -- `ι` is the coercion of `WithVal` into its completion, read in `E_v`
  have hι : Continuous ι :=
    (adicCompletion.continuous_ofCompletion E v).comp (UniformSpace.Completion.continuous_coe _)
  have hnorm (x : WithVal (v.valuation E)) : ‖σ x.ofVal‖ = ‖ι x‖ ^ (n : ℝ)⁻¹ := by
    rw [← Real.pow_rpow_inv_natCast (norm_nonneg (σ x.ofVal)) (Nat.cast_ne_zero.mp hn),
      σ.norm_pow_localDegree p, FinitePlace.mk_apply, FinitePlace.embedding_apply]
  refine continuous_induced_rng.mpr ?_
  let g : WithVal (v.valuation E) →+ F :=
    σ.toAddMonoidHom.comp (WithVal.equiv (v.valuation E)).toAddMonoidHom
  refine continuous_of_continuousAt_zero g ?_
  rw [ContinuousAt, map_zero, tendsto_zero_iff_norm_tendsto_zero]
  have hι0 : ι 0 = 0 := adicCompletion.ext E v (by simp [ι])
  have h := ((continuous_norm.comp hι).rpow_const (p := (n : ℝ)⁻¹)
    fun _ ↦ Or.inr (by positivity)).tendsto 0
  rw [Function.comp_apply, hι0, norm_zero, Real.zero_rpow (inv_ne_zero hn)] at h
  simpa [g, hnorm] using h

/-- **The extension of a `p`-adic embedding to the completion.** The continuous ring homomorphism
`E_v →+* F` extending `σ`, where `E_v` is the completion of `E` at the prime of `σ`
(`RingHom.adicCompletionExtension_coe`, `RingHom.continuous_adicCompletionExtension`). Its
values lie in the subalgebra `ℚ_[p](σ E)` generated by the image of `σ`, which is complete even
when `F` is not. -/
noncomputable def adicCompletionExtension : (σ.padicPrime p).adicCompletion E →+* F :=
  have := σ.completeSpace_adjoin_range (𝕜 := ℚ_[p])
  (Algebra.adjoin ℚ_[p] (Set.range σ)).val.toRingHom.comp <|
    (UniformSpace.Completion.extensionHom _ (continuous_withValAdjoin σ p)).comp
      (adicCompletion.equiv E (σ.padicPrime p)).toRingHom

/-- The values of the extension of `σ` to the completion lie in the subalgebra `ℚ_[p](σ E)`
generated by the image of `σ`. -/
theorem adicCompletionExtension_mem_adjoin (x : (σ.padicPrime p).adicCompletion E) :
    σ.adicCompletionExtension p x ∈ Algebra.adjoin ℚ_[p] (Set.range σ) :=
  -- by definition, the value is the inclusion of an element of `ℚ_[p](σ E)`
  Subtype.property _

/-- The extension of `σ` to the completion extends `σ`. -/
@[simp]
theorem adicCompletionExtension_coe (x : E) :
    σ.adicCompletionExtension p (x : (σ.padicPrime p).adicCompletion E) = σ x := by
  have := σ.completeSpace_adjoin_range (𝕜 := ℚ_[p])
  simp [adicCompletionExtension, UniformSpace.Completion.extensionHom_coe, withValAdjoin]

/-- The extension of `σ` to the completion is continuous. -/
theorem continuous_adicCompletionExtension : Continuous (σ.adicCompletionExtension p) := by
  have := σ.completeSpace_adjoin_range (𝕜 := ℚ_[p])
  -- the definition is the inclusion of `ℚ_[p](σ E)` after the extension to the completion
  exact continuous_subtypeVal.comp <| UniformSpace.Completion.continuous_extension.comp <|
    adicCompletion.continuous_toCompletion E _

/-- The extension of `σ` to the completion is the only continuous ring homomorphism `E_v →+* F`
extending `σ`. -/
theorem eq_adicCompletionExtension_of_continuous {f : (σ.padicPrime p).adicCompletion E →+* F}
    (hf : Continuous f)
    (hσ : ∀ x : E, f (x : (σ.padicPrime p).adicCompletion E) = σ x) :
    f = σ.adicCompletionExtension p :=
  DFunLike.coe_injective <|
    (HeightOneSpectrum.denseRange_algebraMap (R := 𝓞 E) E (σ.padicPrime p)).equalizer hf
      (σ.continuous_adicCompletionExtension p)
      (funext fun x ↦ by simp [algebraMap_adicCompletion, hσ])

/-- The local-degree power of the norm of the extension of `σ` to the completion `E_v` is the norm
of `E_v`. -/
theorem norm_adicCompletionExtension_pow_localDegree (x : (σ.padicPrime p).adicCompletion E) :
    ‖σ.adicCompletionExtension p x‖ ^ (FinitePlace.mk (σ.padicPrime p)).localDegree ℚ = ‖x‖ := by
  induction x using
    (HeightOneSpectrum.denseRange_algebraMap (R := 𝓞 E) E (σ.padicPrime p)).induction_on with
  | hp =>
    exact isClosed_eq
      ((continuous_norm.comp (σ.continuous_adicCompletionExtension p)).pow _) continuous_norm
  | ih x =>
    rw [algebraMap_adicCompletion, Function.comp_apply, Algebra.algebraMap_self_apply,
      adicCompletionExtension_coe, norm_pow_localDegree, FinitePlace.mk_apply,
      FinitePlace.embedding_apply]

/-- **The extension to the completion compares norms as the valuation does.** -/
@[simp]
theorem norm_adicCompletionExtension_le_iff (x y : (σ.padicPrime p).adicCompletion E) :
    ‖σ.adicCompletionExtension p x‖ ≤ ‖σ.adicCompletionExtension p y‖ ↔
      Valued.v x ≤ Valued.v y := by
  rw [← pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _)
      (FinitePlace.localDegree_pos (K := ℚ) (FinitePlace.mk (σ.padicPrime p))).ne',
    norm_adicCompletionExtension_pow_localDegree, norm_adicCompletionExtension_pow_localDegree]
  exact Valued.toNormedField.norm_le_iff

/-- **The valuation of `σ` is that of its prime.** `‖σ x‖ ≤ ‖σ y‖` exactly when the valuation of
`x` at the prime of `σ` is at most that of `y`. -/
theorem norm_apply_le_norm_apply_iff (x y : E) :
    ‖σ x‖ ≤ ‖σ y‖ ↔ (σ.padicPrime p).valuation E x ≤ (σ.padicPrime p).valuation E y := by
  simpa [valuedAdicCompletion_eq_valuation'] using
    σ.norm_adicCompletionExtension_le_iff p (x : (σ.padicPrime p).adicCompletion E) y

/-! ### The extension to the finite adeles -/

/-- **The extension of a `p`-adic embedding to the finite adeles.** The continuous ring
homomorphism `𝔸ᶠ[E] →+* F` extending `σ`: the extension of `σ` to the completion at the prime of
`σ`, applied to the component of a finite adele at that prime. -/
noncomputable def finiteAdeleRingExtension : FiniteAdeleRing (𝓞 E) E →+* F :=
  (σ.adicCompletionExtension p).comp
    (FiniteAdeleRing.proj E (σ.padicPrime p) : FiniteAdeleRing (𝓞 E) E →+* _)

/-- The extension of `σ` to the finite adeles is the extension to the completion, applied to the
component at the prime of `σ`. -/
@[simp]
theorem finiteAdeleRingExtension_apply (x : FiniteAdeleRing (𝓞 E) E) :
    σ.finiteAdeleRingExtension p x = σ.adicCompletionExtension p (x (σ.padicPrime p)) := by
  simp [finiteAdeleRingExtension]

/-- The extension of `σ` to the finite adeles extends `σ`. -/
-- Not `@[simp]`: `simp` proves it from `finiteAdeleRingExtension_apply`.
theorem finiteAdeleRingExtension_algebraMap (x : E) :
    σ.finiteAdeleRingExtension p (algebraMap E (FiniteAdeleRing (𝓞 E) E) x) = σ x := by
  rw [finiteAdeleRingExtension_apply, FiniteAdeleRing.algebraMap_apply, adicCompletionExtension_coe]

/-- The extension of `σ` to the finite adeles is continuous. -/
theorem continuous_finiteAdeleRingExtension : Continuous (σ.finiteAdeleRingExtension p) :=
  (σ.continuous_adicCompletionExtension p).comp (FiniteAdeleRing.proj E _).continuous

/-- By strong approximation, the extension of `σ` to the finite adeles is the only continuous ring
homomorphism `𝔸ᶠ[E] →+* F` extending `σ`. -/
theorem eq_finiteAdeleRingExtension_of_continuous {f : FiniteAdeleRing (𝓞 E) E →+* F}
    (hf : Continuous f) (hσ : ∀ x : E, f (algebraMap E (FiniteAdeleRing (𝓞 E) E) x) = σ x) :
    f = σ.finiteAdeleRingExtension p :=
  DFunLike.coe_injective <| (FiniteAdeleRing.denseRange_algebraMap (𝓞 E) E).equalizer hf
    (σ.continuous_finiteAdeleRingExtension p) (funext fun x ↦ by simp [hσ])

/-- A finite adele has image of norm at most `1` under the extension of `σ` exactly when its
component at the prime of `σ` is integral. -/
theorem norm_finiteAdeleRingExtension_le_one_iff (x : FiniteAdeleRing (𝓞 E) E) :
    ‖σ.finiteAdeleRingExtension p x‖ ≤ 1 ↔
      x (σ.padicPrime p) ∈ (σ.padicPrime p).adicCompletionIntegers E := by
  have h := σ.norm_adicCompletionExtension_le_iff p (x (σ.padicPrime p)) 1
  rwa [map_one, norm_one, map_one, ← mem_adicCompletionIntegers, ← finiteAdeleRingExtension_apply]
    at h

/-- The extension of `σ` has norm at most `1` on the integral finite adeles. -/
theorem norm_finiteAdeleRingExtension_le_one {x : FiniteAdeleRing (𝓞 E) E}
    (hx : x ∈ FiniteAdeleRing.integralAdeles (𝓞 E) E) : ‖σ.finiteAdeleRingExtension p x‖ ≤ 1 :=
  (σ.norm_finiteAdeleRingExtension_le_one_iff p x).mpr (FiniteAdeleRing.mem_integralAdeles.mp hx _)

/-- Two finite adeles have images of equal norm under the extension of `σ` exactly when their
components at the prime of `σ` have equal valuations. -/
theorem norm_finiteAdeleRingExtension_eq_iff (x y : FiniteAdeleRing (𝓞 E) E) :
    ‖σ.finiteAdeleRingExtension p x‖ = ‖σ.finiteAdeleRingExtension p y‖ ↔
      Valued.v (x (σ.padicPrime p)) = Valued.v (y (σ.padicPrime p)) := by
  simp only [le_antisymm_iff, finiteAdeleRingExtension_apply, norm_adicCompletionExtension_le_iff]

end RingHom
