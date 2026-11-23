/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.JamesReducedProduct.Basic
public import TauCeti.Topology.Constructions.ReducedSuspension
public import TauCeti.Topology.PathSpace.Moore.Comparison.Basic

/-!
# The James map

Let `(X, x₀)` be a pointed space and `ΣX` its reduced suspension
(`TauCeti.ReducedSuspension`). The **James map** `J X → ΩΣX` sends a reduced word `x₁ ⋯ xₙ` of
the James reduced product to the concatenation of the meridians `s ↦ [xᵢ, s]` of its letters.
James proved that it is a weak homotopy equivalence when `X` is a connected CW complex; through it
the word-length filtration of `J X` computes the homology of `ΩΣX`, for instance the Pontryagin
ring of the loop space of a sphere.

On the Moore loop space `Ωᴹ(ΣX)` concatenation is strictly associative and unital, so the James
map can be taken to be a monoid homomorphism on the nose. This needs the letter of the basepoint,
the empty word, to go to the unit, the Moore loop of length zero, while the meridian through `x₀`
is the constant loop of length one. So the meridian through `x` is run in time `u x`, for a
continuous `u : X → ℝ≥0` vanishing exactly at the basepoint
(`TauCeti.ReducedSuspension.mooreMeridian`). The meridians through points near the basepoint stay
near the basepoint, so these Moore loops still depend continuously on `x`, also where their length
tends to zero. Such a function exists when the basepoint is a zero set, for instance
`u x = nndist x x₀` on a metric space, in particular on a sphere. Normalized to the unit interval,
the Moore meridian through `x` is the meridian through `x`, whatever `u`
(`TauCeti.ReducedSuspension.toPath_mooreMeridian`).

The James map (`TauCeti.JamesReducedProduct.jamesMap`) is the continuous monoid homomorphism
`J X → Ωᴹ(ΣX)` extending the Moore meridians, given by the universal property of the James reduced
product among topological monoids. It sends a word to the product of the Moore meridians of its
letters (`TauCeti.JamesReducedProduct.jamesMap_mk`), and the length of the image of a word is the
sum of the values of `u` at its letters (`TauCeti.JamesReducedProduct.length_jamesMap_mk`).

## References

* I. M. James, *Reduced product spaces*, Ann. of Math. (2) 62 (1955), 170–197.
* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Section 4.J.
* G. W. Whitehead, *Elements of Homotopy Theory*, GTM 61, Springer, 1978, Chapter VII.2.
-/

public section

noncomputable section

open scoped unitInterval NNReal

universe u

namespace TauCeti

variable {X : Type u} [TopologicalSpace X] {x₀ : X}

namespace ReducedSuspension

/-- The meridian through `x` as a Moore loop of length `ℓ`; for `ℓ = 0` it is the unit. -/
private def meridianOfLength (x : X) (ℓ : ℝ≥0) :
    MooreLoopSpace (ReducedSuspension X x₀) basepoint :=
  ⟨(meridian x).toMoorePath.rescale ℓ, by simp, by
    rcases eq_or_ne ℓ 0 with h | h
    · rw [h, MoorePath.rescale_zero, MoorePath.target_refl, Path.source_toMoorePath]
    · rw [MoorePath.target_rescale _ h, Path.target_toMoorePath]⟩

private theorem meridianOfLength_zero (x : X) : meridianOfLength (x₀ := x₀) x 0 = 1 :=
  MooreLoopSpace.ext <| by simp [meridianOfLength, MoorePath.rescale_zero]

/-- A family of meridians run in continuously varying times is continuous, also where the time
vanishes, provided the meridians run in time zero are the ones through the basepoint. -/
private theorem continuous_meridianOfLength {Y : Type*} [TopologicalSpace Y] {f : Y → X}
    {ℓ : Y → ℝ≥0} (hf : Continuous f) (hℓ : Continuous ℓ) (h : ∀ y, ℓ y = 0 → f y = x₀) :
    Continuous fun y ↦ meridianOfLength (x₀ := x₀) (f y) (ℓ y) :=
  MooreLoopSpace.isEmbedding_toMoorePath.continuous_iff.2 <|
    Continuous.moorePath_rescale_of_forall_eq_source
      (Path.continuous_toMoorePath.comp (meridian.continuous.comp hf)) hℓ
      fun y hy t ↦ by simp [h y hy, meridian_basepoint]

/-- The **Moore meridian** through `x`, run in time `u x`: the meridian `s ↦ [x, s]` of the
reduced suspension as a Moore loop of length `u x` at the basepoint. For a continuous
`u : X → ℝ≥0` vanishing only at the basepoint, it depends continuously on `x`; if moreover
`u x₀ = 0`, the Moore meridian through the basepoint is the unit
(`TauCeti.ReducedSuspension.mooreMeridian_basepoint`). -/
def mooreMeridian (u : C(X, ℝ≥0)) (hu : ∀ x, u x = 0 → x = x₀) :
    C(X, MooreLoopSpace (ReducedSuspension X x₀) basepoint) where
  toFun x := meridianOfLength x (u x)
  continuous_toFun := continuous_meridianOfLength continuous_id u.continuous hu

private theorem mooreMeridian_eq_meridianOfLength (u : C(X, ℝ≥0)) (hu : ∀ x, u x = 0 → x = x₀)
    (x : X) : mooreMeridian u hu x = meridianOfLength x (u x) :=
  (rfl)

variable (u : C(X, ℝ≥0)) (hu : ∀ x, u x = 0 → x = x₀)

@[simp]
theorem toMoorePath_mooreMeridian (x : X) :
    (mooreMeridian u hu x).toMoorePath = (meridian x).toMoorePath.rescale (u x) :=
  (rfl)

@[simp]
theorem length_mooreMeridian (x : X) : (mooreMeridian u hu x).length = u x := by
  rw [← MooreLoopSpace.length_toMoorePath, toMoorePath_mooreMeridian, MoorePath.length_rescale]

/-- The Moore meridian through `x` at time `t` is the point `[x, t / u x]`, stopped at the
basepoint from time `u x` on (with `t / 0 = 0`). -/
theorem mooreMeridian_apply (x : X) (t : ℝ≥0) :
    (mooreMeridian u hu x).toMoorePath t = mk (x, Set.projIcc 0 1 zero_le_one (t / u x : ℝ≥0)) := by
  rw [toMoorePath_mooreMeridian, MoorePath.rescale_apply, Path.toMoorePath_apply,
    Path.length_toMoorePath, one_mul]
  rcases le_total (t / u x : ℝ≥0) 1 with h | h
  · have hmem : ((t / u x : ℝ≥0) : ℝ) ∈ Set.Icc 0 1 := ⟨(t / u x).property, mod_cast h⟩
    rw [Path.extend_apply _ hmem, Set.projIcc_of_mem _ hmem, meridian_apply]
  · rw [Path.extend_of_one_le _ (mod_cast h), Set.projIcc_of_right_le _ (mod_cast h)]
    exact (mk_one x).symm

/-- The Moore meridian through the basepoint, run in time zero, is the unit of the Moore loop
space. -/
theorem mooreMeridian_basepoint (h₀ : u x₀ = 0) : mooreMeridian u hu x₀ = 1 := by
  rw [mooreMeridian_eq_meridianOfLength, h₀, meridianOfLength_zero]

/-- Normalized to the unit interval, the Moore meridian through `x` is the meridian through `x`,
whatever the length `u x`. -/
@[simp]
theorem toPath_mooreMeridian (x : X) : (mooreMeridian u hu x).toPath = meridian x := by
  rcases eq_or_ne (u x) 0 with h | h
  · obtain rfl := hu x h
    rw [mooreMeridian_basepoint u hu h, MooreLoopSpace.toPath_one, meridian_basepoint]
  · ext s
    simp [MoorePath.rescale_apply, h]

end ReducedSuspension

namespace JamesReducedProduct

open ReducedSuspension

variable (u : C(X, ℝ≥0)) (hu : ∀ x, u x = 0 ↔ x = x₀)

/-- The **James map** `J X → Ωᴹ(ΣX)` from the James reduced product of `(X, x₀)` to the Moore loop
space of its reduced suspension: the continuous monoid homomorphism sending a reduced word
`x₁ ⋯ xₙ` to the concatenation of the Moore meridians through `x₁, …, xₙ`, the meridian through
`x` being run in time `u x`. -/
def jamesMap :
    JamesReducedProduct X x₀ →ₜ* MooreLoopSpace (ReducedSuspension X x₀) basepoint :=
  lift (mooreMeridian u fun x ↦ (hu x).1) (mooreMeridian_basepoint _ _ ((hu x₀).2 rfl))

@[simp]
theorem jamesMap_letter (x : X) :
    jamesMap u hu (letter x : JamesReducedProduct X x₀) = mooreMeridian u (fun x ↦ (hu x).1) x :=
  lift_letter _ _ x

/-- The James map sends a word to the product of the Moore meridians of its letters. -/
@[simp]
theorem jamesMap_mk {n : ℕ} (v : Fin n → X) :
    jamesMap u hu (mk v : JamesReducedProduct X x₀) =
      (List.ofFn fun i ↦ mooreMeridian u (fun x ↦ (hu x).1) (v i)).prod :=
  lift_mk _ _ v

/-- The James map is the only continuous monoid homomorphism extending the Moore meridians. -/
theorem eq_jamesMap {f : JamesReducedProduct X x₀ →ₜ* MooreLoopSpace (ReducedSuspension X x₀)
    basepoint} (hf : ∀ x ≠ x₀, f (letter x) = mooreMeridian u (fun x ↦ (hu x).1) x) :
    f = jamesMap u hu :=
  lift_unique _ _ hf

/-- The image under the James map of a word `x₁ ⋯ xₙ` is a Moore loop of length
`u x₁ + ⋯ + u xₙ`. -/
theorem length_jamesMap_mk {n : ℕ} (v : Fin n → X) :
    (jamesMap u hu (mk v : JamesReducedProduct X x₀)).length = ∑ i, u (v i) := by
  simp [MooreLoopSpace.length_list_prod, List.map_ofFn, Function.comp_def, List.sum_ofFn]

/-- Normalized to the unit interval, the image of a one-letter word under the James map is the
meridian through its letter. -/
theorem toPath_jamesMap_letter (x : X) :
    (jamesMap u hu (letter x : JamesReducedProduct X x₀)).toPath = meridian x := by
  rw [jamesMap_letter, toPath_mooreMeridian]

/-- **The James map does not depend on the choice of times up to homotopy**: for two continuous
functions `u` and `u'` vanishing exactly at the basepoint, the James maps they define are
homotopic. -/
theorem jamesMap_homotopic (u' : C(X, ℝ≥0)) (hu' : ∀ x, u' x = 0 ↔ x = x₀) :
    (jamesMap u hu).toContinuousMap.Homotopic (jamesMap u' hu').toContinuousMap := by
  -- The times of the meridians at the stage `t` of the homotopy.
  let v : X × I → ℝ≥0 := fun p ↦ unitInterval.toNNReal (σ p.2) * u p.1 +
    unitInterval.toNNReal p.2 * u' p.1
  have hv0 : ∀ p, v p = 0 → p.1 = x₀ := fun p hp ↦ by
    obtain ⟨h, h'⟩ := add_eq_zero.1 hp
    rcases mul_eq_zero.1 h with h | h
    · rcases mul_eq_zero.1 h' with h' | h'
      · have h₁ := congrArg NNReal.toReal h
        have h₂ := congrArg NNReal.toReal h'
        simp only [unitInterval.coe_toNNReal, unitInterval.coe_symm_eq, NNReal.coe_zero] at h₁ h₂
        linarith
      · exact (hu' _).1 h'
    · exact (hu _).1 h
  -- The meridians at all stages, as a map into the topological monoid of paths of Moore loops.
  let G : C(X, C(I, MooreLoopSpace (ReducedSuspension X x₀) basepoint)) :=
    ContinuousMap.curry ⟨fun p ↦ meridianOfLength p.1 (v p),
      continuous_meridianOfLength continuous_fst (by fun_prop) hv0⟩
  have hG : G x₀ = 1 := ContinuousMap.ext fun t ↦ by
    simp [G, v, (hu x₀).2 rfl, (hu' x₀).2 rfl, meridianOfLength_zero]
  -- At the stage `t`, the homotopy is the monoid homomorphism extending the meridians at `t`.
  have hH : ∀ (t : I) (f : JamesReducedProduct X x₀ →* MooreLoopSpace (ReducedSuspension X x₀)
      basepoint), (∀ x, f (letter x) = meridianOfLength x (v (x, t))) →
      ∀ w, lift G hG w t = f w := fun t f hf w ↦ by
    have h : ((Pi.evalMonoidHom _ t).comp ContinuousMap.coeFnMonoidHom).comp
        (lift G hG).toMonoidHom = f :=
      monoidHom_ext fun x _ ↦ by simp [G, hf x]
    exact DFunLike.congr_fun h w
  refine ⟨{ toFun := fun p ↦ lift G hG p.2 p.1
            continuous_toFun := ContinuousEval.continuous_eval.comp
              (((lift G hG).continuous.comp continuous_snd).prodMk continuous_fst)
            map_zero_left := fun w ↦ hH 0 (jamesMap u hu).toMonoidHom (fun x ↦ by
              simp [v, mooreMeridian_eq_meridianOfLength]) w
            map_one_left := fun w ↦ hH 1 (jamesMap u' hu').toMonoidHom (fun x ↦ by
              simp [v, mooreMeridian_eq_meridianOfLength]) w }⟩

end JamesReducedProduct

end TauCeti
