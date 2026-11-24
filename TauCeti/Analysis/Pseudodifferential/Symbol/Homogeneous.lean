/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.HomogeneousSymbol
public import TauCeti.Analysis.Pseudodifferential.Symbol.Basic
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import TauCeti.Analysis.SpecialFunctions.Pow.Bounds

/-!
# The symbol of a cut-off homogeneous term

The terms `a_{m-j}` of a classical symbol `a ∼ ∑ⱼ χ(ξ) a_{m-j}(x, ξ)` are homogeneous symbols,
singular at `ξ = 0`; multiplying by a frequency cutoff `χ` turns each of them into a symbol of
its degree. For a homogeneous symbol `a` of degree `m` on `ℝⁿ`,
`TauCeti.HomogeneousSymbol.cutoffSymbol χ a` is the symbol `χ(ξ) a(x, ξ)` of order `m`, linear
in `a`. Its symbol estimates are those of the cut-off term
(`TauCeti.HomogeneousSymbol.exists_norm_iteratedFDeriv_smul_coefficient_le`), read on the
coordinate directions through `TauCeti.mixedDeriv_eq_iteratedFDeriv_append`.

The main results are:

* `TauCeti.HomogeneousSymbol.isSmoothing_cutoffSymbol_sub_cutoffSymbol`: changing the cutoff
  changes the cut-off term by a smoothing symbol;
* `TauCeti.HomogeneousSymbol.spatialDeriv_cutoffSymbol` and
  `HomogeneousSymbol.isSmoothing_frequencyDeriv_cutoffSymbol_sub_cutoffSymbol_frequencyDeriv`:
  differentiating the cut-off term differentiates the homogeneous symbol, exactly in the position
  and up to a smoothing symbol in the frequency;
* `TauCeti.HomogeneousSymbol.eq_zero_of_coefficient_eq_cutoffSymbol`: the cut-off term has no
  order below `m` unless `a = 0`, since homogeneity transports any extra decay at large
  frequencies to every frequency;
* `TauCeti.Symbol.ofContDiffHomogeneous`: a coefficient that is smooth on all of `ℝⁿ × ℝⁿ` and
  homogeneous of degree `m` away from `ξ = 0` is a symbol of order `m`, since it agrees with its
  cut-off term at large frequencies.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, Section 18.1.
* M. E. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI*, September 2008,
  Lecture I, (1.17).
-/

public section

noncomputable section

open Filter Topology

namespace TauCeti

variable {n : ℕ} {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W]
  [NormedSpace ℂ W] {m : ℝ}

namespace HomogeneousSymbol

/-- The cut-off term `χ(ξ) a(x, ξ)` of a homogeneous symbol of degree `m` satisfies the symbol
estimates of order `m`. -/
private theorem exists_bound_mixedDeriv_smul_coefficient
    (a : HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W m)
    (χ : FrequencyCutoff (CoordinateSpace n)) {K : Set (CoordinateSpace n)} (hK : IsCompact K)
    (α β : List (Fin n)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ K, ∀ ξ,
      ‖mixedDeriv α β (fun p => χ p.2 • a.coefficient p) x ξ‖ ≤
        C * (1 + ‖ξ‖ ^ 2) ^ ((m - β.length) / 2) := by
  obtain ⟨C, hC, h⟩ := a.exists_norm_iteratedFDeriv_smul_coefficient_le χ hK α.length β.length
  refine ⟨C, hC, fun x hx ξ => ?_⟩
  rw [mixedDeriv_eq_iteratedFDeriv_append α β
    ((a.contDiff_smul_coefficient χ).of_le (mod_cast le_top))]
  simpa [PiLp.norm_single] using
    h x hx ξ (fun i => EuclideanSpace.single (α.get i) 1) fun i => EuclideanSpace.single (β.get i) 1

variable (χ χ' : FrequencyCutoff (CoordinateSpace n))

/-- The cut-off term `χ(ξ) a(x, ξ)` of a homogeneous symbol `a` of degree `m`, as a symbol of order
`m`. The cutoff removes the singularity of `a` at `ξ = 0` and leaves `a` unchanged at frequencies
of norm at least `2`. -/
def cutoffSymbol :
    HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W m →ₗ[ℂ] Symbol n V W m where
  toFun a :=
    { coefficient p := χ p.2 • a.coefficient p
      contDiff_coefficient := a.contDiff_smul_coefficient χ
      exists_bound _ hK α β := exists_bound_mixedDeriv_smul_coefficient a χ hK α β }
  map_add' a b := Symbol.ext <| funext fun p => by simp [smul_add]
  map_smul' c a := Symbol.ext <| funext fun p => by simp [smul_comm (χ p.2) c]

@[simp]
theorem coefficient_cutoffSymbol
    (a : HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W m)
    (p : CoordinateSpace n × CoordinateSpace n) :
    (cutoffSymbol χ a).coefficient p = χ p.2 • a.coefficient p :=
  (rfl)

/-- At frequencies of norm at least `2` the cut-off term is the homogeneous symbol itself. -/
theorem coefficient_cutoffSymbol_of_two_le_norm
    (a : HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W m) {x ξ : CoordinateSpace n}
    (hξ : 2 ≤ ‖ξ‖) : (cutoffSymbol χ a).coefficient (x, ξ) = a.coefficient (x, ξ) := by
  simp [χ.apply_eq_one_of_two_le_norm hξ]

/-- **Independence of the cutoff.** Changing the frequency cutoff changes the cut-off term by a
smoothing symbol: the two cut-off terms agree at all frequencies of norm at least `2`. -/
theorem isSmoothing_cutoffSymbol_sub_cutoffSymbol
    (a : HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W m) :
    (cutoffSymbol χ a - cutoffSymbol χ' a).IsSmoothing :=
  Symbol.isSmoothing_of_coefficient_eq_zero 2 fun x ξ hξ => by
    simp [χ.apply_eq_one_of_two_le_norm hξ, χ'.apply_eq_one_of_two_le_norm hξ]

/-- A spatial derivative of the cut-off term is the cut-off term of the spatial derivative: the
cutoff does not depend on the position. -/
@[simp]
theorem spatialDeriv_cutoffSymbol (j : Fin n)
    (a : HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W m) :
    Symbol.spatialDeriv j (cutoffSymbol χ a) =
      cutoffSymbol χ (a.spatialDeriv (EuclideanSpace.single j 1)) := by
  ext1
  funext ⟨x, ξ⟩
  simp only [Symbol.coefficient_spatialDeriv, coefficient_cutoffSymbol, coordinateDeriv_cons,
    coordinateDeriv_nil]
  rcases eq_or_ne ξ 0 with rfl | hξ
  · simp [χ.apply_zero]
  · have hd : DifferentiableAt ℝ (fun y => a.coefficient (y, ξ)) x :=
      (a.differentiableAt_coefficient (p := (x, ξ)) hξ).comp x (by fun_prop)
    rw [fderiv_fun_const_smul hd, smul_apply, coefficient_spatialDeriv _ _]

/-- A frequency derivative of the cut-off term is the cut-off term of the frequency derivative, up
to a smoothing symbol: the two agree at all frequencies of norm greater than `2`, where the cutoff
is identically `1`. -/
theorem isSmoothing_frequencyDeriv_cutoffSymbol_sub_cutoffSymbol_frequencyDeriv (j : Fin n)
    (a : HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W m) :
    (Symbol.frequencyDeriv j (cutoffSymbol χ a) -
      cutoffSymbol χ (a.frequencyDeriv (EuclideanSpace.single j 1))).IsSmoothing := by
  set d := Symbol.frequencyDeriv j (cutoffSymbol χ a) -
    cutoffSymbol χ (a.frequencyDeriv (EuclideanSpace.single j 1))
  have hR : ∀ x ξ, 3 ≤ ‖ξ‖ → d.coefficient (x, ξ) = 0 := fun x ξ hξ => by
    have hξ2 : 2 < ‖ξ‖ := by linarith
    have hξ0 : ξ ≠ 0 := norm_pos_iff.1 (by linarith)
    have hev : (fun η => χ η • a.coefficient (x, η)) =ᶠ[𝓝 ξ] fun η => a.coefficient (x, η) := by
      filter_upwards [χ.eventuallyEq_one_of_two_lt_norm hξ2] with η hη
      rw [hη, Pi.one_apply, one_smul]
    simp only [d, Symbol.coefficient_sub, Pi.sub_apply, Symbol.coefficient_frequencyDeriv,
      coefficient_cutoffSymbol, coordinateDeriv_cons, coordinateDeriv_nil]
    rw [hev.fderiv_eq, χ.apply_eq_one_of_two_le_norm hξ2.le, one_smul,
      coefficient_frequencyDeriv _ _ hξ0, sub_self]
  rw [← Symbol.ext (Symbol.coefficient_ofBoundedFrequencySupport (m := m - 1) _
    d.contDiff_coefficient 3 hR)]
  exact Symbol.isSmoothing_ofBoundedFrequencySupport _ _ 3 hR

/-- A homogeneous symbol of degree `m` whose cut-off term is a symbol of some order `m' < m`
vanishes. -/
theorem eq_zero_of_coefficient_eq_cutoffSymbol {m' : ℝ} (hm : m' < m)
    {a : HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W m} (b : Symbol n V W m')
    (hb : b.coefficient = (cutoffSymbol χ a).coefficient) : a = 0 := by
  refine ext_of_ne_zero fun x ξ _ => ?_
  obtain ⟨C, -, hbC⟩ := b.exists_bound {x} isCompact_singleton [] []
  refine (coefficient_eq_zero_of_norm_le hm a (C := C) (R := 2) (fun η hη => ?_) ξ).trans
    (by rw [coefficient_zero, Pi.zero_apply])
  have h := hbC x rfl η
  rwa [mixedDeriv_nil_nil, hb, coefficient_cutoffSymbol_of_two_le_norm χ a hη, List.length_nil,
    Nat.cast_zero, sub_zero] at h

end HomogeneousSymbol

namespace Symbol

open HomogeneousSymbol
open scoped ContDiff

/-- A coefficient `f` that is smooth on all of `ℝⁿ × ℝⁿ` and positively homogeneous of degree `m`
in the frequency away from `ξ = 0` is a symbol of order `m`: it agrees with the cut-off term of
the homogeneous symbol `HomogeneousSymbol.mk' f` at frequencies of norm at least `2`. Homogeneous
polynomials in `ξ` with smooth coefficients are of this form. -/
def ofContDiffHomogeneous (f : CoordinateSpace n × CoordinateSpace n → V →L[ℂ] W)
    (hf : ContDiff ℝ ∞ f)
    (hhom : ∀ x ξ, ξ ≠ 0 → ∀ t : ℝ, 0 < t → f (x, t • ξ) = t ^ m • f (x, ξ)) :
    Symbol n V W m where
  coefficient := f
  contDiff_coefficient := hf
  exists_bound := by
    obtain ⟨c, hc⟩ := exists_coefficient_eq_of_forall_le_norm hf
      (cutoffSymbol (default : FrequencyCutoff (CoordinateSpace n)) (mk' f hf.contDiffOn hhom)) 2
      fun x ξ hξ ↦ by
        have hξ0 : ξ ≠ 0 := norm_pos_iff.1 (by linarith)
        rw [coefficient_cutoffSymbol_of_two_le_norm _ _ hξ, coefficient_mk'_of_ne_zero _ _ _ hξ0]
    exact hc ▸ c.exists_bound

@[simp]
theorem coefficient_ofContDiffHomogeneous (f : CoordinateSpace n × CoordinateSpace n → V →L[ℂ] W)
    (hf : ContDiff ℝ ∞ f)
    (hhom : ∀ x ξ, ξ ≠ 0 → ∀ t : ℝ, 0 < t → f (x, t • ξ) = t ^ m • f (x, ξ)) :
    (ofContDiffHomogeneous f hf hhom : Symbol n V W m).coefficient = f :=
  (rfl)

end Symbol

end TauCeti
