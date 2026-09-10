/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.LocalGlobal.Completion
public import TauCeti.NumberTheory.QuadraticForm.Global.Localization

/-!
# Quadratic forms in towers of number-field completions

For an extension of number fields `L/K` and finite places `w` above `v`, localization commutes
with scalar extension from `K` to `L`.  The comparison uses the canonical completion map
`K_v → L_w`, and identifies both iterated tensor-product spaces with `L_w ⊗[K] V`.

This compatibility is the bridge needed to transfer local properties of a quadratic form over
`K` to the completions of a field extension.  In particular, it allows an isotropic vector over
`K_v` to be extended to every `L_w` above it.

## References

* [J. Neukirch, *Algebraic Number Theory*][Neukirch1992], Chapter II, §6.
-/

public section
noncomputable section

open IsDedekindDomain NumberField
open scoped AdicCompletionExtension TensorProduct

universe uK uL uV

namespace QuadraticForm

variable {K : Type uK} [Field K] [NumberField K]
variable {L : Type uL} [Field L] [NumberField L] [Algebra K L]
variable {V : Type uV} [AddCommGroup V] [Module K V]

/-- Localization after extending a quadratic form from `K` to `L` is canonically isometric to
extending its localization along the completion map `K_v → L_w`. -/
def atFinitePlaceBaseChange (Q : _root_.QuadraticForm K V)
    (v : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (w : HeightOneSpectrum (NumberField.RingOfIntegers L))
    [w.asIdeal.LiesOver v.asIdeal] :
    letI : Invertible (2 : v.adicCompletion K) :=
      (Invertible.map (algebraMap K (v.adicCompletion K)) 2).copy 2 (map_ofNat _ _).symm
    (atFinitePlace (Q.baseChange L) w).IsometryEquiv
      ((atFinitePlace Q v).baseChange (w.adicCompletion L)) := by
  letI : Invertible (2 : L) :=
    (Invertible.map (algebraMap K L) 2).copy 2 (map_ofNat _ _).symm
  letI : Invertible (2 : v.adicCompletion K) :=
    (Invertible.map (algebraMap K (v.adicCompletion K)) 2).copy 2 (map_ofNat _ _).symm
  let e := (baseChangeBaseChange (A := L) (B := w.adicCompletion L) Q).symm.trans
    (baseChangeBaseChange (A := v.adicCompletion K) (B := w.adicCompletion L) Q)
  exact
    { toLinearEquiv := e.toLinearEquiv
      map_app' := fun x ↦ by
        have hQ : atFinitePlace (Q.baseChange L) w =
            (Q.baseChange L).baseChange (w.adicCompletion L) := by
          rw [atFinitePlace_def]
          apply _root_.baseChange_ext
          intro y
          simp [Algebra.smul_def]
        rw [hQ, atFinitePlace_def]
        exact e.map_app x }

/-- The localization/base-change isometry is the composite of the two canonical tensor-product
cancellations through `L_w ⊗[K] V`. -/
@[simp]
theorem atFinitePlaceBaseChange_toLinearEquiv (Q : _root_.QuadraticForm K V)
    (v : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (w : HeightOneSpectrum (NumberField.RingOfIntegers L))
    [w.asIdeal.LiesOver v.asIdeal] :
    letI : Invertible (2 : v.adicCompletion K) :=
      (Invertible.map (algebraMap K (v.adicCompletion K)) 2).copy 2 (map_ofNat _ _).symm
    (atFinitePlaceBaseChange Q v w).toLinearEquiv =
      (TensorProduct.AlgebraTensorModule.cancelBaseChange K L (w.adicCompletion L)
        (w.adicCompletion L) V).trans
        (TensorProduct.AlgebraTensorModule.cancelBaseChange K (v.adicCompletion K)
          (w.adicCompletion L) (w.adicCompletion L) V).symm := by
  let _ : Invertible (2 : v.adicCompletion K) :=
    (Invertible.map (algebraMap K (v.adicCompletion K)) 2).copy 2 (map_ofNat _ _).symm
  simp only [atFinitePlaceBaseChange, QuadraticMap.IsometryEquiv.trans,
    QuadraticMap.IsometryEquiv.symm, baseChangeBaseChange_toLinearEquiv,
    LinearEquiv.symm_symm]

/-- The localization/base-change comparison sends a twice-pure tensor to the same global vector,
with the intermediate scalar transported along `K_v → L_w`. -/
@[simp]
theorem atFinitePlaceBaseChange_tmul (Q : _root_.QuadraticForm K V)
    (v : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (w : HeightOneSpectrum (NumberField.RingOfIntegers L))
    [w.asIdeal.LiesOver v.asIdeal] (b : w.adicCompletion L) (a : L) (x : V) :
    atFinitePlaceBaseChange Q v w (b ⊗ₜ (a ⊗ₜ x)) =
      (algebraMap L (w.adicCompletion L) a * b) ⊗ₜ (1 ⊗ₜ x) := by
  let _ : Invertible (2 : v.adicCompletion K) :=
    (Invertible.map (algebraMap K (v.adicCompletion K)) 2).copy 2 (map_ofNat _ _).symm
  have h := DFunLike.congr_fun (atFinitePlaceBaseChange_toLinearEquiv Q v w)
    (b ⊗ₜ (a ⊗ₜ x))
  have hf := congrFun (QuadraticMap.IsometryEquiv.coe_toLinearEquiv
    (atFinitePlaceBaseChange Q v w)) (b ⊗ₜ (a ⊗ₜ x))
  apply hf.symm.trans
  simpa only [LinearEquiv.trans_apply,
    TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul,
    TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul, Algebra.smul_def] using h

/-- The inverse localization/base-change comparison multiplies a completion scalar by the image
of its intermediate `K_v`-scalar. -/
@[simp]
theorem atFinitePlaceBaseChange_symm_tmul (Q : _root_.QuadraticForm K V)
    (v : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (w : HeightOneSpectrum (NumberField.RingOfIntegers L))
    [w.asIdeal.LiesOver v.asIdeal] (b : w.adicCompletion L)
    (a : v.adicCompletion K) (x : V) :
    (atFinitePlaceBaseChange Q v w).symm (b ⊗ₜ (a ⊗ₜ x)) =
      (algebraMap (v.adicCompletion K) (w.adicCompletion L) a * b) ⊗ₜ (1 ⊗ₜ x) := by
  apply (atFinitePlaceBaseChange Q v w).symm_apply_eq.mpr
  symm
  rw [atFinitePlaceBaseChange_tmul]
  simp only [map_one, one_mul]
  rw [← Algebra.smul_def]
  calc
    (a • b) ⊗ₜ (1 ⊗ₜ x) = b ⊗ₜ (a • (1 ⊗ₜ x)) :=
      TensorProduct.smul_tmul a b (1 ⊗ₜ x)
    _ = b ⊗ₜ (a ⊗ₜ x) := by
      apply congrArg (fun y : v.adicCompletion K ⊗[K] V ↦
        b ⊗ₜ[v.adicCompletion K] y)
      simpa only [smul_eq_mul, mul_one] using
        (TensorProduct.smul_tmul' a (1 : v.adicCompletion K) x)

end QuadraticForm
