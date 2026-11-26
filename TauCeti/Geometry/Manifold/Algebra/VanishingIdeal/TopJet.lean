/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Algebra.VanishingIdeal.Pow
public import TauCeti.Topology.Algebra.Module.Multilinear.Symmetric
import TauCeti.Analysis.Calculus.IteratedFDeriv.Symmetric
import TauCeti.Analysis.Calculus.Jet.Realization
import TauCeti.Geometry.Manifold.ContMDiffMap.ExtChartAt
import TauCeti.Geometry.Manifold.MFDeriv.Chart.Basic

/-!
# The top jet quotient of the vanishing ideal

Let `I_x` be the ideal of smooth real functions on a manifold `M` vanishing at an interior point
`x`. The quotient `C^∞(M) / I_x ^ (m + 1)` is the space of `m`-jets at `x`
(`TauCeti.quotient_mk_smoothVanishingIdeal_pow_succ_eq_iff`), and truncation of jets
`C^∞(M) / I_x ^ (m + 1) → C^∞(M) / I_x ^ m` has kernel `I_x ^ m / I_x ^ (m + 1)`, the top-order
part of an `m`-jet. This file identifies that kernel with the symmetric cotangent tensors of
degree `m`, the symmetric `m`-linear forms on the tangent space `T_xM`.

A function `f ∈ I_x ^ m` has a chart expression whose derivatives of order `< m` vanish at the
image of `x`, and its top jet is the `m`-th derivative there,

`TauCeti.smoothTopJet hx m f = D^m (f ∘ φ⁻¹) (φ x)`, `φ = extChartAt I x`,

a symmetric `m`-linear form on `T_xM`. It vanishes exactly on `I_x ^ (m + 1)`
(`TauCeti.smoothTopJet_eq_zero_iff`, Hadamard's lemma of order `m`), and every symmetric form is
the top jet of a function in `I_x ^ m`, realized by a cut-off homogeneous polynomial of degree `m`
in the chart (`TauCeti.smoothTopJet_surjective`). Hence

`TauCeti.smoothTopJetEquiv hx m : I_x ^ m / I_x ^ (m + 1) ≃ Sym^m T_x*M`.

In degree one the top jet is the differential at `x` (`TauCeti.smoothTopJet_one_apply`), as in
the cotangent identification `I_x / I_x² ≃ T_x*M` of `TauCeti.smoothCotangentEquiv`; in degree
zero it is evaluation at `x` (`TauCeti.smoothTopJet_zero_apply`). For `m = 2` the top jet of a
function with a critical zero at `x` is its Hessian there. The forms are those on Mathlib's model
of `T_xM`, the model space of `M` read through the preferred chart at `x`, the same model in which
`mfderiv` takes its values.

The top jet quotient carries the principal part of a jet. A differential operator `D` of order at
most `m` on `C^∞(M)` maps `I_x ^ (m + 1)` into `I_x`, so on `I_x ^ m` the value `(D f)(x)` only
depends on the top jet of `f` (`TauCeti.differentialOperators_apply_eq_of_smoothTopJet_eq`).

## Main definitions

* `TauCeti.smoothTopJet hx m`: the top jet `I_x ^ m → Sym^m T_x*M`, as a real-linear map.
* `TauCeti.smoothTopJetEquiv hx m`: the induced linear equivalence
  `I_x ^ m / I_x ^ (m + 1) ≃ Sym^m T_x*M`.

## Main results

* `TauCeti.smoothTopJet_eq_zero_iff`, `TauCeti.ker_smoothTopJet`: the top jet of `f ∈ I_x ^ m`
  vanishes if and only if `f ∈ I_x ^ (m + 1)`.
* `TauCeti.smoothTopJet_surjective`: every symmetric `m`-linear form on `T_xM` is a top jet.
* `TauCeti.smoothTopJet_zero_apply`, `TauCeti.smoothTopJet_one_apply`: in degrees zero and one
  the top jet is the value and the differential at `x`.
* `TauCeti.differentialOperators_apply_eq_of_smoothTopJet_eq`: on `I_x ^ m`, a differential
  operator of order at most `m` sees only the top jet at `x`.

## References

* I. Kolář, P. W. Michor, J. Slovák, *Natural operations in differential geometry*, Springer,
  1993, §12 (jets and the symmetric tensors in the kernel of jet truncation).
-/

public section

open scoped ContDiff Manifold Topology

noncomputable section

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {x : M}

/-- At an interior point the chart expression of a smooth function is smooth at the image of the
point. -/
private theorem contDiffAt_comp_extChartAt_symm (hx : I.IsInteriorPoint x)
    (f : C^∞⟮I, M; ℝ⟯) :
    ContDiffAt ℝ ∞ ((f : M → ℝ) ∘ (extChartAt I x).symm) (extChartAt I x x) :=
  f.contMDiff.contMDiffAt.contDiffAt_comp_extChartAt_symm_of_isInteriorPoint hx

/-- **The top jet.** At an interior point `x`, the top jet of a function `f ∈ I_x ^ m` is the
symmetric `m`-linear form on `T_xM`, modelled by `E`, given by the `m`-th derivative of its chart
expression at the image of `x`; the derivatives of lower order vanish there. -/
def smoothTopJet (hx : I.IsInteriorPoint x) (m : ℕ) :
    (smoothVanishingIdeal I x ^ m).restrictScalars ℝ →ₗ[ℝ]
      ContinuousMultilinearMap.symmetric ℝ E ℝ (Fin m) where
  toFun f :=
    ⟨iteratedFDeriv ℝ m (((f : C^∞⟮I, M; ℝ⟯) : M → ℝ) ∘ (extChartAt I x).symm)
        (extChartAt I x x),
      ContinuousMultilinearMap.mem_symmetric.mpr fun v σ ↦
        (contDiffAt_comp_extChartAt_symm hx (f : C^∞⟮I, M; ℝ⟯))
          |>.iteratedFDeriv_comp_perm_of_minSmoothness_le (by simp) v σ⟩
  map_add' f g := by
    ext1
    simp only [Submodule.coe_add]
    exact iteratedFDeriv_add_apply ((contDiffAt_comp_extChartAt_symm hx _).of_le (by simp))
      ((contDiffAt_comp_extChartAt_symm hx _).of_le (by simp))
  map_smul' c f := by
    ext1
    simp only [Submodule.coe_smul, RingHom.id_apply]
    exact iteratedFDeriv_const_smul_apply
      ((contDiffAt_comp_extChartAt_symm hx _).of_le (by simp))

/-- The top jet of `f` is the `m`-th derivative of its chart expression at the image of `x`. -/
@[simp]
theorem coe_smoothTopJet (hx : I.IsInteriorPoint x) (m : ℕ)
    (f : (smoothVanishingIdeal I x ^ m).restrictScalars ℝ) :
    (smoothTopJet hx m f : E [×m]→L[ℝ] ℝ) =
      iteratedFDeriv ℝ m (((f : C^∞⟮I, M; ℝ⟯) : M → ℝ) ∘ (extChartAt I x).symm)
        (extChartAt I x x) :=
  (rfl)

/-- In degree zero the top jet is the value at `x`. -/
theorem smoothTopJet_zero_apply (hx : I.IsInteriorPoint x)
    (f : (smoothVanishingIdeal I x ^ 0).restrictScalars ℝ) (v : Fin 0 → E) :
    (smoothTopJet hx 0 f : E [×0]→L[ℝ] ℝ) v =
      (f : C^∞⟮I, M; ℝ⟯) x := by
  simp

/-- In degree one the top jet is the differential at `x`. -/
theorem smoothTopJet_one_apply (hx : I.IsInteriorPoint x)
    (f : (smoothVanishingIdeal I x ^ 1).restrictScalars ℝ) (v : Fin 1 → E) :
    (smoothTopJet hx 1 f : E [×1]→L[ℝ] ℝ) v =
      mvfderiv I (f : C^∞⟮I, M; ℝ⟯) x (v 0 : TangentSpace I x) := by
  -- At an interior point, the differential of `f` is the derivative of its chart expression.
  have hmd : MDifferentiableAt I 𝓘(ℝ, ℝ) (f : C^∞⟮I, M; ℝ⟯) x :=
    ((f : C^∞⟮I, M; ℝ⟯).contMDiff.mdifferentiable (by simp)) x
  have htarget : (extChartAt I x).target ∈ 𝓝 (extChartAt I x x) :=
    Filter.mem_of_superset (isOpen_interior.mem_nhds
      ((ModelWithCorners.isInteriorPoint_iff (I := I)).mp hx)) interior_subset
  rw [mvfderiv_eq_fderivWithin_extChartAt_target hmd, fderivWithin_of_mem_nhds htarget,
    coe_smoothTopJet, iteratedFDeriv_one_apply]
  -- Both sides evaluate the same derivative at `v 0`, read in `E` and in its synonym `T_xM`.
  rfl

variable [FiniteDimensional ℝ E] [IsManifold I ∞ M] [T2Space M]

/-- A function in `I_x ^ m` has a chart expression whose derivatives of order `< m` vanish at the
image of `x`. -/
private theorem iteratedFDeriv_comp_extChartAt_symm_eq_zero_of_lt (hx : I.IsInteriorPoint x)
    {m : ℕ} (f : (smoothVanishingIdeal I x ^ m).restrictScalars ℝ) {k : ℕ} (hk : k < m) :
    iteratedFDeriv ℝ k (((f : C^∞⟮I, M; ℝ⟯) : M → ℝ) ∘ (extChartAt I x).symm)
      (extChartAt I x x) = 0 :=
  (mem_smoothVanishingIdeal_pow_iff_of_isInteriorPoint hx m _).mp
    ((Submodule.restrictScalars_mem ℝ _ _).mp f.property) k hk

/-- **The kernel of the top jet.** The top jet of `f ∈ I_x ^ m` vanishes if and only if
`f ∈ I_x ^ (m + 1)`. -/
theorem smoothTopJet_eq_zero_iff (hx : I.IsInteriorPoint x) {m : ℕ}
    (f : (smoothVanishingIdeal I x ^ m).restrictScalars ℝ) :
    smoothTopJet hx m f = 0 ↔ (f : C^∞⟮I, M; ℝ⟯) ∈ smoothVanishingIdeal I x ^ (m + 1) := by
  rw [mem_smoothVanishingIdeal_pow_succ_iff_of_isInteriorPoint hx, ← Subtype.coe_inj,
    coe_smoothTopJet, ZeroMemClass.coe_zero]
  refine ⟨fun h k hk ↦ ?_, fun h ↦ h m le_rfl⟩
  rcases hk.lt_or_eq with hk | rfl
  · exact iteratedFDeriv_comp_extChartAt_symm_eq_zero_of_lt hx f hk
  · exact h

/-- The kernel of the top jet on `I_x ^ m` is `I_x ^ (m + 1)`. -/
theorem ker_smoothTopJet (hx : I.IsInteriorPoint x) (m : ℕ) :
    LinearMap.ker (smoothTopJet hx m) =
      ((smoothVanishingIdeal I x ^ (m + 1)).restrictScalars ℝ).comap
        ((smoothVanishingIdeal I x ^ m).restrictScalars ℝ).subtype := by
  ext f
  rw [LinearMap.mem_ker, smoothTopJet_eq_zero_iff, Submodule.mem_comap,
    Submodule.restrictScalars_mem, Submodule.subtype_apply]

/-- **Every symmetric form is a top jet.** Every symmetric `m`-linear form on `T_xM` is the top
jet of a function in `I_x ^ m`: a homogeneous polynomial of degree `m` in the chart, cut off away
from `x`. -/
theorem smoothTopJet_surjective (hx : I.IsInteriorPoint x) (m : ℕ) :
    Function.Surjective (smoothTopJet hx m) := by
  intro L
  -- The jet with top coefficient `L` and vanishing lower coefficients.
  let A : (i : Fin (m + 1)) → E [×i.val]→L[ℝ] ℝ :=
    Fin.lastCases (motive := fun i ↦ E [×i.val]→L[ℝ] ℝ)
      (L : E [×m]→L[ℝ] ℝ) fun _ ↦ 0
  have hA : ∀ i (v : Fin i.val → E) (σ : Equiv.Perm (Fin i.val)), A i (v ∘ σ) = A i v := by
    intro i
    induction i using Fin.lastCases with
    | last => simp [A]
    | cast i => simp [A]
  obtain ⟨u, hu, -, -, huA⟩ :=
    exists_contDiff_hasCompactSupport_iteratedFDeriv_eq m A hA (extChartAt I x x) Filter.univ_mem
  -- Transplant `u` to `M` through a globally smooth map with the germ of the chart.
  obtain ⟨F, hF⟩ := exists_contMDiffMap_eventuallyEq_extChartAt (I := I) x
  let f : C^∞⟮I, M; ℝ⟯ := ⟨u ∘ F, hu.contMDiff.comp F.contMDiff⟩
  have hchart : ((f : M → ℝ) ∘ (extChartAt I x).symm) =ᶠ[𝓝 (extChartAt I x x)] u :=
    comp_extChartAt_symm_eventuallyEq_of_eventuallyEq_comp hx hF (Filter.EventuallyEq.refl _ _)
  have hderiv (i : Fin (m + 1)) :
      iteratedFDeriv ℝ i ((f : M → ℝ) ∘ (extChartAt I x).symm) (extChartAt I x x) = A i :=
    ((hchart.iteratedFDeriv ℝ i).eq_of_nhds).trans (huA i)
  have hfm : f ∈ smoothVanishingIdeal I x ^ m :=
    (mem_smoothVanishingIdeal_pow_iff_of_isInteriorPoint hx m f).mpr fun k hk ↦ by
      simpa [A, -Fin.castSucc_mk] using hderiv (Fin.castSucc ⟨k, hk⟩)
  refine ⟨⟨f, (Submodule.restrictScalars_mem ℝ _ _).mpr hfm⟩, Subtype.ext ?_⟩
  simpa [A] using hderiv (Fin.last m)

/-- **Differential operators see only top jets.** At an interior point `x`, a differential operator
of order at most `m` on `C^∞(M)` takes the same value at `x` on two functions of `I_x ^ m` with
the same top jet. -/
theorem differentialOperators_apply_eq_of_smoothTopJet_eq {m : ℕ}
    {D : C^∞⟮I, M; ℝ⟯ →ₗ[ℝ] C^∞⟮I, M; ℝ⟯}
    (hD : D ∈ differentialOperators ℝ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ m)
    (hx : I.IsInteriorPoint x) {f g : (smoothVanishingIdeal I x ^ m).restrictScalars ℝ}
    (hfg : smoothTopJet hx m f = smoothTopJet hx m g) :
    D f x = D g x := by
  refine differentialOperators_apply_eq_of_iteratedFDeriv_eq hD hx fun k hk ↦ ?_
  rcases hk.lt_or_eq with hk | rfl
  · rw [iteratedFDeriv_comp_extChartAt_symm_eq_zero_of_lt hx f hk,
      iteratedFDeriv_comp_extChartAt_symm_eq_zero_of_lt hx g hk]
  · simpa using congrArg Subtype.val hfg

-- Implementation note: `smoothTopJetEquiv` is assembled from this `liftQ` into all `m`-linear
-- forms, `codRestrict` and `LinearEquiv.ofBijective` rather than from
-- `LinearMap.quotKerEquivOfSurjective`: with the submodule of symmetric forms as codomain, the
-- latter times out on an instance defeq check in the module system.
/-- The top jet on the quotient `I_x ^ m / I_x ^ (m + 1)`, with values in all `m`-linear forms. -/
private def smoothTopJetQuot (hx : I.IsInteriorPoint x) (m : ℕ) :
    ((smoothVanishingIdeal I x ^ m).restrictScalars ℝ ⧸
        ((smoothVanishingIdeal I x ^ (m + 1)).restrictScalars ℝ).comap
          ((smoothVanishingIdeal I x ^ m).restrictScalars ℝ).subtype) →ₗ[ℝ] E [×m]→L[ℝ] ℝ :=
  Submodule.liftQ _ ((ContinuousMultilinearMap.symmetric ℝ E ℝ (Fin m)).subtype ∘ₗ
    smoothTopJet hx m) fun f hf ↦ by
      rw [← ker_smoothTopJet hx m, LinearMap.mem_ker] at hf
      simp [hf]

private theorem smoothTopJetQuot_mk (hx : I.IsInteriorPoint x) (m : ℕ)
    (f : (smoothVanishingIdeal I x ^ m).restrictScalars ℝ) :
    smoothTopJetQuot hx m (Submodule.Quotient.mk f) = smoothTopJet hx m f :=
  (rfl)

/-- **The top jet quotient is the space of symmetric cotangent tensors.** At an interior point `x`
of a finite-dimensional Hausdorff real manifold, the top jet induces a real-linear equivalence
`I_x ^ m / I_x ^ (m + 1) ≃ Sym^m T_x*M` onto the symmetric `m`-linear forms on `T_xM`. -/
def smoothTopJetEquiv (hx : I.IsInteriorPoint x) (m : ℕ) :
    ((smoothVanishingIdeal I x ^ m).restrictScalars ℝ ⧸
        ((smoothVanishingIdeal I x ^ (m + 1)).restrictScalars ℝ).comap
          ((smoothVanishingIdeal I x ^ m).restrictScalars ℝ).subtype) ≃ₗ[ℝ]
      ContinuousMultilinearMap.symmetric ℝ E ℝ (Fin m) :=
  LinearEquiv.ofBijective
    (LinearMap.codRestrict _ (smoothTopJetQuot hx m) fun q ↦ by
      induction q using Submodule.Quotient.induction_on with
      | H f => exact smoothTopJetQuot_mk hx m f ▸ (smoothTopJet hx m f).property)
    ⟨fun q₁ q₂ h ↦ by
      induction q₁ using Submodule.Quotient.induction_on with | H f₁ =>
      induction q₂ using Submodule.Quotient.induction_on with | H f₂ =>
      rw [Submodule.Quotient.eq, ← ker_smoothTopJet hx m, LinearMap.mem_ker, map_sub, sub_eq_zero]
      exact Subtype.ext (by simpa [smoothTopJetQuot_mk] using congrArg Subtype.val h),
    fun L ↦ by
      obtain ⟨f, rfl⟩ := smoothTopJet_surjective hx m L
      exact ⟨Submodule.Quotient.mk f, Subtype.ext (smoothTopJetQuot_mk hx m f)⟩⟩

/-- The equivalence `I_x ^ m / I_x ^ (m + 1) ≃ Sym^m T_x*M` sends the class of `f` to its top
jet. -/
@[simp]
theorem smoothTopJetEquiv_mk (hx : I.IsInteriorPoint x) (m : ℕ)
    (f : (smoothVanishingIdeal I x ^ m).restrictScalars ℝ) :
    smoothTopJetEquiv hx m (Submodule.Quotient.mk f) = smoothTopJet hx m f :=
  Subtype.ext (smoothTopJetQuot_mk hx m f)

end TauCeti
