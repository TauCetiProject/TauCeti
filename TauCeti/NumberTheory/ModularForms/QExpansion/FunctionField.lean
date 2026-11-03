/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Fuchsian.Compactification.Meromorphic
public import TauCeti.Analysis.Complex.RiemannSurface.FunctionField.Order
public import TauCeti.NumberTheory.ModularForms.QExpansion.Laurent
public import TauCeti.RingTheory.HahnSeries.Map

/-!
# Laurent `q`-expansions on the function field of a compactified Fuchsian quotient

Let `Γ ≤ PSL(2, ℝ)` be discrete and let `X = Subgroup.CompactifiedQuotient Γ` be its compactified
quotient, a connected Riemann surface. Its meromorphic functions form the field
`TauCeti.RiemannSurface.MeromorphicFunction X`; for a congruence subgroup this is the field of
meromorphic modular functions of that level. Given a normalized cusp datum `D` of width `w`, a
meromorphic function `F` on `X` pulls back to the function `z ↦ F (σ⁻¹ • z)` on the upper
half-plane, read in the scaling `σ` of `D`. This function is periodic of period `w` and is
meromorphic at `i∞`, so it has a Laurent expansion in `q = exp (2 π i z / w)`.

This file shows that this **Laurent `q`-expansion at `D`** is a homomorphism of `ℂ`-algebras
`Subgroup.CompactifiedQuotient.laurentQExpansion D` from the function field to the Laurent series
`ℂ⸨q⸩`. It is injective, which is the `q`-expansion principle for meromorphic functions on `X`; its
order is the order of `F` at the cusp of `D`; its constant term is the value of `F` at that cusp
when `F` is finite there; and the expansion converges to the pullback of `F` sufficiently high in
the upper half-plane.

For a subfield `K` of `ℂ`, the meromorphic functions whose expansion at `D` has all its
coefficients in `K` form a subfield `Subgroup.CompactifiedQuotient.coeffSubfield D K` of the
function field, containing exactly the constants in `K`. For the principal congruence subgroup
`Γ(N)`, its cusp `∞` in the identity scaling, of width `N`, and `K = ℚ(ζ_N)`, this is the field
`F_N` of modular functions of level `N` whose Fourier coefficients lie in `ℚ(ζ_N)`.

## Main declarations

* `Subgroup.CompactifiedQuotient.laurentQExpansion`: the Laurent `q`-expansion at a cusp datum, as a
  `ℂ`-algebra homomorphism.
* `Subgroup.CompactifiedQuotient.laurentQExpansion_injective`: the `q`-expansion principle.
* `Subgroup.CompactifiedQuotient.orderTop_laurentQExpansion`: the order at the cusp.
* `Subgroup.CompactifiedQuotient.laurentQExpansion_coeff_zero_eq_finitePart`: the value at the cusp.
* `Subgroup.CompactifiedQuotient.hasSum_laurentQExpansion`: convergence near the cusp.
* `Subgroup.CompactifiedQuotient.laurentQExpansion_ofMeromorphic`: the expansion of the
  meromorphic function defined by a function meromorphic at every point.
* `Subgroup.CompactifiedQuotient.coeffSubfield` and
  `Subgroup.CompactifiedQuotient.mem_coeffSubfield`: the subfield of functions with coefficients
  in a subfield of `ℂ`.

## References

* Goro Shimura, *Introduction to the Arithmetic Theory of Automorphic Functions*, Princeton
  University Press, 1971, §§2.1, 6.1.
* Fred Diamond and Jerry Shurman, *A First Course in Modular Forms*, Graduate Texts in
  Mathematics 228, Springer, 2005, §§2.4, 7.5.
-/

public noncomputable section

open Filter Function OnePoint Set Topology UpperHalfPlane TauCeti.RiemannSurface
open scoped MatrixGroups

namespace Subgroup.CompactifiedQuotient

variable {Γ : Subgroup PSL(2, ℝ)} [DiscreteTopology Γ] (D : Γ.CuspDatum)
  {F G : MeromorphicFunction Γ.CompactifiedQuotient}

/-- Off `q = 0`, the cusp function of the pullback of a function on the compactified quotient,
read in the scaling of `D`, is the function read in the cusp chart of `D`. -/
private theorem cuspFunction_eventuallyEq_comp_cuspChart_symm (H : Γ.CompactifiedQuotient → ℂ) :
    cuspFunction D.width (fun z ↦ H (ofQuotient (Quotient.mk _ (D.scaling⁻¹ • z))))
      =ᶠ[𝓝[≠] 0] H ∘ (cuspChart D le_rfl).symm := by
  have h := comp_cuspChart_symm_eventuallyEq (F := H) D le_rfl fun _ ↦ rfl
  rw [TauCeti.Subgroup.CuspDatum.cuspExtension_def] at h
  exact h.symm

/-- Two functions on the compactified quotient that agree near the cusp of `D` have pullbacks,
read in the scaling of `D`, whose cusp functions agree off `q = 0`. -/
theorem cuspFunction_eventuallyEq_of_eventuallyEq {H₁ H₂ : Γ.CompactifiedQuotient → ℂ}
    (h : H₁ =ᶠ[𝓝[≠] ofCusp D.cuspOrbit] H₂) :
    cuspFunction D.width (fun z ↦ H₁ (ofQuotient (Quotient.mk _ (D.scaling⁻¹ • z))))
      =ᶠ[𝓝[≠] 0] cuspFunction D.width fun z ↦ H₂ (ofQuotient (Quotient.mk _ (D.scaling⁻¹ • z))) :=
  (cuspFunction_eventuallyEq_comp_cuspChart_symm D H₁).trans <|
    .trans (h.comp_tendsto (tendsto_cuspChart_symm_nhdsNE D le_rfl))
      (cuspFunction_eventuallyEq_comp_cuspChart_symm D H₂).symm

/-- The cusp function of the pullback of a meromorphic function on the compactified quotient,
read in the scaling of `D`, is meromorphic at `0`. -/
theorem meromorphicAt_cuspFunction_finitePart (F : MeromorphicFunction Γ.CompactifiedQuotient) :
    _root_.MeromorphicAt (cuspFunction D.width
      (fun z ↦ F.finitePart (ofQuotient (Quotient.mk _ (D.scaling⁻¹ • z))))) 0 := by
  have h := (meromorphicAt_ofCusp_iff (F := F.finitePart) D fun _ ↦ rfl).mp
    (F.meromorphicAt_finitePart _)
  rwa [TauCeti.Subgroup.CuspDatum.cuspExtension_def] at h

/-- **The Laurent `q`-expansion at a cusp datum.** A meromorphic function `F` on the compactified
quotient is sent to the Laurent expansion in `q = exp (2 π i z / w)` of its pullback
`z ↦ F (σ⁻¹ • z)`, where `σ` is the scaling and `w` the width of `D`. This is a homomorphism of
`ℂ`-algebras. -/
def laurentQExpansion : MeromorphicFunction Γ.CompactifiedQuotient →ₐ[ℂ] LaurentSeries ℂ where
  toFun F := TauCeti.UpperHalfPlane.laurentQExpansion D.width
    fun z ↦ F.finitePart (ofQuotient (Quotient.mk _ (D.scaling⁻¹ • z)))
  map_one' := by
    simp only [MeromorphicFunction.finitePart_one, Pi.one_apply]
    exact TauCeti.UpperHalfPlane.laurentQExpansion_const _ 1 |>.trans (map_one _)
  map_mul' F G := by
    rw [TauCeti.UpperHalfPlane.laurentQExpansion_congr D.width_pos
      (cuspFunction_eventuallyEq_of_eventuallyEq D
        (MeromorphicFunction.finitePart_mul_eventuallyEq F G _))]
    exact TauCeti.UpperHalfPlane.laurentQExpansion_mul D.width_pos
      (meromorphicAt_cuspFunction_finitePart D F) (meromorphicAt_cuspFunction_finitePart D G)
  map_zero' := by
    simp only [MeromorphicFunction.finitePart_zero, Pi.zero_apply]
    exact TauCeti.UpperHalfPlane.laurentQExpansion_const _ 0 |>.trans (map_zero _)
  map_add' F G := by
    rw [TauCeti.UpperHalfPlane.laurentQExpansion_congr D.width_pos
      (cuspFunction_eventuallyEq_of_eventuallyEq D
        (MeromorphicFunction.finitePart_add_eventuallyEq F G _))]
    exact TauCeti.UpperHalfPlane.laurentQExpansion_add D.width_pos
      (meromorphicAt_cuspFunction_finitePart D F) (meromorphicAt_cuspFunction_finitePart D G)
  commutes' c := by
    simp only [MeromorphicFunction.finitePart_algebraMap]
    exact (TauCeti.UpperHalfPlane.laurentQExpansion_const _ c).trans
      (LaurentSeries.algebraMap_apply ℂ c).symm

/-- The Laurent `q`-expansion of `F` at `D` is the Laurent expansion at `i∞` of the pullback of `F`
read in the scaling of `D`. -/
theorem laurentQExpansion_apply (F : MeromorphicFunction Γ.CompactifiedQuotient) :
    laurentQExpansion D F = TauCeti.UpperHalfPlane.laurentQExpansion D.width
      fun z ↦ F.finitePart (ofQuotient (Quotient.mk _ (D.scaling⁻¹ • z))) :=
  (rfl)

/-- **The `q`-expansion principle.** A meromorphic function on the compactified quotient is
determined by its Laurent `q`-expansion at any cusp. -/
theorem laurentQExpansion_injective : Injective (laurentQExpansion D) :=
  (laurentQExpansion D).toRingHom.injective

/-- **The order at a cusp.** The order of the Laurent `q`-expansion of `F` at `D` is the order of
`F` at the cusp of `D`. -/
theorem orderTop_laurentQExpansion (F : MeromorphicFunction Γ.CompactifiedQuotient) :
    (laurentQExpansion D F).orderTop = MeromorphicFunction.order (ofCusp D.cuspOrbit) F := by
  rw [laurentQExpansion_apply, TauCeti.UpperHalfPlane.orderTop_laurentQExpansion D.width_pos
    (meromorphicAt_cuspFunction_finitePart D F), MeromorphicFunction.order_apply,
    meromorphicOrderAt_ofCusp (F := F.finitePart) D fun _ ↦ rfl,
    TauCeti.Subgroup.CuspDatum.cuspExtension_def]

/-- **The value at a cusp.** If `F` is finite at the cusp of `D`, the constant term of its Laurent
`q`-expansion at `D` is its value there. -/
theorem laurentQExpansion_coeff_zero_eq_finitePart (hF : F (ofCusp D.cuspOrbit) ≠ ∞) :
    (laurentQExpansion D F).coeff 0 = F.finitePart (ofCusp D.cuspOrbit) := by
  have hcont : ContinuousAt (F.finitePart ∘ (cuspChart D le_rfl).symm) 0 := by
    refine ContinuousAt.comp ?_ ((cuspChart D le_rfl).continuousAt_symm (by
      simpa using cuspRadius_pos D D.width))
    rw [cuspChart_symm_zero]
    exact MeromorphicFunction.continuousAt_finitePart hF
  have heq := TauCeti.UpperHalfPlane.cuspFunction_eventuallyEq_nhds_of_continuousAt
    (cuspFunction_eventuallyEq_comp_cuspChart_symm D F.finitePart) hcont
  have han : AnalyticAt ℂ (cuspFunction D.width
      (fun z ↦ F.finitePart (ofQuotient (Quotient.mk _ (D.scaling⁻¹ • z))))) 0 :=
    (meromorphicAt_cuspFunction_finitePart D F).analyticAt (hcont.congr heq.symm)
  rw [laurentQExpansion_apply,
    TauCeti.UpperHalfPlane.laurentQExpansion_coeff_zero_of_analyticAt D.width_pos han,
    heq.eq_of_nhds, comp_apply, cuspChart_symm_zero]

/-- **Convergence of the Laurent `q`-expansion.** Sufficiently high in the upper half-plane, the
pullback of `F` read in the scaling of `D` is the sum of the Laurent `q`-expansion of `F` at `D`
evaluated at `q = exp (2 π i z / w)`. -/
theorem hasSum_laurentQExpansion (F : MeromorphicFunction Γ.CompactifiedQuotient) :
    ∀ᶠ z : ℍ in atImInfty, HasSum
      (fun n : ℤ ↦ (laurentQExpansion D F).coeff n * Periodic.qParam D.width z ^ n)
      (F.finitePart (ofQuotient (Quotient.mk _ (D.scaling⁻¹ • z)))) := by
  have hper := TauCeti.Subgroup.CuspDatum.periodic_comp_ofComplex_inv_smul D
    (fun z ↦ F.finitePart (ofQuotient (Quotient.mk _ z))) fun g z ↦
      congrArg (fun p ↦ F.finitePart (ofQuotient p))
        (Quotient.sound (MulAction.orbitRel_apply.mpr (MulAction.mem_orbit z (g : Γ))))
  exact TauCeti.UpperHalfPlane.hasSum_laurentQExpansion D.width_pos hper
    (meromorphicAt_cuspFunction_finitePart D F)

/-- The Laurent `q`-expansion of the meromorphic function defined by a function `H` on the
compactified quotient, meromorphic at every point, is the Laurent expansion at `i∞` of the pullback
of `H` read in the scaling of `D`. -/
theorem laurentQExpansion_ofMeromorphic {H : Γ.CompactifiedQuotient → ℂ}
    (hH : ∀ x, MeromorphicAt H x) :
    laurentQExpansion D (MeromorphicFunction.ofMeromorphic hH) =
      TauCeti.UpperHalfPlane.laurentQExpansion D.width
        fun z ↦ H (ofQuotient (Quotient.mk _ (D.scaling⁻¹ • z))) :=
  TauCeti.UpperHalfPlane.laurentQExpansion_congr D.width_pos
    (cuspFunction_eventuallyEq_of_eventuallyEq D
      (MeromorphicFunction.finitePart_ofMeromorphic_eventuallyEq hH _))

/-! ### Meromorphic functions with coefficients in a subfield -/

/-- The meromorphic functions on the compactified quotient whose Laurent `q`-expansion at `D` has
all its coefficients in a subfield `K` of `ℂ`. They form a subfield of the function field, the
preimage under the expansion of the Laurent series with coefficients in `K`
(`Subgroup.CompactifiedQuotient.mem_coeffSubfield`). -/
def coeffSubfield (K : Subfield ℂ) : Subfield (MeromorphicFunction Γ.CompactifiedQuotient) :=
  (HahnSeries.mapRingHom K.subtype : LaurentSeries K →+* LaurentSeries ℂ).fieldRange.comap
    (laurentQExpansion D : MeromorphicFunction Γ.CompactifiedQuotient →+* LaurentSeries ℂ)

/-- A meromorphic function lies in `coeffSubfield D K` exactly when all the coefficients of its
Laurent `q`-expansion at `D` lie in `K`. -/
theorem mem_coeffSubfield {K : Subfield ℂ} :
    F ∈ coeffSubfield D K ↔ ∀ n, (laurentQExpansion D F).coeff n ∈ K := by
  rw [coeffSubfield, Subfield.mem_comap, RingHom.mem_fieldRange, ← RingHom.mem_rangeS,
    HahnSeries.mem_map_rangeS]
  simp

/-- A constant function lies in `coeffSubfield D K` exactly when its value lies in `K`. -/
@[simp]
theorem algebraMap_mem_coeffSubfield {K : Subfield ℂ} {c : ℂ} :
    algebraMap ℂ (MeromorphicFunction Γ.CompactifiedQuotient) c ∈ coeffSubfield D K ↔ c ∈ K := by
  rw [mem_coeffSubfield, AlgHom.commutes, LaurentSeries.algebraMap_apply]
  refine ⟨fun h ↦ by simpa using h 0, fun hc n ↦ ?_⟩
  rw [HahnSeries.C_apply, HahnSeries.coeff_single]
  split_ifs
  · exact hc
  · exact K.zero_mem

/-- Enlarging the coefficient field enlarges the subfield. -/
theorem coeffSubfield_mono {K L : Subfield ℂ} (h : K ≤ L) : coeffSubfield D K ≤ coeffSubfield D L :=
  fun _ hF ↦ (mem_coeffSubfield D).mpr fun n ↦ h ((mem_coeffSubfield D).mp hF n)

/-- Every meromorphic function has its coefficients in `ℂ`. -/
@[simp]
theorem coeffSubfield_top : coeffSubfield D (⊤ : Subfield ℂ) = ⊤ :=
  eq_top_iff.mpr fun _ _ ↦ (mem_coeffSubfield D).mpr fun _ ↦ Subfield.mem_top _

end Subgroup.CompactifiedQuotient
