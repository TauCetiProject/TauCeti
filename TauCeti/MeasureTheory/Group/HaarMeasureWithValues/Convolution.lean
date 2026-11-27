/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Group.HaarMeasureWithValues.Fubini
public import TauCeti.RepresentationTheory.Smooth.CompactSupport

/-!
# Convolution against a Haar measure with values in a ring

Let `G` be a Hausdorff topological group, `A` a commutative semiring and `μ` an `A`-valued Haar
measure on `G` (`TauCeti.HaarMeasureWithValues A G`). The convolution of two locally constant
functions `f₁ f₂ : G → A` with compact support is
`(f₁ ⋆ f₂)(x) = ∫ f₁(y) f₂(y⁻¹x) dμ(y)` (`TauCeti.HaarMeasureWithValues.convolution`).
It is again locally constant with compact support, being the integral in the second variable of
the kernel `(x, y) ↦ f₁(y) f₂(y⁻¹x)` on `G × G`
(`TauCeti.HaarMeasureWithValues.convolutionKernel`). Convolution is `A`-bilinear and associative,
so `C_c^∞(G, A)` with convolution is an associative non-unital `A`-algebra, the **Hecke algebra**
`TauCeti.HeckeAlgebra μ` of `G` with respect to `μ`. For a locally profinite group this is the
Hecke algebra `H(G, A)` of the representation theory of `G`; the coefficient ring is arbitrary,
for instance `ℤ[1/p]` for a `p`-adic group.

## Main definitions

* `TauCeti.HaarMeasureWithValues.convolution μ`: the `A`-bilinear convolution on `C_c^∞(G, A)`.
* `TauCeti.HeckeAlgebra μ`: `C_c^∞(G, A)` with convolution as multiplication, a non-unital
  semiring (a non-unital ring when `A` is a ring) and an `A`-module with
  `IsScalarTower` and `SMulCommClass`, that is, a non-unital `A`-algebra.

## Main results

* `TauCeti.HaarMeasureWithValues.integral_compactlySupportedRep`: the integral is invariant under
  left translation.
* `TauCeti.HaarMeasureWithValues.convolution_assoc`: convolution is associative.
* `TauCeti.HaarMeasureWithValues.convolution_smul_measure`: `f₁ ⋆_{cμ} f₂ = c (f₁ ⋆_μ f₂)`.
* `TauCeti.HaarMeasureWithValues.support_convolution_subset`:
  `supp (f₁ ⋆ f₂) ⊆ supp f₁ · supp f₂`.
* `TauCeti.HaarMeasureWithValues.convolution_compactlySupportedRep_left`,
  `TauCeti.HaarMeasureWithValues.convolution_compactlySupportedRep_right`: convolution commutes
  with left translation of the first factor and with right translation of the second. In
  particular, if `f₁` is invariant under left translation by a subgroup then so is `f₁ ⋆ f₂`, and
  if `f₂` is invariant under right translation then so is `f₁ ⋆ f₂`.
* `TauCeti.HaarMeasureWithValues.convolution_compactOpenIndicator_self`: `1_U ⋆ 1_U = μ(U) • 1_U`
  for a compact open subgroup `U`.
* `TauCeti.HaarMeasureWithValues.convolution_apply_of_discrete`: on a finite discrete group,
  `(f₁ ⋆ f₂)(x) = μ({1}) • ∑_y f₁(y) f₂(y⁻¹x)`.

## Implementation notes

Associativity is Fubini's theorem
(`TauCeti.HaarMeasureWithValues.integral_integralRight`,
`TauCeti.HaarMeasureWithValues.integral_integralLeft`) for
`(y, z) ↦ f₁(z) f₂(z⁻¹y) f₃(y⁻¹x)`, together with the invariance of the integral under left
translation. The Hecke algebra is a one-field structure around `C_c^∞(G, A)`, so that the
multiplication, which depends on `μ`, is not an instance on `C_c^∞(G, A)` itself.

## References

* J. Bernstein, *Representations of p-adic groups*, Harvard lectures 1992, written by
  K. Rumelhart, Chapter I, §2.1, Definition 7 and Proposition 5, pp. 11–12.
* C. J. Bushnell and G. Henniart, *The Local Langlands Conjecture for GL(2)*, Grundlehren der
  mathematischen Wissenschaften 335, Springer, 2006, §4.1, pp. 33–34.
-/

public section

open Set Function TopologicalSpace LocallyConstant
open scoped Pointwise

namespace TauCeti

namespace HaarMeasureWithValues

variable {A G M : Type*} [CommSemiring A] [Group G] [TopologicalSpace G]

/-! ### Left invariance of the integral -/

section Invariance

variable [ContinuousConstSMul G G] [T2Space G] [AddCommMonoid M] [Module A M]
  (μ : HaarMeasureWithValues A G)

/-- **Left invariance of the integral**: `∫ f(g⁻¹y) dμ(y) = ∫ f dμ`. -/
@[simp]
theorem integral_compactlySupportedRep (g : G) (f : compactlySupported A G M) :
    μ.integral (compactlySupportedRep A G G M g f) = μ.integral f := by
  refine LinearMap.congr_fun (eq_integral_of_apply_compactOpenIndicator μ
    (μ.integral ∘ₗ compactlySupportedRep A G G M g) fun K m ↦ ?_) f
  rw [LinearMap.comp_apply, compactlySupportedRep_apply_compactOpenIndicator,
    integral_compactOpenIndicator, apply_smul]

end Invariance

/-! ### The convolution kernel and convolution -/

section Convolution

variable [IsTopologicalGroup G] [T2Space G]

/-- The **convolution kernel** `(x, y) ↦ f₁(y) f₂(y⁻¹x)` of two locally constant functions with
compact support, a locally constant function on `G × G` with compact support: its support lies in
the image of `supp f₁ × supp f₂` under `(y, z) ↦ (yz, y)`. Integrating it in the second variable
gives the convolution `f₁ ⋆ f₂`. -/
noncomputable def convolutionKernel (f₁ f₂ : compactlySupported A G A) :
    compactlySupported A (G × G) A :=
  ⟨(f₁ : LocallyConstant G A).comap ContinuousMap.snd *
      (f₂ : LocallyConstant G A).comap ⟨fun p : G × G ↦ p.2⁻¹ * p.1, by fun_prop⟩,
    mem_compactlySupported.2 <| HasCompactSupport.intro
      (((hasCompactSupport_iff_isCompact_support.1 (mem_compactlySupported.1 f₁.property)).prod
        (hasCompactSupport_iff_isCompact_support.1 (mem_compactlySupported.1 f₂.property))).image
          (f := fun q : G × G ↦ (q.1 * q.2, q.1)) (by fun_prop)) fun p hp ↦ by
      by_contra h
      refine hp ⟨(p.2, p.2⁻¹ * p.1), ⟨left_ne_zero_of_mul h, right_ne_zero_of_mul h⟩, ?_⟩
      simp⟩

omit [T2Space G] in
/-- The convolution kernel of `f₁` and `f₂` takes the value `f₁(y) f₂(y⁻¹x)` at `(x, y)`. -/
@[simp]
theorem convolutionKernel_apply (f₁ f₂ : compactlySupported A G A) (p : G × G) :
    (convolutionKernel f₁ f₂ : LocallyConstant (G × G) A) p =
      (f₁ : LocallyConstant G A) p.2 * (f₂ : LocallyConstant G A) (p.2⁻¹ * p.1) :=
  (rfl)

variable (μ : HaarMeasureWithValues A G)

/-- **Convolution** of locally constant functions with compact support against an `A`-valued Haar
measure: `(f₁ ⋆ f₂)(x) = ∫ f₁(y) f₂(y⁻¹x) dμ(y)`
(`TauCeti.HaarMeasureWithValues.convolution_apply`), an `A`-bilinear map
`C_c^∞(G, A) → C_c^∞(G, A) → C_c^∞(G, A)`. -/
noncomputable def convolution :
    compactlySupported A G A →ₗ[A] compactlySupported A G A →ₗ[A] compactlySupported A G A :=
  LinearMap.mk₂ A (fun f₁ f₂ ↦ integralRight A μ (convolutionKernel f₁ f₂))
    (fun f₁ f₁' f₂ ↦ by
      rw [← map_add]
      congr 1
      ext p
      simp [add_mul])
    (fun c f₁ f₂ ↦ by
      rw [← map_smul]
      congr 1
      ext p
      simp [mul_assoc])
    (fun f₁ f₂ f₂' ↦ by
      rw [← map_add]
      congr 1
      ext p
      simp [mul_add])
    (fun c f₁ f₂ ↦ by
      rw [← map_smul]
      congr 1
      ext p
      simp [mul_left_comm])

/-- Convolution is the integral in the second variable of the convolution kernel. -/
theorem convolution_eq_integralRight (f₁ f₂ : compactlySupported A G A) :
    μ.convolution f₁ f₂ = integralRight A μ (convolutionKernel f₁ f₂) :=
  (rfl)

/-- The value of a convolution: `(f₁ ⋆ f₂)(x) = ∫ f₁(y) f₂(y⁻¹x) dμ(y)`, the integral of the slice
`y ↦ f₁(y) f₂(y⁻¹x)` of the convolution kernel. -/
theorem convolution_apply (f₁ f₂ : compactlySupported A G A) (x : G) :
    (μ.convolution f₁ f₂ : LocallyConstant G A) x =
      μ.integral (compactlySupported.sliceRight A A x (convolutionKernel f₁ f₂)) := by
  rw [convolution_eq_integralRight, integralRight_apply]

/-- Convolution against the zero Haar measure vanishes. -/
@[simp]
theorem convolution_zero_measure (f₁ f₂ : compactlySupported A G A) :
    (0 : HaarMeasureWithValues A G).convolution f₁ f₂ = 0 := by
  ext x
  simp [convolution_apply]

/-- **Convolution against a rescaled measure**: `f₁ ⋆_{cμ} f₂ = c (f₁ ⋆_μ f₂)`. -/
@[simp]
theorem convolution_smul_measure (c : A) (f₁ f₂ : compactlySupported A G A) :
    (c • μ).convolution f₁ f₂ = c • μ.convolution f₁ f₂ := by
  ext x
  simp [convolution_apply]

/-- **Support of a convolution**: `supp (f₁ ⋆ f₂) ⊆ supp f₁ · supp f₂`. -/
theorem support_convolution_subset (f₁ f₂ : compactlySupported A G A) :
    support (μ.convolution f₁ f₂ : LocallyConstant G A) ⊆
      support (f₁ : LocallyConstant G A) * support (f₂ : LocallyConstant G A) := by
  intro x hx
  rw [mem_support, convolution_apply] at hx
  -- A nonzero integral has a nonzero integrand.
  obtain ⟨y, hy⟩ :
      ∃ y, (f₁ : LocallyConstant G A) y * (f₂ : LocallyConstant G A) (y⁻¹ * x) ≠ 0 := by
    by_contra! h
    have h0 : compactlySupported.sliceRight A A x (convolutionKernel f₁ f₂) = 0 :=
      compactlySupported.ext fun y ↦ by simpa using h y
    exact hx (by rw [h0, map_zero])
  exact ⟨y, left_ne_zero_of_mul hy, y⁻¹ * x, right_ne_zero_of_mul hy, mul_inv_cancel_left y x⟩

/-- **Convolution commutes with left translation of the first factor**:
`(g · f₁) ⋆ f₂ = g · (f₁ ⋆ f₂)`, where `(g · f)(x) = f(g⁻¹x)`. -/
theorem convolution_compactlySupportedRep_left (g : G) (f₁ f₂ : compactlySupported A G A) :
    μ.convolution (compactlySupportedRep A G G A g f₁) f₂ =
      compactlySupportedRep A G G A g (μ.convolution f₁ f₂) := by
  ext x
  rw [convolution_apply, compactlySupportedRep_apply_coe, smul_eq_mul, convolution_apply,
    ← integral_compactlySupportedRep μ g (compactlySupported.sliceRight A A (g⁻¹ * x) _)]
  -- Substitute `y ↦ g⁻¹y` in the integral defining `(f₁ ⋆ f₂)(g⁻¹x)`.
  congr 1
  ext y
  simp [mul_assoc]

/-- **Convolution commutes with right translation of the second factor**:
`f₁ ⋆ (g · f₂) = g · (f₁ ⋆ f₂)` for `g : Gᵐᵒᵖ` acting by right translation,
`(g · f)(x) = f(x · (unop g)⁻¹)`. -/
theorem convolution_compactlySupportedRep_right (g : Gᵐᵒᵖ) (f₁ f₂ : compactlySupported A G A) :
    μ.convolution f₁ (compactlySupportedRep A Gᵐᵒᵖ G A g f₂) =
      compactlySupportedRep A Gᵐᵒᵖ G A g (μ.convolution f₁ f₂) := by
  ext x
  rw [convolution_apply, compactlySupportedRep_apply_coe, convolution_apply]
  congr 1
  ext y
  simp [mul_assoc]

/-- The integrand `(y, z) ↦ f₁(z) f₂(z⁻¹y) f₃(y⁻¹x)` comparing the two bracketings of a triple
convolution at `x`. -/
private noncomputable def assocKernel (f₁ f₂ f₃ : compactlySupported A G A) (x : G) :
    compactlySupported A (G × G) A :=
  ⟨(convolutionKernel f₁ f₂ : LocallyConstant (G × G) A) *
      (f₃ : LocallyConstant G A).comap ⟨fun p : G × G ↦ p.1⁻¹ * x, by fun_prop⟩,
    mem_compactlySupported.2 <| by
      rw [LocallyConstant.coe_mul]
      exact (mem_compactlySupported.1 (convolutionKernel f₁ f₂).property).mul_right⟩

omit [T2Space G] in
private theorem assocKernel_apply (f₁ f₂ f₃ : compactlySupported A G A) (x : G) (p : G × G) :
    (assocKernel f₁ f₂ f₃ x : LocallyConstant (G × G) A) p =
      (f₁ : LocallyConstant G A) p.2 * (f₂ : LocallyConstant G A) (p.2⁻¹ * p.1) *
        (f₃ : LocallyConstant G A) (p.1⁻¹ * x) :=
  (rfl)

/-- Integrating the triple integrand in its second variable gives the slice at `x` of the kernel
of `(f₁ ⋆ f₂) ⋆ f₃`. -/
private theorem integralRight_assocKernel (f₁ f₂ f₃ : compactlySupported A G A) (x : G) :
    integralRight A μ (assocKernel f₁ f₂ f₃ x) =
      compactlySupported.sliceRight A A x (convolutionKernel (μ.convolution f₁ f₂) f₃) := by
  ext y
  rw [integralRight_apply, compactlySupported.sliceRight_apply, convolutionKernel_apply,
    convolution_apply, mul_comm, ← smul_eq_mul, ← map_smul]
  congr 1
  ext z
  simp [assocKernel_apply, mul_comm]

/-- Integrating the triple integrand in its first variable gives the slice at `x` of the kernel
of `f₁ ⋆ (f₂ ⋆ f₃)`; this uses left invariance of `μ`. -/
private theorem integralLeft_assocKernel (f₁ f₂ f₃ : compactlySupported A G A) (x : G) :
    integralLeft A μ (assocKernel f₁ f₂ f₃ x) =
      compactlySupported.sliceRight A A x (convolutionKernel f₁ (μ.convolution f₂ f₃)) := by
  ext z
  rw [integralLeft_apply, compactlySupported.sliceRight_apply, convolutionKernel_apply,
    convolution_apply,
    ← integral_compactlySupportedRep μ z (compactlySupported.sliceRight A A (z⁻¹ * x) _),
    ← smul_eq_mul, ← map_smul]
  -- Substitute `w ↦ z⁻¹y` in the inner integral defining `(f₂ ⋆ f₃)(z⁻¹x)`.
  congr 1
  ext y
  simp [assocKernel_apply, mul_assoc]

/-- **Convolution is associative**: `(f₁ ⋆ f₂) ⋆ f₃ = f₁ ⋆ (f₂ ⋆ f₃)`. -/
theorem convolution_assoc (f₁ f₂ f₃ : compactlySupported A G A) :
    μ.convolution (μ.convolution f₁ f₂) f₃ = μ.convolution f₁ (μ.convolution f₂ f₃) := by
  ext x
  rw [convolution_apply, convolution_apply, ← integralRight_assocKernel,
    ← integralLeft_assocKernel, integral_integralRight, integral_integralLeft]

/-- For a compact open subgroup `U`, `1_U ⋆ 1_U = μ(U) • 1_U`. -/
theorem convolution_compactOpenIndicator_self (U : OpenSubgroup G) (hU : IsCompact (U : Set G)) :
    μ.convolution ⟨compactOpenIndicator (U.toCompactOpens hU) 1,
        compactOpenIndicator_mem_compactlySupported _ 1⟩
      ⟨compactOpenIndicator (U.toCompactOpens hU) 1,
        compactOpenIndicator_mem_compactlySupported _ 1⟩ =
      μ (U.toCompactOpens hU) • ⟨compactOpenIndicator (U.toCompactOpens hU) 1,
        compactOpenIndicator_mem_compactlySupported _ 1⟩ := by
  classical
  ext x
  rw [convolution_apply, Submodule.coe_smul, LocallyConstant.coe_smul, Pi.smul_apply]
  by_cases hx : x ∈ U
  · -- For `x ∈ U`, the integrand `y ↦ 1_U(y) 1_U(y⁻¹x)` is `1_U`.
    rw [compactOpenIndicator_of_mem (OpenSubgroup.mem_toCompactOpens.2 hx),
      ← integral_compactOpenIndicator]
    congr 1
    ext y
    by_cases hy : y ∈ U
    · have : y⁻¹ * x ∈ U := U.mul_mem (U.inv_mem hy) hx
      simp [OpenSubgroup.mem_toCompactOpens, hy, this]
    · simp [OpenSubgroup.mem_toCompactOpens, hy]
  · -- For `x ∉ U`, the integrand vanishes: `y ∈ U` and `y⁻¹x ∈ U` would put `x` in `U`.
    have h0 : compactlySupported.sliceRight A A x (convolutionKernel
        ⟨compactOpenIndicator (U.toCompactOpens hU) 1,
          compactOpenIndicator_mem_compactlySupported _ 1⟩
        ⟨compactOpenIndicator (U.toCompactOpens hU) 1,
          compactOpenIndicator_mem_compactlySupported _ 1⟩) = 0 := by
      ext y
      by_cases hy : y ∈ U
      · have : y⁻¹ * x ∉ U := fun h ↦ hx (by simpa using U.mul_mem hy h)
        simp [OpenSubgroup.mem_toCompactOpens, this]
      · simp [OpenSubgroup.mem_toCompactOpens, hy]
    rw [h0, map_zero, compactOpenIndicator_of_notMem (mt OpenSubgroup.mem_toCompactOpens.1 hx),
      smul_zero]

/-- **Finite discrete groups.** On a finite discrete group, convolution is the group-algebra
product scaled by the volume of a point: `(f₁ ⋆ f₂)(x) = μ({1}) • ∑_y f₁(y) f₂(y⁻¹x)`. -/
theorem convolution_apply_of_discrete [DiscreteTopology G] [Fintype G]
    (f₁ f₂ : compactlySupported A G A) (x : G) :
    (μ.convolution f₁ f₂ : LocallyConstant G A) x =
      μ ⟨⟨{1}, isCompact_singleton⟩, isOpen_discrete _⟩ •
        ∑ y, (f₁ : LocallyConstant G A) y * (f₂ : LocallyConstant G A) (y⁻¹ * x) := by
  simp [convolution_apply, integral_eq_smul_sum_of_discrete]

end Convolution

end HaarMeasureWithValues

/-! ### The Hecke algebra -/

variable {A G : Type*} [CommSemiring A] [Group G] [TopologicalSpace G]
  [ContinuousConstSMul G G]

/-- The **Hecke algebra** of `G` with respect to an `A`-valued Haar measure `μ`: the locally
constant functions `G → A` with compact support, with convolution against `μ` as multiplication
(`TauCeti.HeckeAlgebra.toCompactlySupported_mul`). When `G` is a Hausdorff topological group it
is a non-unital semiring and an `A`-module with `IsScalarTower` and `SMulCommClass`, that is, a
non-unital `A`-algebra, and a non-unital ring when `A` is a ring. Its underlying `A`-module is
`C_c^∞(G, A)`, through `TauCeti.HeckeAlgebra.linearEquiv`. -/
@[ext]
structure HeckeAlgebra (μ : HaarMeasureWithValues A G) where
  /-- A locally constant function with compact support, as an element of the Hecke algebra. -/
  ofCompactlySupported ::
  /-- The underlying locally constant function with compact support. -/
  toCompactlySupported : LocallyConstant.compactlySupported A G A

namespace HeckeAlgebra

variable (μ : HaarMeasureWithValues A G)

/-- An element of the Hecke algebra is determined by its underlying function. -/
theorem toCompactlySupported_injective :
    Injective (toCompactlySupported : HeckeAlgebra μ → LocallyConstant.compactlySupported A G A) :=
  fun _ _ ↦ HeckeAlgebra.ext

instance : Zero (HeckeAlgebra μ) := ⟨⟨0⟩⟩
instance : Add (HeckeAlgebra μ) :=
  ⟨fun f₁ f₂ ↦ ⟨f₁.toCompactlySupported + f₂.toCompactlySupported⟩⟩
instance : SMul ℕ (HeckeAlgebra μ) := ⟨fun n f ↦ ⟨n • f.toCompactlySupported⟩⟩
instance : SMul A (HeckeAlgebra μ) := ⟨fun c f ↦ ⟨c • f.toCompactlySupported⟩⟩

@[simp]
theorem toCompactlySupported_zero : (0 : HeckeAlgebra μ).toCompactlySupported = 0 :=
  (rfl)

@[simp]
theorem toCompactlySupported_add (f₁ f₂ : HeckeAlgebra μ) :
    (f₁ + f₂).toCompactlySupported = f₁.toCompactlySupported + f₂.toCompactlySupported :=
  (rfl)

@[simp]
theorem toCompactlySupported_smul (c : A) (f : HeckeAlgebra μ) :
    (c • f).toCompactlySupported = c • f.toCompactlySupported :=
  (rfl)

@[simp]
theorem toCompactlySupported_nsmul (n : ℕ) (f : HeckeAlgebra μ) :
    (n • f).toCompactlySupported = n • f.toCompactlySupported :=
  (rfl)

instance : AddCommMonoid (HeckeAlgebra μ) :=
  (toCompactlySupported_injective μ).addCommMonoid _ rfl (fun _ _ ↦ rfl) fun _ _ ↦ rfl

instance : Module A (HeckeAlgebra μ) :=
  (toCompactlySupported_injective μ).module A
    ⟨⟨toCompactlySupported, rfl⟩, fun _ _ ↦ rfl⟩ fun _ _ ↦ rfl

/-- The identification of the Hecke algebra with `C_c^∞(G, A)` as an `A`-module. -/
def linearEquiv : HeckeAlgebra μ ≃ₗ[A] LocallyConstant.compactlySupported A G A where
  toFun := toCompactlySupported
  invFun := ofCompactlySupported
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

@[simp]
theorem linearEquiv_apply (f : HeckeAlgebra μ) : linearEquiv μ f = f.toCompactlySupported :=
  (rfl)

@[simp]
theorem linearEquiv_symm_apply (f : LocallyConstant.compactlySupported A G A) :
    (linearEquiv μ).symm f = ofCompactlySupported f :=
  (rfl)

variable [IsTopologicalGroup G] [T2Space G]

/-- Multiplication in the Hecke algebra is convolution against `μ`. -/
noncomputable instance : Mul (HeckeAlgebra μ) where
  mul f₁ f₂ := ⟨μ.convolution f₁.toCompactlySupported f₂.toCompactlySupported⟩

/-- Multiplication in the Hecke algebra is convolution against `μ`. -/
@[simp]
theorem toCompactlySupported_mul (f₁ f₂ : HeckeAlgebra μ) :
    (f₁ * f₂).toCompactlySupported =
      μ.convolution f₁.toCompactlySupported f₂.toCompactlySupported :=
  (rfl)

noncomputable instance : NonUnitalSemiring (HeckeAlgebra μ) where
  left_distrib f₁ f₂ f₃ := HeckeAlgebra.ext <| by simp
  right_distrib f₁ f₂ f₃ := HeckeAlgebra.ext <| by simp
  zero_mul f := HeckeAlgebra.ext <| by simp
  mul_zero f := HeckeAlgebra.ext <| by simp
  mul_assoc f₁ f₂ f₃ := HeckeAlgebra.ext <| by
    simp [HaarMeasureWithValues.convolution_assoc]

instance : IsScalarTower A (HeckeAlgebra μ) (HeckeAlgebra μ) where
  smul_assoc c f₁ f₂ := HeckeAlgebra.ext <| by simp

instance : SMulCommClass A (HeckeAlgebra μ) (HeckeAlgebra μ) where
  smul_comm c f₁ f₂ := HeckeAlgebra.ext <| by simp

end HeckeAlgebra

namespace HeckeAlgebra

variable {A G : Type*} [CommRing A] [Group G] [TopologicalSpace G] [ContinuousConstSMul G G]
  (μ : HaarMeasureWithValues A G)

instance : Neg (HeckeAlgebra μ) := ⟨fun f ↦ ⟨-f.toCompactlySupported⟩⟩
instance : Sub (HeckeAlgebra μ) :=
  ⟨fun f₁ f₂ ↦ ⟨f₁.toCompactlySupported - f₂.toCompactlySupported⟩⟩
instance : SMul ℤ (HeckeAlgebra μ) := ⟨fun n f ↦ ⟨n • f.toCompactlySupported⟩⟩

@[simp]
theorem toCompactlySupported_neg (f : HeckeAlgebra μ) :
    (-f).toCompactlySupported = -f.toCompactlySupported :=
  (rfl)

@[simp]
theorem toCompactlySupported_sub (f₁ f₂ : HeckeAlgebra μ) :
    (f₁ - f₂).toCompactlySupported = f₁.toCompactlySupported - f₂.toCompactlySupported :=
  (rfl)

@[simp]
theorem toCompactlySupported_zsmul (n : ℤ) (f : HeckeAlgebra μ) :
    (n • f).toCompactlySupported = n • f.toCompactlySupported :=
  (rfl)

instance : AddCommGroup (HeckeAlgebra μ) :=
  (toCompactlySupported_injective μ).addCommGroup _ rfl (fun _ _ ↦ rfl) (fun _ ↦ rfl)
    (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) fun _ _ ↦ rfl

noncomputable instance [IsTopologicalGroup G] [T2Space G] : NonUnitalRing (HeckeAlgebra μ) where
  __ := (inferInstance : NonUnitalSemiring (HeckeAlgebra μ))
  __ := (inferInstance : AddCommGroup (HeckeAlgebra μ))

end HeckeAlgebra

end TauCeti
