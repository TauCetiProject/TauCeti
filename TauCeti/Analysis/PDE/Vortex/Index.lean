/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.Fredholm
public import TauCeti.Analysis.PDE.Vortex.WeakKernel
import TauCeti.Analysis.Fredholm.Criteria
import TauCeti.MeasureTheory.Measure.Restrict

/-!
# The gauge-fixed vortex operator on `H¹` has index `2m`

At a field `x` with `L∞` class `a`, the gauge-fixed vortex operator `L_x = d₀* ⊕ d₁` is realized
as a bounded operator `TauCeti.Vortex.sobolevGaugeFixedOperator a : H¹(ℂ)⁴ → L²(ℂ; ℝ⁴)`. At a
plane vortex it is onto (`TauCeti.Vortex.sobolevGaugeFixedOperator_surjective`), so its index is
the real dimension of its kernel. This file computes that dimension: it is `2m` at a plane vortex
of degree `m`, the real dimension of the divisor space `Sym^m ℂ`.

The kernel of the realization is identified with the weak `L²` kernel of `L_x`
(`TauCeti.Vortex.weakGaugeFixedKernel`), the square-integrable weak solutions of `L_x u = 0`. At a
continuous field the map sending `y ∈ H¹(ℂ)⁴` to the `L²` class of its values is a real-linear
isomorphism between the two (`TauCeti.Vortex.kerSobolevGaugeFixedOperatorEquiv`).

* It is well defined because an element of `H¹(ℂ)⁴` lies in the kernel of the realization exactly
  when its values solve `L_x y = 0` weakly
  (`TauCeti.Vortex.mem_ker_sobolevGaugeFixedOperator_iff`).
* It is injective because an element of `H¹(ℂ)` is determined by its value
  (`TauCeti.W1p.value_injective`).
* It is onto because, at a bounded continuous field, every weak `L²` solution of `L_x u = 0` is
  the value of an element of `H¹(ℂ)⁴`
  (`TauCeti.Vortex.exists_sobolevGaugeFixedOperator_eq_of_integral_inner_gaugeFixedAdjoint_eq`).

Let now `x` be a continuous plane vortex lying in the affine field space `A_m^k` for every `k`.
Every smooth framed vortex of degree `m` has such a representative in its framed gauge orbit
(`TauCeti.Vortex.exists_framedGaugeGroup_smul_mem_framedFieldSpace`). Its weak kernel
has real dimension `2m` (`TauCeti.Vortex.finrank_weakGaugeFixedKernel_eq_two_mul`), so:

* `TauCeti.Vortex.finrank_ker_sobolevGaugeFixedOperator_eq_two_mul`: the kernel of the
  realization has real dimension `2m`;
* `TauCeti.Vortex.isFredholm_sobolevGaugeFixedOperator_of_forall_mem_framedFieldSpace`: the
  realization is Fredholm;
* `TauCeti.Vortex.index_sobolevGaugeFixedOperator_eq_two_mul`: its index is `2m`.

## References

* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III.
* T. M. Samols, *Vortex scattering*, Comm. Math. Phys. 145 (1992), 149–179.
-/

public section

noncomputable section

namespace TauCeti.Vortex

open MeasureTheory Filter TopologicalSpace Module
open scoped ENNReal

local notation "μ⊤" => Measure.restrict (volume : Measure ℂ) ((⊤ : Opens ℂ) : Set ℂ)

variable {x : ℂ → EuclideanSpace ℝ (Fin 4)} {a : Lp (EuclideanSpace ℝ (Fin 4)) ∞ μ⊤}

/-- The values of the four coordinates of `y ∈ H¹(ℂ)⁴` form a square-integrable field. -/
private theorem memLp_values (y : Fin 4 → W1p (volume : Measure ℂ) ⊤ 2) :
    MemLp (fun z ↦ (WithLp.toLp 2 fun j ↦ W1p.value (y j) z : EuclideanSpace ℝ (Fin 4)))
      2 volume :=
  memLp_piLp_iff.2 fun j ↦ W1p.memLp_value (y j)

/-- The `L²` class of the values of the four coordinates of `y ∈ H¹(ℂ)⁴`. -/
private def valuesLp :
    (Fin 4 → W1p (volume : Measure ℂ) ⊤ 2) →ₗ[ℝ]
      Lp (EuclideanSpace ℝ (Fin 4)) 2 (volume : Measure ℂ) where
  toFun y := (memLp_values y).toLp _
  map_add' y y' := by
    refine Lp.ext ?_
    have hadd : ∀ᵐ z ∂(volume : Measure ℂ), ∀ j : Fin 4,
        W1p.value (y j + y' j) z = W1p.value (y j) z + W1p.value (y' j) z := by
      refine ae_all_iff.2 fun j ↦ ?_
      filter_upwards [(W1p.value_add_ae (y j) (y' j)).filter_mono
        (ae_mono (Measure.restrict_coe_opens_top _).ge)] with z hz
      exact hz
    filter_upwards [(memLp_values (y + y')).coeFn_toLp, (memLp_values y).coeFn_toLp,
      (memLp_values y').coeFn_toLp, Lp.coeFn_add ((memLp_values y).toLp _)
        ((memLp_values y').toLp _), hadd] with z h h₁ h₂ h₃ h₄
    rw [h, h₃, Pi.add_apply, h₁, h₂]
    ext j
    simp [h₄ j]
  map_smul' c y := by
    refine Lp.ext ?_
    have hsmul : ∀ᵐ z ∂(volume : Measure ℂ), ∀ j : Fin 4,
        W1p.value (c • y j) z = c * W1p.value (y j) z := by
      refine ae_all_iff.2 fun j ↦ ?_
      filter_upwards [(W1p.value_smul_ae c (y j)).filter_mono
        (ae_mono (Measure.restrict_coe_opens_top _).ge)] with z hz
      exact hz
    filter_upwards [(memLp_values (c • y)).coeFn_toLp, (memLp_values y).coeFn_toLp,
      Lp.coeFn_smul c ((memLp_values y).toLp _), hsmul] with z h h₁ h₂ h₃
    rw [h, RingHom.id_apply, h₂, Pi.smul_apply, h₁]
    ext j
    simp [h₃ j]

private theorem coeFn_valuesLp (y : Fin 4 → W1p (volume : Measure ℂ) ⊤ 2) :
    valuesLp y =ᵐ[volume] fun z ↦
      (WithLp.toLp 2 fun j ↦ W1p.value (y j) z : EuclideanSpace ℝ (Fin 4)) :=
  (memLp_values y).coeFn_toLp

private theorem valuesLp_injective : Function.Injective valuesLp := by
  intro y y' h
  funext j
  have hy := coeFn_valuesLp y
  rw [h] at hy
  refine W1p.value_injective (Lp.ext ?_)
  filter_upwards [ae_restrict_of_ae hy, ae_restrict_of_ae (coeFn_valuesLp y')] with z h₁ h₂
  simpa using congrArg (fun v : EuclideanSpace ℝ (Fin 4) ↦ v j) (h₁.symm.trans h₂)

/-- The values of an element of the kernel of the realization lie in the weak kernel. -/
private theorem valuesLp_mem_weakGaugeFixedKernel (hx : Continuous x) (hax : a =ᵐ[μ⊤] x)
    (y : (sobolevGaugeFixedOperator a).ker) : valuesLp y.1 ∈ weakGaugeFixedKernel x := by
  refine (mem_weakGaugeFixedKernel_iff hx).2 fun η hη hηc ↦ ?_
  rw [← (mem_ker_sobolevGaugeFixedOperator_iff hx hax).1 y.2 η hη hηc]
  exact integral_congr_ae ((coeFn_valuesLp y.1).mono fun z hz ↦ by simp only [hz])

/-- Every element of the weak kernel is the class of the values of an element of the kernel of
the realization. -/
private theorem exists_valuesLp_eq (hx : Continuous x) (hax : a =ᵐ[μ⊤] x)
    (u : weakGaugeFixedKernel x) :
    ∃ y : (sobolevGaugeFixedOperator a).ker, valuesLp y.1 = u := by
  obtain ⟨w, hw, hLw⟩ := exists_sobolevGaugeFixedOperator_eq_of_integral_inner_gaugeFixedAdjoint_eq
    hx hax (Lp.memLp (u : Lp (EuclideanSpace ℝ (Fin 4)) 2 volume)) (f := 0)
    fun η hη hηc ↦ by simp [(mem_weakGaugeFixedKernel_iff hx).1 u.2 η hη hηc]
  refine ⟨⟨w, hLw⟩, Lp.ext ?_⟩
  filter_upwards [coeFn_valuesLp w, ae_all_iff.2 hw] with z h₁ h₂
  rw [h₁]
  ext j
  simp [h₂ j]

/-- **The kernel of the `H¹` realization is the weak `L²` kernel.** At a continuous field `x`
with `L∞` class `a`, sending `y ∈ H¹(ℂ)⁴` to the `L²` class of its values is a real-linear
isomorphism from the kernel of `L_x : H¹(ℂ)⁴ → L²(ℂ; ℝ⁴)` onto the weak `L²` kernel of `L_x`
(`coeFn_kerSobolevGaugeFixedOperatorEquiv`). -/
def kerSobolevGaugeFixedOperatorEquiv (hx : Continuous x) (hax : a =ᵐ[μ⊤] x) :
    (sobolevGaugeFixedOperator a).ker ≃ₗ[ℝ] weakGaugeFixedKernel x :=
  LinearEquiv.ofBijective
    ((valuesLp.domRestrict _).codRestrict _ (valuesLp_mem_weakGaugeFixedKernel hx hax))
    ⟨fun _ _ h ↦ Subtype.ext (valuesLp_injective (congrArg Subtype.val h)),
      fun u ↦ (exists_valuesLp_eq hx hax u).imp fun _ h ↦ Subtype.ext h⟩

/-- The isomorphism `kerSobolevGaugeFixedOperatorEquiv` sends `y` to the class of its values. -/
theorem coeFn_kerSobolevGaugeFixedOperatorEquiv (hx : Continuous x) (hax : a =ᵐ[μ⊤] x)
    (y : (sobolevGaugeFixedOperator a).ker) :
    (kerSobolevGaugeFixedOperatorEquiv hx hax y : Lp (EuclideanSpace ℝ (Fin 4)) 2 volume)
      =ᵐ[volume] fun z ↦
        (WithLp.toLp 2 fun j ↦ W1p.value (y.1 j) z : EuclideanSpace ℝ (Fin 4)) :=
  coeFn_valuesLp y.1

/-- At a continuous field, the kernel of the `H¹` realization has the dimension of the weak `L²`
kernel. -/
theorem finrank_ker_sobolevGaugeFixedOperator (hx : Continuous x) (hax : a =ᵐ[μ⊤] x) :
    finrank ℝ (sobolevGaugeFixedOperator a).ker = finrank ℝ (weakGaugeFixedKernel x) :=
  (kerSobolevGaugeFixedOperatorEquiv hx hax).finrank_eq

/-! ### The index at a plane vortex -/

variable {f : ContDiffBump (0 : ℝ)} {m : ℕ}

/-- **The kernel of the `H¹` realization at a plane vortex is finite-dimensional.** Let `x` be a
continuous field lying in `A_m^k` for every `k` whose section satisfies the holomorphicity rows
`∂bar_a α = 0`, for instance a continuous plane vortex lying in every `A_m^k`, and let `a` be its
`L∞` class. Then the kernel of `L_x : H¹(ℂ)⁴ → L²(ℂ; ℝ⁴)` is finite-dimensional. -/
theorem finiteDimensional_ker_sobolevGaugeFixedOperator_of_forall_mem_framedFieldSpace
    (hx : Continuous x) (hmem : ∀ k : ℕ, x ∈ framedFieldSpace f m k)
    (hhol : ∀ w, equation x w 1 = 0 ∧ equation x w 2 = 0) (hax : a =ᵐ[μ⊤] x) :
    FiniteDimensional ℝ (sobolevGaugeFixedOperator a).ker :=
  have := finiteDimensional_weakGaugeFixedKernel hx hmem hhol
  (kerSobolevGaugeFixedOperatorEquiv hx hax).symm.finiteDimensional

/-- **The kernel of the `H¹` realization at a plane vortex has dimension `2m`** (Taubes). Let `x`
be a continuous field lying in `A_m^k` for every `k` whose section satisfies the holomorphicity
rows `∂bar_a α = 0`, for instance a continuous plane vortex lying in every `A_m^k`, and let `a` be
its `L∞` class. Then the kernel of `L_x : H¹(ℂ)⁴ → L²(ℂ; ℝ⁴)` has real dimension `2m`, the
dimension of the divisor space `Sym^m ℂ`. -/
theorem finrank_ker_sobolevGaugeFixedOperator_eq_two_mul (hx : Continuous x)
    (hmem : ∀ k : ℕ, x ∈ framedFieldSpace f m k)
    (hhol : ∀ w, equation x w 1 = 0 ∧ equation x w 2 = 0) (hax : a =ᵐ[μ⊤] x) :
    finrank ℝ (sobolevGaugeFixedOperator a).ker = 2 * m := by
  rw [finrank_ker_sobolevGaugeFixedOperator hx hax,
    finrank_weakGaugeFixedKernel_eq_two_mul hx hmem hhol]

/-- The realization of `L_x` on `H¹` is onto at a continuous plane vortex lying in every
`A_m^k`. -/
private theorem sobolevGaugeFixedOperator_surjective_of_forall_mem_framedFieldSpace
    (hx : Continuous x) (hmem : ∀ k : ℕ, x ∈ framedFieldSpace f m k)
    (hsol : ∀ z, equation x z = 0) (hax : a =ᵐ[μ⊤] x) :
    Function.Surjective (sobolevGaugeFixedOperator a) :=
  sobolevGaugeFixedOperator_surjective
    ((contDiff_of_forall_mem_framedFieldSpace hx hmem).of_le (by simp)) hsol
    (tendsto_normSq_of_mem_framedFieldSpace one_lt_two (by exact_mod_cast hmem 2) hx) hax

/-- **The realization of `L_x` on `H¹` is Fredholm at a plane vortex** lying in every `A_m^k`,
with `L∞` class `a`. -/
theorem isFredholm_sobolevGaugeFixedOperator_of_forall_mem_framedFieldSpace (hx : Continuous x)
    (hmem : ∀ k : ℕ, x ∈ framedFieldSpace f m k) (hsol : ∀ z, equation x z = 0)
    (hax : a =ᵐ[μ⊤] x) :
    (sobolevGaugeFixedOperator a).IsFredholm := by
  have := finiteDimensional_ker_sobolevGaugeFixedOperator_of_forall_mem_framedFieldSpace hx hmem
    (fun w ↦ by simp [hsol w]) hax
  exact .of_surjective
    (sobolevGaugeFixedOperator_surjective_of_forall_mem_framedFieldSpace hx hmem hsol hax)

/-- **The realization of `L_x` on `H¹` has index `2m` at a plane vortex** (Taubes). Let `x` be a
continuous plane vortex lying in the affine field space `A_m^k` for every `k`, for instance the
representative of a smooth framed degree-`m` vortex given by
`exists_framedGaugeGroup_smul_mem_framedFieldSpace`, and let `a` be its `L∞` class. Then
`L_x : H¹(ℂ)⁴ → L²(ℂ; ℝ⁴)` is onto with kernel of real dimension `2m`, so its index is `2m`, the
real dimension of the divisor space `Sym^m ℂ`. -/
theorem index_sobolevGaugeFixedOperator_eq_two_mul (hx : Continuous x)
    (hmem : ∀ k : ℕ, x ∈ framedFieldSpace f m k) (hsol : ∀ z, equation x z = 0)
    (hax : a =ᵐ[μ⊤] x) :
    (sobolevGaugeFixedOperator a).index = 2 * m := by
  rw [LinearMap.index_of_surjective
      (sobolevGaugeFixedOperator_surjective_of_forall_mem_framedFieldSpace hx hmem hsol hax),
    finrank_ker_sobolevGaugeFixedOperator_eq_two_mul hx hmem (fun w ↦ by simp [hsol w]) hax]
  norm_cast

end TauCeti.Vortex
