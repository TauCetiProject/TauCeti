/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Mathlib.RingTheory.Regular.RegularSequence
public import Mathlib.RingTheory.Regular.Category
public import Mathlib.RingTheory.LocalRing.Module
public import TauCeti.LinearAlgebra.TensorProduct.Prod

/-!
# Weakly regular pairs and the two-term Koszul relation

For a pair `x, y` weakly regular on a module, every relation `x • a + y • b = 0` is a
Koszul relation. Tensoring this calculation proves that a finitely presented
module over a local ring is free when a weakly regular pair generates the maximal
ideal and is also weakly regular on the module.

## References

* [pcfawd-formalization](https://github.com/tdupu/pcfawd-formalization/blob/9a20b3f351446d64e6015d704198bc71c7002008/lean/Pcf/Stacks/Purity/MiracleFlatnessTwo.lean):
  `Pcf.Stacks.exists_koszul_relation_of_isSMulRegular_pair`,
  `Pcf.Stacks.exact_koszulPair_of_isSMulRegular`, and
  `Pcf.Stacks.Module.free_of_regular_pair_generates_maximalIdeal`.

-/

public section

open TensorProduct RingTheory.Sequence
open scoped Pointwise

universe u v

namespace TauCeti

variable {R : Type u} {M : Type v}

section Right

variable [CommSemiring R] [AddCommMonoid M] [Module R M]

/-- The second differential of the two-element Koszul complex. -/
def koszulPairRight (x y : R) : M × M →ₗ[R] M :=
  (LinearMap.lsmul R M x).coprod (LinearMap.lsmul R M y)

@[simp]
theorem koszulPairRight_apply (x y : R) (p : M × M) :
    koszulPairRight x y p = x • p.1 + y • p.2 := by
  simp only [koszulPairRight, LinearMap.coprod_apply, LinearMap.lsmul_apply]

/-- The range of the second Koszul differential is the two-generated ideal. -/
@[simp]
theorem range_koszulPairRight_eq_span (x y : R) :
    LinearMap.range (koszulPairRight (M := R) x y) =
      Ideal.span ({x, y} : Set R) := by
  ext z
  constructor
  · rintro ⟨⟨a, b⟩, rfl⟩
    rw [Ideal.mem_span_pair]
    refine ⟨a, b, ?_⟩
    simp only [koszulPairRight_apply, smul_eq_mul]
    ring
  · intro hz
    rw [Ideal.mem_span_pair] at hz
    obtain ⟨a, b, hab⟩ := hz
    refine ⟨(a, b), ?_⟩
    simp only [koszulPairRight_apply, smul_eq_mul]
    calc
      x * a + y * b = a * x + b * y := by ring
      _ = z := hab

end Right

section Left

variable [CommSemiring R] [AddCommGroup M] [Module R M]

/-- The first differential of the two-element Koszul complex, with sign convention
`c ↦ (-y • c, x • c)`. -/
def koszulPairLeft (x y : R) : M →ₗ[R] M × M :=
  (-(LinearMap.lsmul R M y)).prod (LinearMap.lsmul R M x)

@[simp]
theorem koszulPairLeft_apply (x y : R) (c : M) :
    koszulPairLeft x y c = (-(y • c), x • c) := by
  simp only [koszulPairLeft, LinearMap.prod_apply, LinearMap.neg_apply,
    LinearMap.lsmul_apply, Function.prod_apply]

/-- Consecutive differentials in the two-element Koszul complex compose to zero. -/
@[simp]
theorem koszulPairRight_comp_koszulPairLeft (x y : R) :
    (koszulPairRight (M := M) x y).comp (koszulPairLeft (M := M) x y) = 0 := by
  ext c
  simp only [LinearMap.comp_apply, koszulPairLeft_apply, koszulPairRight_apply,
    smul_neg, smul_smul, LinearMap.zero_apply]
  rw [mul_comm x y, neg_add_cancel]

end Left

section RegularPair

variable [CommRing R] [AddCommGroup M] [Module R M]

/-- The first Koszul differential commutes with tensoring by `M`. -/
private theorem prodScalarLeftEquiv_comp_koszulPairLeft_rTensor (x y : R) :
    (TauCeti.TensorProduct.prodScalarLeftEquiv (R := R) (M := M)).toLinearMap.comp
        ((koszulPairLeft (M := R) x y).rTensor M) =
      (koszulPairLeft (M := M) x y).comp (TensorProduct.lid R M).toLinearMap := by
  apply TensorProduct.ext'
  intro r m
  simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    LinearMap.rTensor_tmul, koszulPairLeft_apply, smul_eq_mul,
    TauCeti.TensorProduct.prodScalarLeftEquiv_tmul, neg_smul, TensorProduct.lid_tmul,
    map_smul, Prod.smul_mk, smul_neg, Prod.mk.injEq, neg_inj]
  constructor
  · rw [mul_smul, smul_comm y r m]
  · rw [mul_smul, smul_comm x r m]

/-- The second Koszul differential commutes with tensoring by `M`. -/
private theorem lid_comp_koszulPairRight_rTensor (x y : R) :
    (TensorProduct.lid R M).toLinearMap.comp
        ((koszulPairRight (M := R) x y).rTensor M) =
      (koszulPairRight (M := M) x y).comp
        (TauCeti.TensorProduct.prodScalarLeftEquiv (R := R) (M := M)).toLinearMap := by
  apply TensorProduct.ext'
  rintro ⟨a, b⟩ m
  simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    LinearMap.rTensor_tmul, koszulPairRight_apply, smul_eq_mul,
    TensorProduct.lid_tmul, TauCeti.TensorProduct.prodScalarLeftEquiv_tmul]
  rw [add_smul, mul_smul, mul_smul, smul_comm x a m, smul_comm y b m]

/-- Every relation on a pair weakly regular on `M` is a Koszul relation. -/
theorem exists_koszul_relation_of_isWeaklyRegular_pair
    {x y : R} {a b : M}
    (hreg : IsWeaklyRegular M [x, y])
    (h : x • a + y • b = 0) :
    ∃ c : M, a = -(y • c) ∧ b = x • c := by
  obtain ⟨hx, hweak⟩ := (isWeaklyRegular_cons_iff M x [y]).mp hreg
  have hy := (isWeaklyRegular_singleton_iff (QuotSMulTop x M) y).mp hweak
  let q : M →ₗ[R] QuotSMulTop x M := (x • (⊤ : Submodule R M)).mkQ
  have hxa : q (x • a) = 0 := by
    simp only [q, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact Submodule.smul_mem_pointwise_smul a x ⊤ trivial
  have hyb : y • q b = 0 := by
    have hq := DFunLike.congr_arg q h
    simpa only [map_add, map_smul, map_zero, hxa, zero_add] using hq
  have hqb : q b = 0 := by
    apply hy
    simpa only [smul_zero] using hyb
  have hb_range : b ∈ LinearMap.range (LinearMap.lsmul R M x) := by
    rw [← (LinearMap.exact_lsmul_mkQ_smul_top M x).linearMap_ker_eq]
    exact hqb
  obtain ⟨c, hc⟩ := hb_range
  have hc' : x • c = b := by simpa only [LinearMap.lsmul_apply] using hc
  refine ⟨c, ?_, ?_⟩
  · apply hx
    rw [← hc'] at h
    calc
      x • a = -(y • (x • c)) := eq_neg_of_add_eq_zero_left h
      _ = x • (-(y • c)) := by simp only [smul_neg, smul_smul, mul_comm x y]
  · exact hc'.symm

/-- The two-element Koszul complex is exact at the middle for a weakly regular pair. -/
theorem exact_koszulPair_of_isWeaklyRegular
    {x y : R}
    (hreg : IsWeaklyRegular M [x, y]) :
    Function.Exact (koszulPairLeft (M := M) x y) (koszulPairRight (M := M) x y) := by
  intro p
  constructor
  · intro hp
    obtain ⟨c, hc₁, hc₂⟩ :=
      exists_koszul_relation_of_isWeaklyRegular_pair hreg hp
    refine ⟨c, ?_⟩
    ext
    · exact hc₁.symm
    · exact hc₂.symm
  · rintro ⟨c, rfl⟩
    simpa only [LinearMap.comp_apply, LinearMap.zero_apply] using
      LinearMap.congr_fun (koszulPairRight_comp_koszulPairLeft (M := M) x y) c

/-- The first Koszul differential is injective for a weakly regular pair. -/
theorem koszulPairLeft_injective_of_isWeaklyRegular
    {x y : R} (hreg : IsWeaklyRegular M [x, y]) :
    Function.Injective (koszulPairLeft (M := M) x y) := by
  have hx := ((isWeaklyRegular_cons_iff M x [y]).mp hreg).1
  intro a b hab
  apply hx
  simpa only [koszulPairLeft_apply] using congrArg Prod.snd hab

/-- The second Koszul differential is exact with the quotient by its two-generated ideal. -/
theorem exact_koszulPairRight_quotient (x y : R) :
    Function.Exact (koszulPairRight (M := R) x y)
      (Submodule.mkQ (Ideal.span ({x, y} : Set R))) := by
  rw [LinearMap.exact_iff, Submodule.ker_mkQ, range_koszulPairRight_eq_span]

/-- Tensoring the two-element Koszul complex with `M` preserves exactness at
the middle when the pair is weakly regular on `M`. -/
theorem exact_rTensor_koszulPair_of_isWeaklyRegular
    {x y : R}
    (hreg : IsWeaklyRegular M [x, y]) :
    Function.Exact
      ((koszulPairLeft (M := R) x y).rTensor M)
      ((koszulPairRight (M := R) x y).rTensor M) := by
  let e₁ := TensorProduct.lid R M
  let e₂ := TauCeti.TensorProduct.prodScalarLeftEquiv (R := R) (M := M)
  have hcomm₁ := prodScalarLeftEquiv_comp_koszulPairLeft_rTensor (M := M) x y
  have hcomm₂ := lid_comp_koszulPairRight_rTensor (M := M) x y
  have hexact := exact_koszulPair_of_isWeaklyRegular hreg
  exact (Function.Exact.iff_of_ladder_linearEquiv
    (e₁ := e₁) (e₂ := e₂) (e₃ := e₁) hcomm₁.symm hcomm₂.symm).mp hexact

/-- A weakly regular pair on the ring and module keeps the inclusion of its ideal
injective after tensoring with the module. -/
theorem range_koszulPairRight_subtype_rTensor_injective_of_isWeaklyRegular
    {x y : R}
    (hregR : IsWeaklyRegular R [x, y])
    (hregM : IsWeaklyRegular M [x, y]) :
    Function.Injective
      ((LinearMap.range (koszulPairRight (M := R) x y)).subtype.rTensor M) := by
  let f := koszulPairLeft (M := R) x y
  let g₀ := koszulPairRight (M := R) x y
  let I := LinearMap.range g₀
  let g : R × R →ₗ[R] I := g₀.rangeRestrict
  let i : I →ₗ[R] R := I.subtype
  have hfactor : i.comp g = g₀ := LinearMap.subtype_comp_rangeRestrict g₀
  have hsurj : Function.Surjective g := g₀.surjective_rangeRestrict
  have hexactRing : Function.Exact f g := by
    rw [LinearMap.exact_iff, LinearMap.ker_rangeRestrict]
    exact LinearMap.exact_iff.mp (exact_koszulPair_of_isWeaklyRegular hregR)
  have hexactRange : Function.Exact (f.rTensor M) (g.rTensor M) :=
    _root_.rTensor_exact M hexactRing hsurj
  have hexactModule : Function.Exact (f.rTensor M) (g₀.rTensor M) :=
    exact_rTensor_koszulPair_of_isWeaklyRegular hregM
  apply LinearMap.ker_eq_bot.mp
  apply le_antisymm
  · intro z hz
    rw [Submodule.mem_bot]
    have hz' : (i.rTensor M) z = 0 := LinearMap.mem_ker.mp hz
    obtain ⟨w, hw⟩ := g.rTensor_surjective M hsurj z
    have hg₀w : (g₀.rTensor M) w = 0 := by
      calc
        (g₀.rTensor M) w = ((i.comp g).rTensor M) w := by rw [hfactor]
        _ = (i.rTensor M) ((g.rTensor M) w) :=
          LinearMap.rTensor_comp_apply M i g w
        _ = (i.rTensor M) z := by rw [hw]
        _ = 0 := hz'
    have hwRange : w ∈ LinearMap.range (f.rTensor M) := (hexactModule w).mp hg₀w
    have hgw : (g.rTensor M) w = 0 := (hexactRange w).mpr hwRange
    exact hw.symm.trans hgw
  · exact bot_le

/-- A finitely presented module over a local ring is free when a weakly regular pair
generates the maximal ideal and is also weakly regular on the module. -/
theorem Module.free_of_weaklyRegular_pair_generates_maximalIdeal
    [IsLocalRing R] [Module.FinitePresentation R M]
    {x y : R}
    (hspan : Ideal.span ({x, y} : Set R) = IsLocalRing.maximalIdeal R)
    (hregR : IsWeaklyRegular R [x, y])
    (hregM : IsWeaklyRegular M [x, y]) :
    Module.Free R M := by
  apply Module.free_of_maximalIdeal_rTensor_injective
  rw [← hspan, ← range_koszulPairRight_eq_span x y]
  exact range_koszulPairRight_subtype_rTensor_injective_of_isWeaklyRegular hregR hregM

/-- Freeness for a scalar-regular pair generating the maximal ideal. -/
theorem Module.free_of_regular_pair_generates_maximalIdeal
    [IsLocalRing R] [Module.FinitePresentation R M]
    {x y : R}
    (hspan : Ideal.span ({x, y} : Set R) = IsLocalRing.maximalIdeal R)
    (hxR : IsSMulRegular R x)
    (hyR : IsSMulRegular (QuotSMulTop x R) y)
    (hxM : IsSMulRegular M x)
    (hyM : IsSMulRegular (QuotSMulTop x M) y) :
    Module.Free R M := by
  have hregR : IsWeaklyRegular R [x, y] :=
    IsWeaklyRegular.cons hxR ((isWeaklyRegular_singleton_iff (QuotSMulTop x R) y).mpr hyR)
  have hregM : IsWeaklyRegular M [x, y] :=
    IsWeaklyRegular.cons hxM ((isWeaklyRegular_singleton_iff (QuotSMulTop x M) y).mpr hyM)
  exact Module.free_of_weaklyRegular_pair_generates_maximalIdeal hspan hregR hregM

end RegularPair

end TauCeti
