/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Mathlib.RingTheory.Regular.IsSMulRegular
public import Mathlib.RingTheory.Regular.Category
public import Mathlib.RingTheory.LocalRing.Module
public import TauCeti.LinearAlgebra.TensorProduct.Prod

/-!
# Regular pairs and the two-term Koszul relation

For a pair `x, y` regular on a module, every relation `x • a + y • b = 0` is a
Koszul relation. Tensoring this calculation proves that a finitely presented
module over a local ring is free when a regular pair generates the maximal
ideal and is also regular on the module.

## References

* [pcfawd-formalization](https://github.com/tdupu/pcfawd-formalization/blob/9a20b3f351446d64e6015d704198bc71c7002008/lean/Pcf/Stacks/Purity/MiracleFlatnessTwo.lean):
  `Pcf.Stacks.exists_koszul_relation_of_isSMulRegular_pair`,
  `Pcf.Stacks.exact_koszulPair_of_isSMulRegular`, and
  `Pcf.Stacks.Module.free_of_regular_pair_generates_maximalIdeal`.

-/

public section

open TensorProduct
open scoped Pointwise

universe u v

namespace TauCeti

variable {R : Type u} {M : Type v}
  [CommRing R] [AddCommGroup M] [Module R M]

/-- The first differential of the two-element Koszul complex, with sign convention
`c ↦ (-y • c, x • c)`. -/
def koszulPairLeft (x y : R) : M →ₗ[R] M × M where
  toFun c := (-(y • c), x • c)
  map_add' a b := by
    ext <;> dsimp <;> module
  map_smul' r c := by
    ext <;> dsimp <;> simp only [smul_neg, smul_smul] <;> module

@[simp]
theorem koszulPairLeft_apply (x y : R) (c : M) :
    koszulPairLeft x y c = (-(y • c), x • c) := by
  simp only [koszulPairLeft, LinearMap.coe_mk, AddHom.coe_mk]

@[simp]
theorem koszulPairLeft_fst (x y : R) (c : M) :
    (koszulPairLeft x y c).1 = -(y • c) := by
  rw [koszulPairLeft_apply]

@[simp]
theorem koszulPairLeft_snd (x y : R) (c : M) :
    (koszulPairLeft x y c).2 = x • c := by
  rw [koszulPairLeft_apply]

/-- The second differential of the two-element Koszul complex. -/
def koszulPairRight (x y : R) : M × M →ₗ[R] M where
  toFun p := x • p.1 + y • p.2
  map_add' a b := by simp only [Prod.fst_add, Prod.snd_add, smul_add]; abel
  map_smul' r c := by
    simp only [Prod.smul_fst, Prod.smul_snd, RingHom.id_apply, smul_add, smul_smul]
    module

@[simp]
theorem koszulPairRight_apply (x y : R) (p : M × M) :
    koszulPairRight x y p = x • p.1 + y • p.2 := by
  simp only [koszulPairRight, LinearMap.coe_mk, AddHom.coe_mk]

@[simp]
theorem koszulPairRight_apply_pair (x y : R) (a b : M) :
    koszulPairRight x y (a, b) = x • a + y • b := by
  rw [koszulPairRight_apply]

/-- The first Koszul differential commutes with tensoring by `M`. -/
theorem koszulPairTensorEquiv_rTensor_left (x y : R) :
    (TauCeti.TensorProduct.prodScalarLeftEquiv (R := R) (M := M)).toLinearMap.comp
        ((koszulPairLeft (M := R) x y).rTensor M) =
      (koszulPairLeft (M := M) x y).comp (TensorProduct.lid R M).toLinearMap := by
  apply TensorProduct.ext'
  intro r m
  simp [koszulPairLeft, mul_smul]

/-- The second Koszul differential commutes with tensoring by `M`. -/
theorem lid_rTensor_koszulPairRight (x y : R) :
    (TensorProduct.lid R M).toLinearMap.comp
        ((koszulPairRight (M := R) x y).rTensor M) =
      (koszulPairRight (M := M) x y).comp
        (TauCeti.TensorProduct.prodScalarLeftEquiv (R := R) (M := M)).toLinearMap := by
  apply TensorProduct.ext'
  rintro ⟨a, b⟩ m
  simp [koszulPairRight, add_smul, mul_smul]

/-- Every relation on a pair regular on `M` is a Koszul relation. -/
theorem exists_koszul_relation_of_isSMulRegular_pair
    {x y : R} {a b : M}
    (hx : IsSMulRegular M x)
    (hy : IsSMulRegular (QuotSMulTop x M) y)
    (h : x • a + y • b = 0) :
    ∃ c : M, a = -(y • c) ∧ b = x • c := by
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

/-- The two-element Koszul complex is exact at the middle for a regular pair. -/
theorem exact_koszulPair_of_isSMulRegular
    {x y : R}
    (hx : IsSMulRegular M x)
    (hy : IsSMulRegular (QuotSMulTop x M) y) :
    Function.Exact (koszulPairLeft (M := M) x y) (koszulPairRight (M := M) x y) := by
  intro p
  constructor
  · intro hp
    obtain ⟨c, hc₁, hc₂⟩ :=
      exists_koszul_relation_of_isSMulRegular_pair hx hy hp
    refine ⟨c, ?_⟩
    ext
    · exact hc₁.symm
    · exact hc₂.symm
  · rintro ⟨c, rfl⟩
    simp only [koszulPairLeft_apply, koszulPairRight_apply_pair, smul_neg, smul_smul]
    rw [mul_comm x y, neg_add_cancel]

/-- Tensoring the two-element Koszul complex with `M` preserves exactness at
the middle when the pair is regular on `M`. -/
theorem exact_rTensor_koszulPair_of_isSMulRegular
    {x y : R}
    (hx : IsSMulRegular M x)
    (hy : IsSMulRegular (QuotSMulTop x M) y) :
    Function.Exact
      ((koszulPairLeft (M := R) x y).rTensor M)
      ((koszulPairRight (M := R) x y).rTensor M) := by
  let e₁ := TensorProduct.lid R M
  let e₂ := TauCeti.TensorProduct.prodScalarLeftEquiv (R := R) (M := M)
  have hcomm₁ := koszulPairTensorEquiv_rTensor_left (M := M) x y
  have hcomm₂ := lid_rTensor_koszulPairRight (M := M) x y
  have hexact := exact_koszulPair_of_isSMulRegular hx hy
  exact (Function.Exact.iff_of_ladder_linearEquiv
    (e₁ := e₁) (e₂ := e₂) (e₃ := e₁) hcomm₁.symm hcomm₂.symm).mp hexact

/-- A regular pair on the ring and module keeps the inclusion of its ideal
injective after tensoring with the module. -/
theorem range_koszulPairRight_subtype_rTensor_injective_of_isSMulRegular
    {x y : R}
    (hxR : IsSMulRegular R x)
    (hyR : IsSMulRegular (QuotSMulTop x R) y)
    (hxM : IsSMulRegular M x)
    (hyM : IsSMulRegular (QuotSMulTop x M) y) :
    Function.Injective
      ((LinearMap.range (koszulPairRight (M := R) x y)).subtype.rTensor M) := by
  let f := koszulPairLeft (M := R) x y
  let g₀ := koszulPairRight (M := R) x y
  let I := LinearMap.range g₀
  let g : R × R →ₗ[R] I := g₀.rangeRestrict
  let i : I →ₗ[R] R := I.subtype
  have hsurj : Function.Surjective g := g₀.surjective_rangeRestrict
  have hexactRing : Function.Exact f g := by
    rw [LinearMap.exact_iff, LinearMap.ker_rangeRestrict]
    exact LinearMap.exact_iff.mp (exact_koszulPair_of_isSMulRegular hxR hyR)
  have hexactRange : Function.Exact (f.rTensor M) (g.rTensor M) :=
    _root_.rTensor_exact M hexactRing hsurj
  have hexactModule : Function.Exact (f.rTensor M) (g₀.rTensor M) :=
    exact_rTensor_koszulPair_of_isSMulRegular hxM hyM
  apply LinearMap.ker_eq_bot.mp
  apply le_antisymm
  · intro z hz
    rw [Submodule.mem_bot]
    have hz' : (i.rTensor M) z = 0 := LinearMap.mem_ker.mp hz
    obtain ⟨w, hw⟩ := g.rTensor_surjective M hsurj z
    have hg₀w : (g₀.rTensor M) w = 0 := by
      calc
        (g₀.rTensor M) w = ((i.comp g).rTensor M) w := rfl
        _ = (i.rTensor M) ((g.rTensor M) w) :=
          LinearMap.rTensor_comp_apply M i g w
        _ = (i.rTensor M) z := by rw [hw]
        _ = 0 := hz'
    have hwRange : w ∈ LinearMap.range (f.rTensor M) := (hexactModule w).mp hg₀w
    have hgw : (g.rTensor M) w = 0 := (hexactRange w).mpr hwRange
    exact hw.symm.trans hgw
  · exact bot_le

/-- The range of the second Koszul differential is the two-generated ideal. -/
theorem range_koszulPairRight_eq_span (x y : R) :
    LinearMap.range (koszulPairRight (M := R) x y) =
      Ideal.span ({x, y} : Set R) := by
  ext z
  constructor
  · rintro ⟨⟨a, b⟩, rfl⟩
    rw [Ideal.mem_span_pair]
    refine ⟨a, b, ?_⟩
    simp only [koszulPairRight_apply_pair, smul_eq_mul]
    ring
  · intro hz
    rw [Ideal.mem_span_pair] at hz
    obtain ⟨a, b, hab⟩ := hz
    refine ⟨(a, b), ?_⟩
    simp only [koszulPairRight_apply_pair, smul_eq_mul]
    calc
      x * a + y * b = a * x + b * y := by ring
      _ = z := hab

/-- A finitely presented module over a local ring is free when a regular pair
generates the maximal ideal and is also regular on the module. -/
theorem Module.free_of_regular_pair_generates_maximalIdeal
    [IsLocalRing R] [Module.FinitePresentation R M]
    {x y : R}
    (hspan : Ideal.span ({x, y} : Set R) = IsLocalRing.maximalIdeal R)
    (hxR : IsSMulRegular R x)
    (hyR : IsSMulRegular (QuotSMulTop x R) y)
    (hxM : IsSMulRegular M x)
    (hyM : IsSMulRegular (QuotSMulTop x M) y) :
    Module.Free R M := by
  apply Module.free_of_maximalIdeal_rTensor_injective
  rw [← hspan, ← range_koszulPairRight_eq_span x y]
  exact range_koszulPairRight_subtype_rTensor_injective_of_isSMulRegular hxR hyR hxM hyM

end TauCeti
