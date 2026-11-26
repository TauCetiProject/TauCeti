/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.GroupTheory.DoubleCoset
public import Mathlib.Topology.Algebra.OpenSubgroup
public import TauCeti.RepresentationTheory.WeightSpace
import TauCeti.GroupTheory.Coset.Basic
import TauCeti.GroupTheory.DoubleCoset.Basic
import TauCeti.Topology.Algebra.Group.DoubleCoset

/-!
# Hecke operators of a representation

Let `ρ` be a representation of a group `G` on a module `W` over a commutative semiring `A`, and `K`
a subgroup of `G`. For a character `χ : K →* A` the **level space**
`W^{K,χ} = {v | ρ(k) v = χ(k) v for all k ∈ K}` is the weight space
`Representation.weightSpace (ρ.comp K.subtype) χ` of the restriction of `ρ` to `K`; for `χ = 1` it
is the space `W^K` of `K`-invariants (`Representation.weightSpace_one`).

For `f : G → A` the **Hecke operator** `ρ(f) = ∑_{g K} f(g) ρ(g)` sums over the left cosets of `K`,
at chosen representatives (`Representation.heckeOperator`). On `W^K`, for `f` right `K`-invariant
and supported on finitely many cosets, it does not depend on the representatives
(`Representation.heckeOperator_apply_eq_sum`). The operator of a left translate of `f` is the
translate of the operator (`Representation.heckeOperator_apply_comp_inv_mul`), operators compose by
convolution of the functions (`Representation.heckeOperator_heckeOperator`), and the operator of a
`K`-bi-invariant function preserves `W^K`
(`Representation.heckeOperator_apply_mem_weightSpace`).
For `K` compact and open, the indicator of a double coset `K g K` lives on finitely many cosets
(`QuotientGroup.finite_support_indicator_doubleCoset`), and its operator, the double coset
operator `[K g K]`, preserves `W^K`
(`Representation.doubleCosetOperator_apply_mem_weightSpace`).

## Main definitions

* `Representation.heckeOperator ρ K f`: the Hecke operator `∑_{g K} f(g) ρ(g)`.
* `Representation.doubleCosetOperator ρ K g`: the double coset operator `[K g K]`.

## References

* G. Shimura, *Introduction to the arithmetic theory of automorphic functions*, Princeton
  University Press, 1971, ch. 3.

The definitions and results are adapted from grh-lean (https://github.com/lsernau/grh-lean, Apache
2.0, Copyright 2026 Anthropic PBC), `src/Lib/Adelic/Hecke/Basic.lean` (`New.heckeFun`,
`New.heckeCoset`, `New.heckeFun_eq_sum`, `New.heckeFun_comp_inv_mul`,
`New.heckeFun_heckeFun`, `New.heckeFun_mem_levelSpace`, `New.isHeckeFunction_doubleCoset`).
-/

public section

open Function Set

namespace Representation

variable {A G W : Type*} [CommSemiring A] [Group G] [AddCommMonoid W] [Module A W]
  {ρ : Representation A G W} {K : Subgroup G}

/-! ### Hecke operators -/

variable (ρ K) in
/-- **The Hecke operator** `ρ(f) = ∑_{g K} f(g) ρ(g)` of `f : G → A`, summed over the left cosets of
`K` at their chosen representatives (`0` if infinitely many terms are nonzero). On `K`-invariant
vectors, for `f` right `K`-invariant and supported on finitely many cosets, it does not depend on
the representatives (`Representation.heckeOperator_apply_eq_sum`); it is the action of `f` for the
Haar measure with `vol K = 1`. For the indicator of `K g K` it is the double coset operator
`[K g K]`. -/
noncomputable def heckeOperator (f : G → A) : Module.End A W :=
  ∑ᶠ q : G ⧸ K, f q.out • ρ q.out

variable (ρ K) in
theorem heckeOperator_def (f : G → A) :
    ρ.heckeOperator K f = ∑ᶠ q : G ⧸ K, f q.out • ρ q.out :=
  (rfl)

variable {f : G → A} {v : W}

/-- On a `K`-invariant vector, the Hecke operator of a right `K`-invariant `f` supported on finitely
many cosets is the finite sum `∑ f(r i) ρ(r i) v` over any family `r` of representatives of
distinct cosets covering the support of `f`. -/
theorem heckeOperator_apply_eq_sum (hf : ∀ g, ∀ k ∈ K, f (g * k) = f g)
    (hv : v ∈ weightSpace (ρ.comp K.subtype) 1) {ι : Type*} {s : Finset ι} {r : ι → G}
    (hr : InjOn (fun i ↦ (r i : G ⧸ K)) s) (hs : ∀ g, f g ≠ 0 → ∃ i ∈ s, (r i : G ⧸ K) = g) :
    ρ.heckeOperator K f v = ∑ i ∈ s, f (r i) • ρ (r i) v := by
  classical
  have h_supp (q : G ⧸ K) (hq : f q.out ≠ 0) : q ∈ s.image fun i ↦ (r i : G ⧸ K) := by
    obtain ⟨i, hi, h⟩ := hs _ hq
    exact Finset.mem_image.2 ⟨i, hi, by rw [h, QuotientGroup.out_eq']⟩
  -- the chosen representative of `g K` is some `g k`, and `k` does not change `f g • ρ g v`
  have hvK (k : G) (hk : k ∈ K) : ρ k v = v := by simpa using mem_weightSpace.1 hv ⟨k, hk⟩
  have h_term (g : G) : f (g : G ⧸ K).out • ρ (g : G ⧸ K).out v = f g • ρ g v := by
    rw [QuotientGroup.apply_out_mk hf g, QuotientGroup.apply_out_mk (f := fun g ↦ ρ g v)
      (fun g k hk ↦ by rw [map_mul, mul_apply_eq_comp, hvK k hk]) g]
  have h_support : support (fun q : G ⧸ K ↦ f q.out • ρ q.out) ⊆
      ↑(s.image fun i ↦ (r i : G ⧸ K)) := fun q hq ↦ h_supp q (left_ne_zero_of_smul hq)
  rw [heckeOperator_def, finsum_eq_sum_of_support_subset _ h_support, LinearMap.sum_apply,
    Finset.sum_image hr]
  simp [h_term]

/-- On a `K`-invariant vector, the Hecke operator of a left translate `g ↦ f (x⁻¹ g)` is `ρ(x)`
applied to the Hecke operator of `f`, for `f` right `K`-invariant with finite support modulo `K`. -/
theorem heckeOperator_apply_comp_inv_mul (hf : ∀ g, ∀ k ∈ K, f (g * k) = f g)
    (hf_fin : (support fun q : G ⧸ K ↦ f q.out).Finite) (hv : v ∈ weightSpace (ρ.comp K.subtype) 1)
    (x : G) :
    ρ.heckeOperator K (fun g ↦ f (x⁻¹ * g)) v = ρ x (ρ.heckeOperator K f v) := by
  -- Both are finite sums over the cosets in the support of `f`, translated by `x`.
  classical
  have h_out (g : G) : f (g : G ⧸ K).out = f g := QuotientGroup.apply_out_mk hf g
  have hcov (g : G) (hg : f g ≠ 0) : ∃ q ∈ hf_fin.toFinset, (q.out : G ⧸ K) = g :=
    ⟨g, by simpa [h_out] using hg, QuotientGroup.out_eq' _⟩
  have hinj : InjOn (fun q : G ⧸ K ↦ (q.out : G ⧸ K)) hf_fin.toFinset := fun q _ q' _ h ↦ by
    simpa using h
  rw [heckeOperator_apply_eq_sum hf hv (r := fun q : G ⧸ K ↦ q.out) hinj hcov,
    heckeOperator_apply_eq_sum (s := hf_fin.toFinset) (r := fun q : G ⧸ K ↦ x * q.out)
      (fun g k hk ↦ by rw [← mul_assoc, hf _ k hk]) hv (fun q _ q' _ h ↦ by simpa using h)
      (fun g hg ↦ ⟨((x⁻¹ * g : G) : G ⧸ K), by simpa [h_out] using hg, by
        obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul K (x⁻¹ * g)
        rw [QuotientGroup.eq, hk]
        simp [mul_assoc]⟩)]
  simp [map_sum, map_mul]

/-- For `f` supported on finitely many cosets, the Hecke operator is the finite sum of
`f(q.out) ρ(q.out)` over those cosets. -/
theorem heckeOperator_eq_sum (hf_fin : (support fun q : G ⧸ K ↦ f q.out).Finite) :
    ρ.heckeOperator K f = ∑ q ∈ hf_fin.toFinset, f q.out • ρ q.out := by
  refine finsum_eq_sum_of_support_subset _ fun q hq ↦ ?_
  simpa using left_ne_zero_of_smul hq

/-- **Linearity in the function.** For functions `F i` supported on finitely many cosets,
`ρ(∑ c_i F_i) = ∑ c_i ρ(F_i)`. -/
theorem heckeOperator_sum {ι : Type*} (T : Finset ι) (c : ι → A) (F : ι → G → A)
    (hF : ∀ i ∈ T, (support fun q : G ⧸ K ↦ F i q.out).Finite) :
    ρ.heckeOperator K (fun x ↦ ∑ i ∈ T, c i * F i x) = ∑ i ∈ T, c i • ρ.heckeOperator K (F i) := by
  have hF' (i : ι) (hi : i ∈ T) :
      (support fun q : G ⧸ K ↦ c i • (F i q.out • ρ q.out)).Finite :=
    (hF i hi).subset fun q hq ↦ by
      simp only [mem_support] at hq ⊢
      exact fun h ↦ hq (by rw [h, zero_smul, smul_zero])
  simp only [heckeOperator_def, Finset.sum_smul, mul_smul]
  rw [finsum_sum_comm T _ hF']
  exact Finset.sum_congr rfl fun i hi ↦
    (smul_finsum' (c i) ((hF i hi).subset fun q hq ↦ left_ne_zero_of_smul hq)).symm

/-- **Composition of Hecke operators.** For right `K`-invariant `f` and `f'` supported on finitely
many cosets and a `K`-invariant `v`, `ρ(f') (ρ(f) v) = ρ(f' * f) v`, where
`(f' * f)(x) = ∑_{g K} f'(g) f(g⁻¹ x)` is the convolution over the cosets of the support of `f'`. -/
theorem heckeOperator_heckeOperator (hf : ∀ g, ∀ k ∈ K, f (g * k) = f g)
    (hf_fin : (support fun q : G ⧸ K ↦ f q.out).Finite) (hv : v ∈ weightSpace (ρ.comp K.subtype) 1)
    {f' : G → A}
    (hf'_fin : (support fun q : G ⧸ K ↦ f' q.out).Finite) :
    ρ.heckeOperator K f' (ρ.heckeOperator K f v) =
      ρ.heckeOperator K (fun x ↦ ∑ q ∈ hf'_fin.toFinset, f' q.out * f (q.out⁻¹ * x)) v := by
  rw [heckeOperator_sum _ _ _ fun q _ ↦ QuotientGroup.finite_support_comp_inv_mul hf hf_fin _,
    heckeOperator_eq_sum hf'_fin, LinearMap.sum_apply, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun q _ ↦ ?_
  rw [LinearMap.smul_apply, LinearMap.smul_apply,
    heckeOperator_apply_comp_inv_mul hf hf_fin hv]

/-- **The Hecke operator and level spaces.** Let `f` be right `K`-invariant, supported on finitely
many cosets, with `χ'(k) f(k g) = f(g)` for `k ∈ K'`. Then `ρ(f)` maps `K`-invariant vectors into
the level space `W^{K',χ'}`. In particular the operator of a `K`-bi-invariant function preserves
`W^K`. -/
theorem heckeOperator_apply_mem_weightSpace {K' : Subgroup G} {χ' : K' →* A}
    (hf : ∀ g, ∀ k ∈ K, f (g * k) = f g) (hf_fin : (support fun q : G ⧸ K ↦ f q.out).Finite)
    (hf_left : ∀ (k : K') g, χ' k * f (k * g) = f g)
    (hv : v ∈ weightSpace (ρ.comp K.subtype) 1) :
    ρ.heckeOperator K f v ∈ weightSpace (ρ.comp K'.subtype) χ' := by
  -- `ρ k` replaces `f` by `f (k⁻¹ ·) = χ'(k) f`
  refine mem_weightSpace.2 fun k ↦ ?_
  have h_translate (g : G) : f ((k : G)⁻¹ * g) = χ' k * f g := by
    simpa using (hf_left k ((k : G)⁻¹ * g)).symm
  have h_scale : ρ.heckeOperator K (fun g ↦ f ((k : G)⁻¹ * g)) = χ' k • ρ.heckeOperator K f := by
    simp only [heckeOperator_def, h_translate, mul_smul]
    exact (smul_finsum' _ (hf_fin.subset fun q hq ↦ left_ne_zero_of_smul hq)).symm
  rw [MonoidHom.comp_apply, Subgroup.coe_subtype, ← heckeOperator_apply_comp_inv_mul hf hf_fin hv,
    h_scale, LinearMap.smul_apply]

variable (ρ K) in
/-- **The double coset operator** `[K g K]`: the Hecke operator of the indicator of `K g K`, the sum
of `ρ(h)` over the chosen representatives `h` of the cosets `h K` making up `K g K`. -/
noncomputable def doubleCosetOperator (g : G) : Module.End A W :=
  ρ.heckeOperator K ((DoubleCoset.doubleCoset g K K).indicator 1)

variable (ρ K) in
theorem doubleCosetOperator_def (g : G) :
    ρ.doubleCosetOperator K g = ρ.heckeOperator K ((DoubleCoset.doubleCoset g K K).indicator 1) :=
  (rfl)

/-- For a compact open subgroup `K`, the double coset operator `[K g K]` preserves `W^K`. -/
theorem doubleCosetOperator_apply_mem_weightSpace [TopologicalSpace G] [IsTopologicalGroup G]
    (hK_open : IsOpen (K : Set G)) (hK : IsCompact (K : Set G)) (g : G)
    (hv : v ∈ weightSpace (ρ.comp K.subtype) 1) :
    ρ.doubleCosetOperator K g v ∈ weightSpace (ρ.comp K.subtype) 1 := by
  -- the indicator of `K g K` is invariant on both sides under `K`
  have h_right (x : G) (k : G) (hk : k ∈ K) :
      (DoubleCoset.doubleCoset g K K).indicator (1 : G → A) (x * k) =
        (DoubleCoset.doubleCoset g K K).indicator 1 x := by
    classical
    simp only [Set.indicator_apply, Pi.one_apply, DoubleCoset.mul_mem_doubleCoset_iff_right hk]
  have h_left (k : K) (x : G) :
      (1 : K →* A) k * (DoubleCoset.doubleCoset g K K).indicator (1 : G → A) (k * x) =
        (DoubleCoset.doubleCoset g K K).indicator 1 x := by
    rw [MonoidHom.one_apply, one_mul]
    classical
    simp only [Set.indicator_apply, Pi.one_apply, DoubleCoset.mul_mem_doubleCoset_iff k.property]
  exact heckeOperator_apply_mem_weightSpace h_right
    (QuotientGroup.finite_support_indicator_doubleCoset hK_open hK g) h_left hv

end Representation
