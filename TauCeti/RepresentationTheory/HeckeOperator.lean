/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.GroupTheory.DoubleCoset
public import Mathlib.Topology.Algebra.OpenSubgroup
public import TauCeti.NumberTheory.HeckeRing.CosetSystem.Basic
public import TauCeti.RepresentationTheory.WeightSpace
import TauCeti.GroupTheory.Coset.Basic
import TauCeti.GroupTheory.Coset.Card
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
(`Representation.doubleCosetOperator_apply_mem_weightSpace`). On `W^K`, `[K g K]` is the sum of
the translates `ρ(q g)` over representatives `q` of `K ⧸ (K ∩ g K g⁻¹)`
(`Representation.doubleCosetOperator_apply_eq_finsum`), and it is `0` if there are infinitely many
of them (`Representation.doubleCosetOperator_eq_zero_of_relIndex_eq_zero`). On `W^K` the operator
of the indicator of a subgroup `K' ⊇ K` of finite index is the sum `∑_{h ∈ K' / K} ρ(h)`
(`Representation.heckeOperator_indicator_apply`). Composing two double coset operators is the
operator of the convolution of their indicators, read off a coset system of the first double coset
(`Representation.doubleCosetOperator_doubleCosetOperator_apply`). For a `ρ`-invariant sesquilinear
form `B`, `[K g K]` and `[K g⁻¹ K]` are adjoint on `W^K` when `K g K` and `K g⁻¹ K` consist of the
same number of left cosets of `K` (`Representation.sesqForm_doubleCosetOperator_left_eq_right_inv`).

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

namespace QuotientGroup

open scoped Pointwise

variable {A G : Type*} [Zero A] [One A] [Group G] {K : Subgroup G}

/-- If `K ∩ g K g⁻¹` has finite index in `K`, the indicator of the double coset `K g K` is
supported on finitely many left cosets of `K`. This is the algebraic counterpart of
`QuotientGroup.finite_support_indicator_doubleCoset`. -/
theorem finite_support_indicator_doubleCoset_of_isFiniteRelIndex (g : G)
    [(ConjAct.toConjAct g • K).IsFiniteRelIndex K] :
    (support fun q : G ⧸ K ↦ (DoubleCoset.doubleCoset g K K).indicator (1 : G → A) q.out).Finite :=
  ((Subgroup.isCosetSystem_out_mul K K g).finite_iff.mp inferInstance).subset
    fun q hq ↦ ⟨q.out, Set.mem_of_indicator_ne_zero hq, q.out_eq'⟩

/-- The indicator of a subgroup `K'` containing `K` with finite index is supported on finitely
many left cosets of `K`. -/
theorem finite_support_indicator_of_le {K' : Subgroup G} (hKK' : K ≤ K')
    [K.IsFiniteRelIndex K'] :
    (support fun q : G ⧸ K ↦ (K' : Set G).indicator (1 : G → A) q.out).Finite :=
  (Set.finite_of_ncard_ne_zero (s := ((↑) : G → G ⧸ K) '' K')
    (by rw [Subgroup.ncard_image_mk_eq_relIndex hKK']; exact Subgroup.relIndex_ne_zero)).subset
    fun q hq ↦ ⟨q.out, Set.mem_of_indicator_ne_zero hq, q.out_eq'⟩

end QuotientGroup

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

/-- The indicator of `K g K` is right `K`-invariant. -/
private theorem indicator_doubleCoset_mul_right (g x : G) {k : G} (hk : k ∈ K) :
    (DoubleCoset.doubleCoset g K K).indicator (1 : G → A) (x * k) =
      (DoubleCoset.doubleCoset g K K).indicator 1 x := by
  classical
  simp only [Set.indicator_apply, Pi.one_apply, DoubleCoset.mul_mem_doubleCoset_iff_right hk]

open Pointwise in
/-- On `W^K`, the double coset operator `[K g K]` is the sum of the translates `ρ(q g) v` over
representatives `q` of `K ⧸ (K ∩ g K g⁻¹)`: the cosets `q g K` are the distinct cosets making up
`K g K`. When `K ∩ g K g⁻¹` has infinite index in `K` both sides are `0`. -/
theorem doubleCosetOperator_apply_eq_finsum (g : G) (hv : v ∈ weightSpace (ρ.comp K.subtype) 1) :
    ρ.doubleCosetOperator K g v =
      ∑ᶠ q : K ⧸ (ConjAct.toConjAct g • K).subgroupOf K, ρ ((q.out : G) * g) v := by
  classical
  -- the elements `q g` form the canonical coset system of `K g K`
  have h := Subgroup.isCosetSystem_out_mul K K g
  have hright (x k : G) (hk : k ∈ K) := indicator_doubleCoset_mul_right (A := A) g x hk
  -- every `q g` lies in `K g K`, where the indicator is `1`
  have hterm (q : K ⧸ (ConjAct.toConjAct g • K).subgroupOf K) :
      (DoubleCoset.doubleCoset g K K).indicator (1 : G → A) ((q.out : G) * g) = 1 := by
    rw [Set.indicator_of_mem (h.mem_doubleCoset q), Pi.one_apply]
  cases finite_or_infinite (K ⧸ (ConjAct.toConjAct g • K).subgroupOf K) with
  | inl hfin =>
    have := Fintype.ofFinite (K ⧸ (ConjAct.toConjAct g • K).subgroupOf K)
    rw [doubleCosetOperator_def, heckeOperator_apply_eq_sum hright hv (s := Finset.univ)
      h.injective.injOn fun x hx ↦ ?_, finsum_eq_sum_of_fintype]
    · simp only [hterm, one_smul]
    -- every coset in `K g K` is some `q g K`
    obtain ⟨q, hq⟩ := (Subgroup.isCosetSystem_iff_injective_and_range_eq.1 h).2.ge
      ⟨x, Set.mem_of_indicator_ne_zero hx, rfl⟩
    exact ⟨q, Finset.mem_univ q, hq⟩
  | inr hinf =>
    -- for `v ≠ 0` both sums have infinitely many nonzero terms, as each `ρ(x)` is injective
    rcases eq_or_ne v 0 with rfl | hv0
    · simp
    have hne (x : G) : ρ x v ≠ 0 := fun h0 ↦ hv0 (by simpa [h0] using (ρ.inv_self_apply x v).symm)
    rw [finsum_of_infinite_support (Set.infinite_univ.mono fun q _ ↦ hne _),
      doubleCosetOperator_def, heckeOperator_def,
      finsum_of_infinite_support ((Set.infinite_range_of_injective h.injective).mono ?_),
      LinearMap.zero_apply]
    rintro _ ⟨q, rfl⟩
    rw [Function.mem_support, QuotientGroup.apply_out_mk hright, hterm, one_smul]
    exact fun h0 ↦ hne _ (LinearMap.congr_fun h0 v)

/-- For a compact open subgroup `K`, the double coset operator `[K g K]` preserves `W^K`. -/
theorem doubleCosetOperator_apply_mem_weightSpace [TopologicalSpace G] [IsTopologicalGroup G]
    (hK_open : IsOpen (K : Set G)) (hK : IsCompact (K : Set G)) (g : G)
    (hv : v ∈ weightSpace (ρ.comp K.subtype) 1) :
    ρ.doubleCosetOperator K g v ∈ weightSpace (ρ.comp K.subtype) 1 := by
  -- the indicator of `K g K` is invariant on both sides under `K`
  have h_right (x k : G) (hk : k ∈ K) := indicator_doubleCoset_mul_right (A := A) g x hk
  have h_left (k : K) (x : G) :
      (1 : K →* A) k * (DoubleCoset.doubleCoset g K K).indicator (1 : G → A) (k * x) =
        (DoubleCoset.doubleCoset g K K).indicator 1 x := by
    rw [MonoidHom.one_apply, one_mul]
    classical
    simp only [Set.indicator_apply, Pi.one_apply, DoubleCoset.mul_mem_doubleCoset_iff k.property]
  exact heckeOperator_apply_mem_weightSpace h_right
    (QuotientGroup.finite_support_indicator_doubleCoset hK_open hK g) h_left hv

/-! ### Hecke operators of subgroups -/

/-- On `K`-invariant vectors, the Hecke operator of the indicator of `K` is the identity. -/
theorem heckeOperator_indicator_self_apply (hv : v ∈ weightSpace (ρ.comp K.subtype) 1) :
    ρ.heckeOperator K ((K : Set G).indicator 1) v = v := by
  classical
  rw [heckeOperator_apply_eq_sum (s := {()}) (r := fun _ ↦ 1) (fun g k hk ↦ ?_) hv
    (fun a _ b _ _ ↦ Subsingleton.elim a b) fun g hg ↦ ⟨(), Finset.mem_singleton_self _, ?_⟩]
  · simp
  · simp only [Set.indicator_apply, SetLike.mem_coe, mul_mem_cancel_right hk, Pi.one_apply]
  · exact QuotientGroup.eq.mpr (by simpa using Set.mem_of_indicator_ne_zero hg)

/-- On `K`-invariant vectors, the Hecke operator of the indicator of a subgroup `K'` containing
`K` with finite index is the sum `∑_{q ∈ K' ⧸ K} ρ(q) v` over the cosets of `K` in `K'`. -/
theorem heckeOperator_indicator_apply {K' : Subgroup G} (hKK' : K ≤ K') [K.IsFiniteRelIndex K']
    (hv : v ∈ weightSpace (ρ.comp K.subtype) 1) :
    ρ.heckeOperator K ((K' : Set G).indicator 1) v = ∑ᶠ q : K' ⧸ K.subgroupOf K', ρ q.out v := by
  classical
  have := Fintype.ofFinite (K' ⧸ K.subgroupOf K')
  rw [finsum_eq_sum_of_fintype, heckeOperator_apply_eq_sum (s := Finset.univ)
    (r := fun q : K' ⧸ K.subgroupOf K' ↦ (q.out : G)) (fun g k hk ↦ ?_) hv
    (fun q _ q' _ h ↦ ?_) fun g hg ↦ ?_]
  · simp
  · simp only [Set.indicator_apply, SetLike.mem_coe, mul_mem_cancel_right (hKK' hk), Pi.one_apply]
  · rw [← QuotientGroup.out_eq' q, ← QuotientGroup.out_eq' q', QuotientGroup.eq,
      Subgroup.mem_subgroupOf]
    simpa using QuotientGroup.eq.mp h
  · -- the representative of the coset of `g` in `K'` differs from `g` by an element of `K`
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul (K.subgroupOf K')
      ⟨g, Set.mem_of_indicator_ne_zero hg⟩
    refine ⟨QuotientGroup.mk ⟨g, Set.mem_of_indicator_ne_zero hg⟩, Finset.mem_univ _,
      QuotientGroup.eq.mpr ?_⟩
    simpa [hh] using K.inv_mem (Subgroup.mem_subgroupOf.mp h.property)

/-! ### Products of double coset operators -/

open scoped Pointwise in
/-- **Composing double coset operators.** Let `r` name the left cosets of `K` in `K g K` (a finite
coset system) and let `K ∩ g' K g'⁻¹` have finite index in `K`. On `K`-invariant vectors,
`[K g K] [K g' K]` is the Hecke operator of `x ↦ ∑_c 1_{K g' K}((r c)⁻¹ x)`, the convolution of the
indicators of `K g K` and `K g' K`. -/
theorem doubleCosetOperator_doubleCosetOperator_apply {g g' : G}
    [(ConjAct.toConjAct g' • K).IsFiniteRelIndex K] {κ : Type*} [Fintype κ] {r : κ → G}
    (hr : Subgroup.IsCosetSystem K K g r) (hv : v ∈ weightSpace (ρ.comp K.subtype) 1) :
    ρ.doubleCosetOperator K g (ρ.doubleCosetOperator K g' v) =
      ρ.heckeOperator K (fun x ↦ ∑ c, (DoubleCoset.doubleCoset g' K K).indicator 1
        ((r c)⁻¹ * x)) v := by
  classical
  set f : G → A := (DoubleCoset.doubleCoset g' (K : Set G) K).indicator 1
  have hf (x k : G) (hk : k ∈ K) : f (x * k) = f x := indicator_doubleCoset_mul_right g' x hk
  have hf_left (k : K) (x : G) : (1 : K →* A) k * f (k * x) = f x := by
    simp only [f, MonoidHom.one_apply, one_mul, Set.indicator_apply, Pi.one_apply,
      DoubleCoset.mul_mem_doubleCoset_iff k.property]
  have hf_fin := QuotientGroup.finite_support_indicator_doubleCoset_of_isFiniteRelIndex
    (A := A) (K := K) g'
  have hTv : ρ.doubleCosetOperator K g' v ∈ weightSpace (ρ.comp K.subtype) 1 := by
    rw [doubleCosetOperator_def]
    exact heckeOperator_apply_mem_weightSpace hf hf_fin hf_left hv
  -- expand `[K g K]` over `r`, then each translate of `[K g' K] v` as the operator of a translate
  have h := heckeOperator_sum (ρ := ρ) (K := K) Finset.univ (fun _ ↦ 1)
    (fun c x ↦ f ((r c)⁻¹ * x)) fun c _ ↦ QuotientGroup.finite_support_comp_inv_mul hf hf_fin _
  simp only [one_mul, one_smul] at h
  rw [doubleCosetOperator_def ρ K g, heckeOperator_apply_eq_sum (s := Finset.univ) (r := r)
    (fun x k hk ↦ ?_) hTv hr.injective.injOn fun x hx ↦ ?_, h, LinearMap.sum_apply]
  · refine Finset.sum_congr rfl fun c _ ↦ ?_
    rw [Set.indicator_of_mem (hr.mem_doubleCoset c), Pi.one_apply, one_smul,
      doubleCosetOperator_def, heckeOperator_apply_comp_inv_mul hf hf_fin hv]
  · exact indicator_doubleCoset_mul_right g x hk
  · obtain ⟨c, hc⟩ := Set.mem_iUnion.mp
      (hr.doubleCoset_subset_iUnion (Set.mem_of_indicator_ne_zero hx))
    exact ⟨c, Finset.mem_univ c, QuotientGroup.eq.mpr ((mem_leftCoset_iff _).mp hc)⟩

/-! ### Double coset operators of infinite degree, and invariant sesquilinear forms -/

section InvariantForm

open scoped Pointwise

variable {g : G}

/-- **A double coset of infinite degree.** If `K g K` contains infinitely many left cosets of `K`,
that is `[K : K ∩ g K g⁻¹]` is infinite, the double coset operator `[K g K]` is `0`, the value of
the sum `∑_{q K ⊆ K g K} ρ(q)` with infinitely many nonzero terms. -/
theorem doubleCosetOperator_eq_zero_of_relIndex_eq_zero
    (h : (ConjAct.toConjAct g • K).relIndex K = 0) : ρ.doubleCosetOperator K g = 0 := by
  classical
  rcases subsingleton_or_nontrivial W with hW | hW
  · exact Subsingleton.elim _ _
  have : Nontrivial A := Module.nontrivial A W
  set D := DoubleCoset.doubleCoset g (K : Set G) K
  -- `K g K` meets infinitely many left cosets of `K`
  have hinf : (QuotientGroup.mk '' D : Set (G ⧸ K)).Infinite := fun hfin ↦ by
    have := (Subgroup.isCosetSystem_out_mul K K g).finite_iff.mpr hfin
    exact Nat.card_pos.ne' h
  -- each of them contributes the nonzero term `ρ(q)`
  refine finsum_of_infinite_support (hinf.mono fun q hq ↦ ?_)
  have hD : ∀ x ∈ D, ∀ k ∈ K, x * k ∈ D := fun _ hx _ hk ↦
    DoubleCoset.mul_mem_doubleCoset_of_mem_right hx hk
  have hq' : (q.out : G) ∈ D := by
    rw [← QuotientGroup.out_eq' q] at hq
    exact (Subgroup.mk_mem_image_iff_of_forall_mul_mem hD).mp hq
  rw [mem_support, Set.indicator_of_mem hq', Pi.one_apply, one_smul]
  intro h0
  obtain ⟨w, hw⟩ := exists_ne (0 : W)
  exact hw (by simpa [h0] using (ρ.inv_self_apply q.out w).symm)

variable [StarRing A] {B : W →ₗ⋆[A] W →ₗ[A] A}

/-- For a `ρ`-invariant sesquilinear form `B` and `K`-invariant vectors `x`, `y`, pairing the
double coset operator `[K g K]` in the first variable:
`B ([K g K] x) y = [K : K ∩ g K g⁻¹] • B (g x) y`. -/
theorem sesqForm_doubleCosetOperator_left (hB : ∀ h x y, B (ρ h x) (ρ h y) = B x y) {x y : W}
    (hx : x ∈ weightSpace (ρ.comp K.subtype) 1) (hy : y ∈ weightSpace (ρ.comp K.subtype) 1) :
    B (ρ.doubleCosetOperator K g x) y = (ConjAct.toConjAct g • K).relIndex K • B (ρ g x) y := by
  by_cases hfin : (ConjAct.toConjAct g • K).relIndex K = 0
  · simp [ρ.doubleCosetOperator_eq_zero_of_relIndex_eq_zero hfin, hfin]
  have hcard := (Subgroup.isCosetSystem_out_mul K K g).natCard_eq_relIndex
  have : Finite (DoubleCoset.DecompQuotient K K g) := Nat.finite_of_card_ne_zero (hcard ▸ hfin)
  have := Fintype.ofFinite (DoubleCoset.DecompQuotient K K g)
  have hyK (k : G) (hk : k ∈ K) : ρ k y = y := by simpa using mem_weightSpace.1 hy ⟨k, hk⟩
  rw [doubleCosetOperator_apply_eq_finsum g hx, finsum_eq_sum_of_fintype, map_sum,
    LinearMap.sum_apply, ← hcard, Nat.card_eq_fintype_card, ← Finset.card_univ,
    ← Finset.sum_const]
  -- move the representative `q ∈ K` across `B`
  refine Finset.sum_congr rfl fun q _ ↦ ?_
  calc B (ρ (q.out * g) x) y = B (ρ q.out (ρ g x)) (ρ q.out (ρ (q.out : G)⁻¹ y)) := by
        rw [map_mul, mul_apply_eq_comp, self_inv_apply]
    _ = B (ρ g x) y := by rw [hB, hyK _ (K.inv_mem q.out.property)]

/-- For a `ρ`-invariant sesquilinear form `B` and `K`-invariant vectors `x`, `y`, pairing the
double coset operator `[K g K]` in the second variable:
`B x ([K g K] y) = [K : K ∩ g K g⁻¹] • B x (g y)`. -/
theorem sesqForm_doubleCosetOperator_right (hB : ∀ h x y, B (ρ h x) (ρ h y) = B x y) {x y : W}
    (hx : x ∈ weightSpace (ρ.comp K.subtype) 1) (hy : y ∈ weightSpace (ρ.comp K.subtype) 1) :
    B x (ρ.doubleCosetOperator K g y) = (ConjAct.toConjAct g • K).relIndex K • B x (ρ g y) := by
  by_cases hfin : (ConjAct.toConjAct g • K).relIndex K = 0
  · simp [ρ.doubleCosetOperator_eq_zero_of_relIndex_eq_zero hfin, hfin]
  have hcard := (Subgroup.isCosetSystem_out_mul K K g).natCard_eq_relIndex
  have : Finite (DoubleCoset.DecompQuotient K K g) := Nat.finite_of_card_ne_zero (hcard ▸ hfin)
  have := Fintype.ofFinite (DoubleCoset.DecompQuotient K K g)
  have hxK (k : G) (hk : k ∈ K) : ρ k x = x := by simpa using mem_weightSpace.1 hx ⟨k, hk⟩
  rw [doubleCosetOperator_apply_eq_finsum g hy, finsum_eq_sum_of_fintype, map_sum, ← hcard,
    Nat.card_eq_fintype_card, ← Finset.card_univ, ← Finset.sum_const]
  -- move the representative `q ∈ K` across `B`
  refine Finset.sum_congr rfl fun q _ ↦ ?_
  calc B x (ρ (q.out * g) y) = B (ρ q.out (ρ (q.out : G)⁻¹ x)) (ρ q.out (ρ g y)) := by
        rw [map_mul, mul_apply_eq_comp, self_inv_apply]
    _ = B x (ρ g y) := by rw [hB, hxK _ (K.inv_mem q.out.property)]

/-- **Adjointness of `[K g K]` and `[K g⁻¹ K]`.** If `K ∩ g K g⁻¹` and `K ∩ g⁻¹ K g` have the same
index in `K`, that is `K g K` and `K g⁻¹ K` consist of the same number of left cosets of `K`, then
for every `ρ`-invariant sesquilinear form `B` the double coset operators `[K g K]` and `[K g⁻¹ K]`
are adjoint on the `K`-invariant vectors: `B ([K g K] x) y = B x ([K g⁻¹ K] y)`. For a unitary
representation `B` is the inner product. -/
theorem sesqForm_doubleCosetOperator_left_eq_right_inv (hB : ∀ h x y, B (ρ h x) (ρ h y) = B x y)
    (hdeg : (ConjAct.toConjAct g⁻¹ • K).relIndex K = (ConjAct.toConjAct g • K).relIndex K)
    {x y : W} (hx : x ∈ weightSpace (ρ.comp K.subtype) 1)
    (hy : y ∈ weightSpace (ρ.comp K.subtype) 1) :
    B (ρ.doubleCosetOperator K g x) y = B x (ρ.doubleCosetOperator K g⁻¹ y) := by
  rw [sesqForm_doubleCosetOperator_left hB hx hy, sesqForm_doubleCosetOperator_right hB hx hy,
    hdeg, ← hB g x, self_inv_apply]

end InvariantForm

end Representation
