/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import TauCeti.GroupTheory.DoubleCoset.ClassSum
public import TauCeti.RepresentationTheory.Coinduced

/-!
# Class forms on double cosets

A class form is a vector-valued function supported on one double coset, made equivariant by
summing the vector over the transporters into that coset. In the stabiliser-weighted pairing,
the transporter multiplicity cancels the inverse stabiliser order. Thus pairing against the
class form at `h` evaluates the other form at `h`, even when the stabiliser is nontrivial.

This is the class-form construction for algebraic modular forms (Gross, *Algebraic modular
forms*, 1999), in the normalization of `New.Rows.classForm` and `New.Rows.inner_classForm` in
[lsernau/grh-lean](https://github.com/lsernau/grh-lean), revision `72fead1`,
`grh/src/New/OneLift/TestedForms.lean`.
-/

public section

namespace Representation

open TauCeti

variable {G 𝕜 V : Type*} [Group G] {Γ K : Subgroup G}

private abbrev ClassTransporter (K Γ : Subgroup G) (h y : G) :=
  {γ : Γ // h⁻¹ * (γ : G) * y ∈ K}

private def ClassTransporter.translate {h y : G} (g : Γ) (k : K) :
    ClassTransporter K Γ h ((g : G) * y * k) ≃ ClassTransporter K Γ h y where
  toFun a := ⟨a.val * g, by
    have ha := K.mul_mem a.property (K.inv_mem k.property)
    convert ha using 1; simp [mul_assoc]⟩
  invFun a := ⟨a.val * g⁻¹, by
    have ha := K.mul_mem a.property k.property
    convert ha using 1; simp [mul_assoc]⟩
  left_inv a := Subtype.ext (by simp)
  right_inv a := Subtype.ext (by simp)

private def ClassTransporter.selfEquiv (h : G) :
    ClassTransporter K Γ h h ≃ mackeySubgroup h K Γ where
  toFun a := ⟨a.val, mem_mackeySubgroup_iff.mpr ⟨a.val.property, a.property⟩⟩
  invFun a := ⟨⟨a, (mem_mackeySubgroup_iff.mp a.property).1⟩,
    (mem_mackeySubgroup_iff.mp a.property).2⟩
  left_inv _ := rfl
  right_inv _ := rfl

private theorem ClassTransporter.finite {h y : G} [Finite (mackeySubgroup h K Γ)] :
    Finite (ClassTransporter K Γ h y) := by
  classical
  cases isEmpty_or_nonempty (ClassTransporter K Γ h y) with
  | inl h₀ => infer_instance
  | inr h₀ =>
    obtain ⟨a⟩ := h₀
    let k : K := ⟨h⁻¹ * (a.val : G) * y, a.property⟩
    have hy : y = (↑a.val⁻¹ : G) * h * k := by simp [k, mul_assoc]
    rw [hy]
    exact Finite.of_injective _ ((ClassTransporter.translate (K := K) a.val⁻¹ k).trans
      (ClassTransporter.selfEquiv h)).injective

section Construction

variable [CommSemiring 𝕜] [AddCommMonoid V] [Module 𝕜 V]
  (ρ : Representation 𝕜 Γ V) (χ : K →* 𝕜) (h : G)

private noncomputable def classFormValue (v : V) (y : G) : V :=
  ∑ᶠ a : ClassTransporter K Γ h y,
    χ ⟨h⁻¹ * (a.val : G) * y, a.property⟩ • ρ a.val⁻¹ v

private theorem classFormValue_translate (v : V) (g : Γ) (y : G) (k : K)
    [Finite (mackeySubgroup h K Γ)] :
    classFormValue ρ χ h v ((g : G) * y * k) = χ k • ρ g (classFormValue ρ χ h v y) := by
  classical
  have := ClassTransporter.finite (K := K) (Γ := Γ) (h := h) (y := y)
  -- Right multiplication by `g` reindexes the left transporters, and `k` rescales their weights.
  let e := ClassTransporter.translate (K := K) (h := h) (y := y) g k
  let := Fintype.ofFinite (ClassTransporter K Γ h y)
  unfold classFormValue
  rw [← finsum_comp_equiv e.symm]
  simp only [finsum_eq_sum_of_fintype, map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  have hk : (⟨h⁻¹ * ((e.symm a).val : G) * ((g : G) * y * k), (e.symm a).property⟩ : K) =
      ⟨h⁻¹ * (a.val : G) * y, a.property⟩ * k := by
    apply Subtype.ext
    simp [e, ClassTransporter.translate, mul_assoc]
  have hg : (e.symm a).val⁻¹ = g * a.val⁻¹ := by simp [e, ClassTransporter.translate]
  simp [hk, hg, mul_smul, smul_comm (χ k)]

/-- The class form of `v` at `h`, with right covariance by `χ`. Its values are sums over
`Γ`-translates of `v` whose arguments land in `h K`. Only the stabiliser at `h`
needs to be finite, not the class set. -/
noncomputable def classForm [Finite (mackeySubgroup h K Γ)] :
    V →ₗ[𝕜] weightSpace ((ρ.coind Γ.subtype).comp K.subtype) χ where
  toFun v :=
    ⟨⟨classFormValue ρ χ h v, fun g y ↦ by
        simpa using classFormValue_translate ρ χ h v g y 1⟩,
      mem_weightSpace_coind_comp_subtype_iff.mpr fun k y ↦ by
        simpa using classFormValue_translate ρ χ h v 1 y k⟩
  map_add' v w := by
    classical
    apply Subtype.ext
    apply Subtype.ext
    funext y
    have := ClassTransporter.finite (K := K) (Γ := Γ) (h := h) (y := y)
    have := Fintype.ofFinite (ClassTransporter K Γ h y)
    simp [classFormValue, finsum_eq_sum_of_fintype, smul_add, Finset.sum_add_distrib]
  map_smul' r v := by
    classical
    apply Subtype.ext
    apply Subtype.ext
    funext y
    have := ClassTransporter.finite (K := K) (Γ := Γ) (h := h) (y := y)
    have := Fintype.ofFinite (ClassTransporter K Γ h y)
    simp [classFormValue, finsum_eq_sum_of_fintype, Finset.smul_sum, smul_comm r]

/-- The class form is the sum over all `a ∈ Γ` with `h⁻¹ a y ∈ K`, with coefficient
`χ(h⁻¹ a y)` on the vector `ρ(a⁻¹)v`. -/
theorem classForm_apply [Finite (mackeySubgroup h K Γ)] (v : V) (y : G) :
    (ρ.classForm χ h v).val.val y =
      ∑ᶠ a : {γ : Γ // h⁻¹ * (γ : G) * y ∈ K},
        χ ⟨h⁻¹ * (a.val : G) * y, a.property⟩ • ρ a.val⁻¹ v := (rfl)

/-- The class form vanishes outside the double coset of its defining point. -/
theorem classForm_apply_eq_zero_of_mk_ne [Finite (mackeySubgroup h K Γ)] (v : V) {y : G}
    (hy : DoubleCoset.mk Γ K h ≠ DoubleCoset.mk Γ K y) :
    (ρ.classForm χ h v).val.val y = 0 := by
  have : IsEmpty {γ : Γ // h⁻¹ * (γ : G) * y ∈ K} := ⟨fun a ↦ hy (DoubleCoset.eq.mpr
    ⟨↑a.val⁻¹, Γ.inv_mem a.val.property, _, a.property, by simp [mul_assoc]⟩)⟩
  rw [classForm_apply, finsum_of_isEmpty]

end Construction

section Pairing

open scoped InnerProductSpace

variable [RCLike 𝕜] [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]
  (ρ : Representation 𝕜 Γ V) (χ : K →* 𝕜)
  (hρ : ∀ (g : Γ) (v w : V), ⟪ρ g v, ρ g w⟫_𝕜 = ⟪v, w⟫_𝕜)
  (hχ : ∀ k : K, ‖χ k‖ = 1)

include hρ hχ

private theorem inner_classForm_at_point (h : G) [Finite (mackeySubgroup h K Γ)]
    (v : V) (f : weightSpace ((ρ.coind Γ.subtype).comp K.subtype) χ) :
    ⟪(ρ.classForm χ h v).val.val h, f.val.val h⟫_𝕜 =
      (Nat.card (mackeySubgroup h K Γ) : 𝕜) * ⟪v, f.val.val h⟫_𝕜 := by
  classical
  have := ClassTransporter.finite (K := K) (Γ := Γ) (h := h) (y := h)
  let := Fintype.ofFinite (ClassTransporter K Γ h h)
  rw [classForm_apply, finsum_eq_sum_of_fintype, sum_inner]
  have heval (a : ClassTransporter K Γ h h) :
      let k : K := ⟨h⁻¹ * (a.val : G) * h, a.property⟩
      ρ a.val (f.val.val h) = χ k • f.val.val h := by
    intro k
    have hl := f.val.property a.val h
    have hr := mem_weightSpace_coind_comp_subtype_iff.mp f.property k h
    simpa [k] using hl.symm.trans (by simpa [k, mul_assoc] using hr)
  have hterm (a : ClassTransporter K Γ h h) :
      ⟪χ ⟨h⁻¹ * (a.val : G) * h, a.property⟩ • ρ a.val⁻¹ v, f.val.val h⟫_𝕜 =
        ⟪v, f.val.val h⟫_𝕜 := by
    rw [← hρ a.val, map_smul, ← mul_apply_eq_comp, ← map_mul, mul_inv_cancel, map_one,
      heval a, inner_smul_left, inner_smul_right, ← mul_assoc]
    simp [RCLike.conj_mul, hχ]
  simp_rw [hterm, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    ← Nat.card_eq_fintype_card, Nat.card_congr (ClassTransporter.selfEquiv h)]

/-- The stabiliser-weighted inner product against the class form of `v` at `h` is the inner
product of `v` with the value of the other form at `h`. The class set need not be finite. -/
theorem doubleCosetClassSum_inner_classForm (h : G) [Finite (mackeySubgroup h K Γ)]
    (v : V) (f : weightSpace ((ρ.coind Γ.subtype).comp K.subtype) χ) :
    doubleCosetClassSum Γ K (fun y ↦ ⟪(ρ.classForm χ h v).val.val y, f.val.val y⟫_𝕜) =
      ⟪v, f.val.val h⟫_𝕜 := by
  classical
  -- Use `h` itself to evaluate the only class where the integrand can be nonzero.
  let q₀ := DoubleCoset.mk Γ K h
  let c := Function.update (fun q : DoubleCoset.Quotient (Γ : Set G) K ↦ q.out) q₀ h
  have hc (q : DoubleCoset.Quotient (Γ : Set G) K) : DoubleCoset.mk Γ K (c q) = q := by
    by_cases hq : q = q₀ <;> simp [c, hq, q₀, DoubleCoset.out_eq']
  let u := ρ.classForm χ h v
  have hl (g : G) (hg : g ∈ Γ) (y : G) :
      ⟪u.val.val (g * y), f.val.val (g * y)⟫_𝕜 = ⟪u.val.val y, f.val.val y⟫_𝕜 := by
    have hu : u.val.val (g * y) = ρ ⟨g, hg⟩ (u.val.val y) := u.val.property ⟨g, hg⟩ y
    have hf : f.val.val (g * y) = ρ ⟨g, hg⟩ (f.val.val y) := f.val.property ⟨g, hg⟩ y
    rw [hu, hf, hρ]
  have hr (k : G) (hk : k ∈ K) (y : G) :
      ⟪u.val.val (y * k), f.val.val (y * k)⟫_𝕜 = ⟪u.val.val y, f.val.val y⟫_𝕜 := by
    rw [mem_weightSpace_coind_comp_subtype_iff.mp u.property ⟨k, hk⟩ y,
      mem_weightSpace_coind_comp_subtype_iff.mp f.property ⟨k, hk⟩ y,
      inner_smul_left, inner_smul_right, ← mul_assoc]
    simp [RCLike.conj_mul, hχ]
  rw [doubleCosetClassSum_eq_finsum hl hr c hc, finsum_eq_single _ q₀]
  · have hc₀ : c q₀ = h := Function.update_self _ _ _
    rw [hc₀, inner_classForm_at_point ρ χ hρ hχ, Algebra.smul_def, map_inv₀, map_natCast,
      ← mul_assoc, inv_mul_cancel₀ (Nat.cast_ne_zero.mpr Nat.card_pos.ne'), one_mul]
  · intro q hq
    have hne : DoubleCoset.mk Γ K h ≠ DoubleCoset.mk Γ K (c q) := by
      rw [hc q]
      exact hq.symm
    simp [classForm_apply_eq_zero_of_mk_ne ρ χ h v hne]

end Pairing

end Representation
