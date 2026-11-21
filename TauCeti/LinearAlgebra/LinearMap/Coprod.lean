/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Mathlib.LinearAlgebra.Prod

/-!
# Bijectivity of a coproduct of linear maps

The linear map `f.coprod g : M₁ × M₂ → M`, `(a, b) ↦ f a + g b`, is bijective exactly when `f`
and `g` are injective and their ranges are complementary submodules of `M`. This is the linear
algebra behind recognising an internal direct sum decomposition `M = range f ⊕ range g`, and
behind inverse-function-theorem arguments whose differential has the form `(a, b) ↦ f a + g b`.
For two vectors `a` and `b`, the map `(s, t) ↦ s • a - t • b` out of `R × R` is injective exactly
when `a` and `b` are linearly independent
(`LinearMap.injective_fst_smulRight_sub_snd_smulRight_iff`). Over a domain `R`, the vectors
`(1, c)` and `v` of `R × R` are linearly independent exactly when the determinant `v.2 - c * v.1`
is nonzero (`TauCeti.linearIndependent_pair_mk_one_iff`).
-/

public section

namespace LinearMap

section Bijective

variable {R M₁ M₂ M : Type*} [Semiring R] [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂]
  [Module R M₂] [AddCommGroup M] [Module R M]

/-- The map `(a, b) ↦ f a + g b` is bijective exactly when `f` and `g` are injective and the
ranges of `f` and `g` are complementary. -/
theorem bijective_coprod_iff {f : M₁ →ₗ[R] M} {g : M₂ →ₗ[R] M} :
    Function.Bijective (f.coprod g) ↔
      Function.Injective f ∧ Function.Injective g ∧ IsCompl (range f) (range g) := by
  refine ⟨fun h ↦ ⟨fun a b hab ↦ ?_, fun a b hab ↦ ?_, ⟨?_, ?_⟩⟩, fun ⟨hf, hg, hc⟩ ↦ ⟨?_, ?_⟩⟩
  · simpa using congrArg Prod.fst (h.1 (a₁ := (a, 0)) (a₂ := (b, 0)) (by simpa using hab))
  · simpa using congrArg Prod.snd (h.1 (a₁ := (0, a)) (a₂ := (0, b)) (by simpa using hab))
  · -- A common value `f a = g b` gives `f.coprod g (a, -b) = 0`, so `a = 0`.
    rw [Submodule.disjoint_def]
    rintro _ ⟨a, rfl⟩ ⟨b, hb⟩
    have ha : a = 0 := congrArg Prod.fst (h.1 (a₁ := (a, -b)) (a₂ := 0) (by simp [hb]))
    simp [ha]
  · rw [codisjoint_iff, ← range_coprod, range_eq_top]
    exact h.2
  · rw [injective_iff_map_eq_zero]
    rintro ⟨a, b⟩ hab
    have hk : (a, b) ∈ ker (f.coprod g) := hab
    rw [ker_coprod_of_disjoint_range f g hc.disjoint] at hk
    exact Prod.ext ((injective_iff_map_eq_zero f).1 hf a hk.1)
      ((injective_iff_map_eq_zero g).1 hg b hk.2)
  · rw [← range_eq_top, range_coprod, hc.sup_eq_top]

end Bijective

/-- The map `(s, t) ↦ s • a - t • b` out of `R × R` is injective exactly when `a` and `b` are
linearly independent. -/
theorem injective_fst_smulRight_sub_snd_smulRight_iff {R M : Type*} [Ring R] [AddCommGroup M]
    [Module R M] {a b : M} :
    Function.Injective ((fst R R R).smulRight a - (snd R R R).smulRight b) ↔
      LinearIndependent R ![a, b] := by
  refine ⟨fun h ↦ LinearIndependent.pair_iff.2 fun s t hst ↦ ?_, fun hab ↦ ?_⟩
  · have hp := h (a₁ := (s, -t)) (a₂ := 0) (by simpa [sub_eq_add_neg] using hst)
    exact ⟨congrArg Prod.fst hp, neg_eq_zero.1 (congrArg Prod.snd hp)⟩
  · refine (injective_iff_map_eq_zero _).2 fun p hp ↦ ?_
    have h := LinearIndependent.pair_iff.1 hab p.1 (-p.2) (by simpa [sub_eq_add_neg] using hp)
    exact Prod.ext h.1 (neg_eq_zero.1 h.2)

end LinearMap

namespace TauCeti

/-- Over a domain `R`, the vectors `(1, c)` and `v` of `R × R` are linearly independent exactly
when the determinant `v.2 - c * v.1` is nonzero: the case of
`LinearIndependent.pair_add_smul_add_smul_iff` for the standard basis. -/
theorem linearIndependent_pair_mk_one_iff {R : Type*} [CommRing R] [IsDomain R] {c : R}
    {v : R × R} : LinearIndependent R ![((1 : R), c), v] ↔ v.2 - c * v.1 ≠ 0 := by
  have hbasis : LinearIndependent R ![((1 : R), (0 : R)), ((0 : R), (1 : R))] :=
    LinearIndependent.pair_iff.2 fun s t hst ↦ by simpa [Prod.ext_iff] using hst
  have key := LinearIndependent.pair_add_smul_add_smul_iff (R := R)
    (x := ((1 : R), (0 : R))) (y := ((0 : R), (1 : R))) (1 : R) c v.1 v.2
  simp only [Prod.smul_mk, smul_eq_mul, mul_one, mul_zero, Prod.mk_add_mk, add_zero, zero_add,
    Prod.mk.eta, one_mul] at key
  rw [key]
  exact ⟨fun h ↦ sub_ne_zero.2 h.2, fun h ↦ ⟨hbasis, sub_ne_zero.1 h⟩⟩

end TauCeti
