/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.BilinearForm.Hom
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import Mathlib.LinearAlgebra.PerfectPairing.Basic
public import Mathlib.RingTheory.LocalRing.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import TauCeti.LinearAlgebra.PerfectPairing.Basis
import TauCeti.LinearAlgebra.BilinearForm.Diagonalization
import TauCeti.LinearAlgebra.BilinearForm.Orthogonal

/-!
# Modular bilinear forms

A bilinear form `B` is `a`-modular when it is `a` times a perfect pairing
(`LinearMap.BilinForm.IsModular`). For a lattice over a discrete valuation ring with uniformizer
`π`, a `π^i`-modular form is one of scale `π^i` whose dual lattice is `π^{-i}` times the lattice;
`1`-modular forms are the unimodular ones. The modular forms are the constituents of a Jordan
splitting.

This file proves the facts about modular forms that hold over every commutative ring:

* when `a` is a non-zero-divisor, `a`-modularity is characterized by divisibility of all values
  by `a`, left separation, and the representability of `a f` for each linear functional `f`
  (`LinearMap.BilinForm.isModular_iff`);
* the orthogonal sum of two `a`-modular submodules is `a`-modular
  (`LinearMap.BilinForm.IsModular.restrict_sup`);
* an `a`-modular submodule splits off orthogonally when `a` divides every value of the form
  (`LinearMap.BilinForm.IsModular.isCompl_orthogonal`).

A family whose Gram matrix is `a` times a matrix of unit determinant spans an `a`-modular
submodule (`LinearMap.BilinForm.isModular_restrict_span_range`). Over a local ring, a pairing
`B u w` which is a non-zero-divisor dividing every value of a symmetric form therefore gives a
`B u w`-modular orthogonal summand inside the span of `u` and `w`
(`LinearMap.BilinForm.IsSymm.exists_isModular_restrict_isCompl_orthogonal`): either `B u u` or
`B w w` is `B u w` times a unit, or `u` and `w` span a binary summand whose Gram matrix is `B u w`
times a matrix of unit determinant. No inverse of `2` is needed; this is the splitting step of
the Jordan decomposition at a dyadic prime, where rank-two constituents such as the hyperbolic
plane cannot be diagonalized.

## Main definitions

* `LinearMap.BilinForm.IsModular`: `B` is `a` times a perfect pairing.

## References

* O. T. O'Meara, *Introduction to Quadratic Forms*, §82E and 91C.
* J. W. S. Cassels, *Rational Quadratic Forms*, Chapter 8, Lemma 4.1.
-/

public section

namespace LinearMap.BilinForm

open LinearMap (BilinForm)
open Module Matrix

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {B : BilinForm R M} {a : R}

/-- If `a` is a non-zero-divisor dividing every value of `B`, then `B` is `a` times a bilinear
form. -/
theorem exists_smul_eq_of_forall_dvd (ha : a ∈ nonZeroDivisors R) (h : ∀ x y, a ∣ B x y) :
    ∃ C : BilinForm R M, a • C = B := by
  choose c hc using h
  have hcan : ∀ r s, a * r = a * s → r = s := fun r s ↦ (mul_cancel_left_mem_nonZeroDivisors ha).mp
  refine ⟨LinearMap.mk₂ R c (fun x₁ x₂ y ↦ hcan _ _ ?_) (fun r x y ↦ hcan _ _ ?_)
    (fun x y₁ y₂ ↦ hcan _ _ ?_) (fun r x y ↦ hcan _ _ ?_), ?_⟩
  · rw [← hc, mul_add, ← hc, ← hc, map_add, LinearMap.add_apply]
  · rw [← hc, smul_eq_mul, mul_left_comm, ← hc, map_smul, smul_apply, smul_eq_mul]
  · rw [← hc, mul_add, ← hc, ← hc, map_add]
  · rw [← hc, smul_eq_mul, mul_left_comm, ← hc, map_smul, smul_eq_mul]
  · ext x y
    simp [hc]

/-- A bilinear form `B` is **`a`-modular** when it is `a` times a perfect pairing: `B = a • C`
for a form `C` identifying `M` with its dual on both sides. Over a discrete valuation ring with
uniformizer `π`, a `π ^ i`-modular lattice is one of scale `π ^ i` whose dual lattice is
`π ^ (-i)` times the lattice, and the `1`-modular forms are the unimodular ones. -/
def IsModular (B : BilinForm R M) (a : R) : Prop :=
  ∃ C : BilinForm R M, a • C = B ∧ C.IsPerfPair

/-- A form is `1`-modular exactly when it is a perfect pairing. -/
@[simp]
theorem isModular_one_iff : B.IsModular 1 ↔ B.IsPerfPair :=
  ⟨fun ⟨C, hC, h⟩ ↦ (one_smul R C).symm.trans hC ▸ h, fun h ↦ ⟨B, one_smul R B, h⟩⟩

/-- Every value of an `a`-modular form is divisible by `a`. -/
theorem IsModular.dvd (h : B.IsModular a) (x y : M) : a ∣ B x y := by
  obtain ⟨C, rfl, -⟩ := h
  exact ⟨C x y, by simp⟩

/-- Modularity only depends on `a` up to a unit. -/
theorem IsModular.of_associated (h : B.IsModular a) {b : R} (hab : Associated a b) :
    B.IsModular b := by
  obtain ⟨C, rfl, hC⟩ := h
  obtain ⟨u, rfl⟩ := hab
  have hbij : ∀ D : M →ₗ[R] M →ₗ[R] R, Function.Bijective D →
      Function.Bijective ((↑u⁻¹ : R) • D) := fun D hD ↦
    (LinearEquiv.smulOfUnit (M := Dual R M) u⁻¹).bijective.comp hD
  refine ⟨(↑u⁻¹ : R) • C, by rw [smul_smul, mul_assoc, Units.mul_inv, mul_one],
    ⟨hbij C hC.bijective_left, ?_⟩⟩
  have hflip : LinearMap.flip ((↑u⁻¹ : R) • C) = (↑u⁻¹ : R) • LinearMap.flip C := by
    ext x y
    simp
  rw [hflip]
  exact hbij _ hC.bijective_right

/-- An `a`-modular form with `a` a non-zero-divisor is nondegenerate. -/
theorem IsModular.nondegenerate (h : B.IsModular a) (ha : a ∈ nonZeroDivisors R) :
    B.Nondegenerate := by
  obtain ⟨C, rfl, hC⟩ := h
  refine ⟨fun x hx ↦ hC.nondegenerate.1 x fun y ↦ ?_, fun y hy ↦ hC.nondegenerate.2 y fun x ↦ ?_⟩
  · simpa [mul_comm a, mul_right_mem_nonZeroDivisors_eq_zero_iff ha] using hx y
  · simpa [mul_comm a, mul_right_mem_nonZeroDivisors_eq_zero_iff ha] using hy x

/-- A form on a subsingleton module is `a`-modular for every `a`. -/
theorem isModular_of_subsingleton [Subsingleton M] : B.IsModular a := by
  have : Subsingleton (Dual R M) := ⟨fun f g ↦ LinearMap.ext fun x ↦ by
    rw [Subsingleton.elim x 0, map_zero, map_zero]⟩
  refine ⟨0, Subsingleton.elim _ _, ⟨?_, ?_⟩⟩ <;>
    exact ⟨fun x y _ ↦ Subsingleton.elim x y, fun f ↦ ⟨0, Subsingleton.elim _ _⟩⟩

/-- Modularity is transported along a linear equivalence of the underlying modules. -/
theorem IsModular.congr {M' : Type*} [AddCommGroup M'] [Module R M'] (h : B.IsModular a)
    (e : M ≃ₗ[R] M') : (congr e B).IsModular a := by
  obtain ⟨C, rfl, hC⟩ := h
  refine ⟨congr e C, (map_smul (congr e) a C).symm, ?_⟩
  exact LinearMap.IsPerfPair.congr C e.symm e.symm _ (LinearMap.ext₂ fun x y ↦ by simp)

/-- Modularity is invariant under a linear equivalence of the underlying modules. -/
@[simp]
theorem isModular_congr_iff {M' : Type*} [AddCommGroup M'] [Module R M'] (e : M ≃ₗ[R] M') :
    (congr e B).IsModular a ↔ B.IsModular a :=
  ⟨fun h ↦ by
    simpa only [congr_congr, e.self_trans_symm, congr_refl, LinearEquiv.refl_apply] using
      h.congr e.symm, fun h ↦ h.congr e⟩

/-- Modularity of a restriction to a submodule of a submodule is modularity of the restriction to
its image in the ambient module. -/
@[simp]
theorem isModular_restrict_map_subtype_iff {P : Submodule R M} {K : Submodule R P} :
    (B.restrict (K.map P.subtype)).IsModular a ↔ ((B.restrict P).restrict K).IsModular a := by
  let e := Submodule.equivMapOfInjective P.subtype P.injective_subtype K
  rw [← isModular_congr_iff e]
  refine Iff.of_eq (congrArg (IsModular · a) (LinearMap.ext₂ fun x y ↦ ?_))
  obtain ⟨x, rfl⟩ := e.surjective x
  obtain ⟨y, rfl⟩ := e.surjective y
  simp [e]

/-- **Characterization of modular symmetric forms.** For a non-zero-divisor `a`, a symmetric form
is `a`-modular exactly when `a` divides all of its values, it is left-separating, and `a f` is
represented by a vector for every linear functional `f`. -/
theorem isModular_iff (hB : B.IsSymm) (ha : a ∈ nonZeroDivisors R) :
    B.IsModular a ↔ (∀ x y, a ∣ B x y) ∧ (∀ x, (∀ y, B x y = 0) → x = 0) ∧
      ∀ f : Dual R M, ∃ x, ∀ y, B x y = a * f y := by
  have hcan : ∀ r s, a * r = a * s → r = s := fun r s ↦ (mul_cancel_left_mem_nonZeroDivisors ha).mp
  constructor
  · intro h
    refine ⟨h.dvd, (h.nondegenerate ha).1, fun f ↦ ?_⟩
    obtain ⟨C, rfl, hC⟩ := h
    obtain ⟨x, hx⟩ := hC.bijective_left.2 f
    exact ⟨x, fun y ↦ by rw [smul_apply, smul_apply, smul_eq_mul, hx]⟩
  · rintro ⟨hdvd, hsep, hrep⟩
    obtain ⟨C, rfl⟩ := exists_smul_eq_of_forall_dvd ha hdvd
    have hbij : Function.Bijective C := by
      refine ⟨(injective_iff_map_eq_zero C).mpr fun x hx ↦ hsep x fun y ↦ ?_, fun f ↦ ?_⟩
      · simp [hx]
      · obtain ⟨x, hx⟩ := hrep f
        exact ⟨x, LinearMap.ext fun y ↦ hcan _ _ (by simpa using hx y)⟩
    have hflip : C.flip = C := LinearMap.ext₂ fun x y ↦ hcan _ _ (by
      simpa using hB.eq y x)
    exact ⟨C, rfl, ⟨hbij, hflip ▸ hbij⟩⟩

/-- **Orthogonal sums of modular forms are modular.** If two orthogonal submodules carry
`a`-modular restrictions of a symmetric form, with `a` a non-zero-divisor, so does their sum. -/
theorem IsModular.restrict_sup (hB : B.IsSymm) (ha : a ∈ nonZeroDivisors R)
    {S T : Submodule R M} (hS : (B.restrict S).IsModular a) (hT : (B.restrict T).IsModular a)
    (hST : ∀ x ∈ S, ∀ y ∈ T, B x y = 0) : (B.restrict (S ⊔ T)).IsModular a := by
  have hTS : ∀ y ∈ T, ∀ x ∈ S, B y x = 0 := fun y hy x hx ↦ by rw [hB.eq, hST x hx y hy]
  obtain ⟨dS, sepS, repS⟩ := (isModular_iff (hB.restrict S) ha).mp hS
  obtain ⟨dT, sepT, repT⟩ := (isModular_iff (hB.restrict T) ha).mp hT
  -- On `S ⊔ T` the form is the sum of its values on the two summands.
  have hsplit : ∀ s ∈ S, ∀ t ∈ T, ∀ s' ∈ S, ∀ t' ∈ T,
      B (s + t) (s' + t') = B s s' + B t t' := fun s hs t ht s' hs' t' ht' ↦ by
    simp [hST s hs t' ht', hTS t ht s' hs']
  refine (isModular_iff (hB.restrict _) ha).mpr ⟨fun x y ↦ ?_, fun x hx ↦ ?_, fun f ↦ ?_⟩
  · obtain ⟨s, hs, t, ht, hx⟩ := Submodule.mem_sup.mp x.2
    obtain ⟨s', hs', t', ht', hy⟩ := Submodule.mem_sup.mp y.2
    have := dvd_add (dS ⟨s, hs⟩ ⟨s', hs'⟩) (dT ⟨t, ht⟩ ⟨t', ht'⟩)
    simp only [restrict_apply, domRestrict_apply] at this ⊢
    rwa [← hx, ← hy, hsplit s hs t ht s' hs' t' ht']
  · obtain ⟨s, hs, t, ht, hst⟩ := Submodule.mem_sup.mp x.2
    have h0 : ∀ y ∈ S ⊔ T, B x y = 0 := fun y hy ↦ by simpa using hx ⟨y, hy⟩
    have hs0 : s = 0 := congrArg Subtype.val (sepS ⟨s, hs⟩ fun y ↦ by
      simpa [← hst, hTS t ht y y.2] using h0 y (Submodule.mem_sup_left y.2))
    have ht0 : t = 0 := congrArg Subtype.val (sepT ⟨t, ht⟩ fun y ↦ by
      simpa [← hst, hST s hs y y.2] using h0 y (Submodule.mem_sup_right y.2))
    exact Subtype.ext (by simp [← hst, hs0, ht0])
  · obtain ⟨s, hs⟩ := repS (f ∘ₗ Submodule.inclusion le_sup_left)
    obtain ⟨t, ht⟩ := repT (f ∘ₗ Submodule.inclusion le_sup_right)
    refine ⟨⟨s + t, Submodule.add_mem_sup s.2 t.2⟩, fun y ↦ ?_⟩
    obtain ⟨s', hs', t', ht', hy⟩ := Submodule.mem_sup.mp y.2
    have hy' : y = Submodule.inclusion le_sup_left ⟨s', hs'⟩ +
        Submodule.inclusion le_sup_right ⟨t', ht'⟩ := Subtype.ext hy.symm
    have h1 := hs ⟨s', hs'⟩
    have h2 := ht ⟨t', ht'⟩
    simp only [restrict_apply, domRestrict_apply, LinearMap.comp_apply] at h1 h2 ⊢
    rw [← hy, hsplit s s.2 t t.2 s' hs' t' ht', h1, h2, ← mul_add, ← map_add, ← hy']

/-- **A modular submodule splits off.** If a non-zero-divisor `a` divides every value of a
symmetric form `B` and the restriction of `B` to `S` is `a`-modular, then `S` is complementary to
its orthogonal complement. -/
theorem IsModular.isCompl_orthogonal (hB : B.IsSymm) (ha : a ∈ nonZeroDivisors R)
    (hdvd : ∀ x y, a ∣ B x y) {S : Submodule R M} (h : (B.restrict S).IsModular a) :
    IsCompl S (B.orthogonal S) := by
  have hcan : ∀ r s, a * r = a * s → r = s := fun r s ↦ (mul_cancel_left_mem_nonZeroDivisors ha).mp
  obtain ⟨B', rfl⟩ := exists_smul_eq_of_forall_dvd ha hdvd
  obtain ⟨C, hC, hCp⟩ := h
  have hCB : C = B'.restrict S := LinearMap.ext₂ fun x y ↦ hcan _ _ (by
    simpa using congrArg (fun D : BilinForm R S ↦ D x y) hC)
  have hB' : (B'.restrict S).IsSymm := ⟨fun x y ↦ hcan _ _ (by simpa using hB.eq x y)⟩
  have horth : (a • B').orthogonal S = B'.orthogonal S := by
    ext m
    simp only [mem_orthogonal_iff, smul_apply, smul_eq_mul]
    exact forall₂_congr fun n _ ↦ by
      rw [mul_comm, mul_right_mem_nonZeroDivisors_eq_zero_iff ha]
  rw [horth]
  exact B'.isCompl_orthogonal_of_restrict_bijective S hB' (hCB ▸ hCp.bijective_left)

/-- If the Gram matrix of a finite family `v` is `a` times a matrix of unit determinant, with `a` a
non-zero-divisor, then `v` is linearly independent. -/
theorem linearIndependent_of_isUnit_det {ι : Type*} [Fintype ι] [DecidableEq ι] {v : ι → M}
    {G : Matrix ι ι R} (ha : a ∈ nonZeroDivisors R) (hG : ∀ i j, B (v i) (v j) = a * G i j)
    (hdet : IsUnit G.det) : LinearIndependent R v := by
  refine Fintype.linearIndependent_iff.mpr fun g hg ↦ ?_
  have hgG : g ᵥ* G = 0 := funext fun j ↦ (mul_cancel_left_mem_nonZeroDivisors ha).mp (by
    have := congrArg (fun x ↦ B x (v j)) hg
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, hG,
      map_zero, LinearMap.zero_apply] at this
    rw [Pi.zero_apply, mul_zero, ← this, vecMul, dotProduct, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ ↦ by ring)
  have : g = g ᵥ* G ᵥ* G⁻¹ := by
    rw [vecMul_vecMul, mul_nonsing_inv _ hdet, vecMul_one]
  intro i
  rw [this, hgG, zero_vecMul, Pi.zero_apply]

/-- **A Gram block of unit determinant spans a modular submodule.** If the Gram matrix of a finite
family `v` is `a` times a matrix of unit determinant, with `a` a non-zero-divisor, then the
restriction of `B` to the span of `v` is `a`-modular. -/
theorem isModular_restrict_span_range {ι : Type*} [Fintype ι] [DecidableEq ι] {v : ι → M}
    {G : Matrix ι ι R} (ha : a ∈ nonZeroDivisors R) (hG : ∀ i j, B (v i) (v j) = a * G i j)
    (hdet : IsUnit G.det) : (B.restrict (Submodule.span R (Set.range v))).IsModular a := by
  let b := Basis.span (linearIndependent_of_isUnit_det ha hG hdet)
  have hb : ∀ i j, B.restrict _ (b i) (b j) = a * G i j := fun i j ↦ by
    simp [b, Basis.span_apply, hG]
  obtain ⟨C, hC⟩ := exists_smul_eq_of_forall_dvd ha
    (dvd_apply_of_forall_dvd_basis b fun i j ↦ ⟨G i j, hb i j⟩)
  have hCG : LinearMap.toMatrix₂ b b C = G := Matrix.ext fun i j ↦
    (mul_cancel_left_mem_nonZeroDivisors ha).mp (by
      rw [LinearMap.toMatrix₂_apply, ← hb, ← hC]
      simp)
  exact ⟨C, hC, b.isPerfPair_of_isUnit_det C (hCG ▸ hdet)⟩

/-- **The splitting step of the Jordan decomposition.** Over a local ring, let `B u w` be a
non-zero-divisor dividing every value of a symmetric form `B`. Then some nonzero submodule of the
span of `u` and `w` is `B u w`-modular and complementary to its orthogonal complement. No inverse
of `2` is needed: when neither `B u u` nor `B w w` is `B u w` times a unit, the summand is the
binary one spanned by `u` and `w`. -/
theorem IsSymm.exists_isModular_restrict_isCompl_orthogonal [IsLocalRing R] (hB : B.IsSymm)
    {u w : M} (hd : B u w ∈ nonZeroDivisors R) (hdvd : ∀ x y, B u w ∣ B x y) :
    ∃ S : Submodule R M, S ≠ ⊥ ∧ S ≤ Submodule.span R {u, w} ∧
      (B.restrict S).IsModular (B u w) ∧ IsCompl S (B.orthogonal S) := by
  -- A family whose Gram matrix is `B u w` times a matrix of unit determinant spans the summand.
  have key : ∀ {n : ℕ} (v : Fin (n + 1) → M) (G : Matrix (Fin (n + 1)) (Fin (n + 1)) R),
      (∀ i, v i ∈ ({u, w} : Set M)) → (∀ i j, B (v i) (v j) = B u w * G i j) → IsUnit G.det →
      ∃ S : Submodule R M, S ≠ ⊥ ∧ S ≤ Submodule.span R {u, w} ∧
        (B.restrict S).IsModular (B u w) ∧ IsCompl S (B.orthogonal S) := fun v G hv hG hdet ↦ by
    have hmod := isModular_restrict_span_range hd hG hdet
    refine ⟨_, fun h ↦ (linearIndependent_of_isUnit_det hd hG hdet).ne_zero 0
      ((Submodule.eq_bot_iff _).mp h _ (Submodule.subset_span (Set.mem_range_self 0))),
      Submodule.span_mono (Set.range_subset_iff.mpr hv), hmod,
      hmod.isCompl_orthogonal hB hd hdvd⟩
  obtain ⟨s, hs⟩ := hdvd u u
  obtain ⟨t, ht⟩ := hdvd w w
  by_cases hsu : IsUnit s
  · exact key ![u] !![s] (fun i ↦ by fin_cases i; simp)
      (fun i j ↦ by fin_cases i; fin_cases j; simpa using hs) (by simpa using hsu)
  by_cases htu : IsUnit t
  · exact key ![w] !![t] (fun i ↦ by fin_cases i; simp)
      (fun i j ↦ by fin_cases i; fin_cases j; simpa using ht) (by simpa using htu)
  -- Both `s` and `t` are nonunits, so `s * t - 1` is a unit.
  have hunit : IsUnit (s * t - 1) := by
    have h := IsLocalRing.isUnit_one_sub_self_of_mem_nonunits (s * t)
      (mem_nonunits_iff.mpr fun h ↦ hsu (isUnit_of_mul_isUnit_left h))
    rw [← neg_sub]
    exact h.neg
  refine key ![u, w] !![s, 1; 1, t] (fun i ↦ by fin_cases i <;> simp) (fun i j ↦ ?_)
    (by simpa [det_fin_two] using hunit)
  fin_cases i <;> fin_cases j <;> simp [hs, ht, hB.eq w u]

end LinearMap.BilinForm
