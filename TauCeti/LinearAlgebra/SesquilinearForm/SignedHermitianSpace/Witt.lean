/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import TauCeti.LinearAlgebra.SesquilinearForm.SignedHermitianSpace
public import TauCeti.LinearAlgebra.SesquilinearForm.SignedHermitianSpace.Isometry
public import TauCeti.LinearAlgebra.SesquilinearForm.SignedHermitianSpace.OrthogonalBasis
import Mathlib.Tactic.LinearCombination

/-!
# Witt's extension and cancellation theorems for signed hermitian spaces

Let `K` be a field with an involution `σ` that is not the identity (for instance a separable
quadratic extension `E/F` with its Galois conjugation), and let `(V, h)` be a finite-dimensional
`ε`-hermitian space over `K`, `ε = ±1`. This file proves Witt's theorems for `(V, h)`, in every
characteristic and for both signs:

* **extension**: an isometry between two subspaces of `V`, nondegenerate or not, extends to an
  element of the unitary group `U(V)`, the isometry group of `h`; it can even be chosen as a
  product of quasi-reflections;
* **cancellation**: if `U ⊥ V ≅ U ⊥ V'`, then `V ≅ V'`.

For a unit `s` with `s + ε σ s = h v v`, the **quasi-reflection** along `v` is
`x ↦ x - s⁻¹ h v x • v`. It is an isometry of `h` fixing the hyperplane orthogonal to `v`; for
`h v v ≠ 0` these are the unitary reflections `x ↦ x + (λ - 1) h(v, v)⁻¹ h(v, x) v`, `λ σ λ = 1`,
and for isotropic `v` the unitary transvections. Every `c` with `σ c = ε c`, in particular every
`h v v`, has this form `s + ε σ s` because `σ` is not the identity
(`TauCeti.exists_units_add_smul_eq`); this is where the hypothesis on `σ` enters, and it replaces
the assumption `char K ≠ 2` of the orthogonal case.

The proof of extension moves the vectors of a basis one at a time, by at most two
quasi-reflections each, fixing the vectors already moved (Scharlau, Chapter 7, for
trace-valued forms; every hermitian form over a field with a nontrivial involution is
trace-valued). Cancellation follows: an isometry `U ⊥ V ≅ U ⊥ V'` is corrected by an element of
`U(U ⊥ V')` to one fixing `U` pointwise, which then carries `V = Uᗮ` onto `V' = Uᗮ`.

## Main definitions

* `TauCeti.SignedHermitianSpace.quasiReflection H v s hs`: the quasi-reflection along `v`.
* `TauCeti.SignedHermitianSpace.quasiReflectionSubgroup H`: the subgroup of `V ≃ₗ[K] V` generated
  by the quasi-reflections, contained in the unitary group.

## Main statements

* `TauCeti.SignedHermitianSpace.exists_mem_quasiReflectionSubgroup_apply_eq`: Witt's theorem for
  families: linearly independent families with the same Gram matrix differ by a product of
  quasi-reflections.
* `TauCeti.SignedHermitianSpace.exists_mem_isometryGroup_extend`: **Witt's extension theorem**.
* `TauCeti.SignedHermitianSpace.equivalent_of_equivalent_prod`,
  `TauCeti.SignedHermitianSpace.equivalent_prod_left_iff`: **Witt's cancellation theorem**.
* `TauCeti.exists_units_add_smul_eq`: every `c` with `σ c = ε c` is `s + ε σ s` for a unit `s`.

## Attribution

The quasi-reflections and the column-by-column proof of extension are adapted from grh-lean
(https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic, PBC), file
`src/Lib/Adelic/Witt/WittTheorem.lean`: `New.quasiReflection`, `New.exists_units_add_star_eq`,
`New.exists_quasiReflection_mulVec_eq`, `New.witt_of_quasiReflection_mem` and `New.witt`, where
they are stated for an invertible hermitian matrix over a field with a nontrivial `StarRing`
involution. Here they are restated for signed hermitian spaces of either sign with an explicit
involution, and cancellation is new.

## References

* W. Scharlau, *Quadratic and Hermitian Forms*, Grundlehren der mathematischen Wissenschaften
  270, Springer (1985), Chapter 7.
-/

public section

open Module

namespace TauCeti

variable {K : Type*} [Field K] {σ : K →+* K} {ε : ℤˣ}

/-- The sign `ε` acts on a field through its image `±1`. -/
private theorem units_smul_eq_mul (c : K) : ε • c = ((ε : ℤ) : K) * c := by
  rw [Units.smul_def, zsmul_eq_mul]

private theorem units_cast_sq : ((ε : ℤ) : K) ^ 2 = 1 := by
  rw [← Int.cast_pow, Int.isUnit_sq ε.isUnit, Int.cast_one]

/-- **Every `σ`-hermitian scalar is a trace.** Over a field whose involution `σ` is not the
identity, every `c` with `σ c = c` is `s + σ s` for a unit `s`. -/
theorem exists_units_add_eq [RingHomInvPair σ σ] (hσ : ∃ z, σ z ≠ z) {c : K} (hc : σ c = c) :
    ∃ s : Kˣ, (s : K) + σ s = c := by
  -- Take `s = z (c - σ z) / (z - σ z)`.
  obtain ⟨z, hz⟩ := hσ
  have hσσ (a : K) : σ (σ a) = a := RingHomInvPair.comp_apply_eq₂
  have hd : z - σ z ≠ 0 := sub_ne_zero.2 hz.symm
  have hz₀ : z ≠ 0 := fun h ↦ hz (by rw [h, map_zero])
  have hc₀ : c - σ z ≠ 0 := fun h ↦ hz <| by
    rw [sub_eq_zero.1 h] at hc
    rw [← hc, hσσ]
  refine ⟨Units.mk0 (z * (c - σ z) / (z - σ z)) (div_ne_zero (mul_ne_zero hz₀ hc₀) hd), ?_⟩
  have hd' : σ z - z ≠ 0 := sub_ne_zero.2 hz
  simp only [Units.val_mk0, map_div₀, map_mul, map_sub, hc, hσσ]
  field_simp
  ring

/-- **Every `ε`-hermitian scalar is an `ε`-trace.** Over a field whose involution `σ` is not the
identity, every `c` with `σ c = ε c` is `s + ε σ s` for a unit `s`. These are the parameters of the
quasi-reflections. -/
theorem exists_units_add_smul_eq [RingHomInvPair σ σ] (hσ : ∃ z, σ z ≠ z) {c : K}
    (hc : σ c = ε • c) : ∃ s : Kˣ, (s : K) + ε • σ s = c := by
  rcases Int.units_eq_one_or ε with rfl | rfl
  · simpa using exists_units_add_eq hσ (by simpa using hc)
  rw [Units.neg_smul, one_smul] at hc
  simp only [Units.neg_smul, one_smul, ← sub_eq_add_neg]
  by_cases hc₀ : c = 0
  · exact ⟨1, by simp [hc₀]⟩
  -- Otherwise `s = c u` with `u + σ u = 1`.
  obtain ⟨u, hu⟩ := exists_units_add_eq hσ (map_one σ)
  refine ⟨Units.mk0 c hc₀ * u, ?_⟩
  simp only [Units.val_mul, Units.val_mk0, map_mul, hc]
  linear_combination c * hu

namespace SignedHermitianSpace

variable {V : Type*} [AddCommGroup V] [Module K V] (H : SignedHermitianSpace K V σ ε)

/-! ### Quasi-reflections -/

/-- The linear map `x ↦ x - a h v x • v`. -/
private def quasiReflectionAux (v : V) (a : K) : V →ₗ[K] V :=
  LinearMap.id - (a • H.form v).smulRight v

private theorem quasiReflectionAux_apply (v : V) (a : K) (x : V) :
    H.quasiReflectionAux v a x = x - (a * H.form v x) • v := by
  simp [quasiReflectionAux]

/-- The quasi-reflections along `v` with parameters `a`, `b` are inverse to each other when
`a + b = a b h v v`. -/
private theorem quasiReflectionAux_comp (v : V) {a b : K} (hab : a + b = a * b * H.form v v)
    (x : V) : H.quasiReflectionAux v a (H.quasiReflectionAux v b x) = x := by
  have hv : H.form v (x - (b * H.form v x) • v) = H.form v x - b * H.form v x * H.form v v := by
    rw [map_sub, map_smul, smul_eq_mul]
  rw [quasiReflectionAux_apply, quasiReflectionAux_apply, hv, sub_sub, ← add_smul]
  convert sub_zero x
  convert zero_smul K v
  linear_combination H.form v x * hab

/-- The **quasi-reflection** along `v` with parameter a unit `s` such that `s + ε σ s = h v v`:
the isometry `x ↦ x - s⁻¹ h v x • v` of `(V, h)`. It fixes every vector orthogonal to `v`
(`quasiReflection_apply_of_form_eq_zero`). For `h v v ≠ 0` it is a unitary reflection, for
isotropic `v` a unitary transvection. -/
def quasiReflection (v : V) (s : Kˣ) (hs : (s : K) + ε • σ s = H.form v v) : V ≃ₗ[K] V :=
  have hss : σ (s : K)⁻¹ * σ s = 1 := by rw [← map_mul, inv_mul_cancel₀ s.ne_zero, map_one]
  have hab : (s : K)⁻¹ + ε • σ (s : K)⁻¹ = (s : K)⁻¹ * (ε • σ (s : K)⁻¹) * H.form v v := by
    rw [← hs, units_smul_eq_mul, units_smul_eq_mul]
    linear_combination (-((ε : ℤ) : K) * σ (s : K)⁻¹) * inv_mul_cancel₀ s.ne_zero +
      (-(s : K)⁻¹ * ((ε : ℤ) : K) ^ 2) * hss + (-(s : K)⁻¹) * units_cast_sq (K := K) (ε := ε)
  { H.quasiReflectionAux v (s : K)⁻¹ with
    invFun := H.quasiReflectionAux v (ε • σ (s : K)⁻¹)
    left_inv := H.quasiReflectionAux_comp v (by linear_combination hab)
    right_inv := H.quasiReflectionAux_comp v hab }

theorem quasiReflection_apply (v : V) (s : Kˣ) (hs : (s : K) + ε • σ s = H.form v v) (x : V) :
    H.quasiReflection v s hs x = x - ((s : K)⁻¹ * H.form v x) • v :=
  H.quasiReflectionAux_apply v _ x

/-- A quasi-reflection fixes the vectors orthogonal to its direction. -/
theorem quasiReflection_apply_of_form_eq_zero (v : V) (s : Kˣ)
    (hs : (s : K) + ε • σ s = H.form v v) {x : V} (hx : H.form v x = 0) :
    H.quasiReflection v s hs x = x := by
  rw [quasiReflection_apply, hx, mul_zero, zero_smul, sub_zero]

/-- A quasi-reflection is an isometry: it lies in the unitary group `U(V)`. -/
theorem quasiReflection_mem_isometryGroup (v : V) (s : Kˣ)
    (hs : (s : K) + ε • σ s = H.form v v) :
    H.quasiReflection v s hs ∈ H.form.isometryGroup := by
  refine LinearMap.mem_isometryGroup_iff.2 fun x y ↦ ?_
  have hss : σ (s : K)⁻¹ * σ s = 1 := by rw [← map_mul, inv_mul_cancel₀ s.ne_zero, map_one]
  have hxv : H.form x v = ε • σ (H.form v x) := H.form_swap v x
  simp only [quasiReflection_apply, map_sub, map_smulₛₗ, LinearMap.sub_apply,
    LinearMap.smul_apply, smul_eq_mul, map_mul, hxv, ← hs, RingHom.id_apply]
  rw [units_smul_eq_mul, units_smul_eq_mul]
  linear_combination (σ (H.form v x) * H.form v y * σ (s : K)⁻¹) * inv_mul_cancel₀ s.ne_zero +
    (σ (H.form v x) * H.form v y * ((ε : ℤ) : K) * (s : K)⁻¹) * hss

/-- The subgroup of `V ≃ₗ[K] V` generated by the quasi-reflections. -/
def quasiReflectionSubgroup : Subgroup (V ≃ₗ[K] V) :=
  Subgroup.closure {e | ∃ v s hs, H.quasiReflection v s hs = e}

theorem quasiReflection_mem_quasiReflectionSubgroup (v : V) (s : Kˣ)
    (hs : (s : K) + ε • σ s = H.form v v) :
    H.quasiReflection v s hs ∈ H.quasiReflectionSubgroup :=
  Subgroup.subset_closure ⟨v, s, hs, rfl⟩

/-- Products of quasi-reflections are isometries. -/
theorem quasiReflectionSubgroup_le_isometryGroup :
    H.quasiReflectionSubgroup ≤ H.form.isometryGroup :=
  (Subgroup.closure_le _).2 fun _ ⟨v, s, hs, he⟩ ↦ he ▸ H.quasiReflection_mem_isometryGroup v s hs

/-! ### Witt's extension theorem -/

/-- If `h p p = h q q` and `h q (q - p) ≠ 0`, a quasi-reflection along `p - q` sends `p` to `q`
and fixes every `w` with `h p w = h q w`. -/
theorem exists_quasiReflection_apply_eq {p q : V} (hpq : H.form p p = H.form q q)
    (hne : H.form q (q - p) ≠ 0) :
    ∃ s hs, H.quasiReflection (p - q) s hs p = q ∧
      ∀ w, H.form p w = H.form q w → H.quasiReflection (p - q) s hs w = w := by
  -- The parameter is `s = h q (q - p)`, which is also `h (p - q) p`.
  have hsp : H.form (p - q) p = H.form q (q - p) := by
    simp only [map_sub, LinearMap.sub_apply, hpq]
  have hs : (Units.mk0 _ hne : K) + ε • σ (Units.mk0 _ hne) = H.form (p - q) (p - q) := by
    have hq : H.form (p - q) q = ε • σ (H.form q (p - q)) := H.form_swap q (p - q)
    rw [Units.val_mk0, map_sub (H.form (p - q)) p q, hsp, hq, ← neg_sub p q, map_neg, map_neg,
      smul_neg]
    abel
  refine ⟨Units.mk0 _ hne, hs, ?_, fun w hw ↦ H.quasiReflection_apply_of_form_eq_zero _ _ _ ?_⟩
  · rw [quasiReflection_apply, hsp, Units.val_mk0, inv_mul_cancel₀ hne, one_smul, sub_sub_cancel]
  · rw [map_sub, LinearMap.sub_apply, hw, sub_self]

variable [FiniteDimensional K V]

/-- Through the form, the coordinate functionals of a linearly independent family are
represented: there is `u` with `h u (x i) = 1` for `i = j` and `0` otherwise. -/
theorem exists_form_apply_eq_ite [RingHomSurjective σ] {ι : Type*} [DecidableEq ι] {x : ι → V}
    (hx : LinearIndependent K x) (j : ι) :
    ∃ u, ∀ i, H.form u (x i) = if i = j then 1 else 0 := by
  obtain ⟨f, hf⟩ := LinearMap.exists_extend ((Finsupp.lapply j).comp hx.repr)
  obtain ⟨u, hu⟩ := H.form_bijective.2 f
  refine ⟨u, fun i ↦ ?_⟩
  have hi := LinearMap.congr_fun hf ⟨x i, Submodule.subset_span (Set.mem_range_self i)⟩
  rw [hu]
  simpa [hx.repr_eq_single i ⟨x i, _⟩ rfl, Finsupp.single_apply] using hi

variable [RingHomInvPair σ σ]

omit [RingHomInvPair σ σ] in
/-- If `x` and `y` are linearly independent and agree on `s ∌ j`, some `u` is orthogonal to the
`y i`, `i ∈ s`, but to neither `x j` nor `y j`: among the vectors `a`, `b` dual to `x j` and to
`y j`, and `a + b`, one serves. -/
private theorem exists_form_eq_zero_and_ne_zero [RingHomSurjective σ] {ι : Type*} {x y : ι → V}
    (hx : LinearIndependent K x) (hy : LinearIndependent K y) {s : Finset ι} {j : ι}
    (hj : j ∉ s) (hs : ∀ i ∈ s, x i = y i) :
    ∃ u, (∀ i ∈ s, H.form u (y i) = 0) ∧ H.form u (y j) ≠ 0 ∧ H.form u (x j) ≠ 0 := by
  classical
  obtain ⟨a, ha⟩ := H.exists_form_apply_eq_ite hx j
  obtain ⟨b, hb⟩ := H.exists_form_apply_eq_ite hy j
  have hsj (i) (hi : i ∈ s) : i ≠ j := fun h ↦ hj (h ▸ hi)
  have has (i) (hi : i ∈ s) : H.form a (y i) = 0 := by rw [← hs i hi, ha]; simp [hsj i hi]
  have hbs (i) (hi : i ∈ s) : H.form b (y i) = 0 := by simp [hb, hsj i hi]
  by_cases haj : H.form a (y j) ≠ 0
  · exact ⟨a, has, haj, by simp [ha]⟩
  by_cases hbj : H.form b (x j) ≠ 0
  · exact ⟨b, hbs, by simp [hb], hbj⟩
  push Not at haj hbj
  exact ⟨a + b, fun i hi ↦ by simp [has i hi, hbs i hi], by simp [haj, hb], by simp [hbj, ha]⟩

/-- One step of Witt's theorem: if `x` and `y` are linearly independent with the same Gram
matrix and agree on `s`, a product of quasi-reflections fixing the `y i`, `i ∈ s`, sends `x j` to
`y j`. It takes one quasi-reflection, or two when `h (y j) (y j - x j) = 0`. -/
private theorem exists_mem_quasiReflectionSubgroup_step (hσ : ∃ z, σ z ≠ z) {ι : Type*}
    {x y : ι → V} (hx : LinearIndependent K x) (hy : LinearIndependent K y)
    (hxy : ∀ i k, H.form (x i) (x k) = H.form (y i) (y k)) {s : Finset ι} {j : ι} (hj : j ∉ s)
    (hs : ∀ i ∈ s, x i = y i) :
    ∃ r ∈ H.quasiReflectionSubgroup, r (x j) = y j ∧ ∀ i ∈ s, r (y i) = y i := by
  classical
  have reflect (p : V) (hp : H.form p p = H.form (y j) (y j))
      (hps : ∀ i ∈ s, H.form p (y i) = H.form (y j) (y i)) (hne : H.form (y j) (y j - p) ≠ 0) :
      ∃ r ∈ H.quasiReflectionSubgroup, r p = y j ∧ ∀ i ∈ s, r (y i) = y i := by
    obtain ⟨t, ht, hp', hw⟩ := H.exists_quasiReflection_apply_eq hp hne
    exact ⟨_, H.quasiReflection_mem_quasiReflectionSubgroup _ t ht, hp',
      fun i hi ↦ hw _ (hps i hi)⟩
  have hxs (i) (hi : i ∈ s) : H.form (x j) (y i) = H.form (y j) (y i) := by rw [← hxy j i, hs i hi]
  by_cases hne : H.form (y j) (y j - x j) ≠ 0
  · exact reflect (x j) (hxy j j) hxs hne
  push Not at hne
  -- Otherwise first apply a quasi-reflection along some `u` orthogonal to the `y i`, `i ∈ s`, but
  -- to neither `x j` nor `y j`.
  obtain ⟨u, hus, huy, hux⟩ := H.exists_form_eq_zero_and_ne_zero hx hy hj hs
  obtain ⟨t, ht⟩ := exists_units_add_smul_eq hσ (H.apply_form_self u)
  have hρ := LinearMap.mem_isometryGroup_iff.1 (H.quasiReflection_mem_isometryGroup u t ht)
  have hρy (i) (hi : i ∈ s) : H.quasiReflection u t ht (y i) = y i :=
    H.quasiReflection_apply_of_form_eq_zero _ _ _ (hus i hi)
  -- After it, by `hne` only the term along `u` is left in `h (y j) (y j - ρ (x j))`.
  have hne' : H.form (y j) (y j - H.quasiReflection u t ht (x j)) ≠ 0 := by
    have hyu : H.form (y j) u = ε • σ (H.form u (y j)) := H.form_swap u (y j)
    have hsub : y j - H.quasiReflection u t ht (x j) =
        (y j - x j) + ((t : K)⁻¹ * H.form u (x j)) • u := by
      rw [quasiReflection_apply]
      abel
    rw [hsub, map_add, hne, zero_add, map_smul, smul_eq_mul, hyu, units_smul_eq_mul]
    have hε : ((ε : ℤ) : K) ≠ 0 := by
      intro h0
      simpa [h0] using units_cast_sq (K := K) (ε := ε)
    exact mul_ne_zero (mul_ne_zero (inv_ne_zero t.ne_zero) hux)
      (mul_ne_zero hε ((map_ne_zero σ).2 huy))
  obtain ⟨r, hr, hrx, hry⟩ := reflect (H.quasiReflection u t ht (x j)) (by rw [hρ, hxy])
    (fun i hi ↦ by
      calc H.form (H.quasiReflection u t ht (x j)) (y i)
          = H.form (H.quasiReflection u t ht (x j)) (H.quasiReflection u t ht (y i)) := by
            rw [hρy i hi]
        _ = H.form (y j) (y i) := by rw [hρ, hxs i hi]) hne'
  refine ⟨r * H.quasiReflection u t ht,
    mul_mem hr (H.quasiReflection_mem_quasiReflectionSubgroup u t ht), hrx, fun i hi ↦ ?_⟩
  rw [mul_apply_eq_comp, hρy i hi, hry i hi]

/-- **Witt's theorem for families.** Over a field whose involution `σ` is not the identity, let
`x` and `y` be linearly independent families in a finite-dimensional signed hermitian space with
the same Gram matrix, `h (x i) (x j) = h (y i) (y j)`. Then a product `g` of quasi-reflections
sends each `x i` to `y i`. -/
theorem exists_mem_quasiReflectionSubgroup_apply_eq (hσ : ∃ z, σ z ≠ z) {ι : Type*} [Finite ι]
    {x y : ι → V} (hx : LinearIndependent K x) (hy : LinearIndependent K y)
    (hxy : ∀ i j, H.form (x i) (x j) = H.form (y i) (y j)) :
    ∃ g ∈ H.quasiReflectionSubgroup, ∀ i, g (x i) = y i := by
  classical
  cases nonempty_fintype ι
  suffices ∀ s : Finset ι, ∃ g ∈ H.quasiReflectionSubgroup, ∀ i ∈ s, g (x i) = y i by
    obtain ⟨g, hg, h⟩ := this Finset.univ
    exact ⟨g, hg, fun i ↦ h i (Finset.mem_univ i)⟩
  intro s
  induction s using Finset.induction with
  | empty => exact ⟨1, one_mem _, by simp⟩
  | insert j s hj ih =>
    obtain ⟨g, hg, hgs⟩ := ih
    have hgU := LinearMap.mem_isometryGroup_iff.1 (H.quasiReflectionSubgroup_le_isometryGroup hg)
    obtain ⟨r, hr, hrj, hrs⟩ := H.exists_mem_quasiReflectionSubgroup_step hσ
      (x := fun i ↦ g (x i)) (hx.map' g.toLinearMap g.ker) hy (fun i k ↦ by rw [hgU, hxy]) hj hgs
    refine ⟨r * g, mul_mem hr hg, Finset.forall_mem_insert _ _ _ |>.2 ⟨hrj, fun i hi ↦ ?_⟩⟩
    rw [mul_apply_eq_comp, hgs i hi, hrs i hi]

/-- **Witt's extension theorem** (Scharlau, Chapter 7). Over a field whose involution
`σ` is not the identity, every isometry `f` from a subspace `W` of a finite-dimensional signed
hermitian space `(V, h)` into `V` extends to an element of the unitary group `U(V)`. The subspace
`W` may be degenerate. -/
theorem exists_mem_isometryGroup_extend (hσ : ∃ z, σ z ≠ z) {W : Submodule K V}
    (f : W →ₗ[K] V) (hf : Function.Injective f) (hff : ∀ x y, H.form (f x) (f y) = H.form x y) :
    ∃ g ∈ H.form.isometryGroup, ∀ x : W, g x = f x := by
  let b := Module.finBasis K W
  obtain ⟨g, hg, hgb⟩ := H.exists_mem_quasiReflectionSubgroup_apply_eq hσ
    (x := fun i ↦ (b i : V)) (y := fun i ↦ f (b i))
    (b.linearIndependent.map' W.subtype W.ker_subtype)
    (b.linearIndependent.map' f (LinearMap.ker_eq_bot.2 hf)) fun i j ↦ (hff _ _).symm
  refine ⟨g, H.quasiReflectionSubgroup_le_isometryGroup hg, fun x ↦ ?_⟩
  have : g.toLinearMap ∘ₗ W.subtype = f := b.ext fun i ↦ hgb i
  exact LinearMap.congr_fun this x

/-! ### Witt's cancellation theorem -/

section Cancellation

variable {V₀ V₁ V₂ : Type*} [AddCommGroup V₀] [Module K V₀] [AddCommGroup V₁] [Module K V₁]
  [AddCommGroup V₂] [Module K V₂] {H₀ : SignedHermitianSpace K V₀ σ ε}
  {H₁ : SignedHermitianSpace K V₁ σ ε} {H₂ : SignedHermitianSpace K V₂ σ ε}

omit [FiniteDimensional K V] [RingHomInvPair σ σ] in
/-- An isometry `U ⊥ V ≅ U ⊥ V'` fixing `U` pointwise carries `V = Uᗮ` into `V' = Uᗮ`. -/
private theorem fst_apply_zero_eq_zero (e : IsometryEquiv (H₀.prod H₁) (H₀.prod H₂))
    (he : ∀ a, e (a, 0) = (a, 0)) (b : V₁) : (e (0, b)).1 = 0 :=
  H₀.separatingRight _ fun a ↦ by simpa [he] using e.map_app (a, 0) (0, b)

omit [FiniteDimensional K V] [RingHomInvPair σ σ] in
/-- An isometry `U ⊥ V ≅ U ⊥ V'` fixing `U` pointwise restricts to an isometry `V ≅ V'`. -/
private theorem equivalent_of_isometryEquiv_prod_apply_zero
    (e : IsometryEquiv (H₀.prod H₁) (H₀.prod H₂)) (he : ∀ a, e (a, 0) = (a, 0)) :
    Equivalent H₁ H₂ := by
  have he' (a : V₀) : e.symm (a, 0) = (a, 0) := by
    conv_lhs => rw [← he a]
    exact e.symm_apply_apply _
  have h₁ (b : V₁) : (0, (e (0, b)).2) = e (0, b) :=
    Prod.ext (fst_apply_zero_eq_zero e he b).symm rfl
  have h₂ (d : V₂) : (0, (e.symm (0, d)).2) = e.symm (0, d) :=
    Prod.ext (fst_apply_zero_eq_zero e.symm he' d).symm rfl
  let φ : V₁ →ₗ[K] V₂ := LinearMap.snd K V₀ V₂ ∘ₗ e.toLinearMap ∘ₗ LinearMap.inr K V₀ V₁
  let ψ : V₂ →ₗ[K] V₁ := LinearMap.snd K V₀ V₁ ∘ₗ e.symm.toLinearMap ∘ₗ LinearMap.inr K V₀ V₂
  refine ⟨{ toFun := φ, invFun := ψ, map_add' := φ.map_add, map_smul' := φ.map_smul,
             left_inv := fun b ↦ ?_, right_inv := fun d ↦ ?_, map_app' := fun b b' ↦ ?_ }⟩
  · simp only [φ, ψ, LinearMap.comp_apply, LinearMap.inr_apply, LinearMap.snd_apply,
      LinearEquiv.coe_coe, IsometryEquiv.coe_toLinearEquiv, h₁, IsometryEquiv.symm_apply_apply]
  · simp only [φ, ψ, LinearMap.comp_apply, LinearMap.inr_apply, LinearMap.snd_apply,
      LinearEquiv.coe_coe, IsometryEquiv.coe_toLinearEquiv, h₂, IsometryEquiv.apply_symm_apply]
  · have := e.map_app (0, b) (0, b')
    rw [← h₁ b, ← h₁ b'] at this
    simpa [φ] using this

variable [FiniteDimensional K V₀] [FiniteDimensional K V₂]

/-- **Witt's cancellation theorem.** Over a field whose involution `σ` is not the identity, if
`U ⊥ V` and `U ⊥ V'` are isometric signed hermitian spaces, with `U` and `V'` finite-dimensional,
then `V` and `V'` are isometric. -/
theorem equivalent_of_equivalent_prod (hσ : ∃ z, σ z ≠ z)
    (h : Equivalent (H₀.prod H₁) (H₀.prod H₂)) : Equivalent H₁ H₂ := by
  obtain ⟨e⟩ := h
  -- Extend `(a, 0) ↦ e (a, 0)`, defined on `W = U ⊥ 0`, to some `g ∈ U(U ⊥ V')`.
  let W := LinearMap.ker (LinearMap.snd K V₀ V₂)
  have hW (w : W) : (w : V₀ × V₂) = ((w : V₀ × V₂).1, 0) := Prod.ext rfl w.property
  let f : W →ₗ[K] V₀ × V₂ :=
    e.toLinearMap ∘ₗ LinearMap.inl K V₀ V₁ ∘ₗ LinearMap.fst K V₀ V₂ ∘ₗ W.subtype
  have hf (w : W) : f w = e ((w : V₀ × V₂).1, 0) := rfl
  obtain ⟨g, hg, hgf⟩ := (H₀.prod H₂).exists_mem_isometryGroup_extend hσ f
    (fun w w' hww' ↦ Subtype.ext <| by
      rw [hW w, hW w']
      simpa [hf] using hww')
    (fun w w' ↦ by
      rw [hf, hf, e.map_app]
      conv_rhs => rw [hW w, hW w']
      simp)
  -- Then `g⁻¹ ∘ e` fixes `U` pointwise.
  refine equivalent_of_isometryEquiv_prod_apply_zero
    (e.trans (IsometryEquiv.ofMemIsometryGroup (inv_mem hg))) fun a ↦ ?_
  have hga := hgf ⟨(a, 0), rfl⟩
  rw [hf] at hga
  rw [IsometryEquiv.trans_apply, IsometryEquiv.ofMemIsometryGroup_apply, ← hga]
  exact g.symm_apply_apply _

/-- **Witt's cancellation theorem**, as an equivalence: over a field whose involution is not the
identity, `U ⊥ V ≅ U ⊥ V'` if and only if `V ≅ V'`. -/
theorem equivalent_prod_left_iff (hσ : ∃ z, σ z ≠ z) :
    Equivalent (H₀.prod H₁) (H₀.prod H₂) ↔ Equivalent H₁ H₂ :=
  ⟨equivalent_of_equivalent_prod hσ, (Equivalent.refl H₀).prod⟩

end Cancellation

end SignedHermitianSpace

end TauCeti
