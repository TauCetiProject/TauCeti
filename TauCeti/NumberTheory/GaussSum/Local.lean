/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.NumberTheory.GaussSum
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.Topology.Algebra.Ring.Basic
import TauCeti.Algebra.Group.AddChar.Reduction
import TauCeti.MeasureTheory.Group.OpenSubgroup.Basic
import TauCeti.MeasureTheory.Group.OpenSubgroup.FiniteQuotient
import TauCeti.NumberTheory.GaussSum.Basic
import TauCeti.RingTheory.Ideal.Span
import TauCeti.Topology.Algebra.Ring.Subring

/-!
# The tame local Gauss sum

Let `F` be a topological ring, such as a finite product of non-archimedean local fields, with an
open subring `O` (its integers) of measure one for an additive Haar measure `μ`, and a unit `ϖ` of
`F` lying in `O` (a product of uniformisers). Let `π : O →+* R` be a surjection onto a finite ring
with kernel `ϖ O`, for instance `O → O / ϖ O`. A multiplicative character `η` of `R` is primitive
if for every `a ≠ 0` some unit `1 + c a` has `η (1 + c a) ≠ 1`, and an additive character `ψ` of
`F` has conductor `O` if `ψ` is trivial on `t O` exactly when `t ∈ O`.

The local Gauss sum is the Fourier transform over `O` of `η ∘ π`. Since `x ↦ ψ (t x)` has level
`ϖ` on `O` exactly when `ϖ t ∈ O`, the integral vanishes unless `ϖ t ∈ O`, and is then the
average over `R` of a shifted Gauss sum of `η` against the primitive additive character
`π x ↦ ψ (ϖ⁻¹ x)` of `R`:

* `TauCeti.exists_setIntegral_mul_addChar_eq`: there is `γ` with `‖γ‖ ^ 2 = 1 / #R` such that
  `∫ x in O, η (π x) ψ (t x) dμ` is `γ η⁻¹ (π (ϖ t))` when `ϖ t ∈ O` and `0` otherwise.
* `TauCeti.exists_setIntegral_inv_mulChar_mul_addChar_eq`: the same for a character `χ` of `F`
  whose inverse on the units of `O` is inflated from `η`, with `π` a local homomorphism: the
  integral over `O` of `χ⁻¹ x 1_{O^×} (x) ψ (t x)` is `γ χ (ϖ t)` when `ϖ t` is a unit of `O`
  and `0` otherwise.

The finite part is the Gauss sum of a primitive character of a finite ring,
`MulChar.gaussSum_mulShift_eq_inv_mul_gaussSum`; the reduction of the integral to a finite sum is
`MeasureTheory.card_smul_setIntegral_eq_measureReal_smul_sum`. The reduced additive character is
`TauCeti.exists_isPrimitive_addChar_apply_eq`.

## References

* J. Tate, *Fourier analysis in number fields and Hecke's zeta-functions*, thesis (1950), §2.5.
* E. Lamprecht, *Allgemeine Theorie der Gaußschen Summen in endlichen kommutativen Ringen*,
  Math. Nachr. 9 (1953).
* K. Conrad, *Gauss and Jacobi sums on finite fields and `ℤ/mℤ`*, §4.

The statement and the route follow `New.Exchange.exists_local_gauss_sum` (file
`src/Lib/Weil/TameGaussSum.lean`) of the Lean formalization `grh-lean` of the Riemann hypothesis
for Dirichlet L-functions, https://github.com/lsernau/grh-lean (commit `72fead1`, Apache 2.0).
Here the integrand is any function equal to `η ∘ π` on `O`, and `O` need not be compact. No
separate continuity hypothesis on `ψ` is needed: the conductor condition makes `ψ` trivial on the
open subgroup `O`, hence locally constant.
-/

public section

open MeasureTheory

namespace TauCeti

variable {F R : Type*} [CommRing F] [CommRing R] {O : Subring F} {ϖ : Fˣ} {π : O →+* R}
  [TopologicalSpace F] [IsTopologicalRing F] [MeasurableSpace F] [BorelSpace F]
  {μ : Measure F} [μ.IsAddLeftInvariant] [Fintype R]

open scoped Classical in
/-- **The tame local Gauss sum.** Let `O` be an open subring of `F` of measure one, `ϖ` a unit of
`F` in `O`, and `π : O →+* R` a surjection onto a finite ring with kernel `ϖ O`. Let `η` be a
primitive multiplicative character of `R`, and `ψ` an additive character of `F` with conductor
`O`. Then there is `γ` with `‖γ‖ ^ 2 = 1 / #R` such that for every function `g` equal
to `η ∘ π` on `O` and every `t`, the integral of `g x ψ (t x)` over `O` is `γ η⁻¹ (π (ϖ t))`
when `ϖ t ∈ O`, and `0` otherwise. -/
theorem exists_setIntegral_mul_addChar_eq (hO : IsOpen (O : Set F)) (hμO : μ O = 1)
    (hϖ : (ϖ : F) ∈ O) (hπ : Function.Surjective π)
    (hker : RingHom.ker π = Ideal.span {⟨ϖ, hϖ⟩}) {η : MulChar R ℂ}
    (hη : ∀ a : R, a ≠ 0 → ∃ c : R, IsUnit (1 + c * a) ∧ η (1 + c * a) ≠ 1)
    {ψ : AddChar F ℂ} (hψ : ∀ t : F, (∀ x ∈ O, ψ (t * x) = 1) ↔ t ∈ O) :
    ∃ γ : ℂ, ‖γ‖ ^ 2 = (Fintype.card R : ℝ)⁻¹ ∧
      ∀ g : F → ℂ, (∀ x : O, g x = η (π x)) → ∀ t : F,
        ∫ x in (O : Set F), g x * ψ (t * x) ∂μ =
          if h : (ϖ : F) * t ∈ O then γ * η⁻¹ (π ⟨_, h⟩) else 0 := by
  obtain ⟨φ, hφ, hφψ⟩ := exists_isPrimitive_addChar_apply_eq hϖ hπ hker hψ
  have hshift := MulChar.gaussSum_mulShift_eq_inv_mul_gaussSum hη φ
  have hcard : (Fintype.card R : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  refine ⟨gaussSum η φ / Fintype.card R, ?_, fun g hg t ↦ ?_⟩
  · rw [norm_div, norm_gaussSum_of_forall_mulShift hshift hφ, div_pow,
      Real.sq_sqrt (Nat.cast_nonneg _), Complex.norm_natCast, sq, div_mul_eq_div_div,
      div_self hcard, one_div]
  split_ifs with h
  · -- on `O` the integrand is `η r φ (u r)` at `r = π x`, with `u = π (ϖ t)`
    set u := π ⟨_, h⟩ with hu
    have hfac (x : O) : g x * ψ (t * x) = η (π x) * φ (u * π x) := by
      rw [hg, hu, ← map_mul, hφψ]
      congr 2
      simp [mul_assoc]
    have hsum := card_smul_setIntegral_eq_measureReal_smul_sum (μ := μ) (H := O) hO
      (by simp [hμO]) (π := π.toAddMonoidHom) hπ (isLocallyConstant_of_ker_eq_span hO hϖ hker)
      (f := fun x ↦ g x * ψ (t * x)) (Φ := fun r ↦ η r * φ (u * r)) hfac
    have hgauss : ∑ r, η r * φ (u * r) = η⁻¹ u * gaussSum η φ := by
      rw [← hshift u]
      simp only [gaussSum, AddChar.mulShift_apply]
    rw [measureReal_def, hμO, ENNReal.toReal_one, one_smul, hgauss, nsmul_eq_mul] at hsum
    rw [div_mul_eq_mul_div, eq_div_iff (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)]
    linear_combination hsum
  · -- translating by `ϖ s` multiplies the integral by `ψ (ϖ t s)`, so it vanishes
    by_contra hne
    refine h ((hψ _).mp fun s hs ↦ ?_)
    have hϖs : (ϖ : F) * s ∈ O := O.mul_mem hϖ hs
    have htr := setIntegral_add_left_eq_self_of_mem (μ := μ) (fun x ↦ g x * ψ (t * x)) hϖs
    have hfac : ∫ x in (O : Set F), g ((ϖ : F) * s + x) * ψ (t * ((ϖ : F) * s + x)) ∂μ =
        ψ ((ϖ : F) * t * s) * ∫ x in (O : Set F), g x * ψ (t * x) ∂μ := by
      rw [← integral_const_mul]
      refine setIntegral_congr_fun hO.measurableSet fun x hx ↦ ?_
      have hπs : π ⟨_, hϖs⟩ = 0 := by
        rw [← RingHom.mem_ker, hker, mem_span_singleton_iff_inv_mul_mem]
        simpa using hs
      have hgx : g ((ϖ : F) * s + x) = g x := by
        rw [hg ⟨_, O.add_mem hϖs hx⟩, hg ⟨x, hx⟩]
        congr 1
        rw [← sub_eq_zero, ← map_sub]
        convert hπs using 2
        ext
        simp
      rw [hgx, mul_add, AddChar.map_add_eq_mul]
      ring_nf
    rw [htr] at hfac
    exact (mul_eq_right₀ hne).mp hfac.symm

open scoped Classical in
/-- **The tame local Gauss sum of a character of `F`.** In the setting of
`exists_setIntegral_mul_addChar_eq`, let `π` be a local homomorphism (as it is when `ϖ` lies in
the Jacobson radical of `O`), and let `χ` be a multiplicative character of `F` whose inverse on the
units of `O` is inflated from `η`. Then there is `γ` with `‖γ‖ ^ 2 = 1 / #R` such that for every
`t`, the integral over `O` of `χ⁻¹ x ψ (t x)`, cut off to the units of `O`, is `γ χ (ϖ t)` when
`ϖ t` is a unit of `O`, and `0` otherwise. -/
theorem exists_setIntegral_inv_mulChar_mul_addChar_eq [IsLocalHom π] (hO : IsOpen (O : Set F))
    (hμO : μ O = 1) (hϖ : (ϖ : F) ∈ O) (hπ : Function.Surjective π)
    (hker : RingHom.ker π = Ideal.span {⟨ϖ, hϖ⟩}) {η : MulChar R ℂ}
    (hη : ∀ a : R, a ≠ 0 → ∃ c : R, IsUnit (1 + c * a) ∧ η (1 + c * a) ≠ 1)
    {χ : MulChar F ℂ} (hχ : ∀ x : O, IsUnit x → η (π x) = χ⁻¹ x)
    {ψ : AddChar F ℂ} (hψ : ∀ t : F, (∀ x ∈ O, ψ (t * x) = 1) ↔ t ∈ O) :
    ∃ γ : ℂ, ‖γ‖ ^ 2 = (Fintype.card R : ℝ)⁻¹ ∧ ∀ t : F,
      ∫ x in (O : Set F), {x | ∃ h : x ∈ O, IsUnit (⟨x, h⟩ : O)}.indicator (⇑χ⁻¹) x *
          ψ (t * x) ∂μ =
        if ∃ h : (ϖ : F) * t ∈ O, IsUnit (⟨_, h⟩ : O) then γ * χ (ϖ * t) else 0 := by
  obtain ⟨γ, hγ, hint⟩ := exists_setIntegral_mul_addChar_eq (μ := μ) hO hμO hϖ hπ hker hη hψ
  refine ⟨γ, hγ, fun t ↦ ?_⟩
  rw [hint _ (fun x ↦ ?_) t]
  · split_ifs with h hu hu
    · rw [MulChar.inv_apply_eq_inv', hχ _ hu.2, MulChar.inv_apply_eq_inv', inv_inv]
    · rw [MulChar.map_nonunit _ (fun h' ↦ hu ⟨h, isUnit_of_map_unit π _ h'⟩), mul_zero]
    · exact absurd hu.1 h
    · rfl
  · rw [Set.indicator_apply]
    split_ifs with hx
    · rw [hχ x hx.2]
    · rw [MulChar.map_nonunit _ (fun h' ↦ hx ⟨x.property, isUnit_of_map_unit π _ h'⟩)]

end TauCeti
