/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.DedekindDomain.Different
public import Mathlib.RingTheory.Finiteness.Projective
public import TauCeti.RingTheory.Localization.Finiteness
public import TauCeti.RingTheory.NormTrace.BaseChange

/-!
# Trace-dual families of a projective extension

Let `A` be a domain with fraction field `K`, let `L / K` be a finite separable extension, and let
`B` be the integral closure of `A` in `L`. Every `A`-linear form `B → A` is the restriction of a
trace pairing `x ↦ Tr_{L/K}(y x)`, and the element `y` then lies in the trace dual
`Bᵛ = {y ∈ L | Tr_{L/K}(y B) ⊆ A}`.

When `B` is moreover a finite projective `A`-module, as it is over a Dedekind domain, there is a
finite trace-dual family `bᵢ ∈ B` and `yᵢ ∈ Bᵛ` satisfying

`x = ∑ᵢ Tr_{L/K}(x bᵢ) yᵢ` for every `x ∈ L`.

This identity, together with integrality of the trace pairing on `A₀ ⊗[A] B`
(`TauCeti.trace_baseChangeOfTower_mul_mem`), is used to compare trace duals after extending scalars,
in particular when comparing a global or local different with the different of a completed
extension.

## Main results

* `TauCeti.exists_trace_mul_algebraMap_eq`: every `A`-linear form on `B` is a trace pairing.
* `TauCeti.exists_sum_trace_mul_smul_eq`: a projective integral closure has a finite trace-dual
  family `(bᵢ, yᵢ)` with `bᵢ ∈ B`, `yᵢ ∈ Bᵛ` and `x = ∑ᵢ Tr(x bᵢ) yᵢ`.
* `TauCeti.trace_baseChangeOfTower_mul_mem`: on the image of `A₀ ⊗[R] B` in `A ⊗[K] L`, the trace
  pairing with an element of `Submodule.traceDual R K 1` takes values in `A₀`.

## References

* [J. Neukirch, *Algebraic Number Theory*][Neukirch1992], Chapter III, §2.
-/

public section

open Module

open scoped nonZeroDivisors TensorProduct

namespace TauCeti

section DualFamily

variable (A K : Type*) {L B : Type*} [CommRing A] [Field K] [CommRing B] [Field L]
  [Algebra A K] [Algebra B L] [Algebra A B] [Algebra K L] [Algebra A L]
  [IsScalarTower A K L] [IsScalarTower A B L]
  [IsDomain A] [IsFractionRing A K] [FiniteDimensional K L] [Algebra.IsSeparable K L]
  [IsIntegralClosure B A L]

variable {A} in
/-- **Linear forms are trace pairings.** Every `A`-linear form `f : B → A` on the integral closure
of `A` in a finite separable extension `L / K` is `x ↦ Tr_{L/K}(y x)` for some `y ∈ L`. -/
theorem exists_trace_mul_algebraMap_eq (f : B →ₗ[A] A) :
    ∃ y : L, ∀ x : B, Algebra.trace K L (y * algebraMap B L x) = algebraMap A K (f x) := by
  classical
  obtain ⟨s, b, hb⟩ := FiniteDimensional.exists_is_basis_integral A K L
  choose b' hb' using fun i ↦ (IsIntegralClosure.isIntegral_iff (A := B)).mp (hb i)
  -- The `K`-linear form on `L` taking the values of `f` on the integral basis `b`.
  let φ : L →ₗ[K] K := b.constr K fun i ↦ algebraMap A K (f (b' i))
  refine ⟨((Algebra.traceForm K L).toDual (traceForm_nondegenerate K L)).symm φ, fun x ↦ ?_⟩
  rw [← Algebra.traceForm_apply, LinearMap.BilinForm.apply_toDual_symm_apply]
  -- The two `A`-linear maps `B → K` agree on the `b' i`, hence on multiples of every element.
  let g₁ : B →ₗ[A] K := φ.restrictScalars A ∘ₗ (IsScalarTower.toAlgHom A B L).toLinearMap
  let g₂ : B →ₗ[A] K := (Algebra.linearMap A K) ∘ₗ f
  have hg : Set.EqOn g₁ g₂ (Set.range b') := by
    rintro _ ⟨i, rfl⟩
    simp [g₁, g₂, φ, hb']
  have hspan : (IsScalarTower.toAlgHom A B L).toLinearMap x ∈
      Submodule.span K ((IsScalarTower.toAlgHom A B L).toLinearMap '' Set.range b') := by
    simpa only [← Set.range_comp, Function.comp_def, AlgHom.toLinearMap_apply,
      IsScalarTower.toAlgHom_apply, hb'] using
      b.mem_span (algebraMap B L x)
  obtain ⟨a, ha, hax⟩ := (LinearMap.apply_mem_span_image_iff_exists_smul_mem_span
    (IsIntegralClosure.algebraMap_injective B A L) A⁰).mp hspan
  have h := LinearMap.eqOn_span' hg hax
  simp only [map_smul] at h
  rw [← algebraMap_smul K, ← algebraMap_smul K a (g₂ x)] at h
  exact (IsLocalization.map_units K ⟨a, ha⟩).smul_left_cancel.mp h

variable [Module.Finite A B] [Module.Projective A B]

/-- **A finite trace-dual family.** If the integral closure `B` of `A` in a finite separable
extension `L / K` is a finite projective `A`-module, there are finitely many `bᵢ ∈ B` and
`yᵢ ∈ Bᵛ` such that `x = ∑ᵢ Tr_{L/K}(x bᵢ) yᵢ` for every `x ∈ L`. -/
theorem exists_sum_trace_mul_smul_eq :
    ∃ (n : ℕ) (b : Fin n → B) (y : Fin n → L),
      (∀ i, y i ∈ Submodule.traceDual A K (1 : Submodule B L)) ∧
      ∀ x : L, ∑ i, Algebra.trace K L (x * algebraMap B L (b i)) • y i = x := by
  obtain ⟨n, F, G, -, -, hFG⟩ := Module.Finite.exists_comp_eq_id_of_projective A B
  choose y hy using fun i : Fin n ↦
    exists_trace_mul_algebraMap_eq K (L := L) (LinearMap.proj i ∘ₗ G)
  let b : Fin n → B := fun i ↦ F (Pi.single i 1)
  -- The dual basis `(b, G)` of the projective module `B`, read through the trace pairing.
  have hB (z : B) : ∑ i, algebraMap A K (G z i) • algebraMap B L (b i) = algebraMap B L z := by
    have hG : G z = ∑ i, G z i • Pi.single i (1 : A) := by
      ext j
      simp [Pi.single_apply]
    conv_rhs => rw [← LinearMap.id_apply (R := A) z, ← hFG, LinearMap.comp_apply, hG, map_sum,
      map_sum]
    simp only [b, ← IsScalarTower.toAlgHom_apply A B L, map_smul, algebraMap_smul]
  refine ⟨n, b, y, fun i ↦ ?_, fun x ↦ ?_⟩
  · rw [Submodule.mem_traceDual]
    intro _ hz
    obtain ⟨z, rfl⟩ := Submodule.mem_one.mp hz
    rw [Algebra.traceForm_apply, hy]
    exact ⟨_, rfl⟩
  -- Both sides have the same trace pairing with every element of `B`, hence of `L`.
  have hpair (z : B) : Algebra.trace K L ((∑ i, Algebra.trace K L (x * algebraMap B L (b i)) • y i
      - x) * algebraMap B L z) = 0 := by
    rw [sub_mul, map_sub, Finset.sum_mul, map_sum, sub_eq_zero]
    conv_rhs => rw [← hB z, Finset.mul_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    simp only [mul_smul_comm, map_smul, hy, LinearMap.comp_apply,
      LinearMap.proj_apply, smul_eq_mul, mul_comm]
  rw [← sub_eq_zero]
  refine (traceForm_nondegenerate K L).1 _ fun z ↦ ?_
  obtain ⟨⟨a, ha⟩, hm⟩ := IsIntegral.exists_multiple_integral_of_isLocalization A⁰ z
    (Algebra.IsIntegral.isIntegral (R := K) z)
  obtain ⟨z', hz'⟩ := (IsIntegralClosure.isIntegral_iff (A := B)).mp hm
  have ha' : algebraMap A K a ≠ 0 :=
    (IsFractionRing.injective A K).ne_iff' (map_zero _) |>.mpr (nonZeroDivisors.ne_zero ha)
  simp only [Submonoid.smul_def] at hz'
  rw [← smul_eq_zero_iff_right ha', ← map_smul, algebraMap_smul, ← hz', Algebra.traceForm_apply,
    hpair]

end DualFamily

section BaseChange

variable {R K A₀ A B L : Type*} [CommRing R] [Field K] [Algebra R K]
  [CommRing A₀] [Algebra R A₀] [CommRing A] [Algebra R A] [Algebra K A] [Algebra A₀ A]
  [IsScalarTower R K A] [IsScalarTower R A₀ A]
  [CommRing B] [Algebra R B] [Field L] [Algebra R L] [Algebra K L] [Algebra B L]
  [IsScalarTower R K L] [IsScalarTower R B L]

/-- On the image of `A₀ ⊗[R] B` under `TauCeti.baseChangeOfTower`, the trace pairing with an
element of `Submodule.traceDual R K (1 : Submodule B L)` takes values in `A₀`. -/
theorem trace_baseChangeOfTower_mul_mem {d : L}
    (hd : d ∈ Submodule.traceDual R K (1 : Submodule B L)) (t : A₀ ⊗[R] B) :
    Algebra.trace A (A ⊗[K] L) (baseChangeOfTower R K A₀ A B L t * (1 ⊗ₜ[K] d)) ∈
      (algebraMap A₀ A).range := by
  induction t using TensorProduct.inductionOn with
  | add t u ht hu =>
    rw [map_add, add_mul, map_add]
    exact add_mem ht hu
  | tmul a₀ b =>
    obtain ⟨r, hr⟩ := Submodule.mem_traceDual.mp hd _ (Submodule.mem_one.mpr ⟨b, rfl⟩)
    rw [Algebra.traceForm_apply, mul_comm] at hr
    refine ⟨a₀ * algebraMap R A₀ r, ?_⟩
    rw [Algebra.trace_baseChangeOfTower_tmul_mul, ← hr, map_mul,
      ← IsScalarTower.algebraMap_apply R A₀ A, IsScalarTower.algebraMap_apply R K A]

end BaseChange

end TauCeti
