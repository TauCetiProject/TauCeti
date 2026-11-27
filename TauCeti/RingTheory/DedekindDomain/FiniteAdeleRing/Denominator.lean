/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.DedekindDomain.SInteger
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import TauCeti.RingTheory.DedekindDomain.FiniteAdeleRing.CompletedIdeal
public import TauCeti.RingTheory.DedekindDomain.FiniteAdeleRing.Decomposition
public import TauCeti.RingTheory.Localization.DenIdeal
import TauCeti.RingTheory.DedekindDomain.FiniteAdeleRing.Place

/-!
# Denominators of finite adeles

The denominator ideal of an adele consists of the integral adeles that clear its denominator.
For a diagonal element this is the completion of its global denominator ideal. If the element
is integral outside `S`, the same ideal is obtained after replacing the coordinates outside
`S` by `1`. Its index can be read entirely in the completions at `S`. This gives the denominator
comparison used in `New.Filling.absNorm_denominator_le` in lsernau/grh-lean at `72fead1`.
-/

public section

open IsDedekindDomain
open scoped nonZeroDivisors

namespace IsDedekindDomain.FiniteAdeleRing

variable {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K]

/-- An integral adele clears the denominator of `z` exactly when its product with `z`
is integral at every finite place. -/
theorem mem_denIdeal_iff_mul_mem_integralAdeles {z : 𝔸ᶠ[R, K]} {a : integralAdeles R K} :
    a ∈ Algebra.denIdeal 𝔸ᶠ[R, K] z ↔ (a : 𝔸ᶠ[R, K]) * z ∈ integralAdeles R K := by
  rw [Algebra.mem_denIdeal_iff]
  exact ⟨fun ⟨b, hb⟩ ↦ hb ▸ b.property, fun h ↦ ⟨⟨_, h⟩, rfl⟩⟩

/-- The denominator ideal of a diagonal element is the completed global denominator ideal. -/
theorem denIdeal_algebraMap (x : K) :
    Algebra.denIdeal (R := integralAdeles R K) 𝔸ᶠ[R, K] (algebraMap K 𝔸ᶠ[R, K] x) =
      completedIdeal K (Algebra.denIdeal (R := R) K x) := by
  let D := Algebra.denIdeal (R := integralAdeles R K) 𝔸ᶠ[R, K] (algebraMap K 𝔸ᶠ[R, K] x)
  let I := Algebra.denIdeal (R := R) K x
  have hI : I ≠ ⊥ := Algebra.denIdeal_ne_bot K R⁰ x
  have hmem (r : R) : algebraMap R (integralAdeles R K) r ∈ D ↔ r ∈ I := by
    have hr := (IsScalarTower.algebraMap_apply R (integralAdeles R K) 𝔸ᶠ[R, K] r).symm
    rw [mem_denIdeal_iff_mul_mem_integralAdeles, ← Subalgebra.algebraMap_apply, hr,
      IsScalarTower.algebraMap_apply R K 𝔸ᶠ[R, K], ← map_mul, algebraMap_mem_integralAdeles_iff,
      RingHom.mem_range, Algebra.mem_denIdeal_iff]
    exact exists_congr fun _ ↦ eq_comm
  have hle : completedIdeal K I ≤ D := by
    rw [completedIdeal_def, Ideal.map_le_iff_le_comap]
    exact fun r hr ↦ (hmem r).2 hr
  refine le_antisymm (fun a ha ↦ ?_) hle
  obtain ⟨r, hr⟩ := exists_sub_mem_completedIdeal hI a
  have hrD : algebraMap R (integralAdeles R K) r ∈ D := by
    simpa using D.sub_mem ha (hle hr)
  simpa using (completedIdeal K I).add_mem hr (algebraMap_mem_completedIdeal ((hmem r).1 hrD))

/-- For an `S`-integer, replacing its coordinates away from `S` by `1` does not change the
adelic denominator ideal. -/
theorem denIdeal_awayEquiv_symm_one {S : Set (HeightOneSpectrum R)} (hS : S.Finite)
    {x : K} (hx : x ∈ S.integer K) :
    Algebra.denIdeal (R := integralAdeles R K) 𝔸ᶠ[R, K]
        ((awayEquiv R K hS).symm ((fun v : S ↦ (x : v.val.adicCompletion K)), 1)) =
      completedIdeal K (Algebra.denIdeal (R := R) K x) := by
  rw [← denIdeal_algebraMap]
  ext a
  simp only [mem_denIdeal_iff_mul_mem_integralAdeles, mem_integralAdeles,
    FiniteAdeleRing.mul_apply, algebraMap_apply]
  have hxi := mem_sIntegralAdeles.mp ((algebraMap_mem_sIntegralAdeles_iff S x).mpr hx)
  refine forall_congr' fun v ↦ ?_
  by_cases hv : v ∈ S
  · rw [awayEquiv_symm_apply_of_mem _ _ _ _ _ hv]
  · have hvx : (x : v.adicCompletion K) ∈ v.adicCompletionIntegers K := hxi v hv
    rw [awayEquiv_symm_apply_of_notMem _ _ _ _ _ hv, Away.one_apply, mul_one]
    exact iff_of_true (mem_integralAdeles.mp a.property v)
      (mul_mem (mem_integralAdeles.mp a.property v) hvx)

/-- The index of the denominator ideal of a tuple extended by `1` is the relative index
`[O_S : O_S ∩ z⁻¹ O_S]` in the product of completions, where `O_S` is the product
of the local integers. Here `z⁻¹ O_S` means the preimage under multiplication by `z`,
so the formula does not require `z` to be a unit. -/
theorem cardQuot_denIdeal_awayEquiv_symm_one {S : Set (HeightOneSpectrum R)} (hS : S.Finite)
    (z : ∀ v : S, v.val.adicCompletion K) :
    let O := AddSubgroup.pi Set.univ (fun v : S ↦ (v.val.adicCompletionIntegers K).toAddSubgroup)
    (Algebra.denIdeal (R := integralAdeles R K) 𝔸ᶠ[R, K]
      ((awayEquiv R K hS).symm (z, 1))).cardQuot =
        (O.comap (AddMonoidHom.mulLeft z)).relIndex O := by
  let O := AddSubgroup.pi Set.univ (fun v : S ↦ (v.val.adicCompletionIntegers K).toAddSubgroup)
  let f : integralAdeles R K →+ (∀ v : S, v.val.adicCompletion K) :=
    AddMonoidHom.pi fun v ↦ (proj K v.val).toAddMonoidHom.comp
      (algebraMap (integralAdeles R K) 𝔸ᶠ[R, K]).toAddMonoidHom
  have hf (a : integralAdeles R K) (v : S) : f a v = (a : 𝔸ᶠ[R, K]) v := by
    simp [f, Subalgebra.algebraMap_apply]
  have hr : f.range = O := by
    ext t
    simp only [AddMonoidHom.mem_range, O, AddSubgroup.mem_pi, Set.mem_univ, forall_const]
    constructor
    · rintro ⟨a, rfl⟩ v
      rw [hf]
      exact mem_integralAdeles.mp a.property v
    · intro ht
      let a := (awayEquiv R K hS).symm (t, 1)
      have ha : a ∈ integralAdeles R K := by
        rw [mem_integralAdeles]
        intro v
        by_cases hv : v ∈ S
        · simpa [a, awayEquiv_symm_apply_of_mem _ _ _ _ _ hv] using ht ⟨v, hv⟩
        · simp [a, awayEquiv_symm_apply_of_notMem _ _ _ _ _ hv]
      exact ⟨⟨a, ha⟩, funext fun v ↦ by simp [hf, a, v.property]⟩
  let I := Algebra.denIdeal (R := integralAdeles R K) 𝔸ᶠ[R, K] ((awayEquiv R K hS).symm (z, 1))
  have hd : I.toAddSubgroup =
      (O.comap (AddMonoidHom.mulLeft z)).comap f := by
    ext a
    simp only [Submodule.mem_toAddSubgroup, mem_denIdeal_iff_mul_mem_integralAdeles,
      mem_integralAdeles, FiniteAdeleRing.mul_apply, AddSubgroup.mem_comap,
      AddMonoidHom.coe_mulLeft, Pi.mul_apply, O, AddSubgroup.mem_pi, Set.mem_univ, forall_const,
      hf, I]
    constructor
    · intro h v
      simpa [mul_comm, v.property] using h v
    · intro h v
      by_cases hv : v ∈ S
      · simpa [mul_comm, hv] using h ⟨v, hv⟩
      · simpa [hv] using mem_integralAdeles.mp a.property v
  calc
    _ = I.toAddSubgroup.index := (rfl)
    _ = (O.comap (AddMonoidHom.mulLeft z)).relIndex O := by
      rw [hd, AddSubgroup.index_comap, hr]

end IsDedekindDomain.FiniteAdeleRing
