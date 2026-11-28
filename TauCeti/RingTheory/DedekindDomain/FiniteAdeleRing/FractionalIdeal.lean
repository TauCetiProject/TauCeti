/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.DedekindDomain.FiniteAdeleRing.IntegralIdeal

/-!
# Finite adelic fractional ideals

For a nonzero fractional ideal `I`, its finite adelic extension `finiteAdelicIdeal I` is the
module `I Ô` over the integral finite adeles. It is defined independently of a generator.
Any finite idele representing `I` gives its usual local divisibility criterion.

The module `I Ô` is open and closed in the finite adele ring, it is the closure of the diagonal
image of `I`, and by strong approximation `K + I Ô` is the whole finite adele ring
(`IsDedekindDomain.FiniteAdeleRing.exists_sub_algebraMap_mem_finiteAdelicIdeal`).
-/

public section
noncomputable section

open IsDedekindDomain HeightOneSpectrum
open scoped nonZeroDivisors

namespace IsDedekindDomain.FiniteAdeleRing

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

/-- The finite adelic extension `I Ô` of a nonzero fractional ideal. Divisibility by every
finite idele representing `I` makes this definition independent of any choice of generator. -/
def finiteAdelicIdeal (I : (FractionalIdeal R⁰ K)ˣ) :
    Submodule (integralAdeles R K) 𝔸ᶠ[R, K] where
  carrier := {x | ∀ t : 𝔸ᶠ[R, K]ˣ, toFractionalIdeal t = I →
    (↑t⁻¹ : 𝔸ᶠ[R, K]) * x ∈ integralAdeles R K}
  zero_mem' := by simp
  add_mem' hx hy t ht := by simpa only [mul_add] using add_mem (hx t ht) (hy t ht)
  smul_mem' a x hx t ht := by
    -- The subtype scalar acts by multiplication in the ambient adele ring.
    change (↑t⁻¹ : 𝔸ᶠ[R, K]) * ((a : 𝔸ᶠ[R, K]) * x) ∈ integralAdeles R K
    simpa only [mul_left_comm] using mul_mem a.property (hx t ht)

/-- Any representing finite idele computes membership in the adelic extension. -/
theorem mem_finiteAdelicIdeal_iff {I : (FractionalIdeal R⁰ K)ˣ}
    (t : 𝔸ᶠ[R, K]ˣ) (ht : toFractionalIdeal t = I) {x : 𝔸ᶠ[R, K]} :
    x ∈ finiteAdelicIdeal I ↔ (↑t⁻¹ : 𝔸ᶠ[R, K]) * x ∈ integralAdeles R K := by
  refine ⟨fun hx ↦ hx t ht, fun hx s hs ↦ ?_⟩
  have hu : s⁻¹ * t ∈ integralUnits R K := by
    rw [← ker_toFractionalIdeal, MonoidHom.mem_ker, map_mul, map_inv, hs, ht, inv_mul_cancel]
  have hint := (mem_integralUnits_iff_val_mem_and_inv_mem.mp hu).1
  convert mul_mem hint hx using 1
  simp only [Units.val_mul, mul_assoc, ← mul_assoc (t : 𝔸ᶠ[R, K]), Units.mul_inv, one_mul]

/-- A finite idele belongs to the adelic extension of the fractional ideal it represents. -/
theorem coe_mem_finiteAdelicIdeal (t : 𝔸ᶠ[R, K]ˣ) :
    (t : 𝔸ᶠ[R, K]) ∈ finiteAdelicIdeal (toFractionalIdeal t) := by
  rw [mem_finiteAdelicIdeal_iff t rfl, Units.inv_mul]
  exact one_mem _

/-- The unit ideal extends to the ring of integral finite adeles. -/
@[simp]
theorem mem_finiteAdelicIdeal_one {x : 𝔸ᶠ[R, K]} :
    x ∈ finiteAdelicIdeal (1 : (FractionalIdeal R⁰ K)ˣ) ↔ x ∈ integralAdeles R K := by
  simpa using mem_finiteAdelicIdeal_iff (1 : 𝔸ᶠ[R, K]ˣ) (map_one _) (x := x)

/-- The diagonal rational points of an adelic ideal recover the original fractional ideal. -/
@[simp]
theorem algebraMap_mem_finiteAdelicIdeal_iff (I : (FractionalIdeal R⁰ K)ˣ) (a : K) :
    algebraMap K 𝔸ᶠ[R, K] a ∈ finiteAdelicIdeal I ↔
      a ∈ (I : FractionalIdeal R⁰ K) := by
  obtain ⟨t, ht⟩ := toFractionalIdeal_surjective I
  rw [mem_finiteAdelicIdeal_iff t ht, mem_integralAdeles]
  simpa [mul_apply, algebraMap_apply, algebraMap_adicCompletion, ht] using
    (mem_toFractionalIdeal_iff t (a := a)).symm

/-- Products of adelic ideal elements lie in the extension of the product ideal. -/
theorem mul_mem_finiteAdelicIdeal {I J : (FractionalIdeal R⁰ K)ˣ} {x y : 𝔸ᶠ[R, K]}
    (hx : x ∈ finiteAdelicIdeal I) (hy : y ∈ finiteAdelicIdeal J) :
    x * y ∈ finiteAdelicIdeal (I * J) := by
  obtain ⟨s, hs⟩ := toFractionalIdeal_surjective I
  obtain ⟨t, ht⟩ := toFractionalIdeal_surjective J
  rw [mem_finiteAdelicIdeal_iff (s * t) (by rw [map_mul, hs, ht])]
  rw [mem_finiteAdelicIdeal_iff s hs] at hx
  rw [mem_finiteAdelicIdeal_iff t ht] at hy
  convert mul_mem hx hy using 1
  simp only [mul_inv_rev, Units.val_mul]
  ring

/-- The adelic extension of a fractional ideal is the preimage of the integral finite adeles under
multiplication by the inverse of any finite idele representing the ideal. -/
private theorem coe_finiteAdelicIdeal_eq_preimage {I : (FractionalIdeal R⁰ K)ˣ} (t : 𝔸ᶠ[R, K]ˣ)
    (ht : toFractionalIdeal t = I) :
    (finiteAdelicIdeal I : Set 𝔸ᶠ[R, K]) =
      (fun x : 𝔸ᶠ[R, K] ↦ (↑t⁻¹ : 𝔸ᶠ[R, K]) * x) ⁻¹' (integralAdeles R K : Set 𝔸ᶠ[R, K]) :=
  Set.ext fun _ ↦ mem_finiteAdelicIdeal_iff t ht

/-- The adelic extension `I Ô` of a fractional ideal is open in the finite adele ring. -/
theorem isOpen_finiteAdelicIdeal (I : (FractionalIdeal R⁰ K)ˣ) :
    IsOpen (finiteAdelicIdeal I : Set 𝔸ᶠ[R, K]) := by
  obtain ⟨t, ht⟩ := toFractionalIdeal_surjective I
  rw [coe_finiteAdelicIdeal_eq_preimage t ht]
  exact (isOpen_integralAdeles R K).preimage (continuous_const.mul continuous_id)

/-- The adelic extension `I Ô` of a fractional ideal is closed in the finite adele ring. -/
theorem isClosed_finiteAdelicIdeal (I : (FractionalIdeal R⁰ K)ˣ) :
    IsClosed (finiteAdelicIdeal I : Set 𝔸ᶠ[R, K]) := by
  obtain ⟨t, ht⟩ := toFractionalIdeal_surjective I
  rw [coe_finiteAdelicIdeal_eq_preimage t ht]
  exact (isClosed_integralAdeles R K).preimage (continuous_const.mul continuous_id)

/-- **Strong approximation modulo an adelic ideal**: `K + I Ô` is the whole finite adele ring, that
is, every finite adele differs from the diagonal image of some `x ∈ K` by an element of `I Ô`. -/
theorem exists_sub_algebraMap_mem_finiteAdelicIdeal (I : (FractionalIdeal R⁰ K)ˣ)
    (a : 𝔸ᶠ[R, K]) : ∃ x : K, a - algebraMap K 𝔸ᶠ[R, K] x ∈ finiteAdelicIdeal I := by
  have hopen : IsOpen ((fun y : 𝔸ᶠ[R, K] ↦ a - y) ⁻¹' (finiteAdelicIdeal I : Set 𝔸ᶠ[R, K])) :=
    (isOpen_finiteAdelicIdeal I).preimage (continuous_const.sub continuous_id)
  have ha : a ∈ (fun y : 𝔸ᶠ[R, K] ↦ a - y) ⁻¹' (finiteAdelicIdeal I : Set 𝔸ᶠ[R, K]) := by
    rw [Set.mem_preimage, sub_self, SetLike.mem_coe]
    exact zero_mem _
  exact (denseRange_algebraMap R K).exists_mem_open hopen ⟨a, ha⟩

/-- The finite adelic extension of a fractional ideal is the closure of its diagonal image. -/
theorem closure_image_algebraMap_fractionalIdeal (I : (FractionalIdeal R⁰ K)ˣ) :
    closure ((algebraMap K 𝔸ᶠ[R, K]) '' (↑(I : FractionalIdeal R⁰ K) : Set K)) =
      (finiteAdelicIdeal I : Set 𝔸ᶠ[R, K]) := by
  have hopen := isOpen_finiteAdelicIdeal I
  have hclosed := isClosed_finiteAdelicIdeal I
  have hideal : (↑(I : FractionalIdeal R⁰ K) : Set K) =
      (algebraMap K 𝔸ᶠ[R, K]) ⁻¹' (finiteAdelicIdeal I : Set 𝔸ᶠ[R, K]) :=
    Set.ext fun a ↦ (algebraMap_mem_finiteAdelicIdeal_iff I a).symm
  rw [hideal, Set.image_preimage_eq_inter_range]
  exact le_antisymm (closure_minimal Set.inter_subset_left hclosed)
    ((denseRange_algebraMap R K).open_subset_closure_inter hopen)

end IsDedekindDomain.FiniteAdeleRing
