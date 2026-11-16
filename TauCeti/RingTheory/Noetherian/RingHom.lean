/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Filtration
public import Mathlib.RingTheory.Ideal.Cotangent

/-!
# Endomorphisms of Noetherian rings

Every surjective ring endomorphism of a left-Noetherian ring is injective (the Hopfian property):
the ascending chain of kernels of its iterates stabilizes, and surjectivity pulls back any element
of the kernel into that stable range. No commutativity hypothesis is needed.

For a commutative ring `R`, an endomorphism preserving an ideal `I` that is surjective modulo `I`
and on the conormal module `I ⧸ I ^ 2` is surjective modulo every power `I ^ n`. When `R` is
Noetherian, each quotient `R ⧸ I ^ n` is Noetherian, so the induced endomorphism on every
infinitesimal quotient is bijective; if `I` is adically separated (`⨅ n, I ^ n = ⊥`), in
particular when `R` is a Noetherian domain and `I ≠ ⊤` by Krull's intersection theorem, the
endomorphism is injective.

## Main results

* `RingHom.injective_of_surjective`: a surjective ring endomorphism of a left-Noetherian ring is
  injective.
* `RingHom.bijective_of_surjective`: a surjective ring endomorphism of a left-Noetherian ring is
  bijective.
* `RingHom.surjective_quotientMap_pow`: an ideal-preserving endomorphism surjective on `R ⧸ I` and
  `I ⧸ I ^ 2` is surjective on `R ⧸ I ^ n` for every `n`.
* `RingHom.injective_of_iInf_pow_eq_bot`: when `R` is Noetherian and `⨅ n, I ^ n = ⊥`, such an
  endomorphism is injective.
* `RingHom.injective_of_surjective_quotient_of_surjective_cotangent`: specialization to a proper
  ideal of a Noetherian domain via Krull's intersection theorem.
* `AlgHom.injective_of_iInf_pow_eq_bot_of_surjective_mapCotangent` and
  `AlgHom.injective_of_surjective_mapCotangent`: algebra-homomorphism forms phrased via
  `Ideal.mapCotangent`.

## References

* H. Matsumura, *Commutative Ring Theory*, §8 (Krull's intersection theorem).
-/

public section

namespace RingHom

section Ring

variable {R : Type*} [Ring R]

/-- **Hopfian property of Noetherian rings**: every surjective ring endomorphism of a
left-Noetherian ring is injective. -/
theorem injective_of_surjective [IsNoetherianRing R] (f : R →+* R)
    (hf : Function.Surjective f) : Function.Injective f := by
  let kerChain : ℕ →o Ideal R :=
    ⟨fun n => RingHom.ker (f ^ n), fun m n hmn x hx => by
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
      rw [RingHom.mem_ker] at hx ⊢
      rw [add_comm, pow_add, RingHom.mul_def, RingHom.comp_apply, hx, map_zero]⟩
  obtain ⟨n, hn⟩ := monotone_stabilizes_iff_noetherian.mpr (inferInstance : IsNoetherianRing R)
    kerChain
  have hstab : RingHom.ker (f ^ n) = RingHom.ker (f ^ (n + 1)) := hn (n + 1) (Nat.le_succ n)
  have hfn : ∀ k : ℕ, Function.Surjective (f ^ k) := by
    intro k
    induction k with
    | zero => exact Function.surjective_id
    | succ k ih =>
      rw [pow_succ', RingHom.mul_def, RingHom.coe_comp]
      exact hf.comp ih
  refine (injective_iff_map_eq_zero f).mpr fun x hx => ?_
  obtain ⟨y, rfl⟩ := hfn n x
  have hy : y ∈ RingHom.ker (f ^ (n + 1)) := by
    rw [RingHom.mem_ker, pow_succ', RingHom.mul_def, RingHom.comp_apply, hx]
  exact RingHom.mem_ker.mp (hstab.symm ▸ hy)

/-- Every surjective ring endomorphism of a left-Noetherian ring is bijective. -/
theorem bijective_of_surjective [IsNoetherianRing R] (f : R →+* R)
    (hf : Function.Surjective f) : Function.Bijective f :=
  ⟨f.injective_of_surjective hf, hf⟩

end Ring

section CommRing

variable {R : Type*} [CommRing R]

/-- If an endomorphism maps `I` into `I`, then it maps `I ^ n` into `I ^ n`. -/
private theorem pow_le_comap_pow {I : Ideal R} {f : R →+* R} (hfI : I ≤ I.comap f) (n : ℕ) :
    I ^ n ≤ (I ^ n).comap f := by
  rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow]
  exact Ideal.pow_right_mono (Ideal.map_le_iff_le_comap.mpr hfI) n

/-- Surjectivity of an ideal-preserving endomorphism on `R ⧸ I` and `I ⧸ I ^ 2` implies
surjectivity on every graded piece `I ^ n ⧸ I ^ (n + 1)`. -/
private theorem exists_mem_pow_sub_mem_pow_succ {I : Ideal R} {f : R →+* R}
    (hfI : I ≤ I.comap f)
    (hquot : Function.Surjective (Ideal.quotientMap I f hfI))
    (hcot : ∀ y ∈ I, ∃ x ∈ I, y - f x ∈ I ^ 2) :
    ∀ n : ℕ, ∀ y ∈ I ^ n, ∃ x ∈ I ^ n, y - f x ∈ I ^ (n + 1)
  | 0, y, _ => by
    obtain ⟨q, hq⟩ := hquot (Ideal.Quotient.mk I y)
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective q
    rw [Ideal.quotientMap_mk, Ideal.Quotient.eq] at hq
    refine ⟨x, by simp, ?_⟩
    simpa only [zero_add, pow_one, neg_sub] using I.neg_mem hq
  | 1, y, hy => by
    simpa only [pow_one] using hcot y (by simpa only [pow_one] using hy)
  | n + 2, y, hy => by
    have ih := exists_mem_pow_sub_mem_pow_succ hfI hquot hcot (n + 1)
    rw [pow_succ] at hy
    refine Submodule.mul_induction_on hy (fun a ha b hb => ?_) (fun u v hu hv => ?_)
    · obtain ⟨u, hu, hau⟩ := ih a ha
      obtain ⟨v, hv, hbv⟩ := hcot b hb
      refine ⟨u * v, pow_succ I (n + 1) ▸ Ideal.mul_mem_mul hu hv, ?_⟩
      have hdecomp : a * b - f (u * v) = (a - f u) * b + f u * (b - f v) := by
        rw [map_mul]
        ring
      rw [hdecomp]
      refine Ideal.add_mem _ ?_ ?_
      · rw [pow_succ]
        exact Ideal.mul_mem_mul hau hb
      · have hfu : f u ∈ I ^ (n + 1) := pow_le_comap_pow hfI (n + 1) hu
        have hpow : I ^ (n + 1) * I ^ 2 = I ^ (n + 3) := by
          rw [← pow_add]
        rw [← hpow]
        exact Ideal.mul_mem_mul hfu hbv
    · obtain ⟨x₁, hx₁, hy₁⟩ := hu
      obtain ⟨x₂, hx₂, hy₂⟩ := hv
      refine ⟨x₁ + x₂, Ideal.add_mem _ hx₁ hx₂, ?_⟩
      have hdecomp : (u + v) - f (x₁ + x₂) = (u - f x₁) + (v - f x₂) := by
        rw [map_add]
        ring
      rw [hdecomp]
      exact Ideal.add_mem _ hy₁ hy₂

/-- An endomorphism of a commutative ring preserving an ideal `I` that is surjective modulo `I`
and on `I ⧸ I ^ 2` is surjective modulo every power `I ^ n`. -/
theorem surjective_quotientMap_pow (I : Ideal R) (f : R →+* R) (hfI : I ≤ I.comap f)
    (hquot : Function.Surjective (Ideal.quotientMap I f hfI))
    (hcot : ∀ y ∈ I, ∃ x ∈ I, y - f x ∈ I ^ 2)
    (n : ℕ) (hpow : I ^ n ≤ (I ^ n).comap f) :
    Function.Surjective (Ideal.quotientMap (I ^ n) f hpow) := by
  have hstep : ∀ k : ℕ, ∀ y : R, ∃ x : R, y - f x ∈ I ^ k := by
    intro k
    induction k with
    | zero => intro y; exact ⟨0, by simp⟩
    | succ k ih =>
      intro y
      obtain ⟨x₁, hx₁⟩ := ih y
      obtain ⟨x₂, -, hx₂⟩ :=
        exists_mem_pow_sub_mem_pow_succ hfI hquot hcot k (y - f x₁) hx₁
      refine ⟨x₁ + x₂, ?_⟩
      have hdecomp : y - f (x₁ + x₂) = (y - f x₁) - f x₂ := by
        rw [map_add]
        ring
      rwa [hdecomp]
  intro q
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective q
  obtain ⟨x, hx⟩ := hstep n y
  refine ⟨Ideal.Quotient.mk (I ^ n) x, ?_⟩
  rw [Ideal.quotientMap_mk, Ideal.Quotient.eq]
  simpa only [neg_sub] using (I ^ n).neg_mem hx

/-- An endomorphism of a commutative Noetherian ring preserving an adically separated ideal `I`
(`⨅ n, I ^ n = ⊥`) that is surjective on `R ⧸ I` and `I ⧸ I ^ 2` is injective. -/
theorem injective_of_iInf_pow_eq_bot [IsNoetherianRing R] (I : Ideal R)
    (hsep : ⨅ n : ℕ, I ^ n = ⊥) (f : R →+* R) (hfI : I ≤ I.comap f)
    (hquot : Function.Surjective (Ideal.quotientMap I f hfI))
    (hcot : ∀ y ∈ I, ∃ x ∈ I, y - f x ∈ I ^ 2) :
    Function.Injective f := by
  refine (injective_iff_map_eq_zero f).mpr fun x hx => ?_
  rw [← Ideal.mem_bot, ← hsep, Ideal.mem_iInf]
  intro n
  have hpow : I ^ n ≤ (I ^ n).comap f := pow_le_comap_pow hfI n
  have : IsNoetherianRing (R ⧸ I ^ n) :=
    isNoetherianRing_of_surjective R (R ⧸ I ^ n) (Ideal.Quotient.mk (I ^ n))
      Ideal.Quotient.mk_surjective
  have hinj := (Ideal.quotientMap (I ^ n) f hpow).injective_of_surjective
    (f.surjective_quotientMap_pow I hfI hquot hcot n hpow)
  have hzero : Ideal.quotientMap (I ^ n) f hpow (Ideal.Quotient.mk (I ^ n) x) = 0 := by
    rw [Ideal.quotientMap_mk, hx, map_zero]
  exact Ideal.Quotient.eq_zero_iff_mem.mp (hinj (hzero.trans (map_zero _).symm))

/-- An endomorphism of a Noetherian integral domain preserving a proper ideal `I` that is
surjective on `R ⧸ I` and `I ⧸ I ^ 2` is injective. -/
theorem injective_of_surjective_quotient_of_surjective_cotangent [IsNoetherianRing R] [IsDomain R]
    (I : Ideal R) (hI : I ≠ ⊤) (f : R →+* R) (hfI : I ≤ I.comap f)
    (hquot : Function.Surjective (Ideal.quotientMap I f hfI))
    (hcot : ∀ y ∈ I, ∃ x ∈ I, y - f x ∈ I ^ 2) :
    Function.Injective f :=
  f.injective_of_iInf_pow_eq_bot I (Ideal.iInf_pow_eq_bot_of_isDomain I hI) hfI hquot hcot

end CommRing

end RingHom

namespace AlgHom

variable {k A : Type*} [CommRing k] [CommRing A] [Algebra k A]

/-- An algebra endomorphism of a commutative Noetherian algebra preserving an adically separated
ideal `I` (`⨅ n, I ^ n = ⊥`) that is surjective on `A ⧸ I` and on `I.Cotangent` is
injective. -/
theorem injective_of_iInf_pow_eq_bot_of_surjective_mapCotangent [IsNoetherianRing A]
    (I : Ideal A) (hsep : ⨅ n : ℕ, I ^ n = ⊥) (f : A →ₐ[k] A)
    (hfI : I ≤ I.comap f)
    (hquot : Function.Surjective (Ideal.Quotient.mk I ∘ f))
    (hcot : Function.Surjective (Ideal.mapCotangent I I f hfI)) :
    Function.Injective f := by
  have hfI' : I ≤ I.comap (f : A →+* A) := fun x hx => hfI hx
  have hquot' : Function.Surjective (Ideal.quotientMap I (f : A →+* A) hfI') := by
    intro q
    obtain ⟨x, hx⟩ := hquot q
    exact ⟨Ideal.Quotient.mk I x, by
      simpa only [Ideal.quotientMap_mk, AlgHom.coe_toRingHom, Function.comp_apply] using hx⟩
  refine (f : A →+* A).injective_of_iInf_pow_eq_bot I hsep hfI' hquot' fun y hy => ?_
  obtain ⟨c, hc⟩ := hcot (I.toCotangent ⟨y, hy⟩)
  obtain ⟨x, rfl⟩ := I.toCotangent_surjective c
  rw [Ideal.mapCotangent_toCotangent, Ideal.toCotangent_eq] at hc
  exact ⟨x.1, x.2, by simpa only [AlgHom.coe_toRingHom, neg_sub] using (I ^ 2).neg_mem hc⟩

/-- An algebra endomorphism of a Noetherian integral domain preserving a proper ideal `I` that is
surjective on `A ⧸ I` and on `I.Cotangent` is injective. -/
theorem injective_of_surjective_mapCotangent [IsNoetherianRing A] [IsDomain A]
    (I : Ideal A) (hI : I ≠ ⊤) (f : A →ₐ[k] A) (hfI : I ≤ I.comap f)
    (hquot : Function.Surjective (Ideal.Quotient.mk I ∘ f))
    (hcot : Function.Surjective (Ideal.mapCotangent I I f hfI)) :
    Function.Injective f :=
  f.injective_of_iInf_pow_eq_bot_of_surjective_mapCotangent I
    (Ideal.iInf_pow_eq_bot_of_isDomain I hI) hfI hquot hcot

end AlgHom
