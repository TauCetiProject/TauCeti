/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Noetherian.Basic

/-!
# Endomorphisms of Noetherian rings

Every surjective ring endomorphism of a left-Noetherian ring is injective (the Hopfian property):
the ascending chain of kernels of its iterates stabilizes, and surjectivity pulls back any element
of the kernel into that stable range. No commutativity hypothesis is needed.

## Main results

* `RingHom.injective_of_surjective`: a surjective ring endomorphism of a left-Noetherian ring is
  injective.
* `RingHom.bijective_of_surjective`: a surjective ring endomorphism of a left-Noetherian ring is
  bijective.
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
  have hfn : Function.Surjective (f ^ n) := by
    rw [RingHom.coe_pow]
    exact hf.iterate n
  refine (injective_iff_map_eq_zero f).mpr fun x hx => ?_
  obtain ⟨y, rfl⟩ := hfn x
  have hy : y ∈ RingHom.ker (f ^ (n + 1)) := by
    rw [RingHom.mem_ker, pow_succ', RingHom.mul_def, RingHom.comp_apply, hx]
  exact RingHom.mem_ker.mp (hstab.symm ▸ hy)

/-- Every surjective ring endomorphism of a left-Noetherian ring is bijective. -/
theorem bijective_of_surjective [IsNoetherianRing R] (f : R →+* R)
    (hf : Function.Surjective f) : Function.Bijective f :=
  ⟨f.injective_of_surjective hf, hf⟩

end Ring

end RingHom
