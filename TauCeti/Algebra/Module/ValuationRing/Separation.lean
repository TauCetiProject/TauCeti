/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.ValuationRing

/-!
# Separation by linear functionals modulo an annihilator

A finitely generated submodule of a finite free module over a valuation domain can be
tested by linear functionals modulo any nonzero scalar whose multiples it contains.
This is the dual form of the stacked bases theorem, useful for proving inclusions of lattices.
-/

public section

namespace Submodule

variable {V : Type*} [CommRing V] [IsDomain V] [ValuationRing V]

/-- A finitely generated submodule of a finite coordinate module containing all multiples of
`q ≠ 0` is detected by the linear functionals taking that submodule into `(q)`. -/
private theorem mem_iff_forall_dvd_linearMap_fin {n : ℕ} (N : Submodule V (Fin n → V))
    (hN : N.FG) {q : V} (hq : q ≠ 0) (hcontain : ∀ m, q • m ∈ N) (x : Fin n → V) :
    x ∈ N ↔ ∀ f : (Fin n → V) →ₗ[V] V, (∀ y ∈ N, q ∣ f y) → q ∣ f x := by
  classical
  refine ⟨fun hx f hf ↦ hf x hx, fun hx ↦ ?_⟩
  obtain ⟨e, a, he⟩ := N.exists_linearEquiv_map_eq_pi_span_singleton hN
  have hcoord (y) (hy : y ∈ N) (i) : a i ∣ e y i := by
    have hmem : e y ∈ N.map e.toLinearMap := mem_map_of_mem hy
    rw [he] at hmem
    exact Ideal.mem_span_singleton.mp (mem_pi.mp hmem i (Set.mem_univ i))
  have hai (i) : a i ∣ q := by
    simpa using hcoord _ (hcontain (e.symm (Pi.single i 1))) i
  have hex (i) : a i ∣ e x i := by
    obtain ⟨b, hb⟩ := hai i
    have hb0 : b ≠ 0 := by intro h; apply hq; rw [hb, h, mul_zero]
    let f : (Fin n → V) →ₗ[V] V := b • ((LinearMap.proj i).comp e.toLinearMap)
    have hf (y) (hy : y ∈ N) : q ∣ f y := by
      obtain ⟨c, hc⟩ := hcoord y hy i
      exact ⟨c, by simp [f, hc, hb, mul_comm, mul_left_comm]⟩
    have h := hx f hf
    simp only [f, LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.proj_apply,
      LinearEquiv.coe_coe, smul_eq_mul, hb] at h
    exact (mul_dvd_mul_iff_left hb0).mp (by simpa [mul_comm] using h)
  have hxmap : e x ∈ N.map e.toLinearMap := by
    rw [he, mem_pi]
    exact fun i _ ↦ Ideal.mem_span_singleton.mpr (hex i)
  simpa using (mem_map_equiv N).mp hxmap

variable {M : Type*} [AddCommGroup M] [Module V M] [Module.Free V M]

/-- A finitely generated submodule of a free module over a valuation domain is detected
by linear functionals modulo any nonzero scalar whose multiples it contains. The hypotheses
already force the ambient free module to have finite rank. -/
theorem mem_iff_forall_dvd_linearMap (N : Submodule V M) (hN : N.FG) {q : V}
    (hq : q ≠ 0) (hcontain : ∀ m, q • m ∈ N) (x : M) :
    x ∈ N ↔ ∀ f : M →ₗ[V] V, (∀ y ∈ N, q ∣ f y) → q ∣ f x := by
  refine ⟨fun hx f hf ↦ hf x hx, fun hx ↦ ?_⟩
  have : Module.Finite V N := Module.Finite.of_fg hN
  let f : M →ₗ[V] N := (q • LinearMap.id).codRestrict N hcontain
  have hf : Function.Injective f := by
    intro a b hab
    apply smul_right_injective M hq
    exact congrArg Subtype.val hab
  have : Finite (Module.Free.ChooseBasisIndex V M) :=
    ((Module.Free.chooseBasis V M).linearIndependent.map' f
      (LinearMap.ker_eq_bot.mpr hf)).finite
  have : Module.Finite V M := Module.Finite.of_basis (Module.Free.chooseBasis V M)
  let e := (Module.finBasis V M).equivFun
  have hmem : e x ∈ N.map e.toLinearMap := by
    apply (mem_iff_forall_dvd_linearMap_fin _ (hN.map _) hq (fun m ↦
      ⟨q • e.symm m, hcontain _, by simp⟩) (e x)).mpr
    intro f hf
    exact hx (f.comp e.toLinearMap) (fun y hy ↦ hf _ (mem_map_of_mem hy))
  simpa using (mem_map_equiv N).mp hmem

end Submodule
