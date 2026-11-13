/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Tower.ProZero

/-!
# Towers of kernels of powers

For an endomorphism `f` of a module, the power-kernel tower has terms `ker (f ^ n)` and
transitions induced by `f`, not by inclusion. It is pro-zero exactly when the kernels of
powers stabilize. In particular it is pro-zero for a Noetherian module, or whenever `f`
is nilpotent, without a finiteness hypothesis on the module in the latter case.

For multiplication by a ring element `a`, the limit of this tower is the `a`-adic Tate
module. The pro-zero criterion implies that both its limit and its first derived limit
vanish: apply `TauCeti.ModuleTower.lim_eq_bot_of_isProZero` and
`TauCeti.ModuleTower.subsingleton_limOne_of_isProZero`. These are the torsion-error terms
that occur when comparing completion of cohomology with cohomology of power quotients.
In particular, a cohomology module killed by a power of `a` has no Tate-module obstruction
to the formal-section comparison.

## References

* The Stacks Project, Example 15.95.5 (0BKG), adic Tate modules.
* The Stacks Project, Lemma 52.3.2 (0BLD), completion and cohomology.
* The Stacks Project, Lemma 52.12.7 (0EII), algebraization of formal sections.
-/

public section

open CategoryTheory Opposite

universe u v

namespace Module.End

variable {R : Type u} [Ring R] {M : Type v} [AddCommGroup M] [Module R M]

/-- The tower `ker (f ^ n)` with transitions induced by `f`. For scalar multiplication,
its limit is the adic Tate module. -/
-- Reducibility lets the tower's terms elaborate as submodules in its transition API.
abbrev powerKernelTower (f : Module.End R M) : TauCeti.ModuleTower.{v} R where
  obj n := ModuleCat.of R (LinearMap.ker (f ^ n.unop))
  map {m n} h := ModuleCat.ofHom <|
    ((f ^ (m.unop - n.unop)).comp (LinearMap.ker (f ^ m.unop)).subtype).codRestrict
      (LinearMap.ker (f ^ n.unop)) fun x ↦ by
        rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.subtype_apply,
          ← mul_apply_eq_comp, ← pow_add, Nat.add_sub_of_le (leOfHom h.unop)]
        exact x.property
  map_id n := by
    ext x
    simp
  map_comp {i j k} g h := by
    ext x
    simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.comp_apply,
      LinearMap.codRestrict_apply, Submodule.subtype_apply, ← mul_apply_eq_comp, ← pow_add]
    congr 2
    have hij := leOfHom g.unop
    have hjk := leOfHom h.unop
    omega

/-- The term in degree `n` is the kernel of the `n`-th power. -/
@[simp]
theorem powerKernelTower_obj (f : Module.End R M) (n : ℕ) :
    f.powerKernelTower.obj (op n) = ModuleCat.of R (LinearMap.ker (f ^ n)) :=
  (rfl)

/-- A step transition acts on the ambient module by `f`. -/
@[simp]
theorem powerKernelTower_transition_apply (f : Module.End R M) (n : ℕ)
    (x : LinearMap.ker (f ^ (n + 1))) :
    (f.powerKernelTower.transition n x : M) = f x := by
  simp [TauCeti.ModuleTower.transition_def]

/-- A composite transition from degree `m` to degree `n` acts by `f ^ (m - n)`. -/
@[simp]
theorem powerKernelTower_transitionOfLE_apply (f : Module.End R M) {n m : ℕ}
    (h : n ≤ m) (x : LinearMap.ker (f ^ m)) :
    (f.powerKernelTower.transitionOfLE h x : M) =
      (f ^ (m - n)) x := by
  rw [TauCeti.ModuleTower.transitionOfLE_def]
  rfl

/-- The power-kernel tower is pro-zero if and only if the increasing chain of kernels
stabilizes: one kernel contains the kernels of all powers. -/
theorem isProZero_powerKernelTower_iff (f : Module.End R M) :
    f.powerKernelTower.IsProZero ↔
      ∃ k : ℕ, ∀ n : ℕ, LinearMap.ker (f ^ n) ≤ LinearMap.ker (f ^ k) := by
  rw [TauCeti.ModuleTower.isProZero_iff_exists_transitionOfLE_eq_zero]
  constructor
  · intro h
    obtain ⟨m, hm, hzero⟩ := h 1
    have hstep : LinearMap.ker (f ^ m) ≤ LinearMap.ker (f ^ (m - 1)) := by
      intro x hx
      apply LinearMap.mem_ker.mpr
      calc
        (f ^ (m - 1)) x = (LinearMap.ker (f ^ 1)).subtype
            (f.powerKernelTower.transitionOfLE hm ⟨x, hx⟩) :=
          (f.powerKernelTower_transitionOfLE_apply hm ⟨x, hx⟩).symm
        _ = 0 := by rw [hzero]; rfl
    have hbound (j : ℕ) :
        LinearMap.ker (f ^ (m - 1 + j)) ≤ LinearMap.ker (f ^ (m - 1)) := by
      induction j with
      | zero => simp
      | succ j ih =>
        intro x hx
        have hfx : f x ∈ LinearMap.ker (f ^ (m - 1 + j)) := by
          simpa only [LinearMap.mem_ker, Nat.add_succ, pow_succ, mul_apply_eq_comp] using hx
        have hx' : x ∈ LinearMap.ker (f ^ m) := by
          rw [LinearMap.mem_ker, ← Nat.sub_add_cancel hm, pow_succ, mul_apply_eq_comp]
          exact ih hfx
        exact hstep hx'
    refine ⟨m - 1, fun n ↦ ?_⟩
    exact (f.iterateKer.monotone (Nat.le_add_left n (m - 1))).trans (hbound n)
  · rintro ⟨k, hk⟩ n
    refine ⟨n + k, Nat.le_add_right n k, ?_⟩
    apply LinearMap.ext
    intro x
    apply (LinearMap.ker (f ^ n)).subtype_injective
    have h := f.powerKernelTower_transitionOfLE_apply (Nat.le_add_right n k) x
    rw [Nat.add_sub_cancel_left] at h
    exact h.trans (LinearMap.mem_ker.mp (hk (n + k) x.property))

/-- Power-kernel towers of endomorphisms of Noetherian modules are pro-zero. -/
theorem isProZero_powerKernelTower_of_isNoetherian (f : Module.End R M) [IsNoetherian R M] :
    f.powerKernelTower.IsProZero := by
  obtain ⟨k, hk⟩ := Filter.eventually_atTop.mp f.eventually_iSup_ker_pow_eq
  exact f.isProZero_powerKernelTower_iff.mpr ⟨k, fun n ↦
    (le_iSup (fun j ↦ LinearMap.ker (f ^ j)) n).trans_eq (hk k le_rfl)⟩

/-- Nilpotence makes the power-kernel tower pro-zero, even for an infinitely generated module.
For scalar multiplication, this applies to any module killed by a fixed power of the scalar. -/
theorem isProZero_powerKernelTower_of_isNilpotent (f : Module.End R M) (hf : IsNilpotent f) :
    f.powerKernelTower.IsProZero := by
  obtain ⟨k, hk⟩ := hf
  exact f.isProZero_powerKernelTower_iff.mpr ⟨k, fun _ ↦ by simp [hk]⟩

end Module.End
