/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Submodule.Range
public import Mathlib.LinearAlgebra.Span.Defs

/-!
# Stabilising kernels and ranges of iterates

Once the decreasing chain `range f ⊇ range f² ⊇ ⋯` of an endomorphism `f` stops at stage `n`, all
higher powers have the same range (`range (f ^ n) = ⨅ m, range (f ^ m)`), and the kernel and range
of `f ^ n` together span the module. Dually, once the increasing chain `ker f ⊆ ker f² ⊆ ⋯` stops
at stage `n`, all higher powers have the same kernel (`ker (f ^ n) = ⨆ m, ker (f ^ m)`), and the
kernel and range of `f ^ n` are disjoint. Unlike Mathlib's
`LinearMap.eventually_codisjoint_ker_pow_range_pow` and
`Module.End.eventually_disjoint_ker_pow_range_pow`, no Artinian or Noetherian hypothesis is needed:
chain conditions only serve to make the two chains stop, and unlike `Module.End.ker_pow_constant`
the kernel stabilisation holds over an arbitrary semiring. When both chains have stopped, the
endomorphism restricts to a bijection on the stable range, giving the invertible part of the
Fitting splitting without finite-length assumptions. Finally, linear maps intertwining two
endomorphisms carry kernels and ranges of powers (and their unions and intersections) into those of
the target.
-/

public section

namespace LinearMap

variable {R M : Type*}

section AddCommMonoid

variable [Semiring R] [AddCommMonoid M] [Module R M] {f : Module.End R M} {n : ℕ}

/-- An endomorphism preserves the kernel of each of its powers. -/
theorem mapsTo_ker_pow (f : Module.End R M) (n : ℕ) :
    Set.MapsTo f (ker (f ^ n)) (ker (f ^ n)) := by
  intro x hx
  apply mem_ker.mpr
  have hcomm : (f ^ n) (f x) = f ((f ^ n) x) :=
    LinearMap.congr_fun (Commute.self_pow f n).eq.symm x
  rw [hcomm, mem_ker.mp hx, map_zero]

/-- An endomorphism preserves the range of each of its powers. -/
theorem mapsTo_range_pow (f : Module.End R M) (n : ℕ) :
    Set.MapsTo f (range (f ^ n)) (range (f ^ n)) := by
  rintro x ⟨y, rfl⟩
  exact ⟨f y, LinearMap.congr_fun (Commute.self_pow f n).eq.symm y⟩

/-- An endomorphism preserves the ascending union of the kernels of its powers. -/
theorem mapsTo_iSup_ker_pow (f : Module.End R M) :
    Set.MapsTo f (⨆ k, ker (f ^ k) : Submodule R M) (⨆ k, ker (f ^ k) : Submodule R M) := by
  intro x hx
  rw [SetLike.mem_coe] at hx ⊢
  obtain ⟨k, hk⟩ :=
    (Submodule.mem_iSup_of_directed (fun k ↦ ker (f ^ k)) f.iterateKer.monotone.directed_le).mp hx
  exact Submodule.mem_iSup_of_mem k (f.mapsTo_ker_pow k hk)

/-- An endomorphism preserves the intersection of the ranges of its powers. -/
theorem mapsTo_iInf_range_pow (f : Module.End R M) :
    Set.MapsTo f (⨅ k, range (f ^ k) : Submodule R M) (⨅ k, range (f ^ k) : Submodule R M) := by
  intro x hx
  rw [SetLike.mem_coe, Submodule.mem_iInf] at hx ⊢
  exact fun k ↦ f.mapsTo_range_pow k (hx k)

/-- Restricting an endomorphism to the kernel of its `n`th power gives an endomorphism
annihilated by the same power. -/
theorem pow_restrict_ker_pow_eq_zero (f : Module.End R M) (n : ℕ)
    (h : ∀ x ∈ ker (f ^ n), f x ∈ ker (f ^ n) := f.mapsTo_ker_pow n) :
    (f.restrict h : Module.End R (ker (f ^ n))) ^ n = 0 := by
  rw [Module.End.pow_restrict n h]
  ext x
  exact mem_ker.mp x.property

/-- If the kernel of `f ^ (n + 1)` equals that of `f ^ n`, the kernels of all higher powers of `f`
equal it too. This generalises `Module.End.ker_pow_constant` from division rings to arbitrary
semirings and additive commutative monoids. -/
theorem ker_pow_add_eq_of_ker_pow_succ_eq (h : ker (f ^ (n + 1)) = ker (f ^ n)) (m : ℕ) :
    ker (f ^ (n + m)) = ker (f ^ n) := by
  have hrec : ∀ k, ker (f ^ (k + 1)) = (ker (f ^ k)).comap f := fun k ↦ by
    rw [pow_succ, Module.End.mul_eq_comp, ker_comp]
  induction m with
  | zero => rfl
  | succ m ih => rw [← add_assoc, hrec, ih, ← hrec, h]

/-- If the kernel of `f ^ (n + 1)` equals that of `f ^ n`, the supremum of the kernels of all
powers of `f` equals `ker (f ^ n)`. -/
theorem iSup_ker_pow_eq_of_ker_pow_succ_eq (h : ker (f ^ (n + 1)) = ker (f ^ n)) :
    (⨆ m, ker (f ^ m)) = ker (f ^ n) := by
  refine le_antisymm (iSup_le fun m ↦ ?_) (le_iSup (fun m ↦ ker (f ^ m)) n)
  rcases le_or_gt m n with hmn | hnm
  · exact f.iterateKer.monotone hmn
  · rw [← Nat.add_sub_of_le hnm.le, ker_pow_add_eq_of_ker_pow_succ_eq h]

/-- If the kernel of `f ^ (n + 1)` equals that of `f ^ n`, the kernel and the range of `f ^ n` are
disjoint. -/
theorem disjoint_ker_pow_range_pow_of_ker_pow_succ_eq (h : ker (f ^ (n + 1)) = ker (f ^ n)) :
    Disjoint (ker (f ^ n)) (range (f ^ n)) := by
  rw [Submodule.disjoint_def]
  rintro x hx ⟨y, rfl⟩
  have hy : y ∈ ker (f ^ (n + n)) := by
    simpa only [mem_ker, pow_add, _root_.mul_apply_eq_comp] using hx
  rw [ker_pow_add_eq_of_ker_pow_succ_eq h] at hy
  exact mem_ker.mp hy

/-- Conversely, for `1 ≤ n`, if `ker (f ^ n)` and `range (f ^ n)` are disjoint then the kernel chain
has stabilized at `n`: `ker (f ^ (n + 1)) = ker (f ^ n)`. -/
theorem ker_pow_succ_eq_of_disjoint (hn : 1 ≤ n) (hdisj : Disjoint (ker (f ^ n)) (range (f ^ n))) :
    ker (f ^ (n + 1)) = ker (f ^ n) := by
  refine le_antisymm (fun x hx ↦ ?_) (f.iterateKer.monotone (Nat.le_succ n))
  rw [mem_ker, pow_succ', mul_apply_eq_comp] at hx
  exact mem_ker.mpr (Submodule.disjoint_def.mp hdisj _
    (f.iterateKer.monotone hn (by simpa using hx)) (mem_range_self (f ^ n) x))

/-- If the range of `f ^ (n + 1)` equals that of `f ^ n`, the ranges of all higher powers of `f`
equal it too. -/
theorem range_pow_add_eq_of_range_pow_succ_eq (h : range (f ^ (n + 1)) = range (f ^ n)) (m : ℕ) :
    range (f ^ (n + m)) = range (f ^ n) := by
  have hrec : ∀ k, range (f ^ (k + 1)) = (range (f ^ k)).map f := fun k => by
    rw [pow_succ', Module.End.mul_eq_comp, range_comp]
  induction m with
  | zero => rfl
  | succ m ih => rw [← add_assoc, hrec, ih, ← hrec, h]

/-- If the range of `f ^ (n + 1)` equals that of `f ^ n`, the infimum of the ranges of all powers
of `f` equals `range (f ^ n)`. -/
theorem iInf_range_pow_eq_of_range_pow_succ_eq (h : range (f ^ (n + 1)) = range (f ^ n)) :
    (⨅ m, range (f ^ m)) = range (f ^ n) := by
  refine le_antisymm (iInf_le (fun m ↦ range (f ^ m)) n) (le_iInf fun m ↦ ?_)
  rcases le_or_gt m n with hmn | hnm
  · exact f.iterateRange.monotone hmn
  · rw [← Nat.add_sub_of_le hnm.le, range_pow_add_eq_of_range_pow_succ_eq h]

/-- For `1 ≤ n`, if `ker (f ^ n)` and `range (f ^ n)` span the module then the range chain has
stabilized at `n`: `range (f ^ (n + 1)) = range (f ^ n)`. -/
theorem range_pow_succ_eq_of_codisjoint (hn : 1 ≤ n)
    (hcod : Codisjoint (ker (f ^ n)) (range (f ^ n))) :
    range (f ^ (n + 1)) = range (f ^ n) := by
  refine le_antisymm (f.iterateRange.monotone (Nat.le_succ n)) ?_
  rintro _ ⟨x, rfl⟩
  obtain ⟨u, _, hu, ⟨w, rfl⟩, rfl⟩ := Submodule.codisjoint_iff_exists_add_eq.mp hcod x
  refine ⟨(f ^ (n - 1)) w, ?_⟩
  rw [map_add, mem_ker.mp hu, zero_add, ← mul_apply_eq_comp, ← mul_apply_eq_comp,
    ← pow_add, ← pow_add]
  congr 2
  omega

/-- Restrictions of an endomorphism to equal invariant submodules have equivalent bijectivity. -/
theorem bijective_restrict_iff_of_eq {p q : Submodule R M} (hEq : p = q)
    {hp : ∀ x ∈ p, f x ∈ p} {hq : ∀ x ∈ q, f x ∈ q} :
    Function.Bijective (f.restrict hp) ↔ Function.Bijective (f.restrict hq) := by
  subst hEq
  exact Iff.rfl

end AddCommMonoid

section AddCommGroup

variable [Semiring R] [AddCommGroup M] [Module R M] {f : Module.End R M} {n : ℕ}

/-- If the range of `f ^ 2` equals that of `f`, the kernel and the range of `f` together span the
module. -/
theorem codisjoint_ker_range_of_range_sq_eq (h : range (f ^ 2) = range f) :
    Codisjoint (ker f) (range f) := by
  refine Submodule.codisjoint_iff_exists_add_eq.mpr fun x => ?_
  obtain ⟨z, hz⟩ : f x ∈ range (f ^ 2) := h ▸ mem_range_self f x
  rw [sq, mul_apply_eq_comp] at hz
  exact ⟨x - f z, f z, by simp [hz], mem_range_self f z, sub_add_cancel x _⟩

/-- If the range of `f ^ (n + 1)` equals that of `f ^ n`, the kernel and the range of `f ^ n`
together span the module. -/
theorem codisjoint_ker_pow_range_pow_of_range_pow_succ_eq
    (h : range (f ^ (n + 1)) = range (f ^ n)) :
    Codisjoint (ker (f ^ n)) (range (f ^ n)) :=
  codisjoint_ker_range_of_range_sq_eq <| by
    rw [← pow_mul, mul_two, range_pow_add_eq_of_range_pow_succ_eq h]

end AddCommGroup

section Ring

variable [Ring R] [AddCommGroup M] [Module R M]

/-- If both the kernel and range chains stop at `n`, the endomorphism restricts to a
bijection on the stable range. This is the invertible part of the Fitting decomposition;
no finite-length hypothesis is required once stabilization is known. -/
theorem bijective_restrict_range_pow_of_stable (f : Module.End R M) (n : ℕ)
    (hk : ker (f ^ (n + 1)) = ker (f ^ n))
    (hr : range (f ^ (n + 1)) = range (f ^ n))
    (h : ∀ x ∈ range (f ^ n), f x ∈ range (f ^ n) := f.mapsTo_range_pow n) :
    Function.Bijective (f.restrict h : range (f ^ n) →ₗ[R] range (f ^ n)) := by
  constructor
  · apply LinearMap.ker_eq_bot.mp
    apply le_antisymm _ bot_le
    intro x hx
    obtain ⟨y, hy⟩ := x.property
    have hfy : (f ^ (n + 1)) y = 0 := by
      simpa only [pow_succ', mul_apply_eq_comp, hy,
        LinearMap.coe_restrict_apply, ZeroMemClass.coe_zero] using
        congrArg Subtype.val (LinearMap.mem_ker.mp hx)
    have hy0 := LinearMap.mem_ker.mp (hk ▸ LinearMap.mem_ker.mpr hfy)
    exact Subtype.ext (hy ▸ hy0)
  · intro x
    have hx : (x : M) ∈ range (f ^ (n + 1)) := by
      rw [hr]
      exact x.property
    obtain ⟨y, hy⟩ := hx
    refine ⟨⟨(f ^ n) y, mem_range_self _ _⟩, Subtype.ext ?_⟩
    simpa only [LinearMap.restrict_apply, pow_succ', mul_apply_eq_comp] using hy

end Ring

end LinearMap

namespace Module.End

variable {R M N : Type*} [Semiring R] [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N]

/-- An intertwiner `f ∘ₗ T_M = T_N ∘ₗ f` maps `ker (T_M ^ k)` into `ker (T_N ^ k)`. -/
theorem map_ker_pow_le_of_comp_eq {T_M : End R M} {T_N : End R N} {f : M →ₗ[R] N}
    (hf : f ∘ₗ T_M = T_N ∘ₗ f) (k : ℕ) :
    (LinearMap.ker (T_M ^ k)).map f ≤ LinearMap.ker (T_N ^ k) := by
  rintro _ ⟨x, hx, rfl⟩
  rw [LinearMap.mem_ker, ← LinearMap.comp_apply,
    Module.End.commute_pow_left_of_commute hf.symm k, LinearMap.comp_apply,
    LinearMap.mem_ker.mp hx, map_zero]

/-- An intertwiner `f ∘ₗ T_M = T_N ∘ₗ f` maps `range (T_M ^ k)` into `range (T_N ^ k)`. -/
theorem map_range_pow_le_of_comp_eq {T_M : End R M} {T_N : End R N} {f : M →ₗ[R] N}
    (hf : f ∘ₗ T_M = T_N ∘ₗ f) (k : ℕ) :
    (LinearMap.range (T_M ^ k)).map f ≤ LinearMap.range (T_N ^ k) := by
  rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
  exact ⟨f x, LinearMap.congr_fun (Module.End.commute_pow_left_of_commute hf.symm k) x⟩

/-- An intertwiner `f ∘ₗ T_M = T_N ∘ₗ f` maps `⨆ k, ker (T_M ^ k)` into `⨆ k, ker (T_N ^ k)`. -/
theorem map_iSup_ker_pow_le_of_comp_eq {T_M : End R M} {T_N : End R N} {f : M →ₗ[R] N}
    (hf : f ∘ₗ T_M = T_N ∘ₗ f) :
    (⨆ k, LinearMap.ker (T_M ^ k)).map f ≤ ⨆ k, LinearMap.ker (T_N ^ k) := by
  rw [Submodule.map_iSup]
  exact iSup_mono fun k ↦ map_ker_pow_le_of_comp_eq hf k

/-- An intertwiner `f ∘ₗ T_M = T_N ∘ₗ f` maps `⨅ k, range (T_M ^ k)` into
`⨅ k, range (T_N ^ k)`. -/
theorem map_iInf_range_pow_le_of_comp_eq {T_M : End R M} {T_N : End R N} {f : M →ₗ[R] N}
    (hf : f ∘ₗ T_M = T_N ∘ₗ f) :
    (⨅ k, LinearMap.range (T_M ^ k)).map f ≤ ⨅ k, LinearMap.range (T_N ^ k) :=
  le_iInf fun k ↦ (Submodule.map_mono (iInf_le _ k)).trans (map_range_pow_le_of_comp_eq hf k)

end Module.End

end
