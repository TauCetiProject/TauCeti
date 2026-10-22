/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.DirectSum.Internal
public import TauCeti.Algebra.Lie.AdjointAction.GradingAut
public import TauCeti.Algebra.Lie.Sl2.EigenspaceMap
public import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Defs

/-!
# The Slodowy slice of an `sl₂` triple and its contracting action

Let `(h, e, f)` be an `sl₂` triple in a finite-dimensional Lie algebra `L` over a field `K` of
characteristic zero. The **Slodowy slice** at `e` is the affine subspace `S = e + ker (ad f)` of
`L`. Its direction is complementary to the tangent space `[L, e]` of the adjoint orbit of `e`
(`IsSl2Triple.isCompl_range_ad_e_ker_ad_f`), so `S` is a transverse slice to that orbit.

Over an algebraically closed field `ad h` is diagonalizable with integer eigenvalues, and for a
unit `c` the grading automorphism `TauCeti.gradingAut` acts on the `j`-eigenspace `L(j)` by
`c ^ j`. If `L` is the Lie algebra of an algebraic group `G` and `λ` is a cocharacter of `G` with
differential `h`, this automorphism is `Ad (λ c)`. The **contracting action** is

`c • x = c ^ 2 • Ad (λ c⁻¹) x`,

which acts on `L(j)` by `c ^ (2 - j)`. It fixes `e ∈ L(2)`, and it preserves `S`. The point of the
construction is that its weights on the direction of `S` are all at least `2`. The kernel of
`ad f` consists of lowest weight vectors for the triple, so it is the direct sum of its
intersections with the eigenspaces `L(-n)` for `n : ℕ`
(`IsSl2Triple.ker_toEnd_f_eq_iSup_inf_eigenspace`), and the contracting action has weight
`n + 2` on `ker (ad f) ⊓ L(-n)`. Hence for every `x ∈ S` the orbit map `c ↦ c • x` is the
restriction to `Kˣ` of a polynomial map `K → S` of the form `c ↦ e + ∑ₙ c ^ (n + 2) • vₙ`. It
extends to `c = 0` with value `e`, so the action contracts `S` to `e`
(`IsSl2Triple.exists_contractingAction_eq`).

## Main definitions

* `TauCeti.slodowySlice K e f`: the affine subspace `e + ker (ad f)` of `L`.
* `IsSl2Triple.contractingAction`: the action of `Kˣ` on `L` by `c ↦ c ^ 2 • gradingAut c⁻¹`.

## Main results

* `IsSl2Triple.ker_toEnd_f_eq_iSup_inf_eigenspace`: in a finite-dimensional module over an
  algebraically closed field, the kernel of `f` is spanned by the vectors it contains of weight
  `-n`, `n : ℕ`.
* `IsSl2Triple.contractingAction_apply_of_mem`: the contracting action has weight `2 - j` on
  `L(j)`. In particular it fixes `e` (`IsSl2Triple.contractingAction_apply_e`).
* `IsSl2Triple.contractingAction_apply_of_mem_ker_inf`: its weight on `ker (ad f) ⊓ L(-n)` is
  `n + 2`.
* `IsSl2Triple.exists_contractingAction_eq`: the orbit map of a point of the slice is polynomial,
  with value `e` at `0`.
* `IsSl2Triple.contractingAction_apply_mem_slodowySlice`: the contracting action preserves the
  slice.

## References

* P. Slodowy, *Simple Singularities and Simple Algebraic Groups*, Lecture Notes in Mathematics
  815, Springer, 1980, §7.4.
* W. L. Gan and V. Ginzburg, *Quantization of Slodowy slices*, Int. Math. Res. Not. 2002,
  no. 5, 243–255, §2.
-/

public section

open LieAlgebra LieModule Module

namespace TauCeti

section Slice

variable (R : Type*) {L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]

/-- **The Slodowy slice** `e + ker (ad f)`, as an affine subspace of `L`. When `(h, e, f)` is an
`sl₂` triple this is a transverse slice to the adjoint orbit of `e` at `e`. For `f = 0`, in
particular in the degenerate case `e = f = 0`, it is all of `L`
(`TauCeti.slodowySlice_zero_right`). -/
def slodowySlice (e f : L) : AffineSubspace R L :=
  AffineSubspace.mk' e (LinearMap.ker (ad R L f))

variable {R} {e f x : L}

/-- A point `x` lies in the Slodowy slice `e + ker (ad f)` exactly when `⁅f, x - e⁆ = 0`. -/
@[simp]
theorem mem_slodowySlice : x ∈ slodowySlice R e f ↔ ⁅f, x - e⁆ = 0 := by
  rw [slodowySlice, AffineSubspace.mem_mk', vsub_eq_sub, LinearMap.mem_ker, ad_apply]

/-- The Slodowy slice `e + ker (ad f)` passes through `e`. -/
theorem self_mem_slodowySlice : e ∈ slodowySlice R e f :=
  AffineSubspace.self_mem_mk' _ _

/-- The direction of the Slodowy slice `e + ker (ad f)` is the centralizer `ker (ad f)` of `f`. -/
@[simp]
theorem direction_slodowySlice : (slodowySlice R e f).direction = LinearMap.ker (ad R L f) :=
  AffineSubspace.direction_mk' _ _

/-- For `f = 0` the Slodowy slice is all of `L`. -/
@[simp]
theorem slodowySlice_zero_right : slodowySlice R e (0 : L) = ⊤ :=
  eq_top_iff.2 fun x _ ↦ by simp

end Slice

end TauCeti

open TauCeti

namespace IsSl2Triple

/-! ### The weights of `h` on the lowest weight vectors -/

section Weights

variable {K L M : Type*} [Field K] [CharZero K] [IsAlgClosed K] [LieRing L] [LieAlgebra K L]
  [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M] [FiniteDimensional K M]
  {h e f : L}

/-- **The kernel of the lowering operator is graded by `-ℕ`.** In a finite-dimensional module over
an algebraically closed field of characteristic zero, the kernel of `f` is spanned by the vectors
it contains of weight `-n` for `h`, `n : ℕ`.

The integer eigenspaces of `h` span the module, and `f` lowers weights by `2`, so its kernel is
spanned by its homogeneous parts. A nonzero vector killed by `f` has weight in `-ℕ`
(`IsSl2Triple.disjoint_ker_toEnd_f_eigenspace`). -/
theorem ker_toEnd_f_eq_iSup_inf_eigenspace (t : IsSl2Triple h e f) :
    LinearMap.ker (toEnd K L M f) =
      ⨆ n : ℕ, LinearMap.ker (toEnd K L M f) ⊓ (toEnd K L M h).eigenspace (-(n : K)) := by
  have hsub : Function.Injective fun z : ℤ ↦ (z : K) - 2 := fun a b hab ↦ by
    simpa using hab
  refine (LinearMap.ker_eq_iSup_inf_of_map_le (toEnd K L M f)
    (A := fun z : ℤ ↦ (toEnd K L M h).eigenspace (z : K))
    (A' := fun z : ℤ ↦ (toEnd K L M h).eigenspace ((z : K) - 2))
    (isInternal_eigenspace_toEnd_intCast t).submodule_iSup_eq_top
    ((toEnd K L M h).eigenspaces_iSupIndep.comp hsub)
    fun z ↦ Submodule.map_le_iff_le_comap.2 fun v hv ↦ by
      rw [Submodule.mem_comap, toEnd_apply_apply]
      exact lie_mem_eigenspace_sub_two t hv).trans ?_
  refine le_antisymm (iSup_le fun z ↦ ?_) (iSup_le fun n ↦ le_iSup_of_le (-(n : ℤ)) (by simp))
  by_cases hz : 0 < z
  · have hne (n : ℕ) : (z : K) ≠ -(n : K) := by
      exact_mod_cast (by omega : z ≠ -(n : ℤ))
    rw [(t.disjoint_ker_toEnd_f_eigenspace hne).eq_bot]
    exact bot_le
  · obtain ⟨n, rfl⟩ := Int.exists_eq_neg_ofNat (not_lt.1 hz)
    exact le_iSup_of_le n (by simp)

end Weights

/-! ### The contracting action on the slice -/

section Contraction

variable {K L : Type*} [Field K] [CharZero K] [IsAlgClosed K] [LieRing L] [LieAlgebra K L]
  [FiniteDimensional K L] {h e f : L}

/-- Over an algebraically closed field of characteristic zero, `L` is the internal direct sum of
the integer eigenspaces of `ad h`. This is the hypothesis under which `TauCeti.gradingAut` is
defined. -/
theorem isInternal_eigenspace_ad_intCast (t : IsSl2Triple h e f) :
    DirectSum.IsInternal fun j : ℤ ↦ (ad K L h).eigenspace (j : K) :=
  -- `ad K L` is by definition the action `toEnd K L L` of `L` on itself.
  isInternal_eigenspace_toEnd_intCast (M := L) t

/-- **The contracting action** of `Kˣ` on `L` attached to an `sl₂` triple `(h, e, f)`:
`c` acts by `c ^ 2 • gradingAut c⁻¹`, that is, by `c ^ (2 - j)` on the `j`-eigenspace of `ad h`
(`IsSl2Triple.contractingAction_apply_of_mem`). For an algebraic group with Lie algebra `L` and a
cocharacter `λ` with differential `h` this is `c ↦ c ^ 2 • Ad (λ c⁻¹)`. It fixes `e` and preserves
the Slodowy slice `e + ker (ad f)`, on which it extends to `c = 0`
(`IsSl2Triple.exists_contractingAction_eq`). -/
noncomputable def contractingAction (t : IsSl2Triple h e f) : Kˣ →* Module.End K L where
  toFun c := ((c : K) ^ 2) •
    ((gradingAut t.isInternal_eigenspace_ad_intCast c⁻¹ : L ≃ₗ[K] L) : L →ₗ[K] L)
  map_one' := by
    ext x
    simp
  map_mul' c d := by
    ext x
    simp only [mul_inv_rev, Units.val_mul, LinearMap.smul_apply, LinearEquiv.coe_coe,
      LieEquiv.coe_toLinearEquiv, Module.End.mul_apply, map_smul]
    rw [mul_comm d⁻¹, gradingAut_mul_apply, smul_smul, mul_pow, mul_comm ((c : K) ^ 2)]

/-- **The weights of the contracting action.** The unit `c` acts on the `j`-eigenspace of `ad h`
by `c ^ (2 - j)`. -/
theorem contractingAction_apply_of_mem (t : IsSl2Triple h e f) (c : Kˣ) {j : ℤ} {x : L}
    (hx : x ∈ (ad K L h).eigenspace (j : K)) :
    t.contractingAction c x = (c : K) ^ (2 - j) • x := by
  simp only [contractingAction, MonoidHom.coe_mk, OneHom.coe_mk, LinearMap.smul_apply,
    LinearEquiv.coe_coe, LieEquiv.coe_toLinearEquiv]
  rw [gradingAut_apply_of_mem _ _ hx, smul_smul, inv_zpow', Units.val_zpow_eq_zpow_val,
    zpow_sub₀ (Units.ne_zero c), div_eq_mul_inv, ← zpow_neg, zpow_ofNat]

/-- The contracting action fixes `e`, which has weight `2` for `ad h`. -/
@[simp]
theorem contractingAction_apply_e (t : IsSl2Triple h e f) (c : Kˣ) :
    t.contractingAction c e = e := by
  have he : e ∈ (ad K L h).eigenspace ((2 : ℤ) : K) := by
    rw [Module.End.mem_eigenspace_iff, ad_apply, Int.cast_ofNat]
    exact t.lie_h_e_smul K
  rw [t.contractingAction_apply_of_mem c he, sub_self, zpow_zero, one_smul]

/-- **The weights on the slice are positive.** The contracting action has weight `n + 2` on the
vectors of `ker (ad f)` of weight `-n` for `ad h`. -/
theorem contractingAction_apply_of_mem_ker_inf (t : IsSl2Triple h e f) (c : Kˣ) {n : ℕ} {v : L}
    (hv : v ∈ LinearMap.ker (ad K L f) ⊓ (ad K L h).eigenspace (-(n : K))) :
    t.contractingAction c v = (c : K) ^ (n + 2) • v := by
  have hv' : v ∈ (ad K L h).eigenspace ((-(n : ℤ) : ℤ) : K) := by
    simpa using hv.2
  rw [t.contractingAction_apply_of_mem c hv', sub_neg_eq_add, add_comm, ← zpow_natCast,
    Nat.cast_add, Nat.cast_ofNat]

/-- **The contracting action extends to `c = 0` on the slice.** A point `x` of the Slodowy slice
is `e + ∑ₙ vₙ` with `vₙ ∈ ker (ad f)` of weight `-n` for `ad h`, and the unit `c` moves it to
`e + ∑ₙ c ^ (n + 2) • vₙ`. So the orbit map `c ↦ c • x` is the restriction of a polynomial map
taking the value `e` at `c = 0`. -/
theorem exists_contractingAction_eq (t : IsSl2Triple h e f) {x : L}
    (hx : x ∈ slodowySlice K e f) :
    ∃ v : ℕ →₀ L, (∀ n : ℕ, v n ∈ LinearMap.ker (ad K L f) ⊓ (ad K L h).eigenspace (-(n : K))) ∧
      x = e + v.sum (fun _ w ↦ w) ∧
      ∀ c : Kˣ, t.contractingAction c x = e + v.sum fun n w ↦ (c : K) ^ (n + 2) • w := by
  have hker : x - e ∈ LinearMap.ker (ad K L f) := by
    rw [LinearMap.mem_ker, ad_apply]
    exact mem_slodowySlice.1 hx
  -- `ad K L` is by definition the action `toEnd K L L` of `L` on itself.
  rw [show LinearMap.ker (ad K L f) = _ from t.ker_toEnd_f_eq_iSup_inf_eigenspace (M := L)] at hker
  obtain ⟨v, hv, hsum⟩ := (Submodule.mem_iSup_iff_exists_finsupp _ _).1 hker
  have hx' : x = e + v.sum (fun _ w ↦ w) := by rw [hsum, add_sub_cancel]
  refine ⟨v, hv, hx', fun c ↦ ?_⟩
  rw [hx', map_add, contractingAction_apply_e, Finsupp.sum, map_sum, Finsupp.sum]
  congr 1
  exact Finset.sum_congr rfl fun n _ ↦ t.contractingAction_apply_of_mem_ker_inf c (hv n)

/-- **The contracting action preserves the Slodowy slice.** -/
theorem contractingAction_apply_mem_slodowySlice (t : IsSl2Triple h e f) (c : Kˣ) {x : L}
    (hx : x ∈ slodowySlice K e f) : t.contractingAction c x ∈ slodowySlice K e f := by
  obtain ⟨v, hv, -, hc⟩ := t.exists_contractingAction_eq hx
  rw [hc c, mem_slodowySlice, add_sub_cancel_left, Finsupp.sum, ← ad_apply (R := K), map_sum]
  exact Finset.sum_eq_zero fun n _ ↦ by
    rw [map_smul, (LinearMap.mem_ker.1 (hv n).1), smul_zero]

end Contraction

end IsSl2Triple
