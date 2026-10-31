/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.AdjointAction.GradingAut
public import TauCeti.Algebra.Lie.Sl2.EigenspaceMap
public import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Defs
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import TauCeti.Algebra.Lie.Weights.Eigenvector

/-!
# The Slodowy slice of an `sl₂` triple: contracting action and transversality

Let `(h, e, f)` be an `sl₂` triple in a finite-dimensional Lie algebra `L` over a field `K` of
characteristic zero. The **Slodowy slice** at `e` is the affine subspace `S = e + ker (ad f)` of
`L`. Its direction is complementary to the tangent space `[L, e]` of the adjoint orbit of `e`
(`IsSl2Triple.isCompl_range_ad_e_ker_ad_f`), so `S` is transverse to that orbit at `e` at the
level of tangent spaces.

Over every characteristic-zero field `ad h` is diagonalizable with integer eigenvalues, and for a
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

The slice is transverse not only to the orbit of `e` but to the adjoint orbit of each of its
points: for every `x ∈ S` the tangent space `[L, x]` of the orbit of `x` and the direction
`ker (ad f)` of `S` span `L` (`IsSl2Triple.codisjoint_range_ad_ker_ad_f`). If `L` is the Lie
algebra of an algebraic group `G`, this is the surjectivity of the differential of the action map
`G × S → L` at every point of `G × S`. The proof grades by the eigenvalues of `ad h`: the point
`x` is `e` plus vectors of nonpositive weight, and the graded form of `L = [L, e] ⊕ ker (ad f)`
(`IsSl2Triple.eigenspace_add_two_le_map_toEnd_e_sup_ker_toEnd_f`) lets one absorb each weight
space by induction from the lowest weight. Consequently the two tangent spaces meet in dimension
`dim ker (ad e) - dim ker (ad x)`, and no point of the slice has a larger centralizer than `e`
(`IsSl2Triple.finrank_ker_ad_le_finrank_ker_ad_e`). All three statements hold for the action on
any finite-dimensional module.

## Main definitions

* `TauCeti.slodowySlice K e f`: the affine subspace `e + ker (ad f)` of `L`.
* `IsSl2Triple.contractingAction`: the action of `Kˣ` on `L` by `c ↦ c ^ 2 • gradingAut c⁻¹`.

## Main results

* `IsSl2Triple.contractingAction_apply_of_mem`: the contracting action has weight `2 - j` on
  `L(j)`. In particular it fixes `e` (`IsSl2Triple.contractingAction_apply_e`).
* `IsSl2Triple.exists_contractingAction_eq`: the orbit map of a point of the slice is polynomial,
  with value `e` at `0`.
* `IsSl2Triple.contractingAction_apply_mem_slodowySlice`: the contracting action preserves the
  slice.
* `IsSl2Triple.codisjoint_range_toEnd_ker_toEnd_f`, `IsSl2Triple.codisjoint_range_ad_ker_ad_f`:
  the slice is transverse to every orbit it meets.
* `IsSl2Triple.finrank_range_toEnd_inf_ker_toEnd_f_add_finrank_ker_toEnd`,
  `IsSl2Triple.finrank_range_ad_inf_ker_ad_f_add_finrank_ker_ad`: the dimension of the
  intersection of the two tangent spaces.

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
`sl₂` triple in a finite-dimensional Lie algebra over a field of characteristic zero, its direction
`ker (ad f)` is complementary to `[L, e]` (`IsSl2Triple.isCompl_range_ad_e_ker_ad_f`). For `f = 0`,
in particular in the degenerate case `e = f = 0`, it is all of `L`
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

/-! ### The contracting action on the slice -/

section Contraction

variable {K L : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
  [FiniteDimensional K L] {h e f : L}

/-- **The contracting action** of `Kˣ` on `L` attached to an `sl₂` triple `(h, e, f)`:
`c` acts by `c ^ 2 • gradingAut c⁻¹`, that is, by `c ^ (2 - j)` on the `j`-eigenspace of `ad h`
(`IsSl2Triple.contractingAction_apply_of_mem`). For an algebraic group with Lie algebra `L` and a
cocharacter `λ` with differential `h` this is `c ↦ c ^ 2 • Ad (λ c⁻¹)`. It fixes `e` and preserves
the Slodowy slice `e + ker (ad f)`, on which it extends to `c = 0`
(`IsSl2Triple.exists_contractingAction_eq`). -/
noncomputable def contractingAction (t : IsSl2Triple h e f) : Kˣ →* Module.End K L where
  toFun c := ((c : K) ^ 2) •
    ((gradingAut (ad_eq_toEnd K L ▸ isInternal_eigenspace_toEnd_intCast (M := L) t) c⁻¹ :
      L ≃ₗ[K] L) : L →ₗ[K] L)
  map_one' := by
    ext x
    simp
  map_mul' c d := by
    ext x
    simp only [mul_inv_rev, Units.val_mul, LinearMap.smul_apply, LinearEquiv.coe_coe,
      LieEquiv.coe_toLinearEquiv, Module.End.mul_apply, map_smul]
    rw [mul_comm d⁻¹, gradingAut_mul_apply, smul_smul]
    ring_nf

/-- **The weights of the contracting action.** The unit `c` acts on the `j`-eigenspace of `ad h`
by `c ^ (2 - j)`. -/
theorem contractingAction_apply_of_mem (t : IsSl2Triple h e f) (c : Kˣ) {j : ℤ} {x : L}
    (hx : x ∈ (ad K L h).eigenspace (j : K)) :
    t.contractingAction c x = (c : K) ^ (2 - j) • x := by
  simp only [contractingAction, MonoidHom.coe_mk, OneHom.coe_mk, LinearMap.smul_apply,
    LinearEquiv.coe_coe, LieEquiv.coe_toLinearEquiv]
  rw [gradingAut_apply_of_mem _ _ hx, smul_smul]
  simp [zpow_sub₀ (Units.ne_zero c), div_eq_mul_inv]

/-- The contracting action fixes `e`, which has weight `2` for `ad h`. -/
@[simp]
theorem contractingAction_apply_e (t : IsSl2Triple h e f) (c : Kˣ) :
    t.contractingAction c e = e := by
  have he : e ∈ (ad K L h).eigenspace ((2 : ℤ) : K) := by
    rw [Module.End.mem_eigenspace_iff, ad_apply, Int.cast_ofNat]
    exact t.lie_h_e_smul K
  rw [t.contractingAction_apply_of_mem c he, sub_self, zpow_zero, one_smul]

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
  have hdecomp := t.ker_toEnd_f_eq_iSup_inf_eigenspace (K := K) (M := L)
  rw [← ad_eq_toEnd] at hdecomp
  rw [hdecomp] at hker
  obtain ⟨v, hv, hsum⟩ := (Submodule.mem_iSup_iff_exists_finsupp _ _).1 hker
  have hx' : x = e + v.sum (fun _ w ↦ w) := by rw [hsum, add_sub_cancel]
  refine ⟨v, hv, hx', fun c ↦ ?_⟩
  rw [hx', map_add, contractingAction_apply_e, Finsupp.sum, map_sum, Finsupp.sum]
  congr 1
  refine Finset.sum_congr rfl fun n _ ↦ ?_
  rw [t.contractingAction_apply_of_mem c (j := -n) (by simpa using (hv n).2), sub_neg_eq_add,
    add_comm]
  norm_cast

/-- **The contracting action preserves the Slodowy slice.** -/
theorem contractingAction_apply_mem_slodowySlice (t : IsSl2Triple h e f) (c : Kˣ) {x : L}
    (hx : x ∈ slodowySlice K e f) : t.contractingAction c x ∈ slodowySlice K e f := by
  obtain ⟨v, hv, -, hc⟩ := t.exists_contractingAction_eq hx
  rw [hc c, mem_slodowySlice, add_sub_cancel_left, Finsupp.sum, ← ad_apply (R := K), map_sum]
  exact Finset.sum_eq_zero fun n _ ↦ by
    rw [map_smul, (LinearMap.mem_ker.1 (hv n).1), smul_zero]

end Contraction

/-! ### Transversality of the slice to every orbit it meets -/

section Transversal

variable {K L M : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
  [FiniteDimensional K L] [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]
  [FiniteDimensional K M] {h e f x : L}

/-- For `x` in the Slodowy slice, every eigenspace `M_k` of `h` at an integer `k` lies in
`x • M + ker f`. This is proved by induction on `k`, starting below the lowest weight of `M`. -/
private theorem eigenspace_intCast_le_range_toEnd_sup_ker_toEnd_f (t : IsSl2Triple h e f)
    (hx : x ∈ slodowySlice K e f) (k : ℤ) :
    (toEnd K L M h).eigenspace (k : K) ≤
      LinearMap.range (toEnd K L M x) ⊔ LinearMap.ker (toEnd K L M f) := by
  set N := LinearMap.range (toEnd K L M x) ⊔ LinearMap.ker (toEnd K L M f)
  -- `x - e` is a sum of vectors of `ker (ad f)` of weights `-n` with `n : ℕ`.
  have hv : x - e ∈ ⨆ n : ℕ, LinearMap.ker (ad K L f) ⊓ (ad K L h).eigenspace (-(n : K)) := by
    have hdecomp := t.ker_toEnd_f_eq_iSup_inf_eigenspace (K := K) (M := L)
    rw [← ad_eq_toEnd] at hdecomp
    rw [← hdecomp, LinearMap.mem_ker, ad_apply]
    exact mem_slodowySlice.1 hx
  -- The weights of `h` on `M` are bounded below.
  obtain ⟨B, hB⟩ : ∃ B : ℤ, ∀ j : ℤ, j < B → (toEnd K L M h).eigenspace (j : K) = ⊥ := by
    obtain ⟨B, hB⟩ := ((Module.End.finite_hasEigenvalue (toEnd K L M h)).preimage
      Int.cast_injective.injOn).bddBelow
    exact ⟨B, fun j hj ↦ not_not.1 fun hne ↦ (hB hne).not_gt hj⟩
  -- The inductive step: write `y ∈ M_k` as `⁅e, w⁆ + z` with `w ∈ M_(k - 2)` and `z ∈ ker f`.
  -- Then `⁅e, w⁆ = ⁅x, w⁆ - ⁅x - e, w⁆`, and `⁅x - e, w⁆` only has weights below `k`.
  have step (k : ℤ) (ih : ∀ j < k, (toEnd K L M h).eigenspace (j : K) ≤ N) :
      (toEnd K L M h).eigenspace (k : K) ≤ N := by
    intro y hy
    rw [show ((k : ℤ) : K) = ((k - 2 : ℤ) : K) + 2 by push_cast; ring] at hy
    obtain ⟨-, ⟨w, hw, rfl⟩, z, hz, rfl⟩ :=
      Submodule.mem_sup.1 <|
        t.eigenspace_add_two_le_map_toEnd_e_sup_ker_toEnd_f ((k - 2 : ℤ) : K) hy
    refine N.add_mem ?_ (Submodule.mem_sup_right hz.1)
    rw [show toEnd K L M e w = toEnd K L M x w - ⁅x - e, w⁆ by
      rw [toEnd_apply_apply, toEnd_apply_apply, sub_lie, sub_sub_cancel]]
    refine N.sub_mem (Submodule.mem_sup_left ⟨w, rfl⟩) ?_
    refine Submodule.iSup_induction _ (motive := fun u ↦ ⁅u, w⁆ ∈ N) hv (fun n u hu ↦ ?_)
      (by simp) fun u₁ u₂ h₁ h₂ ↦ by rw [add_lie]; exact N.add_mem h₁ h₂
    refine ih (k - 2 - n) (by omega) ?_
    convert TauCeti.lie_mem_eigenspace_toEnd_add hu.2 hw using 2
    push_cast
    ring
  have key (m : ℕ) : ∀ j : ℤ, j < B + m → (toEnd K L M h).eigenspace (j : K) ≤ N := by
    induction m with
    | zero => exact fun j hj ↦ by simp [hB j (by simpa using hj)]
    | succ m ih =>
      intro j hj
      by_cases hjm : j < B + m
      · exact ih j hjm
      · exact step j fun i hi ↦ ih i (by push_cast at hj; omega)
  exact key ((k - B).toNat + 1) k (by push_cast; omega)

/-- **The Slodowy slice is transverse to every orbit it meets.** For an `sl₂` triple `(h, e, f)`
and every point `x` of the slice `e + ker (ad f)`, the range of `x` and the kernel of `f` acting on
a finite-dimensional module span the module. At `x = e` this is the codisjointness half of
`IsSl2Triple.isCompl_range_toEnd_e_ker_toEnd_f`. -/
theorem codisjoint_range_toEnd_ker_toEnd_f (t : IsSl2Triple h e f)
    (hx : x ∈ slodowySlice K e f) :
    Codisjoint (LinearMap.range (toEnd K L M x)) (LinearMap.ker (toEnd K L M f)) := by
  rw [codisjoint_iff, eq_top_iff,
    ← (TauCeti.isInternal_eigenspace_toEnd_intCast t).submodule_iSup_eq_top]
  exact iSup_le (t.eigenspace_intCast_le_range_toEnd_sup_ker_toEnd_f hx)

/-- **The dimension of the transverse intersection.** For every point `x` of the Slodowy slice
`e + ker (ad f)`, the intersection of the range of `x` with the kernel of `f` acting on a
finite-dimensional module has dimension `dim ker e - dim ker x`. -/
theorem finrank_range_toEnd_inf_ker_toEnd_f_add_finrank_ker_toEnd (t : IsSl2Triple h e f)
    (hx : x ∈ slodowySlice K e f) :
    finrank K ↥(LinearMap.range (toEnd K L M x) ⊓ LinearMap.ker (toEnd K L M f)) +
      finrank K (LinearMap.ker (toEnd K L M x)) = finrank K (LinearMap.ker (toEnd K L M e)) := by
  have h₁ := Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.range (toEnd K L M x))
    (LinearMap.ker (toEnd K L M f))
  rw [(t.codisjoint_range_toEnd_ker_toEnd_f hx).eq_top, finrank_top] at h₁
  have h₂ := LinearMap.finrank_range_add_finrank_ker (toEnd K L M x)
  rw [t.finrank_ker_toEnd_e_eq_finrank_ker_toEnd_f]
  omega

/-- The kernel of `e` has the largest dimension among the kernels of the points of the Slodowy
slice `e + ker (ad f)` acting on a finite-dimensional module. -/
theorem finrank_ker_toEnd_le_finrank_ker_toEnd_e (t : IsSl2Triple h e f)
    (hx : x ∈ slodowySlice K e f) :
    finrank K (LinearMap.ker (toEnd K L M x)) ≤ finrank K (LinearMap.ker (toEnd K L M e)) := by
  have := t.finrank_range_toEnd_inf_ker_toEnd_f_add_finrank_ker_toEnd (M := M) hx
  omega

/-- **The Slodowy slice is transverse to every adjoint orbit it meets.** For every point `x` of
the slice `e + ker (ad f)`, the tangent space `[L, x]` of the adjoint orbit of `x` and the
direction `ker (ad f)` of the slice span `L`. -/
theorem codisjoint_range_ad_ker_ad_f (t : IsSl2Triple h e f) (hx : x ∈ slodowySlice K e f) :
    Codisjoint (LinearMap.range (ad K L x)) (LinearMap.ker (ad K L f)) :=
  -- `ad K L` is by definition the action `toEnd K L L` of `L` on itself.
  t.codisjoint_range_toEnd_ker_toEnd_f (M := L) hx

/-- **The dimension of the transverse intersection.** For every point `x` of the Slodowy slice
`e + ker (ad f)`, the intersection of the tangent space `[L, x]` of the adjoint orbit of `x` with
the direction `ker (ad f)` of the slice has dimension `dim ker (ad e) - dim ker (ad x)`, the
difference of the dimensions of the orbits of `x` and of `e`. -/
theorem finrank_range_ad_inf_ker_ad_f_add_finrank_ker_ad (t : IsSl2Triple h e f)
    (hx : x ∈ slodowySlice K e f) :
    finrank K ↥(LinearMap.range (ad K L x) ⊓ LinearMap.ker (ad K L f)) +
      finrank K (LinearMap.ker (ad K L x)) = finrank K (LinearMap.ker (ad K L e)) :=
  -- `ad K L` is by definition the action `toEnd K L L` of `L` on itself.
  t.finrank_range_toEnd_inf_ker_toEnd_f_add_finrank_ker_toEnd (M := L) hx

/-- The centralizer of `e` has the largest dimension among the centralizers of the points of the
Slodowy slice `e + ker (ad f)`. -/
theorem finrank_ker_ad_le_finrank_ker_ad_e (t : IsSl2Triple h e f)
    (hx : x ∈ slodowySlice K e f) :
    finrank K (LinearMap.ker (ad K L x)) ≤ finrank K (LinearMap.ker (ad K L e)) :=
  -- `ad K L` is by definition the action `toEnd K L L` of `L` on itself.
  t.finrank_ker_toEnd_le_finrank_ker_toEnd_e (M := L) hx

end Transversal

end IsSl2Triple
