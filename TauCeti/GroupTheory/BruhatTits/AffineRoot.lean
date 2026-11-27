/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.BruhatTits.Apartment
public import Mathlib.LinearAlgebra.RootSystem.Reduced

/-!
# Affine roots of a valued root datum

An affine root on the apartment of a valuation `φ` has the form `x ↦ a (x - φ) + k`.
Its constant `k` must occur as the greatest value of `φ a` on a coset `u U (2a)`.
When `2a` is absent, `U (2a)` is trivial and every real value of `φ a` supplies an affine root.

The strict filtration at `k` is the union of the filtration subgroups at depths greater than
`k`. It detects affine-root constants by testing whether a coset meeting the filtration at
`k` also meets the strict filtration. The affine root `a + k` has subgroup `U (a, k)`.
Its closed half-apartment consists of the points whose depth-zero filtration at `a` contains
`U (a, k)`. These descriptions give the signs and groups used in the facet decomposition.

## References

* F. Bruhat, J. Tits, *Groupes réductifs sur un corps local. I*, Publ. Math. IHÉS 41 (1972),
  6.2.2–6.2.6, pp. 117–120.
* F. Bruhat, J. Tits, *Groupes réductifs sur un corps local. II*, Publ. Math. IHÉS 60 (1984),
  4.2.20–4.2.23, pp. 97–99.
-/

public section

open scoped Pointwise

namespace TauCeti.BruhatTits

variable {ι M N : Type*} [AddCommGroup M] [AddCommGroup N] {G : Type*} [Group G]

section Field

variable {R : Type*} [Field R] [LinearOrder R] [Module R M] [Module R N]
  {P : RootPairing ι R M N} {D : RootDatum P G}

namespace Valuation

variable (φ : Valuation D) {i : ι}

/-- The value set `Γ'_a` consists of the finite values attained as maxima on cosets
`u U (2a)` in `U a`. -/
def primedValueSet (i : ι) : Set ℝ :=
  {k | ∃ u : D.U i, φ i u = k ∧ ∀ v : D.doubleRootSubgroup i,
    φ i (u * Subgroup.inclusion (D.doubleRootSubgroup_le i) v) ≤ k}

/-- A real constant is primed if it is attained and bounds the values on the entire coset. -/
@[simp]
theorem mem_primedValueSet_iff {k : ℝ} :
    k ∈ φ.primedValueSet i ↔ ∃ u : D.U i, φ i u = k ∧ ∀ v : D.doubleRootSubgroup i,
      φ i (u * Subgroup.inclusion (D.doubleRootSubgroup_le i) v) ≤ k :=
  Iff.rfl

/-- Every greatest value on a doubled-root coset is a value of the root valuation. -/
theorem primedValueSet_subset_valueSet (i : ι) : φ.primedValueSet i ⊆ φ.valueSet i :=
  fun _ ⟨_u, hu, _⟩ ↦ φ.apply_mem_valueSet hu

/-- If twice the root is absent, every value of the root valuation supplies an affine root
constant. -/
theorem primedValueSet_eq_valueSet_of_forall_root_ne_two_smul
    (hi : ∀ j, P.root j ≠ (2 : R) • P.root i) :
    φ.primedValueSet i = φ.valueSet i := by
  refine Set.Subset.antisymm (φ.primedValueSet_subset_valueSet i) fun _k hk ↦ ?_
  obtain ⟨u, hu⟩ := φ.mem_valueSet_iff.mp hk
  refine ⟨u, hu, fun v ↦ ?_⟩
  have hbot := (D.doubleRootSubgroup_eq_bot_iff i).mpr hi
  have hv : v = 1 := Subtype.ext (Subgroup.mem_bot.mp (hbot ▸ v.property))
  simp [hv, hu]

/-- On a reduced root pairing, all real values of the root valuations supply affine roots. -/
@[simp]
theorem primedValueSet_eq_valueSet [CharZero R] [P.IsReduced] (i : ι) :
    φ.primedValueSet i = φ.valueSet i := by
  let := HasUniqueDiv.of_isTorsionFree R M
  exact φ.primedValueSet_eq_valueSet_of_forall_root_ne_two_smul fun j hj ↦
    P.nsmul_notMem_range_root (n := 2) ⟨j, hj.trans (ofNat_smul_eq_nsmul R 2 _)⟩

/-- A depth is an affine-root constant precisely when there is an element of the filtration
whose coset `g U (2a)` misses the strict filtration. -/
theorem mem_primedValueSet_iff_exists_notMem_mul {k : ℝ} :
    k ∈ φ.primedValueSet i ↔ ∃ g ∈ φ.filtration i k,
      g ∉ (φ.filtrationGT i k : Set G) * (D.doubleRootSubgroup i : Set G) := by
  constructor
  · rintro ⟨u, hu, hcoset⟩
    refine ⟨u, (φ.coe_mem_filtration_iff u).mpr hu.ge, ?_⟩
    rintro ⟨g, hg, v, hv, huv⟩
    have heq : g = (u * Subgroup.inclusion (D.doubleRootSubgroup_le i) ⟨v⁻¹, inv_mem hv⟩ :
        D.U i).val := by rw [Subgroup.coe_mul, Subgroup.coe_inclusion, ← huv, mul_inv_cancel_right]
    exact (not_lt_of_ge (hcoset ⟨v⁻¹, inv_mem hv⟩))
      ((φ.coe_mem_filtrationGT_iff _).mp (heq ▸ hg))
  · rintro ⟨g, hmem, hcoset⟩
    obtain ⟨hg, hk⟩ := φ.mem_filtration_iff.mp hmem
    let u : D.U i := ⟨g, hg⟩
    have hmax (v : D.doubleRootSubgroup i) :
        φ i (u * Subgroup.inclusion (D.doubleRootSubgroup_le i) v) ≤ k := by
      by_contra! h
      have hv : (v : G)⁻¹ ∈ D.doubleRootSubgroup i := inv_mem v.property
      have hm := Set.mul_mem_mul ((φ.coe_mem_filtrationGT_iff _).mpr h) hv
      exact hcoset (by simpa only [SetLike.mem_coe, Subgroup.coe_mul, Subgroup.coe_inclusion,
        mul_inv_cancel_right, u] using hm)
    exact ⟨u, le_antisymm (by simpa using hmax 1) hk, hmax⟩

end Valuation

end Field

variable [Module ℝ M] [Module ℝ N] {P : RootPairing ι ℝ M N} {D : RootDatum P G}

namespace Valuation

variable (φ : Valuation D)

/-- A change of valuation by displacement `v` shifts the primed constants at `a` by `a(v)`. -/
@[simp]
theorem primedValueSet_shift (i : ι) (v : N) :
    (φ.shift v).primedValueSet i = (· + P.root' i v) '' φ.primedValueSet i := by
  ext k
  simp only [mem_primedValueSet_iff, shift_apply, Set.mem_image]
  constructor
  · rintro ⟨u, hu, hmax⟩
    have hk : ((k - P.root' i v : ℝ) : WithTop ℝ) + ↑(P.root' i v) = ↑k := by
      rw [← WithTop.coe_add, sub_add_cancel]
    refine ⟨k - P.root' i v, ⟨u, ?_, fun w ↦ ?_⟩, sub_add_cancel _ _⟩
    · exact WithTop.add_right_cancel WithTop.coe_ne_top (hu.trans hk.symm)
    · exact (WithTop.add_le_add_iff_right WithTop.coe_ne_top).mp (hk.symm ▸ hmax w)
  · rintro ⟨l, ⟨u, hu, hmax⟩, rfl⟩
    rw [WithTop.coe_add]
    exact ⟨u, congrArg (· + (P.root' i v : WithTop ℝ)) hu,
      fun w ↦ add_le_add_left (hmax w) _⟩

end Valuation

/-- An affine root of the apartment of `φ` consists of a root `a` and a constant `k ∈ Γ'_a`.
Its value at `x` is `a (x - φ) + k`. -/
@[ext]
structure AffineRoot (φ : Valuation D) where
  /-- The index of the gradient root. -/
  gradient : ι
  /-- The value at the base point of the apartment. -/
  constant : ℝ
  /-- The constant is attained as a maximum on a coset of the doubled root subgroup. -/
  constant_mem : constant ∈ φ.primedValueSet gradient

namespace AffineRoot

variable {φ : Valuation D}

/-- The affine map `x ↦ a (x - φ) + k` of an affine root `a + k`. -/
def toAffineMap (α : AffineRoot φ) : Apartment φ →ᵃ[ℝ] ℝ :=
  AffineMap.mk' (fun x ↦ P.root' α.gradient x.displacement + α.constant)
    (P.root' α.gradient) (Apartment.base φ) (fun x ↦ by simp)

/-- Evaluation of an affine root at an apartment point. -/
def eval (α : AffineRoot φ) (x : Apartment φ) : ℝ :=
  α.toAffineMap x

@[simp]
theorem toAffineMap_apply (α : AffineRoot φ) (x : Apartment φ) : α.toAffineMap x = α.eval x :=
  (rfl)

/-- The linear part of an affine root is the root functional of its gradient. -/
@[simp]
theorem toAffineMap_linear (α : AffineRoot φ) : α.toAffineMap.linear = P.root' α.gradient :=
  (rfl)

theorem eval_def (α : AffineRoot φ) (x : Apartment φ) :
    α.eval x = P.root' α.gradient x.displacement + α.constant :=
  (rfl)

/-- The value at the base point is the constant term. -/
@[simp]
theorem eval_base (α : AffineRoot φ) : α.eval (Apartment.base φ) = α.constant := by
  simp [α.eval_def]

/-- Translating the argument adds the gradient evaluated on the translation vector. -/
@[simp]
theorem eval_vadd (α : AffineRoot φ) (v : N) (x : Apartment φ) :
    α.eval (v +ᵥ x) = P.root' α.gradient v + α.eval x := by
  simp [α.eval_def, add_assoc]

/-- Every real value is taken by an affine root, since its gradient evaluates to two
on its coroot. -/
theorem eval_surjective (α : AffineRoot φ) : Function.Surjective α.eval := by
  intro r
  refine ⟨((r - α.constant) / 2) • P.coroot α.gradient +ᵥ Apartment.base φ, ?_⟩
  simp

/-- The affine map determines both the gradient root and the constant. -/
theorem toAffineMap_injective : Function.Injective (toAffineMap (φ := φ)) := by
  intro α β h
  apply AffineRoot.ext
  · apply P.root.injective
    exact P.toLinearMap.toPerfPair.injective
      (by simpa using congrArg AffineMap.linear h)
  · simpa using congrArg (fun f : Apartment φ →ᵃ[ℝ] ℝ ↦ f (Apartment.base φ)) h

/-- Pointwise equality of the evaluations determines the affine root. -/
theorem ext_eval {α β : AffineRoot φ} (h : ∀ x, α.eval x = β.eval x) : α = β :=
  toAffineMap_injective (AffineMap.ext h)

/-- The wall of an affine root consists of its zeros. -/
def wall (α : AffineRoot φ) : Set (Apartment φ) :=
  {x | α.eval x = 0}

@[simp]
theorem mem_wall_iff {α : AffineRoot φ} {x : Apartment φ} : x ∈ α.wall ↔ α.eval x = 0 :=
  Iff.rfl

/-- Every affine root has a point on its wall. -/
theorem wall_nonempty (α : AffineRoot φ) : α.wall.Nonempty :=
  α.eval_surjective 0

/-- The zero set of an affine root is a proper subset of the apartment. -/
theorem wall_ne_univ (α : AffineRoot φ) : α.wall ≠ Set.univ := by
  obtain ⟨x, hx⟩ := α.eval_surjective 1
  intro h
  have hx' : x ∈ α.wall := h ▸ Set.mem_univ x
  simp [hx] at hx'

/-- The closed half-apartment of an affine root consists of the points where it is nonnegative. -/
def halfApartment (α : AffineRoot φ) : Set (Apartment φ) :=
  {x | 0 ≤ α.eval x}

@[simp]
theorem mem_halfApartment_iff {α : AffineRoot φ} {x : Apartment φ} :
    x ∈ α.halfApartment ↔ 0 ≤ α.eval x :=
  Iff.rfl

/-- The subgroup of the affine root `a + k` is the filtration subgroup `U (a, k)`. -/
noncomputable def rootSubgroup (α : AffineRoot φ) : Subgroup G :=
  φ.filtration α.gradient α.constant

theorem rootSubgroup_def (α : AffineRoot φ) : α.rootSubgroup = φ.filtration α.gradient α.constant :=
  (rfl)

/-- The affine-root subgroup is contained in the root subgroup of its gradient. -/
theorem rootSubgroup_le (α : AffineRoot φ) : α.rootSubgroup ≤ D.U α.gradient :=
  φ.filtration_le_U _ _

/-- The affine-root subgroup contains an element whose valuation equals the constant of the
affine root. -/
theorem exists_mem_rootSubgroup_eq_constant (α : AffineRoot φ) :
    ∃ u : D.U α.gradient, (u : G) ∈ α.rootSubgroup ∧ φ α.gradient u = α.constant := by
  obtain ⟨u, hu, _⟩ := φ.mem_primedValueSet_iff.mp α.constant_mem
  rw [α.rootSubgroup_def]
  exact ⟨u, (φ.coe_mem_filtration_iff u).mpr hu.ge, hu⟩

/-- An affine root has an element of its exact depth, so its subgroup is nontrivial. -/
theorem rootSubgroup_ne_bot (α : AffineRoot φ) : α.rootSubgroup ≠ ⊥ := by
  obtain ⟨u, hm, hu⟩ := α.exists_mem_rootSubgroup_eq_constant
  intro h
  have h1 : u = 1 := Subtype.ext (Subgroup.mem_bot.mp (h ▸ hm))
  simp [h1] at hu

/-- The subgroup of an affine root is contained in the filtration at `x` and depth `r`
exactly when the value of the root at `x` is at least `r`. -/
theorem rootSubgroup_le_filtration_iff (α : AffineRoot φ) (x : Apartment φ) (r : ℝ) :
    α.rootSubgroup ≤ x.val.filtration α.gradient r ↔ r ≤ α.eval x := by
  rw [x.filtration_val, α.eval_def]
  constructor
  · intro h
    obtain ⟨u, hm, hu⟩ := α.exists_mem_rootSubgroup_eq_constant
    exact sub_le_iff_le_add'.mp
      (WithTop.coe_le_coe.mp (hu ▸ (φ.coe_mem_filtration_iff u).mp (h hm)))
  · rw [α.rootSubgroup_def]
    exact fun h ↦ φ.filtration_antitone _ (sub_le_iff_le_add'.mpr h)

/-- For affine roots with the same gradient, subgroup inclusion is the reverse of the pointwise
order. -/
theorem rootSubgroup_le_rootSubgroup_iff {α β : AffineRoot φ} (hgrad : α.gradient = β.gradient) :
    α.rootSubgroup ≤ β.rootSubgroup ↔ ∀ x, β.eval x ≤ α.eval x := by
  have h := α.rootSubgroup_le_filtration_iff (Apartment.base φ) β.constant
  rw [Apartment.val_base, hgrad, ← β.rootSubgroup_def, α.eval_base] at h
  refine h.trans ⟨fun hconst x ↦ ?_, fun hle ↦ by simpa using hle (Apartment.base φ)⟩
  simp only [eval_def, hgrad]
  exact add_le_add_right hconst _

/-- The subgroup of an affine root lies in the strict filtration at `x` and depth `r`
exactly when the root takes a value strictly above `r` there. -/
theorem rootSubgroup_le_filtrationGT_iff (α : AffineRoot φ) (x : Apartment φ) (r : ℝ) :
    α.rootSubgroup ≤ x.val.filtrationGT α.gradient r ↔ r < α.eval x := by
  rw [x.filtrationGT_val, α.eval_def]
  constructor
  · intro h
    obtain ⟨u, hm, hu⟩ := α.exists_mem_rootSubgroup_eq_constant
    exact sub_lt_iff_lt_add'.mp
      (WithTop.coe_lt_coe.mp (hu ▸ (φ.coe_mem_filtrationGT_iff u).mp (h hm)))
  · intro hr g hg
    rw [α.rootSubgroup_def] at hg
    obtain ⟨hgU, hgk⟩ := φ.mem_filtration_iff.mp hg
    exact φ.mem_filtrationGT_iff.mpr
      ⟨hgU, (WithTop.coe_lt_coe.mpr (sub_lt_iff_lt_add'.mpr hr)).trans_le hgk⟩

/-- The closed half-apartment is the region where the affine-root subgroup lies in the
depth-zero subgroup of its gradient. -/
theorem mem_halfApartment_iff_rootSubgroup_le (α : AffineRoot φ) (x : Apartment φ) :
    x ∈ α.halfApartment ↔ α.rootSubgroup ≤ x.val.filtration α.gradient 0 :=
  (α.rootSubgroup_le_filtration_iff x 0).symm

/-- On the wall, the depth-zero filtration contains the affine-root subgroup, and the strict
depth-zero filtration omits some of its elements. -/
theorem mem_wall_iff_rootSubgroup_le (α : AffineRoot φ) (x : Apartment φ) :
    x ∈ α.wall ↔ α.rootSubgroup ≤ x.val.filtration α.gradient 0 ∧
      ¬ α.rootSubgroup ≤ x.val.filtrationGT α.gradient 0 := by
  rw [mem_wall_iff, α.rootSubgroup_le_filtration_iff, α.rootSubgroup_le_filtrationGT_iff,
    not_lt, le_antisymm_iff, and_comm]

/-- The set of constants occurring for a given gradient is the corresponding primed value set. -/
theorem range_constant (i : ι) :
    Set.range (fun α : {α : AffineRoot φ // α.gradient = i} ↦ α.val.constant) =
      φ.primedValueSet i := by
  ext k
  exact ⟨fun ⟨⟨α, hi⟩, hk⟩ ↦ hi ▸ hk ▸ α.constant_mem,
    fun hk ↦ ⟨⟨⟨i, k, hk⟩, rfl⟩, rfl⟩⟩

/-- Changing the base point to `b` preserves the gradient and uses the value at `b` as the new
constant. -/
def transport (α : AffineRoot φ) (b : Apartment φ) : AffineRoot b.val where
  gradient := α.gradient
  constant := α.eval b
  constant_mem := by
    rw [Apartment.val_def, Valuation.primedValueSet_shift, α.eval_def, add_comm]
    exact ⟨α.constant, α.constant_mem, rfl⟩

@[simp]
theorem gradient_transport (α : AffineRoot φ) (b : Apartment φ) :
    (α.transport b).gradient = α.gradient :=
  (rfl)

@[simp]
theorem constant_transport (α : AffineRoot φ) (b : Apartment φ) :
    (α.transport b).constant = α.eval b :=
  (rfl)

/-- In the new coordinates an affine root has the same value at the corresponding point. -/
@[simp]
theorem eval_transport (α : AffineRoot φ) (b x : Apartment φ) :
    (α.transport b).eval (b.transport x) = α.eval x := by
  simp [eval_def]
  ring

/-- Pulling back the wall in the new coordinates recovers the original wall. -/
@[simp]
theorem preimage_wall_transport (α : AffineRoot φ) (b : Apartment φ) :
    b.transport ⁻¹' (α.transport b).wall = α.wall := by
  ext x
  simp

/-- Pulling back the closed half-apartment in the new coordinates recovers the original one. -/
@[simp]
theorem preimage_halfApartment_transport (α : AffineRoot φ) (b : Apartment φ) :
    b.transport ⁻¹' (α.transport b).halfApartment = α.halfApartment := by
  ext x
  simp

/-- The affine-root subgroup is independent of the choice of base point. -/
@[simp]
theorem rootSubgroup_transport (α : AffineRoot φ) (b : Apartment φ) :
    (α.transport b).rootSubgroup = α.rootSubgroup := by
  simp [rootSubgroup_def, Apartment.val_def, eval_def]

/-- Changing the base point bijects the affine roots of the two coordinate apartments. -/
theorem transport_bijective (b : Apartment φ) : Function.Bijective (fun α : AffineRoot φ ↦
    α.transport b) := by
  constructor
  · intro α β h
    apply ext_eval
    intro x
    simpa using congrArg (fun γ : AffineRoot b.val ↦ γ.eval (b.transport x)) h
  · intro β
    have h : β.constant ∈ (· + P.root' β.gradient b.displacement) ''
        φ.primedValueSet β.gradient := by
      simpa only [Apartment.val_def, Valuation.primedValueSet_shift] using β.constant_mem
    obtain ⟨k, hk, heq⟩ := h
    refine ⟨⟨β.gradient, k, hk⟩, ?_⟩
    apply AffineRoot.ext
    · rfl
    · rw [constant_transport, eval_def, add_comm]
      exact heq

end AffineRoot

end TauCeti.BruhatTits
