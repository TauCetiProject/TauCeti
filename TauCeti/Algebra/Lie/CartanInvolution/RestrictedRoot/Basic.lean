/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.CartanInvolution.Decomposition
public import TauCeti.Algebra.Lie.Weights.Eigenvector
public import TauCeti.LinearAlgebra.Eigenspace.JointEigenvector.Basic
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.Order.CompactlyGenerated.Basic
public import Mathlib.RingTheory.Noetherian.Basic

/-!
# Restricted root spaces and maximal abelian subspaces of `𝔭`

Let `𝔞` be a submodule of a Lie algebra `L` and `λ` a linear functional on `𝔞`. The *restricted
root space* `𝔤_λ = {x | [H, x] = λ(H) x for all H ∈ 𝔞}` is the joint eigenspace of the operators
`ad H`, `H ∈ 𝔞`, and the *restricted roots* are the nonzero `λ` with `𝔤_λ ≠ 0`. The bracket carries
`𝔤_λ × 𝔤_μ` into `𝔤_{λ + μ}`, the Killing form pairs `𝔤_λ` with `𝔤_μ` trivially unless
`λ + μ = 0`, and the restricted root spaces are independent, so a Noetherian `L` has finitely many
restricted roots.

The main case is that of a Cartan involution `θ` of a real semisimple Lie algebra, with `𝔞` a
maximal abelian subspace of the `-1`-eigenspace `𝔭` of `θ`. For any automorphism `θ` and any
`𝔞 ⊆ 𝔭`, `θ` maps `𝔤_λ` onto `𝔤_{-λ}`, so the restricted roots are symmetric under negation,
`λ` and `-λ` have the same multiplicity, and distinct restricted root spaces are orthogonal for
the twisted Killing form `B_θ`. For `𝔞` maximal abelian in `𝔭`, `𝔞` is its own centralizer in
`𝔭`, and, when `θ` is an involution and `2` is a unit, the centralizer `𝔤_0` of `𝔞` is the sum
of `𝔞` and its intersection `𝔪` with the fixed subalgebra `𝔨` of `θ`. Every element of `𝔭` lies
in a maximal abelian subspace of `𝔭`, by Zorn's lemma.

## Main definitions

* `Submodule.restrictedRootSpace`: the restricted root space `𝔤_λ` of `𝔞`.
* `Submodule.restrictedRoots`: the set `Σ` of restricted roots of `𝔞`.
* `LieEquiv.IsMaximalAbelianInP`: `𝔞` is maximal among the abelian subspaces of `𝔭`.

## Main results

* `Submodule.lie_mem_restrictedRootSpace`: `[𝔤_λ, 𝔤_μ] ⊆ 𝔤_{λ + μ}`.
* `Submodule.killingForm_eq_zero_of_mem_restrictedRootSpace`: `B(𝔤_λ, 𝔤_μ) = 0` unless
  `λ + μ = 0`.
* `Submodule.iSupIndep_restrictedRootSpace`, `Submodule.finite_restrictedRoots`: the restricted
  root spaces are independent, and there are finitely many restricted roots.
* `Submodule.exists_dual_eq_of_iInf_eigenspace_ne_bot`: a nonzero joint eigenspace of the
  operators `ad H`, `H ∈ 𝔞`, has a linear eigenvalue function.
* `LieEquiv.map_restrictedRootSpace`: `θ 𝔤_λ = 𝔤_{-λ}` for `𝔞 ⊆ 𝔭`, so that
  `-λ ∈ Σ ↔ λ ∈ Σ` (`LieEquiv.neg_mem_restrictedRoots_iff`) and `m_{-λ} = m_λ`
  (`LieEquiv.finrank_restrictedRootSpace_neg`).
* `LieEquiv.twistedKillingForm_eq_zero_of_mem_restrictedRootSpace`: distinct restricted root
  spaces are `B_θ`-orthogonal.
* `LieEquiv.exists_isMaximalAbelianInP_mem`: every element of `𝔭` lies in a maximal abelian
  subspace of `𝔭`.
* `LieEquiv.IsMaximalAbelianInP.restrictedRootSpace_zero_inf_cartanP`: `𝔞` is its own
  centralizer in `𝔭`.
* `LieEquiv.IsMaximalAbelianInP.restrictedRootSpace_zero_eq_sup`: `𝔤_0 = 𝔪 + 𝔞` with
  `𝔪 = 𝔤_0 ∩ 𝔨`.

## References

* A. W. Knapp, *Lie Groups Beyond an Introduction*, 2nd ed., Chapter VI, §4.
* S. Helgason, *Differential Geometry, Lie Groups, and Symmetric Spaces*, Chapter VII, §2.
-/

public section

open LieAlgebra LieModule Module

namespace Submodule

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]

/-! ### Restricted root spaces -/

/-- The restricted root space `𝔤_λ = {x | [H, x] = λ(H) x for all H ∈ 𝔞}` of a submodule `𝔞` of a
Lie algebra, for a linear functional `λ` on `𝔞`: the joint eigenspace of the operators `ad H`,
`H ∈ 𝔞`, with eigenvalues `λ(H)`. -/
def restrictedRootSpace (𝔞 : Submodule R L) (μ : Dual R 𝔞) : Submodule R L :=
  ⨅ H : 𝔞, End.eigenspace (ad R L H) (μ H)

/-- The restricted roots of a submodule `𝔞` of a Lie algebra: the nonzero linear functionals `λ`
on `𝔞` whose restricted root space `𝔤_λ` is nonzero. -/
def restrictedRoots (𝔞 : Submodule R L) : Set (Dual R 𝔞) :=
  {μ | μ ≠ 0 ∧ 𝔞.restrictedRootSpace μ ≠ ⊥}

variable {𝔞 : Submodule R L} {μ ν : Dual R 𝔞} {x y : L}

/-- The restricted root space `𝔤_λ` is the intersection of the eigenspaces of the `ad H`,
`H ∈ 𝔞`, with eigenvalues `λ(H)`. -/
theorem restrictedRootSpace_eq_iInf :
    𝔞.restrictedRootSpace μ = ⨅ H : 𝔞, End.eigenspace (ad R L H) (μ H) := by
  rw [restrictedRootSpace]

@[simp]
theorem mem_restrictedRootSpace :
    x ∈ 𝔞.restrictedRootSpace μ ↔ ∀ H : 𝔞, ⁅(H : L), x⁆ = μ H • x := by
  simp [restrictedRootSpace]

@[simp]
theorem mem_restrictedRoots : μ ∈ 𝔞.restrictedRoots ↔ μ ≠ 0 ∧ 𝔞.restrictedRootSpace μ ≠ ⊥ :=
  Iff.rfl

/-- The restricted root space `𝔤_0` is the centralizer of `𝔞`. -/
theorem mem_restrictedRootSpace_zero :
    x ∈ 𝔞.restrictedRootSpace 0 ↔ ∀ H : 𝔞, ⁅(H : L), x⁆ = 0 := by
  simp [mem_restrictedRootSpace]

/-- An abelian submodule `𝔞` lies in its centralizer `𝔤_0`. -/
theorem le_restrictedRootSpace_zero (h𝔞 : ∀ x ∈ 𝔞, ∀ y ∈ 𝔞, ⁅x, y⁆ = 0) :
    𝔞 ≤ 𝔞.restrictedRootSpace 0 :=
  fun x hx ↦ mem_restrictedRootSpace_zero.mpr fun H ↦ h𝔞 H H.property x hx

/-- The bracket carries `𝔤_λ × 𝔤_μ` into `𝔤_{λ + μ}`. -/
theorem lie_mem_restrictedRootSpace (hx : x ∈ 𝔞.restrictedRootSpace μ)
    (hy : y ∈ 𝔞.restrictedRootSpace ν) : ⁅x, y⁆ ∈ 𝔞.restrictedRootSpace (μ + ν) := by
  rw [restrictedRootSpace_eq_iInf] at hx hy ⊢
  simp only [LinearMap.add_apply]
  exact TauCeti.lie_mem_iInf_eigenspace_ad (H := ((↑) : 𝔞 → L)) hx hy

/-- The Killing form pairs `𝔤_λ` and `𝔤_μ` trivially unless `λ + μ = 0`. -/
theorem killingForm_eq_zero_of_mem_restrictedRootSpace [NoZeroDivisors R]
    (hx : x ∈ 𝔞.restrictedRootSpace μ) (hy : y ∈ 𝔞.restrictedRootSpace ν) (h : μ + ν ≠ 0) :
    killingForm R L x y = 0 := by
  obtain ⟨H, hH⟩ := not_forall.mp fun h' ↦ h (LinearMap.ext h')
  rw [mem_restrictedRootSpace] at hx hy
  have key : (μ + ν) H * killingForm R L x y = 0 := by
    have := traceForm_apply_lie_apply' R L L (H : L) x y
    rw [hx, hy] at this
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul] at this
    rw [LinearMap.add_apply, killingForm]
    linear_combination this
  exact (mul_eq_zero.mp key).resolve_left hH

/-- The restricted root spaces of `𝔞` are independent. -/
theorem iSupIndep_restrictedRootSpace [IsDomain R] [IsTorsionFree R L] :
    iSupIndep 𝔞.restrictedRootSpace := by
  have h𝔤 : 𝔞.restrictedRootSpace =
      (fun χ : 𝔞 → R ↦ ⨅ H : 𝔞, End.eigenspace (ad R L H) (χ H)) ∘ (⇑) :=
    funext fun _ ↦ restrictedRootSpace_eq_iInf
  rw [h𝔤]
  exact (TauCeti.iSupIndep_iInf_eigenspace fun H : 𝔞 ↦ ad R L H).comp DFunLike.coe_injective

/-- **Eigenvalue functions of `ad 𝔞` are linear.** If the joint eigenspace of the operators
`ad H`, `H ∈ 𝔞`, for eigenvalues `χ H` is nonzero, then `χ` is a linear functional on `𝔞`, and the
joint eigenspace is its restricted root space. -/
theorem exists_dual_eq_of_iInf_eigenspace_ne_bot [IsDomain R] [IsTorsionFree R L] {χ : 𝔞 → R}
    (hχ : ⨅ H : 𝔞, End.eigenspace (ad R L H) (χ H) ≠ ⊥) : ∃ μ : Dual R 𝔞, ⇑μ = χ := by
  obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff _).mp hχ
  have hH (H : 𝔞) : ⁅(H : L), x⁆ = χ H • x := by
    simpa using (Submodule.mem_iInf _).mp hx H
  have hcancel {a b : R} (h : a • x = b • x) : a = b :=
    smul_left_injective R hx0 h
  refine ⟨{ toFun := χ, map_add' := fun H H' ↦ hcancel ?_, map_smul' := fun c H ↦ hcancel ?_ },
    rfl⟩
  · rw [add_smul, ← hH, ← hH, ← hH, coe_add, add_lie]
  · rw [smul_eq_mul, RingHom.id_apply, mul_smul, ← hH, ← hH, coe_smul, smul_lie]

/-- A Noetherian Lie algebra has finitely many restricted roots for each submodule `𝔞`. -/
theorem finite_restrictedRoots [IsDomain R] [IsTorsionFree R L] [IsNoetherian R L] :
    𝔞.restrictedRoots.Finite :=
  (finite_ne_bot_of_iSupIndep iSupIndep_restrictedRootSpace).subset fun _ hμ ↦ hμ.2

/-- The zero subspace has the whole Lie algebra as its only restricted root space. -/
@[simp]
theorem restrictedRootSpace_bot (μ : Dual R (⊥ : Submodule R L)) :
    (⊥ : Submodule R L).restrictedRootSpace μ = ⊤ :=
  eq_top_iff.mpr fun x _ ↦ mem_restrictedRootSpace.mpr fun H ↦ by
    simp [Subsingleton.elim H 0]

/-- The zero subspace has no restricted roots. -/
@[simp]
theorem restrictedRoots_bot : (⊥ : Submodule R L).restrictedRoots = ∅ :=
  Set.eq_empty_of_forall_notMem fun μ hμ ↦ hμ.1 (Subsingleton.elim μ 0)

end Submodule

namespace LieEquiv

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L] {θ : L ≃ₗ⁅R⁆ L}
  {𝔞 : Submodule R L} {μ ν : Dual R 𝔞} {x y : L}

open Submodule

/-! ### Restricted root spaces of a subspace of `𝔭` -/

/-- For `𝔞 ⊆ 𝔭`, an automorphism `θ` maps `𝔤_λ` into `𝔤_{-λ}`. -/
theorem apply_mem_restrictedRootSpace_neg (h𝔞 : 𝔞 ≤ θ.cartanP)
    (hx : x ∈ 𝔞.restrictedRootSpace μ) : θ x ∈ 𝔞.restrictedRootSpace (-μ) := by
  rw [mem_restrictedRootSpace] at hx ⊢
  intro H
  have h := congrArg θ (hx H)
  rw [map_lie, mem_cartanP.mp (h𝔞 H.property), neg_lie, map_smul] at h
  rw [LinearMap.neg_apply, neg_smul, ← h, neg_neg]

/-- For `𝔞 ⊆ 𝔭`, an automorphism `θ` maps `𝔤_λ` onto `𝔤_{-λ}`. -/
theorem map_restrictedRootSpace (h𝔞 : 𝔞 ≤ θ.cartanP) (μ : Dual R 𝔞) :
    (𝔞.restrictedRootSpace μ).map (θ : L →ₗ[R] L) = 𝔞.restrictedRootSpace (-μ) := by
  refine le_antisymm (map_le_iff_le_comap.mpr fun x hx ↦ apply_mem_restrictedRootSpace_neg h𝔞 hx)
    fun y hy ↦ ⟨θ.symm y, ?_, θ.apply_symm_apply y⟩
  simpa using apply_mem_restrictedRootSpace_neg (θ := θ.symm) (cartanP_symm θ ▸ h𝔞) hy

/-- For `𝔞 ⊆ 𝔭`, `-λ` is a restricted root exactly when `λ` is. -/
theorem neg_mem_restrictedRoots_iff (h𝔞 : 𝔞 ≤ θ.cartanP) :
    -μ ∈ 𝔞.restrictedRoots ↔ μ ∈ 𝔞.restrictedRoots := by
  simp only [mem_restrictedRoots, ne_eq, neg_eq_zero, ← map_restrictedRootSpace h𝔞,
    Submodule.map_eq_bot_iff]

/-- For `𝔞 ⊆ 𝔭`, the restricted roots `λ` and `-λ` have the same multiplicity. -/
theorem finrank_restrictedRootSpace_neg (h𝔞 : 𝔞 ≤ θ.cartanP) (μ : Dual R 𝔞) :
    finrank R (𝔞.restrictedRootSpace (-μ)) = finrank R (𝔞.restrictedRootSpace μ) := by
  rw [← map_restrictedRootSpace h𝔞]
  exact θ.toLinearEquiv.finrank_map_eq _

/-- For `𝔞 ⊆ 𝔭`, distinct restricted root spaces are orthogonal for the twisted Killing form
`B_θ(x, y) = -B(x, θ y)`. -/
theorem twistedKillingForm_eq_zero_of_mem_restrictedRootSpace [NoZeroDivisors R]
    (h𝔞 : 𝔞 ≤ θ.cartanP) (hx : x ∈ 𝔞.restrictedRootSpace μ) (hy : y ∈ 𝔞.restrictedRootSpace ν)
    (h : μ ≠ ν) : θ.twistedKillingForm x y = 0 := by
  rw [twistedKillingForm_apply, neg_eq_zero]
  exact killingForm_eq_zero_of_mem_restrictedRootSpace hx
    (apply_mem_restrictedRootSpace_neg h𝔞 hy) (by rwa [← sub_eq_add_neg, sub_ne_zero])

/-! ### Maximal abelian subspaces of `𝔭` -/

variable (θ) in
/-- A maximal abelian subspace of `𝔭`: a submodule `𝔞` of the `-1`-eigenspace `𝔭` of `θ` on
which the bracket vanishes, maximal under inclusion among such submodules. -/
def IsMaximalAbelianInP (𝔞 : Submodule R L) : Prop :=
  Maximal (fun 𝔟 : Submodule R L ↦ 𝔟 ≤ θ.cartanP ∧ ∀ x ∈ 𝔟, ∀ y ∈ 𝔟, ⁅x, y⁆ = 0) 𝔞

/-- `IsMaximalAbelianInP` is maximality among abelian submodules of `𝔭`. -/
theorem isMaximalAbelianInP_iff_maximal :
    θ.IsMaximalAbelianInP 𝔞 ↔
      Maximal (fun 𝔟 : Submodule R L ↦ 𝔟 ≤ θ.cartanP ∧ ∀ x ∈ 𝔟, ∀ y ∈ 𝔟, ⁅x, y⁆ = 0) 𝔞 :=
  Iff.rfl

theorem isMaximalAbelianInP_iff :
    θ.IsMaximalAbelianInP 𝔞 ↔ (𝔞 ≤ θ.cartanP ∧ ∀ x ∈ 𝔞, ∀ y ∈ 𝔞, ⁅x, y⁆ = 0) ∧
      ∀ ⦃𝔟 : Submodule R L⦄, (𝔟 ≤ θ.cartanP ∧ ∀ x ∈ 𝔟, ∀ y ∈ 𝔟, ⁅x, y⁆ = 0) → 𝔞 ≤ 𝔟 → 𝔟 ≤ 𝔞 :=
  Iff.rfl

namespace IsMaximalAbelianInP

theorem le_cartanP (h𝔞 : θ.IsMaximalAbelianInP 𝔞) : 𝔞 ≤ θ.cartanP :=
  (isMaximalAbelianInP_iff_maximal.mp h𝔞).prop.1

theorem lie_eq_zero (h𝔞 : θ.IsMaximalAbelianInP 𝔞) (hx : x ∈ 𝔞) (hy : y ∈ 𝔞) : ⁅x, y⁆ = 0 :=
  (isMaximalAbelianInP_iff_maximal.mp h𝔞).prop.2 x hx y hy

/-- A maximal abelian subspace `𝔞` of `𝔭` lies in its centralizer `𝔤_0`. -/
theorem le_restrictedRootSpace_zero (h𝔞 : θ.IsMaximalAbelianInP 𝔞) :
    𝔞 ≤ 𝔞.restrictedRootSpace 0 :=
  Submodule.le_restrictedRootSpace_zero (isMaximalAbelianInP_iff_maximal.mp h𝔞).prop.2

/-- A maximal abelian subspace `𝔞` of `𝔭` is its own centralizer in `𝔭`: `𝔤_0 ∩ 𝔭 = 𝔞`. -/
theorem restrictedRootSpace_zero_inf_cartanP (h𝔞 : θ.IsMaximalAbelianInP 𝔞) :
    𝔞.restrictedRootSpace 0 ⊓ θ.cartanP = 𝔞 := by
  refine le_antisymm (fun x ⟨hx0, hxp⟩ ↦ ?_) (le_inf h𝔞.le_restrictedRootSpace_zero h𝔞.le_cartanP)
  have hx0 := mem_restrictedRootSpace_zero.mp hx0
  -- `𝔞 + R x` is abelian and contained in `𝔭`, so it equals `𝔞` by maximality.
  have hab : ∀ a ∈ 𝔞 ⊔ span R {x}, ∀ b ∈ 𝔞 ⊔ span R {x}, ⁅a, b⁆ = 0 := by
    intro a' ha' b' hb'
    obtain ⟨a, ha, z, hr, rfl⟩ := mem_sup.mp ha'
    obtain ⟨b, hb, w, hs, rfl⟩ := mem_sup.mp hb'
    obtain ⟨r, rfl⟩ := mem_span_singleton.mp hr
    obtain ⟨s, rfl⟩ := mem_span_singleton.mp hs
    simp only [add_lie, lie_add, smul_lie, lie_smul, h𝔞.lie_eq_zero ha hb, lie_self,
      hx0 ⟨a, ha⟩, hx0 ⟨b, hb⟩, ← lie_skew x b, neg_zero, smul_zero, add_zero]
  exact (isMaximalAbelianInP_iff_maximal.mp h𝔞).le_of_ge
    ⟨sup_le h𝔞.le_cartanP ((span_singleton_le_iff_mem _ _).mpr hxp), hab⟩ le_sup_left
    (mem_sup_right (mem_span_singleton_self x))

/-- The centralizer `𝔤_0` of a maximal abelian subspace `𝔞` of `𝔭` is the sum of `𝔞` and
`𝔪 = 𝔤_0 ∩ 𝔨`, for an involution when `2` is a unit. This states only the sum; that it is
direct, as `𝔞 ⊆ 𝔭` and `𝔨` and `𝔭` are complementary
(`LieEquiv.isCompl_fixedSubalgebra_cartanP`), is not proved here. -/
theorem restrictedRootSpace_zero_eq_sup (h2 : IsUnit (2 : R)) (hθ : Function.Involutive θ)
    (h𝔞 : θ.IsMaximalAbelianInP 𝔞) :
    𝔞.restrictedRootSpace 0 =
      𝔞.restrictedRootSpace 0 ⊓ θ.toLieHom.fixedSubalgebra.toSubmodule ⊔ 𝔞 := by
  refine le_antisymm (fun x hx ↦ ?_) (sup_le inf_le_left h𝔞.le_restrictedRootSpace_zero)
  obtain ⟨u, hu⟩ := h2
  have hθx : θ x ∈ 𝔞.restrictedRootSpace 0 := by
    simpa using apply_mem_restrictedRootSpace_neg h𝔞.le_cartanP hx
  -- Split `x = u⁻¹ (x + θ x) + u⁻¹ (x - θ x)` into its `𝔨`- and `𝔭`-components.
  have hsplit : x = (↑u⁻¹ : R) • (x + θ x) + (↑u⁻¹ : R) • (x - θ x) := by
    rw [← smul_add, add_add_sub_cancel, ← two_smul R x, ← hu, smul_smul, Units.inv_mul, one_smul]
  rw [hsplit]
  refine add_mem (mem_sup_left (mem_inf.mpr ⟨smul_mem _ _ (add_mem hx hθx), ?_⟩))
    (mem_sup_right ?_)
  · rw [LieSubalgebra.mem_toSubmodule, LieHom.mem_fixedSubalgebra, coe_toLieHom, map_smul,
      map_add, hθ x, add_comm]
  · rw [← h𝔞.restrictedRootSpace_zero_inf_cartanP]
    refine ⟨smul_mem _ _ (sub_mem hx hθx), smul_mem _ _ (mem_cartanP.mpr ?_)⟩
    rw [map_sub, hθ x, neg_sub]

end IsMaximalAbelianInP

/-- The zero subspace is maximal abelian in `𝔭` exactly when `𝔭 = 0`. -/
theorem isMaximalAbelianInP_bot_iff : θ.IsMaximalAbelianInP ⊥ ↔ θ.cartanP = ⊥ := by
  refine ⟨fun h ↦ by simpa using h.restrictedRootSpace_zero_inf_cartanP, fun h ↦ ?_⟩
  exact isMaximalAbelianInP_iff.mpr ⟨⟨bot_le, by simp⟩, fun _ h𝔟 _ ↦ h ▸ h𝔟.1⟩

variable (θ) in
/-- Every abelian subspace of `𝔭` lies in a maximal one, by Zorn's lemma. -/
theorem exists_isMaximalAbelianInP_ge {𝔟 : Submodule R L} (h𝔟 : 𝔟 ≤ θ.cartanP)
    (hab : ∀ x ∈ 𝔟, ∀ y ∈ 𝔟, ⁅x, y⁆ = 0) : ∃ 𝔞, 𝔟 ≤ 𝔞 ∧ θ.IsMaximalAbelianInP 𝔞 := by
  refine (zorn_le_nonempty₀ {𝔠 | 𝔠 ≤ θ.cartanP ∧ ∀ x ∈ 𝔠, ∀ y ∈ 𝔠, ⁅x, y⁆ = 0}
    (fun c hc hchain 𝔠 h𝔠 ↦ ⟨sSup c, ⟨sSup_le fun 𝔡 h𝔡 ↦ (hc h𝔡).1, fun x hx y hy ↦ ?_⟩,
      fun _ ↦ le_sSup⟩) 𝔟 ⟨h𝔟, hab⟩).imp
    fun _ h ↦ ⟨h.1, isMaximalAbelianInP_iff_maximal.mpr h.2⟩
  -- The union of a chain of abelian subspaces is abelian: `x` and `y` lie in a common member.
  have hdir := hchain.directedOn
  obtain ⟨𝔡, h𝔡, hx⟩ := (mem_sSup_of_directed ⟨𝔠, h𝔠⟩ hdir).mp hx
  obtain ⟨𝔢, h𝔢, hy⟩ := (mem_sSup_of_directed ⟨𝔠, h𝔠⟩ hdir).mp hy
  obtain ⟨𝔣, h𝔣, h𝔡𝔣, h𝔢𝔣⟩ := hdir 𝔡 h𝔡 𝔢 h𝔢
  exact (hc h𝔣).2 x (h𝔡𝔣 hx) y (h𝔢𝔣 hy)

/-- Every element of `𝔭` lies in a maximal abelian subspace of `𝔭`. -/
theorem exists_isMaximalAbelianInP_mem (hx : x ∈ θ.cartanP) :
    ∃ 𝔞, θ.IsMaximalAbelianInP 𝔞 ∧ x ∈ 𝔞 := by
  obtain ⟨𝔞, hx𝔞, h𝔞⟩ := exists_isMaximalAbelianInP_ge θ
    ((span_singleton_le_iff_mem _ _).mpr hx) fun a ha b hb ↦ by
      obtain ⟨r, rfl⟩ := mem_span_singleton.mp ha
      obtain ⟨s, rfl⟩ := mem_span_singleton.mp hb
      simp
  exact ⟨𝔞, h𝔞, hx𝔞 (mem_span_singleton_self x)⟩

/-- `𝔭` has a maximal abelian subspace. -/
theorem exists_isMaximalAbelianInP (θ : L ≃ₗ⁅R⁆ L) : ∃ 𝔞, θ.IsMaximalAbelianInP 𝔞 :=
  (exists_isMaximalAbelianInP_mem (zero_mem θ.cartanP)).imp fun _ h ↦ h.1

end LieEquiv
