/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Abelian
public import Mathlib.Algebra.Lie.Killing
public import Mathlib.LinearAlgebra.Projection
public import TauCeti.Algebra.Lie.Subalgebra.Fixed.Basic
public import TauCeti.LinearAlgebra.Eigenspace.Involution
import TauCeti.Algebra.Lie.Basic
import TauCeti.LinearAlgebra.Eigenspace.Separation
import TauCeti.LinearAlgebra.FixedSubmodule

/-!
# The Cartan decomposition of a Lie algebra automorphism

Let `θ` be an automorphism of a Lie algebra `L`. Its fixed vectors form the Lie subalgebra
`𝔨 = θ.toLieHom.fixedSubalgebra`, and its `-1`-eigenspace is the submodule `𝔭 = θ.cartanP`.
These satisfy `[𝔨, 𝔭] ⊆ 𝔭` and `[𝔭, 𝔭] ⊆ 𝔨`, and they are orthogonal for the Killing form as soon
as the base ring has no additive torsion. When `θ` is involutive and `2` is a unit,
`L = 𝔨 ⊕ 𝔭`: this is the Cartan decomposition when `θ` is a Cartan involution.

The *twisted Killing form* `B_θ(x, y) = -B(x, θ y)` is invariant under every automorphism
commuting with `θ`, in particular under `θ` itself, and it is symmetric when `θ` is involutive.
For `x ∈ 𝔨` the operator `ad x` is skew-adjoint for `B_θ`, and for `x ∈ 𝔭` it is self-adjoint.

## Main definitions

* `LieEquiv.cartanP`: the `-1`-eigenspace `𝔭` of a Lie algebra automorphism.
* `LieEquiv.twistedKillingForm`: the bilinear form `B_θ(x, y) = -B(x, θ y)`.

## Main results

* `LieEquiv.cartanP_eq_eigenspace`, `LieEquiv.cartanP_eq_ker`: characterizations of `𝔭` as an
  eigenspace and kernel.
* `LieEquiv.isCompl_fixedSubalgebra_cartanP`: `L = 𝔨 ⊕ 𝔭` for an involution when `2` is a unit.
* `LieEquiv.projection_fixedSubalgebra_cartanP_eq_eigenProjOfInvolutive`,
  `LieEquiv.projection_fixedSubalgebra_cartanP_apply`,
  `LieEquiv.projection_cartanP_fixedSubalgebra_eq_eigenProjOfInvolutive`,
  `LieEquiv.projection_cartanP_fixedSubalgebra_apply`: the canonical projections onto `𝔨` and `𝔭`
  are the involution eigenprojections `x ↦ ½ (x ± θ x)`.
* `LieEquiv.map_cartanP`, `LieEquiv.maximal_abelian_submodule_cartanP_iff`,
  `LieEquiv.maximal_isLieAbelian_cartanP_iff`: intertwining equivalences transport `𝔭` and its
  maximal abelian subspaces.
* `LieEquiv.lie_mem_cartanP`, `LieEquiv.lie_mem_fixedSubalgebra_of_mem_cartanP`: the bracket
  relations `[𝔨, 𝔭] ⊆ 𝔭` and `[𝔭, 𝔭] ⊆ 𝔨`.
* `LieEquiv.killingForm_eq_zero_of_mem_fixedSubalgebra_of_mem_cartanP`: `B(𝔨, 𝔭) = 0`.
* `LieEquiv.twistedKillingForm_map_map_of_commute`, `LieEquiv.twistedKillingForm_conj`: invariance
  and conjugation pullback of `B_θ`.
* `LieEquiv.isSymm_twistedKillingForm`: `B_θ` is symmetric when `θ` is involutive.
* `LieEquiv.ad_mem_skewAdjointSubmodule_twistedKillingForm`,
  `LieEquiv.ad_mem_selfAdjointSubmodule_twistedKillingForm`: `ad x` is `B_θ`-skew-adjoint for
  `x ∈ 𝔨` and `B_θ`-self-adjoint for `x ∈ 𝔭`.

## References

* A. W. Knapp, *Lie Groups Beyond an Introduction*, 2nd ed., Chapter VI, §2.
* S. Helgason, *Differential Geometry, Lie Groups, and Symmetric Spaces*, Chapter III, §7.
-/

public section

open LieAlgebra LieModule

namespace LieEquiv

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L] (θ : L ≃ₗ⁅R⁆ L)

/-! ### The eigenspaces `𝔨` and `𝔭` -/

/-- The `-1`-eigenspace `𝔭 = {x | θ x = -x}` of a Lie algebra automorphism `θ`. When `θ` is a
Cartan involution, `L = 𝔨 ⊕ 𝔭` with `𝔨 = θ.toLieHom.fixedSubalgebra` is the Cartan
decomposition. -/
def cartanP : Submodule R L :=
  Module.End.eigenspace (θ.toLinearEquiv : Module.End R L) (-1)

variable {θ}

@[simp]
theorem mem_cartanP {x : L} : x ∈ θ.cartanP ↔ θ x = -x := by
  simp [cartanP]

variable (θ) in
/-- `𝔭` is the `-1`-eigenspace of `θ`, viewed as a linear endomorphism of `L`. -/
theorem cartanP_eq_eigenspace :
    θ.cartanP = Module.End.eigenspace (θ.toLinearEquiv : Module.End R L) (-1) :=
  (rfl)

variable (θ) in
/-- `𝔭` is the kernel of `θ + id`, viewed as linear endomorphisms of `L`. -/
theorem cartanP_eq_ker :
    θ.cartanP = LinearMap.ker ((θ : L →ₗ[R] L) + LinearMap.id) := by
  ext x
  simp [add_eq_zero_iff_eq_neg]

/-- An involutive Lie algebra automorphism is involutive as a linear endomorphism. -/
theorem involutive_toLinearEquiv (hθ : Function.Involutive θ) :
    Function.Involutive (θ.toLinearEquiv : Module.End R L) := fun x ↦ by
  simp only [LinearEquiv.coe_coe, coe_toLinearEquiv, hθ x]

variable (θ) in
/-- For an involution of a Lie algebra over a ring in which `2` is a unit, the fixed subalgebra
`𝔨` and the `-1`-eigenspace `𝔭` are complementary: `L = 𝔨 ⊕ 𝔭`. -/
theorem isCompl_fixedSubalgebra_cartanP (h2 : IsUnit (2 : R)) (hθ : Function.Involutive θ) :
    IsCompl θ.toLieHom.fixedSubalgebra.toSubmodule θ.cartanP := by
  have := TauCeti.isCompl_eigenspace_one_neg_one h2
    (T := (θ.toLinearEquiv : Module.End R L)) (involutive_toLinearEquiv hθ)
  rw [Module.End.eigenspace_one_eq_fixedSubmodule] at this
  rw [LieHom.fixedSubalgebra_toSubmodule]
  exact this

variable (θ) in
/-- The Cartan projection onto `𝔨` along `𝔭` is the `1`-eigenprojection of `θ`. -/
theorem projection_fixedSubalgebra_cartanP_eq_eigenProjOfInvolutive [Invertible (2 : R)]
    (hθ : Function.Involutive θ)
    (h : IsCompl θ.toLieHom.fixedSubalgebra.toSubmodule θ.cartanP) :
    θ.toLieHom.fixedSubalgebra.toSubmodule.projection θ.cartanP h =
      (Module.End.eigenspace (θ.toLinearEquiv : Module.End R L) 1).subtype.comp
        (Module.End.eigenProjOfInvolutive (involutive_toLinearEquiv hθ) (one_mul 1)) := by
  ext x
  let hg := involutive_toLinearEquiv hθ
  let u := Module.End.eigenProjOfInvolutive hg (one_mul (1 : R)) x
  let v := Module.End.eigenProjOfInvolutive hg ((neg_mul_neg (1 : R) 1).trans (one_mul 1)) x
  have hu : (u : L) ∈ θ.toLieHom.fixedSubalgebra.toSubmodule := by
    rw [LieHom.fixedSubalgebra_toSubmodule_eq_eigenspace]
    exact u.property
  have hv : (v : L) ∈ θ.cartanP := v.property
  have huv : (u : L) + v = x :=
    Module.End.eigenProjOfInvolutive_add_eigenProjOfInvolutive_neg hg _ _ x
  calc
    θ.toLieHom.fixedSubalgebra.toSubmodule.projection θ.cartanP h x
        = θ.toLieHom.fixedSubalgebra.toSubmodule.projection θ.cartanP h ((u : L) + v) := by
          rw [huv]
    _ = θ.toLieHom.fixedSubalgebra.toSubmodule.projection θ.cartanP h u +
          θ.toLieHom.fixedSubalgebra.toSubmodule.projection θ.cartanP h v := map_add _ _ _
    _ = (u : L) + 0 := by
          rw [Submodule.projection_apply_of_mem_left h hu,
            Submodule.projection_apply_of_mem_right h hv]
    _ = u := add_zero _

variable (θ) in
/-- On vectors `x : L`, the Cartan projection onto `𝔨` along `𝔭` is `⅟2 • (x + θ x)`. -/
theorem projection_fixedSubalgebra_cartanP_apply [Invertible (2 : R)]
    (hθ : Function.Involutive θ)
    (h : IsCompl θ.toLieHom.fixedSubalgebra.toSubmodule θ.cartanP) (x : L) :
    θ.toLieHom.fixedSubalgebra.toSubmodule.projection θ.cartanP h x = (⅟2 : R) • (x + θ x) := by
  rw [LinearMap.congr_fun (θ.projection_fixedSubalgebra_cartanP_eq_eigenProjOfInvolutive hθ h) x,
    LinearMap.comp_apply, Submodule.coe_subtype,
    Module.End.coe_eigenProjOfInvolutive_apply (hg := involutive_toLinearEquiv hθ), one_smul]
  simp only [LinearEquiv.coe_coe, coe_toLinearEquiv]

variable (θ) in
/-- The Cartan projection onto `𝔭` along `𝔨` is the `-1`-eigenprojection of `θ`. -/
theorem projection_cartanP_fixedSubalgebra_eq_eigenProjOfInvolutive [Invertible (2 : R)]
    (hθ : Function.Involutive θ)
    (h : IsCompl θ.cartanP θ.toLieHom.fixedSubalgebra.toSubmodule) :
    θ.cartanP.projection θ.toLieHom.fixedSubalgebra.toSubmodule h =
      (Module.End.eigenspace (θ.toLinearEquiv : Module.End R L) (-1)).subtype.comp
        (Module.End.eigenProjOfInvolutive (involutive_toLinearEquiv hθ)
          ((neg_mul_neg (1 : R) 1).trans (one_mul 1))) := by
  ext x
  rw [Submodule.projection_eq_self_sub_projection h.symm x,
    LinearMap.congr_fun (θ.projection_fixedSubalgebra_cartanP_eq_eigenProjOfInvolutive hθ h.symm) x,
    LinearMap.comp_apply, Submodule.coe_subtype, LinearMap.comp_apply, Submodule.coe_subtype]
  exact sub_eq_of_eq_add'
    (Module.End.eigenProjOfInvolutive_add_eigenProjOfInvolutive_neg (involutive_toLinearEquiv hθ)
      (one_mul (1 : R)) ((neg_mul_neg (1 : R) 1).trans (one_mul 1)) x).symm

variable (θ) in
/-- On vectors `x : L`, the Cartan projection onto `𝔭` along `𝔨` is `⅟2 • (x - θ x)`. -/
theorem projection_cartanP_fixedSubalgebra_apply [Invertible (2 : R)]
    (hθ : Function.Involutive θ)
    (h : IsCompl θ.cartanP θ.toLieHom.fixedSubalgebra.toSubmodule) (x : L) :
    θ.cartanP.projection θ.toLieHom.fixedSubalgebra.toSubmodule h x = (⅟2 : R) • (x - θ x) := by
  rw [LinearMap.congr_fun (θ.projection_cartanP_fixedSubalgebra_eq_eigenProjOfInvolutive hθ h) x,
    LinearMap.comp_apply, Submodule.coe_subtype,
    Module.End.coe_eigenProjOfInvolutive_apply (hg := involutive_toLinearEquiv hθ),
    neg_one_smul, ← sub_eq_add_neg]
  simp only [LinearEquiv.coe_coe, coe_toLinearEquiv]

/-- For an involutive automorphism `θ`, `x + θ x` lies in the fixed subalgebra `𝔨`. -/
theorem add_apply_mem_fixedSubalgebra (hθ : Function.Involutive θ) (x : L) :
    x + θ x ∈ θ.toLieHom.fixedSubalgebra := by
  rw [LieHom.mem_fixedSubalgebra, coe_toLieHom, map_add, hθ x, add_comm]

/-- For an involutive automorphism `θ`, `x - θ x` lies in `θ.cartanP`. -/
theorem sub_apply_mem_cartanP (hθ : Function.Involutive θ) (x : L) :
    x - θ x ∈ θ.cartanP := by
  rw [mem_cartanP, map_sub, hθ x, neg_sub]

/-- When `2` is a unit, the identity automorphism has trivial `-1`-eigenspace. -/
@[simp]
theorem cartanP_refl (h2 : IsUnit (2 : R)) : (LieEquiv.refl : L ≃ₗ⁅R⁆ L).cartanP = ⊥ := by
  ext x
  simp only [mem_cartanP, refl_apply, Submodule.mem_bot]
  exact ⟨fun hx ↦ h2.smul_eq_zero.mp (by rw [two_smul]; exact add_eq_zero_iff_eq_neg.mpr hx),
    fun hx ↦ by simp [hx]⟩

/-- For an involutive automorphism over a ring where `2` is a unit, `θ.cartanP = ⊥` iff `θ = 1`. -/
theorem cartanP_eq_bot_iff (h2 : IsUnit (2 : R)) (hθ : Function.Involutive θ) :
    θ.cartanP = ⊥ ↔ θ = LieEquiv.refl := by
  refine ⟨fun hbot ↦ LieEquiv.ext fun x ↦ ?_, fun h ↦ h ▸ cartanP_refl h2⟩
  have hx := sub_apply_mem_cartanP hθ x
  rw [hbot, Submodule.mem_bot, sub_eq_zero] at hx
  exact hx.symm

/-- An intertwining Lie equivalence maps `θ.cartanP` onto `θ'.cartanP`. -/
theorem map_cartanP {M : Type*} [LieRing M] [LieAlgebra R M] (e : L ≃ₗ⁅R⁆ M) {θ' : M ≃ₗ⁅R⁆ M}
    (h : ∀ x, θ' (e x) = e (θ x)) : θ.cartanP.map (e : L →ₗ[R] M) = θ'.cartanP := by
  ext y
  simp only [Submodule.mem_map, mem_cartanP]
  refine ⟨fun ⟨x, hx, hy⟩ ↦ by rw [← hy]; simp [h, hx], fun hy ↦ ⟨e.symm y, ?_, by simp⟩⟩
  exact e.injective (by
    simp only [coe_toLieHom]
    rw [← h, e.apply_symm_apply, hy, map_neg, e.apply_symm_apply])

/-- An intertwining Lie equivalence preserves maximal abelian subspaces inside `𝔭`. -/
theorem maximal_abelian_submodule_cartanP_iff {M : Type*} [LieRing M] [LieAlgebra R M]
    (e : L ≃ₗ⁅R⁆ M) {θ' : M ≃ₗ⁅R⁆ M} (h : ∀ x, θ' (e x) = e (θ x)) (𝔞 : Submodule R L) :
    Maximal (fun 𝔟 : Submodule R M ↦ 𝔟 ≤ θ'.cartanP ∧ ∀ x ∈ 𝔟, ∀ y ∈ 𝔟, ⁅x, y⁆ = 0)
        (𝔞.map (e : L →ₗ[R] M)) ↔
      Maximal (fun 𝔟 : Submodule R L ↦ 𝔟 ≤ θ.cartanP ∧ ∀ x ∈ 𝔟, ∀ y ∈ 𝔟, ⁅x, y⁆ = 0) 𝔞 := by
  let φ : Submodule R L ≃o Submodule R M := Submodule.orderIsoMapComap e.toLinearEquiv
  have he_lin : (e.toLinearEquiv : L →ₗ[R] M) = (e : L →ₗ[R] M) :=
    LinearMap.ext fun x ↦ by simp
  have hP (𝔟 : Submodule R L) :
      (φ 𝔟 ≤ θ'.cartanP ∧ ∀ x ∈ φ 𝔟, ∀ y ∈ φ 𝔟, ⁅x, y⁆ = 0) ↔
        (𝔟 ≤ θ.cartanP ∧ ∀ x ∈ 𝔟, ∀ y ∈ 𝔟, ⁅x, y⁆ = 0) := by
    have hsub : φ 𝔟 ≤ θ'.cartanP ↔ 𝔟 ≤ θ.cartanP := by
      rw [← map_cartanP (θ := θ) e h, ← he_lin]
      exact φ.le_iff_le
    refine and_congr hsub ⟨fun hab x hx y hy ↦ e.injective ?_, fun hab x hx y hy ↦ ?_⟩
    · rw [e.toLieHom.map_lie, map_zero]
      exact hab (e x) ⟨x, hx, by simp⟩ (e y) ⟨y, hy, by simp⟩
    · obtain ⟨x₀, hx₀, rfl⟩ := hx
      obtain ⟨y₀, hy₀, rfl⟩ := hy
      simp only [LinearEquiv.coe_coe, coe_toLinearEquiv]
      rw [← e.map_lie, hab x₀ hx₀ y₀ hy₀, map_zero]
  have hmax := φ.toOrderEmbedding.maximal_apply_mem_iff
    (t := {𝔟 : Submodule R M | 𝔟 ≤ θ'.cartanP ∧ ∀ x ∈ 𝔟, ∀ y ∈ 𝔟, ⁅x, y⁆ = 0})
    (x := 𝔞) (by simp [φ.range_eq])
  simp only [OrderIso.coe_toOrderEmbedding, Set.mem_ofPred_eq, hP] at hmax
  simpa only [φ, Submodule.orderIsoMapComap_apply, he_lin] using hmax

/-- An intertwining Lie equivalence preserves maximal abelian Lie subalgebras inside `𝔭`. -/
theorem maximal_isLieAbelian_cartanP_iff {M : Type*} [LieRing M] [LieAlgebra R M]
    (e : L ≃ₗ⁅R⁆ M) {θ' : M ≃ₗ⁅R⁆ M} (h : ∀ x, θ' (e x) = e (θ x)) (𝔞 : LieSubalgebra R L) :
    Maximal (fun 𝔟 : LieSubalgebra R M ↦ 𝔟.toSubmodule ≤ θ'.cartanP ∧ IsLieAbelian 𝔟)
        (𝔞.map e.toLieHom) ↔
      Maximal (fun 𝔟 : LieSubalgebra R L ↦ 𝔟.toSubmodule ≤ θ.cartanP ∧ IsLieAbelian 𝔟) 𝔞 := by
  let φ : LieSubalgebra R L ≃o LieSubalgebra R M :=
    { toFun := LieSubalgebra.map e.toLieHom
      invFun := LieSubalgebra.map e.symm.toLieHom
      left_inv := fun 𝔟 ↦ by
        ext x; simp only [LieSubalgebra.mem_map, coe_toLieHom]
        exact ⟨fun ⟨y, ⟨z, hz, hzy⟩, hyx⟩ ↦ by simpa [← hyx, ← hzy] using hz,
          fun hx ↦ ⟨e x, ⟨x, hx, rfl⟩, e.symm_apply_apply x⟩⟩
      right_inv := fun 𝔟 ↦ by
        ext y; simp only [LieSubalgebra.mem_map, coe_toLieHom]
        exact ⟨fun ⟨x, ⟨z, hz, hzx⟩, hxy⟩ ↦ by simpa [← hxy, ← hzx] using hz,
          fun hy ↦ ⟨e.symm y, ⟨y, hy, rfl⟩, e.apply_symm_apply y⟩⟩
      map_rel_iff' := fun {𝔟₁ 𝔟₂} ↦ by
        simp only [Equiv.coe_fn_mk, ← LieSubalgebra.toSubmodule_le_toSubmodule,
          LieSubalgebra.map_toSubmodule, Submodule.map_le_map_iff_of_injective e.injective] }
  have hφ (𝔟 : LieSubalgebra R L) : φ 𝔟 = 𝔟.map e.toLieHom := rfl
  have he_lin : (e.toLieHom : L →ₗ[R] M) = (e : L →ₗ[R] M) := LinearMap.ext fun x ↦ by simp
  have hP (𝔟 : LieSubalgebra R L) :
      ((φ 𝔟).toSubmodule ≤ θ'.cartanP ∧ IsLieAbelian (φ 𝔟)) ↔
        (𝔟.toSubmodule ≤ θ.cartanP ∧ IsLieAbelian 𝔟) := by
    have hsub : (φ 𝔟).toSubmodule ≤ θ'.cartanP ↔ 𝔟.toSubmodule ≤ θ.cartanP := by
      rw [hφ, LieSubalgebra.map_toSubmodule, ← map_cartanP (θ := θ) e h, ← he_lin]
      exact Submodule.map_le_map_iff_of_injective e.injective _ _
    exact and_congr hsub (lie_abelian_iff_equiv_lie_abelian (e.lieSubalgebraMap 𝔟)).symm
  have hmax := φ.toOrderEmbedding.maximal_apply_mem_iff
    (t := {𝔟 : LieSubalgebra R M | 𝔟.toSubmodule ≤ θ'.cartanP ∧ IsLieAbelian 𝔟})
    (x := 𝔞) (by simp [φ.range_eq])
  simp only [OrderIso.coe_toOrderEmbedding, Set.mem_ofPred_eq, hP] at hmax
  simpa only [hφ] using hmax

/-- `[𝔨, 𝔭] ⊆ 𝔭`. -/
theorem lie_mem_cartanP {x y : L} (hx : x ∈ θ.toLieHom.fixedSubalgebra) (hy : y ∈ θ.cartanP) :
    ⁅x, y⁆ ∈ θ.cartanP := by
  rw [LieHom.mem_fixedSubalgebra, coe_toLieHom] at hx
  rw [mem_cartanP] at hy ⊢
  rw [map_lie, hx, hy, lie_neg]

/-- `[𝔭, 𝔭] ⊆ 𝔨`. -/
theorem lie_mem_fixedSubalgebra_of_mem_cartanP {x y : L} (hx : x ∈ θ.cartanP)
    (hy : y ∈ θ.cartanP) : ⁅x, y⁆ ∈ θ.toLieHom.fixedSubalgebra := by
  rw [mem_cartanP] at hx hy
  rw [LieHom.mem_fixedSubalgebra, coe_toLieHom, map_lie, hx, hy, neg_lie, lie_neg, neg_neg]

/-- `𝔨` and `𝔭` are orthogonal for the Killing form, over a base ring without additive
torsion. -/
theorem killingForm_eq_zero_of_mem_fixedSubalgebra_of_mem_cartanP [IsAddTorsionFree R]
    {x y : L} (hx : x ∈ θ.toLieHom.fixedSubalgebra) (hy : y ∈ θ.cartanP) :
    killingForm R L x y = 0 := by
  rw [LieHom.mem_fixedSubalgebra, coe_toLieHom] at hx
  rw [mem_cartanP] at hy
  refine self_eq_neg.mp ?_
  conv_lhs => rw [← killingForm_of_equiv_apply θ, hx, hy, map_neg]

/-! ### The twisted Killing form -/

variable (θ) in
/-- The twisted Killing form `B_θ(x, y) = -B(x, θ y)` of a Lie algebra automorphism `θ`, where
`B` is the Killing form. When `θ` is a Cartan involution it is an inner product. -/
noncomputable def twistedKillingForm : LinearMap.BilinForm R L :=
  -(killingForm R L).compl₂ (θ.toLinearEquiv : L →ₗ[R] L)

@[simp]
theorem twistedKillingForm_apply (x y : L) :
    θ.twistedKillingForm x y = -killingForm R L x (θ y) := by
  simp [twistedKillingForm]

/-- Pulling back the twisted Killing form of a conjugate automorphism `e.symm.trans (θ.trans e)`
along `e` recovers `θ.twistedKillingForm`. -/
theorem twistedKillingForm_conj {M : Type*} [LieRing M] [LieAlgebra R M]
    (θ : L ≃ₗ⁅R⁆ L) (e : L ≃ₗ⁅R⁆ M) (x y : M) :
    (e.symm.trans (θ.trans e)).twistedKillingForm x y =
      θ.twistedKillingForm (e.symm x) (e.symm y) := by
  simp only [twistedKillingForm_apply, trans_apply]
  rw [← killingForm_of_equiv_apply e (e.symm x) (θ (e.symm y)), e.apply_symm_apply]

/-- On the second argument in `𝔨`, the twisted Killing form is `-B`. -/
theorem twistedKillingForm_apply_of_mem_fixedSubalgebra {x y : L}
    (hy : y ∈ θ.toLieHom.fixedSubalgebra) : θ.twistedKillingForm x y = -killingForm R L x y := by
  rw [LieHom.mem_fixedSubalgebra, coe_toLieHom] at hy
  rw [twistedKillingForm_apply, hy]

/-- On the second argument in `𝔭`, the twisted Killing form coincides with `B`. -/
theorem twistedKillingForm_apply_of_mem_cartanP {x y : L} (hy : y ∈ θ.cartanP) :
    θ.twistedKillingForm x y = killingForm R L x y := by
  rw [twistedKillingForm_apply, mem_cartanP.mp hy, map_neg, neg_neg]

/-- The twisted Killing form is invariant under every automorphism commuting with `θ`. -/
theorem twistedKillingForm_map_map_of_commute {φ : L ≃ₗ⁅R⁆ L} (hφ : ∀ x, θ (φ x) = φ (θ x))
    (x y : L) :
    θ.twistedKillingForm (φ x) (φ y) = θ.twistedKillingForm x y := by
  rw [twistedKillingForm_apply, twistedKillingForm_apply, hφ, killingForm_of_equiv_apply]

/-- `θ` is orthogonal for its twisted Killing form. -/
theorem twistedKillingForm_map_map (x y : L) :
    θ.twistedKillingForm (θ x) (θ y) = θ.twistedKillingForm x y :=
  twistedKillingForm_map_map_of_commute (fun _ ↦ rfl) x y

/-- The twisted Killing form of an involution is symmetric. -/
theorem isSymm_twistedKillingForm (hθ : Function.Involutive θ) : θ.twistedKillingForm.IsSymm := by
  refine ⟨fun x y ↦ ?_⟩
  rw [twistedKillingForm_apply, twistedKillingForm_apply,
    ← killingForm_of_equiv_apply θ y, hθ, traceForm_comm]

/-- For `x ∈ 𝔨`, `ad x` is skew-adjoint for the twisted Killing form. -/
theorem ad_mem_skewAdjointSubmodule_twistedKillingForm {x : L}
    (hx : x ∈ θ.toLieHom.fixedSubalgebra) :
    ad R L x ∈ θ.twistedKillingForm.skewAdjointSubmodule := by
  rw [LieHom.mem_fixedSubalgebra, coe_toLieHom] at hx
  rw [LinearMap.mem_skewAdjointSubmodule]
  intro y z
  simp only [twistedKillingForm_apply, Pi.neg_apply, ad_apply, map_neg, map_lie, hx, neg_neg,
    traceForm_apply_lie_apply']

/-- For `x ∈ 𝔭`, `ad x` is self-adjoint for the twisted Killing form. -/
theorem ad_mem_selfAdjointSubmodule_twistedKillingForm {x : L} (hx : x ∈ θ.cartanP) :
    ad R L x ∈ θ.twistedKillingForm.selfAdjointSubmodule := by
  rw [mem_cartanP] at hx
  rw [LinearMap.mem_selfAdjointSubmodule]
  intro y z
  simp only [twistedKillingForm_apply, ad_apply, map_lie, hx, neg_lie, map_neg,
    traceForm_apply_lie_apply']

end LieEquiv
