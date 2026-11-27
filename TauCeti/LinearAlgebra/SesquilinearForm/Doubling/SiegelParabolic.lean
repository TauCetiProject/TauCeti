/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Complement
public import TauCeti.Algebra.Module.Equiv.Basic
public import TauCeti.LinearAlgebra.SesquilinearForm.Doubling.Basic
public import TauCeti.LinearAlgebra.SesquilinearForm.SignedHermitianSpace.Basic

/-!
# The Siegel parabolic of a doubled space and its Levi decomposition

Let `B` be a sesquilinear form on an `R`-module `M`, and `W = M × M` with the doubled form
`B ⊕ (-B)` (`LinearMap.doubled`). The diagonal `D = {(y, y)}` and the antidiagonal
`A = {(x, -x)}` are isotropic, and when `2` is invertible `W = A ⊕ D`, the doubled form pairing
`A` with `D` through `2 • B`. For a hermitian form `h` on a space `V` over a quadratic étale
algebra this is the doubled hermitian space `V ⊕ (-V)` of the doubling method, and the
stabilizer of `D` in its unitary similitude group `GU(W)` is the **Siegel parabolic** `P`,
the parabolic subgroup from which the Siegel Eisenstein series of the doubling method is induced.

Write automorphisms of `W` in the polarization coordinates `A ⊕ D`
(`TauCeti.antidiagDiagEquiv`). An automorphism stabilizes `D` exactly when it is block
triangular, acting by some `a` on `W / D ≅ A`, by some `d` on `D`, with an off-diagonal block
`A → D`. This file proves the Levi decomposition of `P`:

* the **Levi subgroup** `L ≤ P`, the similitudes stabilizing both `A` and `D`, consists of the
  block-diagonal maps `m(a, d)` (`TauCeti.siegelLeviHom`) with multiplier `c` such that
  `B (a x) (d y) = c • B x y` and `B (d x) (a y) = c • B x y`. For a nondegenerate hermitian
  form this says `a = c (d*)⁻¹`, so the Levi elements are the `m(c (d*)⁻¹, d)`;
* the **unipotent radical** `N ≤ P`, the similitudes of multiplier `1` acting trivially on `D`
  and on `W / D`, consists of the maps `n(X)` (`TauCeti.siegelUnipotentHom`) for the
  skew-adjoint `X : A → D`, `B (X x) y = -B x (X y)`; and `n(X) n(Y) = n(X + Y)`;
* every element of `P` is uniquely `m n` with `m ∈ L` and `n ∈ N`, `N` is normal in `P`, and
  `m(a, d) n(X) m(a, d)⁻¹ = n(d X a⁻¹)`.

The restriction of an element of `P` to `D` is a group morphism `Δ : P → GL(M)`
(`LinearMap.siegelDiagHom`). Its product `(Δ, ν)` with the multiplier is injective on `L` when
`B` is left-separating (`LinearMap.eq_of_mem_siegelLevi`). On a signed hermitian space, `m(a, d)`
with multiplier `c` fixed by the involution lies in `L` as soon as `h (a x) (d y) = c h x y`
(`TauCeti.SignedHermitianSpace.siegelLeviHom_mem_siegelLevi`); this needs no field, so it covers
split algebras such as `F × F`. On a finite-dimensional space over a field the adjoint provides
such an `a` for every `d`, so the image of `(Δ, ν)` on `L` contains every pair `(d, c)` with `c`
fixed by the involution (`TauCeti.SignedHermitianSpace.exists_siegelLeviHom_mem_siegelLevi`).

## Main definitions

* `LinearMap.siegelParabolic`: the similitudes of the doubled form stabilizing the diagonal.
* `LinearMap.siegelLevi`: the elements of the Siegel parabolic stabilizing the antidiagonal.
* `LinearMap.siegelRadical`: the similitudes of multiplier `1` fixing the diagonal pointwise and
  acting trivially modulo it.
* `TauCeti.siegelLeviHom`, `TauCeti.siegelUnipotentHom`: the block-diagonal and the unipotent
  automorphisms of `M × M` in polarization coordinates.
* `LinearMap.siegelDiagHom`: the restriction of the Siegel parabolic to the diagonal.

## Main results

* `LinearMap.mem_siegelLevi_iff_exists_siegelLeviHom`: the Levi subgroup in coordinates.
* `LinearMap.mem_siegelRadical_iff_exists_siegelUnipotentHom`: the unipotent radical is the
  group of the `n(X)` for skew-adjoint `X`.
* `LinearMap.mem_siegelParabolic_iff_exists_siegelLeviHom_mul_siegelUnipotentHom`: the Siegel
  parabolic in coordinates.
* `LinearMap.isComplement'_siegelLevi_siegelRadical`,
  `LinearMap.normal_siegelRadical_subgroupOf` (an instance): the Levi decomposition
  `P = L ⋉ N`.
* `TauCeti.siegelLeviHom_mul_siegelUnipotentHom_mul_inv`: the conjugation action of the Levi
  subgroup on the unipotent radical.

## References

* E. Eischen, M. Harris, J.-S. Li and C. Skinner, *p-adic L-functions for unitary groups*,
  Forum Math. Pi 8 (2020), §4.1.1–4.1.2.
* S. Gelbart, I. Piatetski-Shapiro and S. Rallis, *Explicit constructions of automorphic
  L-functions*, Lecture Notes in Math. 1254 (1987), Part A.
-/

public section

open Module Submodule
open scoped Pointwise

/-! ### Block-diagonal and unipotent automorphisms in polarization coordinates -/

namespace TauCeti

variable (R M : Type*) [CommRing R] [Invertible (2 : R)] [AddCommGroup M] [Module R M]

/-- The automorphism `m(a, d)` of `M × M` acting by `a` on the antidiagonal and by `d` on the
diagonal: `(x, -x) ↦ (a x, -a x)` and `(y, y) ↦ (d y, d y)`. It is the block-diagonal map
`a × d` read in the polarization coordinates `antidiagDiagEquiv`. -/
def siegelLeviHom : (M ≃ₗ[R] M) × (M ≃ₗ[R] M) →* (M × M) ≃ₗ[R] M × M :=
  (MulAut.conj (antidiagDiagEquiv R M)).toMonoidHom.comp
    { toFun := fun p ↦ p.1.prodCongr p.2
      map_one' := LinearEquiv.ext fun _ ↦ rfl
      map_mul' := fun _ _ ↦ LinearEquiv.ext fun _ ↦ rfl }

/-- The unipotent automorphism `n(X)` of `M × M` fixing the diagonal pointwise and sending
`(x, -x)` to `(x, -x) + (X x, X x)`. It is the shear `(u, v) ↦ (u, v + X u)` read in the
polarization coordinates `antidiagDiagEquiv`; additively in `X`, `n(X + Y) = n(X) n(Y)`. -/
def siegelUnipotentHom : Multiplicative (M →ₗ[R] M) →* (M × M) ≃ₗ[R] M × M :=
  (MulAut.conj (antidiagDiagEquiv R M)).toMonoidHom.comp
    { toFun := fun X ↦ (LinearEquiv.refl R M).skewProd (LinearEquiv.refl R M) X.toAdd
      map_one' := LinearEquiv.ext fun _ ↦ by simp [LinearEquiv.skewProd_apply]
      map_mul' := fun _ _ ↦ LinearEquiv.ext fun _ ↦ Prod.ext (by simp [LinearEquiv.skewProd_apply])
        (by simp only [LinearEquiv.skewProd_apply, LinearEquiv.refl_apply, toAdd_mul,
          LinearMap.add_apply, mul_apply_eq_comp]; abel) }

variable {R M}

/-- `m(a, d)` is the conjugate of `a.prodCongr d` by the polarization coordinates. -/
theorem siegelLeviHom_def (a d : M ≃ₗ[R] M) :
    siegelLeviHom R M (a, d) = MulAut.conj (antidiagDiagEquiv R M) (a.prodCongr d) := (rfl)

/-- `n(X)` is the conjugate of the shear `(u, v) ↦ (u, v + X u)` by the polarization
coordinates. -/
theorem siegelUnipotentHom_def (X : M →ₗ[R] M) :
    siegelUnipotentHom R M (.ofAdd X) = MulAut.conj (antidiagDiagEquiv R M)
      ((LinearEquiv.refl R M).skewProd (LinearEquiv.refl R M) X) := (rfl)

private theorem antidiag_eq (x : M) : ((x, -x) : M × M) = antidiagDiagEquiv R M (x, 0) := by
  simp

private theorem diag_eq (y : M) : ((y, y) : M × M) = antidiagDiagEquiv R M (0, y) := by
  simp

/-- `m(a, d)` acts by `a` on the antidiagonal. -/
@[simp]
theorem siegelLeviHom_apply_antidiag (a d : M ≃ₗ[R] M) (x : M) :
    siegelLeviHom R M (a, d) (x, -x) = (a x, -a x) := by
  rw [antidiag_eq (R := R), siegelLeviHom_def, LinearEquiv.mulAut_conj_apply_apply]
  simp

/-- `m(a, d)` acts by `d` on the diagonal. -/
@[simp]
theorem siegelLeviHom_apply_diag (a d : M ≃ₗ[R] M) (y : M) :
    siegelLeviHom R M (a, d) (y, y) = (d y, d y) := by
  rw [diag_eq (R := R), siegelLeviHom_def, LinearEquiv.mulAut_conj_apply_apply]
  simp

/-- `n(X)` sends `(x, -x)` to `(x, -x) + (X x, X x)`. -/
@[simp]
theorem siegelUnipotentHom_apply_antidiag (X : M →ₗ[R] M) (x : M) :
    siegelUnipotentHom R M (.ofAdd X) (x, -x) = (x + X x, -x + X x) := by
  rw [antidiag_eq (R := R), siegelUnipotentHom_def, LinearEquiv.mulAut_conj_apply_apply]
  simp [LinearEquiv.skewProd_apply, sub_eq_neg_add]

/-- `n(X)` fixes the diagonal pointwise. -/
@[simp]
theorem siegelUnipotentHom_apply_diag (X : M →ₗ[R] M) (y : M) :
    siegelUnipotentHom R M (.ofAdd X) (y, y) = (y, y) := by
  rw [diag_eq (R := R), siegelUnipotentHom_def, LinearEquiv.mulAut_conj_apply_apply]
  simp [LinearEquiv.skewProd_apply]

/-- The block-diagonal map `m(a, d)` determines `a` and `d`. -/
theorem siegelLeviHom_injective : Function.Injective (siegelLeviHom R M) := by
  rintro ⟨a, d⟩ ⟨a', d'⟩ h
  rw [siegelLeviHom_def, siegelLeviHom_def] at h
  have := (MulAut.conj (antidiagDiagEquiv R M)).injective h
  rw [LinearEquiv.prodCongr_inj] at this
  rw [this.1, this.2]

/-- The unipotent map `n(X)` determines `X`. -/
theorem siegelUnipotentHom_injective : Function.Injective (siegelUnipotentHom R M) := by
  intro X Y h
  obtain ⟨X, rfl⟩ := Multiplicative.ofAdd.surjective X
  obtain ⟨Y, rfl⟩ := Multiplicative.ofAdd.surjective Y
  rw [siegelUnipotentHom_def, siegelUnipotentHom_def] at h
  have h := (MulAut.conj (antidiagDiagEquiv R M)).injective h
  refine congrArg Multiplicative.ofAdd (LinearMap.ext fun x ↦ ?_)
  simpa [LinearEquiv.skewProd_apply] using congrArg Prod.snd (DFunLike.congr_fun h (x, 0))

/-- **Conjugation of the unipotent radical by the Levi subgroup**:
`m(a, d) n(X) m(a, d)⁻¹ = n(d X a⁻¹)`. -/
theorem siegelLeviHom_mul_siegelUnipotentHom_mul_inv (a d : M ≃ₗ[R] M) (X : M →ₗ[R] M) :
    siegelLeviHom R M (a, d) * siegelUnipotentHom R M (.ofAdd X) * (siegelLeviHom R M (a, d))⁻¹ =
      siegelUnipotentHom R M (.ofAdd ((d : M →ₗ[R] M) ∘ₗ X ∘ₗ (a.symm : M →ₗ[R] M))) := by
  rw [← map_inv, siegelLeviHom_def, siegelLeviHom_def, siegelUnipotentHom_def,
    siegelUnipotentHom_def, ← map_mul, ← map_mul]
  congr 1
  ext ⟨x, y⟩ <;> simp [LinearEquiv.skewProd_apply, mul_apply_eq_comp]

end TauCeti

namespace LinearMap

open TauCeti

variable {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] {I₁ I₂ : R →+* R} (B : M →ₛₗ[I₁] M →ₛₗ[I₂] N)
  (S : Type*) [Monoid S] [DistribMulAction S N]

/-! ### The Siegel parabolic, its Levi subgroup and its unipotent radical -/

/-- The **Siegel parabolic** of the doubled form `B ⊕ (-B)`: its similitudes (with multipliers in
`Sˣ`) stabilizing the diagonal `D = {(y, y)}`. For a hermitian form on `V` this is the Siegel
parabolic subgroup `P` of `GU(V ⊕ (-V))` of the doubling method. -/
def siegelParabolic : Subgroup (((M × M) ≃ₗ[R] M × M) × Sˣ) :=
  B.doubled.similitudeGroup S ⊓
    (MulAction.stabilizer ((M × M) ≃ₗ[R] M × M) (LinearMap.id : M →ₗ[R] M).graph).comap
      (MonoidHom.fst _ _)

variable {B S} in
theorem mem_siegelParabolic_iff {g : ((M × M) ≃ₗ[R] M × M) × Sˣ} :
    g ∈ B.siegelParabolic S ↔ g ∈ B.doubled.similitudeGroup S ∧
      (LinearMap.id : M →ₗ[R] M).graph.map (g.1 : (M × M) →ₗ[R] M × M) =
        (LinearMap.id : M →ₗ[R] M).graph :=
  Iff.rfl

/-- The Siegel parabolic consists of similitudes of the doubled form. -/
theorem siegelParabolic_le : B.siegelParabolic S ≤ B.doubled.similitudeGroup S := inf_le_left

/-- The **Levi subgroup** of the Siegel parabolic: its elements which also stabilize the
antidiagonal `A = {(x, -x)}`. -/
def siegelLevi : Subgroup (((M × M) ≃ₗ[R] M × M) × Sˣ) :=
  B.siegelParabolic S ⊓
    (MulAction.stabilizer ((M × M) ≃ₗ[R] M × M) (-LinearMap.id : M →ₗ[R] M).graph).comap
      (MonoidHom.fst _ _)

variable {B S} in
theorem mem_siegelLevi_iff {g : ((M × M) ≃ₗ[R] M × M) × Sˣ} :
    g ∈ B.siegelLevi S ↔ g ∈ B.siegelParabolic S ∧
      (-LinearMap.id : M →ₗ[R] M).graph.map (g.1 : (M × M) →ₗ[R] M × M) =
        (-LinearMap.id : M →ₗ[R] M).graph :=
  Iff.rfl

/-- The Levi subgroup lies in the Siegel parabolic. -/
theorem siegelLevi_le_siegelParabolic : B.siegelLevi S ≤ B.siegelParabolic S := inf_le_left

/-- The **unipotent radical** of the Siegel parabolic: the similitudes of multiplier `1` fixing
the diagonal `D` pointwise and acting trivially on `W / D`, that is `g v - v ∈ D` for every
`v`. -/
def siegelRadical : Subgroup (((M × M) ≃ₗ[R] M × M) × Sˣ) where
  carrier := {g | g ∈ B.doubled.similitudeGroup S ∧ g.2 = 1 ∧ (∀ y, g.1 (y, y) = (y, y)) ∧
    ∀ v, g.1 v - v ∈ (LinearMap.id : M →ₗ[R] M).graph}
  one_mem' := ⟨one_mem _, rfl, fun _ ↦ rfl, fun _ ↦ by simp⟩
  mul_mem' {g h} hg hh := by
    refine ⟨mul_mem hg.1 hh.1, by simp [hg.2.1, hh.2.1], fun y ↦ ?_, fun v ↦ ?_⟩
    · simp [mul_apply_eq_comp, hh.2.2.1, hg.2.2.1]
    · rw [Prod.fst_mul, mul_apply_eq_comp,
        show g.1 (h.1 v) - v = (g.1 (h.1 v) - h.1 v) + (h.1 v - v) by abel]
      exact add_mem (hg.2.2.2 _) (hh.2.2.2 v)
  inv_mem' {g} hg := by
    have hfix (y : M) : g.1.symm (y, y) = (y, y) := by
      rw [LinearEquiv.symm_apply_eq, hg.2.2.1]
    refine ⟨inv_mem hg.1, by simp [hg.2.1], fun y ↦ hfix y, fun v ↦ ?_⟩
    have := neg_mem (hg.2.2.2 (g.1.symm v))
    rwa [LinearEquiv.apply_symm_apply, neg_sub] at this

variable {B S} in
theorem mem_siegelRadical_iff {g : ((M × M) ≃ₗ[R] M × M) × Sˣ} :
    g ∈ B.siegelRadical S ↔ g ∈ B.doubled.similitudeGroup S ∧ g.2 = 1 ∧
      (∀ y, g.1 (y, y) = (y, y)) ∧ ∀ v, g.1 v - v ∈ (LinearMap.id : M →ₗ[R] M).graph :=
  Iff.rfl

/-- The unipotent radical lies in the Siegel parabolic. -/
theorem siegelRadical_le_siegelParabolic : B.siegelRadical S ≤ B.siegelParabolic S := by
  intro g hg
  have hD (v : M × M) (hv : v ∈ (LinearMap.id : M →ₗ[R] M).graph) : g.1 v = v := by
    obtain ⟨y, rfl⟩ : ∃ y, v = (y, y) := ⟨v.1, Prod.ext rfl (by simpa using hv)⟩
    exact hg.2.2.1 y
  refine mem_siegelParabolic_iff.2 ⟨hg.1, le_antisymm ?_ fun v hv ↦ ⟨v, hv, hD v hv⟩⟩
  rintro _ ⟨v, hv, rfl⟩
  rwa [LinearEquiv.coe_coe, hD v hv]

/-! ### The restriction to the diagonal -/

section Diag

variable {B S}

private theorem apply_diag_eq {g : (M × M) ≃ₗ[R] M × M}
    (hg : (LinearMap.id : M →ₗ[R] M).graph.map (g : (M × M) →ₗ[R] M × M) =
      (LinearMap.id : M →ₗ[R] M).graph) (y : M) :
    ((g (y, y)).1, (g (y, y)).1) = g (y, y) := by
  have : g (y, y) ∈ (LinearMap.id : M →ₗ[R] M).graph :=
    hg ▸ Submodule.mem_map_of_mem (by simp)
  exact Prod.ext rfl (by simpa [eq_comm] using this)

private theorem map_symm_graph_id {g : (M × M) ≃ₗ[R] M × M}
    (hg : (LinearMap.id : M →ₗ[R] M).graph.map (g : (M × M) →ₗ[R] M × M) =
      (LinearMap.id : M →ₗ[R] M).graph) :
    (LinearMap.id : M →ₗ[R] M).graph.map (g.symm : (M × M) →ₗ[R] M × M) =
      (LinearMap.id : M →ₗ[R] M).graph :=
  (Submodule.map_symm_eq_iff g).2 hg

end Diag

/-- The **restriction to the diagonal** `Δ : P → GL(M)`: an element `p` of the Siegel parabolic
maps `(y, y)` to `(Δ p y, Δ p y)` (`LinearMap.siegelDiagHom_apply_diag`). For a hermitian form
this is `p ↦ p|_D`. -/
def siegelDiagHom : B.siegelParabolic S →* M ≃ₗ[R] M where
  toFun p :=
    { toFun y := ((p : ((M × M) ≃ₗ[R] M × M) × Sˣ).1 (y, y)).1
      invFun y := ((p : ((M × M) ≃ₗ[R] M × M) × Sˣ).1.symm (y, y)).1
      map_add' x y := by rw [← Prod.fst_add, ← map_add, Prod.mk_add_mk]
      map_smul' c y := by rw [RingHom.id_apply, ← Prod.smul_fst, ← map_smul, Prod.smul_mk]
      left_inv y := by
        dsimp only
        rw [apply_diag_eq (mem_siegelParabolic_iff.1 p.property).2, LinearEquiv.symm_apply_apply]
      right_inv y := by
        dsimp only
        rw [apply_diag_eq (map_symm_graph_id (mem_siegelParabolic_iff.1 p.property).2),
          LinearEquiv.apply_symm_apply] }
  map_one' := LinearEquiv.ext fun _ ↦ rfl
  map_mul' p q := LinearEquiv.ext fun y ↦ by
    simp only [Subgroup.coe_mul, Prod.fst_mul, mul_apply_eq_comp, LinearEquiv.coe_mk,
      LinearMap.coe_mk, AddHom.coe_mk]
    rw [apply_diag_eq (mem_siegelParabolic_iff.1 q.property).2]

variable {B S} in
/-- An element `p` of the Siegel parabolic maps `(y, y)` to `(Δ p y, Δ p y)`. -/
@[simp]
theorem siegelDiagHom_apply_diag (p : B.siegelParabolic S) (y : M) :
    (p : ((M × M) ≃ₗ[R] M × M) × Sˣ).1 (y, y) = (B.siegelDiagHom S p y, B.siegelDiagHom S p y) :=
  (apply_diag_eq (mem_siegelParabolic_iff.1 p.property).2 y).symm

/-- The restriction to the diagonal reads off the first coordinate of the image of `(y, y)`. -/
theorem siegelDiagHom_apply (p : B.siegelParabolic S) (y : M) :
    B.siegelDiagHom S p y = ((p : ((M × M) ≃ₗ[R] M × M) × Sˣ).1 (y, y)).1 := (rfl)

/-! ### The Levi decomposition in polarization coordinates -/

section Polarization

variable [Invertible (2 : R)]

/-- The similitude condition for `B ⊕ (-B)` in polarization coordinates, where the doubled form
is twice the hyperbolic pairing `(p, q) ↦ B p.1 q.2 + B p.2 q.1`. -/
private theorem conj_mem_similitudeGroup_doubled_iff (g : (M × M) ≃ₗ[R] M × M) (c : Sˣ) :
    (MulAut.conj (antidiagDiagEquiv R M) g, c) ∈ B.doubled.similitudeGroup S ↔
      ∀ p q : M × M, B (g p).1 (g q).2 + B (g p).2 (g q).1 = c • (B p.1 q.2 + B p.2 q.1) := by
  rw [mem_similitudeGroup_iff]
  refine ⟨fun h p q ↦ (isUnit_of_invertible (2 : R)).smul_left_cancel.1 ?_, fun h u v ↦ ?_⟩
  · have := h (antidiagDiagEquiv R M p) (antidiagDiagEquiv R M q)
    rw [LinearEquiv.mulAut_conj_apply_apply, LinearEquiv.mulAut_conj_apply_apply,
      doubled_antidiagDiagEquiv, doubled_antidiagDiagEquiv] at this
    simpa only [two_nsmul, smul_add, two_smul] using this
  · obtain ⟨p, rfl⟩ := (antidiagDiagEquiv R M).surjective u
    obtain ⟨q, rfl⟩ := (antidiagDiagEquiv R M).surjective v
    rw [LinearEquiv.mulAut_conj_apply_apply, LinearEquiv.mulAut_conj_apply_apply,
      doubled_antidiagDiagEquiv, doubled_antidiagDiagEquiv, h]
    simp only [two_nsmul, smul_add]

/-- The block-diagonal map `m(a, d)` with multiplier `c` is a similitude of `B ⊕ (-B)` exactly
when `B (a x) (d y) = c • B x y` and `B (d x) (a y) = c • B x y`. For a nondegenerate hermitian
form the first condition says `a = c (d*)⁻¹`. -/
theorem siegelLeviHom_mem_similitudeGroup_iff (a d : M ≃ₗ[R] M) (c : Sˣ) :
    (siegelLeviHom R M (a, d), c) ∈ B.doubled.similitudeGroup S ↔
      (∀ x y, B (a x) (d y) = c • B x y) ∧ ∀ x y, B (d x) (a y) = c • B x y := by
  rw [siegelLeviHom_def, conj_mem_similitudeGroup_doubled_iff]
  refine ⟨fun h ↦ ⟨fun x y ↦ by simpa using h (x, 0) (0, y),
    fun x y ↦ by simpa using h (0, x) (y, 0)⟩, fun ⟨h₁, h₂⟩ p q ↦ ?_⟩
  simp [h₁, h₂, smul_add]

/-- The unipotent map `n(X)` is an isometry of `B ⊕ (-B)` exactly when `X` is skew-adjoint for
`B`. -/
theorem siegelUnipotentHom_mem_similitudeGroup_iff (X : M →ₗ[R] M) :
    (siegelUnipotentHom R M (.ofAdd X), (1 : Sˣ)) ∈ B.doubled.similitudeGroup S ↔
      X ∈ B.skewAdjointAddSubgroup := by
  rw [siegelUnipotentHom_def, conj_mem_similitudeGroup_doubled_iff,
    mem_skewAdjointAddSubgroup_iff]
  refine ⟨fun h x y ↦ ?_, fun h p q ↦ ?_⟩
  · have := h (x, 0) (y, 0)
    simp only [LinearEquiv.skewProd_apply, LinearEquiv.refl_apply, zero_add, map_zero,
      LinearMap.zero_apply, add_zero, smul_zero] at this
    exact eq_neg_of_add_eq_zero_left (by rwa [add_comm] at this)
  · simp only [LinearEquiv.skewProd_apply, LinearEquiv.refl_apply, map_add, LinearMap.add_apply,
      h, one_smul]
    abel

private theorem map_graph_id_conj_eq_iff (g : (M × M) ≃ₗ[R] M × M) :
    (LinearMap.id : M →ₗ[R] M).graph.map
        (MulAut.conj (antidiagDiagEquiv R M) g : (M × M) →ₗ[R] M × M) =
      (LinearMap.id : M →ₗ[R] M).graph ↔
      (range (inr R M M)).map (g : (M × M) →ₗ[R] M × M) = range (inr R M M) := by
  rw [← map_antidiagDiagEquiv_range_inr, LinearEquiv.map_map_mulAut_conj]
  exact (Submodule.map_injective_of_injective (antidiagDiagEquiv R M).injective).eq_iff

private theorem map_graph_neg_id_conj_eq_iff (g : (M × M) ≃ₗ[R] M × M) :
    (-LinearMap.id : M →ₗ[R] M).graph.map
        (MulAut.conj (antidiagDiagEquiv R M) g : (M × M) →ₗ[R] M × M) =
      (-LinearMap.id : M →ₗ[R] M).graph ↔
      (range (inl R M M)).map (g : (M × M) →ₗ[R] M × M) = range (inl R M M) := by
  rw [← map_antidiagDiagEquiv_range_inl, LinearEquiv.map_map_mulAut_conj]
  exact (Submodule.map_injective_of_injective (antidiagDiagEquiv R M).injective).eq_iff

variable {B S}

/-- **The Levi subgroup in coordinates.** An element of the Levi subgroup is a block-diagonal
map `m(a, d)`, acting by `a` on the antidiagonal and by `d` on the diagonal, whose multiplier `c`
satisfies `B (a x) (d y) = c • B x y` and `B (d x) (a y) = c • B x y`. -/
theorem mem_siegelLevi_iff_exists_siegelLeviHom {g : ((M × M) ≃ₗ[R] M × M) × Sˣ} :
    g ∈ B.siegelLevi S ↔ ∃ a d : M ≃ₗ[R] M, siegelLeviHom R M (a, d) = g.1 ∧
      (∀ x y, B (a x) (d y) = g.2 • B x y) ∧ ∀ x y, B (d x) (a y) = g.2 • B x y := by
  refine ⟨fun hg ↦ ?_, ?_⟩
  · obtain ⟨hP, hA⟩ := mem_siegelLevi_iff.1 hg
    obtain ⟨hsim, hD⟩ := mem_siegelParabolic_iff.1 hP
    obtain ⟨g', hg'⟩ := (MulAut.conj (antidiagDiagEquiv R M)).surjective g.1
    rw [← hg', map_graph_id_conj_eq_iff] at hD
    rw [← hg', map_graph_neg_id_conj_eq_iff] at hA
    obtain ⟨a, d, rfl⟩ := LinearEquiv.exists_prodCongr_eq_iff.2
      ⟨fun x ↦ by
        obtain ⟨y, hy⟩ : g' (x, 0) ∈ range (inl R M M) :=
          hA ▸ Submodule.mem_map_of_mem (mem_range_self (inl R M M) x)
        rw [← hy, inl_apply],
      fun y ↦ by
        obtain ⟨x, hx⟩ : g' (0, y) ∈ range (inr R M M) :=
          hD ▸ Submodule.mem_map_of_mem (mem_range_self (inr R M M) y)
        rw [← hx, inr_apply]⟩
    rw [← siegelLeviHom_def] at hg'
    refine ⟨a, d, hg', (siegelLeviHom_mem_similitudeGroup_iff B S a d g.2).1 ?_⟩
    rwa [hg']
  · rintro ⟨a, d, hg, h₁, h₂⟩
    have hsim := (siegelLeviHom_mem_similitudeGroup_iff B S a d g.2).2 ⟨h₁, h₂⟩
    rw [hg] at hsim
    refine mem_siegelLevi_iff.2 ⟨mem_siegelParabolic_iff.2 ⟨hsim, ?_⟩, ?_⟩
    · rw [← hg, siegelLeviHom_def, map_graph_id_conj_eq_iff]
      exact LinearEquiv.map_range_inr_prodCongr a d
    · rw [← hg, siegelLeviHom_def, map_graph_neg_id_conj_eq_iff]
      exact LinearEquiv.map_range_inl_prodCongr a d

/-- **The unipotent radical in coordinates.** The unipotent radical consists of the maps `n(X)`,
`(x, -x) ↦ (x, -x) + (X x, X x)` fixing the diagonal, for the endomorphisms `X` skew-adjoint
for `B`, with multiplier `1`. -/
theorem mem_siegelRadical_iff_exists_siegelUnipotentHom {g : ((M × M) ≃ₗ[R] M × M) × Sˣ} :
    g ∈ B.siegelRadical S ↔
      g.2 = 1 ∧ ∃ X ∈ B.skewAdjointAddSubgroup, siegelUnipotentHom R M (.ofAdd X) = g.1 := by
  refine ⟨fun ⟨hsim, hc, hfix, hD⟩ ↦ ⟨hc, ?_⟩, ?_⟩
  · obtain ⟨g', hg'⟩ := (MulAut.conj (antidiagDiagEquiv R M)).surjective g.1
    have hφ (p : M × M) : g.1 (antidiagDiagEquiv R M p) = antidiagDiagEquiv R M (g' p) := by
      rw [← hg', LinearEquiv.mulAut_conj_apply_apply]
    -- `g'` fixes `0 × M` pointwise and acts trivially modulo it.
    have h₀ (y : M) : g' (0, y) = (0, y) :=
      (antidiagDiagEquiv R M).injective (by rw [← hφ]; simpa using hfix y)
    have h₁ (x : M) : (g' (x, 0)).1 = x := by
      have := hD (antidiagDiagEquiv R M (x, 0))
      rw [hφ, ← map_sub, antidiagDiagEquiv_apply, mem_graph_iff, id_apply] at this
      dsimp only at this
      refine sub_eq_zero.1 ((isUnit_of_invertible (2 : R)).smul_left_cancel.1 ?_)
      calc (2 : R) • ((g' (x, 0)).1 - x)
          = (g' (x, 0) - (x, 0)).1 + (g' (x, 0) - (x, 0)).2 -
            ((g' (x, 0) - (x, 0)).2 - (g' (x, 0) - (x, 0)).1) := by
            simp only [Prod.fst_sub, Prod.snd_sub, sub_zero, two_smul]; abel
        _ = (2 : R) • 0 := by rw [this, sub_self, smul_zero]
    let X : M →ₗ[R] M := snd R M M ∘ₗ (g' : (M × M) →ₗ[R] M × M) ∘ₗ inl R M M
    have hX : siegelUnipotentHom R M (.ofAdd X) = g.1 := by
      rw [siegelUnipotentHom_def, ← hg']
      congr 1
      ext ⟨x, y⟩ <;>
        rw [show ((x, y) : M × M) = (x, 0) + (0, y) by simp, map_add, map_add] <;>
        simp [LinearEquiv.skewProd_apply, X, h₀, h₁, add_comm]
    refine ⟨X, (siegelUnipotentHom_mem_similitudeGroup_iff B S X).1 ?_, hX⟩
    rw [hX, ← hc]
    exact hsim
  · rintro ⟨hc, X, hX, hg⟩
    have hsim := (siegelUnipotentHom_mem_similitudeGroup_iff B S X).2 hX
    rw [hg, ← hc] at hsim
    refine ⟨hsim, hc, fun y ↦ by rw [← hg, siegelUnipotentHom_apply_diag], fun v ↦ ?_⟩
    obtain ⟨p, rfl⟩ := (antidiagDiagEquiv R M).surjective v
    rw [← hg, siegelUnipotentHom_def, LinearEquiv.mulAut_conj_apply_apply, ← map_sub]
    simp [LinearEquiv.skewProd_apply]

/-- **The Siegel parabolic in coordinates.** Every element of the Siegel parabolic is
`m(a, d) n(X)` for automorphisms `a`, `d` and an endomorphism `X` skew-adjoint for `B`, its
multiplier `c` satisfying `B (a x) (d y) = c • B x y` and `B (d x) (a y) = c • B x y`; and each
such product lies in the Siegel parabolic. -/
theorem mem_siegelParabolic_iff_exists_siegelLeviHom_mul_siegelUnipotentHom
    {g : ((M × M) ≃ₗ[R] M × M) × Sˣ} :
    g ∈ B.siegelParabolic S ↔ ∃ (a d : M ≃ₗ[R] M) (X : M →ₗ[R] M),
      siegelLeviHom R M (a, d) * siegelUnipotentHom R M (.ofAdd X) = g.1 ∧
      (∀ x y, B (a x) (d y) = g.2 • B x y) ∧ (∀ x y, B (d x) (a y) = g.2 • B x y) ∧
      X ∈ B.skewAdjointAddSubgroup := by
  refine ⟨fun hg ↦ ?_, ?_⟩
  · obtain ⟨hsim, hD⟩ := mem_siegelParabolic_iff.1 hg
    obtain ⟨g', hg'⟩ := (MulAut.conj (antidiagDiagEquiv R M)).surjective g.1
    rw [← hg', map_graph_id_conj_eq_iff] at hD
    obtain ⟨a, d, f, rfl⟩ := LinearEquiv.exists_skewProd_eq_iff.2 hD
    let X : M →ₗ[R] M := (d.symm : M →ₗ[R] M) ∘ₗ f
    have hX : siegelLeviHom R M (a, d) * siegelUnipotentHom R M (.ofAdd X) = g.1 := by
      rw [siegelLeviHom_def, siegelUnipotentHom_def, ← map_mul, ← hg']
      congr 1
      ext ⟨x, y⟩ <;> simp [LinearEquiv.skewProd_apply, mul_apply_eq_comp, X]
    have hsim' := (conj_mem_similitudeGroup_doubled_iff B S (a.skewProd d f) g.2).1
      (by rw [hg']; exact hsim)
    have h₁ (x y : M) : B (a x) (d y) = g.2 • B x y := by
      simpa [LinearEquiv.skewProd_apply] using hsim' (x, 0) (0, y)
    have h₂ (x y : M) : B (d x) (a y) = g.2 • B x y := by
      simpa [LinearEquiv.skewProd_apply] using hsim' (0, x) (y, 0)
    refine ⟨a, d, X, hX, h₁, h₂, (siegelUnipotentHom_mem_similitudeGroup_iff B S X).1 ?_⟩
    have hm := (siegelLeviHom_mem_similitudeGroup_iff B S a d g.2).2 ⟨h₁, h₂⟩
    have heq : (siegelLeviHom R M (a, d), g.2)⁻¹ * g = (siegelUnipotentHom R M (.ofAdd X), 1) :=
      Prod.ext (by rw [Prod.fst_mul, Prod.fst_inv, ← hX, inv_mul_cancel_left])
        (by rw [Prod.snd_mul, Prod.snd_inv, inv_mul_cancel])
    rw [← heq]
    exact mul_mem (inv_mem hm) hsim
  · rintro ⟨a, d, X, hg, h₁, h₂, hX⟩
    have hm : (siegelLeviHom R M (a, d), g.2) ∈ B.siegelLevi S :=
      mem_siegelLevi_iff_exists_siegelLeviHom.2 ⟨a, d, rfl, h₁, h₂⟩
    have hn : (siegelUnipotentHom R M (.ofAdd X), (1 : Sˣ)) ∈ B.siegelRadical S :=
      mem_siegelRadical_iff_exists_siegelUnipotentHom.2 ⟨rfl, X, hX, rfl⟩
    have := mul_mem (siegelLevi_le_siegelParabolic B S hm) (siegelRadical_le_siegelParabolic B S hn)
    rwa [Prod.mk_mul_mk, hg, mul_one] at this

/-- In the coordinates `p = m(a, d) n(X)`, the restriction of `p` to the diagonal is `d`. -/
theorem siegelDiagHom_eq_of_eq_siegelLeviHom_mul_siegelUnipotentHom (p : B.siegelParabolic S)
    {a d : M ≃ₗ[R] M} {X : M →ₗ[R] M}
    (hp : siegelLeviHom R M (a, d) * siegelUnipotentHom R M (.ofAdd X) =
      (p : ((M × M) ≃ₗ[R] M × M) × Sˣ).1) :
    B.siegelDiagHom S p = d :=
  LinearEquiv.ext fun y ↦ by simp [siegelDiagHom_apply, ← hp, mul_apply_eq_comp]

/-- **Uniqueness of the Levi coordinates.** For a left-separating form, an element of the Levi
subgroup is determined by its action on the diagonal and its multiplier. For a hermitian form
this identifies the Levi subgroup with a subgroup of `GL(V) × Sˣ` through `(Δ, ν)`. -/
theorem eq_of_mem_siegelLevi (hB : B.SeparatingLeft) {g g' : ((M × M) ≃ₗ[R] M × M) × Sˣ}
    (hg : g ∈ B.siegelLevi S) (hg' : g' ∈ B.siegelLevi S)
    (hd : ∀ y, g.1 (y, y) = g'.1 (y, y)) (hc : g.2 = g'.2) : g = g' := by
  obtain ⟨a, d, hgad, h₁, -⟩ := mem_siegelLevi_iff_exists_siegelLeviHom.1 hg
  obtain ⟨a', d', hgad', h₁', -⟩ := mem_siegelLevi_iff_exists_siegelLeviHom.1 hg'
  have hdd : d = d' := LinearEquiv.ext fun y ↦ by
    simpa [← hgad, ← hgad'] using congrArg Prod.fst (hd y)
  subst hdd
  have haa : a = a' := LinearEquiv.ext fun x ↦ sub_eq_zero.1 <| hB _ fun z ↦ by
    obtain ⟨y, rfl⟩ := d.surjective z
    rw [map_sub, LinearMap.sub_apply, h₁, h₁', hc, sub_self]
  subst haa
  exact Prod.ext (hgad.symm.trans hgad') hc

/-- The Levi subgroup and the unipotent radical meet trivially. -/
theorem disjoint_siegelLevi_siegelRadical : Disjoint (B.siegelLevi S) (B.siegelRadical S) := by
  refine Subgroup.disjoint_def.2 fun {g} hL hN ↦ ?_
  obtain ⟨a, d, hgad, -⟩ := mem_siegelLevi_iff_exists_siegelLeviHom.1 hL
  obtain ⟨hc, X, -, hgX⟩ := mem_siegelRadical_iff_exists_siegelUnipotentHom.1 hN
  have h := hgad.trans hgX.symm
  rw [siegelLeviHom_def, siegelUnipotentHom_def] at h
  have h := (MulAut.conj (antidiagDiagEquiv R M)).injective h
  have hX : X = 0 := LinearMap.ext fun x ↦ by
    simpa [LinearEquiv.skewProd_apply] using (congrArg Prod.snd (DFunLike.congr_fun h (x, 0))).symm
  rw [hX, ofAdd_zero, map_one] at hgX
  exact Prod.ext hgX.symm hc

variable (B S)

/-- **The Levi decomposition, existence.** Every element of the Siegel parabolic is a product
`m n` of an element `m` of the Levi subgroup and an element `n` of the unipotent radical. -/
theorem exists_mem_siegelLevi_mem_siegelRadical_mul_eq {g : ((M × M) ≃ₗ[R] M × M) × Sˣ}
    (hg : g ∈ B.siegelParabolic S) :
    ∃ m ∈ B.siegelLevi S, ∃ n ∈ B.siegelRadical S, m * n = g := by
  obtain ⟨a, d, X, hg, h₁, h₂, hX⟩ :=
    mem_siegelParabolic_iff_exists_siegelLeviHom_mul_siegelUnipotentHom.1 hg
  exact ⟨(siegelLeviHom R M (a, d), g.2),
    mem_siegelLevi_iff_exists_siegelLeviHom.2 ⟨a, d, rfl, h₁, h₂⟩,
    (siegelUnipotentHom R M (.ofAdd X), 1),
    mem_siegelRadical_iff_exists_siegelUnipotentHom.2 ⟨rfl, X, hX, rfl⟩,
    Prod.ext hg (mul_one _)⟩

/-- **The Levi decomposition.** Inside the Siegel parabolic, the Levi subgroup and the unipotent
radical are complements: every element of the Siegel parabolic is uniquely `m n` with `m` in the
Levi subgroup and `n` in the unipotent radical. -/
theorem isComplement'_siegelLevi_siegelRadical :
    ((B.siegelLevi S).subgroupOf (B.siegelParabolic S)).IsComplement'
      ((B.siegelRadical S).subgroupOf (B.siegelParabolic S)) := by
  refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ
    (Subgroup.disjoint_def.2 fun {g} hL hN ↦ Subtype.ext <|
      Subgroup.disjoint_def.1 disjoint_siegelLevi_siegelRadical hL hN)
    (Set.eq_univ_iff_forall.2 fun g ↦ ?_)
  obtain ⟨m, hm, n, hn, hmn⟩ := B.exists_mem_siegelLevi_mem_siegelRadical_mul_eq S g.property
  exact ⟨⟨m, siegelLevi_le_siegelParabolic B S hm⟩, hm,
    ⟨n, siegelRadical_le_siegelParabolic B S hn⟩, hn, Subtype.ext hmn⟩

end Polarization

/-- The unipotent radical is normal in the Siegel parabolic. -/
instance normal_siegelRadical_subgroupOf :
    ((B.siegelRadical S).subgroupOf (B.siegelParabolic S)).Normal := by
  refine ⟨fun n hn p ↦ ?_⟩
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  obtain ⟨hsim, hc, hfix, hD⟩ := hn
  have hpD := (mem_siegelParabolic_iff.1 p.property).2
  set q := (p : ((M × M) ≃ₗ[R] M × M) × Sˣ)
  refine ⟨?_, ?_, fun y ↦ ?_, fun v ↦ ?_⟩
  · have hp := siegelParabolic_le B S p.property
    exact mul_mem (mul_mem hp hsim) (inv_mem hp)
  · simp [hc]
  · simp only [Subgroup.coe_mul, Subgroup.coe_inv, Prod.fst_mul, Prod.fst_inv, mul_apply_eq_comp,
      LinearEquiv.coe_inv]
    rw [← apply_diag_eq (map_symm_graph_id hpD), hfix, apply_diag_eq (map_symm_graph_id hpD),
      LinearEquiv.apply_symm_apply]
  · simp only [Subgroup.coe_mul, Subgroup.coe_inv, Prod.fst_mul, Prod.fst_inv, mul_apply_eq_comp,
      LinearEquiv.coe_inv]
    have hmem := Submodule.mem_map_of_mem (f := (q.1 : (M × M) →ₗ[R] M × M)) (hD (q.1.symm v))
    rwa [hpD, map_sub, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] at hmem

end LinearMap

/-! ### The Levi subgroup of a doubled hermitian space -/

namespace TauCeti.SignedHermitianSpace

section CommRing

variable {K V : Type*} [CommRing K] [Invertible (2 : K)] [AddCommGroup V] [Module K V]
  {σ : K →+* K} {ε : ℤˣ}

/-- On a signed hermitian space `(V, h)`, a block-diagonal map `m(a, d)` with multiplier `c` fixed
by the involution lies in the Levi subgroup of the Siegel parabolic of `V ⊕ (-V)` as soon as
`h (a x) (d y) = c h x y`, that is `a = c (d*)⁻¹`: the second similitude condition follows by
`ε`-hermitian symmetry. No field is needed, so this covers split algebras such as `F × F`. -/
theorem siegelLeviHom_mem_siegelLevi (H : SignedHermitianSpace K V σ ε) (S : Type*)
    [CommSemiring S] [Algebra S K] (a d : V ≃ₗ[K] V) (c : Sˣ)
    (hc : σ (algebraMap S K c) = algebraMap S K c)
    (h : ∀ x y, H.form (a x) (d y) = c • H.form x y) :
    (siegelLeviHom K V (a, d), c) ∈ H.form.siegelLevi S := by
  have hsmul (z : K) : c • z = algebraMap S K c * z := by
    rw [Units.smul_def, Algebra.smul_def]
  refine LinearMap.mem_siegelLevi_iff_exists_siegelLeviHom.2 ⟨a, d, rfl, h, fun x y ↦ ?_⟩
  rw [H.form_swap (a y), h, hsmul, map_mul, hc, hsmul, H.form_swap y x, mul_smul_comm]

end CommRing

section Field

variable {K V : Type*} [Field K] [Invertible (2 : K)] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {σ : K →+* K} {ε : ℤˣ}

/-- **Surjectivity of the Levi coordinates.** On a finite-dimensional signed hermitian space
`(V, h)` over a field, for every automorphism `d` of `V` and every multiplier `c` fixed by the
involution there is a block-diagonal element `m(a, d)` of multiplier `c` in the Levi subgroup of
the Siegel parabolic of `V ⊕ (-V)`: take `a = c (d*)⁻¹`. So the image of the Levi subgroup under
`(Δ, ν)`, which is injective on it by `LinearMap.eq_of_mem_siegelLevi`, contains every pair
`(d, c)` with `c` fixed by the involution. -/
theorem exists_siegelLeviHom_mem_siegelLevi (H : SignedHermitianSpace K V σ ε) (S : Type*)
    [CommSemiring S] [Algebra S K] (d : V ≃ₗ[K] V) (c : Sˣ)
    (hc : σ (algebraMap S K c) = algebraMap S K c) :
    ∃ a : V ≃ₗ[K] V, (siegelLeviHom K V (a, d), c) ∈ H.form.siegelLevi S := by
  set k : Kˣ := Units.map (algebraMap S K : S →* K) c
  have hk : σ k = k := by simpa [k] using hc
  have hsmul (z : K) : c • z = k * z := by
    simp [k, Units.smul_def, Algebra.smul_def]
  -- The adjoints of `d⁻¹` and of `d` are mutually inverse.
  have h₁ :
      signedHermitianAdjoint H (d.symm : Module.End K V) * signedHermitianAdjoint H d = 1 := by
    rw [← signedHermitianAdjoint_mul, ← signedHermitianAdjoint_one H]
    congr 1
    exact LinearMap.ext fun x ↦ d.apply_symm_apply x
  have h₂ :
      signedHermitianAdjoint H d * signedHermitianAdjoint H (d.symm : Module.End K V) = 1 := by
    rw [← signedHermitianAdjoint_mul, ← signedHermitianAdjoint_one H]
    congr 1
    exact LinearMap.ext fun x ↦ d.symm_apply_apply x
  let a : V ≃ₗ[K] V := LinearEquiv.ofLinearMap
    ((k : K) • signedHermitianAdjoint H (d.symm : Module.End K V))
    ((k : K)⁻¹ • signedHermitianAdjoint H d)
    (LinearMap.ext fun x ↦ by
      simpa [smul_smul, k.ne_zero, mul_apply_eq_comp] using LinearMap.congr_fun h₁ x)
    (LinearMap.ext fun x ↦ by
      simpa [smul_smul, k.ne_zero, mul_apply_eq_comp] using LinearMap.congr_fun h₂ x)
  exact ⟨a, H.siegelLeviHom_mem_siegelLevi S a d c hc fun x y ↦ by simp [a, hsmul, hk]⟩

end Field

end TauCeti.SignedHermitianSpace
