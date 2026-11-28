/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.BilinearForm.Properties
public import TauCeti.LinearAlgebra.SesquilinearForm.IsometryGroup
public import TauCeti.LinearAlgebra.Transvection
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Symplectic transvections of an alternating form

Let `ω` be an alternating bilinear form on a module `M` over a commutative ring `R`. For a vector
`v` and a scalar `r`, the **symplectic transvection**

```text
T_v^r : x ↦ x + r ω(v, x) v
```

is Mathlib's transvection `LinearMap.transvection (r • ω v) v`; since `ω(v, v) = 0` it is invertible
and it preserves `ω`. This file packages `T_v^r` as an element of the isometry group
`LinearMap.isometryGroup ω`, the symplectic group `Sp(M, ω)` when `ω` is nondegenerate, and proves
its basic laws:

* `T_v^r T_v^s = T_v^{r+s}`, `T_v^0 = 1`, `T_0^r = 1` and `(T_v^r)⁻¹ = T_v^{-r}`, so that
  `r ↦ T_v^r` is a one-parameter subgroup;
* `T_{cv}^r = T_v^{c²r}`;
* `g T_v^r g⁻¹ = T_{gv}^r` for every isometry `g` of `ω`;
* `T_v^r` is a transvection in the sense of `LinearEquiv.transvections`, hence unipotent:
  `(T_v^r - 1)² = 0`.

Over a field, for `r ≠ 0`, the fixed space of `T_v^r` is the orthogonal `v^⊥ = ker ω(v, ·)` of
`v`, which is a hyperplane when `ω` is left-separating and `v ≠ 0`, and the image of
`T_v^r - 1` is the line through `v`. Conversely, when `ω` is left-separating, every unipotent
isometry of `ω` whose fixed space is a hyperplane is a symplectic transvection
(`LinearMap.BilinForm.IsAlt.exists_eq_symplecticTransvection`).

For the standard form `ω(x, y) = xᵀ J y` on `Fin (m + m) → R`, both this `T_v^r` and the matrix
`TauCeti.GLSymplecticFin.symplecticTransvection v r` of the standard symplectic group are the map
`LinearMap.transvection (r • ω v) v` (`LinearMap.BilinForm.IsAlt.coe_symplecticTransvection` and
`TauCeti.GLSymplecticFin.toLin'_symplecticTransvection`), so the coordinate laws proved there are
the laws below written in a symplectic basis.

## Main declarations

* `LinearMap.BilinForm.IsAlt.symplecticTransvection`: the transvection `T_v^r` as an isometry of
  `ω`, with its action `LinearMap.BilinForm.IsAlt.symplecticTransvection_apply`.
* `LinearMap.BilinForm.IsAlt.symplecticTransvectionHom`: the one-parameter subgroup `r ↦ T_v^r`.
* `LinearMap.BilinForm.IsAlt.mul_symplecticTransvection_mul_inv`: the conjugation law.
* `LinearMap.BilinForm.IsAlt.sub_one_sq_symplecticTransvection`: unipotence.
* `LinearMap.BilinForm.IsAlt.fixedSubmodule_symplecticTransvection`,
  `LinearMap.BilinForm.IsAlt.range_sub_one_symplecticTransvection`: the fixed hyperplane and the
  displacement line.
* `LinearMap.BilinForm.IsAlt.exists_eq_symplecticTransvection`: the unipotent isometries with a
  fixed hyperplane are the symplectic transvections.

## References

* E. Artin, *Geometric Algebra* (1957), Chapter III, §4.
* B. Lawrence and A. Venkatesh, *Diophantine problems and p-adic period mappings*, Invent. Math.
  221 (2020), §2.7, (2.4).
-/

public section

open Module

namespace LinearMap.BilinForm.IsAlt

section CommRing

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {ω : LinearMap.BilinForm R M}
  (hω : ω.IsAlt)

include hω in
/-- The linear form `r ω(v, ·)` vanishes on `v`, so the transvection it defines is invertible. -/
private theorem smul_apply_self (v : M) (r : R) : (r • ω v) v = 0 := by
  rw [LinearMap.smul_apply, hω.self_eq_zero, smul_zero]

include hω in
/-- The map `x ↦ x + r ω(v, x) v` preserves the alternating form `ω`. -/
private theorem transvection_mem_isometryGroup (v : M) (r : R) :
    LinearEquiv.transvection (hω.smul_apply_self v r) ∈ ω.isometryGroup := by
  refine LinearMap.mem_isometryGroup_iff.mpr fun x y => ?_
  have hxv := hω.neg_eq x v
  simp only [LinearEquiv.transvection.coe_apply, LinearMap.transvection.apply, map_add, map_smul,
    LinearMap.add_apply, LinearMap.smul_apply, hω.self_eq_zero, smul_eq_mul, ← hxv]
  ring

/-- **The symplectic transvection** `T_v^r : x ↦ x + r ω(v, x) v` of an alternating form `ω`, as
an element of the isometry group of `ω`. As a linear map it is Mathlib's
`LinearMap.transvection (r • ω v) v` (`LinearMap.BilinForm.IsAlt.coe_symplecticTransvection`). -/
def symplecticTransvection (v : M) (r : R) : ω.isometryGroup :=
  ⟨LinearEquiv.transvection (hω.smul_apply_self v r), hω.transvection_mem_isometryGroup v r⟩

/-- The symplectic transvection `T_v^r` sends `x` to `x + r ω(v, x) v`. -/
@[simp]
theorem symplecticTransvection_apply (v : M) (r : R) (x : M) :
    (hω.symplecticTransvection v r : M ≃ₗ[R] M) x = x + (r * ω v x) • v :=
  (rfl)

/-- As a linear map, the symplectic transvection `T_v^r` is Mathlib's transvection
`x ↦ x + f x • v` for the linear form `f = r ω(v, ·)`. -/
theorem coe_symplecticTransvection (v : M) (r : R) :
    ((hω.symplecticTransvection v r : M ≃ₗ[R] M) : M →ₗ[R] M) =
      LinearMap.transvection (r • ω v) v :=
  (rfl)

/-- The transvection with parameter zero is the identity. -/
@[simp]
theorem symplecticTransvection_zero_right (v : M) : hω.symplecticTransvection v 0 = 1 :=
  Subtype.ext <| LinearEquiv.ext fun x => by simp

/-- The transvection along the zero vector is the identity. -/
@[simp]
theorem symplecticTransvection_zero_left (r : R) : hω.symplecticTransvection 0 r = 1 :=
  Subtype.ext <| LinearEquiv.ext fun x => by simp

/-- Adding parameters multiplies transvections along the same vector:
`T_v^{r+s} = T_v^r T_v^s`. -/
@[simp]
theorem symplecticTransvection_add (v : M) (r s : R) :
    hω.symplecticTransvection v (r + s) =
      hω.symplecticTransvection v r * hω.symplecticTransvection v s :=
  Subtype.ext <| LinearEquiv.ext fun x => by
    simp only [Subgroup.coe_mul, mul_apply_eq_comp, symplecticTransvection_apply, map_add,
      map_smul, hω.self_eq_zero, mul_zero]
    module

/-- Inverting a transvection negates its parameter: `(T_v^r)⁻¹ = T_v^{-r}`. -/
@[simp]
theorem symplecticTransvection_inv (v : M) (r : R) :
    (hω.symplecticTransvection v r)⁻¹ = hω.symplecticTransvection v (-r) := by
  rw [inv_eq_iff_mul_eq_one, ← symplecticTransvection_add, add_neg_cancel,
    symplecticTransvection_zero_right]

/-- **Rescaling the vector of a transvection** multiplies the parameter by the square of the
scalar: `T_{cv}^r = T_v^{c²r}`. -/
theorem symplecticTransvection_smul (c : R) (v : M) (r : R) :
    hω.symplecticTransvection (c • v) r = hω.symplecticTransvection v (c ^ 2 * r) :=
  Subtype.ext <| LinearEquiv.ext fun x => by
    simp only [symplecticTransvection_apply, map_smul, LinearMap.smul_apply, smul_eq_mul, smul_smul]
    ring_nf

/-- The symplectic transvections along a vector `v` form a one-parameter subgroup `r ↦ T_v^r` of
the isometry group. -/
def symplecticTransvectionHom (v : M) : Multiplicative R →* ω.isometryGroup where
  toFun r := hω.symplecticTransvection v r.toAdd
  map_one' := hω.symplecticTransvection_zero_right v
  map_mul' r s := hω.symplecticTransvection_add v r.toAdd s.toAdd

/-- The one-parameter subgroup of transvections along `v` sends `r` to `T_v^r`. -/
@[simp]
theorem symplecticTransvectionHom_apply (v : M) (r : Multiplicative R) :
    hω.symplecticTransvectionHom v r = hω.symplecticTransvection v r.toAdd :=
  (rfl)

/-- **Conjugating a symplectic transvection** by an isometry `g` of `ω` moves its vector by `g`:
`g T_v^r g⁻¹ = T_{gv}^r`. -/
theorem mul_symplecticTransvection_mul_inv (g : ω.isometryGroup) (v : M) (r : R) :
    g * hω.symplecticTransvection v r * g⁻¹ =
      hω.symplecticTransvection ((g : M ≃ₗ[R] M) v) r := by
  refine Subtype.ext <| LinearEquiv.ext fun x => ?_
  -- Write `x = g y`; then `ω(g v, x) = ω(v, y)` because `g` preserves `ω`.
  obtain ⟨y, rfl⟩ := (g : M ≃ₗ[R] M).surjective x
  have hy : (((g⁻¹ : ω.isometryGroup) : M ≃ₗ[R] M)) ((g : M ≃ₗ[R] M) y) = y := by
    rw [← mul_apply_eq_comp, ← Subgroup.coe_mul, inv_mul_cancel, Subgroup.coe_one,
      one_apply_eq_self]
  simp only [Subgroup.coe_mul, mul_apply_eq_comp, hy, symplecticTransvection_apply, map_add,
    map_smul, LinearMap.isometryGroup_map_app]

/-- The symplectic transvection `T_v^r` is a transvection in the sense of
`LinearEquiv.transvections`. -/
theorem symplecticTransvection_mem_transvections (v : M) (r : R) :
    (hω.symplecticTransvection v r : M ≃ₗ[R] M) ∈ LinearEquiv.transvections R M :=
  ⟨_, _, hω.smul_apply_self v r, rfl⟩

/-- **Symplectic transvections are unipotent**: `(T_v^r - 1)² = 0`. -/
theorem sub_one_sq_symplecticTransvection (v : M) (r : R) :
    (((hω.symplecticTransvection v r : M ≃ₗ[R] M) : Module.End R M) - 1) ^ 2 = 0 :=
  LinearEquiv.sub_one_sq_eq_zero_of_mem_transvections
    (hω.symplecticTransvection_mem_transvections v r)

end CommRing

section Field

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {ω : LinearMap.BilinForm K V}
  (hω : ω.IsAlt)

/-- **The fixed space of a symplectic transvection.** For `r ≠ 0`, the vectors fixed by `T_v^r`
are those orthogonal to `v`, the kernel of `ω(v, ·)`. -/
theorem fixedSubmodule_symplecticTransvection (v : V) {r : K} (hr : r ≠ 0) :
    LinearMap.fixedSubmodule ((hω.symplecticTransvection v r : V ≃ₗ[K] V) : V →ₗ[K] V) =
      LinearMap.ker (ω v) := by
  obtain rfl | hv := eq_or_ne v 0
  · ext x
    simp [LinearMap.mem_fixedSubmodule_iff]
  rw [coe_symplecticTransvection, LinearMap.transvection.fixedSubmodule_eq_ker hv,
    LinearMap.ker_smul _ _ hr]

/-- **The fixed space of a symplectic transvection is a hyperplane.** For a left-separating
alternating form `ω`, `v ≠ 0` and `r ≠ 0`, the fixed space of `T_v^r` has codimension one. -/
theorem finrank_quotient_fixedSubmodule_symplecticTransvection (hsep : ω.SeparatingLeft)
    {v : V} (hv : v ≠ 0) {r : K} (hr : r ≠ 0) :
    finrank K (V ⧸ LinearMap.fixedSubmodule
      ((hω.symplecticTransvection v r : V ≃ₗ[K] V) : V →ₗ[K] V)) = 1 := by
  have hωv : ω v ≠ 0 := fun h => hv (hsep v fun y => by rw [h, LinearMap.zero_apply])
  rw [hω.fixedSubmodule_symplecticTransvection v hr, (ω v).quotKerEquivRange.finrank_eq,
    Module.Dual.range_eq_top_of_ne_zero hωv, finrank_top, finrank_self]

/-- **The displacement of a symplectic transvection.** For a left-separating alternating form
`ω` and `r ≠ 0`, the image of `T_v^r - 1` is the line through `v`. -/
theorem range_sub_one_symplecticTransvection (hsep : ω.SeparatingLeft) (v : V) {r : K}
    (hr : r ≠ 0) :
    LinearMap.range (((hω.symplecticTransvection v r : V ≃ₗ[K] V) : Module.End K V) - 1) =
      K ∙ v := by
  obtain rfl | hv := eq_or_ne v 0
  · simp [Module.End.one_eq_id]
  obtain ⟨y, hy⟩ : ∃ y, ω v y ≠ 0 := by
    by_contra! h
    exact hv (hsep v h)
  refine le_antisymm ?_ ?_
  · rintro _ ⟨x, rfl⟩
    rw [LinearMap.sub_apply, LinearEquiv.coe_coe, symplecticTransvection_apply,
      one_apply_eq_self, add_sub_cancel_left]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v)
  · rw [Submodule.span_singleton_le_iff_mem]
    refine ⟨(r * ω v y)⁻¹ • y, ?_⟩
    rw [LinearMap.sub_apply, LinearEquiv.coe_coe, symplecticTransvection_apply,
      one_apply_eq_self, add_sub_cancel_left, map_smul, smul_eq_mul]
    convert one_smul K v using 2
    field_simp

include hω in
/-- An isometry `x ↦ x + f x • u` of a left-separating alternating form, with `u ≠ 0`, has
`f = r ω(u, ·)` for some scalar `r`. -/
private theorem exists_eq_smul_of_transvection_mem_isometryGroup (hsep : ω.SeparatingLeft)
    {f : Dual K V} {u : V} (hu : u ≠ 0) (hfu : f u = 0)
    (hg : LinearEquiv.transvection hfu ∈ ω.isometryGroup) : ∃ r : K, f = r • ω u := by
  obtain ⟨y, hy⟩ : ∃ y, ω u y ≠ 0 := by
    by_contra! h
    exact hu (hsep u h)
  refine ⟨f y / ω u y, LinearMap.ext fun x => ?_⟩
  -- Expanding `ω(g x, g y) = ω(x, y)` leaves `f y ω(x, u) + f x ω(u, y) = 0`.
  have h := LinearMap.mem_isometryGroup_iff.mp hg x y
  have hxu := hω.neg_eq x u
  simp only [LinearEquiv.transvection.coe_apply, LinearMap.transvection.apply, map_add, map_smul,
    LinearMap.add_apply, LinearMap.smul_apply, hω.self_eq_zero, smul_eq_mul] at h
  rw [LinearMap.smul_apply, smul_eq_mul, div_mul_eq_mul_div, eq_div_iff hy]
  linear_combination h + f y * hxu

/-- **Unipotent isometries with a fixed hyperplane are symplectic transvections.** Let `ω` be a
left-separating alternating form. An isometry `g` of `ω` with `g - 1` nilpotent whose fixed space
has codimension one is `T_v^r` for some `v ≠ 0` and `r ≠ 0`. -/
theorem exists_eq_symplecticTransvection (hsep : ω.SeparatingLeft) {g : ω.isometryGroup}
    (hg : IsNilpotent (((g : V ≃ₗ[K] V) : Module.End K V) - 1))
    (hfix : finrank K (V ⧸ LinearMap.fixedSubmodule ((g : V ≃ₗ[K] V) : V →ₗ[K] V)) = 1) :
    ∃ v ≠ 0, ∃ r ≠ 0, g = hω.symplecticTransvection v r := by
  have hdil : (g : V ≃ₗ[K] V) ∈ LinearEquiv.dilatransvections K V :=
    LinearEquiv.mem_dilatransvections_iff_rank_quotient.mpr
      (rank_eq_one_iff_finrank_eq_one.mpr hfix).le
  obtain ⟨f, u, hfu, hgfu⟩ := (LinearEquiv.mem_transvections_iff_isNilpotent_sub_one hdil).mpr hg
  -- `g` moves some vector, so it is not the identity and `u ≠ 0`.
  have hne : LinearMap.fixedSubmodule ((g : V ≃ₗ[K] V) : V →ₗ[K] V) ≠ ⊤ := by
    intro h
    rw [h, finrank_zero_of_subsingleton] at hfix
    exact zero_ne_one hfix
  have hu : u ≠ 0 := by
    rintro rfl
    refine hne (LinearMap.fixedSubmodule_eq_top_iff.mpr ?_)
    rw [hgfu, LinearEquiv.transvection.coe_toLinearMap, LinearMap.transvection.of_right_eq_zero]
  obtain ⟨r, rfl⟩ := hω.exists_eq_smul_of_transvection_mem_isometryGroup hsep hu hfu
    (hgfu ▸ g.property)
  have hr : r ≠ 0 := by
    rintro rfl
    refine hne (LinearMap.fixedSubmodule_eq_top_iff.mpr ?_)
    rw [hgfu, LinearEquiv.transvection.coe_toLinearMap, zero_smul,
      LinearMap.transvection.of_left_eq_zero]
  exact ⟨u, hu, r, hr, Subtype.ext hgfu⟩

end Field

end LinearMap.BilinForm.IsAlt
