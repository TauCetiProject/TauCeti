/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Isometry.Basic
public import TauCeti.LinearAlgebra.Matrix.SiegelTransvection
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
public import Mathlib.Algebra.Group.Subgroup.Pointwise
import TauCeti.LinearAlgebra.Matrix.SesquilinearForm

/-!
# Unitary transvection groups of isotropic points

Let `h(x, y) = (σ ∘ x) ⬝ᵥ (Q *ᵥ y)` be the `σ`-sesquilinear form of a Gram matrix `Q`
(`Matrix.specialIsometryGroup`), and `τ_{v,a} = 1 + a v (vᵀ ^ σ Q)` the unitary transvection
`Matrix.unitaryTransvection Q σ v a`. When `v` is isotropic, `h(v, v) = 0`, the matrix `τ_{v,a}`
has determinant one, and if `σ` is an involution and `Q` is `ε`-Hermitian, `(Q ^ σ)ᵀ = ε • Q`, it
lies in the special isometry group when `a + ε σ(a) = 0`. Over a field, for a nondegenerate `Q` and
`v ≠ 0`, only then. For a Hermitian form (`ε = 1`) the admissible parameters are the elements of
trace zero. An isometry `g` conjugates `τ_{v,a}` to `τ_{g v,a}`. More generally, the Siegel
transformation `S(u, w, c)` (`Matrix.siegelTransvection`) along an isotropic `u` with
`h(u, w) = 0` lies in the special isometry group when `c + ε σ(c) + ε h(w, w) = 0`, and
is conjugated by `g` to `S(g u, g w, c)`.

To an isotropic point `p` of projective space this attaches the group
`Matrix.unitaryTransvectionSubgroup Q σ p` of isometries that are unitary transvections along a
representative of `p`. It does not depend on the representative, it is abelian, and conjugation
by an isometry `g` carries it to the group of `g • p`. These are the commutativity and conjugacy
axioms of an Iwasawa structure (`MulAction.IwasawaStructure`) for the action of a special unitary
group on its isotropic points, the action from which the simplicity of the projective special
unitary groups is deduced.

The Iwasawa structure of the symplectic groups in
`TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Symplectic.Iwasawa`, built from the symplectic
transvections of `TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Symplectic.Transvection`, served
as the model for this file.

## Main definitions

* `Matrix.unitaryTransvectionSubgroup Q σ p`: the unitary transvections along an isotropic point.

## Main results

* `Matrix.exists_mem_specialIsometryGroup_coe_eq_unitaryTransvection` and
  `Matrix.exists_mem_specialIsometryGroup_coe_eq_siegelTransvection`: admissible unitary
  transvections `τ_{v,a}` and Siegel transformations `S(u, w, c)` lie in the special isometry
  group.
* `Matrix.exists_coe_eq_unitaryTransvection_iff` and
  `Matrix.exists_mem_specialIsometryGroup_coe_eq_siegelTransvection_iff`: for a nondegenerate
  `ε`-Hermitian `Q`, `τ_{v,a}` and `S(u, w, c)` are isometries exactly when their parameters
  satisfy `a + ε σ(a) = 0` and `c + ε σ(c) + ε h(w, w) = 0`.
* `Matrix.coe_mul_unitaryTransvection_mul_coe_inv` and
  `Matrix.coe_mul_siegelTransvection_mul_coe_inv`: an isometry `g` conjugates `τ_{v,a}` to
  `τ_{g v,a}` and `S(u, w, c)` to `S(g u, g w, c)`.
* `Matrix.coe_inv_specialIsometryGroup_eq_unitaryTransvection` and
  `Matrix.coe_inv_specialIsometryGroup_eq_siegelTransvection`: explicit matrices for the inverses
  of unitary transvections and Siegel transformations in `Q.specialIsometryGroup σ`.
* `Matrix.coe_commutatorElement_eq_unitaryTransvection_of_mulVec_eq_smul` and
  `Matrix.coe_commutatorElement_eq_unitaryTransvection_of_coe_eq_siegelTransvection`: explicit
  unitary transvection matrices for commutators in `Q.specialIsometryGroup σ` of an
  isotropic-vector rescaling with a transvection and of two Siegel transformations.
* `Matrix.unitaryTransvectionSubgroup_smul`: `T(g • p) = g T(p) g⁻¹`.

## References

* D. E. Taylor, *The Geometry of the Classical Groups* (1992), Chapters 10 and 11.
* L. C. Grove, *Classical Groups and Geometric Algebra* (2002), Chapter 11.
-/

public section

open scoped LinearAlgebra.Projectivization Pointwise commutatorElement

namespace Matrix

variable {n K : Type*} [Fintype n] [DecidableEq n]

section CommRing

variable [CommRing K] {Q : Matrix n n K} {σ : K →+* K}

/-- **An isometry conjugates `τ_{v,a}` to `τ_{g v,a}`.** -/
theorem coe_mul_unitaryTransvection_mul_coe_inv {g : SpecialLinearGroup n K}
    (hg : g ∈ Q.specialIsometryGroup σ) (v : n → K) (a : K) :
    (g : Matrix n n K) * Q.unitaryTransvection σ v a * ((g⁻¹ : SpecialLinearGroup n K) :
      Matrix n n K) = Q.unitaryTransvection σ ((g : Matrix n n K) *ᵥ v) a :=
  by rw [mul_unitaryTransvection (mem_specialIsometryGroup_iff.mp hg), Matrix.mul_assoc,
    ← SpecialLinearGroup.coe_mul, mul_inv_cancel, SpecialLinearGroup.coe_one, Matrix.mul_one]

/-- **Admissible unitary transvections are isometries.** If `σ` is an involution, `Q` is
`ε`-Hermitian, `v` is isotropic and `a + ε σ(a) = 0`, then `τ_{v,a}` is the matrix of an element of
the special isometry group of `Q`. -/
theorem exists_mem_specialIsometryGroup_coe_eq_unitaryTransvection (hσ : Function.Involutive σ)
    {ε : K} (hQ : (Q.map σ)ᵀ = ε • Q) {v : n → K} (hv : (σ ∘ v) ⬝ᵥ (Q *ᵥ v) = 0) {a : K}
    (ha : a + ε * σ a = 0) :
    ∃ g ∈ Q.specialIsometryGroup σ, (g : Matrix n n K) = Q.unitaryTransvection σ v a := by
  let t : SpecialLinearGroup n K := .mk _ (det_unitaryTransvection hv a)
  refine ⟨t, ?_, rfl⟩
  rw [mem_specialIsometryGroup_iff, SpecialLinearGroup.coe_mk]
  exact transpose_map_unitaryTransvection_mul_mul_self hσ hQ hv ha

/-- **An isometry conjugates `S(u, w, c)` to `S(g u, g w, c)`.** -/
theorem coe_mul_siegelTransvection_mul_coe_inv {g : SpecialLinearGroup n K}
    (hg : g ∈ Q.specialIsometryGroup σ) (ε : K) (u w : n → K) (c : K) :
    (g : Matrix n n K) * Q.siegelTransvection σ ε u w c *
      ((g⁻¹ : SpecialLinearGroup n K) : Matrix n n K) =
      Q.siegelTransvection σ ε ((g : Matrix n n K) *ᵥ u) ((g : Matrix n n K) *ᵥ w) c := by
  rw [mul_siegelTransvection (mem_specialIsometryGroup_iff.mp hg), Matrix.mul_assoc,
    ← SpecialLinearGroup.coe_mul, mul_inv_cancel, SpecialLinearGroup.coe_one, Matrix.mul_one]

/-- **Admissible Siegel transformations belong to the special isometry group.** -/
theorem exists_mem_specialIsometryGroup_coe_eq_siegelTransvection (hσ : Function.Involutive σ)
    {ε : K} (hQ : (Q.map σ)ᵀ = ε • Q) {u w : n → K} (hu : (σ ∘ u) ⬝ᵥ (Q *ᵥ u) = 0)
    (huw : (σ ∘ u) ⬝ᵥ (Q *ᵥ w) = 0) {c : K}
    (hc : c + ε * σ c + ε * ((σ ∘ w) ⬝ᵥ (Q *ᵥ w)) = 0) :
    ∃ g ∈ Q.specialIsometryGroup σ,
      (g : Matrix n n K) = Q.siegelTransvection σ ε u w c :=
  ⟨⟨_, det_siegelTransvection hu huw ((comp_dotProduct_mulVec_eq_zero_comm hσ hQ).mp huw) c⟩,
    mem_specialIsometryGroup_iff.mpr
      (transpose_map_siegelTransvection_mul_mul_self hσ hQ hu huw hc),
    rfl⟩

/-- The inverse in `Q.specialIsometryGroup σ` of a Siegel transformation `S(u, w, c)` with
`B(u, u) = B(u, w) = B(w, u) = 0` has matrix `S(u, -w, -c - ε B(w, w))`. -/
theorem coe_inv_specialIsometryGroup_eq_siegelTransvection {s : Q.specialIsometryGroup σ} {ε : K}
    {u w : n → K} (hu : (σ ∘ u) ⬝ᵥ (Q *ᵥ u) = 0) (huw : (σ ∘ u) ⬝ᵥ (Q *ᵥ w) = 0)
    (hwu : (σ ∘ w) ⬝ᵥ (Q *ᵥ u) = 0) {c : K}
    (hcs : ((s : SpecialLinearGroup n K) : Matrix n n K) = Q.siegelTransvection σ ε u w c) :
    (((s⁻¹ : Q.specialIsometryGroup σ) : SpecialLinearGroup n K) : Matrix n n K) =
      Q.siegelTransvection σ ε u (-w) (-c - ε * ((σ ∘ w) ⬝ᵥ (Q *ᵥ w))) :=
  coe_inv_specialIsometryGroup_eq_of_mul_eq_one <| by
    rw [hcs]
    exact siegelTransvection_mul_siegelTransvection_neg_eq_one hu huw hwu c

/-- The inverse in `Q.specialIsometryGroup σ` of a unitary transvection `τ_{v,a}` along an
isotropic vector `v` has matrix `τ_{v,-a}`. -/
theorem coe_inv_specialIsometryGroup_eq_unitaryTransvection {t : Q.specialIsometryGroup σ}
    {v : n → K} (hv : (σ ∘ v) ⬝ᵥ (Q *ᵥ v) = 0) {a : K}
    (hct : ((t : SpecialLinearGroup n K) : Matrix n n K) = Q.unitaryTransvection σ v a) :
    (((t⁻¹ : Q.specialIsometryGroup σ) : SpecialLinearGroup n K) : Matrix n n K) =
      Q.unitaryTransvection σ v (-a) :=
  coe_inv_specialIsometryGroup_eq_of_mul_eq_one <| by
    rw [hct, unitaryTransvection_mul_unitaryTransvection hv, add_neg_cancel,
      unitaryTransvection_zero]

/-- If `g : Q.specialIsometryGroup σ` scales an isotropic vector `v` by `c` and `t` has matrix
`τ_{v,a}`, then the commutator `⁅g, t⁆` has matrix `τ_{v, a (c σ(c) - 1)}`. -/
theorem coe_commutatorElement_eq_unitaryTransvection_of_mulVec_eq_smul
    {g t : Q.specialIsometryGroup σ} {v : n → K} {c a : K}
    (hv : (σ ∘ v) ⬝ᵥ (Q *ᵥ v) = 0)
    (hgv : ((g : SpecialLinearGroup n K) : Matrix n n K) *ᵥ v = c • v)
    (hct : ((t : SpecialLinearGroup n K) : Matrix n n K) = Q.unitaryTransvection σ v a) :
    (((⁅g, t⁆ : Q.specialIsometryGroup σ) : SpecialLinearGroup n K) : Matrix n n K) =
      Q.unitaryTransvection σ v (a * (c * σ c - 1)) := by
  rw [coe_commutatorElement_specialIsometryGroup,
    coe_inv_specialIsometryGroup_eq_unitaryTransvection hv hct, Subgroup.coe_inv, hct,
    coe_mul_unitaryTransvection_mul_coe_inv g.property, hgv, unitaryTransvection_smul,
    unitaryTransvection_mul_unitaryTransvection hv]
  congr 1
  ring

/-- The commutator in `Q.specialIsometryGroup σ` of two Siegel transformations `S(u, w₁, c₁)` and
`S(u, w₂, c₂)` along an isotropic `u` orthogonal on both sides to `w₁` and `w₂` has matrix
`τ_{u, ε (h(w₂, w₁) - h(w₁, w₂))}`. -/
theorem coe_commutatorElement_eq_unitaryTransvection_of_coe_eq_siegelTransvection
    {s₁ s₂ : Q.specialIsometryGroup σ} {ε c₁ c₂ : K} {u w₁ w₂ : n → K}
    (hu : (σ ∘ u) ⬝ᵥ (Q *ᵥ u) = 0)
    (huw₁ : (σ ∘ u) ⬝ᵥ (Q *ᵥ w₁) = 0) (hw₁u : (σ ∘ w₁) ⬝ᵥ (Q *ᵥ u) = 0)
    (huw₂ : (σ ∘ u) ⬝ᵥ (Q *ᵥ w₂) = 0) (hw₂u : (σ ∘ w₂) ⬝ᵥ (Q *ᵥ u) = 0)
    (hcs₁ : ((s₁ : SpecialLinearGroup n K) : Matrix n n K) =
      Q.siegelTransvection σ ε u w₁ c₁)
    (hcs₂ : ((s₂ : SpecialLinearGroup n K) : Matrix n n K) =
      Q.siegelTransvection σ ε u w₂ c₂) :
    (((⁅s₁, s₂⁆ : Q.specialIsometryGroup σ) : SpecialLinearGroup n K) : Matrix n n K) =
      Q.unitaryTransvection σ u
        (ε * ((σ ∘ w₂) ⬝ᵥ (Q *ᵥ w₁) - (σ ∘ w₁) ⬝ᵥ (Q *ᵥ w₂))) := by
  rw [coe_commutatorElement_specialIsometryGroup,
    coe_inv_specialIsometryGroup_eq_siegelTransvection hu huw₁ hw₁u hcs₁,
    coe_inv_specialIsometryGroup_eq_siegelTransvection hu huw₂ hw₂u hcs₂, hcs₁, hcs₂,
    siegelTransvection_mul_siegelTransvection_mul_neg_mul_neg_eq_unitaryTransvection hu huw₁ hw₁u
      huw₂ hw₂u]

end CommRing

section Field

variable [Field K] {Q : Matrix n n K} {σ : K →+* K}

variable (Q σ) in
/-- **The unitary transvection group of an isotropic point** `p`: the isometries that are unitary
transvections `τ_{v,a}` along a representative `v` of `p`. It does not depend on the
representative (`Matrix.mem_unitaryTransvectionSubgroup_mk_iff`), and is abelian. -/
def unitaryTransvectionSubgroup (p : Q.isotropicPoints σ) :
    Subgroup (Q.specialIsometryGroup σ) where
  carrier := {g | ∃ a : K, ((g : SpecialLinearGroup n K) : Matrix n n K) =
    Q.unitaryTransvection σ (p : ℙ K (n → K)).rep a}
  one_mem' := ⟨0, by simp⟩
  mul_mem' {g g'} := by
    rintro ⟨a, ha⟩ ⟨b, hb⟩
    refine ⟨a + b, ?_⟩
    rw [Subgroup.coe_mul, SpecialLinearGroup.coe_mul, ha, hb,
      unitaryTransvection_mul_unitaryTransvection (comp_rep_dotProduct_mulVec_rep p)]
  inv_mem' {g} := by
    rintro ⟨a, ha⟩
    exact ⟨-a,
      coe_inv_specialIsometryGroup_eq_unitaryTransvection (comp_rep_dotProduct_mulVec_rep p) ha⟩

/-- An isometry lies in the transvection group of `p` exactly when it is a unitary transvection
along the chosen representative of `p`. -/
theorem mem_unitaryTransvectionSubgroup_iff {p : Q.isotropicPoints σ}
    {g : Q.specialIsometryGroup σ} :
    g ∈ Q.unitaryTransvectionSubgroup σ p ↔
      ∃ a, ((g : SpecialLinearGroup n K) : Matrix n n K) =
        Q.unitaryTransvection σ (p : ℙ K (n → K)).rep a :=
  Iff.rfl

/-- **The transvection group does not depend on the representative**: an isometry lies in the
transvection group of the point `[v]` exactly when it is a unitary transvection along `v`. -/
@[simp]
theorem mem_unitaryTransvectionSubgroup_mk_iff {v : n → K} (hv : v ≠ 0)
    (hp : Projectivization.mk K v hv ∈ Q.isotropicPoints σ) {g : Q.specialIsometryGroup σ} :
    g ∈ Q.unitaryTransvectionSubgroup σ ⟨_, hp⟩ ↔
      ∃ a, ((g : SpecialLinearGroup n K) : Matrix n n K) = Q.unitaryTransvection σ v a := by
  obtain ⟨c, hc⟩ := Projectivization.exists_smul_eq_mk_rep K v hv
  rw [mem_unitaryTransvectionSubgroup_iff]
  dsimp only
  rw [← hc, Units.smul_def, exists_eq_unitaryTransvection_smul_iff c.ne_zero]

/-- **The transvection group of an isotropic point is abelian.** -/
instance (p : Q.isotropicPoints σ) : IsMulCommutative (Q.unitaryTransvectionSubgroup σ p) :=
  ⟨⟨fun x y ↦ by
    obtain ⟨a, ha⟩ := x.property
    obtain ⟨b, hb⟩ := y.property
    have hv := comp_rep_dotProduct_mulVec_rep p
    have h : ((((x * y : Q.unitaryTransvectionSubgroup σ p) : Q.specialIsometryGroup σ) :
        SpecialLinearGroup n K) : Matrix n n K) =
        ((((y * x : Q.unitaryTransvectionSubgroup σ p) : Q.specialIsometryGroup σ) :
          SpecialLinearGroup n K) : Matrix n n K) := by
      rw [Subgroup.coe_mul, Subgroup.coe_mul, SpecialLinearGroup.coe_mul, Subgroup.coe_mul,
        Subgroup.coe_mul, SpecialLinearGroup.coe_mul, ha, hb,
        unitaryTransvection_mul_unitaryTransvection hv,
        unitaryTransvection_mul_unitaryTransvection hv, add_comm]
    exact Subtype.ext (specialIsometryGroup_ext h)⟩⟩

/-- **Conjugation moves transvection groups along the action**: `T(g • p) = g T(p) g⁻¹`. -/
theorem unitaryTransvectionSubgroup_smul (g : Q.specialIsometryGroup σ)
    (p : Q.isotropicPoints σ) :
    Q.unitaryTransvectionSubgroup σ (g • p) =
      MulAut.conj g • Q.unitaryTransvectionSubgroup σ p := by
  -- Both groups consist of the unitary transvections along `g v`, for a representative `v`.
  set v := (p : ℙ K (n → K)).rep
  have hgv : (g : SpecialLinearGroup n K) • v ≠ 0 :=
    (smul_ne_zero_iff_ne (g : SpecialLinearGroup n K)).mpr (p : ℙ K (n → K)).rep_ne_zero
  have hgp : ((g • p : Q.isotropicPoints σ) : ℙ K (n → K)) =
      Projectivization.mk K ((g : SpecialLinearGroup n K) • v) hgv := by
    rw [SubMulAction.val_smul, Subgroup.smul_def,
      ← Projectivization.smul_mk _ (p : ℙ K (n → K)).rep_ne_zero, Projectivization.mk_rep]
  have hconj : ∀ h : Q.specialIsometryGroup σ, ∀ (u : n → K) (a : K),
      ((h : SpecialLinearGroup n K) : Matrix n n K) * Q.unitaryTransvection σ u a *
        ((h⁻¹ : Q.specialIsometryGroup σ) : SpecialLinearGroup n K) =
        Q.unitaryTransvection σ (((h : SpecialLinearGroup n K) : Matrix n n K) *ᵥ u) a :=
    fun h u a ↦ by
      rw [Subgroup.coe_inv]
      exact coe_mul_unitaryTransvection_mul_coe_inv h.property u a
  ext x
  rw [Subgroup.mem_smul_pointwise_iff_exists]
  have hmem : x ∈ Q.unitaryTransvectionSubgroup σ (g • p) ↔
      ∃ a, ((x : SpecialLinearGroup n K) : Matrix n n K) =
        Q.unitaryTransvection σ (((g : SpecialLinearGroup n K) : Matrix n n K) *ᵥ v) a := by
    obtain ⟨c, hc⟩ := Projectivization.exists_smul_eq_mk_rep K _ hgv
    rw [mem_unitaryTransvectionSubgroup_iff, hgp, ← hc, Units.smul_def,
      exists_eq_unitaryTransvection_smul_iff c.ne_zero, SpecialLinearGroup.smul_def,
      smul_eq_mulVec]
  rw [hmem]
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨g⁻¹ * x * g, ⟨a, ?_⟩, by simp [MulAut.smul_def, mul_assoc]⟩
    have h := hconj g⁻¹ (((g : SpecialLinearGroup n K) : Matrix n n K) *ᵥ v) a
    rw [inv_inv, ← ha] at h
    rw [Subgroup.coe_mul, Subgroup.coe_mul, SpecialLinearGroup.coe_mul,
      SpecialLinearGroup.coe_mul, h, mulVec_mulVec, ← SpecialLinearGroup.coe_mul,
      ← Subgroup.coe_mul, inv_mul_cancel, Subgroup.coe_one, SpecialLinearGroup.coe_one,
      one_mulVec]
  · rintro ⟨y, ⟨a, ha⟩, rfl⟩
    refine ⟨a, ?_⟩
    rw [MulAut.smul_def, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul,
      SpecialLinearGroup.coe_mul, SpecialLinearGroup.coe_mul, ha, hconj]

variable {ε : K}

/-- **Every admissible parameter gives an isometry.** If `σ` is an involution and `Q` is
`ε`-Hermitian, then for every `a` with `a + ε σ(a) = 0` the transvection `τ_{v,a}` along the
representative `v` of an isotropic point lies in its transvection group. -/
theorem exists_coe_eq_unitaryTransvection (hσ : Function.Involutive σ) (hQ : (Q.map σ)ᵀ = ε • Q)
    (p : Q.isotropicPoints σ) {a : K} (ha : a + ε * σ a = 0) :
    ∃ g : Q.unitaryTransvectionSubgroup σ p,
      (((g : Q.specialIsometryGroup σ) : SpecialLinearGroup n K) : Matrix n n K) =
        Q.unitaryTransvection σ (p : ℙ K (n → K)).rep a := by
  obtain ⟨g, hg, hga⟩ := exists_mem_specialIsometryGroup_coe_eq_unitaryTransvection hσ hQ
    (comp_rep_dotProduct_mulVec_rep p) ha
  exact ⟨⟨⟨g, hg⟩, a, hga⟩, hga⟩

/-- **The parameters of the transvection group of an isotropic point.** If `σ` is an involution
and `Q` is a nondegenerate `ε`-Hermitian matrix, the transvection `τ_{v,a}` along the
representative `v` of an isotropic point is an isometry exactly when `a + ε σ(a) = 0`. For a
Hermitian form these are the elements of trace zero. -/
theorem exists_coe_eq_unitaryTransvection_iff (hσ : Function.Involutive σ)
    (hQ : (Q.map σ)ᵀ = ε • Q) (hdet : Q.det ≠ 0) (p : Q.isotropicPoints σ) (a : K) :
    (∃ g : Q.unitaryTransvectionSubgroup σ p,
      (((g : Q.specialIsometryGroup σ) : SpecialLinearGroup n K) : Matrix n n K) =
        Q.unitaryTransvection σ (p : ℙ K (n → K)).rep a) ↔ a + ε * σ a = 0 := by
  refine ⟨fun ⟨g, hg⟩ ↦ ?_, exists_coe_eq_unitaryTransvection hσ hQ p⟩
  have h := mem_specialIsometryGroup_iff.mp (g : Q.specialIsometryGroup σ).property
  rw [hg, transpose_map_unitaryTransvection_mul_mul hσ hQ, comp_rep_dotProduct_mulVec_rep p,
    mul_zero, add_zero, add_eq_left, smul_eq_zero] at h
  exact h.resolve_right
    (vecMulVec_mulVec_comp_vecMul_ne_zero hσ.injective hdet (p : ℙ K (n → K)).rep_ne_zero)

/-- **The parameters of Siegel transformations in the special isometry group.** If `σ` is an
involution and `Q` is a nondegenerate `ε`-Hermitian matrix, the Siegel transformation `S(u, w, c)`
along a nonzero isotropic vector `u` with `h(u, w) = 0` belongs to `Q.specialIsometryGroup σ` if
and only if `c + ε * σ c + ε * h(w, w) = 0`. -/
theorem exists_mem_specialIsometryGroup_coe_eq_siegelTransvection_iff
    (hσ : Function.Involutive σ) (hQ : (Q.map σ)ᵀ = ε • Q) (hdet : Q.det ≠ 0)
    {u w : n → K} (hu0 : u ≠ 0) (hu : (σ ∘ u) ⬝ᵥ (Q *ᵥ u) = 0)
    (huw : (σ ∘ u) ⬝ᵥ (Q *ᵥ w) = 0) (c : K) :
    (∃ g ∈ Q.specialIsometryGroup σ,
      (g : Matrix n n K) = Q.siegelTransvection σ ε u w c) ↔
      c + ε * σ c + ε * ((σ ∘ w) ⬝ᵥ (Q *ᵥ w)) = 0 := by
  refine ⟨fun ⟨g, hg, hcg⟩ ↦ ?_,
    exists_mem_specialIsometryGroup_coe_eq_siegelTransvection hσ hQ hu huw⟩
  have h := mem_specialIsometryGroup_iff.mp hg
  rw [hcg, transpose_map_siegelTransvection_mul_mul hσ hQ hu huw, add_eq_left, smul_eq_zero] at h
  exact h.resolve_right (vecMulVec_mulVec_comp_vecMul_ne_zero hσ.injective hdet hu0)

end Field

end Matrix
