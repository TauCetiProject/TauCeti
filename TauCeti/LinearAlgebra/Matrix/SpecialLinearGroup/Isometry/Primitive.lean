/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.GroupAction.Primitive
public import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Isometry.IsotropicPoints
import Mathlib.Tactic.LinearCombination
import TauCeti.Algebra.Group.Hom.Defs
import TauCeti.Algebra.Group.Submonoid.Defs
import TauCeti.Algebra.Ring.Hom
import TauCeti.LinearAlgebra.Matrix.MulVec
import TauCeti.LinearAlgebra.Matrix.Nondegenerate
import TauCeti.LinearAlgebra.Matrix.SesquilinearForm
import TauCeti.LinearAlgebra.Projectivization.Action
import TauCeti.LinearAlgebra.Projectivization.Basic

/-!
# Primitivity of a special unitary group on its isotropic points

Let `σ` be an involution of a field `K`, let `Q` be an invertible `ε`-Hermitian matrix,
`(Q ^ σ)ᵀ = ε • Q`, and write `B(x, y) = (σ ∘ x) ⬝ᵥ (Q *ᵥ y)` for its sesquilinear form. The
special isometry group `Matrix.specialIsometryGroup Q σ` acts on the isotropic points
`Matrix.isotropicPoints Q σ` of projective space; under the two trace hypotheses of
`Matrix.isPretransitive_isotropicPoints` (`t ↦ t + ε σ(t)` is onto `{s | σ(s) = ε s}` and has a
nonzero kernel element), this action is transitive and has central kernel when nonempty. This file
proves that it is **primitive** (`Matrix.isPreprimitive_isotropicPoints`). Through
`MulAction.IsPreprimitive.isQuasiPreprimitive`, this supplies the quasiprimitivity input of
Iwasawa's simplicity criterion `MulAction.IwasawaStructure.isSimpleGroup` for the projective
special unitary groups.

The stabilizer in `SU(Q)` of an isotropic point `[u]` preserves orthogonality to `[u]`, so on the
remaining isotropic points it has at most two orbits: those `[x] ≠ [u]` with `B(u, x) = 0` and
those with `B(u, x) ≠ 0`. Unlike in the symplectic case, unitary transvections alone do not exhaust
the second orbit: in Witt index one (for instance `SU_3(q)`), `u^⊥ / K ∙ u` is anisotropic, so the
only unitary transvections fixing `u` are those along `u`, which cannot act transitively on the
isotropic points outside `u^⊥`. Instead, the two stabilizer orbits come from two families of
special isometries:

* **Non-orthogonal orbit (`B(u, x) ≠ 0` and `B(u, y) ≠ 0`).** After normalizing `u` to `u'` with
  `B(u', x) = 1` and rescaling `y` so that `B(u', y) = 1`, the Siegel transformation
  `Matrix.siegelTransvection Q σ ε u' (y - x - c' • u') c'` with `c' = ε B(x, y)` lies in
  `Q.specialIsometryGroup σ`, fixes `u`, and sends `x` to `y`; rescaling `u'` back to `u` via
  `Matrix.siegelTransvection_smul_left` exhibits it as an admissible Siegel transformation along `u`
  (`Matrix.exists_mem_specialIsometryGroup_coe_eq_siegelTransvection_mulVec_eq_self_and_mulVec_eq`)
  without using either trace hypothesis or nondegeneracy of `Q`.
* **Orthogonal orbit (`B(u, x) = 0` and `B(u, y) = 0`, off `K ∙ u`).** When `B(y, x) ≠ 0`, a
  unitary transvection along `c • y - x` fixes `u` (since `c • y - x ∈ u^⊥`) and sends `x` to
  `c • y`; when `B(y, x) = 0`, two such steps pass through an isotropic vector `v + a • x ∈ u^⊥`
  paired nontrivially with both `x` and `y`
  (`Matrix.exists_mem_specialIsometryGroup_mulVec_eq_self_and_mulVec_eq_smul_of_eq_zero` in
  `TauCeti/LinearAlgebra/Matrix/SpecialLinearGroup/Isometry/IsotropicPoints.lean`).

Together these give `Matrix.exists_mem_specialIsometryGroup_mulVec_eq_self_and_mulVec_eq_smul`: the
stabilizer of `u` connects `[x]` to `[y]` whenever both lie off `K ∙ u` and `B(u, x) = 0` holds
for both or for neither. Any block containing two distinct isotropic points `[u] ≠ [x]` is
therefore invariant under the stabilizer of each of its points, meets both orbits when both are
nonempty (via an isotropic vector `v + c • u ∈ x^⊥ \ u^⊥` if `B(u, x) = 0`, or `[y]` / `[y + u]` if
`B(u, x) ≠ 0`), and so equals the whole space of isotropic points. No rank or Witt-index hypothesis
is needed.

The block-closure argument is modeled on the symplectic case in
`TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Symplectic.Primitive`.

## Main results

* `Matrix.exists_mem_specialIsometryGroup_coe_eq_siegelTransvection_mulVec_eq_self_and_mulVec_eq`:
  an admissible Siegel transformation along an isotropic `u` in `Q.specialIsometryGroup σ` fixes `u`
  and sends an isotropic `x` to an isotropic `y` whenever `B(u, x) = B(u, y) ≠ 0`.
* `Matrix.exists_mem_specialIsometryGroup_mulVec_eq_self_and_mulVec_eq_smul`: the stabilizer of an
  isotropic `u` sends an isotropic `x ∉ K ∙ u` to a nonzero multiple of an isotropic `y ∉ K ∙ u`
  whenever `B(u, x) = 0 ↔ B(u, y) = 0`.
* `Matrix.isPreprimitive_isotropicPoints`: `Q.specialIsometryGroup σ` acts primitively on
  `Q.isotropicPoints σ`.

## References

* D. E. Taylor, *The Geometry of the Classical Groups* (1992), Chapters 10 and 11.
* L. C. Grove, *Classical Groups and Geometric Algebra* (2002), Chapter 11.
* M. Eichler, *Quadratische Formen und orthogonale Gruppen*, Springer (1952).
-/

public section

open MulAction
open scoped LinearAlgebra.Projectivization Pointwise

namespace Matrix

variable {n K : Type*} [Fintype n] [DecidableEq n] [Field K] {Q : Matrix n n K} {σ : K →+* K}
  {ε : K}

/-! ### Stabilizer orbits on isotropic vectors -/

/-- **An admissible Siegel transformation joins two isotropic vectors at a given nonzero pairing
with `u`.** Let `σ` be an involution and let `Q` be an `ε`-Hermitian matrix with `ε * ε = 1`. If
`u`, `x`, `y` are isotropic and `B(u, x) = B(u, y) ≠ 0`, then for some `w` orthogonal to `u` and
some `c` with `c + ε σ(c) + ε B(w, w) = 0`, the Siegel transformation `S(u, w, c)` lies in
`Q.specialIsometryGroup σ`, fixes `u`, and sends `x` to `y`. -/
theorem exists_mem_specialIsometryGroup_coe_eq_siegelTransvection_mulVec_eq_self_and_mulVec_eq
    (hσ : Function.Involutive σ) (hQ : (Q.map σ)ᵀ = ε • Q) (hε : ε * ε = 1)
    {u x y : n → K} (hu : (σ ∘ u) ⬝ᵥ (Q *ᵥ u) = 0)
    (hx : (σ ∘ x) ⬝ᵥ (Q *ᵥ x) = 0) (hy : (σ ∘ y) ⬝ᵥ (Q *ᵥ y) = 0)
    (hux : (σ ∘ u) ⬝ᵥ (Q *ᵥ x) ≠ 0)
    (hxy : (σ ∘ u) ⬝ᵥ (Q *ᵥ x) = (σ ∘ u) ⬝ᵥ (Q *ᵥ y)) :
    ∃ g ∈ Q.specialIsometryGroup σ, ∃ (w : n → K) (c : K),
      (σ ∘ u) ⬝ᵥ (Q *ᵥ w) = 0 ∧
        c + ε * σ c + ε * ((σ ∘ w) ⬝ᵥ (Q *ᵥ w)) = 0 ∧
        (g : Matrix n n K) = Q.siegelTransvection σ ε u w c ∧
        (g : Matrix n n K) *ᵥ u = u ∧ (g : Matrix n n K) *ᵥ x = y := by
  have hσε : σ ε = ε := TauCeti.map_eq_self_of_mul_self_eq_one σ hε
  -- Normalize `u` to `u' = σ(b)⁻¹ • u` so that `B(u', x) = B(u', y) = 1`.
  set b := (σ ∘ u) ⬝ᵥ (Q *ᵥ x)
  set u' := (σ b)⁻¹ • u
  set c' := ε * ((σ ∘ x) ⬝ᵥ (Q *ᵥ y))
  set w' := y - x - c' • u'
  have hu'pair (v : n → K) : (σ ∘ u') ⬝ᵥ (Q *ᵥ v) = b⁻¹ * ((σ ∘ u) ⬝ᵥ (Q *ᵥ v)) := by
    rw [TauCeti.map_comp_smul, smul_dotProduct, smul_eq_mul, map_inv₀, hσ]
  have hu' : (σ ∘ u') ⬝ᵥ (Q *ᵥ u') = 0 := by rw [comp_smul_dotProduct_mulVec_smul, hu, mul_zero]
  have hu'x : (σ ∘ u') ⬝ᵥ (Q *ᵥ x) = 1 := by rw [hu'pair, inv_mul_cancel₀ hux]
  have hu'y : (σ ∘ u') ⬝ᵥ (Q *ᵥ y) = 1 := by rw [hu'pair, ← hxy, inv_mul_cancel₀ hux]
  have hu'w' : (σ ∘ u') ⬝ᵥ (Q *ᵥ w') = 0 := by
    simp [w', mulVec_sub, mulVec_smul, hu'y, hu'x, hu']
  have hwu' : (σ ∘ w') ⬝ᵥ (Q *ᵥ u') = 0 :=
    (comp_dotProduct_mulVec_eq_zero_comm hσ hQ).mp hu'w'
  have hxu' : (σ ∘ x) ⬝ᵥ (Q *ᵥ u') = ε := by
    rw [comp_dotProduct_mulVec_swap hσ hQ hε, hu'x, map_one, mul_one]
  have hxw' : (σ ∘ x) ⬝ᵥ (Q *ᵥ w') = 0 := by
    simp only [w', mulVec_sub, mulVec_smul, dotProduct_sub, dotProduct_smul, smul_eq_mul, hx, hxu']
    linear_combination -((σ ∘ x) ⬝ᵥ (Q *ᵥ y)) * hε
  have hwx : (σ ∘ w') ⬝ᵥ (Q *ᵥ x) = 0 :=
    (comp_dotProduct_mulVec_eq_zero_comm hσ hQ).mp hxw'
  -- Isotropy of `y = (x + w') + c' • u'` gives `c' + ε σ(c') + ε B(w', w') = 0`.
  have hc' : c' + ε * σ c' + ε * ((σ ∘ w') ⬝ᵥ (Q *ᵥ w')) = 0 := by
    have hy_eq : (x + w') + c' • u' = y := by dsimp [w']; abel
    have hxwu' : (σ ∘ (x + w')) ⬝ᵥ (Q *ᵥ u') = ε := by
      simp [hxu', hwu']
    have hxw_self : (σ ∘ (x + w')) ⬝ᵥ (Q *ᵥ (x + w')) = (σ ∘ w') ⬝ᵥ (Q *ᵥ w') := by
      simp [mulVec_add, hx, hxw', hwx]
    have h0 := comp_add_smul_dotProduct_mulVec_add_smul hσ hQ hε hu' (x + w') c'
    rw [hy_eq, hy, hxw_self, hxwu', map_mul, hσε, mul_left_comm ε (σ c') ε, hε, mul_one] at h0
    linear_combination -ε * h0 - c' * hε
  obtain ⟨g, hg, hS⟩ :=
    exists_mem_specialIsometryGroup_coe_eq_siegelTransvection hσ hQ hu' hu'w' hc'
  have hσb : σ b ≠ 0 := (map_ne_zero σ).mpr hux
  have hu_eq : σ b • u' = u := smul_inv_smul₀ hσb u
  -- Rescale `u'` back to `u` via `siegelTransvection_smul_left`.
  refine ⟨g, hg, b⁻¹ • w', c' * (σ b)⁻¹ * b⁻¹, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hu_eq, TauCeti.map_comp_smul, mulVec_smul, smul_dotProduct, dotProduct_smul, hu'w',
      smul_zero, smul_zero]
  · rw [comp_smul_dotProduct_mulVec_smul, map_mul, map_mul, map_inv₀, map_inv₀, hσ]
    linear_combination ((σ b)⁻¹ * b⁻¹) * hc'
  · rw [hS, siegelTransvection_smul_left hσ, map_inv₀, hσ]
  · rw [← hu_eq, mulVec_smul, hS, siegelTransvection_mulVec_self hu' hwu']
  · simp only [w', hS, siegelTransvection_mulVec, hu'x, hwx, one_smul, mul_zero, zero_smul,
      sub_zero]
    abel

/-- **The stabilizer of an isotropic vector `u` is projectively transitive on both orthogonality
classes off `K ∙ u`.** Let `σ` be an involution, let `Q` be an invertible `ε`-Hermitian matrix, and
suppose that the trace `t ↦ t + ε σ(t)` is onto the elements `s` with `σ(s) = ε s` and has a
nonzero kernel element. If `u`, `x`, `y` are isotropic vectors with `x ∉ K ∙ u`, `y ∉ K ∙ u`, and
`B(u, x) = 0 ↔ B(u, y) = 0`, then some element of `Q.specialIsometryGroup σ` fixes `u` and sends
`x` to a nonzero scalar multiple of `y`. -/
theorem exists_mem_specialIsometryGroup_mulVec_eq_self_and_mulVec_eq_smul
    (hσ : Function.Involutive σ) (hQ : (Q.map σ)ᵀ = ε • Q) (hdet : Q.det ≠ 0)
    (htr : ∀ s, σ s = ε * s → ∃ t, t + ε * σ t = s) (hadm : ∃ d ≠ 0, d + ε * σ d = 0)
    {u x y : n → K} (hu : (σ ∘ u) ⬝ᵥ (Q *ᵥ u) = 0)
    (hx : (σ ∘ x) ⬝ᵥ (Q *ᵥ x) = 0) (hy : (σ ∘ y) ⬝ᵥ (Q *ᵥ y) = 0)
    (hx_span : x ∉ K ∙ u) (hy_span : y ∉ K ∙ u)
    (h : (σ ∘ u) ⬝ᵥ (Q *ᵥ x) = 0 ↔ (σ ∘ u) ⬝ᵥ (Q *ᵥ y) = 0) :
    ∃ g ∈ Q.specialIsometryGroup σ, ∃ c ≠ (0 : K),
      (g : Matrix n n K) *ᵥ u = u ∧ (g : Matrix n n K) *ᵥ x = c • y := by
  by_cases hux : (σ ∘ u) ⬝ᵥ (Q *ᵥ x) = 0
  · exact exists_mem_specialIsometryGroup_mulVec_eq_self_and_mulVec_eq_smul_of_eq_zero
      hσ hQ hdet htr hadm hx hy hx_span hy_span hux (h.mp hux)
  · have huy : (σ ∘ u) ⬝ᵥ (Q *ᵥ y) ≠ 0 := mt h.mpr hux
    have hε : ε * ε = 1 := by
      refine mul_self_eq_one_of_trace hσ hQ htr ?_
      rintro rfl
      simp at hux
    set c := ((σ ∘ u) ⬝ᵥ (Q *ᵥ x)) / ((σ ∘ u) ⬝ᵥ (Q *ᵥ y))
    have hc : c ≠ 0 := div_ne_zero hux huy
    have hcy : (σ ∘ (c • y)) ⬝ᵥ (Q *ᵥ (c • y)) = 0 := by
      rw [comp_smul_dotProduct_mulVec_smul, hy, mul_zero]
    have hucy : (σ ∘ u) ⬝ᵥ (Q *ᵥ x) = (σ ∘ u) ⬝ᵥ (Q *ᵥ (c • y)) := by
      rw [mulVec_smul, dotProduct_smul, smul_eq_mul, div_mul_cancel₀ _ huy]
    obtain ⟨g, hg, -, -, -, -, -, hgu, hgx⟩ :=
      exists_mem_specialIsometryGroup_coe_eq_siegelTransvection_mulVec_eq_self_and_mulVec_eq
        hσ hQ hε hu hx hcy hux hucy
    exact ⟨g, hg, c, hc, hgu, hgx⟩

/-! ### Block closure and primitivity -/

/-- Package a nonzero isotropic vector as an element of `Q.isotropicPoints σ`. -/
private def isotropicPointMk {v : n → K} (hv₀ : v ≠ 0) (hv : (σ ∘ v) ⬝ᵥ (Q *ᵥ v) = 0) :
    Q.isotropicPoints σ :=
  ⟨Projectivization.mk K v hv₀, (mk_mem_isotropicPoints_iff hv₀).mpr hv⟩

/-- **A block contains each stabilizer orbit that it meets.** -/
private theorem isotropicPointMk_mem_of_isBlock (hσ : Function.Involutive σ)
    (hQ : (Q.map σ)ᵀ = ε • Q) (hdet : Q.det ≠ 0)
    (htr : ∀ s, σ s = ε * s → ∃ t, t + ε * σ t = s) (hadm : ∃ d ≠ 0, d + ε * σ d = 0)
    {B : Set (Q.isotropicPoints σ)} (hB : IsBlock (Q.specialIsometryGroup σ) B)
    {u x y : n → K} (hu₀ : u ≠ 0) (hu : (σ ∘ u) ⬝ᵥ (Q *ᵥ u) = 0)
    (hx : (σ ∘ x) ⬝ᵥ (Q *ᵥ x) = 0) (hy : (σ ∘ y) ⬝ᵥ (Q *ᵥ y) = 0)
    (hx_span : x ∉ K ∙ u) (hy_span : y ∉ K ∙ u)
    (huB : isotropicPointMk hu₀ hu ∈ B)
    (hxB : isotropicPointMk (TauCeti.ne_zero_of_notMem hx_span) hx ∈ B)
    (h : (σ ∘ u) ⬝ᵥ (Q *ᵥ x) = 0 ↔ (σ ∘ u) ⬝ᵥ (Q *ᵥ y) = 0) :
    isotropicPointMk (TauCeti.ne_zero_of_notMem hy_span) hy ∈ B := by
  obtain ⟨g, hg, c, -, hgu, hgx⟩ :=
    exists_mem_specialIsometryGroup_mulVec_eq_self_and_mulVec_eq_smul
      hσ hQ hdet htr hadm hu hx hy hx_span hy_span h
  let g' : Q.specialIsometryGroup σ := ⟨g, hg⟩
  have hgu_pt : g' • isotropicPointMk hu₀ hu = isotropicPointMk hu₀ hu :=
    Subtype.ext <| TauCeti.Projectivization.smul_mk_eq_mk_of_smul_eq_smul hu₀ hu₀ (c := 1)
      (by simpa [Subgroup.smul_def, SpecialLinearGroup.smul_def, smul_eq_mulVec] using hgu)
  have hgy_pt :
      isotropicPointMk (TauCeti.ne_zero_of_notMem hy_span) hy =
        g' • isotropicPointMk (TauCeti.ne_zero_of_notMem hx_span) hx :=
    Subtype.ext <| (TauCeti.Projectivization.smul_mk_eq_mk_of_smul_eq_smul _ _
      (by rwa [Subgroup.smul_def, SpecialLinearGroup.smul_def, smul_eq_mulVec])).symm
  have hgB : g' • B = B := hB.smul_eq_of_mem huB (by rwa [hgu_pt])
  rw [hgy_pt, ← hgB]
  exact Set.smul_mem_smul_set hxB

/-- **Non-orthogonal block closure.** If a block `B` contains two isotropic points `[u]` and `[x]`
with `B(u, x) ≠ 0`, then `B` contains every isotropic point `[y]` off `K ∙ u`. -/
private theorem isotropicPointMk_mem_of_isBlock_of_ne_zero (hσ : Function.Involutive σ)
    (hQ : (Q.map σ)ᵀ = ε • Q) (hε : ε * ε = 1) (hdet : Q.det ≠ 0)
    (htr : ∀ s, σ s = ε * s → ∃ t, t + ε * σ t = s) (hadm : ∃ d ≠ 0, d + ε * σ d = 0)
    {B : Set (Q.isotropicPoints σ)} (hB : IsBlock (Q.specialIsometryGroup σ) B)
    {u x y : n → K} (hu₀ : u ≠ 0) (hu : (σ ∘ u) ⬝ᵥ (Q *ᵥ u) = 0)
    (hx : (σ ∘ x) ⬝ᵥ (Q *ᵥ x) = 0) (hy : (σ ∘ y) ⬝ᵥ (Q *ᵥ y) = 0)
    (hu_span : u ∉ K ∙ x) (hx_span : x ∉ K ∙ u) (hy_span : y ∉ K ∙ u)
    (huB : isotropicPointMk hu₀ hu ∈ B)
    (hxB : isotropicPointMk (TauCeti.ne_zero_of_notMem hx_span) hx ∈ B)
    (hux : (σ ∘ u) ⬝ᵥ (Q *ᵥ x) ≠ 0) :
    isotropicPointMk (TauCeti.ne_zero_of_notMem hy_span) hy ∈ B := by
  by_cases huy : (σ ∘ u) ⬝ᵥ (Q *ᵥ y) = 0
  swap
  · exact isotropicPointMk_mem_of_isBlock hσ hQ hdet htr hadm hB hu₀ hu hx hy hx_span hy_span
      huB hxB (iff_of_false hux huy)
  have hxu : (σ ∘ x) ⬝ᵥ (Q *ᵥ u) ≠ 0 :=
    (comp_dotProduct_mulVec_ne_zero_comm hσ hQ).mp hux
  have hx₀ := TauCeti.ne_zero_of_notMem hx_span
  by_cases hxy : (σ ∘ x) ⬝ᵥ (Q *ᵥ y) = 0
  swap
  · exact isotropicPointMk_mem_of_isBlock hσ hQ hdet htr hadm hB hx₀ hx hu hy hu_span
      (notMem_span_of_dotProduct_mulVec_of_ne_zero huy hux (TauCeti.ne_zero_of_notMem hy_span))
      hxB huB (iff_of_false hxu hxy)
  -- Both `u` and `x` are orthogonal to `y`, so `[y + u]` is isotropic, orthogonal to `u`, and
  -- paired nontrivially with `x`.
  have hyu : (σ ∘ y) ⬝ᵥ (Q *ᵥ u) = 0 :=
    (comp_dotProduct_mulVec_eq_zero_comm hσ hQ).mp huy
  have hs : (σ ∘ (y + u)) ⬝ᵥ (Q *ᵥ (y + u)) = 0 := by
    simpa [hy, hyu] using comp_add_smul_dotProduct_mulVec_add_smul hσ hQ hε hu y 1
  have hsu : (σ ∘ u) ⬝ᵥ (Q *ᵥ (y + u)) = 0 := by
    simp [mulVec_add, huy, hu]
  have hs_span : y + u ∉ K ∙ u :=
    mt ((K ∙ u).add_mem_iff_left (Submodule.mem_span_singleton_self u)).mp hy_span
  have hxs : (σ ∘ x) ⬝ᵥ (Q *ᵥ (y + u)) ≠ 0 := by
    simpa [mulVec_add, hxy] using hxu
  have hsB := isotropicPointMk_mem_of_isBlock hσ hQ hdet htr hadm hB hx₀ hx hu hs hu_span
    (notMem_span_of_dotProduct_mulVec_of_ne_zero hsu hux (TauCeti.ne_zero_of_notMem hs_span))
    hxB huB (iff_of_false hxu hxs)
  exact isotropicPointMk_mem_of_isBlock hσ hQ hdet htr hadm hB hu₀ hu hs hy hs_span hy_span
    huB hsB (iff_of_true hsu huy)

/-- **The special unitary group acts primitively on its isotropic points.** Let `σ` be an
involution, let `Q` be an invertible `ε`-Hermitian matrix, and suppose that the trace
`t ↦ t + ε σ(t)` is onto the elements `s` with `σ(s) = ε s` and has a nonzero kernel element.
Then `Matrix.specialIsometryGroup Q σ` acts primitively on `Matrix.isotropicPoints Q σ`. -/
theorem isPreprimitive_isotropicPoints (hσ : Function.Involutive σ)
    (hQ : (Q.map σ)ᵀ = ε • Q) (hdet : Q.det ≠ 0)
    (htr : ∀ s, σ s = ε * s → ∃ t, t + ε * σ t = s) (hadm : ∃ d ≠ 0, d + ε * σ d = 0) :
    IsPreprimitive (Q.specialIsometryGroup σ) (Q.isotropicPoints σ) := by
  rcases subsingleton_or_nontrivial (Q.isotropicPoints σ) with _ | ⟨p₀, -, -⟩
  · exact IsPreprimitive.of_subsingleton
  have : Nonempty n := let ⟨i, _⟩ := Function.ne_iff.mp (p₀ : ℙ K (n → K)).rep_ne_zero; ⟨i⟩
  have hε := mul_self_eq_one_of_trace_of_det_ne_zero hσ hQ hdet htr
  have := isPretransitive_isotropicPoints hσ hQ hdet htr hadm
  refine { isTrivialBlock_of_isBlock := fun {B} hB ↦ ?_ }
  rcases B.subsingleton_or_nontrivial with hB₁ | ⟨p, hpB, q, hqB, hpq⟩
  · exact Or.inl hB₁
  refine Or.inr (Set.eq_univ_of_forall fun r ↦ ?_)
  obtain ⟨p, hp⟩ := p
  obtain ⟨q, hq⟩ := q
  obtain ⟨r, hr⟩ := r
  induction p using Projectivization.ind with | h u hu₀ => ?_
  induction q using Projectivization.ind with | h x hx₀ => ?_
  induction r using Projectivization.ind with | h y hy₀ => ?_
  have hu : (σ ∘ u) ⬝ᵥ (Q *ᵥ u) = 0 := (mk_mem_isotropicPoints_iff hu₀).mp hp
  have hx : (σ ∘ x) ⬝ᵥ (Q *ᵥ x) = 0 := (mk_mem_isotropicPoints_iff hx₀).mp hq
  have hy : (σ ∘ y) ⬝ᵥ (Q *ᵥ y) = 0 := (mk_mem_isotropicPoints_iff hy₀).mp hr
  have hpq' : Projectivization.mk K u hu₀ ≠ Projectivization.mk K x hx₀ :=
    Subtype.ext_iff.not.mp hpq
  have hx_span : x ∉ K ∙ u := (Projectivization.mk_eq_mk_iff_mem_span hx₀ hu₀).not.mp hpq'.symm
  by_cases hy_span : y ∈ K ∙ u
  · have hyu_mk : (⟨Projectivization.mk K y hy₀, hr⟩ : Q.isotropicPoints σ) =
        ⟨Projectivization.mk K u hu₀, hp⟩ :=
      Subtype.ext ((Projectivization.mk_eq_mk_iff_mem_span hy₀ hu₀).mpr hy_span)
    rwa [hyu_mk]
  have hu_span : u ∉ K ∙ x := (Projectivization.mk_eq_mk_iff_mem_span hu₀ hx₀).not.mp hpq'
  by_cases hux : (σ ∘ u) ⬝ᵥ (Q *ᵥ x) = 0
  · by_cases huy : (σ ∘ u) ⬝ᵥ (Q *ᵥ y) = 0
    · exact isotropicPointMk_mem_of_isBlock hσ hQ hdet htr hadm hB hu₀ hu hx hy hx_span hy_span
        hpB hqB (iff_of_true hux huy)
    have hxu : (σ ∘ x) ⬝ᵥ (Q *ᵥ u) = 0 :=
      (comp_dotProduct_mulVec_eq_zero_comm hσ hQ).mp hux
    obtain ⟨s, hs, hxs, hus⟩ :=
      exists_comp_dotProduct_mulVec_self_eq_zero_and_eq_zero_and_ne_zero hσ hQ hdet htr hu hu_span
        hux
    have hsB := isotropicPointMk_mem_of_isBlock hσ hQ hdet htr hadm hB hx₀ hx hu hs hu_span
      (notMem_span_of_dotProduct_mulVec hux hus) hqB hpB (iff_of_true hxu hxs)
    exact isotropicPointMk_mem_of_isBlock hσ hQ hdet htr hadm hB hu₀ hu hs hy
      (notMem_span_of_dotProduct_mulVec hu hus) hy_span hpB hsB (iff_of_false hus huy)
  · exact isotropicPointMk_mem_of_isBlock_of_ne_zero hσ hQ hε hdet htr hadm hB hu₀ hu hx hy
      hu_span hx_span hy_span hpB hqB hux

end Matrix

end
