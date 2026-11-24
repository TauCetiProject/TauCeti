/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Analysis.Normed.Affine.MazurUlam
public import Mathlib.Data.ZMod.Defs
public import Mathlib.GroupTheory.QuotientGroup.Defs
public import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.LinearAlgebra.Dimension.RankNullity
import TauCeti.Analysis.Normed.Operator.LinearIsometryEquiv.OfMapSMul
import TauCeti.LinearAlgebra.Projectivization.Action

/-!
# The unitary–antiunitary group and its action on rays

For a complex normed space `H`, the **unitary–antiunitary group** `UA(H)` is the group of
surjective real-linear isometries of `H` which are either complex linear or conjugate linear
(`TauCeti.unitaryAntiunitary H`, a subgroup of `H ≃ₗᵢ[ℝ] H`). For a complex Hilbert space these
are exactly the unitary and the antiunitary operators, the symmetries of quantum mechanics in
Wigner's sense: by Wigner's theorem (not proved here), for a Hilbert space of dimension at least
two, `UA(H)` modulo the scalar circle is the group of transition-probability-preserving
bijections of the space of rays `ℙ ℂ H`.

The **grade** `TauCeti.unitaryAntiunitary.grade : UA(H) →* Multiplicative (ZMod 2)` is `0` on the
complex-linear elements and `1` on the others; on a nonzero space the others are exactly the
conjugate-linear elements, because a map which is both complex linear and conjugate linear sends
`i • x` to both `i • f x` and `-(i • f x)`, hence vanishes. The kernel of the grade is the
group `H ≃ₗᵢ[ℂ] H` of complex-linear isometric equivalences
(`TauCeti.unitaryAntiunitary.range_ofLinearIsometryEquiv`).

The scalar circle `𝕋 · Id` (`TauCeti.unitaryAntiunitary.scalar`) commutes with the even
elements, while an odd element conjugates a scalar `z` to `z⁻¹ = conj z`, so the scalars form a
normal subgroup which is not central in general. Every element of `UA(H)` maps complex lines to
complex lines, which gives the action on rays `MulAction (unitaryAntiunitary H) (ℙ ℂ H)`. Its kernel
is exactly `𝕋 · Id` as soon as `H` has complex dimension at least two
(`TauCeti.unitaryAntiunitary.ker_toPermHom`); on `ℂ` itself complex conjugation acts trivially on
the single ray without being a scalar, so the dimension hypothesis cannot be dropped. Hence the
**projective unitary–antiunitary group** `PUA(H) = UA(H) ⧸ 𝕋`
(`TauCeti.ProjectiveUnitaryAntiunitary H`) acts faithfully on `ℙ ℂ H` in dimension at least two,
and the grade of an element of `UA(H)` is determined by its action on rays.

## Main definitions

* `TauCeti.unitaryAntiunitary H`: the unitary–antiunitary group `UA(H)`.
* `TauCeti.unitaryAntiunitary.grade`: the grade homomorphism `UA(H) →* ℤ/2`.
* `TauCeti.unitaryAntiunitary.ofLinearIsometryEquiv`,
  `TauCeti.unitaryAntiunitary.ofConjLinearIsometryEquiv`: the even and the odd elements built from
  Mathlib's complex-linear and conjugate-linear isometric equivalences.
* `TauCeti.unitaryAntiunitary.scalar`: the scalar circle `𝕋 →* UA(H)`.
* `TauCeti.ProjectiveUnitaryAntiunitary H`: the quotient `PUA(H) = UA(H) ⧸ 𝕋`, with its action on
  rays and its grade.

## Main statements

* `TauCeti.unitaryAntiunitary.eq_ofLinearIsometryEquiv_or_eq_ofConjLinearIsometryEquiv`: every
  element of `UA(H)` comes from a complex-linear or from a conjugate-linear isometric equivalence.
* `TauCeti.unitaryAntiunitary.mul_scalar_mul_inv_of_grade_ne_one`: an odd element conjugates the
  scalar `z` to `z⁻¹`.
* `TauCeti.unitaryAntiunitary.ker_toPermHom`: for `1 < Module.rank ℂ H` the elements acting
  trivially on rays are exactly the scalars.
* `TauCeti.ProjectiveUnitaryAntiunitary.toPermHom_injective`,
  `TauCeti.ProjectiveUnitaryAntiunitary.faithfulSMul`: `PUA(H)` acts faithfully on rays in
  dimension at least two.
* `TauCeti.unitaryAntiunitary.grade_eq_grade_of_forall_smul_eq`: in dimension at least two the
  grade is determined by the action on rays.

## References

* D. S. Freed, *On Wigner's theorem*, Geometry & Topology Monographs 18 (2012), 83–89.
-/

public section

noncomputable section

open scoped ComplexConjugate LinearAlgebra.Projectivization

namespace TauCeti

variable (H : Type*) [NormedAddCommGroup H] [NormedSpace ℂ H]

/-- The **unitary–antiunitary group** `UA(H)` of a complex normed space: the surjective real-linear
isometries of `H` which are either complex linear or conjugate linear. For a complex Hilbert space
these are the unitary and the antiunitary operators. -/
def unitaryAntiunitary : Subgroup (H ≃ₗᵢ[ℝ] H) where
  carrier := {f | (∀ (c : ℂ) (x : H), f (c • x) = c • f x) ∨
    ∀ (c : ℂ) (x : H), f (c • x) = conj c • f x}
  one_mem' := Or.inl fun _ _ ↦ rfl
  mul_mem' := by
    rintro f g (hf | hf) (hg | hg)
    · exact Or.inl fun c x ↦ by simp [hf, hg]
    · exact Or.inr fun c x ↦ by simp [hf, hg]
    · exact Or.inr fun c x ↦ by simp [hf, hg]
    · exact Or.inl fun c x ↦ by simp [hf, hg]
  inv_mem' := by
    rintro f (hf | hf)
    · exact Or.inl fun c x ↦ f.injective <| by simp [hf]
    · exact Or.inr fun c x ↦ f.injective <| by simp [hf]

variable {H}

/-- Membership in `UA(H)`: being complex linear or conjugate linear. -/
theorem mem_unitaryAntiunitary_iff {f : H ≃ₗᵢ[ℝ] H} :
    f ∈ unitaryAntiunitary H ↔ (∀ (c : ℂ) (x : H), f (c • x) = c • f x) ∨
      ∀ (c : ℂ) (x : H), f (c • x) = conj c • f x :=
  Iff.rfl

namespace unitaryAntiunitary

section Classification

variable (H)

/-- A complex-linear isometric equivalence, as an (even) element of `UA(H)`. -/
def ofLinearIsometryEquiv : (H ≃ₗᵢ[ℂ] H) →* unitaryAntiunitary H where
  toFun U := ⟨U.toIsometryEquiv.toRealLinearIsometryEquivOfMapZero U.map_zero,
    Or.inl fun c x ↦ U.map_smul c x⟩
  map_one' := rfl
  map_mul' _ _ := rfl

/-- A conjugate-linear isometric equivalence, as an (odd, if `H ≠ 0`) element of `UA(H)`. -/
def ofConjLinearIsometryEquiv (U : H ≃ₗᵢ⋆[ℂ] H) : unitaryAntiunitary H :=
  ⟨U.toIsometryEquiv.toRealLinearIsometryEquivOfMapZero U.map_zero,
    Or.inr fun c x ↦ U.map_smulₛₗ c x⟩

variable {H}

@[simp]
theorem coe_ofLinearIsometryEquiv (U : H ≃ₗᵢ[ℂ] H) :
    ⇑(ofLinearIsometryEquiv H U : H ≃ₗᵢ[ℝ] H) = U :=
  (rfl)

@[simp]
theorem coe_ofConjLinearIsometryEquiv (U : H ≃ₗᵢ⋆[ℂ] H) :
    ⇑(ofConjLinearIsometryEquiv H U : H ≃ₗᵢ[ℝ] H) = U :=
  (rfl)

theorem ofLinearIsometryEquiv_injective : Function.Injective (ofLinearIsometryEquiv H) :=
  fun U V h ↦ LinearIsometryEquiv.ext fun x ↦ by
    simpa using congr($(congrArg Subtype.val h) x)

theorem ofConjLinearIsometryEquiv_injective :
    Function.Injective (ofConjLinearIsometryEquiv H) :=
  fun U V h ↦ LinearIsometryEquiv.ext fun x ↦ by
    simpa using congr($(congrArg Subtype.val h) x)

/-- Every element of `UA(H)` comes from a complex-linear or from a conjugate-linear isometric
equivalence. -/
theorem eq_ofLinearIsometryEquiv_or_eq_ofConjLinearIsometryEquiv (g : unitaryAntiunitary H) :
    (∃ U : H ≃ₗᵢ[ℂ] H, g = ofLinearIsometryEquiv H U) ∨
      ∃ U : H ≃ₗᵢ⋆[ℂ] H, g = ofConjLinearIsometryEquiv H U := by
  rcases g.property with hg | hg
  · exact Or.inl ⟨(g : H ≃ₗᵢ[ℝ] H).toSemilinearIsometryEquivOfMapSMul hg,
      Subtype.ext <| LinearIsometryEquiv.ext fun _ ↦ by simp⟩
  · exact Or.inr ⟨(g : H ≃ₗᵢ[ℝ] H).toSemilinearIsometryEquivOfMapSMul hg,
      Subtype.ext <| LinearIsometryEquiv.ext fun _ ↦ by simp⟩

end Classification

section Grade

/-- An element of `UA(H)` is complex linear. -/
private def IsLinear (k : unitaryAntiunitary H) : Prop :=
  ∀ (c : ℂ) (x : H), (k : H ≃ₗᵢ[ℝ] H) (c • x) = c • (k : H ≃ₗᵢ[ℝ] H) x

/-- On a nonzero space an element of `UA(H)` is conjugate linear exactly when it is not complex
linear. -/
private theorem map_smul_conj_iff_not_isLinear [Nontrivial H] (k : unitaryAntiunitary H) :
    (∀ (c : ℂ) (x : H), (k : H ≃ₗᵢ[ℝ] H) (c • x) = conj c • (k : H ≃ₗᵢ[ℝ] H) x) ↔
      ¬ IsLinear k := by
  refine ⟨fun ha hl ↦ ?_, fun hk ↦ k.property.resolve_left hk⟩
  -- A map that is both complex linear and conjugate linear sends `i • x` to both `i • k x` and
  -- `-(i • k x)`, hence vanishes; this is impossible for an injective map on `H ≠ 0`.
  obtain ⟨x, hx⟩ := exists_ne (0 : H)
  have hI := ha Complex.I x
  rw [Complex.conj_I] at hI
  have h : (2 * Complex.I) • (k : H ≃ₗᵢ[ℝ] H) x = 0 := by
    linear_combination (norm := module) hI - hl Complex.I x
  simp [Complex.I_ne_zero, hx] at h

private theorem isLinear_mul_iff [Nontrivial H] (g h : unitaryAntiunitary H) :
    IsLinear (g * h) ↔ (IsLinear g ↔ IsLinear h) := by
  have hmul (x : H) : ((g * h : unitaryAntiunitary H) : H ≃ₗᵢ[ℝ] H) x =
      (g : H ≃ₗᵢ[ℝ] H) ((h : H ≃ₗᵢ[ℝ] H) x) := rfl
  have hconj (k : unitaryAntiunitary H) := map_smul_conj_iff_not_isLinear k
  rcases g.property with hg | hg <;> rcases h.property with hh | hh
  · exact iff_of_true (fun c x ↦ by rw [hmul, hmul, hh, hg]) (iff_of_true hg hh)
  · refine iff_of_false ((hconj _).1 fun c x ↦ by rw [hmul, hmul, hh, hg]) fun hgh ↦ ?_
    exact (hconj h).1 hh (hgh.1 hg)
  · refine iff_of_false ((hconj _).1 fun c x ↦ by rw [hmul, hmul, hh, hg]) fun hgh ↦ ?_
    exact (hconj g).1 hg (hgh.2 hh)
  · refine iff_of_true (fun c x ↦ by rw [hmul, hmul, hh, hg, Complex.conj_conj]) ?_
    exact iff_of_false ((hconj g).1 hg) ((hconj h).1 hh)

variable (H) in
open Classical in
/-- The **grade** `UA(H) →* ℤ/2`: `0` on the complex-linear elements and `1` on the others, which
for `H ≠ 0` are exactly the conjugate-linear ones (`grade_eq_ofAdd_one_iff`). -/
def grade : unitaryAntiunitary H →* Multiplicative (ZMod 2) where
  toFun g := if IsLinear g then 1 else Multiplicative.ofAdd 1
  map_one' := ite_eq_left_iff.2 fun h ↦ absurd (fun _ _ ↦ rfl) h
  map_mul' g h := by
    rcases subsingleton_or_nontrivial H with hH | hH
    · have hl (k : unitaryAntiunitary H) : IsLinear k := fun _ _ ↦ Subsingleton.elim _ _
      simp [hl]
    rw [isLinear_mul_iff]
    by_cases hg : IsLinear g <;> by_cases hh : IsLinear h
    · simp [hg, hh]
    · simp [hg, hh]
    · simp [hg, hh]
    · simp only [hg, hh, iff_self, ite_true, ite_false]
      decide

open Classical in
private theorem grade_apply (g : unitaryAntiunitary H) :
    grade H g = if IsLinear g then 1 else Multiplicative.ofAdd 1 :=
  rfl

/-- An element of `UA(H)` is even exactly when it is complex linear. -/
theorem grade_eq_one_iff (g : unitaryAntiunitary H) :
    grade H g = 1 ↔ ∀ (c : ℂ) (x : H), (g : H ≃ₗᵢ[ℝ] H) (c • x) = c • (g : H ≃ₗᵢ[ℝ] H) x := by
  rw [grade_apply]
  split_ifs with h
  · exact iff_of_true rfl h
  · exact iff_of_false (by decide) h

/-- On a nonzero space an element of `UA(H)` is odd exactly when it is conjugate linear. -/
theorem grade_eq_ofAdd_one_iff [Nontrivial H] (g : unitaryAntiunitary H) :
    grade H g = Multiplicative.ofAdd 1 ↔
      ∀ (c : ℂ) (x : H), (g : H ≃ₗᵢ[ℝ] H) (c • x) = conj c • (g : H ≃ₗᵢ[ℝ] H) x := by
  rw [map_smul_conj_iff_not_isLinear, grade_apply]
  split_ifs with h
  · exact iff_of_false (by decide) (not_not_intro h)
  · exact iff_of_true rfl h

@[simp]
theorem grade_ofLinearIsometryEquiv (U : H ≃ₗᵢ[ℂ] H) : grade H (ofLinearIsometryEquiv H U) = 1 :=
  (grade_eq_one_iff _).2 fun c x ↦ by simp

@[simp]
theorem grade_ofConjLinearIsometryEquiv [Nontrivial H] (U : H ≃ₗᵢ⋆[ℂ] H) :
    grade H (ofConjLinearIsometryEquiv H U) = Multiplicative.ofAdd 1 :=
  (grade_eq_ofAdd_one_iff _).2 fun c x ↦ U.map_smulₛₗ c x

/-- The even part of `UA(H)` is the group of complex-linear isometric equivalences. -/
theorem range_ofLinearIsometryEquiv : (ofLinearIsometryEquiv H).range = (grade H).ker := by
  ext g
  refine ⟨?_, fun hg ↦ ⟨(g : H ≃ₗᵢ[ℝ] H).toSemilinearIsometryEquivOfMapSMul
    ((grade_eq_one_iff g).1 hg), Subtype.ext <| LinearIsometryEquiv.ext fun _ ↦ by simp⟩⟩
  rintro ⟨U, rfl⟩
  exact grade_ofLinearIsometryEquiv U

end Grade

section Scalar

variable (H) in
/-- The scalar circle `𝕋 · Id` in `UA(H)`: `z` acts by `x ↦ z • x`. -/
def scalar : Circle →* unitaryAntiunitary H :=
  (ofLinearIsometryEquiv H).comp
    { toFun z := { DistribMulAction.toLinearEquiv ℂ H z with norm_map' := Circle.norm_smul z }
      map_one' := LinearIsometryEquiv.ext fun x ↦ one_smul _ x
      map_mul' z w := LinearIsometryEquiv.ext fun x ↦ mul_smul z w x }

@[simp]
theorem scalar_apply (z : Circle) (x : H) : (scalar H z : H ≃ₗᵢ[ℝ] H) x = (z : ℂ) • x :=
  (rfl)

@[simp]
theorem grade_scalar (z : Circle) : grade H (scalar H z) = 1 :=
  grade_ofLinearIsometryEquiv _

theorem scalar_injective [Nontrivial H] : Function.Injective (scalar H) := fun z w h ↦ by
  obtain ⟨x, hx⟩ := exists_ne (0 : H)
  have hzw := congr($(congrArg Subtype.val h) x)
  simp only [scalar_apply] at hzw
  exact Circle.ext (smul_left_injective ℂ hx hzw)

theorem range_scalar_le_ker_grade : (scalar H).range ≤ (grade H).ker := by
  rintro _ ⟨z, rfl⟩
  exact grade_scalar z

/-- The scalars commute with the even elements of `UA(H)`. -/
theorem commute_scalar_of_grade_eq_one {g : unitaryAntiunitary H} (hg : grade H g = 1)
    (z : Circle) : Commute g (scalar H z) :=
  Subtype.ext <| LinearIsometryEquiv.ext fun x ↦ by simp [(grade_eq_one_iff g).1 hg]

/-- An odd element of `UA(H)` conjugates the scalar `z` to `z⁻¹ = conj z`. -/
theorem mul_scalar_mul_inv_of_grade_ne_one {g : unitaryAntiunitary H} (hg : grade H g ≠ 1)
    (z : Circle) : g * scalar H z * g⁻¹ = scalar H z⁻¹ := by
  have hc := g.property.resolve_left (mt (grade_eq_one_iff g).2 hg)
  refine Subtype.ext <| LinearIsometryEquiv.ext fun x ↦ ?_
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, LinearIsometryEquiv.coe_mul,
    LinearIsometryEquiv.coe_inv, Function.comp_apply, scalar_apply, hc,
    LinearIsometryEquiv.apply_symm_apply, Circle.coe_inv_eq_conj]

instance normal_range_scalar : (scalar H).range.Normal where
  conj_mem := by
    rintro _ ⟨z, rfl⟩ g
    by_cases hg : grade H g = 1
    · exact ⟨z, ((commute_scalar_of_grade_eq_one hg z).mul_inv_cancel).symm⟩
    · exact ⟨z⁻¹, (mul_scalar_mul_inv_of_grade_ne_one hg z).symm⟩

end Scalar

section Rays

/-- `UA(H)` acts on the rays of `H`: complex-linear and conjugate-linear maps both send complex
lines to complex lines. -/
instance : MulAction (unitaryAntiunitary H) (ℙ ℂ H) where
  smul g := Projectivization.lift
    (fun v ↦ Projectivization.mk ℂ ((g : H ≃ₗᵢ[ℝ] H) v)
      ((g : H ≃ₗᵢ[ℝ] H).map_eq_zero_iff.not.2 v.property))
    fun a b t hab ↦ by
      rw [Projectivization.mk_eq_mk_iff']
      rcases g.property with hg | hg
      · exact ⟨t, by rw [hab, hg]⟩
      · exact ⟨conj t, by rw [hab, hg]⟩
  one_smul p := by
    induction p using Projectivization.ind
    rfl
  mul_smul g h p := by
    induction p using Projectivization.ind
    rfl

@[simp]
theorem smul_mk (g : unitaryAntiunitary H) {v : H} (hv : v ≠ 0) :
    g • Projectivization.mk ℂ v hv = Projectivization.mk ℂ ((g : H ≃ₗᵢ[ℝ] H) v)
      ((g : H ≃ₗᵢ[ℝ] H).map_eq_zero_iff.not.2 hv) :=
  (rfl)

/-- An even element acts on rays through Mathlib's projectivization of its linear map. -/
theorem ofLinearIsometryEquiv_smul (U : H ≃ₗᵢ[ℂ] H) (p : ℙ ℂ H) :
    ofLinearIsometryEquiv H U • p = p.map U.toLinearEquiv.toLinearMap U.injective := by
  induction p using Projectivization.ind
  simp [Projectivization.map_mk]

/-- A conjugate-linear element acts on rays through Mathlib's projectivization of its semilinear
map. -/
theorem ofConjLinearIsometryEquiv_smul (U : H ≃ₗᵢ⋆[ℂ] H) (p : ℙ ℂ H) :
    ofConjLinearIsometryEquiv H U • p = p.map U.toLinearEquiv.toLinearMap U.injective := by
  induction p using Projectivization.ind
  simp [Projectivization.map_mk]

@[simp]
theorem scalar_smul (z : Circle) (p : ℙ ℂ H) : scalar H z • p = p := by
  induction p using Projectivization.ind
  simp [Projectivization.mk_eq_mk_iff']

theorem range_scalar_le_ker_toPermHom :
    (scalar H).range ≤ (MulAction.toPermHom (unitaryAntiunitary H) (ℙ ℂ H)).ker := by
  rintro _ ⟨z, rfl⟩
  exact Equiv.ext (scalar_smul z)

/-- An even element of `UA(H)` fixes every ray exactly when it is a scalar. No dimension
hypothesis is needed: on `ℂ` and on `0` every even element is a scalar. -/
theorem forall_smul_eq_iff_mem_range_scalar_of_grade_eq_one {g : unitaryAntiunitary H}
    (hg : grade H g = 1) : (∀ p : ℙ ℂ H, g • p = p) ↔ g ∈ (scalar H).range := by
  refine ⟨fun hfix ↦ ?_, fun ⟨z, hz⟩ p ↦ hz ▸ scalar_smul z p⟩
  rw [← MonoidHom.mem_ker, ← range_ofLinearIsometryEquiv] at hg
  obtain ⟨U, rfl⟩ := hg
  obtain ⟨c, hc⟩ := (TauCeti.Projectivization.forall_smul_eq_iff_exists_smul (K := ℂ) (V := H)
    U.toLinearEquiv).1 fun p ↦ by
      induction p using Projectivization.ind with | _ v hv =>
      rw [Projectivization.smul_mk]
      exact hfix (Projectivization.mk ℂ v hv)
  rcases subsingleton_or_nontrivial H with hH | hH
  · exact ⟨1, Subtype.ext <| LinearIsometryEquiv.ext fun _ ↦ Subsingleton.elim _ _⟩
  obtain ⟨x, hx⟩ := exists_ne (0 : H)
  have hnorm : ‖c‖ = 1 := by
    have := U.norm_map x
    rw [show U x = c • x from hc x, norm_smul] at this
    exact (mul_eq_right₀ (norm_ne_zero_iff.2 hx)).1 this
  exact ⟨⟨c, mem_sphere_zero_iff_norm.2 hnorm⟩,
    Subtype.ext <| LinearIsometryEquiv.ext fun v ↦ (hc v).symm⟩

/-- In complex dimension at least two an element of `UA(H)` fixing every ray is even. -/
theorem grade_eq_one_of_forall_smul_eq (h : 1 < Module.rank ℂ H) {g : unitaryAntiunitary H}
    (hfix : ∀ p : ℙ ℂ H, g • p = p) : grade H g = 1 := by
  -- A conjugate-linear map fixing the rays of `x`, `y`, `x + y` and `x + i • y` for linearly
  -- independent `x`, `y` would vanish at `x`.
  by_contra hg
  have hc := g.property.resolve_left (mt (grade_eq_one_iff g).2 hg)
  have : Nontrivial H := rank_pos_iff_nontrivial.1 (zero_lt_one.trans h)
  obtain ⟨x, hx⟩ := exists_ne (0 : H)
  obtain ⟨y, hxy⟩ := exists_linearIndependent_pair_of_one_lt_rank h hx
  -- `g` multiplies each nonzero vector by a scalar.
  have hray (v : H) (hv : v ≠ 0) : ∃ a : ℂ, a • v = (g : H ≃ₗᵢ[ℝ] H) v := by
    simpa [Projectivization.mk_eq_mk_iff'] using hfix (Projectivization.mk ℂ v hv)
  have hne (s : ℂ) : x + s • y ≠ 0 := fun h0 ↦ by
    simpa using LinearIndependent.pair_iff.1 hxy 1 s (by simpa using h0)
  obtain ⟨a, ha⟩ := hray x hx
  obtain ⟨b, hb⟩ := hray y (hxy.ne_zero 1)
  obtain ⟨c, hc'⟩ := hray (x + y) (by simpa using hne 1)
  obtain ⟨d, hd⟩ := hray (x + Complex.I • y) (hne Complex.I)
  rw [map_add] at hc'
  rw [map_add, hc, Complex.conj_I] at hd
  obtain ⟨hca, hcb⟩ := LinearIndependent.pair_iff.1 hxy (c - a) (c - b) <| by
    linear_combination (norm := module) hc' - ha - hb
  obtain ⟨hda, hdb⟩ := LinearIndependent.pair_iff.1 hxy (d - a)
    (d * Complex.I + Complex.I * b) <| by
      linear_combination (norm := module) hd - ha + Complex.I • hb
  have ha0 : a = 0 := by
    have h2 : 2 * Complex.I * a = 0 := by
      linear_combination hdb - Complex.I * hda + Complex.I * (hcb - hca)
    simpa using h2
  exact hx ((g : H ≃ₗᵢ[ℝ] H).map_eq_zero_iff.1 (by rw [← ha, ha0, zero_smul]))

/-- In complex dimension at least two an element of `UA(H)` fixes every ray exactly when it is a
scalar. -/
theorem forall_smul_eq_iff_mem_range_scalar (h : 1 < Module.rank ℂ H)
    (g : unitaryAntiunitary H) :
    (∀ p : ℙ ℂ H, g • p = p) ↔ g ∈ (scalar H).range :=
  ⟨fun hfix ↦ (forall_smul_eq_iff_mem_range_scalar_of_grade_eq_one
    (grade_eq_one_of_forall_smul_eq h hfix)).1 hfix,
    fun ⟨z, hz⟩ p ↦ hz ▸ scalar_smul z p⟩

/-- In complex dimension at least two the kernel of the action of `UA(H)` on rays is the scalar
circle `𝕋 · Id`. -/
theorem ker_toPermHom (h : 1 < Module.rank ℂ H) :
    (MulAction.toPermHom (unitaryAntiunitary H) (ℙ ℂ H)).ker = (scalar H).range := by
  ext g
  simp [Equiv.Perm.ext_iff, ← forall_smul_eq_iff_mem_range_scalar h]

end Rays

end unitaryAntiunitary

variable (H) in
/-- The **projective unitary–antiunitary group** `PUA(H) = UA(H) ⧸ 𝕋` of a complex normed space. -/
abbrev ProjectiveUnitaryAntiunitary : Type _ :=
  unitaryAntiunitary H ⧸ (unitaryAntiunitary.scalar H).range

namespace ProjectiveUnitaryAntiunitary

open unitaryAntiunitary

variable (H) in
/-- The action of `PUA(H)` on the rays of `H`, through which the action of `UA(H)` factors. -/
def toPermHom : ProjectiveUnitaryAntiunitary H →* Equiv.Perm (ℙ ℂ H) :=
  QuotientGroup.lift _ (MulAction.toPermHom _ _) range_scalar_le_ker_toPermHom

instance : MulAction (ProjectiveUnitaryAntiunitary H) (ℙ ℂ H) :=
  MulAction.compHom _ (toPermHom H)

@[simp]
theorem mk_smul (g : unitaryAntiunitary H) (p : ℙ ℂ H) :
    (g : ProjectiveUnitaryAntiunitary H) • p = g • p :=
  (rfl)

@[simp]
theorem toPermHom_mk_apply (g : unitaryAntiunitary H) (p : ℙ ℂ H) :
    toPermHom H (g : ProjectiveUnitaryAntiunitary H) p = g • p :=
  (rfl)

/-- In complex dimension at least two, `PUA(H)` acts faithfully on the rays of `H`. -/
theorem toPermHom_injective (h : 1 < Module.rank ℂ H) : Function.Injective (toPermHom H) := by
  rw [← MonoidHom.ker_eq_bot_iff, toPermHom, QuotientGroup.ker_lift, ker_toPermHom h,
    QuotientGroup.map_mk'_self]

/-- In complex dimension at least two, `PUA(H)` acts faithfully on the rays of `H`. -/
theorem faithfulSMul (h : 1 < Module.rank ℂ H) :
    FaithfulSMul (ProjectiveUnitaryAntiunitary H) (ℙ ℂ H) :=
  ⟨fun hxy ↦ toPermHom_injective h (Equiv.ext hxy)⟩

variable (H) in
/-- The grade `PUA(H) →* ℤ/2`, well defined because the scalars are even. -/
def grade : ProjectiveUnitaryAntiunitary H →* Multiplicative (ZMod 2) :=
  QuotientGroup.lift _ (unitaryAntiunitary.grade H) range_scalar_le_ker_grade

@[simp]
theorem grade_mk (g : unitaryAntiunitary H) :
    grade H (g : ProjectiveUnitaryAntiunitary H) = unitaryAntiunitary.grade H g :=
  (rfl)

end ProjectiveUnitaryAntiunitary

/-- In complex dimension at least two, the grade of an element of `UA(H)` is determined by its
action on rays: two elements inducing the same ray map are both unitary or both antiunitary. -/
theorem unitaryAntiunitary.grade_eq_grade_of_forall_smul_eq (h : 1 < Module.rank ℂ H)
    {g g' : unitaryAntiunitary H} (hgg' : ∀ p : ℙ ℂ H, g • p = g' • p) :
    unitaryAntiunitary.grade H g = unitaryAntiunitary.grade H g' := by
  have : (g : ProjectiveUnitaryAntiunitary H) = g' :=
    ProjectiveUnitaryAntiunitary.toPermHom_injective h (Equiv.ext hgg')
  rw [← ProjectiveUnitaryAntiunitary.grade_mk, this, ProjectiveUnitaryAntiunitary.grade_mk]

end TauCeti
