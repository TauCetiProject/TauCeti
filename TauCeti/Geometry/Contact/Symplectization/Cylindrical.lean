/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.AlmostComplex
public import TauCeti.LinearAlgebra.BilinearForm.Contact
import TauCeti.Geometry.Symplectic.ExistsCompatible

/-!
# Cylindrical complex structures

Let `a` be a covector on a finite-dimensional real vector space `V` which is contact for an
alternating bilinear form `B` (`Module.Dual.IsContact`), and let `R = a.reebVector B` be its Reeb
vector, so that `a R = 1`, `B R = 0` and `V = ker a ⊕ ℝ R`. This is the pointwise linear algebra
of a contact form `α` with `B = dα`, and more generally of a stable Hamiltonian structure
`(α, ω)` with `B = ω`, at a point of a manifold `V`.

A complex structure `J` on `ℝ × V` is **cylindrical** for `a` and `B`
(`Module.Dual.IsCylindricalComplexStructure`) when it sends the unit vector `∂_s = (1, 0)` of the
`ℝ` factor to `(0, R)`, preserves the hyperplane `ξ = {0} × ker a`, and restricts there to a
complex structure compatible with `B`: `B(v, J v) > 0` for every nonzero `v ∈ ξ` and
`B(J v, J w) = B(v, w)` for `v, w ∈ ξ`. These are the pointwise conditions on a
translation-invariant almost complex structure on the cylinder `ℝ × V` over a contact manifold or
a stable Hamiltonian manifold, as used for holomorphic curves in symplectizations and in
cylindrical ends.

Such a `J` is determined by its restriction to `ξ`
(`Module.Dual.IsCylindricalComplexStructure.apply_eq`): writing `v = a(v) R + u` with `u ∈ ker a`,

`J (s, v) = (-a v, s R + J u)`.

The symplectization form `Ω((s, v), (t, w)) = s a(w) - t a(v) + B(v, w)`
(`Module.Dual.symplectizationForm`) is the value of `ds ∧ α + ω` on `ℝ × V`, and it is symplectic
for a contact covector (`Module.Dual.symplectizationSymplecticForm`). Every cylindrical `J` is
compatible with it (`Module.Dual.IsCylindricalComplexStructure.compatible`):
`Ω(x, J x) = s² + a(v)² + B(u, J u)`, which is positive for `x ≠ 0`. This is the positivity
behind the energy of holomorphic curves in cylindrical ends; its two parts are nonnegative
separately: the `ds ∧ a` part `s a(w) - t a(v)`, for `J x = (t, w)`, is `s² + a(v)²`
(`Module.Dual.IsCylindricalComplexStructure.mul_apply_snd_sub_fst_mul`), and the `B` part
`B(v, w) = B(u, J u)` is nonnegative
(`Module.Dual.IsCylindricalComplexStructure.apply_apply_snd_nonneg`). Cylindrical complex
structures exist (`Module.Dual.IsContact.exists_isCylindricalComplexStructure`): extend a complex
structure on the symplectic vector space `(ker a, B)` compatible with `B`, as provided by
`TauCeti.SymplecticForm.exists_compatible`, by the formula above.

## Main declarations

* `Module.Dual.IsCylindricalComplexStructure`: cylindrical complex structures on `ℝ × V`.
* `Module.Dual.IsCylindricalComplexStructure.apply_eq`: the formula for `J` in terms of its
  restriction to `ker a`.
* `Module.Dual.symplectizationSymplecticForm`: the symplectization form of a contact covector, as
  a symplectic form.
* `Module.Dual.IsCylindricalComplexStructure.compatible`: a cylindrical complex structure is
  compatible with the symplectization form.
* `Module.Dual.IsCylindricalComplexStructure.mul_apply_snd_sub_fst_mul`,
  `Module.Dual.IsCylindricalComplexStructure.apply_apply_snd_nonneg`: the `ds ∧ a` and `B` parts
  of the symplectization form on `(x, J x)` are nonnegative.
* `Module.Dual.IsContact.exists_isCylindricalComplexStructure`: existence.

## References

* F. Bourgeois, Y. Eliashberg, H. Hofer, K. Wysocki, E. Zehnder, *Compactness results in
  symplectic field theory*, Geom. Topol. 7 (2003), 799–888, arXiv:math/0308183, §2.1 and §2.2.
-/

public section

noncomputable section

open Module TauCeti

namespace Module.Dual

variable {V : Type*} [AddCommGroup V] [Module ℝ V] {a : Module.Dual ℝ V}
  {B : LinearMap.BilinForm ℝ V} {J : AlmostComplexStructure (ℝ × V)}

variable (a B) in
/-- A complex structure `J` on `ℝ × V` is **cylindrical** for a covector `a` and a bilinear form
`B` when `J (1, 0) = (0, R)` for the Reeb vector `R = a.reebVector B`, `J` preserves the
hyperplane `{0} × ker a`, and `B` is `J`-compatible on `ker a`: it is positive on the pairs
`(v, J v)` with `v ≠ 0` and `J`-invariant. -/
structure IsCylindricalComplexStructure (J : AlmostComplexStructure (ℝ × V)) : Prop where
  /-- `J` sends the unit vector of the `ℝ` factor to the Reeb vector. -/
  apply_one_zero : J (1, 0) = (0, a.reebVector B)
  /-- `J` preserves `{0} × V` on vectors of `ker a`. -/
  fst_apply_zero : ∀ v, a v = 0 → (J (0, v)).1 = 0
  /-- `J` preserves `ker a`. -/
  apply_snd_apply_zero : ∀ v, a v = 0 → a (J (0, v)).2 = 0
  /-- `B(v, J v)` is positive for every nonzero `v ∈ ker a`. -/
  pos : ∀ v, a v = 0 → v ≠ 0 → 0 < B v (J (0, v)).2
  /-- `B` is `J`-invariant on `ker a`. -/
  invariant : ∀ v w, a v = 0 → a w = 0 → B (J (0, v)).2 (J (0, w)).2 = B v w

namespace IsCylindricalComplexStructure

/-- A cylindrical complex structure sends the Reeb vector to `-∂_s`. -/
theorem apply_zero_reebVector (hJ : a.IsCylindricalComplexStructure B J) :
    J (0, a.reebVector B) = (-1, 0) := by
  have h := J.apply_apply (1, 0)
  rw [hJ.apply_one_zero] at h
  rw [h, Prod.neg_mk, neg_zero]

/-- On `ker a`, a cylindrical complex structure takes values in `{0} × ker a`. -/
theorem apply_zero_eq (hJ : a.IsCylindricalComplexStructure B J) {v : V} (hv : a v = 0) :
    J (0, v) = (0, (J (0, v)).2) :=
  Prod.ext (hJ.fst_apply_zero v hv) rfl

variable [FiniteDimensional ℝ V]

/-- **A cylindrical complex structure is determined by its restriction to `ker a`.** Writing
`v = a(v) R + u` with `u ∈ ker a`, it is `J (s, v) = (-a v, s R + J u)`. -/
theorem apply_eq (hJ : a.IsCylindricalComplexStructure B J) (ha : a.IsContact B) (s : ℝ)
    (v : V) :
    J (s, v) = (-a v, s • a.reebVector B + (J (0, v - a v • a.reebVector B)).2) := by
  have hdecomp : ((s, v) : ℝ × V) = s • ((1, 0) : ℝ × V) + a v • ((0, a.reebVector B) : ℝ × V) +
      (0, v - a v • a.reebVector B) := by
    ext <;> simp
  rw [hdecomp, J.apply_add, J.apply_add, J.apply_smul, J.apply_smul, hJ.apply_one_zero,
    hJ.apply_zero_reebVector, hJ.apply_zero_eq (ha.apply_sub_smul_reebVector v)]
  ext <;> simp

/-- The first coordinate of `J (s, v)` is `-a v`. -/
theorem fst_apply (hJ : a.IsCylindricalComplexStructure B J) (ha : a.IsContact B) (s : ℝ)
    (v : V) : (J (s, v)).1 = -a v := by
  simp [hJ.apply_eq ha s v]

/-- The second coordinate of `J (s, v)` takes the value `s` under `a`. -/
theorem apply_snd_apply (hJ : a.IsCylindricalComplexStructure B J) (ha : a.IsContact B) (s : ℝ)
    (v : V) : a (J (s, v)).2 = s := by
  simp [hJ.apply_eq ha s v, ha.apply_reebVector,
    hJ.apply_snd_apply_zero _ (ha.apply_sub_smul_reebVector v)]

/-- **The `ds ∧ a` part of the symplectization form on `(x, J x)`.** For `x = (s, v)` and
`J x = (t, w)`, `s a(w) - t a(v) = s² + a(v)²`. -/
theorem mul_apply_snd_sub_fst_mul (hJ : a.IsCylindricalComplexStructure B J)
    (ha : a.IsContact B) (s : ℝ) (v : V) :
    s * a (J (s, v)).2 - (J (s, v)).1 * a v = s ^ 2 + a v ^ 2 := by
  rw [hJ.apply_snd_apply ha, hJ.fst_apply ha]
  ring

variable (hB : B.IsAlt) (ha : a.IsContact B)
include hB ha

/-- **The `B` part of the symplectization form on `(x, J x)`.** For `x = (s, v)`, the value
`B(v, (J x)₂)` is `B(u, J u)`, where `u = v - a(v) R` is the component of `v` in `ker a`. -/
theorem apply_apply_snd_eq (hJ : a.IsCylindricalComplexStructure B J) (s : ℝ) (v : V) :
    B v (J (s, v)).2 =
      B (v - a v • a.reebVector B) (J (0, v - a v • a.reebVector B)).2 := by
  have key := ha.apply_sub_smul_reebVector_apply hB v (J (0, v - a v • a.reebVector B)).2
  rw [hJ.apply_snd_apply_zero _ (ha.apply_sub_smul_reebVector v), zero_smul, sub_zero] at key
  simp only [hJ.apply_eq ha s v, map_add, map_smul, ha.apply_reebVector_right hB, smul_zero,
    zero_add]
  exact key.symm

/-- **The `B` part of the symplectization form on `(x, J x)` is nonnegative:**
`0 ≤ B(v, (J (s, v))₂)`. -/
theorem apply_apply_snd_nonneg (hJ : a.IsCylindricalComplexStructure B J) (s : ℝ) (v : V) :
    0 ≤ B v (J (s, v)).2 := by
  rw [hJ.apply_apply_snd_eq hB ha]
  rcases eq_or_ne (v - a v • a.reebVector B) 0 with h | h
  · rw [h, map_zero, LinearMap.zero_apply]
  · exact (hJ.pos _ (ha.apply_sub_smul_reebVector v) h).le

/-- The symplectization form evaluated on `x = (s, v)` and `J x` is `s² + a(v)² + B(u, J u)`,
where `u = v - a(v) R` is the component of `v` in `ker a`. -/
theorem symplectizationForm_apply_eq (hJ : a.IsCylindricalComplexStructure B J) (s : ℝ)
    (v : V) :
    a.symplectizationForm B (s, v) (J (s, v)) =
      s ^ 2 + a v ^ 2 + B (v - a v • a.reebVector B)
        (J (0, v - a v • a.reebVector B)).2 := by
  rw [symplectizationForm_apply, ← hJ.apply_apply_snd_eq hB ha s v,
    ← hJ.mul_apply_snd_sub_fst_mul ha s v]

/-- The symplectization form is positive on the pairs `(x, J x)` with `x ≠ 0`. -/
private theorem symplectizationForm_apply_pos (hJ : a.IsCylindricalComplexStructure B J)
    {x : ℝ × V} (hx : x ≠ 0) : 0 < a.symplectizationForm B x (J x) := by
  obtain ⟨s, v⟩ := x
  rw [hJ.symplectizationForm_apply_eq hB ha]
  have hu := ha.apply_sub_smul_reebVector v
  have hnonneg : 0 ≤ B (v - a v • a.reebVector B) (J (0, v - a v • a.reebVector B)).2 := by
    rcases eq_or_ne (v - a v • a.reebVector B) 0 with h | h
    · rw [h, map_zero, LinearMap.zero_apply]
    · exact (hJ.pos _ hu h).le
  by_cases hs : s = 0
  · by_cases hav : a v = 0
    · have hv : v ≠ 0 := fun hv ↦ hx (by simp [hs, hv])
      have := hJ.pos _ hu (by simpa [hav] using hv)
      positivity
    · have := sq_pos_of_ne_zero hav
      positivity
  · have := sq_pos_of_ne_zero hs
    positivity

/-- A cylindrical complex structure preserves the symplectization form. -/
private theorem symplectizationForm_apply_apply_eq (hJ : a.IsCylindricalComplexStructure B J)
    (x y : ℝ × V) : a.symplectizationForm B (J x) (J y) = a.symplectizationForm B x y := by
  obtain ⟨s, v⟩ := x
  obtain ⟨t, w⟩ := y
  have hu := ha.apply_sub_smul_reebVector v
  have hu' := ha.apply_sub_smul_reebVector w
  rw [hJ.apply_eq ha s v, hJ.apply_eq ha t w, symplectizationForm_apply,
    symplectizationForm_apply]
  simp only [map_add, map_smul, ha.apply_reebVector, hJ.apply_snd_apply_zero _ hu,
    hJ.apply_snd_apply_zero _ hu', LinearMap.add_apply, LinearMap.smul_apply,
    ha.apply_reebVector_left hB, ha.apply_reebVector_right hB, hJ.invariant _ _ hu hu',
    ha.apply_sub_smul_reebVector_apply hB, smul_eq_mul]
  ring

end IsCylindricalComplexStructure

variable (a B) in
/-- The symplectization form `((s, v), (t, w)) ↦ s a(w) - t a(v) + B(v, w)` of a contact covector
`a` for an alternating form `B`, as a symplectic form on `ℝ × V`. It is the linear model of the
two-form `ds ∧ α + ω` on the cylinder `ℝ × V` over a stable Hamiltonian structure `(α, ω)`. -/
def symplectizationSymplecticForm (hB : B.IsAlt) (ha : a.IsContact B) :
    SymplecticForm (ℝ × V) where
  toBilinForm := a.symplectizationForm B
  isAlt := isAlt_symplectizationForm hB
  nondegenerate := isContact_iff_nondegenerate_symplectizationForm.1 ha

@[simp]
theorem symplectizationSymplecticForm_toBilinForm (hB : B.IsAlt) (ha : a.IsContact B) :
    (a.symplectizationSymplecticForm B hB ha).toBilinForm = a.symplectizationForm B :=
  (rfl)

variable [FiniteDimensional ℝ V]

/-- **A cylindrical complex structure is compatible with the symplectization form.** -/
theorem IsCylindricalComplexStructure.compatible (hJ : a.IsCylindricalComplexStructure B J)
    (hB : B.IsAlt) (ha : a.IsContact B) :
    (a.symplectizationSymplecticForm B hB ha).Compatible J :=
  .of_tames ((SymplecticForm.invariant_iff _ _).2 fun x y ↦
      hJ.symplectizationForm_apply_apply_eq hB ha x y)
    fun _ hx ↦ hJ.symplectizationForm_apply_pos hB ha hx

/-- **Existence of cylindrical complex structures.** Every contact covector `a` for an alternating
form `B` on a finite-dimensional real vector space admits a cylindrical complex structure on
`ℝ × V`. -/
theorem IsContact.exists_isCylindricalComplexStructure (hB : B.IsAlt) (ha : a.IsContact B) :
    ∃ J : AlmostComplexStructure (ℝ × V), a.IsCylindricalComplexStructure B J := by
  obtain ⟨R, hR⟩ : ∃ R, R = a.reebVector B := ⟨_, rfl⟩
  have hR1 : a R = 1 := hR ▸ ha.apply_reebVector
  set ξ := LinearMap.ker a
  -- The symplectic vector space `(ker a, B)` carries a compatible complex structure `j`.
  let ωξ : SymplecticForm ξ :=
    { toBilinForm := B.restrict ξ
      isAlt := fun v ↦ hB v
      nondegenerate := ha.nondegenerate_restrict }
  obtain ⟨j, hj⟩ := ωξ.exists_compatible
  -- The projection onto `ker a` along the Reeb vector.
  let π : V →ₗ[ℝ] ξ := LinearMap.codRestrict ξ (LinearMap.id - a.smulRight R)
    fun v ↦ by simp [ξ, hR1]
  have hπ : ∀ v, (π v : V) = v - a v • R := fun _ ↦ rfl
  have hπξ : ∀ v : ξ, π v = v := fun v ↦ Subtype.ext <| by
    rw [hπ, LinearMap.mem_ker.1 v.property, zero_smul, sub_zero]
  have hjξ : ∀ v : ξ, a (j v : V) = 0 := fun v ↦ (j v).property
  have hπR : ∀ (s : ℝ) (v : ξ), π (s • R + (v : V)) = v := fun s v ↦ Subtype.ext <| by
    rw [hπ, map_add, map_smul, hR1, LinearMap.mem_ker.1 v.property, smul_eq_mul, mul_one, add_zero]
    abel
  -- The cylindrical extension `(s, v) ↦ (-a v, s R + j (π v))` of `j`.
  let L : ℝ × V →ₗ[ℝ] ℝ × V :=
    (-(a ∘ₗ LinearMap.snd ℝ ℝ V)).prod
      ((LinearMap.fst ℝ ℝ V).smulRight R + ξ.subtype ∘ₗ j.toLinearMap ∘ₗ π ∘ₗ LinearMap.snd ℝ ℝ V)
  have hL : ∀ s v, L (s, v) = (-a v, s • R + (j (π v) : V)) := fun _ _ ↦ rfl
  let J : AlmostComplexStructure (ℝ × V) :=
    { toLinearMap := L
      square_neg := LinearMap.ext fun ⟨s, v⟩ ↦ by
        rw [LinearMap.comp_apply, hL, hL, hπR, j.apply_apply]
        ext
        · simp [hjξ, hR1]
        · simp only [hπ, LinearMap.neg_apply, LinearMap.id_apply, Prod.snd_neg,
            Submodule.coe_neg]
          module }
  have hJ : ∀ s v, J (s, v) = (-a v, s • R + (j (π v) : V)) := hL
  refine ⟨J, ⟨?_, fun v hv ↦ ?_, fun v _ ↦ ?_, fun v hv hv0 ↦ ?_, fun v w hv hw ↦ ?_⟩⟩
  · simp [hJ, hR]
  · simp [hJ, hv]
  · simp [hJ, hjξ]
  · rw [hJ, zero_smul, zero_add, hπξ ⟨v, hv⟩]
    exact hj.tames ⟨v, hv⟩ fun h ↦ hv0 (congrArg Subtype.val h)
  · simp only [hJ, zero_smul, zero_add]
    rw [hπξ ⟨v, hv⟩, hπξ ⟨w, hw⟩]
    exact hj.invariant_apply ⟨v, hv⟩ ⟨w, hw⟩

end Module.Dual
