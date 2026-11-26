/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Instances.ComplexProjectiveSpace.Generator
public import TauCeti.Geometry.Manifold.Instances.ComplexProjectiveSpace.Line
public import TauCeti.Geometry.Symplectic.Manifold.Energy.Sphere

/-!
# Holomorphic spheres in complex projective space and the line class

The Fubini–Study form `ω_FS` of `CPⁿ⁺¹` (`TauCeti.ComplexProjectiveSpace.fubiniStudyForm`) has
area `1` on the class of a line, and the line class generates `π₂(CPⁿ⁺¹) ≅ ℤ`. This file draws
the consequences for the areas of sphere classes and of holomorphic spheres.

* **Areas of sphere classes.** At the base point `[e₁]`, the area of a class is its image under
  the isomorphism `π₂(CPⁿ⁺¹) ≃ ℤ` of the Hopf fibration
  (`TauCeti.ComplexProjectiveSpace.sphereIntegral_fubiniStudyForm_eq_toAdd_pi2MulEquivInt`). The
  integral over spheres does not change under base-point change, so at every base point the area
  of a sphere class is an integer
  (`TauCeti.ComplexProjectiveSpace.exists_sphereIntegral_fubiniStudyForm_eq_intCast`) and a sphere
  class is determined by its area
  (`TauCeti.ComplexProjectiveSpace.sphereIntegral_fubiniStudyForm_injective`). In particular a
  class is carried to the line class along a path exactly when its area is `1`
  (`TauCeti.ComplexProjectiveSpace.homotopyGroupTransport_eq_lineClass_iff`).
* **Holomorphic spheres.** The form `ω_FS` is compatible with the standard complex structure of
  `CPⁿ⁺¹`, so the class of a holomorphic sphere `u : OnePoint ℂ → CPⁿ⁺¹` has area its energy,
  which is nonnegative and vanishes only for constant `u`
  (`TauCeti.SmoothTwoForm.Tames.sphereIntegral_eq_zero_iff`). Hence the area of a holomorphic
  sphere is a natural number
  (`TauCeti.ComplexProjectiveSpace.exists_sphereIntegral_fubiniStudyForm_eq_natCast`), at least
  `1` when the sphere is not constant
  (`TauCeti.ComplexProjectiveSpace.one_le_sphereIntegral_fubiniStudyForm`).
* **The line class is indecomposable.** If the areas of finitely many holomorphic spheres add up
  to `1`, exactly one of them is not constant
  (`TauCeti.ComplexProjectiveSpace.existsUnique_not_forall_eq_of_sum_sphereIntegral_eq_one`), and
  it has area `1`
  (`TauCeti.ComplexProjectiveSpace.sphereIntegral_fubiniStudyForm_eq_one_of_sum_eq_one`), so it
  represents the line class. Since a class is determined by its area, this applies to the
  components of a genus-zero stable map in the line class of `CPⁿ⁺¹`: the classes of its
  components add up to the line class, so exactly one component is not constant, and that
  component represents the line class itself. This is the first step in showing that every such
  stable map is a line with contracted components attached, the input to the regularity of the
  moduli space of lines and to the count of lines through two points.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS
  Colloquium Publications 52, 2012, Section 2.2 (Lemma 2.2.1: the energy of a holomorphic sphere
  is the symplectic area of its class).
* W. Fulton and R. Pandharipande, *Notes on stable maps and quantum cohomology*, in *Algebraic
  geometry, Santa Cruz 1995*, Proc. Sympos. Pure Math. 62, Part 2, AMS (1997), 45–96, Section 10
  (stable maps of degree one to projective space and the quantum cohomology of `ℙʳ`).
-/

public section

open scoped Manifold ContDiff Topology Topology.Homotopy TauCeti.ComplexManifold

namespace TauCeti.ComplexProjectiveSpace

variable {n : ℕ}

/-! ### Areas of sphere classes -/

/-- The Fubini–Study form is `C¹`, as the integral over spheres requires. -/
private theorem isSmoothForm_fubiniStudyForm_one :
    IsSmoothForm 𝓘(ℝ, Fin (n + 1) → ℂ) 1 (fubiniStudyForm (n + 1)).val :=
  (fubiniStudyForm (n + 1)).isSmoothForm.of_le (by simp)

/-- The Fubini–Study form is closed. -/
private theorem mextDeriv_fubiniStudyForm_val :
    mextDeriv (fubiniStudyForm (n + 1)).val = 0 :=
  (SmoothForm.isClosed_def _).1 (isSymplectic_fubiniStudyForm (n := n + 1)).isClosed

/-- The line class has Fubini–Study area `1`: it is the class of `lineSquare n`, of area `1`,
carried to `[e₁]` by the identity. -/
private theorem sphereIntegral_fubiniStudyForm_lineClass :
    sphereIntegral (fubiniStudyForm (n + 1)).val (mk (n + 1) (affineUnitVector 1 0))
      (lineClass n) = 1 := by
  have key : ∀ y (hy : ContinuousMap.id _ (affineParam 1 0) = y)
      (a : π_ 2 (ComplexProjectiveSpace (n + 1)) (affineParam 1 0)),
      sphereIntegral (fubiniStudyForm (n + 1)).val y (HomotopyGroup.map (ContinuousMap.id _) hy a) =
        sphereIntegral (fubiniStudyForm (n + 1)).val (affineParam 1 0) a := by
    rintro _ rfl a
    -- The base point `ContinuousMap.id _ (affineParam 1 0)` is `affineParam 1 0` by `id_apply`.
    exact congrArg _ (HomotopyGroup.map_id_apply a)
  rw [lineClass_def]
  exact (key _ _ ⟦lineSquare n⟧).trans sphereIntegral_fubiniStudyForm_lineSquare

/-- **The area of a sphere class of `CPⁿ⁺¹` is its degree.** At the base point
`[e₁] = mk (n + 1) (affineUnitVector 1 0)`, the integral of the Fubini–Study form over a class of
`π₂(CPⁿ⁺¹)` is its image in `ℤ` under the isomorphism
`TauCeti.ComplexProjectiveSpace.pi2MulEquivInt` of the Hopf fibration. -/
theorem sphereIntegral_fubiniStudyForm_eq_toAdd_pi2MulEquivInt
    (a : π_ 2 (ComplexProjectiveSpace (n + 1)) (mk (n + 1) (affineUnitVector 1 0))) :
    sphereIntegral (fubiniStudyForm (n + 1)).val (mk (n + 1) (affineUnitVector 1 0)) a =
      Multiplicative.toAdd (pi2MulEquivInt (affineUnitVector 1 0) n.add_one_ne_zero a) := by
  -- Every class is a power of the line class, and the integral is a homomorphism.
  set e := pi2MulEquivInt (affineUnitVector 1 0) n.add_one_ne_zero
  obtain ⟨k, hk⟩ : ∃ k : ℤ, e a = Multiplicative.ofAdd k := ⟨_, (ofAdd_toAdd _).symm⟩
  have ha : a = lineClass n ^ k := by
    rw [← pi2MulEquivInt_symm_ofAdd_one, ← map_zpow, ← ofAdd_zsmul, smul_eq_mul, mul_one,
      ← hk, MulEquiv.symm_apply_apply]
  have hpow := map_zsmul (sphereIntegralHom (mk (n + 1) (affineUnitVector 1 0))
    isSmoothForm_fubiniStudyForm_one mextDeriv_fubiniStudyForm_val) k (Additive.ofMul (lineClass n))
  rw [← ofMul_zpow, sphereIntegralHom_apply, sphereIntegralHom_apply, toMul_ofMul, toMul_ofMul,
    sphereIntegral_fubiniStudyForm_lineClass] at hpow
  rw [hk, toAdd_ofAdd, ha, hpow, zsmul_eq_mul, mul_one]

/-- **Sphere classes of `CPⁿ⁺¹` have integral area.** At every base point `x`, the integral of the
Fubini–Study form over a class of `π₂(CPⁿ⁺¹, x)` is an integer. -/
theorem exists_sphereIntegral_fubiniStudyForm_eq_intCast {x : ComplexProjectiveSpace (n + 1)}
    (a : π_ 2 (ComplexProjectiveSpace (n + 1)) x) :
    ∃ k : ℤ, sphereIntegral (fubiniStudyForm (n + 1)).val x a = k :=
  ⟨_, (sphereIntegral_homotopyGroupTransport isSmoothForm_fubiniStudyForm_one
    mextDeriv_fubiniStudyForm_val (PathConnectedSpace.somePath _ _) a).symm.trans
    (sphereIntegral_fubiniStudyForm_eq_toAdd_pi2MulEquivInt _)⟩

/-- **A sphere class of `CPⁿ⁺¹` is determined by its area.** At every base point `x`, the integral
of the Fubini–Study form is injective on `π₂(CPⁿ⁺¹, x)`. -/
theorem sphereIntegral_fubiniStudyForm_injective (x : ComplexProjectiveSpace (n + 1)) :
    Function.Injective (sphereIntegral (fubiniStudyForm (n + 1)).val x) := by
  let γ : Path x (mk (n + 1) (affineUnitVector 1 0)) := PathConnectedSpace.somePath _ _
  intro a b hab
  -- Transport both classes to `[e₁]`, where the area is the degree.
  rw [← sphereIntegral_homotopyGroupTransport isSmoothForm_fubiniStudyForm_one
      mextDeriv_fubiniStudyForm_val γ a,
    ← sphereIntegral_homotopyGroupTransport isSmoothForm_fubiniStudyForm_one
      mextDeriv_fubiniStudyForm_val γ b,
    sphereIntegral_fubiniStudyForm_eq_toAdd_pi2MulEquivInt,
    sphereIntegral_fubiniStudyForm_eq_toAdd_pi2MulEquivInt, Int.cast_inj] at hab
  refine (homotopyGroupEquivOfPath γ).injective ?_
  rw [homotopyGroupEquivOfPath_apply, homotopyGroupEquivOfPath_apply]
  exact (pi2MulEquivInt _ _).injective (Multiplicative.toAdd.injective hab)

/-- **The classes of area one are the line class.** A class of `π₂(CPⁿ⁺¹, x)` is carried to the
line class `TauCeti.ComplexProjectiveSpace.lineClass n` along a path from `x` to its base point
exactly when its Fubini–Study area is `1`. -/
theorem homotopyGroupTransport_eq_lineClass_iff {x : ComplexProjectiveSpace (n + 1)}
    (γ : Path x (mk (n + 1) (affineUnitVector 1 0))) (a : π_ 2 (ComplexProjectiveSpace (n + 1)) x) :
    homotopyGroupTransport γ a = lineClass n ↔
      sphereIntegral (fubiniStudyForm (n + 1)).val x a = 1 := by
  rw [← sphereIntegral_homotopyGroupTransport isSmoothForm_fubiniStudyForm_one
    mextDeriv_fubiniStudyForm_val γ a]
  refine ⟨fun h ↦ h ▸ sphereIntegral_fubiniStudyForm_lineClass, fun h ↦ ?_⟩
  exact sphereIntegral_fubiniStudyForm_injective _
    (h.trans sphereIntegral_fubiniStudyForm_lineClass.symm)

/-! ### Holomorphic spheres -/

section Holomorphic

attribute [local instance] Complex.finrank_real_complex_fact

variable {u : OnePoint ℂ → ComplexProjectiveSpace (n + 1)}

/-- **Holomorphic spheres in `CPⁿ⁺¹` have area a natural number.** The Fubini–Study area of the
class `u_*[S²]` of a smooth holomorphic map `u` of the Riemann sphere to `CPⁿ⁺¹` is a natural
number. -/
theorem exists_sphereIntegral_fubiniStudyForm_eq_natCast
    (hu : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, Fin (n + 1) → ℂ) ∞ u)
    (hhol : IsPseudoholomorphic (SmoothAlmostComplexStructure.ofComplexManifold ℂ (OnePoint ℂ))
      (SmoothAlmostComplexStructure.ofComplexManifold (Fin (n + 1) → ℂ)
        (ComplexProjectiveSpace (n + 1))) u) :
    ∃ k : ℕ, sphereIntegral (fubiniStudyForm (n + 1)).val (u OnePoint.infty)
      (HomotopyGroup.map ⟨u, hu.continuous⟩ rfl ⟦riemannSphereSquare⟧) = k := by
  obtain ⟨k, hk⟩ : ∃ k : ℤ, sphereIntegral (fubiniStudyForm (n + 1)).val (u OnePoint.infty)
      (HomotopyGroup.map ⟨u, hu.continuous⟩ rfl ⟦riemannSphereSquare⟧) = k :=
    exists_sphereIntegral_fubiniStudyForm_eq_intCast _
  have h0 := compatible_fubiniStudyForm.tames.sphereIntegral_nonneg
    (isSymplectic_fubiniStudyForm (n := n + 1)).isClosed hu hhol
  rw [hk, Int.cast_nonneg_iff] at h0
  exact ⟨k.toNat, by rw [hk, ← Int.cast_natCast, Int.toNat_of_nonneg h0]⟩

/-- **Nonconstant holomorphic spheres in `CPⁿ⁺¹` have area at least one.** The Fubini–Study area
of the class `u_*[S²]` of a smooth holomorphic map `u` of the Riemann sphere to `CPⁿ⁺¹` is at
least `1` unless `u` is constant. -/
theorem one_le_sphereIntegral_fubiniStudyForm
    (hu : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, Fin (n + 1) → ℂ) ∞ u)
    (hhol : IsPseudoholomorphic (SmoothAlmostComplexStructure.ofComplexManifold ℂ (OnePoint ℂ))
      (SmoothAlmostComplexStructure.ofComplexManifold (Fin (n + 1) → ℂ)
        (ComplexProjectiveSpace (n + 1))) u)
    (hnc : ¬ ∀ z z', u z = u z') :
    1 ≤ sphereIntegral (fubiniStudyForm (n + 1)).val (u OnePoint.infty)
      (HomotopyGroup.map ⟨u, hu.continuous⟩ rfl ⟦riemannSphereSquare⟧) := by
  obtain ⟨k, hk⟩ := exists_sphereIntegral_fubiniStudyForm_eq_natCast hu hhol
  have h0 : k ≠ 0 := by
    rintro rfl
    exact hnc ((compatible_fubiniStudyForm.tames.sphereIntegral_eq_zero_iff
      (isSymplectic_fubiniStudyForm (n := n + 1)).isClosed hu hhol).1 (by rw [hk, Nat.cast_zero]))
  rw [hk, Nat.one_le_cast]
  exact Nat.one_le_iff_ne_zero.2 h0

end Holomorphic

/-! ### Families of holomorphic spheres of total area one -/

section Family

attribute [local instance] Complex.finrank_real_complex_fact

variable {ι : Type*} [Fintype ι] {u : ι → OnePoint ℂ → ComplexProjectiveSpace (n + 1)}
  (hu : ∀ i, ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, Fin (n + 1) → ℂ) ∞ (u i))
  (hhol : ∀ i, IsPseudoholomorphic
    (SmoothAlmostComplexStructure.ofComplexManifold ℂ (OnePoint ℂ))
    (SmoothAlmostComplexStructure.ofComplexManifold (Fin (n + 1) → ℂ)
      (ComplexProjectiveSpace (n + 1))) (u i))
include hu hhol

/-- The areas `kᵢ` of a family of holomorphic spheres of total area one, read in `ℕ`: exactly one
of them is `1`, and the others vanish. -/
private theorem exists_eq_one_and_forall_ne_eq_zero
    (hsum : ∑ i, sphereIntegral (fubiniStudyForm (n + 1)).val (u i OnePoint.infty)
      (HomotopyGroup.map ⟨u i, (hu i).continuous⟩ rfl ⟦riemannSphereSquare⟧) = 1) :
    ∃ i, sphereIntegral (fubiniStudyForm (n + 1)).val (u i OnePoint.infty)
        (HomotopyGroup.map ⟨u i, (hu i).continuous⟩ rfl ⟦riemannSphereSquare⟧) = 1 ∧
      ∀ j ≠ i, sphereIntegral (fubiniStudyForm (n + 1)).val (u j OnePoint.infty)
        (HomotopyGroup.map ⟨u j, (hu j).continuous⟩ rfl ⟦riemannSphereSquare⟧) = 0 := by
  classical
  choose k hk using fun i ↦ exists_sphereIntegral_fubiniStudyForm_eq_natCast (hu i) (hhol i)
  simp_rw [hk] at hsum ⊢
  rw [← Nat.cast_sum, Nat.cast_eq_one] at hsum
  -- Some area is nonzero, hence it is the whole sum `1`, and the others vanish.
  obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero (s := Finset.univ) (f := k)
    (by rw [hsum]; exact one_ne_zero)
  have hrest := Finset.add_sum_erase Finset.univ k (Finset.mem_univ i)
  rw [hsum] at hrest
  have hki : k i = 1 := by omega
  rw [hki, add_eq_left, Finset.sum_eq_zero_iff] at hrest
  exact ⟨i, by rw [hki, Nat.cast_one], fun j hj ↦ by
    rw [hrest j (Finset.mem_erase.2 ⟨hj, Finset.mem_univ j⟩), Nat.cast_zero]⟩

/-- **Exactly one sphere of a family of total area one is not constant.** If the Fubini–Study
areas of finitely many smooth holomorphic maps `uᵢ` of the Riemann sphere to `CPⁿ⁺¹` add up to
`1`, as for the components of a genus-zero stable map in the line class, exactly one `uᵢ` is not
constant. -/
theorem existsUnique_not_forall_eq_of_sum_sphereIntegral_eq_one
    (hsum : ∑ i, sphereIntegral (fubiniStudyForm (n + 1)).val (u i OnePoint.infty)
      (HomotopyGroup.map ⟨u i, (hu i).continuous⟩ rfl ⟦riemannSphereSquare⟧) = 1) :
    ∃! i, ¬ ∀ z z', u i z = u i z' := by
  have hzero (j : ι) := compatible_fubiniStudyForm.tames.sphereIntegral_eq_zero_iff
    (isSymplectic_fubiniStudyForm (n := n + 1)).isClosed (hu j) (hhol j)
  obtain ⟨i, hi, hj⟩ := exists_eq_one_and_forall_ne_eq_zero hu hhol hsum
  refine ⟨i, fun h ↦ one_ne_zero (hi.symm.trans ((hzero i).2 h)), fun j hnc ↦ ?_⟩
  by_contra hji
  exact hnc ((hzero j).1 (hj j hji))

/-- **The nonconstant sphere of a family of total area one has area one.** If the Fubini–Study
areas of finitely many smooth holomorphic maps `uᵢ` of the Riemann sphere to `CPⁿ⁺¹` add up to
`1`, a nonconstant `uᵢ` has area `1`: by
`TauCeti.ComplexProjectiveSpace.homotopyGroupTransport_eq_lineClass_iff`, it represents the line
class. -/
theorem sphereIntegral_fubiniStudyForm_eq_one_of_sum_eq_one
    (hsum : ∑ i, sphereIntegral (fubiniStudyForm (n + 1)).val (u i OnePoint.infty)
      (HomotopyGroup.map ⟨u i, (hu i).continuous⟩ rfl ⟦riemannSphereSquare⟧) = 1)
    {i : ι} (hi : ¬ ∀ z z', u i z = u i z') :
    sphereIntegral (fubiniStudyForm (n + 1)).val (u i OnePoint.infty)
      (HomotopyGroup.map ⟨u i, (hu i).continuous⟩ rfl ⟦riemannSphereSquare⟧) = 1 := by
  obtain ⟨j, hj, hk⟩ := exists_eq_one_and_forall_ne_eq_zero hu hhol hsum
  obtain rfl : i = j := by
    by_contra hij
    exact hi ((compatible_fubiniStudyForm.tames.sphereIntegral_eq_zero_iff
      (isSymplectic_fubiniStudyForm (n := n + 1)).isClosed (hu i) (hhol i)).1 (hk i hij))
  exact hj

end Family

end TauCeti.ComplexProjectiveSpace
