/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wentao Li
-/
module

public import TauCeti.LinearAlgebra.FiniteBilinearModule.GaussSum

/-!
# Comparing quadratic refinements of finite bilinear modules

Two nondegenerate finite quadratic modules are isometric exactly when their polar bilinear
modules are isometric and their Gauss-sum invariants agree. This is Nikulin's Theorem 1.11.3.

Given a bilinear isometry `f`, the discrepancy `q_B(f x) - q_A(x)` is an additive character
killed by two. Nondegeneracy represents it as `b_A(a, x)` for a vector `a` killed by two.
Translation by `a` compares the Gauss sums, so equality of their invariants forces `q_A(a) = 0`.
The additive involution that fixes `x` when `b_A(a, x) = 0` and sends it to `x + a` otherwise
then corrects `f` to a quadratic isometry. The given bilinear isometry need not itself preserve
the quadratic maps.

## Main declarations

* `TauCeti.FiniteQuadraticModule.isometryOfBilinearIsometry`: correct a bilinear isometry
  between nondegenerate quadratic modules with equal Gauss-sum invariants.
* `TauCeti.FiniteQuadraticModule.nonempty_isometry_iff_bilinear_isometry_and_gaussSign_eq`:
  the classification comparison theorem.
* `TauCeti.FiniteQuadraticModule.isometryOfBilinearIsometryOfOdd` and
  `TauCeti.FiniteQuadraticModule.nonempty_isometry_iff_bilinear_isometry_of_odd`: on a module of
  odd order, every bilinear isometry already preserves the quadratic map.
* `TauCeti.FiniteBilinearModule.toFiniteQuadraticModuleOfOdd`: the unique quadratic refinement
  `q(x) = ((#B + 1) / 2) • b(x, x)` of a finite bilinear module of odd order.

## References

* V. V. Nikulin, *Integral symmetric bilinear forms and some of their applications*,
  Theorem 1.11.3.
* F. Deloup and G. Massuyeau, *Quadratic functions on torsion groups*, Journal of Pure and
  Applied Algebra 198 (2005), 105–121, Corollary 4.2 and Lemma 4.3. The proof here follows
  their isotropic two-torsion correction, in the homogeneous case.
-/

public section

namespace TauCeti.FiniteQuadraticModule

universe u v

variable {A : FiniteQuadraticModule.{u}} {B : FiniteQuadraticModule.{v}}

/-- The discrepancy of two quadratic refinements of isometric polar pairings is additive. -/
private def discrepancy (f : FiniteBilinearModule.Isometry
    A.toFiniteBilinearModule B.toFiniteBilinearModule) : CharacterModule A where
  toFun x := B.quadratic (f x) - A.quadratic x
  map_zero' := by simp
  map_add' x y := by
    -- Expose the additive-equivalence coercion so its map-add lemma can rewrite the argument.
    change B.quadratic (f.toAddEquiv (x + y)) - A.quadratic (x + y) = _
    rw [f.toAddEquiv.map_add, QuadraticMap.map_add B.quadratic,
      QuadraticMap.map_add A.quadratic,
      A.polar_eq_pairing, B.polar_eq_pairing, FiniteBilinearModule.Isometry.coe_toAddEquiv,
      f.map_pairing]
    abel

private theorem two_zsmul_discrepancy (f : FiniteBilinearModule.Isometry
    A.toFiniteBilinearModule B.toFiniteBilinearModule) (x : A) :
    (2 : ℤ) • discrepancy f x = 0 := by
  -- Unfold the application of the private discrepancy character before comparing polar forms.
  change (2 : ℤ) • (B.quadratic (f x) - A.quadratic x) = 0
  rw [ofNat_zsmul, nsmul_sub, ← QuadraticMap.polar_self, ← QuadraticMap.polar_self,
    A.polar_eq_pairing, B.polar_eq_pairing, f.map_pairing, sub_self]

/-- The character with values `0` and `1/2` acts on a vector killed by two. -/
private noncomputable def correction (d : CharacterModule A)
    (hd : ∀ x, (2 : ℤ) • d x = 0) (a : A) (ha : 2 • a = 0) : A →+ A where
  toFun x := if d x = 0 then 0 else a
  map_zero' := by simp
  map_add' x y := by
    have haa : a + a = 0 := by simpa only [two_nsmul] using ha
    by_cases hx : d x = 0
    · by_cases hy : d y = 0 <;> simp [map_add, hx, hy]
    · by_cases hy : d y = 0
      · simp [map_add, hx, hy]
      · have hhalf (z : A) (hz : d z ≠ 0) :
            d z = ((1 / 2 : ℚ) : AddCircle (1 : ℚ)) :=
          (AddCircle.eq_zero_or_eq_coe_period_div_two (1 : ℚ) two_ne_zero (hd z)).resolve_left hz
        have hxy : d x + d y = 0 := by
          rw [hhalf y hy, ← hhalf x hx]
          simpa only [two_zsmul] using hd x
        simp [map_add, hx, hy, hxy, haa]

private theorem gaussSum_discrepancy (f : FiniteBilinearModule.Isometry
    A.toFiniteBilinearModule B.toFiniteBilinearModule) (a : A)
    (ha : A.toFiniteBilinearModule.pairing a = discrepancy f) :
    expCircle (A.quadratic a) * B.gaussSum = A.gaussSum := by
  let := Fintype.ofFinite A
  let := Fintype.ofFinite B
  have hax (x : A) : A.toFiniteBilinearModule.pairing a x =
      B.quadratic (f x) - A.quadratic x := DFunLike.congr_fun ha x
  rw [gaussSum_eq_sum, gaussSum_eq_sum, Finset.mul_sum]
  calc
    ∑ y : B, expCircle (A.quadratic a) * expCircle (B.quadratic y)
        = ∑ x : A, expCircle (A.quadratic (x + a)) := by
      refine (Fintype.sum_equiv f.toAddEquiv.toEquiv _ _ fun x ↦ ?_).symm
      rw [← AddChar.map_add_eq_mul, QuadraticMap.map_add A.quadratic, A.polar_eq_pairing,
        A.toFiniteBilinearModule.pairing_comm, hax]
      congr 1
      abel
    _ = ∑ x : A, expCircle (A.quadratic x) :=
      Equiv.sum_comp (Equiv.addRight a) (fun x ↦ expCircle (A.quadratic x))

private theorem quadratic_eq_zero_of_discrepancy (hA : A.IsNondegenerate)
    (f : FiniteBilinearModule.Isometry A.toFiniteBilinearModule B.toFiniteBilinearModule)
    (h : A.gaussSign = B.gaussSign) (a : A)
    (ha : A.toFiniteBilinearModule.pairing a = discrepancy f) : A.quadratic a = 0 := by
  have hsum : A.gaussSum = B.gaussSum := by
    rw [hA.gaussSum_eq, IsNondegenerate.gaussSum_eq (f.isNondegenerate hA),
      Nat.card_congr f.toAddEquiv.toEquiv, h]
  have hne : A.gaussSum ≠ 0 := by
    intro hz
    have hc := hA.gaussSum_mul_conj
    rw [hz, zero_mul] at hc
    exact (Nat.cast_ne_zero.mpr Nat.card_pos.ne' : (Nat.card A : ℂ) ≠ 0) hc.symm
  apply expCircle_eq_one_iff.mp
  apply mul_right_cancel₀ hne
  simpa only [← hsum, one_mul] using gaussSum_discrepancy f a ha

/-- **Correct a bilinear isometry to a quadratic isometry.** For a nondegenerate source, equal
Gauss-sum invariants ensure that an isotropic two-torsion involution corrects the discrepancy.
The target is nondegenerate because its polar form is isometric to the source's. -/
noncomputable def isometryOfBilinearIsometry (hA : A.IsNondegenerate)
    (f : FiniteBilinearModule.Isometry A.toFiniteBilinearModule B.toFiniteBilinearModule)
    (h : A.gaussSign = B.gaussSign) : Isometry A B := by
  classical
  let a := (A.toFiniteBilinearModule.adjointEquiv hA).symm (discrepancy f)
  have ha : A.toFiniteBilinearModule.pairing a = discrepancy f := by
    rw [← FiniteBilinearModule.adjointEquiv_apply A.toFiniteBilinearModule hA]
    exact (A.toFiniteBilinearModule.adjointEquiv hA).apply_symm_apply (discrepancy f)
  have hax (x : A) : A.toFiniteBilinearModule.pairing a x = discrepancy f x :=
    DFunLike.congr_fun ha x
  have htwo : 2 • a = 0 := by
    apply FiniteBilinearModule.IsNondegenerate.injective A.toFiniteBilinearModule hA
    ext x
    rw [FiniteBilinearModule.pairing_nsmul_left, hax,
      A.toFiniteBilinearModule.pairing_zero_left]
    simpa only [ofNat_zsmul] using two_zsmul_discrepancy f x
  have hqa := quadratic_eq_zero_of_discrepancy hA f h a ha
  have hda : discrepancy f a = 0 := by
    rw [← hax, ← A.polar_eq_pairing, QuadraticMap.polar_self, hqa, smul_zero]
  let g : A →+ A := AddMonoidHom.id A + correction (discrepancy f)
    (two_zsmul_discrepancy f) a htwo
  have hg (x : A) : g (g x) = x := by
    have haa : a + a = 0 := by simpa only [two_nsmul] using htwo
    by_cases hx : discrepancy f x = 0
    · simp [g, correction, hx]
    · simp [g, correction, hx, map_add, hda, add_assoc, haa]
  let e : A ≃+ A := AddEquiv.ofBijective g (Function.Involutive.bijective hg)
  refine { toLinearEquiv := (e.trans f.toAddEquiv).toIntLinearEquiv
           map_app' := fun x ↦ ?_ }
  -- The local equivalence was defined from `g`; expose its function through the ℤ-linear coercion.
  change B.quadratic (f (g x)) = A.quadratic x
  have hq (z : A) : B.quadratic (f z) = A.quadratic z + discrepancy f z := by
    -- This is the defining equation of the private discrepancy character, rearranged additively.
    change B.quadratic (f z) = A.quadratic z + (B.quadratic (f z) - A.quadratic z)
    abel
  by_cases hx : discrepancy f x = 0
  · simpa [g, correction, hx] using hq x
  · -- Expose the local corrective homomorphism to use the nonzero-character branch.
    change B.quadratic (f (x + if discrepancy f x = 0 then 0 else a)) = _
    rw [ite_eq_right hx, hq, QuadraticMap.map_add A.quadratic, A.polar_eq_pairing,
      A.toFiniteBilinearModule.pairing_comm, hax, hqa, map_add, hda]
    have hd : discrepancy f x + discrepancy f x = 0 := by
      simpa only [two_zsmul] using two_zsmul_discrepancy f x
    simp only [add_zero]
    rw [add_assoc, hd, add_zero]

/-- **Nikulin's comparison theorem.** Two nondegenerate finite quadratic modules are isometric
exactly when their polar bilinear modules are isometric and their Gauss-sum invariants agree. -/
theorem nonempty_isometry_iff_bilinear_isometry_and_gaussSign_eq
    (hA : A.IsNondegenerate) :
    Nonempty (Isometry A B) ↔
      Nonempty (FiniteBilinearModule.Isometry A.toFiniteBilinearModule B.toFiniteBilinearModule) ∧
        A.gaussSign = B.gaussSign := by
  constructor
  · rintro ⟨f⟩
    exact ⟨⟨f.toFiniteBilinearModule⟩, f.gaussSign_eq⟩
  · rintro ⟨⟨f⟩, h⟩
    exact ⟨isometryOfBilinearIsometry hA f h⟩

/-- **On a module of odd order, every bilinear isometry is a quadratic isometry.** The discrepancy
character `q_B(f x) - q_A(x)` is killed both by `2` and by `#A`, hence vanishes; neither
nondegeneracy nor equality of Gauss-sum invariants is required. -/
def isometryOfBilinearIsometryOfOdd (hm : Odd (Nat.card A))
    (f : FiniteBilinearModule.Isometry A.toFiniteBilinearModule B.toFiniteBilinearModule) :
    Isometry A B where
  toLinearEquiv := f.toAddEquiv.toIntLinearEquiv
  map_app' x := by
    have h2 : 2 • discrepancy f x = 0 := by simpa only [ofNat_zsmul] using two_zsmul_discrepancy f x
    have hm0 : Nat.card A • discrepancy f x = 0 := by
      rw [← map_nsmul, card_nsmul_eq_zero', map_zero]
    exact sub_eq_zero.mp ((nsmul_eq_zero_iff_of_coprime hm.coprime_two_right).mp ⟨hm0, h2⟩)

@[simp]
theorem isometryOfBilinearIsometryOfOdd_apply (hm : Odd (Nat.card A))
    (f : FiniteBilinearModule.Isometry A.toFiniteBilinearModule B.toFiniteBilinearModule) (x : A) :
    isometryOfBilinearIsometryOfOdd hm f x = f x := by
  rfl

/-- **Polar pairings classify odd-order finite quadratic modules.** Two finite quadratic modules of
odd order are isometric if and only if their polar bilinear modules are isometric. -/
theorem nonempty_isometry_iff_bilinear_isometry_of_odd (hm : Odd (Nat.card A)) :
    Nonempty (Isometry A B) ↔
      Nonempty (FiniteBilinearModule.Isometry A.toFiniteBilinearModule B.toFiniteBilinearModule) :=
  ⟨fun ⟨f⟩ ↦ ⟨f.toFiniteBilinearModule⟩, fun ⟨f⟩ ↦ ⟨isometryOfBilinearIsometryOfOdd hm f⟩⟩

end TauCeti.FiniteQuadraticModule

namespace TauCeti.FiniteBilinearModule

/-- **The canonical quadratic refinement of a finite bilinear module of odd order**, given by
`q(x) = ((#B + 1) / 2) • b(x, x)`. Since `2 * ((#B + 1) / 2) = #B + 1` acts as the identity on a
group of odd order `#B`, the polar form of `q` is `b`, and every quadratic refinement of `b` is
isometric to it (`TauCeti.FiniteQuadraticModule.isometryToFiniteQuadraticModuleOfOdd`). -/
@[expose] noncomputable def toFiniteQuadraticModuleOfOdd (B : FiniteBilinearModule)
    (hm : Odd (Nat.card B)) : FiniteQuadraticModule where
  toFiniteBilinearModule := B
  quadratic := LinearMap.BilinMap.toQuadraticMap (((Nat.card B + 1) / 2 : ℕ) • B.toBilin)
  polar_eq_pairing' x y := by
    obtain ⟨t, ht⟩ := hm
    have hk : 2 * ((Nat.card B + 1) / 2) = Nat.card B + 1 := by omega
    rw [LinearMap.BilinMap.polar_toQuadraticMap]
    simp only [LinearMap.smul_apply, toBilin_apply, B.pairing_comm y x]
    rw [← two_nsmul, ← mul_nsmul', hk, add_nsmul, one_nsmul, ← pairing_nsmul_left,
      card_nsmul_eq_zero', B.pairing_zero_left, zero_add]

/-- The polar bilinear module of `toFiniteQuadraticModuleOfOdd` is the original module. -/
theorem toFiniteQuadraticModuleOfOdd_toFiniteBilinearModule (B : FiniteBilinearModule)
    (hm : Odd (Nat.card B)) : (B.toFiniteQuadraticModuleOfOdd hm).toFiniteBilinearModule = B :=
  rfl

/-- Evaluating the canonical odd-order quadratic refinement gives `((#B + 1) / 2) • b(x, x)`. -/
@[simp]
theorem toFiniteQuadraticModuleOfOdd_quadratic (B : FiniteBilinearModule)
    (hm : Odd (Nat.card B)) (x : B) :
    (B.toFiniteQuadraticModuleOfOdd hm).quadratic x = ((Nat.card B + 1) / 2) • B.pairing x x :=
  (LinearMap.BilinMap.toQuadraticMap_apply _ x).trans (by simp)

/-- A bilinear isometry between modules of odd order preserves the Gauss-sum invariant of their
canonical quadratic refinements. -/
theorem Isometry.gaussSign_toFiniteQuadraticModuleOfOdd_eq {A B : FiniteBilinearModule}
    (hm : Odd (Nat.card A)) (f : Isometry A B) :
    (A.toFiniteQuadraticModuleOfOdd hm).gaussSign =
      (B.toFiniteQuadraticModuleOfOdd (Nat.card_congr f.toAddEquiv.toEquiv ▸ hm)).gaussSign :=
  (FiniteQuadraticModule.isometryOfBilinearIsometryOfOdd hm f).gaussSign_eq

end TauCeti.FiniteBilinearModule

namespace TauCeti.FiniteQuadraticModule

/-- Every finite quadratic module of odd order is canonically isometric to the canonical quadratic
refinement of its polar bilinear module. -/
noncomputable def isometryToFiniteQuadraticModuleOfOdd (A : FiniteQuadraticModule)
    (hm : Odd (Nat.card A)) :
    Isometry A (A.toFiniteBilinearModule.toFiniteQuadraticModuleOfOdd hm) :=
  isometryOfBilinearIsometryOfOdd hm (FiniteBilinearModule.Isometry.refl _)

@[simp]
theorem isometryToFiniteQuadraticModuleOfOdd_apply (A : FiniteQuadraticModule)
    (hm : Odd (Nat.card A)) (x : A) :
    A.isometryToFiniteQuadraticModuleOfOdd hm x = x :=
  (isometryOfBilinearIsometryOfOdd_apply hm (FiniteBilinearModule.Isometry.refl _) x).trans
    (FiniteBilinearModule.Isometry.refl_apply _ x)

end TauCeti.FiniteQuadraticModule
