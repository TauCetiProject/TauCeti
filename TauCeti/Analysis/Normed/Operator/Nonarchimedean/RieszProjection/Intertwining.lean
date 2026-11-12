/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Operator.Nonarchimedean.RieszProjection.Splitting
public import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Intertwining

/-!
# Functoriality of Riesz splittings

A linear map intertwining two operators also intertwines their Riesz projectors at the same
scalar, even when the nilpotence bounds differ. It therefore carries the nilpotent spectral
summand and its complementary summand into the corresponding summands of the target. The
complementary inverses are intertwined as well. Continuity of the intertwiner is unnecessary.

In particular every bounded operator commuting with an operator commutes with its Riesz
projector and complementary inverse. These results allow commuting actions to restrict to the
spectral splitting, without choosing bases or assuming that the coefficient ring is a field.

## References

* J.-P. Serre, *Endomorphismes complètement continus des espaces de Banach p-adiques*,
  Publ. Math. IHÉS **12** (1962), 69–85, §7.
* R. Coleman, *p-adic Banach spaces and families of modular forms*, Invent. Math. **127**
  (1997), 417–479, Appendix A4.
-/

public section

open scoped ZeroAtInfty TauCeti.RingOpNorm

namespace ContinuousLinearMap.IsRieszProjection

variable {I J R : Type*} [TopologicalSpace I] [TopologicalSpace J]
  [NormedCommRing R] [TauCeti.NormedRing.IsTate R]
  {u E : C₀(I, R) →L[R] C₀(I, R)} {v F : C₀(J, R) →L[R] C₀(J, R)}
  {a : R} {h k : ℕ}

/-- An intertwiner carries Riesz projectors at the same scalar to one another. The two
nilpotence bounds may differ, and the intertwiner need not be continuous. -/
theorem semiconj (hE : IsRieszProjection u a h E) (hF : IsRieszProjection v a k F)
    (f : C₀(I, R) →ₗ[R] C₀(J, R)) (hf : Function.Semiconj f u v) :
    Function.Semiconj f E F := by
  -- A common bound identifies both splittings with kernels and ranges of the same power.
  let n := max h k
  have hEn := hE.of_le (Nat.le_max_left h k)
  have hFn := hF.of_le (Nat.le_max_right h k)
  intro x
  have hfixed : F (f (E x)) = f (E x) := by
    apply (LinearMap.IsIdempotentElem.mem_range_iff
      (ContinuousLinearMap.IsIdempotentElem.toLinearMap hF.isIdempotentElem)).mp
    rw [hFn.range_eq_ker]
    apply LinearMap.mem_ker.mpr
    simp only [coe_coe]
    rw [← hf.one_sub_smul_pow a n]
    have hz := congr($(hEn.pow_mul_eq_zero) x)
    simpa only [mul_apply_eq_comp, zero_apply, map_zero, coe_coe] using congr(f $hz)
  -- The remaining part lies in the stable range, which the intertwiner also preserves.
  have hzero : F (f (x - E x)) = 0 := by
    have hx : x - E x ∈ E.ker := by
      apply LinearMap.mem_ker.mpr
      have hid := congr($(hE.isIdempotentElem.eq) x)
      simpa only [coe_coe, map_sub, mul_apply_eq_comp, sub_eq_zero] using hid.symm
    rw [← hE.range_pow_eq_ker (n := n) (Nat.le_max_left h k)] at hx
    obtain ⟨y, hy⟩ := hx
    simp only [coe_coe] at hy
    have hy' : f (x - E x) = ((1 - a • v) ^ n : C₀(J, R) →L[R] C₀(J, R)) (f y) := by
      rw [← hf.one_sub_smul_pow a n, hy]
    apply LinearMap.mem_ker.mp
    rw [← hF.range_pow_eq_ker (n := n) (Nat.le_max_right h k)]
    exact ⟨f y, hy'.symm⟩
  rw [map_sub, map_sub, hfixed, sub_eq_zero] at hzero
  exact hzero.symm

/-- An intertwiner sends the nilpotent spectral summand into the corresponding summand. -/
theorem mapsTo_range_of_semiconj (hE : IsRieszProjection u a h E)
    (hF : IsRieszProjection v a k F) (f : C₀(I, R) →ₗ[R] C₀(J, R))
    (hf : Function.Semiconj f u v) : Set.MapsTo f E.range F.range := by
  rintro _ ⟨x, rfl⟩
  exact ⟨f x, (hE.semiconj hF f hf x).symm⟩

/-- An intertwiner sends the complementary spectral summand into the corresponding summand. -/
theorem mapsTo_ker_of_semiconj (hE : IsRieszProjection u a h E)
    (hF : IsRieszProjection v a k F) (f : C₀(I, R) →ₗ[R] C₀(J, R))
    (hf : Function.Semiconj f u v) : Set.MapsTo f E.ker F.ker := by
  intro x hx
  apply LinearMap.mem_ker.mpr
  simp only [coe_coe]
  have hx' : E x = 0 := LinearMap.mem_ker.mp hx
  rw [← hE.semiconj hF f hf, hx', map_zero]

/-- Intertwiners also carry the complementary inverses of the spectral operators to one
another. This includes order zero, when the complementary inverse is the full inverse. -/
theorem semiconj_inverse (hE : IsRieszProjection u a h E) (hF : IsRieszProjection v a k F)
    (f : C₀(I, R) →ₗ[R] C₀(J, R)) (hf : Function.Semiconj f u v) :
    Function.Semiconj f hE.inverse hF.inverse := by
  have hEF := hE.semiconj hF f hf
  intro x
  have hker : f (hE.inverse x) ∈ F.ker := by
    apply LinearMap.mem_ker.mpr
    simp only [coe_coe]
    rw [← hEF]
    have hz := congr($(hE.mul_inverse_eq_zero) x)
    simpa only [mul_apply_eq_comp, zero_apply, map_zero] using congr(f $hz)
  calc f (hE.inverse x) = hF.inverse ((1 - a • v) (f (hE.inverse x))) :=
        (hF.inverse_one_sub_smul_apply hker).symm
    _ = hF.inverse (f ((1 - a • u) (hE.inverse x))) := by
        rw [hf.one_sub_smul a]
    _ = hF.inverse (f (x - E x)) := by
        have hz := congr($(hE.one_sub_smul_mul_inverse) x)
        exact congrArg (fun y ↦ hF.inverse (f y)) hz
    _ = hF.inverse (f x - F (f x)) := by rw [map_sub, hEF x]
    _ = hF.inverse (f x) := by
        rw [map_sub, ← mul_apply_eq_comp, hF.inverse_mul_eq_zero, zero_apply, sub_zero]

/-- A bounded operator commuting with `u` commutes with every Riesz projector of `u`. -/
theorem commute_of_commute (hE : IsRieszProjection u a h E)
    {w : C₀(I, R) →L[R] C₀(I, R)} (hw : Commute w u) : Commute w E := by
  apply ContinuousLinearMap.ext
  intro x
  exact hE.semiconj hE w.toLinearMap (fun x ↦ congr($(hw.eq) x)) x

/-- A bounded operator commuting with `u` commutes with the complementary inverse of any
Riesz projector of `u`. -/
theorem commute_inverse_of_commute (hE : IsRieszProjection u a h E)
    {w : C₀(I, R) →L[R] C₀(I, R)} (hw : Commute w u) : Commute w hE.inverse := by
  apply ContinuousLinearMap.ext
  intro x
  exact hE.semiconj_inverse hE w.toLinearMap (fun x ↦ congr($(hw.eq) x)) x

end ContinuousLinearMap.IsRieszProjection
