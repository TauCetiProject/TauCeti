/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Sol.Basic
public import TauCeti.GroupTheory.SpecificGroups.Dihedral.Basic

/-!
# Dihedral isometries of Sol

The maps `(x, y, z) ↦ (x, -y, z)` and `(x, y, z) ↦ (y, x, -z)` preserve the
metric `e^{2z} dx² + e^{-2z} dy² + dz²`. They generate a faithful dihedral group of
eight Riemannian isometries fixing the identity of Sol. Together with left translations,
these give the candidates for the full isometry group. This file constructs the finite
subgroup; it does not assert that every isometry fixing the identity belongs to it.

The homomorphism and its injectivity reuse `TauCeti.dihedralHom` and
`TauCeti.dihedralHom_injective`.

## References

* P. Scott, *The geometries of 3-manifolds*, Bull. London Math. Soc. 15 (1983),
  401–487, Section 4, pp. 470–471 (the geometry Sol and its eight linear isometries).
-/

public section

noncomputable section

open Bundle Manifold Real
open scoped ContDiff Manifold

namespace TauCeti.Sol

private def reflectionL : (ℝ × ℝ × ℝ) ≃L[ℝ] ℝ × ℝ × ℝ :=
  (ContinuousLinearEquiv.refl ℝ ℝ).prodCongr
    ((ContinuousLinearEquiv.neg ℝ).prodCongr (ContinuousLinearEquiv.refl ℝ ℝ))

private theorem reflectionL_apply (v : ℝ × ℝ × ℝ) :
    reflectionL v = (v.1, -v.2.1, v.2.2) := rfl

private def axisSwapL : (ℝ × ℝ × ℝ) ≃L[ℝ] ℝ × ℝ × ℝ :=
  (ContinuousLinearEquiv.prodAssoc ℝ ℝ ℝ ℝ).symm.trans
    (((ContinuousLinearEquiv.prodComm ℝ ℝ ℝ).prodCongr
      (ContinuousLinearEquiv.neg ℝ)).trans (ContinuousLinearEquiv.prodAssoc ℝ ℝ ℝ ℝ))

private theorem axisSwapL_apply (v : ℝ × ℝ × ℝ) :
    axisSwapL v = (v.2.1, v.1, -v.2.2) := rfl

-- Sol has the topology and charts of its coordinate space. This helper packages linear
-- involutions satisfying the explicit metric identity, without changing that metric.
private def isometryOfInvolution (L : (ℝ × ℝ × ℝ) →L[ℝ] ℝ × ℝ × ℝ)
    (hL : Function.Involutive L)
    (hmetric : ∀ p v w : ℝ × ℝ × ℝ,
      exp (2 * (L p).2.2) * (L v).1 * (L w).1 +
        exp (-2 * (L p).2.2) * (L v).2.1 * (L w).2.1 + (L v).2.2 * (L w).2.2 =
      exp (2 * p.2.2) * v.1 * w.1 + exp (-2 * p.2.2) * v.2.1 * w.2.1 + v.2.2 * w.2.2) :
    Isom 𝓘(ℝ, ℝ × ℝ × ℝ) Sol where
  toFun := toProd.symm ∘ L ∘ toProd
  invFun := toProd.symm ∘ L ∘ toProd
  left_inv p := by
    simp only [Function.comp_apply, Equiv.apply_symm_apply]
    rw [hL (toProd p), Equiv.symm_apply_apply]
  right_inv p := by
    simp only [Function.comp_apply, Equiv.apply_symm_apply]
    rw [hL (toProd p), Equiv.symm_apply_apply]
  contMDiff_toFun := by
    -- The anonymous equivalence's coercion is its specified forward function.
    change ContMDiff 𝓘(ℝ, ℝ × ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ × ℝ) ∞ (toProd.symm ∘ L ∘ toProd)
    simpa only [coe_toProdDiffeomorph, coe_toProdDiffeomorph_symm] using
      toProdDiffeomorph.symm.contMDiff.comp
        (L.contDiff.contMDiff.comp toProdDiffeomorph.contMDiff)
  contMDiff_invFun := by
    -- Both functions of the anonymous equivalence are the same involution.
    change ContMDiff 𝓘(ℝ, ℝ × ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ × ℝ) ∞ (toProd.symm ∘ L ∘ toProd)
    simpa only [coe_toProdDiffeomorph, coe_toProdDiffeomorph_symm] using
      toProdDiffeomorph.symm.contMDiff.comp
        (L.contDiff.contMDiff.comp toProdDiffeomorph.contMDiff)
  inner_mfderiv' p v w := by
    -- The goal contains the coercion of the structure literal under construction.
    -- Give it its specified coordinate function before applying the chain rule.
    change inner ℝ (mfderiv 𝓘(ℝ, ℝ × ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ × ℝ)
      (toProd.symm ∘ L ∘ toProd) p v)
      (mfderiv 𝓘(ℝ, ℝ × ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ × ℝ)
        (toProd.symm ∘ L ∘ toProd) p w) = inner ℝ v w
    have hf : MDifferentiable 𝓘(ℝ, ℝ × ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ × ℝ) toProd := by
      simpa only [coe_toProdDiffeomorph] using toProdDiffeomorph.mdifferentiable (by simp)
    have hg : MDifferentiable 𝓘(ℝ, ℝ × ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ × ℝ) toProd.symm := by
      simpa only [coe_toProdDiffeomorph_symm] using
        toProdDiffeomorph.symm.mdifferentiable (by simp)
    have hd (v : TangentSpace 𝓘(ℝ, ℝ × ℝ × ℝ) p) :
        tangentSpaceCastModel 𝓘(ℝ, ℝ × ℝ × ℝ) (toProd.symm (L (toProd p)))
          (mfderiv 𝓘(ℝ, ℝ × ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ × ℝ) (toProd.symm ∘ L ∘ toProd) p v) =
        L (tangentSpaceCastModel 𝓘(ℝ, ℝ × ℝ × ℝ) p v) := by
      rw [mfderiv_comp p (hg _) (L.differentiable.mdifferentiable.comp hf p)]
      simp only [ContinuousLinearMap.comp_apply, Function.comp_apply,
        tangentSpaceCastModel_mfderiv_toProd_symm]
      rw [mfderiv_comp p L.differentiableAt.mdifferentiableAt (hf p)]
      rw [L.hasFDerivAt.hasMFDerivAt.mfderiv]
      exact congrArg L (mfderiv_toProd_apply p v)
    rw [inner_def, inner_def]
    simp only [Function.comp_apply]
    rw [hd v, hd w]
    simpa only [z_toProd_symm, snd_snd_toProd, Function.comp_apply] using
      hmetric (toProd p) (tangentSpaceCastModel 𝓘(ℝ, ℝ × ℝ × ℝ) p v)
        (tangentSpaceCastModel 𝓘(ℝ, ℝ × ℝ × ℝ) p w)

/-- Reflection in the `xz`-plane, as a Riemannian isometry of Sol. -/
def reflection : Isom 𝓘(ℝ, ℝ × ℝ × ℝ) Sol :=
  isometryOfInvolution reflectionL.toContinuousLinearMap
    (fun v => by
      simpa only [ContinuousLinearEquiv.coe_coe, reflectionL,
        ContinuousLinearEquiv.prodCongr_symm, ContinuousLinearEquiv.refl_symm,
        ContinuousLinearEquiv.symm_neg] using reflectionL.symm_apply_apply v)
    (fun p v w => by simp only [ContinuousLinearEquiv.coe_coe, reflectionL_apply]; ring)

/-- Reflection negates the `y` coordinate and preserves the other two coordinates. -/
@[simp] theorem reflection_apply (p : Sol) : reflection p = mk p.x (-p.y) p.z := by
  calc
    reflection p = toProd.symm (reflectionL (toProd p)) := (rfl)
    _ = mk p.x (-p.y) p.z := by
      apply toProd.injective
      simp [reflectionL_apply]

/-- Interchange the horizontal coordinates and reverse the height, as a Riemannian
isometry of Sol. -/
def axisSwap : Isom 𝓘(ℝ, ℝ × ℝ × ℝ) Sol :=
  isometryOfInvolution axisSwapL.toContinuousLinearMap
    (fun v => by
      simpa only [ContinuousLinearEquiv.coe_coe, axisSwapL,
        ContinuousLinearEquiv.symm_trans_apply, ContinuousLinearEquiv.trans_apply,
        ContinuousLinearEquiv.prodCongr_symm, ContinuousLinearEquiv.prodComm_symm,
        ContinuousLinearEquiv.symm_neg, ContinuousLinearEquiv.symm_symm] using
          axisSwapL.symm_apply_apply v)
    (fun p v w => by simp only [ContinuousLinearEquiv.coe_coe, axisSwapL_apply]; ring_nf)

/-- The horizontal interchange is accompanied by reversal of the height. -/
@[simp] theorem axisSwap_apply (p : Sol) : axisSwap p = mk p.y p.x (-p.z) := by
  calc
    axisSwap p = toProd.symm (axisSwapL (toProd p)) := (rfl)
    _ = mk p.y p.x (-p.z) := by
      apply toProd.injective
      simp [axisSwapL_apply]

/-- Reflection in the `xz`-plane preserves the solvable group product of Sol. -/
theorem reflection_map_mul (p q : Sol) : reflection (p * q) = reflection p * reflection q := by
  ext <;> simp [add_comm]

/-- Swapping the horizontal axes and reversing height preserves the group product of Sol. -/
theorem axisSwap_map_mul (p q : Sol) : axisSwap (p * q) = axisSwap p * axisSwap q := by
  ext <;> simp [add_comm]

/-- Reflection in the `xz`-plane is an involution. -/
@[simp] theorem reflection_mul_self : reflection * reflection = 1 := by
  apply RiemannianIsometry.ext
  intro p
  simp [RiemannianIsometry.mul_apply, RiemannianIsometry.one_apply]

/-- Interchanging the horizontal coordinates and reversing the height is an involution. -/
@[simp] theorem axisSwap_mul_self : axisSwap * axisSwap = 1 := by
  apply RiemannianIsometry.ext
  intro p
  simp [RiemannianIsometry.mul_apply, RiemannianIsometry.one_apply]

/-- The product of the two reflections has order four. -/
@[simp] theorem orderOf_reflection_mul_axisSwap : orderOf (reflection * axisSwap) = 4 := by
  have hfour : (reflection * axisSwap) ^ 4 = 1 := by
    apply RiemannianIsometry.ext
    intro p
    simp [pow_succ, RiemannianIsometry.mul_apply, RiemannianIsometry.one_apply]
  have htwo : (reflection * axisSwap) ^ 2 ≠ 1 := by
    intro h
    have := congrArg Sol.x (DFunLike.congr_fun h (mk 1 0 0))
    norm_num [pow_succ] at this
  exact orderOf_eq_prime_pow (p := 2) (n := 1) (by simpa using htwo) (by simpa using hfour)

private theorem reflection_ne_one : reflection ≠ 1 := by
  intro h
  have := congrArg Sol.y (DFunLike.congr_fun h (mk 0 1 0))
  norm_num at this

private theorem axisSwap_ne_one : axisSwap ≠ 1 := by
  intro h
  have := congrArg Sol.x (DFunLike.congr_fun h (mk 1 0 0))
  norm_num at this

/-- The dihedral action by the eight linear isometries of Sol.
The basic rotation maps to `reflection * axisSwap` and the basic reflection to `reflection`. -/
def dihedralToIsom : DihedralGroup 4 →* Isom 𝓘(ℝ, ℝ × ℝ × ℝ) Sol :=
  dihedralHom reflection_mul_self axisSwap_mul_self
    (orderOf_reflection_mul_axisSwap ▸ pow_orderOf_eq_one (reflection * axisSwap))

/-- Dihedral rotations act by powers of the horizontal quarter-turn with height reversal. -/
@[simp] theorem dihedralToIsom_r (i : ZMod 4) :
    dihedralToIsom (.r i) = (reflection * axisSwap) ^ (ZMod.cast i : ℤ) :=
  dihedralHom_r _ _ _ i

/-- Dihedral reflections act by the `xz`-reflection followed by a dihedral rotation. -/
@[simp] theorem dihedralToIsom_sr (i : ZMod 4) :
    dihedralToIsom (.sr i) = reflection * (reflection * axisSwap) ^ (ZMod.cast i : ℤ) :=
  dihedralHom_sr _ _ _ i

/-- The eight dihedral elements give distinct isometries of Sol. -/
theorem dihedralToIsom_injective : Function.Injective dihedralToIsom :=
  dihedralHom_injective reflection_mul_self axisSwap_mul_self reflection_ne_one axisSwap_ne_one
    orderOf_reflection_mul_axisSwap

/-- The dihedral image is exactly the subgroup generated by the two linear reflections. -/
theorem range_dihedralToIsom :
    dihedralToIsom.range = Subgroup.closure {reflection, axisSwap} :=
  range_dihedralHom _ _ _

/-- Every isometry in the dihedral action fixes the identity of Sol. -/
@[simp] theorem dihedralToIsom_apply_one (g : DihedralGroup 4) : dihedralToIsom g 1 = 1 := by
  have hr : reflection ∈ MulAction.stabilizer (Isom 𝓘(ℝ, ℝ × ℝ × ℝ) Sol) (1 : Sol) := by
    simpa [MulAction.mem_stabilizer_iff, RiemannianIsometry.smul_def] using mk_x_y_z (1 : Sol)
  have ht : axisSwap ∈ MulAction.stabilizer (Isom 𝓘(ℝ, ℝ × ℝ × ℝ) Sol) (1 : Sol) := by
    simpa [MulAction.mem_stabilizer_iff, RiemannianIsometry.smul_def] using mk_x_y_z (1 : Sol)
  have hle : dihedralToIsom.range ≤
      MulAction.stabilizer (Isom 𝓘(ℝ, ℝ × ℝ × ℝ) Sol) (1 : Sol) := by
    rw [range_dihedralToIsom, Subgroup.closure_le]
    rintro _ (rfl | rfl)
    exacts [hr, ht]
  exact MulAction.mem_stabilizer_iff.mp (hle ⟨g, rfl⟩)

/-- Every dihedral isometry preserves the solvable group product of Sol. -/
@[simp]
theorem dihedralToIsom_map_mul (g : DihedralGroup 4) (p q : Sol) :
    dihedralToIsom g (p * q) = dihedralToIsom g p * dihedralToIsom g q := by
  have hg : dihedralToIsom g ∈ Subgroup.closure {reflection, axisSwap} := by
    rw [← range_dihedralToIsom]
    exact ⟨g, rfl⟩
  have h : ∀ p q : Sol, dihedralToIsom g (p * q) =
      dihedralToIsom g p * dihedralToIsom g q := by
    refine Subgroup.closure_induction
      (p := fun f _ => ∀ p q : Sol, f (p * q) = f p * f q) ?_ ?_ ?_ ?_ hg
    · intro f hf
      rcases hf with rfl | rfl
      exacts [reflection_map_mul, axisSwap_map_mul]
    · simp
    · intro f k _ _ hf hk p q
      simp only [RiemannianIsometry.mul_apply, hk, hf]
    · intro f _ hf
      -- Mathlib transports multiplicativity across a two-sided inverse.
      simpa only [RiemannianIsometry.inv_apply, MulHom.inverse, MulHom.coe_mk] using
        (MulHom.inverse ⟨f, hf⟩ f.symm f.symm_apply_apply f.apply_symm_apply).map_mul
  exact h p q

end TauCeti.Sol
