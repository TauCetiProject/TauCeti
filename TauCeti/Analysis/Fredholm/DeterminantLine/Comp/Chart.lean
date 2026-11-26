/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fredholm.DeterminantLine.DirectSum
public import TauCeti.LinearAlgebra.Determinant.Comp.Basic
import TauCeti.Algebra.Ring.Parity
import TauCeti.Data.Fin.Tuple.Basic
import TauCeti.LinearAlgebra.LinearIndependent.Fin
import TauCeti.LinearAlgebra.TensorProduct.Cyclic
import TauCeti.RingTheory.PicardGroup.Contraction

/-!
# Composition of Fredholm determinant lines in kernel charts

For linear maps `f` and `g` with finite-dimensional kernels and cokernels, the kernel–cokernel
sequence `0 → ker f → ker (g ∘ f) → ker g → coker f → coker (g ∘ f) → coker g → 0` gives the
canonical composition law `det (g ∘ f) ≃ det f ⊗ det g` of determinant lines
(`LinearMap.detLineCompEquiv`). This file compares it with the kernel charts through which the
determinant lines of a continuous family of Fredholm operators are compared and oriented
(`ContinuousLinearMap.detLineChartEquiv`). The consequence for continuous families of operators
and for orientation transport is in `TauCeti.Analysis.Fredholm.DeterminantLine.Comp.Family`.

**The composite chart.** Kernel charts `(D₁, q₁)` of `f : E → F` and `(D₂, q₂)` of `g : F → P`,
with `D₁ : Λ₁ → F`, `q₁ : E × Λ₁ → G₁`, `D₂ : Λ₂ → P` and `q₂ : F × Λ₂ → G₂`, give the kernel chart
of `g ∘ f` with stabilizer `(l₁, l₂) ↦ g (D₁ l₁) + D₂ l₂` and coordinate
`(x, (l₁, l₂)) ↦ (q₁ (x, l₁), q₂ (f x + D₁ l₁, l₂))` (`ContinuousLinearMap.compKerCoord`,
`ContinuousLinearMap.IsInvertible.prod_coprod_compKerCoord`): `(x, l₁, l₂)` lies in the stabilized
kernel of `g ∘ f` exactly when `(f x + D₁ l₁, l₂)` lies in that of `g`, and the stabilized kernel of
`f` is the kernel of this map.

**The composition law in the composite chart.** In the composite chart, the element
`(detLineCompEquiv f g).symm (v ⊗ w)` of the determinant line of `g ∘ f` is read as the product of
the readings of `v` and `w` (`TauCeti.detLineTensorDualProdEquiv`), up to a sign
(`ContinuousLinearMap.detLineChartEquiv_detLineCompEquiv_symm`). Its proof evaluates the three
stabilization isomorphisms and the composition law on exterior products of families adapted to all
four exact sequences at once. Write `r` and `t` for the ranks of the maps `ker (g ∘ f) → ker g` and
`coker f → coker (g ∘ f)` of the kernel–cokernel sequence. Normalized by
`(-1) ^ (dim coker f * r + t * dim coker g)`, the composition law is read in the composite chart as
the product of the readings times `(-1) ^ (dim Λ₁ * (dim G₂ + dim Λ₂))`
(`ContinuousLinearMap.detLineChartEquiv_neg_one_pow_smul_comp`), a sign depending only on the
charts. The normalization is needed because `r`, `t` and the cokernel dimensions jump along a
family of operators.

## Main definitions

* `ContinuousLinearMap.compKerCoord`: the kernel coordinate of the composite of two kernel charts.

## Main results

* `ContinuousLinearMap.IsInvertible.prod_coprod_compKerCoord`: the composite of kernel charts is a
  kernel chart.
* `ContinuousLinearMap.detLineChartEquiv_detLineCompEquiv_symm`: the composite chart reads the
  composition law as the product of the readings, up to sign.
* `ContinuousLinearMap.detLineChartEquiv_neg_one_pow_smul_comp`: after normalization the sign
  depends only on the charts.

## References

* A. Zinger, *The determinant line bundle for Fredholm operators: construction, properties, and
  classification*, Math. Scand. 118 (2016), 203–268, arXiv:1304.6368 (stabilizations, and the
  continuity of the composition isomorphisms of determinant lines).
* D. McDuff, D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  AMS Colloquium Publications 52, 2012, Section A.2 (determinant line bundles).
-/

public section

open Module TensorProduct

namespace ContinuousLinearMap

-- Stabilized kernels `(D₁.coprod D₂).ker` are finite-dimensional when `D₁.ker` and `Λ` are.
attribute [local instance] finiteDimensional_ker_coprod

section Chart

variable {𝕜 E F P Λ₁ Λ₂ G₁ G₂ : Type*} [Field 𝕜] [AddCommGroup E] [Module 𝕜 E]
  [TopologicalSpace E] [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F] [ContinuousAdd F]
  [AddCommGroup P] [Module 𝕜 P] [TopologicalSpace P] [ContinuousAdd P] [AddCommGroup Λ₁]
  [Module 𝕜 Λ₁] [TopologicalSpace Λ₁] [AddCommGroup Λ₂] [Module 𝕜 Λ₂] [TopologicalSpace Λ₂]
  [AddCommGroup G₁] [Module 𝕜 G₁] [TopologicalSpace G₁] [AddCommGroup G₂] [Module 𝕜 G₂]
  [TopologicalSpace G₂]
  {f : E →L[𝕜] F} {D₁ : Λ₁ →L[𝕜] F} {q₁ : E × Λ₁ →L[𝕜] G₁}
  {g : F →L[𝕜] P} {D₂ : Λ₂ →L[𝕜] P} {q₂ : F × Λ₂ →L[𝕜] G₂}

variable (f D₁ q₁ q₂) in
/-- **The kernel coordinate of a composite of kernel charts.** Kernel coordinates
`q₁ : E × Λ₁ → G₁` and `q₂ : F × Λ₂ → G₂` of stabilizations of `f` by `D₁` and of `g` by `D₂`
give the coordinate `(x, (l₁, l₂)) ↦ (q₁ (x, l₁), q₂ (f x + D₁ l₁, l₂))` of the stabilization of
`g ∘ f` by `(l₁, l₂) ↦ g (D₁ l₁) + D₂ l₂`. -/
def compKerCoord : E × (Λ₁ × Λ₂) →L[𝕜] G₁ × G₂ :=
  (q₁ ∘L (ContinuousLinearMap.id 𝕜 E).prodMap (fst 𝕜 Λ₁ Λ₂)).prod
    (q₂ ∘L ((f.coprod D₁ ∘L (ContinuousLinearMap.id 𝕜 E).prodMap (fst 𝕜 Λ₁ Λ₂)).prod
      (snd 𝕜 Λ₁ Λ₂ ∘L snd 𝕜 E (Λ₁ × Λ₂))))

@[simp]
theorem compKerCoord_apply (x : E) (l : Λ₁ × Λ₂) :
    compKerCoord f D₁ q₁ q₂ (x, l) = (q₁ (x, l.1), q₂ (f x + D₁ l.1, l.2)) :=
  (rfl)

/-- **The composite of kernel charts is a kernel chart.** If `(D₁, q₁)` is a kernel chart of `f`
and `(D₂, q₂)` one of `g`, then the stabilizer `(l₁, l₂) ↦ g (D₁ l₁) + D₂ l₂` with the coordinate
`ContinuousLinearMap.compKerCoord f D₁ q₁ q₂` is a kernel chart of `g ∘ f`: up to reordering the
factors, its pair is the pair of `g` applied after the pair of `f`. -/
theorem IsInvertible.prod_coprod_compKerCoord (h₁ : ((f.coprod D₁).prod q₁).IsInvertible)
    (h₂ : ((g.coprod D₂).prod q₂).IsInvertible) :
    (((g ∘L f).coprod ((g ∘L D₁).coprod D₂)).prod (compKerCoord f D₁ q₁ q₂)).IsInvertible := by
  obtain ⟨e₁, he₁⟩ := h₁
  obtain ⟨e₂, he₂⟩ := h₂
  -- `(x, (l₁, l₂)) ↦ ((f x + D₁ l₁, q₁ (x, l₁)), l₂) ↦ ((f x + D₁ l₁, l₂), q₁ (x, l₁))`, then the
  -- pair of `g` on the first factor and a final reordering.
  refine ⟨(ContinuousLinearEquiv.prodAssoc 𝕜 E Λ₁ Λ₂).symm.trans
    ((e₁.prodCongr (ContinuousLinearEquiv.refl 𝕜 Λ₂)).trans
      ((ContinuousLinearEquiv.prodAssoc 𝕜 F G₁ Λ₂).trans
        (((ContinuousLinearEquiv.refl 𝕜 F).prodCongr (ContinuousLinearEquiv.prodComm 𝕜 G₁ Λ₂)).trans
          ((ContinuousLinearEquiv.prodAssoc 𝕜 F Λ₂ G₁).symm.trans
            ((e₂.prodCongr (ContinuousLinearEquiv.refl 𝕜 G₁)).trans
              ((ContinuousLinearEquiv.prodAssoc 𝕜 P G₂ G₁).trans
                ((ContinuousLinearEquiv.refl 𝕜 P).prodCongr
                  (ContinuousLinearEquiv.prodComm 𝕜 G₂ G₁)))))))), ?_⟩
  refine ContinuousLinearMap.ext fun ⟨x, ⟨l₁, l₂⟩⟩ ↦ ?_
  have h₁ := DFunLike.congr_fun he₁ (x, l₁)
  simp only [ContinuousLinearEquiv.coe_coe] at h₁
  have h₂ := DFunLike.congr_fun he₂ (f x + D₁ l₁, l₂)
  simp only [ContinuousLinearEquiv.coe_coe] at h₂
  simp [h₁, h₂, map_add, add_assoc]

section Core

/-! ### Adapted families -/

variable [FiniteDimensional 𝕜 Λ₁] [FiniteDimensional 𝕜 Λ₂] [FiniteDimensional 𝕜 f.ker]
  [FiniteDimensional 𝕜 g.ker] [FiniteDimensional 𝕜 (F ⧸ f.range)]
  [FiniteDimensional 𝕜 (P ⧸ g.range)]

variable (f D₁ g D₂) in
/-- Families of vectors adapted at once to the stabilization sequences of `f` by `D₁` and of `g` by
`D₂` and to the kernel–cokernel sequence of the composition `g ∘ f`: vectors `v` of `ker (g ∘ f)`,
`w` of `ker g` and `x` of `coker f` completing bases along that sequence, parameters `zw` and `zx`
whose stabilizing directions represent the classes of `w` and `x` in `coker f`, stabilized kernel
vectors `v₁` and `v₂` whose parameters form bases of the ranges of the parameter projections,
parameters `z₂` whose classes form a basis of `coker g`, and lifts `ew` and `e₂` through
`f.coprod D₁`. -/
private structure CompData where
  v : Fin (finrank 𝕜 (LinearMap.range ((f : E →ₗ[𝕜] F).kerCompToKer (g : F →ₗ[𝕜] P)))) →
    LinearMap.ker ((g : F →ₗ[𝕜] P) ∘ₗ (f : E →ₗ[𝕜] F))
  w : Fin (finrank 𝕜 (LinearMap.range ((f : E →ₗ[𝕜] F).kerToCoker (g : F →ₗ[𝕜] P)))) → g.ker
  x : Fin (finrank 𝕜 (LinearMap.range ((f : E →ₗ[𝕜] F).cokerToCokerComp (g : F →ₗ[𝕜] P)))) →
    F ⧸ f.range
  zw : Fin (finrank 𝕜 (LinearMap.range ((f : E →ₗ[𝕜] F).kerToCoker (g : F →ₗ[𝕜] P)))) → Λ₁
  zx : Fin (finrank 𝕜 (LinearMap.range ((f : E →ₗ[𝕜] F).cokerToCokerComp (g : F →ₗ[𝕜] P)))) → Λ₁
  v₁ : Fin (finrank 𝕜 (parameterProj f D₁).range) → (f.coprod D₁).ker
  z₂ : Fin (finrank 𝕜 (P ⧸ g.range)) → Λ₂
  v₂ : Fin (finrank 𝕜 (parameterProj g D₂).range) → (g.coprod D₂).ker
  ew : Fin (finrank 𝕜 (LinearMap.range ((f : E →ₗ[𝕜] F).kerToCoker (g : F →ₗ[𝕜] P)))) → E
  e₂ : Fin (finrank 𝕜 (parameterProj g D₂).range) → E × Λ₁
  li_v : LinearIndependent 𝕜 ((f : E →ₗ[𝕜] F).kerCompToKer (g : F →ₗ[𝕜] P) ∘ v)
  li_w : LinearIndependent 𝕜 ((f : E →ₗ[𝕜] F).kerToCoker (g : F →ₗ[𝕜] P) ∘ w)
  li_x : LinearIndependent 𝕜 ((f : E →ₗ[𝕜] F).cokerToCokerComp (g : F →ₗ[𝕜] P) ∘ x)
  hzw : ∀ i, parameterToCoker f D₁ (zw i) = (f : E →ₗ[𝕜] F).kerToCoker (g : F →ₗ[𝕜] P) (w i)
  hzx : ∀ i, parameterToCoker f D₁ (zx i) = x i
  li_v₁ : LinearIndependent 𝕜 (parameterProj f D₁ ∘ v₁)
  li_z₂ : LinearIndependent 𝕜 (parameterToCoker g D₂ ∘ z₂)
  li_v₂ : LinearIndependent 𝕜 (parameterProj g D₂ ∘ v₂)
  hew : ∀ i, f (ew i) + D₁ (zw i) = (w i : F)
  he₂ : ∀ j, f (e₂ j).1 + D₁ (e₂ j).2 = (v₂ j : F × Λ₂).1

/-- Adapted families exist when both stabilizations are onto. -/
private theorem nonempty_compData (hf : Function.Surjective (f.coprod D₁))
    (hg : Function.Surjective (g.coprod D₂)) : Nonempty (CompData f D₁ g D₂) := by
  have hf' := (parameterToCoker_surjective_iff_coprod_surjective f D₁).2 hf
  have hg' := (parameterToCoker_surjective_iff_coprod_surjective g D₂).2 hg
  obtain ⟨v, hv⟩ := LinearMap.exists_linearIndependent_comp
    ((f : E →ₗ[𝕜] F).kerCompToKer (g : F →ₗ[𝕜] P))
  obtain ⟨w, hw⟩ := LinearMap.exists_linearIndependent_comp
    ((f : E →ₗ[𝕜] F).kerToCoker (g : F →ₗ[𝕜] P))
  obtain ⟨x, hx⟩ := LinearMap.exists_linearIndependent_comp
    ((f : E →ₗ[𝕜] F).cokerToCokerComp (g : F →ₗ[𝕜] P))
  choose zw hzw using fun i ↦ hf' ((f : E →ₗ[𝕜] F).kerToCoker (g : F →ₗ[𝕜] P) (w i))
  choose zx hzx using fun i ↦ hf' (x i)
  obtain ⟨v₁, hv₁⟩ := LinearMap.exists_linearIndependent_comp
    (parameterProj f D₁ : (f.coprod D₁).ker →ₗ[𝕜] Λ₁)
  obtain ⟨z₂, hz₂⟩ := LinearMap.exists_linearIndependent_comp_of_surjective hg'
  obtain ⟨v₂, hv₂⟩ := LinearMap.exists_linearIndependent_comp
    (parameterProj g D₂ : (g.coprod D₂).ker →ₗ[𝕜] Λ₂)
  -- The class of `D₁ (zw i)` in `coker f` is that of `w i`, so `w i - D₁ (zw i)` lies in the
  -- range of `f`.
  have hmem (i) : (w i : F) - D₁ (zw i) ∈ f.range := by
    have h := hzw i
    rw [parameterToCoker_apply, LinearMap.kerToCoker_apply] at h
    exact (Submodule.Quotient.eq _).1 h.symm
  choose ew hew using fun i ↦ hmem i
  choose e₂ he₂ using fun j ↦ hf (v₂ j : F × Λ₂).1
  exact ⟨⟨v, w, x, zw, zx, v₁, z₂, v₂, ew, e₂, hv, hw, hx, hzw, hzx, hv₁, hz₂, hv₂,
    fun i ↦ by
      have h := hew i
      rw [ContinuousLinearMap.coe_coe] at h
      rw [h, sub_add_cancel], fun j ↦ by rw [← he₂ j, coprod_apply]⟩⟩

/-- The dimension counts of a surjective stabilization `T.coprod D`: the parameters split into the
range of the parameter projection and a copy of the cokernel of `T`, and the stabilized kernel
into a copy of the kernel of `T` and the range of the parameter projection. -/
private theorem finrank_stabilization {E' Λ F' : Type*} [AddCommGroup E'] [Module 𝕜 E']
    [TopologicalSpace E'] [AddCommGroup Λ] [Module 𝕜 Λ] [TopologicalSpace Λ] [AddCommGroup F']
    [Module 𝕜 F'] [TopologicalSpace F'] [ContinuousAdd F'] {T : E' →L[𝕜] F'} {D : Λ →L[𝕜] F'}
    [FiniteDimensional 𝕜 T.ker] [FiniteDimensional 𝕜 Λ] (h : Function.Surjective (T.coprod D)) :
    finrank 𝕜 Λ = finrank 𝕜 (parameterProj T D).range + finrank 𝕜 (F' ⧸ T.range) ∧
      finrank 𝕜 (T.coprod D).ker = finrank 𝕜 T.ker + finrank 𝕜 (parameterProj T D).range := by
  refine ⟨?_, ?_⟩
  · rw [← finrank_quotient_range_parameterProj T D h, add_comm]
    exact (Submodule.finrank_quotient_add_finrank _).symm
  · have h₁ := (parameterProj T D : (T.coprod D).ker →ₗ[𝕜] Λ).finrank_range_add_finrank_ker
    have h₂ := finrank_ker_parameterProj T D
    change finrank 𝕜 (parameterProj T D).range + finrank 𝕜 (parameterProj T D).ker = _ at h₁
    omega

omit [FiniteDimensional 𝕜 Λ₂] [FiniteDimensional 𝕜 g.ker] [FiniteDimensional 𝕜 (P ⧸ g.range)] in
/-- The normalized stabilization isomorphism of `f` on the exterior product of a basis `u` of
`ker f`, completed by `v₁`, tensored with `φ₁`: the parameters `p₁ ∘ v₁`, `zw`, `zx` evaluate
`φ₁`, and the classes of `zw` and `zx` in `coker f` are `δ`, on which `ψ` is normalized. -/
private theorem stab_left (d : CompData f D₁ g D₂) (hf : Function.Surjective (f.coprod D₁))
    {κ₁ : TauCeti.detLine 𝕜 (f.coprod D₁).ker}
    (hκ₁ : (κ₁ : ExteriorAlgebra 𝕜 (f.coprod D₁).ker) = ExteriorAlgebra.ιMulti 𝕜 _
      (Fin.append (kerCoprodHom f D₁ ∘ Module.finBasis 𝕜 f.ker) d.v₁))
    {c₁ : TauCeti.detLine 𝕜 Λ₁} (hc₁ : (c₁ : ExteriorAlgebra 𝕜 Λ₁) = ExteriorAlgebra.ιMulti 𝕜 _
      (Fin.append (parameterProj f D₁ ∘ d.v₁) (Fin.append d.zw d.zx)))
    {δ : TauCeti.detLine 𝕜 (F ⧸ f.range)} (hδ : (δ : ExteriorAlgebra 𝕜 (F ⧸ f.range)) =
      ExteriorAlgebra.ιMulti 𝕜 _
        (Fin.append ((f : E →ₗ[𝕜] F).kerToCoker (g : F →ₗ[𝕜] P) ∘ d.w) d.x))
    {ψ : Dual 𝕜 (TauCeti.detLine 𝕜 (F ⧸ f.range))} (hψ : ψ δ = 1)
    (φ₁ : Dual 𝕜 (TauCeti.detLine 𝕜 Λ₁)) :
    detLineStabilizationEquiv f D₁ hf (κ₁ ⊗ₜ φ₁) =
      ((-1 : 𝕜) ^ (finrank 𝕜 (F ⧸ f.range) * finrank 𝕜 Λ₁) * φ₁ c₁) •
        (exteriorPower.ιMulti 𝕜 _ (Module.finBasis 𝕜 f.ker) ⊗ₜ ψ) := by
  have hb := (f : E →ₗ[𝕜] F).finrank_quotient_range_eq_finrank_range_kerToCoker_add
    (g : F →ₗ[𝕜] P)
  have hc₁' : (c₁ : ExteriorAlgebra 𝕜 Λ₁) = ExteriorAlgebra.ιMulti 𝕜 _
      (Fin.append (parameterProj f D₁ ∘ d.v₁) (Fin.append d.zw d.zx ∘ Fin.cast hb)) := by
    rw [hc₁]
    simp only [← ExteriorAlgebra.ιMulti_mul_ιMulti, TauCeti.ExteriorAlgebra.ιMulti_comp_cast]
  have hξ : ψ (exteriorPower.ιMulti 𝕜 _ (parameterToCoker f D₁ ∘
      (Fin.append d.zw d.zx ∘ Fin.cast hb))) = 1 := by
    convert hψ using 2
    refine Subtype.ext ?_
    rw [exteriorPower.ιMulti_apply_coe, hδ, ← Function.comp_assoc, Fin.comp_append,
      TauCeti.ExteriorAlgebra.ιMulti_comp_cast]
    congr 2
    · exact funext d.hzw
    · exact funext d.hzx
  rw [detLineStabilizationEquiv_apply, detLineCoprodEquiv_def,
    TauCeti.detLineFourTermEquiv_tmul_eq_smul_tmul _ _ _ _ (Module.finBasis 𝕜 f.ker) d.v₁ _
      hκ₁ hc₁' φ₁ hξ, smul_smul]

omit [FiniteDimensional 𝕜 Λ₁] [FiniteDimensional 𝕜 f.ker] [FiniteDimensional 𝕜 (F ⧸ f.range)]
  [FiniteDimensional 𝕜 (P ⧸ g.range)] in
/-- The normalized stabilization isomorphism of `g` on the exterior product of the images of `v`
and `w` in `ker g`, completed by `v₂`, tensored with `φ₂`: the parameters `p₂ ∘ v₂` and `z₂`
evaluate `φ₂`, and `χ` is normalized on the classes of `z₂` in `coker g`. -/
private theorem stab_right (d : CompData f D₁ g D₂) (hg : Function.Surjective (g.coprod D₂))
    {κ₂ : TauCeti.detLine 𝕜 (g.coprod D₂).ker}
    (hκ₂ : (κ₂ : ExteriorAlgebra 𝕜 (g.coprod D₂).ker) = ExteriorAlgebra.ιMulti 𝕜 _
      (Fin.append (Fin.append (kerCoprodHom g D₂ ∘ (f : E →ₗ[𝕜] F).kerCompToKer (g : F →ₗ[𝕜] P) ∘
        d.v) (kerCoprodHom g D₂ ∘ d.w)) d.v₂))
    {c₂ : TauCeti.detLine 𝕜 Λ₂} (hc₂ : (c₂ : ExteriorAlgebra 𝕜 Λ₂) = ExteriorAlgebra.ιMulti 𝕜 _
      (Fin.append (parameterProj g D₂ ∘ d.v₂) d.z₂))
    {γ : TauCeti.detLine 𝕜 g.ker} (hγ : (γ : ExteriorAlgebra 𝕜 g.ker) = ExteriorAlgebra.ιMulti 𝕜 _
      (Fin.append ((f : E →ₗ[𝕜] F).kerCompToKer (g : F →ₗ[𝕜] P) ∘ d.v) d.w))
    {χ : Dual 𝕜 (TauCeti.detLine 𝕜 (P ⧸ g.range))}
    (hχ : χ (exteriorPower.ιMulti 𝕜 _ (parameterToCoker g D₂ ∘ d.z₂)) = 1)
    (φ₂ : Dual 𝕜 (TauCeti.detLine 𝕜 Λ₂)) :
    detLineStabilizationEquiv g D₂ hg (κ₂ ⊗ₜ φ₂) =
      ((-1 : 𝕜) ^ (finrank 𝕜 (P ⧸ g.range) * finrank 𝕜 Λ₂) * φ₂ c₂) • (γ ⊗ₜ χ) := by
  have hc := (f : E →ₗ[𝕜] F).finrank_ker_eq_finrank_range_kerCompToKer_add (g : F →ₗ[𝕜] P)
  set U := Fin.append ((f : E →ₗ[𝕜] F).kerCompToKer (g : F →ₗ[𝕜] P) ∘ d.v) d.w ∘ Fin.cast hc
  have hκ₂' : (κ₂ : ExteriorAlgebra 𝕜 (g.coprod D₂).ker) = ExteriorAlgebra.ιMulti 𝕜 _
      (Fin.append (kerCoprodHom g D₂ ∘ U) d.v₂) := by
    rw [hκ₂]
    simp only [U, ← ExteriorAlgebra.ιMulti_mul_ιMulti, TauCeti.ExteriorAlgebra.ιMulti_comp_cast,
      ← Function.comp_assoc, Fin.comp_append]
  have hγ' : exteriorPower.ιMulti 𝕜 _ U = γ :=
    Subtype.ext (by rw [exteriorPower.ιMulti_apply_coe, TauCeti.ExteriorAlgebra.ιMulti_comp_cast,
      hγ])
  rw [detLineStabilizationEquiv_apply, detLineCoprodEquiv_def,
    TauCeti.detLineFourTermEquiv_tmul_eq_smul_tmul _ _ _ _ U d.v₂ d.z₂ hκ₂' hc₂ φ₂ hχ, smul_smul,
    hγ']

/-! ### The stabilized kernel of the composite -/

omit [FiniteDimensional 𝕜 Λ₁] [FiniteDimensional 𝕜 Λ₂] [FiniteDimensional 𝕜 f.ker]
  [FiniteDimensional 𝕜 g.ker] [FiniteDimensional 𝕜 (F ⧸ f.range)]
  [FiniteDimensional 𝕜 (P ⧸ g.range)] [ContinuousAdd F] in
/-- A point `(x, (l₁, l₂))` lies in the stabilized kernel of `g ∘ f` as soon as `g` kills
`f x + D₁ l₁` and `D₂ l₂` together. -/
private theorem mem_ker_coprod_comp {x : E} {l₁ : Λ₁} {l₂ : Λ₂}
    (h : g (f x + D₁ l₁) + D₂ l₂ = 0) :
    ((x, (l₁, l₂)) : E × (Λ₁ × Λ₂)) ∈ ((g ∘L f).coprod ((g ∘L D₁).coprod D₂)).ker := by
  rw [LinearMap.mem_ker, ← h]
  simp [map_add, add_assoc]

/-- The stabilized kernel vectors of `f` placed in the stabilized kernel of `g ∘ f`, with zero
`Λ₂`-parameter. -/
private def CompData.ι₁ (d : CompData f D₁ g D₂) (i : Fin (finrank 𝕜 (parameterProj f D₁).range)) :
    ((g ∘L f).coprod ((g ∘L D₁).coprod D₂)).ker :=
  ⟨((d.v₁ i : E × Λ₁).1, ((d.v₁ i : E × Λ₁).2, 0)), mem_ker_coprod_comp (by
    have h := LinearMap.mem_ker.1 (d.v₁ i).property
    rw [coe_coe, coprod_apply] at h
    rw [h, map_zero, map_zero, add_zero])⟩

/-- Lifts of the vectors `w` of `ker g` to the stabilized kernel of `g ∘ f`. -/
private def CompData.σw (d : CompData f D₁ g D₂)
    (i : Fin (finrank 𝕜 (LinearMap.range ((f : E →ₗ[𝕜] F).kerToCoker (g : F →ₗ[𝕜] P))))) :
    ((g ∘L f).coprod ((g ∘L D₁).coprod D₂)).ker :=
  ⟨(d.ew i, (d.zw i, 0)), mem_ker_coprod_comp (by
    rw [d.hew i, map_zero, add_zero]
    exact LinearMap.mem_ker.1 (d.w i).property)⟩

/-- Lifts of the stabilized kernel vectors `v₂` of `g` to the stabilized kernel of `g ∘ f`. -/
private def CompData.σv₂ (d : CompData f D₁ g D₂)
    (j : Fin (finrank 𝕜 (parameterProj g D₂).range)) :
    ((g ∘L f).coprod ((g ∘L D₁).coprod D₂)).ker :=
  ⟨((d.e₂ j).1, ((d.e₂ j).2, (d.v₂ j : F × Λ₂).2)), mem_ker_coprod_comp (by
    have h := LinearMap.mem_ker.1 (d.v₂ j).property
    rw [coe_coe, coprod_apply] at h
    rw [d.he₂ j, h])⟩

/-- The classes in `coker (g ∘ f)` of the stabilizing directions `D₂ ∘ z₂`; their images in
`coker g` form a basis. -/
private def CompData.y (d : CompData f D₁ g D₂) (j : Fin (finrank 𝕜 (P ⧸ g.range))) :
    P ⧸ LinearMap.range ((g : F →ₗ[𝕜] P) ∘ₗ (f : E →ₗ[𝕜] F)) :=
  Submodule.Quotient.mk (D₂ (d.z₂ j))

/-- The lifts `σv₂` of the stabilized kernel vectors of `g` have parameters `(e₂ j).2` and
`p₂ (v₂ j)`. -/
private def CompData.lift₂ (d : CompData f D₁ g D₂)
    (j : Fin (finrank 𝕜 (parameterProj g D₂).range)) : Λ₁ × Λ₂ :=
  ((d.e₂ j).2, parameterProj g D₂ (d.v₂ j))

omit [FiniteDimensional 𝕜 Λ₁] [FiniteDimensional 𝕜 Λ₂] [FiniteDimensional 𝕜 f.ker]
  [FiniteDimensional 𝕜 g.ker] [FiniteDimensional 𝕜 (F ⧸ f.range)]
  [FiniteDimensional 𝕜 (P ⧸ g.range)] [ContinuousAdd F] [ContinuousAdd P] in
variable (f g) in
/-- The kernel of `g ∘ f` has dimension `dim ker f + r`, for the rank `r` of
`ker (g ∘ f) → ker g`. -/
private theorem finrank_ker_comp_eq [FiniteDimensional 𝕜 (g ∘L f).ker] :
    finrank 𝕜 (g ∘L f).ker = finrank 𝕜 f.ker +
      finrank 𝕜 (LinearMap.range ((f : E →ₗ[𝕜] F).kerCompToKer (g : F →ₗ[𝕜] P))) :=
  have : FiniteDimensional 𝕜 (LinearMap.ker ((g : F →ₗ[𝕜] P) ∘ₗ (f : E →ₗ[𝕜] F))) :=
    ‹FiniteDimensional 𝕜 (g ∘L f).ker›
  (f : E →ₗ[𝕜] F).finrank_ker_comp_eq_finrank_ker_add (g : F →ₗ[𝕜] P)

omit [FiniteDimensional 𝕜 Λ₁] [FiniteDimensional 𝕜 Λ₂] [FiniteDimensional 𝕜 f.ker]
  [FiniteDimensional 𝕜 g.ker] [FiniteDimensional 𝕜 (F ⧸ f.range)]
  [FiniteDimensional 𝕜 (P ⧸ g.range)] [ContinuousAdd F] [ContinuousAdd P] in
variable (f g) in
/-- The cokernel of `g ∘ f` has dimension `t + dim coker g`, for the rank `t` of
`coker f → coker (g ∘ f)`. -/
private theorem finrank_quotient_range_comp_eq [FiniteDimensional 𝕜 (P ⧸ (g ∘L f).range)] :
    finrank 𝕜 (P ⧸ (g ∘L f).range) =
      finrank 𝕜 (LinearMap.range ((f : E →ₗ[𝕜] F).cokerToCokerComp (g : F →ₗ[𝕜] P))) +
        finrank 𝕜 (P ⧸ g.range) :=
  have : FiniteDimensional 𝕜 (P ⧸ LinearMap.range ((g : F →ₗ[𝕜] P) ∘ₗ (f : E →ₗ[𝕜] F))) :=
    ‹FiniteDimensional 𝕜 (P ⧸ (g ∘L f).range)›
  (f : E →ₗ[𝕜] F).finrank_quotient_range_comp_eq_finrank_range_cokerToCokerComp_add
    (g : F →ₗ[𝕜] P)

omit [FiniteDimensional 𝕜 (P ⧸ g.range)] in
/-- The parameters of the composite stabilization spanning the range of its parameter projection
are those of `f`, the lifts `zw` of the classes of `w`, and those of `g`. -/
private theorem finrank_range_parameterProj_comp (hf : Function.Surjective (f.coprod D₁))
    (hg : Function.Surjective (g.coprod D₂))
    (hh : Function.Surjective ((g ∘L f).coprod ((g ∘L D₁).coprod D₂)))
    [FiniteDimensional 𝕜 (g ∘L f).ker] [FiniteDimensional 𝕜 (P ⧸ (g ∘L f).range)] :
    finrank 𝕜 (parameterProj (g ∘L f) ((g ∘L D₁).coprod D₂)).range =
      finrank 𝕜 (parameterProj f D₁).range +
        (finrank 𝕜 (LinearMap.range ((f : E →ₗ[𝕜] F).kerToCoker (g : F →ₗ[𝕜] P))) +
          finrank 𝕜 (parameterProj g D₂).range) := by
  have hb := (f : E →ₗ[𝕜] F).finrank_quotient_range_eq_finrank_range_kerToCoker_add
    (g : F →ₗ[𝕜] P)
  have hd := finrank_quotient_range_comp_eq f g
  obtain ⟨hl₁, -⟩ := finrank_stabilization hf
  obtain ⟨hl₂, -⟩ := finrank_stabilization hg
  obtain ⟨hl, -⟩ := finrank_stabilization hh
  rw [Module.finrank_prod] at hl
  omega

omit [FiniteDimensional 𝕜 Λ₁] [FiniteDimensional 𝕜 Λ₂] [FiniteDimensional 𝕜 g.ker]
  [FiniteDimensional 𝕜 (F ⧸ f.range)] [FiniteDimensional 𝕜 (P ⧸ g.range)] in
/-- The exterior product `β` of the stabilized kernel of `g ∘ f` lists `ι₁` before the vectors
`(v, 0)`; the four-term formula lists the kernel of `g ∘ f` first, which costs `(-1) ^ (r m₁)`. -/
private theorem coe_neg_one_pow_smul_stabilizedKer_comp (d : CompData f D₁ g D₂)
    {β : TauCeti.detLine 𝕜 ((g ∘L f).coprod ((g ∘L D₁).coprod D₂)).ker}
    (hβ : (β : ExteriorAlgebra 𝕜 ((g ∘L f).coprod ((g ∘L D₁).coprod D₂)).ker) =
      ExteriorAlgebra.ιMulti 𝕜 _ (Fin.append
        (Fin.append (kerCoprodHom (g ∘L f) ((g ∘L D₁).coprod D₂) ∘
          Submodule.inclusion (LinearMap.ker_le_ker_comp (f : E →ₗ[𝕜] F) (g : F →ₗ[𝕜] P)) ∘
            Module.finBasis 𝕜 f.ker) d.ι₁)
        (Fin.append (kerCoprodHom (g ∘L f) ((g ∘L D₁).coprod D₂) ∘ d.v)
          (Fin.append d.σw d.σv₂))))
    (hk : finrank 𝕜 (g ∘L f).ker = finrank 𝕜 f.ker +
      finrank 𝕜 (LinearMap.range ((f : E →ₗ[𝕜] F).kerCompToKer (g : F →ₗ[𝕜] P))))
    (hV : finrank 𝕜 (parameterProj (g ∘L f) ((g ∘L D₁).coprod D₂)).range =
      finrank 𝕜 (parameterProj f D₁).range +
        (finrank 𝕜 (LinearMap.range ((f : E →ₗ[𝕜] F).kerToCoker (g : F →ₗ[𝕜] P))) +
          finrank 𝕜 (parameterProj g D₂).range)) :
    ((((-1 : 𝕜) ^ (finrank 𝕜 (LinearMap.range
        ((f : E →ₗ[𝕜] F).kerCompToKer (g : F →ₗ[𝕜] P))) * finrank 𝕜 (parameterProj f D₁).range)) •
          β : TauCeti.detLine 𝕜 ((g ∘L f).coprod ((g ∘L D₁).coprod D₂)).ker) :
            ExteriorAlgebra 𝕜 ((g ∘L f).coprod ((g ∘L D₁).coprod D₂)).ker) =
      ExteriorAlgebra.ιMulti 𝕜 _ (Fin.append
        ((kerCoprodHom (g ∘L f) ((g ∘L D₁).coprod D₂) ∘ Fin.append (Submodule.inclusion
          (LinearMap.ker_le_ker_comp (f : E →ₗ[𝕜] F) (g : F →ₗ[𝕜] P)) ∘
            Module.finBasis 𝕜 f.ker) d.v) ∘ Fin.cast hk)
        (Fin.append d.ι₁ (Fin.append d.σw d.σv₂) ∘ Fin.cast hV)) := by
  -- `Fin.comp_append` does not see through the two spellings of the kernel of `g ∘ f`.
  have hkA : kerCoprodHom (g ∘L f) ((g ∘L D₁).coprod D₂) ∘ Fin.append (Submodule.inclusion
      (LinearMap.ker_le_ker_comp (f : E →ₗ[𝕜] F) (g : F →ₗ[𝕜] P)) ∘
        Module.finBasis 𝕜 f.ker) d.v =
      Fin.append (kerCoprodHom (g ∘L f) ((g ∘L D₁).coprod D₂) ∘ Submodule.inclusion
        (LinearMap.ker_le_ker_comp (f : E →ₗ[𝕜] F) (g : F →ₗ[𝕜] P)) ∘
          Module.finBasis 𝕜 f.ker) (kerCoprodHom (g ∘L f) ((g ∘L D₁).coprod D₂) ∘ d.v) :=
    funext fun i ↦ Fin.addCases (fun _ ↦ by simp) (fun _ ↦ by simp) i
  rw [Submodule.coe_smul, hβ]
  simp only [← ExteriorAlgebra.ιMulti_mul_ιMulti, TauCeti.ExteriorAlgebra.ιMulti_comp_cast,
    hkA, mul_assoc]
  rw [ExteriorAlgebra.ιMulti_mul_ιMulti_mul_eq_neg_one_pow_smul (u := kerCoprodHom (g ∘L f)
    ((g ∘L D₁).coprod D₂) ∘ d.v) (v := d.ι₁), mul_smul_comm,
    Nat.mul_comm (finrank 𝕜 (parameterProj f D₁).range)]

omit [FiniteDimensional 𝕜 Λ₁] [FiniteDimensional 𝕜 Λ₂] [FiniteDimensional 𝕜 f.ker]
  [FiniteDimensional 𝕜 g.ker] [FiniteDimensional 𝕜 (F ⧸ f.range)]
  [FiniteDimensional 𝕜 (P ⧸ g.range)] in
/-- The parameters `γ` of the composite list those of `σv₂` before `(zx, 0)`; the four-term formula
lists the parameters of the stabilized kernel first, which costs `(-1) ^ (t m₂)`. -/
private theorem coe_neg_one_pow_smul_parameters_comp (d : CompData f D₁ g D₂)
    {γ : TauCeti.detLine 𝕜 (Λ₁ × Λ₂)} (hγ : (γ : ExteriorAlgebra 𝕜 (Λ₁ × Λ₂)) =
      ExteriorAlgebra.ιMulti 𝕜 _ (Fin.append
        (LinearMap.inl 𝕜 Λ₁ Λ₂ ∘ Fin.append (parameterProj f D₁ ∘ d.v₁) (Fin.append d.zw d.zx))
        (Fin.append d.lift₂ (LinearMap.inr 𝕜 Λ₁ Λ₂ ∘ d.z₂))))
    (hV : finrank 𝕜 (parameterProj (g ∘L f) ((g ∘L D₁).coprod D₂)).range =
      finrank 𝕜 (parameterProj f D₁).range +
        (finrank 𝕜 (LinearMap.range ((f : E →ₗ[𝕜] F).kerToCoker (g : F →ₗ[𝕜] P))) +
          finrank 𝕜 (parameterProj g D₂).range))
    (hd : finrank 𝕜 (P ⧸ (g ∘L f).range) =
      finrank 𝕜 (LinearMap.range ((f : E →ₗ[𝕜] F).cokerToCokerComp (g : F →ₗ[𝕜] P))) +
        finrank 𝕜 (P ⧸ g.range)) :
    ((((-1 : 𝕜) ^ (finrank 𝕜 (LinearMap.range
        ((f : E →ₗ[𝕜] F).cokerToCokerComp (g : F →ₗ[𝕜] P))) *
          finrank 𝕜 (parameterProj g D₂).range)) • γ : TauCeti.detLine 𝕜 (Λ₁ × Λ₂)) :
            ExteriorAlgebra 𝕜 (Λ₁ × Λ₂)) =
      ExteriorAlgebra.ιMulti 𝕜 _ (Fin.append
        ((parameterProj (g ∘L f) ((g ∘L D₁).coprod D₂) ∘ Fin.append d.ι₁
          (Fin.append d.σw d.σv₂)) ∘ Fin.cast hV)
        (Fin.append (LinearMap.inl 𝕜 Λ₁ Λ₂ ∘ d.zx) (LinearMap.inr 𝕜 Λ₁ Λ₂ ∘ d.z₂) ∘
          Fin.cast hd)) := by
  have h₁ : parameterProj (g ∘L f) ((g ∘L D₁).coprod D₂) ∘ d.ι₁ =
      LinearMap.inl 𝕜 Λ₁ Λ₂ ∘ parameterProj f D₁ ∘ d.v₁ :=
    funext fun _ ↦ by simp [parameterProj_apply, CompData.ι₁]
  have h₂ : parameterProj (g ∘L f) ((g ∘L D₁).coprod D₂) ∘ d.σw =
      LinearMap.inl 𝕜 Λ₁ Λ₂ ∘ d.zw :=
    funext fun _ ↦ by simp [parameterProj_apply, CompData.σw]
  have h₃ : parameterProj (g ∘L f) ((g ∘L D₁).coprod D₂) ∘ d.σv₂ = d.lift₂ :=
    funext fun _ ↦ by simp [parameterProj_apply, CompData.σv₂, CompData.lift₂]
  rw [Submodule.coe_smul, hγ]
  simp only [← ExteriorAlgebra.ιMulti_mul_ιMulti, TauCeti.ExteriorAlgebra.ιMulti_comp_cast,
    Fin.comp_append, mul_assoc, h₁, h₂, h₃]
  rw [ExteriorAlgebra.ιMulti_mul_ιMulti_mul_eq_neg_one_pow_smul (u := d.lift₂), mul_smul_comm,
    mul_smul_comm]

omit [FiniteDimensional 𝕜 Λ₁] [FiniteDimensional 𝕜 Λ₂] [FiniteDimensional 𝕜 f.ker]
  [FiniteDimensional 𝕜 g.ker] [FiniteDimensional 𝕜 (F ⧸ f.range)]
  [FiniteDimensional 𝕜 (P ⧸ g.range)] in
/-- The classes in `coker (g ∘ f)` of the parameters `(zx, 0)` and `(0, z₂)` are those listed in
`ε`, so a functional normalized on `ε` is normalized on them. -/
private theorem apply_ιMulti_parameterToCoker_comp (d : CompData f D₁ g D₂)
    (hd : finrank 𝕜 (P ⧸ (g ∘L f).range) =
      finrank 𝕜 (LinearMap.range ((f : E →ₗ[𝕜] F).cokerToCokerComp (g : F →ₗ[𝕜] P))) +
        finrank 𝕜 (P ⧸ g.range))
    {ε : TauCeti.detLine 𝕜 (P ⧸ (g ∘L f).range)}
    (hε : (ε : ExteriorAlgebra 𝕜 (P ⧸ (g ∘L f).range)) = ExteriorAlgebra.ιMulti 𝕜 _
      (Fin.append ((f : E →ₗ[𝕜] F).cokerToCokerComp (g : F →ₗ[𝕜] P) ∘ d.x) d.y))
    {ξ : Dual 𝕜 (TauCeti.detLine 𝕜 (P ⧸ (g ∘L f).range))} (hξ : ξ ε = 1) :
    ξ (exteriorPower.ιMulti 𝕜 _ (parameterToCoker (g ∘L f) ((g ∘L D₁).coprod D₂) ∘
      (Fin.append (LinearMap.inl 𝕜 Λ₁ Λ₂ ∘ d.zx) (LinearMap.inr 𝕜 Λ₁ Λ₂ ∘ d.z₂) ∘
        Fin.cast hd))) = 1 := by
  have hx : parameterToCoker (g ∘L f) ((g ∘L D₁).coprod D₂) ∘ LinearMap.inl 𝕜 Λ₁ Λ₂ ∘ d.zx =
      (f : E →ₗ[𝕜] F).cokerToCokerComp (g : F →ₗ[𝕜] P) ∘ d.x := funext fun i ↦ by
    simp only [Function.comp_apply]
    rw [← d.hzx i, parameterToCoker_apply]
    simp only [LinearMap.inl_apply, coprod_apply, comp_apply, map_zero, add_zero,
      parameterToCoker_apply, Submodule.mkQ_apply, LinearMap.cokerToCokerComp_mk]
    rfl
  have hy : parameterToCoker (g ∘L f) ((g ∘L D₁).coprod D₂) ∘ LinearMap.inr 𝕜 Λ₁ Λ₂ ∘ d.z₂ =
      d.y := funext fun j ↦ by
    simp only [Function.comp_apply, parameterToCoker_apply, LinearMap.inr_apply, coprod_apply,
      map_zero, zero_add, CompData.y]
    rfl
  convert hξ using 2
  refine Subtype.ext ?_
  rw [exteriorPower.ιMulti_apply_coe, hε, Fin.comp_append_comp_cast,
    TauCeti.ExteriorAlgebra.ιMulti_comp_cast, hx, hy]
  rfl

omit [FiniteDimensional 𝕜 (P ⧸ g.range)] in
/-- The normalized stabilization isomorphism of `g ∘ f` on the exterior product `β` of the vectors
`(u, 0)`, `ι₁`, `(v, 0)`, `σw` and `σv₂` of its stabilized kernel, tensored with `φ`. Listing the
kernel of `g ∘ f` first exchanges `ι₁` with `v`, and listing the classes in `coker (g ∘ f)` last
exchanges the parameters of `σv₂` with those of `zx`; these cost the signs `(-1) ^ (r m₁)` and
`(-1) ^ (t m₂)`. -/
private theorem stab_comp (d : CompData f D₁ g D₂) (hf : Function.Surjective (f.coprod D₁))
    (hg : Function.Surjective (g.coprod D₂))
    (hh : Function.Surjective ((g ∘L f).coprod ((g ∘L D₁).coprod D₂)))
    [FiniteDimensional 𝕜 (g ∘L f).ker] [FiniteDimensional 𝕜 (P ⧸ (g ∘L f).range)]
    {β : TauCeti.detLine 𝕜 ((g ∘L f).coprod ((g ∘L D₁).coprod D₂)).ker}
    (hβ : (β : ExteriorAlgebra 𝕜 ((g ∘L f).coprod ((g ∘L D₁).coprod D₂)).ker) =
      ExteriorAlgebra.ιMulti 𝕜 _ (Fin.append
        (Fin.append (kerCoprodHom (g ∘L f) ((g ∘L D₁).coprod D₂) ∘
          Submodule.inclusion (LinearMap.ker_le_ker_comp (f : E →ₗ[𝕜] F) (g : F →ₗ[𝕜] P)) ∘
            Module.finBasis 𝕜 f.ker) d.ι₁)
        (Fin.append (kerCoprodHom (g ∘L f) ((g ∘L D₁).coprod D₂) ∘ d.v)
          (Fin.append d.σw d.σv₂))))
    {γ : TauCeti.detLine 𝕜 (Λ₁ × Λ₂)} (hγ : (γ : ExteriorAlgebra 𝕜 (Λ₁ × Λ₂)) =
      ExteriorAlgebra.ιMulti 𝕜 _ (Fin.append
        (LinearMap.inl 𝕜 Λ₁ Λ₂ ∘ Fin.append (parameterProj f D₁ ∘ d.v₁) (Fin.append d.zw d.zx))
        (Fin.append d.lift₂ (LinearMap.inr 𝕜 Λ₁ Λ₂ ∘ d.z₂))))
    {α : TauCeti.detLine 𝕜 (g ∘L f).ker} (hα : (α : ExteriorAlgebra 𝕜 (g ∘L f).ker) =
      ExteriorAlgebra.ιMulti 𝕜 _ (Fin.append
        (Submodule.inclusion (LinearMap.ker_le_ker_comp (f : E →ₗ[𝕜] F) (g : F →ₗ[𝕜] P)) ∘
          Module.finBasis 𝕜 f.ker) d.v))
    {ε : TauCeti.detLine 𝕜 (P ⧸ (g ∘L f).range)}
    (hε : (ε : ExteriorAlgebra 𝕜 (P ⧸ (g ∘L f).range)) = ExteriorAlgebra.ιMulti 𝕜 _
      (Fin.append ((f : E →ₗ[𝕜] F).cokerToCokerComp (g : F →ₗ[𝕜] P) ∘ d.x) d.y))
    {ξ : Dual 𝕜 (TauCeti.detLine 𝕜 (P ⧸ (g ∘L f).range))} (hξ : ξ ε = 1)
    (φ : Dual 𝕜 (TauCeti.detLine 𝕜 (Λ₁ × Λ₂))) :
    detLineStabilizationEquiv (g ∘L f) ((g ∘L D₁).coprod D₂) hh (β ⊗ₜ φ) =
      ((-1 : 𝕜) ^ (finrank 𝕜 (P ⧸ (g ∘L f).range) * finrank 𝕜 (Λ₁ × Λ₂) +
        finrank 𝕜 (LinearMap.range ((f : E →ₗ[𝕜] F).kerCompToKer (g : F →ₗ[𝕜] P))) *
          finrank 𝕜 (parameterProj f D₁).range +
        finrank 𝕜 (LinearMap.range ((f : E →ₗ[𝕜] F).cokerToCokerComp (g : F →ₗ[𝕜] P))) *
          finrank 𝕜 (parameterProj g D₂).range) * φ γ) • (α ⊗ₜ ξ) := by
  have hk := finrank_ker_comp_eq f g
  have hd := finrank_quotient_range_comp_eq f g
  have hV := finrank_range_parameterProj_comp hf hg hh
  -- The four-term formula lists the kernel of `g ∘ f`, then lifts of the parameters spanning the
  -- range of the parameter projection, then parameters lifting a basis of the cokernel.
  have hβ' := coe_neg_one_pow_smul_stabilizedKer_comp d hβ hk hV
  have hγ' := coe_neg_one_pow_smul_parameters_comp d hγ hV hd
  have hξ' := apply_ιMulti_parameterToCoker_comp d hd hε hξ
  rw [detLineStabilizationEquiv_apply, detLineCoprodEquiv_def]
  have key := TauCeti.detLineFourTermEquiv_tmul_eq_smul_tmul
    (kerCoprodHom_injective (g ∘L f) ((g ∘L D₁).coprod D₂))
    (exact_kerCoprodHom_parameterProj _ _) (exact_parameterProj_parameterToCoker _ _)
    ((parameterToCoker_surjective_iff_coprod_surjective _ _).2 hh) _ _ _ hβ' hγ' φ hξ'
  have hα' : exteriorPower.ιMulti 𝕜 _ (Fin.append (Submodule.inclusion
      (LinearMap.ker_le_ker_comp (f : E →ₗ[𝕜] F) (g : F →ₗ[𝕜] P)) ∘ Module.finBasis 𝕜 f.ker) d.v ∘
        Fin.cast hk) = α :=
    Subtype.ext (by rw [exteriorPower.ιMulti_apply_coe, TauCeti.ExteriorAlgebra.ιMulti_comp_cast,
      hα])
  rw [← TensorProduct.smul_tmul', map_smul, map_smul, smul_eq_mul] at key
  -- Cancel the sign `(-1) ^ (r m₁)`, which squares to one.
  have key' := congrArg (((-1 : 𝕜) ^ (finrank 𝕜 (LinearMap.range
    ((f : E →ₗ[𝕜] F).kerCompToKer (g : F →ₗ[𝕜] P))) * finrank 𝕜 (parameterProj f D₁).range)) • ·)
    key
  simp only [smul_smul, TauCeti.neg_one_pow_mul_neg_one_pow, one_smul] at key'
  rw [key', ← hα', smul_smul, pow_add, pow_add]
  congr 1
  ring

/-! ### Linear independence of the adapted families -/

omit [FiniteDimensional 𝕜 Λ₁] [FiniteDimensional 𝕜 Λ₂] [FiniteDimensional 𝕜 f.ker]
  [FiniteDimensional 𝕜 g.ker] [FiniteDimensional 𝕜 (F ⧸ f.range)]
  [FiniteDimensional 𝕜 (P ⧸ g.range)] in
/-- The images of `v` in `ker g` followed by `w` are linearly independent. -/
private theorem CompData.linearIndependent_kerCompToKer_append (d : CompData f D₁ g D₂) :
    LinearIndependent 𝕜
      (Fin.append ((f : E →ₗ[𝕜] F).kerCompToKer (g : F →ₗ[𝕜] P) ∘ d.v) d.w) :=
  d.li_v.fin_append_of_linearIndependent_comp ((f : E →ₗ[𝕜] F).kerToCoker (g : F →ₗ[𝕜] P))
    (fun _ ↦ ((f : E →ₗ[𝕜] F).exact_kerCompToKer_kerToCoker
      (g : F →ₗ[𝕜] P)).apply_apply_eq_zero _) d.li_w

omit [FiniteDimensional 𝕜 Λ₁] [FiniteDimensional 𝕜 Λ₂] [FiniteDimensional 𝕜 f.ker]
  [FiniteDimensional 𝕜 g.ker] [FiniteDimensional 𝕜 (F ⧸ f.range)]
  [FiniteDimensional 𝕜 (P ⧸ g.range)] in
/-- The classes of `w` in `coker f` followed by `x` are linearly independent. -/
private theorem CompData.linearIndependent_kerToCoker_append (d : CompData f D₁ g D₂) :
    LinearIndependent 𝕜
      (Fin.append ((f : E →ₗ[𝕜] F).kerToCoker (g : F →ₗ[𝕜] P) ∘ d.w) d.x) :=
  d.li_w.fin_append_of_linearIndependent_comp
    ((f : E →ₗ[𝕜] F).cokerToCokerComp (g : F →ₗ[𝕜] P))
    (fun _ ↦ ((f : E →ₗ[𝕜] F).exact_kerToCoker_cokerToCokerComp
      (g : F →ₗ[𝕜] P)).apply_apply_eq_zero _) d.li_x

omit [FiniteDimensional 𝕜 Λ₁] [FiniteDimensional 𝕜 Λ₂] [FiniteDimensional 𝕜 f.ker]
  [FiniteDimensional 𝕜 g.ker] [FiniteDimensional 𝕜 (F ⧸ f.range)]
  [FiniteDimensional 𝕜 (P ⧸ g.range)] in
/-- The classes `y` in `coker (g ∘ f)` map to the classes of `D₂ ∘ z₂` in `coker g`. -/
private theorem CompData.factor_comp_y (d : CompData f D₁ g D₂) :
    ⇑(Submodule.factor (LinearMap.range_comp_le_range (f : E →ₗ[𝕜] F) (g : F →ₗ[𝕜] P))) ∘ d.y =
      parameterToCoker g D₂ ∘ d.z₂ := by
  funext j
  simp [CompData.y, parameterToCoker_apply]

omit [FiniteDimensional 𝕜 Λ₁] [FiniteDimensional 𝕜 Λ₂] [FiniteDimensional 𝕜 f.ker]
  [FiniteDimensional 𝕜 g.ker] [FiniteDimensional 𝕜 (F ⧸ f.range)]
  [FiniteDimensional 𝕜 (P ⧸ g.range)] in
/-- The images of `x` in `coker (g ∘ f)` followed by `y` are linearly independent. -/
private theorem CompData.linearIndependent_cokerToCokerComp_append (d : CompData f D₁ g D₂) :
    LinearIndependent 𝕜
      (Fin.append ((f : E →ₗ[𝕜] F).cokerToCokerComp (g : F →ₗ[𝕜] P) ∘ d.x) d.y) :=
  d.li_x.fin_append_of_linearIndependent_comp (Submodule.factor
    (LinearMap.range_comp_le_range (f : E →ₗ[𝕜] F) (g : F →ₗ[𝕜] P)))
    (fun _ ↦ ((f : E →ₗ[𝕜] F).exact_cokerToCokerComp_factor
      (g : F →ₗ[𝕜] P)).apply_apply_eq_zero _) (by rw [d.factor_comp_y]; exact d.li_z₂)

omit [FiniteDimensional 𝕜 Λ₁] [FiniteDimensional 𝕜 Λ₂] [FiniteDimensional 𝕜 g.ker]
  [FiniteDimensional 𝕜 (F ⧸ f.range)] [FiniteDimensional 𝕜 (P ⧸ g.range)] in
/-- The family spanning the stabilized kernel of `f` is linearly independent. -/
private theorem CompData.linearIndependent_κ₁ (d : CompData f D₁ g D₂) :
    LinearIndependent 𝕜 (Fin.append (kerCoprodHom f D₁ ∘ Module.finBasis 𝕜 f.ker) d.v₁) :=
  ((Module.finBasis 𝕜 f.ker).linearIndependent.map' _
    (LinearMap.ker_eq_bot.2 (kerCoprodHom_injective f D₁))).fin_append_of_linearIndependent_comp
    (parameterProj f D₁ : (f.coprod D₁).ker →ₗ[𝕜] Λ₁)
    (fun _ ↦ (exact_kerCoprodHom_parameterProj f D₁).apply_apply_eq_zero _) d.li_v₁

omit [FiniteDimensional 𝕜 Λ₁] [FiniteDimensional 𝕜 Λ₂] [FiniteDimensional 𝕜 f.ker]
  [FiniteDimensional 𝕜 g.ker] [FiniteDimensional 𝕜 (F ⧸ f.range)]
  [FiniteDimensional 𝕜 (P ⧸ g.range)] in
/-- The family spanning the stabilized kernel of `g` is linearly independent. -/
private theorem CompData.linearIndependent_κ₂ (d : CompData f D₁ g D₂) :
    LinearIndependent 𝕜 (Fin.append (Fin.append (kerCoprodHom g D₂ ∘
      (f : E →ₗ[𝕜] F).kerCompToKer (g : F →ₗ[𝕜] P) ∘ d.v) (kerCoprodHom g D₂ ∘ d.w)) d.v₂) := by
  refine LinearIndependent.fin_append_of_linearIndependent_comp ?_
    (parameterProj g D₂ : (g.coprod D₂).ker →ₗ[𝕜] Λ₂) (fun i ↦ ?_) d.li_v₂
  · rw [← Fin.comp_append]
    exact d.linearIndependent_kerCompToKer_append.map' _
      (LinearMap.ker_eq_bot.2 (kerCoprodHom_injective g D₂))
  · refine Fin.addCases (fun _ ↦ ?_) (fun _ ↦ ?_) i <;>
      simp only [Fin.append_left, Fin.append_right, Function.comp_apply] <;>
      exact (exact_kerCoprodHom_parameterProj g D₂).apply_apply_eq_zero _

omit [FiniteDimensional 𝕜 (P ⧸ g.range)] in
/-- The parameters of the composite stabilization: the exterior product `c₁` of the parameters
`p₁ ∘ v₁`, `zw`, `zx` of `f`, the exterior product `c₂` of the parameters `p₂ ∘ v₂`, `z₂` of `g`,
and their product, which lists the parameters of `g ∘ f`, lifting those of `g`. -/
private theorem CompData.exists_parameters (d : CompData f D₁ g D₂)
    (hf : Function.Surjective (f.coprod D₁)) (hg : Function.Surjective (g.coprod D₂)) :
    ∃ (c₁ : TauCeti.detLine 𝕜 Λ₁) (c₂ : TauCeti.detLine 𝕜 Λ₂),
      (c₁ : ExteriorAlgebra 𝕜 Λ₁) = ExteriorAlgebra.ιMulti 𝕜 _
        (Fin.append (parameterProj f D₁ ∘ d.v₁) (Fin.append d.zw d.zx)) ∧
      (c₂ : ExteriorAlgebra 𝕜 Λ₂) = ExteriorAlgebra.ιMulti 𝕜 _
        (Fin.append (parameterProj g D₂ ∘ d.v₂) d.z₂) ∧
      (TauCeti.detLineProdEquiv 𝕜 Λ₁ Λ₂ (c₁ ⊗ₜ c₂) : ExteriorAlgebra 𝕜 (Λ₁ × Λ₂)) =
        ExteriorAlgebra.ιMulti 𝕜 _ (Fin.append
          (LinearMap.inl 𝕜 Λ₁ Λ₂ ∘ Fin.append (parameterProj f D₁ ∘ d.v₁) (Fin.append d.zw d.zx))
          (Fin.append d.lift₂ (LinearMap.inr 𝕜 Λ₁ Λ₂ ∘ d.z₂))) := by
  have hb := (f : E →ₗ[𝕜] F).finrank_quotient_range_eq_finrank_range_kerToCoker_add
    (g : F →ₗ[𝕜] P)
  obtain ⟨hl₁, -⟩ := finrank_stabilization hf
  obtain ⟨hl₂, -⟩ := finrank_stabilization hg
  have hl₁' : finrank 𝕜 Λ₁ = finrank 𝕜 (parameterProj f D₁).range +
      (finrank 𝕜 (LinearMap.range ((f : E →ₗ[𝕜] F).kerToCoker (g : F →ₗ[𝕜] P))) +
        finrank 𝕜 (LinearMap.range ((f : E →ₗ[𝕜] F).cokerToCokerComp (g : F →ₗ[𝕜] P)))) := by
    omega
  have hL : ⇑(LinearMap.snd 𝕜 Λ₁ Λ₂) ∘ Fin.append d.lift₂ (LinearMap.inr 𝕜 Λ₁ Λ₂ ∘ d.z₂) =
      Fin.append (parameterProj g D₂ ∘ d.v₂) d.z₂ :=
    funext fun i ↦ Fin.addCases (fun _ ↦ by simp [CompData.lift₂]) (fun _ ↦ by simp) i
  refine ⟨exteriorPower.ιMulti 𝕜 _ (Fin.append (parameterProj f D₁ ∘ d.v₁)
      (Fin.append d.zw d.zx) ∘ Fin.cast hl₁'),
    exteriorPower.ιMulti 𝕜 _ (⇑(LinearMap.snd 𝕜 Λ₁ Λ₂) ∘
      (Fin.append d.lift₂ (LinearMap.inr 𝕜 Λ₁ Λ₂ ∘ d.z₂) ∘ Fin.cast hl₂)), ?_, ?_, ?_⟩
  · rw [exteriorPower.ιMulti_apply_coe, TauCeti.ExteriorAlgebra.ιMulti_comp_cast]
  · rw [exteriorPower.ιMulti_apply_coe, ← Function.comp_assoc, hL,
      TauCeti.ExteriorAlgebra.ιMulti_comp_cast]
  · rw [TauCeti.coe_detLineProdEquiv_tmul_snd_comp]
    simp only [← ExteriorAlgebra.ιMulti_mul_ιMulti, ← Function.comp_assoc,
      TauCeti.ExteriorAlgebra.ιMulti_comp_cast]

/-- Two factors of `(-1) ^ b` and `(-1) ^ c` are absorbed by the sign `(-1) ^ (a + b + c)`. -/
private theorem neg_one_pow_mul_mul_eq {a b c : ℕ} (x y : 𝕜) :
    (-1 : 𝕜) ^ a * (x * y) = (-1) ^ (a + b + c) * ((-1) ^ b * x) * ((-1) ^ c * y) := by
  rw [pow_add, pow_add]
  linear_combination (-((-1 : 𝕜) ^ a * (x * y))) * TauCeti.neg_one_pow_mul_neg_one_pow (α := 𝕜) b +
    (-((-1 : 𝕜) ^ a * (x * y) * ((-1 : 𝕜) ^ b) ^ 2)) *
      TauCeti.neg_one_pow_mul_neg_one_pow (α := 𝕜) c

/-- The exterior products adapted to `d`: `κ₁` spans the determinant line of the stabilized kernel
of `f`, `κ₂` that of `g`, and `β` that of `g ∘ f`, and the normalized stabilization of `g ∘ f` of
`β` tensored with the product of `φ₁` and `φ₂` corresponds under the composition law to the
tensor product of the normalized stabilizations of `κ₁ ⊗ φ₁` and of `κ₂ ⊗ φ₂`, up to sign. -/
private theorem exists_comp_stab (d : CompData f D₁ g D₂) (hf : Function.Surjective (f.coprod D₁))
    (hg : Function.Surjective (g.coprod D₂))
    (hh : Function.Surjective ((g ∘L f).coprod ((g ∘L D₁).coprod D₂)))
    [FiniteDimensional 𝕜 (g ∘L f).ker] [FiniteDimensional 𝕜 (P ⧸ (g ∘L f).range)] :
    ∃ (κ₁ : TauCeti.detLine 𝕜 (f.coprod D₁).ker) (η₁ : Dual 𝕜 (TauCeti.detLine 𝕜 (f.coprod D₁).ker))
      (κ₂ : TauCeti.detLine 𝕜 (g.coprod D₂).ker) (η₂ : Dual 𝕜 (TauCeti.detLine 𝕜 (g.coprod D₂).ker))
      (β : TauCeti.detLine 𝕜 ((g ∘L f).coprod ((g ∘L D₁).coprod D₂)).ker),
      (κ₁ : ExteriorAlgebra 𝕜 (f.coprod D₁).ker) = ExteriorAlgebra.ιMulti 𝕜 _
        (Fin.append (kerCoprodHom f D₁ ∘ Module.finBasis 𝕜 f.ker) d.v₁) ∧ η₁ κ₁ = 1 ∧
      (κ₂ : ExteriorAlgebra 𝕜 (g.coprod D₂).ker) = ExteriorAlgebra.ιMulti 𝕜 _
        (Fin.append (Fin.append (kerCoprodHom g D₂ ∘
          (f : E →ₗ[𝕜] F).kerCompToKer (g : F →ₗ[𝕜] P) ∘ d.v) (kerCoprodHom g D₂ ∘ d.w)) d.v₂) ∧
      η₂ κ₂ = 1 ∧
      (β : ExteriorAlgebra 𝕜 ((g ∘L f).coprod ((g ∘L D₁).coprod D₂)).ker) =
        ExteriorAlgebra.ιMulti 𝕜 _ (Fin.append
          (Fin.append (kerCoprodHom (g ∘L f) ((g ∘L D₁).coprod D₂) ∘
            Submodule.inclusion (LinearMap.ker_le_ker_comp (f : E →ₗ[𝕜] F) (g : F →ₗ[𝕜] P)) ∘
              Module.finBasis 𝕜 f.ker) d.ι₁)
          (Fin.append (kerCoprodHom (g ∘L f) ((g ∘L D₁).coprod D₂) ∘ d.v)
            (Fin.append d.σw d.σv₂))) ∧
      ∀ (φ₁ : Dual 𝕜 (TauCeti.detLine 𝕜 Λ₁)) (φ₂ : Dual 𝕜 (TauCeti.detLine 𝕜 Λ₂)),
        (f : E →ₗ[𝕜] F).detLineCompEquiv (g : F →ₗ[𝕜] P)
            (detLineStabilizationEquiv (g ∘L f) ((g ∘L D₁).coprod D₂) hh
              (β ⊗ₜ TauCeti.detLineDualProdEquiv 𝕜 Λ₁ Λ₂ (φ₁ ⊗ₜ φ₂))) =
          (-1 : 𝕜) ^ (finrank 𝕜 (P ⧸ (g ∘L f).range) * finrank 𝕜 (Λ₁ × Λ₂) +
              finrank 𝕜 (LinearMap.range ((f : E →ₗ[𝕜] F).kerCompToKer (g : F →ₗ[𝕜] P))) *
                finrank 𝕜 (parameterProj f D₁).range +
              finrank 𝕜 (LinearMap.range ((f : E →ₗ[𝕜] F).cokerToCokerComp (g : F →ₗ[𝕜] P))) *
                finrank 𝕜 (parameterProj g D₂).range +
            finrank 𝕜 (F ⧸ f.range) * finrank 𝕜 Λ₁ + finrank 𝕜 (P ⧸ g.range) * finrank 𝕜 Λ₂) •
            (detLineStabilizationEquiv f D₁ hf (κ₁ ⊗ₜ φ₁) ⊗ₜ
              detLineStabilizationEquiv g D₂ hg (κ₂ ⊗ₜ φ₂)) := by
  have : FiniteDimensional 𝕜 (LinearMap.ker ((g : F →ₗ[𝕜] P) ∘ₗ (f : E →ₗ[𝕜] F))) :=
    ‹FiniteDimensional 𝕜 (g ∘L f).ker›
  have : FiniteDimensional 𝕜 (P ⧸ LinearMap.range ((g : F →ₗ[𝕜] P) ∘ₗ (f : E →ₗ[𝕜] F))) :=
    ‹FiniteDimensional 𝕜 (P ⧸ (g ∘L f).range)›
  -- Dimension counts.
  have hk := finrank_ker_comp_eq f g
  have hd := finrank_quotient_range_comp_eq f g
  have hV := finrank_range_parameterProj_comp hf hg hh
  have hc := (f : E →ₗ[𝕜] F).finrank_ker_eq_finrank_range_kerCompToKer_add (g : F →ₗ[𝕜] P)
  have hb := (f : E →ₗ[𝕜] F).finrank_quotient_range_eq_finrank_range_kerToCoker_add
    (g : F →ₗ[𝕜] P)
  obtain ⟨-, hK₁⟩ := finrank_stabilization hf
  obtain ⟨-, hK₂⟩ := finrank_stabilization hg
  obtain ⟨-, hK⟩ := finrank_stabilization hh
  -- The exterior products spanning the three stabilized kernels.
  obtain ⟨κ₁, η₁, hκ₁, hη₁⟩ :=
    TauCeti.exists_detLine_coe_eq_ιMulti_and_apply_eq_one (by omega) d.linearIndependent_κ₁
  obtain ⟨κ₂, η₂, hκ₂, hη₂⟩ :=
    TauCeti.exists_detLine_coe_eq_ιMulti_and_apply_eq_one (by omega) d.linearIndependent_κ₂
  obtain ⟨β, hβ⟩ := TauCeti.exists_detLine_coe_eq_ιMulti (R := 𝕜)
    (V := ((g ∘L f).coprod ((g ∘L D₁).coprod D₂)).ker) (by omega) (Fin.append
      (Fin.append (kerCoprodHom (g ∘L f) ((g ∘L D₁).coprod D₂) ∘
        Submodule.inclusion (LinearMap.ker_le_ker_comp (f : E →ₗ[𝕜] F) (g : F →ₗ[𝕜] P)) ∘
          Module.finBasis 𝕜 f.ker) d.ι₁)
      (Fin.append (kerCoprodHom (g ∘L f) ((g ∘L D₁).coprod D₂) ∘ d.v) (Fin.append d.σw d.σv₂)))
  refine ⟨κ₁, η₁, κ₂, η₂, β, hκ₁, hη₁, hκ₂, hη₂, hβ, fun φ₁ φ₂ ↦ ?_⟩
  -- The exterior products and normalized functionals of the kernel–cokernel sequence of `g ∘ f`.
  obtain ⟨α, hα⟩ := TauCeti.exists_detLine_coe_eq_ιMulti (R := 𝕜) (V := (g ∘L f).ker) hk
    (Fin.append (Submodule.inclusion (LinearMap.ker_le_ker_comp (f : E →ₗ[𝕜] F)
      (g : F →ₗ[𝕜] P)) ∘ Module.finBasis 𝕜 f.ker) d.v)
  obtain ⟨ε, ξ, hε, hξ⟩ := TauCeti.exists_detLine_coe_eq_ιMulti_and_apply_eq_one
    (W := P ⧸ (g ∘L f).range) hd d.linearIndependent_cokerToCokerComp_append
  obtain ⟨δ, ψ, hδ, hψ⟩ := TauCeti.exists_detLine_coe_eq_ιMulti_and_apply_eq_one
    (W := F ⧸ f.range) hb d.linearIndependent_kerToCoker_append
  obtain ⟨γg, hγg⟩ := TauCeti.exists_detLine_coe_eq_ιMulti (R := 𝕜) (V := g.ker) hc
    (Fin.append ((f : E →ₗ[𝕜] F).kerCompToKer (g : F →ₗ[𝕜] P) ∘ d.v) d.w)
  obtain ⟨χ, hχ⟩ := Projective.exists_dual_eq_one 𝕜
    ((exteriorPower.ιMulti_ne_zero_iff _).2 d.li_z₂)
  -- The parameters: `c₁` lists those of `f`, `c₂` those of `g`, and their product lists the
  -- parameters of the composite, lifting those of `g`.
  obtain ⟨c₁, c₂, hc₁, hc₂, hγ⟩ := d.exists_parameters hf hg
  -- The composition law reads `α ⊗ ξ` through the families of `d`, with `ξ ε = 1`.
  refine (congrArg _ (stab_comp d hf hg hh hβ hγ hα hε hξ _)).trans
    ((LinearEquiv.map_smul _ _ _).trans ((congrArg (_ • ·) (LinearMap.detLineCompEquiv_tmul
      (f : E →ₗ[𝕜] F) (g : F →ₗ[𝕜] P) _ d.v d.w d.x d.y hα hγg hδ hε ξ hψ
      (by rw [d.factor_comp_y]; exact hχ))).trans ?_))
  -- `ξ ε` appears with the cokernel of `g ∘ f` spelled through the composite of linear maps, equal
  -- to that of `g ∘L f` only up to unfolding the coercion, hence `erw`.
  erw [hξ]
  rw [one_smul, stab_left d hf hκ₁ hc₁ hδ hψ φ₁, stab_right d hg hκ₂ hc₂ hγg hχ φ₂,
    TauCeti.detLineDualProdEquiv_tmul_apply, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul,
    smul_smul, smul_smul]
  congr 1
  exact neg_one_pow_mul_mul_eq (𝕜 := 𝕜) _ _

omit [FiniteDimensional 𝕜 Λ₁] [FiniteDimensional 𝕜 Λ₂] [FiniteDimensional 𝕜 f.ker]
  [FiniteDimensional 𝕜 g.ker] [FiniteDimensional 𝕜 (F ⧸ f.range)]
  [FiniteDimensional 𝕜 (P ⧸ g.range)] in
/-- The second components of the coordinates of the last three blocks `(v, 0)`, `σw`, `σv₂` of the
stabilized kernel of `g ∘ f` are the coordinates under `q₂` of the vectors listed in `κ₂`. -/
private theorem snd_detLineCongr_compKerCoord (d : CompData f D₁ g D₂)
    (h₁ : ((f.coprod D₁).prod q₁).IsInvertible)
    (h₂ : ((g.coprod D₂).prod q₂).IsInvertible) {κ₂ : TauCeti.detLine 𝕜 (g.coprod D₂).ker}
    (hκ₂ : (κ₂ : ExteriorAlgebra 𝕜 (g.coprod D₂).ker) = ExteriorAlgebra.ιMulti 𝕜 _
      (Fin.append (Fin.append (kerCoprodHom g D₂ ∘ (f : E →ₗ[𝕜] F).kerCompToKer (g : F →ₗ[𝕜] P) ∘
        d.v) (kerCoprodHom g D₂ ∘ d.w)) d.v₂))
    (hG₂ : finrank 𝕜 G₂ =
      finrank 𝕜 (LinearMap.range ((f : E →ₗ[𝕜] F).kerCompToKer (g : F →ₗ[𝕜] P))) +
        (finrank 𝕜 (LinearMap.range ((f : E →ₗ[𝕜] F).kerToCoker (g : F →ₗ[𝕜] P))) +
          finrank 𝕜 (parameterProj g D₂).range)) :
    exteriorPower.ιMulti 𝕜 _ (LinearMap.snd 𝕜 G₁ G₂ ∘
      ((⇑(kerEquivOfProd _ _ (h₁.prod_coprod_compKerCoord h₂)).toLinearEquiv.symm ∘
        Fin.append (kerCoprodHom (g ∘L f) ((g ∘L D₁).coprod D₂) ∘ d.v)
          (Fin.append d.σw d.σv₂)) ∘ Fin.cast hG₂)) =
      (kerEquivOfProd _ q₂ h₂).toLinearEquiv.symm.detLineCongr κ₂ := by
  set e := (kerEquivOfProd _ _ (h₁.prod_coprod_compKerCoord h₂)).toLinearEquiv.symm with he
  set e₂ := (kerEquivOfProd _ q₂ h₂).toLinearEquiv.symm with he₂
  -- `kerCoprodHom_apply` for the kernel of `g ∘ f` spelled through the composite of linear maps;
  -- the two spellings are only equal up to unfolding the coercion of `g ∘L f`, so it is used with
  -- `erw`.
  have hk (x : LinearMap.ker ((g : F →ₗ[𝕜] P) ∘ₗ (f : E →ₗ[𝕜] F))) :
      (kerCoprodHom (g ∘L f) ((g ∘L D₁).coprod D₂) x : E × (Λ₁ × Λ₂)) = ((x : E), 0) :=
    kerCoprodHom_apply (g ∘L f) ((g ∘L D₁).coprod D₂) x
  have hb₃ : LinearMap.snd 𝕜 G₁ G₂ ∘ e ∘ (kerCoprodHom (g ∘L f) ((g ∘L D₁).coprod D₂) ∘ d.v) =
      e₂ ∘ (kerCoprodHom g D₂ ∘ (f : E →ₗ[𝕜] F).kerCompToKer (g : F →ₗ[𝕜] P) ∘ d.v) := by
    funext i
    simp only [Function.comp_apply, he, he₂, ContinuousLinearEquiv.coe_symm_toLinearEquiv,
      kerEquivOfProd_symm_apply]
    erw [hk]
    simp
  have hb₄ : LinearMap.snd 𝕜 G₁ G₂ ∘ e ∘ d.σw = e₂ ∘ (kerCoprodHom g D₂ ∘ d.w) := by
    funext i
    simp [he, he₂, CompData.σw, d.hew i]
  have hb₅ : LinearMap.snd 𝕜 G₁ G₂ ∘ e ∘ d.σv₂ = e₂ ∘ d.v₂ := by
    funext j
    simp [he, he₂, CompData.σv₂, d.he₂ j]
  refine Subtype.ext ?_
  rw [exteriorPower.ιMulti_apply_coe, LinearEquiv.coe_detLineCongr_of_coe_eq_ιMulti e₂ hκ₂]
  simp only [Fin.comp_append, Fin.comp_append_comp_cast, TauCeti.ExteriorAlgebra.ιMulti_comp_cast,
    ← ExteriorAlgebra.ιMulti_mul_ιMulti, hb₃, hb₄, hb₅, mul_assoc]

omit [FiniteDimensional 𝕜 (F ⧸ f.range)] [FiniteDimensional 𝕜 (P ⧸ g.range)] in
/-- **The composite coordinate splits the stabilized kernel.** The coordinate
`ContinuousLinearMap.compKerCoord f D₁ q₁ q₂` sends the exterior product `β` of the vectors
`(u, 0)`, `ι₁`, `(v, 0)`, `σw`, `σv₂` of the stabilized kernel of `g ∘ f` to the product of the
images of `κ₁` under `q₁` and of `κ₂` under `q₂`: the first two blocks are `(q₁ (u, 0), 0)` and
`(q₁ v₁, 0)`, and the second components of the last three blocks are the images of `κ₂`. -/
private theorem detLineCongr_compKerCoord (d : CompData f D₁ g D₂) [FiniteDimensional 𝕜 G₁]
    [FiniteDimensional 𝕜 G₂] (h₁ : ((f.coprod D₁).prod q₁).IsInvertible)
    (h₂ : ((g.coprod D₂).prod q₂).IsInvertible) {κ₁ : TauCeti.detLine 𝕜 (f.coprod D₁).ker}
    (hκ₁ : (κ₁ : ExteriorAlgebra 𝕜 (f.coprod D₁).ker) = ExteriorAlgebra.ιMulti 𝕜 _
      (Fin.append (kerCoprodHom f D₁ ∘ Module.finBasis 𝕜 f.ker) d.v₁))
    {κ₂ : TauCeti.detLine 𝕜 (g.coprod D₂).ker}
    (hκ₂ : (κ₂ : ExteriorAlgebra 𝕜 (g.coprod D₂).ker) = ExteriorAlgebra.ιMulti 𝕜 _
      (Fin.append (Fin.append (kerCoprodHom g D₂ ∘ (f : E →ₗ[𝕜] F).kerCompToKer (g : F →ₗ[𝕜] P) ∘
        d.v) (kerCoprodHom g D₂ ∘ d.w)) d.v₂))
    {β : TauCeti.detLine 𝕜 ((g ∘L f).coprod ((g ∘L D₁).coprod D₂)).ker}
    (hβ : (β : ExteriorAlgebra 𝕜 ((g ∘L f).coprod ((g ∘L D₁).coprod D₂)).ker) =
      ExteriorAlgebra.ιMulti 𝕜 _ (Fin.append
        (Fin.append (kerCoprodHom (g ∘L f) ((g ∘L D₁).coprod D₂) ∘
          Submodule.inclusion (LinearMap.ker_le_ker_comp (f : E →ₗ[𝕜] F) (g : F →ₗ[𝕜] P)) ∘
            Module.finBasis 𝕜 f.ker) d.ι₁)
        (Fin.append (kerCoprodHom (g ∘L f) ((g ∘L D₁).coprod D₂) ∘ d.v)
          (Fin.append d.σw d.σv₂)))) :
    (kerEquivOfProd _ _ (h₁.prod_coprod_compKerCoord h₂)).toLinearEquiv.symm.detLineCongr β =
      TauCeti.detLineProdEquiv 𝕜 G₁ G₂
        ((kerEquivOfProd _ q₁ h₁).toLinearEquiv.symm.detLineCongr κ₁ ⊗ₜ
          (kerEquivOfProd _ q₂ h₂).toLinearEquiv.symm.detLineCongr κ₂) := by
  set e := (kerEquivOfProd _ _ (h₁.prod_coprod_compKerCoord h₂)).toLinearEquiv.symm with he
  set e₁ := (kerEquivOfProd _ q₁ h₁).toLinearEquiv.symm with he₁
  set e₂ := (kerEquivOfProd _ q₂ h₂).toLinearEquiv.symm with he₂
  have hc := (f : E →ₗ[𝕜] F).finrank_ker_eq_finrank_range_kerCompToKer_add (g : F →ₗ[𝕜] P)
  obtain ⟨-, hK₁⟩ := finrank_stabilization (surjective_of_isInvertible_prod h₁)
  obtain ⟨-, hK₂⟩ := finrank_stabilization (surjective_of_isInvertible_prod h₂)
  have hG₁ : finrank 𝕜 G₁ = finrank 𝕜 f.ker + finrank 𝕜 (parameterProj f D₁).range :=
    e₁.finrank_eq.symm.trans hK₁
  have hG₂ : finrank 𝕜 G₂ =
      finrank 𝕜 (LinearMap.range ((f : E →ₗ[𝕜] F).kerCompToKer (g : F →ₗ[𝕜] P))) +
        (finrank 𝕜 (LinearMap.range ((f : E →ₗ[𝕜] F).kerToCoker (g : F →ₗ[𝕜] P))) +
          finrank 𝕜 (parameterProj g D₂).range) := by
    have := e₂.finrank_eq
    omega
  -- `kerCoprodHom_apply` for the kernel of `g ∘ f` spelled through the composite of linear maps;
  -- the two spellings are only equal up to unfolding the coercion of `g ∘L f`, so it is used with
  -- `erw`.
  have hk (x : LinearMap.ker ((g : F →ₗ[𝕜] P) ∘ₗ (f : E →ₗ[𝕜] F))) :
      (kerCoprodHom (g ∘L f) ((g ∘L D₁).coprod D₂) x : E × (Λ₁ × Λ₂)) = ((x : E), 0) :=
    kerCoprodHom_apply (g ∘L f) ((g ∘L D₁).coprod D₂) x
  -- The coordinates of the five blocks of `β`.
  have hb₁ : e ∘ (kerCoprodHom (g ∘L f) ((g ∘L D₁).coprod D₂) ∘
      Submodule.inclusion (LinearMap.ker_le_ker_comp (f : E →ₗ[𝕜] F) (g : F →ₗ[𝕜] P)) ∘
        Module.finBasis 𝕜 f.ker) =
      LinearMap.inl 𝕜 G₁ G₂ ∘ e₁ ∘ (kerCoprodHom f D₁ ∘ Module.finBasis 𝕜 f.ker) := by
    funext i
    have hu : f (Module.finBasis 𝕜 f.ker i : E) = 0 := (Module.finBasis 𝕜 f.ker i).property
    simp only [Function.comp_apply, he, he₁, ContinuousLinearEquiv.coe_symm_toLinearEquiv,
      kerEquivOfProd_symm_apply]
    erw [hk]
    refine Prod.ext ?_ ?_ <;> simp [hu, Prod.mk_zero_zero]
  have hb₂ : e ∘ d.ι₁ = LinearMap.inl 𝕜 G₁ G₂ ∘ e₁ ∘ d.v₁ := by
    funext i
    have hv : f (d.v₁ i : E × Λ₁).1 + D₁ (d.v₁ i : E × Λ₁).2 = 0 := by
      simpa using (d.v₁ i).property
    refine Prod.ext ?_ ?_ <;> simp [he, he₁, CompData.ι₁, hv, Prod.mk_zero_zero]
  -- The images of `κ₁` and `κ₂`, as exterior products of families of the right lengths.
  have hu : exteriorPower.ιMulti 𝕜 _ ((e₁ ∘ Fin.append (kerCoprodHom f D₁ ∘
      Module.finBasis 𝕜 f.ker) d.v₁) ∘ Fin.cast hG₁) = e₁.detLineCongr κ₁ :=
    Subtype.ext (by rw [exteriorPower.ιMulti_apply_coe, TauCeti.ExteriorAlgebra.ιMulti_comp_cast,
      LinearEquiv.coe_detLineCongr_of_coe_eq_ιMulti e₁ hκ₁])
  have hw := snd_detLineCongr_compKerCoord d h₁ h₂ hκ₂ hG₂
  rw [← he, ← he₂] at hw
  rw [← hu, ← hw]
  refine Subtype.ext ?_
  rw [TauCeti.coe_detLineProdEquiv_tmul_snd_comp,
    LinearEquiv.coe_detLineCongr_of_coe_eq_ιMulti e hβ]
  simp only [Fin.comp_append, Fin.comp_append_comp_cast, TauCeti.ExteriorAlgebra.ιMulti_comp_cast,
    ← ExteriorAlgebra.ιMulti_mul_ιMulti, hb₁, hb₂, mul_assoc]

/-- Every element of `det L ⊗ M` is `κ ⊗ φ` for some `φ`, when `κ` spans the line `det L`, as
witnessed by a functional `η` with `η κ = 1`. -/
private theorem exists_eq_tmul_of_apply_eq_one {L M : Type*} [AddCommGroup L] [Module 𝕜 L]
    [FiniteDimensional 𝕜 L] [AddCommGroup M] [Module 𝕜 M] {κ : TauCeti.detLine 𝕜 L}
    {η : Dual 𝕜 (TauCeti.detLine 𝕜 L)} (hη : η κ = 1) (y : TauCeti.detLine 𝕜 L ⊗[𝕜] M) :
    ∃ m, y = κ ⊗ₜ m := by
  have hspan : Submodule.span 𝕜 {κ} = ⊤ := Submodule.eq_top_iff'.2 fun z ↦
    Module.Invertible.apply_smul_eq_self hη z ▸
      Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self κ)
  obtain ⟨m, hm⟩ := TensorProduct.exists_eq_tmul_of_span_singleton_eq_top hspan
    (TensorProduct.comm 𝕜 _ _ y)
  exact ⟨m, by
    rw [← (TensorProduct.comm 𝕜 _ _).symm_apply_apply y, hm, TensorProduct.comm_symm_tmul]⟩

/-- The parity count behind `ContinuousLinearMap.detLineChartEquiv_neg_one_pow_smul_comp`: with
`b = s + t`, `bh = t + d`, `l₁ = m₁ + b`, `l₂ = m₂ + d` and `G₂ = r + s + m₂`, the sign of the
composite kernel chart times the normalization `(-1) ^ (b r + t d)` is `(-1) ^ (l₁ (G₂ + l₂))`. The
two exponents differ by `2 (d m₂ + d² + t m₁ + t d + t² + s t - m₁ m₂ - s m₂)`. -/
private theorem neg_one_pow_comp_sign {b r s t d bh l₁ l₂ m₁ m₂ G₂ : ℕ} (hb : b = s + t)
    (hbh : bh = t + d) (hl₁ : l₁ = m₁ + b) (hl₂ : l₂ = m₂ + d) (hG : G₂ = r + s + m₂) :
    (-1 : 𝕜) ^ (b * r + t * d + (bh * (l₁ + l₂) + r * m₁ + t * m₂ + b * l₁ + d * l₂)) =
      (-1) ^ (l₁ * (G₂ + l₂)) := by
  subst hb hbh hl₁ hl₂ hG
  rw [← TauCeti.neg_one_pow_add_two_mul _ (m₁ * m₂ + s * m₂)]
  conv_rhs => rw [← TauCeti.neg_one_pow_add_two_mul _
    (d * m₂ + d * d + t * m₁ + t * d + t * t + s * t)]
  congr 1
  ring

end Core

section Main

variable [FiniteDimensional 𝕜 Λ₁] [FiniteDimensional 𝕜 Λ₂] [FiniteDimensional 𝕜 G₁]
  [FiniteDimensional 𝕜 G₂]

/-- **The composite kernel chart reads the composition law.** Let `(D₁, q₁)` be a kernel chart of
`f` and `(D₂, q₂)` one of `g`, with composite chart `((g ∘ D₁).coprod D₂, compKerCoord f D₁ q₁ q₂)`
of `g ∘ f` (`ContinuousLinearMap.IsInvertible.prod_coprod_compKerCoord`). The element of the
determinant line of `g ∘ f` corresponding to `v ⊗ w` under the composition law
`LinearMap.detLineCompEquiv` is read in the composite chart as the product, under
`TauCeti.detLineTensorDualProdEquiv`, of the readings of `v` and `w`, up to a sign depending on the
dimensions of the kernels and cokernels of `f`, `g` and `g ∘ f` and on those of the charts. -/
theorem detLineChartEquiv_detLineCompEquiv_symm (h₁ : ((f.coprod D₁).prod q₁).IsInvertible)
    (h₂ : ((g.coprod D₂).prod q₂).IsInvertible) [FiniteDimensional 𝕜 f.ker]
    [FiniteDimensional 𝕜 (F ⧸ f.range)] [FiniteDimensional 𝕜 g.ker]
    [FiniteDimensional 𝕜 (P ⧸ g.range)] (v : (f : E →ₗ[𝕜] F).detLine)
    (w : (g : F →ₗ[𝕜] P).detLine) :
    detLineChartEquiv (g ∘L f) ((g ∘L D₁).coprod D₂) (compKerCoord f D₁ q₁ q₂)
        (h₁.prod_coprod_compKerCoord h₂)
        (((f : E →ₗ[𝕜] F).detLineCompEquiv (g : F →ₗ[𝕜] P)).symm (v ⊗ₜ w)) =
      (-1 : 𝕜) ^ (finrank 𝕜 (P ⧸ (g ∘L f).range) * finrank 𝕜 (Λ₁ × Λ₂) +
          finrank 𝕜 (LinearMap.range ((f : E →ₗ[𝕜] F).kerCompToKer (g : F →ₗ[𝕜] P))) *
            finrank 𝕜 (parameterProj f D₁).range +
          finrank 𝕜 (LinearMap.range ((f : E →ₗ[𝕜] F).cokerToCokerComp (g : F →ₗ[𝕜] P))) *
            finrank 𝕜 (parameterProj g D₂).range +
        finrank 𝕜 (F ⧸ f.range) * finrank 𝕜 Λ₁ + finrank 𝕜 (P ⧸ g.range) * finrank 𝕜 Λ₂) •
        TauCeti.detLineTensorDualProdEquiv 𝕜 G₁ Λ₁ G₂ Λ₂
          (detLineChartEquiv f D₁ q₁ h₁ v ⊗ₜ detLineChartEquiv g D₂ q₂ h₂ w) := by
  have hf := surjective_of_isInvertible_prod h₁
  have hg := surjective_of_isInvertible_prod h₂
  have hh := surjective_of_isInvertible_prod (h₁.prod_coprod_compKerCoord h₂)
  -- The kernel and cokernel of `g ∘ f` are finite-dimensional, as those of the composite of
  -- linear maps.
  have hk₀ : FiniteDimensional 𝕜 (LinearMap.ker ((g : F →ₗ[𝕜] P) ∘ₗ (f : E →ₗ[𝕜] F))) :=
    Module.Finite.ker_comp (f : E →ₗ[𝕜] F) (g : F →ₗ[𝕜] P)
  have : FiniteDimensional 𝕜 (g ∘L f).ker := hk₀
  have hc₀ : FiniteDimensional 𝕜 (P ⧸ LinearMap.range ((g : F →ₗ[𝕜] P) ∘ₗ (f : E →ₗ[𝕜] F))) :=
    Module.Finite.quotient_range_comp (f : E →ₗ[𝕜] F) (g : F →ₗ[𝕜] P)
  have : FiniteDimensional 𝕜 (P ⧸ (g ∘L f).range) := hc₀
  obtain ⟨d⟩ := nonempty_compData hf hg
  obtain ⟨κ₁, η₁, κ₂, η₂, β, hκ₁, hη₁, hκ₂, hη₂, hβ, hcomp⟩ := exists_comp_stab d hf hg hh
  set N := finrank 𝕜 (P ⧸ (g ∘L f).range) * finrank 𝕜 (Λ₁ × Λ₂) +
      finrank 𝕜 (LinearMap.range ((f : E →ₗ[𝕜] F).kerCompToKer (g : F →ₗ[𝕜] P))) *
        finrank 𝕜 (parameterProj f D₁).range +
      finrank 𝕜 (LinearMap.range ((f : E →ₗ[𝕜] F).cokerToCokerComp (g : F →ₗ[𝕜] P))) *
        finrank 𝕜 (parameterProj g D₂).range +
    finrank 𝕜 (F ⧸ f.range) * finrank 𝕜 Λ₁ + finrank 𝕜 (P ⧸ g.range) * finrank 𝕜 Λ₂
  -- The identity on the stabilizations of `κ₁ ⊗ φ₁` and `κ₂ ⊗ φ₂`.
  have key (φ₁ : Dual 𝕜 (TauCeti.detLine 𝕜 Λ₁)) (φ₂ : Dual 𝕜 (TauCeti.detLine 𝕜 Λ₂)) :
      detLineChartEquiv (g ∘L f) ((g ∘L D₁).coprod D₂) (compKerCoord f D₁ q₁ q₂)
          (h₁.prod_coprod_compKerCoord h₂)
          (((f : E →ₗ[𝕜] F).detLineCompEquiv (g : F →ₗ[𝕜] P)).symm
            (detLineStabilizationEquiv f D₁ hf (κ₁ ⊗ₜ φ₁) ⊗ₜ
              detLineStabilizationEquiv g D₂ hg (κ₂ ⊗ₜ φ₂))) =
        (-1 : 𝕜) ^ N • TauCeti.detLineTensorDualProdEquiv 𝕜 G₁ Λ₁ G₂ Λ₂
          (detLineChartEquiv f D₁ q₁ h₁ (detLineStabilizationEquiv f D₁ hf (κ₁ ⊗ₜ φ₁)) ⊗ₜ
            detLineChartEquiv g D₂ q₂ h₂ (detLineStabilizationEquiv g D₂ hg (κ₂ ⊗ₜ φ₂))) := by
    -- Solve the composition law of the stabilizations for the inverse composition law.
    have hsymm : ((f : E →ₗ[𝕜] F).detLineCompEquiv (g : F →ₗ[𝕜] P)).symm
        (detLineStabilizationEquiv f D₁ hf (κ₁ ⊗ₜ φ₁) ⊗ₜ
          detLineStabilizationEquiv g D₂ hg (κ₂ ⊗ₜ φ₂)) =
        (-1 : 𝕜) ^ N • detLineStabilizationEquiv (g ∘L f) ((g ∘L D₁).coprod D₂) hh
          (β ⊗ₜ TauCeti.detLineDualProdEquiv 𝕜 Λ₁ Λ₂ (φ₁ ⊗ₜ φ₂)) := by
      refine (LinearEquiv.symm_apply_eq _).2 (Eq.symm ((LinearEquiv.map_smul _ _ _).trans
        ((congrArg ((-1 : 𝕜) ^ N • ·) (hcomp φ₁ φ₂)).trans ?_)))
      rw [smul_smul, TauCeti.neg_one_pow_mul_neg_one_pow, one_smul]
    refine (congrArg _ hsymm).trans ?_
    rw [map_smul, detLineChartEquiv_detLineStabilizationEquiv, LinearEquiv.rTensor_tmul,
      detLineChartEquiv_detLineStabilizationEquiv, detLineChartEquiv_detLineStabilizationEquiv,
      LinearEquiv.rTensor_tmul, LinearEquiv.rTensor_tmul,
      TauCeti.detLineTensorDualProdEquiv_tmul, detLineCongr_compKerCoord d h₁ h₂ hκ₁ hκ₂ hβ]
  obtain ⟨y₁, rfl⟩ := (detLineStabilizationEquiv f D₁ hf).surjective v
  obtain ⟨y₂, rfl⟩ := (detLineStabilizationEquiv g D₂ hg).surjective w
  obtain ⟨φ₁, rfl⟩ := exists_eq_tmul_of_apply_eq_one hη₁ y₁
  obtain ⟨φ₂, rfl⟩ := exists_eq_tmul_of_apply_eq_one hη₂ y₂
  exact key φ₁ φ₂

/-- **The normalized composition law in a composite kernel chart.** With the sign
`(-1) ^ (dim coker f * r + t * dim coker g)`, where `r` and `t` are the ranks of the maps
`ker (g ∘ f) → ker g` and `coker f → coker (g ∘ f)` of the kernel–cokernel sequence of `g ∘ f`, the
element of the determinant line of `g ∘ f` corresponding to `v ⊗ w` under the composition law is
read in the composite of kernel charts of `f` and `g` as the product of the readings of `v` and
`w` times the sign `(-1) ^ (dim Λ₁ * (dim G₂ + dim Λ₂))`, which depends only on the charts. -/
theorem detLineChartEquiv_neg_one_pow_smul_comp (h₁ : ((f.coprod D₁).prod q₁).IsInvertible)
    (h₂ : ((g.coprod D₂).prod q₂).IsInvertible) [FiniteDimensional 𝕜 f.ker]
    [FiniteDimensional 𝕜 (F ⧸ f.range)] [FiniteDimensional 𝕜 g.ker]
    [FiniteDimensional 𝕜 (P ⧸ g.range)] (v : (f : E →ₗ[𝕜] F).detLine)
    (w : (g : F →ₗ[𝕜] P).detLine) :
    detLineChartEquiv (g ∘L f) ((g ∘L D₁).coprod D₂) (compKerCoord f D₁ q₁ q₂)
        (h₁.prod_coprod_compKerCoord h₂)
        ((-1 : 𝕜) ^ (finrank 𝕜 (F ⧸ f.range) *
            finrank 𝕜 (LinearMap.range ((f : E →ₗ[𝕜] F).kerCompToKer (g : F →ₗ[𝕜] P))) +
          finrank 𝕜 (LinearMap.range ((f : E →ₗ[𝕜] F).cokerToCokerComp (g : F →ₗ[𝕜] P))) *
            finrank 𝕜 (P ⧸ g.range)) •
          ((f : E →ₗ[𝕜] F).detLineCompEquiv (g : F →ₗ[𝕜] P)).symm (v ⊗ₜ w)) =
      (-1 : 𝕜) ^ (finrank 𝕜 Λ₁ * (finrank 𝕜 G₂ + finrank 𝕜 Λ₂)) •
        TauCeti.detLineTensorDualProdEquiv 𝕜 G₁ Λ₁ G₂ Λ₂
          (detLineChartEquiv f D₁ q₁ h₁ v ⊗ₜ detLineChartEquiv g D₂ q₂ h₂ w) := by
  refine ((detLineChartEquiv _ _ _ _).map_smul _ _).trans ?_
  rw [detLineChartEquiv_detLineCompEquiv_symm h₁ h₂ v w, smul_smul, ← pow_add]
  congr 1
  -- The dimension counts of the stabilizations, of the kernel–cokernel sequence of `g ∘ f` and of
  -- the index of `g` read in its chart.
  obtain ⟨hl₁, -⟩ := finrank_stabilization (surjective_of_isInvertible_prod h₁)
  obtain ⟨hl₂, -⟩ := finrank_stabilization (surjective_of_isInvertible_prod h₂)
  have hidx := finrank_ker_add_finrank_eq_of_isInvertible_prod_coprod h₂
  have hc := (f : E →ₗ[𝕜] F).finrank_ker_eq_finrank_range_kerCompToKer_add (g : F →ₗ[𝕜] P)
  have hb := (f : E →ₗ[𝕜] F).finrank_quotient_range_eq_finrank_range_kerToCoker_add
    (g : F →ₗ[𝕜] P)
  have : FiniteDimensional 𝕜 (P ⧸ LinearMap.range ((g : F →ₗ[𝕜] P) ∘ₗ (f : E →ₗ[𝕜] F))) :=
    Module.Finite.quotient_range_comp (f : E →ₗ[𝕜] F) (g : F →ₗ[𝕜] P)
  have hbh : finrank 𝕜 (P ⧸ (g ∘L f).range) =
      finrank 𝕜 (LinearMap.range ((f : E →ₗ[𝕜] F).cokerToCokerComp (g : F →ₗ[𝕜] P))) +
        finrank 𝕜 (P ⧸ g.range) :=
    (f : E →ₗ[𝕜] F).finrank_quotient_range_comp_eq_finrank_range_cokerToCokerComp_add
      (g : F →ₗ[𝕜] P)
  rw [Module.finrank_prod]
  exact neg_one_pow_comp_sign hb hbh hl₁ hl₂ (by omega)

end Main

end Chart

end ContinuousLinearMap
