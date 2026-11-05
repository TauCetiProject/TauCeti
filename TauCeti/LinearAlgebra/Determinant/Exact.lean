/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Determinant.Line
public import TauCeti.LinearAlgebra.ExteriorPower.ShortExact
import TauCeti.LinearAlgebra.Exact
import TauCeti.RingTheory.PicardGroup.Contraction

/-!
# Determinant lines of exact sequences

A short exact sequence `0 → U → V → W → 0` of finite-dimensional vector spaces identifies
`det U ⊗ det W` with `det V` (`TauCeti.detLineShortExactEquiv`); this is
`TauCeti.exteriorPower.shortExactEquiv` with its target read as the determinant line of `V`.

Let `0 → A → B → C → D → 0` be an exact sequence of finite-dimensional vector spaces, with maps
`f : A → B`, `g : B → C` and `h : C → D`. The alternating sum of the dimensions vanishes, and the
determinant lines satisfy the corresponding identity

`det B ⊗ (det C)^* ≃ det A ⊗ (det D)^*`

(`TauCeti.detLineFourTermEquiv`). This is the identity through which the determinant line
`det (ker T) ⊗ (det (coker T))^*` of a Fredholm operator `T` is compared with the determinant of
a finite stabilization of `T`: the kernel of the stabilized operator and the stabilizing space sit
between `ker T` and `coker T` in such a sequence.

The isomorphism is canonical, with no choice of bases or splittings. The sequence breaks at the
image `range g = ker h` into two short exact sequences `0 → A → B → range g → 0` and
`0 → range g → C → D → 0`, each of which identifies determinant lines through
`TauCeti.detLineShortExactEquiv`, subspace factor first. The two copies of
`det (range g)` then cancel by the contraction `det (range g) ⊗ (det (range g))^* ≃ K` of the
line with its dual (`Module.Invertible.leftCancelDualEquiv`).

Explicitly, for `u₁, …, uₐ` in `A`, `v₁, …, vₖ` in `B` with `k = dim (range g)`, and lifts
`z₁, …, z_d` in `C` of a basis of `D`, the isomorphism sends
`(f u₁ ∧ ⋯ ∧ f uₐ ∧ v₁ ∧ ⋯ ∧ vₖ) ⊗ φ` to `(u₁ ∧ ⋯ ∧ uₐ) ⊗ ψ`, where the functional `ψ` on
`det D` takes the value `φ (g v₁ ∧ ⋯ ∧ g vₖ ∧ z₁ ∧ ⋯ ∧ z_d)` at `h z₁ ∧ ⋯ ∧ h z_d`
(`TauCeti.detLineFourTermEquiv_tmul`). The wedge products of different lengths are compared as
elements of the exterior algebra, so that no renumbering of the factors appears in the statement.

## Main declarations

* `TauCeti.detLineShortExactEquiv`: the isomorphism `det U ⊗ det W ≃ det V` of a short exact
  sequence `0 → U → V → W → 0`, with its value `TauCeti.coe_detLineShortExactEquiv_tmul`.
* `TauCeti.detLineFourTermEquiv`: the isomorphism `det B ⊗ (det C)^* ≃ det A ⊗ (det D)^*` of a
  four-term exact sequence `0 → A → B → C → D → 0`.
* `TauCeti.detLineFourTermEquiv_tmul`: its value on exterior products.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS
  Colloquium Publications **52**, 2012, Appendix A.2 (determinant lines of exact sequences).
-/

public section

noncomputable section

open Module TensorProduct

namespace TauCeti

variable {K : Type*} [Field K]

section ShortExact

variable {U V W : Type*} [AddCommGroup U] [Module K U] [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W] [FiniteDimensional K U] [FiniteDimensional K W]
  {f : U →ₗ[K] V} {g : V →ₗ[K] W} (hf : Function.Injective f) (hfg : Function.Exact f g)
  (hg : Function.Surjective g)

/-- **The determinant line of a short exact sequence.** For a short exact sequence
`0 → U → V → W → 0` of finite-dimensional vector spaces, the isomorphism
`det U ⊗ det W ≃ det V` sending `(u₁ ∧ ⋯ ∧ uₐ) ⊗ (g v₁ ∧ ⋯ ∧ g v_c)` to
`f u₁ ∧ ⋯ ∧ f uₐ ∧ v₁ ∧ ⋯ ∧ v_c` (`TauCeti.coe_detLineShortExactEquiv_tmul`). This is
`TauCeti.exteriorPower.shortExactEquiv`, whose target `⋀^(dim U + dim W) V` is the determinant
line of `V`. -/
def detLineShortExactEquiv : detLine K U ⊗[K] detLine K W ≃ₗ[K] detLine K V :=
  have : FiniteDimensional K V := finiteDimensional_of_exact hfg
  exteriorPower.shortExactEquiv hf hfg hg ≪≫ₗ
    LinearEquiv.ofEq _ _ (congrArg (⋀[K]^· V) (hfg.finrank_eq_add hf hg).symm)

/-- `TauCeti.detLineShortExactEquiv` sends `(u₁ ∧ ⋯ ∧ uₐ) ⊗ (g v₁ ∧ ⋯ ∧ g v_c)` to
`f u₁ ∧ ⋯ ∧ f uₐ ∧ v₁ ∧ ⋯ ∧ v_c`, as elements of the exterior algebra of `V`. -/
@[simp]
theorem coe_detLineShortExactEquiv_tmul (u : Fin (finrank K U) → U)
    (v : Fin (finrank K W) → V) :
    (detLineShortExactEquiv hf hfg hg (exteriorPower.ιMulti K _ u ⊗ₜ
        exteriorPower.ιMulti K _ (g ∘ v)) : ExteriorAlgebra K V) =
      ExteriorAlgebra.ιMulti K _ (Fin.append (f ∘ u) v) := by
  rw [detLineShortExactEquiv, LinearEquiv.trans_apply, LinearEquiv.coe_ofEq_apply,
    exteriorPower.shortExactEquiv_tmul_ιMulti_comp, exteriorPower.ιMulti_apply_coe]

end ShortExact

variable {A B C D : Type*} [AddCommGroup A] [Module K A] [AddCommGroup B] [Module K B]
  [AddCommGroup C] [Module K C] [AddCommGroup D] [Module K D]
  {f : A →ₗ[K] B} {g : B →ₗ[K] C} {h : C →ₗ[K] D}
  [FiniteDimensional K A] [FiniteDimensional K C] (hf : Function.Injective f)
  (hfg : Function.Exact f g) (hgh : Function.Exact g h) (hh : Function.Surjective h)

/-- **The determinant lines of a four-term exact sequence.** For an exact sequence
`0 → A → B → C → D → 0` of finite-dimensional vector spaces, with maps `f`, `g` and `h`, the
canonical isomorphism `det B ⊗ (det C)^* ≃ det A ⊗ (det D)^*`. Both short exact sequences
`0 → A → B → range g → 0` and `0 → range g → C → D → 0` identify determinant lines with the
subspace factor first, and the two copies of `det (range g)` cancel. Its value on exterior
products is `TauCeti.detLineFourTermEquiv_tmul`. Only `A` and `C` are assumed
finite-dimensional, since `B` and `D` are then finite-dimensional by exactness. -/
def detLineFourTermEquiv :
    detLine K B ⊗[K] Dual K (detLine K C) ≃ₗ[K] detLine K A ⊗[K] Dual K (detLine K D) :=
  have : FiniteDimensional K D := Module.Finite.of_surjective h hh
  TensorProduct.congr (detLineShortExactEquiv hf hfg.rangeRestrict g.surjective_rangeRestrict).symm
      (detLineShortExactEquiv (LinearMap.range g).injective_subtype hgh.range_subtype
        hh).dualMap ≪≫ₗ
    (dualDistribEquiv K _ _).symm.lTensor _ ≪≫ₗ
    TensorProduct.assoc K _ _ _ ≪≫ₗ
    (Module.Invertible.leftCancelDualEquiv K _ _).lTensor _

/-- **The value of `TauCeti.detLineFourTermEquiv` on exterior products.** Let `u` be a family of
`dim A` vectors of `A`, `v` a family of `dim (range g)` vectors of `B`, and `z` a family of
`dim D` vectors of `C`. Let `β ∈ det B` be the exterior product of `f ∘ u` followed by `v`, and
`γ ∈ det C` that of `g ∘ v` followed by `z`. Then the isomorphism sends `β ⊗ φ` to `α ⊗ ψ`,
with `α` the exterior product of `u` and `ψ` the functional taking the value `φ γ` at the exterior
product of `h ∘ z`. When `h ∘ z` is a basis of `D`, its exterior product spans the line `det D`,
so this determines `ψ`; otherwise that exterior product is zero and both sides vanish. -/
theorem detLineFourTermEquiv_tmul (u : Fin (finrank K A) → A)
    (v : Fin (finrank K (LinearMap.range g)) → B) (z : Fin (finrank K D) → C)
    {β : detLine K B} (hβ : (β : ExteriorAlgebra K B) =
      ExteriorAlgebra.ιMulti K _ (Fin.append (f ∘ u) v))
    {γ : detLine K C} (hγ : (γ : ExteriorAlgebra K C) =
      ExteriorAlgebra.ιMulti K _ (Fin.append (g ∘ v) z))
    (φ : Dual K (detLine K C)) :
    TensorProduct.rid K _ ((Dual.eval K _ (exteriorPower.ιMulti K _ (h ∘ z))).lTensor _
        (detLineFourTermEquiv hf hfg hgh hh (β ⊗ₜ φ))) =
      φ γ • exteriorPower.ιMulti K _ u := by
  have : FiniteDimensional K D := Module.Finite.of_surjective h hh
  -- Split `β` along `0 → A → B → range g → 0`.
  have hβ' : (detLineShortExactEquiv hf hfg.rangeRestrict g.surjective_rangeRestrict).symm β =
      exteriorPower.ιMulti K _ u ⊗ₜ exteriorPower.ιMulti K _ (g.rangeRestrict ∘ v) := by
    rw [LinearEquiv.symm_apply_eq]
    exact Subtype.ext (by rw [hβ, coe_detLineShortExactEquiv_tmul])
  -- Join the two halves of `γ` along `0 → range g → C → D → 0`.
  have hγ' : detLineShortExactEquiv (LinearMap.range g).injective_subtype hgh.range_subtype hh
      (exteriorPower.ιMulti K _ (g.rangeRestrict ∘ v) ⊗ₜ exteriorPower.ιMulti K _ (h ∘ z)) = γ :=
    Subtype.ext (by rw [hγ, coe_detLineShortExactEquiv_tmul, ← Function.comp_assoc,
      ← LinearMap.coe_comp, LinearMap.subtype_comp_rangeRestrict])
  simp only [detLineFourTermEquiv, LinearEquiv.trans_apply, TensorProduct.congr_tmul, hβ',
    LinearEquiv.lTensor_tmul, TensorProduct.assoc_tmul, LinearMap.lTensor_tmul,
    TensorProduct.rid_tmul, Dual.eval_apply, Module.Invertible.leftCancelDualEquiv_tmul_apply,
    LinearEquiv.apply_symm_apply, LinearEquiv.dualMap_apply, hγ']

end TauCeti
