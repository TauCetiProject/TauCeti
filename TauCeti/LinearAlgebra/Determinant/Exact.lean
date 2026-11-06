/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Determinant.Line
public import TauCeti.LinearAlgebra.ExteriorPower.ShortExact
import TauCeti.LinearAlgebra.Dual.Contraction
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
Against a functional `ξ` normalized by `ξ (h z₁ ∧ ⋯ ∧ h z_d) = 1`, this says that `β ⊗ φ` goes to
`φ γ • (α ⊗ ξ)` (`TauCeti.detLineFourTermEquiv_tmul_eq_smul_tmul`).

A six-term exact sequence `0 → A₁ → A₂ → A₃ → A₄ → A₅ → A₆ → 0` of finite-dimensional vector
spaces likewise gives the canonical isomorphism

`det A₂ ⊗ (det A₅)^* ≃ (det A₁ ⊗ (det A₄)^*) ⊗ (det A₃ ⊗ (det A₆)^*)`

(`TauCeti.detLineSixTermEquiv`). This is the shape of the kernel–cokernel sequence of a
composition `g ∘ f`, where it identifies the determinant line of `g ∘ f` with the tensor product of
those of `f` and `g` (`LinearMap.detLineCompEquiv`). The sequence breaks at the image of `A₃` in
`A₄` into two four-term sequences, and the two copies of the determinant line of that image
cancel.

## Main declarations

* `TauCeti.detLineShortExactEquiv`: the isomorphism `det U ⊗ det W ≃ det V` of a short exact
  sequence `0 → U → V → W → 0`, with its value `TauCeti.coe_detLineShortExactEquiv_tmul`.
* `TauCeti.detLineFourTermEquiv`: the isomorphism `det B ⊗ (det C)^* ≃ det A ⊗ (det D)^*` of a
  four-term exact sequence `0 → A → B → C → D → 0`.
* `TauCeti.detLineFourTermEquiv_tmul`, `TauCeti.detLineFourTermEquiv_tmul_eq_smul_tmul`: its value
  on exterior products.
* `TauCeti.detLineSixTermEquiv`: the isomorphism
  `det A₂ ⊗ (det A₅)^* ≃ (det A₁ ⊗ (det A₄)^*) ⊗ (det A₃ ⊗ (det A₆)^*)` of a six-term exact
  sequence `0 → A₁ → A₂ → A₃ → A₄ → A₅ → A₆ → 0`, with its value
  `TauCeti.detLineSixTermEquiv_tmul`.

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

section FourTerm

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

/-- **The value of `TauCeti.detLineFourTermEquiv` against a normalized functional.** With `u`, `v`,
`z`, `β` and `γ` as in `TauCeti.detLineFourTermEquiv_tmul`, let `ξ` be a functional on `det D`
taking the value `1` at the exterior product of `h ∘ z`. Then the isomorphism sends `β ⊗ φ` to
`φ γ • (α ⊗ ξ)`, with `α` the exterior product of `u`. -/
theorem detLineFourTermEquiv_tmul_eq_smul_tmul (u : Fin (finrank K A) → A)
    (v : Fin (finrank K (LinearMap.range g)) → B) (z : Fin (finrank K D) → C)
    {β : detLine K B} (hβ : (β : ExteriorAlgebra K B) =
      ExteriorAlgebra.ιMulti K _ (Fin.append (f ∘ u) v))
    {γ : detLine K C} (hγ : (γ : ExteriorAlgebra K C) =
      ExteriorAlgebra.ιMulti K _ (Fin.append (g ∘ v) z))
    (φ : Dual K (detLine K C)) {ξ : Dual K (detLine K D)}
    (hξ : ξ (exteriorPower.ιMulti K _ (h ∘ z)) = 1) :
    detLineFourTermEquiv hf hfg hgh hh (β ⊗ₜ φ) = φ γ • (exteriorPower.ιMulti K _ u ⊗ₜ ξ) := by
  have : FiniteDimensional K D := Module.Finite.of_surjective h hh
  rw [← rid_lTensor_eval_tmul_eq_self_of_finrank_eq_one (finrank_detLine K D) hξ
    (detLineFourTermEquiv hf hfg hgh hh (β ⊗ₜ φ)), detLineFourTermEquiv_tmul hf hfg hgh hh u v z hβ
    hγ φ, TensorProduct.smul_tmul']

end FourTerm

section SixTerm

variable {A₁ A₂ A₃ A₄ A₅ A₆ : Type*} [AddCommGroup A₁] [Module K A₁] [AddCommGroup A₂]
  [Module K A₂] [AddCommGroup A₃] [Module K A₃] [AddCommGroup A₄] [Module K A₄]
  [AddCommGroup A₅] [Module K A₅] [AddCommGroup A₆] [Module K A₆]
  {f₁ : A₁ →ₗ[K] A₂} {f₂ : A₂ →ₗ[K] A₃} {f₃ : A₃ →ₗ[K] A₄} {f₄ : A₄ →ₗ[K] A₅}
  {f₅ : A₅ →ₗ[K] A₆} [FiniteDimensional K A₁] [FiniteDimensional K A₃] [FiniteDimensional K A₅]
  (hf₁ : Function.Injective f₁) (h₁₂ : Function.Exact f₁ f₂) (h₂₃ : Function.Exact f₂ f₃)
  (h₃₄ : Function.Exact f₃ f₄) (h₄₅ : Function.Exact f₄ f₅) (hf₅ : Function.Surjective f₅)

/-- **The determinant lines of a six-term exact sequence.** For an exact sequence
`0 → A₁ → A₂ → A₃ → A₄ → A₅ → A₆ → 0` of finite-dimensional vector spaces, with maps `f₁`, …,
`f₅`, the canonical isomorphism

`det A₂ ⊗ (det A₅)^* ≃ (det A₁ ⊗ (det A₄)^*) ⊗ (det A₃ ⊗ (det A₆)^*)`.

This is the shape taken by the kernel–cokernel sequence of a composition, where it compares the
determinant line of a composite with the determinant lines of its factors. The sequence breaks at
the image `range f₃` into the four-term sequences `0 → A₁ → A₂ → A₃ → range f₃ → 0` and
`0 → range f₃ → A₄ → A₅ → A₆ → 0`, each identified by `TauCeti.detLineFourTermEquiv`, and the two
copies of `det (range f₃)` cancel. Its value on exterior products is
`TauCeti.detLineSixTermEquiv_tmul`. Only `A₁`, `A₃` and `A₅` are assumed finite-dimensional,
since the others then are by exactness. -/
def detLineSixTermEquiv :
    detLine K A₂ ⊗[K] Dual K (detLine K A₅) ≃ₗ[K]
      (detLine K A₁ ⊗[K] Dual K (detLine K A₄)) ⊗[K]
        (detLine K A₃ ⊗[K] Dual K (detLine K A₆)) :=
  have : FiniteDimensional K A₄ := finiteDimensional_of_exact h₃₄
  open Module.Invertible in
  (rightCancelEquiv _ (linearEquiv K (detLine K A₃))).symm.rTensor _ ≪≫ₗ
    (leftCancelEquiv _ (linearEquiv K (detLine K A₄))).symm.lTensor _ ≪≫ₗ
    TensorProduct.congr
      ((detLineFourTermEquiv hf₁ h₁₂ h₂₃.rangeRestrict f₃.surjective_rangeRestrict).rTensor _)
      ((detLineFourTermEquiv (LinearMap.range f₃).injective_subtype h₃₄.range_subtype h₄₅
        hf₅).lTensor _) ≪≫ₗ
    TensorProduct.tensorTensorTensorComm K _ _ _ _ ≪≫ₗ
    TensorProduct.congr (TensorProduct.rightComm K _ _ _) (TensorProduct.leftComm K _ _ _) ≪≫ₗ
    TensorProduct.assoc K _ _ _ ≪≫ₗ
    (leftCancelEquiv _ (linearEquiv K (detLine K (LinearMap.range f₃)))).lTensor _

/-- **The value of `TauCeti.detLineSixTermEquiv` on exterior products.** Let `u` be a family of
`dim A₁` vectors of `A₁`, and `v`, `w`, `x` families of `dim (range fᵢ)` vectors of `A₂`, `A₃`,
`A₄` for `i = 2, 3, 4`, and `y` a family of `dim A₆` vectors of `A₅`. Let `β`, `γ`, `δ` and `ε` be
the exterior products of `f₁ ∘ u` followed by `v`, of `f₂ ∘ v` followed by `w`, of `f₃ ∘ w`
followed by `x`, and of `f₄ ∘ x` followed by `y`. If `ψ` takes the value `1` at `δ` and `χ` takes
the value `1` at the exterior product of `f₅ ∘ y`, then the isomorphism sends `β ⊗ φ` to
`φ ε • ((α ⊗ ψ) ⊗ (γ ⊗ χ))`, with `α` the exterior product of `u`. -/
theorem detLineSixTermEquiv_tmul (u : Fin (finrank K A₁) → A₁)
    (v : Fin (finrank K (LinearMap.range f₂)) → A₂) (w : Fin (finrank K (LinearMap.range f₃)) → A₃)
    (x : Fin (finrank K (LinearMap.range f₄)) → A₄) (y : Fin (finrank K A₆) → A₅)
    {β : detLine K A₂} (hβ : (β : ExteriorAlgebra K A₂) =
      ExteriorAlgebra.ιMulti K _ (Fin.append (f₁ ∘ u) v))
    {γ : detLine K A₃} (hγ : (γ : ExteriorAlgebra K A₃) =
      ExteriorAlgebra.ιMulti K _ (Fin.append (f₂ ∘ v) w))
    {δ : detLine K A₄} (hδ : (δ : ExteriorAlgebra K A₄) =
      ExteriorAlgebra.ιMulti K _ (Fin.append (f₃ ∘ w) x))
    {ε : detLine K A₅} (hε : (ε : ExteriorAlgebra K A₅) =
      ExteriorAlgebra.ιMulti K _ (Fin.append (f₄ ∘ x) y))
    (φ : Dual K (detLine K A₅)) {ψ : Dual K (detLine K A₄)} (hψ : ψ δ = 1)
    {χ : Dual K (detLine K A₆)} (hχ : χ (exteriorPower.ιMulti K _ (f₅ ∘ y)) = 1) :
    detLineSixTermEquiv hf₁ h₁₂ h₂₃ h₃₄ h₄₅ hf₅ (β ⊗ₜ φ) =
      φ ε • ((exteriorPower.ιMulti K _ u ⊗ₜ ψ) ⊗ₜ (γ ⊗ₜ χ)) := by
  have : FiniteDimensional K A₄ := finiteDimensional_of_exact h₃₄
  have : FiniteDimensional K A₆ := Module.Finite.of_surjective f₅ hf₅
  -- Normalized pairs `γ₀' γ₀ = 1` in `det A₃` and `ι₀' ι₀ = 1` in `det (range f₃)`.
  have : Nontrivial (detLine K A₃) := Module.nontrivial_of_finrank_eq_succ (finrank_detLine K A₃)
  obtain ⟨γ₀, hγ₀⟩ := exists_ne (0 : detLine K A₃)
  obtain ⟨γ₀', hγ₀'⟩ := Module.Projective.exists_dual_eq_one K hγ₀
  have : Nontrivial (detLine K (LinearMap.range f₃)) :=
    Module.nontrivial_of_finrank_eq_succ (finrank_detLine K _)
  obtain ⟨ι₀, hι₀⟩ := exists_ne (0 : detLine K (LinearMap.range f₃))
  obtain ⟨ι₀', hι₀'⟩ := Module.Projective.exists_dual_eq_one K hι₀
  -- The first four-term sequence, written against `ι₀'`.
  obtain ⟨X, hE₁⟩ : ∃ X, detLineFourTermEquiv hf₁ h₁₂ h₂₃.rangeRestrict
      f₃.surjective_rangeRestrict (β ⊗ₜ γ₀') = X ⊗ₜ ι₀' :=
    ⟨_, (rid_lTensor_eval_tmul_eq_self_of_finrank_eq_one (finrank_detLine K _) hι₀' _).symm⟩
  have hX : ι₀' (exteriorPower.ιMulti K _ (f₃.rangeRestrict ∘ w)) • X =
      γ₀' γ • exteriorPower.ιMulti K _ u := by
    have := detLineFourTermEquiv_tmul hf₁ h₁₂ h₂₃.rangeRestrict f₃.surjective_rangeRestrict u v w
      hβ hγ γ₀'
    rwa [hE₁, LinearMap.lTensor_tmul, TensorProduct.rid_tmul, Dual.eval_apply] at this
  -- The second four-term sequence, written against `χ`.
  have hE₂ := detLineFourTermEquiv_tmul_eq_smul_tmul (LinearMap.range f₃).injective_subtype
    h₃₄.range_subtype h₄₅ hf₅ (f₃.rangeRestrict ∘ w) x y (β := δ)
    (by rw [hδ, ← Function.comp_assoc, ← LinearMap.coe_comp, LinearMap.subtype_comp_rangeRestrict])
    hε φ hχ
  have h₁ : (Module.Invertible.rightCancelEquiv _
      (Module.Invertible.linearEquiv K (detLine K A₃))).symm β = (β ⊗ₜ γ₀') ⊗ₜ γ₀ := by
    rw [LinearEquiv.symm_apply_eq]
    simp [Module.Invertible.linearEquiv, hγ₀']
  have h₂ : (Module.Invertible.leftCancelEquiv _
      (Module.Invertible.linearEquiv K (detLine K A₄))).symm φ = ψ ⊗ₜ (δ ⊗ₜ φ) := by
    rw [LinearEquiv.symm_apply_eq]
    simp [Module.Invertible.linearEquiv, hψ]
  simp only [detLineSixTermEquiv, LinearEquiv.trans_apply, LinearEquiv.rTensor_tmul,
    LinearEquiv.lTensor_tmul, h₁, h₂, TensorProduct.congr_tmul, hE₁, hE₂]
  simp only [TensorProduct.tmul_smul, TensorProduct.tensorTensorTensorComm_tmul,
    TensorProduct.rightComm_tmul, TensorProduct.leftComm_tmul, TensorProduct.assoc_tmul,
    TensorProduct.assoc_symm_tmul, LinearEquiv.rTensor_tmul, TensorProduct.lid_tmul,
    Module.Invertible.linearEquiv, LinearEquiv.ofBijective_apply, contractLeft_apply, map_smul,
    LinearEquiv.trans_apply, LinearEquiv.lTensor_tmul, TensorProduct.congr_tmul]
  -- Cancel the scalars: `ι₀' ι • X = γ₀' γ • α` and `γ₀' γ • γ₀ = γ`.
  rw [← apply_smul_eq_self_of_finrank_eq_one (finrank_detLine K A₃) hγ₀' γ]
  simp only [TensorProduct.tmul_smul, ← TensorProduct.smul_tmul', smul_smul]
  rw [mul_smul, mul_smul]
  congr 1
  rw [TensorProduct.smul_tmul', TensorProduct.smul_tmul', hX, TensorProduct.smul_tmul',
    TensorProduct.smul_tmul']

end SixTerm

end TauCeti
