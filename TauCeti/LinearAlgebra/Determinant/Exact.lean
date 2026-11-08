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
import TauCeti.LinearAlgebra.ExteriorPower.Basis
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

Two short exact sequences `0 → U → V → W → 0` and `0 → U' → V' → W → 0` with the same quotient
identify `det V ⊗ (det V')^*` with `det U ⊗ (det U')^*` by cancelling `det W`
(`TauCeti.detLineShortExactCancelEquiv`). This compares the four-term isomorphisms of two exact
sequences `0 → A → B → C → D → 0` and `0 → A → B' → C' → D → 0` related by injections
`B → B'` and `C → C'` with a common cokernel `W`: up to the sign `(-1) ^ (dim D * dim W)`, the
cancellation of `W` turns one four-term isomorphism into the other
(`TauCeti.detLineFourTermEquiv_detLineShortExactCancelEquiv`). For Fredholm operators this says
that enlarging the stabilization changes the identification of determinant lines only by a sign.

## Main declarations

* `TauCeti.detLineShortExactEquiv`: the isomorphism `det U ⊗ det W ≃ det V` of a short exact
  sequence `0 → U → V → W → 0`, with its value `TauCeti.coe_detLineShortExactEquiv_tmul`.
* `TauCeti.detLineFourTermEquiv`: the isomorphism `det B ⊗ (det C)^* ≃ det A ⊗ (det D)^*` of a
  four-term exact sequence `0 → A → B → C → D → 0`.
* `TauCeti.detLineFourTermEquiv_tmul`, `TauCeti.detLineFourTermEquiv_tmul_eq_smul_tmul`: its value
  on exterior products, which determine it by `TauCeti.rid_lTensor_eval_injective`.
* `TauCeti.detLineShortExactCancelEquiv`: the isomorphism `det V ⊗ (det V')^* ≃ det U ⊗ (det U')^*`
  of two short exact sequences with the same quotient, with its value
  `TauCeti.detLineShortExactCancelEquiv_tmul`.
* `TauCeti.detLineFourTermEquiv_detLineShortExactCancelEquiv`: the four-term isomorphisms of two
  exact sequences with enlarged middle terms agree up to sign through this cancellation.
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

/-- `TauCeti.detLineShortExactEquiv` sends `a ⊗ (g v₁ ∧ ⋯ ∧ g v_c)`, for any `a ∈ det U`, to the
product of the image of `a` with `v₁ ∧ ⋯ ∧ v_c` in the exterior algebra of `V`. -/
theorem coe_detLineShortExactEquiv_tmul_eq_map_mul (a : detLine K U)
    (v : Fin (finrank K W) → V) :
    (detLineShortExactEquiv hf hfg hg (a ⊗ₜ exteriorPower.ιMulti K _ (g ∘ v)) :
        ExteriorAlgebra K V) =
      ExteriorAlgebra.map f (a : ExteriorAlgebra K U) * ExteriorAlgebra.ιMulti K _ v := by
  have key : (Submodule.subtype _ ∘ₗ (detLineShortExactEquiv hf hfg hg).toLinearMap ∘ₗ
      (TensorProduct.mk K _ _).flip (exteriorPower.ιMulti K _ (g ∘ v))) =
      LinearMap.mulRight K (ExteriorAlgebra.ιMulti K _ v) ∘ₗ
        (ExteriorAlgebra.map f).toLinearMap ∘ₗ Submodule.subtype _ := by
    ext u
    simp [ExteriorAlgebra.ιMulti_mul_ιMulti]
  exact LinearMap.congr_fun key a

end ShortExact

section CommonQuotient

variable {U V U' V' W : Type*} [AddCommGroup U] [Module K U] [AddCommGroup V] [Module K V]
  [AddCommGroup U'] [Module K U'] [AddCommGroup V'] [Module K V'] [AddCommGroup W] [Module K W]
  [FiniteDimensional K U] [FiniteDimensional K U'] [FiniteDimensional K W]
  {f : U →ₗ[K] V} {g : V →ₗ[K] W} {f' : U' →ₗ[K] V'} {g' : V' →ₗ[K] W}
  (hf : Function.Injective f) (hfg : Function.Exact f g) (hg : Function.Surjective g)
  (hf' : Function.Injective f') (hfg' : Function.Exact f' g') (hg' : Function.Surjective g')

/-- **Cancelling a common quotient.** Two short exact sequences `0 → U → V → W → 0` and
`0 → U' → V' → W → 0` of finite-dimensional vector spaces with the same quotient `W` give the
isomorphism `det V ⊗ (det V')^* ≃ det U ⊗ (det U')^*`: both `det V` and `det V'` split off a
factor `det W` by `TauCeti.detLineShortExactEquiv`, subspace factor first, and the two copies of
`det W` cancel. Its value is `TauCeti.detLineShortExactCancelEquiv_tmul`. -/
def detLineShortExactCancelEquiv :
    detLine K V ⊗[K] Dual K (detLine K V') ≃ₗ[K] detLine K U ⊗[K] Dual K (detLine K U') :=
  TensorProduct.congr (detLineShortExactEquiv hf hfg hg).symm
      ((TensorProduct.comm K _ _ ≪≫ₗ detLineShortExactEquiv hf' hfg' hg').dualMap ≪≫ₗ
        (dualDistribEquiv K _ _).symm) ≪≫ₗ
    TensorProduct.assoc K _ _ _ ≪≫ₗ
    (Module.Invertible.leftCancelDualEquiv K _ _).lTensor _

/-- **The value of `TauCeti.detLineShortExactCancelEquiv`.** It sends the image of `a ⊗ w` in
`det V`, tensored with `φ`, to `a ⊗ ψ`, where `ψ` takes the value `φ` of the image of `a' ⊗ w`
in `det V'` at every `a' ∈ det U'`. -/
theorem detLineShortExactCancelEquiv_tmul (a : detLine K U) (w : detLine K W)
    (φ : Dual K (detLine K V')) :
    detLineShortExactCancelEquiv hf hfg hg hf' hfg' hg'
        (detLineShortExactEquiv hf hfg hg (a ⊗ₜ w) ⊗ₜ φ) =
      a ⊗ₜ (φ ∘ₗ (detLineShortExactEquiv hf' hfg' hg').toLinearMap ∘ₗ
        (TensorProduct.mk K _ _).flip w) := by
  simp only [detLineShortExactCancelEquiv, LinearEquiv.trans_apply, TensorProduct.congr_tmul,
    LinearEquiv.symm_apply_apply, TensorProduct.assoc_tmul, LinearEquiv.lTensor_tmul]
  congr 1
  refine LinearMap.ext fun a' ↦ ?_
  rw [Module.Invertible.leftCancelDualEquiv_tmul_apply, LinearEquiv.apply_symm_apply]
  simp

end CommonQuotient

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

/-- Pairing the dual factor with a nonzero element `ω` of a line `L` is injective on `M ⊗ L^*`.
With `TauCeti.detLineFourTermEquiv_tmul`, taking `L = det D` and `ω` the exterior product of the
images of a basis of `D`, this determines `TauCeti.detLineFourTermEquiv` by its values on
exterior products. -/
theorem rid_lTensor_eval_injective {M L : Type*} [AddCommGroup M] [Module K M] [AddCommGroup L]
    [Module K L] (hL : finrank K L = 1) {ω : L} (hω : ω ≠ 0) :
    Function.Injective fun y : M ⊗[K] Dual K L ↦
      TensorProduct.rid K M ((Dual.eval K L ω).lTensor M y) := by
  refine (TensorProduct.rid K M).injective.comp
    (Module.Flat.lTensor_preserves_injective_linearMap _ fun ψ₁ ψ₂ hψ ↦ LinearMap.ext fun y ↦ ?_)
  obtain ⟨a, rfl⟩ := (finrank_eq_one_iff_of_ne_zero' _ hω).1 hL y
  simp only [Dual.eval_apply] at hψ
  rw [map_smul, map_smul, hψ]

section ChangeOfMiddle

/-! ### Enlarging the middle of a four-term exact sequence -/

variable {B' C' W : Type*} [AddCommGroup B'] [Module K B'] [AddCommGroup C'] [Module K C']
  [AddCommGroup W] [Module K W] [FiniteDimensional K B] [FiniteDimensional K C']
  [FiniteDimensional K W] {f' : A →ₗ[K] B'} {g' : B' →ₗ[K] C'} {h' : C' →ₗ[K] D}
  (hf' : Function.Injective f') (hfg' : Function.Exact f' g') (hgh' : Function.Exact g' h')
  (hh' : Function.Surjective h') {j : B →ₗ[K] B'} {ι : C →ₗ[K] C'} {π : C' →ₗ[K] W}
  (hj : Function.Injective j) (hjπ : Function.Exact j (π ∘ₗ g'))
  (hπg : Function.Surjective (π ∘ₗ g')) (hι : Function.Injective ι)
  (hιπ : Function.Exact ι π) (hπ : Function.Surjective π)

include hf hfg hgh hh hf' hfg' hgh' hh' hj hjπ hπg hι hιπ hπ in
/-- `TauCeti.detLineFourTermEquiv_detLineShortExactCancelEquiv` on exterior products. Let `z` be
`dim D` vectors of `C` mapping to a basis of `D`. Both four-term isomorphisms put the directions
`z` after those of the range of `g` or `g'`, while the cancellation of `W` puts the `dim W`
directions of `w` last; moving them past `z` is the sign. -/
private theorem detLineFourTermEquiv_detLineShortExactCancelEquiv_ιMulti
    (hjf : j ∘ₗ f = f') (hgj : g' ∘ₗ j = ι ∘ₗ g) (hhι : h' ∘ₗ ι = h)
    (u : Fin (finrank K A) → A) (v : Fin (finrank K (LinearMap.range g)) → B)
    (w : Fin (finrank K W) → B') (φ : Dual K (detLine K C')) :
    detLineFourTermEquiv hf hfg hgh hh (detLineShortExactCancelEquiv hj hjπ hπg hι hιπ hπ
      (detLineShortExactEquiv hj hjπ hπg
        (detLineShortExactEquiv hf hfg.rangeRestrict g.surjective_rangeRestrict
          (exteriorPower.ιMulti K _ u ⊗ₜ exteriorPower.ιMulti K _ (g.rangeRestrict ∘ v)) ⊗ₜ
        exteriorPower.ιMulti K _ ((π ∘ₗ g') ∘ w)) ⊗ₜ φ)) =
      (-1 : K) ^ (finrank K D * finrank K W) • detLineFourTermEquiv hf' hfg' hgh' hh'
        (detLineShortExactEquiv hj hjπ hπg
          (detLineShortExactEquiv hf hfg.rangeRestrict g.surjective_rangeRestrict
            (exteriorPower.ιMulti K _ u ⊗ₜ exteriorPower.ιMulti K _ (g.rangeRestrict ∘ v)) ⊗ₜ
          exteriorPower.ιMulti K _ ((π ∘ₗ g') ∘ w)) ⊗ₜ φ) := by
  have : FiniteDimensional K D := Module.Finite.of_surjective h hh
  have : FiniteDimensional K B' := finiteDimensional_of_exact hjπ
  -- Vectors `z` of `C` lifting a basis of `D`, whose images span the line `det D`.
  choose z hz using fun i ↦ hh (Module.finBasis K D i)
  have hω : exteriorPower.ιMulti K _ (h ∘ z) ≠ 0 := by
    rw [show h ∘ z = ⇑(Module.finBasis K D) from funext hz]
    exact (exteriorPower.ιMulti_ne_zero_iff _).2 (Module.finBasis K D).linearIndependent
  refine rid_lTensor_eval_injective (finrank_detLine K D) hω ?_
  dsimp only
  -- The exterior products entering the two four-term isomorphisms.
  have hβ : (detLineShortExactEquiv hf hfg.rangeRestrict g.surjective_rangeRestrict
      (exteriorPower.ιMulti K _ u ⊗ₜ exteriorPower.ιMulti K _ (g.rangeRestrict ∘ v)) :
        ExteriorAlgebra K B) = ExteriorAlgebra.ιMulti K _ (Fin.append (f ∘ u) v) :=
    coe_detLineShortExactEquiv_tmul _ _ _ u v
  have hγ : (detLineShortExactEquiv (LinearMap.range g).injective_subtype hgh.range_subtype hh
      (exteriorPower.ιMulti K _ (g.rangeRestrict ∘ v) ⊗ₜ exteriorPower.ιMulti K _ (h ∘ z)) :
        ExteriorAlgebra K C) = ExteriorAlgebra.ιMulti K _ (Fin.append (g ∘ v) z) :=
    coe_detLineShortExactEquiv_tmul _ _ _ _ _
  have hr : finrank K (LinearMap.range g') = finrank K (LinearMap.range g) + finrank K W := by
    have e₁ := hfg.rangeRestrict.finrank_eq_add hf g.surjective_rangeRestrict
    have e₂ := hfg'.rangeRestrict.finrank_eq_add hf' g'.surjective_rangeRestrict
    have e₃ := hjπ.finrank_eq_add hj hπg
    omega
  have hjfu : ⇑j ∘ (⇑f ∘ u) = ⇑f' ∘ u := funext fun i ↦ LinearMap.congr_fun hjf (u i)
  have hgjv : ⇑g' ∘ (⇑j ∘ v) = ⇑ι ∘ (⇑g ∘ v) := funext fun i ↦ LinearMap.congr_fun hgj (v i)
  have hz' : ⇑h' ∘ (⇑ι ∘ z) = ⇑h ∘ z := funext fun i ↦ LinearMap.congr_fun hhι (z i)
  have hβ' : (detLineShortExactEquiv hj hjπ hπg
      (detLineShortExactEquiv hf hfg.rangeRestrict g.surjective_rangeRestrict
        (exteriorPower.ιMulti K _ u ⊗ₜ exteriorPower.ιMulti K _ (g.rangeRestrict ∘ v)) ⊗ₜ
        exteriorPower.ιMulti K _ ((π ∘ₗ g') ∘ w)) : ExteriorAlgebra K B') =
      ExteriorAlgebra.ιMulti K _ (Fin.append (f' ∘ u) (Fin.append (j ∘ v) w ∘ Fin.cast hr)) := by
    simp only [coe_detLineShortExactEquiv_tmul_eq_map_mul, hβ, ← ExteriorAlgebra.ιMulti_mul_ιMulti,
      map_mul, ExteriorAlgebra.map_apply_ιMulti, ExteriorAlgebra.ιMulti_comp_cast, hjfu, mul_assoc]
  have hγ' : ((((-1 : K) ^ (finrank K D * finrank K W)) •
      detLineShortExactEquiv hι hιπ hπ
        (detLineShortExactEquiv (LinearMap.range g).injective_subtype hgh.range_subtype hh
          (exteriorPower.ιMulti K _ (g.rangeRestrict ∘ v) ⊗ₜ exteriorPower.ιMulti K _ (h ∘ z)) ⊗ₜ
          exteriorPower.ιMulti K _ (π ∘ (g' ∘ w))) : detLine K C') : ExteriorAlgebra K C') =
      ExteriorAlgebra.ιMulti K _ (Fin.append (g' ∘ (Fin.append (j ∘ v) w ∘ Fin.cast hr))
        (ι ∘ z)) := by
    rw [← Function.comp_assoc (⇑g')]
    simp only [Submodule.coe_smul, coe_detLineShortExactEquiv_tmul_eq_map_mul, hγ,
      ← ExteriorAlgebra.ιMulti_mul_ιMulti, map_mul, ExteriorAlgebra.map_apply_ιMulti,
      ExteriorAlgebra.ιMulti_comp_cast, ExteriorAlgebra.ιMulti_comp_append, hgjv, mul_assoc]
    -- Move the `dim W` directions `g' ∘ w` past the `dim D` directions `ι ∘ z`.
    rw [ExteriorAlgebra.ιMulti_mul_ιMulti_eq_neg_one_pow_smul (⇑g' ∘ w) (⇑ι ∘ z), mul_smul_comm]
  have hA := detLineFourTermEquiv_tmul hf' hfg' hgh' hh' u
    (Fin.append (j ∘ v) w ∘ Fin.cast hr) (ι ∘ z) hβ' hγ' φ
  rw [hz'] at hA
  rw [detLineShortExactCancelEquiv_tmul, detLineFourTermEquiv_tmul hf hfg hgh hh u v z hβ hγ,
    map_smul, map_smul, hA]
  simp only [LinearMap.comp_apply, LinearMap.flip_apply, TensorProduct.mk_apply,
    LinearEquiv.coe_coe, map_smul, smul_smul, smul_eq_mul, ← mul_assoc, ← mul_pow, neg_mul_neg,
    mul_one, one_pow, one_mul, LinearMap.coe_comp, Function.comp_assoc]

include hf hfg hgh hh hf' hfg' hgh' hh' hj hjπ hπg hι hιπ hπ in
/-- **Enlarging the middle of a four-term exact sequence.** Let `0 → A → B → C → D → 0` and
`0 → A → B' → C' → D → 0` be exact sequences of finite-dimensional vector spaces, related by maps
`j : B → B'` and `ι : C → C'` that commute with all the maps and restrict to the identity on `A`
and `D`. Suppose that `0 → C → C' → W → 0` is exact, with maps `ι` and `π`, and that so is
`0 → B → B' → W → 0`, with maps `j` and `π ∘ g'`. Then cancelling the common quotient `W`
(`TauCeti.detLineShortExactCancelEquiv`) relates the two four-term isomorphisms
`TauCeti.detLineFourTermEquiv` by the sign `(-1) ^ (dim D * dim W)`. -/
theorem detLineFourTermEquiv_detLineShortExactCancelEquiv
    (hjf : j ∘ₗ f = f') (hgj : g' ∘ₗ j = ι ∘ₗ g) (hhι : h' ∘ₗ ι = h)
    (x : detLine K B' ⊗[K] Dual K (detLine K C')) :
    detLineFourTermEquiv hf hfg hgh hh (detLineShortExactCancelEquiv hj hjπ hπg hι hιπ hπ x) =
      (-1 : K) ^ (finrank K D * finrank K W) • detLineFourTermEquiv hf' hfg' hgh' hh' x := by
  -- `x` is a sum of images of `α ⊗ β ⊗ μ ⊗ φ`, and each of the lines `det A`, `det (range g)`
  -- and `det W` is spanned by the exterior product of a basis.
  obtain ⟨y, rfl⟩ := (TensorProduct.congr
    ((detLineShortExactEquiv hf hfg.rangeRestrict g.surjective_rangeRestrict).rTensor _ ≪≫ₗ
      detLineShortExactEquiv hj hjπ hπg) (LinearEquiv.refl K (Dual K (detLine K C')))).surjective x
  induction y using TensorProduct.inductionOn with
  | add y₁ y₂ h₁ h₂ => simp only [map_add, h₁, h₂, smul_add]
  | tmul y φ =>
  induction y using TensorProduct.inductionOn with
  | add y₁ y₂ h₁ h₂ => simp only [TensorProduct.add_tmul, map_add, h₁, h₂, smul_add]
  | tmul y μ =>
  induction y using TensorProduct.inductionOn with
  | add y₁ y₂ h₁ h₂ => simp only [TensorProduct.add_tmul, map_add, h₁, h₂, smul_add]
  | tmul α β =>
  choose v hv using fun i ↦ g.surjective_rangeRestrict (Module.finBasis K (LinearMap.range g) i)
  choose w hw using fun i ↦ hπg (Module.finBasis K W i)
  obtain ⟨a, rfl⟩ := (Module.finBasis K A).exists_smul_ιMulti_eq α
  obtain ⟨b, rfl⟩ := (Module.finBasis K (LinearMap.range g)).exists_smul_ιMulti_eq β
  obtain ⟨c, rfl⟩ := (Module.finBasis K W).exists_smul_ιMulti_eq μ
  rw [show ⇑(Module.finBasis K (LinearMap.range g)) = g.rangeRestrict ∘ v from (funext hv).symm,
    show ⇑(Module.finBasis K W) = (π ∘ₗ g') ∘ w from (funext hw).symm]
  simp only [TensorProduct.congr_tmul, LinearEquiv.trans_apply, LinearEquiv.rTensor_tmul,
    LinearEquiv.refl_apply, TensorProduct.smul_tmul, TensorProduct.tmul_smul, map_smul,
    detLineFourTermEquiv_detLineShortExactCancelEquiv_ιMulti hf hfg hgh hh hf' hfg' hgh' hh' hj hjπ
      hπg hι hιπ hπ hjf hgj hhι]
  simp only [smul_smul]
  congr 1
  ring

end ChangeOfMiddle

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
    simp [hγ₀']
  have h₂ : (Module.Invertible.leftCancelEquiv _
      (Module.Invertible.linearEquiv K (detLine K A₄))).symm φ = ψ ⊗ₜ (δ ⊗ₜ φ) := by
    rw [LinearEquiv.symm_apply_eq]
    simp [hψ]
  simp only [detLineSixTermEquiv, LinearEquiv.trans_apply, LinearEquiv.rTensor_tmul,
    LinearEquiv.lTensor_tmul, h₁, h₂, TensorProduct.congr_tmul, hE₁, hE₂]
  simp only [TensorProduct.tmul_smul, TensorProduct.tensorTensorTensorComm_tmul,
    TensorProduct.rightComm_tmul, TensorProduct.leftComm_tmul, TensorProduct.assoc_tmul,
    TensorProduct.assoc_symm_tmul, LinearEquiv.rTensor_tmul, TensorProduct.lid_tmul,
    Module.Invertible.linearEquiv_tmul, map_smul, LinearEquiv.trans_apply,
    LinearEquiv.lTensor_tmul, TensorProduct.congr_tmul]
  -- Cancel the scalars: `ι₀' ι • X = γ₀' γ • α` and `γ₀' γ • γ₀ = γ`.
  rw [← apply_smul_eq_self_of_finrank_eq_one (finrank_detLine K A₃) hγ₀' γ]
  simp only [TensorProduct.tmul_smul, ← TensorProduct.smul_tmul', smul_smul]
  rw [mul_smul, mul_smul]
  congr 1
  rw [TensorProduct.smul_tmul', TensorProduct.smul_tmul', hX, TensorProduct.smul_tmul',
    TensorProduct.smul_tmul']

end SixTerm

end TauCeti
