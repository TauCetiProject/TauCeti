/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Determinant.Line
public import TauCeti.LinearAlgebra.ExteriorPower.ShortExact
import TauCeti.LinearAlgebra.Exact
import TauCeti.LinearAlgebra.ExteriorPower.Basis
import TauCeti.LinearAlgebra.LinearMap.Range
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
Being canonical, the isomorphism is natural: isomorphisms of four-term exact sequences intertwine
the isomorphisms of the two sequences with the induced isomorphisms of determinant lines
(`TauCeti.detLineFourTermEquiv_congr`).

A six-term exact sequence `0 → A₁ → A₂ → A₃ → A₄ → A₅ → A₆ → 0` of finite-dimensional vector
spaces likewise gives the canonical isomorphism

`det A₂ ⊗ (det A₅)^* ≃ (det A₁ ⊗ (det A₄)^*) ⊗ (det A₃ ⊗ (det A₆)^*)`

(`TauCeti.detLineSixTermEquiv`). This is the shape of the kernel–cokernel sequence of a
composition `g ∘ f`, where it identifies the determinant line of `g ∘ f` with the tensor product of
those of `f` and `g` (`LinearMap.detLineCompEquiv`). The sequence breaks at the image of `A₃` in
`A₄` into two four-term sequences, and the two copies of the determinant line of that image
cancel. Like the four-term isomorphism it is natural for isomorphisms of six-term exact sequences
(`TauCeti.detLineSixTermEquiv_congr`).

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
  sequence `0 → U → V → W → 0`, with its value `TauCeti.coe_detLineShortExactEquiv_tmul`; the
  image of the exterior products of bases spans `det V`
  (`TauCeti.exists_eq_smul_detLineShortExactEquiv`).
* `TauCeti.detLineFourTermEquiv`: the isomorphism `det B ⊗ (det C)^* ≃ det A ⊗ (det D)^*` of a
  four-term exact sequence `0 → A → B → C → D → 0`.
* `TauCeti.detLineFourTermEquiv_tmul`, `TauCeti.detLineFourTermEquiv_tmul_eq_smul_tmul`: its value
  on exterior products, which determine it by `TauCeti.rid_lTensor_eval_injective`.
* `TauCeti.exists_spanning_ιMulti_append`: exterior products spanning `det B`, with the data
  evaluating the isomorphism on them.
* `TauCeti.detLineFourTermEquiv_ιMulti_tmul_of_finrank_eq_zero`: when all four terms are zero, it
  matches the empty exterior products tensored with their normalized functionals.
* `TauCeti.detLineFourTermEquiv_congr`: it is natural for isomorphisms of four-term exact
  sequences.
* `TauCeti.detLineShortExactCancelEquiv`: the isomorphism `det V ⊗ (det V')^* ≃ det U ⊗ (det U')^*`
  of two short exact sequences with the same quotient, with its value
  `TauCeti.detLineShortExactCancelEquiv_tmul`.
* `TauCeti.detLineFourTermEquiv_detLineShortExactCancelEquiv`: the four-term isomorphisms of two
  exact sequences with enlarged middle terms agree up to sign through this cancellation.
* `TauCeti.detLineSixTermEquiv`: the isomorphism
  `det A₂ ⊗ (det A₅)^* ≃ (det A₁ ⊗ (det A₄)^*) ⊗ (det A₃ ⊗ (det A₆)^*)` of a six-term exact
  sequence `0 → A₁ → A₂ → A₃ → A₄ → A₅ → A₆ → 0`, with its value
  `TauCeti.detLineSixTermEquiv_tmul`.
* `TauCeti.exists_spanning_ιMulti_append_sixTerm`: exterior products spanning `det A₂`, with the
  data evaluating the six-term isomorphism on them.
* `TauCeti.detLineSixTermEquiv_congr`: it is natural for isomorphisms of six-term exact sequences.

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
  have : FiniteDimensional K V := hfg.moduleFinite
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

/-- The determinant line of the middle term `V` of a short exact sequence `0 → U → V → W → 0` is
spanned by the image under `TauCeti.detLineShortExactEquiv` of the exterior products of bases of
`U` and `W`. -/
theorem exists_eq_smul_detLineShortExactEquiv (y : detLine K V) :
    ∃ r : K, y = r • detLineShortExactEquiv hf hfg hg
      (exteriorPower.ιMulti K _ (Module.finBasis K U) ⊗ₜ
        exteriorPower.ιMulti K _ (Module.finBasis K W)) := by
  obtain ⟨w, rfl⟩ := (detLineShortExactEquiv hf hfg hg).surjective y
  induction w using TensorProduct.inductionOn with
  | add w w' hw hw' =>
    obtain ⟨r, hr⟩ := hw
    obtain ⟨r', hr'⟩ := hw'
    exact ⟨r + r', by rw [map_add, hr, hr', add_smul]⟩
  | tmul α ρ =>
    obtain ⟨a, rfl⟩ := (Module.finBasis K U).exists_smul_ιMulti_eq α
    obtain ⟨b, rfl⟩ := (Module.finBasis K W).exists_smul_ιMulti_eq ρ
    exact ⟨a * b, by rw [TensorProduct.smul_tmul_smul, map_smul]⟩

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
    Subtype.ext (by rw [hγ, coe_detLineShortExactEquiv_tmul,
      LinearMap.subtype_comp_rangeRestrict_comp])
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
  rw [← Module.Invertible.rid_lTensor_eval_tmul_eq_self hξ
    (detLineFourTermEquiv hf hfg hgh hh (β ⊗ₜ φ)), detLineFourTermEquiv_tmul hf hfg hgh hh u v z hβ
    hγ φ, TensorProduct.smul_tmul']

include hf hfg hgh hh in
/-- **Exterior products spanning `det B`.** For an exact sequence `0 → A → B → C → D → 0`, there
are a family `v` of `dim (range g)` vectors of `B`, a family `z` of `dim D` vectors of `C`, and a
functional `ξ` on `det D` taking the value `1` at the exterior product of `h ∘ z`, such that the
exterior product `β` of `f` applied to a basis of `A` followed by `v` spans `det B`. With the
exterior product `γ` of `g ∘ v` followed by `z`, these are the data with which
`TauCeti.detLineFourTermEquiv_tmul_eq_smul_tmul` evaluates `TauCeti.detLineFourTermEquiv`. -/
theorem exists_spanning_ιMulti_append :
    ∃ (v : Fin (finrank K (LinearMap.range g)) → B) (z : Fin (finrank K D) → C)
      (β : detLine K B) (γ : detLine K C) (ξ : Dual K (detLine K D)),
      (β : ExteriorAlgebra K B) =
          ExteriorAlgebra.ιMulti K _ (Fin.append (f ∘ Module.finBasis K A) v) ∧
        (γ : ExteriorAlgebra K C) = ExteriorAlgebra.ιMulti K _ (Fin.append (g ∘ v) z) ∧
        ξ (exteriorPower.ιMulti K _ (h ∘ z)) = 1 ∧ ∀ x : detLine K B, ∃ r : K, x = r • β := by
  have : FiniteDimensional K D := Module.Finite.of_surjective h hh
  -- Vectors of `B` lifting a basis of `range g`, and of `C` lifting a basis of `D`.
  choose v hv using fun i ↦ g.surjective_rangeRestrict (Module.finBasis K (LinearMap.range g) i)
  choose z hz using fun i ↦ hh (Module.finBasis K D i)
  have hω : exteriorPower.ιMulti K _ (h ∘ z) ≠ 0 := by
    rw [show h ∘ z = ⇑(Module.finBasis K D) from funext hz]
    exact (exteriorPower.ιMulti_ne_zero_iff _).2 (Module.finBasis K D).linearIndependent
  obtain ⟨ξ, hξ⟩ := Projective.exists_dual_eq_one K hω
  refine ⟨v, z, detLineShortExactEquiv hf hfg.rangeRestrict g.surjective_rangeRestrict
      (exteriorPower.ιMulti K _ (Module.finBasis K A) ⊗ₜ
        exteriorPower.ιMulti K _ (g.rangeRestrict ∘ v)),
    detLineShortExactEquiv (LinearMap.range g).injective_subtype hgh.range_subtype hh
      (exteriorPower.ιMulti K _ (g.rangeRestrict ∘ v) ⊗ₜ exteriorPower.ιMulti K _ (h ∘ z)), ξ,
    coe_detLineShortExactEquiv_tmul _ _ _ _ v, coe_detLineShortExactEquiv_tmul _ _ _ _ _, hξ, ?_⟩
  rw [show g.rangeRestrict ∘ v = ⇑(Module.finBasis K (LinearMap.range g)) from funext hv]
  exact exists_eq_smul_detLineShortExactEquiv hf hfg.rangeRestrict g.surjective_rangeRestrict

/-- **`TauCeti.detLineFourTermEquiv` of a sequence of zero spaces.** When all four terms of the
exact sequence have dimension zero, the isomorphism sends the empty exterior product of `B`
tensored with the functional taking the value `1` on the empty exterior product of `C` to the
empty exterior product of `A` tensored with the functional taking the value `1` on the empty
exterior product of `D`. -/
theorem detLineFourTermEquiv_ιMulti_tmul_of_finrank_eq_zero (hA : finrank K A = 0)
    (hB : finrank K B = 0) (hC : finrank K C = 0) (hD : finrank K D = 0)
    (u : Fin (finrank K A) → A) (b : Fin (finrank K B) → B) :
    detLineFourTermEquiv hf hfg hgh hh
        (exteriorPower.ιMulti K _ b ⊗ₜ (detLineEquivOfFinrankEqZero hC).toLinearMap) =
      exteriorPower.ιMulti K _ u ⊗ₜ (detLineEquivOfFinrankEqZero hD).toLinearMap := by
  have hg : finrank K (LinearMap.range g) = 0 :=
    Nat.eq_zero_of_le_zero ((Submodule.finrank_le _).trans hC.le)
  rw [detLineFourTermEquiv_tmul_eq_smul_tmul hf hfg hgh hh u 0 0
      (γ := exteriorPower.ιMulti K _ 0) ?_ ?_ _ (detLineEquivOfFinrankEqZero_ιMulti hD _),
    LinearEquiv.coe_coe, detLineEquivOfFinrankEqZero_ιMulti, one_smul]
  · rw [exteriorPower.ιMulti_apply_coe, ExteriorAlgebra.ιMulti_of_eq_zero hB,
      ExteriorAlgebra.ιMulti_of_eq_zero (by rw [hA, hg])]
  · rw [exteriorPower.ιMulti_apply_coe, ExteriorAlgebra.ιMulti_of_eq_zero hC,
      ExteriorAlgebra.ιMulti_of_eq_zero (by rw [hg, hD])]

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

/-- Two linear maps out of `L ⊗ N`, with `L` a line, that agree on `y ⊗ n` and on `y₀ ⊗ n`
respectively, where `y₀ = c • y` is nonzero, differ by the factor `c`. -/
theorem eq_smul_of_tmul_eq_tmul {L N P : Type*} [AddCommGroup L] [Module K L] [AddCommGroup N]
    [Module K N] [AddCommGroup P] [Module K P] (hL : finrank K L = 1)
    {M M₀ : L ⊗[K] N →ₗ[K] P} {y y₀ : L} {c : K} (hy₀ : y₀ ≠ 0) (hyy : y₀ = c • y)
    (hM : ∀ n, M (y ⊗ₜ n) = M₀ (y₀ ⊗ₜ n)) : M = c • M₀ := by
  refine TensorProduct.ext' fun e n ↦ ?_
  obtain ⟨s, rfl⟩ := (finrank_eq_one_iff_of_ne_zero' _ hy₀).1 hL e
  have h₀ : M (y₀ ⊗ₜ n) = c • M₀ (y₀ ⊗ₜ n) := by
    rw [← hM, ← map_smul, smul_tmul', ← hyy]
  rw [LinearMap.smul_apply, ← smul_tmul', map_smul, map_smul, h₀, smul_comm]

section Naturality

/-! ### Naturality under isomorphisms of exact sequences -/

variable {A' B' C' D' : Type*} [AddCommGroup A'] [Module K A'] [AddCommGroup B'] [Module K B']
  [AddCommGroup C'] [Module K C'] [AddCommGroup D'] [Module K D']
  {f' : A' →ₗ[K] B'} {g' : B' →ₗ[K] C'} {h' : C' →ₗ[K] D'}
  [FiniteDimensional K A'] [FiniteDimensional K C'] (hf' : Function.Injective f')
  (hfg' : Function.Exact f' g') (hgh' : Function.Exact g' h') (hh' : Function.Surjective h')
  (eA : A ≃ₗ[K] A') (eB : B ≃ₗ[K] B') (eC : C ≃ₗ[K] C') (eD : D ≃ₗ[K] D')

omit [FiniteDimensional K A] [FiniteDimensional K C] in
/-- An isomorphism `e` sends an element of `det B` that is the exterior product of an appended
family `Fin.append p v` to the exterior product of the appended images of the two parts,
renumbered along `Fin.cast`. -/
private theorem coe_detLineCongr_eq_ιMulti_append (e : B ≃ₗ[K] B') {x : detLine K B}
    {m k m' k' : ℕ} {p : Fin m → B} {v : Fin k → B} {p' : Fin m' → B'} {v' : Fin k' → B'}
    (hx : (x : ExteriorAlgebra K B) = ExteriorAlgebra.ιMulti K _ (Fin.append p v))
    (hm : m' = m) (hk : k' = k) (hp : p' = e ∘ p ∘ Fin.cast hm) (hv : v' = e ∘ v ∘ Fin.cast hk) :
    (e.detLineCongr x : ExteriorAlgebra K B') = ExteriorAlgebra.ιMulti K _ (Fin.append p' v') := by
  subst hp hv
  rw [LinearEquiv.coe_detLineCongr, hx, ← ExteriorAlgebra.ιMulti_mul_ιMulti,
    ← ExteriorAlgebra.ιMulti_mul_ιMulti, map_mul, ExteriorAlgebra.map_apply_ιMulti,
    ExteriorAlgebra.map_apply_ιMulti, ← Function.comp_assoc, ExteriorAlgebra.ιMulti_comp_cast,
    ← Function.comp_assoc, ExteriorAlgebra.ιMulti_comp_cast, LinearEquiv.coe_coe]

include hf hfg hgh hh hf' hfg' hgh' hh' in
/-- **Naturality of the four-term isomorphism.** An isomorphism of four-term exact sequences,
given by isomorphisms `eA`, `eB`, `eC` and `eD` commuting with the maps of the two sequences,
intertwines their isomorphisms `det B ⊗ (det C)^* ≃ det A ⊗ (det D)^*`
(`TauCeti.detLineFourTermEquiv`) with the induced isomorphisms of determinant lines. -/
theorem detLineFourTermEquiv_congr (hfA : f' ∘ₗ eA.toLinearMap = eB.toLinearMap ∘ₗ f)
    (hgB : g' ∘ₗ eB.toLinearMap = eC.toLinearMap ∘ₗ g)
    (hhC : h' ∘ₗ eC.toLinearMap = eD.toLinearMap ∘ₗ h)
    (t : detLine K B ⊗[K] Dual K (detLine K C)) :
    detLineFourTermEquiv hf' hfg' hgh' hh'
        (TensorProduct.congr eB.detLineCongr eC.detLineCongr.symm.dualMap t) =
      TensorProduct.congr eA.detLineCongr eD.detLineCongr.symm.dualMap
        (detLineFourTermEquiv hf hfg hgh hh t) := by
  have : FiniteDimensional K D := Module.Finite.of_surjective h hh
  -- The exterior products of the first sequence entering `TauCeti.detLineFourTermEquiv_tmul`;
  -- `β` spans `det B`.
  obtain ⟨v, z, β, γ, ξ, hβ, hγ, hξ, hspan⟩ := exists_spanning_ιMulti_append hf hfg hgh hh
  set u := ⇑(Module.finBasis K A)
  -- Their images in the second sequence, and the families computing them.
  have hr : finrank K (LinearMap.range g') = finrank K (LinearMap.range g) := by
    have hrange : LinearMap.range g' = (LinearMap.range g).map eC.toLinearMap := by
      rw [← LinearMap.range_comp, ← hgB, LinearMap.range_comp, LinearEquiv.range,
        Submodule.map_top]
    rw [hrange, LinearEquiv.finrank_map_eq]
  set u' := eA ∘ u ∘ Fin.cast eA.finrank_eq.symm
  set v' := eB ∘ v ∘ Fin.cast hr
  set z' := eC ∘ z ∘ Fin.cast eD.finrank_eq.symm
  have hfu : ⇑f' ∘ ⇑eA = ⇑eB ∘ ⇑f := funext (LinearMap.congr_fun hfA)
  have hgv : ⇑g' ∘ ⇑eB = ⇑eC ∘ ⇑g := funext (LinearMap.congr_fun hgB)
  have hhz : ⇑h' ∘ (⇑eC ∘ z) = ⇑eD ∘ (⇑h ∘ z) := funext fun i ↦ LinearMap.congr_fun hhC (z i)
  have hβ' : (eB.detLineCongr β : ExteriorAlgebra K B') =
      ExteriorAlgebra.ιMulti K _ (Fin.append (f' ∘ u') v') :=
    coe_detLineCongr_eq_ιMulti_append eB hβ eA.finrank_eq.symm hr
      (by simp only [u', ← Function.comp_assoc, hfu]) rfl
  have hγ' : (eC.detLineCongr γ : ExteriorAlgebra K C') =
      ExteriorAlgebra.ιMulti K _ (Fin.append (g' ∘ v') z') :=
    coe_detLineCongr_eq_ιMulti_append eC hγ hr eD.finrank_eq.symm
      (by simp only [v', ← Function.comp_assoc, hgv]) rfl
  have hξ' : (ξ ∘ₗ eD.detLineCongr.symm.toLinearMap) (exteriorPower.ιMulti K _ (h' ∘ z')) = 1 := by
    have : h' ∘ z' = eD ∘ (h ∘ z) ∘ Fin.cast eD.finrank_eq.symm := by
      simp only [z', ← Function.comp_assoc, hhz]
    rw [LinearMap.comp_apply, LinearEquiv.coe_coe, this, ← LinearEquiv.detLineCongr_ιMulti,
      LinearEquiv.symm_apply_apply, hξ]
  -- Both sides are linear in `t`, and `det B` is spanned by `β`.
  induction t using TensorProduct.inductionOn with
  | add t₁ t₂ h₁ h₂ => simp only [map_add, h₁, h₂]
  | tmul x φ =>
  obtain ⟨r, rfl⟩ := hspan x
  rw [← TensorProduct.smul_tmul']
  simp only [map_smul]
  congr 1
  rw [TensorProduct.congr_tmul,
    detLineFourTermEquiv_tmul_eq_smul_tmul hf' hfg' hgh' hh' u' v' z' hβ' hγ' _ hξ',
    detLineFourTermEquiv_tmul_eq_smul_tmul hf hfg hgh hh u v z hβ hγ φ hξ, map_smul,
    TensorProduct.congr_tmul, LinearEquiv.detLineCongr_ιMulti, LinearEquiv.dualMap_apply,
    LinearEquiv.symm_apply_apply]
  -- The exterior products agree since `u'` is `eA ∘ u ∘ Fin.cast _`; compare the functionals
  -- pointwise.
  exact congrArg (φ γ • ·) (congrArg (_ ⊗ₜ ·)
    (LinearMap.ext fun x ↦ (LinearEquiv.dualMap_apply _ ξ x).symm))

end Naturality

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
  have : FiniteDimensional K B' := hjπ.moduleFinite
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
  have hr := finrank_range_eq_finrank_range_add_of_exact_comp hf hfg hf' hfg' hj hjπ hπg
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
  have : FiniteDimensional K A₄ := h₃₄.moduleFinite
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
  have : FiniteDimensional K A₄ := h₃₄.moduleFinite
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
    ⟨_, (Module.Invertible.rid_lTensor_eval_tmul_eq_self hι₀' _).symm⟩
  have hX : ι₀' (exteriorPower.ιMulti K _ (f₃.rangeRestrict ∘ w)) • X =
      γ₀' γ • exteriorPower.ιMulti K _ u := by
    have := detLineFourTermEquiv_tmul hf₁ h₁₂ h₂₃.rangeRestrict f₃.surjective_rangeRestrict u v w
      hβ hγ γ₀'
    rwa [hE₁, LinearMap.lTensor_tmul, TensorProduct.rid_tmul, Dual.eval_apply] at this
  -- The second four-term sequence, written against `χ`.
  have hE₂ := detLineFourTermEquiv_tmul_eq_smul_tmul (LinearMap.range f₃).injective_subtype
    h₃₄.range_subtype h₄₅ hf₅ (f₃.rangeRestrict ∘ w) x y (β := δ)
    (by rw [hδ, LinearMap.subtype_comp_rangeRestrict_comp])
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
  rw [← Module.Invertible.apply_smul_eq_self hγ₀' γ]
  simp only [TensorProduct.tmul_smul, ← TensorProduct.smul_tmul', smul_smul]
  rw [mul_smul, mul_smul]
  congr 1
  rw [TensorProduct.smul_tmul', TensorProduct.smul_tmul', hX, TensorProduct.smul_tmul',
    TensorProduct.smul_tmul']

include hf₁ h₁₂ h₂₃ h₃₄ h₄₅ hf₅ in
/-- **Exterior products spanning `det A₂`.** For an exact sequence
`0 → A₁ → A₂ → A₃ → A₄ → A₅ → A₆ → 0`, there are families `v`, `w`, `x` of `dim (range fᵢ)`
vectors of `A₂`, `A₃`, `A₄` for `i = 2, 3, 4` and a family `y` of `dim A₆` vectors of `A₅`, the
exterior products `β`, `γ`, `δ`, `ε` built from them as in `TauCeti.detLineSixTermEquiv_tmul`
(with a basis of `A₁` as first family), and functionals `ψ` and `χ` normalized at `δ` and at the
exterior product of `f₅ ∘ y`, such that `β` spans `det A₂`. -/
theorem exists_spanning_ιMulti_append_sixTerm :
    ∃ (v : Fin (finrank K (LinearMap.range f₂)) → A₂)
      (w : Fin (finrank K (LinearMap.range f₃)) → A₃)
      (x : Fin (finrank K (LinearMap.range f₄)) → A₄) (y : Fin (finrank K A₆) → A₅)
      (β : detLine K A₂) (γ : detLine K A₃) (δ : detLine K A₄) (ε : detLine K A₅)
      (ψ : Dual K (detLine K A₄)) (χ : Dual K (detLine K A₆)),
      (β : ExteriorAlgebra K A₂) =
          ExteriorAlgebra.ιMulti K _ (Fin.append (f₁ ∘ Module.finBasis K A₁) v) ∧
        (γ : ExteriorAlgebra K A₃) = ExteriorAlgebra.ιMulti K _ (Fin.append (f₂ ∘ v) w) ∧
        (δ : ExteriorAlgebra K A₄) = ExteriorAlgebra.ιMulti K _ (Fin.append (f₃ ∘ w) x) ∧
        (ε : ExteriorAlgebra K A₅) = ExteriorAlgebra.ιMulti K _ (Fin.append (f₄ ∘ x) y) ∧
        ψ δ = 1 ∧ χ (exteriorPower.ιMulti K _ (f₅ ∘ y)) = 1 ∧
        ∀ z : detLine K A₂, ∃ r : K, z = r • β := by
  have : FiniteDimensional K A₄ := h₃₄.moduleFinite
  have : FiniteDimensional K A₆ := Module.Finite.of_surjective f₅ hf₅
  -- The first four-term sequence `0 → A₁ → A₂ → A₃ → range f₃ → 0` supplies `v`, `w`, `β`, `γ`.
  obtain ⟨v, w, β, γ, ξ, hβ, hγ, hξ, hspan⟩ :=
    exists_spanning_ιMulti_append hf₁ h₁₂ h₂₃.rangeRestrict f₃.surjective_rangeRestrict
  -- Vectors lifting bases of `range f₄` and `A₆`.
  choose x hx using fun i ↦ f₄.surjective_rangeRestrict (Module.finBasis K (LinearMap.range f₄) i)
  choose y hy using fun i ↦ hf₅ (Module.finBasis K A₆ i)
  have hx' : exteriorPower.ιMulti K _ (f₄.rangeRestrict ∘ x) ≠ 0 := by
    rw [show f₄.rangeRestrict ∘ x = ⇑(Module.finBasis K (LinearMap.range f₄)) from funext hx]
    exact (exteriorPower.ιMulti_ne_zero_iff _).2 (Module.finBasis K _).linearIndependent
  obtain ⟨η, hη⟩ := Projective.exists_dual_eq_one K hx'
  -- The exterior product `δ` is nonzero: `ξ ⊗ η` contracts it to `1`.
  have hδ : detLineShortExactEquiv (LinearMap.range f₃).injective_subtype
      h₃₄.rangeRestrict.range_subtype f₄.surjective_rangeRestrict
      (exteriorPower.ιMulti K _ (f₃.rangeRestrict ∘ w) ⊗ₜ
        exteriorPower.ιMulti K _ (f₄.rangeRestrict ∘ x)) ≠ 0 := by
    refine (LinearEquiv.map_ne_zero_iff _).2 fun h ↦ one_ne_zero (α := K) ?_
    simpa [hξ, hη] using congrArg (TensorProduct.lid K K ∘ TensorProduct.map ξ η) h
  obtain ⟨ψ, hψ⟩ := Projective.exists_dual_eq_one K hδ
  have hω : exteriorPower.ιMulti K _ (f₅ ∘ y) ≠ 0 := by
    rw [show f₅ ∘ y = ⇑(Module.finBasis K A₆) from funext hy]
    exact (exteriorPower.ιMulti_ne_zero_iff _).2 (Module.finBasis K A₆).linearIndependent
  obtain ⟨χ, hχ⟩ := Projective.exists_dual_eq_one K hω
  refine ⟨v, w, x, y, β, γ, _,
    detLineShortExactEquiv (LinearMap.range f₄).injective_subtype h₄₅.range_subtype hf₅
      (exteriorPower.ιMulti K _ (f₄.rangeRestrict ∘ x) ⊗ₜ exteriorPower.ιMulti K _ (f₅ ∘ y)),
    ψ, χ, hβ, hγ, ?_, ?_, hψ, hχ, hspan⟩ <;>
  rw [coe_detLineShortExactEquiv_tmul, LinearMap.subtype_comp_rangeRestrict_comp]

section Naturality

/-! ### Naturality under isomorphisms of six-term exact sequences -/

variable {A₁' A₂' A₃' A₄' A₅' A₆' : Type*} [AddCommGroup A₁'] [Module K A₁'] [AddCommGroup A₂']
  [Module K A₂'] [AddCommGroup A₃'] [Module K A₃'] [AddCommGroup A₄'] [Module K A₄']
  [AddCommGroup A₅'] [Module K A₅'] [AddCommGroup A₆'] [Module K A₆']
  {f₁' : A₁' →ₗ[K] A₂'} {f₂' : A₂' →ₗ[K] A₃'} {f₃' : A₃' →ₗ[K] A₄'} {f₄' : A₄' →ₗ[K] A₅'}
  {f₅' : A₅' →ₗ[K] A₆'} [FiniteDimensional K A₁'] [FiniteDimensional K A₃']
  [FiniteDimensional K A₅'] (hf₁' : Function.Injective f₁') (h₁₂' : Function.Exact f₁' f₂')
  (h₂₃' : Function.Exact f₂' f₃') (h₃₄' : Function.Exact f₃' f₄') (h₄₅' : Function.Exact f₄' f₅')
  (hf₅' : Function.Surjective f₅') (e₁ : A₁ ≃ₗ[K] A₁') (e₂ : A₂ ≃ₗ[K] A₂') (e₃ : A₃ ≃ₗ[K] A₃')
  (e₄ : A₄ ≃ₗ[K] A₄') (e₅ : A₅ ≃ₗ[K] A₅') (e₆ : A₆ ≃ₗ[K] A₆')

include hf₁ h₁₂ h₂₃ h₃₄ h₄₅ hf₅ hf₁' h₁₂' h₂₃' h₃₄' h₄₅' hf₅' in
/-- `TauCeti.detLineSixTermEquiv_congr` on an exterior product `β ⊗ φ`, given the data with which
`TauCeti.detLineSixTermEquiv_tmul` evaluates both six-term isomorphisms, the second set of data
being the image of the first. -/
private theorem detLineSixTermEquiv_congr_tmul (u : Fin (finrank K A₁) → A₁)
    (v : Fin (finrank K (LinearMap.range f₂)) → A₂) (w : Fin (finrank K (LinearMap.range f₃)) → A₃)
    (x : Fin (finrank K (LinearMap.range f₄)) → A₄) (y : Fin (finrank K A₆) → A₅)
    (u' : Fin (finrank K A₁') → A₁') (v' : Fin (finrank K (LinearMap.range f₂')) → A₂')
    (w' : Fin (finrank K (LinearMap.range f₃')) → A₃')
    (x' : Fin (finrank K (LinearMap.range f₄')) → A₄') (y' : Fin (finrank K A₆') → A₅')
    {β : detLine K A₂} (hβ : (β : ExteriorAlgebra K A₂) =
      ExteriorAlgebra.ιMulti K _ (Fin.append (f₁ ∘ u) v))
    {γ : detLine K A₃} (hγ : (γ : ExteriorAlgebra K A₃) =
      ExteriorAlgebra.ιMulti K _ (Fin.append (f₂ ∘ v) w))
    {δ : detLine K A₄} (hδ : (δ : ExteriorAlgebra K A₄) =
      ExteriorAlgebra.ιMulti K _ (Fin.append (f₃ ∘ w) x))
    {ε : detLine K A₅} (hε : (ε : ExteriorAlgebra K A₅) =
      ExteriorAlgebra.ιMulti K _ (Fin.append (f₄ ∘ x) y))
    (hβ' : (e₂.detLineCongr β : ExteriorAlgebra K A₂') =
      ExteriorAlgebra.ιMulti K _ (Fin.append (f₁' ∘ u') v'))
    (hγ' : (e₃.detLineCongr γ : ExteriorAlgebra K A₃') =
      ExteriorAlgebra.ιMulti K _ (Fin.append (f₂' ∘ v') w'))
    (hδ' : (e₄.detLineCongr δ : ExteriorAlgebra K A₄') =
      ExteriorAlgebra.ιMulti K _ (Fin.append (f₃' ∘ w') x'))
    (hε' : (e₅.detLineCongr ε : ExteriorAlgebra K A₅') =
      ExteriorAlgebra.ιMulti K _ (Fin.append (f₄' ∘ x') y'))
    (hu : exteriorPower.ιMulti K _ u' = e₁.detLineCongr (exteriorPower.ιMulti K _ u))
    (φ : Dual K (detLine K A₅)) {ψ : Dual K (detLine K A₄)} (hψ : ψ δ = 1)
    {χ : Dual K (detLine K A₆)} (hχ : χ (exteriorPower.ιMulti K _ (f₅ ∘ y)) = 1)
    (hχ' : χ (e₆.detLineCongr.symm (exteriorPower.ιMulti K _ (f₅' ∘ y'))) = 1) :
    detLineSixTermEquiv hf₁' h₁₂' h₂₃' h₃₄' h₄₅' hf₅'
        (TensorProduct.congr e₂.detLineCongr e₅.detLineCongr.symm.dualMap (β ⊗ₜ φ)) =
      TensorProduct.congr
        (TensorProduct.congr e₁.detLineCongr e₄.detLineCongr.symm.dualMap)
        (TensorProduct.congr e₃.detLineCongr e₆.detLineCongr.symm.dualMap)
        (detLineSixTermEquiv hf₁ h₁₂ h₂₃ h₃₄ h₄₅ hf₅ (β ⊗ₜ φ)) := by
  -- The transported functionals `ψ ∘ e₄⁻¹` and `χ ∘ e₆⁻¹` are normalized for the second sequence.
  have hψ' : e₄.detLineCongr.symm.dualMap ψ (e₄.detLineCongr δ) = 1 := by
    rw [LinearEquiv.dualMap_apply, LinearEquiv.symm_apply_apply, hψ]
  have hχ'' : e₆.detLineCongr.symm.dualMap χ (exteriorPower.ιMulti K _ (f₅' ∘ y')) = 1 := by
    rw [LinearEquiv.dualMap_apply, hχ']
  have hs : e₅.detLineCongr.symm.dualMap φ (e₅.detLineCongr ε) = φ ε := by
    rw [LinearEquiv.dualMap_apply, LinearEquiv.symm_apply_apply]
  rw [TensorProduct.congr_tmul,
    detLineSixTermEquiv_tmul hf₁' h₁₂' h₂₃' h₃₄' h₄₅' hf₅' u' v' w' x' y' hβ' hγ' hδ' hε' _ hψ'
      hχ'',
    detLineSixTermEquiv_tmul hf₁ h₁₂ h₂₃ h₃₄ h₄₅ hf₅ u v w x y hβ hγ hδ hε φ hψ hχ, map_smul, hs,
    hu, TensorProduct.congr_tmul, TensorProduct.congr_tmul, TensorProduct.congr_tmul]

include hf₁ h₁₂ h₂₃ h₃₄ h₄₅ hf₅ hf₁' h₁₂' h₂₃' h₃₄' h₄₅' hf₅' in
/-- **Naturality of the six-term isomorphism.** An isomorphism of six-term exact sequences,
given by isomorphisms `e₁`, …, `e₆` commuting with the maps of the two sequences, intertwines
their isomorphisms `det A₂ ⊗ (det A₅)^* ≃ (det A₁ ⊗ (det A₄)^*) ⊗ (det A₃ ⊗ (det A₆)^*)`
(`TauCeti.detLineSixTermEquiv`) with the induced isomorphisms of determinant lines. -/
theorem detLineSixTermEquiv_congr (h₁ : f₁' ∘ₗ e₁.toLinearMap = e₂.toLinearMap ∘ₗ f₁)
    (h₂ : f₂' ∘ₗ e₂.toLinearMap = e₃.toLinearMap ∘ₗ f₂)
    (h₃ : f₃' ∘ₗ e₃.toLinearMap = e₄.toLinearMap ∘ₗ f₃)
    (h₄ : f₄' ∘ₗ e₄.toLinearMap = e₅.toLinearMap ∘ₗ f₄)
    (h₅ : f₅' ∘ₗ e₅.toLinearMap = e₆.toLinearMap ∘ₗ f₅)
    (t : detLine K A₂ ⊗[K] Dual K (detLine K A₅)) :
    detLineSixTermEquiv hf₁' h₁₂' h₂₃' h₃₄' h₄₅' hf₅'
        (TensorProduct.congr e₂.detLineCongr e₅.detLineCongr.symm.dualMap t) =
      TensorProduct.congr
        (TensorProduct.congr e₁.detLineCongr e₄.detLineCongr.symm.dualMap)
        (TensorProduct.congr e₃.detLineCongr e₆.detLineCongr.symm.dualMap)
        (detLineSixTermEquiv hf₁ h₁₂ h₂₃ h₃₄ h₄₅ hf₅ t) := by
  -- The exterior products of the first sequence entering `TauCeti.detLineSixTermEquiv_tmul`;
  -- `β` spans `det A₂`.
  obtain ⟨v, w, x, y, β, γ, δ, ε, ψ, χ, hβ, hγ, hδ, hε, hψ, hχ, hspan⟩ :=
    exists_spanning_ιMulti_append_sixTerm hf₁ h₁₂ h₂₃ h₃₄ h₄₅ hf₅
  -- Their images in the second sequence are computed by the transported families.
  have r₂ : finrank K (LinearMap.range f₂') = finrank K (LinearMap.range f₂) := by
    rw [← f₂.map_range_eq_range_of_comp_eq e₂.surjective h₂, LinearEquiv.finrank_map_eq]
  have r₃ : finrank K (LinearMap.range f₃') = finrank K (LinearMap.range f₃) := by
    rw [← f₃.map_range_eq_range_of_comp_eq e₃.surjective h₃, LinearEquiv.finrank_map_eq]
  have r₄ : finrank K (LinearMap.range f₄') = finrank K (LinearMap.range f₄) := by
    rw [← f₄.map_range_eq_range_of_comp_eq e₄.surjective h₄, LinearEquiv.finrank_map_eq]
  have c₁ : ⇑f₁' ∘ ⇑e₁ = ⇑e₂ ∘ ⇑f₁ := funext (LinearMap.congr_fun h₁)
  have c₂ : ⇑f₂' ∘ ⇑e₂ = ⇑e₃ ∘ ⇑f₂ := funext (LinearMap.congr_fun h₂)
  have c₃ : ⇑f₃' ∘ ⇑e₃ = ⇑e₄ ∘ ⇑f₃ := funext (LinearMap.congr_fun h₃)
  have c₄ : ⇑f₄' ∘ ⇑e₄ = ⇑e₅ ∘ ⇑f₄ := funext (LinearMap.congr_fun h₄)
  have c₅ : ⇑f₅' ∘ (⇑e₅ ∘ y) = ⇑e₆ ∘ (⇑f₅ ∘ y) := funext fun i ↦ LinearMap.congr_fun h₅ (y i)
  have hβ' := coe_detLineCongr_eq_ιMulti_append e₂ hβ e₁.finrank_eq.symm r₂
    (p' := f₁' ∘ (e₁ ∘ Module.finBasis K A₁ ∘ Fin.cast e₁.finrank_eq.symm))
    (by simp only [← Function.comp_assoc, c₁]) rfl
  have hγ' := coe_detLineCongr_eq_ιMulti_append e₃ hγ r₂ r₃
    (p' := f₂' ∘ (e₂ ∘ v ∘ Fin.cast r₂)) (by simp only [← Function.comp_assoc, c₂]) rfl
  have hδ' := coe_detLineCongr_eq_ιMulti_append e₄ hδ r₃ r₄
    (p' := f₃' ∘ (e₃ ∘ w ∘ Fin.cast r₃)) (by simp only [← Function.comp_assoc, c₃]) rfl
  have hε' := coe_detLineCongr_eq_ιMulti_append e₅ hε r₄ e₆.finrank_eq.symm
    (p' := f₄' ∘ (e₄ ∘ x ∘ Fin.cast r₄)) (by simp only [← Function.comp_assoc, c₄]) rfl
  have hχ' : χ (e₆.detLineCongr.symm (exteriorPower.ιMulti K _
      (f₅' ∘ (e₅ ∘ y ∘ Fin.cast e₆.finrank_eq.symm)))) = 1 := by
    have : f₅' ∘ (e₅ ∘ y ∘ Fin.cast e₆.finrank_eq.symm) =
        e₆ ∘ (f₅ ∘ y) ∘ Fin.cast e₆.finrank_eq.symm := by
      simp only [← Function.comp_assoc, c₅]
    rw [this, ← LinearEquiv.detLineCongr_ιMulti, LinearEquiv.symm_apply_apply, hχ]
  -- Both sides are linear in `t`, and `det A₂` is spanned by `β`.
  induction t using TensorProduct.inductionOn with
  | add t₁ t₂ h₁ h₂ => simp only [map_add, h₁, h₂]
  | tmul z φ =>
  obtain ⟨r, rfl⟩ := hspan z
  rw [← TensorProduct.smul_tmul']
  simp only [map_smul]
  exact congrArg (r • ·) (detLineSixTermEquiv_congr_tmul hf₁ h₁₂ h₂₃ h₃₄ h₄₅ hf₅ hf₁' h₁₂' h₂₃'
    h₃₄' h₄₅' hf₅' e₁ e₂ e₃ e₄ e₅ e₆ _ v w x y _ _ _ _ _ hβ hγ hδ hε hβ' hγ' hδ' hε'
    (LinearEquiv.detLineCongr_ιMulti e₁ _).symm φ hψ hχ hχ')

end Naturality

end SixTerm

end TauCeti
